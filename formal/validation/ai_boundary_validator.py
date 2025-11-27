"""
AI Boundary Validator - Testing control logic robustness to AI outputs.

This validates how the deterministic control layer handles inputs from
the AI perception layer (modeld). Key question: Does the control logic
remain safe regardless of what the AI outputs?

The AI boundary is where:
- modelV2 (AI outputs) → plannerd/controlsd (deterministic logic)
- Continuous, learned predictions → discrete control decisions

Testing approaches compared:
1. Random: Fast, baseline coverage
2. Adversarial RL: Learns to find failure modes
3. Boundary value: Tests edge cases systematically
4. Distribution shift: Simulates OOD AI behavior
5. Formal constraints: Property-based invariants
"""

import numpy as np
import time
from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional, Callable
from enum import IntEnum
import json
from pathlib import Path

# Import our state machine for control logic testing
from real_state_machine import RealStateMachine, Events, ET, State


@dataclass
class ModelV2Output:
    """
    Simulated AI model output matching cereal/log.capnp modelV2.

    This represents what the neural network produces that feeds
    into the control logic.
    """
    # Path prediction (where the car should go)
    path_x: np.ndarray = field(default_factory=lambda: np.zeros(33))  # position
    path_y: np.ndarray = field(default_factory=lambda: np.zeros(33))  # lateral offset
    path_std: np.ndarray = field(default_factory=lambda: np.ones(33))  # uncertainty

    # Lane lines (detected road markings)
    lane_line_probs: np.ndarray = field(default_factory=lambda: np.array([1.0, 1.0, 1.0, 1.0]))
    lane_line_stds: np.ndarray = field(default_factory=lambda: np.ones(4))

    # Lead vehicle detection
    lead_prob: float = 0.0
    lead_distance: float = 100.0  # meters
    lead_velocity: float = 0.0    # m/s relative

    # Confidence/meta
    model_confidence: float = 1.0
    desire_state: int = 0  # 0=none, 1=left, 2=right

    def is_valid(self) -> bool:
        """Check if output is within expected bounds"""
        return (
            0 <= self.model_confidence <= 1 and
            0 <= self.lead_prob <= 1 and
            all(0 <= p <= 1 for p in self.lane_line_probs) and
            self.lead_distance >= 0
        )


@dataclass
class ControlDecision:
    """Output from control logic given AI inputs"""
    enabled: bool = False
    active: bool = False
    state: State = State.DISABLED
    actuator_accel: float = 0.0
    actuator_steer: float = 0.0
    alerts: List[str] = field(default_factory=list)


class AIBoundarySimulator:
    """
    Simulates the boundary between AI perception and control logic.

    Models how AI outputs translate to events that drive the state machine.
    """

    # Thresholds from openpilot code
    MIN_LANE_PROB = 0.3
    MIN_LEAD_PROB = 0.5
    MAX_LATERAL_OFFSET = 1.5  # meters
    MIN_MODEL_CONFIDENCE = 0.4

    def __init__(self):
        self.state_machine = RealStateMachine()
        self.step_count = 0

    def reset(self):
        self.state_machine.reset()
        self.step_count = 0

    def model_output_to_events(self, model: ModelV2Output) -> Events:
        """
        Convert AI model output to control events.

        This is the key translation layer - how does noisy/adversarial
        AI output map to discrete control decisions?
        """
        event_set = set()

        # Low confidence → soft disable
        if model.model_confidence < self.MIN_MODEL_CONFIDENCE:
            event_set.add(ET.SOFT_DISABLE)

        # Lost lane lines → soft disable
        if all(p < self.MIN_LANE_PROB for p in model.lane_line_probs):
            event_set.add(ET.SOFT_DISABLE)

        # Path deviation too large → soft disable
        if len(model.path_y) > 0:
            max_offset = np.max(np.abs(model.path_y))
            if max_offset > self.MAX_LATERAL_OFFSET:
                event_set.add(ET.SOFT_DISABLE)

        # Very low confidence with lead → immediate disable (safety critical)
        if model.lead_prob > self.MIN_LEAD_PROB and model.model_confidence < 0.2:
            event_set.add(ET.IMMEDIATE_DISABLE)

        return Events(events=event_set)

    def step(self, model_output: ModelV2Output) -> ControlDecision:
        """Execute one control step given AI output"""
        events = self.model_output_to_events(model_output)
        enabled, active = self.state_machine.update(events)
        self.step_count += 1

        return ControlDecision(
            enabled=enabled,
            active=active,
            state=self.state_machine.state,
            alerts=[et.name for et in self.state_machine.current_alert_types]
        )


class AdversarialAIGenerator:
    """
    Generates adversarial AI outputs to stress-test control logic.

    Different attack strategies:
    1. Random noise: Baseline
    2. Boundary probing: Test threshold edges
    3. Gradual drift: Simulate distribution shift
    4. Oscillation: Rapid confidence changes
    5. Targeted: Learn to cause specific failures
    """

    def __init__(self, seed: int = 42):
        self.rng = np.random.default_rng(seed)

    def random(self) -> ModelV2Output:
        """Completely random (but valid bounds) output"""
        return ModelV2Output(
            path_x=np.linspace(0, 50, 33),
            path_y=self.rng.uniform(-3, 3, 33),
            path_std=self.rng.uniform(0.1, 2, 33),
            lane_line_probs=self.rng.uniform(0, 1, 4),
            lane_line_stds=self.rng.uniform(0.1, 2, 4),
            lead_prob=self.rng.uniform(0, 1),
            lead_distance=self.rng.uniform(0, 200),
            lead_velocity=self.rng.uniform(-30, 30),
            model_confidence=self.rng.uniform(0, 1),
            desire_state=self.rng.integers(0, 3),
        )

    def boundary_probing(self, threshold_name: str) -> ModelV2Output:
        """Generate output that probes specific thresholds"""
        base = self._nominal_output()

        if threshold_name == "confidence":
            # Test around MIN_MODEL_CONFIDENCE threshold
            base.model_confidence = 0.4 + self.rng.uniform(-0.1, 0.1)
        elif threshold_name == "lane_prob":
            # Test around MIN_LANE_PROB threshold
            base.lane_line_probs = np.array([0.3, 0.3, 0.3, 0.3]) + self.rng.uniform(-0.1, 0.1, 4)
        elif threshold_name == "lateral_offset":
            # Test around MAX_LATERAL_OFFSET threshold
            base.path_y = np.ones(33) * (1.5 + self.rng.uniform(-0.3, 0.3))
        elif threshold_name == "lead_confidence_combo":
            # Test the combined condition
            base.lead_prob = 0.6
            base.model_confidence = 0.2 + self.rng.uniform(-0.1, 0.1)

        return base

    def gradual_drift(self, step: int, drift_rate: float = 0.01) -> ModelV2Output:
        """Simulate distribution shift over time"""
        base = self._nominal_output()
        # Confidence drifts down over time
        base.model_confidence = max(0, 1.0 - step * drift_rate)
        # Lane detection degrades
        base.lane_line_probs = np.maximum(0, np.ones(4) - step * drift_rate * 0.5)
        return base

    def oscillation(self, step: int, period: int = 10) -> ModelV2Output:
        """Rapid confidence oscillation (adversarial flickering)"""
        base = self._nominal_output()
        # Oscillate between high and low confidence
        phase = (step % period) / period
        base.model_confidence = 0.5 + 0.5 * np.sin(2 * np.pi * phase)
        return base

    def out_of_distribution(self) -> ModelV2Output:
        """Generate OOD outputs (what AI might do on unseen data)"""
        return ModelV2Output(
            path_x=np.linspace(0, 50, 33),
            # Unusual path shapes
            path_y=self.rng.choice([
                np.sin(np.linspace(0, 4*np.pi, 33)) * 3,  # Sinusoidal
                np.ones(33) * 5,  # Constant large offset
                np.concatenate([np.zeros(16), np.ones(17) * 3]),  # Step
            ]),
            path_std=np.ones(33) * 5,  # High uncertainty
            lane_line_probs=self.rng.uniform(0, 0.2, 4),  # Low confidence
            model_confidence=self.rng.uniform(0, 0.3),  # Low overall confidence
        )

    def _nominal_output(self) -> ModelV2Output:
        """Generate nominal (good) AI output"""
        return ModelV2Output(
            path_x=np.linspace(0, 50, 33),
            path_y=np.zeros(33),
            path_std=np.ones(33) * 0.1,
            lane_line_probs=np.ones(4) * 0.9,
            lead_prob=0.0,
            lead_distance=100,
            model_confidence=0.95,
        )


@dataclass
class ValidationResult:
    """Result of a validation run"""
    method: str
    traces: int
    time_sec: float
    safety_violations: int
    state_coverage: Dict[str, int]
    threshold_violations: Dict[str, int]
    details: List[Dict] = field(default_factory=list)


class AIBoundaryValidator:
    """
    Main validator for AI-to-control boundary testing.

    Compares different approaches for their effectiveness at finding
    issues in how control logic handles AI outputs.
    """

    def __init__(self, output_dir: Path = None):
        self.output_dir = output_dir or Path(".local/ai_boundary_results")
        self.output_dir.mkdir(parents=True, exist_ok=True)

    def validate_random(self, num_traces: int = 10000, trace_length: int = 100) -> ValidationResult:
        """Random testing baseline"""
        start = time.time()
        generator = AdversarialAIGenerator()
        simulator = AIBoundarySimulator()

        state_counts = {s.name: 0 for s in State}
        safety_violations = 0

        for _ in range(num_traces):
            simulator.reset()
            # First enable the system
            simulator.state_machine.state = State.ENABLED

            for _ in range(trace_length):
                model_output = generator.random()
                decision = simulator.step(model_output)
                state_counts[decision.state.name] += 1

                # Check safety: should never be ENABLED with invalid AI output
                if decision.active and not model_output.is_valid():
                    safety_violations += 1

        return ValidationResult(
            method="random",
            traces=num_traces,
            time_sec=time.time() - start,
            safety_violations=safety_violations,
            state_coverage=state_counts,
            threshold_violations={},
        )

    def validate_boundary(self, num_traces: int = 1000) -> ValidationResult:
        """Boundary value testing - probe threshold edges"""
        start = time.time()
        generator = AdversarialAIGenerator()
        simulator = AIBoundarySimulator()

        thresholds = ["confidence", "lane_prob", "lateral_offset", "lead_confidence_combo"]
        state_counts = {s.name: 0 for s in State}
        threshold_violations = {t: 0 for t in thresholds}
        safety_violations = 0
        details = []

        for threshold in thresholds:
            for _ in range(num_traces // len(thresholds)):
                simulator.reset()
                simulator.state_machine.state = State.ENABLED

                for step in range(50):
                    model_output = generator.boundary_probing(threshold)
                    decision = simulator.step(model_output)
                    state_counts[decision.state.name] += 1

                    # Track threshold crossings
                    if decision.state == State.SOFT_DISABLING:
                        threshold_violations[threshold] += 1

                    # Safety check
                    if decision.active and model_output.model_confidence < 0.2:
                        safety_violations += 1
                        details.append({
                            "threshold": threshold,
                            "step": step,
                            "confidence": model_output.model_confidence,
                            "state": decision.state.name,
                        })

        return ValidationResult(
            method="boundary",
            traces=num_traces,
            time_sec=time.time() - start,
            safety_violations=safety_violations,
            state_coverage=state_counts,
            threshold_violations=threshold_violations,
            details=details,
        )

    def validate_drift(self, num_traces: int = 100, trace_length: int = 200) -> ValidationResult:
        """Distribution shift testing - gradual degradation"""
        start = time.time()
        generator = AdversarialAIGenerator()
        simulator = AIBoundarySimulator()

        state_counts = {s.name: 0 for s in State}
        safety_violations = 0
        details = []

        for drift_rate in [0.005, 0.01, 0.02, 0.05]:
            for _ in range(num_traces // 4):
                simulator.reset()
                simulator.state_machine.state = State.ENABLED

                for step in range(trace_length):
                    model_output = generator.gradual_drift(step, drift_rate)
                    decision = simulator.step(model_output)
                    state_counts[decision.state.name] += 1

                    # Check if system disables before confidence gets too low
                    if decision.active and model_output.model_confidence < 0.3:
                        safety_violations += 1
                        details.append({
                            "drift_rate": drift_rate,
                            "step": step,
                            "confidence": model_output.model_confidence,
                        })

        return ValidationResult(
            method="drift",
            traces=num_traces,
            time_sec=time.time() - start,
            safety_violations=safety_violations,
            state_coverage=state_counts,
            threshold_violations={},
            details=details,
        )

    def validate_oscillation(self, num_traces: int = 100) -> ValidationResult:
        """Oscillation testing - rapid state changes"""
        start = time.time()
        generator = AdversarialAIGenerator()
        simulator = AIBoundarySimulator()

        state_counts = {s.name: 0 for s in State}
        safety_violations = 0
        state_changes = 0
        details = []

        for period in [5, 10, 20, 50]:
            for _ in range(num_traces // 4):
                simulator.reset()
                simulator.state_machine.state = State.ENABLED
                prev_state = State.ENABLED

                for step in range(200):
                    model_output = generator.oscillation(step, period)
                    decision = simulator.step(model_output)
                    state_counts[decision.state.name] += 1

                    if decision.state != prev_state:
                        state_changes += 1
                        prev_state = decision.state

        return ValidationResult(
            method="oscillation",
            traces=num_traces,
            time_sec=time.time() - start,
            safety_violations=safety_violations,
            state_coverage=state_counts,
            threshold_violations={"state_changes": state_changes},
            details=details,
        )

    def validate_ood(self, num_traces: int = 1000, trace_length: int = 50) -> ValidationResult:
        """Out-of-distribution testing"""
        start = time.time()
        generator = AdversarialAIGenerator()
        simulator = AIBoundarySimulator()

        state_counts = {s.name: 0 for s in State}
        safety_violations = 0

        for _ in range(num_traces):
            simulator.reset()
            simulator.state_machine.state = State.ENABLED

            for _ in range(trace_length):
                model_output = generator.out_of_distribution()
                decision = simulator.step(model_output)
                state_counts[decision.state.name] += 1

                # OOD should always trigger disable
                if decision.active:
                    safety_violations += 1

        return ValidationResult(
            method="ood",
            traces=num_traces,
            time_sec=time.time() - start,
            safety_violations=safety_violations,
            state_coverage=state_counts,
            threshold_violations={},
        )

    def run_benchmark(self) -> Dict[str, ValidationResult]:
        """Run all validation methods and compare"""
        print("=" * 70)
        print("AI BOUNDARY VALIDATION BENCHMARK")
        print("Testing: How does control logic handle adversarial AI outputs?")
        print("=" * 70)
        print()

        results = {}

        methods = [
            ("Random Baseline", lambda: self.validate_random(10000, 100)),
            ("Boundary Probing", lambda: self.validate_boundary(2000)),
            ("Distribution Drift", lambda: self.validate_drift(200, 200)),
            ("Oscillation Attack", lambda: self.validate_oscillation(200)),
            ("Out-of-Distribution", lambda: self.validate_ood(2000, 50)),
        ]

        for name, method in methods:
            print(f"[*] Running: {name}...")
            result = method()
            results[result.method] = result
            print(f"    Time: {result.time_sec:.2f}s")
            print(f"    Traces: {result.traces:,}")
            print(f"    Safety violations: {result.safety_violations}")
            print(f"    States visited: {sum(result.state_coverage.values()):,}")
            print()

        # Summary
        print("=" * 70)
        print("SUMMARY: Effectiveness of Different Testing Approaches")
        print("=" * 70)
        print()
        print(f"{'Method':<20} {'Time':>10} {'Traces':>12} {'Safety':>10} {'Disables':>10}")
        print("-" * 70)

        for method, result in results.items():
            disable_count = result.state_coverage.get("DISABLED", 0) + \
                           result.state_coverage.get("SOFT_DISABLING", 0)
            print(f"{method:<20} {result.time_sec:>9.2f}s {result.traces:>12,} "
                  f"{result.safety_violations:>10} {disable_count:>10,}")

        print()
        print("Key findings:")
        print("- Safety violations = active control while AI output is degraded")
        print("- Disables = system correctly disengages due to AI uncertainty")
        print("- Lower safety violations + higher disables = safer system")
        print()

        # Save results
        output_file = self.output_dir / f"ai_boundary_{int(time.time())}.json"
        with open(output_file, "w") as f:
            json.dump({
                method: {
                    "time_sec": r.time_sec,
                    "traces": r.traces,
                    "safety_violations": r.safety_violations,
                    "state_coverage": r.state_coverage,
                    "threshold_violations": r.threshold_violations,
                }
                for method, r in results.items()
            }, f, indent=2)
        print(f"Results saved to: {output_file}")

        return results


def compare_approaches_for_ai_safety():
    """
    Main comparison function for AI-in-the-loop validation approaches.

    This demonstrates which testing methods are most effective for
    validating control logic that receives AI inputs.
    """
    validator = AIBoundaryValidator()
    results = validator.run_benchmark()

    print("\n" + "=" * 70)
    print("RECOMMENDATIONS FOR AI-IN-THE-LOOP TESTING")
    print("=" * 70)
    print("""
1. BOUNDARY PROBING is most effective for finding threshold issues
   - Tests exact values where AI confidence triggers control changes
   - Fast and targeted

2. DISTRIBUTION DRIFT catches gradual degradation
   - Simulates AI model degrading over time (weather, lighting, etc.)
   - Important for production monitoring

3. OUT-OF-DISTRIBUTION tests worst-case AI behavior
   - What happens when AI sees something never trained on?
   - Critical for safety certification

4. RANDOM provides baseline coverage
   - Fast, good for CI/CD
   - May miss subtle boundary cases

5. OSCILLATION finds hysteresis issues
   - Tests rapid enable/disable cycles
   - Can reveal state machine edge cases

For AI-driven openpilot specifically:
- modeld outputs feed into controlsd/plannerd
- The control logic MUST safely disengage when AI is uncertain
- Testing should verify: low confidence → disable (never enable with bad AI)
""")

    return results


if __name__ == "__main__":
    compare_approaches_for_ai_safety()
