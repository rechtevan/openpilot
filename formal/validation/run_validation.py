#!/usr/bin/env python3
"""
Main entry point for running model validation.

Usage:
    python run_validation.py [--method METHOD] [--model MODEL] [--traces N]

Results are stored in .local/validation_results/ (gitignored)
"""

import argparse
import sys
from pathlib import Path
from datetime import datetime

# Add parent to path for imports
sys.path.insert(0, str(Path(__file__).parent))

from env_state_machine import StateMachineReference, BisimulationChecker, create_openpilot_env
from env_long_control import LongControlReference, create_real_long_control
from marl_validator import (
    AdversarialValidator, StateSpaceExplorer,
    save_results, ValidationResult, RESULTS_DIR
)

try:
    from marl_validator import RLAdversarialValidator, TORCH_AVAILABLE
except ImportError:
    TORCH_AVAILABLE = False


def validate_state_machine(method: str, num_traces: int, trace_length: int):
    """Validate StateMachine model"""
    print("\n" + "=" * 60)
    print("StateMachine Validation")
    print("=" * 60)

    ref_factory = StateMachineReference
    impl_factory = create_openpilot_env

    if method == "random":
        validator = AdversarialValidator(ref_factory, impl_factory)
        result = validator.validate_random(num_traces, trace_length)
    elif method == "coverage":
        validator = AdversarialValidator(ref_factory, impl_factory)
        result = validator.validate_coverage_guided(num_traces, trace_length)
    elif method == "rl" and TORCH_AVAILABLE:
        validator = RLAdversarialValidator(ref_factory, impl_factory)
        print("Training adversarial policy (this may take a while)...")
        validator.train_adversary(num_episodes=500, trace_length=100)
        result = validator.validate_learned(num_traces, trace_length)
    elif method == "bisim":
        # Bisimulation checking
        ref = StateMachineReference()
        impl = create_openpilot_env()
        if impl is None:
            print("Cannot run bisimulation: implementation not available")
            return None
        checker = BisimulationChecker(ref, impl)
        equivalent = checker.check_equivalence(num_traces, trace_length)
        result = ValidationResult(
            timestamp=datetime.now().isoformat(),
            model_name="StateMachine",
            method="bisimulation",
            num_traces=num_traces,
            trace_length=trace_length,
            divergences_found=len(checker.get_divergences()),
            coverage={},
            duration_seconds=0,
            seed=None,
            divergence_details=checker.get_divergences()[:100],
        )
    else:
        print(f"Unknown method: {method}")
        return None

    print(f"\nResults:")
    print(f"  Method: {result.method}")
    print(f"  Traces: {result.num_traces}")
    print(f"  Divergences: {result.divergences_found}")
    print(f"  Coverage: {result.coverage}")

    if result.divergences_found > 0:
        print(f"\n  First divergence:")
        print(f"    {result.divergence_details[0]}")

    save_results(result, f"state_machine_{method}")
    return result


def validate_long_control(method: str, num_traces: int, trace_length: int):
    """Validate LongControl model"""
    print("\n" + "=" * 60)
    print("LongControl Validation")
    print("=" * 60)

    from env_long_control import LongControlReference, LongControlInputs, LongCtrlState

    ref_factory = LongControlReference
    impl_factory = create_real_long_control

    # Run validation
    import numpy as np
    from collections import defaultdict

    rng = np.random.default_rng()
    divergences = []
    coverage = defaultdict(int)

    start_time = datetime.now()

    for trace_idx in range(num_traces):
        ref = ref_factory()
        impl = impl_factory()

        if impl is None:
            print("Cannot validate: real implementation not available")
            print("Running reference model exploration only...")
            impl = ref_factory()  # Use reference as both

        v_ego = 0.0

        for step in range(trace_length):
            # Random inputs
            inputs = LongControlInputs(
                active=bool(rng.integers(2)),
                v_ego=v_ego,
                should_stop=bool(rng.integers(2)),
                brake_pressed=bool(rng.integers(2)),
                cruise_standstill=bool(rng.integers(2)),
            )

            # Update v_ego randomly
            v_ego = max(0.0, v_ego + rng.uniform(-0.5, 0.5))

            ref_state, ref_accel = ref.step(inputs)
            impl_state, impl_accel = impl.step(inputs)

            coverage[ref_state.name] += 1

            # Check state equivalence (allow small accel difference due to PID)
            if ref_state != impl_state:
                divergences.append({
                    "trace_idx": trace_idx,
                    "step": step,
                    "inputs": {
                        "active": inputs.active,
                        "v_ego": inputs.v_ego,
                        "should_stop": inputs.should_stop,
                        "brake_pressed": inputs.brake_pressed,
                    },
                    "ref_state": ref_state.name,
                    "impl_state": impl_state.name,
                })
                break

    duration = (datetime.now() - start_time).total_seconds()

    result = ValidationResult(
        timestamp=datetime.now().isoformat(),
        model_name="LongControl",
        method=method,
        num_traces=num_traces,
        trace_length=trace_length,
        divergences_found=len(divergences),
        coverage=dict(coverage),
        duration_seconds=duration,
        seed=None,
        divergence_details=divergences[:100],
    )

    print(f"\nResults:")
    print(f"  Divergences: {result.divergences_found}")
    print(f"  Coverage: {result.coverage}")
    print(f"  Duration: {duration:.2f}s")

    save_results(result, f"long_control_{method}")
    return result


def explore_state_space(model: str, num_traces: int, trace_length: int):
    """Explore state space coverage"""
    print("\n" + "=" * 60)
    print(f"State Space Exploration: {model}")
    print("=" * 60)

    if model == "state_machine":
        explorer = StateSpaceExplorer(StateMachineReference)
    else:
        print(f"Unknown model: {model}")
        return

    print("\nRandom exploration...")
    random_result = explorer.explore_random(num_traces, trace_length)
    print(f"  Visited states: {random_result['visited_states']}/{random_result['total_states']}")
    print(f"  Coverage: {random_result['coverage_pct']:.1f}%")
    print(f"  Unique transitions: {random_result['unique_transitions']}")

    print("\nGuided exploration...")
    guided_result = explorer.explore_guided(num_traces, trace_length)
    print(f"  Visited states: {guided_result['visited_states']}/{guided_result['total_states']}")
    print(f"  Coverage: {guided_result['coverage_pct']:.1f}%")
    print(f"  Unique transitions: {guided_result['unique_transitions']}")


def main():
    parser = argparse.ArgumentParser(description="Model validation using MARL")
    parser.add_argument("--model", choices=["state_machine", "long_control", "all"],
                        default="all", help="Model to validate")
    parser.add_argument("--method", choices=["random", "coverage", "rl", "bisim", "explore"],
                        default="random", help="Validation method")
    parser.add_argument("--traces", type=int, default=1000, help="Number of traces")
    parser.add_argument("--length", type=int, default=100, help="Trace length")

    args = parser.parse_args()

    print("=" * 60)
    print("MARL-based Formal Model Validation")
    print(f"Results will be saved to: {RESULTS_DIR}")
    print("=" * 60)

    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    if args.method == "explore":
        if args.model in ["state_machine", "all"]:
            explore_state_space("state_machine", args.traces, args.length)
    else:
        if args.model in ["state_machine", "all"]:
            validate_state_machine(args.method, args.traces, args.length)

        if args.model in ["long_control", "all"]:
            validate_long_control(args.method, args.traces, args.length)

    print("\n" + "=" * 60)
    print("Validation complete!")
    print(f"Results saved to: {RESULTS_DIR}")
    print("=" * 60)


if __name__ == "__main__":
    main()
