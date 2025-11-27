"""
Multi-Agent Reinforcement Learning (MARL) based model validation.

Uses adversarial agents to find divergences between:
1. TLA+ specification (reference model)
2. Python implementation (actual code)

The adversary tries to find input sequences that cause different behavior.
The defender tries to prove equivalence.

Results are stored in .local/ (gitignored).
"""

import os
import json
import pickle
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, asdict
from collections import defaultdict

import numpy as np

try:
    import torch
    import torch.nn as nn
    import torch.optim as optim
    TORCH_AVAILABLE = True
except ImportError:
    TORCH_AVAILABLE = False

from env_state_machine import (
    StateMachineEnv, StateMachineReference,
    BisimulationChecker, State, EventType, Events,
    create_openpilot_env
)


# Results directory (gitignored)
RESULTS_DIR = Path(__file__).parent.parent.parent / ".local" / "validation_results"


@dataclass
class ValidationResult:
    """Result of a validation run"""
    timestamp: str
    model_name: str
    method: str
    num_traces: int
    trace_length: int
    divergences_found: int
    coverage: Dict[str, int]
    duration_seconds: float
    seed: Optional[int]
    divergence_details: List[Dict]

    def to_dict(self) -> dict:
        return asdict(self)


class StateSpaceExplorer:
    """
    Systematic state space exploration using various strategies.
    """

    def __init__(self, machine_factory, seed: Optional[int] = None):
        self.machine_factory = machine_factory
        self.rng = np.random.default_rng(seed)
        self.visited_states = set()
        self.transition_counts = defaultdict(int)
        self.traces = []

    def explore_random(self, num_traces: int = 1000, trace_length: int = 100) -> Dict:
        """Random exploration of state space"""
        self.visited_states.clear()
        self.transition_counts.clear()

        for _ in range(num_traces):
            machine = self.machine_factory()
            trace = []

            for _ in range(trace_length):
                state_before = machine.state

                # Random events
                events_bitmap = self.rng.integers(0, 2, size=9)
                event_set = {EventType(i) for i, v in enumerate(events_bitmap) if v}
                events = Events(events=event_set)

                state_after = machine.step(events)

                # Track coverage
                self.visited_states.add(state_before)
                self.visited_states.add(state_after)
                self.transition_counts[(state_before, state_after)] += 1

                trace.append((state_before, frozenset(event_set), state_after))

            self.traces.append(trace)

        return {
            "visited_states": len(self.visited_states),
            "total_states": len(State),
            "coverage_pct": len(self.visited_states) / len(State) * 100,
            "unique_transitions": len(self.transition_counts),
        }

    def explore_guided(self, num_traces: int = 1000, trace_length: int = 100) -> Dict:
        """
        Coverage-guided exploration.
        Prioritizes events that lead to unexplored states.
        """
        self.visited_states.clear()
        self.transition_counts.clear()

        # Track which events lead to new states
        event_scores = defaultdict(float)

        for trace_idx in range(num_traces):
            machine = self.machine_factory()

            for step in range(trace_length):
                state_before = machine.state

                # Select events based on scores (exploration vs exploitation)
                if self.rng.random() < 0.3:  # Exploration
                    events_bitmap = self.rng.integers(0, 2, size=9)
                else:  # Exploitation - prefer high-scoring events
                    events_bitmap = np.zeros(9, dtype=int)
                    for i in range(9):
                        score = event_scores[(state_before, EventType(i))]
                        if self.rng.random() < (0.5 + score * 0.5):
                            events_bitmap[i] = 1

                event_set = {EventType(i) for i, v in enumerate(events_bitmap) if v}
                events = Events(events=event_set)

                state_after = machine.step(events)

                # Update scores - reward transitions to new states
                is_new_transition = (state_before, state_after) not in self.transition_counts
                for event in event_set:
                    if is_new_transition:
                        event_scores[(state_before, event)] += 0.1

                self.visited_states.add(state_before)
                self.visited_states.add(state_after)
                self.transition_counts[(state_before, state_after)] += 1

        return {
            "visited_states": len(self.visited_states),
            "total_states": len(State),
            "coverage_pct": len(self.visited_states) / len(State) * 100,
            "unique_transitions": len(self.transition_counts),
        }


class AdversarialValidator:
    """
    Adversarial validation using learned policies.

    The adversary learns to generate input sequences that maximize
    the chance of finding divergences between two implementations.
    """

    def __init__(self, reference_factory, implementation_factory,
                 seed: Optional[int] = None):
        self.reference_factory = reference_factory
        self.implementation_factory = implementation_factory
        self.rng = np.random.default_rng(seed)
        self.divergences = []

    def validate_random(self, num_traces: int = 10000, trace_length: int = 200) -> ValidationResult:
        """Validate using random input sequences"""
        start_time = datetime.now()
        self.divergences = []
        coverage = defaultdict(int)

        for trace_idx in range(num_traces):
            ref = self.reference_factory()
            impl = self.implementation_factory()

            if impl is None:
                # Can't import real implementation, skip
                break

            for step in range(trace_length):
                # Random events
                events_bitmap = self.rng.integers(0, 2, size=9)
                event_set = {EventType(i) for i, v in enumerate(events_bitmap) if v}
                events = Events(events=event_set)

                ref_state = ref.step(events)
                impl_state = impl.step(events)

                coverage[ref_state.name] += 1

                if ref_state != impl_state:
                    self.divergences.append({
                        "trace_idx": trace_idx,
                        "step": step,
                        "events": [e.name for e in event_set],
                        "ref_state": ref_state.name,
                        "impl_state": impl_state.name,
                    })
                    break

        duration = (datetime.now() - start_time).total_seconds()

        return ValidationResult(
            timestamp=datetime.now().isoformat(),
            model_name="StateMachine",
            method="random",
            num_traces=num_traces,
            trace_length=trace_length,
            divergences_found=len(self.divergences),
            coverage=dict(coverage),
            duration_seconds=duration,
            seed=None,
            divergence_details=self.divergences[:100],  # Limit stored divergences
        )

    def validate_coverage_guided(self, num_traces: int = 10000,
                                  trace_length: int = 200) -> ValidationResult:
        """
        Coverage-guided validation.
        Prioritizes inputs that increase state/transition coverage.
        """
        start_time = datetime.now()
        self.divergences = []
        coverage = defaultdict(int)
        transition_coverage = set()

        # Track which event combinations lead to new coverage
        event_utility = defaultdict(float)

        for trace_idx in range(num_traces):
            ref = self.reference_factory()
            impl = self.implementation_factory()

            if impl is None:
                break

            prev_state = State.DISABLED

            for step in range(trace_length):
                # Select events - mix of random and utility-guided
                if self.rng.random() < 0.2:
                    events_bitmap = self.rng.integers(0, 2, size=9)
                else:
                    events_bitmap = np.zeros(9, dtype=int)
                    for i in range(9):
                        utility = event_utility[(prev_state, i)]
                        prob = 0.3 + 0.7 * min(utility, 1.0)
                        if self.rng.random() < prob:
                            events_bitmap[i] = 1

                event_set = {EventType(i) for i, v in enumerate(events_bitmap) if v}
                events = Events(events=event_set)

                ref_state = ref.step(events)
                impl_state = impl.step(events)

                # Update coverage
                coverage[ref_state.name] += 1
                transition = (prev_state, ref_state)
                is_new = transition not in transition_coverage
                transition_coverage.add(transition)

                # Update event utility
                if is_new:
                    for i, v in enumerate(events_bitmap):
                        if v:
                            event_utility[(prev_state, i)] += 0.1

                # Check for divergence
                if ref_state != impl_state:
                    self.divergences.append({
                        "trace_idx": trace_idx,
                        "step": step,
                        "events": [e.name for e in event_set],
                        "ref_state": ref_state.name,
                        "impl_state": impl_state.name,
                    })
                    break

                prev_state = ref_state

        duration = (datetime.now() - start_time).total_seconds()

        return ValidationResult(
            timestamp=datetime.now().isoformat(),
            model_name="StateMachine",
            method="coverage_guided",
            num_traces=num_traces,
            trace_length=trace_length,
            divergences_found=len(self.divergences),
            coverage=dict(coverage),
            duration_seconds=duration,
            seed=None,
            divergence_details=self.divergences[:100],
        )


if TORCH_AVAILABLE:
    class AdversarialPolicyNetwork(nn.Module):
        """
        Neural network policy for adversarial input generation.
        Learns to generate event sequences that find divergences.
        """

        def __init__(self, state_dim: int = 5, action_dim: int = 9, hidden_dim: int = 64):
            super().__init__()
            self.network = nn.Sequential(
                nn.Linear(state_dim + 1, hidden_dim),  # state + timer
                nn.ReLU(),
                nn.Linear(hidden_dim, hidden_dim),
                nn.ReLU(),
                nn.Linear(hidden_dim, action_dim),
                nn.Sigmoid(),  # Output probabilities for each event
            )

        def forward(self, state: torch.Tensor, timer: torch.Tensor) -> torch.Tensor:
            x = torch.cat([state, timer], dim=-1)
            return self.network(x)

        def sample_action(self, state: int, timer: int) -> np.ndarray:
            """Sample events from learned distribution"""
            with torch.no_grad():
                state_onehot = torch.zeros(5)
                state_onehot[state] = 1
                timer_norm = torch.tensor([timer / 300.0])
                probs = self.forward(state_onehot.unsqueeze(0), timer_norm.unsqueeze(0))
                events = (torch.rand_like(probs) < probs).squeeze().numpy().astype(int)
            return events


    class RLAdversarialValidator(AdversarialValidator):
        """
        RL-based adversarial validator.
        Uses policy gradient to learn adversarial input generation.
        """

        def __init__(self, reference_factory, implementation_factory,
                     seed: Optional[int] = None, lr: float = 1e-3):
            super().__init__(reference_factory, implementation_factory, seed)
            self.policy = AdversarialPolicyNetwork()
            self.optimizer = optim.Adam(self.policy.parameters(), lr=lr)

        def train_adversary(self, num_episodes: int = 1000, trace_length: int = 100):
            """Train adversarial policy using REINFORCE

            If implementation not available, trains for state space coverage instead.
            """
            impl_available = self.implementation_factory() is not None

            for episode in range(num_episodes):
                ref = self.reference_factory()

                if impl_available:
                    impl = self.implementation_factory()
                else:
                    impl = None  # Will train for coverage instead

                log_probs = []
                rewards = []
                found_divergence = False
                prev_state = ref.state
                visited_states = set()

                for step in range(trace_length):
                    # Get action from policy
                    state_onehot = torch.zeros(5)
                    state_onehot[ref.state] = 1
                    timer_norm = torch.tensor([ref.soft_disable_timer / 300.0])

                    probs = self.policy(state_onehot.unsqueeze(0), timer_norm.unsqueeze(0))
                    events_tensor = torch.bernoulli(probs)

                    # Calculate log probability
                    log_prob = (events_tensor * torch.log(probs + 1e-8) +
                                (1 - events_tensor) * torch.log(1 - probs + 1e-8)).sum()
                    log_probs.append(log_prob)

                    # Execute action
                    events_bitmap = events_tensor.squeeze().detach().numpy().astype(int)
                    event_set = {EventType(i) for i, v in enumerate(events_bitmap) if v}
                    events = Events(events=event_set)

                    ref_state = ref.step(events)

                    if impl_available:
                        impl_state = impl.step(events)
                        # Reward: +10 for finding divergence
                        if ref_state != impl_state:
                            rewards.append(10.0)
                            found_divergence = True
                            self.divergences.append({
                                "episode": episode,
                                "step": step,
                                "events": [e.name for e in event_set],
                                "ref_state": ref_state.name,
                                "impl_state": impl_state.name,
                            })
                            break
                        else:
                            rewards.append(0.01)
                    else:
                        # No impl available - reward for coverage/exploration
                        reward = 0.01
                        if ref_state != prev_state:
                            reward += 0.5  # Reward state transitions
                        if ref_state not in visited_states:
                            reward += 1.0  # Reward visiting new states
                            visited_states.add(ref_state)
                        rewards.append(reward)

                    prev_state = ref_state

                if not found_divergence:
                    rewards.append(0.0)

                # Policy gradient update
                returns = []
                G = 0
                for r in reversed(rewards):
                    G = r + 0.99 * G
                    returns.insert(0, G)

                returns = torch.tensor(returns)
                returns = (returns - returns.mean()) / (returns.std() + 1e-8)

                loss = 0
                for log_prob, R in zip(log_probs, returns):
                    loss -= log_prob * R

                self.optimizer.zero_grad()
                loss.backward()
                self.optimizer.step()

                if episode % 100 == 0:
                    mode = "adversarial" if impl_available else "coverage"
                    print(f"Episode {episode}, Mode: {mode}, Divergences: {len(self.divergences)}")

        def validate_learned(self, num_traces: int = 1000,
                             trace_length: int = 100) -> ValidationResult:
            """Validate using learned adversarial policy"""
            start_time = datetime.now()
            test_divergences = []
            coverage = defaultdict(int)

            for trace_idx in range(num_traces):
                ref = self.reference_factory()
                impl = self.implementation_factory()

                if impl is None:
                    break

                for step in range(trace_length):
                    events_bitmap = self.policy.sample_action(ref.state, ref.soft_disable_timer)
                    event_set = {EventType(i) for i, v in enumerate(events_bitmap) if v}
                    events = Events(events=event_set)

                    ref_state = ref.step(events)
                    impl_state = impl.step(events)

                    coverage[ref_state.name] += 1

                    if ref_state != impl_state:
                        test_divergences.append({
                            "trace_idx": trace_idx,
                            "step": step,
                            "events": [e.name for e in event_set],
                            "ref_state": ref_state.name,
                            "impl_state": impl_state.name,
                        })
                        break

            duration = (datetime.now() - start_time).total_seconds()

            return ValidationResult(
                timestamp=datetime.now().isoformat(),
                model_name="StateMachine",
                method="rl_adversarial",
                num_traces=num_traces,
                trace_length=trace_length,
                divergences_found=len(test_divergences),
                coverage=dict(coverage),
                duration_seconds=duration,
                seed=None,
                divergence_details=test_divergences[:100],
            )


def save_results(result: ValidationResult, name: str = "validation"):
    """Save validation results to .local/ directory"""
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    filename = RESULTS_DIR / f"{name}_{timestamp}.json"

    with open(filename, "w") as f:
        json.dump(result.to_dict(), f, indent=2)

    print(f"Results saved to: {filename}")
    return filename


def run_full_validation():
    """Run complete validation suite"""
    print("=" * 60)
    print("MARL-based Model Validation")
    print("=" * 60)

    # Create factories
    def ref_factory():
        return StateMachineReference()

    impl_factory = create_openpilot_env

    # 1. Random validation
    print("\n[1/3] Random Validation...")
    validator = AdversarialValidator(ref_factory, impl_factory)
    result_random = validator.validate_random(num_traces=10000, trace_length=200)
    print(f"  Divergences: {result_random.divergences_found}")
    print(f"  Coverage: {result_random.coverage}")
    save_results(result_random, "random")

    # 2. Coverage-guided validation
    print("\n[2/3] Coverage-Guided Validation...")
    result_guided = validator.validate_coverage_guided(num_traces=10000, trace_length=200)
    print(f"  Divergences: {result_guided.divergences_found}")
    print(f"  Coverage: {result_guided.coverage}")
    save_results(result_guided, "coverage_guided")

    # 3. RL-based validation (if PyTorch available)
    if TORCH_AVAILABLE:
        print("\n[3/3] RL Adversarial Validation...")
        rl_validator = RLAdversarialValidator(ref_factory, impl_factory)
        print("  Training adversarial policy...")
        rl_validator.train_adversary(num_episodes=500, trace_length=100)
        result_rl = rl_validator.validate_learned(num_traces=1000, trace_length=100)
        print(f"  Divergences: {result_rl.divergences_found}")
        save_results(result_rl, "rl_adversarial")
    else:
        print("\n[3/3] Skipping RL validation (PyTorch not available)")

    print("\n" + "=" * 60)
    print("Validation complete. Results in .local/validation_results/")
    print("=" * 60)


if __name__ == "__main__":
    run_full_validation()
