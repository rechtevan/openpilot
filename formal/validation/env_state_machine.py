"""
Gym environments for openpilot state machines.

These environments wrap both the actual Python implementation and a reference
model (from TLA+ specs) to enable:
1. RL-based adversarial testing
2. Bisimulation equivalence checking
3. Property-based fuzzing

Results/artifacts go to .local/ (gitignored), source code is committed.
"""

import gymnasium as gym
import numpy as np
from gymnasium import spaces
from enum import IntEnum
from typing import Optional, Tuple, Dict, Any
from dataclasses import dataclass


class State(IntEnum):
    """Engagement states matching selfdrive/selfdrived/state.py"""
    DISABLED = 0
    PRE_ENABLED = 1
    ENABLED = 2
    SOFT_DISABLING = 3
    OVERRIDING = 4


class EventType(IntEnum):
    """Event types matching selfdrive/selfdrived/events.py"""
    NONE = 0
    ENABLE = 1
    PRE_ENABLE = 2
    OVERRIDE_LATERAL = 3
    OVERRIDE_LONGITUDINAL = 4
    NO_ENTRY = 5
    USER_DISABLE = 6
    SOFT_DISABLE = 7
    IMMEDIATE_DISABLE = 8


@dataclass
class Events:
    """Event container mimicking the real Events class"""
    events: set

    def contains(self, event_type: EventType) -> bool:
        return event_type in self.events


class StateMachineReference:
    """
    Reference implementation matching TLA+ StateMachine.tla spec.
    Used as ground truth for comparison.
    """
    SOFT_DISABLE_TIME = 3  # seconds
    DT_CTRL = 0.01  # 100 Hz

    def __init__(self):
        self.state = State.DISABLED
        self.soft_disable_timer = 0

    def reset(self):
        self.state = State.DISABLED
        self.soft_disable_timer = 0

    def step(self, events: Events) -> State:
        """Execute one step of the state machine"""
        # Decrement timer
        self.soft_disable_timer = max(0, self.soft_disable_timer - 1)

        if self.state != State.DISABLED:
            # Priority: USER_DISABLE and IMMEDIATE_DISABLE
            if events.contains(EventType.USER_DISABLE):
                self.state = State.DISABLED
            elif events.contains(EventType.IMMEDIATE_DISABLE):
                self.state = State.DISABLED
            else:
                if self.state == State.ENABLED:
                    if events.contains(EventType.SOFT_DISABLE):
                        self.state = State.SOFT_DISABLING
                        self.soft_disable_timer = int(self.SOFT_DISABLE_TIME / self.DT_CTRL)
                    elif events.contains(EventType.OVERRIDE_LATERAL) or events.contains(EventType.OVERRIDE_LONGITUDINAL):
                        self.state = State.OVERRIDING

                elif self.state == State.SOFT_DISABLING:
                    if not events.contains(EventType.SOFT_DISABLE):
                        self.state = State.ENABLED
                    elif self.soft_disable_timer <= 0:
                        self.state = State.DISABLED

                elif self.state == State.PRE_ENABLED:
                    if not events.contains(EventType.PRE_ENABLE):
                        self.state = State.ENABLED

                elif self.state == State.OVERRIDING:
                    if events.contains(EventType.SOFT_DISABLE):
                        self.state = State.SOFT_DISABLING
                        self.soft_disable_timer = int(self.SOFT_DISABLE_TIME / self.DT_CTRL)
                    elif not (events.contains(EventType.OVERRIDE_LATERAL) or events.contains(EventType.OVERRIDE_LONGITUDINAL)):
                        self.state = State.ENABLED

        else:  # DISABLED
            if events.contains(EventType.ENABLE):
                if not events.contains(EventType.NO_ENTRY):
                    if events.contains(EventType.PRE_ENABLE):
                        self.state = State.PRE_ENABLED
                    elif events.contains(EventType.OVERRIDE_LATERAL) or events.contains(EventType.OVERRIDE_LONGITUDINAL):
                        self.state = State.OVERRIDING
                    else:
                        self.state = State.ENABLED

        return self.state


class StateMachineEnv(gym.Env):
    """
    Gym environment for the openpilot state machine.

    Observation: [state, soft_disable_timer]
    Action: bitmap of events to trigger

    This can be used with RL agents to find adversarial event sequences
    that expose bugs or verify safety properties.
    """

    metadata = {"render_modes": ["human", "ansi"]}

    def __init__(self, render_mode: Optional[str] = None, use_reference: bool = True):
        super().__init__()

        self.render_mode = render_mode
        self.use_reference = use_reference

        # Observation: state (5 values) + timer (0-300)
        self.observation_space = spaces.Dict({
            "state": spaces.Discrete(5),
            "timer": spaces.Box(low=0, high=300, shape=(1,), dtype=np.int32),
        })

        # Action: bitmap of 9 event types (each can be on/off)
        self.action_space = spaces.MultiBinary(9)

        self.machine = StateMachineReference()
        self.step_count = 0
        self.max_steps = 1000

    def _get_obs(self) -> Dict[str, Any]:
        return {
            "state": int(self.machine.state),
            "timer": np.array([self.machine.soft_disable_timer], dtype=np.int32),
        }

    def _get_info(self) -> Dict[str, Any]:
        return {
            "step_count": self.step_count,
            "state_name": self.machine.state.name,
        }

    def reset(self, seed: Optional[int] = None, options: Optional[dict] = None) -> Tuple[Dict, Dict]:
        super().reset(seed=seed)
        self.machine.reset()
        self.step_count = 0
        return self._get_obs(), self._get_info()

    def step(self, action: np.ndarray) -> Tuple[Dict, float, bool, bool, Dict]:
        """
        Execute one step.

        Args:
            action: Binary array of events to trigger

        Returns:
            observation, reward, terminated, truncated, info
        """
        # Convert action to events
        event_set = set()
        for i, triggered in enumerate(action):
            if triggered:
                event_set.add(EventType(i))

        events = Events(events=event_set)

        # Store previous state for reward calculation
        prev_state = self.machine.state

        # Execute step
        new_state = self.machine.step(events)
        self.step_count += 1

        # Calculate reward (can be customized for different objectives)
        reward = self._calculate_reward(prev_state, new_state, events)

        # Check termination
        terminated = False
        truncated = self.step_count >= self.max_steps

        return self._get_obs(), reward, terminated, truncated, self._get_info()

    def _calculate_reward(self, prev_state: State, new_state: State, events: Events) -> float:
        """
        Calculate reward for RL agent.

        Different reward schemes for different objectives:
        - Coverage: reward for visiting new states
        - Adversarial: reward for finding safety violations
        - Conformance: reward for matching reference behavior
        """
        reward = 0.0

        # Reward state transitions (encourages exploration)
        if new_state != prev_state:
            reward += 1.0

        # Penalize invalid states (safety check)
        # Example: SOFT_DISABLING should have timer > 0 on entry
        if new_state == State.SOFT_DISABLING and self.machine.soft_disable_timer == 0:
            reward -= 10.0  # Safety violation!

        return reward

    def render(self) -> Optional[str]:
        if self.render_mode == "ansi":
            return f"State: {self.machine.state.name}, Timer: {self.machine.soft_disable_timer}"
        return None


class BisimulationChecker:
    """
    Check bisimulation equivalence between two state machines.

    Two systems are bisimilar if they have the same observable behavior
    for all possible input sequences.
    """

    def __init__(self, machine_a, machine_b):
        self.machine_a = machine_a
        self.machine_b = machine_b
        self.divergences = []

    def check_equivalence(self, num_traces: int = 1000, trace_length: int = 100,
                          seed: Optional[int] = None) -> bool:
        """
        Check equivalence by random testing.

        Args:
            num_traces: Number of random traces to test
            trace_length: Length of each trace
            seed: Random seed for reproducibility

        Returns:
            True if no divergences found
        """
        rng = np.random.default_rng(seed)
        self.divergences = []

        for trace_idx in range(num_traces):
            self.machine_a.reset()
            self.machine_b.reset()

            trace = []
            for step in range(trace_length):
                # Generate random events
                events_bitmap = rng.integers(0, 2, size=9)
                event_set = {EventType(i) for i, v in enumerate(events_bitmap) if v}
                events = Events(events=event_set)

                trace.append(event_set)

                # Step both machines
                state_a = self.machine_a.step(events)
                state_b = self.machine_b.step(events)

                # Check equivalence
                if state_a != state_b:
                    self.divergences.append({
                        "trace_idx": trace_idx,
                        "step": step,
                        "events": event_set,
                        "state_a": state_a,
                        "state_b": state_b,
                        "trace": trace.copy(),
                    })
                    break

        return len(self.divergences) == 0

    def get_divergences(self) -> list:
        return self.divergences


_OPENPILOT_IMPORT_WARNED = False

# Factory function to create environment from actual openpilot code
def create_openpilot_env():
    """
    Create environment using actual openpilot state machine.

    Uses the standalone real implementation that matches the openpilot code
    exactly, without requiring openpilot build dependencies.
    """
    from real_state_machine import RealStateMachine, Events as RealEvents, ET

    class RealStateMachineWrapper:
        """Wrapper to make real StateMachine compatible with our interface"""
        def __init__(self):
            self.machine = RealStateMachine()

        @property
        def state(self):
            return State(self.machine.state)

        @property
        def soft_disable_timer(self):
            return self.machine.soft_disable_timer

        def reset(self):
            self.machine = RealStateMachine()

        def step(self, events: Events) -> State:
            # Convert our Events to real Events
            real_event_set = set()
            event_mapping = {
                EventType.ENABLE: ET.ENABLE,
                EventType.PRE_ENABLE: ET.PRE_ENABLE,
                EventType.OVERRIDE_LATERAL: ET.OVERRIDE_LATERAL,
                EventType.OVERRIDE_LONGITUDINAL: ET.OVERRIDE_LONGITUDINAL,
                EventType.NO_ENTRY: ET.NO_ENTRY,
                EventType.USER_DISABLE: ET.USER_DISABLE,
                EventType.SOFT_DISABLE: ET.SOFT_DISABLE,
                EventType.IMMEDIATE_DISABLE: ET.IMMEDIATE_DISABLE,
            }
            for event in events.events:
                if event in event_mapping:
                    real_event_set.add(event_mapping[event])

            real_events = RealEvents(events=real_event_set)
            self.machine.update(real_events)
            return State(self.machine.state)

    return RealStateMachineWrapper()


if __name__ == "__main__":
    # Quick test
    env = StateMachineEnv(render_mode="ansi")
    obs, info = env.reset(seed=42)
    print(f"Initial: {info['state_name']}")

    # Test some transitions
    for _ in range(10):
        action = env.action_space.sample()
        obs, reward, term, trunc, info = env.step(action)
        print(f"Action: {action} -> {info['state_name']}, Reward: {reward:.2f}")
