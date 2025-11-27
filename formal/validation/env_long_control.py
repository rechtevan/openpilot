"""
Gym environment for LongControl state machine validation.

Wraps both reference (TLA+ spec) and actual implementation.
"""

import gymnasium as gym
import numpy as np
from gymnasium import spaces
from enum import IntEnum
from typing import Optional, Dict, Any, Tuple
from dataclasses import dataclass


class LongCtrlState(IntEnum):
    """States matching selfdrive/controls/lib/longcontrol.py"""
    OFF = 0
    STOPPING = 1
    STARTING = 2
    PID = 3


@dataclass
class LongControlInputs:
    """Input signals for longitudinal control"""
    active: bool
    v_ego: float
    should_stop: bool
    brake_pressed: bool
    cruise_standstill: bool
    starting_state: bool = True  # CP.startingState
    v_ego_starting: float = 0.5  # CP.vEgoStarting


class LongControlReference:
    """
    Reference implementation matching TLA+ LongControl.tla spec.
    """
    ACCEL_MIN = -3.5
    ACCEL_MAX = 2.0
    STOP_ACCEL = -2.0
    START_ACCEL = 1.2
    STOPPING_DECEL_RATE = 0.8
    DT_CTRL = 0.01

    def __init__(self):
        self.state = LongCtrlState.OFF
        self.output_accel = 0.0
        self.last_output_accel = 0.0

    def reset(self):
        self.state = LongCtrlState.OFF
        self.output_accel = 0.0
        self.last_output_accel = 0.0

    def _clip(self, val: float) -> float:
        return np.clip(val, self.ACCEL_MIN, self.ACCEL_MAX)

    def step(self, inputs: LongControlInputs) -> Tuple[LongCtrlState, float]:
        """Execute one step matching long_control_state_trans"""
        stopping_condition = inputs.should_stop
        starting_condition = (not inputs.should_stop and
                              not inputs.cruise_standstill and
                              not inputs.brake_pressed)
        started_condition = inputs.v_ego > inputs.v_ego_starting

        if not inputs.active:
            self.state = LongCtrlState.OFF
            self.output_accel = 0.0
            self.last_output_accel = 0.0

        else:
            if self.state == LongCtrlState.OFF:
                if not starting_condition:
                    self.state = LongCtrlState.STOPPING
                    self.output_accel = 0.0
                else:
                    if inputs.starting_state:
                        self.state = LongCtrlState.STARTING
                        self.output_accel = self._clip(self.START_ACCEL)
                    else:
                        self.state = LongCtrlState.PID
                        self.output_accel = 0.0  # PID would compute this

            elif self.state == LongCtrlState.STOPPING:
                if starting_condition:
                    if inputs.starting_state:
                        self.state = LongCtrlState.STARTING
                        self.output_accel = self._clip(self.START_ACCEL)
                    else:
                        self.state = LongCtrlState.PID
                        self.output_accel = 0.0
                else:
                    # Ramp down deceleration
                    if self.last_output_accel > self.STOP_ACCEL:
                        self.output_accel = self._clip(
                            min(self.last_output_accel, 0.0) -
                            self.STOPPING_DECEL_RATE * self.DT_CTRL
                        )
                    else:
                        self.output_accel = self.last_output_accel

            elif self.state == LongCtrlState.STARTING:
                if stopping_condition:
                    self.state = LongCtrlState.STOPPING
                    if self.last_output_accel > self.STOP_ACCEL:
                        self.output_accel = self._clip(
                            min(self.last_output_accel, 0.0) -
                            self.STOPPING_DECEL_RATE * self.DT_CTRL
                        )
                elif started_condition:
                    self.state = LongCtrlState.PID
                    self.output_accel = 0.0  # PID would compute
                else:
                    self.output_accel = self._clip(self.START_ACCEL)

            elif self.state == LongCtrlState.PID:
                if stopping_condition:
                    self.state = LongCtrlState.STOPPING
                    if self.last_output_accel > self.STOP_ACCEL:
                        self.output_accel = self._clip(
                            min(self.last_output_accel, 0.0) -
                            self.STOPPING_DECEL_RATE * self.DT_CTRL
                        )
                else:
                    # PID control - simplified for validation
                    self.output_accel = self._clip(self.output_accel)

        self.last_output_accel = self._clip(self.output_accel)
        return self.state, self.output_accel


class LongControlEnv(gym.Env):
    """
    Gym environment for longitudinal control validation.

    Observation: [state, output_accel, v_ego]
    Action: [active, should_stop, brake_pressed, cruise_standstill, v_ego_delta]
    """

    def __init__(self, render_mode: Optional[str] = None):
        super().__init__()
        self.render_mode = render_mode

        # Observation space
        self.observation_space = spaces.Dict({
            "state": spaces.Discrete(4),
            "output_accel": spaces.Box(low=-4.0, high=3.0, shape=(1,), dtype=np.float32),
            "v_ego": spaces.Box(low=0.0, high=50.0, shape=(1,), dtype=np.float32),
        })

        # Action space: discrete choices for each input
        self.action_space = spaces.Dict({
            "active": spaces.Discrete(2),
            "should_stop": spaces.Discrete(2),
            "brake_pressed": spaces.Discrete(2),
            "cruise_standstill": spaces.Discrete(2),
            "v_ego_change": spaces.Discrete(3),  # decrease, same, increase
        })

        self.control = LongControlReference()
        self.v_ego = 0.0
        self.step_count = 0

    def _get_obs(self) -> Dict:
        return {
            "state": int(self.control.state),
            "output_accel": np.array([self.control.output_accel], dtype=np.float32),
            "v_ego": np.array([self.v_ego], dtype=np.float32),
        }

    def reset(self, seed: Optional[int] = None, options: Optional[dict] = None):
        super().reset(seed=seed)
        self.control.reset()
        self.v_ego = 0.0
        self.step_count = 0
        return self._get_obs(), {}

    def step(self, action: Dict):
        # Update v_ego based on action
        v_change = action["v_ego_change"] - 1  # -1, 0, or 1
        self.v_ego = max(0.0, self.v_ego + v_change * 0.5)

        # Create inputs
        inputs = LongControlInputs(
            active=bool(action["active"]),
            v_ego=self.v_ego,
            should_stop=bool(action["should_stop"]),
            brake_pressed=bool(action["brake_pressed"]),
            cruise_standstill=bool(action["cruise_standstill"]),
        )

        # Step the control
        prev_state = self.control.state
        new_state, output = self.control.step(inputs)

        self.step_count += 1

        # Reward for state coverage
        reward = 0.1 if new_state != prev_state else 0.0

        # Safety check: in STOPPING state, should never accelerate
        if new_state == LongCtrlState.STOPPING and output > 0.01:
            reward -= 10.0  # Safety violation

        terminated = False
        truncated = self.step_count >= 1000

        return self._get_obs(), reward, terminated, truncated, {"state_name": new_state.name}


_IMPORT_WARNED = False

def create_real_long_control():
    """Create wrapper for real LongControl implementation"""
    global _IMPORT_WARNED
    try:
        from openpilot.selfdrive.controls.lib.longcontrol import LongControl, long_control_state_trans
        from cereal import car

        class RealLongControlWrapper:
            def __init__(self):
                # Create a minimal CarParams mock
                class MockCP:
                    startingState = True
                    vEgoStarting = 0.5
                    stopAccel = -2.0
                    startAccel = 1.2
                    stoppingDecelRate = 0.8
                    longitudinalTuning = type('obj', (object,), {
                        'kpBP': [0.0],
                        'kpV': [1.0],
                        'kiBP': [0.0],
                        'kiV': [0.0],
                    })()

                self.CP = MockCP()
                self.control = LongControl(self.CP)

            @property
            def state(self):
                return LongCtrlState(self.control.long_control_state)

            @property
            def output_accel(self):
                return self.control.last_output_accel

            def reset(self):
                self.control = LongControl(self.CP)

            def step(self, inputs: LongControlInputs) -> Tuple[LongCtrlState, float]:
                # Create mock CarState
                class MockCS:
                    vEgo = inputs.v_ego
                    aEgo = 0.0
                    brakePressed = inputs.brake_pressed
                    cruiseState = type('obj', (object,), {'standstill': inputs.cruise_standstill})()

                accel_limits = [-3.5, 2.0]
                a_target = 0.0

                output = self.control.update(
                    inputs.active, MockCS(), a_target,
                    inputs.should_stop, accel_limits
                )

                return self.state, output

        return RealLongControlWrapper()
    except ImportError as e:
        if not _IMPORT_WARNED:
            print(f"Note: Cannot import real LongControl: {e}")
            _IMPORT_WARNED = True
        return None


if __name__ == "__main__":
    # Quick test
    env = LongControlEnv()
    obs, _ = env.reset()
    print(f"Initial state: {LongCtrlState(obs['state']).name}")

    for i in range(20):
        action = {
            "active": np.random.randint(2),
            "should_stop": np.random.randint(2),
            "brake_pressed": np.random.randint(2),
            "cruise_standstill": np.random.randint(2),
            "v_ego_change": np.random.randint(3),
        }
        obs, reward, term, trunc, info = env.step(action)
        print(f"Step {i}: {info['state_name']}, accel={obs['output_accel'][0]:.2f}")
