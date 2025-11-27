"""
Standalone implementation of openpilot's StateMachine.

This is a direct copy of the logic from selfdrive/selfdrived/state.py
for validation purposes, without requiring openpilot dependencies.

This allows full validation even without building openpilot.
"""

from enum import IntEnum
from dataclasses import dataclass
from typing import Set


# Constants from common/realtime.py
DT_CTRL = 0.01  # 100 Hz

# States from cereal/log.capnp
class State(IntEnum):
    DISABLED = 0
    PRE_ENABLED = 1
    ENABLED = 2
    SOFT_DISABLING = 3
    OVERRIDING = 4


# Event types from selfdrive/selfdrived/events.py
class ET(IntEnum):
    NONE = 0
    ENABLE = 1
    PRE_ENABLE = 2
    OVERRIDE_LATERAL = 3
    OVERRIDE_LONGITUDINAL = 4
    NO_ENTRY = 5
    USER_DISABLE = 6
    SOFT_DISABLE = 7
    IMMEDIATE_DISABLE = 8
    PERMANENT = 9
    WARNING = 10


# Constants
SOFT_DISABLE_TIME = 3  # seconds
ACTIVE_STATES = (State.ENABLED, State.SOFT_DISABLING, State.OVERRIDING)
ENABLED_STATES = (State.PRE_ENABLED, *ACTIVE_STATES)


@dataclass
class Events:
    """Event container matching selfdrive/selfdrived/events.py"""
    events: Set[ET]

    def contains(self, event_type: ET) -> bool:
        return event_type in self.events

    def add(self, event_type: ET):
        self.events.add(event_type)


class RealStateMachine:
    """
    Exact copy of StateMachine from selfdrive/selfdrived/state.py

    This implementation matches the real code line-by-line for validation.
    """

    def __init__(self):
        self.current_alert_types = [ET.PERMANENT]
        self.state = State.DISABLED
        self.soft_disable_timer = 0

    def reset(self):
        """Reset to initial state"""
        self.current_alert_types = [ET.PERMANENT]
        self.state = State.DISABLED
        self.soft_disable_timer = 0

    def update(self, events: Events):
        """
        Update state machine - exact copy from state.py lines 17-97
        """
        # decrement the soft disable timer at every step, as it's reset on
        # entrance in SOFT_DISABLING state
        self.soft_disable_timer = max(0, self.soft_disable_timer - 1)

        self.current_alert_types = [ET.PERMANENT]

        # ENABLED, SOFT DISABLING, PRE ENABLING, OVERRIDING
        if self.state != State.DISABLED:
            # user and immediate disable always have priority in a non-disabled state
            if events.contains(ET.USER_DISABLE):
                self.state = State.DISABLED
                self.current_alert_types.append(ET.USER_DISABLE)

            elif events.contains(ET.IMMEDIATE_DISABLE):
                self.state = State.DISABLED
                self.current_alert_types.append(ET.IMMEDIATE_DISABLE)

            else:
                # ENABLED
                if self.state == State.ENABLED:
                    if events.contains(ET.SOFT_DISABLE):
                        self.state = State.SOFT_DISABLING
                        self.soft_disable_timer = int(SOFT_DISABLE_TIME / DT_CTRL)
                        self.current_alert_types.append(ET.SOFT_DISABLE)

                    elif events.contains(ET.OVERRIDE_LATERAL) or events.contains(ET.OVERRIDE_LONGITUDINAL):
                        self.state = State.OVERRIDING
                        self.current_alert_types += [ET.OVERRIDE_LATERAL, ET.OVERRIDE_LONGITUDINAL]

                # SOFT DISABLING
                elif self.state == State.SOFT_DISABLING:
                    if not events.contains(ET.SOFT_DISABLE):
                        # no more soft disabling condition, so go back to ENABLED
                        self.state = State.ENABLED

                    elif self.soft_disable_timer > 0:
                        self.current_alert_types.append(ET.SOFT_DISABLE)

                    elif self.soft_disable_timer <= 0:
                        self.state = State.DISABLED

                # PRE ENABLING
                elif self.state == State.PRE_ENABLED:
                    if not events.contains(ET.PRE_ENABLE):
                        self.state = State.ENABLED
                    else:
                        self.current_alert_types.append(ET.PRE_ENABLE)

                # OVERRIDING
                elif self.state == State.OVERRIDING:
                    if events.contains(ET.SOFT_DISABLE):
                        self.state = State.SOFT_DISABLING
                        self.soft_disable_timer = int(SOFT_DISABLE_TIME / DT_CTRL)
                        self.current_alert_types.append(ET.SOFT_DISABLE)
                    elif not (events.contains(ET.OVERRIDE_LATERAL) or events.contains(ET.OVERRIDE_LONGITUDINAL)):
                        self.state = State.ENABLED
                    else:
                        self.current_alert_types += [ET.OVERRIDE_LATERAL, ET.OVERRIDE_LONGITUDINAL]

        # DISABLED
        elif self.state == State.DISABLED:
            if events.contains(ET.ENABLE):
                if events.contains(ET.NO_ENTRY):
                    self.current_alert_types.append(ET.NO_ENTRY)

                else:
                    if events.contains(ET.PRE_ENABLE):
                        self.state = State.PRE_ENABLED
                    elif events.contains(ET.OVERRIDE_LATERAL) or events.contains(ET.OVERRIDE_LONGITUDINAL):
                        self.state = State.OVERRIDING
                    else:
                        self.state = State.ENABLED
                    self.current_alert_types.append(ET.ENABLE)

        # Check if openpilot is engaged and actuators are enabled
        enabled = self.state in ENABLED_STATES
        active = self.state in ACTIVE_STATES
        if active:
            self.current_alert_types.append(ET.WARNING)
        return enabled, active


def create_real_state_machine():
    """Factory function for RealStateMachine"""
    return RealStateMachine()


if __name__ == "__main__":
    # Quick test
    sm = RealStateMachine()
    print(f"Initial state: {sm.state.name}")

    # Test enable
    events = Events(events={ET.ENABLE})
    sm.update(events)
    print(f"After ENABLE: {sm.state.name}")

    # Test soft disable
    events = Events(events={ET.SOFT_DISABLE})
    sm.update(events)
    print(f"After SOFT_DISABLE: {sm.state.name}, timer={sm.soft_disable_timer}")

    # Let timer expire
    for i in range(305):
        events = Events(events={ET.SOFT_DISABLE})
        sm.update(events)

    print(f"After timer expires: {sm.state.name}")
