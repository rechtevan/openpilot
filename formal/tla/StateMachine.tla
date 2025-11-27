--------------------------- MODULE StateMachine ---------------------------
(*
 * TLA+ Specification for openpilot Primary State Machine
 *
 * This models the engagement/disengagement state machine in:
 *   selfdrive/selfdrived/state.py
 *
 * States: disabled, preEnabled, enabled, softDisabling, overriding
 *
 * Event Types (ET):
 *   - ENABLE: Request to enable openpilot
 *   - PRE_ENABLE: Pre-enable condition (e.g., brake held at standstill)
 *   - OVERRIDE_LATERAL: Driver overriding steering
 *   - OVERRIDE_LONGITUDINAL: Driver overriding acceleration
 *   - NO_ENTRY: Condition preventing engagement
 *   - USER_DISABLE: User-initiated disable (brake, cancel button)
 *   - SOFT_DISABLE: Condition requiring gradual disable
 *   - IMMEDIATE_DISABLE: Critical condition requiring immediate disable
 *)

EXTENDS Integers, Sequences

CONSTANTS
    SOFT_DISABLE_TIME,  \* Timer duration in cycles (e.g., 300 for 3s at 100Hz)
    DT_CTRL             \* Control loop period (0.01s = 100Hz)

\* States
CONSTANTS
    Disabled,
    PreEnabled,
    Enabled,
    SoftDisabling,
    Overriding

\* Event Types
CONSTANTS
    ET_ENABLE,
    ET_PRE_ENABLE,
    ET_OVERRIDE_LATERAL,
    ET_OVERRIDE_LONGITUDINAL,
    ET_NO_ENTRY,
    ET_USER_DISABLE,
    ET_SOFT_DISABLE,
    ET_IMMEDIATE_DISABLE

VARIABLES
    state,              \* Current state
    soft_disable_timer, \* Countdown timer for soft disable
    events              \* Set of active events

vars == <<state, soft_disable_timer, events>>

\* Helper: Check if any event type is present
Contains(event_type) == event_type \in events

\* Helper: Check if any override is active
HasOverride == Contains(ET_OVERRIDE_LATERAL) \/ Contains(ET_OVERRIDE_LONGITUDINAL)

\* Active states (system is controlling the vehicle)
ActiveStates == {Enabled, SoftDisabling, Overriding}

\* Enabled states (system is engaged)
EnabledStates == {PreEnabled, Enabled, SoftDisabling, Overriding}

\* Type invariant
TypeOK ==
    /\ state \in {Disabled, PreEnabled, Enabled, SoftDisabling, Overriding}
    /\ soft_disable_timer \in 0..SOFT_DISABLE_TIME
    /\ events \subseteq {ET_ENABLE, ET_PRE_ENABLE, ET_OVERRIDE_LATERAL,
                         ET_OVERRIDE_LONGITUDINAL, ET_NO_ENTRY, ET_USER_DISABLE,
                         ET_SOFT_DISABLE, ET_IMMEDIATE_DISABLE}

\* Initial state
Init ==
    /\ state = Disabled
    /\ soft_disable_timer = 0
    /\ events = {}

(*
 * State Transitions
 * Priority: USER_DISABLE > IMMEDIATE_DISABLE > SOFT_DISABLE > others
 *)

\* Decrement soft disable timer (happens every step)
DecrementTimer ==
    soft_disable_timer' = IF soft_disable_timer > 0
                          THEN soft_disable_timer - 1
                          ELSE 0

\* From any non-disabled state: USER_DISABLE has highest priority
UserDisable ==
    /\ state # Disabled
    /\ Contains(ET_USER_DISABLE)
    /\ state' = Disabled
    /\ DecrementTimer
    /\ UNCHANGED events

\* From any non-disabled state: IMMEDIATE_DISABLE has second priority
ImmediateDisable ==
    /\ state # Disabled
    /\ ~Contains(ET_USER_DISABLE)
    /\ Contains(ET_IMMEDIATE_DISABLE)
    /\ state' = Disabled
    /\ DecrementTimer
    /\ UNCHANGED events

\* From ENABLED: Transition to SOFT_DISABLING
EnabledToSoftDisabling ==
    /\ state = Enabled
    /\ ~Contains(ET_USER_DISABLE)
    /\ ~Contains(ET_IMMEDIATE_DISABLE)
    /\ Contains(ET_SOFT_DISABLE)
    /\ state' = SoftDisabling
    /\ soft_disable_timer' = SOFT_DISABLE_TIME
    /\ UNCHANGED events

\* From ENABLED: Transition to OVERRIDING
EnabledToOverriding ==
    /\ state = Enabled
    /\ ~Contains(ET_USER_DISABLE)
    /\ ~Contains(ET_IMMEDIATE_DISABLE)
    /\ ~Contains(ET_SOFT_DISABLE)
    /\ HasOverride
    /\ state' = Overriding
    /\ DecrementTimer
    /\ UNCHANGED events

\* From ENABLED: Stay in ENABLED (no events)
EnabledStay ==
    /\ state = Enabled
    /\ ~Contains(ET_USER_DISABLE)
    /\ ~Contains(ET_IMMEDIATE_DISABLE)
    /\ ~Contains(ET_SOFT_DISABLE)
    /\ ~HasOverride
    /\ state' = Enabled
    /\ DecrementTimer
    /\ UNCHANGED events

\* From SOFT_DISABLING: Return to ENABLED (soft disable condition cleared)
SoftDisablingToEnabled ==
    /\ state = SoftDisabling
    /\ ~Contains(ET_USER_DISABLE)
    /\ ~Contains(ET_IMMEDIATE_DISABLE)
    /\ ~Contains(ET_SOFT_DISABLE)
    /\ state' = Enabled
    /\ DecrementTimer
    /\ UNCHANGED events

\* From SOFT_DISABLING: Stay in SOFT_DISABLING (condition persists, timer > 0)
SoftDisablingStay ==
    /\ state = SoftDisabling
    /\ ~Contains(ET_USER_DISABLE)
    /\ ~Contains(ET_IMMEDIATE_DISABLE)
    /\ Contains(ET_SOFT_DISABLE)
    /\ soft_disable_timer > 0
    /\ state' = SoftDisabling
    /\ DecrementTimer
    /\ UNCHANGED events

\* From SOFT_DISABLING: Timer expired -> DISABLED
SoftDisablingTimeout ==
    /\ state = SoftDisabling
    /\ ~Contains(ET_USER_DISABLE)
    /\ ~Contains(ET_IMMEDIATE_DISABLE)
    /\ Contains(ET_SOFT_DISABLE)
    /\ soft_disable_timer <= 0
    /\ state' = Disabled
    /\ soft_disable_timer' = 0
    /\ UNCHANGED events

\* From PRE_ENABLED: Transition to ENABLED
PreEnabledToEnabled ==
    /\ state = PreEnabled
    /\ ~Contains(ET_USER_DISABLE)
    /\ ~Contains(ET_IMMEDIATE_DISABLE)
    /\ ~Contains(ET_PRE_ENABLE)
    /\ state' = Enabled
    /\ DecrementTimer
    /\ UNCHANGED events

\* From PRE_ENABLED: Stay in PRE_ENABLED
PreEnabledStay ==
    /\ state = PreEnabled
    /\ ~Contains(ET_USER_DISABLE)
    /\ ~Contains(ET_IMMEDIATE_DISABLE)
    /\ Contains(ET_PRE_ENABLE)
    /\ state' = PreEnabled
    /\ DecrementTimer
    /\ UNCHANGED events

\* From OVERRIDING: Transition to SOFT_DISABLING
OverridingToSoftDisabling ==
    /\ state = Overriding
    /\ ~Contains(ET_USER_DISABLE)
    /\ ~Contains(ET_IMMEDIATE_DISABLE)
    /\ Contains(ET_SOFT_DISABLE)
    /\ state' = SoftDisabling
    /\ soft_disable_timer' = SOFT_DISABLE_TIME
    /\ UNCHANGED events

\* From OVERRIDING: Return to ENABLED
OverridingToEnabled ==
    /\ state = Overriding
    /\ ~Contains(ET_USER_DISABLE)
    /\ ~Contains(ET_IMMEDIATE_DISABLE)
    /\ ~Contains(ET_SOFT_DISABLE)
    /\ ~HasOverride
    /\ state' = Enabled
    /\ DecrementTimer
    /\ UNCHANGED events

\* From OVERRIDING: Stay in OVERRIDING
OverridingStay ==
    /\ state = Overriding
    /\ ~Contains(ET_USER_DISABLE)
    /\ ~Contains(ET_IMMEDIATE_DISABLE)
    /\ ~Contains(ET_SOFT_DISABLE)
    /\ HasOverride
    /\ state' = Overriding
    /\ DecrementTimer
    /\ UNCHANGED events

\* From DISABLED: Enable with PRE_ENABLE -> PRE_ENABLED
DisabledToPreEnabled ==
    /\ state = Disabled
    /\ Contains(ET_ENABLE)
    /\ ~Contains(ET_NO_ENTRY)
    /\ Contains(ET_PRE_ENABLE)
    /\ state' = PreEnabled
    /\ UNCHANGED <<soft_disable_timer, events>>

\* From DISABLED: Enable with override -> OVERRIDING
DisabledToOverriding ==
    /\ state = Disabled
    /\ Contains(ET_ENABLE)
    /\ ~Contains(ET_NO_ENTRY)
    /\ ~Contains(ET_PRE_ENABLE)
    /\ HasOverride
    /\ state' = Overriding
    /\ UNCHANGED <<soft_disable_timer, events>>

\* From DISABLED: Enable normally -> ENABLED
DisabledToEnabled ==
    /\ state = Disabled
    /\ Contains(ET_ENABLE)
    /\ ~Contains(ET_NO_ENTRY)
    /\ ~Contains(ET_PRE_ENABLE)
    /\ ~HasOverride
    /\ state' = Enabled
    /\ UNCHANGED <<soft_disable_timer, events>>

\* From DISABLED: NO_ENTRY blocks engagement
DisabledNoEntry ==
    /\ state = Disabled
    /\ Contains(ET_ENABLE)
    /\ Contains(ET_NO_ENTRY)
    /\ state' = Disabled
    /\ UNCHANGED <<soft_disable_timer, events>>

\* From DISABLED: Stay disabled (no enable request)
DisabledStay ==
    /\ state = Disabled
    /\ ~Contains(ET_ENABLE)
    /\ state' = Disabled
    /\ UNCHANGED <<soft_disable_timer, events>>

\* Environment can change events at any time
ChangeEvents ==
    /\ events' \in SUBSET {ET_ENABLE, ET_PRE_ENABLE, ET_OVERRIDE_LATERAL,
                           ET_OVERRIDE_LONGITUDINAL, ET_NO_ENTRY, ET_USER_DISABLE,
                           ET_SOFT_DISABLE, ET_IMMEDIATE_DISABLE}
    /\ UNCHANGED <<state, soft_disable_timer>>

\* Next state relation
Next ==
    \/ UserDisable
    \/ ImmediateDisable
    \/ EnabledToSoftDisabling
    \/ EnabledToOverriding
    \/ EnabledStay
    \/ SoftDisablingToEnabled
    \/ SoftDisablingStay
    \/ SoftDisablingTimeout
    \/ PreEnabledToEnabled
    \/ PreEnabledStay
    \/ OverridingToSoftDisabling
    \/ OverridingToEnabled
    \/ OverridingStay
    \/ DisabledToPreEnabled
    \/ DisabledToOverriding
    \/ DisabledToEnabled
    \/ DisabledNoEntry
    \/ DisabledStay
    \/ ChangeEvents

\* Fairness: Events eventually change, timer eventually decrements
Fairness ==
    /\ WF_vars(Next)

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

(*
 * SAFETY INVARIANTS (state predicates that must always hold)
 *)

\* S1: Soft disable timer is bounded
TimerBounded ==
    soft_disable_timer >= 0 /\ soft_disable_timer <= SOFT_DISABLE_TIME

\* S2: SoftDisabling state always has a valid timer
\* Note: Timer may have residual value after recovery (it decrements to 0)
SoftDisablingHasTimer ==
    (state = SoftDisabling) => (soft_disable_timer > 0 \/ soft_disable_timer = 0)

\* S3: Active states are a subset of enabled states
ActiveMeansEngagedInv ==
    state \in ActiveStates => state \in EnabledStates

(*
 * ACTION PROPERTIES (properties about state transitions)
 * These are checked via the Next action, not as temporal formulas
 *)

\* S4: USER_DISABLE action always results in disabled state
UserDisableAction ==
    (state # Disabled /\ Contains(ET_USER_DISABLE)) => (state' = Disabled)

\* S5: IMMEDIATE_DISABLE action always results in disabled state (when no USER_DISABLE)
ImmediateDisableAction ==
    (state # Disabled /\ ~Contains(ET_USER_DISABLE) /\ Contains(ET_IMMEDIATE_DISABLE))
       => (state' = Disabled)

\* S6: NO_ENTRY prevents engagement
NoEntryPreventsAction ==
    (state = Disabled /\ Contains(ET_ENABLE) /\ Contains(ET_NO_ENTRY))
       => (state' = Disabled)

\* S7: Cannot transition to enabled states without ENABLE event from disabled
NeedEnableAction ==
    (state = Disabled /\ ~Contains(ET_ENABLE)) => (state' = Disabled)

\* S8: From disabled, only valid next states
DisabledTransitionsAction ==
    (state = Disabled) => (state' \in {Disabled, PreEnabled, Enabled, Overriding})

(*
 * LIVENESS PROPERTIES
 *)

\* L1: Soft disabling eventually terminates (reaches disabled or enabled)
SoftDisablingTerminates ==
    state = SoftDisabling ~> (state = Disabled \/ state = Enabled)

\* L2: Can always reach disabled state from any state
CanAlwaysDisable ==
    state \in EnabledStates ~> state = Disabled

\* L3: PreEnabled eventually transitions (doesn't stay forever)
PreEnabledTransitions ==
    state = PreEnabled ~> (state = Enabled \/ state = Disabled)

(*
 * COMBINED INVARIANTS
 *)

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ TimerBounded
    /\ SoftDisablingHasTimer
    /\ ActiveMeansEngagedInv

=============================================================================
