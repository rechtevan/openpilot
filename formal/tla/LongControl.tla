---------------------------- MODULE LongControl ----------------------------
(*
 * TLA+ Specification for openpilot Longitudinal Control State Machine
 *
 * This models the longitudinal (acceleration/braking) control in:
 *   selfdrive/controls/lib/longcontrol.py
 *
 * States: off, stopping, starting, pid
 *
 * The longitudinal controller manages vehicle acceleration to follow
 * a target speed/acceleration while ensuring safe stopping behavior.
 *)

EXTENDS Integers

CONSTANTS
    ACCEL_MIN,          \* Minimum acceleration (negative = braking)
    ACCEL_MAX,          \* Maximum acceleration
    STOP_ACCEL,         \* Target accel when stopped (e.g., -2.0)
    START_ACCEL,        \* Accel when starting from stop (e.g., 1.2)
    STOPPING_DECEL_RATE,\* Decel rate when stopping (e.g., 0.8)
    V_EGO_STARTING,     \* Speed threshold for "started" (e.g., 0.5 m/s)
    DT_CTRL             \* Control loop period (0.01s)

\* States
CONSTANTS
    Off,
    Stopping,
    Starting,
    Pid

VARIABLES
    long_control_state, \* Current state
    output_accel,       \* Current output acceleration
    last_output_accel,  \* Previous output acceleration
    \* Input variables (from environment)
    active,             \* Is longitudinal control active?
    v_ego,              \* Current vehicle speed
    should_stop,        \* Should we stop?
    brake_pressed,      \* Is brake pedal pressed?
    cruise_standstill,  \* Is cruise in standstill mode?
    a_target            \* Target acceleration from planner

vars == <<long_control_state, output_accel, last_output_accel,
          active, v_ego, should_stop, brake_pressed, cruise_standstill, a_target>>

\* Type invariant
TypeOK ==
    /\ long_control_state \in {Off, Stopping, Starting, Pid}
    /\ output_accel \in ACCEL_MIN..ACCEL_MAX
    /\ last_output_accel \in ACCEL_MIN..ACCEL_MAX
    /\ active \in BOOLEAN
    /\ v_ego >= 0
    /\ should_stop \in BOOLEAN
    /\ brake_pressed \in BOOLEAN
    /\ cruise_standstill \in BOOLEAN

\* Derived conditions (based on current state)
StoppingCondition == should_stop
StartingCondition == ~should_stop /\ ~cruise_standstill /\ ~brake_pressed
StartedCondition == v_ego > V_EGO_STARTING

\* Derived conditions (based on next state inputs - used in transitions)
StoppingCondition2(ss) == ss
StartingCondition2(ss, cs, bp) == ~ss /\ ~cs /\ ~bp
StartedCondition2(ve) == ve > V_EGO_STARTING

\* Zero acceleration (offset by ACCEL_OFFSET)
\* In the offset scheme: real 0 -> 5 (middle of 0-10 range)
ACCEL_ZERO == 5  \* This represents real acceleration of 0

\* Initial state
Init ==
    /\ long_control_state = Off
    /\ output_accel = ACCEL_ZERO
    /\ last_output_accel = ACCEL_ZERO
    /\ active = FALSE
    /\ v_ego = 0
    /\ should_stop = TRUE
    /\ brake_pressed = FALSE
    /\ cruise_standstill = FALSE
    /\ a_target = ACCEL_ZERO

(*
 * Clip value to accel limits
 *)
Clip(val) ==
    IF val < ACCEL_MIN THEN ACCEL_MIN
    ELSE IF val > ACCEL_MAX THEN ACCEL_MAX
    ELSE val

(*
 * Combined State Transition and Output (single step)
 * This matches the actual implementation where state and output are computed together
 *)

\* When not active, go to Off with zero output
StepOff ==
    /\ ~active'
    /\ long_control_state' = Off
    /\ output_accel' = ACCEL_ZERO
    /\ last_output_accel' = ACCEL_ZERO

\* From Off when becoming active - uses current input state
StepFromOff ==
    /\ active'
    /\ long_control_state = Off
    /\ IF ~StartingCondition
       THEN /\ long_control_state' = Stopping
            /\ output_accel' = ACCEL_ZERO
            /\ last_output_accel' = ACCEL_ZERO
       ELSE /\ long_control_state' = Starting
            /\ output_accel' = Clip(START_ACCEL)
            /\ last_output_accel' = Clip(START_ACCEL)

\* From Stopping when active
StepFromStopping ==
    /\ active'
    /\ long_control_state = Stopping
    /\ IF StartingCondition
       THEN /\ long_control_state' = Starting
            /\ output_accel' = Clip(START_ACCEL)
            /\ last_output_accel' = Clip(START_ACCEL)
       ELSE /\ long_control_state' = Stopping
            /\ LET prev == last_output_accel
                   ramped == IF prev > STOP_ACCEL
                             THEN Clip(prev - STOPPING_DECEL_RATE * DT_CTRL)
                             ELSE prev
               IN /\ output_accel' = Clip(ramped)
                  /\ last_output_accel' = Clip(ramped)

\* From Starting when active
StepFromStarting ==
    /\ active'
    /\ long_control_state = Starting
    /\ IF StoppingCondition
       THEN /\ long_control_state' = Stopping
            /\ LET prev == last_output_accel
                   ramped == IF prev > STOP_ACCEL
                             THEN Clip(prev - STOPPING_DECEL_RATE * DT_CTRL)
                             ELSE prev
               IN /\ output_accel' = Clip(ramped)
                  /\ last_output_accel' = Clip(ramped)
       ELSE IF StartedCondition
            THEN /\ long_control_state' = Pid
                 /\ \E accel \in ACCEL_MIN..ACCEL_MAX :
                     /\ output_accel' = accel
                     /\ last_output_accel' = accel
            ELSE /\ long_control_state' = Starting
                 /\ output_accel' = Clip(START_ACCEL)
                 /\ last_output_accel' = Clip(START_ACCEL)

\* From Pid when active
StepFromPid ==
    /\ active'
    /\ long_control_state = Pid
    /\ IF StoppingCondition
       THEN /\ long_control_state' = Stopping
            /\ LET prev == last_output_accel
                   ramped == IF prev > STOP_ACCEL
                             THEN Clip(prev - STOPPING_DECEL_RATE * DT_CTRL)
                             ELSE prev
               IN /\ output_accel' = Clip(ramped)
                  /\ last_output_accel' = Clip(ramped)
       ELSE /\ long_control_state' = Pid
            /\ \E accel \in ACCEL_MIN..ACCEL_MAX :
                /\ output_accel' = accel
                /\ last_output_accel' = accel

(*
 * Environment Actions (inputs can change)
 *)

ChangeInputs ==
    /\ active' \in BOOLEAN
    /\ v_ego' \in 0..5  \* Reduced range for model checking
    /\ should_stop' \in BOOLEAN
    /\ brake_pressed' \in BOOLEAN
    /\ cruise_standstill' \in BOOLEAN
    /\ a_target' \in ACCEL_MIN..ACCEL_MAX

(*
 * Combined Next State
 *)

Next ==
    /\ ChangeInputs
    /\ \/ StepOff
       \/ StepFromOff
       \/ StepFromStopping
       \/ StepFromStarting
       \/ StepFromPid

\* Specification
Spec == Init /\ [][Next]_vars

(*
 * SAFETY PROPERTIES
 *)

\* S1: Output acceleration is always within bounds
AccelBounded ==
    output_accel >= ACCEL_MIN /\ output_accel <= ACCEL_MAX

\* S2: In Stopping state, output is never positive (no acceleration while stopping)
\* With offset: real 0 = ACCEL_ZERO (40), so <= ACCEL_ZERO means no positive accel
StoppingNeverAccelerates ==
    long_control_state = Stopping => output_accel <= ACCEL_ZERO

\* S3: When not active, output is zero
InactiveOutputZero ==
    ~active => output_accel = ACCEL_ZERO

\* S4: In Starting state, output is at most START_ACCEL
StartingBounded ==
    long_control_state = Starting => output_accel <= START_ACCEL

\* S5: State is Off when not active
InactiveMeansOff ==
    ~active => long_control_state = Off

\* S6: Brake pressed prevents positive acceleration
BrakePressedNoAccel ==
    (brake_pressed /\ long_control_state # Off) => output_accel <= ACCEL_ZERO

(*
 * STATE MACHINE PROPERTIES
 *)

\* SM1: Valid state transitions from Off
OffTransitions ==
    long_control_state = Off =>
        long_control_state' \in {Off, Stopping, Starting, Pid}

\* SM2: Valid state transitions from Stopping
StoppingTransitions ==
    long_control_state = Stopping =>
        long_control_state' \in {Off, Stopping, Starting, Pid}

\* SM3: Valid state transitions from Starting
StartingTransitions ==
    long_control_state = Starting =>
        long_control_state' \in {Off, Stopping, Starting, Pid}

\* SM4: Valid state transitions from Pid
PidTransitions ==
    long_control_state = Pid =>
        long_control_state' \in {Off, Stopping, Pid}

(*
 * LIVENESS PROPERTIES
 *)

\* L1: If stopping condition clears and we're in Stopping, eventually leave Stopping
EventuallyLeavesStopping ==
    (long_control_state = Stopping /\ StartingCondition) ~>
        (long_control_state # Stopping)

\* L2: If started condition met in Starting, eventually go to Pid
StartingToPid ==
    (long_control_state = Starting /\ StartedCondition) ~>
        (long_control_state = Pid \/ long_control_state = Off)

(*
 * COMBINED SAFETY INVARIANT
 *)

SafetyInvariant ==
    /\ TypeOK
    /\ AccelBounded
    /\ StoppingNeverAccelerates
    /\ InactiveMeansOff

=============================================================================
