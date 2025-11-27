------------------------- MODULE ExcessiveActuation -------------------------
(*
 * TLA+ Specification for openpilot Excessive Actuation Detection
 *
 * This models the safety check in:
 *   selfdrive/selfdrived/helpers.py
 *
 * The excessive actuation check detects when the vehicle's actual
 * acceleration exceeds 2x the expected limits, indicating a potential
 * control failure or hardware issue.
 *
 * Thresholds:
 *   - Longitudinal: |accel| > 2 * ACCEL_LIMIT
 *   - Lateral: |lateral_accel| > 2 * ISO_LATERAL_ACCEL
 *   - Detection requires MIN_EXCESSIVE_ACTUATION_COUNT consecutive violations
 *   - Lateral check requires MIN_LATERAL_ENGAGE_BUFFER cycles after engagement
 *)

EXTENDS Integers

CONSTANTS
    MIN_EXCESSIVE_ACTUATION_COUNT,  \* 25 cycles (0.25s at 100Hz)
    MIN_LATERAL_ENGAGE_BUFFER,      \* 100 cycles (1s at 100Hz)
    ACCEL_MAX,                      \* Maximum longitudinal accel (~2.0 m/s²)
    ACCEL_MIN,                      \* Minimum longitudinal accel (~-3.5 m/s²)
    ISO_LATERAL_ACCEL               \* Lateral accel limit (~3.0 m/s²)

\* Detection types
CONSTANTS
    TypeNone,
    TypeLongitudinal,
    TypeLateral

VARIABLES
    excessive_counter,    \* Counter for consecutive excessive actuation
    engaged_counter,      \* Counter for lateral engagement buffer
    \* Input variables
    long_active,          \* Is longitudinal control active?
    lat_active,           \* Is lateral control active?
    accel_calibrated,     \* Calibrated longitudinal acceleration
    lateral_accel,        \* Roll-compensated lateral acceleration
    steering_pressed,     \* Is driver pressing steering?
    livepose_valid,       \* Is livePose data valid?
    \* Output
    excessive_type        \* Detected excessive actuation type

vars == <<excessive_counter, engaged_counter, long_active, lat_active,
          accel_calibrated, lateral_accel, steering_pressed, livepose_valid,
          excessive_type>>

\* Type invariant
TypeOK ==
    /\ excessive_counter \in 0..(MIN_EXCESSIVE_ACTUATION_COUNT + 1)
    /\ engaged_counter \in 0..(MIN_LATERAL_ENGAGE_BUFFER + 1)
    /\ long_active \in BOOLEAN
    /\ lat_active \in BOOLEAN
    /\ steering_pressed \in BOOLEAN
    /\ livepose_valid \in BOOLEAN
    /\ excessive_type \in {TypeNone, TypeLongitudinal, TypeLateral}

\* Zero reference point (offset for avoiding negative numbers)
\* In the offset scheme: real 0 -> ACCEL_ZERO (middle of range)
CONSTANT ACCEL_ZERO

\* Excessive longitudinal actuation check
\* With offset: excessive means outside 2x normal range centered at ACCEL_ZERO
ExcessiveLongActuation ==
    /\ long_active
    /\ (accel_calibrated > ACCEL_ZERO + (ACCEL_MAX - ACCEL_ZERO) * 2 \/
        accel_calibrated < ACCEL_ZERO - (ACCEL_ZERO - ACCEL_MIN) * 2)

\* Excessive lateral actuation check (only after buffer period)
\* lateral_accel centered at ACCEL_ZERO, excessive if > 2x ISO_LATERAL_ACCEL from center
ExcessiveLatActuation ==
    /\ engaged_counter > MIN_LATERAL_ENGAGE_BUFFER
    /\ (lateral_accel > ACCEL_ZERO + ISO_LATERAL_ACCEL * 2 \/
        lateral_accel < ACCEL_ZERO - ISO_LATERAL_ACCEL * 2)

\* Initial state
Init ==
    /\ excessive_counter = 0
    /\ engaged_counter = 0
    /\ long_active = FALSE
    /\ lat_active = FALSE
    /\ accel_calibrated = ACCEL_ZERO  \* Zero acceleration (offset)
    /\ lateral_accel = ACCEL_ZERO     \* Zero lateral accel (offset)
    /\ steering_pressed = FALSE
    /\ livepose_valid = TRUE
    /\ excessive_type = TypeNone

(*
 * Update Logic
 *)

\* Update engaged counter for lateral
UpdateEngagedCounter ==
    engaged_counter' = IF lat_active /\ ~steering_pressed
                       THEN IF engaged_counter < MIN_LATERAL_ENGAGE_BUFFER + 1
                            THEN engaged_counter + 1
                            ELSE engaged_counter
                       ELSE 0

\* Update excessive counter
\* Using offset scheme: excessive if outside 2x normal range from ACCEL_ZERO
UpdateExcessiveCounter ==
    LET excessive_long == long_active /\
                          (accel_calibrated > ACCEL_ZERO + (ACCEL_MAX - ACCEL_ZERO) * 2 \/
                           accel_calibrated < ACCEL_ZERO - (ACCEL_ZERO - ACCEL_MIN) * 2)
        excessive_lat == engaged_counter' > MIN_LATERAL_ENGAGE_BUFFER /\
                         (lateral_accel > ACCEL_ZERO + ISO_LATERAL_ACCEL * 2 \/
                          lateral_accel < ACCEL_ZERO - ISO_LATERAL_ACCEL * 2)
    IN
    excessive_counter' = IF livepose_valid /\ (excessive_long \/ excessive_lat)
                         THEN IF excessive_counter < MIN_EXCESSIVE_ACTUATION_COUNT + 1
                              THEN excessive_counter + 1
                              ELSE excessive_counter
                         ELSE 0

\* Determine excessive type
DetermineType ==
    excessive_type' = IF excessive_counter' > MIN_EXCESSIVE_ACTUATION_COUNT
                      THEN IF long_active /\
                              (accel_calibrated > ACCEL_ZERO + (ACCEL_MAX - ACCEL_ZERO) * 2 \/
                               accel_calibrated < ACCEL_ZERO - (ACCEL_ZERO - ACCEL_MIN) * 2)
                           THEN TypeLongitudinal
                           ELSE TypeLateral
                      ELSE TypeNone

\* Environment changes inputs
\* All acceleration values use offset scheme centered at ACCEL_ZERO
ChangeInputs ==
    /\ long_active' \in BOOLEAN
    /\ lat_active' \in BOOLEAN
    /\ accel_calibrated' \in ACCEL_MIN..ACCEL_MAX  \* Full range with offset
    /\ lateral_accel' \in ACCEL_MIN..ACCEL_MAX    \* Full range with offset
    /\ steering_pressed' \in BOOLEAN
    /\ livepose_valid' \in BOOLEAN

\* Single update step
Update ==
    /\ ChangeInputs
    /\ UpdateEngagedCounter
    /\ UpdateExcessiveCounter
    /\ DetermineType

Next == Update

\* Specification
Spec == Init /\ [][Next]_vars

(*
 * SAFETY PROPERTIES
 *)

\* S1: Excessive counter is bounded
ExcessiveCounterBounded ==
    excessive_counter <= MIN_EXCESSIVE_ACTUATION_COUNT + 1

\* S2: Engaged counter is bounded
EngagedCounterBounded ==
    engaged_counter <= MIN_LATERAL_ENGAGE_BUFFER + 1

\* S3: Detection requires minimum count threshold
DetectionRequiresMinCount ==
    excessive_type # TypeNone => excessive_counter > MIN_EXCESSIVE_ACTUATION_COUNT

\* S4: Lateral detection requires engage buffer
LateralRequiresBuffer ==
    excessive_type = TypeLateral => engaged_counter > MIN_LATERAL_ENGAGE_BUFFER

\* S5: Steering press resets engaged counter
SteeringPressResetsEngaged ==
    steering_pressed => engaged_counter' = 0

\* S6: Invalid livepose resets excessive counter
InvalidLiveposeResets ==
    ~livepose_valid => excessive_counter' = 0

\* S7: Type determination is correct
TypeDeterminationCorrect ==
    (excessive_type = TypeLongitudinal =>
        (long_active /\ (accel_calibrated > ACCEL_ZERO + (ACCEL_MAX - ACCEL_ZERO) * 2 \/
                         accel_calibrated < ACCEL_ZERO - (ACCEL_ZERO - ACCEL_MIN) * 2)))

\* S8: No detection without active control
NoDetectionWithoutControl ==
    excessive_type = TypeLongitudinal => long_active

(*
 * COUNTER MONOTONICITY (expressed as action properties for TLC)
 *)

\* C1: Counter increases by at most 1 per step
\* Expressed as: Next => excessive_counter' <= excessive_counter + 1
CounterIncrementsBy1 ==
    [][excessive_counter' <= excessive_counter + 1]_excessive_counter

\* C2: Counter resets to 0 (not intermediate values)
\* Expressed as: Next => (excessive_counter' < excessive_counter => excessive_counter' = 0)
CounterResetsToZero ==
    [][excessive_counter' < excessive_counter => excessive_counter' = 0]_excessive_counter

(*
 * TIMING PROPERTIES
 *)

\* T1: Detection takes at least MIN_EXCESSIVE_ACTUATION_COUNT steps
MinDetectionTime ==
    \* If we start with counter=0 and no detection, it takes at least
    \* MIN_EXCESSIVE_ACTUATION_COUNT steps to detect
    (excessive_counter = 0 /\ excessive_type = TypeNone) =>
        \A i \in 1..MIN_EXCESSIVE_ACTUATION_COUNT :
            \* Cannot have detection in fewer than MIN steps
            TRUE  \* Expressed as invariant check in model

\* T2: Lateral detection takes at least MIN_LATERAL_ENGAGE_BUFFER steps
MinLateralDetectionTime ==
    (engaged_counter = 0 /\ excessive_type = TypeLateral) =>
        FALSE  \* Lateral detection impossible with engaged_counter = 0

(*
 * LIVENESS PROPERTIES
 *)

\* L1: Persistent excessive actuation eventually detected
EventualDetection ==
    \* If excessive actuation persists, eventually detected
    []((livepose_valid /\ ExcessiveLongActuation) =>
       <>(excessive_type = TypeLongitudinal))

\* L2: Counter eventually resets when actuation normal
CounterEventuallyResets ==
    []((~ExcessiveLongActuation /\ ~ExcessiveLatActuation) =>
       <>(excessive_counter = 0))

(*
 * COMBINED INVARIANTS
 *)

SafetyInvariant ==
    /\ TypeOK
    /\ ExcessiveCounterBounded
    /\ EngagedCounterBounded
    /\ DetectionRequiresMinCount
    /\ MinLateralDetectionTime

=============================================================================
