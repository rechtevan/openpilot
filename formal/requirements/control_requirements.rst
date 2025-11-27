Control Requirements
====================

Requirements for longitudinal control, lane change, and actuation limits.

.. note::

   **Upstream Sources:**

   - ``selfdrive/controls/lib/longcontrol.py`` - Longitudinal control
   - ``selfdrive/controls/lib/desire_helper.py`` - Lane change logic
   - ``selfdrive/selfdrived/helpers.py`` - Excessive actuation detection


Longitudinal Control Requirements
---------------------------------

.. spec:: Acceleration Bounds
   :id: SPEC-LONG-001
   :status: approved
   :derives_from: REQ-SAFE-002
   :upstream_source: selfdrive/controls/lib/longcontrol.py
   :standard: ISO15622
   :verification_method: formal

   Longitudinal acceleration output shall be bounded within safe limits:

   - **Minimum acceleration:** -4.0 m/s² (maximum braking)
   - **Maximum acceleration:** 2.5 m/s² (maximum throttle)

   **Rationale:**
      Prevents sudden acceleration/deceleration that could destabilize
      the vehicle or surprise the driver.

   **TLA+ Property:**
      ``AccelBounded == [](accel_output >= -4 /\ accel_output <= 2.5)``


.. spec:: Jerk Rate Limiting
   :id: SPEC-LONG-002
   :status: approved
   :derives_from: REQ-SAFE-002
   :upstream_source: selfdrive/controls/lib/longcontrol.py
   :verification_method: test

   Rate of change of acceleration (jerk) shall be limited to prevent
   abrupt changes in vehicle motion.

   **Implementation:**
      Acceleration is rate-limited per control cycle to ensure smooth
      transitions.


.. spec:: Speed Control Output
   :id: SPEC-LONG-003
   :status: approved
   :derives_from: REQ-SAFE-002
   :upstream_source: selfdrive/controls/lib/longcontrol.py
   :verification_method: formal, test

   The longitudinal controller shall always produce a valid output
   when active. Output is computed via PID control of speed error.

   **TLA+ Property:**
      ``AlwaysProducesOutput == [](active => output_computed)``


Lane Change Requirements
------------------------

.. spec:: Lane Change State Machine
   :id: SPEC-LC-001
   :status: approved
   :derives_from: REQ-SAFE-002
   :upstream_source: selfdrive/controls/lib/desire_helper.py
   :verification_method: formal

   Lane change shall follow a defined state machine:

   - **OFF**: No lane change active
   - **PRE_LANE_CHANGE**: Preparing for lane change
   - **LANE_CHANGE_STARTING**: Lane change initiated
   - **LANE_CHANGE_FINISHING**: Lane change completing

   **TLA+ Model:**
      ``formal/tla/LaneChange.tla``


.. spec:: Lane Change Requires Desire
   :id: SPEC-LC-002
   :status: approved
   :derives_from: REQ-SAFE-001
   :upstream_source: selfdrive/controls/lib/desire_helper.py
   :verification_method: formal

   Lane change shall only initiate when the driver explicitly indicates
   desire via turn signal activation.

   **Rationale:**
      Prevents unintended lane changes. Driver must explicitly request.

   **TLA+ Property:**
      ``LaneChangeRequiresDesire == [](state' = LANE_CHANGE_STARTING => desire # NONE)``


.. spec:: Complete Before New Lane Change
   :id: SPEC-LC-003
   :status: approved
   :derives_from: REQ-SAFE-002
   :upstream_source: selfdrive/controls/lib/desire_helper.py
   :verification_method: formal

   A lane change must complete or abort before a new lane change
   can be initiated.

   **Rationale:**
      Prevents oscillation between lanes, ensures stable trajectory.


Excessive Actuation Requirements
--------------------------------

.. spec:: Excessive Actuation Detection
   :id: SPEC-ACT-001
   :status: approved
   :derives_from: REQ-SAFE-002, REQ-FORK-002
   :upstream_source: selfdrive/selfdrived/helpers.py
   :verification_method: formal

   The system shall detect when actuation commands exceed safe thresholds
   for consecutive frames and trigger an alert.

   **Implementation:**
      Counter increments when torque exceeds threshold, resets when below.
      Alert triggered when counter reaches MAX_CONSECUTIVE_ACTUATIONS.

   **TLA+ Model:**
      ``formal/tla/ExcessiveActuation.tla``


.. spec:: Excessive Counter Bounded
   :id: SPEC-ACT-002
   :status: approved
   :derives_from: REQ-SAFE-002
   :upstream_source: selfdrive/selfdrived/helpers.py
   :verification_method: formal

   The excessive actuation counter shall be bounded:

   - Minimum: 0
   - Maximum: MAX_CONSECUTIVE_ACTUATIONS + 1

   **TLA+ Property:**
      ``CounterBounded == [](excessive_counter >= 0 /\ excessive_counter <= MAX + 1)``


.. spec:: Actuation Threshold Based on Physics
   :id: SPEC-ACT-003
   :status: approved
   :derives_from: REQ-SAFE-002
   :upstream_source: selfdrive/selfdrived/helpers.py
   :standard: ISO11270
   :verification_method: analysis

   Actuation thresholds are derived from vehicle physics to ensure
   lateral deviation stays within safe bounds.

   **Standard Reference:**
      ISO11270 specifies 0.9 seconds maximum actuation for 1m lateral deviation.

   **Implementation:**
      ``torque_from_lateral_accel_linear()`` converts lateral acceleration
      to expected torque for comparison.


Traceability to Safety Requirements
-----------------------------------

.. list-table:: Control Requirements Traceability
   :header-rows: 1
   :widths: 20 20 60

   * - Spec ID
     - Traces To
     - Description
   * - SPEC-LONG-001
     - REQ-SAFE-002
     - Bounded acceleration prevents sudden trajectory changes
   * - SPEC-LONG-002
     - REQ-SAFE-002
     - Jerk limiting ensures smooth motion
   * - SPEC-LC-001
     - REQ-SAFE-002
     - Defined state machine ensures predictable behavior
   * - SPEC-LC-002
     - REQ-SAFE-001
     - Driver intent required prevents unwanted lane changes
   * - SPEC-ACT-001
     - REQ-SAFE-002, REQ-FORK-002
     - Excessive actuation detection is safety-critical
   * - SPEC-ACT-003
     - REQ-SAFE-002
     - Physics-based thresholds from ISO11270
