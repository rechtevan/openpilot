State Machine Requirements
==========================

Requirements for the primary engagement state machine (selfdrived).

.. note::

   **Upstream Source:** ``selfdrive/selfdrived/state.py``

   These requirements are derived from analyzing the state machine implementation
   and its safety properties. They trace to high-level safety requirements.


State Machine Specifications
----------------------------

.. spec:: State Machine States
   :id: SPEC-SM-001
   :status: approved
   :derives_from: REQ-SAFE-001
   :upstream_source: selfdrive/selfdrived/state.py
   :verification_method: formal

   The engagement state machine shall have exactly five states:

   - **DISABLED**: System is not engaged, no actuation
   - **PRE_ENABLED**: Transitional state before engagement
   - **ENABLED**: System is actively controlling the vehicle
   - **SOFT_DISABLING**: Graceful disengagement in progress (3 second timer)
   - **OVERRIDING**: Driver is temporarily overriding control

   **TLA+ Formalization:**
      ``State \in {DISABLED, PRE_ENABLED, ENABLED, SOFT_DISABLING, OVERRIDING}``


.. spec:: Immediate Disable Priority
   :id: SPEC-SM-002
   :status: approved
   :derives_from: REQ-SAFE-001
   :upstream_source: selfdrive/selfdrived/state.py
   :verification_method: formal

   IMMEDIATE_DISABLE events shall always take priority and transition
   the system to DISABLED from any non-disabled state.

   **Rationale:**
      Critical safety events (e.g., sensor failure, panda disconnect) must
      immediately disable the system regardless of current state.

   **TLA+ Property:**
      ``ImmediateDisablePriority == [](events.immediate_disable /\ state # DISABLED => state' = DISABLED)``


.. spec:: User Disable Priority
   :id: SPEC-SM-003
   :status: approved
   :derives_from: REQ-SAFE-001
   :upstream_source: selfdrive/selfdrived/state.py
   :verification_method: formal

   USER_DISABLE events (brake pedal, cancel button) shall take priority
   over all events except IMMEDIATE_DISABLE, transitioning to DISABLED.

   **Rationale:**
      Driver must always be able to retake control immediately.

   **TLA+ Property:**
      ``UserDisablePriority == [](events.user_disable /\ state # DISABLED => state' = DISABLED)``


.. spec:: Soft Disable Timer
   :id: SPEC-SM-004
   :status: approved
   :derives_from: REQ-SAFE-002
   :upstream_source: selfdrive/selfdrived/state.py
   :verification_method: formal

   SOFT_DISABLING state shall have a 3-second countdown timer.
   The system remains in SOFT_DISABLING while alerting the driver,
   then transitions to DISABLED when the timer expires.

   **Rationale:**
      Gradual handoff is safer than abrupt disengagement. Gives driver
      time to retake control.

   **Constants:**
      - SOFT_DISABLE_TIME = 3 seconds
      - DT_CTRL = 0.01 seconds (100 Hz)
      - Timer ticks = 300

   **TLA+ Property:**
      ``SoftDisableTimerBounded == [](soft_disable_timer >= 0 /\ soft_disable_timer <= 300)``


.. spec:: No Entry Prevents Enable
   :id: SPEC-SM-005
   :status: approved
   :derives_from: REQ-SAFE-001
   :upstream_source: selfdrive/selfdrived/state.py
   :verification_method: formal

   When NO_ENTRY events are present, ENABLE events shall not transition
   the system out of DISABLED state.

   **Rationale:**
      NO_ENTRY indicates conditions are not safe for engagement
      (e.g., seatbelt unbuckled, door open).

   **TLA+ Property:**
      ``NoEntryPreventsEnable == [](events.no_entry /\ events.enable /\ state = DISABLED => state' = DISABLED)``


Event Priority Hierarchy
------------------------

.. spec:: Event Priority Order
   :id: SPEC-SM-006
   :status: approved
   :derives_from: REQ-SAFE-001, REQ-SAFE-002
   :upstream_source: selfdrive/selfdrived/state.py
   :verification_method: formal, test

   Events shall be processed in the following priority order (highest first):

   1. **IMMEDIATE_DISABLE** - Critical failures, always processed first
   2. **USER_DISABLE** - Driver-initiated disable (brake/cancel)
   3. **SOFT_DISABLE** - Non-critical issues requiring graceful handoff
   4. **OVERRIDE** - Driver override (steering/gas pedal)
   5. **ENABLE/PRE_ENABLE** - Engagement events
   6. **NO_ENTRY** - Blocks engagement but doesn't disable

   **Implementation:**
      Priority is enforced by the order of if/elif checks in ``state.py``.


State Transition Requirements
-----------------------------

.. spec:: From DISABLED Transitions
   :id: SPEC-SM-010
   :status: approved
   :derives_from: REQ-SAFE-001
   :verification_method: formal

   From DISABLED state, valid transitions are:

   - DISABLED → ENABLED: On ENABLE without NO_ENTRY
   - DISABLED → PRE_ENABLED: On ENABLE + PRE_ENABLE without NO_ENTRY
   - DISABLED → OVERRIDING: On ENABLE + OVERRIDE without NO_ENTRY
   - DISABLED → DISABLED: On NO_ENTRY (stay disabled)


.. spec:: From ENABLED Transitions
   :id: SPEC-SM-011
   :status: approved
   :derives_from: REQ-SAFE-001, REQ-SAFE-002
   :verification_method: formal

   From ENABLED state, valid transitions are:

   - ENABLED → DISABLED: On USER_DISABLE or IMMEDIATE_DISABLE
   - ENABLED → SOFT_DISABLING: On SOFT_DISABLE
   - ENABLED → OVERRIDING: On OVERRIDE_LATERAL or OVERRIDE_LONGITUDINAL


.. spec:: From SOFT_DISABLING Transitions
   :id: SPEC-SM-012
   :status: approved
   :derives_from: REQ-SAFE-002
   :verification_method: formal

   From SOFT_DISABLING state, valid transitions are:

   - SOFT_DISABLING → DISABLED: Timer expires OR USER/IMMEDIATE_DISABLE
   - SOFT_DISABLING → ENABLED: SOFT_DISABLE condition clears


.. spec:: Liveness - Soft Disable Terminates
   :id: SPEC-SM-020
   :status: approved
   :derives_from: REQ-SAFE-002
   :verification_method: formal

   If the system enters SOFT_DISABLING state, it shall eventually
   exit to either DISABLED or ENABLED within a bounded time.

   **TLA+ Property (Liveness):**
      ``SoftDisableTerminates == [](state = SOFT_DISABLING => <>(state # SOFT_DISABLING))``

   **Bound:**
      Maximum 3 seconds (300 ticks at 100 Hz).


Traceability to Safety Requirements
-----------------------------------

.. list-table:: Safety Requirement Traceability
   :header-rows: 1
   :widths: 20 20 60

   * - Spec ID
     - Traces To
     - Description
   * - SPEC-SM-002
     - REQ-SAFE-001
     - Immediate disable ensures driver can retake control
   * - SPEC-SM-003
     - REQ-SAFE-001
     - User disable ensures driver can retake control
   * - SPEC-SM-004
     - REQ-SAFE-002
     - Soft disable timer ensures gradual handoff
   * - SPEC-SM-005
     - REQ-SAFE-001
     - No entry prevents unsafe engagement
   * - SPEC-SM-006
     - REQ-SAFE-001, REQ-SAFE-002
     - Priority hierarchy ensures safety events take precedence
