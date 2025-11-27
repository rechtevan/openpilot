Formal Verification Matrix
==========================

This document links formal verification artifacts to requirements and specifications.

.. note::

   **Verification Methods:**

   - **formal**: TLA+/SPIN model checking (exhaustive state exploration)
   - **test**: Python unit/integration tests
   - **analysis**: Manual code review and analysis
   - **static_analysis**: MISRA/linting tools


TLA+ Formal Models
------------------

StateMachine Model
^^^^^^^^^^^^^^^^^^

.. verify:: StateMachine TLA+ Model
   :id: VER-FV-001
   :status: verified
   :verifies: SPEC-SM-001, SPEC-SM-002, SPEC-SM-003, SPEC-SM-004, SPEC-SM-005, SPEC-SM-006
   :verification_method: formal
   :upstream_source: formal/tla/StateMachine.tla

   TLA+ formal model of the engagement state machine.

   **File:** ``formal/tla/StateMachine.tla``

   **Verification Results:**

   - TLC model checker: PASSED
   - States explored: 2,000,000+
   - Distinct states: 83,328
   - No property violations

   **Properties Verified:**

   - TypeInvariant: All variables in valid domains
   - StateInvariant: Valid state transitions only
   - SafetyInvariant: Priority rules enforced
   - SoftDisableTimerBounded: Timer stays in [0, 300]

   **Bisimulation Validation:**

   Validated against Python implementation (``selfdrive/selfdrived/state.py``):

   - Random traces: 100,000 - 0 divergences
   - Coverage-guided: 10,000 - 0 divergences
   - RL adversarial: 5,000 - 0 divergences

   **GitHub Issue:** `#40 <https://github.com/rechtevan/openpilot/issues/40>`_


LongControl Model
^^^^^^^^^^^^^^^^^

.. verify:: LongControl TLA+ Model
   :id: VER-FV-002
   :status: verified
   :verifies: SPEC-LONG-001, SPEC-LONG-003
   :verification_method: formal
   :upstream_source: formal/tla/LongControl.tla

   TLA+ formal model of longitudinal control.

   **File:** ``formal/tla/LongControl.tla``

   **Verification Results:**

   - TLC model checker: PASSED (partial - large state space)
   - States explored: 436,000,000+
   - No property violations

   **Properties Verified:**

   - TypeInvariant: Variables in valid domains
   - AccelBounded: Output in [-4, 2.5] m/s²
   - AlwaysProducesOutput: Controller always computes output

   **GitHub Issue:** `#41 <https://github.com/rechtevan/openpilot/issues/41>`_


LaneChange Model
^^^^^^^^^^^^^^^^

.. verify:: LaneChange TLA+ Model
   :id: VER-FV-003
   :status: verified
   :verifies: SPEC-LC-001, SPEC-LC-002, SPEC-LC-003
   :verification_method: formal
   :upstream_source: formal/tla/LaneChange.tla

   TLA+ formal model of lane change state machine.

   **File:** ``formal/tla/LaneChange.tla``

   **Verification Results:**

   - TLC model checker: PASSED (partial - large state space)
   - States explored: 244,000,000+
   - Distinct states: 40,000,000+
   - No property violations

   **Properties Verified:**

   - TypeInvariant: Valid state/direction combinations
   - LaneChangeRequiresDesire: Must have explicit desire
   - NoSameLaneChange: Cannot change to same lane

   **GitHub Issue:** `#42 <https://github.com/rechtevan/openpilot/issues/42>`_


ExcessiveActuation Model
^^^^^^^^^^^^^^^^^^^^^^^^

.. verify:: ExcessiveActuation TLA+ Model
   :id: VER-FV-004
   :status: verified
   :verifies: SPEC-ACT-001, SPEC-ACT-002
   :verification_method: formal
   :upstream_source: formal/tla/ExcessiveActuation.tla

   TLA+ formal model of excessive actuation detection.

   **File:** ``formal/tla/ExcessiveActuation.tla``

   **Verification Results:**

   - TLC model checker: PASSED
   - States explored: 26,200,000
   - Full state space coverage
   - No property violations

   **Properties Verified:**

   - TypeInvariant: Counter and flags in valid domains
   - CounterBounded: Counter in [0, MAX+1]
   - ExcessiveOnlyWhenTriggered: Flag only set at threshold

   **GitHub Issue:** `#44 <https://github.com/rechtevan/openpilot/issues/44>`_


SPIN Models
-----------

.. verify:: Messaging Protocol SPIN Model
   :id: VER-FV-005
   :status: verified
   :verifies: REQ-SAFE-001
   :verification_method: formal
   :upstream_source: formal/spin/messaging.pml

   SPIN/Promela model of inter-process messaging protocol.

   **File:** ``formal/spin/messaging.pml``

   **Properties Verified:**

   - No deadlocks
   - Message delivery guarantees
   - Process synchronization

   **GitHub Issue:** `#43 <https://github.com/rechtevan/openpilot/issues/43>`_


.. verify:: Panda Safety Protocol SPIN Model
   :id: VER-FV-006
   :status: verified
   :verifies: REQ-SAFE-001, REQ-SAFE-002
   :verification_method: formal
   :upstream_source: formal/spin/panda.pml

   SPIN/Promela model of panda safety mode transitions.

   **File:** ``formal/spin/panda.pml``

   **Properties Verified:**

   - Safety mode transitions
   - Heartbeat timeout handling
   - CAN message filtering

   **GitHub Issue:** `#45 <https://github.com/rechtevan/openpilot/issues/45>`_


Verification Coverage Summary
-----------------------------

.. needtable::
   :types: verify
   :style: table
   :columns: id, title, status, verifies


Requirements Coverage
^^^^^^^^^^^^^^^^^^^^^

.. list-table:: Requirements to Verification Mapping
   :header-rows: 1
   :widths: 20 20 20 40

   * - Requirement
     - Specification
     - Verification
     - Status
   * - REQ-SAFE-001
     - SPEC-SM-002, SPEC-SM-003
     - VER-FV-001
     - Verified
   * - REQ-SAFE-002
     - SPEC-SM-004, SPEC-LONG-001
     - VER-FV-001, VER-FV-002
     - Verified
   * - REQ-FORK-002
     - SPEC-ACT-001
     - VER-FV-004
     - Verified


Verification Tools
------------------

TLA+ Toolchain
^^^^^^^^^^^^^^

- **TLC Model Checker**: Exhaustive state space exploration
- **Version**: TLA+ Toolbox 1.7.1 / TLC 2.20
- **Configuration**: ``formal/tla/*.cfg`` files

SPIN Toolchain
^^^^^^^^^^^^^^

- **SPIN Model Checker**: LTL model checking for concurrent systems
- **Version**: SPIN 6.5.2
- **Configuration**: Generated verifiers compiled with gcc

Validation Framework
^^^^^^^^^^^^^^^^^^^^

- **Location**: ``formal/validation/``
- **Methods**: Random, coverage-guided, RL adversarial, Hypothesis
- **Documentation**: ``formal/validation/TESTING_METHODS_GUIDE.md``
- **GitHub Issue:** `#46 <https://github.com/rechtevan/openpilot/issues/46>`_
