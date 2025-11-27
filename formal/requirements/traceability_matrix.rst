Traceability Matrix
===================

Complete bidirectional traceability from upstream requirements through
specifications to verification artifacts.


Full Traceability Chain
-----------------------

.. needflow::
   :types: req, spec, verify
   :show_link_names:


Requirements → Specifications
-----------------------------

.. needtable::
   :types: req
   :style: table
   :columns: id, title, status


Specifications → Verification
-----------------------------

.. needtable::
   :types: spec
   :style: table
   :columns: id, title, derives_from, status


Verification Artifacts
----------------------

.. needtable::
   :types: verify
   :style: table
   :columns: id, title, verifies, status


Upstream Document Sync Status
-----------------------------

This section tracks synchronization with upstream comma.ai documents.

.. list-table:: Upstream Sync Status
   :header-rows: 1
   :widths: 30 20 20 30

   * - Upstream Document
     - Last Synced
     - Upstream Hash
     - Notes
   * - docs/SAFETY.md
     - 2024-11-27
     - (check git log)
     - Core safety requirements
   * - docs/LIMITATIONS.md
     - 2024-11-27
     - (check git log)
     - System limitations
   * - selfdrive/selfdrived/state.py
     - 2024-11-27
     - (check git log)
     - State machine implementation


Update Process
^^^^^^^^^^^^^^

When upstream documents change:

1. Run ``git fetch upstream && git diff upstream/master -- docs/SAFETY.md``
2. Review changes for impact on derived requirements
3. Update affected REQ-* items with new upstream quotes
4. Update SPEC-* items if behavior changes
5. Re-run formal verification if properties change
6. Update this sync status table


Traceability Links Summary
--------------------------

Forward Traceability (Requirements → Implementation)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: text

   REQ-SAFE-001 (Driver Override)
   ├── SPEC-SM-002 (Immediate Disable Priority)
   │   └── VER-FV-001 (StateMachine TLA+ Model)
   ├── SPEC-SM-003 (User Disable Priority)
   │   └── VER-FV-001 (StateMachine TLA+ Model)
   └── SPEC-SM-005 (No Entry Prevents Enable)
       └── VER-FV-001 (StateMachine TLA+ Model)

   REQ-SAFE-002 (Bounded Actuation)
   ├── SPEC-SM-004 (Soft Disable Timer)
   │   └── VER-FV-001 (StateMachine TLA+ Model)
   ├── SPEC-LONG-001 (Acceleration Bounds)
   │   └── VER-FV-002 (LongControl TLA+ Model)
   ├── SPEC-LC-001 (Lane Change State Machine)
   │   └── VER-FV-003 (LaneChange TLA+ Model)
   └── SPEC-ACT-001 (Excessive Actuation Detection)
       └── VER-FV-004 (ExcessiveActuation TLA+ Model)

   REQ-FORK-002 (Preserve Excessive Actuation)
   └── SPEC-ACT-001 (Excessive Actuation Detection)
       └── VER-FV-004 (ExcessiveActuation TLA+ Model)


Backward Traceability (Implementation → Requirements)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: text

   VER-FV-001 (StateMachine TLA+ Model)
   └── Verifies: SPEC-SM-001 through SPEC-SM-006
       └── Derives from: REQ-SAFE-001, REQ-SAFE-002

   VER-FV-002 (LongControl TLA+ Model)
   └── Verifies: SPEC-LONG-001, SPEC-LONG-003
       └── Derives from: REQ-SAFE-002

   VER-FV-003 (LaneChange TLA+ Model)
   └── Verifies: SPEC-LC-001, SPEC-LC-002, SPEC-LC-003
       └── Derives from: REQ-SAFE-001, REQ-SAFE-002

   VER-FV-004 (ExcessiveActuation TLA+ Model)
   └── Verifies: SPEC-ACT-001, SPEC-ACT-002
       └── Derives from: REQ-SAFE-002, REQ-FORK-002


Coverage Gaps
-------------

Requirements without formal verification:

.. list-table:: Uncovered Requirements
   :header-rows: 1
   :widths: 20 40 40

   * - Requirement
     - Description
     - Coverage Plan
   * - REQ-SAFE-003
     - Driver Monitoring Required
     - Test coverage only (ML-based)
   * - REQ-FORK-001
     - Preserve Driver Monitoring
     - Code review
   * - REQ-FORK-003
     - Preserve Safety Test Suite
     - CI/CD checks
   * - REQ-STD-001
     - ISO26262 Compliance
     - Process/documentation
   * - REQ-STD-002
     - MISRA C Compliance
     - Static analysis (clang-tidy)
