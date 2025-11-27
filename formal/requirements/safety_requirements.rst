Safety Requirements
===================

This document captures safety requirements derived from upstream openpilot documentation.
Each requirement traces back to specific sections in comma.ai's documentation.

.. note::

   **Upstream Source:** ``docs/SAFETY.md``

   Last synchronized: 2024-11-27

   These requirements are derived from comma.ai's safety documentation.
   When upstream updates occur, review and update these derived requirements.


High-Level Safety Principles
----------------------------

These are the foundational safety requirements stated in upstream SAFETY.md.

.. req:: Driver Override Capability
   :id: REQ-SAFE-001
   :status: approved
   :upstream_source: docs/SAFETY.md
   :upstream_section: Safety Requirements #1
   :standard: ISO26262, FMVSS
   :priority: critical
   :verification_method: formal, test

   The driver must always be capable to immediately retake manual control
   of the vehicle, by stepping on the brake pedal or by pressing the
   cancel button.

   **Upstream Quote:**
      "The driver must always be capable to immediately retake manual control
      of the vehicle, by stepping on the brake pedal or by pressing the cancel button."

   **Verification:**
      - Formal: TLA+ StateMachine model verifies USER_DISABLE always transitions to DISABLED
      - Test: ``selfdrive/selfdrived/tests/test_state_machine.py``


.. req:: Bounded Actuation Rate
   :id: REQ-SAFE-002
   :status: approved
   :upstream_source: docs/SAFETY.md
   :upstream_section: Safety Requirements #2
   :standard: ISO11270, ISO15622
   :priority: critical
   :verification_method: formal, test

   The vehicle must not alter its trajectory too quickly for the driver
   to safely react. While the system is engaged, actuators are constrained
   to operate within reasonable limits.

   **Upstream Quote:**
      "The vehicle must not alter its trajectory too quickly for the driver to safely
      react. This means that while the system is engaged, the actuators are constrained
      to operate within reasonable limits."

   **Standard Reference:**
      ISO11270 and ISO15622 specify lateral limits that translate to 0.9 seconds
      of maximum actuation to achieve a 1m lateral deviation.

   **Verification:**
      - Formal: TLA+ ExcessiveActuation model
      - Formal: TLA+ LongControl model (accel bounds)
      - Test: panda safety tests


.. req:: Driver Monitoring Required
   :id: REQ-SAFE-003
   :status: approved
   :upstream_source: docs/SAFETY.md
   :upstream_section: Driver Alertness
   :standard: ISO26262
   :priority: critical
   :verification_method: test

   openpilot includes a driver monitoring feature that alerts the driver
   when distracted. Driver alertness is necessary (but not sufficient)
   for safe operation.

   **Upstream Quote:**
      "In order to enforce driver alertness, openpilot includes a driver monitoring
      feature that alerts the driver when distracted."

   **Note:** Driver monitoring is explicitly called out as must-not-disable for forks.


Fork Safety Requirements
------------------------

Requirements for forks derived from upstream SAFETY.md "Forks of openpilot" section.

.. req:: Preserve Driver Monitoring
   :id: REQ-FORK-001
   :status: approved
   :upstream_source: docs/SAFETY.md
   :upstream_section: Forks of openpilot
   :priority: critical
   :verification_method: review

   Forks must not disable or nerf driver monitoring.

   **Upstream Quote:**
      "Do not disable or nerf driver monitoring"

   **Implementation:**
      ``selfdrive/monitoring/``


.. req:: Preserve Excessive Actuation Checks
   :id: REQ-FORK-002
   :status: approved
   :upstream_source: docs/SAFETY.md
   :upstream_section: Forks of openpilot
   :priority: critical
   :verification_method: formal, test

   Forks must not disable or nerf excessive actuation checks.

   **Upstream Quote:**
      "Do not disable or nerf excessive actuation checks"

   **Implementation:**
      ``selfdrive/selfdrived/helpers.py``

   **Verification:**
      - Formal: TLA+ ExcessiveActuation model (VER-FV-003)


.. req:: Preserve Safety Test Suite
   :id: REQ-FORK-003
   :status: approved
   :upstream_source: docs/SAFETY.md
   :upstream_section: Forks of openpilot
   :priority: critical
   :verification_method: test

   If a fork modifies safety code in ``opendbc/safety/``, it must preserve
   the full safety test suite and all tests must pass.

   **Upstream Quote:**
      "your fork must preserve the full safety test suite and all tests must pass,
      including any new coverage required by the fork's changes"


Standards Compliance Requirements
---------------------------------

.. req:: ISO26262 Compliance
   :id: REQ-STD-001
   :status: approved
   :upstream_source: docs/SAFETY.md
   :upstream_section: Standards
   :standard: ISO26262
   :priority: high
   :verification_method: analysis

   openpilot follows ISO26262 guidelines for functional safety in
   automotive systems.

   **Upstream Quote:**
      "openpilot is developed in good faith to be compliant with FMVSS requirements
      and to follow industry standards of safety for Level 2 Driver Assistance Systems.
      In particular, we observe ISO26262 guidelines"


.. req:: MISRA C Compliance for Safety Code
   :id: REQ-STD-002
   :status: approved
   :upstream_source: docs/SAFETY.md
   :upstream_section: Standards
   :standard: MISRA C:2012
   :priority: high
   :verification_method: static_analysis

   Safety-relevant code follows MISRA C:2012 coding guidelines.

   **Upstream Quote:**
      "we impose strict coding guidelines (like MISRA C : 2012) on parts of
      openpilot that are safety relevant"

   **Scope:**
      Primarily applies to panda firmware and safety-critical C/C++ code.


Traceability to Upstream
------------------------

.. list-table:: Upstream Document Mapping
   :header-rows: 1
   :widths: 20 40 40

   * - Requirement ID
     - Upstream Source
     - Upstream Section
   * - REQ-SAFE-001
     - docs/SAFETY.md
     - Safety Requirements #1
   * - REQ-SAFE-002
     - docs/SAFETY.md
     - Safety Requirements #2
   * - REQ-SAFE-003
     - docs/SAFETY.md
     - Driver Alertness
   * - REQ-FORK-001
     - docs/SAFETY.md
     - Forks of openpilot
   * - REQ-FORK-002
     - docs/SAFETY.md
     - Forks of openpilot
   * - REQ-FORK-003
     - docs/SAFETY.md
     - Forks of openpilot
   * - REQ-STD-001
     - docs/SAFETY.md
     - Standards
   * - REQ-STD-002
     - docs/SAFETY.md
     - Standards
