openpilot Requirements Traceability
===================================

This documentation provides formal requirements traceability for openpilot,
linking upstream requirements from comma.ai to our formal verification artifacts.

.. note::

   **Upstream Source Tracking**

   Requirements in this document are derived from upstream comma.ai documentation.
   When upstream documents are updated, this traceability layer should be updated
   to maintain alignment. The upstream documents remain the source of truth.

   Key upstream sources:

   - ``docs/SAFETY.md`` - Safety requirements and principles
   - ``docs/LIMITATIONS.md`` - System limitations
   - ``panda/`` - Hardware safety model
   - ``opendbc/safety/`` - Vehicle safety implementations


Contents
--------

.. toctree::
   :maxdepth: 2
   :caption: Requirements:

   safety_requirements
   state_machine_requirements
   control_requirements
   verification_matrix

.. toctree::
   :maxdepth: 2
   :caption: Traceability:

   traceability_matrix
   formal_verification_coverage


Requirement Statistics
----------------------

.. needtable::
   :types: req
   :style: table
   :columns: id, title, status, verification_method


Verification Coverage
---------------------

.. needflow::
   :types: req, spec, verify, test
   :show_link_names:
