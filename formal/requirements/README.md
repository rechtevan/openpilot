# Requirements Traceability (Sphinx-Needs)

Formal requirements traceability for openpilot using [sphinx-needs](https://sphinx-needs.readthedocs.io/).

## Design Principles

### Upstream Source Tracking

This requirements layer **references but does not modify** upstream comma.ai documentation. When upstream updates their docs, we update our derived requirements to maintain alignment.

```
┌─────────────────────────────────────────────────────────┐
│  UPSTREAM (comma.ai)                                    │
│  └── docs/SAFETY.md (source of truth)                   │
│      └── docs/LIMITATIONS.md                            │
│          └── selfdrive/selfdrived/state.py              │
└─────────────────────────────────────────────────────────┘
                          │
                          ▼ (derives from)
┌─────────────────────────────────────────────────────────┐
│  THIS LAYER (rechtevan/openpilot)                       │
│  └── formal/requirements/ (traceability)                │
│      ├── REQ-* (requirements from upstream)             │
│      ├── SPEC-* (specifications)                        │
│      └── VER-* (verification artifacts)                 │
└─────────────────────────────────────────────────────────┘
                          │
                          ▼ (verifies)
┌─────────────────────────────────────────────────────────┐
│  FORMAL VERIFICATION                                    │
│  └── formal/tla/*.tla (TLA+ models)                     │
│      └── formal/spin/*.pml (SPIN models)                │
│          └── formal/validation/ (test framework)        │
└─────────────────────────────────────────────────────────┘
```

## Quick Start

### Install Dependencies

```bash
pip install -r requirements.txt
```

### Build Documentation

```bash
cd formal/requirements
sphinx-build -b html . _build/html
```

### View Documentation

```bash
open _build/html/index.html  # macOS
xdg-open _build/html/index.html  # Linux
```

## Requirement Types

| Type | Prefix | Description |
|------|--------|-------------|
| `req` | REQ- | Requirements from upstream docs |
| `spec` | SPEC- | Specifications derived from requirements |
| `verify` | VER- | Verification artifacts (TLA+, tests) |
| `test` | TEST- | Test cases |
| `impl` | IMPL- | Implementation references |

## File Structure

```
requirements/
├── conf.py                        # Sphinx configuration
├── index.rst                      # Main documentation entry
├── safety_requirements.rst        # REQ-SAFE-* from SAFETY.md
├── state_machine_requirements.rst # SPEC-SM-* for state machine
├── control_requirements.rst       # SPEC-LONG-*, SPEC-LC-*, SPEC-ACT-*
├── verification_matrix.rst        # VER-FV-* linking to TLA+
├── traceability_matrix.rst        # Full traceability view
├── formal_verification_coverage.rst # Coverage analysis
├── requirements.txt               # Python dependencies
└── README.md                      # This file
```

## Keeping in Sync with Upstream

When comma.ai updates their documentation:

1. **Check for changes:**
   ```bash
   git fetch upstream
   git diff upstream/master -- docs/SAFETY.md
   ```

2. **Review impact:**
   - New requirements? Add REQ-* items
   - Changed requirements? Update quotes and specs
   - Removed requirements? Mark as deprecated

3. **Update traceability:**
   - Update `upstream_source` and `upstream_section` fields
   - Verify SPEC-* items still align
   - Re-run formal verification if needed

4. **Update sync status:**
   - Update date in `traceability_matrix.rst`
   - Note upstream commit hash

## Example Requirement

```rst
.. req:: Driver Override Capability
   :id: REQ-SAFE-001
   :status: approved
   :upstream_source: docs/SAFETY.md
   :upstream_section: Safety Requirements #1
   :standard: ISO26262, FMVSS
   :priority: critical
   :verification_method: formal, test

   The driver must always be capable to immediately retake manual control
   of the vehicle.

   **Upstream Quote:**
      "The driver must always be capable to immediately retake manual control
      of the vehicle, by stepping on the brake pedal or by pressing the cancel button."
```

## Traceability Links

Requirements support these link types:

- `derives_from` / `derived_by` - REQ → SPEC
- `verifies` / `verified_by` - VER → SPEC
- `implements` / `implemented_by` - IMPL → SPEC
- `tests` / `tested_by` - TEST → SPEC
- `traces_to` / `traced_from` - Generic tracing

## Integration with CI/CD

Add to your CI pipeline:

```yaml
- name: Build Requirements Docs
  run: |
    pip install -r formal/requirements/requirements.txt
    cd formal/requirements
    sphinx-build -W -b html . _build/html

- name: Check Traceability
  run: |
    cd formal/requirements
    sphinx-build -b needs . _build/needs
    # Check for orphan requirements
```

## Related Issues

- [#40](https://github.com/rechtevan/openpilot/issues/40) - StateMachine TLA+
- [#41](https://github.com/rechtevan/openpilot/issues/41) - LongControl TLA+
- [#42](https://github.com/rechtevan/openpilot/issues/42) - LaneChange TLA+
- [#44](https://github.com/rechtevan/openpilot/issues/44) - ExcessiveActuation TLA+
- [#46](https://github.com/rechtevan/openpilot/issues/46) - Validation Framework
