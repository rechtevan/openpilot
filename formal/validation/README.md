# Formal Model Validation

This package validates TLA+ formal specifications against actual Python implementations using advanced techniques including MARL (Multi-Agent Reinforcement Learning).

**Educational Resource**: See [TESTING_METHODS_GUIDE.md](TESTING_METHODS_GUIDE.md) for a comprehensive comparison of testing approaches for safety-critical AI systems.

## Overview

The validation framework provides:

1. **Gym Environments** - Wrap both reference models (from TLA+ specs) and real implementations
2. **Bisimulation Checking** - Verify behavioral equivalence between models
3. **Coverage-Guided Testing** - Prioritize inputs that increase state/transition coverage
4. **RL Adversarial Testing** - Train agents to find divergences between implementations
5. **AI Boundary Testing** - Validate control logic handles adversarial AI outputs

## Quick Start

```bash
# Run full validation suite
python run_validation.py

# Validate specific model with specific method
python run_validation.py --model state_machine --method coverage --traces 10000

# Explore state space
python run_validation.py --method explore
```

## Validation Methods

| Method | Description | Use Case |
|--------|-------------|----------|
| `random` | Random input sequences | Baseline validation |
| `coverage` | Coverage-guided fuzzing | Find edge cases |
| `rl` | RL adversarial policy | Find subtle bugs |
| `bisim` | Bisimulation checking | Formal equivalence |
| `explore` | State space exploration | Coverage analysis |

## Architecture

```
validation/
├── env_state_machine.py      # StateMachine gym environment
├── env_long_control.py       # LongControl gym environment
├── real_state_machine.py     # Standalone impl for validation
├── marl_validator.py         # MARL-based validation
├── advanced_validator.py     # Hypothesis + coverage methods
├── ai_boundary_validator.py  # AI-to-control boundary testing
├── visualize.py              # Generate visualizations
├── run_validation.py         # CLI entry point
├── TESTING_METHODS_GUIDE.md  # Educational documentation
└── README.md
```

## Results Storage

All results are stored in `.local/validation_results/` which is gitignored.
Only source code is version controlled.

Results include:
- Divergence traces
- Coverage statistics
- Timing information
- Reproducibility data (seeds)

## Adding New Models

1. Create `env_<model>.py` with:
   - Reference implementation (matching TLA+ spec)
   - Gym environment wrapper
   - Factory function for real implementation

2. Add validation logic to `run_validation.py`

3. Update `__init__.py` exports

## Requirements

- Python 3.8+
- numpy
- gymnasium

Optional (for RL methods):
- torch

## Example: Validating StateMachine

```python
from formal.validation import (
    StateMachineReference,
    BisimulationChecker,
    create_openpilot_env
)

# Create reference and implementation
ref = StateMachineReference()
impl = create_openpilot_env()

# Check bisimulation equivalence
checker = BisimulationChecker(ref, impl)
equivalent = checker.check_equivalence(num_traces=10000)

if not equivalent:
    print("Divergences found:")
    for d in checker.get_divergences():
        print(f"  {d}")
```

## Theory

### Bisimulation Equivalence

Two systems S1 and S2 are bisimilar if:
1. They start in equivalent states
2. For any action, if S1 transitions to s1', there exists s2' such that S2 transitions to s2' and s1' ~ s2'

### Adversarial RL

The adversary learns a policy π(a|s) that maximizes:
```
J(π) = E[Σ r_t | divergence found]
```

This finds input sequences that expose implementation bugs.

### Coverage-Guided Fuzzing

Prioritizes inputs that:
1. Visit new states
2. Exercise new transitions
3. Increase code coverage

Similar to AFL/libFuzzer but for state machines.

## AI Boundary Testing

For systems where AI feeds into deterministic control logic:

```bash
# Run AI boundary validation
python ai_boundary_validator.py
```

This tests how control logic handles:
- **Random**: Baseline random AI outputs
- **Boundary probing**: Threshold edge cases
- **Distribution drift**: Gradual AI degradation
- **Oscillation**: Rapid confidence changes
- **Out-of-distribution**: Worst-case AI behavior

### Key Insight

The control layer must be safe regardless of what the AI produces:

```
AI OUTPUT → [VALIDATION] → CONTROL EVENTS → SAFE BEHAVIOR
              ↑
         Test here!
```

## Benchmark Results

From our validation runs:

| Method | Speed | Best For |
|--------|-------|----------|
| Random | 6,340/sec | CI/CD, baseline |
| Boundary | 520/sec | Threshold testing |
| Coverage-guided | 520/sec | Code path coverage |
| RL Adversarial | 30/sec | Complex edge cases |
| Hypothesis | 18/sec | Minimal failing examples |

See [TESTING_METHODS_GUIDE.md](TESTING_METHODS_GUIDE.md) for detailed comparison.
