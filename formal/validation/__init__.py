"""
Formal model validation using MARL and other advanced techniques.

This package provides tools for validating that TLA+ formal specifications
align with the actual Python implementation using:

1. Gym environments for both reference models and real implementations
2. Random and coverage-guided testing
3. Bisimulation equivalence checking
4. RL-based adversarial testing (finds divergences)

Results are stored in .local/validation_results/ (gitignored).
Source code is version controlled.

Usage:
    # Run full validation
    python -m formal.validation.run_validation

    # Validate specific model
    python -m formal.validation.run_validation --model state_machine --method coverage

    # Use in code
    from formal.validation import StateMachineEnv, BisimulationChecker
"""

from .env_state_machine import (
    StateMachineEnv,
    StateMachineReference,
    BisimulationChecker,
    State,
    EventType,
    Events,
)

from .env_long_control import (
    LongControlEnv,
    LongControlReference,
    LongCtrlState,
    LongControlInputs,
)

from .marl_validator import (
    AdversarialValidator,
    StateSpaceExplorer,
    ValidationResult,
    save_results,
    RESULTS_DIR,
)

from .visualize import (
    StateTransitionVisualizer,
    ValidationResultsVisualizer,
    generate_all_visualizations,
)

__all__ = [
    # State Machine
    "StateMachineEnv",
    "StateMachineReference",
    "BisimulationChecker",
    "State",
    "EventType",
    "Events",
    # Long Control
    "LongControlEnv",
    "LongControlReference",
    "LongCtrlState",
    "LongControlInputs",
    # Validation
    "AdversarialValidator",
    "StateSpaceExplorer",
    "ValidationResult",
    "save_results",
    "RESULTS_DIR",
    # Visualization
    "StateTransitionVisualizer",
    "ValidationResultsVisualizer",
    "generate_all_visualizations",
]
