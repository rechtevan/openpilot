#!/usr/bin/env python3
"""CI validation script for formal verification.

This script runs both bisimulation and coverage-guided validation,
exiting with non-zero status if divergences are found.
"""
import sys


def run_bisimulation_validation():
    """Run bisimulation check between reference model and implementation."""
    from marl_validator import AdversarialValidator
    from env_state_machine import StateMachineReference, create_openpilot_env, BisimulationChecker

    print("=== Running bisimulation validation ===")

    # Create reference and implementation
    ref = StateMachineReference()
    impl = create_openpilot_env()

    # Run bisimulation check
    checker = BisimulationChecker(ref, impl)
    equivalent = checker.check_equivalence(num_traces=10000, seed=42)

    if not equivalent:
        print("DIVERGENCES FOUND:")
        for d in checker.get_divergences()[:5]:
            print(f'  Step {d["step"]}: {d["state_a"]} != {d["state_b"]}')
        return False
    else:
        print("Bisimulation check PASSED: 10,000 traces, 0 divergences")
        return True


def run_coverage_validation():
    """Run coverage-guided validation."""
    from marl_validator import AdversarialValidator
    from env_state_machine import StateMachineReference, create_openpilot_env

    print("\n=== Running coverage-guided validation ===")

    validator = AdversarialValidator(
        reference_factory=StateMachineReference,
        implementation_factory=create_openpilot_env,
        seed=42
    )
    result = validator.validate_coverage_guided(num_traces=5000)

    print(f"Coverage-guided validation:")
    print(f"  Traces: {result.num_traces}")
    print(f"  States covered: {len(result.coverage)}")
    print(f"  Divergences: {result.divergences_found}")

    return result.divergences_found == 0


def main():
    """Run all validation checks."""
    bisim_ok = run_bisimulation_validation()
    coverage_ok = run_coverage_validation()

    if bisim_ok and coverage_ok:
        print("\n=== All validations PASSED ===")
        return 0
    else:
        print("\n=== Validation FAILED ===")
        return 1


if __name__ == "__main__":
    sys.exit(main())
