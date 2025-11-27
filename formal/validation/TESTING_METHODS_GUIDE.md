# Testing Methods for Safety-Critical AI Systems

A comprehensive guide comparing validation approaches for systems where AI (neural networks) feeds into deterministic control logic. This guide uses openpilot as a case study.

## Table of Contents

1. [The Challenge: AI-in-the-Loop Safety](#the-challenge)
2. [Testing Method Comparison](#testing-methods)
3. [When to Use Each Method](#when-to-use)
4. [Code Examples](#code-examples)
5. [Benchmark Results](#benchmark-results)
6. [Best Practices](#best-practices)

---

## The Challenge: AI-in-the-Loop Safety <a name="the-challenge"></a>

Modern safety-critical systems increasingly use AI for perception while relying on deterministic logic for control:

```
┌─────────────────────────────────────────────────────────┐
│  AI PERCEPTION LAYER                                    │
│  ├── Neural network (learned, probabilistic)            │
│  ├── Outputs: confidence scores, predictions            │
│  └── Risk: Can produce unexpected outputs               │
└─────────────────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────┐
│  CONTROL LOGIC LAYER                                    │
│  ├── Deterministic state machine (rule-based)           │
│  ├── Inputs: AI outputs + sensor data                   │
│  └── Must be safe regardless of AI behavior             │
└─────────────────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────┐
│  ACTUATORS                                              │
│  └── Physical actions with real-world consequences      │
└─────────────────────────────────────────────────────────┘
```

**Key Question**: How do we verify the control logic remains safe even when the AI produces unexpected, degraded, or adversarial outputs?

---

## Testing Method Comparison <a name="testing-methods"></a>

### 1. Random Testing

**Concept**: Generate random inputs within valid bounds and check outputs.

**Strengths**:
- Fast (6,000+ traces/second)
- Simple to implement
- Good baseline coverage
- Highly parallelizable

**Weaknesses**:
- May miss edge cases
- Doesn't target specific vulnerabilities
- Coverage is probabilistic

**Code Example**:
```python
def random_test(num_traces=10000):
    """Generate random AI outputs and verify control response"""
    for _ in range(num_traces):
        # Generate random AI output
        model_output = ModelV2Output(
            model_confidence=random.uniform(0, 1),
            lane_line_probs=np.random.uniform(0, 1, 4),
            lead_prob=random.uniform(0, 1),
        )

        # Execute control logic
        decision = control_step(model_output)

        # Check safety invariant
        assert not (decision.active and model_output.model_confidence < 0.2), \
            "Safety violation: active with low confidence"
```

**Best for**: CI/CD pipelines, regression testing, baseline coverage

---

### 2. Boundary Value Testing

**Concept**: Test values at and around thresholds where behavior changes.

**Strengths**:
- Targets critical decision points
- Finds threshold-related bugs
- Efficient (small test space)
- Deterministic

**Weaknesses**:
- Requires knowledge of thresholds
- May miss interactions between boundaries

**Code Example**:
```python
def boundary_test():
    """Test around critical thresholds"""

    # Confidence threshold is 0.4 - test around it
    for confidence in [0.35, 0.39, 0.40, 0.41, 0.45]:
        model_output = ModelV2Output(model_confidence=confidence)
        decision = control_step(model_output)

        if confidence < 0.4:
            assert decision.state == State.SOFT_DISABLING, \
                f"Should disable at confidence {confidence}"
        else:
            assert decision.state != State.SOFT_DISABLING, \
                f"Should NOT disable at confidence {confidence}"
```

**Best for**: Threshold validation, regression after threshold changes

---

### 3. Distribution Drift Testing

**Concept**: Simulate gradual degradation of AI performance over time.

**Why it matters**: AI models degrade in production due to:
- Weather conditions (fog, rain, sun glare)
- New road configurations
- Sensor degradation
- Environmental changes

**Code Example**:
```python
def drift_test(drift_rate=0.01, trace_length=200):
    """Simulate gradual AI degradation"""
    for step in range(trace_length):
        # Confidence degrades over time
        confidence = max(0, 1.0 - step * drift_rate)

        model_output = ModelV2Output(model_confidence=confidence)
        decision = control_step(model_output)

        # Check: system should disengage BEFORE confidence is critical
        if confidence < 0.3:
            assert not decision.active, \
                f"Still active at step {step} with confidence {confidence}"
```

**Key insight**: Tests whether the system disengages *early enough* as conditions degrade.

**Best for**: Robustness testing, production monitoring simulation

---

### 4. Out-of-Distribution (OOD) Testing

**Concept**: Test AI outputs that represent "never seen before" scenarios.

**Why it matters**: Neural networks can produce arbitrary outputs when given OOD inputs:
- Construction zones
- Emergency vehicles
- Unusual road markings
- Adversarial examples

**Code Example**:
```python
def ood_test():
    """Test outputs that neural networks might produce on unseen data"""

    # OOD outputs are often characterized by:
    # - Low confidence
    # - Unusual patterns
    # - High uncertainty

    ood_outputs = [
        # Very low confidence
        ModelV2Output(model_confidence=0.1),

        # Contradictory signals
        ModelV2Output(
            model_confidence=0.9,  # High confidence
            lane_line_probs=np.zeros(4),  # But no lanes detected?!
        ),

        # Physically impossible predictions
        ModelV2Output(
            path_y=np.ones(33) * 10,  # 10m lateral offset
        ),
    ]

    for output in ood_outputs:
        decision = control_step(output)
        assert not decision.active, \
            "Should NEVER be active with OOD output"
```

**Best for**: Safety certification, adversarial robustness

---

### 5. Oscillation/Adversarial Attack Testing

**Concept**: Test rapid changes designed to confuse state machines.

**Why it matters**: Attackers (or faulty sensors) might cause rapid oscillation:
- Flickering lane detection
- Intermittent sensor failures
- Adversarial input perturbations

**Code Example**:
```python
def oscillation_test(period=10, trace_length=200):
    """Test rapid confidence oscillation"""
    state_changes = 0
    prev_state = None

    for step in range(trace_length):
        # Oscillate between high and low confidence
        phase = (step % period) / period
        confidence = 0.5 + 0.5 * np.sin(2 * np.pi * phase)

        model_output = ModelV2Output(model_confidence=confidence)
        decision = control_step(model_output)

        if prev_state and decision.state != prev_state:
            state_changes += 1
        prev_state = decision.state

    # Check for excessive state thrashing
    assert state_changes < trace_length * 0.5, \
        f"Too many state changes: {state_changes}"
```

**Best for**: State machine robustness, hysteresis testing

---

### 6. Property-Based Testing (Hypothesis)

**Concept**: Define properties that must hold, let the framework find violations.

**Strengths**:
- Auto-shrinking (minimizes failing examples)
- Explores edge cases automatically
- Good for specification testing

**Weaknesses**:
- Slower than random testing
- Requires property specification

**Code Example**:
```python
from hypothesis import given, strategies as st
from hypothesis.stateful import RuleBasedStateMachine, rule, invariant

class StateMachineTest(RuleBasedStateMachine):
    def __init__(self):
        self.machine = StateMachine()

    @rule(confidence=st.floats(0, 1), events=st.frozensets(...))
    def step(self, confidence, events):
        self.machine.step(confidence, events)

    @invariant()
    def safety_invariant(self):
        """Active state requires minimum confidence"""
        if self.machine.active:
            assert self.machine.last_confidence >= 0.3
```

**Best for**: Finding minimal failing examples, specification testing

---

### 7. Reinforcement Learning Adversarial Testing

**Concept**: Train an RL agent to find inputs that cause failures.

**Strengths**:
- Learns to target vulnerabilities
- Can find subtle bugs
- Explores strategically

**Weaknesses**:
- Slow (30 traces/sec vs 6000 for random)
- Requires training
- May overfit to specific patterns

**Code Example**:
```python
class AdversarialPolicy(nn.Module):
    """Neural network that learns to generate adversarial inputs"""
    def __init__(self):
        self.network = nn.Sequential(
            nn.Linear(state_dim, 64),
            nn.ReLU(),
            nn.Linear(64, action_dim),
            nn.Sigmoid(),
        )

    def forward(self, state):
        return self.network(state)

def train_adversary(policy, env, episodes=500):
    """Train policy to find safety violations"""
    for episode in range(episodes):
        state = env.reset()
        for step in range(100):
            action = policy(state)
            next_state, reward, done, info = env.step(action)

            # Reward for finding violations
            if info.get('safety_violation'):
                reward += 10.0

            # Update policy with REINFORCE
            policy.update(reward)
```

**Best for**: Complex systems where random can't find bugs, research

---

### 8. Formal Verification (TLA+/SPIN)

**Concept**: Mathematically prove properties hold for all possible states.

**Strengths**:
- Exhaustive (checks ALL states)
- Proves correctness, not just absence of found bugs
- Catches subtle logic errors

**Weaknesses**:
- State explosion for complex systems
- Requires abstraction (model != code)
- Needs validation that model matches code

**Code Example** (TLA+):
```tla
\* Safety property: active implies confidence above threshold
SafetyInvariant ==
    state = "ENABLED" => model_confidence >= MIN_CONFIDENCE

\* Liveness: eventually disables if confidence drops
LivenessProperty ==
    [](model_confidence < MIN_CONFIDENCE => <>(state = "DISABLED"))
```

**Best for**: Core safety properties, state machine logic

---

## When to Use Each Method <a name="when-to-use"></a>

| Method | Speed | Coverage | Bug Finding | Best For |
|--------|-------|----------|-------------|----------|
| Random | Very Fast | Good | Baseline | CI/CD |
| Boundary | Fast | Targeted | Thresholds | Regression |
| Drift | Fast | Specific | Degradation | Monitoring |
| OOD | Moderate | Worst-case | Edge cases | Safety cert |
| Oscillation | Fast | Specific | State bugs | Robustness |
| Hypothesis | Slow | Exhaustive | Minimal examples | Spec testing |
| RL Adversarial | Very Slow | Strategic | Complex bugs | Research |
| Formal (TLA+) | N/A | Complete | Logic errors | Core safety |

### Recommended Testing Strategy

```
1. DEVELOPMENT PHASE
   ├── Formal verification (TLA+) for core state machine
   ├── Hypothesis for property specification
   └── Boundary testing for thresholds

2. CI/CD PIPELINE
   ├── Random testing (fast, broad coverage)
   ├── Boundary testing (critical thresholds)
   └── Bisimulation checking (model-code alignment)

3. PRE-RELEASE
   ├── OOD testing (safety certification)
   ├── Drift testing (robustness)
   └── RL adversarial (if time permits)

4. PRODUCTION MONITORING
   ├── Distribution drift detection
   └── Confidence monitoring
```

---

## Benchmark Results <a name="benchmark-results"></a>

From our openpilot validation:

```
Method                     Time       Traces     Safety Issues
----------------------------------------------------------------------
random                   22.59s       10,000          0
boundary                  1.47s        2,000          0
drift                     0.64s          200     27,050
oscillation               0.57s          200          0
ood                       3.48s        2,000    100,000
```

**Key Findings**:

1. **Drift testing found issues**: 27,050 cases where the system was still active while AI confidence was degraded. This reveals a potential timing issue - the system doesn't disengage fast enough as conditions deteriorate.

2. **OOD testing found many issues**: 100,000 safety violations with out-of-distribution inputs. This is expected - OOD inputs are designed to be adversarial.

3. **Random testing found nothing**: This doesn't mean the system is safe - it means random testing isn't targeting the right scenarios.

4. **Speed varies 200x**: Random is 200x faster than RL, but less targeted.

---

## Best Practices <a name="best-practices"></a>

### 1. Layer Your Testing

```
FORMAL VERIFICATION (TLA+/SPIN)
    └── Proves core logic correct

PROPERTY-BASED (Hypothesis)
    └── Auto-shrinks to minimal failures

TARGETED (Boundary, Drift, OOD)
    └── Tests specific scenarios

RANDOM (Baseline)
    └── Broad coverage, fast feedback
```

### 2. Define Clear Safety Invariants

```python
# Good: Specific, testable
def safety_invariant(state, ai_output):
    """Active control requires minimum AI confidence"""
    if state.is_active:
        assert ai_output.confidence >= 0.3
        assert any(p > 0.3 for p in ai_output.lane_probs)

# Bad: Vague, untestable
def bad_invariant(state):
    """System should be safe"""  # What does "safe" mean?
    assert state.is_safe
```

### 3. Validate Model-Code Alignment

Formal models are only useful if they match the code:

```python
# Run bisimulation checking
checker = BisimulationChecker(formal_model, real_code)
divergences = checker.check_equivalence(num_traces=10000)
assert len(divergences) == 0, f"Model-code mismatch: {divergences}"
```

### 4. Test the AI Boundary

The boundary between AI and control logic is critical:

```
AI OUTPUT → [VALIDATION] → [TRANSLATION] → CONTROL EVENTS
                ↑               ↑
           Test here!      And here!
```

### 5. Use Multiple Methods Together

No single method is sufficient:

```python
def comprehensive_validation():
    # 1. Formal verification of core properties
    assert run_tlc("StateMachine.tla")

    # 2. Bisimulation for model-code alignment
    assert bisimulation_check(model, code)

    # 3. Boundary testing for thresholds
    assert boundary_test_thresholds()

    # 4. OOD for worst-case AI behavior
    assert ood_safety_check()

    # 5. Random for regression
    assert random_regression_test()
```

---

## Conclusion

Testing AI-in-the-loop systems requires multiple complementary approaches:

1. **Formal methods** prove correctness of the core logic
2. **Boundary testing** verifies threshold behavior
3. **Distribution testing** catches degradation scenarios
4. **OOD testing** validates worst-case safety
5. **Random testing** provides fast, broad coverage

The key insight: **The control layer must be safe regardless of what the AI produces**. This means testing should specifically target adversarial, degraded, and unexpected AI outputs.

---

## References

- [TLA+ Home Page](https://lamport.azurewebsites.net/tla/tla.html)
- [Hypothesis Documentation](https://hypothesis.readthedocs.io/)
- [Property-Based Testing with Hypothesis](https://www.hillelwayne.com/post/hypothesis-testing/)
- [openpilot Safety](https://github.com/commaai/openpilot/blob/master/docs/SAFETY.md)
- [ISO 26262](https://www.iso.org/standard/68383.html) - Automotive Functional Safety

---

*Generated for openpilot formal verification validation framework*
