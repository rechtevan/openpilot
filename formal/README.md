# Formal Verification Models for openpilot

This directory contains formal specifications for safety-critical components of openpilot using TLA+ and SPIN/Promela.

## Directory Structure

```
formal/
├── tla/                    # TLA+ specifications
│   ├── StateMachine.tla    # Primary engagement state machine
│   ├── StateMachine.cfg    # TLC configuration
│   ├── LongControl.tla     # Longitudinal control state machine
│   ├── LongControl.cfg
│   ├── LaneChange.tla      # Lane change state machine
│   ├── LaneChange.cfg
│   ├── ExcessiveActuation.tla  # Safety detection logic
│   └── ExcessiveActuation.cfg
├── spin/                   # SPIN/Promela specifications
│   ├── messaging.pml       # Inter-process messaging protocol
│   └── panda_safety.pml    # Panda safety mode protocol
├── validation/             # Model-to-code validation framework
│   ├── TESTING_METHODS_GUIDE.md  # Educational comparison of testing methods
│   ├── env_state_machine.py      # Gym environment for state machine
│   ├── marl_validator.py         # MARL-based validation
│   ├── advanced_validator.py     # Hypothesis + coverage methods
│   ├── ai_boundary_validator.py  # AI-to-control boundary testing
│   └── run_validation.py         # CLI entry point
├── requirements/           # Sphinx-needs requirements traceability
│   ├── safety_requirements.rst   # REQ-* from upstream SAFETY.md
│   ├── verification_matrix.rst   # VER-* linking to formal models
│   └── traceability_matrix.rst   # Full bidirectional traceability
└── README.md               # This file
```

## Prerequisites

### TLA+ Toolbox

Download and install the TLA+ Toolbox:
- https://lamport.azurewebsites.net/tla/toolbox.html

Or use the command-line tools:
```bash
# Install TLC model checker
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
```

### SPIN

Install SPIN model checker:
```bash
# Ubuntu/Debian
sudo apt-get install spin

# macOS
brew install spin

# Verify installation
spin -V
```

## Running the Models

### TLA+ Models

Using TLA+ Toolbox (GUI):
1. Open TLA+ Toolbox
2. File → Open Spec → Add New Spec
3. Select the .tla file
4. Create a new model (Model → New Model)
5. Load the corresponding .cfg file
6. Run TLC (TLC Model Checker → Run)

Using command line:
```bash
cd formal/tla

# Run StateMachine model
java -jar tla2tools.jar -config StateMachine.cfg StateMachine.tla

# Run LongControl model
java -jar tla2tools.jar -config LongControl.cfg LongControl.tla

# Run LaneChange model
java -jar tla2tools.jar -config LaneChange.cfg LaneChange.tla

# Run ExcessiveActuation model
java -jar tla2tools.jar -config ExcessiveActuation.cfg ExcessiveActuation.tla
```

### SPIN Models

```bash
cd formal/spin

# Verify messaging protocol
spin -a messaging.pml
gcc -o pan pan.c
./pan

# Verify with specific LTL property
spin -a -f 'all_processes_start' messaging.pml
gcc -o pan pan.c
./pan -a

# Verify panda safety protocol
spin -a panda_safety.pml
gcc -o pan pan.c
./pan

# Check specific property
spin -a -f 'safety_requires_params' panda_safety.pml
gcc -o pan pan.c
./pan -a
```

## Model Descriptions

### StateMachine.tla (Issue #40)

Models the primary engagement/disengagement state machine from `selfdrive/selfdrived/state.py`.

**States:** disabled, preEnabled, enabled, softDisabling, overriding

**Key Properties Verified:**
- USER_DISABLE and IMMEDIATE_DISABLE always result in disabled state
- Soft disable timer is bounded
- NO_ENTRY prevents engagement
- ENABLE event required to engage from disabled

### LongControl.tla (Issue #41)

Models the longitudinal control state machine from `selfdrive/controls/lib/longcontrol.py`.

**States:** off, stopping, starting, pid

**Key Properties Verified:**
- Acceleration always bounded within ACCEL_MIN to ACCEL_MAX
- Stopping state never produces positive acceleration
- Output is zero when not active

### LaneChange.tla (Issue #42)

Models the lane change assistant from `selfdrive/controls/lib/desire_helper.py`.

**States:** off, preLaneChange, laneChangeStarting, laneChangeFinishing

**Key Properties Verified:**
- Lane changes only occur above minimum speed
- Blindspot detection blocks lane change initiation
- Timer has maximum duration
- Torque required to initiate lane change

### ExcessiveActuation.tla (Issue #44)

Models the excessive actuation safety check from `selfdrive/selfdrived/helpers.py`.

**Key Properties Verified:**
- Detection requires minimum consecutive violation count
- Lateral detection requires engagement buffer
- Counters are bounded
- Invalid sensor data resets detection

### messaging.pml (Issue #43)

Models the inter-process communication protocol from `cereal/messaging/` and `system/manager/`.

**Key Properties Verified:**
- No deadlock in messaging
- All critical processes eventually start
- Graceful shutdown sequence
- Message buffers don't permanently fill

### panda_safety.pml (Issue #45)

Models the panda safety mode configuration from `selfdrive/pandad/panda_safety.cc`.

**Key Properties Verified:**
- All pandas have consistent safety mode
- Safety mode only set after car params available
- Initialization before configuration
- Offroad resets safety state

## Model Checking Tips

1. **State Space Explosion:** Use smaller constants for initial verification, then increase for more thorough checking.

2. **Bounded Model Checking:** For liveness properties, use bounded checking first:
   ```bash
   ./pan -a -m10000  # Limit to 10000 steps
   ```

3. **Coverage:** Check state coverage:
   ```bash
   ./pan -C  # Coverage analysis
   ```

4. **Counterexamples:** When a property fails, examine the trail:
   ```bash
   spin -t -p messaging.pml  # Replay counterexample
   ```

## Contributing

When modifying openpilot's safety-critical code:

1. Update the corresponding formal model
2. Verify the properties still hold
3. Add new properties for new functionality
4. Document any assumptions in the model

## References

- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- [SPIN Documentation](http://spinroot.com/spin/whatispin.html)
- [Promela Manual](http://spinroot.com/spin/Man/promela.html)

