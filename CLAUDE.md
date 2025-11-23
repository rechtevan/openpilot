# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## About openpilot

openpilot is an operating system for robotics that upgrades the driver assistance system in 300+ supported cars. It's developed by comma.ai and is fully open source under the MIT license.

**Key principles**: Safety, stability, quality, and features (in that order).

## Quick Start Commands

### Setup
```bash
# Full setup (installs dependencies, creates .venv)
tools/op.sh setup

# Activate Python environment
source .venv/bin/activate
```

### Building
```bash
# Build everything (uses all CPU cores)
scons -j$(nproc)

# Build in subdirectory
scons -u -j$(nproc)

# Build with sanitizers
scons --asan          # AddressSanitizer
scons --ubsan         # UndefinedBehaviorSanitizer

# Minimal build (no tests/tools)
scons --minimal
```

### Testing
```bash
# Run all tests
pytest

# Run specific test directory
pytest selfdrive/controls/tests/

# Skip slow tests
pytest -m 'not slow'

# Run tests in parallel
pytest -n auto

# Run specific test file
pytest selfdrive/test/test_onroad.py

# Process replay tests (regression testing)
pytest selfdrive/test/process_replay/test_processes.py
```

### Coverage
```bash
# Run tests with coverage locally
pytest --cov=selfdrive --cov=system --cov=common --cov=tools \
       --cov-report=html \
       --cov-report=term \
       -m 'not slow'

# View HTML coverage report
open .local/htmlcov/index.html  # macOS
xdg-open .local/htmlcov/index.html  # Linux

# Generate coverage report
coverage report -m

# Combine coverage from parallel runs
coverage combine
coverage report
```

**Code Coverage Standards:**
- Target: 80% coverage for new code
- PR checks: Coverage should not decrease by more than 1%
- View coverage reports at: https://codecov.io/gh/rechtevan/openpilot
- Configuration: `pyproject.toml` [tool.coverage.*] sections

### Linting
```bash
# Run all linting (from scripts/lint/lint.sh)
ruff check .          # Python linting
mypy .                # Type checking
codespell .           # Spell checking
```

### Development Tools
```bash
# Replay a drive (for debugging)
tools/replay/replay --data_dir /path/to/data <segment>

# View/plot CAN messages
tools/cabana/cabana

# Run openpilot with simulator
python3 -m tools.sim.bridge

# Run on PC with webcams
cd tools/webcam && python3 -m camerad

# Stream camera over network
tools/camerastream/camerastream.py
```

## High-Level Architecture

### Process-Based Architecture

openpilot uses a **multi-process architecture** where each component runs as an independent process, managed by `system/manager/manager.py`. Process definitions live in `system/manager/process_config.py`.

**Key always-running processes:**
- `pandad` - Communicates with panda device (CAN/car interface)
- `ui` - User interface
- `uploader` - Uploads logs to comma servers
- `athenad` - Cloud connectivity

**Key on-road processes (when driving):**
- `camerad` - Camera capture (road/driver/wide cameras)
- `modeld` - Driving neural network model (lane lines, path)
- `dmonitoringmodeld` - Driver monitoring model
- `controlsd` - Main control loop (lateral + longitudinal control)
- `plannerd` - Path planning
- `radard` - Radar processing and lead vehicle tracking
- `card` - Car state processing
- `selfdrived` - High-level state machine and event management
- `locationd` - GPS/IMU fusion for vehicle localization
- `calibrationd` - Camera calibration
- `loggerd` - Log recording
- `encoderd` - Video encoding

### Message Passing with cereal + msgq

All processes communicate via **msgq** (message queue) using **cereal** (Cap'n Proto) serialization:

**Publishing:**
```python
pm = messaging.PubMaster(['carControl', 'controlsState'])
msg = messaging.new_message('carControl')
pm.send('carControl', msg)
```

**Subscribing:**
```python
sm = messaging.SubMaster(['carState', 'modelV2', 'selfdriveState'])
sm.update(timeout_ms)
value = sm['carState'].vEgo
```

**Message definitions:**
- Schema: `cereal/log.capnp` (Event struct with union of ~80 message types)
- Service registry: `cereal/services.py` (~80 services with frequencies, logging flags)
- Zero-copy IPC via shared memory

### Directory Structure

**selfdrive/** - Main openpilot logic
- `car/` - Vehicle-specific interfaces (symlinked from opendbc_repo)
- `controls/` - Control systems (controlsd, plannerd, radard)
- `locationd/` - Location/pose estimation
- `modeld/` - Neural network models
- `pandad/` - Interface to panda hardware
- `ui/` - User interface
- `selfdrived/` - High-level state machine

**system/** - System services and hardware abstraction
- `manager/` - Process manager
- `camerad/` - Camera capture
- `loggerd/` - Logging and encoding
- `hardware/` - Hardware abstraction (tici vs pc)
- `athena/` - Cloud connectivity

**cereal/** - Message definitions (Cap'n Proto)

**msgq/** - Message queue (symlinked from msgq_repo)

**opendbc/** - CAN database and car interfaces (symlinked from opendbc_repo)

**panda/** - Car interface hardware/firmware (submodule)

**common/** - Shared utilities (params, realtime, transformations)

**tools/** - Development tools (replay, cabana, sim, webcam)

**third_party/** - External dependencies

### Car Interface Architecture

The car interface abstracts different vehicle makes/models:

1. **opendbc** - DBC files for CAN message definitions
2. **CarInterface** - Per-manufacturer implementations in `selfdrive/car/<brand>/`
3. **Fingerprinting** - Automatic car detection via CAN messages
4. **panda** - Hardware device connecting to car's CAN bus with safety model in firmware

Each car brand directory contains:
- `carstate.py` - Parses CAN to populate CarState
- `carcontroller.py` - Sends CarControl commands to CAN
- `interface.py` - CarInterface implementation
- `values.py` - Constants and supported models
- `radar_interface.py` - Radar data parsing (if applicable)

### Key Technologies

**cereal** - Messaging
- Cap'n Proto for fast serialization
- SI units enforced by convention
- Schema in `cereal/log.capnp`

**msgq** - Message queue
- Zero-copy shared memory IPC
- zmq backend

**panda** - Car hardware interface
- USB device for CAN communication
- Safety model in firmware (C code)
- Handles CAN Tx/Rx, GPS, IMU

**SCons** - Build system
- SConstruct is main build file
- Compiler: clang/clang++
- Supports: x86_64, aarch64, larch64 (tici), Darwin (macOS)

**tinygrad** - ML framework for neural network inference

**rednose** - Kalman filter code generation

## Important Development Patterns

### Control Loop Pattern
```python
class Controls:
    def __init__(self):
        self.sm = messaging.SubMaster([...])  # Subscribe to inputs
        self.pm = messaging.PubMaster([...])  # Publish outputs

    def update(self):
        self.sm.update(timeout_ms)            # Get latest messages
        # Process and compute outputs

    def publish(self, msg):
        self.pm.send('topic', msg)
```

### Real-Time Execution
- Fixed update rates (e.g., DT_CTRL = 0.01s = 100 Hz for controls)
- `Ratekeeper` maintains loop frequency
- `config_realtime_process()` sets scheduling priorities

### Parameter Store
- Persistent key-value store: `common/params`
- Used for settings, calibration, state persistence
```python
from common.params import Params
params = Params()
params.put("key", "value")
value = params.get("key")
```

### Hardware Abstraction
- `HARDWARE` singleton from `system/hardware/hw.h`
- Platform-specific implementations (Tici vs PC)

## CI/CD and Code Quality

**GitHub Actions** (`.github/workflows/tests.yaml`):
- Build on Ubuntu 24.04 and macOS
- Unit tests with pytest
- Process replay tests
- Static analysis (ruff, mypy, codespell)
- Docker-based for Linux builds

**Jenkins** (Jenkinsfile):
- Hardware-in-the-loop tests on tici devices
- Runs on actual hardware

**Code Quality Tools:**
- **ruff** - Fast Python linter
- **mypy** - Static type checking
- **codespell** - Spell checker
- Line length: 160 chars
- Target: Python 3.11

## Contributing Guidelines

From `docs/CONTRIBUTING.md`:

**What gets merged:**
- Simple, well-tested bug fixes
- Typo fixes
- Removing unused code
- Car model/brand ports (with verification)

**What doesn't get merged:**
- Style changes
- 500+ line PRs
- PRs without clear goal
- New features (openpilot is considered feature-complete)
- Negative expected value changes

**Pull request requirements:**
- Clearly stated purpose
- Every line contributes to stated purpose
- Verification (how did you test?)
- Justification (benchmarks for optimizations, plots for tuning)
- Passes CI tests

## Platform Support

**Primary development target:** Ubuntu 24.04

**Also supported:**
- macOS (with Homebrew)
- WSL2 on Windows
- AGNOS (custom OS on comma 3X device)

**Device architecture detection:**
- `larch64` - Linux tici arm64 (comma 3X)
- `aarch64` - Linux PC arm64
- `x86_64` - Linux PC x64
- `Darwin` - macOS arm64

## Logging Architecture

**Log types:**
- **rlogs** - Full resolution logs (all messages, bz2 compressed)
- **qlogs** - Decimated logs for quick upload
- **Camera streams** - H.265 encoded (fcamera, dcamera, ecamera)

**Organization:**
- **Segments** - 1-minute chunks
- **Routes** - Ignition on → ignition off

## Safety

From `docs/SAFETY.md`:
- ISO26262 guidelines followed
- Safety logic in panda firmware (C code)
- Multiple defensive layers
- Hardware-in-the-loop testing
- Software-in-the-loop tests on every commit
