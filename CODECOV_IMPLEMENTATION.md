# Codecov Integration Plan for rechtevan/openpilot

This document outlines the implementation plan for adding code coverage tracking and reporting to the openpilot fork, following the quality standards established in rechtevan/JaxMARL.

## Current State Analysis

### What openpilot Already Has
✅ **Testing Infrastructure**
- Pytest configured in `pyproject.toml` with extensive test paths
- Multiple test jobs in CI: unit tests, process replay, simulator tests
- Parallel test execution with pytest-xdist
- Docker-based CI environment

✅ **Code Quality Tools**
- ruff for linting (comprehensive rule set)
- mypy for type checking
- codespell for spell checking
- Line length: 160 chars, Python 3.11 target

✅ **CI/CD**
- GitHub Actions workflows in `.github/workflows/tests.yaml`
- Namespace runners for performance
- Caching for scons and downloads

### What's Missing
❌ Code coverage measurement
❌ Codecov integration
❌ Coverage badge in README
❌ Pre-commit hooks
❌ Security scanning (CodeQL)
❌ Coverage configuration (.coveragerc or tool.coverage in pyproject.toml)
❌ pytest-cov dependency

## Implementation Plan

### Phase 1: Basic Coverage Setup

#### 1.1 Add pytest-cov Dependency
**File:** `pyproject.toml`
**Change:** Add to `[project.optional-dependencies]` testing section:
```toml
testing = [
  # ... existing dependencies ...
  "pytest-cov",
  "coverage[toml]>=7.0",
]
```

#### 1.2 Create Coverage Configuration
**File:** `pyproject.toml` (add new section)
```toml
[tool.coverage.run]
source = ["selfdrive", "system", "common", "tools"]
omit = [
  "*/tests/*",
  "*/test_*.py",
  "*/__init__.py",
  "*/SConscript",
  # Submodules
  "opendbc/*",
  "panda/*",
  "cereal/*",
  "msgq/*",
  "rednose/*",
  "tinygrad/*",
  "teleoprtc/*",
  # Generated code
  "*/generated/*",
  "*/c_generated_code/*",
  # Third party
  "third_party/*",
  # Tools that don't need coverage
  "tools/cabana/*",
  "tools/replay/*",
  "tools/sim/*",
]
parallel = true
concurrency = ["multiprocessing", "thread"]

[tool.coverage.report]
precision = 2
show_missing = true
skip_covered = false
skip_empty = true
sort = "Cover"
exclude_lines = [
  "pragma: no cover",
  "def __repr__",
  "raise AssertionError",
  "raise NotImplementedError",
  "if __name__ == .__main__.:",
  "if TYPE_CHECKING:",
  "if typing.TYPE_CHECKING:",
  "@abstractmethod",
  "@abc.abstractmethod",
  "class .*\\bProtocol\\):",
  "@overload",
  "except ImportError:",
  "\\.\\.\\.",
]

[tool.coverage.html]
directory = ".local/htmlcov"

[tool.coverage.xml]
output = ".local/coverage.xml"
```

#### 1.3 Update .gitignore
**File:** `.gitignore`
**Add:**
```
# AI-generated analysis and reports (should NOT be committed)
.local/
```

Note: Coverage files (`.coverage*`, `coverage.xml`, `htmlcov`) are already in .gitignore.
We'll use `.local/` for coverage HTML/XML outputs following JaxMARL's pattern.

### Phase 2: CI/CD Integration

#### 2.1 Create Dedicated Coverage Workflow
**File:** `.github/workflows/coverage.yml`
```yaml
name: Coverage

on:
  push:
    branches: [master]
  pull_request:
    branches: [master]

permissions:
  contents: read
  pull-requests: write

env:
  PYTHONWARNINGS: error
  BASE_IMAGE: openpilot-base
  DOCKER_LOGIN: docker login ghcr.io -u ${{ github.actor }} -p ${{ secrets.GITHUB_TOKEN }}
  BUILD: selfdrive/test/docker_build.sh base
  RUN: docker run --shm-size 2G -v $PWD:/tmp/openpilot -w /tmp/openpilot -e CI=1 -e PYTHONWARNINGS=error -e FILEREADER_CACHE=1 -e PYTHONPATH=/tmp/openpilot -v $GITHUB_WORKSPACE/.ci_cache/scons_cache:/tmp/scons_cache -v $GITHUB_WORKSPACE/.ci_cache/comma_download_cache:/tmp/comma_download_cache $BASE_IMAGE /bin/bash -c

jobs:
  coverage:
    name: Test Coverage
    runs-on: ubuntu-24.04
    steps:
      - name: Checkout
        uses: actions/checkout@v4
        with:
          submodules: true

      - name: Setup with retry
        uses: ./.github/workflows/setup-with-retry
        id: setup-step

      - name: Build openpilot
        run: ${{ env.RUN }} "scons -j$(nproc)"

      - name: Run tests with coverage
        timeout-minutes: 20
        run: |
          ${{ env.RUN }} "source selfdrive/test/setup_xvfb.sh && \
                          pip install pytest-cov coverage[toml] && \
                          mkdir -p .local && \
                          pytest --cov=selfdrive --cov=system --cov=common --cov=tools \
                                 --cov-report=xml:.local/coverage.xml \
                                 --cov-report=term \
                                 -m 'not slow' \
                                 -n auto && \
                          chmod 666 .local/coverage.xml"

      - name: Upload coverage to Codecov
        uses: codecov/codecov-action@v5
        with:
          file: ./.local/coverage.xml
          flags: unittests
          token: ${{ secrets.CODECOV_TOKEN }}
          fail_ci_if_error: false
          verbose: true

      - name: Coverage Summary
        if: github.event_name == 'pull_request'
        run: |
          echo "### 📊 Coverage Report" >> $GITHUB_STEP_SUMMARY
          echo "Coverage results have been uploaded to Codecov." >> $GITHUB_STEP_SUMMARY
```

#### 2.2 Update Existing Test Workflow (Optional)
Add coverage collection to the existing `unit_tests` job in `.github/workflows/tests.yaml`:
- This allows coverage tracking without creating a separate workflow
- Add `--cov` flags to the pytest command in line 166

### Phase 3: Codecov Configuration

#### 3.1 Create codecov.yml
**File:** `codecov.yml` (root directory)
```yaml
coverage:
  precision: 2
  round: down
  range: "70...95"

  status:
    project:
      default:
        target: auto
        threshold: 1%
        informational: false
    patch:
      default:
        target: 80%
        threshold: 5%
        informational: true

comment:
  layout: "reach, diff, flags, files"
  behavior: default
  require_changes: false
  require_base: false
  require_head: true

ignore:
  - "tests/**/*"
  - "**/*_test.py"
  - "**/test_*.py"
  - "third_party/**/*"
  - "opendbc/**/*"
  - "panda/**/*"
  - "cereal/**/*"
  - "msgq/**/*"
  - "rednose/**/*"
  - "tinygrad/**/*"
  - "teleoprtc/**/*"
  - "**/SConscript"
  - "SConstruct"
```

#### 3.2 Add Codecov Badge to README
**File:** `README.md`
**Add after existing badges (line 26-28):**
```markdown
[![codecov](https://codecov.io/gh/rechtevan/openpilot/branch/master/graph/badge.svg)](https://codecov.io/gh/rechtevan/openpilot)
```

### Phase 4: Pre-commit Hooks (Following JaxMARL Standards)

#### 4.1 Create Pre-commit Configuration
**File:** `.pre-commit-config.yaml`
```yaml
repos:
  - repo: https://github.com/astral-sh/ruff-pre-commit
    rev: v0.8.4
    hooks:
      - id: ruff
        args: [--fix]
      - id: ruff-format

  - repo: https://github.com/pre-commit/mirrors-mypy
    rev: v1.11.2
    hooks:
      - id: mypy
        exclude: ^(tests/|cereal/|msgq/|opendbc/|panda/|rednose/|tinygrad/|teleoprtc/|third_party/)
        additional_dependencies:
          - types-requests
          - types-tabulate

  - repo: https://github.com/codespell-project/codespell
    rev: v2.3.0
    hooks:
      - id: codespell
        args: [--config, pyproject.toml]

  - repo: https://github.com/pre-commit/pre-commit-hooks
    rev: v5.0.0
    hooks:
      - id: trailing-whitespace
        exclude: ^(tests/.*snapshots/.*|.*\.patch)$
      - id: end-of-file-fixer
        exclude: ^(tests/.*snapshots/.*|.*\.patch)$
      - id: check-yaml
        args: [--allow-multiple-documents]
      - id: check-added-large-files
        args: [--maxkb=1024]
      - id: check-merge-conflict
      - id: check-toml
      - id: mixed-line-ending
        args: [--fix=lf]

ci:
  autofix_commit_msg: |
    [pre-commit.ci] auto fixes from pre-commit.com hooks
  autofix_prs: true
  autoupdate_branch: ''
  autoupdate_commit_msg: '[pre-commit.ci] pre-commit autoupdate'
  autoupdate_schedule: weekly
  skip: []
  submodules: false
```

**Installation instructions to add to README or CONTRIBUTING.md:**
```bash
# Install pre-commit
pip install pre-commit

# Install git hooks
pre-commit install

# Run manually on all files
pre-commit run --all-files
```

### Phase 5: Security Scanning (CodeQL)

#### 5.1 Create CodeQL Workflow
**File:** `.github/workflows/codeql-analysis.yml`
```yaml
name: "CodeQL"

on:
  push:
    branches: [master]
  pull_request:
    branches: [master]
  schedule:
    - cron: '0 0 * * 1'  # Weekly on Monday

jobs:
  analyze:
    name: Analyze
    runs-on: ubuntu-24.04
    permissions:
      actions: read
      contents: read
      security-events: write

    strategy:
      fail-fast: false
      matrix:
        language: ['python', 'cpp']

    steps:
      - name: Checkout
        uses: actions/checkout@v4
        with:
          submodules: true

      - name: Initialize CodeQL
        uses: github/codeql-action/init@v3
        with:
          languages: ${{ matrix.language }}
          queries: security-extended

      - name: Autobuild
        uses: github/codeql-action/autobuild@v3
        if: matrix.language == 'python'

      - name: Build C++ code
        if: matrix.language == 'cpp'
        run: |
          sudo apt-get update
          sudo apt-get install -y clang
          scons -j$(nproc)

      - name: Perform CodeQL Analysis
        uses: github/codeql-action/analyze@v3
        with:
          category: "/language:${{ matrix.language }}"
```

### Phase 6: Documentation Updates

#### 6.1 Update CLAUDE.md
**File:** `CLAUDE.md`
**Add section after "Testing":**
```markdown
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
```

#### 6.2 Update CONTRIBUTING.md
Add section about code coverage requirements:
```markdown
### Code Coverage

Pull requests should maintain or improve code coverage:
- New features should include tests covering ≥80% of new code
- Bug fixes should include regression tests
- Coverage reports are automatically generated and commented on PRs
- View detailed coverage at https://codecov.io/gh/rechtevan/openpilot
```

#### 6.3 Add Security Badge to README
**File:** `README.md`
**Add after codecov badge:**
```markdown
[![CodeQL](https://github.com/rechtevan/openpilot/workflows/CodeQL/badge.svg)](https://github.com/rechtevan/openpilot/actions?query=workflow%3ACodeQL)
```

## Implementation Steps (Priority Order)

1. **Phase 1: Basic Coverage Setup** (30 minutes)
   - Add pytest-cov to dependencies
   - Add coverage configuration to pyproject.toml
   - Update .gitignore
   - Test locally: `pytest --cov=selfdrive -m 'not slow'`

2. **Phase 2: CI Integration** (45 minutes)
   - Create coverage.yml workflow
   - Set up CODECOV_TOKEN secret in GitHub repo settings
   - Test with a commit to see coverage upload

3. **Phase 3: Codecov Configuration** (15 minutes)
   - Create codecov.yml
   - Add badge to README
   - Verify badge appears after first coverage upload

4. **Phase 4: Pre-commit Hooks** (30 minutes)
   - Create .pre-commit-config.yaml
   - Test locally with `pre-commit run --all-files`
   - Document in README/CONTRIBUTING.md

5. **Phase 5: Security Scanning** (20 minutes)
   - Create codeql-analysis.yml
   - Enable CodeQL in GitHub Security settings
   - Add badge to README

6. **Phase 6: Documentation** (20 minutes)
   - Update CLAUDE.md
   - Update CONTRIBUTING.md
   - Add coverage standards documentation

**Total Estimated Time:** 2.5-3 hours

## Testing the Implementation

### Local Testing
```bash
# 1. Install coverage dependencies
source .venv/bin/activate
pip install pytest-cov coverage[toml]

# 2. Run a small test with coverage
pytest selfdrive/controls/tests/test_startup.py --cov=selfdrive.controls --cov-report=term

# 3. Run full test suite with coverage (slow)
pytest --cov=selfdrive --cov=system --cov=common --cov-report=html -m 'not slow'

# 4. View HTML report
open .coverage_html/index.html
```

### CI Testing
1. Create a test branch
2. Make the Phase 1 changes
3. Push and verify the coverage workflow runs
4. Check Codecov dashboard for results

## Maintenance

### Regular Tasks
- **Weekly:** Review codecov reports for coverage trends
- **Per PR:** Ensure coverage doesn't decrease
- **Monthly:** Update pre-commit hook versions
- **Quarterly:** Review CodeQL security findings

### Monitoring
- Codecov dashboard: https://codecov.io/gh/rechtevan/openpilot
- GitHub Actions: https://github.com/rechtevan/openpilot/actions
- Security alerts: https://github.com/rechtevan/openpilot/security

## References

- JaxMARL coverage setup: https://github.com/rechtevan/JaxMARL/blob/main/.coveragerc
- Codecov documentation: https://docs.codecov.com/
- pytest-cov documentation: https://pytest-cov.readthedocs.io/
- Pre-commit documentation: https://pre-commit.com/
- CodeQL documentation: https://codeql.github.com/
