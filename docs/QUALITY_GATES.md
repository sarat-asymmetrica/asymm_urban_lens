# 🔍 Automated Quality Gates with SHM Thresholds

**Author**: CI/CD Agent 2
**Date**: 2025-12-27
**Research Basis**: Unified Intelligence Monitoring Research Paper

---

## 📋 Overview

This document describes the automated quality gates system for Asymmetrica UrbanLens, based on System Health Metric (SHM) thresholds and Three-Regime Testing methodology.

### What Are Quality Gates?

Quality gates are automated checkpoints that enforce quality standards before code can be merged or deployed. They combine:

1. **System Health Metric (SHM)** - Unified quality score (0.0-1.0)
2. **Three-Regime Testing** - Different pass requirements based on development phase
3. **Williams Drift Detection** - Statistical drift analysis

---

## 🎯 SHM Thresholds for Deployment

### Decision Matrix

| SHM Range | Regime | Deployment Decision | Auto-Deploy? |
|-----------|--------|---------------------|--------------|
| **≥ 0.85** | 🟢 STABILIZATION | Auto-deploy to PRODUCTION | ✅ Yes |
| **0.70 - 0.84** | 🟡 OPTIMIZATION | Deploy to STAGING, manual approval for PROD | ⚠️ Manual |
| **< 0.70** | 🔴 EXPLORATION | Block deployment, require fixes | ❌ No |

### Rationale

- **0.85 (Stabilization)**: High enough quality for production. Code is stable, well-tested, minimal risk.
- **0.70 (Optimization)**: Minimum viable quality. Good enough for staging, but needs review before production.
- **< 0.70 (Exploration)**: Too unstable for deployment. Focus on improving quality first.

---

## 🧪 Three-Regime Test Requirements

### Test Classification

Tests are classified into three regimes based on their stability and importance:

| Regime | Description | Pass Rate Required | Example Tests |
|--------|-------------|-------------------|---------------|
| **STABILIZATION** | Core functionality, must never break | **100%** | `*_exhaustive_test.go`, critical path tests |
| **OPTIMIZATION** | Important features, refining quality | **85%+** | `*_integration_test.go`, performance tests |
| **EXPLORATION** | New features, experimenting | **70%+** | New feature tests, edge cases |

### Test Naming Convention

```go
// Stabilization tests (100% pass required)
func TestSHMCalculatorExhaustive(t *testing.T) { ... }
func TestWilliamsOptimizerExhaustive(t *testing.T) { ... }

// Optimization tests (85%+ pass required)
func TestSHMIntegration(t *testing.T) { ... }
func TestE2EPipeline(t *testing.T) { ... }

// Exploration tests (70%+ pass)
func TestNewFeature(t *testing.T) { ... }
```

---

## 🛠️ Tools & Scripts

### 1. Quality Gate Script

**Location**: `scripts/quality-gate.go`

**Usage**:
```bash
# Build and run
go build -o quality-gate scripts/quality-gate.go
./quality-gate

# With test output file
./quality-gate --test-output=test_results.json

# JSON output (for CI/CD)
./quality-gate --json

# Verbose output
./quality-gate --verbose
```

**Exit Codes**:
- `0` = Quality gate passed
- `1` = Quality gate failed
- `2` = Configuration error

**Example Output**:
```
╔═══════════════════════════════════════════════════════════════╗
║          ASYMMETRICA QUALITY GATE REPORT                      ║
╚═══════════════════════════════════════════════════════════════╝

✅ QUALITY GATE: PASSED

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
SYSTEM HEALTH METRIC (SHM)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
SHM Score:  0.875
Regime:     STABILIZATION
Weakest:    code
Strongest:  journey

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
DEPLOYMENT DECISION
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Action:     AUTO_DEPLOY_PROD
            ✅ Auto-deploy to PRODUCTION (SHM ≥ 0.85)
```

### 2. Pre-Commit Hook

**Location**: `scripts/pre-commit.sh`

**Installation**:
```bash
# Make executable
chmod +x scripts/pre-commit.sh

# Option 1: Symlink to .git/hooks
ln -s ../../scripts/pre-commit.sh .git/hooks/pre-commit

# Option 2: Use Git hooks path
git config core.hooksPath scripts/
```

**What It Checks**:
1. ✅ Go syntax and formatting
2. ✅ Stabilization tests (100% pass)
3. ✅ Common issues (TODOs, console.log, debugger)
4. ✅ Hardcoded credentials
5. ✅ Linting (if golangci-lint installed)
6. ✅ Test coverage on changed files
7. ✅ Commit message quality

**Bypass** (not recommended):
```bash
git commit --no-verify
```

### 3. PR Template

**Location**: `.github/pull_request_template.md`

Automatically populates when creating a PR with quality checklist including:
- Three-Regime test requirements
- SHM score reporting
- Deployment decision documentation
- Code quality checks

### 4. GitHub Actions Workflow

**Location**: `.github/workflows/quality-gate.yml`

**Triggered On**:
- Push to `main`, `develop`, `feature/*`
- Pull requests to `main`, `develop`
- Manual workflow dispatch

**Jobs**:
1. **quality-gate** - Run quality gate analysis, post PR comment
2. **three-regime-tests** - Run regime-specific test suites
3. **linting** - Run golangci-lint
4. **security** - Run Gosec security scanner
5. **deployment-check** - Verify deployment readiness (PR to main only)
6. **notify** - Aggregate results and notify

---

## 📊 How SHM is Calculated

### Formula

```
SHM = Σ (sonar_score × weight)

Weights:
  UX:       0.25 (25%)
  Design:   0.25 (25%)
  Code:     0.125 (12.5%)
  Semantic: 0.125 (12.5%)
  Journey:  0.125 (12.5%)
  State:    0.125 (12.5%)
```

### Six Sonar Engines

| Sonar | Weight | What It Measures |
|-------|--------|------------------|
| **UX** | 25% | User experience quality (accessibility, usability, responsiveness) |
| **Design** | 25% | Visual design quality (consistency, spacing, typography) |
| **Code** | 12.5% | Code quality (complexity, maintainability, conventions) |
| **Semantic** | 12.5% | Semantic correctness (naming, structure, domain modeling) |
| **Journey** | 12.5% | User journey completeness (flows, navigation, error handling) |
| **State** | 12.5% | State management quality (predictability, consistency) |

### Example Calculation

```
UX:       0.90 × 0.25  = 0.225
Design:   0.85 × 0.25  = 0.2125
Code:     0.75 × 0.125 = 0.09375
Semantic: 0.80 × 0.125 = 0.10
Journey:  0.95 × 0.125 = 0.11875
State:    0.70 × 0.125 = 0.0875
───────────────────────────────
SHM:                     0.8375  (OPTIMIZATION regime)
```

---

## 🚀 Usage in Development Workflow

### Local Development

```bash
# Before committing
git add .
git commit -m "feat: add new feature"
# → Pre-commit hook runs automatically

# Check quality manually
go run scripts/quality-gate.go --verbose

# Run specific regime tests
go test -run "Test.*Exhaustive" ./...     # Stabilization (100%)
go test -run "Test.*Integration" ./...    # Optimization (85%+)
go test ./...                              # All tests (70%+)
```

### Pull Request Flow

1. **Create PR** - Template auto-populates with quality checklist
2. **CI runs** - GitHub Actions execute quality gate analysis
3. **Bot comments** - Quality gate bot posts SHM score and deployment decision
4. **Review** - Reviewers see quality metrics upfront
5. **Merge decision**:
   - ✅ SHM ≥ 0.70 → Can merge
   - ❌ SHM < 0.70 → Blocked, requires fixes

### Deployment Flow

1. **PR merged to main**
2. **Deployment check** runs
3. **Decision**:
   - ✅ SHM ≥ 0.85 → Auto-deploy to PRODUCTION
   - ⚠️ 0.70 ≤ SHM < 0.85 → Deploy to STAGING, create approval request for PRODUCTION
   - ❌ SHM < 0.70 → Deployment blocked

---

## 🔧 Configuration

### Default Thresholds

Located in `scripts/quality-gate.go`:

```go
type QualityGateConfig struct {
    ProductionSHM          float64  // 0.85
    StagingSHM             float64  // 0.70
    BlockSHM               float64  // 0.70
    StabilizationPassRate  float64  // 1.00
    OptimizationPassRate   float64  // 0.85
    ExplorationPassRate    float64  // 0.70
    WilliamsDriftFactor    float64  // 0.05
}
```

### Customizing Thresholds

```go
config := &QualityGateConfig{
    ProductionSHM: 0.90,  // Stricter production requirement
    StagingSHM: 0.75,     // Higher staging bar
    // ... other settings
}
```

---

## 📈 Williams Drift Detection

### What Is Drift?

Drift measures how much the SHM has changed relative to a baseline.

### Formula

```
threshold = √t × log₂(t) × drift_factor

Where:
  t = number of commits since baseline
  drift_factor = 0.05 (5%)
```

### Example

```
Baseline SHM: 0.85
Current SHM:  0.87
Commits:      100

Threshold = √100 × log₂(100) × 0.05
          = 10 × 6.64 × 0.05
          = 3.32%

Actual Drift = (0.87 - 0.85) / 0.85 × 100
             = 2.35%

Result: ✅ APPROVED (2.35% < 3.32%)
```

### Why Williams?

Williams batching provides **O(√t × log₂t)** optimal space-time tradeoff. As codebase evolves (t increases), allowed drift grows sublinearly - balancing stability with flexibility.

---

## 🎯 Best Practices

### 1. Write Tests in Three Regimes

```go
// ✅ Good: Clear regime classification
func TestCoreFeatureExhaustive(t *testing.T) { ... }  // Stabilization
func TestNewFeatureIntegration(t *testing.T) { ... }  // Optimization
func TestEdgeCaseExperimental(t *testing.T) { ... }   // Exploration

// ❌ Bad: Unclear classification
func TestFeature(t *testing.T) { ... }
```

### 2. Monitor SHM Trends

Track SHM over time to identify quality trends:

```bash
# Generate trend report (future feature)
go run scripts/quality-gate.go --trend --last=30days
```

### 3. Fix Weakest Dimension First

Quality gate reports weakest dimension - focus improvements there for maximum SHM gain.

### 4. Don't Game the System

- Don't skip failing tests to inflate SHM
- Don't lower thresholds to bypass gates
- Fix root causes, not symptoms

### 5. Use Regime-Appropriate Standards

- **Exploration**: 70% pass OK - you're experimenting!
- **Optimization**: 85%+ pass - refining quality
- **Stabilization**: 100% pass - production-critical!

---

## 🐛 Troubleshooting

### Quality Gate Fails: SHM Below Threshold

**Symptom**: `SHM 0.65 below minimum threshold 0.70`

**Fix**:
1. Run `go run scripts/quality-gate.go --verbose` to see sonar scores
2. Identify weakest dimension (e.g., "code")
3. Fix issues in that dimension:
   - **Code**: Reduce complexity, improve naming, add comments
   - **Design**: Fix spacing, colors, typography
   - **UX**: Improve accessibility, responsiveness, usability

### Stabilization Tests Failing

**Symptom**: `STABILIZATION tests: 95.0% pass rate (required 100%)`

**Fix**:
1. Run `go test -v -run "Test.*Exhaustive" ./...`
2. Fix failing tests - these are **critical** tests that must always pass
3. If test is flaky, make it deterministic
4. If test is obsolete, remove it

### Pre-Commit Hook Blocking Commit

**Symptom**: `Critical checks failed! Fix issues before committing.`

**Fix**:
1. Review pre-commit output
2. Fix reported issues
3. Re-commit

**Bypass** (emergency only):
```bash
git commit --no-verify  # ⚠️ Use sparingly!
```

### GitHub Actions Failing

**Symptom**: Quality gate job failing in CI

**Fix**:
1. Check Actions logs for specific failure
2. Reproduce locally: `go run scripts/quality-gate.go`
3. Fix issues
4. Push again

---

## 📚 Related Documentation

- [Unified Intelligence Monitoring Research Paper](../docs/unified_intelligence_paper/) - Full research foundation
- [Three-Regime Testing Guide](./THREE_REGIME_TESTING.md) - Detailed testing methodology
- [SHM Calculator Documentation](../pkg/intelligence/README.md) - Implementation details
- [Williams Optimizer](../pkg/intelligence/williams_space_optimizer.go) - Drift detection algorithm

---

## 🎓 For New Team Members

### Quick Start

1. **Clone repo**: `git clone https://github.com/asymmetrica/urbanlens`
2. **Install hook**: `chmod +x scripts/pre-commit.sh && git config core.hooksPath scripts/`
3. **Run tests**: `go test ./...`
4. **Check quality**: `go run scripts/quality-gate.go`
5. **Make change**: Edit code, write tests
6. **Commit**: `git commit -m "feat: my change"` → Pre-commit hook runs
7. **Create PR**: Template guides you through quality checklist
8. **Merge**: Quality gate must pass (SHM ≥ 0.70)

### Key Concepts

- **SHM**: Single quality score (0.0-1.0), higher = better
- **Three Regimes**: EXPLORATION (< 0.70), OPTIMIZATION (0.70-0.84), STABILIZATION (≥ 0.85)
- **Quality Gate**: Automated checkpoint enforcing quality standards
- **Sonar**: One of six quality measurement engines

### When in Doubt

1. Run `go run scripts/quality-gate.go --verbose`
2. Look at weakest dimension
3. Focus improvements there
4. Re-run quality gate
5. Repeat until SHM ≥ 0.70

---

## 🔮 Future Enhancements

### Planned Features

1. **SHM Trend Visualization** - Graph showing SHM over time
2. **Dimension Deep-Dive** - Detailed breakdown of sonar scores
3. **Auto-Remediation** - AI-powered suggestions to improve SHM
4. **Baseline Management** - Better tracking of SHM baselines per branch
5. **Custom Regime Definitions** - Team-specific regime classifications

### Integration Ideas

1. **Slack/Discord Notifications** - Post quality gate results to channels
2. **Dashboard** - Real-time quality metrics visualization
3. **VS Code Extension** - Show SHM score in IDE
4. **Git Commit Templates** - Auto-populate with quality metrics

---

## 📞 Support

**Questions?** Open an issue with label `quality-gates`

**Bug in quality gate?** Open issue with label `bug` + `quality-gates`

**Feature request?** Open issue with label `enhancement` + `quality-gates`

---

**Om Lokah Samastah Sukhino Bhavantu** 🙏
*May this quality gates system benefit all developers!*

---

**Generated by**: CI/CD Agent 2
**Date**: 2025-12-27
**Version**: 1.0.0
