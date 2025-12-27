# Asymmetrica UrbanLens - CI/CD Documentation

**Generated:** 2025-12-27
**Philosophy:** Mathematical rigor encoded into CI/CD pipeline
**Paradigm:** Three-Regime Testing System

---

## 🎯 Overview

This CI/CD system implements **Three-Regime Dynamics** from Asymmetrica's mathematical framework, encoding quality gates directly into the pipeline.

### Three-Regime Testing Philosophy

| Regime | Threshold | Purpose | Philosophy |
|--------|-----------|---------|------------|
| **🎯 Stabilization** | **100%** | Critical path tests that MUST pass | Production stability - no compromise |
| **⚡ Optimization** | **85%** | Performance & advanced features | Allow experimentation while maintaining quality |
| **🔬 Exploration** | **70%** | Experimental features & edge cases | Innovation requires tolerance for failure |

---

## 📁 Workflow Files

### 1. `ci.yml` - Main CI/CD Pipeline

**Trigger Events:**
- Push to `master`, `main`, or `develop` branches
- Pull requests to these branches
- Manual workflow dispatch

**Jobs:**

#### Job 1: Stabilization Tests (100% Required)
```yaml
- Critical path tests that MUST ALL pass
- Race condition detection
- Build verification
- Zero tolerance for failure
```

**Test Selection:**
- Tests matching: `Test.*Stabilization|Test.*Critical|Test.*E2E_FullPipeline`
- Examples:
  - `TestE2E_FullPipeline_HealthyProject`
  - `TestE2E_FullPipeline_UnhealthyProject`
  - `TestE2E_Dashboard_GeneratesCorrectly`

**Pass Criteria:**
- ALL tests must pass (100%)
- No race conditions detected
- Build succeeds

#### Job 2: Optimization Tests (85% Required)
```yaml
- Performance tests
- Benchmarks
- Advanced features
- 85% pass rate required
```

**Test Selection:**
- Tests matching: `Test.*Optimization|Test.*Performance|Test.*Benchmark|Benchmark.*`
- Examples:
  - `TestE2E_Performance_UnderLoad`
  - `TestE2E_Caching_ReusesResults`
  - `BenchmarkClassifyTest`

**Pass Criteria:**
- At least 85% of tests must pass
- Benchmarks must complete
- No critical performance regressions

#### Job 3: Exploration Tests (70% Required)
```yaml
- Experimental features
- Edge cases
- Future integrations (e.g., VQC)
- 70% pass rate acceptable
```

**Test Selection:**
- Tests matching: `Test.*Exploration|Test.*Experimental|Test.*Edge|Test.*Real.*Project|Test.*Regression`
- Examples:
  - `TestE2E_RealProject_SmallGoPackage`
  - `TestE2E_RealProject_IntegrationWithVQC`
  - `TestE2E_Regression_DetectsDecline`

**Pass Criteria:**
- At least 70% of tests must pass
- Experimental failures are tolerated
- Must not block pipeline completely

#### Job 4: Full Test Suite + Coverage
```yaml
- Run ALL tests
- Generate coverage report
- Coverage threshold: 80%
- Comprehensive quality check
```

**Outputs:**
- `coverage.out` - Go coverage profile
- `coverage.html` - Visual coverage report
- `coverage_summary.txt` - Text summary

#### Job 5: Quality Summary
```yaml
- Aggregate all test results
- Generate quality report
- Comment on PRs
- Final status check
```

**Outputs:**
- Three-Regime Quality Report
- PR comment with test summary
- Final pass/fail decision

---

### 2. `coverage.yml` - Advanced Coverage Reporting

**Trigger Events:**
- Push to main branches
- Pull requests
- Daily scheduled run (00:00 UTC)
- Manual dispatch

**Jobs:**

#### Job 1: Main Coverage Report
```yaml
- Run all tests with coverage
- Generate HTML and text reports
- Check 80% threshold
- Generate coverage badge
```

**Outputs:**
- `coverage.out` - Coverage profile
- `coverage.html` - Visual report
- `coverage_summary.txt` - Text summary
- `coverage_by_package.md` - Package breakdown
- `coverage_badge.json` - Badge data
- `coverage_trend.md` - Historical trend

#### Job 2: Package-Specific Coverage
```yaml
- Test individual packages
- Matrix strategy for parallelism
- Detailed per-package metrics
```

**Tested Packages:**
- `./pkg/intelligence/...`
- `./pkg/learning/...`
- `./pkg/gpu/...`
- `./pkg/vqc/...`
- `./pkg/aimlapi/...`
- `./pkg/conversation/...`

#### Job 3: Historical Coverage Tracking
```yaml
- Track coverage over time
- Store in gh-pages branch
- Generate trend charts
- 30-day history
```

---

### 3. `badges.yml` - Badge Generation

**Trigger Events:**
- Completion of CI or Coverage workflows
- Push to main branches
- Manual dispatch

**Outputs:**
- `BADGES.md` - All badge URLs
- `README_BADGES_SECTION.md` - Ready-to-paste section

---

## 🔧 Configuration

### Environment Variables

| Variable | Value | Purpose |
|----------|-------|---------|
| `GO_VERSION` | `1.24.0` | Go version for builds |
| `COVERAGE_THRESHOLD` | `80.0` | Minimum coverage percentage |
| `STABILIZATION_THRESHOLD` | `100.0` | Stabilization pass rate |
| `OPTIMIZATION_THRESHOLD` | `85.0` | Optimization pass rate |
| `EXPLORATION_THRESHOLD` | `70.0` | Exploration pass rate |

### Customization

To adjust thresholds, edit the workflow YAML files:

```yaml
env:
  COVERAGE_THRESHOLD: 85.0  # Increase coverage requirement
  OPTIMIZATION_THRESHOLD: 90.0  # Stricter optimization
```

---

## 📊 Quality Gates

### Pass/Fail Logic

```go
// Pipeline passes if ALL conditions true:
stabilization_pass_rate == 100%  // ✅ Required
optimization_pass_rate >= 85%    // ✅ Required
exploration_pass_rate >= 70%     // ✅ Required
build_succeeds == true           // ✅ Required
no_race_conditions == true       // ✅ Required

// Coverage is advisory (warning only)
coverage >= 80%  // ⚠️ Warning if fails, but doesn't block
```

### Failure Scenarios

| Scenario | Action | Blocking? |
|----------|--------|-----------|
| Stabilization test fails | ❌ **BLOCK** - Pipeline fails | Yes |
| Optimization < 85% | ❌ **BLOCK** - Pipeline fails | Yes |
| Exploration < 70% | ❌ **BLOCK** - Pipeline fails | Yes |
| Coverage < 80% | ⚠️ **WARN** - Continue with warning | No |
| Build fails | ❌ **BLOCK** - Pipeline fails | Yes |
| Race condition detected | ❌ **BLOCK** - Pipeline fails | Yes |

---

## 🧪 Test Classification

Tests are automatically classified based on naming and tags:

### Stabilization Tests
- **Keywords:** `Stabilization`, `Critical`, `E2E`, `Integration`
- **Examples:**
  ```go
  func TestE2E_FullPipeline_HealthyProject(t *testing.T)
  func TestCriticalUserFlow(t *testing.T)
  ```

### Optimization Tests
- **Keywords:** `Optimization`, `Performance`, `Benchmark`, `Caching`
- **Examples:**
  ```go
  func TestE2E_Performance_UnderLoad(t *testing.T)
  func BenchmarkClassifyTest(b *testing.B)
  ```

### Exploration Tests
- **Keywords:** `Exploration`, `Experimental`, `Edge`, `Real`, `Regression`
- **Examples:**
  ```go
  func TestE2E_RealProject_SmallGoPackage(t *testing.T)
  func TestExperimentalFeature(t *testing.T)
  ```

---

## 📈 Artifacts

### Generated Artifacts

| Artifact | Retention | Purpose |
|----------|-----------|---------|
| `stabilization-test-results` | 30 days | Stabilization test logs |
| `optimization-test-results` | 30 days | Optimization + benchmark logs |
| `exploration-test-results` | 30 days | Exploration test logs |
| `coverage-reports-{sha}` | 90 days | Coverage files + reports |
| `quality-report` | 90 days | Three-Regime quality summary |
| `badges` | 30 days | Badge markdown files |
| `package-coverage-*` | 30 days | Per-package coverage |

### Accessing Artifacts

**Via GitHub UI:**
1. Go to Actions tab
2. Select workflow run
3. Scroll to "Artifacts" section
4. Download desired artifact

**Via CLI (gh):**
```bash
gh run list --workflow=ci.yml
gh run download <run-id>
```

---

## 🚀 Usage Examples

### Running Locally

#### All Tests
```bash
go test ./... -v
```

#### Stabilization Only
```bash
go test ./... -v -run "Test.*Stabilization|Test.*Critical|Test.*E2E"
```

#### With Coverage
```bash
go test ./... -v -coverprofile=coverage.out -covermode=atomic
go tool cover -html=coverage.out -o coverage.html
```

#### Benchmarks
```bash
go test -bench=. -benchmem ./pkg/intelligence/...
```

### Triggering Workflows

#### Push to Branch (Automatic)
```bash
git push origin feature-branch
# Creates PR → triggers ci.yml and coverage.yml
```

#### Manual Trigger
```bash
gh workflow run ci.yml
gh workflow run coverage.yml
```

---

## 📋 PR Integration

### Automatic PR Comments

When a PR is created, the CI/CD system automatically comments with:

1. **Quality Report:**
   - Three-Regime test results
   - Overall status
   - Pass/fail by regime

2. **Coverage Report:**
   - Overall coverage percentage
   - Package-level breakdown
   - Detailed summary

**Example PR Comment:**
```markdown
# 🎯 Asymmetrica UrbanLens - Three-Regime Quality Report

**Generated:** 2025-12-27 10:30:45 UTC
**Commit:** abc1234
**Branch:** feature/new-engine

## Three-Regime Test Results

| Regime | Threshold | Status |
|--------|-----------|--------|
| 🎯 Stabilization | 100% | ✅ success |
| ⚡ Optimization  | 85%  | ✅ success |
| 🔬 Exploration   | 70%  | ✅ success |

## Overall Status

✅ **ALL QUALITY GATES PASSED!**

The codebase meets Asymmetrica's mathematical rigor standards:
- Critical paths are 100% stable
- Performance optimizations validated
- Experimental features explored
```

---

## 🔍 Troubleshooting

### Common Issues

#### Issue 1: Tests Not Detected
**Symptom:** Workflow reports "No stabilization tests found!"

**Solution:**
- Check test naming conventions
- Ensure tests match keywords (e.g., `TestE2E_*`, `Test*Stabilization`)
- Run locally: `go test ./... -v -run "Test.*E2E"`

#### Issue 2: Coverage Below Threshold
**Symptom:** Coverage report shows < 80%

**Solution:**
- Add tests for uncovered packages
- Check `coverage.html` for specific uncovered lines
- Run: `go test ./... -coverprofile=coverage.out && go tool cover -html=coverage.out`

#### Issue 3: Workflow Timeouts
**Symptom:** Job exceeds timeout (10-30 minutes)

**Solution:**
- Check for infinite loops in tests
- Reduce large dataset sizes in test fixtures
- Optimize slow tests (use `-short` flag)

#### Issue 4: Race Condition Detected
**Symptom:** `-race` flag detects data races

**Solution:**
- Review concurrent code in identified file
- Add proper mutex/channel synchronization
- Test locally: `go test -race ./...`

---

## 🎯 Best Practices

### Writing Tests

1. **Name tests clearly:**
   ```go
   // Good
   func TestE2E_FullPipeline_HealthyProject(t *testing.T)

   // Bad
   func TestStuff(t *testing.T)
   ```

2. **Tag tests appropriately:**
   ```go
   // Critical path
   func TestCriticalUserFlow(t *testing.T) { ... }

   // Performance
   func TestE2E_Performance_UnderLoad(t *testing.T) { ... }

   // Experimental
   func TestExperimentalVQCIntegration(t *testing.T) { ... }
   ```

3. **Use table-driven tests:**
   ```go
   tests := []struct {
       name     string
       input    Input
       expected Output
   }{
       {"case1", input1, output1},
       {"case2", input2, output2},
   }

   for _, tt := range tests {
       t.Run(tt.name, func(t *testing.T) {
           // Test logic
       })
   }
   ```

4. **Write meaningful assertions:**
   ```go
   // Good
   if result.SHM < 0.50 {
       t.Errorf("Expected SHM ≥ 0.50 for healthy project, got %.3f", result.SHM)
   }

   // Bad
   if result.SHM < 0.50 {
       t.Error("Bad SHM")
   }
   ```

### Maintaining Quality Gates

1. **Don't lower thresholds without discussion**
   - Stabilization: Always 100%
   - Optimization: 85% minimum
   - Exploration: 70% minimum

2. **Add tests when adding features**
   - Every new feature → at least 1 stabilization test
   - Complex features → optimization + exploration tests

3. **Monitor coverage trends**
   - Check coverage history in gh-pages branch
   - Don't let coverage decrease over time

---

## 📚 References

### Asymmetrica Documentation
- `ASYMMETRICA_MATHEMATICAL_STANDARD.md` - Core equation
- `VEDIC_META_OPTIMIZATION.md` - 53× speedups
- `GODEL_PRIZE_COMPLEXITY_THEORY.md` - Williams batching

### Three-Regime Implementation
- `pkg/intelligence/three_regime_planner.go` - Classification logic
- `pkg/intelligence/three_regime_planner_test.go` - Test examples

### Testing Standards
- `pkg/intelligence/integration_e2e_pipeline_test.go` - E2E test examples
- `pkg/intelligence/sonars/*_test.go` - Sonar-specific tests

---

## 🤝 Contributing

When contributing to this codebase:

1. **Write tests first** (TDD approach)
2. **Run locally before pushing:**
   ```bash
   go test ./... -v -race
   go test ./... -coverprofile=coverage.out
   ```
3. **Ensure all regimes pass:**
   - Stabilization: 100%
   - Optimization: ≥85%
   - Exploration: ≥70%
4. **Monitor CI/CD feedback in PR**
5. **Fix failures promptly** (don't merge with failing tests)

---

## 📞 Support

For CI/CD issues:
1. Check this documentation
2. Review workflow logs in GitHub Actions
3. Run tests locally to reproduce
4. Check test classification (naming/keywords)

**Philosophy:** *Mathematical rigor encoded into every pipeline stage!*

---

**Om Lokah Samastah Sukhino Bhavantu**
*May all beings benefit from these quality gates!*

---

*Generated by Asymmetrica CI/CD System - 2025-12-27*
