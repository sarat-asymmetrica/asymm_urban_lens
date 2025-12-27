# Quick Start - CI/CD for Developers

**For:** Developers working on Asymmetrica UrbanLens
**Updated:** 2025-12-27

---

## 🚀 The 30-Second Overview

**Three-Regime Testing System = Math-Encoded Quality Gates**

```
Stabilization: 100% ✅ (Critical path - MUST pass)
Optimization:   85% ⚡ (Performance - HIGH bar)
Exploration:    70% 🔬 (Experimental - TOLERANCE for innovation)
```

**Every PR automatically runs:**
1. ✅ All tests categorized by regime
2. 📊 Coverage analysis (80% threshold)
3. 🏆 Quality report generated
4. 💬 Results posted to PR

---

## 🧪 Running Tests Locally

### All Tests
```bash
go test ./... -v
```

### By Regime

**Stabilization (Critical):**
```bash
go test ./... -v -run "Test.*Stabilization|Test.*Critical|Test.*E2E"
```

**Optimization (Performance):**
```bash
go test ./... -v -run "Test.*Optimization|Test.*Performance|Benchmark.*"
go test -bench=. -benchmem ./pkg/intelligence/...
```

**Exploration (Experimental):**
```bash
go test ./... -v -run "Test.*Exploration|Test.*Experimental|Test.*Real"
```

### With Coverage
```bash
go test ./... -v -coverprofile=coverage.out -covermode=atomic
go tool cover -html=coverage.out  # Open in browser
```

### Race Detection
```bash
go test -race ./...
```

---

## 📝 Writing Tests

### Naming Convention

**Pattern:** `Test[E2E|Unit|Integration]_[Feature]_[Scenario]`

**Examples:**
```go
// Stabilization (100% required)
func TestE2E_FullPipeline_HealthyProject(t *testing.T) { ... }
func TestCriticalUserAuthentication(t *testing.T) { ... }

// Optimization (85% required)
func TestE2E_Performance_UnderLoad(t *testing.T) { ... }
func BenchmarkSHMCalculation(b *testing.B) { ... }

// Exploration (70% required)
func TestE2E_RealProject_Integration(t *testing.T) { ... }
func TestExperimentalVQCAcceleration(t *testing.T) { ... }
```

### Keywords for Auto-Classification

| Regime | Keywords |
|--------|----------|
| **Stabilization** | `Stabilization`, `Critical`, `E2E`, `Integration`, `Production` |
| **Optimization** | `Optimization`, `Performance`, `Benchmark`, `Caching`, `Speed` |
| **Exploration** | `Exploration`, `Experimental`, `Edge`, `Real`, `Regression`, `Future` |

### Table-Driven Test Pattern
```go
func TestFeature(t *testing.T) {
    tests := []struct {
        name     string
        input    Input
        expected Output
    }{
        {"happy path", validInput, validOutput},
        {"edge case", edgeInput, edgeOutput},
        {"error case", invalidInput, errorOutput},
    }

    for _, tt := range tests {
        t.Run(tt.name, func(t *testing.T) {
            actual := Feature(tt.input)
            if actual != tt.expected {
                t.Errorf("got %v, want %v", actual, tt.expected)
            }
        })
    }
}
```

---

## 🔄 PR Workflow

### 1. Create Branch
```bash
git checkout -b feature/your-feature
```

### 2. Write Code + Tests
- Add feature code
- Write at least 1 stabilization test
- Optional: optimization + exploration tests

### 3. Run Tests Locally
```bash
go test ./... -v -race
go test ./... -coverprofile=coverage.out
```

### 4. Commit & Push
```bash
git add .
git commit -m "feat: your feature"
git push origin feature/your-feature
```

### 5. Create PR
- CI/CD runs automatically
- Check Actions tab for results
- Quality report posted as PR comment

### 6. Review Results

**Green ✅:** All quality gates passed!
- Stabilization: 100% ✅
- Optimization: ≥85% ✅
- Exploration: ≥70% ✅

**Red ❌:** Something failed
- Check workflow logs
- Fix failing tests
- Push again (CI re-runs automatically)

### 7. Merge
- Only merge when ALL checks pass
- Squash commits if needed
- Delete feature branch after merge

---

## 📊 Understanding Test Results

### GitHub Actions Output

**Example Stabilization Job:**
```
🎯 Stabilization Tests (100% Required)
================================================
STABILIZATION TESTS - 100% Pass Rate Required
These are CRITICAL PATH tests that MUST pass
================================================

PASS: TestE2E_FullPipeline_HealthyProject
PASS: TestE2E_FullPipeline_UnhealthyProject
PASS: TestE2E_Dashboard_GeneratesCorrectly

📊 Stabilization Results: 3 passed, 0 failed
✅ All stabilization tests passed!
```

**Example Quality Report (PR Comment):**
```markdown
# 🎯 Asymmetrica UrbanLens - Three-Regime Quality Report

**Commit:** abc1234

## Three-Regime Test Results

| Regime | Threshold | Status |
|--------|-----------|--------|
| 🎯 Stabilization | 100% | ✅ success |
| ⚡ Optimization  | 85%  | ✅ success |
| 🔬 Exploration   | 70%  | ✅ success |

✅ **ALL QUALITY GATES PASSED!**
```

---

## 🐛 Troubleshooting

### Issue: "No stabilization tests found!"

**Cause:** Test names don't match keywords

**Fix:**
```go
// ❌ Bad
func TestMyFeature(t *testing.T) { ... }

// ✅ Good
func TestE2E_MyFeature_Stabilization(t *testing.T) { ... }
```

### Issue: Coverage < 80%

**Find uncovered code:**
```bash
go test ./... -coverprofile=coverage.out
go tool cover -html=coverage.out
# Opens browser with highlighted coverage
```

**Add tests for red-highlighted code**

### Issue: Race condition detected

**Reproduce locally:**
```bash
go test -race ./...
```

**Fix:** Add proper synchronization (mutex, channels)

### Issue: Workflow timeout

**Check:** Test taking too long?

**Fix:**
- Use `-short` flag for expensive tests
- Reduce test dataset size
- Optimize slow operations

---

## 🎯 Quality Gate Philosophy

### Why Three Regimes?

**Mathematical Foundation:**
- **R1 (30%):** Exploration - high variance, divergent thinking
- **R2 (20%):** Optimization - gradient descent, peak complexity
- **R3 (50%):** Stabilization - convergence, production-ready

**In Testing:**
- **Stabilization (100%):** Zero compromise on critical paths
- **Optimization (85%):** High bar, but allow some experimentation
- **Exploration (70%):** Innovation requires tolerance for failure

### What Blocks Merge?

| Condition | Blocks? |
|-----------|---------|
| Stabilization test fails | ✅ YES |
| Optimization < 85% | ✅ YES |
| Exploration < 70% | ✅ YES |
| Build fails | ✅ YES |
| Race condition | ✅ YES |
| Coverage < 80% | ❌ NO (warning only) |

---

## 🏆 Best Practices

### Do ✅
- Write tests FIRST (TDD)
- Name tests clearly with keywords
- Run tests locally before pushing
- Fix failures immediately
- Add tests when adding features
- Check coverage for new code

### Don't ❌
- Push untested code
- Ignore failing tests
- Lower quality thresholds
- Merge with red CI
- Skip race detection
- Write tests without assertions

---

## 📚 Resources

### Documentation
- [Full CI/CD Documentation](./.github/CI_CD_DOCUMENTATION.md)
- [Test Examples](../pkg/intelligence/integration_e2e_pipeline_test.go)
- [Three-Regime Planner](../pkg/intelligence/three_regime_planner.go)

### Workflows
- [Main CI](./workflows/ci.yml)
- [Coverage](./workflows/coverage.yml)
- [Badges](./workflows/badges.yml)

### Commands Reference
```bash
# Test all
go test ./... -v

# Test with coverage
go test ./... -coverprofile=coverage.out

# Test with race detection
go test -race ./...

# Benchmarks
go test -bench=. -benchmem ./pkg/intelligence/...

# View coverage
go tool cover -html=coverage.out

# Coverage by package
go test ./pkg/intelligence/... -coverprofile=intel_coverage.out

# Run specific test
go test ./pkg/intelligence -run TestE2E_FullPipeline_HealthyProject -v
```

---

## 💡 Pro Tips

1. **Write stabilization tests first** - ensures critical paths work
2. **Use table-driven tests** - easy to add cases
3. **Test error cases** - not just happy paths
4. **Run race detector** - catch concurrency bugs early
5. **Check coverage locally** - don't wait for CI
6. **Name tests descriptively** - helps with debugging
7. **Keep tests fast** - enables quick iteration

---

## 🤝 Need Help?

1. Check [CI/CD Documentation](./.github/CI_CD_DOCUMENTATION.md)
2. Review test examples in `pkg/intelligence/*_test.go`
3. Check workflow logs in GitHub Actions
4. Ask in PR comments

---

**Remember:** The CI/CD system is here to HELP you ship quality code faster, not to slow you down!

---

*Generated by Asymmetrica CI/CD Team - 2025-12-27*

**Om Lokah Samastah Sukhino Bhavantu** 🙏
