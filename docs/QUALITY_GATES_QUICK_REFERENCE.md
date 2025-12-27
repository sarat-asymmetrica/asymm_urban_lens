# 🚀 Quality Gates Quick Reference

**Quick access guide for daily development**

---

## 📊 Decision Matrix (Memorize This!)

| SHM Score | Regime | Action |
|-----------|--------|--------|
| **≥ 0.85** | 🟢 STABILIZATION | ✅ Auto-deploy to PRODUCTION |
| **0.70 - 0.84** | 🟡 OPTIMIZATION | ⚠️ STAGING only, manual prod approval |
| **< 0.70** | 🔴 EXPLORATION | ❌ Deployment BLOCKED |

---

## 🧪 Test Requirements

| Test Type | Pass Rate | Example |
|-----------|-----------|---------|
| **Stabilization** | **100%** | `*_exhaustive_test.go` |
| **Optimization** | **85%+** | `*_integration_test.go` |
| **Exploration** | **70%+** | New feature tests |

---

## ⚡ Quick Commands

```bash
# Check quality locally
go run scripts/quality-gate.go --verbose

# Run stabilization tests (must pass 100%)
go test -run "Test.*Exhaustive" ./...

# Run all tests with coverage
go test -cover ./...

# Build quality gate
go build -o quality-gate scripts/quality-gate.go
./quality-gate

# Install pre-commit hook
chmod +x scripts/pre-commit.sh
git config core.hooksPath scripts/
```

---

## 🔧 Pre-Commit Hook

**What it checks:**
1. ✅ Go formatting
2. ✅ Stabilization tests (100% pass)
3. ✅ No orphaned TODOs
4. ✅ No console.log or debugger
5. ✅ No hardcoded credentials
6. ✅ Linting (if available)
7. ✅ Test coverage on changed files

**Bypass** (emergency only):
```bash
git commit --no-verify
```

---

## 📋 PR Checklist (Copy-Paste)

```markdown
Quality Gate Status:
- [ ] SHM ≥ 0.70 ✅
- [ ] Stabilization tests: 100% pass
- [ ] Optimization tests: 85%+ pass
- [ ] Exploration tests: 70%+ pass
- [ ] No hardcoded secrets
- [ ] No console.log/debugger
- [ ] Coverage ≥ 70%
```

---

## 🐛 Common Issues & Fixes

### Issue: Quality gate fails (SHM < 0.70)

**Fix:**
```bash
# 1. See detailed report
go run scripts/quality-gate.go --verbose

# 2. Identify weakest dimension
# Look for "Weakest: code" in output

# 3. Fix that dimension
#    - code: Reduce complexity, improve naming
#    - design: Fix spacing, colors
#    - ux: Improve accessibility
```

### Issue: Stabilization tests failing

**Fix:**
```bash
# 1. Run exhaustive tests
go test -v -run "Test.*Exhaustive" ./...

# 2. Fix failing tests (CRITICAL - must be 100%)

# 3. Re-run quality gate
go run scripts/quality-gate.go
```

### Issue: Pre-commit hook blocking commit

**Fix:**
```bash
# 1. Read pre-commit output carefully
# 2. Fix reported issues
# 3. Re-commit

# Emergency bypass (NOT recommended):
git commit --no-verify
```

---

## 📈 SHM Formula (For Reference)

```
SHM = UX×0.25 + Design×0.25 + Code×0.125 +
      Semantic×0.125 + Journey×0.125 + State×0.125

Where each sonar score is 0.0-1.0
```

---

## 🎯 Regime Goals

### 🔴 EXPLORATION (SHM < 0.70)
**Goal**: Stabilize core functionality
**Focus**: Get basic tests passing, reduce critical bugs
**Next**: Reach SHM ≥ 0.70 to enter OPTIMIZATION

### 🟡 OPTIMIZATION (0.70 ≤ SHM < 0.85)
**Goal**: Refine quality, reduce tech debt
**Focus**: Improve weakest dimension, increase coverage
**Next**: Reach SHM ≥ 0.85 to enter STABILIZATION

### 🟢 STABILIZATION (SHM ≥ 0.85)
**Goal**: Maintain quality, prepare for production
**Focus**: Keep all tests passing, prevent regression
**Ready**: Can auto-deploy to production!

---

## 🔮 Reading Quality Gate Output

```
╔═══════════════════════════════════════════════╗
║     ASYMMETRICA QUALITY GATE REPORT           ║
╚═══════════════════════════════════════════════╝

✅ QUALITY GATE: PASSED          ← Overall status

SHM Score:  0.875                ← Your quality score
Regime:     STABILIZATION        ← Current phase
Weakest:    code                 ← Focus here!
Strongest:  journey              ← Doing well!

Total:      100                  ← Test counts
Passed:     95 (95.0%)
Failed:     5                    ← Fix these!
Coverage:   87.0%                ← Aim for 80%+

Action:     AUTO_DEPLOY_PROD     ← Deployment decision
            ✅ Auto-deploy to PRODUCTION
```

---

## 💡 Pro Tips

1. **Run quality gate before pushing**: Saves CI/CD time
2. **Fix weakest dimension first**: Maximum SHM improvement
3. **Don't skip stabilization tests**: They're critical for a reason
4. **Watch coverage on new code**: Should be ≥70%
5. **Use pre-commit hook**: Catches issues before commit
6. **Read recommendations**: They're generated based on your metrics

---

## 📞 Getting Help

**Quality gate question?**: Check [QUALITY_GATES.md](./QUALITY_GATES.md)

**Bug in quality gate?**: Open issue with label `bug` + `quality-gates`

**How do I improve SHM?**: Run with `--verbose`, focus on weakest dimension

---

## 🎓 For New Developers

**Day 1 Setup:**
```bash
# 1. Clone repo
git clone https://github.com/asymmetrica/urbanlens

# 2. Install pre-commit hook
cd urbanlens
chmod +x scripts/pre-commit.sh
git config core.hooksPath scripts/

# 3. Run quality gate
go run scripts/quality-gate.go --verbose

# 4. You're ready!
```

**Daily Workflow:**
```bash
# 1. Make changes
# 2. Write tests (classify by regime!)
# 3. Run quality gate
go run scripts/quality-gate.go

# 4. Commit (pre-commit hook runs automatically)
git add .
git commit -m "feat: my awesome feature"

# 5. Push and create PR (template guides you)
git push
```

---

**Remember**: Quality gates are here to **help** you ship better code, not **block** you. If gate fails, it's feedback - not failure! 🚀

---

**Om Lokah Samastah Sukhino Bhavantu** 🙏

**Version**: 1.0.0 | **Date**: 2025-12-27
