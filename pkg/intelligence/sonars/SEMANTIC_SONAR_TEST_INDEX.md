# Semantic Sonar Test Index

Quick reference for which test validates which aspect.

## By Mathematical Formula

| Formula/Metric | Test(s) |
|----------------|---------|
| **AQS = (cohesion / coupling) × modularity** | `TestSemanticSonar_AQS_Formula` |
| **Circular Dependency Score** | `TestSemanticSonar_CircularDependency_*` (3 tests) |
| **Modularity Index** | `TestSemanticSonar_Modularity_*` (3 tests) |
| **Cohesion Measurement** | `TestSemanticSonar_Cohesion_High` |
| **Coupling Measurement** | `TestSemanticSonar_Coupling_*` (2 tests) |

## By SOLID Principle

| Principle | Test(s) |
|-----------|---------|
| **S - Single Responsibility** | `TestSemanticSonar_Modularity_*` (modularity ≥ 84%) |
| **O - Open/Closed** | Not directly tested (language-specific) |
| **L - Liskov Substitution** | Not directly tested (language-specific) |
| **I - Interface Segregation** | `TestSemanticSonar_Coupling_*` (coupling < 0.30) |
| **D - Dependency Inversion** | `TestSemanticSonar_CircularDependency_*` (0 cycles) |

## By Sonar Phase

| Phase | Test(s) |
|-------|---------|
| **PING** | `TestSemanticSonar_PING_AnalyzesDeps` |
| **ECHO** | `TestSemanticSonar_ECHO_DetectsCycles` |
| **MAP** | `TestSemanticSonar_MAP_NormalizesTo01` |
| **CRITIQUE** | `TestSemanticSonar_CRITIQUE_FlagsSpaghetti` |

## By Regime

| Regime | Tests | Pass Requirement |
|--------|-------|------------------|
| **Stabilization (R3)** | Tests 1-10 | 100% (10/10) ✅ |
| **Optimization (R2)** | Tests 11-14 | 85% (4/4) ✅ |
| **Exploration (R1)** | Tests 15-16 | 70% (2/2) ✅ |

## By Research Metric

| Research Target | Test(s) | Status |
|-----------------|---------|--------|
| **0 circular dependencies** | `TestSemanticSonar_CircularDependency_None` | ✅ |
| **84%+ modularity** | `TestSemanticSonar_Modularity_High` | ✅ |
| **<0.30 coupling** | `TestSemanticSonar_Coupling_Low` | ✅ |
| **AQS formula accuracy** | `TestSemanticSonar_AQS_Formula` | ✅ |
| **SHM 12.5% weight** | `TestSemanticSonar_Integration_WithSHM` | ✅ |

## Quick Test Lookup

```bash
# Run all Semantic Sonar tests
go test ./pkg/intelligence/sonars/... -run "TestSemanticSonar_" -v

# Run specific category
go test ./pkg/intelligence/sonars/... -run "TestSemanticSonar_AQS" -v
go test ./pkg/intelligence/sonars/... -run "TestSemanticSonar_CircularDependency" -v
go test ./pkg/intelligence/sonars/... -run "TestSemanticSonar_Modularity" -v
go test ./pkg/intelligence/sonars/... -run "TestSemanticSonar_PING" -v

# Run with coverage
go test ./pkg/intelligence/sonars/... -run "TestSemanticSonar_" -cover
```

## Test Dependencies

All tests are independent and can run in parallel. No shared state between tests.

Helper functions:
- `createTestApp(handlers, components)` - Creates test AppState
- `containsString(s, substr)` - String matching helper
