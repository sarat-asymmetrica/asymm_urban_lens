# Performance Report

**Generated**: 2025-12-27T09:42:22+05:30

## Summary

- **Total Operations**: 4
- **Total Samples**: 116000
- **Overall Status**: **CRITICAL**

### Status Distribution

- ✅ Excellent: 0
- ✓ Good: 0
- ⚠️ Needs Work: 0
- ❌ Critical: 4

## Operation Details

### digital_root

**Status**: ❌ CRITICAL

**Statistics**:

- Count: 100000
- Ops/Sec: 4.76 M
- Avg Duration: 210ns
- P50: 0s
- P95: 0s
- P99: 0s
- Avg Allocs: 0 bytes/op

**Target**:

- Target Ops/Sec: 100.00 M
- Throughput Gap: -95.2%
- Description: Vedic digital root (53× speedup)

**Recommendations**:

- CRITICAL: 95.2% below target (4.76 M ops/sec vs 100.00 M ops/sec)
- Consider GPU acceleration (50-100× speedup)
- Apply Williams batching O(√n × log₂n)
- Use object pooling to eliminate allocations

---

### quaternion_multiply

**Status**: ❌ CRITICAL

**Statistics**:

- Count: 10000
- Ops/Sec: 0.00 M
- Avg Duration: 0s
- P50: 0s
- P95: 0s
- P99: 0s
- Avg Allocs: 0 bytes/op

**Target**:

- Target Ops/Sec: 1.00 M
- Throughput Gap: -100.0%
- Description: CPU-only quaternion multiplication

**Recommendations**:

- CRITICAL: 100.0% below target (0.00 M ops/sec vs 1.00 M ops/sec)
- Consider GPU acceleration (50-100× speedup)
- Apply Williams batching O(√n × log₂n)
- Use object pooling to eliminate allocations

---

### quaternion_slerp

**Status**: ❌ CRITICAL

**Statistics**:

- Count: 5000
- Ops/Sec: 0.00 M
- Avg Duration: 0s
- P50: 0s
- P95: 0s
- P99: 0s
- Avg Allocs: 0 bytes/op

**Target**:

- Target Ops/Sec: 0.50 M
- Throughput Gap: -100.0%
- Description: Spherical linear interpolation

**Recommendations**:

- CRITICAL: 100.0% below target (0.00 M ops/sec vs 0.50 M ops/sec)
- Consider GPU acceleration (50-100× speedup)
- Apply Williams batching O(√n × log₂n)
- Use object pooling to eliminate allocations

---

### vqc_engine

**Status**: ❌ CRITICAL

**Statistics**:

- Count: 1000
- Ops/Sec: 0.00 M
- Avg Duration: 0s
- P50: 0s
- P95: 0s
- P99: 0s
- Avg Allocs: 0 bytes/op

**Target**:

- Target Ops/Sec: 71.00 M
- Throughput Gap: -100.0%
- Description: Quaternion operations on GPU (71M ops/sec target)

**Recommendations**:

- CRITICAL: 100.0% below target (0.00 M ops/sec vs 71.00 M ops/sec)
- Consider GPU acceleration (50-100× speedup)
- Apply Williams batching O(√n × log₂n)
- Use object pooling to eliminate allocations

---

