# How to Use Cold-Cache Benchmarks

**Purpose**: Measure REALISTIC production performance, not synthetic cache-hot fantasies.

---

## Quick Start

### Run All Benchmarks

```bash
cd /c/Projects/asymm_urbanlens/benchmarks
go test -bench=. -benchmem -benchtime=1s . | tee results.txt
```

### Run Specific Comparisons

```bash
# Warm cache (baseline)
go test -bench=Benchmark_Warm_SimpleCompute -benchmem -benchtime=2s .

# Cold cache (reality)
go test -bench=Benchmark_Cold_SimpleCompute -benchmem -benchtime=500ms .
```

**Note**: Cold benchmarks run slower, so use shorter `-benchtime` to avoid waiting forever!

---

## Interpreting Results

### Example Output

```
Benchmark_Warm_SimpleCompute-4   8266   149398 ns/op   0 B/op   0 allocs/op
Benchmark_Cold_SimpleCompute-4     19  74152489 ns/op  16777232 B/op  1 allocs/op
```

### What Each Column Means

| Column | Meaning | Warm | Cold |
|--------|---------|------|------|
| **Name** | Benchmark identifier | Benchmark_Warm_... | Benchmark_Cold_... |
| **Iterations** | How many times Go ran it | 8,266 | 19 |
| **ns/op** | Nanoseconds per operation | 149,398 ns | 74,152,489 ns |
| **B/op** | Bytes allocated per op | 0 | 16,777,232 |
| **allocs/op** | Allocations per op | 0 | 1 |

### Calculate the Cache Penalty

```
Cache Penalty = Cold ns/op ÷ Warm ns/op
              = 74,152,489 ÷ 149,398
              = 496×
```

**Translation**: "This operation is 496× slower in production than benchmarks suggest!"

---

## Understanding Memory Allocations

### Warm Cache

```
0 B/op, 0 allocs/op
```

**Meaning**: Data already in cache, no new allocations needed. This is IDEAL but UNREALISTIC in production.

### Cold Cache

```
16777232 B/op, 1 allocs/op
```

**Meaning**:
- 16 MB allocated for cache flush
- 1 allocation (the flush buffer)
- This simulates production where caches are cold

**Why 16 MB?**
- Typical L3 cache: 8 MB
- Flush buffer: 2× L3 = 16 MB
- Ensures complete cache eviction

---

## Common Patterns

### Pattern 1: Massive Slowdown (10,000×+)

```
Benchmark_Warm_RandomAccess-4   97470   13095 ns/op
Benchmark_Cold_RandomAccess-4      15  202900393 ns/op
Ratio: 15,493×
```

**What This Means**:
- Pointer chasing / random access
- Every access is a cache miss
- Production will be TERRIBLE
- **Action**: Redesign data structures for locality

### Pattern 2: Moderate Slowdown (100-1000×)

```
Benchmark_Warm_ArraySum-4   22458   56645 ns/op
Benchmark_Cold_ArraySum-4      19  70139221 ns/op
Ratio: 1,238×
```

**What This Means**:
- Sequential access helps
- Prefetcher kicks in
- Still bad, but not catastrophic
- **Action**: Use SIMD, batching, prefetch hints

### Pattern 3: Small Slowdown (2-10×)

```
Benchmark_Warm_MapLookup-4   92902   13106 ns/op
Benchmark_Cold_MapLookup-4     182  6822958 ns/op
Ratio: 521×
```

**What This Means**:
- Some cache benefit from map buckets
- Hash table locality helps
- Acceptable for non-hot-path
- **Action**: Pre-size maps, use integer keys

---

## Creating Your Own Cold-Cache Benchmarks

### Step 1: Identify Hot Path

Find code that runs frequently:
- Request handlers
- Database queries
- Computation kernels
- Data processing loops

### Step 2: Write Warm Benchmark (Baseline)

```go
func Benchmark_Warm_MyOperation(b *testing.B) {
    // Setup
    data := createTestData()

    // Warmup (optional but realistic)
    for i := 0; i < 10; i++ {
        myOperation(data)
    }

    b.ResetTimer()
    for i := 0; i < b.N; i++ {
        result := myOperation(data)
        _ = result  // Prevent dead code elimination
    }
}
```

### Step 3: Write Cold Benchmark (Reality)

```go
func Benchmark_Cold_MyOperation(b *testing.B) {
    // Setup
    data := createTestData()

    b.ResetTimer()
    for i := 0; i < b.N; i++ {
        ClearCPUCache()  // Force cold cache!

        result := myOperation(data)
        _ = result
    }
}
```

### Step 4: Run and Compare

```bash
go test -bench=Benchmark_Warm_MyOperation -benchtime=2s .
go test -bench=Benchmark_Cold_MyOperation -benchtime=500ms .
```

### Step 5: Analyze

```python
# Calculate penalty
penalty = cold_ns_per_op / warm_ns_per_op

# Estimate realistic throughput
realistic_ops_per_sec = 1_000_000_000 / cold_ns_per_op

# Calculate production capacity
servers = 10
total_capacity = realistic_ops_per_sec * servers
```

---

## Advanced: Adding I/O Simulation

Real production has file I/O, network latency, database queries. Add these to cold benchmarks:

```go
func Benchmark_Cold_Production_MyOperation(b *testing.B) {
    b.ResetTimer()
    for i := 0; i < b.N; i++ {
        ClearCPUCache()

        // Simulate file read (SSD: 1-5ms)
        time.Sleep(2 * time.Millisecond)

        data := loadFromDisk()
        result := myOperation(data)

        // Simulate database write (5-10ms)
        time.Sleep(5 * time.Millisecond)

        saveToDB(result)
    }
}
```

---

## Troubleshooting

### Problem 1: Cold benchmark is TOO slow

**Symptom**:
```
Benchmark_Cold_MyOperation-4   1  10000000000 ns/op
(timeout!)
```

**Solution**:
- Reduce `-benchtime` to `100ms` or `500ms`
- Reduce data size
- Cache flush is expensive - this is expected!

### Problem 2: Warm and cold are the same

**Symptom**:
```
Benchmark_Warm_MyOp-4   1000  1500 ns/op
Benchmark_Cold_MyOp-4   1000  1600 ns/op
Ratio: 1.06× (too small!)
```

**Likely Causes**:
1. Data size too small (fits in L1 cache)
2. Operation is compute-bound (not memory-bound)
3. Cache flush not working

**Solutions**:
1. Increase data size to > 100 KB
2. If compute-bound, this is correct! Document it.
3. Verify ClearCPUCache() is called

### Problem 3: Allocations are confusing

**Symptom**:
```
Warm: 0 B/op, 0 allocs/op  (expected)
Cold: 16777232 B/op, 1 allocs/op  (the 16 MB flush buffer)
```

**Explanation**: The 16 MB allocation is the cache flush buffer, NOT your code's allocation!

**To measure YOUR code's allocations**:
```go
func Benchmark_YourAllocs(b *testing.B) {
    b.ReportAllocs()  // Enable allocation tracking
    for i := 0; i < b.N; i++ {
        // Your code that allocates
        data := make([]int, 100)
        _ = data
    }
}
```

---

## Integration with Existing Tests

### Option 1: Add to existing test file

```go
// File: pkg/vqc/vqc_test.go

// Existing warm benchmark
func BenchmarkDigitalRoot(b *testing.B) {
    for i := 0; i < b.N; i++ {
        DigitalRoot(i)
    }
}

// NEW: Add cold variant
func BenchmarkDigitalRoot_Cold(b *testing.B) {
    for i := 0; i < b.N; i++ {
        if i % 100 == 0 {
            ClearCPUCache()  // Clear every 100 iterations
        }
        DigitalRoot(i)
    }
}
```

### Option 2: Create separate cold_test.go

```go
// File: pkg/vqc/vqc_cold_test.go

//go:build cold_benchmarks
// +build cold_benchmarks

package vqc

// All cold-cache benchmarks here
func BenchmarkCold_DigitalRoot(b *testing.B) { ... }
func BenchmarkCold_SLERP(b *testing.B) { ... }
func BenchmarkCold_Williams(b *testing.B) { ... }
```

**Run with**:
```bash
go test -tags=cold_benchmarks -bench=. ./pkg/vqc/
```

---

## Capacity Planning Example

### Step 1: Run Production Simulation

```bash
go test -bench=Benchmark_Cold_Production -benchmem -benchtime=10s .
```

**Result**:
```
Benchmark_Cold_Production-4   100  12345678 ns/op
```

### Step 2: Calculate Throughput

```python
ns_per_op = 12_345_678
ops_per_second = 1_000_000_000 / ns_per_op
                = 81 ops/sec  (per core)
```

### Step 3: Scale to Production

```python
cores_per_server = 16
servers = 10

total_capacity = ops_per_second * cores_per_server * servers
                = 81 * 16 * 10
                = 12,960 ops/sec
```

### Step 4: Add Safety Margin

```python
# 50% headroom for spikes
production_capacity = total_capacity * 0.5
                     = 6,480 ops/sec
```

### Step 5: Compare to Requirements

```python
required_ops_per_sec = 10_000

if production_capacity < required_ops_per_sec:
    additional_servers = ceil(required_ops_per_sec / (ops_per_second * cores * 0.5))
    print(f"Need {additional_servers} more servers")
```

---

## When to Use Each Benchmark Type

| Scenario | Benchmark Type | Reason |
|----------|---------------|--------|
| **Algorithm comparison** | Warm | Fair comparison, caching doesn't matter |
| **Capacity planning** | Cold | Must account for real-world cache misses |
| **Hot path optimization** | Cold | Optimize for worst case |
| **API documentation** | Warm | Show best-case performance |
| **SLA commitments** | Cold | Guarantee realistic numbers |
| **Academic research** | Warm | Isolate algorithm complexity |
| **Production monitoring** | Cold | Detect regressions in reality |

---

## Carmack's Wisdom Applied

> "Measure what matters. Cache-cold numbers matter more than cache-hot fantasies."

**Before Cold-Cache Benchmarks**:
- "We can handle 100,000 ops/sec!" (warm cache lie)
- Production: crashes at 100 ops/sec
- Confused engineers, angry customers

**After Cold-Cache Benchmarks**:
- "We can handle 80 ops/sec per core" (cold cache truth)
- Plan for 10 cores = 800 ops/sec
- Add 50% headroom = 400 ops/sec guarantee
- Production: stable, predictable, no surprises

---

## Files in This Directory

| File | Purpose |
|------|---------|
| `cold_cache_bench_test.go` | Actual benchmark code (stdlib only) |
| `COLD_CACHE_PERFORMANCE_REPORT.md` | Detailed analysis of results |
| `HOW_TO_USE_COLD_CACHE_BENCHMARKS.md` | This guide |
| `go.mod` | Standalone module (no dependencies) |
| `benchmark_results.txt` | Raw output from last run |

---

## Next Steps

1. ✅ Run benchmarks: `go test -bench=. -benchmem .`
2. ✅ Read report: `COLD_CACHE_PERFORMANCE_REPORT.md`
3. ⏭️  Apply to UrbanLens hot paths:
   - `pkg/vqc/*` (VQC operations)
   - `pkg/intelligence/sonars/*` (code analysis)
   - `pkg/gpu/*` (GPU kernels)
   - `pkg/learning/*` (pattern extraction)
4. ⏭️  Update capacity planning with realistic numbers
5. ⏭️  Set SLAs based on cold-cache performance
6. ⏭️  Optimize based on cold-cache profiles (not warm fantasies!)

---

**Om Lokah Samastah Sukhino Bhavantu** 🙏
*May all engineers benefit from realistic performance data!*
