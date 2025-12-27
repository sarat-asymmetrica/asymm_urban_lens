# GPU Fallback Integration Example

**Purpose**: Show how to integrate the fallback system into existing code

---

## Current State

The `Accelerator` currently has a simple if/else implementation:

```go
func (a *Accelerator) BatchSLERP(pairs [][2]Quaternion, t float32) []Quaternion {
    if a.gpuAvailable {
        results = a.batchSLERPGPU(pairs, t)
    } else {
        for i, pair := range pairs {
            results[i] = SLERP(pair[0], pair[1], t)
        }
    }
    return results
}
```

This works fine! GPU unavailable simply uses the CPU path.

---

## Enhanced Integration (Optional)

When you want **logging + stats tracking**, use the fallback infrastructure:

```go
func (a *Accelerator) BatchSLERP(pairs [][2]Quaternion, t float32) []Quaternion {
    start := time.Now()

    // Use fallback infrastructure for logging + stats
    results, mode, err := ExecuteWithFallback(
        "BatchSLERP",
        a.gpuAvailable,
        func() ([]Quaternion, error) {
            return a.batchSLERPGPU(pairs, t), nil
        },
        func() ([]Quaternion, error) {
            cpuResults := make([]Quaternion, len(pairs))
            for i, pair := range pairs {
                cpuResults[i] = SLERP(pair[0], pair[1], t)
            }
            return cpuResults, nil
        },
    )

    // Track stats
    gpuUsed := (mode == ComputeModeGPU)
    a.recordOp(len(pairs), gpuUsed, time.Since(start))

    if err != nil {
        // Both paths failed - return empty results
        results = make([]Quaternion, len(pairs))
    }

    return results
}
```

**Benefits**:
- Automatic logging when GPU fails
- Fallback stats tracking
- Compute mode reporting

---

## Using Fallback in New Code

### Example: VQC Provider Matching

```go
package vqc

import "github.com/asymmetrica/urbanlens/pkg/gpu"

func (e *Engine) MatchProviders(candidates []Provider, query Provider) ([]Match, error) {
    // Encode to quaternions
    queryQ := encodeProvider(query)
    candQs := make([]gpu.Quaternion, len(candidates))
    for i, c := range candidates {
        candQs[i] = encodeProvider(c)
    }

    // Use GPU fallback for similarity computation
    results, err := gpu.WithGPUFallbackTyped(
        func() ([]Match, error) {
            // GPU path: batch dot products
            return e.matchOnGPU(queryQ, candQs)
        },
        func() ([]Match, error) {
            // CPU path: sequential dot products
            return e.matchOnCPU(queryQ, candQs)
        },
    )

    if err != nil {
        return nil, fmt.Errorf("provider matching failed: %w", err)
    }

    return results, nil
}
```

---

## Checking Compute Mode

```go
// In API handler
func (h *Handler) GetStatus(w http.ResponseWriter, r *http.Request) {
    mode := gpu.GetComputeMode()  // "GPU" or "CPU"
    stats := gpu.GetFallbackStats()

    json.NewEncoder(w).Encode(map[string]interface{}{
        "compute_mode":  mode,
        "fallback_rate": stats.FallbackRate(),
        "gpu_available": gpu.GPUAvailable(),
    })
}
```

---

## Error Handling Pattern

```go
func ProcessLargeDataset(data []DataPoint) error {
    return gpu.WithGPUFallback(
        func() error {
            // Try GPU
            return processOnGPU(data)
        },
        func() error {
            // Fallback to CPU
            return processOnCPU(data)
        },
    )
}

// User never sees "GPU not available" error
// System logs warning and continues on CPU
```

---

## Testing Fallback Behavior

```go
func TestMyOperation_WorksWithoutGPU(t *testing.T) {
    gpu.ResetFallbackStats()

    // Run operation (will use CPU since GPU not available)
    result := MyOperation(data)

    // Verify it worked
    if result == nil {
        t.Error("Operation failed")
    }

    // Check stats
    stats := gpu.GetFallbackStats()
    if stats.FallbackRate() != 100.0 {
        t.Logf("Fallback rate: %.1f%% (GPU might be available)", stats.FallbackRate())
    }
}
```

---

## Migration Path

### Phase 1: Current (Works)
```go
if gpuAvailable {
    useGPU()
} else {
    useCPU()
}
```

### Phase 2: With Fallback (Enhanced)
```go
gpu.WithGPUFallback(
    func() error { return useGPU() },
    func() error { return useCPU() },
)
```

### Phase 3: When GPU Arrives
```go
// No code changes needed!
// detectGPU() returns true
// Stats automatically track GPU usage
// Fallback rate drops
```

---

## Key Takeaways

1. **Current implementation works fine** - no urgent need to change
2. **Fallback infrastructure is ready** when you want enhanced logging/stats
3. **When GPU arrives**, minimal changes needed (just detectGPU implementation)
4. **Users never see GPU errors** - system always works

**The fallback system is there when you need it, doesn't get in the way when you don't.** ✨
