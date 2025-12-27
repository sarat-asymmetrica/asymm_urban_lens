# UrbanLens Error Handling Runbooks

**Philosophy**: "Every error must be documented. Every failure must have a recovery path." — Margaret Hamilton

**Version**: 1.0.0
**Last Updated**: 2025-12-27

---

## Table of Contents

1. [GPU Failures](#1-gpu-failures)
2. [Sonar Failures](#2-sonar-failures)
3. [API Timeouts](#3-api-timeouts)
4. [Memory Pressure](#4-memory-pressure)
5. [Circuit Breaker Events](#5-circuit-breaker-events)
6. [OCR Processing Failures](#6-ocr-processing-failures)
7. [Pipeline Failures](#7-pipeline-failures)
8. [Observability Setup](#8-observability-setup)
9. [Alert Thresholds](#9-alert-thresholds)
10. [Escalation Paths](#10-escalation-paths)

---

## 1. GPU Failures

### Error Codes
- `GPU-INIT-001`: GPU initialization failed
- `GPU-MEM-002`: GPU memory exhausted
- `GPU-KERNEL-003`: GPU kernel execution failed
- `GPU-DRIVER-004`: GPU driver version mismatch
- `GPU-AVAIL-005`: GPU not available on system

### Severity Levels
- **WARNING**: GPU unavailable, falling back to CPU
- **CRITICAL**: GPU memory exhausted during operation

---

### 1.1 GPU Initialization Failure (`GPU-INIT-001`)

**Symptoms**:
- Application starts but GPU operations fail
- Log message: `[GPU-INIT-001] GPU initialization failed`
- Automatic fallback to CPU mode
- Performance degradation (10-100x slower depending on workload)

**Root Causes**:
1. GPU driver not installed or outdated
2. CUDA/Level Zero runtime missing
3. Insufficient GPU permissions
4. GPU already in use by another process
5. Incompatible GPU hardware (non-Intel/NVIDIA)

**Immediate Actions**:
```bash
# 1. Check GPU availability
nvidia-smi  # For NVIDIA GPUs
clinfo      # For Intel/AMD GPUs

# 2. Verify driver installation
dpkg -l | grep nvidia-driver  # Ubuntu/Debian
rpm -qa | grep nvidia-driver  # RHEL/CentOS

# 3. Check application logs
grep "GPU-INIT" /var/log/urbanlens/app.log

# 4. Verify fallback to CPU mode
grep "fallback.*CPU" /var/log/urbanlens/app.log
```

**Recovery Path**:
1. **Auto-recovery**: Application continues in CPU mode (degraded performance)
2. **Manual fix**: Install/update GPU drivers and restart application
3. **Permanent fix**: Add GPU health check to startup script

**Long-term Fixes**:
```bash
# Ubuntu: Install NVIDIA drivers
sudo apt update
sudo apt install nvidia-driver-535 nvidia-cuda-toolkit

# Ubuntu: Install Intel GPU drivers (Level Zero)
sudo apt install intel-opencl-icd intel-level-zero-gpu

# Verify installation
urbanlens --check-gpu
```

**Monitoring**:
- Metric: `urbanlens_errors_total{code="GPU-INIT-001", severity="WARNING"}`
- Alert threshold: > 5 failures in 10 minutes (indicates persistent GPU issue)

**Escalation Path**:
- **Level 1** (Auto): Fallback to CPU, log warning
- **Level 2** (15min): Page on-call engineer if persistent failures
- **Level 3** (1hr): Escalate to infrastructure team for hardware check

---

### 1.2 GPU Memory Exhaustion (`GPU-MEM-002`)

**Symptoms**:
- Mid-operation crashes with `GPU-MEM-002` error
- Out of memory (OOM) errors in GPU driver logs
- Batch size reduction triggers
- Fallback to CPU mode mid-processing

**Root Causes**:
1. Batch size too large for available GPU memory
2. Memory leak in GPU kernels
3. Multiple concurrent GPU operations
4. Insufficient GPU memory for workload (e.g., 4GB GPU processing 8K images)

**Immediate Actions**:
```bash
# 1. Check GPU memory usage
nvidia-smi --query-gpu=memory.used,memory.free,memory.total --format=csv

# 2. Identify memory-hungry processes
nvidia-smi pmon -c 1

# 3. Check batch size settings
grep "batch_size" /etc/urbanlens/config.yaml

# 4. Review memory allocation patterns
grep "GPU-MEM" /var/log/urbanlens/app.log | tail -50
```

**Recovery Path**:
1. **Auto-recovery**: Reduce batch size by 50% using Williams optimizer
2. **Retry**: Attempt operation with smaller batch
3. **Fallback**: Process on CPU if batch reduction insufficient

**Long-term Fixes**:
```yaml
# config.yaml: Enable adaptive batch sizing
gpu:
  enable_adaptive_batching: true
  max_memory_usage_percent: 80  # Reserve 20% headroom
  fallback_to_cpu_on_oom: true
```

**Code Example**:
```go
// Automatic batch size optimization
batchSize := math.OptimalBatchSize(totalItems)
gpuMem := gpu.AvailableMemory()

if estimatedMemory := batchSize * itemSize; estimatedMemory > gpuMem*0.8 {
    // Reduce batch to fit in 80% of available memory
    batchSize = int(float64(gpuMem) * 0.8 / float64(itemSize))
    log.Warn("Reducing batch size due to GPU memory constraints",
        "new_batch_size", batchSize)
}
```

**Monitoring**:
- Metric: `urbanlens_gpu_memory_used_percent`
- Alert threshold: > 85% sustained for 5 minutes (WARNING), > 95% (CRITICAL)

**Escalation Path**:
- **Level 1** (Auto): Reduce batch size, retry operation
- **Level 2** (3 failures): Log error, switch to CPU mode
- **Level 3** (Persistent): Recommend GPU upgrade (e.g., 8GB → 16GB)

---

### 1.3 GPU Not Available (`GPU-AVAIL-005`)

**Symptoms**:
- Application starts with warning: `GPU not available on this system`
- All operations run on CPU
- Slower processing times (expected on CPU-only systems)

**Root Causes**:
1. Running on CPU-only hardware (no discrete GPU)
2. GPU disabled in BIOS
3. GPU passed through to VM (not available to host)

**Immediate Actions**:
```bash
# 1. Check for GPU hardware
lspci | grep -i vga
lspci | grep -i nvidia

# 2. Check BIOS/UEFI settings (if physical access available)
# Ensure GPU is enabled

# 3. Verify VM configuration (if running in VM)
virsh dumpxml <vm-name> | grep hostdev  # Check GPU passthrough
```

**Recovery Path**:
1. **Expected behavior**: CPU mode is normal for non-GPU systems
2. **If GPU expected**: Check hardware/BIOS/VM configuration
3. **Production**: Deploy to GPU-enabled instances

**Long-term Fixes**:
- Use infrastructure-as-code to ensure GPU instances:
```yaml
# terraform/ec2.tf
resource "aws_instance" "urbanlens" {
  instance_type = "g4dn.xlarge"  # GPU instance
  ami           = var.urbanlens_ami

  # Ensure GPU is available
  ebs_optimized = true
}
```

**Monitoring**:
- Metric: `urbanlens_gpu_available{status="false"}`
- Alert threshold: Only alert if GPU expected but not found

**Escalation Path**:
- **Level 1** (Auto): Log info, run in CPU mode
- **Level 2** (Manual): Verify infrastructure configuration
- **No escalation**: CPU-only deployment is valid configuration

---

## 2. Sonar Failures

### Error Codes
- `SONAR-PING-001`: Sonar ping (data collection) failed
- `SONAR-ECHO-002`: Sonar echo (processing) failed
- `SONAR-MAP-003`: Sonar mapping (normalization) failed
- `SONAR-CRITIQUE-004`: Sonar critique (reporting) failed
- `SONAR-THRESHOLD-005`: Sonar score below threshold
- `SONAR-CASCADE-006`: Multiple sonars failed (cascade failure)

### Severity Levels
- **WARNING**: Single sonar failure (others compensate)
- **ERROR**: Multiple sonars failed (> 50% failure rate)

---

### 2.1 Single Sonar Failure (`SONAR-PING-001`)

**Symptoms**:
- One sonar reports failure while others succeed
- Log message: `[SONAR-PING-001] Sonar ping failed: <sonar_name>`
- Overall system health degraded but functional
- Missing metrics for failed sonar

**Root Causes**:
1. **CodeSonar**: Source files not accessible, git repository issues
2. **DesignSonar**: UI components not found, frontend build failed
3. **SemanticSonar**: AI/ML inference service unavailable
4. **JourneySonar**: User analytics database connection lost
5. **StateSonar**: Redis/state store unreachable

**Immediate Actions**:
```bash
# 1. Identify which sonar failed
grep "SONAR-PING-001" /var/log/urbanlens/app.log | tail -20

# 2. Check sonar-specific dependencies
# For CodeSonar:
ls -la /path/to/source/code  # Verify source files accessible

# For SemanticSonar:
curl http://localhost:8001/health  # Check AI inference service

# For JourneySonar:
psql -U urbanlens -c "SELECT 1"  # Check database connection

# For StateSonar:
redis-cli ping  # Check Redis connection

# 3. Review sonar health metrics
curl http://localhost:9090/metrics | grep sonar_health
```

**Recovery Path**:
1. **Auto-retry**: Sonar automatically retries after 30 seconds
2. **Degraded mode**: Other sonars compensate for missing data
3. **Manual fix**: Restore failed dependency (database, service, etc.)

**Long-term Fixes**:
```go
// Implement sonar circuit breaker
sonar := NewCodeSonar()
sonarWithCB := NewCircuitBreaker(sonar, CircuitBreakerConfig{
    FailureThreshold: 3,        // Open after 3 failures
    SuccessThreshold: 2,        // Close after 2 successes
    Timeout:          30 * time.Second,
})

// Ping with automatic recovery
telemetry, err := sonarWithCB.Ping(ctx, app)
if err != nil {
    log.Warn("Sonar ping failed, will retry",
        "sonar", sonar.Name(),
        "error", err,
        "retryable", true)
}
```

**Monitoring**:
- Metric: `urbanlens_sonar_failures_total{sonar="<name>"}`
- Alert threshold: > 5 failures in 10 minutes for same sonar

**Escalation Path**:
- **Level 1** (Auto): Log warning, retry with backoff
- **Level 2** (5min): Alert on-call if sonar stays down
- **Level 3** (15min): Escalate to service owner (database team, AI team, etc.)

---

### 2.2 Cascade Failure (`SONAR-CASCADE-006`)

**Symptoms**:
- Multiple sonars failing simultaneously
- Log message: `[SONAR-CASCADE-006] Multiple sonars failed: 3/5 failed`
- Health percentage drops below 50%
- Intelligence layer severely degraded

**Root Causes**:
1. Network partition (all remote services unreachable)
2. Shared dependency failure (e.g., shared Redis instance down)
3. Resource exhaustion (CPU/memory affecting all sonars)
4. Configuration error affecting multiple sonars
5. Cascading timeout (one slow sonar blocks others)

**Immediate Actions**:
```bash
# 1. Check overall system health
curl http://localhost:8080/health

# 2. Identify all failed sonars
grep "SONAR.*FAILED" /var/log/urbanlens/app.log | tail -50

# 3. Check network connectivity
ping -c 3 ai-inference.internal
ping -c 3 analytics-db.internal
ping -c 3 redis.internal

# 4. Check system resources
top -b -n 1 | head -20
free -h
df -h

# 5. Review circuit breaker states
curl http://localhost:9090/metrics | grep circuit_breaker_state
```

**Recovery Path**:
1. **Auto-degradation**: Disable non-critical sonars, continue with reduced intelligence
2. **Health check**: Verify shared dependencies (network, Redis, databases)
3. **Shed load**: Reduce concurrent requests to prevent further degradation
4. **Restart**: If resource exhaustion, graceful restart of service

**Long-term Fixes**:
```yaml
# config.yaml: Configure sonar resilience
sonars:
  # Independent execution (no shared blocking)
  parallel_execution: true

  # Timeout per sonar (prevent cascade)
  timeout_seconds: 30

  # Circuit breaker per sonar
  circuit_breaker:
    enabled: true
    failure_threshold: 3
    recovery_timeout: 60

  # Graceful degradation
  min_required_sonars: 2  # Need at least 2/5 sonars working
```

**Code Example**:
```go
// Parallel sonar execution with timeout
ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
defer cancel()

var wg sync.WaitGroup
results := make(chan SonarResult, len(sonars))

for _, sonar := range sonars {
    wg.Add(1)
    go func(s Sonar) {
        defer wg.Done()
        telemetry, err := s.Ping(ctx, app)
        results <- SonarResult{Sonar: s.Name(), Data: telemetry, Err: err}
    }(sonar)
}

wg.Wait()
close(results)

// Analyze cascade health
successCount := 0
for result := range results {
    if result.Err == nil {
        successCount++
    }
}

healthPercent := float64(successCount) / float64(len(sonars)) * 100
if healthPercent < 50.0 {
    return NewSonarCascadeError(len(sonars)-successCount, len(sonars))
}
```

**Monitoring**:
- Metric: `urbanlens_sonar_health_percentage`
- Alert threshold: < 60% (WARNING), < 40% (CRITICAL)

**Escalation Path**:
- **Level 1** (Immediate): Auto-disable failing sonars, continue degraded
- **Level 2** (2min): Page on-call engineer, investigate shared dependencies
- **Level 3** (5min): Escalate to platform team for infrastructure issues

---

## 3. API Timeouts

### Error Codes
- `API-TIMEOUT-001`: API request exceeded timeout
- `API-RATE-002`: API rate limit exceeded
- `API-AUTH-003`: API authentication failed
- `API-REQUEST-004`: Invalid API request format
- `API-SERVER-005`: API server error (5xx)
- `API-CIRCUIT-006`: Circuit breaker is open

### Severity Levels
- **ERROR**: Timeout occurred, retrying
- **WARNING**: Circuit breaker opened (waiting for recovery)

---

### 3.1 API Timeout (`API-TIMEOUT-001`)

**Symptoms**:
- Request exceeds configured timeout (typically 30-120 seconds)
- Log message: `[API-TIMEOUT-001] API request timed out: <url>`
- Automatic retry triggered
- User sees delayed response or error message

**Root Causes**:
1. Downstream service slow (database query, ML inference)
2. Network latency/packet loss
3. Server overloaded (high request queue)
4. Deadlock or infinite loop in API handler
5. Timeout configured too aggressively

**Immediate Actions**:
```bash
# 1. Check API latency metrics
curl http://localhost:9090/metrics | grep api_request_duration

# 2. Identify slow endpoints
grep "API-TIMEOUT-001" /var/log/urbanlens/app.log | \
  awk -F'"url":"' '{print $2}' | awk -F'"' '{print $1}' | sort | uniq -c | sort -rn

# 3. Check downstream service health
curl https://api.example.com/health
curl https://ai-inference.internal/health

# 4. Review network connectivity
traceroute api.example.com
mtr -c 10 api.example.com

# 5. Check server load
uptime  # Load average
ss -s   # Socket statistics
```

**Recovery Path**:
1. **Auto-retry**: Exponential backoff (1s → 2s → 4s → 8s)
2. **Circuit breaker**: Open after 5 consecutive failures
3. **Fallback**: Use cached response if available
4. **Timeout increase**: Temporarily increase timeout for known-slow endpoints

**Long-term Fixes**:
```go
// Implement retry with exponential backoff
func CallAPIWithRetry(ctx context.Context, url string) (*Response, error) {
    maxRetries := 3
    baseDelay := 1 * time.Second

    for attempt := 0; attempt < maxRetries; attempt++ {
        resp, err := CallAPI(ctx, url)

        if err == nil {
            return resp, nil
        }

        // Check if retryable
        if !IsRetryable(err) {
            return nil, err
        }

        // Exponential backoff: 1s, 2s, 4s
        delay := baseDelay * (1 << attempt)

        log.Warn("API call failed, retrying",
            "url", url,
            "attempt", attempt+1,
            "max_retries", maxRetries,
            "delay", delay)

        RecordRetry(ErrorAPITimeout, attempt+1)

        select {
        case <-time.After(delay):
            // Continue to next attempt
        case <-ctx.Done():
            return nil, ctx.Err()
        }
    }

    return nil, fmt.Errorf("max retries exceeded")
}
```

**Monitoring**:
- Metric: `urbanlens_api_request_duration_seconds{endpoint="<path>"}`
- Alert threshold: p95 > 5s (WARNING), p95 > 10s (CRITICAL)

**Escalation Path**:
- **Level 1** (Auto): Retry with backoff (3 attempts)
- **Level 2** (3 failures): Open circuit breaker, alert on-call
- **Level 3** (Persistent): Escalate to API provider or infrastructure team

---

### 3.2 Circuit Breaker Open (`API-CIRCUIT-006`)

**Symptoms**:
- Requests failing immediately without attempting network call
- Log message: `[API-CIRCUIT-006] Circuit breaker is open: <service>`
- Fast-fail behavior (no timeout wait)
- Service degraded but responsive

**Root Causes**:
1. Downstream service completely down
2. Network partition
3. High error rate exceeded circuit breaker threshold (e.g., 50% failures)
4. Previous cascade timeout causing circuit to open

**Immediate Actions**:
```bash
# 1. Check circuit breaker state
curl http://localhost:9090/metrics | grep circuit_breaker_state

# 2. Verify downstream service status
curl https://api.example.com/health

# 3. Check failure rate that triggered circuit
grep "CIRCUIT.*OPEN" /var/log/urbanlens/app.log | tail -20

# 4. Review recent API errors
grep "API-.*-00" /var/log/urbanlens/app.log | tail -50

# 5. Test manual API call
curl -v --max-time 10 https://api.example.com/endpoint
```

**Recovery Path**:
1. **Auto-recovery**: Circuit enters half-open state after timeout (60-300s)
2. **Test request**: Send single test request in half-open state
3. **Success → Close**: If test succeeds, circuit closes (normal operation)
4. **Failure → Open**: If test fails, circuit reopens (wait another cycle)

**Long-term Fixes**:
```go
// Circuit breaker configuration
type CircuitBreakerConfig struct {
    FailureThreshold  int           // Open after N failures (e.g., 5)
    SuccessThreshold  int           // Close after N successes (e.g., 2)
    Timeout           time.Duration // Wait before half-open (e.g., 60s)
    MaxHalfOpenCalls  int           // Max concurrent calls in half-open (e.g., 1)
}

// Example usage
cb := NewCircuitBreaker(CircuitBreakerConfig{
    FailureThreshold: 5,
    SuccessThreshold: 2,
    Timeout:          60 * time.Second,
    MaxHalfOpenCalls: 1,
})

resp, err := cb.Execute(func() (interface{}, error) {
    return CallAPI(ctx, url)
})

if err != nil {
    if errors.Is(err, ErrCircuitBreakerOpen) {
        // Circuit is open, use fallback
        return useCachedResponse()
    }
    return err
}
```

**Monitoring**:
- Metric: `urbanlens_circuit_breaker_state{service="<name>", state="open|closed|half_open"}`
- Alert threshold: Circuit open for > 5 minutes (indicates persistent downstream issue)

**Escalation Path**:
- **Level 1** (Auto): Fast-fail requests, wait for auto-recovery
- **Level 2** (5min): Alert on-call, verify downstream service status
- **Level 3** (15min): Escalate to service owner, consider manual intervention

---

## 4. Memory Pressure

### Error Codes
- `MEM-PRESSURE-001`: Memory pressure detected (high usage)
- `MEM-PRESSURE-002`: Critical memory pressure (imminent OOM)
- `MEM-ALLOC-003`: Memory allocation failed
- `MEM-LEAK-004`: Memory leak detected

### Severity Levels
- **WARNING**: Memory usage > 80% (shed non-critical load)
- **CRITICAL**: Memory usage > 90% (imminent OOM kill)

---

### 4.1 High Memory Pressure (`MEM-PRESSURE-001`)

**Symptoms**:
- Memory usage exceeds 80% of available RAM
- Log message: `[MEM-PRESSURE-001] Memory pressure detected: 85.3%`
- Load shedding activated (rejecting new requests)
- Performance degradation (disk swapping)

**Root Causes**:
1. Traffic spike (more concurrent requests than capacity)
2. Memory leak in application code
3. Large batch processing jobs
4. Insufficient memory for workload
5. Cache growth unbounded

**Immediate Actions**:
```bash
# 1. Check current memory usage
free -h
vmstat 1 5  # Monitor over 5 seconds

# 2. Identify memory-hungry processes
ps aux --sort=-%mem | head -10

# 3. Check for memory leaks (increasing RSS over time)
watch -n 5 'ps aux | grep urbanlens'

# 4. Review memory metrics
curl http://localhost:9090/metrics | grep memory_used

# 5. Check swap usage (high swap = thrashing)
swapon --show
```

**Recovery Path**:
1. **Auto-load-shedding**: Reject new requests with 503 Service Unavailable
2. **Cache eviction**: Clear least-recently-used (LRU) cache entries
3. **GC trigger**: Force garbage collection (Go: `runtime.GC()`)
4. **Graceful restart**: If leak suspected, schedule rolling restart

**Long-term Fixes**:
```go
// Implement memory pressure monitoring
func MonitorMemoryPressure(ctx context.Context) {
    ticker := time.NewTicker(10 * time.Second)
    defer ticker.Stop()

    for {
        select {
        case <-ticker.C:
            var m runtime.MemStats
            runtime.ReadMemStats(&m)

            usedMB := m.Alloc / 1024 / 1024
            totalMB := m.Sys / 1024 / 1024
            usedPercent := float64(usedMB) / float64(totalMB) * 100

            // Record metric
            memoryUsedGauge.Set(usedPercent)

            // Check thresholds
            if usedPercent > 90.0 {
                err := NewMemoryPressureError(usedPercent)
                RecordError(err)

                // CRITICAL: Shed load aggressively
                loadShedder.SetThreshold(0.1) // Accept only 10% of requests

            } else if usedPercent > 80.0 {
                err := NewMemoryPressureError(usedPercent)
                RecordError(err)

                // WARNING: Shed some load
                loadShedder.SetThreshold(0.5) // Accept 50% of requests

                // Trigger garbage collection
                runtime.GC()

                // Evict cache entries
                cache.EvictLRU(0.2) // Evict 20% of cache
            }

        case <-ctx.Done():
            return
        }
    }
}
```

**Monitoring**:
- Metric: `urbanlens_memory_used_percent`
- Alert threshold: > 80% for 5 minutes (WARNING), > 90% (CRITICAL)

**Escalation Path**:
- **Level 1** (Auto): Shed load, trigger GC, evict cache
- **Level 2** (5min): Alert on-call, investigate memory leak
- **Level 3** (Persistent): Scale horizontally or upgrade instance memory

---

### 4.2 Critical Memory Pressure (`MEM-PRESSURE-002`)

**Symptoms**:
- Memory usage > 90% (imminent OOM killer)
- Kernel OOM messages in system logs
- Process killed by OOM killer
- System unresponsive

**Root Causes**:
1. Catastrophic memory leak
2. Traffic spike beyond capacity
3. Large allocation (e.g., loading multi-GB file)
4. Configuration error (e.g., unlimited cache size)

**Immediate Actions**:
```bash
# 1. Check if OOM killer has been invoked
dmesg | grep -i "out of memory"
dmesg | grep -i "killed process"

# 2. Identify OOM victim (if killed)
journalctl -xe | grep -i oom

# 3. Restart service if killed
systemctl status urbanlens
systemctl restart urbanlens

# 4. Emergency memory release
echo 3 > /proc/sys/vm/drop_caches  # Drop page cache (safe)

# 5. Check for runaway processes
ps aux --sort=-%mem | head -5
```

**Recovery Path**:
1. **OOM killer**: Kernel automatically kills largest memory consumer
2. **Service restart**: Systemd/supervisor restarts killed process
3. **Emergency mode**: Start with reduced capacity (smaller cache, batch sizes)
4. **Root cause**: Investigate memory leak before resuming normal operation

**Long-term Fixes**:
```yaml
# systemd service: Configure memory limits
[Service]
MemoryMax=8G          # Hard limit (OOM kill if exceeded)
MemoryHigh=7G         # Soft limit (throttle if exceeded)
OOMScoreAdjust=-500   # Less likely to be killed than other processes

# config.yaml: Conservative memory settings
memory:
  max_cache_size_mb: 2048        # 2GB cache maximum
  max_batch_size: 128            # Smaller batches
  enable_memory_limit: true
  oom_headroom_percent: 20       # Reserve 20% headroom
```

**Monitoring**:
- Metric: `urbanlens_oom_kills_total`
- Alert threshold: Any OOM kill (CRITICAL - immediate investigation)

**Escalation Path**:
- **Level 1** (Immediate): Auto-restart, emergency mode
- **Level 2** (Immediate): Page on-call, investigate root cause
- **Level 3** (Urgent): Scale infrastructure, fix memory leak

---

## 5. Circuit Breaker Events

### Error Codes
- `CB-OPEN-001`: Circuit breaker opened due to failures
- `CB-HALFOPEN-002`: Circuit breaker half-open state test failed
- `CB-THRESHOLD-003`: Circuit breaker failure threshold exceeded

### Severity Levels
- **WARNING**: Circuit opened (fast-fail active, waiting for recovery)
- **ERROR**: Circuit stuck open (downstream service persistently down)

---

### 5.1 Circuit Breaker Opened (`CB-OPEN-001`)

**Symptoms**:
- Downstream service calls failing immediately
- Log message: `[CB-OPEN-001] Circuit breaker opened: <service> (failure_rate: 75%)`
- No network delay (fast-fail)
- Fallback behavior activated

**Root Causes**:
1. Downstream service degraded/down
2. High error rate exceeded threshold (e.g., 50% failures)
3. Cascading timeout causing rapid failures
4. Network partition

**Immediate Actions**:
```bash
# 1. Identify which circuit opened
grep "CB-OPEN-001" /var/log/urbanlens/app.log | tail -10

# 2. Check downstream service health
curl https://downstream-service.com/health

# 3. Review failure rate
curl http://localhost:9090/metrics | grep circuit_breaker_failures

# 4. Check circuit state
curl http://localhost:9090/metrics | grep circuit_breaker_state

# 5. Verify fallback working
curl http://localhost:8080/api/endpoint  # Should use fallback
```

**Recovery Path**:
1. **Auto-recovery**: Wait for timeout (60s default), enter half-open
2. **Half-open test**: Send 1 test request
3. **Success path**: If test succeeds, close circuit (resume normal operation)
4. **Failure path**: If test fails, reopen circuit (wait another cycle)

**Long-term Fixes**:
```go
// Implement fallback strategies
func CallWithFallback(cb *CircuitBreaker, primary, fallback func() (interface{}, error)) (interface{}, error) {
    result, err := cb.Execute(primary)

    if err != nil {
        if errors.Is(err, ErrCircuitBreakerOpen) {
            log.Warn("Circuit breaker open, using fallback")
            RecordRecovery(ErrorCBOpen, "fallback")
            return fallback()
        }
        return nil, err
    }

    return result, nil
}

// Example usage
resp, err := CallWithFallback(cb,
    func() (interface{}, error) {
        // Primary: Call live API
        return CallExternalAPI(ctx, url)
    },
    func() (interface{}, error) {
        // Fallback: Use cached response
        return cache.Get(url)
    },
)
```

**Monitoring**:
- Metric: `urbanlens_circuit_breaker_state{service="<name>", state="open"}`
- Alert threshold: Circuit open for > 5 minutes (indicates persistent issue)

**Escalation Path**:
- **Level 1** (Auto): Fast-fail + fallback, wait for auto-recovery
- **Level 2** (5min): Alert on-call if circuit stays open
- **Level 3** (15min): Escalate to downstream service owner

---

## 6. OCR Processing Failures

### Error Codes
- `OCR-PROCESS-001`: OCR processing failed
- `OCR-QUALITY-002`: OCR quality below threshold
- `OCR-LANG-003`: Language not supported
- `OCR-TIMEOUT-004`: OCR timeout exceeded

### Severity Levels
- **ERROR**: Processing failed (retryable)
- **WARNING**: Quality low (results returned with warning)

---

### 6.1 OCR Processing Failed (`OCR-PROCESS-001`)

**Symptoms**:
- Document processing fails with error
- Log message: `[OCR-PROCESS-001] OCR processing failed: <file>`
- Automatic retry triggered
- User sees error message or degraded results

**Root Causes**:
1. Corrupted/invalid input file (unsupported format)
2. Image quality too low (resolution, contrast)
3. OCR engine (Florence-2, Tesseract) unavailable
4. Timeout exceeded for large documents
5. GPU memory exhausted during processing

**Immediate Actions**:
```bash
# 1. Check OCR service health
curl http://localhost:8001/health  # Florence-2 health check

# 2. Verify input file
file /path/to/document.pdf
identify /path/to/image.png  # ImageMagick

# 3. Review OCR logs
grep "OCR-PROCESS-001" /var/log/urbanlens/ocr.log | tail -20

# 4. Test manual OCR
urbanlens ocr --file /path/to/document.pdf --debug

# 5. Check GPU/CPU usage during OCR
nvidia-smi dmon -c 10  # GPU utilization
top -b -n 1 | grep urbanlens  # CPU utilization
```

**Recovery Path**:
1. **Auto-retry**: Retry 3 times with exponential backoff
2. **Fallback**: Try simpler OCR engine (Tesseract if Florence-2 fails)
3. **Preprocessing**: Apply image enhancement (contrast, deskew, denoise)
4. **Manual review**: Flag for human review if auto-processing fails

**Long-term Fixes**:
```go
// Implement OCR pipeline with fallbacks
func ProcessDocumentWithFallback(ctx context.Context, doc Document) (*OCRResult, error) {
    // Try Florence-2 (GPU-accelerated, high quality)
    result, err := florence2.Process(ctx, doc)
    if err == nil && result.Confidence > 0.85 {
        return result, nil
    }

    if err != nil {
        log.Warn("Florence-2 failed, trying Tesseract",
            "error", err)
        RecordRecovery(ErrorOCRProcessingFailed, "fallback_tesseract")
    }

    // Fallback: Tesseract (CPU-based, moderate quality)
    result, err = tesseract.Process(ctx, doc)
    if err == nil && result.Confidence > 0.70 {
        return result, nil
    }

    // Last resort: Flag for manual review
    return &OCRResult{
        Text:       "",
        Confidence: 0.0,
        Status:     "manual_review_required",
        Error:      err,
    }, NewOCRProcessingError(doc.Filename, err)
}
```

**Monitoring**:
- Metric: `urbanlens_ocr_failures_total{engine="florence2|tesseract"}`
- Alert threshold: > 10% failure rate over 10 minutes

**Escalation Path**:
- **Level 1** (Auto): Retry + fallback to Tesseract
- **Level 2** (Manual): Flag for human review
- **Level 3** (Persistent): Investigate OCR service, GPU issues

---

## 7. Pipeline Failures

### Error Codes
- `PIPELINE-STAGE-001`: Pipeline stage failed
- `PIPELINE-VALIDATE-002`: Pipeline validation failed
- `PIPELINE-TRANSFORM-003`: Pipeline transformation failed

### Severity Levels
- **ERROR**: Stage failed (pipeline halted)
- **CRITICAL**: Multiple stage failures (data corruption risk)

---

### 7.1 Pipeline Stage Failure (`PIPELINE-STAGE-001`)

**Symptoms**:
- Data processing pipeline halts at specific stage
- Log message: `[PIPELINE-STAGE-001] Pipeline stage failed: <stage_name>`
- Downstream stages not executed
- Partial data in output

**Root Causes**:
1. Invalid input data (schema mismatch)
2. Transformation logic error (bug in code)
3. Dependency unavailable (database, API)
4. Resource exhaustion (memory, disk)
5. Timeout exceeded

**Immediate Actions**:
```bash
# 1. Identify failed stage
grep "PIPELINE-STAGE-001" /var/log/urbanlens/pipeline.log | tail -10

# 2. Check input data validity
urbanlens pipeline validate --input data.json

# 3. Review stage configuration
cat /etc/urbanlens/pipelines/<pipeline>.yaml

# 4. Test stage in isolation
urbanlens pipeline run-stage --stage <stage_name> --input data.json

# 5. Check dependencies
curl http://database:5432/health
curl http://api:8080/health
```

**Recovery Path**:
1. **Auto-retry**: Retry stage with exponential backoff
2. **Skip stage**: If non-critical, skip and continue pipeline
3. **Fallback data**: Use previous successful result if available
4. **Manual intervention**: Fix data/code and rerun pipeline

**Long-term Fixes**:
```go
// Implement resilient pipeline
type PipelineStage struct {
    Name      string
    Critical  bool  // If false, failure doesn't halt pipeline
    Retryable bool
    Timeout   time.Duration
}

func (p *Pipeline) Execute(ctx context.Context, data interface{}) error {
    for _, stage := range p.Stages {
        stageCtx, cancel := context.WithTimeout(ctx, stage.Timeout)
        defer cancel()

        err := p.executeStage(stageCtx, stage, data)

        if err != nil {
            if stage.Retryable {
                // Retry with backoff
                err = p.retryStage(ctx, stage, data)
            }

            if err != nil {
                if stage.Critical {
                    // Critical stage failed - halt pipeline
                    return fmt.Errorf("critical stage %s failed: %w", stage.Name, err)
                }

                // Non-critical stage - log and continue
                log.Warn("Non-critical stage failed, continuing",
                    "stage", stage.Name,
                    "error", err)
            }
        }
    }

    return nil
}
```

**Monitoring**:
- Metric: `urbanlens_pipeline_stage_failures_total{pipeline="<name>", stage="<stage>"}`
- Alert threshold: > 5% failure rate for any stage

**Escalation Path**:
- **Level 1** (Auto): Retry stage, skip if non-critical
- **Level 2** (Manual): Investigate data quality, fix transformation logic
- **Level 3** (Persistent): Review pipeline design, add validation

---

## 8. Observability Setup

### 8.1 Metrics Collection (Prometheus)

**Installation**:
```bash
# Ubuntu: Install Prometheus
sudo apt install prometheus

# Configure Prometheus to scrape UrbanLens
cat <<EOF | sudo tee /etc/prometheus/prometheus.yml
global:
  scrape_interval: 15s

scrape_configs:
  - job_name: 'urbanlens'
    static_configs:
      - targets: ['localhost:9090']
EOF

sudo systemctl restart prometheus
```

**Key Metrics to Monitor**:
```promql
# Error rates
rate(urbanlens_errors_total[5m])

# Error count by severity
sum by (severity) (urbanlens_errors_total)

# Circuit breaker states
urbanlens_circuit_breaker_state

# Memory pressure
urbanlens_memory_used_percent

# GPU availability
urbanlens_gpu_available

# Sonar health
urbanlens_sonar_health_percentage

# API latency
histogram_quantile(0.95, rate(urbanlens_api_request_duration_seconds_bucket[5m]))
```

---

### 8.2 Logging (Structured Logs)

**Configuration**:
```yaml
# config.yaml
logging:
  level: info  # debug, info, warn, error
  format: json  # json or text
  output: /var/log/urbanlens/app.log

  # Rotate logs
  max_size_mb: 100
  max_backups: 10
  max_age_days: 30
```

**Log Aggregation (Loki + Grafana)**:
```bash
# Install Grafana Loki
sudo apt install loki

# Configure Promtail to ship logs
cat <<EOF | sudo tee /etc/promtail/config.yml
server:
  http_listen_port: 9080

clients:
  - url: http://localhost:3100/loki/api/v1/push

scrape_configs:
  - job_name: urbanlens
    static_configs:
      - targets:
          - localhost
        labels:
          job: urbanlens
          __path__: /var/log/urbanlens/*.log
EOF

sudo systemctl restart promtail
```

**Query Examples**:
```logql
# All errors
{job="urbanlens"} |= "ERROR"

# GPU errors
{job="urbanlens"} |= "GPU-"

# Sonar failures
{job="urbanlens"} |= "SONAR-" |= "FAILED"

# API timeouts
{job="urbanlens"} |= "API-TIMEOUT-001"
```

---

### 8.3 Dashboards (Grafana)

**Install Grafana**:
```bash
sudo apt install grafana
sudo systemctl enable grafana-server
sudo systemctl start grafana-server

# Access at http://localhost:3000 (admin/admin)
```

**Pre-built Dashboard Panels**:

**Panel 1: Error Rate by Severity**
```promql
sum by (severity) (rate(urbanlens_errors_total[5m]))
```

**Panel 2: Circuit Breaker States**
```promql
urbanlens_circuit_breaker_state
```

**Panel 3: Memory Pressure**
```promql
urbanlens_memory_used_percent
```

**Panel 4: Sonar Health**
```promql
urbanlens_sonar_health_percentage
```

**Panel 5: API Latency (p50, p95, p99)**
```promql
histogram_quantile(0.50, rate(urbanlens_api_request_duration_seconds_bucket[5m]))
histogram_quantile(0.95, rate(urbanlens_api_request_duration_seconds_bucket[5m]))
histogram_quantile(0.99, rate(urbanlens_api_request_duration_seconds_bucket[5m]))
```

---

## 9. Alert Thresholds

### 9.1 Alerting Rules (Prometheus)

**Configure Alerts**:
```yaml
# /etc/prometheus/rules/urbanlens.yml
groups:
  - name: urbanlens_alerts
    interval: 30s
    rules:
      # HIGH ERROR RATE
      - alert: HighErrorRate
        expr: rate(urbanlens_errors_total[5m]) > 10
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High error rate detected"
          description: "Error rate is {{ $value }} errors/sec (threshold: 10)"

      # CRITICAL MEMORY PRESSURE
      - alert: CriticalMemoryPressure
        expr: urbanlens_memory_used_percent > 90
        for: 2m
        labels:
          severity: critical
        annotations:
          summary: "Critical memory pressure"
          description: "Memory usage is {{ $value }}% (threshold: 90%)"

      # CIRCUIT BREAKER STUCK OPEN
      - alert: CircuitBreakerStuckOpen
        expr: urbanlens_circuit_breaker_state{state="open"} == 1
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "Circuit breaker stuck open"
          description: "Circuit {{ $labels.service }} has been open for >5min"

      # SONAR CASCADE FAILURE
      - alert: SonarCascadeFailure
        expr: urbanlens_sonar_health_percentage < 50
        for: 2m
        labels:
          severity: error
        annotations:
          summary: "Sonar cascade failure"
          description: "Sonar health is {{ $value }}% (threshold: 50%)"

      # GPU UNAVAILABLE
      - alert: GPUUnavailable
        expr: urbanlens_gpu_available{status="false"} == 1
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "GPU unavailable (running on CPU)"
          description: "GPU has been unavailable for >10min"

      # HIGH API LATENCY
      - alert: HighAPILatency
        expr: histogram_quantile(0.95, rate(urbanlens_api_request_duration_seconds_bucket[5m])) > 5
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High API latency"
          description: "p95 latency is {{ $value }}s (threshold: 5s)"
```

---

### 9.2 Alert Routing (Alertmanager)

**Configure Alertmanager**:
```yaml
# /etc/alertmanager/alertmanager.yml
global:
  resolve_timeout: 5m

route:
  receiver: 'default'
  group_by: ['alertname', 'severity']
  group_wait: 10s
  group_interval: 10s
  repeat_interval: 12h

  routes:
    # CRITICAL alerts → PagerDuty
    - match:
        severity: critical
      receiver: 'pagerduty'
      continue: true

    # WARNING alerts → Slack
    - match:
        severity: warning
      receiver: 'slack'

receivers:
  - name: 'default'
    webhook_configs:
      - url: 'http://localhost:5001/alert'

  - name: 'pagerduty'
    pagerduty_configs:
      - service_key: '<PAGERDUTY_SERVICE_KEY>'

  - name: 'slack'
    slack_configs:
      - api_url: '<SLACK_WEBHOOK_URL>'
        channel: '#urbanlens-alerts'
```

---

## 10. Escalation Paths

### 10.1 On-Call Rotation

**Responsibilities**:
- **L1 (Auto)**: Automated recovery (retries, fallbacks, circuit breakers)
- **L2 (On-call Engineer)**: Investigate alerts, manual intervention
- **L3 (Service Owners)**: Deep investigation, code fixes, infrastructure changes

**Response Times**:
- **CRITICAL**: 15 minutes (page immediately)
- **ERROR**: 1 hour (investigate during business hours)
- **WARNING**: 4 hours (review during next shift)

---

### 10.2 Runbook Checklist

For each alert, on-call engineer should:

1. **Acknowledge alert** (within 5 minutes)
2. **Check runbook** (this document - find matching error code)
3. **Execute immediate actions** (as documented above)
4. **Verify recovery** (check metrics, test functionality)
5. **Document incident** (create incident report)
6. **Follow up** (implement long-term fix if needed)

---

### 10.3 Contact Information

**Service Owners**:
- **GPU Stack**: Platform Team (`platform@urbanlens.com`, Slack: `#platform`)
- **Sonar Intelligence**: AI Team (`ai@urbanlens.com`, Slack: `#ai-ml`)
- **OCR Pipeline**: Document Team (`docs@urbanlens.com`, Slack: `#document-processing`)
- **API Gateway**: Backend Team (`backend@urbanlens.com`, Slack: `#backend`)
- **Infrastructure**: SRE Team (`sre@urbanlens.com`, Slack: `#sre`)

**Escalation**:
- **Business Hours**: Slack channels (response SLA: 1 hour)
- **After Hours**: PagerDuty (response SLA: 15 minutes)
- **Outage**: Incident Commander (`incident@urbanlens.com`, PagerDuty: HIGH)

---

## Appendix A: Error Code Quick Reference

| Code | Category | Severity | Auto-Retry | Fallback Available |
|------|----------|----------|------------|-------------------|
| GPU-INIT-001 | GPU | WARNING | No | Yes (CPU mode) |
| GPU-MEM-002 | GPU | CRITICAL | No | Yes (reduce batch) |
| GPU-AVAIL-005 | GPU | INFO | No | Yes (CPU mode) |
| SONAR-PING-001 | Sonar | WARNING | Yes (3×) | Partial (other sonars) |
| SONAR-CASCADE-006 | Sonar | ERROR | No | Degraded mode |
| API-TIMEOUT-001 | API | ERROR | Yes (3×) | Yes (cached response) |
| API-CIRCUIT-006 | Circuit | WARNING | No | Yes (fallback) |
| MEM-PRESSURE-001 | Memory | WARNING | No | Yes (shed load) |
| MEM-PRESSURE-002 | Memory | CRITICAL | No | Emergency mode |
| CB-OPEN-001 | Circuit | WARNING | No | Yes (fallback) |
| OCR-PROCESS-001 | OCR | ERROR | Yes (3×) | Yes (Tesseract) |
| PIPELINE-STAGE-001 | Pipeline | ERROR | Yes (if configured) | Conditional |

---

## Appendix B: Metrics Glossary

| Metric | Type | Description | Alert Threshold |
|--------|------|-------------|----------------|
| `urbanlens_errors_total` | Counter | Total errors by code/severity | > 10/sec |
| `urbanlens_errors_rate_seconds` | Histogram | Error rate distribution | p95 > 1/sec |
| `urbanlens_memory_used_percent` | Gauge | Memory usage percentage | > 90% |
| `urbanlens_gpu_available` | Gauge | GPU availability (0/1) | N/A |
| `urbanlens_sonar_health_percentage` | Gauge | Sonar health (0-100%) | < 50% |
| `urbanlens_circuit_breaker_state` | Gauge | Circuit state (0=closed, 1=open) | Open > 5min |
| `urbanlens_api_request_duration_seconds` | Histogram | API latency distribution | p95 > 5s |
| `urbanlens_ocr_failures_total` | Counter | OCR failures by engine | > 10% rate |
| `urbanlens_oom_kills_total` | Counter | OOM kill events | > 0 |

---

**Document Version**: 1.0.0
**Last Reviewed**: 2025-12-27
**Next Review**: 2026-01-27

---

> "In preparing for battle I have always found that plans are useless, but planning is indispensable." — Dwight D. Eisenhower

This runbook is a living document. Update it as new failure modes are discovered. Every production incident should result in a runbook update.

**End of Runbooks** 🚀
