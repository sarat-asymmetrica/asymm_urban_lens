// Package chaos implements chaos engineering infrastructure for UrbanLens
//
// Philosophy: "Test your failures before production tests them for you." - Margaret Hamilton
//
// Chaos Monkey can inject:
// - Latency (network delays, slow GPU, database lag)
// - Errors (API failures, GPU unavailable, database deadlock)
// - Timeouts (partial completion, hanging requests)
// - Partial failures (N out of M sonars fail)
//
// Usage:
//   monkey := chaos.NewChaosMonkey()
//   monkey.InjectLatency("gpu", 500*time.Millisecond)
//   monkey.InjectError("sonar:code", errors.New("timeout"))
//   monkey.Start(chaos.ScenarioGPUFailure())
//
// Author: Margaret Hamilton's spirit (Apollo 11 guidance computer, 1969)
package chaos

import (
	"context"
	"errors"
	"fmt"
	"math/rand"
	"sync"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// CHAOS MONKEY - FAILURE INJECTION ENGINE
// ═══════════════════════════════════════════════════════════════════════════

// ChaosMonkey injects controlled failures into the system
type ChaosMonkey struct {
	mu              sync.RWMutex
	latencyInjected map[string]time.Duration // target -> delay
	errorInjected   map[string]error         // target -> error
	timeoutInjected map[string]bool          // target -> timeout flag
	partialFailures map[string]float64       // target -> failure rate (0.0-1.0)
	enabled         bool
	logger          func(msg string)
	faults          []Fault
}

// Fault records an injected failure
type Fault struct {
	Target      string        // Component that failed
	Type        FaultType     // Type of failure
	InjectedAt  time.Time     // When fault was injected
	Duration    time.Duration // How long fault lasted
	Recovered   bool          // Did system recover?
	Impact      string        // What broke?
	Mitigation  string        // What fixed it?
}

// FaultType categorizes failures
type FaultType string

const (
	FaultLatency        FaultType = "LATENCY"
	FaultError          FaultType = "ERROR"
	FaultTimeout        FaultType = "TIMEOUT"
	FaultPartialFailure FaultType = "PARTIAL_FAILURE"
	FaultMemoryPressure FaultType = "MEMORY_PRESSURE"
	FaultNetworkPartition FaultType = "NETWORK_PARTITION"
)

// NewChaosMonkey creates failure injection engine
func NewChaosMonkey() *ChaosMonkey {
	return &ChaosMonkey{
		latencyInjected: make(map[string]time.Duration),
		errorInjected:   make(map[string]error),
		timeoutInjected: make(map[string]bool),
		partialFailures: make(map[string]float64),
		enabled:         false,
		logger:          func(msg string) { fmt.Println("[CHAOS]", msg) },
		faults:          make([]Fault, 0, 100),
	}
}

// InjectLatency adds delay to target component
//
// Examples:
//   monkey.InjectLatency("gpu", 500*time.Millisecond)          // Slow GPU
//   monkey.InjectLatency("sonar:code", 2*time.Second)          // Slow code sonar
//   monkey.InjectLatency("api:openai", 5*time.Second)          // Slow API
//   monkey.InjectLatency("db:query", 100*time.Millisecond)     // Slow database
func (cm *ChaosMonkey) InjectLatency(target string, duration time.Duration) {
	cm.mu.Lock()
	defer cm.mu.Unlock()

	cm.latencyInjected[target] = duration
	cm.logger(fmt.Sprintf("⏱️  Injected latency: %s will delay %v", target, duration))

	cm.faults = append(cm.faults, Fault{
		Target:     target,
		Type:       FaultLatency,
		InjectedAt: time.Now(),
		Duration:   duration,
		Impact:     fmt.Sprintf("Delays of %v on %s", duration, target),
	})
}

// InjectError makes target component return error
//
// Examples:
//   monkey.InjectError("gpu", errors.New("GPU not available"))
//   monkey.InjectError("sonar:ux", errors.New("telemetry collection failed"))
//   monkey.InjectError("api:aimlapi", errors.New("rate limit exceeded"))
func (cm *ChaosMonkey) InjectError(target string, err error) {
	cm.mu.Lock()
	defer cm.mu.Unlock()

	cm.errorInjected[target] = err
	cm.logger(fmt.Sprintf("❌ Injected error: %s will fail with '%v'", target, err))

	cm.faults = append(cm.faults, Fault{
		Target:     target,
		Type:       FaultError,
		InjectedAt: time.Now(),
		Impact:     fmt.Sprintf("Error on %s: %v", target, err),
	})
}

// InjectTimeout makes target component time out (never return)
//
// Examples:
//   monkey.InjectTimeout("gpu")                    // GPU hangs forever
//   monkey.InjectTimeout("sonar:journey")          // Journey sonar times out
func (cm *ChaosMonkey) InjectTimeout(target string) {
	cm.mu.Lock()
	defer cm.mu.Unlock()

	cm.timeoutInjected[target] = true
	cm.logger(fmt.Sprintf("⏰ Injected timeout: %s will hang", target))

	cm.faults = append(cm.faults, Fault{
		Target:     target,
		Type:       FaultTimeout,
		InjectedAt: time.Now(),
		Impact:     fmt.Sprintf("Timeout on %s (hangs forever)", target),
	})
}

// InjectPartialFailure makes N% of requests to targets fail
//
// Examples:
//   monkey.InjectPartialFailure([]string{"sonar:code", "sonar:ux"}, 0.5)  // 50% fail
//   monkey.InjectPartialFailure([]string{"gpu"}, 0.1)                      // 10% fail
func (cm *ChaosMonkey) InjectPartialFailure(targets []string, failureRate float64) {
	cm.mu.Lock()
	defer cm.mu.Unlock()

	for _, target := range targets {
		cm.partialFailures[target] = failureRate
		cm.logger(fmt.Sprintf("💥 Injected partial failure: %s will fail %.1f%% of the time",
			target, failureRate*100))

		cm.faults = append(cm.faults, Fault{
			Target:     target,
			Type:       FaultPartialFailure,
			InjectedAt: time.Now(),
			Impact:     fmt.Sprintf("%.1f%% failure rate on %s", failureRate*100, target),
		})
	}
}

// Enable activates chaos injection
func (cm *ChaosMonkey) Enable() {
	cm.mu.Lock()
	defer cm.mu.Unlock()
	cm.enabled = true
	cm.logger("🐵 Chaos Monkey ENABLED")
}

// Disable stops chaos injection
func (cm *ChaosMonkey) Disable() {
	cm.mu.Lock()
	defer cm.mu.Unlock()
	cm.enabled = false
	cm.logger("🛑 Chaos Monkey DISABLED")
}

// ClearAll removes all injected faults
func (cm *ChaosMonkey) ClearAll() {
	cm.mu.Lock()
	defer cm.mu.Unlock()

	cm.latencyInjected = make(map[string]time.Duration)
	cm.errorInjected = make(map[string]error)
	cm.timeoutInjected = make(map[string]bool)
	cm.partialFailures = make(map[string]float64)
	cm.logger("🧹 Cleared all injected faults")
}

// Check applies chaos to target and returns error/delay
//
// Usage in production code:
//   if err := chaosMonkey.Check(ctx, "gpu"); err != nil {
//       return nil, fmt.Errorf("GPU unavailable: %w", err)
//   }
func (cm *ChaosMonkey) Check(ctx context.Context, target string) error {
	cm.mu.RLock()
	defer cm.mu.RUnlock()

	if !cm.enabled {
		return nil
	}

	// Check for timeout injection
	if cm.timeoutInjected[target] {
		cm.logger(fmt.Sprintf("⏰ Timeout triggered on %s - hanging forever!", target))
		<-ctx.Done() // Wait until context cancelled
		return ctx.Err()
	}

	// Check for error injection
	if err, ok := cm.errorInjected[target]; ok {
		cm.logger(fmt.Sprintf("❌ Error triggered on %s: %v", target, err))
		return err
	}

	// Check for partial failure injection
	if rate, ok := cm.partialFailures[target]; ok {
		if rand.Float64() < rate {
			err := fmt.Errorf("partial failure: %s randomly failed", target)
			cm.logger(fmt.Sprintf("💥 Partial failure triggered on %s", target))
			return err
		}
	}

	// Check for latency injection
	if delay, ok := cm.latencyInjected[target]; ok {
		cm.logger(fmt.Sprintf("⏱️  Latency triggered on %s - sleeping %v", target, delay))
		select {
		case <-time.After(delay):
			// Delay completed
		case <-ctx.Done():
			return ctx.Err()
		}
	}

	return nil
}

// GetInjectedFaults returns all recorded faults
func (cm *ChaosMonkey) GetInjectedFaults() []Fault {
	cm.mu.RLock()
	defer cm.mu.RUnlock()

	result := make([]Fault, len(cm.faults))
	copy(result, cm.faults)
	return result
}

// RecordRecovery marks a fault as recovered
func (cm *ChaosMonkey) RecordRecovery(target string, mitigation string) {
	cm.mu.Lock()
	defer cm.mu.Unlock()

	// Find most recent fault for target
	for i := len(cm.faults) - 1; i >= 0; i-- {
		if cm.faults[i].Target == target && !cm.faults[i].Recovered {
			cm.faults[i].Recovered = true
			cm.faults[i].Mitigation = mitigation
			cm.faults[i].Duration = time.Since(cm.faults[i].InjectedAt)
			cm.logger(fmt.Sprintf("✅ Recovery recorded: %s recovered via '%s'", target, mitigation))
			break
		}
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// CHAOS SCENARIOS - PRE-DEFINED FAILURE PATTERNS
// ═══════════════════════════════════════════════════════════════════════════

// Scenario represents a chaos testing scenario
type Scenario struct {
	Name        string
	Description string
	Apply       func(cm *ChaosMonkey)
	Validate    func(cm *ChaosMonkey) error
}

// ScenarioGPUFailure simulates GPU unavailable
//
// Impact: GPU operations should fallback to CPU
// Expected: System continues with degraded performance
func ScenarioGPUFailure() Scenario {
	return Scenario{
		Name:        "GPU Failure",
		Description: "GPU becomes unavailable - should fallback to CPU",
		Apply: func(cm *ChaosMonkey) {
			cm.InjectError("gpu", errors.New("GPU not available"))
			cm.InjectError("gpu:quaternion", errors.New("GPU compute failed"))
			cm.InjectError("gpu:vqc", errors.New("GPU VQC engine unavailable"))
		},
		Validate: func(cm *ChaosMonkey) error {
			// Check that at least one fault was recorded
			faults := cm.GetInjectedFaults()
			if len(faults) == 0 {
				return errors.New("no GPU faults injected")
			}

			// Check for recovery (fallback to CPU)
			recovered := false
			for _, f := range faults {
				if f.Target == "gpu" && f.Recovered {
					recovered = true
					break
				}
			}

			if !recovered {
				return errors.New("GPU failure not recovered (CPU fallback missing?)")
			}

			return nil
		},
	}
}

// ScenarioSonarPartialOutage simulates N sonars failing
//
// Impact: Some sonars unavailable, others continue
// Expected: System returns partial results, logs failures
func ScenarioSonarPartialOutage(n int) Scenario {
	sonarNames := []string{"code", "ux", "design", "journey", "state", "semantic"}

	return Scenario{
		Name:        fmt.Sprintf("Sonar Partial Outage (%d/%d)", n, len(sonarNames)),
		Description: fmt.Sprintf("%d out of %d sonars fail", n, len(sonarNames)),
		Apply: func(cm *ChaosMonkey) {
			// Fail first N sonars
			for i := 0; i < n && i < len(sonarNames); i++ {
				target := fmt.Sprintf("sonar:%s", sonarNames[i])
				cm.InjectError(target, fmt.Errorf("%s sonar unavailable", sonarNames[i]))
			}
		},
		Validate: func(cm *ChaosMonkey) error {
			faults := cm.GetInjectedFaults()
			failedSonars := 0
			for _, f := range faults {
				if f.Type == FaultError && len(f.Target) > 6 && f.Target[:6] == "sonar:" {
					failedSonars++
				}
			}

			if failedSonars != n {
				return fmt.Errorf("expected %d sonar failures, got %d", n, failedSonars)
			}

			return nil
		},
	}
}

// ScenarioNetworkLatency simulates slow network
//
// Impact: All API calls delayed
// Expected: System waits patiently, times out gracefully
func ScenarioNetworkLatency(delay time.Duration) Scenario {
	return Scenario{
		Name:        "Network Latency",
		Description: fmt.Sprintf("All API calls delayed by %v", delay),
		Apply: func(cm *ChaosMonkey) {
			cm.InjectLatency("api:openai", delay)
			cm.InjectLatency("api:aimlapi", delay)
			cm.InjectLatency("api:anthropic", delay)
			cm.InjectLatency("network", delay)
		},
		Validate: func(cm *ChaosMonkey) error {
			faults := cm.GetInjectedFaults()
			latencyFaults := 0
			for _, f := range faults {
				if f.Type == FaultLatency {
					latencyFaults++
				}
			}

			if latencyFaults == 0 {
				return errors.New("no latency faults injected")
			}

			return nil
		},
	}
}

// ScenarioAPITimeout simulates API never responding
//
// Impact: API calls hang forever
// Expected: Context timeout triggers, error returned
func ScenarioAPITimeout() Scenario {
	return Scenario{
		Name:        "API Timeout",
		Description: "API calls hang forever - context timeout should fire",
		Apply: func(cm *ChaosMonkey) {
			cm.InjectTimeout("api:openai")
			cm.InjectTimeout("api:aimlapi")
		},
		Validate: func(cm *ChaosMonkey) error {
			faults := cm.GetInjectedFaults()
			timeoutFaults := 0
			for _, f := range faults {
				if f.Type == FaultTimeout {
					timeoutFaults++
				}
			}

			if timeoutFaults == 0 {
				return errors.New("no timeout faults injected")
			}

			return nil
		},
	}
}

// ScenarioMemoryPressure simulates low memory
//
// Impact: Allocations fail, GC thrashes
// Expected: Graceful degradation, error messages
func ScenarioMemoryPressure() Scenario {
	return Scenario{
		Name:        "Memory Pressure",
		Description: "System under memory pressure - allocations may fail",
		Apply: func(cm *ChaosMonkey) {
			cm.InjectError("memory", errors.New("out of memory"))
			cm.InjectError("alloc:large", errors.New("allocation failed"))
			cm.InjectPartialFailure([]string{"alloc:medium"}, 0.3) // 30% fail
		},
		Validate: func(cm *ChaosMonkey) error {
			faults := cm.GetInjectedFaults()
			memoryFaults := 0
			for _, f := range faults {
				if f.Type == FaultError || f.Type == FaultPartialFailure {
					if len(f.Target) >= 5 && (f.Target[:6] == "memory" || f.Target[:5] == "alloc") {
						memoryFaults++
					}
				}
			}

			if memoryFaults == 0 {
				return errors.New("no memory pressure faults injected")
			}

			return nil
		},
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// CHAOS CONTROLLER - SCENARIO ORCHESTRATION
// ═══════════════════════════════════════════════════════════════════════════

// ChaosController manages scenario execution
type ChaosController struct {
	monkey       *ChaosMonkey
	scenario     *Scenario
	startTime    time.Time
	stopTime     time.Time
	running      bool
	mu           sync.Mutex
}

// NewChaosController creates scenario orchestrator
func NewChaosController(monkey *ChaosMonkey) *ChaosController {
	return &ChaosController{
		monkey:  monkey,
		running: false,
	}
}

// Start executes chaos scenario
func (cc *ChaosController) Start(scenario Scenario) error {
	cc.mu.Lock()
	defer cc.mu.Unlock()

	if cc.running {
		return errors.New("scenario already running")
	}

	cc.scenario = &scenario
	cc.startTime = time.Now()
	cc.running = true

	cc.monkey.logger(fmt.Sprintf("🎬 Starting scenario: %s", scenario.Name))
	cc.monkey.logger(fmt.Sprintf("📋 Description: %s", scenario.Description))

	// Apply scenario
	scenario.Apply(cc.monkey)
	cc.monkey.Enable()

	return nil
}

// Stop ends chaos scenario and validates results
func (cc *ChaosController) Stop() error {
	cc.mu.Lock()
	defer cc.mu.Unlock()

	if !cc.running {
		return errors.New("no scenario running")
	}

	cc.stopTime = time.Now()
	cc.monkey.Disable()

	duration := cc.stopTime.Sub(cc.startTime)
	cc.monkey.logger(fmt.Sprintf("🛑 Stopping scenario: %s (ran for %v)", cc.scenario.Name, duration))

	// Validate scenario
	if err := cc.scenario.Validate(cc.monkey); err != nil {
		return fmt.Errorf("scenario validation failed: %w", err)
	}

	cc.monkey.logger("✅ Scenario validation passed")
	cc.running = false

	return nil
}

// GetInjectedFaults returns all faults from current scenario
func (cc *ChaosController) GetInjectedFaults() []Fault {
	return cc.monkey.GetInjectedFaults()
}

// IsRunning returns true if scenario is active
func (cc *ChaosController) IsRunning() bool {
	cc.mu.Lock()
	defer cc.mu.Unlock()
	return cc.running
}
