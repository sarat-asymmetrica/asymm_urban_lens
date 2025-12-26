// Package swarm implements Williams-optimized swarm orchestration for Urban Lens
//
// Swarm Configuration: Define swarm parameters and resource limits
// Adapted from Ananta self-healing to Urban Lens parallel hypothesis exploration
//
// This module configures swarm behavior:
// - Sizing bounds (min/max swarm size)
// - Variant generation strategies
// - Resource limits (parallel swarms, timeouts)
// - Collatz convergence parameters for democratic superposition
package swarm

import (
	"fmt"
	"time"
)

// SwarmConfig controls swarm orchestration behavior
//
// This configuration determines:
//   - How many parallel agents to spawn per task
//   - Which adaptation strategies to enable
//   - Resource limits to prevent system overload
//   - Convergence parameters for Collatz guarantee
//
// Example:
//
//	config := DefaultSwarmConfig()
//	config.MaxSwarmSize = 30  // Allow more workers
//	config.EnableHybrid = true // Enable experimental hybrid strategy
//	err := config.Validate()
type SwarmConfig struct {
	// === SIZING PARAMETERS ===

	// MinSwarmSize is minimum number of parallel workers per task
	// Default: 1 (always try at least one hypothesis)
	// Range: [1, MaxSwarmSize]
	MinSwarmSize int

	// MaxSwarmSize is maximum number of parallel workers per task
	// Default: 20 (resource constraint)
	// Range: [MinSwarmSize, ∞)
	//
	// Note: With 4 tasks and max 20 workers each, you get 80 parallel processes.
	// Tune based on available CPU cores and memory.
	MaxSwarmSize int

	// === VARIANT GENERATION ===

	// EnableConservative enables conservative adaptation strategy
	// Default: true
	// Conservative: Minimal changes, preserve context, 75% success rate
	EnableConservative bool

	// EnableAggressive enables aggressive adaptation strategy
	// Default: true
	// Aggressive: Full integration, comprehensive exploration, 70% success rate
	EnableAggressive bool

	// EnableHybrid enables hybrid adaptation strategy
	// Default: false (experimental)
	// Hybrid: Mix of conservative and aggressive, 65% success rate
	EnableHybrid bool

	// === RESOURCE LIMITS ===

	// MaxParallelSwarms is maximum number of tasks to process simultaneously
	// Default: 4 (4 tasks × 20 variants = 80 max processes)
	// Range: [1, ∞)
	//
	// Total parallel processes = MaxParallelSwarms × MaxSwarmSize
	// Example: 4 swarms × 20 workers = 80 parallel sub-agents
	MaxParallelSwarms int

	// TimeoutPerVariant is maximum time per variant attempt
	// Default: 30s (execute + validate + score)
	// Range: [1s, ∞)
	//
	// If a sub-agent takes longer than this, it's killed.
	TimeoutPerVariant time.Duration

	// === COLLATZ CONVERGENCE ===

	// MaxIterations is maximum attempts before declaring stuck
	// Default: 100 (max iterations before giving up)
	// Range: [1, ∞)
	//
	// Collatz guarantee: quality score increases each iteration.
	// If stuck in loop (not improving), we switch strategy.
	// After MaxIterations without convergence, declare failure.
	MaxIterations int

	// MinProgress is minimum quality improvement required per iteration
	// Default: 0.01 (1% quality improvement required)
	// Range: [0.0, 1.0]
	//
	// If quality[i] >= quality[i-1] × (1 + MinProgress),
	// we're not making progress → switch strategy.
	MinProgress float64
}

// DefaultSwarmConfig returns recommended default configuration
//
// These defaults are tuned for:
//   - 4-8 CPU cores
//   - 8-16 GB RAM
//   - Typical AI workload (parallel hypothesis exploration)
//   - Local development environment
//
// For production/cloud environments, increase MaxParallelSwarms and MaxSwarmSize.
//
// Returns:
//   - Default configuration ready to use
//
// Example:
//
//	config := DefaultSwarmConfig()
//	// Use as-is or customize specific fields
//	config.MaxSwarmSize = 30
func DefaultSwarmConfig() *SwarmConfig {
	return &SwarmConfig{
		// Sizing
		MinSwarmSize: 1,
		MaxSwarmSize: 20,

		// Variant generation
		EnableConservative: true,
		EnableAggressive:   true,
		EnableHybrid:       false, // Experimental

		// Resource limits
		MaxParallelSwarms: 4,
		TimeoutPerVariant: 30 * time.Second,

		// Collatz convergence
		MaxIterations: 100,
		MinProgress:   0.01, // 1% improvement required
	}
}

// Validate checks configuration for consistency and bounds
//
// Validates:
//   - MinSwarmSize ≥ 1
//   - MaxSwarmSize ≥ MinSwarmSize
//   - MaxParallelSwarms ≥ 1
//   - TimeoutPerVariant ≥ 1s
//   - MaxIterations ≥ 1
//   - MinProgress in [0.0, 1.0]
//   - At least one strategy enabled
//
// Returns:
//   - nil if valid
//   - error describing validation failure
//
// Example:
//
//	config := &SwarmConfig{MinSwarmSize: 0, ...}
//	err := config.Validate()
//	// Returns error: "MinSwarmSize must be >= 1"
func (c *SwarmConfig) Validate() error {
	// Validate sizing
	if c.MinSwarmSize < 1 {
		return fmt.Errorf("MinSwarmSize must be >= 1, got %d", c.MinSwarmSize)
	}

	if c.MaxSwarmSize < c.MinSwarmSize {
		return fmt.Errorf(
			"MaxSwarmSize (%d) must be >= MinSwarmSize (%d)",
			c.MaxSwarmSize, c.MinSwarmSize,
		)
	}

	// Validate resource limits
	if c.MaxParallelSwarms < 1 {
		return fmt.Errorf("MaxParallelSwarms must be >= 1, got %d", c.MaxParallelSwarms)
	}

	if c.TimeoutPerVariant < time.Second {
		return fmt.Errorf(
			"TimeoutPerVariant must be >= 1s, got %v",
			c.TimeoutPerVariant,
		)
	}

	// Validate convergence
	if c.MaxIterations < 1 {
		return fmt.Errorf("MaxIterations must be >= 1, got %d", c.MaxIterations)
	}

	if c.MinProgress < 0.0 || c.MinProgress > 1.0 {
		return fmt.Errorf(
			"MinProgress must be in [0.0, 1.0], got %.3f",
			c.MinProgress,
		)
	}

	// Validate at least one strategy enabled
	if !c.EnableConservative && !c.EnableAggressive && !c.EnableHybrid {
		return fmt.Errorf("at least one adaptation strategy must be enabled")
	}

	return nil
}

// EstimateMaxParallelProcesses estimates maximum concurrent processes
//
// Calculates worst-case parallel process count:
//   Total = MaxParallelSwarms × MaxSwarmSize
//
// Use this to ensure your system can handle the load.
//
// Returns:
//   - Maximum number of parallel sub-agent processes
//
// Example:
//
//	config := DefaultSwarmConfig()
//	maxProcs := config.EstimateMaxParallelProcesses()
//	// Returns 80 (4 swarms × 20 workers)
//	//
//	// If you have 8 CPU cores, each core handles ~10 processes.
//	// If you have 16 GB RAM and each process uses ~100 MB, you need ~8 GB.
func (c *SwarmConfig) EstimateMaxParallelProcesses() int {
	return c.MaxParallelSwarms * c.MaxSwarmSize
}

// EstimateEnabledStrategies returns count of enabled strategies
//
// Used for variant count estimation:
//   Variants per task ≈ swarm_size × enabled_strategies
//
// Returns:
//   - Number of enabled adaptation strategies
//
// Example:
//
//	config := DefaultSwarmConfig()
//	strategyCount := config.EstimateEnabledStrategies()
//	// Returns 2 (conservative + aggressive)
func (c *SwarmConfig) EstimateEnabledStrategies() int {
	count := 1 // Always have direct strategy

	if c.EnableConservative {
		count++
	}

	if c.EnableAggressive {
		count++
	}

	if c.EnableHybrid {
		count++
	}

	return count
}

// Clone creates a deep copy of the configuration
//
// Useful for creating modified versions without affecting original.
//
// Returns:
//   - Independent copy of configuration
//
// Example:
//
//	base := DefaultSwarmConfig()
//	custom := base.Clone()
//	custom.MaxSwarmSize = 50 // Doesn't affect base
func (c *SwarmConfig) Clone() *SwarmConfig {
	return &SwarmConfig{
		MinSwarmSize:       c.MinSwarmSize,
		MaxSwarmSize:       c.MaxSwarmSize,
		EnableConservative: c.EnableConservative,
		EnableAggressive:   c.EnableAggressive,
		EnableHybrid:       c.EnableHybrid,
		MaxParallelSwarms:  c.MaxParallelSwarms,
		TimeoutPerVariant:  c.TimeoutPerVariant,
		MaxIterations:      c.MaxIterations,
		MinProgress:        c.MinProgress,
	}
}

// String returns human-readable configuration summary
//
// Returns:
//   - Multi-line string describing all config parameters
//
// Example:
//
//	config := DefaultSwarmConfig()
//	fmt.Println(config.String())
//	// Output:
//	// SwarmConfig{
//	//   Sizing: min=1, max=20
//	//   Strategies: conservative=true, aggressive=true, hybrid=false
//	//   Resources: maxSwarms=4, timeout=30s
//	//   Convergence: maxIter=100, minProgress=0.01
//	//   Max Parallel: 80 processes
//	// }
func (c *SwarmConfig) String() string {
	return fmt.Sprintf(
		"SwarmConfig{\n"+
			"  Sizing: min=%d, max=%d\n"+
			"  Strategies: conservative=%t, aggressive=%t, hybrid=%t\n"+
			"  Resources: maxSwarms=%d, timeout=%v\n"+
			"  Convergence: maxIter=%d, minProgress=%.3f\n"+
			"  Max Parallel: %d processes\n"+
			"}",
		c.MinSwarmSize,
		c.MaxSwarmSize,
		c.EnableConservative,
		c.EnableAggressive,
		c.EnableHybrid,
		c.MaxParallelSwarms,
		c.TimeoutPerVariant,
		c.MaxIterations,
		c.MinProgress,
		c.EstimateMaxParallelProcesses(),
	)
}
