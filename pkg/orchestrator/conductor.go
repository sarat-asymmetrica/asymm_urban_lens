// Package orchestrator provides the Urban Lens Conductor
// Unified tool orchestration with three-regime routing
package orchestrator

import (
	"context"
	"fmt"
	"sync"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/math"
)

// ============================================================================
// CONSTANTS
// ============================================================================

const (
	// Timeouts (research-friendly)
	DefaultTimeout = 120 * time.Second
	ShortTimeout   = 30 * time.Second
	LongTimeout    = 300 * time.Second

	// Batch sizes (Williams optimal)
	MinBatchSize = 16
	MaxBatchSize = 1024

	// Three-Regime Thresholds
	R1ExplorationThreshold  = 0.3 // 30% - Exploratory, high variance
	R2OptimizationThreshold = 0.5 // 20% range - Maximum complexity
	R3StabilizationThreshold = 1.0 // 50% - Stable, cached
)

// ============================================================================
// REGIME (Three-Regime Dynamics)
// ============================================================================

// Regime represents the three-regime dynamics state
type Regime int

const (
	RegimeUnknown Regime = iota
	R1Exploration        // 30% - Exploratory, divergent
	R2Optimization       // 20% - Maximum complexity, refinement
	R3Stabilization      // 50% - Stable, convergent, cached
)

func (r Regime) String() string {
	switch r {
	case R1Exploration:
		return "Exploration"
	case R2Optimization:
		return "Optimization"
	case R3Stabilization:
		return "Stabilization"
	default:
		return "Unknown"
	}
}

// ============================================================================
// TOOL TYPES
// ============================================================================

// ToolType categorizes different kinds of tools
type ToolType string

const (
	ToolTypeCensus    ToolType = "census"    // Census data processing
	ToolTypeSurvey    ToolType = "survey"    // Survey data validation
	ToolTypeSpatial   ToolType = "spatial"   // Spatial analysis
	ToolTypeDocument  ToolType = "document"  // Document OCR & extraction
	ToolTypeFlood     ToolType = "flood"     // Flood monitoring
	ToolTypeAI        ToolType = "ai"        // AI inference
	ToolTypeData      ToolType = "data"      // General data processing
)

// ============================================================================
// TASK
// ============================================================================

// Task represents a unified task for orchestration
type Task struct {
	ID          string
	Type        ToolType
	Tool        string
	Description string

	Input   interface{}
	Output  string
	Params  map[string]interface{}

	Timeout    time.Duration
	Regime     Regime
	Priority   int
	RetryCount int
	UseCache   bool

	DependsOn []string

	CreatedAt   time.Time
	StartedAt   time.Time
	CompletedAt time.Time
	Metadata    map[string]interface{}
}

// NewTask creates a new task with defaults
func NewTask(toolType ToolType, tool string) *Task {
	return &Task{
		ID:         fmt.Sprintf("task_%d", time.Now().UnixNano()),
		Type:       toolType,
		Tool:       tool,
		Params:     make(map[string]interface{}),
		Timeout:    DefaultTimeout,
		Regime:     RegimeUnknown,
		Priority:   50,
		RetryCount: 3,
		UseCache:   true,
		CreatedAt:  time.Now(),
		Metadata:   make(map[string]interface{}),
	}
}

// Builder methods
func (t *Task) WithInput(input interface{}) *Task    { t.Input = input; return t }
func (t *Task) WithOutput(output string) *Task       { t.Output = output; return t }
func (t *Task) WithParam(key string, val interface{}) *Task { t.Params[key] = val; return t }
func (t *Task) WithTimeout(d time.Duration) *Task    { t.Timeout = d; return t }
func (t *Task) WithRegime(r Regime) *Task            { t.Regime = r; return t }
func (t *Task) WithPriority(p int) *Task             { t.Priority = p; return t }

// ============================================================================
// RESULT
// ============================================================================

// Result represents the outcome of task execution
type Result struct {
	TaskID   string
	Tool     string
	Success  bool
	Error    error
	ErrorMsg string
	ExitCode int

	Data      interface{}
	RawOutput []byte
	Files     []string

	Duration   time.Duration
	BytesIn    int64
	BytesOut   int64

	Regime      Regime
	RegimeScore float64

	FromCache bool
	CacheKey  string
	Timestamp time.Time
	Metadata  map[string]interface{}
}

// NewResult creates a new result
func NewResult(taskID, tool string) *Result {
	return &Result{
		TaskID:    taskID,
		Tool:      tool,
		Timestamp: time.Now(),
		Metadata:  make(map[string]interface{}),
		Files:     []string{},
	}
}

// ============================================================================
// CONDUCTOR
// ============================================================================

// Conductor is the main orchestration engine
type Conductor struct {
	config    *Config
	executors map[ToolType]Executor
	cache     *Cache
	Metrics   *Metrics // Exported for access
	semaphore chan struct{}
	mu        sync.RWMutex
}

// Config holds conductor configuration
type Config struct {
	MaxConcurrent  int
	DefaultTimeout time.Duration
	EnableCache    bool
	CacheDir       string
	EnableOptimizations bool
	LogLevel       string
}

// DefaultConfig returns sensible defaults
func DefaultConfig() *Config {
	return &Config{
		MaxConcurrent:       10,
		DefaultTimeout:      DefaultTimeout,
		EnableCache:         true,
		CacheDir:           "",
		EnableOptimizations: true,
		LogLevel:           "info",
	}
}

// NewConductor creates a new conductor
func NewConductor(config *Config) (*Conductor, error) {
	if config == nil {
		config = DefaultConfig()
	}

	c := &Conductor{
		config:    config,
		executors: make(map[ToolType]Executor),
		cache:     NewCache(),
		Metrics:   NewMetrics(),
		semaphore: make(chan struct{}, config.MaxConcurrent),
	}

	c.registerExecutors()

	return c, nil
}

func (c *Conductor) registerExecutors() {
	// Register built-in executors
	c.executors[ToolTypeData] = &GenericExecutor{}
}

// ============================================================================
// EXECUTE
// ============================================================================

// Execute runs a single task
func (c *Conductor) Execute(ctx context.Context, task *Task) (*Result, error) {
	if task == nil {
		return nil, fmt.Errorf("task cannot be nil")
	}

	task.StartedAt = time.Now()

	// Determine regime
	if task.Regime == RegimeUnknown {
		task.Regime = c.determineRegime(task)
	}

	// Check cache for R3 tasks
	if task.UseCache && c.config.EnableCache && task.Regime == R3Stabilization {
		if cached := c.cache.Get(task); cached != nil {
			c.Metrics.CacheHit()
			return cached, nil
		}
	}

	// Acquire semaphore
	select {
	case c.semaphore <- struct{}{}:
		defer func() { <-c.semaphore }()
	case <-ctx.Done():
		return nil, ctx.Err()
	}

	// Execute
	execCtx, cancel := context.WithTimeout(ctx, task.Timeout)
	defer cancel()

	executor, ok := c.executors[task.Type]
	if !ok {
		executor = &GenericExecutor{}
	}

	result, err := executor.Execute(execCtx, task)
	if err != nil {
		result = NewResult(task.ID, task.Tool)
		result.Success = false
		result.Error = err
		result.ErrorMsg = err.Error()
	}

	task.CompletedAt = time.Now()
	result.Duration = task.CompletedAt.Sub(task.StartedAt)

	c.Metrics.TaskComplete(result.Success, result.Duration)

	// Cache successful R3 results
	if result.Success && task.UseCache && task.Regime == R3Stabilization {
		c.cache.Set(task, result)
	}

	return result, err
}

// Do is the simplest interface: conductor.Do(task)
func (c *Conductor) Do(task *Task) (*Result, error) {
	return c.Execute(context.Background(), task)
}

// ============================================================================
// BATCH EXECUTION (Williams Optimization)
// ============================================================================

// BatchExecute executes multiple tasks with Williams batching
func (c *Conductor) BatchExecute(ctx context.Context, tasks []*Task) ([]*Result, error) {
	n := len(tasks)
	if n == 0 {
		return []*Result{}, nil
	}

	batchSize := math.OptimalBatchSize(n)
	results := make([]*Result, n)

	var wg sync.WaitGroup
	errChan := make(chan error, n)

	for i := 0; i < n; i += batchSize {
		end := i + batchSize
		if end > n {
			end = n
		}

		batch := tasks[i:end]

		for j, task := range batch {
			idx := i + j
			wg.Add(1)

			go func(index int, t *Task) {
				defer wg.Done()
				result, err := c.Execute(ctx, t)
				if err != nil {
					errChan <- fmt.Errorf("task %d failed: %w", index, err)
					return
				}
				results[index] = result
			}(idx, task)
		}

		wg.Wait()
	}

	return results, nil
}

// ============================================================================
// REGIME DETECTION
// ============================================================================

func (c *Conductor) determineRegime(task *Task) Regime {
	score := c.calculateRegimeScore(task)

	if score < R1ExplorationThreshold {
		return R1Exploration
	} else if score < R2OptimizationThreshold {
		return R2Optimization
	}
	return R3Stabilization
}

func (c *Conductor) calculateRegimeScore(task *Task) float64 {
	score := 0.5

	// R3 indicators
	if task.UseCache {
		score += 0.1
	}
	if task.Priority < 50 {
		score += 0.1
	}

	// R1 indicators
	if task.Timeout > DefaultTimeout {
		score -= 0.1
	}
	if task.Priority > 75 {
		score -= 0.15
	}

	// Pattern cluster influence
	if c.config.EnableOptimizations {
		paramCount := len(task.Params)
		cluster := math.PatternCluster(paramCount)
		if cluster == 9 {
			score += 0.1 // Completion cluster → R3
		} else if cluster == 1 {
			score -= 0.1 // Beginning cluster → R1
		}
	}

	if score < 0 {
		score = 0
	}
	if score > 1 {
		score = 1
	}

	return score
}

// ============================================================================
// EXECUTOR INTERFACE
// ============================================================================

// Executor defines the interface for tool execution
type Executor interface {
	Execute(ctx context.Context, task *Task) (*Result, error)
}

// GenericExecutor handles generic tasks
type GenericExecutor struct{}

// Execute runs a generic task
func (e *GenericExecutor) Execute(ctx context.Context, task *Task) (*Result, error) {
	result := NewResult(task.ID, task.Tool)
	result.Success = true
	result.Data = task.Input
	return result, nil
}

// ============================================================================
// CACHE
// ============================================================================

// Cache provides result caching
type Cache struct {
	store map[string]*Result
	mu    sync.RWMutex
}

// NewCache creates a new cache
func NewCache() *Cache {
	return &Cache{
		store: make(map[string]*Result),
	}
}

// Get retrieves from cache
func (c *Cache) Get(task *Task) *Result {
	c.mu.RLock()
	defer c.mu.RUnlock()

	key := fmt.Sprintf("%s:%v", task.Tool, task.Input)
	result, ok := c.store[key]
	if !ok {
		return nil
	}

	result.FromCache = true
	return result
}

// Set stores in cache
func (c *Cache) Set(task *Task, result *Result) {
	c.mu.Lock()
	defer c.mu.Unlock()

	key := fmt.Sprintf("%s:%v", task.Tool, task.Input)
	c.store[key] = result
}

// ============================================================================
// METRICS
// ============================================================================

// Metrics tracks performance
type Metrics struct {
	tasksTotal    int64
	tasksSuccess  int64
	tasksFailed   int64
	cacheHits     int64
	totalDuration time.Duration
	mu            sync.RWMutex
}

// NewMetrics creates metrics tracker
func NewMetrics() *Metrics {
	return &Metrics{}
}

// TaskComplete records task completion
func (m *Metrics) TaskComplete(success bool, duration time.Duration) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.tasksTotal++
	if success {
		m.tasksSuccess++
	} else {
		m.tasksFailed++
	}
	m.totalDuration += duration
}

// CacheHit records cache hit
func (m *Metrics) CacheHit() {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.cacheHits++
}

// Stats returns current metrics
func (m *Metrics) Stats() map[string]interface{} {
	m.mu.RLock()
	defer m.mu.RUnlock()

	return map[string]interface{}{
		"tasks_total":   m.tasksTotal,
		"tasks_success": m.tasksSuccess,
		"tasks_failed":  m.tasksFailed,
		"cache_hits":    m.cacheHits,
	}
}
