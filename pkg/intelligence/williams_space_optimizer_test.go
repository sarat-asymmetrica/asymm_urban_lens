package intelligence

import (
	"math"
	"testing"
)

// TestNewWilliamsSpaceOptimizer validates optimizer initialization
func TestNewWilliamsSpaceOptimizer(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	if optimizer == nil {
		t.Fatal("NewWilliamsSpaceOptimizer returned nil")
	}
}

// TestCalculateSpaceBound validates Williams space bound formula
func TestCalculateSpaceBound(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	tests := []struct {
		name           string
		timeComplexity int
		expectedMin    int
		expectedMax    int
		minEfficiency  float64
	}{
		{"t=1 (base case)", 1, 1, 1, 1.0},
		{"t=10", 10, 10, 11, 1.0},
		{"t=100", 100, 66, 67, 1.5}, // √100 × log₂(100) ≈ 66.4
		{"t=1000", 1000, 315, 316, 3.0}, // √1000 × log₂(1000) ≈ 315
		{"t=0 (invalid)", 0, 0, 0, 0.0},
		{"t=-1 (invalid)", -1, 0, 0, 0.0},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := optimizer.CalculateSpaceBound(tt.timeComplexity)

			// Check space bound range
			if result.SpaceBound < tt.expectedMin || result.SpaceBound > tt.expectedMax {
				t.Errorf("Expected space bound in [%d, %d], got %d",
					tt.expectedMin, tt.expectedMax, result.SpaceBound)
			}

			// Check efficiency
			if result.Efficiency < tt.minEfficiency {
				t.Errorf("Expected efficiency ≥ %.2f, got %.2f",
					tt.minEfficiency, result.Efficiency)
			}

			// Check formula string
			if tt.timeComplexity > 0 && result.Formula == "" {
				t.Error("Expected non-empty formula string")
			}
		})
	}
}

// TestCalculateEfficiency validates efficiency calculation
func TestCalculateEfficiency(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	tests := []struct {
		timeComplexity int
		minEfficiency  float64
		maxEfficiency  float64
	}{
		{10, 1.0, 1.0},
		{100, 1.5, 1.6},
		{1000, 3.1, 3.2},
		{10000, 6.0, 8.0}, // Higher complexities = higher efficiency
	}

	for _, tt := range tests {
		efficiency := optimizer.CalculateEfficiency(tt.timeComplexity)

		if efficiency < tt.minEfficiency || efficiency > tt.maxEfficiency {
			t.Errorf("t=%d: Expected efficiency in [%.2f, %.2f], got %.2f",
				tt.timeComplexity, tt.minEfficiency, tt.maxEfficiency, efficiency)
		}
	}
}

// TestCalculateConfidenceMultiplier validates OCR confidence enhancement
func TestCalculateConfidenceMultiplier(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	tests := []struct {
		fieldsExtracted int
		minConfidence   float64
		maxConfidence   float64
	}{
		{0, 0.85, 0.85},   // Minimum
		{1, 0.85, 0.86},   // Low extraction
		{5, 0.87, 0.90},   // Medium extraction
		{10, 0.90, 0.95},  // Good extraction
		{15, 0.95, 1.00},  // High extraction
		{20, 0.98, 1.00},  // Maximum
	}

	for _, tt := range tests {
		confidence := optimizer.CalculateConfidenceMultiplier(tt.fieldsExtracted, "OCR")

		if confidence < tt.minConfidence || confidence > tt.maxConfidence {
			t.Errorf("Fields=%d: Expected confidence in [%.2f, %.2f], got %.2f",
				tt.fieldsExtracted, tt.minConfidence, tt.maxConfidence, confidence)
		}

		// Confidence must be in [0.85, 1.00]
		if confidence < 0.85 || confidence > 1.00 {
			t.Errorf("Confidence %.2f outside valid range [0.85, 1.00]", confidence)
		}
	}
}

// TestOptimizeBatchSize validates batch optimization
func TestOptimizeBatchSize(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	tests := []struct {
		name             string
		totalItems       int
		memoryMB         int
		avgItemSize      int
		expectedMinBatch int
		expectedMaxBatch int
	}{
		{
			"1000 items, 64MB memory",
			1000, 64, 1024,
			300, 320, // Williams bound ~315
		},
		{
			"100 items, small memory (constrained)",
			100, 1, 1024,
			1, 2, // Memory-constrained
		},
		{
			"Small batch",
			10, 64, 1024,
			10, 11,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := optimizer.OptimizeBatchSize(tt.totalItems, tt.memoryMB, tt.avgItemSize)

			if result.OptimalBatchSize < tt.expectedMinBatch || result.OptimalBatchSize > tt.expectedMaxBatch {
				t.Errorf("Expected batch size in [%d, %d], got %d",
					tt.expectedMinBatch, tt.expectedMaxBatch, result.OptimalBatchSize)
			}

			// Ensure batch count makes sense
			expectedBatches := (tt.totalItems + result.OptimalBatchSize - 1) / result.OptimalBatchSize
			if result.NumBatches != expectedBatches {
				t.Errorf("Expected %d batches, got %d", expectedBatches, result.NumBatches)
			}

			if result.Explanation == "" {
				t.Error("Expected non-empty explanation")
			}
		})
	}
}

// TestGenerateOptimalTestSamples validates test sample generation
func TestGenerateOptimalTestSamples(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	tests := []struct {
		totalCoverage int
		minSamples    int
		maxSamples    int
	}{
		{100, 66, 67},
		{1000, 315, 316},
		{10, 10, 11},
		{1, 1, 1},
		{0, 0, 0},
	}

	for _, tt := range tests {
		samples := optimizer.GenerateOptimalTestSamples(tt.totalCoverage)

		if samples < tt.minSamples || samples > tt.maxSamples {
			t.Errorf("Coverage=%d: Expected samples in [%d, %d], got %d",
				tt.totalCoverage, tt.minSamples, tt.maxSamples, samples)
		}
	}
}

// TestCalculateMemoryReduction validates memory savings calculation
func TestCalculateMemoryReduction(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	tests := []struct {
		timeComplexity  int
		minReduction    float64
		maxReduction    float64
	}{
		{10, 0.0, 10.0},    // Small n = small reduction
		{100, 30.0, 40.0},  // 100 → 66 ≈ 34% reduction
		{1000, 68.0, 69.0}, // 1000 → 315 ≈ 68.5% reduction
		{10000, 85.0, 88.0}, // Higher n = higher reduction
	}

	for _, tt := range tests {
		reduction := optimizer.CalculateMemoryReduction(tt.timeComplexity)

		if reduction < tt.minReduction || reduction > tt.maxReduction {
			t.Errorf("t=%d: Expected reduction in [%.1f%%, %.1f%%], got %.1f%%",
				tt.timeComplexity, tt.minReduction, tt.maxReduction, reduction)
		}
	}
}

// TestValidateEfficiencyGain validates efficiency threshold
func TestValidateEfficiencyGain(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	tests := []struct {
		timeComplexity int
		shouldPass     bool
	}{
		{1, false},    // Base case, efficiency = 1.0
		{10, false},   // Small n, efficiency ≈ 1.0
		{100, true},   // efficiency ≈ 1.5
		{1000, true},  // efficiency ≈ 3.17
		{10000, true}, // efficiency > 6.0
	}

	for _, tt := range tests {
		passed := optimizer.ValidateEfficiencyGain(tt.timeComplexity)

		if passed != tt.shouldPass {
			t.Errorf("t=%d: Expected validation=%v, got %v",
				tt.timeComplexity, tt.shouldPass, passed)
		}
	}
}

// TestFormatSpaceBound validates formatting
func TestFormatSpaceBound(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	output := optimizer.FormatSpaceBound(1000)

	expected := []string{
		"1000",
		"operations",
		"space",
		"efficiency",
		"reduction",
	}

	for _, exp := range expected {
		if !williamsTestStringContains(output, exp) {
			t.Errorf("Output missing expected string: %s\nOutput: %s", exp, output)
		}
	}
}

// TestBoostOCRConfidence validates OCR confidence boosting
func TestBoostOCRConfidence(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	tests := []struct {
		name            string
		baseConfidence  float64
		fieldsExtracted int
		minBoosted      float64
		maxBoosted      float64
	}{
		{
			"High base, high extraction",
			0.90, 15,
			0.90, 1.00,
		},
		{
			"Low base, low extraction",
			0.70, 2,
			0.59, 0.61, // 0.70 × 0.85 ≈ 0.60
		},
		{
			"High base, no extraction",
			0.95, 0,
			0.80, 0.81, // 0.95 × 0.85 ≈ 0.81
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			boost := optimizer.BoostOCRConfidence(tt.baseConfidence, tt.fieldsExtracted)

			if boost.BoostedConfidence < tt.minBoosted || boost.BoostedConfidence > tt.maxBoosted {
				t.Errorf("Expected boosted confidence in [%.2f, %.2f], got %.2f",
					tt.minBoosted, tt.maxBoosted, boost.BoostedConfidence)
			}

			// Boosted confidence must not exceed 1.0
			if boost.BoostedConfidence > 1.0 {
				t.Errorf("Boosted confidence %.2f exceeds 1.0", boost.BoostedConfidence)
			}

			// Check fields extracted
			if boost.FieldsExtracted != tt.fieldsExtracted {
				t.Errorf("Expected %d fields, got %d", tt.fieldsExtracted, boost.FieldsExtracted)
			}

			// Check multiplier range
			if boost.EfficiencyMultiplier < 0.85 || boost.EfficiencyMultiplier > 1.00 {
				t.Errorf("Multiplier %.2f outside valid range [0.85, 1.00]",
					boost.EfficiencyMultiplier)
			}
		})
	}
}

// TestWilliamsFormulaAccuracy validates mathematical correctness
func TestWilliamsFormulaAccuracy(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	// Manually calculate Williams formula for t=100
	t_val := 100.0
	sqrtT := math.Sqrt(t_val)      // 10.0
	log2T := math.Log2(t_val)      // ≈ 6.64
	expected := int(math.Floor(sqrtT * log2T)) // ≈ 66

	result := optimizer.CalculateSpaceBound(100)

	if result.SpaceBound != expected {
		t.Errorf("Manual calculation: expected %d, formula returned %d",
			expected, result.SpaceBound)
	}

	// Verify efficiency calculation
	expectedEfficiency := t_val / float64(expected)
	if math.Abs(result.Efficiency-expectedEfficiency) > 0.01 {
		t.Errorf("Expected efficiency %.2f, got %.2f",
			expectedEfficiency, result.Efficiency)
	}
}

// TestResearchValidationThresholds validates research paper claims
func TestResearchValidationThresholds(t *testing.T) {
	optimizer := NewWilliamsSpaceOptimizer()

	// Research claims: 1.5x-7.5x efficiency gains
	tests := []int{10, 50, 100, 500, 1000, 5000}

	for _, tc := range tests {
		efficiency := optimizer.CalculateEfficiency(tc)

		// Must be within research-validated range
		if efficiency < 1.0 || efficiency > 8.0 {
			t.Errorf("t=%d: Efficiency %.2f outside validated range [1.0, 8.0]",
				tc, efficiency)
		}

		// For t ≥ 100, should achieve at least 1.5x
		if tc >= 100 && efficiency < 1.5 {
			t.Errorf("t=%d: Efficiency %.2f below minimum validated 1.5x",
				tc, efficiency)
		}
	}
}

// BenchmarkCalculateSpaceBound benchmarks space bound calculation
func BenchmarkCalculateSpaceBound(b *testing.B) {
	optimizer := NewWilliamsSpaceOptimizer()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = optimizer.CalculateSpaceBound(1000)
	}
}

// BenchmarkCalculateConfidenceMultiplier benchmarks confidence calculation
func BenchmarkCalculateConfidenceMultiplier(b *testing.B) {
	optimizer := NewWilliamsSpaceOptimizer()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = optimizer.CalculateConfidenceMultiplier(15, "OCR")
	}
}

// BenchmarkOptimizeBatchSize benchmarks batch optimization
func BenchmarkOptimizeBatchSize(b *testing.B) {
	optimizer := NewWilliamsSpaceOptimizer()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = optimizer.OptimizeBatchSize(1000, 64, 1024)
	}
}

// williamsTestStringContains checks if haystack contains needle (simple substring check)
func williamsTestStringContains(haystack, needle string) bool {
	if len(needle) == 0 {
		return true
	}
	if len(haystack) < len(needle) {
		return false
	}
	for i := 0; i <= len(haystack)-len(needle); i++ {
		if haystack[i:i+len(needle)] == needle {
			return true
		}
	}
	return false
}
