// Package aimlapi - Model configurations and registry
package aimlapi

// ═══════════════════════════════════════════════════════════════════════════
// TYPES
// ═══════════════════════════════════════════════════════════════════════════

// Capability flags (bitmask for model capabilities)
type Capability int

const (
	TEXT      Capability = 1 << 0
	VISION    Capability = 1 << 1
	CODE      Capability = 1 << 2
	REASONING Capability = 1 << 3
	SPEECH    Capability = 1 << 4
	IMAGE_GEN Capability = 1 << 5
	CREATIVE  Capability = 1 << 6
	MATH      Capability = 1 << 7
)

// ModelConfig represents a model configuration
type ModelConfig struct {
	ModelID        string     `json:"model_id"`
	Name           string     `json:"name"`
	Provider       string     `json:"provider"` // anthropic, openai, google, meta, mistral, etc.
	MaxTokens      int        `json:"max_tokens"`
	Temperature    float64    `json:"temperature"`
	Capabilities   Capability `json:"capabilities"`
	ContextSize    int        `json:"context_size"`
	SpeedRating    float64    `json:"speed_rating"`    // 0-10
	QualityRating  float64    `json:"quality_rating"`  // 0-10
	CostPerMInput  float64    `json:"cost_per_m_input"`  // per 1M tokens
	CostPerMOutput float64    `json:"cost_per_m_output"` // per 1M tokens
	UseCases       []string   `json:"use_cases"`
	Notes          string     `json:"notes"`
}

// TaskType defines the type of task for intelligent routing
type TaskType string

const (
	TASK_CHAT      TaskType = "chat"
	TASK_CODE      TaskType = "code"
	TASK_VISION    TaskType = "vision"
	TASK_REASONING TaskType = "reasoning"
	TASK_CREATIVE  TaskType = "creative"
	TASK_MATH      TaskType = "math"
	TASK_SPEECH    TaskType = "speech"
	TASK_IMAGE_GEN TaskType = "image_gen"
)

// ═══════════════════════════════════════════════════════════════════════════
// AVAILABLE MODELS
// ═══════════════════════════════════════════════════════════════════════════

var AvailableModels = map[string]ModelConfig{
	// ─────────────────────────────────────────────────────────────────────────
	// ANTHROPIC (Claude) - Best for complex reasoning, coding, research
	// ─────────────────────────────────────────────────────────────────────────
	"claude-opus": {
		ModelID:        "claude-3-5-sonnet-20241022",
		Name:           "Claude 3.5 Sonnet",
		Provider:       "anthropic",
		MaxTokens:      8192,
		Temperature:    0.7,
		Capabilities:   TEXT | VISION | CODE | REASONING | MATH | CREATIVE,
		ContextSize:    200000,
		SpeedRating:    8.0,
		QualityRating:  9.5,
		CostPerMInput:  3.00,
		CostPerMOutput: 15.00,
		UseCases:       []string{"research", "complex analysis", "creative writing", "advanced coding"},
		Notes:          "Best for nuanced, sophisticated tasks. Excellent code quality.",
	},
	"claude-sonnet": {
		ModelID:        "claude-3-5-sonnet-20241022",
		Name:           "Claude 3.5 Sonnet",
		Provider:       "anthropic",
		MaxTokens:      8192,
		Temperature:    0.7,
		Capabilities:   TEXT | VISION | CODE | REASONING | MATH | CREATIVE,
		ContextSize:    200000,
		SpeedRating:    8.5,
		QualityRating:  9.0,
		CostPerMInput:  3.00,
		CostPerMOutput: 15.00,
		UseCases:       []string{"balanced tasks", "coding", "analysis"},
		Notes:          "Best balance of speed and intelligence",
	},
	"claude-haiku": {
		ModelID:        "claude-3-haiku-20240307",
		Name:           "Claude 3 Haiku",
		Provider:       "anthropic",
		MaxTokens:      4096,
		Temperature:    0.7,
		Capabilities:   TEXT | CODE | REASONING,
		ContextSize:    200000,
		SpeedRating:    9.5,
		QualityRating:  7.5,
		CostPerMInput:  0.25,
		CostPerMOutput: 1.25,
		UseCases:       []string{"fast responses", "simple tasks", "high volume"},
		Notes:          "Fastest Claude, cost-effective for simple tasks",
	},

	// ─────────────────────────────────────────────────────────────────────────
	// OPENAI (GPT) - General purpose, vision, structured outputs
	// ─────────────────────────────────────────────────────────────────────────
	"gpt-4o": {
		ModelID:        "gpt-4o",
		Name:           "GPT-4o",
		Provider:       "openai",
		MaxTokens:      16384,
		Temperature:    0.7,
		Capabilities:   TEXT | VISION | CODE | REASONING | MATH | CREATIVE,
		ContextSize:    128000,
		SpeedRating:    8.0,
		QualityRating:  9.0,
		CostPerMInput:  2.50,
		CostPerMOutput: 10.00,
		UseCases:       []string{"multimodal", "vision", "general tasks"},
		Notes:          "OpenAI's flagship omni-model. Excellent vision.",
	},
	"gpt-4o-mini": {
		ModelID:        "gpt-4o-mini",
		Name:           "GPT-4o Mini",
		Provider:       "openai",
		MaxTokens:      16384,
		Temperature:    0.7,
		Capabilities:   TEXT | VISION | CODE | REASONING | MATH,
		ContextSize:    128000,
		SpeedRating:    9.5,
		QualityRating:  8.5,
		CostPerMInput:  0.15,
		CostPerMOutput: 0.60,
		UseCases:       []string{"cost-effective", "research", "analysis", "coding"},
		Notes:          "Best value. Excellent for most tasks.",
	},
	"gpt-4-turbo": {
		ModelID:        "gpt-4-turbo-2024-04-09",
		Name:           "GPT-4 Turbo",
		Provider:       "openai",
		MaxTokens:      4096,
		Temperature:    0.7,
		Capabilities:   TEXT | VISION | CODE | REASONING | MATH,
		ContextSize:    128000,
		SpeedRating:    7.5,
		QualityRating:  8.8,
		CostPerMInput:  10.00,
		CostPerMOutput: 30.00,
		UseCases:       []string{"complex tasks", "vision"},
		Notes:          "Previous flagship. Still very capable.",
	},

	// ─────────────────────────────────────────────────────────────────────────
	// GOOGLE (Gemini) - Long context, multimodal
	// ─────────────────────────────────────────────────────────────────────────
	"gemini": {
		ModelID:        "gemini-1.5-pro",
		Name:           "Gemini 1.5 Pro",
		Provider:       "google",
		MaxTokens:      8192,
		Temperature:    0.7,
		Capabilities:   TEXT | VISION | CODE | REASONING | MATH,
		ContextSize:    2000000,
		SpeedRating:    7.5,
		QualityRating:  8.5,
		CostPerMInput:  1.25,
		CostPerMOutput: 5.00,
		UseCases:       []string{"long documents", "multimodal", "research"},
		Notes:          "2M context! Best for extremely long documents.",
	},
	"gemini-flash": {
		ModelID:        "gemini-1.5-flash",
		Name:           "Gemini 1.5 Flash",
		Provider:       "google",
		MaxTokens:      8192,
		Temperature:    0.7,
		Capabilities:   TEXT | VISION | CODE | REASONING,
		ContextSize:    1000000,
		SpeedRating:    9.5,
		QualityRating:  8.0,
		CostPerMInput:  0.075,
		CostPerMOutput: 0.30,
		UseCases:       []string{"fast responses", "long context", "multimodal"},
		Notes:          "1M context, ultra-fast, very cheap",
	},

	// ─────────────────────────────────────────────────────────────────────────
	// META (Llama) - Open source, cost-effective
	// ─────────────────────────────────────────────────────────────────────────
	"llama-70b": {
		ModelID:        "llama-3.1-70b",
		Name:           "Llama 3.1 70B",
		Provider:       "meta",
		MaxTokens:      8192,
		Temperature:    0.7,
		Capabilities:   TEXT | CODE | REASONING | MATH,
		ContextSize:    128000,
		SpeedRating:    8.5,
		QualityRating:  8.0,
		CostPerMInput:  0.59,
		CostPerMOutput: 0.79,
		UseCases:       []string{"open source", "general tasks", "coding"},
		Notes:          "Open-source flagship. Very capable.",
	},
	"llama-405b": {
		ModelID:        "llama-3.1-405b",
		Name:           "Llama 3.1 405B",
		Provider:       "meta",
		MaxTokens:      8192,
		Temperature:    0.7,
		Capabilities:   TEXT | CODE | REASONING | MATH | CREATIVE,
		ContextSize:    128000,
		SpeedRating:    6.0,
		QualityRating:  9.0,
		CostPerMInput:  2.70,
		CostPerMOutput: 2.70,
		UseCases:       []string{"complex reasoning", "research", "open source"},
		Notes:          "Largest open-source model. Competes with GPT-4.",
	},

	// ─────────────────────────────────────────────────────────────────────────
	// MISTRAL - European, efficient, cost-effective
	// ─────────────────────────────────────────────────────────────────────────
	"mistral-large": {
		ModelID:        "mistral-large-latest",
		Name:           "Mistral Large",
		Provider:       "mistral",
		MaxTokens:      8192,
		Temperature:    0.7,
		Capabilities:   TEXT | CODE | REASONING | MATH,
		ContextSize:    128000,
		SpeedRating:    8.5,
		QualityRating:  8.5,
		CostPerMInput:  2.00,
		CostPerMOutput: 6.00,
		UseCases:       []string{"european compliance", "coding", "reasoning"},
		Notes:          "European alternative to GPT-4",
	},
	"mistral-ocr": {
		ModelID:        "mistral-ocr-latest",
		Name:           "Mistral OCR",
		Provider:       "mistral",
		MaxTokens:      4096,
		Temperature:    0.3,
		Capabilities:   TEXT | VISION,
		ContextSize:    128000,
		SpeedRating:    9.0,
		QualityRating:  8.5,
		CostPerMInput:  0.20,
		CostPerMOutput: 0.60,
		UseCases:       []string{"ocr", "document extraction", "vision"},
		Notes:          "Optimized for OCR and document processing",
	},

	// ─────────────────────────────────────────────────────────────────────────
	// DEEPSEEK - Ultra cost-effective Chinese model
	// ─────────────────────────────────────────────────────────────────────────
	"deepseek-chat": {
		ModelID:        "deepseek-chat",
		Name:           "DeepSeek Chat",
		Provider:       "deepseek",
		MaxTokens:      8192,
		Temperature:    0.7,
		Capabilities:   TEXT | CODE | REASONING | MATH,
		ContextSize:    128000,
		SpeedRating:    8.5,
		QualityRating:  8.0,
		CostPerMInput:  0.14,
		CostPerMOutput: 0.28,
		UseCases:       []string{"ultra cost-effective", "high volume", "coding"},
		Notes:          "Cheapest capable model. Excellent for high-volume tasks.",
	},

	// ─────────────────────────────────────────────────────────────────────────
	// PERPLEXITY - Online search integration
	// ─────────────────────────────────────────────────────────────────────────
	"perplexity": {
		ModelID:        "llama-3.1-sonar-large-128k-online",
		Name:           "Perplexity Sonar Large",
		Provider:       "perplexity",
		MaxTokens:      8192,
		Temperature:    0.7,
		Capabilities:   TEXT | REASONING,
		ContextSize:    128000,
		SpeedRating:    7.0,
		QualityRating:  8.5,
		CostPerMInput:  1.00,
		CostPerMOutput: 1.00,
		UseCases:       []string{"online search", "current events", "research"},
		Notes:          "Has access to live internet search. Best for current info.",
	},

	// ─────────────────────────────────────────────────────────────────────────
	// IMAGE GENERATION - FLUX, Stable Diffusion
	// ─────────────────────────────────────────────────────────────────────────
	"flux-image": {
		ModelID:        "flux/dev",
		Name:           "FLUX.1 Dev",
		Provider:       "flux",
		MaxTokens:      0,
		Temperature:    0,
		Capabilities:   IMAGE_GEN,
		ContextSize:    0,
		SpeedRating:    7.0,
		QualityRating:  9.0,
		CostPerMInput:  0.025, // per image
		CostPerMOutput: 0.025,
		UseCases:       []string{"image generation", "art", "visualization"},
		Notes:          "High-quality image generation. Best for realistic images.",
	},
	"flux-pro": {
		ModelID:        "flux-pro",
		Name:           "FLUX Pro",
		Provider:       "flux",
		MaxTokens:      0,
		Temperature:    0,
		Capabilities:   IMAGE_GEN,
		ContextSize:    0,
		SpeedRating:    6.0,
		QualityRating:  9.5,
		CostPerMInput:  0.055, // per image
		CostPerMOutput: 0.055,
		UseCases:       []string{"professional images", "high quality", "commercial"},
		Notes:          "Professional-grade image generation",
	},
	"stable-diffusion": {
		ModelID:        "stable-diffusion-xl-base-1.0",
		Name:           "Stable Diffusion XL",
		Provider:       "stability",
		MaxTokens:      0,
		Temperature:    0,
		Capabilities:   IMAGE_GEN,
		ContextSize:    0,
		SpeedRating:    8.0,
		QualityRating:  8.0,
		CostPerMInput:  0.008, // per image
		CostPerMOutput: 0.008,
		UseCases:       []string{"image generation", "art", "fast generation"},
		Notes:          "Fast, cost-effective image generation",
	},
}

// buildModelRegistry creates the model registry map
func buildModelRegistry() map[string]ModelConfig {
	registry := make(map[string]ModelConfig)
	for id, model := range AvailableModels {
		model.ModelID = id // Ensure ID is set
		registry[id] = model
	}
	return registry
}

// SelectModelForTask intelligently selects best model for a task type
func SelectModelForTask(task TaskType) ModelConfig {
	switch task {
	case TASK_CHAT:
		return AvailableModels["gpt-4o-mini"] // Best value for chat
	case TASK_CODE:
		return AvailableModels["claude-sonnet"] // Best for coding
	case TASK_VISION:
		return AvailableModels["gpt-4o"] // Best vision
	case TASK_REASONING:
		return AvailableModels["claude-opus"] // Best reasoning
	case TASK_CREATIVE:
		return AvailableModels["claude-opus"] // Best creative writing
	case TASK_MATH:
		return AvailableModels["gpt-4o"] // Strong math capabilities
	case TASK_IMAGE_GEN:
		return AvailableModels["flux-image"] // Best image generation
	default:
		return AvailableModels["gpt-4o-mini"] // Safe default
	}
}

// GetRequiredCapabilities returns required capabilities for a task type
func GetRequiredCapabilities(taskType TaskType) Capability {
	switch taskType {
	case TASK_CHAT:
		return TEXT
	case TASK_CODE:
		return TEXT | CODE
	case TASK_VISION:
		return TEXT | VISION
	case TASK_REASONING:
		return TEXT | REASONING
	case TASK_CREATIVE:
		return TEXT | CREATIVE
	case TASK_MATH:
		return TEXT | MATH
	case TASK_SPEECH:
		return SPEECH
	case TASK_IMAGE_GEN:
		return IMAGE_GEN
	default:
		return TEXT
	}
}
