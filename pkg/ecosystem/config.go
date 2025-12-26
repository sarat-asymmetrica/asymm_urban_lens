// Package ecosystem provides shared configuration for Asymmetrica tools
// Enables one AIMLAPI key to work across Urban Lens, OpenCode, Asymmetrica.Runtime
package ecosystem

import (
	"os"
	"sync"
)

// Config holds ecosystem-wide configuration
type Config struct {
	AIMLAPIKey     string
	AIMLAPIBaseURL string
	Environment    string // "development", "production"
	Debug          bool
}

var (
	globalConfig *Config
	configOnce   sync.Once
)

// GetConfig returns the global ecosystem configuration
// Loads from environment variables on first call
func GetConfig() *Config {
	configOnce.Do(func() {
		globalConfig = loadConfig()
	})
	return globalConfig
}

// loadConfig loads configuration from environment
func loadConfig() *Config {
	// Try multiple environment variable names for AIMLAPI key
	// This ensures compatibility across all Asymmetrica tools
	apiKey := firstNonEmpty(
		os.Getenv("AIMLAPI_KEY"),
		os.Getenv("ASYMM_AIML_API_KEY"),
		os.Getenv("OPENCODE_AIMLAPI_KEY"),
	)

	baseURL := os.Getenv("AIMLAPI_BASE_URL")
	if baseURL == "" {
		baseURL = "https://api.aimlapi.com/v1"
	}

	env := os.Getenv("ASYMM_ENV")
	if env == "" {
		env = "development"
	}

	return &Config{
		AIMLAPIKey:     apiKey,
		AIMLAPIBaseURL: baseURL,
		Environment:    env,
		Debug:          os.Getenv("ASYMM_DEBUG") == "true",
	}
}

// IsConfigured returns true if AIMLAPI is configured
func (c *Config) IsConfigured() bool {
	return c.AIMLAPIKey != ""
}

// IsProduction returns true if running in production
func (c *Config) IsProduction() bool {
	return c.Environment == "production"
}

// firstNonEmpty returns the first non-empty string
func firstNonEmpty(values ...string) string {
	for _, v := range values {
		if v != "" {
			return v
		}
	}
	return ""
}

// ToolInfo represents information about an Asymmetrica tool
type ToolInfo struct {
	Name        string `json:"name"`
	Version     string `json:"version"`
	Description string `json:"description"`
	Endpoint    string `json:"endpoint,omitempty"`
}

// EcosystemStatus represents the status of the Asymmetrica ecosystem
type EcosystemStatus struct {
	AIMLAPIConfigured bool       `json:"aimlapi_configured"`
	Environment       string     `json:"environment"`
	Tools             []ToolInfo `json:"tools"`
}

// GetEcosystemStatus returns the current ecosystem status
func GetEcosystemStatus() *EcosystemStatus {
	cfg := GetConfig()
	return &EcosystemStatus{
		AIMLAPIConfigured: cfg.IsConfigured(),
		Environment:       cfg.Environment,
		Tools: []ToolInfo{
			{
				Name:        "Urban Lens",
				Version:     "0.4.0",
				Description: "AI-powered urban research assistant",
				Endpoint:    "http://localhost:8080",
			},
			{
				Name:        "OpenCode",
				Version:     "1.0.0",
				Description: "AI-powered development tool",
				Endpoint:    "CLI",
			},
			{
				Name:        "Asymmetrica.Runtime",
				Version:     "1.0.0",
				Description: "Microsoft Office intelligence platform",
				Endpoint:    "http://localhost:5000",
			},
		},
	}
}

// SharedModels returns models available across the ecosystem
func SharedModels() []string {
	return []string{
		"claude-3-5-sonnet-20241022",
		"claude-3-5-haiku-20241022",
		"gpt-4o",
		"gpt-4o-mini",
		"gpt-4-turbo",
		"mistral-large-latest",
		"mistral-medium-latest",
		"llama-3.1-70b-instruct",
		"llama-3.1-8b-instruct",
		"gemini-1.5-pro",
		"gemini-1.5-flash",
	}
}
