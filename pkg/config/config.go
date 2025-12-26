// Package config provides configuration management for ASYA server
package config

import (
	"os"
	"strconv"
	"strings"
)

// ═══════════════════════════════════════════════════════════════════════════
// CONFIGURATION
// ═══════════════════════════════════════════════════════════════════════════

// Config holds all server configuration
type Config struct {
	Port           string
	AIMLAPIKey     string
	AllowedOrigins []string
	Debug          bool
	MaxSessions    int
	SessionTimeout int // in minutes
	RateLimit      RateLimitConfig
}

// RateLimitConfig holds rate limiting configuration
type RateLimitConfig struct {
	Enabled       bool
	RequestsLimit int // Max requests per window
	WindowMinutes int // Time window in minutes
}

// LoadFromEnv loads configuration from environment variables
func LoadFromEnv() Config {
	return Config{
		Port:           getEnv("PORT", "8080"),
		AIMLAPIKey:     getEnv("AIMLAPI_KEY", ""),
		AllowedOrigins: getAllowedOrigins(),
		Debug:          getEnvBool("DEBUG", false),
		MaxSessions:    getEnvInt("MAX_SESSIONS", 1000),
		SessionTimeout: getEnvInt("SESSION_TIMEOUT", 60), // 60 minutes default
		RateLimit: RateLimitConfig{
			Enabled:       getEnvBool("RATE_LIMIT_ENABLED", true),
			RequestsLimit: getEnvInt("RATE_LIMIT_REQUESTS", 100),
			WindowMinutes: getEnvInt("RATE_LIMIT_WINDOW", 1),
		},
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════════════════════════

func getEnv(key, defaultValue string) string {
	value := os.Getenv(key)
	if value == "" {
		return defaultValue
	}
	return value
}

func getEnvBool(key string, defaultValue bool) bool {
	value := os.Getenv(key)
	if value == "" {
		return defaultValue
	}
	parsed, err := strconv.ParseBool(value)
	if err != nil {
		return defaultValue
	}
	return parsed
}

func getEnvInt(key string, defaultValue int) int {
	value := os.Getenv(key)
	if value == "" {
		return defaultValue
	}
	parsed, err := strconv.Atoi(value)
	if err != nil {
		return defaultValue
	}
	return parsed
}

func getAllowedOrigins() []string {
	origins := os.Getenv("ALLOWED_ORIGINS")
	if origins == "" {
		// Default allowed origins for development
		return []string{
			"http://localhost:5173",
			"http://localhost:3000",
			"http://localhost:8080",
		}
	}

	// Split by comma
	parts := strings.Split(origins, ",")
	result := []string{}
	for _, part := range parts {
		trimmed := strings.TrimSpace(part)
		if trimmed != "" {
			result = append(result, trimmed)
		}
	}
	return result
}

// Validate checks if configuration is valid
func (c *Config) Validate() error {
	// Add validation logic here
	if c.Port == "" {
		c.Port = "8080"
	}
	if !strings.HasPrefix(c.Port, ":") {
		c.Port = ":" + c.Port
	}
	return nil
}

// IsAIEnabled returns true if AI is configured
func (c *Config) IsAIEnabled() bool {
	return c.AIMLAPIKey != ""
}
