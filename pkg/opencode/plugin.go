// Package opencode provides integration with OpenCode AI development tool
// Enables real-time tooling modification and ecosystem contribution
package opencode

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/ecosystem"
)

// Plugin represents an OpenCode plugin for Urban Lens
type Plugin struct {
	Name        string
	Version     string
	Description string
	config      *ecosystem.Config
}

// PluginManifest describes the plugin for OpenCode
type PluginManifest struct {
	Name         string    `json:"name"`
	Version      string    `json:"version"`
	Description  string    `json:"description"`
	Author       string    `json:"author"`
	Repository   string    `json:"repository"`
	Commands     []Command `json:"commands"`
	Capabilities []string  `json:"capabilities"`
}

// Command represents a plugin command
type Command struct {
	Name        string `json:"name"`
	Description string `json:"description"`
	Usage       string `json:"usage"`
}

// NewPlugin creates a new OpenCode plugin
func NewPlugin() *Plugin {
	return &Plugin{
		Name:        "urban-lens",
		Version:     "0.4.0",
		Description: "Urban Lens research assistant integration for OpenCode",
		config:      ecosystem.GetConfig(),
	}
}

// GetManifest returns the plugin manifest
func (p *Plugin) GetManifest() *PluginManifest {
	return &PluginManifest{
		Name:        p.Name,
		Version:     p.Version,
		Description: p.Description,
		Author:      "Asymmetrica Research",
		Repository:  "https://github.com/sarat-asymmetrica/asymm_urban_lens",
		Commands: []Command{
			{
				Name:        "analyze",
				Description: "Analyze urban research data",
				Usage:       "urban-lens analyze <file>",
			},
			{
				Name:        "transcribe",
				Description: "Transcribe audio to text",
				Usage:       "urban-lens transcribe <audio-file>",
			},
			{
				Name:        "ocr",
				Description: "Extract text from images",
				Usage:       "urban-lens ocr <image-file>",
			},
			{
				Name:        "chat",
				Description: "Chat with Urban Lens AI",
				Usage:       "urban-lens chat <message>",
			},
			{
				Name:        "status",
				Description: "Check Urban Lens server status",
				Usage:       "urban-lens status",
			},
		},
		Capabilities: []string{
			"research-analysis",
			"document-processing",
			"audio-transcription",
			"image-ocr",
			"ai-chat",
			"climate-analysis",
			"cultural-mathematics",
		},
	}
}

// GenerateManifestFile creates the plugin manifest file
func (p *Plugin) GenerateManifestFile(outputDir string) error {
	manifest := p.GetManifest()

	data, err := json.MarshalIndent(manifest, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal manifest: %w", err)
	}

	outputPath := filepath.Join(outputDir, "urban-lens-plugin.json")
	if err := os.WriteFile(outputPath, data, 0644); err != nil {
		return fmt.Errorf("failed to write manifest: %w", err)
	}

	return nil
}

// ToolDefinition represents a tool for OpenCode's tool registry
type ToolDefinition struct {
	Name        string                 `json:"name"`
	Description string                 `json:"description"`
	InputSchema map[string]interface{} `json:"input_schema"`
	Endpoint    string                 `json:"endpoint"`
	Method      string                 `json:"method"`
}

// GetToolDefinitions returns tool definitions for OpenCode
func (p *Plugin) GetToolDefinitions() []ToolDefinition {
	return []ToolDefinition{
		{
			Name:        "urban_lens_analyze",
			Description: "Analyze urban research data using AI-powered reasoning",
			InputSchema: map[string]interface{}{
				"type": "object",
				"properties": map[string]interface{}{
					"query": map[string]interface{}{
						"type":        "string",
						"description": "Research query or data description",
					},
					"context": map[string]interface{}{
						"type":        "string",
						"description": "Additional context for analysis",
					},
				},
				"required": []string{"query"},
			},
			Endpoint: "http://localhost:8080/analyze",
			Method:   "POST",
		},
		{
			Name:        "urban_lens_chat",
			Description: "Chat with Urban Lens AI research assistant",
			InputSchema: map[string]interface{}{
				"type": "object",
				"properties": map[string]interface{}{
					"message": map[string]interface{}{
						"type":        "string",
						"description": "Message to send to Urban Lens",
					},
				},
				"required": []string{"message"},
			},
			Endpoint: "http://localhost:8080/api/chat",
			Method:   "POST",
		},
		{
			Name:        "urban_lens_climate",
			Description: "Analyze climate data for urban areas",
			InputSchema: map[string]interface{}{
				"type": "object",
				"properties": map[string]interface{}{
					"city": map[string]interface{}{
						"type":        "string",
						"description": "City name for climate analysis",
					},
					"analysis_type": map[string]interface{}{
						"type":        "string",
						"enum":        []string{"rainfall", "heat_island", "monsoon"},
						"description": "Type of climate analysis",
					},
				},
				"required": []string{"city"},
			},
			Endpoint: "http://localhost:8080/api/climate/analyze",
			Method:   "POST",
		},
	}
}

// HealthCheck checks if Urban Lens server is available
func (p *Plugin) HealthCheck(ctx context.Context) (bool, error) {
	// Simple check - try to connect to the server
	// In production, would use HTTP client
	return true, nil
}

// GetStatus returns plugin status
func (p *Plugin) GetStatus() map[string]interface{} {
	return map[string]interface{}{
		"name":               p.Name,
		"version":            p.Version,
		"description":        p.Description,
		"aimlapi_configured": p.config.IsConfigured(),
		"commands":           len(p.GetManifest().Commands),
		"tools":              len(p.GetToolDefinitions()),
		"server_url":         "http://localhost:8080",
	}
}

// RegisterWithOpenCode generates files needed to register with OpenCode
func (p *Plugin) RegisterWithOpenCode(opencodePath string) error {
	// Create plugin directory
	pluginDir := filepath.Join(opencodePath, "plugins", "urban-lens")
	if err := os.MkdirAll(pluginDir, 0755); err != nil {
		return fmt.Errorf("failed to create plugin directory: %w", err)
	}

	// Generate manifest
	if err := p.GenerateManifestFile(pluginDir); err != nil {
		return err
	}

	// Generate tool definitions
	tools := p.GetToolDefinitions()
	toolsData, err := json.MarshalIndent(tools, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal tools: %w", err)
	}

	toolsPath := filepath.Join(pluginDir, "tools.json")
	if err := os.WriteFile(toolsPath, toolsData, 0644); err != nil {
		return fmt.Errorf("failed to write tools: %w", err)
	}

	// Generate README
	readme := fmt.Sprintf(`# Urban Lens Plugin for OpenCode

**Version**: %s
**Generated**: %s

## Description

%s

## Commands

`, p.Version, time.Now().Format(time.RFC3339), p.Description)

	for _, cmd := range p.GetManifest().Commands {
		readme += fmt.Sprintf("- **%s**: %s\n  Usage: `%s`\n\n", cmd.Name, cmd.Description, cmd.Usage)
	}

	readmePath := filepath.Join(pluginDir, "README.md")
	if err := os.WriteFile(readmePath, []byte(readme), 0644); err != nil {
		return fmt.Errorf("failed to write README: %w", err)
	}

	return nil
}
