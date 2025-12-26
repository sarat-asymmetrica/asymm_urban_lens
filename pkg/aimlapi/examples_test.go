// Package aimlapi - Example usage patterns
package aimlapi_test

import (
	"context"
	"fmt"
	"log"

	"github.com/asymmetrica/urbanlens/pkg/aimlapi"
)

// Example_basicChat demonstrates basic chat usage
func Example_basicChat() {
	client := aimlapi.NewClient("") // Uses AIMLAPI_KEY env var
	ctx := context.Background()

	response, err := client.SimpleChat(ctx, "What is urban planning?")
	if err != nil {
		log.Fatal(err)
	}

	fmt.Println(response)
}

// Example_systemPrompt demonstrates using system prompts
func Example_systemPrompt() {
	client := aimlapi.NewClient("")
	ctx := context.Background()

	systemPrompt := "You are an urban research assistant for IIHS."
	userMessage := "Explain TOD (Transit-Oriented Development)"

	response, err := client.SystemChat(ctx, systemPrompt, userMessage)
	if err != nil {
		log.Fatal(err)
	}

	fmt.Println(response)
}

// Example_conversation demonstrates multi-turn conversation
func Example_conversation() {
	client := aimlapi.NewClient("")
	ctx := context.Background()

	// Build conversation
	conv := aimlapi.NewConversation()
	conv.AddSystem("You are a helpful urban planning expert.")
	conv.AddUser("What is smart city planning?")
	conv.AddAssistant("Smart city planning integrates technology...")
	conv.AddUser("Give examples from India")

	// Send conversation
	req := conv.ToChatRequest("gpt-4o-mini")
	resp, err := client.Chat(ctx, req)
	if err != nil {
		log.Fatal(err)
	}

	fmt.Println(resp.Choices[0].Message.Content)
}

// Example_intelligentSelection demonstrates three-regime selection
func Example_intelligentSelection() {
	client := aimlapi.NewClient("")

	// REGIME 1: EXPLORATION - Random selection
	client.SetRegime(1)
	constraints := aimlapi.SelectionConstraints{
		TaskType:   aimlapi.TASK_CODE,
		MinQuality: 8.0,
	}
	model, _ := client.SelectModel(constraints)
	fmt.Printf("Exploration selected: %s\n", model.Name)

	// REGIME 2: OPTIMIZATION - Best quality/cost
	client.SetRegime(2)
	model, _ = client.SelectModel(constraints)
	fmt.Printf("Optimization selected: %s\n", model.Name)

	// REGIME 3: STABILIZATION - Cached selection
	client.SetRegime(3)
	model, _ = client.SelectModel(constraints)
	fmt.Printf("Stabilization selected: %s\n", model.Name)
}

// Example_streaming demonstrates streaming chat
func Example_streaming() {
	client := aimlapi.NewClient("")
	ctx := context.Background()

	req := aimlapi.ChatRequest{
		Messages: []aimlapi.Message{
			{Role: "user", Content: "Explain climate change in 3 sentences"},
		},
	}

	// Stream response
	chunks, err := client.ChatStream(ctx, req)
	if err != nil {
		log.Fatal(err)
	}

	for chunk := range chunks {
		if chunk.Error != nil {
			log.Fatal(chunk.Error)
		}
		if !chunk.Done {
			fmt.Print(chunk.Content)
		}
	}
	fmt.Println()
}

// Example_streamingCallback demonstrates streaming with callback
func Example_streamingCallback() {
	client := aimlapi.NewClient("")
	ctx := context.Background()

	req := aimlapi.ChatRequest{
		Messages: []aimlapi.Message{
			{Role: "user", Content: "Count from 1 to 5"},
		},
	}

	// Stream with callback
	err := client.StreamChat(ctx, req, func(chunk aimlapi.StreamChunk) {
		if !chunk.Done {
			fmt.Print(chunk.Content)
		}
	})

	if err != nil {
		log.Fatal(err)
	}
	fmt.Println()
}

// Example_imageGeneration demonstrates image generation
func Example_imageGeneration() {
	client := aimlapi.NewClient("")
	ctx := context.Background()

	// Simple image generation
	url, err := client.GenerateImage(ctx, "A futuristic smart city at night")
	if err != nil {
		log.Fatal(err)
	}

	fmt.Println("Image URL:", url)
}

// Example_diagramGeneration demonstrates diagram creation
func Example_diagramGeneration() {
	client := aimlapi.NewClient("")
	ctx := context.Background()

	// Generate technical diagram
	diagram, err := client.GenerateDiagram(ctx, "Urban planning workflow from survey to implementation")
	if err != nil {
		log.Fatal(err)
	}

	fmt.Printf("Diagram: %s (%dx%d)\n", diagram.URL, diagram.Width, diagram.Height)
}

// Example_chartVisualization demonstrates chart generation
func Example_chartVisualization() {
	client := aimlapi.NewClient("")
	ctx := context.Background()

	chart, err := client.GenerateChartVisualization(ctx,
		"Urban population growth 2000-2024, showing exponential increase",
		"line chart")
	if err != nil {
		log.Fatal(err)
	}

	fmt.Println("Chart URL:", chart.URL)
}

// Example_fallbackRouting demonstrates router with fallback chains
func Example_fallbackRouting() {
	client := aimlapi.NewClient("")
	router := aimlapi.NewRouter(client)
	ctx := context.Background()

	req := aimlapi.ChatRequest{
		Messages: []aimlapi.Message{
			{Role: "user", Content: "Write a Python function to sort a list"},
		},
	}

	// Automatically tries fallback chain if primary fails
	resp, err := router.RouteWithFallback(ctx, req)
	if err != nil {
		log.Fatal(err)
	}

	fmt.Println(resp.Choices[0].Message.Content)
}

// Example_customFallbackChain demonstrates custom fallback chains
func Example_customFallbackChain() {
	client := aimlapi.NewClient("")
	router := aimlapi.NewRouter(client)

	// Set custom fallback chain for code tasks
	router.SetFallbackChain(aimlapi.TASK_CODE, []string{
		"claude-sonnet", // First choice
		"gpt-4o",        // Second choice
		"llama-70b",     // Last resort
	})

	ctx := context.Background()
	req := aimlapi.ChatRequest{
		Messages: []aimlapi.Message{
			{Role: "user", Content: "Debug this code"},
		},
	}

	resp, err := router.RouteWithFallback(ctx, req)
	if err != nil {
		log.Fatal(err)
	}

	fmt.Println(resp.Choices[0].Message.Content)
}

// Example_batchProcessing demonstrates Williams batching
func Example_batchProcessing() {
	client := aimlapi.NewClient("")
	ctx := context.Background()

	// Create multiple requests
	requests := []aimlapi.ChatRequest{
		{Messages: []aimlapi.Message{{Role: "user", Content: "What is TOD?"}}},
		{Messages: []aimlapi.Message{{Role: "user", Content: "What is smart city?"}}},
		{Messages: []aimlapi.Message{{Role: "user", Content: "What is urban sprawl?"}}},
	}

	// Process with Williams batching (O(√n × log₂n))
	batchResp, err := client.BatchChat(ctx, requests)
	if err != nil {
		log.Fatal(err)
	}

	for i, resp := range batchResp.Responses {
		if batchResp.Errors[i] != nil {
			fmt.Printf("Request %d failed: %v\n", i, batchResp.Errors[i])
			continue
		}
		fmt.Printf("Answer %d: %s\n", i+1, resp.Choices[0].Message.Content)
	}
}

// Example_costEstimation demonstrates cost calculation
func Example_costEstimation() {
	client := aimlapi.NewClient("")

	model, _ := client.GetModel("gpt-4o")

	req := aimlapi.ChatRequest{
		Model: "gpt-4o",
		Messages: []aimlapi.Message{
			{Role: "user", Content: "Explain quantum computing"},
		},
		MaxTokens: 1000,
	}

	estimatedCost := aimlapi.EstimateRequestCost(model, req)
	fmt.Printf("Estimated cost: $%.4f\n", estimatedCost)
}

// Example_modelComparison demonstrates comparing models
func Example_modelComparison() {
	client := aimlapi.NewClient("")
	models := client.ListModels()

	fmt.Println("Available Models:")
	for _, model := range models {
		if model.Capabilities&aimlapi.CODE != 0 {
			avgCost := (model.CostPerMInput + model.CostPerMOutput) / 2.0
			fmt.Printf("- %s: Quality %.1f, Speed %.1f, Cost $%.2f/M\n",
				model.Name, model.QualityRating, model.SpeedRating, avgCost)
		}
	}
}

// Example_advancedSelection demonstrates constraint-based selection
func Example_advancedSelection() {
	client := aimlapi.NewClient("")

	// Select cheapest model with quality > 8.0
	constraints := aimlapi.SelectionConstraints{
		TaskType:    aimlapi.TASK_REASONING,
		MinQuality:  8.0,
		MaxCostPerM: 1.0, // Max $1 per million tokens
		MinSpeed:    7.0,
	}

	model, err := client.SelectModel(constraints)
	if err != nil {
		log.Fatal(err)
	}

	fmt.Printf("Selected: %s (Quality: %.1f, Cost: $%.2f/M)\n",
		model.Name, model.QualityRating,
		(model.CostPerMInput+model.CostPerMOutput)/2.0)
}

// Example_contextManagement demonstrates context window handling
func Example_contextManagement() {
	messages := []aimlapi.Message{
		{Role: "system", Content: "You are a helpful assistant"},
		{Role: "user", Content: "Long message 1..."},
		{Role: "assistant", Content: "Response 1..."},
		{Role: "user", Content: "Long message 2..."},
		{Role: "assistant", Content: "Response 2..."},
		{Role: "user", Content: "Long message 3..."},
	}

	// Truncate to fit 100K context window
	truncated := aimlapi.TruncateToContext(messages, 100000)

	fmt.Printf("Original messages: %d\n", len(messages))
	fmt.Printf("Truncated messages: %d\n", len(truncated))
	fmt.Printf("System message preserved: %v\n", truncated[0].Role == "system")
}

// Example_errorHandling demonstrates error handling patterns
func Example_errorHandling() {
	client := aimlapi.NewClient("invalid-key")
	ctx := context.Background()

	resp, err := client.SimpleChat(ctx, "Hello")
	if err != nil {
		// Check for specific error types
		if apiErr, ok := err.(*aimlapi.APIError); ok {
			fmt.Printf("API Error: %s (code: %s)\n", apiErr.Message, apiErr.Code)
		} else {
			fmt.Printf("Error: %v\n", err)
		}
		return
	}

	fmt.Println(resp)
}

// Example_healthCheck demonstrates API health verification
func Example_healthCheck() {
	client := aimlapi.NewClient("")
	ctx := context.Background()

	if err := client.HealthCheck(ctx); err != nil {
		log.Fatal("AIMLAPI is not available:", err)
	}

	fmt.Println("AIMLAPI is healthy")
}
