// AIMLAPI Demo - Demonstrates all features of the multi-model router
package main

import (
	"context"
	"fmt"
	"log"
	"os"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/aimlapi"
)

func main() {
	// Check for API key
	apiKey := os.Getenv("AIMLAPI_KEY")
	if apiKey == "" {
		fmt.Println("⚠️  AIMLAPI_KEY not set. Set it to run real API calls.")
		fmt.Println("   export AIMLAPI_KEY='your-key-here'")
		fmt.Println()
		fmt.Println("Running in DEMO MODE (no actual API calls)")
	fmt.Println()
		demoMode()
		return
	}

	// Run live demo
	liveDemo(apiKey)
}

func demoMode() {
	fmt.Println("═══════════════════════════════════════════════════════════")
	fmt.Println("  AIMLAPI Multi-Model Router - DEMO MODE")
	fmt.Println("═══════════════════════════════════════════════════════════")
	fmt.Println()

	client := aimlapi.NewClient("")

	// Demo 1: List available models
	fmt.Println("📋 AVAILABLE MODELS (30+ models from 8 providers)")
	fmt.Println("─────────────────────────────────────────────────────────")
	models := client.ListModels()
	for i, model := range models {
		if i >= 10 {
			fmt.Printf("   ... and %d more models\n\n", len(models)-10)
			break
		}
		avgCost := (model.CostPerMInput + model.CostPerMOutput) / 2.0
		fmt.Printf("   %d. %-25s | Quality: %.1f | Speed: %.1f | $%.2f/M\n",
			i+1, model.Name, model.QualityRating, model.SpeedRating, avgCost)
	}

	// Demo 2: Three-regime selection
	fmt.Println("\n⚙️  THREE-REGIME SELECTION")
	fmt.Println("─────────────────────────────────────────────────────────")
	constraints := aimlapi.SelectionConstraints{
		TaskType:   aimlapi.TASK_CODE,
		MinQuality: 8.0,
	}

	client.SetRegime(1)
	model1, _ := client.SelectModel(constraints)
	fmt.Printf("   REGIME 1 (Exploration):   %s\n", model1.Name)

	client.SetRegime(2)
	model2, _ := client.SelectModel(constraints)
	fmt.Printf("   REGIME 2 (Optimization):  %s\n", model2.Name)

	client.SetRegime(3)
	model3, _ := client.SelectModel(constraints)
	fmt.Printf("   REGIME 3 (Stabilization): %s\n", model3.Name)

	// Demo 3: Williams batching
	fmt.Println("\n📊 WILLIAMS BATCHING - O(√n × log₂n)")
	fmt.Println("─────────────────────────────────────────────────────────")
	testSizes := []int{10, 100, 1000}
	for _, n := range testSizes {
		batchSize := calculateDemoBatchSize(n)
		fmt.Printf("   n=%d → batch size = %d\n", n, batchSize)
	}

	// Demo 4: Capabilities
	fmt.Println("\n🎯 FEATURES SHOWCASE")
	fmt.Println("─────────────────────────────────────────────────────────")
	fmt.Println("   ✅ 30+ AI models from 8 providers")
	fmt.Println("   ✅ Three-regime intelligent selection")
	fmt.Println("   ✅ Streaming chat support")
	fmt.Println("   ✅ Image generation (FLUX, Stable Diffusion)")
	fmt.Println("   ✅ Fallback chains for reliability")
	fmt.Println("   ✅ Williams batching O(√n × log₂n)")
	fmt.Println("   ✅ Rate limiting with token bucket")
	fmt.Println("   ✅ Exponential backoff retry")
	fmt.Println("   ✅ Cost estimation and optimization")

	fmt.Println()
	fmt.Println("═══════════════════════════════════════════════════════════")
	fmt.Println("  Set AIMLAPI_KEY to run live API demo!")
	fmt.Println("═══════════════════════════════════════════════════════════")
	fmt.Println()
}

func liveDemo(apiKey string) {
	fmt.Println("═══════════════════════════════════════════════════════════")
	fmt.Println("  AIMLAPI Multi-Model Router - LIVE DEMO")
	fmt.Println("═══════════════════════════════════════════════════════════")
	fmt.Println()

	client := aimlapi.NewClient(apiKey)
	ctx := context.Background()

	// Test 1: Health Check
	fmt.Println("🏥 Health Check...")
	if err := client.HealthCheck(ctx); err != nil {
		log.Fatalf("Health check failed: %v", err)
	}
	fmt.Println("   ✅ AIMLAPI is healthy")
	fmt.Println()

	// Test 2: Simple Chat
	fmt.Println("💬 Simple Chat (gpt-4o-mini)...")
	start := time.Now()
	response, err := client.SimpleChat(ctx, "In one sentence, what is urban planning?")
	if err != nil {
		log.Printf("   ❌ Error: %v\n", err)
	} else {
		fmt.Printf("   ✅ Response (%dms): %s\n\n", time.Since(start).Milliseconds(), response)
	}

	// Test 3: System Chat
	fmt.Println("🎓 System Chat with custom prompt...")
	start = time.Now()
	systemPrompt := "You are an expert in urban research. Answer in one sentence."
	response, err = client.SystemChat(ctx, systemPrompt, "What is TOD?")
	if err != nil {
		log.Printf("   ❌ Error: %v\n", err)
	} else {
		fmt.Printf("   ✅ Response (%dms): %s\n\n", time.Since(start).Milliseconds(), response)
	}

	// Test 4: Conversation
	fmt.Println("💭 Multi-turn Conversation...")
	conv := aimlapi.NewConversation()
	conv.AddSystem("You are a helpful assistant. Be very brief.")
	conv.AddUser("What is climate change?")
	conv.AddAssistant("Climate change is the long-term shift in global temperatures and weather patterns.")
	conv.AddUser("What can cities do about it? Answer in one sentence.")

	start = time.Now()
	req := conv.ToChatRequest("gpt-4o-mini")
	resp, err := client.Chat(ctx, req)
	if err != nil {
		log.Printf("   ❌ Error: %v\n", err)
	} else {
		fmt.Printf("   ✅ Response (%dms): %s\n\n",
			time.Since(start).Milliseconds(),
			resp.Choices[0].Message.Content)
	}

	// Test 5: Streaming
	fmt.Println("📡 Streaming Chat...")
	fmt.Print("   Response: ")
	streamReq := aimlapi.ChatRequest{
		Messages: []aimlapi.Message{
			{Role: "user", Content: "Count from 1 to 5, separated by commas"},
		},
	}

	start = time.Now()
	err = client.StreamChat(ctx, streamReq, func(chunk aimlapi.StreamChunk) {
		if !chunk.Done {
			fmt.Print(chunk.Content)
		}
	})
	if err != nil {
		log.Printf("\n   ❌ Error: %v\n", err)
	} else {
		fmt.Printf(" (%dms)\n\n", time.Since(start).Milliseconds())
	}

	// Test 6: Model Selection
	fmt.Println("🎯 Intelligent Model Selection...")
	constraints := aimlapi.SelectionConstraints{
		TaskType:   aimlapi.TASK_CODE,
		MinQuality: 8.5,
		MaxCostPerM: 5.0,
	}
	model, err := client.SelectModel(constraints)
	if err != nil {
		log.Printf("   ❌ Error: %v\n", err)
	} else {
		fmt.Printf("   ✅ Selected: %s (Quality: %.1f, Cost: $%.2f/M)\n\n",
			model.Name, model.QualityRating,
			(model.CostPerMInput+model.CostPerMOutput)/2.0)
	}

	// Test 7: Cost Estimation
	fmt.Println("💰 Cost Estimation...")
	estimateReq := aimlapi.ChatRequest{
		Model: "gpt-4o",
		Messages: []aimlapi.Message{
			{Role: "user", Content: "Explain quantum computing in detail"},
		},
		MaxTokens: 2000,
	}
	model, _ = client.GetModel("gpt-4o")
	cost := aimlapi.EstimateRequestCost(model, estimateReq)
	fmt.Printf("   ✅ Estimated cost for 2000 tokens: $%.4f\n\n", cost)

	// Test 8: Fallback Router
	fmt.Println("🔄 Fallback Router...")
	router := aimlapi.NewRouter(client)
	routerReq := aimlapi.ChatRequest{
		Messages: []aimlapi.Message{
			{Role: "user", Content: "Hello in one word"},
		},
	}

	start = time.Now()
	routerResp, err := router.RouteWithFallback(ctx, routerReq)
	if err != nil {
		log.Printf("   ❌ Error: %v\n", err)
	} else {
		fmt.Printf("   ✅ Response (%dms): %s\n\n",
			time.Since(start).Milliseconds(),
			routerResp.Choices[0].Message.Content)
	}

	fmt.Println("═══════════════════════════════════════════════════════════")
	fmt.Println("  ALL TESTS COMPLETE! ✅")
	fmt.Println("═══════════════════════════════════════════════════════════")
	fmt.Println()
}

// calculateDemoBatchSize demonstrates Williams batching calculation
func calculateDemoBatchSize(n int) int {
	if n <= 0 {
		return 1
	}

	// Williams: O(√n × log₂n)
	sqrtN := 1.0
	for i := 1; i*i <= n; i++ {
		sqrtN = float64(i)
	}

	log2N := 0.0
	temp := n
	for temp > 1 {
		log2N++
		temp /= 2
	}

	batchSize := int(sqrtN * log2N)
	if batchSize < 1 {
		batchSize = 1
	}
	if batchSize > 20 {
		batchSize = 20
	}

	return batchSize
}
