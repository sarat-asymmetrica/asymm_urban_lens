package main

import (
	"bufio"
	"fmt"
	"os"
	"strings"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/persona"
)

func main() {
	// Initialize Asya
	asya := persona.NewAsya()

	// Initialize user profile
	profile := persona.UserProfile{
		MessageHistory:      []persona.Message{},
		IntelligenceWeights: make(map[string]float64),
		AvgResponseTime:     2.0,
		Location:            "",
		Language:            "en",
	}

	// Set initial intelligence weights
	profile.IntelligenceWeights = map[string]float64{
		"linguistic":          0.5,
		"logical_mathematical": 0.5,
		"spatial":             0.5,
		"musical":             0.1,
		"bodily_kinesthetic":  0.5,
		"interpersonal":       0.5,
		"intrapersonal":       0.5,
		"naturalistic":        0.5,
	}

	// Display welcome banner
	printBanner()

	// Detect language and location
	fmt.Print("Where are you located? (e.g., Mumbai, Lagos, London): ")
	reader := bufio.NewReader(os.Stdin)
	location, _ := reader.ReadString('\n')
	profile.Location = strings.TrimSpace(location)

	fmt.Print("Preferred language? (en/hi/es/fr/de): ")
	lang, _ := reader.ReadString('\n')
	profile.Language = strings.TrimSpace(lang)
	if profile.Language == "" {
		profile.Language = "en"
	}

	// Get initial greeting
	greeting := persona.GetGreeting(profile.Language, "casual")
	fmt.Printf("\n%s\n\n", greeting)

	// Conversation loop
	messageCount := 0
	for {
		// Get user input
		fmt.Print("You: ")
		input, _ := reader.ReadString('\n')
		input = strings.TrimSpace(input)

		if input == "" {
			continue
		}

		// Exit commands
		if strings.ToLower(input) == "exit" || strings.ToLower(input) == "quit" {
			fmt.Println("\nAsya: Thank you for exploring with me! May your curiosity never end. 🙏")
			break
		}

		// Help command
		if strings.ToLower(input) == "help" {
			printHelp()
			continue
		}

		// Stats command
		if strings.ToLower(input) == "stats" {
			printStats(asya, profile)
			continue
		}

		messageCount++
		startTime := time.Now()

		// Add to message history
		profile.MessageHistory = append(profile.MessageHistory, persona.Message{
			Content:   input,
			Timestamp: time.Now(),
		})

		// Update avg response time
		if messageCount > 1 {
			responseTime := time.Since(startTime).Seconds()
			profile.AvgResponseTime = (profile.AvgResponseTime + responseTime) / 2.0
		}

		// Adapt to user
		state := asya.AdaptToUser(profile)

		// Show debug info (optional)
		if os.Getenv("DEBUG") == "1" {
			fmt.Printf("\n[DEBUG] Tone: %s | Regime: %s | Intelligence Leaders: %v\n",
				state.Tone, state.CurrentRegime, state.IntelligenceLeaders)
		}

		// Check for negative energy and redirect
		redirected := checkForRedirection(input, profile, state)
		if redirected != "" {
			fmt.Printf("\nAsya: %s\n\n", redirected)
			continue
		}

		// Generate response content (simplified - in real app, this would be LLM)
		content := generateMockResponse(input, state, profile)

		// Wrap with persona adaptation
		response := asya.GenerateResponse(state, content, state.CurrentRegime)

		fmt.Printf("\nAsya: %s\n\n", response)
	}
}

func printBanner() {
	fmt.Println("╔════════════════════════════════════════════════════════════╗")
	fmt.Println("║                                                            ║")
	fmt.Println("║           ASYA - Adaptive Persona System Demo             ║")
	fmt.Println("║        \"Meet the user WHERE THEY ARE\"                      ║")
	fmt.Println("║                                                            ║")
	fmt.Println("║  Features:                                                 ║")
	fmt.Println("║  • 6 tone adaptations (formal, casual, playful, edgy...)  ║")
	fmt.Println("║  • 8 intelligence types (Gardner's MI)                    ║")
	fmt.Println("║  • 3 flow phases (Void, Fire, Water)                      ║")
	fmt.Println("║  • Cultural analogies (Indian, Nigerian, universal...)    ║")
	fmt.Println("║  • Way of Water redirection                               ║")
	fmt.Println("║                                                            ║")
	fmt.Println("║  Commands: 'help', 'stats', 'exit'                        ║")
	fmt.Println("║                                                            ║")
	fmt.Println("╚════════════════════════════════════════════════════════════╝")
	fmt.Println()
}

func printHelp() {
	fmt.Println("\n=== ASYA COMMANDS ===")
	fmt.Println("help  - Show this help message")
	fmt.Println("stats - Show conversation statistics")
	fmt.Println("exit  - End the conversation")
	fmt.Println("\nJust talk naturally! Asya adapts to:")
	fmt.Println("• Your tone (formal, casual, edgy, etc.)")
	fmt.Println("• Your intelligence type (spatial, logical, etc.)")
	fmt.Println("• Your flow state (exploration, flow, recovery)")
	fmt.Println("• Your cultural context (based on location)")
	fmt.Println()
}

func printStats(asya *persona.Asya, profile persona.UserProfile) {
	state := asya.StateEngine

	fmt.Println("\n=== CONVERSATION STATISTICS ===")
	fmt.Printf("Messages Exchanged: %d\n", len(profile.MessageHistory))
	fmt.Printf("Session Duration: %s\n", time.Since(state.SessionStart).Round(time.Second))
	fmt.Printf("\nCurrent State:\n")
	fmt.Printf("  Tone: %s\n", state.CurrentTone)
	fmt.Printf("  Regime: %s\n", state.CurrentRegime)
	fmt.Printf("  Cultural Context: %s\n", state.CulturalContext)
	fmt.Printf("\nUser Quaternion (W, X, Y, Z):\n")
	fmt.Printf("  Coherence:   %.2f\n", state.UserQuaternion.W)
	fmt.Printf("  Focus:       %.2f\n", state.UserQuaternion.X)
	fmt.Printf("  Creativity:  %.2f\n", state.UserQuaternion.Y)
	fmt.Printf("  Persistence: %.2f\n", state.UserQuaternion.Z)
	fmt.Printf("\nRegime History:\n")
	fmt.Printf("  R1 (Exploration): %d transitions\n", len(state.RegimeHistory["R1"]))
	fmt.Printf("  R2 (Flow):        %d transitions\n", len(state.RegimeHistory["R2"]))
	fmt.Printf("  R3 (Recovery):    %d transitions\n", len(state.RegimeHistory["R3"]))

	totalTransitions := float64(len(state.RegimeHistory["R1"]) + len(state.RegimeHistory["R2"]) + len(state.RegimeHistory["R3"]))
	if totalTransitions > 0 {
		r1Pct := float64(len(state.RegimeHistory["R1"])) / totalTransitions * 100
		r2Pct := float64(len(state.RegimeHistory["R2"])) / totalTransitions * 100
		r3Pct := float64(len(state.RegimeHistory["R3"])) / totalTransitions * 100
		fmt.Printf("\nRegime Distribution:\n")
		fmt.Printf("  R1: %.1f%% (target: 30%%)\n", r1Pct)
		fmt.Printf("  R2: %.1f%% (target: 20%%)\n", r2Pct)
		fmt.Printf("  R3: %.1f%% (target: 50%%)\n", r3Pct)

		if r3Pct < 50 {
			fmt.Println("\n⚠️  Warning: R3 < 50% - Consider taking a break!")
		}
	}

	fmt.Printf("\nTop Intelligence Types:\n")
	topIntelligences := persona.GetTopIntelligences(profile.IntelligenceWeights, 3)
	for i, intel := range topIntelligences {
		fmt.Printf("  %d. %s (%.2f)\n", i+1, intel, profile.IntelligenceWeights[intel])
	}

	fmt.Println()
}

func checkForRedirection(input string, profile persona.UserProfile, state persona.PersonaState) string {
	inputLower := strings.ToLower(input)

	// Check for frustration
	if strings.Contains(inputLower, "frustrated") || strings.Contains(inputLower, "confused") ||
		strings.Contains(inputLower, "don't get") || strings.Contains(inputLower, "hard") {
		return persona.HandleFrustration(&persona.Conversation{
			Messages:    profile.MessageHistory,
			UserProfile: profile,
		})
	}

	// Check for aggression
	if strings.Contains(inputLower, "fuck") || strings.Contains(inputLower, "shit") ||
		strings.Contains(inputLower, "damn") || strings.Contains(inputLower, "hate") {
		return persona.HandleAggression(&persona.Conversation{
			Messages:    profile.MessageHistory,
			UserProfile: profile,
		})
	}

	// Check for boredom
	if strings.Contains(inputLower, "boring") || strings.Contains(inputLower, "bored") {
		return persona.HandleBoredom(&persona.Conversation{
			Messages:    profile.MessageHistory,
			UserProfile: profile,
		})
	}

	return ""
}

func generateMockResponse(input string, state persona.PersonaState, profile persona.UserProfile) string {
	// This is a mock - in production, this would call an LLM or knowledge engine

	inputLower := strings.ToLower(input)

	// Check for question patterns
	if strings.Contains(inputLower, "quaternion") {
		// Use cultural analogy if available
		analogies := persona.GetAnalogiesForConcept("quaternion_rotation", state.CulturalContext)
		if len(analogies) > 0 {
			analogy := analogies[0]
			return fmt.Sprintf("Great question! %s\n\n%s\n\nQuaternions are 4D numbers (w, x, y, z) that represent rotations in 3D space. They're used in game engines, robotics, and aerospace!",
				analogy.Example, analogy.Explanation)
		}
		return "Quaternions are 4D numbers that represent rotations in 3D space. Think of them as instructions for rotating objects - used in games, robotics, and physics simulations!"
	}

	if strings.Contains(inputLower, "exponential") || strings.Contains(inputLower, "growth") {
		analogies := persona.GetAnalogiesForConcept("exponential_growth", state.CulturalContext)
		if len(analogies) > 0 {
			analogy := analogies[0]
			return fmt.Sprintf("%s\n\n%s", analogy.Example, analogy.Explanation)
		}
	}

	if strings.Contains(inputLower, "thermodynamics") || strings.Contains(inputLower, "heat") {
		analogies := persona.GetAnalogiesForConcept("thermodynamics", state.CulturalContext)
		if len(analogies) > 0 {
			analogy := analogies[0]
			return fmt.Sprintf("%s\n\n%s", analogy.Example, analogy.Explanation)
		}
	}

	// Default response based on intelligence type
	topIntel := state.IntelligenceLeaders[0]
	switch topIntel {
	case "spatial":
		return "Let me show you visually... [Diagram would appear here]\n\nDoes a visual representation help?"
	case "logical_mathematical":
		return "Let's formalize this mathematically:\n\n[Equation would appear here]\n\nWant to derive this together?"
	case "naturalistic":
		return "Let's connect this to something you observe in nature...\n\n[Real-world example would appear here]"
	default:
		return "That's an interesting question! Let's explore it together."
	}
}
