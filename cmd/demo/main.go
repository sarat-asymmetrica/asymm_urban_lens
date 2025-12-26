//go:build ignore
// +build ignore

// ASYA Demo - Interactive CLI demonstration
// Shows Asya's conversational AI in action with rich terminal UI
// NOTE: This demo needs interface updates to match current conversation.LeanBridge
package main

import (
	"bufio"
	"context"
	"fmt"
	"os"
	"strings"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/conversation"
	"github.com/asymmetrica/urbanlens/pkg/lean"
	"github.com/asymmetrica/urbanlens/scripts"
)

// ═══════════════════════════════════════════════════════════════════════════
// CONFIGURATION
// ═══════════════════════════════════════════════════════════════════════════

const (
	// Colors for terminal output
	ColorReset  = "\033[0m"
	ColorRed    = "\033[31m"
	ColorGreen  = "\033[32m"
	ColorYellow = "\033[33m"
	ColorBlue   = "\033[34m"
	ColorPurple = "\033[35m"
	ColorCyan   = "\033[36m"
	ColorWhite  = "\033[37m"
	ColorBold   = "\033[1m"

	// Phase indicators
	PhaseVoidIcon     = "🌑" // Dark moon - exploration
	PhaseFlowIcon     = "🔥" // Fire - flow state
	PhaseSolutionIcon = "💧" // Water - solution/recovery
)

// ═══════════════════════════════════════════════════════════════════════════
// MAIN
// ═══════════════════════════════════════════════════════════════════════════

func main() {
	printBanner()

	// Show menu
	fmt.Println("\n" + ColorCyan + "Choose an option:" + ColorReset)
	fmt.Println("  1. Try a pre-built demo conversation")
	fmt.Println("  2. Have your own conversation with Asya")
	fmt.Println("  3. Quick automated run (all demos)")
	fmt.Print("\nChoice [1-3]: ")

	reader := bufio.NewReader(os.Stdin)
	choice, _ := reader.ReadString('\n')
	choice = strings.TrimSpace(choice)

	switch choice {
	case "1":
		runDemoSelection(reader)
	case "2":
		runInteractiveConversation(reader)
	case "3":
		runAllDemos()
	default:
		fmt.Println(ColorRed + "Invalid choice!" + ColorReset)
		os.Exit(1)
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// DEMO SELECTION
// ═══════════════════════════════════════════════════════════════════════════

func runDemoSelection(reader *bufio.Reader) {
	fmt.Println("\n" + ColorCyan + "Available Demo Conversations:" + ColorReset)

	for i, demo := range scripts.DemoConversations {
		fmt.Printf("  %d. %s (%s, %s)\n",
			i+1,
			demo.Name,
			demo.Language,
			demo.CulturalContext)
	}

	fmt.Print("\nChoose demo [1-" + fmt.Sprintf("%d", len(scripts.DemoConversations)) + "]: ")
	choice, _ := reader.ReadString('\n')
	choice = strings.TrimSpace(choice)

	var demoIdx int
	fmt.Sscanf(choice, "%d", &demoIdx)

	if demoIdx < 1 || demoIdx > len(scripts.DemoConversations) {
		fmt.Println(ColorRed + "Invalid choice!" + ColorReset)
		return
	}

	demo := scripts.DemoConversations[demoIdx-1]
	runDemo(demo)
}

// runDemo executes a pre-built demo conversation
func runDemo(demo scripts.DemoConversation) {
	printSectionHeader("Demo: " + demo.Name)

	// Create engine (with mock AI for demo playback)
	engine := conversation.NewEngine(
		&DemoAIClient{demo: demo},
		&lean.MockBridge{Theorem: demo.ExpectedTheorem, Valid: true},
		&MockKnowledgeGraph{},
		&MockLanguageDetector{Language: demo.Language},
	)

	conv := engine.NewConversation("demo_user")
	ctx := context.Background()

	// Play through demo messages
	for i, msg := range demo.Messages {
		if msg.Role == "user" {
			// Print user message
			printUserMessage(msg.Content, msg.Notes)

			// Process it
			resp, err := engine.ProcessMessage(ctx, conv, msg.Content)
			if err != nil {
				fmt.Printf(ColorRed+"Error: %v\n"+ColorReset, err)
				continue
			}

			// Print state indicators
			printStateIndicators(conv)

			// Print AI response
			time.Sleep(300 * time.Millisecond) // Simulate typing
			printAssistantMessage(resp)

			// Wait for user to continue
			if i < len(demo.Messages)-2 {
				fmt.Print(ColorYellow + "\n[Press Enter to continue...]" + ColorReset)
				bufio.NewReader(os.Stdin).ReadString('\n')
			}
		}
	}

	// Show final theorem
	if demo.ExpectedTheorem != "" {
		time.Sleep(500 * time.Millisecond)
		printSectionHeader("Generated Theorem")
		fmt.Println(ColorGreen + demo.ExpectedTheorem + ColorReset)
	}

	// Summary
	printSummary(conv)
}

// ═══════════════════════════════════════════════════════════════════════════
// INTERACTIVE CONVERSATION
// ═══════════════════════════════════════════════════════════════════════════

func runInteractiveConversation(reader *bufio.Reader) {
	printSectionHeader("Interactive Conversation with Asya")

	// Create real engine (would use real AIMLAPI here)
	engine := conversation.NewEngine(
		&MockAIClient{}, // Replace with real AIMLAPI client
		&lean.MockBridge{Valid: true},
		&MockKnowledgeGraph{},
		&MockLanguageDetector{Language: "en"},
	)

	conv := engine.NewConversation("interactive_user")
	ctx := context.Background()

	fmt.Println(ColorCyan + "Asya: Hello! I'd love to explore something with you. What have you noticed?" + ColorReset)
	fmt.Println(ColorYellow + "(Type 'quit' to exit)\n" + ColorReset)

	for {
		// Get user input
		fmt.Print(ColorWhite + "You: " + ColorReset)
		userMsg, _ := reader.ReadString('\n')
		userMsg = strings.TrimSpace(userMsg)

		if strings.ToLower(userMsg) == "quit" {
			fmt.Println(ColorCyan + "\nAsya: Thank you for exploring with me! Come back anytime! ✨" + ColorReset)
			break
		}

		if userMsg == "" {
			continue
		}

		// Process message
		resp, err := engine.ProcessMessage(ctx, conv, userMsg)
		if err != nil {
			fmt.Printf(ColorRed+"Error: %v\n"+ColorReset, err)
			continue
		}

		// Show state
		printStateIndicators(conv)

		// Show response
		time.Sleep(200 * time.Millisecond) // Simulate thinking
		printAssistantMessage(resp)

		// Check if we reached formalization
		if conv.State == conversation.StateFormalizing && conv.LeanTheorem != "" {
			time.Sleep(500 * time.Millisecond)
			printSectionHeader("Your Theorem!")
			fmt.Println(ColorGreen + conv.LeanTheorem + ColorReset)
			fmt.Println(ColorYellow + "\nContinue chatting or type 'quit' to exit." + ColorReset)
		}
	}

	// Summary
	printSummary(conv)
}

// ═══════════════════════════════════════════════════════════════════════════
// AUTOMATED RUN (ALL DEMOS)
// ═══════════════════════════════════════════════════════════════════════════

func runAllDemos() {
	printSectionHeader("Running All Demos (Automated)")

	for i, demo := range scripts.DemoConversations {
		fmt.Printf("\n%s[%d/%d] %s%s\n",
			ColorBold, i+1, len(scripts.DemoConversations), demo.Name, ColorReset)

		// Quick run
		engine := conversation.NewEngine(
			&DemoAIClient{demo: demo},
			&lean.MockBridge{Theorem: demo.ExpectedTheorem, Valid: true},
			&MockKnowledgeGraph{},
			&MockLanguageDetector{Language: demo.Language},
		)

		conv := engine.NewConversation(fmt.Sprintf("demo_user_%d", i))
		ctx := context.Background()

		// Process all user messages
		userMsgCount := 0
		for _, msg := range demo.Messages {
			if msg.Role == "user" {
				userMsgCount++
				_, err := engine.ProcessMessage(ctx, conv, msg.Content)
				if err != nil {
					fmt.Printf(ColorRed+"  Error: %v\n"+ColorReset, err)
					break
				}
			}
		}

		// Report
		fmt.Printf("  ✓ Completed: %d messages, final state: %s%s%s\n",
			userMsgCount,
			ColorGreen,
			conv.State,
			ColorReset)
		fmt.Printf("  Domain: %s, Language: %s\n",
			demo.ExpectedDomain,
			demo.Language)

		time.Sleep(200 * time.Millisecond)
	}

	fmt.Println("\n" + ColorGreen + "All demos completed successfully! ✨" + ColorReset)
}

// ═══════════════════════════════════════════════════════════════════════════
// UI HELPERS
// ═══════════════════════════════════════════════════════════════════════════

func printBanner() {
	banner := `
 █████╗ ███████╗██╗   ██╗ █████╗
██╔══██╗██╔════╝╚██╗ ██╔╝██╔══██╗
███████║███████╗ ╚████╔╝ ███████║
██╔══██║╚════██║  ╚██╔╝  ██╔══██║
██║  ██║███████║   ██║   ██║  ██║
╚═╝  ╚═╝╚══════╝   ╚═╝   ╚═╝  ╚═╝

Universal Science Platform - Interactive Demo
"Her" for Curious Minds Everywhere ✨
`
	fmt.Println(ColorCyan + banner + ColorReset)
}

func printSectionHeader(title string) {
	fmt.Println("\n" + ColorBold + "═══════════════════════════════════════════════════════════════════" + ColorReset)
	fmt.Println(ColorBold + "  " + title + ColorReset)
	fmt.Println(ColorBold + "═══════════════════════════════════════════════════════════════════" + ColorReset + "\n")
}

func printUserMessage(content, notes string) {
	fmt.Printf("%sYou: %s%s\n", ColorWhite, ColorReset, content)
	if notes != "" {
		fmt.Printf("%s      [%s]%s\n", ColorYellow, notes, ColorReset)
	}
}

func printAssistantMessage(content string) {
	fmt.Printf("\n%sAsya: %s%s\n\n", ColorCyan, ColorReset, content)
}

func printStateIndicators(conv *conversation.Conversation) {
	// Phase indicator
	phaseIcon := PhaseVoidIcon
	switch conv.Phase {
	case conversation.PhaseVoid:
		phaseIcon = PhaseVoidIcon
	case conversation.PhaseFlow:
		phaseIcon = PhaseFlowIcon
	case conversation.PhaseSolution:
		phaseIcon = PhaseSolutionIcon
	}

	// Intelligence indicator
	intType := conv.Profile.DominantIntelligence
	if intType == "" {
		intType = conversation.IntUnknown
	}

	// Regime calculation (simplified)
	r1, r2, r3 := calculateRegimes(conv)

	fmt.Printf("%s┌─ State: %s | Phase: %s %s | Intelligence: %s%s\n",
		ColorYellow,
		conv.State,
		conv.Phase,
		phaseIcon,
		intType,
		ColorReset)

	fmt.Printf("%s└─ Regimes: R1=%.0f%% R2=%.0f%% R3=%.0f%% | Why-depth: %d%s\n",
		ColorYellow,
		r1*100,
		r2*100,
		r3*100,
		conv.WhyChainDepth,
		ColorReset)
}

func printSummary(conv *conversation.Conversation) {
	printSectionHeader("Conversation Summary")

	fmt.Printf("Total messages: %s%d%s\n", ColorGreen, len(conv.Messages), ColorReset)
	fmt.Printf("Why-chain depth: %s%d%s\n", ColorGreen, conv.WhyChainDepth, ColorReset)
	fmt.Printf("Insights discovered: %s%d%s\n", ColorGreen, len(conv.Insights), ColorReset)
	fmt.Printf("Final state: %s%s%s\n", ColorGreen, conv.State, ColorReset)
	fmt.Printf("Final phase: %s%s%s\n", ColorGreen, conv.Phase, ColorReset)

	if conv.Anchor != "" {
		fmt.Printf("Anchor: %s%s%s\n", ColorCyan, conv.Anchor, ColorReset)
	}

	if conv.LeanTheorem != "" {
		fmt.Printf("\n%sTheorem generated: ✓%s\n", ColorGreen, ColorReset)
	}

	// Show intelligence profile
	fmt.Println("\nIntelligence Profile:")
	for intType, score := range conv.Profile.IntelligenceProfile {
		if score > 0 {
			bars := int(score * 10)
			if bars > 20 {
				bars = 20
			}
			barStr := strings.Repeat("█", bars)
			fmt.Printf("  %-15s %s%s%s %.2f\n",
				intType,
				ColorGreen,
				barStr,
				ColorReset,
				score)
		}
	}
}

func calculateRegimes(conv *conversation.Conversation) (r1, r2, r3 float64) {
	// Simplified regime calculation for demo
	// In real implementation, this uses VQC network

	totalMsgs := len(conv.Messages)
	if totalMsgs == 0 {
		return 0.3, 0.2, 0.5 // Default
	}

	// Approximate based on state
	switch conv.State {
	case conversation.StateGreeting, conversation.StateAnchoring:
		return 0.5, 0.2, 0.3 // High exploration
	case conversation.StateWhyChaining:
		return 0.2, 0.5, 0.3 // High optimization
	case conversation.StateSynthesizing, conversation.StateFormalizing:
		return 0.2, 0.3, 0.5 // High stabilization
	case conversation.StateCelebrating:
		return 0.1, 0.1, 0.8 // Very high stabilization
	default:
		return 0.3, 0.2, 0.5
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// MOCK IMPLEMENTATIONS
// ═══════════════════════════════════════════════════════════════════════════

type DemoAIClient struct {
	demo scripts.DemoConversation
}

func (d *DemoAIClient) GenerateResponse(conv *conversation.Conversation, systemPrompt, userMessage string) (string, error) {
	// Find corresponding assistant response in demo
	for i, msg := range d.demo.Messages {
		if msg.Role == "user" && msg.Content == userMessage {
			// Return next assistant message
			if i+1 < len(d.demo.Messages) && d.demo.Messages[i+1].Role == "assistant" {
				return d.demo.Messages[i+1].Content, nil
			}
		}
	}

	// Fallback
	return "I'm here to explore with you!", nil
}

type MockAIClient struct{}

func (m *MockAIClient) GenerateResponse(conv *conversation.Conversation, systemPrompt, userMessage string) (string, error) {
	// Simple state-based responses for interactive mode
	switch conv.State {
	case conversation.StateGreeting:
		return "Hello! I'd love to explore something with you. What have you noticed?", nil
	case conversation.StateAnchoring:
		return "Tell me more about what you're experiencing. What do your senses tell you?", nil
	case conversation.StateWhyChaining:
		return "That's interesting! Why do you think that happens?", nil
	case conversation.StateSynthesizing:
		return "I see the connection! This relates to fundamental principles. Would you like to see it formalized?", nil
	case conversation.StateFormalizing:
		return "Let me create a theorem for your discovery!", nil
	case conversation.StateCelebrating:
		return "You've made a wonderful discovery! Thank you for exploring with me!", nil
	default:
		return "I'm here to help you explore!", nil
	}
}

type MockKnowledgeGraph struct{}

func (m *MockKnowledgeGraph) FindRelatedConcepts(domain string, concept string) ([]string, error) {
	return []string{"thermodynamics", "phase_transition", "energy"}, nil
}

func (m *MockKnowledgeGraph) StoreInsight(insight conversation.Insight) error {
	return nil
}

type MockLanguageDetector struct {
	Language string
}

func (m *MockLanguageDetector) Detect(text string) (string, error) {
	return m.Language, nil
}
