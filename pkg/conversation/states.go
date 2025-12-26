// Package conversation - State handlers for Sarat Method phases
// Each handler implements one phase of: Anchor → Chain → Synthesize → Formalize → Celebrate
package conversation

import (
	"context"
	"fmt"
	"strings"
)

// ═══════════════════════════════════════════════════════════════════════════
// STATE HANDLERS - The Sarat Method Flow
// ═══════════════════════════════════════════════════════════════════════════

// handleGreeting - Initial contact, detect language and intelligence
// Goal: Get first observation, establish rapport
func (e *Engine) handleGreeting(ctx context.Context, conv *Conversation, msg string) (string, error) {
	// Check if user already gave an observation in greeting
	if hasObservation(msg) {
		conv.Anchor = extractObservation(msg)
		conv.State = StateAnchoring
		return e.getAnchoringPrompt(conv), nil
	}

	// Otherwise, ask for observation
	greeting := e.getGreetingPrompt(conv.Profile)
	return e.sendResponse(conv, greeting), nil
}

// handleAnchoring - Get concrete, sensory observation
// PHASE 1 of Sarat Method: THE ANCHOR
// Goal: Ensure observation is CONCRETE, SENSORY, and PERSONAL
func (e *Engine) handleAnchoring(ctx context.Context, conv *Conversation, msg string) (string, error) {
	// Check if anchor is concrete enough
	if !isConcrete(msg) {
		// Need more concreteness
		response := e.makeMoreConcrete(msg, conv.Profile)
		return e.sendResponse(conv, response), nil
	}

	// Good anchor! Store it and transition to why-chaining
	conv.Anchor = msg
	conv.State = StateWhyChaining
	conv.WhyChainDepth = 0
	conv.Phase = PhaseVoid // Entering deep Void exploration

	response := e.getFirstWhyPrompt(conv.Anchor, conv.Profile)
	return e.sendResponse(conv, response), nil
}

// handleWhyChaining - Ask "why" repeatedly, go deep
// PHASE 2 of Sarat Method: THE WHY CHAIN
// Goal: Follow ONE thread to bedrock (physics/chemistry/biology)
func (e *Engine) handleWhyChaining(ctx context.Context, conv *Conversation, msg string) (string, error) {
	conv.WhyChainDepth++

	// Check if we've reached bedrock
	// Triggers: 5+ steps OR fundamental science mentioned
	reachedBedrock := conv.WhyChainDepth >= 5 || mentionsFundamental(msg)

	if reachedBedrock {
		// Transition to synthesis
		conv.State = StateSynthesizing
		conv.Phase = PhaseFlow // Entering exponential convergence

		response := e.getFirstSynthesisPrompt(conv.Anchor, msg, conv.Profile)
		return e.sendResponse(conv, response), nil
	}

	// Continue chaining deeper
	response := e.getNextWhyPrompt(msg, conv.WhyChainDepth, conv.Profile)
	return e.sendResponse(conv, response), nil
}

// handleSynthesizing - Connect to existing knowledge
// PHASE 3 of Sarat Method: THE SYNTHESIS
// Goal: Bridge to other domains, find existing knowledge
func (e *Engine) handleSynthesizing(ctx context.Context, conv *Conversation, msg string) (string, error) {
	// Extract domain connections
	connections := extractConnections(msg)

	// Check if user made connections to ≥2 domains
	if len(connections) >= 2 {
		// Good synthesis! Transition to formalization
		conv.State = StateFormalizing
		conv.Phase = PhaseSolution // Entering stable attractor

		// Store insight
		insight := Insight{
			Description: conv.Anchor,
			Domain:      connections[0],
			Connections: connections,
			WhyDepth:    conv.WhyChainDepth,
		}
		conv.Insights = append(conv.Insights, insight)

		// Introduce Lean formalization
		response := e.getFormalizationIntro(conv.Profile)
		return e.sendResponse(conv, response), nil
	}

	// Need more synthesis
	response := e.getSynthesisPrompt(msg, conv.Profile)
	return e.sendResponse(conv, response), nil
}

// handleFormalizing - Introduce Lean, create theorem
// PHASE 4 of Sarat Method: THE FORMALIZATION
// Goal: Make it CONCRETE and ACTIONABLE with Lean code
func (e *Engine) handleFormalizing(ctx context.Context, conv *Conversation, msg string) (string, error) {
	// Generate Lean theorem from insights
	leanCode := ""
	var err error

	if e.leanBridge != nil {
		leanCode, err = e.leanBridge.GenerateTheorem(conv)
		if err != nil {
			return "", fmt.Errorf("error generating Lean theorem: %w", err)
		}

		// Validate it compiles
		valid, validErr := e.leanBridge.ValidateTheorem(leanCode)
		if !valid {
			return "", fmt.Errorf("generated Lean doesn't compile: %w", validErr)
		}

		conv.LeanTheorem = leanCode
	} else {
		// Fallback: Generate simple theorem structure
		leanCode = e.generateSimpleLeanTheorem(conv)
		conv.LeanTheorem = leanCode
	}

	// Transition to celebration
	conv.State = StateCelebrating

	// Present Lean code with explanation
	response := e.presentLeanCode(leanCode, conv.Profile)
	return e.sendResponse(conv, response), nil
}

// handleCelebrating - Honor the discovery, encourage sharing
// PHASE 5 of Sarat Method: THE CELEBRATION
// Goal: Empower user as scientist, encourage continuation
func (e *Engine) handleCelebrating(ctx context.Context, conv *Conversation, msg string) (string, error) {
	// Check if user wants to continue or stop
	if wantsToContinue(msg) {
		// Reset for new discovery cycle
		conv.State = StateAnchoring
		conv.WhyChainDepth = 0
		conv.Anchor = ""
		conv.Phase = PhaseVoid

		response := "Wonderful! What else have you noticed? What's another observation you'd like to explore?"
		return e.sendResponse(conv, response), nil
	}

	// Final celebration message
	response := e.getCelebrationMessage(conv.Profile, conv.Insights)
	return e.sendResponse(conv, response), nil
}

// handleStuck - Help user when stuck
// Goal: Diagnose issue and guide back to appropriate phase
func (e *Engine) handleStuck(ctx context.Context, conv *Conversation, msg string) (string, error) {
	// Diagnose which phase they're stuck in
	phase := e.detectPhase(conv, msg)

	var response string

	switch phase {
	case PhaseVoid:
		response = "Let's go back to what you observed. Can you describe it again with more sensory detail? " +
			"What did it FEEL like, LOOK like, SOUND like?"

	case PhaseFlow:
		response = "What if we try a different angle? What ELSE could cause this? " +
			"Or let's slow down - what do you already know about this?"

	case PhaseSolution:
		response = "Let's check: does this fit what you originally observed? " +
			"What would DISPROVE this? Can you think of a counter-example?"
	}

	// Transition back to appropriate state
	if conv.WhyChainDepth == 0 {
		conv.State = StateAnchoring
	} else if conv.WhyChainDepth < 5 {
		conv.State = StateWhyChaining
	} else {
		conv.State = StateSynthesizing
	}

	return e.sendResponse(conv, response), nil
}

// ═══════════════════════════════════════════════════════════════════════════
// PROMPT GENERATORS - Adaptive to intelligence type and language
// ═══════════════════════════════════════════════════════════════════════════

// getGreetingPrompt generates greeting in user's language
func (e *Engine) getGreetingPrompt(profile UserProfile) string {
	// TODO: Localize based on profile.Language
	greetings := map[string]string{
		"en": "Hello! What's something you've noticed today? Something that caught your attention?",
		"te": "నమస్కారం! మీరు ఈ రోజు ఏమి గమనించారు? ఏదైనా ఆసక్తికరమైన విషయం చూశారా?",
		"hi": "नमस्ते! आपने आज क्या देखा? कुछ दिलचस्प?",
		"es": "¡Hola! ¿Qué has notado hoy? ¿Algo que te llamó la atención?",
	}

	if greeting, ok := greetings[profile.Language]; ok {
		return greeting
	}
	return greetings["en"] // Default English
}

// getAnchoringPrompt generates anchoring prompt based on intelligence type
func (e *Engine) getAnchoringPrompt(conv *Conversation) string {
	intType := conv.Profile.DominantIntelligence

	prompts := map[IntelligenceType]string{
		IntKinesthetic: "Interesting! What do you FEEL? Can you describe the texture, temperature, or how it moves?",
		IntVisual:      "Fascinating! What do you SEE? Can you describe the colors, shapes, or patterns?",
		IntAuditory:    "Intriguing! What do you HEAR? Can you describe the sound, rhythm, or pitch?",
		IntSpatial:     "Great! Can you describe the pattern or shape? How would you draw it?",
		IntLogical:     "Excellent! What data are you observing? Can you measure or quantify it?",
		IntLinguistic:  "Wonderful! How would you describe this to someone? What metaphor fits?",
	}

	if prompt, ok := prompts[intType]; ok {
		return prompt
	}
	return "That's interesting! Can you tell me more about what you observed? What details did you notice?"
}

// makeMoreConcrete helps user make observation more concrete
func (e *Engine) makeMoreConcrete(msg string, profile UserProfile) string {
	intType := profile.DominantIntelligence

	suggestions := map[IntelligenceType]string{
		IntKinesthetic: "Let's make this more concrete. When you experience this, what do you FEEL in your body? Temperature? Pressure? Movement?",
		IntVisual:      "Let's get more specific. What exactly do you SEE? Colors? Shapes? How does it look?",
		IntSpatial:     "Let's be more precise. Can you describe the spatial arrangement? What's the pattern?",
		IntLogical:     "Let's quantify this. What numbers or measurements are involved? What's the data?",
	}

	if suggestion, ok := suggestions[intType]; ok {
		return suggestion
	}
	return "That's a bit abstract. Can you describe something you can touch, see, hear, or measure? Something concrete from your experience?"
}

// getFirstWhyPrompt starts the why-chain
func (e *Engine) getFirstWhyPrompt(anchor string, profile UserProfile) string {
	return fmt.Sprintf("Great observation! Now, WHY does this happen? What causes %s?", anchor)
}

// getNextWhyPrompt continues the why-chain deeper
func (e *Engine) getNextWhyPrompt(previousAnswer string, depth int, profile UserProfile) string {
	// Vary the phrasing to avoid repetition
	prompts := []string{
		"Interesting! But WHY does that happen?",
		"Good! Now what CONTROLS that?",
		"What's the mechanism behind this?",
		"What would happen if you changed that?",
		"What's happening at a deeper level?",
		"What's the underlying cause?",
	}

	idx := depth % len(prompts)
	return prompts[idx]
}

// getFirstSynthesisPrompt starts the synthesis phase
func (e *Engine) getFirstSynthesisPrompt(anchor, lastWhy string, profile UserProfile) string {
	return fmt.Sprintf("Excellent! You've discovered something fundamental. "+
		"Now, where ELSE have you seen this pattern? What other things work the same way as %s?", anchor)
}

// getSynthesisPrompt continues synthesis
func (e *Engine) getSynthesisPrompt(msg string, profile UserProfile) string {
	prompts := []string{
		"What else works this way?",
		"What does this remind you of?",
		"In what other areas might this principle apply?",
		"What existing knowledge does this connect to?",
	}
	return prompts[0] // Can randomize if needed
}

// getFormalizationIntro introduces Lean
func (e *Engine) getFormalizationIntro(profile UserProfile) string {
	// Adapt based on intelligence type
	intType := profile.DominantIntelligence

	intros := map[IntelligenceType]string{
		IntKinesthetic: "You've made a real discovery! Let's write it as a formula - like a recipe that anyone can follow. This is called Lean.",
		IntVisual:      "Amazing! Let's draw this as a precise blueprint - that's what Lean is, a language for exact specifications.",
		IntSpatial:     "Brilliant! Let's map this precisely - like coordinates for your idea. That's what Lean does.",
		IntLogical:     "Excellent work! Now let's formalize this in Lean - a logic system with zero ambiguity.",
		IntLinguistic:  "Beautiful insight! Let's express this in Lean - it's like poetry where every word matters.",
	}

	if intro, ok := intros[intType]; ok {
		return intro
	}
	return "You've discovered something real! Let's write it in a language that makes it formal and shareable. This is called Lean - a way to express truth precisely."
}

// presentLeanCode presents Lean theorem with explanation
func (e *Engine) presentLeanCode(leanCode string, profile UserProfile) string {
	return fmt.Sprintf("Here's your discovery in Lean:\n\n```lean\n%s\n```\n\n"+
		"See that? The '∀' means 'for all' - universal truth. "+
		"The '→' means 'implies' - if this, then that. "+
		"Your observation is now a formal theorem! You're doing real science! 🎉",
		leanCode)
}

// getCelebrationMessage celebrates the user's discovery
func (e *Engine) getCelebrationMessage(profile UserProfile, insights []Insight) string {
	insightCount := len(insights)
	if insightCount == 0 {
		return "Thank you for exploring with me! Come back anytime you notice something interesting. " +
			"Remember: you're a scientist every day - you just need to notice and ask why! 🌱"
	}

	// Personalize based on dominant intelligence
	intType := profile.DominantIntelligence
	celebrations := map[IntelligenceType]string{
		IntKinesthetic: "🎉 You just did what physicists do! Your hands and body taught you real science!",
		IntVisual:      "🎉 You just discovered this through observation! Artists and scientists both see patterns!",
		IntSpatial:     "🎉 You just mapped real knowledge! Architects and mathematicians think the same way!",
		IntLogical:     "🎉 You just formalized real truth! That's exactly what researchers do!",
		IntLinguistic:  "🎉 You just articulated deep insight! Poets and scientists both find truth!",
	}

	celebration := celebrations[intType]
	if celebration == "" {
		celebration = "🎉 You just did real science!"
	}

	return fmt.Sprintf("%s\n\nYou discovered %d insight(s) today:\n%s\n\n"+
		"Your observations can change the world. This is research sovereignty - "+
		"you discovered this yourself! Want to explore more?",
		celebration, insightCount, e.summarizeInsights(insights))
}

// summarizeInsights creates summary of insights
func (e *Engine) summarizeInsights(insights []Insight) string {
	var summary strings.Builder
	for i, insight := range insights {
		summary.WriteString(fmt.Sprintf("%d. %s (connected to: %s)\n",
			i+1, insight.Description, strings.Join(insight.Connections, ", ")))
	}
	return summary.String()
}

// generateSimpleLeanTheorem generates basic theorem structure (fallback)
func (e *Engine) generateSimpleLeanTheorem(conv *Conversation) string {
	anchor := conv.Anchor
	if anchor == "" {
		anchor = "observation"
	}

	// Simple template
	return fmt.Sprintf(`theorem discovery_theorem :
  ∀ (observation : Observation),
  is_concrete observation →
  has_mechanism observation →
  ∃ (insight : Insight),
  validates insight observation :=
begin
  -- Your observation: %s
  -- This connects fundamental principles to everyday experience
  -- You discovered this through careful observation and reasoning!
  sorry  -- Proof to be completed
end`, anchor)
}
