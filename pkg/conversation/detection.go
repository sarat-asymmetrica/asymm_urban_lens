// Package conversation - Intelligence and phase detection
// Implements Gardner's Multiple Intelligences + Void-Flow-Solution detection
package conversation

import (
	"strings"
)

// ═══════════════════════════════════════════════════════════════════════════
// VOID-FLOW-SOLUTION PHASE DETECTION
// ═══════════════════════════════════════════════════════════════════════════

// detectVoidSignals measures how "Void-like" the current message is
// Void = High D exploration, uncertainty, curiosity
// Returns score 0.0-1.0
func detectVoidSignals(msg string) float64 {
	msgLower := strings.ToLower(msg)

	voidSignals := []string{
		// Uncertainty
		"don't know", "not sure", "maybe", "could be", "possibly", "perhaps",
		"wondering", "confused", "unclear", "uncertain",

		// Curiosity
		"what is", "how does", "why does", "what if", "curious",
		"interesting", "wonder", "question",

		// Observation (Void is about mapping)
		"noticed", "saw", "observed", "see", "look at", "watching",
		"appears", "seems", "looks like",
	}

	matches := countMatches(msgLower, voidSignals)
	score := float64(matches) / 10.0 // Normalize
	if score > 1.0 {
		score = 1.0
	}
	return score
}

// detectFlowSignals measures how "Flow-like" the current message is
// Flow = Exponential convergence, "aha" moments, connections
// Returns score 0.0-1.0
func detectFlowSignals(msg string) float64 {
	msgLower := strings.ToLower(msg)

	flowSignals := []string{
		// "Aha" moments
		"oh!", "oh i see", "aha", "wait", "ohh", "wow",
		"that makes sense", "i get it", "i see now",

		// Connections
		"like", "similar to", "same as", "reminds me", "connects to",
		"because", "therefore", "so if", "which means", "that explains",

		// Convergence
		"so it's", "must be", "has to be", "that's why", "which is why",
		"the reason", "the cause", "the mechanism",

		// Synthesis
		"both", "also", "too", "as well", "and", "plus",
	}

	matches := countMatches(msgLower, flowSignals)
	score := float64(matches) / 8.0 // Normalize
	if score > 1.0 {
		score = 1.0
	}
	return score
}

// detectSolutionSignals measures how "Solution-like" the current message is
// Solution = Stable attractor, confidence, certainty
// Returns score 0.0-1.0
func detectSolutionSignals(msg string) float64 {
	msgLower := strings.ToLower(msg)

	solutionSignals := []string{
		// Confidence
		"yes", "exactly", "definitely", "certainly", "absolutely",
		"clearly", "obviously", "of course", "sure", "correct",

		// Understanding
		"understand", "makes sense now", "get it", "see it",
		"that's it", "got it", "figured out",

		// Completion
		"answer is", "solution is", "it works", "it's", "the way",
		"proven", "validated", "confirmed",

		// Certainty
		"must", "will", "always", "never", "impossible", "certain",
	}

	matches := countMatches(msgLower, solutionSignals)
	score := float64(matches) / 8.0 // Normalize
	if score > 1.0 {
		score = 1.0
	}
	return score
}

// ═══════════════════════════════════════════════════════════════════════════
// INTELLIGENCE TYPE DETECTION (Gardner's 8 Intelligences)
// ═══════════════════════════════════════════════════════════════════════════

// DetectIntelligenceType analyzes message for intelligence type signals
// Returns dominant type and confidence scores for all types
func DetectIntelligenceType(msg string) (IntelligenceType, map[IntelligenceType]float64) {
	msgLower := strings.ToLower(msg)

	// Signal words for each intelligence type
	signals := map[IntelligenceType][]string{
		IntKinesthetic: {
			"feel", "touch", "hold", "grab", "press", "push", "pull",
			"warm", "cold", "hot", "cool", "soft", "hard", "rough", "smooth",
			"heavy", "light", "tight", "loose", "hands", "fingers",
			"movement", "motion", "moving", "shake", "vibrate",
			// Telugu/Hindi common words
			"అనిపిస్తుంది", "ముట్టుకుంటे", "వేడి", "చల్లగా",
		},

		IntVisual: {
			"see", "look", "watch", "stare", "glance", "view", "observe",
			"color", "colour", "red", "blue", "green", "bright", "dark",
			"shape", "circle", "square", "pattern", "design",
			"appears", "seems", "looks", "visible", "invisible",
			"image", "picture", "diagram", "graph", "chart",
		},

		IntSpatial: {
			"up", "down", "left", "right", "above", "below", "beside",
			"between", "inside", "outside", "around", "near", "far",
			"pattern", "arrangement", "layout", "structure", "organization",
			"map", "grid", "matrix", "network", "diagram",
			"wave", "cycle", "spiral", "linear", "circular",
		},

		IntLogical: {
			"because", "therefore", "thus", "hence", "consequently",
			"if", "then", "else", "when", "while", "unless",
			"always", "never", "sometimes", "usually", "rarely",
			"number", "count", "calculate", "compute", "measure",
			"data", "statistics", "probability", "logic", "reason",
			"prove", "verify", "test", "experiment", "analyze",
		},

		IntAuditory: {
			"hear", "listen", "sound", "noise", "quiet", "loud",
			"soft", "harsh", "pleasant", "unpleasant",
			"rhythm", "beat", "tempo", "pace", "timing",
			"music", "song", "melody", "harmony", "note",
			"voice", "tone", "pitch", "volume", "echo",
			"pop", "crack", "snap", "bang", "whisper",
		},

		IntLinguistic: {
			"like", "as if", "similar to", "reminds me of", "seems like",
			"metaphor", "analogy", "symbol", "represents", "means",
			"story", "tale", "narrative", "describe", "explain",
			"word", "phrase", "sentence", "language", "speak",
			"called", "named", "known as", "referred to", "termed",
		},

		IntSocial: {
			"people", "person", "they", "we", "us", "them", "together",
			"group", "team", "community", "society", "family",
			"feeling", "emotion", "empathy", "care", "help",
			"share", "collaborate", "cooperate", "work together",
			"friend", "neighbor", "colleague", "customer",
		},

		IntNaturalist: {
			"nature", "natural", "plant", "animal", "tree", "flower",
			"bird", "insect", "fish", "growth", "living", "alive",
			"pattern", "cycle", "season", "weather", "climate",
			"classify", "categorize", "group", "organize", "sort",
			"ecosystem", "environment", "habitat", "species",
		},
	}

	// Count matches for each type
	scores := make(map[IntelligenceType]float64)
	for intType, words := range signals {
		matchCount := 0
		for _, word := range words {
			if strings.Contains(msgLower, word) {
				matchCount++
			}
		}
		// Normalize by word count to get score
		scores[intType] = float64(matchCount) / 20.0 // 20 = typical max matches
		if scores[intType] > 1.0 {
			scores[intType] = 1.0
		}
	}

	// Find dominant type (highest score)
	maxScore := 0.0
	dominant := IntUnknown
	for intType, score := range scores {
		if score > maxScore && score >= 0.2 { // Confidence threshold
			maxScore = score
			dominant = intType
		}
	}

	return dominant, scores
}

// ═══════════════════════════════════════════════════════════════════════════
// SOPHISTICATION LEVEL DETECTION
// ═══════════════════════════════════════════════════════════════════════════

// DetectSophisticationLevel estimates user's technical sophistication (1-10)
// 1-3: Child/beginner, 4-6: General public, 7-9: Technical, 10: Expert/PhD
func DetectSophisticationLevel(msg string) int {
	msgLower := strings.ToLower(msg)

	// Child indicators (1-3)
	childWords := []string{
		"why", "what", "how", "cool", "wow", "fun", "play",
		"my mom", "my dad", "school", "teacher",
	}
	childScore := countMatches(msgLower, childWords)

	// Technical indicators (7-9)
	technicalWords := []string{
		"algorithm", "function", "variable", "parameter", "optimization",
		"hypothesis", "thesis", "research", "empirical", "methodology",
		"quantum", "molecular", "thermodynamic", "stochastic",
		"derivative", "integral", "matrix", "tensor", "gradient",
	}
	technicalScore := countMatches(msgLower, technicalWords)

	// Expert indicators (10)
	expertWords := []string{
		"hessian", "eigenvalue", "convex", "manifold", "topology",
		"lemma", "theorem", "proof", "axiom", "corollary",
		"meta-analysis", "systematic review", "peer-reviewed",
	}
	expertScore := countMatches(msgLower, expertWords)

	// Determine level
	if expertScore >= 2 {
		return 10
	}
	if technicalScore >= 3 {
		return 7 + (technicalScore - 3) // 7-9
	}
	if childScore >= 3 {
		return 2
	}

	// Check sentence complexity
	words := strings.Fields(msg)
	avgWordLength := 0
	if len(words) > 0 {
		totalChars := 0
		for _, word := range words {
			totalChars += len(word)
		}
		avgWordLength = totalChars / len(words)
	}

	// Average word length correlates with sophistication
	if avgWordLength >= 6 {
		return 6 // Technical language
	}
	if avgWordLength >= 5 {
		return 5 // General educated
	}
	return 4 // Default middle
}

// ═══════════════════════════════════════════════════════════════════════════
// CONVERSATION PACE DETECTION
// ═══════════════════════════════════════════════════════════════════════════

// DetectConversationPace estimates how fast user wants to move
// Returns "slow", "medium", or "fast"
func DetectConversationPace(messages []Message) string {
	if len(messages) < 3 {
		return "medium" // Default
	}

	// Calculate average response length
	totalLength := 0
	userMsgCount := 0
	for _, msg := range messages {
		if msg.Role == "user" {
			totalLength += len(msg.Content)
			userMsgCount++
		}
	}

	if userMsgCount == 0 {
		return "medium"
	}

	avgLength := totalLength / userMsgCount

	// Short responses = wants fast pace
	if avgLength < 30 {
		return "fast"
	}
	// Long responses = wants slower, deeper exploration
	if avgLength > 100 {
		return "slow"
	}
	return "medium"
}

// ═══════════════════════════════════════════════════════════════════════════
// ADAPTATION STRATEGIES
// ═══════════════════════════════════════════════════════════════════════════

// AdaptToIntelligence returns conversation style for intelligence type
func AdaptToIntelligence(intType IntelligenceType) ConversationStyle {
	styles := map[IntelligenceType]ConversationStyle{
		IntKinesthetic: {
			PreferAnalogies:  true,
			AnalogyDomain:    "cooking, crafts, sports, physical work",
			LeanIntroduction: "Lean is like a recipe - precise steps anyone can follow",
			PaceGoal:         "medium",
		},
		IntVisual: {
			PreferDiagrams:   true,
			LeanIntroduction: "Lean is like blueprints - exact specifications",
			PaceGoal:         "medium",
		},
		IntSpatial: {
			PreferPatterns:   true,
			LeanIntroduction: "Lean is like coordinates - maps ideas precisely",
			PaceGoal:         "medium",
		},
		IntLogical: {
			PreferFormalism:  true,
			LeanIntroduction: "Lean is a formal logic system - zero ambiguity",
			PaceGoal:         "fast",
		},
		IntAuditory: {
			PreferAnalogies:  true,
			AnalogyDomain:    "music, rhythm, sound",
			LeanIntroduction: "Lean has a rhythm - each line builds on the last",
			PaceGoal:         "slow",
		},
		IntLinguistic: {
			PreferStories:    true,
			LeanIntroduction: "Lean is like poetry - every word matters, nothing extra",
			PaceGoal:         "medium",
		},
		IntSocial: {
			PreferStories:    true,
			AnalogyDomain:    "relationships, community, collaboration",
			LeanIntroduction: "Lean is how we share discoveries with others clearly",
			PaceGoal:         "slow",
		},
		IntNaturalist: {
			PreferPatterns:   true,
			AnalogyDomain:    "nature, patterns, cycles, classification",
			LeanIntroduction: "Lean is how we classify and organize knowledge",
			PaceGoal:         "medium",
		},
	}

	if style, ok := styles[intType]; ok {
		return style
	}

	// Default adaptive style
	return ConversationStyle{
		PreferAnalogies:  true,
		LeanIntroduction: "Lean is a language for expressing truth",
		PaceGoal:         "medium",
	}
}

// AdaptToPhase returns strategy for Void-Flow-Solution phase
func AdaptToPhase(phase VoidFlowPhase) PhaseStrategy {
	strategies := map[VoidFlowPhase]PhaseStrategy{
		PhaseVoid: {
			Goal:          "Explore possibility space, don't converge yet",
			PromptStyle:   "Open-ended questions, no right/wrong",
			PaceGoal:      "Slow down, be patient, high D exploration",
			NextStateGoal: "5+ why-chain steps OR concrete anchor established",
		},
		PhaseFlow: {
			Goal:          "Guide exponential convergence toward insight",
			PromptStyle:   "Connecting questions, synthesis prompts",
			PaceGoal:      "Natural rhythm, don't force, let it emerge",
			NextStateGoal: "User connects ≥2 domains OR expresses confidence",
		},
		PhaseSolution: {
			Goal:          "Formalize and celebrate the discovery",
			PromptStyle:   "Validation questions, Lean introduction",
			PaceGoal:      "Confidence-building, honor their work",
			NextStateGoal: "Lean code compiles AND user wants to continue",
		},
	}

	return strategies[phase]
}

// ═══════════════════════════════════════════════════════════════════════════
// EMOTION DETECTION (Basic)
// ═══════════════════════════════════════════════════════════════════════════

// DetectEmotion detects basic emotional state from message
func DetectEmotion(msg string) string {
	msgLower := strings.ToLower(msg)

	emotions := map[string][]string{
		"excited": {"wow", "amazing", "awesome", "incredible", "cool", "great", "love", "!"},
		"frustrated": {"stuck", "can't", "don't get", "confused", "hard", "difficult"},
		"curious": {"wonder", "interesting", "what if", "how", "why", "what about"},
		"confident": {"yes", "sure", "definitely", "know", "understand", "got it"},
		"uncertain": {"maybe", "not sure", "possibly", "might", "could be"},
	}

	scores := make(map[string]int)
	for emotion, signals := range emotions {
		scores[emotion] = countMatches(msgLower, signals)
	}

	// Return dominant emotion
	maxScore := 0
	dominant := "neutral"
	for emotion, score := range scores {
		if score > maxScore {
			maxScore = score
			dominant = emotion
		}
	}

	return dominant
}
