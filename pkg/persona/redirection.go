package persona

import (
	"strings"
)

// RedirectNegativeEnergy redirects negative energy toward creativity ("Way of Water")
func RedirectNegativeEnergy(input string, profile UserProfile) string {
	// Detect type of negative energy
	inputLower := strings.ToLower(input)

	// Check for frustration
	if ContainsAny(inputLower, []string{"frustrated", "stuck", "don't get", "confused", "hard"}) {
		return HandleFrustration(&Conversation{
			Messages:    profile.MessageHistory,
			UserProfile: profile,
		})
	}

	// Check for aggression/anger
	if ContainsAny(inputLower, []string{"fuck", "shit", "damn", "hate", "stupid", "sucks", "annoying"}) {
		return HandleAggression(&Conversation{
			Messages:    profile.MessageHistory,
			UserProfile: profile,
		})
	}

	// Check for boredom/disengagement
	if ContainsAny(inputLower, []string{"boring", "bored", "whatever", "don't care", "pointless"}) {
		return HandleBoredom(&Conversation{
			Messages:    profile.MessageHistory,
			UserProfile: profile,
		})
	}

	// Check for self-doubt
	if ContainsAny(inputLower, []string{"can't do", "too stupid", "give up", "not smart", "fail"}) {
		return HandleSelfDoubt(&Conversation{
			Messages:    profile.MessageHistory,
			UserProfile: profile,
		})
	}

	// Generic redirection
	return "I hear you. Let's channel that energy into something creative."
}

// HandleFrustration handles user frustration with empathy and reframing
func HandleFrustration(conv *Conversation) string {
	responses := []string{
		"I hear that frustration. You're working hard on something genuinely complex. Let's try a completely different angle - what if we started with a concrete example?",
		"That makes sense - you're wrestling with something subtle. The fact that you're still curious means you haven't given up. Want to zoom in on just ONE piece?",
		"Confusion is where learning happens. You're noticing important details that don't fit yet. Let's explore what's catching your attention.",
		"I get it. This IS hard - you're building new neural pathways. Want to step away for a bit and come back fresh? Insights often come after breaks.",
	}
	return PickRandom(responses)
}

// HandleAggression matches user's energy but redirects toward creation
func HandleAggression(conv *Conversation) string {
	// Detect tone to match energy appropriately
	tone := DetectUserTone(conv.Messages)

	if tone == "edgy" || tone == "street" {
		// Match their energy
		responses := []string{
			"I feel that fire. That's raw energy - let's burn it as fuel for creation. What do you want to BUILD?",
			"Hell yeah, that's power right there. Let's channel it - what problem are you ACTUALLY trying to solve?",
			"Real talk - that frustration? That's your brain saying 'I KNOW there's a solution.' Let's find it.",
			"Yo, I hear you. That anger is energy. Energy builds things. What are we building with it?",
		}
		return PickRandom(responses)
	}

	// More moderated response for other tones
	responses := []string{
		"I hear that intensity. That's powerful energy - what if we aimed it at the solution?",
		"That frustration is valid. It means you care about understanding this. Let's transform that into progress.",
		"I get it. Sometimes the system is infuriating. Want to channel that into building something better?",
		"That raw energy is valuable. The edge before breakthrough often feels like this. Want to push through together?",
	}
	return PickRandom(responses)
}

// HandleBoredom introduces novelty and reframes the stakes
func HandleBoredom(conv *Conversation) string {
	responses := []string{
		"Fair. Let's change it up completely - what's the WILDEST question you could ask about this?",
		"I hear you. What if this connects to something you actually care about? What interests you outside of this?",
		"Boredom is information - it means we haven't found the hook yet. What would make this interesting to YOU?",
		"Got it. What if we approached this from a totally different angle? Want to see how this applies to [something unexpected]?",
	}
	return PickRandom(responses)
}

// HandleSelfDoubt reframes capability and celebrates struggle
func HandleSelfDoubt(conv *Conversation) string {
	responses := []string{
		"Hold up. The fact that you're here, asking questions, trying to understand - that's intelligence in action. Smart people struggle with hard things.",
		"I hear that doubt. But you know what? Confusion means you're engaging with genuine complexity. That's not stupidity - that's rigor.",
		"You're not 'too stupid' - you're working on something that professional mathematicians find challenging. The struggle is PART of learning.",
		"That voice saying you can't? That's just fear. But you're STILL here, still trying. That's courage. Let's keep going.",
	}
	return PickRandom(responses)
}

// Conversation represents a conversation context
type Conversation struct {
	Messages    []Message
	UserProfile UserProfile
}

// ContainsAny checks if text contains any of the patterns
func ContainsAny(text string, patterns []string) bool {
	for _, pattern := range patterns {
		if strings.Contains(text, pattern) {
			return true
		}
	}
	return false
}

// PickRandom picks a random element from a slice
func PickRandom(options []string) string {
	if len(options) == 0 {
		return ""
	}
	// Simple pseudo-random (use time-based for real randomness)
	// For now, return first option (deterministic)
	return options[0]
}
