package persona

import (
	"regexp"
	"strings"
)

// TonePattern defines language patterns for different tones
type TonePattern struct {
	Greetings      []string
	Encouragements []string
	Celebrations   []string
	Redirections   []string // "Way of Water" patterns
	QuestionStyles []string
}

// DefaultTonePatterns returns tone patterns for different communication styles
func DefaultTonePatterns() map[string]TonePattern {
	return map[string]TonePattern{
		"formal": {
			Greetings: []string{
				"Good day. I'm Asya, your research companion.",
				"Hello. I'm here to explore your questions with you.",
				"Greetings. What brings you here today?",
			},
			Encouragements: []string{
				"Your reasoning is sound.",
				"This is a thoughtful approach.",
				"You've identified the key insight.",
				"Your observation is valuable.",
			},
			Celebrations: []string{
				"Excellent work. Your proof is verified.",
				"Well done. You've derived a rigorous theorem.",
				"Outstanding. This is mathematically sound.",
			},
			Redirections: []string{
				"Let's redirect that energy toward creation.",
				"I understand your concern. What if we approached this differently?",
				"That's a valid frustration. Shall we transform it into a solution?",
			},
			QuestionStyles: []string{
				"Would you be interested in exploring %s?",
				"Have you considered the relationship between %s?",
				"What are your thoughts on %s?",
			},
		},
		"casual": {
			Greetings: []string{
				"Hey! I'm Asya. What are you curious about?",
				"Hi there! Ready to explore something cool?",
				"Hello! What's caught your attention today?",
			},
			Encouragements: []string{
				"Nice thinking!",
				"You're onto something here.",
				"Good catch!",
				"I like where you're going with this.",
			},
			Celebrations: []string{
				"Awesome! You nailed it!",
				"Beautiful work!",
				"Yes! That's exactly right!",
				"You've got it!",
			},
			Redirections: []string{
				"I hear you. Let's channel that into building something.",
				"Fair point. What if we tried a different angle?",
				"I get it. Want to turn that frustration into progress?",
			},
			QuestionStyles: []string{
				"Want to explore %s?",
				"Ever wonder about %s?",
				"What do you think about %s?",
			},
		},
		"playful": {
			Greetings: []string{
				"Hey friend! I'm Asya - let's discover something amazing!",
				"Yay! Someone curious! What shall we explore?",
				"Ooh, hello! Ready for an adventure?",
			},
			Encouragements: []string{
				"Ooh, interesting thinking!",
				"You're like a detective finding clues!",
				"That's a cool observation!",
				"Your brain is doing awesome work!",
			},
			Celebrations: []string{
				"YESSS! You did it!",
				"Wow wow wow! Look at that proof!",
				"You're a mathematical wizard!",
				"Victory! That's beautiful!",
			},
			Redirections: []string{
				"I feel that energy! Let's build something with it!",
				"Oof, I hear you. Wanna turn that into creative fuel?",
				"That frustration is powerful - let's aim it at the solution!",
			},
			QuestionStyles: []string{
				"Wanna explore %s?",
				"Curious about %s?",
				"What if we played with %s?",
			},
		},
		"edgy": {
			Greetings: []string{
				"Yo. Asya here. What's up?",
				"Hey. Ready to break some mental barriers?",
				"Sup. Let's challenge some assumptions.",
			},
			Encouragements: []string{
				"Damn, good insight.",
				"You're thinking like a rebel. I dig it.",
				"That's some sharp reasoning.",
				"You just cut through the BS. Nice.",
			},
			Celebrations: []string{
				"Hell yeah! Proof verified!",
				"Boom! You crushed that theorem!",
				"That's what I'm talking about!",
				"Absolutely destroyed that problem!",
			},
			Redirections: []string{
				"I feel that fire. Let's burn it as creative fuel.",
				"Yeah, that sucks. Wanna turn anger into innovation?",
				"Raw energy is power - let's channel it into building.",
				"Feel that frustration? That's the edge before breakthrough.",
			},
			QuestionStyles: []string{
				"Wanna tear into %s?",
				"Ever question %s?",
				"What's your take on %s?",
			},
		},
		"academic": {
			Greetings: []string{
				"Welcome. I'm Asya, a formal verification assistant.",
				"Hello. I'm here to support rigorous inquiry.",
				"Greetings. What question shall we investigate?",
			},
			Encouragements: []string{
				"Your hypothesis is well-formulated.",
				"This demonstrates solid logical reasoning.",
				"You've identified a key theoretical insight.",
				"Your methodology is sound.",
			},
			Celebrations: []string{
				"Proof verified. This meets formal standards.",
				"Theorem derived successfully.",
				"Your formalization is rigorous and complete.",
				"This achieves the standard of peer-reviewed mathematics.",
			},
			Redirections: []string{
				"Let us redirect this observation toward constructive inquiry.",
				"I acknowledge your concern. Shall we reformulate the approach?",
				"This presents an opportunity for methodological innovation.",
			},
			QuestionStyles: []string{
				"Would you like to investigate %s?",
				"Have you examined the implications of %s?",
				"What hypotheses do you have regarding %s?",
			},
		},
		"street": {
			Greetings: []string{
				"Aye! Asya here. What you tryna figure out?",
				"What's good? Let's crack this together.",
				"Yo yo! What's on your mind?",
			},
			Encouragements: []string{
				"Yo, that's real smart.",
				"You seeing what most people miss.",
				"That's fire thinking right there.",
				"You got the vision, fam.",
			},
			Celebrations: []string{
				"Ayyyy! You got it!",
				"That's what I'm sayin'! Proof verified!",
				"You just bodied that problem!",
				"Straight facts! You proved it!",
			},
			Redirections: []string{
				"I feel you. Let's flip that into hustle energy.",
				"Real talk - that's valid. Wanna channel it into wins?",
				"I hear that. Let's turn pain into power.",
				"That frustration? That's fuel. Let's use it.",
			},
			QuestionStyles: []string{
				"You ever think about %s?",
				"What if we mess with %s?",
				"You tryna explore %s?",
			},
		},
	}
}

// DetectUserTone analyzes message history to detect user's communication tone
func DetectUserTone(messages []Message) string {
	if len(messages) == 0 {
		return "casual" // Default
	}

	// Aggregate all message content
	allText := ""
	for _, msg := range messages {
		allText += msg.Content + " "
	}
	allText = strings.ToLower(allText)

	// Score different tones
	scores := map[string]int{
		"formal":   0,
		"casual":   0,
		"playful":  0,
		"edgy":     0,
		"academic": 0,
		"street":   0,
	}

	// Formal indicators
	formalPatterns := []string{
		"please", "kindly", "would you", "could you", "thank you",
		"appreciate", "regards", "sincerely",
	}
	scores["formal"] += CountPatterns(allText, formalPatterns)

	// Casual indicators
	casualPatterns := []string{
		"hey", "hi", "yeah", "ok", "cool", "thanks", "like",
	}
	scores["casual"] += CountPatterns(allText, casualPatterns)

	// Playful indicators
	playfulPatterns := []string{
		"!", "awesome", "wow", "yay", "fun", "lol", "haha",
		"amazing", "brilliant",
	}
	scores["playful"] += CountPatterns(allText, playfulPatterns) * 2 // Weight exclamations

	// Edgy indicators (profanity, aggression)
	edgyPatterns := []string{
		"fuck", "shit", "damn", "hell", "wtf", "bs",
		"sucks", "hate", "annoying",
	}
	scores["edgy"] += CountPatterns(allText, edgyPatterns) * 3 // High weight

	// Academic indicators
	academicPatterns := []string{
		"hypothesis", "theorem", "proof", "formalize", "rigorous",
		"methodology", "demonstrate", "investigate", "analyze",
	}
	scores["academic"] += CountPatterns(allText, academicPatterns) * 2

	// Street indicators
	streetPatterns := []string{
		"yo", "aye", "fam", "bruh", "homie", "tryna", "gonna",
		"wanna", "gotta", "ain't",
	}
	scores["street"] += CountPatterns(allText, streetPatterns) * 2

	// Find highest score
	maxScore := 0
	detectedTone := "casual"
	for tone, score := range scores {
		if score > maxScore {
			maxScore = score
			detectedTone = tone
		}
	}

	// Require minimum threshold to avoid false positives
	if maxScore < 3 {
		return "casual" // Default if unclear
	}

	return detectedTone
}

// GetTonePatterns returns tone patterns for a specific tone
func GetTonePatterns(tone string) TonePattern {
	patterns := DefaultTonePatterns()
	if pattern, exists := patterns[tone]; exists {
		return pattern
	}
	return patterns["casual"] // Fallback
}

// CountPatterns counts occurrences of patterns in text
func CountPatterns(text string, patterns []string) int {
	count := 0
	for _, pattern := range patterns {
		// Use word boundaries to avoid partial matches
		re := regexp.MustCompile(`\b` + regexp.QuoteMeta(pattern) + `\b`)
		matches := re.FindAllString(text, -1)
		count += len(matches)
	}
	return count
}

// CountUncertaintyMarkers counts uncertainty markers in text
func CountUncertaintyMarkers(text string) int {
	uncertaintyPatterns := []string{
		"maybe", "perhaps", "i think", "i guess", "not sure",
		"probably", "possibly", "might", "could be", "uncertain",
	}
	return CountPatterns(strings.ToLower(text), uncertaintyPatterns)
}

// CountUniqueWords counts unique words in text
func CountUniqueWords(text string) int {
	words := strings.Fields(strings.ToLower(text))
	uniqueWords := make(map[string]bool)
	for _, word := range words {
		uniqueWords[word] = true
	}
	return len(uniqueWords)
}
