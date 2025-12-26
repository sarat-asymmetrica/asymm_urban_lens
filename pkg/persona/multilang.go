package persona

import (
	"strings"
)

// DetectLanguage detects the language of the input text
// Returns ISO 639-1 language code (e.g., "en", "hi", "es")
func DetectLanguage(text string) string {
	// Simple heuristic-based detection
	// In production, use a proper language detection library

	textLower := strings.ToLower(text)

	// Hindi detection (Devanagari script or common Hindi words in Latin script)
	if ContainsDevanagari(text) || ContainsAny(textLower, []string{
		"namaste", "dhanyavaad", "kaise", "kya", "hai", "hoon",
	}) {
		return "hi"
	}

	// Spanish detection
	if ContainsAny(textLower, []string{
		"hola", "gracias", "por favor", "buenos días", "qué",
		"cómo", "está", "soy", "¿", "¡",
	}) {
		return "es"
	}

	// French detection
	if ContainsAny(textLower, []string{
		"bonjour", "merci", "s'il vous plaît", "comment", "je suis",
		"où", "quand", "pourquoi",
	}) {
		return "fr"
	}

	// German detection
	if ContainsAny(textLower, []string{
		"guten tag", "danke", "bitte", "wie", "wo", "wann",
		"ich bin", "ß", "ä", "ö", "ü",
	}) {
		return "de"
	}

	// Yoruba detection (Nigerian language)
	if ContainsAny(textLower, []string{
		"bawo", "e ku", "se", "ṣe", "ẹ", "ọ",
	}) {
		return "yo"
	}

	// Default to English
	return "en"
}

// GetGreeting returns a greeting in the specified language and tone
func GetGreeting(lang string, tone string) string {
	greetings := map[string]map[string]string{
		"en": {
			"formal":   "Good day. I'm Asya, your research companion.",
			"casual":   "Hey! I'm Asya. What are you curious about?",
			"playful":  "Hey friend! I'm Asya - let's discover something amazing!",
			"edgy":     "Yo. Asya here. What's up?",
			"academic": "Welcome. I'm Asya, a formal verification assistant.",
			"street":   "Aye! Asya here. What you tryna figure out?",
		},
		"hi": {
			"formal":   "Namaste. Main Asya hoon, aapki research companion.",
			"casual":   "Namaste! Main Asya hoon. Aap kya jaanna chahte hain?",
			"playful":  "Namaste dost! Main Asya hoon - kuch amazing discover karein!",
			"edgy":     "Kya haal hai? Asya here. Kya chal raha hai?",
			"academic": "Namaste. Main Asya hoon, ek formal verification assistant.",
			"street":   "Aye! Asya here. Kya seekhna chahte ho?",
		},
		"es": {
			"formal":   "Buenos días. Soy Asya, tu compañera de investigación.",
			"casual":   "¡Hola! Soy Asya. ¿Qué te da curiosidad?",
			"playful":  "¡Hola amigo! Soy Asya - ¡descubramos algo increíble!",
			"edgy":     "Oye. Asya aquí. ¿Qué pasa?",
			"academic": "Bienvenido. Soy Asya, una asistente de verificación formal.",
			"street":   "¡Ey! Asya aquí. ¿Qué quieres aprender?",
		},
		"fr": {
			"formal":   "Bonjour. Je suis Asya, votre compagne de recherche.",
			"casual":   "Salut! Je suis Asya. Qu'est-ce qui vous intéresse?",
			"playful":  "Salut! Je suis Asya - découvrons quelque chose d'incroyable!",
			"edgy":     "Yo. Asya ici. Quoi de neuf?",
			"academic": "Bienvenue. Je suis Asya, une assistante de vérification formelle.",
			"street":   "Yo! Asya ici. Tu veux apprendre quoi?",
		},
		"de": {
			"formal":   "Guten Tag. Ich bin Asya, Ihre Forschungsbegleiterin.",
			"casual":   "Hallo! Ich bin Asya. Was interessiert dich?",
			"playful":  "Hallo Freund! Ich bin Asya - lass uns etwas Erstaunliches entdecken!",
			"edgy":     "Yo. Asya hier. Was geht?",
			"academic": "Willkommen. Ich bin Asya, eine formale Verifikationsassistentin.",
			"street":   "Ey! Asya hier. Was willst du lernen?",
		},
	}

	// Get language greetings
	langGreetings, exists := greetings[lang]
	if !exists {
		langGreetings = greetings["en"] // Fallback to English
	}

	// Get tone-specific greeting
	greeting, exists := langGreetings[tone]
	if !exists {
		greeting = langGreetings["casual"] // Fallback to casual
	}

	return greeting
}

// TranslateWithContext translates text with contextual awareness
// In production, use a proper translation API (Google Translate, DeepL, etc.)
func TranslateWithContext(text string, fromLang string, toLang string, context string) string {
	// Simple stub - in production, call translation API with context
	// Context helps disambiguate (e.g., "bat" = animal or sports equipment?)

	if fromLang == toLang {
		return text // No translation needed
	}

	// Stub: Return placeholder
	return text + " [Translation: " + fromLang + " → " + toLang + "]"
}

// ContainsDevanagari checks if text contains Devanagari script (Hindi, Sanskrit, Marathi, etc.)
func ContainsDevanagari(text string) bool {
	for _, r := range text {
		// Devanagari Unicode range: U+0900 to U+097F
		if r >= '\u0900' && r <= '\u097F' {
			return true
		}
	}
	return false
}

// GetMultilingualEncouragement returns encouragement in user's language
func GetMultilingualEncouragement(lang string, tone string) []string {
	encouragements := map[string]map[string][]string{
		"en": {
			"casual": {
				"Nice thinking!",
				"You're onto something here.",
				"Good catch!",
			},
			"edgy": {
				"Damn, good insight.",
				"You're thinking like a rebel. I dig it.",
				"That's some sharp reasoning.",
			},
		},
		"hi": {
			"casual": {
				"Badhiya soch!",
				"Aap sahi raah par hain.",
				"Accha observation!",
			},
			"edgy": {
				"Ekdum kadak insight!",
				"Ye toh ekdum tight reasoning hai.",
				"Zabardast thinking!",
			},
		},
		"es": {
			"casual": {
				"¡Buen pensamiento!",
				"Vas por buen camino.",
				"¡Buena observación!",
			},
			"edgy": {
				"Ese insight está brutal.",
				"Piensas como un rebelde. Me gusta.",
				"Ese razonamiento está afilado.",
			},
		},
	}

	// Get language encouragements
	langEncouragements, exists := encouragements[lang]
	if !exists {
		langEncouragements = encouragements["en"] // Fallback
	}

	// Get tone-specific encouragements
	toneEncouragements, exists := langEncouragements[tone]
	if !exists {
		toneEncouragements = langEncouragements["casual"] // Fallback
	}

	return toneEncouragements
}
