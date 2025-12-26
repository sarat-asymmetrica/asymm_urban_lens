package i18n

import (
	"math/rand"
	"strings"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// GREETINGS - CULTURALLY-AWARE BY TIME OF DAY
// ═══════════════════════════════════════════════════════════════════════════

// TimeOfDay represents different times for appropriate greetings
type TimeOfDay string

const (
	Morning   TimeOfDay = "morning"   // 5 AM - 12 PM
	Afternoon TimeOfDay = "afternoon" // 12 PM - 5 PM
	Evening   TimeOfDay = "evening"   // 5 PM - 9 PM
	Night     TimeOfDay = "night"     // 9 PM - 5 AM
)

// Greetings maps language -> time of day -> greetings
var Greetings = map[string]map[TimeOfDay][]string{
	"en": {
		Morning:   {"Good morning!", "Morning!", "Hey, good morning!", "Rise and shine!"},
		Afternoon: {"Good afternoon!", "Hello!", "Hi there!", "Hey!"},
		Evening:   {"Good evening!", "Evening!", "Hey there!", "Hello!"},
		Night:     {"Good evening!", "Hey!", "Hi there!", "Hello!"},
	},
	"te": {
		Morning:   {"శుభోదయం!", "నమస్కారం!", "ఉదయాన్నే స్వాగతం!", "మంచి ఉదయం!"},
		Afternoon: {"నమస్కారం!", "మధ్యాహ్నం శుభం!", "బాగున్నారా?"},
		Evening:   {"శుభ సాయంత్రం!", "నమస్కారం!", "సాయంత్రం శుభం!"},
		Night:     {"శుభ రాత్రి!", "నమస్కారం!", "రాత్రి శుభం!"},
	},
	"hi": {
		Morning:   {"सुप्रभात!", "नमस्ते!", "शुभ प्रभात!", "सुबह की नमस्ते!"},
		Afternoon: {"नमस्ते!", "शुभ दोपहर!", "आदाब!"},
		Evening:   {"शुभ संध्या!", "नमस्ते!", "संध्या की नमस्ते!"},
		Night:     {"शुभ रात्रि!", "नमस्ते!", "रात्रि की नमस्ते!"},
	},
	"es": {
		Morning:   {"¡Buenos días!", "¡Buen día!", "¡Hola, buenos días!", "¡Feliz mañana!"},
		Afternoon: {"¡Buenas tardes!", "¡Hola!", "¡Qué tal!", "¡Saludos!"},
		Evening:   {"¡Buenas noches!", "¡Buenas tardes!", "¡Hola!", "¡Saludos!"},
		Night:     {"¡Buenas noches!", "¡Hola!", "¡Saludos!"},
	},
	"yo": {
		Morning:   {"Ẹ ku ojumo!", "Ẹ kaabo!", "Ẹ ku ìsẹ́!", "Eku owuro!"},
		Afternoon: {"Ẹ ku ọsan!", "Ẹ n lẹ!", "Ẹ kaabo!", "Bawo ni?"},
		Evening:   {"Ẹ ku irọlẹ!", "Ẹ kaabo!", "Ẹ ku alẹ!"},
		Night:     {"O da aro!", "Ẹ kaabo!", "Sun re o!"},
	},
	"fr": {
		Morning:   {"Bonjour!", "Bon matin!", "Salut, bonjour!", "Bonne matinée!"},
		Afternoon: {"Bon après-midi!", "Bonjour!", "Salut!", "Ça va?"},
		Evening:   {"Bonsoir!", "Bonne soirée!", "Salut!", "Bonjour!"},
		Night:     {"Bonsoir!", "Bonne nuit!", "Salut!"},
	},
	"ar": {
		Morning:   {"!صباح الخير", "!السلام عليكم", "!صباح النور", "!مرحبا بك"},
		Afternoon: {"!السلام عليكم", "!مساء الخير", "!مرحبا", "!أهلا"},
		Evening:   {"!مساء الخير", "!السلام عليكم", "!مساء النور"},
		Night:     {"!تصبح على خير", "!السلام عليكم", "!مساء الخير"},
	},
	"sw": {
		Morning:   {"Habari za asubuhi!", "Jambo!", "Shikamoo!", "Habari yako?"},
		Afternoon: {"Habari za mchana!", "Jambo!", "Mambo!", "Habari?"},
		Evening:   {"Habari za jioni!", "Jambo!", "Mambo!", "Salamu!"},
		Night:     {"Usiku mwema!", "Jambo!", "Lala salama!"},
	},
	"ur": {
		Morning:   {"!صبح بخیر", "!السلام علیکم", "!صبح بخیر", "!خوش آمدید"},
		Afternoon: {"!السلام علیکم", "!دوپہر بخیر", "!ہیلو", "!آداب"},
		Evening:   {"!شام بخیر", "!السلام علیکم", "!شام مبارک"},
		Night:     {"!شب بخیر", "!السلام علیکم", "!رات بخیر"},
	},
	"ta": {
		Morning:   {"காலை வணக்கம்!", "வணக்கம்!", "நல்ல காலை!", "காலை வாழ்த்துக்கள்!"},
		Afternoon: {"வணக்கம்!", "மதிய வணக்கம்!", "எப்படி இருக்கீங்க?"},
		Evening:   {"மாலை வணக்கம்!", "வணக்கம்!", "மாலை வாழ்த்துக்கள்!"},
		Night:     {"இரவு வணக்கம்!", "வணக்கம்!", "இனிய இரவு!"},
	},
	"kn": {
		Morning:   {"ಶುಭೋದಯ!", "ನಮಸ್ಕಾರ!", "ಮುಂಜಾನೆ ನಮಸ್ಕಾರ!", "ಒಳ್ಳೆಯ ಬೆಳಿಗ್ಗೆ!"},
		Afternoon: {"ನಮಸ್ಕಾರ!", "ಮಧ್ಯಾಹ್ನ ನಮಸ್ಕಾರ!", "ಹೇಗಿದ್ದೀರಿ?"},
		Evening:   {"ಶುಭ ಸಂಜೆ!", "ನಮಸ್ಕಾರ!", "ಸಂಜೆ ನಮಸ್ಕಾರ!"},
		Night:     {"ಶುಭ ರಾತ್ರಿ!", "ನಮಸ್ಕಾರ!", "ರಾತ್ರಿ ನಮಸ್ಕಾರ!"},
	},
	"mr": {
		Morning:   {"शुभ प्रभात!", "नमस्कार!", "सकाळी नमस्कार!", "सुप्रभात!"},
		Afternoon: {"नमस्कार!", "दुपारी नमस्कार!", "कसे आहात?"},
		Evening:   {"शुभ संध्याकाळ!", "नमस्कार!", "संध्याकाळी नमस्कार!"},
		Night:     {"शुभ रात्री!", "नमस्कार!", "रात्री नमस्कार!"},
	},
}

// CasualGreetings for informal contexts
var CasualGreetings = map[string][]string{
	"en": {"Hey!", "Hi!", "What's up?", "Yo!", "Howdy!", "Sup?"},
	"te": {"ఏమిటండి!", "బాగున్నారా?", "ఏం కబురు?", "చెప్పండి!"},
	"hi": {"क्या हाल है?", "कैसे हो?", "सुनाओ!", "क्या चल रहा है?"},
	"es": {"¡Qué tal!", "¿Cómo estás?", "¿Qué onda?", "¡Hola!"},
	"yo": {"Bawo ni?", "Ṣe daadaa ni?", "Kí lọ ṣẹlẹ?"},
	"fr": {"Salut!", "Ça va?", "Quoi de neuf?", "Comment ça va?"},
	"ar": {"كيف الحال؟", "شو أخبارك؟", "شلونك؟", "!مرحبا"},
	"sw": {"Mambo vipi?", "Habari gani?", "Poa?", "Vipi?"},
	"ur": {"کیا حال ہے؟", "کیسے ہو؟", "سناؤ!", "کیا چل رہا ہے؟"},
	"ta": {"எப்படி இருக்கே?", "என்ன விசேஷம்?", "எப்படி போகுது?"},
	"kn": {"ಹೇಗಿದ್ದೀರಿ?", "ಏನು ವಿಶೇಷ?", "ಹೇಗೆ ಇದೆ?"},
	"mr": {"कसे आहात?", "काय चालू आहे?", "काय विशेष?"},
}

// FormalGreetings for professional/academic contexts
var FormalGreetings = map[string][]string{
	"en": {"Good day.", "Greetings.", "Welcome.", "Hello."},
	"te": {"స్వాగతం.", "నమస్కారం.", "శుభాకాంక్షలు."},
	"hi": {"स्वागत है.", "नमस्ते.", "आदाब.", "शुभकामनाएं."},
	"es": {"Bienvenido.", "Saludos cordiales.", "Buenos días."},
	"yo": {"Ẹ kaabo.", "Ẹ ku alẹ.", "Mo kí yin."},
	"fr": {"Bienvenue.", "Mes salutations.", "Bonjour."},
	"ar": {".مرحبا بك", ".تحياتي", ".السلام عليكم"},
	"sw": {"Karibu.", "Salamu.", "Heshima."},
	"ur": {".خوش آمدید", ".سلام", ".آداب عرض ہے"},
	"ta": {"வரவேற்கிறோம்.", "வணக்கம்.", "நல்வரவு."},
	"kn": {"ಸ್ವಾಗತ.", "ನಮಸ್ಕಾರ.", "ಸುಸ್ವಾಗತ."},
	"mr": {"स्वागत आहे.", "नमस्कार.", "शुभेच्छा."},
}

// ═══════════════════════════════════════════════════════════════════════════
// GREETING FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// GetGreeting returns a culturally-appropriate greeting
func GetGreeting(langCode string, timeOfDay TimeOfDay) string {
	// Get greetings for this language
	langGreetings, exists := Greetings[langCode]
	if !exists {
		langGreetings = Greetings["en"] // Fallback to English
	}

	// Get greetings for this time of day
	timeGreetings, exists := langGreetings[timeOfDay]
	if !exists || len(timeGreetings) == 0 {
		timeGreetings = langGreetings[Morning] // Fallback to morning
	}

	// Return random greeting from list
	if len(timeGreetings) > 0 {
		return timeGreetings[rand.Intn(len(timeGreetings))]
	}

	return "Hello!" // Ultimate fallback
}

// GetCasualGreeting returns a casual/informal greeting
func GetCasualGreeting(langCode string) string {
	greetings, exists := CasualGreetings[langCode]
	if !exists || len(greetings) == 0 {
		greetings = CasualGreetings["en"]
	}
	return greetings[rand.Intn(len(greetings))]
}

// GetFormalGreeting returns a formal/professional greeting
func GetFormalGreeting(langCode string) string {
	greetings, exists := FormalGreetings[langCode]
	if !exists || len(greetings) == 0 {
		greetings = FormalGreetings["en"]
	}
	return greetings[rand.Intn(len(greetings))]
}

// GetTimeOfDay determines time of day from current time
func GetTimeOfDay() TimeOfDay {
	hour := time.Now().Hour()

	switch {
	case hour >= 5 && hour < 12:
		return Morning
	case hour >= 12 && hour < 17:
		return Afternoon
	case hour >= 17 && hour < 21:
		return Evening
	default:
		return Night
	}
}

// GetContextualGreeting returns a greeting based on context
// context can be: "casual", "formal", or "" for time-based
func GetContextualGreeting(langCode string, context string) string {
	context = strings.ToLower(context)

	switch context {
	case "casual", "informal":
		return GetCasualGreeting(langCode)
	case "formal", "professional", "academic":
		return GetFormalGreeting(langCode)
	default:
		return GetGreeting(langCode, GetTimeOfDay())
	}
}

// GetAllGreetings returns all greetings for a language (for testing/display)
func GetAllGreetings(langCode string) map[string][]string {
	result := make(map[string][]string)

	// Time-based greetings
	if langGreetings, exists := Greetings[langCode]; exists {
		for timeOfDay, greetings := range langGreetings {
			result[string(timeOfDay)] = greetings
		}
	}

	// Casual greetings
	if casual, exists := CasualGreetings[langCode]; exists {
		result["casual"] = casual
	}

	// Formal greetings
	if formal, exists := FormalGreetings[langCode]; exists {
		result["formal"] = formal
	}

	return result
}
