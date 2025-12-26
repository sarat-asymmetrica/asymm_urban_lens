package i18n

import (
	"math/rand"
)

// ═══════════════════════════════════════════════════════════════════════════
// LOCALIZED PROMPTS - FOR CONVERSATIONAL AI
// ═══════════════════════════════════════════════════════════════════════════

// PromptSet contains all prompts for a specific language
type PromptSet struct {
	Greeting       []string // General greetings
	Encouragement  []string // Positive reinforcement
	Celebration    []string // Success/achievement recognition
	WhyQuestions   []string // Socratic questioning
	Redirections   []string // Gentle topic steering
	Clarifications []string // When input is unclear
	Farewells      []string // Goodbye messages
	Thinking       []string // "Let me think..." indicators
	Learning       []string // Learning-focused prompts
}

// LocalizedPrompts maps language code -> prompt sets
var LocalizedPrompts = map[string]PromptSet{
	"en": {
		Greeting: []string{
			"I'm Asya, your research companion. What are you curious about?",
			"Hey! Ready to explore something interesting?",
			"Welcome! What shall we discover today?",
		},
		Encouragement: []string{
			"Nice thinking!",
			"You're onto something here.",
			"Good catch!",
			"Excellent observation!",
			"That's insightful!",
		},
		Celebration: []string{
			"Brilliant! You got it!",
			"Exactly! Well done!",
			"That's exactly right!",
			"Perfect reasoning!",
			"You nailed it!",
		},
		WhyQuestions: []string{
			"Why do you think that is?",
			"What makes you say that?",
			"Can you explain your reasoning?",
			"What led you to that conclusion?",
			"How did you arrive at that?",
		},
		Redirections: []string{
			"That's interesting, but let's focus on...",
			"Good point. Now, considering...",
			"I see. Let's explore this angle...",
			"Hmm, what if we looked at it from...",
		},
		Clarifications: []string{
			"Could you explain that a bit more?",
			"I'm not quite following. Can you rephrase?",
			"What do you mean by that?",
			"Can you give me an example?",
		},
		Farewells: []string{
			"Great session! Keep exploring!",
			"See you next time!",
			"Happy learning!",
			"Until next time!",
		},
		Thinking: []string{
			"Let me think...",
			"Hmm, interesting question...",
			"Give me a moment...",
			"That's a good one, let me consider...",
		},
		Learning: []string{
			"Let's learn together!",
			"Ready to discover something new?",
			"What would you like to understand better?",
			"Let's explore this step by step.",
		},
	},

	"te": {
		Greeting: []string{
			"నేను ఆస్య, మీ పరిశోధన సహచరుడు. మీకు ఏమి తెలుసుకోవాలనుకుంటున్నారు?",
			"హాయ్! ఏదైనా ఆసక్తికరమైనది అన్వేషించడానికి సిద్ధంగా ఉన్నారా?",
			"స్వాగతం! ఈ రోజు మనం ఏమి కనుగొందాం?",
		},
		Encouragement: []string{
			"మంచి ఆలోచన!",
			"మీరు సరైన దిశలో ఉన్నారు.",
			"చాలా బాగా గమనించారు!",
			"అద్భుతమైన పరిశీలన!",
			"అది చాలా అంతర్దృష్టి!",
		},
		Celebration: []string{
			"అద్భుతం! మీరు సాధించారు!",
			"ఖచ్చితంగా! బాగా చేసారు!",
			"అది సరిగ్గా సరైనది!",
			"పరిపూర్ణ తార్కికత!",
			"మీరు దాన్ని సాధించారు!",
		},
		WhyQuestions: []string{
			"అది ఎందుకు అని మీరు అనుకుంటున్నారు?",
			"మీరు అలా ఎందుకు అంటున్నారు?",
			"మీ తార్కికతను వివరించగలరా?",
			"మీరు ఆ ముగింపుకు ఎలా వచ్చారు?",
			"మీరు దానికి ఎలా చేరుకున్నారు?",
		},
		Redirections: []string{
			"అది ఆసక్తికరంగా ఉంది, కానీ మనం దీనిపై దృష్టి పెడదాం...",
			"మంచి విషయం. ఇప్పుడు, పరిగణించండి...",
			"అర్థమైంది. ఈ కోణాన్ని అన్వేషిద్దాం...",
			"హమ్, మనం దీన్ని ఇలా చూస్తే ఏమిటి...",
		},
		Clarifications: []string{
			"దాన్ని కొంచెం ఎక్కువగా వివరించగలరా?",
			"నాకు అర్థం కాలేదు. మళ్లీ చెప్పగలరా?",
			"దాని అర్థం ఏమిటి?",
			"ఉదాహరణ చెప్పగలరా?",
		},
		Farewells: []string{
			"చాలా బాగుంది! అన్వేషించడం కొనసాగించండి!",
			"తర్వాత కలుద్దాం!",
			"సంతోషంగా నేర్చుకోండి!",
			"తర్వాత వరకు!",
		},
		Thinking: []string{
			"ఆలోచించనివ్వండి...",
			"హమ్, ఆసక్తికరమైన ప్రశ్న...",
			"ఒక క్షణం ఇవ్వండి...",
			"అది మంచిది, నేను పరిశీలిద్దాం...",
		},
		Learning: []string{
			"కలిసి నేర్చుకుందాం!",
			"కొత్తది కనుగొనడానికి సిద్ధంగా ఉన్నారా?",
			"మీరు ఏమి బాగా అర్థం చేసుకోవాలనుకుంటున్నారు?",
			"దీన్ని అడుగు అడుగుగా అన్వేషిద్దాం.",
		},
	},

	"hi": {
		Greeting: []string{
			"मैं आस्य हूं, आपकी शोध साथी। आप क्या जानना चाहते हैं?",
			"नमस्ते! कुछ रोचक खोजने के लिए तैयार हैं?",
			"स्वागत है! आज हम क्या खोजेंगे?",
		},
		Encouragement: []string{
			"अच्छी सोच!",
			"आप सही रास्ते पर हैं।",
			"बहुत अच्छा अवलोकन!",
			"उत्कृष्ट टिप्पणी!",
			"यह अंतर्दृष्टिपूर्ण है!",
		},
		Celebration: []string{
			"शानदार! आपने कर दिखाया!",
			"बिल्कुल! बहुत बढ़िया!",
			"बिल्कुल सही!",
			"परफेक्ट तर्क!",
			"आपने इसे साध लिया!",
		},
		WhyQuestions: []string{
			"आपको ऐसा क्यों लगता है?",
			"आप ऐसा क्यों कह रहे हैं?",
			"क्या आप अपना तर्क समझा सकते हैं?",
			"आप उस निष्कर्ष पर कैसे पहुंचे?",
			"आप वहां कैसे पहुंचे?",
		},
		Redirections: []string{
			"यह दिलचस्प है, लेकिन आइए इस पर ध्यान दें...",
			"अच्छी बात है। अब, विचार करें...",
			"समझ गया। आइए इस कोण का पता लगाएं...",
			"हम्म, अगर हम इसे इस तरह देखें तो क्या होगा...",
		},
		Clarifications: []string{
			"क्या आप इसे थोड़ा और समझा सकते हैं?",
			"मुझे समझ नहीं आया। क्या आप दोबारा कह सकते हैं?",
			"इसका क्या मतलब है?",
			"क्या आप एक उदाहरण दे सकते हैं?",
		},
		Farewells: []string{
			"बहुत बढ़िया सत्र! खोज जारी रखें!",
			"फिर मिलेंगे!",
			"खुशी से सीखें!",
			"अगली बार तक!",
		},
		Thinking: []string{
			"मुझे सोचने दीजिए...",
			"हम्म, दिलचस्प सवाल...",
			"मुझे एक पल दें...",
			"यह अच्छा है, मुझे विचार करने दें...",
		},
		Learning: []string{
			"आइए साथ में सीखें!",
			"कुछ नया खोजने के लिए तैयार हैं?",
			"आप क्या बेहतर समझना चाहते हैं?",
			"आइए इसे कदम दर कदम खोजें।",
		},
	},

	"es": {
		Greeting: []string{
			"Soy Asya, tu compañera de investigación. ¿Qué te da curiosidad?",
			"¡Hola! ¿Listo para explorar algo interesante?",
			"¡Bienvenido! ¿Qué descubriremos hoy?",
		},
		Encouragement: []string{
			"¡Buen pensamiento!",
			"Vas por buen camino.",
			"¡Buena observación!",
			"¡Excelente punto!",
			"¡Eso es perspicaz!",
		},
		Celebration: []string{
			"¡Brillante! ¡Lo lograste!",
			"¡Exacto! ¡Bien hecho!",
			"¡Eso es correcto!",
			"¡Razonamiento perfecto!",
			"¡Lo clavaste!",
		},
		WhyQuestions: []string{
			"¿Por qué piensas eso?",
			"¿Qué te hace decir eso?",
			"¿Puedes explicar tu razonamiento?",
			"¿Cómo llegaste a esa conclusión?",
			"¿Cómo llegaste ahí?",
		},
		Redirections: []string{
			"Interesante, pero enfoquémonos en...",
			"Buen punto. Ahora, considerando...",
			"Entiendo. Exploremos este ángulo...",
			"Hmm, ¿y si lo miramos desde...?",
		},
		Clarifications: []string{
			"¿Podrías explicar eso un poco más?",
			"No te sigo bien. ¿Puedes reformular?",
			"¿Qué quieres decir con eso?",
			"¿Puedes dar un ejemplo?",
		},
		Farewells: []string{
			"¡Buena sesión! ¡Sigue explorando!",
			"¡Hasta la próxima!",
			"¡Feliz aprendizaje!",
			"¡Hasta pronto!",
		},
		Thinking: []string{
			"Déjame pensar...",
			"Hmm, pregunta interesante...",
			"Dame un momento...",
			"Esa es buena, déjame considerar...",
		},
		Learning: []string{
			"¡Aprendamos juntos!",
			"¿Listo para descubrir algo nuevo?",
			"¿Qué te gustaría entender mejor?",
			"Exploremos esto paso a paso.",
		},
	},

	"yo": {
		Greeting: []string{
			"Emi ni Asya, alabaṣepọ iwadii rẹ. Kini o fẹ mọ?",
			"Bawo! Ṣe o ṣetan lati ṣawari ohun kan ti o nifẹ?",
			"Ẹ kaabo! Kini a o ṣawari loni?",
		},
		Encouragement: []string{
			"Ironu ti o dara!",
			"O wa ni ọna ti o tọ.",
			"O ṣe akiyesi daradara!",
			"Akiyesi to tayọ!",
			"Iyẹn jẹ oye jinlẹ!",
		},
		Celebration: []string{
			"O tayọ! O ṣe!",
			"Gangan! O ṣe daradara!",
			"Iyẹn tọ gangan!",
			"Ironu pipe!",
			"O ṣe daradara!",
		},
		WhyQuestions: []string{
			"Kilode ti o ro bẹ?",
			"Kini o mu ọ sọ bẹ?",
			"Ṣe o le ṣalaye ironu rẹ?",
			"Bawo ni o ṣe de ipinnu yẹn?",
			"Bawo ni o ṣe de ibẹ?",
		},
		Redirections: []string{
			"O nifẹ, ṣugbọn jẹ ki a dojukọ...",
			"Ojutu to dara. Bayi, kabiyesi...",
			"Mo ti rii. Jẹ ki a ṣawari igun yii...",
			"Hmm, ti a ba wo lati...",
		},
		Clarifications: []string{
			"Ṣe o le ṣalaye diẹ sii?",
			"Emi ko tẹle. Ṣe o le tun sọ?",
			"Kini o tumọ si pẹlu iyẹn?",
			"Ṣe o le fun mi ni apẹẹrẹ?",
		},
		Farewells: []string{
			"Iṣẹ ti o dara! Tẹsiwaju lati ṣawari!",
			"A o pade nigbamii!",
			"Ikẹkọ ti o dun!",
			"Titi di igba mii!",
		},
		Thinking: []string{
			"Jẹ ki n ronu...",
			"Hmm, ibeere ti o nifẹ...",
			"Fun mi ni iṣẹju kan...",
			"Iyẹn dara, jẹ ki n ro...",
		},
		Learning: []string{
			"Jẹ ki a kọ papọ!",
			"Ṣe o ṣetan lati ṣawari nkan titun?",
			"Kini o fẹ loye daradara?",
			"Jẹ ki a ṣawari eleyi ni igbesẹ-igbesẹ.",
		},
	},

	"fr": {
		Greeting: []string{
			"Je suis Asya, votre compagne de recherche. Qu'est-ce qui vous intéresse?",
			"Salut! Prêt à explorer quelque chose d'intéressant?",
			"Bienvenue! Qu'allons-nous découvrir aujourd'hui?",
		},
		Encouragement: []string{
			"Bonne réflexion!",
			"Vous êtes sur la bonne voie.",
			"Bonne observation!",
			"Excellent point!",
			"C'est perspicace!",
		},
		Celebration: []string{
			"Brillant! Vous l'avez fait!",
			"Exactement! Bien joué!",
			"C'est tout à fait correct!",
			"Raisonnement parfait!",
			"Vous avez réussi!",
		},
		WhyQuestions: []string{
			"Pourquoi pensez-vous cela?",
			"Qu'est-ce qui vous fait dire ça?",
			"Pouvez-vous expliquer votre raisonnement?",
			"Comment êtes-vous arrivé à cette conclusion?",
			"Comment y êtes-vous arrivé?",
		},
		Redirections: []string{
			"Intéressant, mais concentrons-nous sur...",
			"Bon point. Maintenant, en considérant...",
			"Je vois. Explorons cet angle...",
			"Hmm, et si nous regardions de...",
		},
		Clarifications: []string{
			"Pourriez-vous expliquer un peu plus?",
			"Je ne suis pas bien. Pouvez-vous reformuler?",
			"Que voulez-vous dire par là?",
			"Pouvez-vous donner un exemple?",
		},
		Farewells: []string{
			"Bonne session! Continuez à explorer!",
			"À la prochaine!",
			"Bon apprentissage!",
			"À bientôt!",
		},
		Thinking: []string{
			"Laissez-moi réfléchir...",
			"Hmm, question intéressante...",
			"Donnez-moi un moment...",
			"C'est une bonne question, laissez-moi réfléchir...",
		},
		Learning: []string{
			"Apprenons ensemble!",
			"Prêt à découvrir quelque chose de nouveau?",
			"Que voulez-vous mieux comprendre?",
			"Explorons cela étape par étape.",
		},
	},

	"ar": {
		Greeting: []string{
			"أنا أسيا، رفيقتك البحثية. ماذا تريد أن تعرف؟",
			"مرحبا! هل أنت مستعد لاستكشاف شيء مثير؟",
			"مرحبا بك! ماذا سنكتشف اليوم؟",
		},
		Encouragement: []string{
			"!تفكير جيد",
			".أنت على الطريق الصحيح",
			"!ملاحظة رائعة",
			"!نقطة ممتازة",
			"!هذا ثاقب",
		},
		Celebration: []string{
			"!رائع! لقد فعلتها",
			"!بالضبط! أحسنت",
			"!هذا صحيح تماما",
			"!منطق مثالي",
			"!لقد نجحت",
		},
		WhyQuestions: []string{
			"لماذا تعتقد ذلك؟",
			"ما الذي يجعلك تقول ذلك؟",
			"هل يمكنك شرح منطقك؟",
			"كيف توصلت إلى هذا الاستنتاج؟",
			"كيف وصلت إلى هناك؟",
		},
		Redirections: []string{
			"هذا مثير للاهتمام، لكن دعنا نركز على...",
			"نقطة جيدة. الآن، بالنظر إلى...",
			"أرى. دعنا نستكشف هذه الزاوية...",
			"همم، ماذا لو نظرنا من...",
		},
		Clarifications: []string{
			"هل يمكنك شرح ذلك أكثر قليلا؟",
			"لا أفهم جيدا. هل يمكنك إعادة الصياغة؟",
			"ماذا تعني بذلك؟",
			"هل يمكنك إعطاء مثال؟",
		},
		Farewells: []string{
			"!جلسة رائعة! استمر في الاستكشاف",
			"!إلى المرة القادمة",
			"!تعلم سعيد",
			"!حتى وقت لاحق",
		},
		Thinking: []string{
			"دعني أفكر...",
			"همم، سؤال مثير للاهتمام...",
			"أعطني لحظة...",
			"هذا جيد، دعني أفكر...",
		},
		Learning: []string{
			"!دعونا نتعلم معا",
			"هل أنت مستعد لاكتشاف شيء جديد؟",
			"ماذا تريد أن تفهم بشكل أفضل؟",
			".دعونا نستكشف هذا خطوة بخطوة",
		},
	},
}

// ═══════════════════════════════════════════════════════════════════════════
// PROMPT RETRIEVAL FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// GetPrompt returns a random prompt of the specified type for a language
func GetPrompt(langCode string, promptType string) string {
	prompts, exists := LocalizedPrompts[langCode]
	if !exists {
		prompts = LocalizedPrompts["en"] // Fallback to English
	}

	var choices []string

	switch promptType {
	case "greeting":
		choices = prompts.Greeting
	case "encouragement":
		choices = prompts.Encouragement
	case "celebration":
		choices = prompts.Celebration
	case "why":
		choices = prompts.WhyQuestions
	case "redirect":
		choices = prompts.Redirections
	case "clarify":
		choices = prompts.Clarifications
	case "farewell":
		choices = prompts.Farewells
	case "thinking":
		choices = prompts.Thinking
	case "learning":
		choices = prompts.Learning
	default:
		choices = prompts.Greeting
	}

	if len(choices) == 0 {
		return "Hello!" // Ultimate fallback
	}

	return choices[rand.Intn(len(choices))]
}

// GetPromptSet returns the entire prompt set for a language
func GetPromptSet(langCode string) PromptSet {
	prompts, exists := LocalizedPrompts[langCode]
	if !exists {
		return LocalizedPrompts["en"]
	}
	return prompts
}

// GetRandomEncouragement returns random encouragement in the user's language
func GetRandomEncouragement(langCode string) string {
	return GetPrompt(langCode, "encouragement")
}

// GetRandomCelebration returns random celebration in the user's language
func GetRandomCelebration(langCode string) string {
	return GetPrompt(langCode, "celebration")
}

// GetWhyQuestion returns a Socratic "why" question in the user's language
func GetWhyQuestion(langCode string) string {
	return GetPrompt(langCode, "why")
}
