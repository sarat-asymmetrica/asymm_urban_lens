package i18n

import (
	"math/rand"
)

// ═══════════════════════════════════════════════════════════════════════════
// CULTURAL ANALOGIES - RESONANT EXPLANATIONS
// ═══════════════════════════════════════════════════════════════════════════

// CulturalSet contains culturally-appropriate analogies for a region
type CulturalSet struct {
	Language  string              // Language code
	Region    string              // Region code (e.g., "IN", "NG", "MX")
	Analogies map[string][]string // Concept -> culturally resonant examples
}

// CulturalAnalogies maps language-region -> cultural analogies
var CulturalAnalogies = map[string]CulturalSet{
	"te-IN": {
		Language: "te",
		Region:   "IN",
		Analogies: map[string][]string{
			"exponential_growth": {
				"పులిహోర లో పప్పు పెరుగుట లాగా - మొదట కొంచెం, తర్వాత చాలా!",
				"దీపావళి దీపాల వెలుగు లాగా - ఒకటి వెలిగించితే మరొకటి వెలుగుతుంది.",
				"వర్షం కాలంలో చెట్టు ఆకులు పెరగడం లాగా - ప్రతి రోజు రెట్టింపు.",
			},
			"conservation": {
				"నీళ్ళు → ఆవిరి → మేఘాలు → మళ్ళీ వర్షం - రూపం మారుతుంది, పరిమాణం ఒకటే!",
				"బియ్యం నుండి అన్నం - రూపం మారినా, బరువు అలాగే ఉంటుంది.",
				"పూజ లో దీపం - నూనె తగ్గుతుంది కానీ శక్తి వెలుగుగా మారుతుంది.",
			},
			"recursion": {
				"అద్దాల గది లాగా - ఒక అద్దం మరొక అద్దం లో ప్రతిబింబిస్తుంది, అనంతంగా.",
				"బామ్మ కథ చెప్పేటప్పుడు, కథలో మరో బామ్మ కథ చెప్తుంది.",
				"కొబ్బరి లో కొబ్బరి - లోపల మళ్ళీ అదే నమూనా.",
			},
			"complexity": {
				"బిర్యానీ వంట - చాలా మసాలాలు, సమయం, శ్రమ, కానీ ఫలితం అద్భుతం!",
				"టెంపుల్ గోపురం - ప్రతి రాయి ముఖ్యం, మొత్తం నిర్మాణం అందం.",
				"కొలతల అల్లిక - చాలా దారాలు, అల్లికలు, కానీ చీర అందంగా వస్తుంది.",
			},
			"abstraction": {
				"హల్దీ పౌడర్ - పసుపు కంద నుండి వచ్చింది, కానీ సారాంశం మాత్రమే.",
				"పండుగ పాటలు - పురాణ కథల సారాంశం పాటల్లో.",
				"కాలేజీ రంగులు మారడం - ప్రతి సీజన్ లో వేరే రంగు, కానీ చెట్టు ఒకటే.",
			},
			"feedback_loop": {
				"ఊయల - ఒక వైపు నెట్టితే, తిరిగి వస్తుంది, మళ్ళీ నెట్టవచ్చు.",
				"వడకట్టిన పెరుగు - కొంచెం పెరుగు ఉంటే, పాలు మొత్తం పెరుగవుతాయి.",
				"మాట ప్రతిధ్వని - కొండల్లో అరిస్తే, తిరిగి వినిపిస్తుంది.",
			},
		},
	},

	"hi-IN": {
		Language: "hi",
		Region:   "IN",
		Analogies: map[string][]string{
			"exponential_growth": {
				"दीया से दीया जलाना - एक से दो, दो से चार, बढ़ता जाता है।",
				"फसल की बढ़वार - पहले धीरे, फिर तेज़ी से।",
				"चैन रिएक्शन जैसे - एक पटाखा फूटे तो सब फूट जाते हैं।",
			},
			"conservation": {
				"पानी → भाप → बादल → बारिश - रूप बदलता है, मात्रा नहीं!",
				"आटा से रोटी - रूप बदला, वजन वैसा ही।",
				"दीये का तेल - तेल कम होता है पर रोशनी बनती है।",
			},
			"recursion": {
				"आईने का कमरा - एक आईना दूसरे में दिखता है, अनंत तक।",
				"दादी की कहानी में दादी कहानी सुनाती है।",
				"नारियल में नारियल - अंदर फिर वही पैटर्न।",
			},
			"complexity": {
				"बिरयानी पकाना - बहुत मसाले, समय, मेहनत, पर नतीजा लाजवाब!",
				"मंदिर का शिखर - हर पत्थर ज़रूरी है, पूरी इमारत खूबसूरत।",
				"साड़ी बुनना - बहुत धागे, बुनाई, पर साड़ी सुंदर बनती है।",
			},
			"abstraction": {
				"हल्दी पाउडर - हल्दी की जड़ से आया, पर सिर्फ सार।",
				"भजन - पुराण की कहानी का सार गीतों में।",
				"पेड़ के पत्ते बदलना - हर मौसम नया रंग, पर पेड़ वही।",
			},
			"feedback_loop": {
				"झूला - एक तरफ धक्का दो, वापस आता है, फिर धक्का लगा सकते हैं।",
				"जमाया हुआ दही - थोड़ा दही हो तो पूरा दूध जम जाता है।",
				"गूंज - पहाड़ों में चिल्लाओ तो वापस सुनाई देता है।",
			},
		},
	},

	"es-MX": {
		Language: "es",
		Region:   "MX",
		Analogies: map[string][]string{
			"exponential_growth": {
				"Como masa madre - un poco crece toda la masa.",
				"Fuegos artificiales en cadena - uno explota y todos siguen.",
				"Planta de frijol - lenta al inicio, luego explosiva.",
			},
			"conservation": {
				"Agua → vapor → nubes → lluvia - cambia forma, no cantidad!",
				"Masa a tortilla - forma cambia, peso igual.",
				"Vela que se quema - cera disminuye pero luz aumenta.",
			},
			"recursion": {
				"Cuarto de espejos - un espejo refleja otro, infinitamente.",
				"Abuela cuenta historia donde otra abuela cuenta historia.",
				"Muñecas rusas - dentro hay otra más pequeña.",
			},
			"complexity": {
				"Hacer mole - muchas especias, tiempo, trabajo, ¡pero delicioso!",
				"Pirámide maya - cada piedra importa, toda estructura es bella.",
				"Bordado oaxaqueño - muchos hilos, puntadas, pero hermoso.",
			},
			"abstraction": {
				"Chile en polvo - del chile fresco, solo la esencia.",
				"Corrido - historia de la Revolución en canción.",
				"Árbol cambia hojas - cada estación color diferente, árbol igual.",
			},
			"feedback_loop": {
				"Columpio - empujas, regresa, empujas otra vez.",
				"Masa fermentada - un poco fermenta toda la masa.",
				"Eco en barranca - gritas y regresa tu voz.",
			},
		},
	},

	"yo-NG": {
		Language: "yo",
		Region:   "NG",
		Analogies: map[string][]string{
			"exponential_growth": {
				"Bi ẹyin adiye - ọkan yọ, mẹwa yọ, ọgọrun yọ.",
				"Ina ti o tan ka - ọkan tan, gbogbo wa tan.",
				"Irugbin ẹwa - kekere lakoko, sugbon o dagba kia.",
			},
			"conservation": {
				"Omi → oru → awọsanma → ojo - apẹrẹ yipada, iwọn ko yipada!",
				"Iyẹfun si iyan - apẹrẹ yipada, iwuwo kanna.",
				"Fila ti o jo - epo dinku ṣugbọn imọlẹ pọ si.",
			},
			"recursion": {
				"Yara ti awọn digi - digi kan ṣe afihan omiiran, lailai.",
				"Itan iya agba ninu itan iya agba.",
				"Agbọn ninu agbọn - inu tun jẹ apẹrẹ kanna.",
			},
			"complexity": {
				"Ṣiṣe efo riro - ọpọlọpọ turari, akoko, iṣẹ, ṣugbọn aladun!",
				"Ile-oriṣa atijọ - okuta kọọkan pataki, gbogbo ile lẹwa.",
				"Aṣọ hunhun - ọpọlọpọ okun, hunhun, ṣugbọn lẹwa.",
			},
			"abstraction": {
				"Lulú ata - lati ata tutu, ipilẹ nikan.",
				"Orin atijọ - itan-itan ninu orin.",
				"Igi yipada ewe - akoko kọọkan awọ yatọ, igi kanna.",
			},
			"feedback_loop": {
				"Kẹkẹ ọmọde - ti o ba ti, o pada, ti o tun ti.",
				"Ogi bibajẹ - diẹ ba gbogbo jẹ.",
				"Ìró ninu oke - ti o ba pariwo, yoo pada.",
			},
		},
	},

	"fr-FR": {
		Language: "fr",
		Region:   "FR",
		Analogies: map[string][]string{
			"exponential_growth": {
				"Comme le levain - un peu lève toute la pâte.",
				"Feux d'artifice en chaîne - l'un explose, tous suivent.",
				"Plant de haricot - lent au début, puis explosif.",
			},
			"conservation": {
				"Eau → vapeur → nuages → pluie - forme change, quantité non!",
				"Pâte à pain - forme change, poids identique.",
				"Bougie qui brûle - cire diminue mais lumière augmente.",
			},
			"recursion": {
				"Salle de miroirs - un miroir reflète l'autre, infiniment.",
				"Grand-mère raconte histoire où grand-mère raconte histoire.",
				"Poupées russes - à l'intérieur une autre plus petite.",
			},
			"complexity": {
				"Faire une ratatouille - beaucoup d'ingrédients, temps, travail, mais délicieux!",
				"Cathédrale Notre-Dame - chaque pierre compte, structure entière belle.",
				"Broderie - beaucoup de fils, points, mais magnifique.",
			},
			"abstraction": {
				"Extrait de vanille - de la gousse, seulement l'essence.",
				"Chanson - histoire de la Révolution en musique.",
				"Arbre change feuilles - chaque saison couleur différente, arbre pareil.",
			},
			"feedback_loop": {
				"Balançoire - vous poussez, revient, vous poussez encore.",
				"Pâte fermentée - un peu fermente toute la pâte.",
				"Écho dans canyon - vous criez, votre voix revient.",
			},
		},
	},

	"ar-SA": {
		Language: "ar",
		Region:   "SA",
		Analogies: map[string][]string{
			"exponential_growth": {
				"مثل الخميرة - قليل يرفع كل العجين.",
				"الألعاب النارية المتسلسلة - واحدة تنفجر، الكل يتبع.",
				"نبتة الفول - بطيئة في البداية، ثم انفجارية.",
			},
			"conservation": {
				"ماء ← بخار ← سحاب ← مطر - الشكل يتغير، الكمية لا!",
				"عجين إلى خبز - الشكل يتغير، الوزن نفسه.",
				"شمعة تحترق - الشمع ينقص لكن النور يزيد.",
			},
			"recursion": {
				"غرفة المرايا - مرآة تعكس أخرى، إلى ما لا نهاية.",
				"جدة تحكي قصة فيها جدة تحكي قصة.",
				"دمى روسية - في الداخل أخرى أصغر.",
			},
			"complexity": {
				"طبخ الكبسة - توابل كثيرة، وقت، جهد، لكن لذيذ!",
				"المسجد النبوي - كل حجر مهم، البناء كله جميل.",
				"التطريز - خيوط كثيرة، غرز، لكن جميل.",
			},
			"abstraction": {
				"ماء الورد - من الورد الطازج، الجوهر فقط.",
				"قصيدة - تاريخ في أبيات.",
				"شجرة تبدل أوراقها - كل موسم لون مختلف، الشجرة نفسها.",
			},
			"feedback_loop": {
				"أرجوحة - تدفع، ترجع، تدفع مرة أخرى.",
				"عجين مخمر - قليل يخمر كل العجين.",
				"صدى في الجبل - تصرخ وصوتك يرجع.",
			},
		},
	},
}

// ═══════════════════════════════════════════════════════════════════════════
// ANALOGY RETRIEVAL FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// GetAnalogy returns a culturally-appropriate analogy for a concept
func GetAnalogy(langCode string, region string, concept string) string {
	key := langCode + "-" + region
	culturalSet, exists := CulturalAnalogies[key]
	if !exists {
		// Fallback to just language code without region
		for k, v := range CulturalAnalogies {
			if len(k) >= 2 && k[:2] == langCode {
				culturalSet = v
				exists = true
				break
			}
		}
	}

	if !exists {
		// Fallback to English
		culturalSet = CulturalAnalogies["en-US"]
		if culturalSet.Analogies == nil {
			return "" // No analogy available
		}
	}

	analogies, exists := culturalSet.Analogies[concept]
	if !exists || len(analogies) == 0 {
		return "" // No analogy for this concept
	}

	return analogies[rand.Intn(len(analogies))]
}

// GetAllAnalogies returns all analogies for a language-region
func GetAllAnalogies(langCode string, region string) map[string][]string {
	key := langCode + "-" + region
	culturalSet, exists := CulturalAnalogies[key]
	if !exists {
		return make(map[string][]string)
	}
	return culturalSet.Analogies
}

// GetSupportedConcepts returns all concepts that have analogies defined
func GetSupportedConcepts() []string {
	concepts := make(map[string]bool)
	for _, culturalSet := range CulturalAnalogies {
		for concept := range culturalSet.Analogies {
			concepts[concept] = true
		}
	}

	result := make([]string, 0, len(concepts))
	for concept := range concepts {
		result = append(result, concept)
	}
	return result
}

// HasAnalogy checks if an analogy exists for a concept in a language
func HasAnalogy(langCode string, region string, concept string) bool {
	key := langCode + "-" + region
	culturalSet, exists := CulturalAnalogies[key]
	if !exists {
		return false
	}
	analogies, exists := culturalSet.Analogies[concept]
	return exists && len(analogies) > 0
}
