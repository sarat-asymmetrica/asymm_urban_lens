// Package cultural provides cross-cultural mathematical systems
// Katapayadi (Sanskrit), Gematria (Hebrew/Greek/Arabic), and more
// Cultural reclamation through code - honoring ancient mathematical traditions
package cultural

import (
	"math"
	"strings"
	"unicode"
)

// ═══════════════════════════════════════════════════════════════════════════
// KATAPAYADI - Sanskrit Number Encoding (1500+ years old!)
// ═══════════════════════════════════════════════════════════════════════════

// KatapaydiMapping maps consonants to digits
// This is how ancient Indian mathematicians encoded π as devotional poetry!
var KatapaydiMapping = map[rune]int{
	// 1: ka, ṭa, pa, ya
	'k': 1, 'ṭ': 1, 'p': 1, 'y': 1,
	// 2: kha, ṭha, pha, ra
	'K': 2, 'r': 2,
	// 3: ga, ḍa, ba, la
	'g': 3, 'b': 3, 'l': 3,
	// 4: gha, ḍha, bha, va
	'G': 4, 'v': 4,
	// 5: ṅa, ṇa, ma, śa
	'ṅ': 5, 'ṇ': 5, 'm': 5, 'ś': 5,
	// 6: ca, ta, ṣa
	'c': 6, 't': 6, 'ṣ': 6,
	// 7: cha, tha, sa
	'C': 7, 'T': 7, 's': 7,
	// 8: ja, da, ha
	'j': 8, 'd': 8, 'h': 8,
	// 9: jha, dha
	'J': 9, 'D': 9,
	// 0: ña, na
	'ñ': 0, 'n': 0,
}

// ReverseKatapayadi maps digits to consonants (first option)
var ReverseKatapayadi = map[int]rune{
	0: 'n', 1: 'k', 2: 'K', 3: 'g', 4: 'G',
	5: 'm', 6: 't', 7: 's', 8: 'j', 9: 'J',
}

// EncodeKatapayadi encodes a number as Sanskrit consonants
func EncodeKatapayadi(n int64) string {
	if n == 0 {
		return "na"
	}

	var result []rune
	for n > 0 {
		digit := int(n % 10)
		result = append([]rune{ReverseKatapayadi[digit], 'a'}, result...)
		n /= 10
	}
	return string(result)
}

// DecodeKatapayadi decodes Sanskrit consonants to a number
// Reading is RIGHT-TO-LEFT (like Sanskrit poetry)
func DecodeKatapayadi(s string) int64 {
	var digits []int
	for _, r := range strings.ToLower(s) {
		if val, ok := KatapaydiMapping[r]; ok {
			digits = append(digits, val)
		}
	}

	// Reverse (right-to-left reading)
	var result int64
	multiplier := int64(1)
	for i := len(digits) - 1; i >= 0; i-- {
		result += int64(digits[i]) * multiplier
		multiplier *= 10
	}
	return result
}

// ═══════════════════════════════════════════════════════════════════════════
// GEMATRIA - Hebrew/Greek/Arabic Numerology
// ═══════════════════════════════════════════════════════════════════════════

// HebrewGematria maps Hebrew letters to values
var HebrewGematria = map[rune]int{
	'א': 1, 'ב': 2, 'ג': 3, 'ד': 4, 'ה': 5,
	'ו': 6, 'ז': 7, 'ח': 8, 'ט': 9, 'י': 10,
	'כ': 20, 'ך': 20, 'ל': 30, 'מ': 40, 'ם': 40,
	'נ': 50, 'ן': 50, 'ס': 60, 'ע': 70, 'פ': 80,
	'ף': 80, 'צ': 90, 'ץ': 90, 'ק': 100, 'ר': 200,
	'ש': 300, 'ת': 400,
}

// GreekIsopsephy maps Greek letters to values
var GreekIsopsephy = map[rune]int{
	'α': 1, 'β': 2, 'γ': 3, 'δ': 4, 'ε': 5,
	'ϛ': 6, 'ζ': 7, 'η': 8, 'θ': 9, 'ι': 10,
	'κ': 20, 'λ': 30, 'μ': 40, 'ν': 50, 'ξ': 60,
	'ο': 70, 'π': 80, 'ϟ': 90, 'ρ': 100, 'σ': 200,
	'ς': 200, 'τ': 300, 'υ': 400, 'φ': 500, 'χ': 600,
	'ψ': 700, 'ω': 800, 'ϡ': 900,
}

// ArabicAbjad maps Arabic letters to values
var ArabicAbjad = map[rune]int{
	'ا': 1, 'ب': 2, 'ج': 3, 'د': 4, 'ه': 5,
	'و': 6, 'ز': 7, 'ح': 8, 'ط': 9, 'ي': 10,
	'ك': 20, 'ل': 30, 'م': 40, 'ن': 50, 'س': 60,
	'ع': 70, 'ف': 80, 'ص': 90, 'ق': 100, 'ر': 200,
	'ش': 300, 'ت': 400, 'ث': 500, 'خ': 600, 'ذ': 700,
	'ض': 800, 'ظ': 900, 'غ': 1000,
}

// CalculateGematria computes gematria value for any script
func CalculateGematria(text string, system string) int {
	var mapping map[rune]int
	switch system {
	case "hebrew":
		mapping = HebrewGematria
	case "greek":
		mapping = GreekIsopsephy
	case "arabic":
		mapping = ArabicAbjad
	default:
		// Simple English: A=1, B=2, ..., Z=26
		total := 0
		for _, r := range strings.ToUpper(text) {
			if r >= 'A' && r <= 'Z' {
				total += int(r - 'A' + 1)
			}
		}
		return total
	}

	total := 0
	for _, r := range text {
		if val, ok := mapping[r]; ok {
			total += val
		}
	}
	return total
}

// ═══════════════════════════════════════════════════════════════════════════
// DIGITAL ROOT - Vedic Mathematics (Sutra 12)
// ═══════════════════════════════════════════════════════════════════════════

// DigitalRoot computes the Vedic digital root (1-9, or 0)
// This enables 88.9% search space elimination!
func DigitalRoot(n int64) int {
	if n == 0 {
		return 0
	}
	return 1 + int((n-1)%9)
}

// DigitalRootString computes digital root of a gematria value
func DigitalRootString(text string, system string) int {
	value := CalculateGematria(text, system)
	return DigitalRoot(int64(value))
}

// ═══════════════════════════════════════════════════════════════════════════
// SACRED NUMBERS - Cross-Cultural Constants
// ═══════════════════════════════════════════════════════════════════════════

// SacredNumber represents a culturally significant number
type SacredNumber struct {
	Value        int64  `json:"value"`
	Name         string `json:"name"`
	Culture      string `json:"culture"`
	Significance string `json:"significance"`
	DigitalRoot  int    `json:"digital_root"`
}

// SacredNumbers contains cross-cultural sacred numbers
var SacredNumbers = []SacredNumber{
	{108, "Ashtottara", "Hindu/Buddhist", "Upanishads, mala beads, Sun-Earth distance ratio", 9},
	{216, "Cube of 6", "Vedic", "6³, half of 432", 9},
	{432, "Kali Yuga", "Hindu", "432,000 years in Kali Yuga", 9},
	{27, "Nakshatras", "Hindu", "Lunar mansions in Vedic astrology", 9},
	{54, "Half-mala", "Buddhist", "Half of 108", 9},
	{7, "Sapta", "Universal", "Days of week, chakras, notes", 7},
	{12, "Zodiac", "Universal", "Months, zodiac signs, apostles", 3},
	{40, "Arba'in", "Abrahamic", "Days of flood, years in desert", 4},
	{13, "Mayan", "Mesoamerican", "Baktun cycle, sacred calendar", 4},
	{20, "Vigesimal", "Mayan", "Base-20 counting system", 2},
	{64, "I Ching", "Chinese", "Hexagrams in I Ching", 1},
	{81, "Tao", "Chinese", "9×9, chapters in Tao Te Ching", 9},
	{666, "Beast", "Christian", "Number of the beast", 9},
	{786, "Bismillah", "Islamic", "Abjad value of بسم الله", 3},
	{18, "Chai", "Jewish", "Gematria of חי (life)", 9},
}

// GetSacredNumbersByDigitalRoot filters sacred numbers by digital root
func GetSacredNumbersByDigitalRoot(dr int) []SacredNumber {
	var result []SacredNumber
	for _, sn := range SacredNumbers {
		if sn.DigitalRoot == dr {
			result = append(result, sn)
		}
	}
	return result
}

// ═══════════════════════════════════════════════════════════════════════════
// MANDALA GENERATION - Quaternion to SVG
// ═══════════════════════════════════════════════════════════════════════════

// MandalaConfig configures mandala generation
type MandalaConfig struct {
	Seed        int64  `json:"seed"`
	Petals      int    `json:"petals"`
	Rings       int    `json:"rings"`
	Size        int    `json:"size"`
	ColorScheme string `json:"color_scheme"`
}

// GenerateMandalaSVG creates an SVG mandala from a seed
func GenerateMandalaSVG(config MandalaConfig) string {
	if config.Petals == 0 {
		config.Petals = 8
	}
	if config.Rings == 0 {
		config.Rings = 5
	}
	if config.Size == 0 {
		config.Size = 400
	}

	center := config.Size / 2
	var sb strings.Builder

	sb.WriteString(`<?xml version="1.0" encoding="UTF-8"?>`)
	sb.WriteString("\n")
	sb.WriteString(`<svg xmlns="http://www.w3.org/2000/svg" `)
	sb.WriteString(`width="` + itoa(config.Size) + `" height="` + itoa(config.Size) + `">`)
	sb.WriteString("\n")

	// Background
	sb.WriteString(`<rect width="100%" height="100%" fill="#1a1a2e"/>`)
	sb.WriteString("\n")

	// Generate rings
	for ring := 1; ring <= config.Rings; ring++ {
		radius := float64(ring) * float64(center) / float64(config.Rings+1)
		opacity := 0.3 + 0.7*float64(ring)/float64(config.Rings)

		// Ring circle
		sb.WriteString(`<circle cx="` + itoa(center) + `" cy="` + itoa(center) + `" `)
		sb.WriteString(`r="` + ftoa(radius) + `" `)
		sb.WriteString(`fill="none" stroke="#e94560" stroke-width="1" `)
		sb.WriteString(`opacity="` + ftoa(opacity) + `"/>`)
		sb.WriteString("\n")

		// Petals for this ring
		for petal := 0; petal < config.Petals; petal++ {
			angle := 2 * math.Pi * float64(petal) / float64(config.Petals)
			// Add seed-based variation
			seedOffset := math.Sin(float64(config.Seed)*0.1+float64(petal)) * 0.2
			angle += seedOffset

			x := float64(center) + radius*math.Cos(angle)
			y := float64(center) + radius*math.Sin(angle)

			// Petal shape
			petalSize := radius * 0.3
			sb.WriteString(`<ellipse cx="` + ftoa(x) + `" cy="` + ftoa(y) + `" `)
			sb.WriteString(`rx="` + ftoa(petalSize) + `" ry="` + ftoa(petalSize*0.5) + `" `)
			sb.WriteString(`fill="#16213e" stroke="#0f3460" `)
			sb.WriteString(`transform="rotate(` + ftoa(angle*180/math.Pi) + ` ` + ftoa(x) + ` ` + ftoa(y) + `)"/>`)
			sb.WriteString("\n")
		}
	}

	// Center circle
	sb.WriteString(`<circle cx="` + itoa(center) + `" cy="` + itoa(center) + `" `)
	sb.WriteString(`r="20" fill="#e94560"/>`)
	sb.WriteString("\n")

	sb.WriteString(`</svg>`)
	return sb.String()
}

// Helper functions
func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	var result []byte
	negative := n < 0
	if negative {
		n = -n
	}
	for n > 0 {
		result = append([]byte{byte('0' + n%10)}, result...)
		n /= 10
	}
	if negative {
		result = append([]byte{'-'}, result...)
	}
	return string(result)
}

func ftoa(f float64) string {
	return strings.TrimRight(strings.TrimRight(
		strings.Replace(itoa(int(f*100)), "", "", 0), "0"), ".")
}

// ═══════════════════════════════════════════════════════════════════════════
// UNICODE SCRIPT DETECTION
// ═══════════════════════════════════════════════════════════════════════════

// DetectScript identifies the writing system of text
func DetectScript(text string) string {
	for _, r := range text {
		if unicode.Is(unicode.Devanagari, r) {
			return "devanagari"
		}
		if unicode.Is(unicode.Hebrew, r) {
			return "hebrew"
		}
		if unicode.Is(unicode.Arabic, r) {
			return "arabic"
		}
		if unicode.Is(unicode.Greek, r) {
			return "greek"
		}
		if unicode.Is(unicode.Han, r) {
			return "chinese"
		}
		if unicode.Is(unicode.Tamil, r) {
			return "tamil"
		}
		if unicode.Is(unicode.Telugu, r) {
			return "telugu"
		}
		if unicode.Is(unicode.Kannada, r) {
			return "kannada"
		}
		if unicode.Is(unicode.Malayalam, r) {
			return "malayalam"
		}
		if unicode.Is(unicode.Bengali, r) {
			return "bengali"
		}
		if unicode.Is(unicode.Gujarati, r) {
			return "gujarati"
		}
	}
	return "latin"
}
