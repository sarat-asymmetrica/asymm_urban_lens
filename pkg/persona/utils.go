package persona

import (
	"math/rand"
	"time"
)

// init initializes the random number generator
func init() {
	rand.Seed(time.Now().UnixNano())
}

// PickRandomWeighted picks a random element with weights
func PickRandomWeighted(options []string, weights []float64) string {
	if len(options) == 0 || len(options) != len(weights) {
		return ""
	}

	// Calculate total weight
	totalWeight := 0.0
	for _, w := range weights {
		totalWeight += w
	}

	// Pick random value in [0, totalWeight)
	r := rand.Float64() * totalWeight

	// Find which option this corresponds to
	cumulative := 0.0
	for i, w := range weights {
		cumulative += w
		if r < cumulative {
			return options[i]
		}
	}

	// Fallback (shouldn't happen)
	return options[0]
}

// RandomIndex returns a random index in [0, n)
func RandomIndex(n int) int {
	if n <= 0 {
		return 0
	}
	return rand.Intn(n)
}

// ShuffleSlice shuffles a slice in place
func ShuffleSlice(slice []string) {
	for i := len(slice) - 1; i > 0; i-- {
		j := rand.Intn(i + 1)
		slice[i], slice[j] = slice[j], slice[i]
	}
}

// FormatList formats a slice as a bulleted list
func FormatList(items []string) string {
	result := ""
	for _, item := range items {
		result += "• " + item + "\n"
	}
	return result
}

// FormatNumberedList formats a slice as a numbered list
func FormatNumberedList(items []string) string {
	result := ""
	for i, item := range items {
		result += string(rune('1'+i)) + ". " + item + "\n"
	}
	return result
}

// Clamp clamps a value between min and max
func Clamp(value, min, max float64) float64 {
	if value < min {
		return min
	}
	if value > max {
		return max
	}
	return value
}

// Lerp performs linear interpolation between a and b
func Lerp(a, b, t float64) float64 {
	return a + (b-a)*t
}

// MapRange maps a value from one range to another
func MapRange(value, inMin, inMax, outMin, outMax float64) float64 {
	return outMin + (value-inMin)*(outMax-outMin)/(inMax-inMin)
}
