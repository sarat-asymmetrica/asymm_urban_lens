package persona

import (
	"strings"
)

// Analogy represents a cultural analogy for explaining concepts
type Analogy struct {
	Concept     string // e.g., "exponential_growth"
	Culture     string // e.g., "indian_cooking"
	Example     string // e.g., "Like yeast in dosa batter"
	Explanation string
}

// DefaultCulturalAnalogies returns rich cultural analogy mappings
func DefaultCulturalAnalogies() map[string][]Analogy {
	return map[string][]Analogy{
		"exponential_growth": {
			{
				Concept:     "exponential_growth",
				Culture:     "indian_cooking",
				Example:     "Like yeast in dosa batter",
				Explanation: "A small amount of yeast makes the batter double, then double again. Each doubling happens faster - that's exponential growth!",
			},
			{
				Concept:     "exponential_growth",
				Culture:     "nigerian_markets",
				Example:     "Like viral news in Lagos",
				Explanation: "One person tells two, those two each tell two more. Soon the whole market knows - that's exponential spreading!",
			},
			{
				Concept:     "exponential_growth",
				Culture:     "farming",
				Example:     "Like a single seed becoming a field",
				Explanation: "One seed makes a plant with many seeds, each growing more plants. The field explodes in size - exponential growth!",
			},
		},
		"phase_transition": {
			{
				Concept:     "phase_transition",
				Culture:     "indian_cooking",
				Example:     "Like water boiling for chai",
				Explanation: "Water stays liquid as you heat it, heat it, heat it... then suddenly BOOM - it's steam! That instant change is a phase transition.",
			},
			{
				Concept:     "phase_transition",
				Culture:     "weather",
				Example:     "Like rain suddenly turning to hail",
				Explanation: "Water droplets falling, then temperature drops just enough - instantly they freeze into ice. Phase transition!",
			},
			{
				Concept:     "phase_transition",
				Culture:     "social",
				Example:     "Like a quiet market suddenly erupting in celebration",
				Explanation: "Normal activity, normal activity... then one person shouts good news and EVERYONE erupts. The mood phase-shifts!",
			},
		},
		"quaternion_rotation": {
			{
				Concept:     "quaternion_rotation",
				Culture:     "dance",
				Example:     "Like a bharatanatyam dancer's hand mudra",
				Explanation: "The dancer's hand rotates smoothly in 3D space - that rotation is exactly what quaternions describe!",
			},
			{
				Concept:     "quaternion_rotation",
				Culture:     "sports",
				Example:     "Like a cricket ball spinning through the air",
				Explanation: "The ball spins on multiple axes at once. Quaternions capture that complex 3D rotation perfectly!",
			},
			{
				Concept:     "quaternion_rotation",
				Culture:     "nature",
				Example:     "Like a seed sprouting and twisting toward the sun",
				Explanation: "The sprout doesn't just grow up - it spirals and rotates in 3D. That's quaternion motion!",
			},
		},
		"thermodynamics": {
			{
				Concept:     "thermodynamics",
				Culture:     "indian_cooking",
				Example:     "Like roti puffing on the tawa",
				Explanation: "Heat the roti, trapped air expands, roti puffs up. That's PV=nRT - the ideal gas law in action!",
			},
			{
				Concept:     "thermodynamics",
				Culture:     "nigerian_cooking",
				Example:     "Like akara expanding when fried",
				Explanation: "Bean cakes hit hot oil, water turns to steam, they puff up. Thermodynamics at work!",
			},
			{
				Concept:     "thermodynamics",
				Culture:     "weather",
				Example:     "Like air rising on a hot day",
				Explanation: "Sun heats the ground, air gets hot and expands, rises up creating wind. Energy flow - thermodynamics!",
			},
		},
		"network_effects": {
			{
				Concept:     "network_effects",
				Culture:     "social",
				Example:     "Like WhatsApp becoming valuable because everyone uses it",
				Explanation: "The more people on WhatsApp, the more valuable it is to join. Each new person makes it better for everyone - network effects!",
			},
			{
				Concept:     "network_effects",
				Culture:     "nigerian_markets",
				Example:     "Like vendors clustering in Balogun Market",
				Explanation: "Each vendor attracts customers, which attracts more vendors, which attracts more customers. The network feeds itself!",
			},
			{
				Concept:     "network_effects",
				Culture:     "biology",
				Example:     "Like neurons forming connections",
				Explanation: "Each neuron that connects makes it easier for more to connect. The brain network grows exponentially!",
			},
		},
		"optimization": {
			{
				Concept:     "optimization",
				Culture:     "indian_cooking",
				Example:     "Like finding the perfect spice balance for masala",
				Explanation: "Too much chili? Too bitter. Too little? Bland. You adjust until it's PERFECT - that's optimization!",
			},
			{
				Concept:     "optimization",
				Culture:     "navigation",
				Example:     "Like finding the fastest route through Lagos traffic",
				Explanation: "You try different roads, learn which are jammed, find the optimal path. That's gradient descent!",
			},
			{
				Concept:     "optimization",
				Culture:     "farming",
				Example:     "Like finding the best time to plant crops",
				Explanation: "Too early? Frost kills them. Too late? Not enough sun. You optimize for the perfect window!",
			},
		},
		"fractal_patterns": {
			{
				Concept:     "fractal_patterns",
				Culture:     "indian_art",
				Example:     "Like kolam patterns repeating at different scales",
				Explanation: "Big circles made of smaller circles made of even smaller circles. Same pattern, different sizes - fractals!",
			},
			{
				Concept:     "fractal_patterns",
				Culture:     "nature",
				Example:     "Like tree branches splitting into smaller branches",
				Explanation: "Trunk splits into branches, branches into twigs, twigs into smaller twigs. Fractal branching!",
			},
			{
				Concept:     "fractal_patterns",
				Culture:     "geography",
				Example:     "Like coastlines looking jagged at every zoom level",
				Explanation: "Zoom out? Jagged coast. Zoom in? Still jagged. Zoom more? STILL jagged. Fractal geometry!",
			},
		},
		"probability": {
			{
				Concept:     "probability",
				Culture:     "indian_street_vendor",
				Example:     "Like predicting which snacks will sell today",
				Explanation: "Rainy day? Pakoras sell more. Sunny? Kulfi. You learn the probabilities from experience!",
			},
			{
				Concept:     "probability",
				Culture:     "nigerian_markets",
				Example:     "Like estimating customer arrivals at your stall",
				Explanation: "Morning rush? Many customers. Afternoon? Fewer. You predict probabilities to stock right!",
			},
			{
				Concept:     "probability",
				Culture:     "farming",
				Example:     "Like knowing the chance of rain this month",
				Explanation: "Monsoon season? High probability. Dry season? Low. Farmers use probability to plan planting!",
			},
		},
		"equilibrium": {
			{
				Concept:     "equilibrium",
				Culture:     "indian_cooking",
				Example:     "Like balancing sweet and sour in chutney",
				Explanation: "Too sweet? Add tamarind. Too sour? Add jaggery. You find the perfect balance - equilibrium!",
			},
			{
				Concept:     "equilibrium",
				Culture:     "economics",
				Example:     "Like market price settling where buyers meet sellers",
				Explanation: "Too high? No buyers. Too low? No sellers. Price finds equilibrium where both agree!",
			},
			{
				Concept:     "equilibrium",
				Culture:     "ecology",
				Example:     "Like predator-prey populations balancing",
				Explanation: "Too many predators? Prey decline. Too few? Prey explode, then predators increase. Nature finds equilibrium!",
			},
		},
		"feedback_loops": {
			{
				Concept:     "feedback_loops",
				Culture:     "music",
				Example:     "Like tabla and sitar responding to each other",
				Explanation: "Tabla speeds up, sitar follows. Sitar gets louder, tabla matches. They create a feedback loop of energy!",
			},
			{
				Concept:     "feedback_loops",
				Culture:     "climate",
				Example:     "Like ice melting causing more warming",
				Explanation: "Ice reflects sun. Ice melts, less reflection, more heat absorbed, more melting. Feedback loop!",
			},
			{
				Concept:     "feedback_loops",
				Culture:     "social",
				Example:     "Like a market panic feeding on itself",
				Explanation: "One person sells, others get scared and sell, making more people scared. Feedback loop of fear!",
			},
		},
	}
}

// GetAnalogiesForConcept returns analogies for a specific concept and culture
func GetAnalogiesForConcept(concept string, culture string) []Analogy {
	allAnalogies := DefaultCulturalAnalogies()
	conceptAnalogies, exists := allAnalogies[concept]
	if !exists {
		return []Analogy{} // No analogies for this concept
	}

	// Filter by culture if specified
	if culture == "" {
		return conceptAnalogies // Return all
	}

	filtered := []Analogy{}
	for _, analogy := range conceptAnalogies {
		if analogy.Culture == culture {
			filtered = append(filtered, analogy)
		}
	}

	return filtered
}

// GetAnalogiesForUser returns analogies for a concept adapted to user profile
func GetAnalogiesForUser(concept string, profile UserProfile) []Analogy {
	// Try to get culture-specific analogies
	culturalContext := DetectCulturalContext(profile)
	analogies := GetAnalogiesForConcept(concept, culturalContext)

	// If no culture-specific analogies, return all
	if len(analogies) == 0 {
		return GetAnalogiesForConcept(concept, "")
	}

	return analogies
}

// DetectCulturalContext attempts to detect user's cultural context from profile
func DetectCulturalContext(profile UserProfile) string {
	// Check location
	location := strings.ToLower(profile.Location)

	if strings.Contains(location, "india") || strings.Contains(location, "delhi") ||
		strings.Contains(location, "mumbai") || strings.Contains(location, "bangalore") {
		return "indian_cooking"
	}

	if strings.Contains(location, "nigeria") || strings.Contains(location, "lagos") ||
		strings.Contains(location, "abuja") {
		return "nigerian_markets"
	}

	// Check message content for cultural hints
	allText := ""
	for _, msg := range profile.MessageHistory {
		allText += strings.ToLower(msg.Content) + " "
	}

	if strings.Contains(allText, "roti") || strings.Contains(allText, "masala") ||
		strings.Contains(allText, "kolam") || strings.Contains(allText, "rangoli") {
		return "indian_cooking"
	}

	if strings.Contains(allText, "jollof") || strings.Contains(allText, "market") ||
		strings.Contains(allText, "lagos") {
		return "nigerian_markets"
	}

	if strings.Contains(allText, "farm") || strings.Contains(allText, "crop") ||
		strings.Contains(allText, "harvest") {
		return "farming"
	}

	// Default to generic nature/universal examples
	return "nature"
}

// GetTopIntelligences returns the top N intelligence types from profile
func GetTopIntelligences(profile map[string]float64, n int) []string {
	// Create slice of (intelligence, score) pairs
	type pair struct {
		intelligence string
		score        float64
	}

	pairs := []pair{}
	for intelligence, score := range profile {
		pairs = append(pairs, pair{intelligence, score})
	}

	// Simple bubble sort (small dataset)
	for i := 0; i < len(pairs); i++ {
		for j := i + 1; j < len(pairs); j++ {
			if pairs[j].score > pairs[i].score {
				pairs[i], pairs[j] = pairs[j], pairs[i]
			}
		}
	}

	// Take top N
	result := []string{}
	for i := 0; i < n && i < len(pairs); i++ {
		result = append(result, pairs[i].intelligence)
	}

	return result
}
