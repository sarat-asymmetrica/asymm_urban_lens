// Package knowledge - Initial knowledge base seeding with foundational concepts
package knowledge

import (
	"context"
	"fmt"
	"strings"
)

// ═══════════════════════════════════════════════════════════════════════════
// FOUNDATIONAL DATA
// ═══════════════════════════════════════════════════════════════════════════

// FoundationalDomains defines the core scientific domains
var FoundationalDomains = []Domain{
	{
		Name:        "Physics",
		Description: "The study of matter, energy, and the fundamental forces of nature",
		SubDomains:  []string{"Mechanics", "Thermodynamics", "Waves", "Electromagnetism", "Optics", "Quantum"},
	},
	{
		Name:        "Chemistry",
		Description: "The study of matter and its properties, composition, structure, and reactions",
		SubDomains:  []string{"Organic", "Inorganic", "Biochemistry", "Physical Chemistry", "Analytical"},
	},
	{
		Name:        "Biology",
		Description: "The study of living organisms and their interactions",
		SubDomains:  []string{"Genetics", "Ecology", "Neuroscience", "Evolution", "Microbiology", "Anatomy"},
	},
	{
		Name:        "Mathematics",
		Description: "The study of numbers, quantities, shapes, and patterns",
		SubDomains:  []string{"Algebra", "Geometry", "Calculus", "Probability", "Number Theory", "Topology"},
	},
	{
		Name:        "Everyday Life",
		Description: "Practical observations from daily experience",
		SubDomains:  []string{"Cooking", "Music", "Sports", "Weather", "Technology", "Health"},
	},
}

// FoundationalConcepts defines core concepts across domains
var FoundationalConcepts = []Concept{
	// Physics
	{
		Name:        "Density",
		Domain:      "Physics",
		Description: "Mass per unit volume of a substance (ρ = m/V)",
		Tags:        []string{"fundamental", "measurement", "property"},
		Difficulty:  3,
	},
	{
		Name:        "Buoyancy",
		Domain:      "Physics",
		Description: "Upward force exerted by a fluid on an immersed object",
		Tags:        []string{"force", "fluid", "archimedes"},
		Difficulty:  4,
		Prerequisites: []string{"density"},
	},
	{
		Name:        "Phase Transition",
		Domain:      "Physics",
		Description: "Change of matter from one state to another (solid, liquid, gas)",
		Tags:        []string{"thermodynamics", "state", "energy"},
		Difficulty:  5,
	},
	{
		Name:        "Wave Frequency",
		Domain:      "Physics",
		Description: "Number of wave cycles per unit time (measured in Hertz)",
		Tags:        []string{"waves", "oscillation", "periodic"},
		Difficulty:  3,
	},
	{
		Name:        "Heat Transfer",
		Domain:      "Physics",
		Description: "Movement of thermal energy from hotter to cooler objects",
		Tags:        []string{"thermodynamics", "energy", "temperature"},
		Difficulty:  4,
	},

	// Chemistry
	{
		Name:        "Molecular Bonding",
		Domain:      "Chemistry",
		Description: "Attractive forces that hold atoms together in molecules",
		Tags:        []string{"molecule", "bond", "structure"},
		Difficulty:  5,
	},
	{
		Name:        "Hydrogen Bond",
		Domain:      "Chemistry",
		Description: "Weak attraction between hydrogen and electronegative atoms",
		Tags:        []string{"bond", "water", "weak"},
		Difficulty:  6,
		Prerequisites: []string{"molecular_bonding"},
	},
	{
		Name:        "Chemical Reaction",
		Domain:      "Chemistry",
		Description: "Process where substances transform into different substances",
		Tags:        []string{"reaction", "transformation", "energy"},
		Difficulty:  4,
	},

	// Biology
	{
		Name:        "Homeostasis",
		Domain:      "Biology",
		Description: "Self-regulating process to maintain internal stability",
		Tags:        []string{"regulation", "balance", "equilibrium"},
		Difficulty:  5,
	},
	{
		Name:        "Evolution",
		Domain:      "Biology",
		Description: "Change in heritable traits of populations over generations",
		Tags:        []string{"darwin", "adaptation", "selection"},
		Difficulty:  6,
	},
	{
		Name:        "Photosynthesis",
		Domain:      "Biology",
		Description: "Process where plants convert light energy into chemical energy",
		Tags:        []string{"plant", "energy", "chlorophyll"},
		Difficulty:  5,
	},

	// Mathematics
	{
		Name:        "Ratio",
		Domain:      "Mathematics",
		Description: "Quantitative relationship between two numbers",
		Tags:        []string{"proportion", "comparison", "fundamental"},
		Difficulty:  2,
	},
	{
		Name:        "Exponential Growth",
		Domain:      "Mathematics",
		Description: "Growth whose rate is proportional to current value",
		Tags:        []string{"growth", "compound", "geometric"},
		Difficulty:  5,
	},
	{
		Name:        "Probability",
		Domain:      "Mathematics",
		Description: "Measure of likelihood of an event occurring",
		Tags:        []string{"chance", "statistics", "likelihood"},
		Difficulty:  4,
	},

	// Everyday Life
	{
		Name:        "Cooking Temperature",
		Domain:      "Everyday Life",
		Description: "Heat application in food preparation",
		Tags:        []string{"cooking", "heat", "food"},
		Difficulty:  1,
	},
	{
		Name:        "Musical Pitch",
		Domain:      "Everyday Life",
		Description: "Perceived frequency of a sound",
		Tags:        []string{"music", "sound", "hearing"},
		Difficulty:  2,
	},
	{
		Name:        "Weather Patterns",
		Domain:      "Everyday Life",
		Description: "Observable atmospheric conditions and their changes",
		Tags:        []string{"weather", "climate", "observation"},
		Difficulty:  3,
	},
}

// FoundationalBridges defines cross-domain connections
var FoundationalBridges = []Connection{
	// Physics → Everyday Life
	{
		FromID:      "heat_transfer",
		ToID:        "cooking_temperature",
		BridgeType:  BridgeApplication,
		Strength:    0.9,
		Description: "Cooking applies heat transfer principles (conduction, convection, radiation)",
		Examples:    []string{"Pan conducts heat to food", "Oven uses convection", "Broiler uses radiation"},
		Difficulty:  2,
	},
	{
		FromID:      "wave_frequency",
		ToID:        "musical_pitch",
		BridgeType:  BridgeMathematical,
		Strength:    0.95,
		Description: "Musical pitch is perceived wave frequency",
		Examples:    []string{"A4 = 440 Hz", "Higher frequency = higher pitch"},
		Difficulty:  2,
	},
	{
		FromID:      "phase_transition",
		ToID:        "weather_patterns",
		BridgeType:  BridgeApplication,
		Strength:    0.85,
		Description: "Weather involves phase transitions (rain, snow, fog)",
		Examples:    []string{"Water evaporates to form clouds", "Clouds condense to form rain", "Water freezes to snow"},
		Difficulty:  3,
	},

	// Chemistry → Physics
	{
		FromID:      "hydrogen_bond",
		ToID:        "density",
		BridgeType:  BridgeMathematical,
		Strength:    0.8,
		Description: "Hydrogen bonding explains ice's lower density than water",
		Examples:    []string{"Ice floats because H-bonds create open structure"},
		Difficulty:  6,
	},
	{
		FromID:      "molecular_bonding",
		ToID:        "phase_transition",
		BridgeType:  BridgeMathematical,
		Strength:    0.9,
		Description: "Phase transitions involve breaking/forming molecular bonds",
		Examples:    []string{"Melting breaks bonds", "Freezing forms bonds"},
		Difficulty:  5,
	},

	// Biology → Chemistry
	{
		FromID:      "photosynthesis",
		ToID:        "chemical_reaction",
		BridgeType:  BridgeApplication,
		Strength:    0.95,
		Description: "Photosynthesis is a chemical reaction (6CO2 + 6H2O → C6H12O6 + 6O2)",
		Examples:    []string{"Converts CO2 and water to glucose and oxygen"},
		Difficulty:  5,
	},

	// Mathematics → Physics
	{
		FromID:      "ratio",
		ToID:        "density",
		BridgeType:  BridgeMathematical,
		Strength:    0.9,
		Description: "Density is a ratio of mass to volume",
		Examples:    []string{"ρ = m/V is a simple ratio"},
		Difficulty:  3,
	},
	{
		FromID:      "exponential_growth",
		ToID:        "evolution",
		BridgeType:  BridgeMathematical,
		Strength:    0.75,
		Description: "Population growth follows exponential patterns",
		Examples:    []string{"Bacteria double every 20 minutes", "Compound reproduction"},
		Difficulty:  6,
	},
	{
		FromID:      "probability",
		ToID:        "weather_patterns",
		BridgeType:  BridgeApplication,
		Strength:    0.7,
		Description: "Weather forecasting uses probability",
		Examples:    []string{"70% chance of rain", "Hurricane probability cones"},
		Difficulty:  4,
	},

	// Cross-domain analogies
	{
		FromID:      "homeostasis",
		ToID:        "weather_patterns",
		BridgeType:  BridgeAnalogy,
		Strength:    0.6,
		Description: "Both involve self-regulating systems seeking equilibrium",
		Examples:    []string{"Body temperature regulation", "Earth's climate balance"},
		Difficulty:  5,
	},
}

// SampleDiscoveries defines example discoveries from conversations
var SampleDiscoveries = []Discovery{
	{
		UserID:    "example_user",
		Anchor:    "Why does ice float in water?",
		WhyChain: []string{
			"Why does ice float? → Ice is less dense than water",
			"Why is ice less dense? → Water molecules arrange differently when frozen",
			"Why does arrangement change? → Hydrogen bonds form crystalline structure",
			"Why crystalline structure? → Maximum H-bonds requires open lattice",
			"Why open lattice lighter? → Same mass, more volume = lower density",
		},
		Insight:       "Ice floats because hydrogen bonding creates an open crystalline structure with lower density than liquid water",
		LeanTheorem:   "theorem ice_floats : density ice < density water := by ...",
		Verified:      false,
		Domains:       []string{"Physics", "Chemistry"},
		Connections:   []string{"density", "hydrogen_bond", "buoyancy"},
		Tags:          []string{"water", "density", "hydrogen-bond", "phase-transition"},
		Celebrations:  12,
		Shares:        5,
	},
	{
		UserID:    "example_user",
		Anchor:    "Why do musical instruments sound different?",
		WhyChain: []string{
			"Why different sounds? → Different wave patterns (timbre)",
			"Why different patterns? → Different harmonics/overtones",
			"Why different harmonics? → Shape and material affect vibration",
			"Why does shape matter? → Resonance amplifies certain frequencies",
		},
		Insight:       "Musical timbre results from unique harmonic series shaped by instrument geometry and material properties",
		LeanTheorem:   "",
		Verified:      false,
		Domains:       []string{"Physics", "Mathematics", "Everyday Life"},
		Connections:   []string{"wave_frequency", "musical_pitch"},
		Tags:          []string{"music", "waves", "harmonics", "resonance"},
		Celebrations:  8,
		Shares:        3,
	},
	{
		UserID:    "example_user",
		Anchor:    "Why does food brown when cooked?",
		WhyChain: []string{
			"Why does it brown? → Maillard reaction between sugars and amino acids",
			"Why does reaction happen? → Heat provides activation energy",
			"Why at specific temperature? → Reaction needs ~140°C to proceed",
			"Why that temperature? → Energy barrier for breaking molecular bonds",
		},
		Insight:       "Browning (Maillard reaction) requires sufficient thermal energy to overcome activation barrier for sugar-protein reactions",
		LeanTheorem:   "",
		Verified:      false,
		Domains:       []string{"Chemistry", "Physics", "Everyday Life"},
		Connections:   []string{"chemical_reaction", "heat_transfer", "cooking_temperature"},
		Tags:          []string{"cooking", "chemistry", "energy", "reaction"},
		Celebrations:  15,
		Shares:        7,
	},
}

// ═══════════════════════════════════════════════════════════════════════════
// SEEDING FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// SeedFoundations populates the graph with foundational knowledge
func (g *MemoryConnectionGraph) SeedFoundations(ctx context.Context) error {
	// 1. Seed domains
	if err := g.seedDomains(ctx); err != nil {
		return fmt.Errorf("failed to seed domains: %w", err)
	}

	// 2. Seed concepts
	if err := g.seedConcepts(ctx); err != nil {
		return fmt.Errorf("failed to seed concepts: %w", err)
	}

	// 3. Seed bridges
	if err := g.seedBridges(ctx); err != nil {
		return fmt.Errorf("failed to seed bridges: %w", err)
	}

	// 4. Seed sample discoveries
	if err := g.seedDiscoveries(ctx); err != nil {
		return fmt.Errorf("failed to seed discoveries: %w", err)
	}

	// 5. Create prerequisite relationships
	if err := g.seedPrerequisites(ctx); err != nil {
		return fmt.Errorf("failed to seed prerequisites: %w", err)
	}

	return nil
}

// seedDomains adds foundational domains
func (g *MemoryConnectionGraph) seedDomains(ctx context.Context) error {
	for _, domain := range FoundationalDomains {
		g.MemoryGraph.domains[domain.Name] = &domain
	}
	return nil
}

// seedConcepts adds foundational concepts
func (g *MemoryConnectionGraph) seedConcepts(ctx context.Context) error {
	conceptIDMap := make(map[string]string) // name -> ID mapping

	for i := range FoundationalConcepts {
		concept := &FoundationalConcepts[i]

		// Generate ID from name
		conceptID := normalizeID(concept.Name)
		concept.ID = conceptID
		conceptIDMap[concept.Name] = conceptID

		if err := g.MemoryGraph.AddConcept(ctx, concept); err != nil {
			return err
		}
	}

	// Update prerequisites to use IDs
	for _, concept := range g.MemoryGraph.concepts {
		var prereqIDs []string
		for _, prereqName := range concept.Prerequisites {
			if id, ok := conceptIDMap[prereqName]; ok {
				prereqIDs = append(prereqIDs, id)
			}
		}
		concept.Prerequisites = prereqIDs
	}

	return nil
}

// seedBridges adds foundational cross-domain connections
func (g *MemoryConnectionGraph) seedBridges(ctx context.Context) error {
	for i := range FoundationalBridges {
		bridge := &FoundationalBridges[i]

		// Normalize IDs
		bridge.FromID = normalizeID(bridge.FromID)
		bridge.ToID = normalizeID(bridge.ToID)

		if err := g.AddBridge(ctx, bridge); err != nil {
			return err
		}
	}

	return nil
}

// seedDiscoveries adds sample discoveries
func (g *MemoryConnectionGraph) seedDiscoveries(ctx context.Context) error {
	for i := range SampleDiscoveries {
		discovery := &SampleDiscoveries[i]

		// Normalize connection IDs
		var normalizedConns []string
		for _, conn := range discovery.Connections {
			normalizedConns = append(normalizedConns, normalizeID(conn))
		}
		discovery.Connections = normalizedConns

		if err := g.RecordDiscovery(ctx, discovery); err != nil {
			return err
		}
	}

	return nil
}

// seedPrerequisites creates prerequisite relationships
func (g *MemoryConnectionGraph) seedPrerequisites(ctx context.Context) error {
	for _, concept := range g.MemoryGraph.concepts {
		for _, prereqID := range concept.Prerequisites {
			err := g.MemoryGraph.AddRelationship(ctx, &Relationship{
				SourceID: prereqID,
				TargetID: concept.ID,
				Type:     RelPrerequisite,
				Strength: 1.0,
			})
			if err != nil {
				return err
			}
		}
	}

	return nil
}

// GetSeedStats returns statistics about seeded data
func (g *MemoryConnectionGraph) GetSeedStats(ctx context.Context) map[string]int {
	g.mu.RLock()
	defer g.mu.RUnlock()

	return map[string]int{
		"domains":     len(g.MemoryGraph.domains),
		"concepts":    len(g.MemoryGraph.concepts),
		"bridges":     len(g.connections),
		"discoveries": len(g.discoveries),
		"relationships": len(g.MemoryGraph.relationships),
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// UTILITIES
// ═══════════════════════════════════════════════════════════════════════════

// normalizeID converts a name to a valid ID
func normalizeID(name string) string {
	// Convert to lowercase and replace spaces with underscores
	normalized := strings.ToLower(name)
	normalized = strings.ReplaceAll(normalized, " ", "_")
	normalized = strings.ReplaceAll(normalized, "-", "_")
	return normalized
}

// AddSampleInteractions simulates user interactions for demo
func (g *MemoryConnectionGraph) AddSampleInteractions(ctx context.Context, userID string) error {
	// Visit some concepts
	concepts := []string{"density", "buoyancy", "hydrogen_bond", "heat_transfer"}

	for _, conceptID := range concepts {
		if err := g.MemoryGraph.RecordInteraction(ctx, userID, conceptID, "view"); err != nil {
			return err
		}
	}

	// Update user journey with domain interests
	journey, err := g.MemoryGraph.GetUserJourney(ctx, userID)
	if err != nil {
		// Create new journey
		journey = &UserJourney{
			UserID:       userID,
			CurrentLevel: make(map[string]int),
			Interests:    make(map[string]float64),
		}
		g.MemoryGraph.journeys[userID] = journey
	}

	// Set interests
	journey.Interests["Physics"] = 0.8
	journey.Interests["Chemistry"] = 0.6
	journey.Interests["Everyday Life"] = 0.9

	// Set skill levels
	journey.CurrentLevel["Physics"] = 4
	journey.CurrentLevel["Chemistry"] = 3
	journey.CurrentLevel["Mathematics"] = 5

	return nil
}
