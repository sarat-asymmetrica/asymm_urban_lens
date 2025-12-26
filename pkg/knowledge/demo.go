// Package knowledge - Interactive demo of knowledge graph capabilities
package knowledge

import (
	"context"
	"fmt"
	"strings"
)

// ═══════════════════════════════════════════════════════════════════════════
// DEMO FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// RunDemo executes a comprehensive demonstration of the knowledge graph
func RunDemo() {
	fmt.Println("╔══════════════════════════════════════════════════════════════════╗")
	fmt.Println("║      ASYA KNOWLEDGE GRAPH - COMPREHENSIVE DEMO                   ║")
	fmt.Println("║      Discovery → Formalization → Celebration                     ║")
	fmt.Println("╚══════════════════════════════════════════════════════════════════╝")
	fmt.Println()

	ctx := context.Background()

	// Initialize full graph
	g := NewMemoryJourneyGraph()

	// 1. Seed foundational knowledge
	demoSeeding(ctx, g)

	// 2. Create user journey
	userID := "demo_learner"
	demoJourneyCreation(ctx, g, userID)

	// 3. Make discoveries
	demoDiscoveries(ctx, g, userID)

	// 4. Find connections
	demoConnections(ctx, g)

	// 5. Build learning paths
	demoLearningPaths(ctx, g)

	// 6. View progress
	demoProgress(ctx, g, userID)

	// 7. Final summary
	demoSummary(ctx, g, userID)
}

// demoSeeding shows the seeding process
func demoSeeding(ctx context.Context, g *MemoryJourneyGraph) {
	printHeader("1. SEEDING FOUNDATIONAL KNOWLEDGE")

	err := g.SeedFoundations(ctx)
	if err != nil {
		fmt.Printf("❌ Error seeding: %v\n", err)
		return
	}

	stats := g.GetSeedStats(ctx)

	fmt.Println("✅ Foundations seeded successfully!")
	fmt.Println()
	fmt.Printf("   📚 Domains:       %d\n", stats["domains"])
	fmt.Printf("   💡 Concepts:      %d\n", stats["concepts"])
	fmt.Printf("   🌉 Bridges:       %d\n", stats["bridges"])
	fmt.Printf("   🔬 Discoveries:   %d (sample)\n", stats["discoveries"])
	fmt.Printf("   🔗 Relationships: %d\n", stats["relationships"])
	fmt.Println()

	// Show sample domains
	domains, _ := g.ListDomains(ctx)
	fmt.Println("   Sample Domains:")
	for i, d := range domains {
		if i >= 3 {
			break
		}
		fmt.Printf("     • %s (%d subdomains)\n", d.Name, len(d.SubDomains))
	}
	fmt.Println()
}

// demoJourneyCreation shows creating a learning journey
func demoJourneyCreation(ctx context.Context, g *MemoryJourneyGraph, userID string) {
	printHeader("2. CREATING LEARNING JOURNEY")

	journey, err := g.CreateJourney(ctx, userID)
	if err != nil {
		fmt.Printf("❌ Error creating journey: %v\n", err)
		return
	}

	fmt.Printf("✅ Journey created for: %s\n", userID)
	fmt.Printf("   🕐 Started: %v\n", journey.StartTime.Format("2006-01-02 15:04:05"))
	fmt.Println()
}

// demoDiscoveries shows the discovery process
func demoDiscoveries(ctx context.Context, g *MemoryJourneyGraph, userID string) {
	printHeader("3. MAKING DISCOVERIES (\"WHY?\" CHAINS)")

	discoveries := []Discovery{
		{
			UserID:    userID,
			Anchor:    "Why does ice float in water?",
			WhyChain: []string{
				"Why does ice float? → Ice is less dense than water",
				"Why is ice less dense? → Water molecules arrange differently when frozen",
				"Why does arrangement change? → Hydrogen bonds form crystalline structure",
				"Why crystalline structure? → Maximum H-bonds requires open lattice",
				"Why open lattice lighter? → Same mass, more volume = lower density",
			},
			Insight:      "Ice floats because hydrogen bonding creates an open crystalline structure with lower density than liquid water",
			LeanTheorem:  "theorem ice_floats : density ice < density water := by ...",
			Verified:     true,
			Domains:      []string{"Physics", "Chemistry"},
			Connections:  []string{"density", "hydrogen_bond", "buoyancy"},
			Tags:         []string{"water", "density", "hydrogen-bond"},
			Celebrations: 12,
		},
		{
			UserID:    userID,
			Anchor:    "Why do musical instruments sound different?",
			WhyChain: []string{
				"Why different sounds? → Different wave patterns (timbre)",
				"Why different patterns? → Different harmonics/overtones",
				"Why different harmonics? → Shape and material affect vibration",
				"Why does shape matter? → Resonance amplifies certain frequencies",
			},
			Insight:      "Musical timbre results from unique harmonic series shaped by instrument geometry and material properties",
			Domains:      []string{"Physics", "Mathematics", "Everyday Life"},
			Connections:  []string{"wave_frequency", "musical_pitch"},
			Tags:         []string{"music", "waves", "harmonics"},
			Celebrations: 8,
		},
		{
			UserID:    userID,
			Anchor:    "Why does food brown when cooked?",
			WhyChain: []string{
				"Why does it brown? → Maillard reaction between sugars and amino acids",
				"Why does reaction happen? → Heat provides activation energy",
				"Why at specific temperature? → Reaction needs ~140°C to proceed",
				"Why that temperature? → Energy barrier for breaking molecular bonds",
			},
			Insight:      "Browning (Maillard reaction) requires sufficient thermal energy to overcome activation barrier",
			Domains:      []string{"Chemistry", "Physics", "Everyday Life"},
			Connections:  []string{"chemical_reaction", "heat_transfer", "cooking_temperature"},
			Tags:         []string{"cooking", "chemistry", "energy"},
			Celebrations: 15,
		},
	}

	for i, d := range discoveries {
		discovery := d // Copy for pointer
		err := g.RecordDiscovery(ctx, &discovery)
		if err != nil {
			fmt.Printf("❌ Error recording discovery %d: %v\n", i+1, err)
			continue
		}

		fmt.Printf("🔬 Discovery %d: \"%s\"\n", i+1, discovery.Anchor)
		fmt.Printf("   📊 Why-chain depth: %d levels\n", len(discovery.WhyChain))
		fmt.Printf("   💡 Insight: %s\n", truncate(discovery.Insight, 80))
		fmt.Printf("   🌍 Domains: %s\n", strings.Join(discovery.Domains, ", "))
		if discovery.Verified {
			fmt.Printf("   ✅ Lean proof verified!\n")
		}
		fmt.Printf("   🎉 Celebrations: %d\n", discovery.Celebrations)
		fmt.Println()
	}

	// Check milestones
	milestones, _ := g.GetUserMilestones(ctx, userID)
	if len(milestones) > 0 {
		fmt.Println("🏆 Milestones Earned:")
		for _, m := range milestones {
			fmt.Printf("   • %s: %s\n", m.Title, m.Description)
		}
		fmt.Println()
	}
}

// demoConnections shows cross-domain connections
func demoConnections(ctx context.Context, g *MemoryJourneyGraph) {
	printHeader("4. EXPLORING CROSS-DOMAIN CONNECTIONS")

	// Find bridges between Physics and Everyday Life
	bridges, err := g.FindBridges(ctx, "Physics", "Everyday Life")
	if err != nil {
		fmt.Printf("❌ Error finding bridges: %v\n", err)
		return
	}

	fmt.Printf("🌉 Found %d bridges between Physics and Everyday Life:\n\n", len(bridges))

	for i, bridge := range bridges {
		if i >= 3 {
			fmt.Printf("   ... and %d more\n", len(bridges)-3)
			break
		}

		fromConcept, _ := g.GetConcept(ctx, bridge.FromID)
		toConcept, _ := g.GetConcept(ctx, bridge.ToID)

		if fromConcept != nil && toConcept != nil {
			fmt.Printf("   %d. %s ⟷ %s\n", i+1, fromConcept.Name, toConcept.Name)
			fmt.Printf("      Type: %s | Strength: %.1f\n", bridge.BridgeType, bridge.Strength)
			fmt.Printf("      %s\n", bridge.Description)
			if len(bridge.Examples) > 0 {
				fmt.Printf("      Example: %s\n", bridge.Examples[0])
			}
			fmt.Println()
		}
	}

	// Domain connectivity
	connectivity, _ := g.GetDomainConnectivity(ctx, "Physics")
	fmt.Println("📊 Physics domain connectivity:")
	for domain, strength := range connectivity {
		fmt.Printf("   • %s: %.2f\n", domain, strength)
	}
	fmt.Println()
}

// demoLearningPaths shows path construction
func demoLearningPaths(ctx context.Context, g *MemoryJourneyGraph) {
	printHeader("5. BUILDING LEARNING PATHS")

	// Try to build a path
	fromID := "density"
	toID := "buoyancy"

	path, err := g.BuildLearningPath(ctx, fromID, toID)
	if err != nil {
		fmt.Printf("⚠️  No direct path found from %s to %s\n", fromID, toID)
		fmt.Println()
		return
	}

	fromConcept, _ := g.GetConcept(ctx, fromID)
	toConcept, _ := g.GetConcept(ctx, toID)

	if fromConcept != nil && toConcept != nil {
		fmt.Printf("🗺️  Learning path: %s → %s\n\n", fromConcept.Name, toConcept.Name)
		fmt.Printf("   Difficulty: %d/10\n", path.Difficulty)
		fmt.Printf("   Estimated time: %d minutes\n", path.TotalTime)
		fmt.Printf("   Steps: %d\n\n", len(path.Nodes))

		if len(path.Nodes) > 0 {
			fmt.Println("   Path nodes:")
			for i, node := range path.Nodes {
				concept, _ := g.GetConcept(ctx, node.ConceptID)
				if concept != nil {
					fmt.Printf("     %d. %s (difficulty %d, ~%d min)\n",
						i+1, concept.Name, node.Difficulty, node.Estimated)
				}
			}
			fmt.Println()
		}
	}
}

// demoProgress shows progress tracking
func demoProgress(ctx context.Context, g *MemoryJourneyGraph, userID string) {
	printHeader("6. TRACKING PROGRESS")

	// Record some concept interactions
	concepts := []string{"density", "buoyancy", "heat_transfer", "wave_frequency"}
	for i, conceptID := range concepts {
		timeSpent := 10 + i*5 // Varying time
		err := g.RecordProgress(ctx, userID, conceptID, timeSpent)
		if err == nil {
			concept, _ := g.GetConcept(ctx, conceptID)
			if concept != nil {
				fmt.Printf("   📖 Studied: %s (%d minutes)\n", concept.Name, timeSpent)
			}
		}
	}
	fmt.Println()

	// Get progress report
	report, err := g.GetProgressReport(ctx, userID)
	if err != nil {
		fmt.Printf("❌ Error getting report: %v\n", err)
		return
	}

	fmt.Println("📊 Progress Report:")
	fmt.Printf("   🕐 Active for: %d days\n", report.DaysActive)
	fmt.Printf("   ⏱️  Total time: %d minutes\n", report.TotalTime)
	fmt.Printf("   📚 Concepts learned: %d\n", report.ConceptsLearned)
	fmt.Printf("   🔬 Discoveries made: %d\n", report.DiscoveriesMade)
	fmt.Printf("   ✅ Proofs verified: %d\n", report.ProofsVerified)
	fmt.Printf("   🌍 Domains explored: %d (%s)\n", len(report.DomainsExplored), strings.Join(report.DomainsExplored, ", "))
	fmt.Printf("   💪 Strongest domain: %s\n", report.StrongestDomain)
	fmt.Printf("   🏆 Milestones: %d\n", report.MilestoneCount)
	fmt.Printf("   📏 Average depth: %.1f levels\n", report.AverageDepth)
	fmt.Printf("   🌉 Cross-domain links: %d\n", report.CrossDomainLinks)
	fmt.Println()

	// Suggestions
	if len(report.SuggestedNext) > 0 {
		fmt.Println("💡 Suggested next concepts:")
		for i, s := range report.SuggestedNext {
			if i >= 3 {
				break
			}
			concept, _ := g.GetConcept(ctx, s.ConceptID)
			if concept != nil {
				fmt.Printf("   %d. %s (%s)\n", i+1, concept.Name, s.Reason)
				fmt.Printf("      Relevance: %.1f%% | Difficulty: %d/10\n",
					s.Relevance*100, s.Difficulty)
			}
		}
		fmt.Println()
	}
}

// demoSummary shows final summary generation
func demoSummary(ctx context.Context, g *MemoryJourneyGraph, userID string) {
	printHeader("7. LEARNING JOURNEY SUMMARY")

	summary, err := g.GenerateJourneySummary(ctx, userID)
	if err != nil {
		fmt.Printf("❌ Error generating summary: %v\n", err)
		return
	}

	fmt.Println(summary)

	// Take snapshot
	snapshot, _ := g.TakeSnapshot(ctx, userID)
	if snapshot != nil {
		fmt.Println("📸 Progress snapshot saved!")
		fmt.Printf("   Timestamp: %v\n", snapshot.Timestamp.Format("2006-01-02 15:04:05"))
		fmt.Printf("   Concepts: %d | Discoveries: %d | Proofs: %d\n",
			snapshot.ConceptsLearned, snapshot.DiscoveriesMade, snapshot.ProofsVerified)
		fmt.Println()
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPER FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

func printHeader(title string) {
	width := 70
	padding := (width - len(title) - 2) / 2

	fmt.Println(strings.Repeat("═", width))
	fmt.Printf("%s %s %s\n", strings.Repeat(" ", padding), title, strings.Repeat(" ", padding))
	fmt.Println(strings.Repeat("═", width))
	fmt.Println()
}

func truncate(s string, maxLen int) string {
	if len(s) <= maxLen {
		return s
	}
	return s[:maxLen-3] + "..."
}

// ═══════════════════════════════════════════════════════════════════════════
// INTERACTIVE DEMO SCENARIOS
// ═══════════════════════════════════════════════════════════════════════════

// DemoScenario represents a pre-configured demo scenario
type DemoScenario struct {
	Name        string
	Description string
	UserID      string
	Run         func(context.Context, *MemoryJourneyGraph)
}

var DemoScenarios = []DemoScenario{
	{
		Name:        "curious_child",
		Description: "A curious child asking \"why?\" about everyday observations",
		UserID:      "alice_age_8",
		Run:         runCuriousChildScenario,
	},
	{
		Name:        "cross_domain_explorer",
		Description: "Finding connections between different scientific domains",
		UserID:      "bob_polymath",
		Run:         runCrossDomainScenario,
	},
	{
		Name:        "proof_builder",
		Description: "Building and verifying mathematical proofs",
		UserID:      "charlie_mathematician",
		Run:         runProofBuilderScenario,
	},
}

func runCuriousChildScenario(ctx context.Context, g *MemoryJourneyGraph) {
	userID := "alice_age_8"
	g.SeedFoundations(ctx)
	g.CreateJourney(ctx, userID)

	// Child asks simple questions, discovers deep principles
	discoveries := []Discovery{
		{
			UserID: userID,
			Anchor: "Why is the sky blue?",
			WhyChain: []string{
				"Sunlight scatters in atmosphere",
				"Blue light scatters more than red",
				"Wavelength affects scattering",
			},
			Insight: "Short wavelengths scatter more (Rayleigh scattering)",
			Domains: []string{"Physics"},
		},
		{
			UserID: userID,
			Anchor: "Why do balloons float?",
			WhyChain: []string{
				"Helium is lighter than air",
				"Buoyant force pushes upward",
				"Density difference causes buoyancy",
			},
			Insight: "Objects less dense than fluid experience upward buoyancy",
			Domains: []string{"Physics"},
		},
	}

	for _, d := range discoveries {
		discovery := d
		g.RecordDiscovery(ctx, &discovery)
		fmt.Printf("👧 Alice asks: \"%s\"\n", discovery.Anchor)
		fmt.Printf("   💡 Discovers: %s\n\n", discovery.Insight)
	}
}

func runCrossDomainScenario(ctx context.Context, g *MemoryJourneyGraph) {
	userID := "bob_polymath"
	g.SeedFoundations(ctx)
	g.CreateJourney(ctx, userID)

	// Explore connections between domains
	bridges, _ := g.FindBridges(ctx, "Mathematics", "Biology")
	fmt.Printf("🌉 Found %d bridges between Math and Biology\n", len(bridges))

	bridges2, _ := g.FindBridges(ctx, "Chemistry", "Everyday Life")
	fmt.Printf("🌉 Found %d bridges between Chemistry and Daily Life\n", len(bridges2))
}

func runProofBuilderScenario(ctx context.Context, g *MemoryJourneyGraph) {
	userID := "charlie_mathematician"
	g.SeedFoundations(ctx)
	g.CreateJourney(ctx, userID)

	// Build formal proofs
	discovery := Discovery{
		UserID:      userID,
		Anchor:      "Prove density of ice < water",
		Insight:     "Formal proof using molecular structure",
		LeanTheorem: "theorem ice_density_theorem : ρ_ice < ρ_water",
		Verified:    true,
		Domains:     []string{"Mathematics", "Physics", "Chemistry"},
	}

	g.RecordDiscovery(ctx, &discovery)
	fmt.Printf("✅ Proof verified in Lean 4!\n")
}

// RunScenario executes a specific demo scenario
func RunScenario(scenarioName string) error {
	ctx := context.Background()
	g := NewMemoryJourneyGraph()

	for _, scenario := range DemoScenarios {
		if scenario.Name == scenarioName {
			fmt.Printf("Running scenario: %s\n", scenario.Description)
			fmt.Println()
			scenario.Run(ctx, g)
			return nil
		}
	}

	return fmt.Errorf("scenario not found: %s", scenarioName)
}
