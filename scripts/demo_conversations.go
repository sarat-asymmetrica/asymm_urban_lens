// Package scripts - Demo Conversations Library
// Realistic conversation examples for testing and demonstration
package scripts

// DemoConversation represents a complete demo conversation
type DemoConversation struct {
	Name            string
	Language        string
	CulturalContext string
	Messages        []DemoMessage
	ExpectedTheorem string
	ExpectedDomain  string
}

// DemoMessage represents one message in a demo conversation
type DemoMessage struct {
	Role    string // "user" or "assistant"
	Content string
	Notes   string // Developer notes about this step
}

// ═══════════════════════════════════════════════════════════════════════════
// DEMO CONVERSATIONS LIBRARY
// ═══════════════════════════════════════════════════════════════════════════

var DemoConversations = []DemoConversation{
	WarangalGrandmom,
	LagosStreetVendor,
	CuriousChild,
	SiliconValleyEngineer,
	FarmerObservation,
	BakerIntuition,
}

// WarangalGrandmom - Telugu grandmom cooking roti
var WarangalGrandmom = DemoConversation{
	Name:            "Warangal Grandmom",
	Language:        "te",
	CulturalContext: "indian_cooking",
	Messages: []DemoMessage{
		{
			Role:    "user",
			Content: "నమస్కారం! నేను ఏదో అర్థం చేసుకోవాలనుకుంటున్నాను.",
			Notes:   "Greeting in Telugu",
		},
		{
			Role:    "assistant",
			Content: "నమస్కారం! నేను మీకు సహాయం చేయడానికి ఇక్కడ ఉన్నాను. మీరు ఏమి గమనించారు?",
			Notes:   "Warm greeting, ask for observation",
		},
		{
			Role:    "user",
			Content: "నేను రొట్టె చేస్తున్నప్పుడు, పిండి నా చేతుల్లో మారుతుంది.",
			Notes:   "Anchor: roti dough changing in hands",
		},
		{
			Role:    "assistant",
			Content: "ఆహా! మీ చేతుల్లో ఏమి అనుభూతి చెందుతుంది? ఎలా మారుతుంది?",
			Notes:   "Ask for sensory details (kinesthetic intelligence)",
		},
		{
			Role:    "user",
			Content: "మొదట గట్టిగా ఉంటుంది, కానీ నేను పిసికినప్పుడు మెత్తగా మరియు సాగేలా మారుతుంది.",
			Notes:   "Concrete sensory observation",
		},
		{
			Role:    "assistant",
			Content: "అద్భుతం! ఎందుకు ఇలా మారుతుందని మీరు అనుకుంటున్నారు?",
			Notes:   "First 'why' question",
		},
		{
			Role:    "user",
			Content: "పిండిలో గ్లూటెన్ ఉంటుంది, అది నీటితో కలుస్తుంది.",
			Notes:   "First-level explanation",
		},
		{
			Role:    "assistant",
			Content: "సరియైనది! గ్లూటెన్ నీటితో ఎందుకు కలుస్తుంది?",
			Notes:   "Second 'why'",
		},
		{
			Role:    "user",
			Content: "గ్లూటెన్ ప్రోటీన్ గొలుసులు ఉన్నాయి, అవి నీటి అణువులను పట్టుకుంటాయి.",
			Notes:   "Molecular level starting",
		},
		{
			Role:    "assistant",
			Content: "అవును! ప్రోటీన్ గొలుసులు ఎలా నీటిని పట్టుకుంటాయి?",
			Notes:   "Third 'why' - going molecular",
		},
		{
			Role:    "user",
			Content: "హైడ్రోజన్ బంధాలు ఏర్పడతాయి. నీటి అణువులు ప్రోటీన్‌కు అతుక్కుంటాయి.",
			Notes:   "Molecular mechanism",
		},
		{
			Role:    "assistant",
			Content: "పర్ఫెక్ట్! ఇది రసాయన శాస్త్రం! హైడ్రోజన్ బంధాలు ఎందుకు ఏర్పడతాయి?",
			Notes:   "Fourth 'why' - fundamental physics",
		},
		{
			Role:    "user",
			Content: "ఎందుకంటే అణువులకు విద్యుత్ చార్జ్ వ్యత్యాసాలు ఉన్నాయి. ధనాత్మక మరియు ఋణాత్మక భాగాలు ఆకర్షించుకుంటాయి.",
			Notes:   "Electrostatics - fundamental!",
		},
		{
			Role:    "assistant",
			Content: "అద్భుతం! మీరు క్వాంటం మెకానిక్స్ వరకు చేరుకున్నారు! ఇది నీటి ఉడకడం లాంటిదా?",
			Notes:   "Synthesize - connect to known phenomena",
		},
		{
			Role:    "user",
			Content: "అవును! రెండూ అణువుల మధ్య శక్తి మార్పిడి!",
			Notes:   "User makes connection",
		},
		{
			Role:    "assistant",
			Content: "పర్ఫెక్ట్! ఇది థర్మోడైనమిక్స్! మీరు దీన్ని సిద్ధాంతంగా చూడాలనుకుంటున్నారా?",
			Notes:   "Offer formalization",
		},
		{
			Role:    "user",
			Content: "అవును!",
			Notes:   "Accept formalization",
		},
	},
	ExpectedTheorem: `theorem roti_thermodynamics
  (flour : WheatFlour)
  (water : H2O)
  (kneading : MechanicalWork) :
  ∃ (gluten_network : ProteinStructure),
    hydrogen_bonds_form flour.gluten water ∧
    elastic_matrix_emerges gluten_network kneading ∧
    viscoelastic_behavior gluten_network := by
  -- Every grandmom is a chemist! 🙏
  sorry`,
	ExpectedDomain: "thermodynamics",
}

// LagosStreetVendor - Business pattern observation
var LagosStreetVendor = DemoConversation{
	Name:            "Lagos Street Vendor",
	Language:        "en",
	CulturalContext: "nigerian_markets",
	Messages: []DemoMessage{
		{
			Role:    "user",
			Content: "Hello! I want to understand something about my business.",
			Notes:   "Greeting - business context",
		},
		{
			Role:    "assistant",
			Content: "Welcome! I'm here to explore with you. What have you noticed?",
			Notes:   "Warm greeting",
		},
		{
			Role:    "user",
			Content: "I notice customers come in waves throughout the day.",
			Notes:   "Anchor: customer wave pattern",
		},
		{
			Role:    "assistant",
			Content: "Interesting! Tell me more. When do you see these waves?",
			Notes:   "Ask for concrete details",
		},
		{
			Role:    "user",
			Content: "Morning rush at 7-8am, lunch at 12-1pm, evening at 5-6pm. Like clockwork.",
			Notes:   "Specific times - concrete observation",
		},
		{
			Role:    "assistant",
			Content: "Why do you think they come at these times?",
			Notes:   "First 'why'",
		},
		{
			Role:    "user",
			Content: "Work schedules. People go to work, take lunch break, come home.",
			Notes:   "First-level: social patterns",
		},
		{
			Role:    "assistant",
			Content: "Yes! Why do work schedules create waves instead of steady flow?",
			Notes:   "Second 'why' - pattern mechanism",
		},
		{
			Role:    "user",
			Content: "Because everyone starts work at similar times. The system synchronizes.",
			Notes:   "Synchronization insight",
		},
		{
			Role:    "assistant",
			Content: "Exactly! What causes this synchronization?",
			Notes:   "Third 'why' - root cause",
		},
		{
			Role:    "user",
			Content: "Shared constraints - sun cycle, office hours, traffic patterns. Everything couples together.",
			Notes:   "Coupled oscillators insight!",
		},
		{
			Role:    "assistant",
			Content: "Beautiful! This is like pendulum clocks synchronizing on a wall!",
			Notes:   "Make analogy to known physics",
		},
		{
			Role:    "user",
			Content: "Yes! It's all connected - the city breathes like one organism!",
			Notes:   "User grasps the pattern",
		},
		{
			Role:    "assistant",
			Content: "Exactly! This is network dynamics - coupled oscillators! Want to see it as math?",
			Notes:   "Offer formalization",
		},
		{
			Role:    "user",
			Content: "Yes, show me!",
			Notes:   "Accept",
		},
	},
	ExpectedTheorem: `theorem customer_wave_pattern
  (city : UrbanNetwork)
  (vendors : Set Business)
  (oscillator : Business → TimeSeries) :
  synchronized_oscillations city vendors ∧
  phase_coupling (λ v, oscillator v) := by
  -- The market knows physics! 📊
  sorry`,
	ExpectedDomain: "network_dynamics",
}

// CuriousChild - Classic child curiosity
var CuriousChild = DemoConversation{
	Name:            "Curious Child",
	Language:        "en",
	CulturalContext: "childhood_wonder",
	Messages: []DemoMessage{
		{
			Role:    "user",
			Content: "Why is the sky blue?",
			Notes:   "Classic child question - immediate anchor!",
		},
		{
			Role:    "assistant",
			Content: "Great question! Let's discover this together. What do you see when you look at the sky?",
			Notes:   "Anchor in direct observation",
		},
		{
			Role:    "user",
			Content: "It's blue during the day, but red and orange at sunset.",
			Notes:   "Concrete observation with variation",
		},
		{
			Role:    "assistant",
			Content: "Perfect observation! Why do you think it changes color?",
			Notes:   "First 'why'",
		},
		{
			Role:    "user",
			Content: "Maybe because the sun moves?",
			Notes:   "First hypothesis",
		},
		{
			Role:    "assistant",
			Content: "Yes, the sun's position matters! What's between you and the sun?",
			Notes:   "Guide to medium",
		},
		{
			Role:    "user",
			Content: "Air! The atmosphere!",
			Notes:   "Identify the medium",
		},
		{
			Role:    "assistant",
			Content: "Exactly! What does light do when it goes through air?",
			Notes:   "Second 'why' - interaction",
		},
		{
			Role:    "user",
			Content: "It scatters! Like when dust makes light beams visible.",
			Notes:   "Make connection to known phenomenon",
		},
		{
			Role:    "assistant",
			Content: "Perfect analogy! Why does it scatter more blue than red?",
			Notes:   "Third 'why' - wavelength dependence",
		},
		{
			Role:    "user",
			Content: "Blue light has shorter waves, so it bounces more?",
			Notes:   "Wavelength insight!",
		},
		{
			Role:    "assistant",
			Content: "YES! Small particles scatter short wavelengths more! This is Rayleigh scattering!",
			Notes:   "Name the phenomenon",
		},
		{
			Role:    "user",
			Content: "So at sunset, light travels longer through air, blue scatters away, red reaches me!",
			Notes:   "Complete synthesis!",
		},
		{
			Role:    "assistant",
			Content: "EXACTLY! You just discovered physics! Want to see it as a theorem?",
			Notes:   "Offer formalization",
		},
		{
			Role:    "user",
			Content: "Yes!",
			Notes:   "Accept",
		},
	},
	ExpectedTheorem: `theorem rayleigh_scattering
  (λ : Wavelength)
  (atmosphere : Medium)
  (I_scattered : Wavelength → ℝ) :
  I_scattered λ ∝ λ⁻⁴ ∧
  (λ_blue < λ_red → I_scattered λ_blue > I_scattered λ_red) := by
  -- Children are natural scientists! 🌈
  sorry`,
	ExpectedDomain: "optics",
}

// SiliconValleyEngineer - Technical observation
var SiliconValleyEngineer = DemoConversation{
	Name:            "Silicon Valley Engineer",
	Language:        "en",
	CulturalContext: "tech_industry",
	Messages: []DemoMessage{
		{
			Role:    "user",
			Content: "I'm debugging a weird performance issue in our distributed system.",
			Notes:   "Technical context",
		},
		{
			Role:    "assistant",
			Content: "Let's investigate! What behavior are you observing?",
			Notes:   "Anchor in observation",
		},
		{
			Role:    "user",
			Content: "Latency spikes occur in waves - every 60 seconds like clockwork, across all nodes simultaneously.",
			Notes:   "Specific, measurable observation",
		},
		{
			Role:    "assistant",
			Content: "Synchronized spikes across nodes - interesting! What do you think causes the 60-second period?",
			Notes:   "First 'why' - periodicity",
		},
		{
			Role:    "user",
			Content: "Checked cron jobs, garbage collection, network retries - nothing at 60s. It's a mystery.",
			Notes:   "Eliminated obvious causes",
		},
		{
			Role:    "assistant",
			Content: "The synchronization is the clue! What could make independent nodes spike together?",
			Notes:   "Focus on synchronization",
		},
		{
			Role:    "user",
			Content: "They share a database. Connection pool refreshes... wait, that's it! Pool timeout is 60s!",
			Notes:   "Discovery moment!",
		},
		{
			Role:    "assistant",
			Content: "Yes! Why does pool refresh cause latency spikes?",
			Notes:   "Second 'why' - mechanism",
		},
		{
			Role:    "user",
			Content: "All connections close simultaneously, then requests queue while new connections establish. TCP handshake latency!",
			Notes:   "Detailed mechanism",
		},
		{
			Role:    "assistant",
			Content: "Perfect! This is a phase transition - synchronized state change! Like water freezing all at once!",
			Notes:   "Connect to physics",
		},
		{
			Role:    "user",
			Content: "Exactly! It's an emergent synchronization from identical configurations. Coupled oscillators!",
			Notes:   "User makes deep connection",
		},
		{
			Role:    "assistant",
			Content: "You've discovered a universal pattern! Want to formalize it?",
			Notes:   "Offer formalization",
		},
		{
			Role:    "user",
			Content: "Absolutely. Let's do it.",
			Notes:   "Accept",
		},
	},
	ExpectedTheorem: `theorem connection_pool_synchronization
  (nodes : Set DistributedNode)
  (pool : Node → ConnectionPool)
  (timeout : ℝ) (h_timeout : ∀ n ∈ nodes, (pool n).timeout = timeout) :
  synchronized_phase_transition nodes timeout := by
  -- Even bugs teach us physics! 🐛
  sorry`,
	ExpectedDomain: "network_dynamics",
}

// FarmerObservation - Agricultural pattern
var FarmerObservation = DemoConversation{
	Name:            "Farmer Observation",
	Language:        "en",
	CulturalContext: "agriculture",
	Messages: []DemoMessage{
		{
			Role:    "user",
			Content: "I've been farming for 30 years, and I notice the crops grow in rhythms.",
			Notes:   "Long-term pattern observation",
		},
		{
			Role:    "assistant",
			Content: "That's a beautiful observation! What rhythms do you see?",
			Notes:   "Ask for specifics",
		},
		{
			Role:    "user",
			Content: "Fast growth in the morning, slow in afternoon, faster again in evening. Every day, same pattern.",
			Notes:   "Diurnal rhythm",
		},
		{
			Role:    "assistant",
			Content: "Fascinating! Why do you think morning and evening have fast growth?",
			Notes:   "First 'why'",
		},
		{
			Role:    "user",
			Content: "Temperature maybe? Morning is cool, midday is hot, evening cools again.",
			Notes:   "Temperature hypothesis",
		},
		{
			Role:    "assistant",
			Content: "Good hypothesis! But you said faster in evening too - there's less sunlight then. What else could it be?",
			Notes:   "Challenge to think deeper",
		},
		{
			Role:    "user",
			Content: "Water stress! Midday heat causes water loss, plant closes stomata, growth slows.",
			Notes:   "Water stress mechanism",
		},
		{
			Role:    "assistant",
			Content: "Exactly! Why does the plant close stomata when water-stressed?",
			Notes:   "Second 'why' - survival mechanism",
		},
		{
			Role:    "user",
			Content: "To prevent transpiration - water loss through leaves. It's survival!",
			Notes:   "Biological purpose",
		},
		{
			Role:    "assistant",
			Content: "Yes! This is optimal control - the plant solves a minimization problem!",
			Notes:   "Frame as optimization",
		},
		{
			Role:    "user",
			Content: "Like it's computing the best trade-off between growth and water conservation!",
			Notes:   "Optimization insight",
		},
		{
			Role:    "assistant",
			Content: "Perfect! Evolution solved an optimization problem over millions of years! See it as math?",
			Notes:   "Offer formalization",
		},
		{
			Role:    "user",
			Content: "Show me!",
			Notes:   "Accept",
		},
	},
	ExpectedTheorem: `theorem plant_stomatal_control
  (plant : Plant)
  (water_stress : ℝ)
  (stomata_state : ℝ → StomataState) :
  ∀ t, stomata_state t = argmin (λ s, growth_loss s + transpiration_cost s water_stress t) := by
  -- Plants are optimal controllers! 🌱
  sorry`,
	ExpectedDomain: "optimization",
}

// BakerIntuition - Professional baking insight
var BakerIntuition = DemoConversation{
	Name:            "Baker Intuition",
	Language:        "en",
	CulturalContext: "professional_baking",
	Messages: []DemoMessage{
		{
			Role:    "user",
			Content: "I can tell when bread dough is ready just by touch, but I can't explain it to my apprentices.",
			Notes:   "Tacit knowledge problem",
		},
		{
			Role:    "assistant",
			Content: "That's expert intuition! Let's make it explicit. What does ready dough feel like?",
			Notes:   "Anchor in sensation",
		},
		{
			Role:    "user",
			Content: "It has a certain springiness - push it, it bounces back slowly but completely.",
			Notes:   "Viscoelastic behavior",
		},
		{
			Role:    "assistant",
			Content: "Perfect description! Why does it bounce back?",
			Notes:   "First 'why'",
		},
		{
			Role:    "user",
			Content: "Gluten network is fully developed - the strands are connected and elastic.",
			Notes:   "Structural explanation",
		},
		{
			Role:    "assistant",
			Content: "Yes! What makes the network elastic instead of brittle?",
			Notes:   "Second 'why' - material property",
		},
		{
			Role:    "user",
			Content: "The proteins are long chains, cross-linked but still mobile. Like a mesh that can stretch.",
			Notes:   "Molecular structure",
		},
		{
			Role:    "assistant",
			Content: "Beautiful! Why do they cross-link but stay mobile?",
			Notes:   "Third 'why' - molecular dynamics",
		},
		{
			Role:    "user",
			Content: "Hydrogen bonds and disulfide bridges! Strong enough to hold, weak enough to rearrange.",
			Notes:   "Bond chemistry",
		},
		{
			Role:    "assistant",
			Content: "Perfect! This is viscoelasticity - it's rheology, the physics of deformation!",
			Notes:   "Name the field",
		},
		{
			Role:    "user",
			Content: "So I'm feeling the stress-strain relationship of a polymer network!",
			Notes:   "Technical synthesis",
		},
		{
			Role:    "assistant",
			Content: "EXACTLY! You're a rheologist! Want to see the math?",
			Notes:   "Offer formalization",
		},
		{
			Role:    "user",
			Content: "Yes! Let's formalize my hands' knowledge!",
			Notes:   "Accept - embodied cognition!",
		},
	},
	ExpectedTheorem: `theorem dough_viscoelasticity
  (dough : GlutenNetwork)
  (σ : Stress)
  (ε : Strain)
  (t : Time) :
  σ t = ∫ G(t - τ) * (∂ε/∂τ) dτ ∧
  (dough.ready ↔ ∃ G₀ τ, G(t) = G₀ * exp(-t/τ) ∧ G₀ ∈ [optimal_range]) := by
  -- Master bakers are material scientists! 🍞
  sorry`,
	ExpectedDomain: "rheology",
}

// ═══════════════════════════════════════════════════════════════════════════
// UTILITY FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// GetDemoByName retrieves a demo conversation by name
func GetDemoByName(name string) *DemoConversation {
	for i := range DemoConversations {
		if DemoConversations[i].Name == name {
			return &DemoConversations[i]
		}
	}
	return nil
}

// GetDemosByLanguage retrieves all demos in a specific language
func GetDemosByLanguage(lang string) []DemoConversation {
	var demos []DemoConversation
	for _, demo := range DemoConversations {
		if demo.Language == lang {
			demos = append(demos, demo)
		}
	}
	return demos
}

// GetDemosByCulture retrieves all demos in a specific cultural context
func GetDemosByCulture(culture string) []DemoConversation {
	var demos []DemoConversation
	for _, demo := range DemoConversations {
		if demo.CulturalContext == culture {
			demos = append(demos, demo)
		}
	}
	return demos
}
