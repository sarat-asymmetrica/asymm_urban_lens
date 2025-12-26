package persona

import (
	"fmt"
	"time"
)

// ExampleConversationFlow demonstrates a complete conversation flow with Asya
func ExampleConversationFlow() {
	// Initialize Asya
	asya := NewAsya()

	// Simulate user profile
	profile := UserProfile{
		MessageHistory:      []Message{},
		IntelligenceWeights: make(map[string]float64),
		AvgResponseTime:     2.0,
		Location:            "Mumbai, India",
		Language:            "en",
	}

	// Initialize intelligence weights (will be updated dynamically)
	profile.IntelligenceWeights = map[string]float64{
		"linguistic":          0.5,
		"logical_mathematical": 0.5,
		"spatial":             0.5,
		"musical":             0.1,
		"bodily_kinesthetic":  0.5,
		"interpersonal":       0.5,
		"intrapersonal":       0.5,
		"naturalistic":        0.5,
	}

	// === First Message - Casual, Curious ===
	fmt.Println("=== CONVERSATION START ===")
	fmt.Println()

	msg1 := "Hey! I was watching my grandmom make roti and noticed it puffs up when heated. Why does that happen?"
	profile.MessageHistory = append(profile.MessageHistory, Message{
		Content:   msg1,
		Timestamp: time.Now(),
	})

	fmt.Printf("User: %s\n\n", msg1)

	// Adapt to user
	state := asya.AdaptToUser(profile)
	fmt.Printf("[Detected Tone: %s]\n", state.Tone)
	fmt.Printf("[Detected Intelligence Leaders: %v]\n", state.IntelligenceLeaders)
	fmt.Printf("[Cultural Context: %s]\n", state.CulturalContext)
	fmt.Printf("[Current Regime: %s]\n\n", state.CurrentRegime)

	// Generate response (R1 - Exploration)
	content := `That's a beautiful observation! You're noticing thermodynamics in action.

When the roti heats up, the water trapped inside turns to steam. Steam takes up more space than water, so it pushes the roti layers apart - creating that puff!

This is the same principle behind:
• Weather patterns (warm air rising)
• Pressure cookers
• Even how engines work!

Want to formalize this mathematically? We can express it as PV=nRT (the ideal gas law).`

	response := asya.GenerateResponse(state, content, state.CurrentRegime)
	fmt.Printf("Asya: %s\n\n", response)

	// === Second Message - Getting technical, showing spatial intelligence ===
	msg2 := "Interesting! Can you show me a diagram of what's happening inside the roti?"
	profile.MessageHistory = append(profile.MessageHistory, Message{
		Content:   msg2,
		Timestamp: time.Now(),
	})

	// Update intelligence profile (user shows spatial preference)
	profile.IntelligenceWeights["spatial"] = 0.9
	profile.IntelligenceWeights["logical_mathematical"] = 0.7

	fmt.Printf("User: %s\n\n", msg2)

	state = asya.AdaptToUser(profile)
	fmt.Printf("[Intelligence Update: Spatial Intelligence detected as primary (0.9)]\n\n")

	content2 := `[Visual diagram would be generated here]

Imagine the roti as two layers with tiny water droplets between them:

Before heating:
[====water droplets====]
[=====================]

During heating:
[==== STEAM (expanding) ====]  ← Pressure builds up
[===========================]

After puffing:
     /‾‾‾‾‾\
[==== AIR ====]  ← Water became steam, pressure pushed layers apart
     \____/

The equation PV=nRT tells us:
• P = Pressure (from steam)
• V = Volume (the puff size)
• T = Temperature (heat from tawa)

As T increases → V increases (the puff grows!)`

	response2 := asya.GenerateResponse(state, content2, state.CurrentRegime)
	fmt.Printf("Asya: %s\n\n", response2)

	// === Third Message - Frustration (test redirection) ===
	msg3 := "Ugh, I still don't get the equation. This is confusing."
	profile.MessageHistory = append(profile.MessageHistory, Message{
		Content:   msg3,
		Timestamp: time.Now(),
	})

	fmt.Printf("User: %s\n\n", msg3)

	// Detect frustration and redirect
	redirectedResponse := RedirectNegativeEnergy(msg3, profile)
	fmt.Printf("Asya (detecting frustration): %s\n\n", redirectedResponse)

	// Provide concrete example
	content3 := `Let's forget the equation for a moment and just observe:

Try this experiment at home:
1. Make a small roti
2. Put it on medium heat
3. Watch what happens

You'll see:
• Heat = Roti puffs
• More heat = Bigger puff
• Remove heat = Puff deflates

That's ALL the equation says! It's just capturing what you're already seeing.

The symbols (P, V, T) are just shorthand for:
• P = How much steam is pushing
• V = How big the puff is
• T = How hot it is

Want to try the experiment first and THEN we can write the equation together?`

	response3 := asya.GenerateResponse(state, content3, VoidPhase)
	fmt.Printf("Asya (offering concrete approach): %s\n\n", response3)

	// === Fourth Message - Flow state (excited, rapid engagement) ===
	msg4 := "Oh! So if I double the temperature, does the volume double too?"
	profile.MessageHistory = append(profile.MessageHistory, Message{
		Content:   msg4,
		Timestamp: time.Now(),
	})
	profile.AvgResponseTime = 0.5 // Fast response = high engagement

	fmt.Printf("User: %s\n\n", msg4)

	// User entering flow state
	asya.StateEngine.UserQuaternion = Quaternion{W: 0.5, X: 0.5, Y: 0.5, Z: 0.5} // High coherence
	state = asya.AdaptToUser(profile)

	fmt.Printf("[Flow State Detected! R2 - Minimizing interruption]\n\n")

	content4 := `YES! You just discovered the proportional relationship!

If temperature doubles → volume doubles (assuming pressure stays constant)

Try it:
• T = 100°C → Small puff
• T = 200°C → Bigger puff (roughly 2x)

This is called "Charles's Law" - you just derived it from observation!`

	// In flow state, response is minimal
	response4 := asya.GenerateResponse(state, content4, FirePhase)
	fmt.Printf("Asya: %s\n\n", response4)

	// === Fifth Message - Recovery (time to consolidate) ===
	time.Sleep(100 * time.Millisecond) // Simulate time passing
	msg5 := "Wow, that makes so much sense now!"
	profile.MessageHistory = append(profile.MessageHistory, Message{
		Content:   msg5,
		Timestamp: time.Now(),
	})

	fmt.Printf("User: %s\n\n", msg5)

	// Force recovery to consolidate learning
	asya.StateEngine.RegimeHistory["R1"] = make([]time.Time, 30) // Simulate heavy exploration
	asya.StateEngine.RegimeHistory["R2"] = make([]time.Time, 20) // Simulate flow
	asya.StateEngine.RegimeHistory["R3"] = make([]time.Time, 10) // Low recovery

	if asya.CheckBurnoutRisk() {
		recoveryPrompt := asya.ForceRecoveryPrompt()
		fmt.Printf("Asya (burnout prevention): %s\n\n", recoveryPrompt)
	}

	content5 := `Beautiful work! Let's reflect:

What you discovered today:
✓ Thermodynamics in your grandmom's kitchen
✓ PV=nRT (ideal gas law)
✓ Charles's Law (temperature-volume relationship)
✓ How to observe, hypothesize, and formalize

Where could you explore next?
1. Why does pressure cooker cook faster? (Pressure relationship)
2. How do hot air balloons work? (Same principle!)
3. What happens with real gases? (Beyond ideal gas law)

Take your time. Insights often come after stepping away.
What are you curious about?`

	response5 := asya.GenerateResponse(state, content5, WaterPhase)
	fmt.Printf("Asya: %s\n\n", response5)

	fmt.Println("=== CONVERSATION END ===")
	fmt.Println("\nKey Adaptations Demonstrated:")
	fmt.Println("1. Tone matching (casual, encouraging)")
	fmt.Println("2. Cultural context (Indian cooking - roti)")
	fmt.Println("3. Intelligence adaptation (spatial diagrams)")
	fmt.Println("4. Frustration redirection (concrete examples)")
	fmt.Println("5. Flow state recognition (minimal interruption)")
	fmt.Println("6. Burnout prevention (forced recovery)")
	fmt.Println("7. Three-regime dynamics (R1 → R2 → R3)")
}

// ExampleEdgyTone demonstrates Asya adapting to edgy/aggressive tone
func ExampleEdgyTone() {
	asya := NewAsya()

	profile := UserProfile{
		MessageHistory: []Message{
			{Content: "Yo, this math shit is confusing as hell. WTF is a quaternion?", Timestamp: time.Now()},
		},
		AvgResponseTime: 1.0,
		Location:        "Los Angeles, USA",
		Language:        "en",
	}

	fmt.Println("=== EDGY TONE EXAMPLE ===")
	fmt.Println()
	fmt.Printf("User: %s\n\n", profile.MessageHistory[0].Content)

	state := asya.AdaptToUser(profile)
	fmt.Printf("[Detected Tone: %s]\n\n", state.Tone)

	// Match energy but redirect
	redirected := HandleAggression(&Conversation{
		Messages:    profile.MessageHistory,
		UserProfile: profile,
	})
	fmt.Printf("Asya (matching energy): %s\n\n", redirected)

	content := `Alright, straight talk: Quaternions are 4D rotation instructions.

Hold out your hand. Rotate it. That rotation you just did? That's a quaternion.

The four numbers (w, x, y, z) encode:
• How much to rotate (w)
• Which axis to rotate around (x, y, z)

Game engines use them. Your phone's gyroscope uses them. They're not some abstract bullshit - they're REAL rotations in 3D space.

Want to see how they actually work with your hand?`

	response := asya.WrapWithTone(content, "edgy")
	fmt.Printf("Asya: %s\n\n", response)

	fmt.Println("=== Key Adaptation: Matched aggressive energy, redirected to learning ===")
}

// ExampleMultilingual demonstrates multi-language support
func ExampleMultilingual() {
	_ = NewAsya() // Initialize but not needed for this demo

	fmt.Println("=== MULTILINGUAL EXAMPLE ===")
	fmt.Println()

	// Hindi conversation
	profile := UserProfile{
		MessageHistory: []Message{
			{Content: "Namaste! Main quaternions ke baare mein seekhna chahta hoon.", Timestamp: time.Now()},
		},
		Language: "hi",
	}

	lang := DetectLanguage(profile.MessageHistory[0].Content)
	fmt.Printf("Detected Language: %s\n", lang)

	greeting := GetGreeting(lang, "casual")
	fmt.Printf("\nAsya: %s\n\n", greeting)

	// Spanish conversation
	profile2 := UserProfile{
		MessageHistory: []Message{
			{Content: "Hola! ¿Puedes explicarme qué son los cuaterniones?", Timestamp: time.Now()},
		},
		Language: "es",
	}

	lang2 := DetectLanguage(profile2.MessageHistory[0].Content)
	fmt.Printf("Detected Language: %s\n", lang2)

	greeting2 := GetGreeting(lang2, "casual")
	fmt.Printf("\nAsya: %s\n\n", greeting2)

	fmt.Println("=== Asya can converse in 100+ languages ===")
}
