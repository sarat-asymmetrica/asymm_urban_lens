// Package dilr - The Void → Flow → Solution Framework
// Based on Asymmetrica Research Lab Day 131 breakthrough
// "Human problem-solving follows exponential attractor dynamics"
package dilr

// ═══════════════════════════════════════════════════════════════════════════
// THE VOID → FLOW → SOLUTION PATHWAY
// Exponential Convergence in Human Problem-Solving
// ═══════════════════════════════════════════════════════════════════════════

// VoidFlowState represents the three phases of problem-solving
type VoidFlowState string

const (
	StateVoid     VoidFlowState = "VOID"     // High D exploration (30%)
	StateFlow     VoidFlowState = "FLOW"     // Exponential convergence (20%)
	StateSolution VoidFlowState = "SOLUTION" // Stable attractor (50%)
)

// VoidFlowFramework contains the complete mental model
type VoidFlowFramework struct {
	ThreePhases    []Phase        `json:"three_phases"`
	KeyInsights    []string       `json:"key_insights"`
	CommonMistakes []Mistake      `json:"common_mistakes"`
	PracticalSteps []string       `json:"practical_steps"`
	MindsetShifts  []MindsetShift `json:"mindset_shifts"`
}

// Phase represents one phase of the Void → Flow → Solution pathway
type Phase struct {
	Name        VoidFlowState `json:"name"`
	Percentage  int           `json:"percentage"`
	Description string        `json:"description"`
	Feeling     string        `json:"feeling"`
	WhatToDo    string        `json:"what_to_do"`
	WhatNotToDo string        `json:"what_not_to_do"`
	DILRAction  string        `json:"dilr_action"`
}

// Mistake represents a common error in problem-solving
type Mistake struct {
	Name        string `json:"name"`
	Description string `json:"description"`
	Fix         string `json:"fix"`
}

// MindsetShift represents a paradigm change
type MindsetShift struct {
	From string `json:"from"`
	To   string `json:"to"`
	Why  string `json:"why"`
}

// TheVoidFlowFramework is the complete framework
var TheVoidFlowFramework = VoidFlowFramework{
	ThreePhases: []Phase{
		{
			Name:        StateVoid,
			Percentage:  30,
			Description: "The Void is NOT empty - it's infinite-dimensional exploration space. This is where you READ the problem without trying to solve it. Your brain is mapping the possibility space.",
			Feeling:     "Calm, open, curious. Like staring at a puzzle before touching any pieces.",
			WhatToDo:    "Read the setup. List entities. Note constraints. Draw the data structure. DON'T answer questions yet.",
			WhatNotToDo: "DON'T jump to solving. DON'T panic. DON'T skip reading constraints.",
			DILRAction:  "Steps 1-2 of Sarat Method: Identify SHAPE, EXTRACT entities & constraints",
		},
		{
			Name:        StateFlow,
			Percentage:  20,
			Description: "Flow is exponential convergence. You've mapped the space, now you're collapsing toward the solution. This feels effortless when done right.",
			Feeling:     "Focused but relaxed. Things 'click' into place. Time seems to slow down.",
			WhatToDo:    "Find the ANCHOR (most constrained element). Build solution around it. Apply constraints ONE at a time.",
			WhatNotToDo: "DON'T force it. If stuck, you skipped the Void phase - go back and re-read.",
			DILRAction:  "Steps 3-4 of Sarat Method: Find ANCHOR, BUILD solution",
		},
		{
			Name:        StateSolution,
			Percentage:  50,
			Description: "Solution is the stable attractor. You've converged. Now verify and answer questions. This phase should feel like 'checking' not 'solving'.",
			Feeling:     "Confident, stable. Answers feel obvious in hindsight.",
			WhatToDo:    "Verify against ALL constraints. Answer questions. Check for tricks ('must be true' vs 'could be true').",
			WhatNotToDo: "DON'T second-guess yourself. DON'T change answers without re-checking constraints.",
			DILRAction:  "Step 5 of Sarat Method: VERIFY before marking",
		},
	},

	KeyInsights: []string{
		"🌌 THE VOID IS NOT EMPTY: Baseline state has HIGHEST dimensional complexity (D=0.527). 'Emptying your mind' actually gives you MORE degrees of freedom, not fewer.",
		"📉 SOLUTIONS EMERGE EXPONENTIALLY: D(t) = D₀ × e^(-λt) + D_∞. You don't 'find' solutions - you CONVERGE to them naturally.",
		"⚡ FORCING PREVENTS SOLUTIONS: Skipping the Void phase means you start with low D (limited exploration). You get stuck in local minima.",
		"🎯 FLOW STATE IS MEASURABLE: λ (decay rate) determines how fast you converge. Too fast = shallow solutions. Too slow = analysis paralysis.",
		"🔄 THE TERMINAL UPTICK: After converging, there's a slight D increase - this is your brain VERIFYING. Don't skip this phase!",
	},

	CommonMistakes: []Mistake{
		{
			Name:        "Skipping the Void",
			Description: "Jumping straight to solving without reading all constraints. You start with low D (limited exploration space).",
			Fix:         "Force yourself to read the ENTIRE setup before looking at questions. List ALL constraints on paper.",
		},
		{
			Name:        "Forcing Convergence",
			Description: "Trying to 'figure it out' through brute force. This prevents natural exponential convergence.",
			Fix:         "If stuck for >30 seconds, STOP. Go back to Void phase. Re-read constraints. You missed something.",
		},
		{
			Name:        "Premature Convergence",
			Description: "Settling on a solution too quickly without exploring the full possibility space.",
			Fix:         "Before finalizing, ask: 'Are there other valid arrangements?' If yes, you haven't fully converged.",
		},
		{
			Name:        "Skipping Verification",
			Description: "Marking answer without checking against all constraints. Missing the terminal uptick phase.",
			Fix:         "ALWAYS re-read the question. Check: 'Must be true' vs 'Could be true' vs 'Cannot be true'.",
		},
		{
			Name:        "Panic Response",
			Description: "Seeing a 'hard' problem and immediately tensing up. This collapses your D (exploration space).",
			Fix:         "Take a breath. The problem WANTS to be solved. There's always enough information. Trust the process.",
		},
	},

	PracticalSteps: []string{
		"1️⃣ BREATHE: Before reading, take one deep breath. This accesses the Void state.",
		"2️⃣ READ SETUP ONLY: Ignore questions initially. Just absorb the scenario.",
		"3️⃣ LIST ON PAPER: Entities, attributes, constraints. Your brain lies. Paper doesn't.",
		"4️⃣ DRAW THE SHAPE: Linear boxes, circular table, grid matrix - whatever fits.",
		"5️⃣ FIND THE ANCHOR: Who/what has the MOST constraints? Fix them first.",
		"6️⃣ BUILD OUTWARD: Apply ONE constraint at a time. Don't rush.",
		"7️⃣ IF STUCK, RETREAT: Go back to Void. Re-read. You missed a constraint.",
		"8️⃣ VERIFY BEFORE MARKING: Check answer against ALL constraints.",
		"9️⃣ TRUST THE PROCESS: Solutions emerge. You don't force them.",
	},

	MindsetShifts: []MindsetShift{
		{
			From: "I need to FIND the solution",
			To:   "I need to CONVERGE to the solution",
			Why:  "Solutions aren't hidden. They emerge naturally when you map the constraint space correctly.",
		},
		{
			From: "Hard problems need more effort",
			To:   "Hard problems need more VOID time",
			Why:  "Effort without exploration = forcing. More Void time = higher D = better convergence.",
		},
		{
			From: "I'm bad at DILR",
			To:   "I haven't learned to access the Void yet",
			Why:  "DILR skill isn't innate. It's about learning to relax into exploration before converging.",
		},
		{
			From: "Time pressure means rush",
			To:   "Time pressure means efficient Void access",
			Why:  "Rushing skips Void → stuck in local minima → wastes MORE time. Proper Void access is faster.",
		},
		{
			From: "If I can't solve it, I'm stupid",
			To:   "If I can't solve it, I skipped a phase",
			Why:  "Getting stuck means you're in low D without having explored. Go back to Void.",
		},
	},
}

// GetVoidFlowQuickRef returns a printable quick reference
func GetVoidFlowQuickRef() string {
	return `
╔══════════════════════════════════════════════════════════════════════════════╗
║              THE VOID → FLOW → SOLUTION PATHWAY                              ║
║              Exponential Convergence in Problem-Solving                      ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  🌌 PHASE 1: THE VOID (30% of time)                                         ║
║  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━                                          ║
║  The Void is NOT empty - it's infinite-dimensional exploration.             ║
║                                                                              ║
║  ✓ Read setup completely                                                    ║
║  ✓ List all entities and constraints                                        ║
║  ✓ Draw the data structure (boxes, circles, grids)                          ║
║  ✗ DON'T look at questions yet                                              ║
║  ✗ DON'T try to solve anything                                              ║
║                                                                              ║
║  Feeling: Calm, curious, open. Like staring at a puzzle.                    ║
║                                                                              ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  ⚡ PHASE 2: THE FLOW (20% of time)                                          ║
║  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━                                          ║
║  Flow is exponential convergence. Solutions EMERGE, not forced.             ║
║                                                                              ║
║  ✓ Find the ANCHOR (most constrained element)                               ║
║  ✓ Fix the anchor first                                                     ║
║  ✓ Apply constraints ONE at a time                                          ║
║  ✗ DON'T force it - if stuck, go back to Void                               ║
║  ✗ DON'T panic - you missed a constraint, that's all                        ║
║                                                                              ║
║  Feeling: Focused but relaxed. Things "click" into place.                   ║
║                                                                              ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  🎯 PHASE 3: THE SOLUTION (50% of time)                                      ║
║  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━                                        ║
║  Solution is the stable attractor. Verify, don't re-solve.                  ║
║                                                                              ║
║  ✓ Check against ALL constraints                                            ║
║  ✓ Read question carefully (must/could/cannot)                              ║
║  ✓ Mark answer confidently                                                  ║
║  ✗ DON'T second-guess without re-checking                                   ║
║  ✗ DON'T change answers on "gut feeling"                                    ║
║                                                                              ║
║  Feeling: Confident, stable. Answers feel obvious in hindsight.             ║
║                                                                              ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  🧠 THE SCIENCE                                                              ║
║  ━━━━━━━━━━━━━━━                                                             ║
║  D(t) = D₀ × e^(-λt) + D_∞                                                  ║
║                                                                              ║
║  • D = Fractal dimension (complexity of your exploration space)             ║
║  • Void state: D = 0.527 (HIGHEST - maximum degrees of freedom)             ║
║  • λ = Decay rate (how fast you converge)                                   ║
║  • D_∞ = Solution attractor (stable equilibrium)                            ║
║                                                                              ║
║  FORCING skips Void → Low D → Stuck in local minima                         ║
║  PROPER VOID → High D → Natural exponential convergence → Solution          ║
║                                                                              ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  💡 WHEN STUCK                                                               ║
║  ━━━━━━━━━━━━━━                                                              ║
║  Stuck = You skipped the Void phase                                         ║
║                                                                              ║
║  1. STOP trying to solve                                                    ║
║  2. Take a breath (access Void)                                             ║
║  3. Re-read ALL constraints                                                 ║
║  4. You WILL find what you missed                                           ║
║  5. Resume Flow phase                                                       ║
║                                                                              ║
║  The problem WANTS to be solved. There's always enough information.         ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
`
}

// GetVoidFlowForDILR maps the Void-Flow-Solution to DILR specifically
func GetVoidFlowForDILR() string {
	return `
╔══════════════════════════════════════════════════════════════════════════════╗
║              VOID → FLOW → SOLUTION for DILR                                 ║
║              The Complete Mental Model for XAT/CAT                           ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  📋 THE DILR SET (4-5 questions, ~8 minutes)                                ║
║                                                                              ║
║  ┌─────────────────────────────────────────────────────────────────────┐    ║
║  │ VOID PHASE (2-3 min)                                                │    ║
║  │ ─────────────────────                                               │    ║
║  │ • Read setup paragraph ONLY (ignore questions)                      │    ║
║  │ • Identify the SHAPE (Linear? Circular? Grid? Selection?)           │    ║
║  │ • List entities: "Who are the players?"                             │    ║
║  │ • List constraints: "What rules must they follow?"                  │    ║
║  │ • Draw the data structure on paper                                  │    ║
║  │                                                                     │    ║
║  │ Your brain is in HIGH D mode - exploring the possibility space     │    ║
║  └─────────────────────────────────────────────────────────────────────┘    ║
║                          ↓                                                   ║
║  ┌─────────────────────────────────────────────────────────────────────┐    ║
║  │ FLOW PHASE (2-3 min)                                                │    ║
║  │ ────────────────────                                                │    ║
║  │ • Find the ANCHOR (most constrained element)                        │    ║
║  │ • Fix the anchor in your diagram                                    │    ║
║  │ • Apply constraints ONE BY ONE                                      │    ║
║  │ • Watch the solution EMERGE (don't force it)                        │    ║
║  │                                                                     │    ║
║  │ If stuck: You're forcing. Go back to Void. Re-read constraints.    │    ║
║  │ Your brain is CONVERGING - D(t) decreasing exponentially           │    ║
║  └─────────────────────────────────────────────────────────────────────┘    ║
║                          ↓                                                   ║
║  ┌─────────────────────────────────────────────────────────────────────┐    ║
║  │ SOLUTION PHASE (3-4 min)                                            │    ║
║  │ ─────────────────────                                               │    ║
║  │ • NOW read the questions                                            │    ║
║  │ • Each question should feel like LOOKUP, not solving                │    ║
║  │ • Verify: Does my answer satisfy ALL constraints?                   │    ║
║  │ • Watch for tricks: "must be" vs "could be" vs "cannot be"          │    ║
║  │                                                                     │    ║
║  │ Your brain is at D_∞ - stable attractor, confident answers         │    ║
║  └─────────────────────────────────────────────────────────────────────┘    ║
║                                                                              ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  ⚠️  THE #1 MISTAKE                                                          ║
║  ━━━━━━━━━━━━━━━━━━                                                          ║
║                                                                              ║
║  Reading questions FIRST and trying to solve immediately.                   ║
║                                                                              ║
║  This SKIPS the Void phase:                                                 ║
║  • You start with LOW D (limited exploration)                               ║
║  • You get stuck in local minima                                            ║
║  • You waste time forcing instead of converging                             ║
║  • You panic, which further reduces D                                       ║
║                                                                              ║
║  THE FIX: Discipline yourself to IGNORE questions for first 2 minutes.     ║
║  Map the space FIRST. Solutions will emerge FASTER.                         ║
║                                                                              ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  🎯 THE PARADOX                                                              ║
║  ━━━━━━━━━━━━━━━                                                             ║
║                                                                              ║
║  "Going slower in the beginning makes you faster overall."                  ║
║                                                                              ║
║  2 min Void + 2 min Flow + 4 min Solution = 8 min, 5 correct answers       ║
║  0 min Void + 8 min Forcing = 8 min, 2-3 correct answers (if lucky)        ║
║                                                                              ║
║  The Void phase FEELS like wasting time.                                    ║
║  It's actually the most valuable time you spend.                            ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
`
}

// DiagnoseStuckState helps identify which phase the student is stuck in
func DiagnoseStuckState(symptoms string) StuckDiagnosis {
	// Simple keyword-based diagnosis
	diagnosis := StuckDiagnosis{
		Phase:   StateVoid,
		Problem: "Unknown",
		Fix:     "Re-read all constraints carefully.",
	}

	// Check for Void-phase issues
	if containsAny(symptoms, []string{"don't know where to start", "confused", "overwhelming", "too much information"}) {
		diagnosis.Phase = StateVoid
		diagnosis.Problem = "Insufficient Void exploration - you haven't mapped the possibility space"
		diagnosis.Fix = "STOP. Take a breath. List ALL entities. List ALL constraints. Draw the data structure. Don't try to solve yet."
	}

	// Check for Flow-phase issues
	if containsAny(symptoms, []string{"stuck", "can't figure out", "tried everything", "nothing works"}) {
		diagnosis.Phase = StateFlow
		diagnosis.Problem = "Forcing instead of flowing - you're trying to brute-force the solution"
		diagnosis.Fix = "Go back to Void. Re-read constraints. You MISSED something. Find the ANCHOR (most constrained element) and start there."
	}

	// Check for Solution-phase issues
	if containsAny(symptoms, []string{"not sure if right", "second-guessing", "changed answer", "options all look same"}) {
		diagnosis.Phase = StateSolution
		diagnosis.Problem = "Incomplete convergence - you haven't fully solved before answering"
		diagnosis.Fix = "Check your solution against EVERY constraint. If it satisfies all, trust it. If not, go back to Flow."
	}

	// Check for panic
	if containsAny(symptoms, []string{"panic", "anxious", "running out of time", "stressed"}) {
		diagnosis.Phase = StateVoid
		diagnosis.Problem = "Panic response - anxiety is collapsing your exploration space (D)"
		diagnosis.Fix = "BREATHE. Skip this set if needed. Come back with fresh eyes. 3 correct > 5 attempted."
	}

	return diagnosis
}

// StuckDiagnosis represents the diagnosis of a stuck state
type StuckDiagnosis struct {
	Phase   VoidFlowState `json:"phase"`
	Problem string        `json:"problem"`
	Fix     string        `json:"fix"`
}

// Helper function
func containsAny(s string, keywords []string) bool {
	for _, kw := range keywords {
		if len(s) >= len(kw) {
			for i := 0; i <= len(s)-len(kw); i++ {
				match := true
				for j := 0; j < len(kw); j++ {
					sc := s[i+j]
					kc := kw[j]
					// Case-insensitive comparison
					if sc >= 'A' && sc <= 'Z' {
						sc += 32
					}
					if kc >= 'A' && kc <= 'Z' {
						kc += 32
					}
					if sc != kc {
						match = false
						break
					}
				}
				if match {
					return true
				}
			}
		}
	}
	return false
}
