// Package dilr provides the Sarat Method for DILR problem decomposition
// "Cut the jargon cruft, get to the shape of the problem"
//
// Philosophy: Every DILR problem is one of ~12 fundamental SHAPES.
// Recognize the shape → Apply the matching solution template → Win.
package dilr

import (
	"strings"
)

// ═══════════════════════════════════════════════════════════════════════════
// THE 12 FUNDAMENTAL SHAPES OF DILR PROBLEMS
// ═══════════════════════════════════════════════════════════════════════════

// ProblemShape represents the fundamental structure of a DILR problem
type ProblemShape string

const (
	// ARRANGEMENT SHAPES (Who sits where? What order?)
	ShapeLinear      ProblemShape = "LINEAR"      // People in a row, sequence
	ShapeCircular    ProblemShape = "CIRCULAR"    // Round table, cycle
	ShapeGrid        ProblemShape = "GRID"        // Matrix arrangement (rows × cols)
	ShapeFloors      ProblemShape = "FLOORS"      // Building floors, vertical stack

	// GROUPING SHAPES (Who goes with whom?)
	ShapeTeams       ProblemShape = "TEAMS"       // Divide into groups
	ShapeSelection   ProblemShape = "SELECTION"   // Pick k from n with constraints
	ShapeMatching    ProblemShape = "MATCHING"    // Pair items (bipartite)

	// ORDERING SHAPES (What comes first?)
	ShapeScheduling  ProblemShape = "SCHEDULING"  // Tasks over time slots
	ShapeRanking     ProblemShape = "RANKING"     // Relative positions (A > B > C)
	ShapeSequencing  ProblemShape = "SEQUENCING"  // Order with dependencies

	// QUANTITATIVE SHAPES (How much?)
	ShapeDistribution ProblemShape = "DISTRIBUTION" // Divide quantities
	ShapeOptimization ProblemShape = "OPTIMIZATION" // Maximize/minimize something

	// META SHAPE
	ShapeHybrid      ProblemShape = "HYBRID"      // Combination of above
)

// ShapeDescription provides human-friendly explanation
var ShapeDescription = map[ProblemShape]string{
	ShapeLinear:       "🪑 LINEAR: Things in a row. Think: movie theater seats.",
	ShapeCircular:     "🔄 CIRCULAR: Round arrangement. Think: dinner party table.",
	ShapeGrid:         "📊 GRID: Rows and columns. Think: Excel spreadsheet.",
	ShapeFloors:       "🏢 FLOORS: Vertical stack. Think: apartment building.",
	ShapeTeams:        "👥 TEAMS: Split into groups. Think: cricket team selection.",
	ShapeSelection:    "✅ SELECTION: Pick some, leave others. Think: shopping with budget.",
	ShapeMatching:     "🔗 MATCHING: Pair things up. Think: arranged marriage (lol).",
	ShapeScheduling:   "📅 SCHEDULING: When does what happen? Think: exam timetable.",
	ShapeRanking:      "🏆 RANKING: Who's better than whom? Think: leaderboard.",
	ShapeSequencing:   "➡️ SEQUENCING: What must come before what? Think: recipe steps.",
	ShapeDistribution: "🍰 DISTRIBUTION: Divide the pie. Think: splitting bill.",
	ShapeOptimization: "📈 OPTIMIZATION: Best possible outcome. Think: max marks in min time.",
	ShapeHybrid:       "🧩 HYBRID: Multiple shapes combined. Break it down!",
}

// ═══════════════════════════════════════════════════════════════════════════
// SOLUTION TEMPLATES - The "Shape of the Solution"
// ═══════════════════════════════════════════════════════════════════════════

// SolutionTemplate provides the attack strategy for each shape
type SolutionTemplate struct {
	Shape       ProblemShape
	FirstMove   string   // What to do IMMEDIATELY
	DataStruct  string   // How to organize information
	KeyInsight  string   // The "aha!" that cracks it
	TimeEstimate string  // How long this should take
	Pitfalls    []string // Common mistakes to avoid
}

var SolutionTemplates = map[ProblemShape]SolutionTemplate{
	ShapeLinear: {
		Shape:      ShapeLinear,
		FirstMove:  "Draw a row of boxes. Label positions 1,2,3... or L,R",
		DataStruct: "Array of slots: [ _ | _ | _ | _ | _ ]",
		KeyInsight: "Fix ONE person first (usually the most constrained). Build around them.",
		TimeEstimate: "5-7 min for 4-5 questions",
		Pitfalls: []string{
			"Don't start filling randomly - find the ANCHOR first",
			"'Adjacent' means next to, 'between' means in the middle",
			"Count positions from BOTH ends to verify",
		},
	},
	ShapeCircular: {
		Shape:      ShapeCircular,
		FirstMove:  "Draw a circle with N points. FIX one person's position (eliminates rotation symmetry)",
		DataStruct: "Circle with fixed reference point",
		KeyInsight: "In circular, only RELATIVE positions matter. Fix one, everything else follows.",
		TimeEstimate: "6-8 min",
		Pitfalls: []string{
			"ALWAYS fix one person first - this is non-negotiable",
			"'Opposite' in circle of 8 = 4 positions apart",
			"Clockwise vs counter-clockwise - draw arrows!",
		},
	},
	ShapeGrid: {
		Shape:      ShapeGrid,
		FirstMove:  "Draw the grid. Label rows AND columns clearly.",
		DataStruct: "Matrix: rows = one attribute, cols = another",
		KeyInsight: "Each cell is an intersection of TWO constraints. Use elimination.",
		TimeEstimate: "7-10 min",
		Pitfalls: []string{
			"Don't confuse row constraints with column constraints",
			"Mark impossibilities with X, certainties with ✓",
			"If stuck, count: how many unknowns vs how many equations?",
		},
	},
	ShapeFloors: {
		Shape:      ShapeFloors,
		FirstMove:  "Draw vertical stack. Ground floor = 1 or 0? CLARIFY FIRST.",
		DataStruct: "Vertical array: top to bottom or bottom to top",
		KeyInsight: "'Above' and 'below' are absolute. 'X floors above Y' = Y's floor + X",
		TimeEstimate: "5-7 min",
		Pitfalls: []string{
			"Ground floor numbering varies - check problem statement",
			"'Immediately above' vs 'somewhere above' - huge difference",
			"Vacant floors are valid - don't forget them",
		},
	},
	ShapeTeams: {
		Shape:      ShapeTeams,
		FirstMove:  "List all items. Note group sizes. Calculate: does it add up?",
		DataStruct: "Sets with size constraints",
		KeyInsight: "Start with MUST-BE-TOGETHER and CANNOT-BE-TOGETHER constraints.",
		TimeEstimate: "6-8 min",
		Pitfalls: []string{
			"Verify total = sum of group sizes",
			"If A and B must be together, treat them as ONE unit",
			"If A and B can't be together, one constraint eliminates many possibilities",
		},
	},
	ShapeSelection: {
		Shape:      ShapeSelection,
		FirstMove:  "List all items with their attributes. Note: selecting k from n.",
		DataStruct: "Checklist with constraints",
		KeyInsight: "FORCED selections first (must include), then FORBIDDEN (must exclude), then choose freely.",
		TimeEstimate: "5-8 min",
		Pitfalls: []string{
			"'At least' vs 'at most' vs 'exactly' - read carefully",
			"Conditional constraints: 'If A then B' means A→B, not B→A",
			"Count remaining slots after forced selections",
		},
	},
	ShapeMatching: {
		Shape:      ShapeMatching,
		FirstMove:  "Draw two columns. Items on left, matches on right.",
		DataStruct: "Bipartite graph or two-column table",
		KeyInsight: "Find the item with FEWEST possible matches. Fix that first.",
		TimeEstimate: "6-8 min",
		Pitfalls: []string{
			"One-to-one vs one-to-many - clarify the matching type",
			"Process of elimination is your friend",
			"If X matches Y, cross out Y from all other possibilities",
		},
	},
	ShapeScheduling: {
		Shape:      ShapeScheduling,
		FirstMove:  "Draw timeline. Mark fixed events first.",
		DataStruct: "Time slots array with constraints",
		KeyInsight: "Find CLASHES first - what can't happen at the same time?",
		TimeEstimate: "7-10 min",
		Pitfalls: []string{
			"Duration matters - a 2-hour task blocks 2 slots",
			"'Before' vs 'immediately before' - different constraints",
			"Gaps/breaks might be required - don't over-pack",
		},
	},
	ShapeRanking: {
		Shape:      ShapeRanking,
		FirstMove:  "List all comparison statements. Draw inequality chain.",
		DataStruct: "Directed graph or inequality chain: A > B > C",
		KeyInsight: "Transitivity! If A > B and B > C, then A > C. Chain them.",
		TimeEstimate: "5-7 min",
		Pitfalls: []string{
			"'A is better than B' vs 'A is not worse than B' (allows equal)",
			"Ties possible? Check problem statement",
			"Draw the full chain before answering questions",
		},
	},
	ShapeSequencing: {
		Shape:      ShapeSequencing,
		FirstMove:  "Identify dependencies: what MUST come before what?",
		DataStruct: "Dependency graph (DAG)",
		KeyInsight: "Find items with NO dependencies - they can go first. Topological sort.",
		TimeEstimate: "6-8 min",
		Pitfalls: []string{
			"'A before B' doesn't mean IMMEDIATELY before",
			"Look for cycles - if found, problem is unsolvable (trick question)",
			"Multiple valid orderings possible - questions test specific constraints",
		},
	},
	ShapeDistribution: {
		Shape:      ShapeDistribution,
		FirstMove:  "Note the TOTAL. Set up equations: parts must sum to whole.",
		DataStruct: "Variables with sum constraint",
		KeyInsight: "Extreme cases first: what's the MIN and MAX each can get?",
		TimeEstimate: "6-8 min",
		Pitfalls: []string{
			"Integer constraints - can't give 2.5 apples",
			"'At least' gives lower bound, 'at most' gives upper bound",
			"If 3 unknowns and 2 equations, you need to find ranges, not exact values",
		},
	},
	ShapeOptimization: {
		Shape:      ShapeOptimization,
		FirstMove:  "Identify: What are we maximizing/minimizing? What are the constraints?",
		DataStruct: "Objective function + constraint inequalities",
		KeyInsight: "Optimal solutions are usually at BOUNDARIES or CORNERS of feasible region.",
		TimeEstimate: "8-10 min",
		Pitfalls: []string{
			"Don't just find A solution - verify it's THE BEST",
			"Check all boundary cases",
			"Sometimes 'good enough' is asked, not 'optimal'",
		},
	},
	ShapeHybrid: {
		Shape:      ShapeHybrid,
		FirstMove:  "DECOMPOSE! Identify which sub-shapes are present.",
		DataStruct: "Multiple structures - one for each sub-problem",
		KeyInsight: "Solve the most constrained sub-problem first. It will constrain others.",
		TimeEstimate: "10-12 min",
		Pitfalls: []string{
			"Don't try to solve everything at once",
			"Information from one sub-problem feeds into another",
			"If stuck, re-read - you probably missed a constraint",
		},
	},
}

// ═══════════════════════════════════════════════════════════════════════════
// PATTERN DETECTION - Identify the Shape from Problem Text
// ═══════════════════════════════════════════════════════════════════════════

// ShapeSignal represents keywords that indicate a particular shape
type ShapeSignal struct {
	Keywords []string
	Weight   float64 // How strongly this indicates the shape
}

var ShapeSignals = map[ProblemShape][]ShapeSignal{
	ShapeLinear: {
		{Keywords: []string{"row", "line", "left", "right", "adjacent", "next to", "end"}, Weight: 1.0},
		{Keywords: []string{"bench", "queue", "seats in a row"}, Weight: 0.9},
	},
	ShapeCircular: {
		{Keywords: []string{"circular", "round table", "circle", "clockwise", "anticlockwise"}, Weight: 1.0},
		{Keywords: []string{"opposite", "facing"}, Weight: 0.6},
	},
	ShapeGrid: {
		{Keywords: []string{"rows and columns", "matrix", "grid", "table"}, Weight: 1.0},
		{Keywords: []string{"each row", "each column", "cell"}, Weight: 0.8},
	},
	ShapeFloors: {
		{Keywords: []string{"floor", "storey", "building", "above", "below"}, Weight: 1.0},
		{Keywords: []string{"top floor", "ground floor", "penthouse"}, Weight: 0.9},
	},
	ShapeTeams: {
		{Keywords: []string{"team", "group", "divide into", "committee"}, Weight: 1.0},
		{Keywords: []string{"together", "same group", "different groups"}, Weight: 0.8},
	},
	ShapeSelection: {
		{Keywords: []string{"select", "choose", "pick", "at least", "at most"}, Weight: 1.0},
		{Keywords: []string{"must include", "cannot include", "if selected"}, Weight: 0.9},
	},
	ShapeMatching: {
		{Keywords: []string{"match", "pair", "assign", "allot", "corresponds"}, Weight: 1.0},
		{Keywords: []string{"each person gets", "one-to-one"}, Weight: 0.9},
	},
	ShapeScheduling: {
		{Keywords: []string{"schedule", "timetable", "slot", "day", "hour", "session"}, Weight: 1.0},
		{Keywords: []string{"monday", "tuesday", "morning", "afternoon"}, Weight: 0.8},
	},
	ShapeRanking: {
		{Keywords: []string{"rank", "better than", "worse than", "scored more", "scored less"}, Weight: 1.0},
		{Keywords: []string{"highest", "lowest", "top", "bottom", "position"}, Weight: 0.7},
	},
	ShapeSequencing: {
		{Keywords: []string{"sequence", "order", "before", "after", "first", "last"}, Weight: 0.8},
		{Keywords: []string{"precedes", "follows", "earlier", "later"}, Weight: 0.9},
	},
	ShapeDistribution: {
		{Keywords: []string{"distribute", "divide", "share", "total", "sum"}, Weight: 1.0},
		{Keywords: []string{"each gets", "remaining", "split"}, Weight: 0.8},
	},
	ShapeOptimization: {
		{Keywords: []string{"maximum", "minimum", "optimize", "best", "worst"}, Weight: 1.0},
		{Keywords: []string{"most profit", "least cost", "highest score"}, Weight: 0.9},
	},
}

// DetectShape analyzes problem text and returns likely shapes with confidence
func DetectShape(problemText string) []ShapeMatch {
	text := strings.ToLower(problemText)
	scores := make(map[ProblemShape]float64)

	for shape, signals := range ShapeSignals {
		for _, signal := range signals {
			for _, keyword := range signal.Keywords {
				if strings.Contains(text, keyword) {
					scores[shape] += signal.Weight
				}
			}
		}
	}

	// Convert to sorted list
	var matches []ShapeMatch
	for shape, score := range scores {
		if score > 0 {
			matches = append(matches, ShapeMatch{
				Shape:      shape,
				Confidence: score,
				Template:   SolutionTemplates[shape],
			})
		}
	}

	// Sort by confidence (descending)
	for i := 0; i < len(matches)-1; i++ {
		for j := i + 1; j < len(matches); j++ {
			if matches[j].Confidence > matches[i].Confidence {
				matches[i], matches[j] = matches[j], matches[i]
			}
		}
	}

	// If multiple high-confidence matches, might be hybrid
	if len(matches) >= 2 && matches[1].Confidence > 1.5 {
		hybridMatch := ShapeMatch{
			Shape:      ShapeHybrid,
			Confidence: matches[0].Confidence + matches[1].Confidence,
			Template:   SolutionTemplates[ShapeHybrid],
			SubShapes:  []ProblemShape{matches[0].Shape, matches[1].Shape},
		}
		matches = append([]ShapeMatch{hybridMatch}, matches...)
	}

	return matches
}

// ShapeMatch represents a detected shape with confidence
type ShapeMatch struct {
	Shape      ProblemShape
	Confidence float64
	Template   SolutionTemplate
	SubShapes  []ProblemShape // For hybrid problems
}

// ═══════════════════════════════════════════════════════════════════════════
// THE SARAT METHOD - Step by Step
// ═══════════════════════════════════════════════════════════════════════════

// SaratMethod provides the complete problem-solving framework
type SaratMethod struct {
	Step1_Shape    string // What shape is this?
	Step2_Extract  string // What are the entities and constraints?
	Step3_Anchor   string // What's the most constrained element?
	Step4_Build    string // Build solution around anchor
	Step5_Verify   string // Sanity check
}

var TheSaratMethod = SaratMethod{
	Step1_Shape: `
🔍 STEP 1: IDENTIFY THE SHAPE (30 seconds)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Read the SETUP paragraph only. Ask:
- Are things being ARRANGED? (Linear/Circular/Grid/Floors)
- Are things being GROUPED? (Teams/Selection/Matching)  
- Are things being ORDERED? (Scheduling/Ranking/Sequencing)
- Are things being COUNTED? (Distribution/Optimization)

The shape tells you WHAT DATA STRUCTURE to draw.
Don't read the questions yet!`,

	Step2_Extract: `
📝 STEP 2: EXTRACT ENTITIES & CONSTRAINTS (1-2 minutes)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
List:
- ENTITIES: Who/what are we arranging? (People, items, tasks)
- ATTRIBUTES: What properties do they have? (Color, size, skill)
- HARD CONSTRAINTS: What MUST be true? ("A sits next to B")
- SOFT CONSTRAINTS: What MIGHT be true? ("If X then Y")

Write these down. Don't hold them in your head.`,

	Step3_Anchor: `
⚓ STEP 3: FIND THE ANCHOR (30 seconds)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
The ANCHOR is the most constrained element.
- Who has the MOST conditions attached to them?
- What position has the MOST restrictions?
- Which slot can only have ONE possibility?

FIX THE ANCHOR FIRST. Everything else builds around it.
In circular arrangements, ALWAYS fix one person arbitrarily.`,

	Step4_Build: `
🏗️ STEP 4: BUILD THE SOLUTION (2-4 minutes)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Starting from anchor:
1. Apply direct constraints (A next to B → place B)
2. Apply indirect constraints (C not next to A → eliminate positions)
3. For remaining slots, check: what CAN go here?

If you get stuck:
- Re-read constraints - you missed something
- Try the OTHER possibility (if A can be in 2 places, try each)
- Count: slots remaining vs items remaining`,

	Step5_Verify: `
✅ STEP 5: VERIFY (30 seconds per question)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Before marking answer:
- Does it satisfy ALL constraints?
- Did I answer what was ASKED? (not what I assumed)
- For "definitely true" - is there ANY case where it's false?
- For "definitely false" - is there ANY case where it's true?
- For "cannot be determined" - do I have multiple valid scenarios?`,
}

// ═══════════════════════════════════════════════════════════════════════════
// QUICK REFERENCE CARD
// ═══════════════════════════════════════════════════════════════════════════

// QuickRef returns a printable quick reference
func QuickRef() string {
	return `
╔══════════════════════════════════════════════════════════════════════════════╗
║                    THE SARAT METHOD - DILR QUICK REFERENCE                   ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  🎯 THE 5-STEP FLOW (Total: 6-8 minutes per set)                            ║
║  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━                              ║
║  1. SHAPE    (30s)  → What type of problem is this?                         ║
║  2. EXTRACT  (1-2m) → List entities, attributes, constraints                ║
║  3. ANCHOR   (30s)  → Find most constrained element, fix it                 ║
║  4. BUILD    (2-4m) → Construct solution around anchor                      ║
║  5. VERIFY   (30s)  → Sanity check before marking                           ║
║                                                                              ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  📊 SHAPE → DATA STRUCTURE                                                   ║
║  ━━━━━━━━━━━━━━━━━━━━━━━━━━                                                  ║
║  LINEAR      → [ _ | _ | _ | _ ]     (row of boxes)                         ║
║  CIRCULAR    → ○ with fixed point    (fix one person!)                      ║
║  GRID        → Matrix rows × cols    (two attributes)                       ║
║  FLOORS      → Vertical stack        (bottom to top)                        ║
║  TEAMS       → Sets with sizes       (who's together?)                      ║
║  SELECTION   → Checklist             (in or out?)                           ║
║  MATCHING    → Two columns           (left ↔ right)                         ║
║  SCHEDULING  → Timeline              (when?)                                ║
║  RANKING     → A > B > C chain       (who's better?)                        ║
║  SEQUENCING  → Dependency arrows     (what's first?)                        ║
║  DISTRIBUTION→ X + Y + Z = Total     (how much each?)                       ║
║  OPTIMIZATION→ Max/Min + constraints (best outcome?)                        ║
║                                                                              ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  ⚡ SPEED HACKS                                                              ║
║  ━━━━━━━━━━━━━━                                                              ║
║  • "If A then B" does NOT mean "If B then A"                                ║
║  • "At least 2" means 2 or more. "At most 2" means 2 or fewer.             ║
║  • "Adjacent" = next to. "Between" = in the middle.                         ║
║  • In circular: fix ONE person first. Always. No exceptions.                ║
║  • When stuck: you missed a constraint. Re-read.                            ║
║  • "Cannot be determined" = multiple valid arrangements exist               ║
║                                                                              ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  🧠 MINDSET                                                                  ║
║  ━━━━━━━━━━━                                                                 ║
║  • The problem WANTS to be solved. There's always enough info.              ║
║  • If it feels impossible, you're overcomplicating it.                      ║
║  • Draw EVERYTHING. Your brain lies. Paper doesn't.                         ║
║  • Skip hard sets. Come back with fresh eyes.                               ║
║  • 3 correct answers > 5 attempted answers                                  ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
`
}
