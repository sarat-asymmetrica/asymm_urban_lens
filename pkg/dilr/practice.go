// Package dilr - Practice problem generator with Sarat-style breakdowns
package dilr

import (
	"fmt"
	"math/rand"
)

// PracticeProblem represents a DILR problem with solution breakdown
type PracticeProblem struct {
	ID             string       `json:"id"`
	Title          string       `json:"title"`
	Shape          ProblemShape `json:"shape"`
	Difficulty     string       `json:"difficulty"` // Easy, Medium, Hard
	Setup          string       `json:"setup"`
	Questions      []Question   `json:"questions"`
	SaratBreakdown Breakdown    `json:"sarat_breakdown"`
}

// Question represents a single question in a DILR set
type Question struct {
	Number  int      `json:"number"`
	Text    string   `json:"text"`
	Options []string `json:"options"`
	Answer  string   `json:"answer"`
	Why     string   `json:"why"` // Explanation
}

// Breakdown shows the Sarat Method applied to this problem
type Breakdown struct {
	Shape         string   `json:"shape"`
	WhyThisShape  string   `json:"why_this_shape"`
	Entities      []string `json:"entities"`
	Constraints   []string `json:"constraints"`
	Anchor        string   `json:"anchor"`
	WhyAnchor     string   `json:"why_anchor"`
	Solution      []string `json:"solution_steps"`
	DataStructure string   `json:"data_structure"`
	TimeEstimate  string   `json:"time_estimate"`
}

// PracticeBank contains sample problems for each shape
var PracticeBank = []PracticeProblem{
	// LINEAR ARRANGEMENT
	{
		ID:         "linear-001",
		Title:      "The Movie Theater",
		Shape:      ShapeLinear,
		Difficulty: "Easy",
		Setup: `Five friends - Amit, Bala, Chitra, Deepa, and Esha - are sitting in a row of five seats in a movie theater. The seats are numbered 1 to 5 from left to right.

• Amit is sitting at one of the ends.
• Bala is sitting exactly in the middle (seat 3).
• Chitra is not adjacent to Amit.
• Deepa is sitting to the right of Esha.`,
		Questions: []Question{
			{
				Number:  1,
				Text:    "If Amit is in seat 1, who can be in seat 2?",
				Options: []string{"A) Only Chitra", "B) Only Deepa", "C) Only Esha", "D) Either Deepa or Esha"},
				Answer:  "D",
				Why:     "Chitra can't be adjacent to Amit (seat 1), so seat 2 must be Deepa or Esha. Both are possible since we only know Deepa is right of Esha somewhere.",
			},
			{
				Number:  2,
				Text:    "What is the maximum number of seats between Deepa and Esha?",
				Options: []string{"A) 1", "B) 2", "C) 3", "D) 4"},
				Answer:  "B",
				Why:     "Esha must be left of Deepa. If Esha is in seat 1 (Amit's spot) - wait, Amit is at an end. If Amit is seat 1, Esha could be seat 2, Deepa seat 5 = 2 seats between. If Amit is seat 5, Esha seat 1, Deepa seat 4 = 2 seats between.",
			},
		},
		SaratBreakdown: Breakdown{
			Shape:        "LINEAR",
			WhyThisShape: "Keywords: 'row', 'seats numbered 1 to 5', 'left to right', 'ends', 'adjacent'",
			Entities:     []string{"Amit", "Bala", "Chitra", "Deepa", "Esha"},
			Constraints: []string{
				"Amit → seat 1 OR seat 5 (end)",
				"Bala → seat 3 (fixed!)",
				"Chitra NOT adjacent to Amit",
				"Deepa RIGHT OF Esha (Esha...Deepa)",
			},
			Anchor:    "Bala in seat 3",
			WhyAnchor: "Bala's position is FIXED. This is our anchor. Amit is also constrained to ends.",
			Solution: []string{
				"1. Draw: [ 1 | 2 | 3 | 4 | 5 ]",
				"2. Fix Bala: [ _ | _ | B | _ | _ ]",
				"3. Amit at end: [ A | _ | B | _ | _ ] OR [ _ | _ | B | _ | A ]",
				"4. Chitra not adjacent to Amit: If Amit=1, Chitra≠2. If Amit=5, Chitra≠4",
				"5. Deepa right of Esha: Place E before D in remaining slots",
				"6. Try both Amit positions, fill in Chitra, Deepa, Esha",
			},
			DataStructure: "[ _ | _ | B | _ | _ ] with position labels 1-5",
			TimeEstimate:  "4-5 minutes",
		},
	},

	// CIRCULAR ARRANGEMENT
	{
		ID:         "circular-001",
		Title:      "The Round Table Meeting",
		Shape:      ShapeCircular,
		Difficulty: "Medium",
		Setup: `Eight people - P, Q, R, S, T, U, V, and W - are sitting around a circular table facing the center.

• P sits third to the left of Q.
• R sits opposite to P.
• S sits between P and T.
• U is not adjacent to R or P.
• V sits second to the right of W.`,
		Questions: []Question{
			{
				Number:  1,
				Text:    "Who sits opposite to Q?",
				Options: []string{"A) S", "B) T", "C) U", "D) V"},
				Answer:  "B",
				Why:     "Fix P at position 1. Q is 3 to the right of P (position 4). Opposite to Q (position 4) is position 8. Work through constraints to find T at position 8.",
			},
		},
		SaratBreakdown: Breakdown{
			Shape:        "CIRCULAR",
			WhyThisShape: "Keywords: 'circular table', 'facing the center', 'opposite', 'left of', 'right of'",
			Entities:     []string{"P", "Q", "R", "S", "T", "U", "V", "W"},
			Constraints: []string{
				"P is 3 LEFT of Q (so Q is 3 RIGHT of P)",
				"R OPPOSITE P",
				"S BETWEEN P and T",
				"U NOT adjacent to R or P",
				"V is 2 RIGHT of W",
			},
			Anchor:    "P (fix arbitrarily at position 1)",
			WhyAnchor: "In circular arrangements, ALWAYS fix one person first to eliminate rotational symmetry. P has the most connections.",
			Solution: []string{
				"1. Draw circle with 8 positions (1-8)",
				"2. FIX P at position 1 (arbitrary but necessary)",
				"3. Q is 3 right of P → Q at position 4",
				"4. R opposite P → R at position 5 (1+4 in circle of 8)",
				"5. S between P and T → S at 2 or 8, T on other side",
				"6. Apply U constraint (not adjacent to R or P)",
				"7. Apply V-W constraint (V is 2 right of W)",
			},
			DataStructure: "Circle with P fixed at 12 o'clock position",
			TimeEstimate:  "6-7 minutes",
		},
	},

	// SELECTION
	{
		ID:         "selection-001",
		Title:      "The Committee",
		Shape:      ShapeSelection,
		Difficulty: "Medium",
		Setup: `A committee of 5 members is to be formed from 4 men (A, B, C, D) and 4 women (P, Q, R, S).

• The committee must have at least 2 men and at least 2 women.
• If A is selected, B must also be selected.
• If P is selected, Q cannot be selected.
• C and R cannot both be on the committee.`,
		Questions: []Question{
			{
				Number:  1,
				Text:    "If A is selected, what is the maximum number of women on the committee?",
				Options: []string{"A) 2", "B) 3", "C) 4", "D) Cannot be determined"},
				Answer:  "A",
				Why:     "If A selected → B must be selected. That's 2 men. Committee needs 5 people with at least 2 men and 2 women. With A and B fixed, we need 3 more. At least 2 must be women. But we also need at least 2 men total (satisfied). Max women = 5 - 2 = 3? No wait, 'at least 2 men' means we could have 2 men + 3 women. So max women = 3.",
			},
		},
		SaratBreakdown: Breakdown{
			Shape:        "SELECTION",
			WhyThisShape: "Keywords: 'committee', 'formed from', 'selected', 'at least', 'cannot'",
			Entities:     []string{"Men: A, B, C, D", "Women: P, Q, R, S"},
			Constraints: []string{
				"Total = 5 members",
				"Men ≥ 2",
				"Women ≥ 2",
				"A → B (If A then B)",
				"P → ¬Q (If P then not Q)",
				"¬(C ∧ R) (Not both C and R)",
			},
			Anchor:    "The gender constraints (≥2 men, ≥2 women)",
			WhyAnchor: "This limits us to only 3 valid compositions: 2M+3W, 3M+2W, or impossible 4M+1W/1M+4W",
			Solution: []string{
				"1. Valid compositions: 2M+3W or 3M+2W only",
				"2. List forced selections: If A → must have B",
				"3. List forbidden pairs: P+Q can't coexist, C+R can't coexist",
				"4. For each question, apply constraints and count possibilities",
			},
			DataStructure: "Two checklists: Men [A B C D], Women [P Q R S]",
			TimeEstimate:  "5-6 minutes",
		},
	},

	// RANKING
	{
		ID:         "ranking-001",
		Title:      "The Race",
		Shape:      ShapeRanking,
		Difficulty: "Easy",
		Setup: `Six runners - J, K, L, M, N, and O - participated in a race. No two runners finished at the same time.

• J finished before K but after L.
• M finished immediately after N.
• O did not finish first or last.
• Exactly two runners finished between J and M.`,
		Questions: []Question{
			{
				Number:  1,
				Text:    "Who finished first?",
				Options: []string{"A) J", "B) L", "C) M", "D) N"},
				Answer:  "B",
				Why:     "From L > J > K, L is before J. From the constraints, L must be first since J can't be first (L is before J) and O can't be first.",
			},
		},
		SaratBreakdown: Breakdown{
			Shape:        "RANKING",
			WhyThisShape: "Keywords: 'race', 'finished before', 'finished after', 'first', 'last', 'immediately after'",
			Entities:     []string{"J", "K", "L", "M", "N", "O"},
			Constraints: []string{
				"L > J > K (L before J before K)",
				"N immediately before M (NM together)",
				"O ≠ 1st, O ≠ 6th",
				"Exactly 2 runners between J and M",
			},
			Anchor:    "The L > J > K chain",
			WhyAnchor: "This gives us a fixed ordering of 3 people. Build around it.",
			Solution: []string{
				"1. Write chain: L ... J ... K",
				"2. NM must be consecutive (treat as unit)",
				"3. 2 runners between J and M → positions differ by 3",
				"4. O not at ends → O in positions 2-5",
				"5. Try placing NM unit, check all constraints",
			},
			DataStructure: "Ranking: 1st [ ] 2nd [ ] 3rd [ ] 4th [ ] 5th [ ] 6th [ ]",
			TimeEstimate:  "5-6 minutes",
		},
	},

	// GRID/MATRIX
	{
		ID:         "grid-001",
		Title:      "The Office Seating",
		Shape:      ShapeGrid,
		Difficulty: "Hard",
		Setup: `In an office, 6 employees (A, B, C, D, E, F) sit in a 2×3 grid (2 rows, 3 columns). Each employee belongs to one of three departments: HR, Tech, or Sales.

Row 1: [Col1] [Col2] [Col3]
Row 2: [Col1] [Col2] [Col3]

• A and B are in the same row.
• C is in Tech and sits in column 2.
• D is directly below A.
• E is in HR and is not in the same column as F.
• No two employees in the same row are from the same department.
• Each department has exactly 2 employees.`,
		Questions: []Question{
			{
				Number:  1,
				Text:    "If A is in HR, which column must F be in?",
				Options: []string{"A) Column 1", "B) Column 2", "C) Column 3", "D) Cannot be determined"},
				Answer:  "C",
				Why:     "C is in Col2. If A is HR in Row1, D is below A. E is HR and not same column as F. Work through the department constraint (no same dept in row) to find F must be Col3.",
			},
		},
		SaratBreakdown: Breakdown{
			Shape:        "GRID",
			WhyThisShape: "Keywords: '2×3 grid', 'rows', 'columns', 'directly below', 'same row'",
			Entities:     []string{"Employees: A, B, C, D, E, F", "Departments: HR, Tech, Sales"},
			Constraints: []string{
				"A, B same row",
				"C = Tech, Column 2",
				"D directly below A",
				"E = HR, E and F different columns",
				"No same department in same row",
				"Each department has exactly 2 people",
			},
			Anchor:    "C in Column 2 (Tech)",
			WhyAnchor: "C's position AND department are both fixed. This is the most constrained.",
			Solution: []string{
				"1. Draw 2×3 grid, mark C in Col2",
				"2. D below A → if A in Row1, D in Row2 same column",
				"3. A, B same row → they're both in Row1 or both in Row2",
				"4. Apply department constraint row by row",
				"5. E is HR, different column from F",
			},
			DataStructure: "2×3 matrix with employee names AND department labels",
			TimeEstimate:  "8-10 minutes",
		},
	},
}

// GetPracticeByShape returns problems of a specific shape
func GetPracticeByShape(shape ProblemShape) []PracticeProblem {
	var result []PracticeProblem
	for _, p := range PracticeBank {
		if p.Shape == shape {
			result = append(result, p)
		}
	}
	return result
}

// GetPracticeByDifficulty returns problems of a specific difficulty
func GetPracticeByDifficulty(difficulty string) []PracticeProblem {
	var result []PracticeProblem
	for _, p := range PracticeBank {
		if p.Difficulty == difficulty {
			result = append(result, p)
		}
	}
	return result
}

// GetRandomPractice returns a random practice problem
func GetRandomPractice() PracticeProblem {
	return PracticeBank[rand.Intn(len(PracticeBank))]
}

// AnalyzeProblem takes raw problem text and returns Sarat-style analysis
func AnalyzeProblem(problemText string) ProblemAnalysis {
	matches := DetectShape(problemText)

	var primaryShape ProblemShape = ShapeHybrid
	var confidence float64 = 0
	if len(matches) > 0 {
		primaryShape = matches[0].Shape
		confidence = matches[0].Confidence
	}

	template := SolutionTemplates[primaryShape]

	return ProblemAnalysis{
		DetectedShape:  primaryShape,
		Confidence:     confidence,
		AllMatches:     matches,
		Template:       template,
		Description:    ShapeDescription[primaryShape],
		Method:         TheSaratMethod,
		QuickReference: QuickRef(),
	}
}

// ProblemAnalysis is the full analysis output
type ProblemAnalysis struct {
	DetectedShape  ProblemShape     `json:"detected_shape"`
	Confidence     float64          `json:"confidence"`
	AllMatches     []ShapeMatch     `json:"all_matches"`
	Template       SolutionTemplate `json:"template"`
	Description    string           `json:"description"`
	Method         SaratMethod      `json:"method"`
	QuickReference string           `json:"quick_reference"`
}

// GenerateHint provides a contextual hint based on where student is stuck
func GenerateHint(shape ProblemShape, stuckAt string) string {
	hints := map[string]string{
		"start":       "Don't read questions yet! First identify all entities and list ALL constraints.",
		"constraints": "Write each constraint as a simple statement. 'A before B' → A...B. 'Not adjacent' → A_X_B",
		"anchor":      "Find the element with MOST constraints. Or in circular, just fix anyone at position 1.",
		"building":    "Start from anchor, apply ONE constraint at a time. If stuck, try the other possibility.",
		"verify":      "Re-read the question. 'Must be true' vs 'Could be true' vs 'Cannot be true' are different!",
	}

	if hint, ok := hints[stuckAt]; ok {
		return hint
	}

	// Shape-specific hints
	shapeHints := map[ProblemShape]string{
		ShapeLinear:    "Draw boxes in a row. Number them. Fill the FIXED positions first.",
		ShapeCircular:  "FIX ONE PERSON at 12 o'clock. Everything else is relative to them.",
		ShapeGrid:      "Make a table. Rows = one attribute, Columns = another. Mark X for impossible.",
		ShapeRanking:   "Draw the inequality chain. A > B > C. Use transitivity!",
		ShapeSelection: "List MUST-HAVE first, then CAN'T-HAVE, then fill remaining slots.",
	}

	if hint, ok := shapeHints[shape]; ok {
		return hint
	}

	return "Re-read the problem. You probably missed a constraint."
}

// FormatProblemForPractice formats a problem nicely for display
func FormatProblemForPractice(p PracticeProblem) string {
	result := fmt.Sprintf(`
╔══════════════════════════════════════════════════════════════════════════════╗
║  %s
║  Shape: %s | Difficulty: %s
╠══════════════════════════════════════════════════════════════════════════════╣

%s

`, p.Title, p.Shape, p.Difficulty, p.Setup)

	for _, q := range p.Questions {
		result += fmt.Sprintf(`
Q%d. %s
%s

`, q.Number, q.Text, formatOptions(q.Options))
	}

	result += `
╠══════════════════════════════════════════════════════════════════════════════╣
║  💡 SARAT BREAKDOWN (Don't peek until you've tried!)
╠══════════════════════════════════════════════════════════════════════════════╣
`
	result += fmt.Sprintf(`
Shape: %s
Why: %s

Entities: %v

Constraints:
`, p.SaratBreakdown.Shape, p.SaratBreakdown.WhyThisShape, p.SaratBreakdown.Entities)

	for _, c := range p.SaratBreakdown.Constraints {
		result += fmt.Sprintf("  • %s\n", c)
	}

	result += fmt.Sprintf(`
Anchor: %s
Why: %s

Data Structure: %s

Solution Steps:
`, p.SaratBreakdown.Anchor, p.SaratBreakdown.WhyAnchor, p.SaratBreakdown.DataStructure)

	for _, s := range p.SaratBreakdown.Solution {
		result += fmt.Sprintf("  %s\n", s)
	}

	result += fmt.Sprintf(`
⏱️ Target Time: %s
`, p.SaratBreakdown.TimeEstimate)

	return result
}

func formatOptions(options []string) string {
	result := ""
	for _, o := range options {
		result += fmt.Sprintf("    %s\n", o)
	}
	return result
}
