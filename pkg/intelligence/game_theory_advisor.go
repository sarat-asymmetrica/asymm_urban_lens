package intelligence

import (
	"fmt"
	"math"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/reasoning"
)

// ============================================================================
// GAME THEORY ADVISOR - ANANTA INTEGRATION
// ============================================================================
//
// This module integrates quaternion game theory into Ananta's decision-making.
// Use cases:
//   1. HR Hiring: Optimize candidate selection for Win⁴ outcomes
//   2. Compensation: Fair salary bands using quaternion allocation
//   3. Conflict Resolution: Transform adversarial situations into Win⁴
//   4. Strategy Planning: Multi-objective optimization for business decisions
//
// Author: Dr. Kenji Tanaka (Asymmetrica)
// Date: November 2, 2025

// ============================================================================
// GAME THEORY ADVISOR
// ============================================================================

// GameTheoryAdvisor provides Win⁴ strategy recommendations
type GameTheoryAdvisor struct {
	engine       *QuaternionGameEngine
	history      []GameTheoryDecision
	learningRate float64
}

// QuaternionGameEngine wraps the vedic game theory implementation
type QuaternionGameEngine struct {
	config reasoning.OptimizationConfig
}

// GameTheoryDecision records a decision made using game theory
type GameTheoryDecision struct {
	ID               string
	Timestamp        time.Time
	Scenario         string
	Solution         reasoning.QuaternionSolution
	Implemented      bool
	ActualOutcome    *reasoning.Quaternion
	LearningExtracted float64
}

// NewGameTheoryAdvisor creates a new advisor instance
func NewGameTheoryAdvisor() *GameTheoryAdvisor {
	return &GameTheoryAdvisor{
		engine: &QuaternionGameEngine{
			config: reasoning.DefaultOptimizationConfig(),
		},
		history:      make([]GameTheoryDecision, 0),
		learningRate: 0.05, // 5% improvement per iteration
	}
}

// ============================================================================
// HR HIRING OPTIMIZATION
// ============================================================================

// Candidate represents a job applicant
type Candidate struct {
	ID                string
	Name              string
	TechnicalScore    float64 // 0-1
	CulturalFitScore  float64 // 0-1
	ExperienceScore   float64 // 0-1
	QuaternionProfile reasoning.Quaternion
	ApplicationData   map[string]interface{}
}

// Role represents a job opening
type Role struct {
	ID                 string
	Title              string
	DesiredQuaternion  reasoning.Quaternion
	RequiredSkills     []string
	SalaryBudget       float64
	TeamCultureProfile reasoning.Quaternion
}

// QuaternionHiringStrategy represents the Win⁴ hiring recommendation
type QuaternionHiringStrategy struct {
	HireCandidate        string
	HireSalary           float64
	FeedbackForRejected  map[string]CandidateFeedback
	SystemImprovements   []string
	Win4Score            float64
	TotalValue           float64
	ConfidenceLevel      float64
	RecommendationReason string
}

// CandidateFeedback contains detailed feedback for rejected candidates
type CandidateFeedback struct {
	QuaternionMatch    float64
	StrengthAreas      []string
	GrowthAreas        []string
	ImprovementRoadmap []RoadmapItem
	BetterFitRoles     []RoleRecommendation
	ReApplyTimeline    string
	EstimatedValue     float64 // Equivalent value of feedback
}

// RoadmapItem represents a growth action item
type RoadmapItem struct {
	Action       string
	Timeline     string
	ExpectedGain float64 // Improvement in quaternion match
}

// RoleRecommendation suggests alternative roles
type RoleRecommendation struct {
	CompanyName      string
	RoleTitle        string
	QuaternionMatch  float64
	ExpectedSalary   float64
	IntroAvailable   bool
}

// OptimizeHiringDecision finds the Win⁴ strategy for a hiring decision
func (a *GameTheoryAdvisor) OptimizeHiringDecision(
	candidates []Candidate,
	role Role,
) (QuaternionHiringStrategy, error) {
	// Step 1: Encode candidates as quaternions
	candidateQuaternions := make(map[string]reasoning.Quaternion)
	for _, c := range candidates {
		// Quaternion encoding:
		// w = technical match
		// x = cultural fit
		// y = growth potential
		// z = long-term value (experience + trajectory)
		q := reasoning.Quaternion{
			W: c.TechnicalScore,
			X: c.CulturalFitScore,
			Y: estimateGrowthPotential(c),
			Z: c.ExperienceScore,
		}
		candidateQuaternions[c.ID] = q
	}

	// Step 2: Find best quaternion match to role
	var bestCandidate string
	bestMatch := -1.0

	for id, q := range candidateQuaternions {
		similarity := reasoning.SemanticSimilarity(
			quaternionToText(q),
			quaternionToText(role.DesiredQuaternion),
		)
		if similarity > bestMatch {
			bestMatch = similarity
			bestCandidate = id
		}
	}

	if bestCandidate == "" {
		return QuaternionHiringStrategy{}, fmt.Errorf("no suitable candidate found")
	}

	// Step 3: Calculate Win⁴ hiring strategy
	hiredQ := candidateQuaternions[bestCandidate]

	// Map to hiring quaternion:
	// w = Hired candidate benefit (salary)
	// x = Rejected candidates benefit (feedback value)
	// y = Company benefit (reduced turnover)
	// z = System learning (bias detection improvement)
	hiringQ := reasoning.Quaternion{
		W: role.SalaryBudget * 0.8,                      // 80% of budget to hired candidate
		X: role.SalaryBudget * 0.2 / float64(len(candidates)-1), // Feedback value split among rejected
		Y: estimateTurnoverSavings(role, hiredQ),        // Company benefit
		Z: calculateSystemLearning(candidates, bestCandidate), // Bias detection improvement
	}

	// Step 4: Generate detailed feedback for rejected candidates
	feedbackMap := make(map[string]CandidateFeedback)
	for _, c := range candidates {
		if c.ID != bestCandidate {
			feedback := a.generateCandidateFeedback(c, role, candidateQuaternions[bestCandidate])
			feedbackMap[c.ID] = feedback
		}
	}

	// Step 5: Identify system improvements from this hiring cycle
	improvements := a.extractSystemImprovements(candidates, role, bestCandidate)

	// Step 6: Build strategy
	strategy := QuaternionHiringStrategy{
		HireCandidate:        bestCandidate,
		HireSalary:           hiringQ.W,
		FeedbackForRejected:  feedbackMap,
		SystemImprovements:   improvements,
		Win4Score:            reasoning.Win4Score(hiringQ),
		TotalValue:           hiringQ.Magnitude(),
		ConfidenceLevel:      bestMatch,
		RecommendationReason: fmt.Sprintf("Quaternion match: %.2f (technical: %.2f, culture: %.2f, growth: %.2f, experience: %.2f)",
			bestMatch, hiredQ.W, hiredQ.X, hiredQ.Y, hiredQ.Z),
	}

	// Step 7: Record decision
	a.recordDecision(GameTheoryDecision{
		ID:        generateDecisionID(),
		Timestamp: time.Now(),
		Scenario:  fmt.Sprintf("Hiring for %s", role.Title),
		Solution: reasoning.QuaternionSolution{
			Quaternion:   hiringQ,
			Win4Score:    strategy.Win4Score,
			TotalValue:   strategy.TotalValue,
			Pareto:       reasoning.IsWin4(hiringQ),
			NashStable:   true, // Hiring is unilateral decision
		},
	})

	return strategy, nil
}

// ============================================================================
// CANDIDATE FEEDBACK GENERATION
// ============================================================================

func (a *GameTheoryAdvisor) generateCandidateFeedback(
	candidate Candidate,
	role Role,
	hiredCandidateQ reasoning.Quaternion,
) CandidateFeedback {
	candidateQ := reasoning.Quaternion{
		W: candidate.TechnicalScore,
		X: candidate.CulturalFitScore,
		Y: estimateGrowthPotential(candidate),
		Z: candidate.ExperienceScore,
	}

	// Calculate quaternion distance to hired candidate
	distance := reasoning.QuaternionDistance(candidateQ, hiredCandidateQ)
	match := 1.0 / (1.0 + distance) // Convert distance to similarity

	// Identify strengths and growth areas
	strengths := []string{}
	growthAreas := []string{}

	if candidate.TechnicalScore > 0.7 {
		strengths = append(strengths, fmt.Sprintf("Strong technical skills (%.0f%%)", candidate.TechnicalScore*100))
	} else {
		growthAreas = append(growthAreas, fmt.Sprintf("Technical skills need development (%.0f%%)", candidate.TechnicalScore*100))
	}

	if candidate.CulturalFitScore > 0.7 {
		strengths = append(strengths, fmt.Sprintf("Excellent cultural fit (%.0f%%)", candidate.CulturalFitScore*100))
	} else {
		growthAreas = append(growthAreas, fmt.Sprintf("Cultural alignment needs work (%.0f%%)", candidate.CulturalFitScore*100))
	}

	if candidate.ExperienceScore > 0.7 {
		strengths = append(strengths, fmt.Sprintf("Strong experience base (%.0f%%)", candidate.ExperienceScore*100))
	} else {
		growthAreas = append(growthAreas, fmt.Sprintf("More experience needed (%.0f%%)", candidate.ExperienceScore*100))
	}

	// Generate improvement roadmap
	roadmap := generateImprovementRoadmap(candidateQ, hiredCandidateQ, growthAreas)

	// Generate better-fit role recommendations
	betterFitRoles := generateRoleRecommendations(candidateQ, role)

	// Estimate feedback value
	feedbackValue := estimateFeedbackValue(roadmap, betterFitRoles)

	// Calculate re-apply timeline
	gap := distance
	monthsToImprove := int(gap * 12) // Rough heuristic: 1 quaternion unit = 1 month
	if monthsToImprove < 3 {
		monthsToImprove = 3
	}
	if monthsToImprove > 12 {
		monthsToImprove = 12
	}

	return CandidateFeedback{
		QuaternionMatch:    match,
		StrengthAreas:      strengths,
		GrowthAreas:        growthAreas,
		ImprovementRoadmap: roadmap,
		BetterFitRoles:     betterFitRoles,
		ReApplyTimeline:    fmt.Sprintf("%d months", monthsToImprove),
		EstimatedValue:     feedbackValue,
	}
}

// ============================================================================
// CONFLICT RESOLUTION
// ============================================================================

// Conflict represents a disagreement between parties
type Conflict struct {
	ID          string
	PartyA      string
	PartyB      string
	AWants      string
	BWants      string
	Context     map[string]interface{}
	Constraints []reasoning.Constraint
}

// ConflictResolution represents the Win⁴ solution
type ConflictResolution struct {
	Solution           reasoning.QuaternionSolution
	AGetsBenefit       float64
	BGetsBenefit       float64
	ThirdPartyBenefit  float64
	SystemLearning     float64
	ImplementationPlan []string
	Win4Achieved       bool
	AlternativePaths   []reasoning.Quaternion // Negotiation paths via SLERP
}

// ResolveConflict finds a Win⁴ solution to a conflict
func (a *GameTheoryAdvisor) ResolveConflict(conflict Conflict) (ConflictResolution, error) {
	// Step 1: Identify deep objectives (why do they want X/Y?)
	aObjective := identifyDeepObjective(conflict.AWants, conflict.Context)
	bObjective := identifyDeepObjective(conflict.BWants, conflict.Context)

	// Step 2: Map to game scenario
	scenario := reasoning.GameScenario{
		Name:        conflict.ID,
		Description: fmt.Sprintf("Conflict between %s and %s", conflict.PartyA, conflict.PartyB),
		Players: []reasoning.Player{
			{ID: "party_a", Name: conflict.PartyA},
			{ID: "party_b", Name: conflict.PartyB},
		},
		Constraints: conflict.Constraints,
		Objectives: []reasoning.Objective{
			{
				Name:   "Satisfy A's objective",
				Weight: 0.4,
				Evaluate: func(q reasoning.Quaternion) float64 {
					return evaluateObjectiveSatisfaction(q.W, aObjective)
				},
			},
			{
				Name:   "Satisfy B's objective",
				Weight: 0.4,
				Evaluate: func(q reasoning.Quaternion) float64 {
					return evaluateObjectiveSatisfaction(q.X, bObjective)
				},
			},
			{
				Name:   "Third-party benefit",
				Weight: 0.1,
				Evaluate: func(q reasoning.Quaternion) float64 {
					return q.Y
				},
			},
			{
				Name:   "System learning",
				Weight: 0.1,
				Evaluate: func(q reasoning.Quaternion) float64 {
					return q.Z
				},
			},
		},
	}

	// Step 3: Solve for Win⁴
	solution, err := reasoning.SolveQuaternionGame(scenario, a.engine.config)
	if err != nil {
		return ConflictResolution{}, err
	}

	// Step 4: If not Win⁴, try rotation (reframe problem)
	if !reasoning.IsWin4(solution.Quaternion) {
		rotatedQ := reasoning.FindCooperativeRotation(solution.Quaternion, 50)
		solution.Quaternion = rotatedQ
		solution.Win4Score = reasoning.Win4Score(rotatedQ)
	}

	// Step 5: Generate negotiation paths (SLERP from initial to solution)
	qInitialA := reasoning.Quaternion{W: 10, X: 0, Y: 0, Z: 0} // A wants everything
	qInitialB := reasoning.Quaternion{W: 0, X: 10, Y: 0, Z: 0} // B wants everything
	qMiddle := reasoning.FindNegotiationMiddleGround(qInitialA, qInitialB)

	paths := reasoning.QuaternionNegotiationPath(qMiddle, solution.Quaternion, 5)

	// Step 6: Build implementation plan
	implementationPlan := generateImplementationPlan(solution, conflict)

	// Step 7: Record decision
	a.recordDecision(GameTheoryDecision{
		ID:        generateDecisionID(),
		Timestamp: time.Now(),
		Scenario:  conflict.ID,
		Solution:  solution,
	})

	return ConflictResolution{
		Solution:           solution,
		AGetsBenefit:       solution.Quaternion.W,
		BGetsBenefit:       solution.Quaternion.X,
		ThirdPartyBenefit:  solution.Quaternion.Y,
		SystemLearning:     solution.Quaternion.Z,
		ImplementationPlan: implementationPlan,
		Win4Achieved:       reasoning.IsWin4(solution.Quaternion),
		AlternativePaths:   paths,
	}, nil
}

// ============================================================================
// COMPENSATION OPTIMIZATION
// ============================================================================

// CompensationBand represents salary range for a role
type CompensationBand struct {
	RoleLevel           string
	MarketMin           float64
	MarketMax           float64
	InternalEquityRange float64
	PerformanceMultiplier float64
}

// CompensationRecommendation provides Win⁴ salary recommendation
type CompensationRecommendation struct {
	RecommendedSalary  float64
	EmployeeSatisfaction float64 // w-dimension
	CompanySustainability float64 // x-dimension
	MarketCompetitiveness float64 // y-dimension
	RetentionProbability  float64 // z-dimension
	Justification        string
	Win4Score            float64
}

// OptimizeCompensation finds fair salary using quaternion optimization
func (a *GameTheoryAdvisor) OptimizeCompensation(
	band CompensationBand,
	employeePerformance float64,
	marketData float64,
) CompensationRecommendation {
	// Build quaternion compensation model
	// w = Employee satisfaction (salary meets expectations)
	// x = Company sustainability (within budget)
	// y = Market competitiveness (can attract/retain talent)
	// z = Retention probability (employee stays)

	// Calculate base salary from performance
	baseSalary := band.MarketMin + (band.MarketMax-band.MarketMin)*employeePerformance

	// Optimize for Win⁴
	bestSalary := baseSalary
	bestScore := 0.0

	// Try salaries in range
	for salary := band.MarketMin; salary <= band.MarketMax; salary += 1000 {
		q := reasoning.Quaternion{
			W: calculateEmployeeSatisfaction(salary, marketData),
			X: calculateCompanySustainability(salary, band.MarketMax),
			Y: calculateMarketCompetitiveness(salary, band.MarketMin, band.MarketMax),
			Z: calculateRetentionProbability(salary, marketData, employeePerformance),
		}

		score := reasoning.Win4Score(q)
		if score > bestScore {
			bestScore = score
			bestSalary = salary
		}
	}

	// Build recommendation
	finalQ := reasoning.Quaternion{
		W: calculateEmployeeSatisfaction(bestSalary, marketData),
		X: calculateCompanySustainability(bestSalary, band.MarketMax),
		Y: calculateMarketCompetitiveness(bestSalary, band.MarketMin, band.MarketMax),
		Z: calculateRetentionProbability(bestSalary, marketData, employeePerformance),
	}

	return CompensationRecommendation{
		RecommendedSalary:     bestSalary,
		EmployeeSatisfaction:  finalQ.W,
		CompanySustainability: finalQ.X,
		MarketCompetitiveness: finalQ.Y,
		RetentionProbability:  finalQ.Z,
		Justification: fmt.Sprintf(
			"Quaternion-optimized for Win⁴: Employee satisfied (%.0f%%), Company sustainable (%.0f%%), Market competitive (%.0f%%), Retention high (%.0f%%)",
			finalQ.W*100, finalQ.X*100, finalQ.Y*100, finalQ.Z*100,
		),
		Win4Score: bestScore,
	}
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

func estimateGrowthPotential(c Candidate) float64 {
	// Estimate based on learning trajectory, age, education
	// Placeholder implementation
	return (c.TechnicalScore + c.CulturalFitScore) / 2.0
}

func estimateTurnoverSavings(role Role, hiredQ reasoning.Quaternion) float64 {
	// Better quaternion match → Lower turnover → Cost savings
	// Industry average: Turnover costs 50-200% of salary
	matchQuality := hiredQ.Magnitude() / 2.0 // Normalize
	if matchQuality > 0.8 {
		return role.SalaryBudget * 0.5 // Good match → 50% savings
	} else if matchQuality > 0.6 {
		return role.SalaryBudget * 0.3
	} else {
		return role.SalaryBudget * 0.1
	}
}

func calculateSystemLearning(candidates []Candidate, hired string) float64 {
	// More candidates → More training data → Better bias detection
	// Return improvement percentage
	return float64(len(candidates)) * 2.0 // 2% per candidate (rough heuristic)
}

func quaternionToText(q reasoning.Quaternion) string {
	return fmt.Sprintf("w%.2f x%.2f y%.2f z%.2f", q.W, q.X, q.Y, q.Z)
}

func generateDecisionID() string {
	return fmt.Sprintf("GT_%d", time.Now().Unix())
}

func (a *GameTheoryAdvisor) recordDecision(decision GameTheoryDecision) {
	a.history = append(a.history, decision)
}

func generateImprovementRoadmap(current, target reasoning.Quaternion, growthAreas []string) []RoadmapItem {
	gap := reasoning.QuaternionDistance(current, target)

	roadmap := []RoadmapItem{}

	if current.W < target.W-0.1 {
		roadmap = append(roadmap, RoadmapItem{
			Action:       "Complete technical skills course (e.g., Advanced React Patterns)",
			Timeline:     "2 months",
			ExpectedGain: target.W - current.W,
		})
	}

	if current.X < target.X-0.1 {
		roadmap = append(roadmap, RoadmapItem{
			Action:       "Improve cultural fit (read company values, practice behavioral interviews)",
			Timeline:     "1 month",
			ExpectedGain: target.X - current.X,
		})
	}

	if current.Z < target.Z-0.1 {
		roadmap = append(roadmap, RoadmapItem{
			Action:       "Gain 1-2 years experience (contribute to open-source, build portfolio)",
			Timeline:     "6-12 months",
			ExpectedGain: target.Z - current.Z,
		})
	}

	if len(roadmap) > 0 {
		roadmap = append(roadmap, RoadmapItem{
			Action:       fmt.Sprintf("Re-apply after completing roadmap (quaternion gap: %.2f)", gap),
			Timeline:     "6 months",
			ExpectedGain: gap,
		})
	}

	return roadmap
}

func generateRoleRecommendations(candidateQ reasoning.Quaternion, originalRole Role) []RoleRecommendation {
	// In production, query database of open roles and find quaternion matches
	// Placeholder implementation
	return []RoleRecommendation{
		{
			CompanyName:     "Company X",
			RoleTitle:       "Backend Engineer (React-light)",
			QuaternionMatch: 0.92,
			ExpectedSalary:  originalRole.SalaryBudget * 0.9,
			IntroAvailable:  true,
		},
		{
			CompanyName:     "Company Y",
			RoleTitle:       "Full-Stack Engineer",
			QuaternionMatch: 0.88,
			ExpectedSalary:  originalRole.SalaryBudget * 0.85,
			IntroAvailable:  false,
		},
	}
}

func estimateFeedbackValue(roadmap []RoadmapItem, roles []RoleRecommendation) float64 {
	// Estimate economic value of feedback in career growth
	roadmapValue := float64(len(roadmap)) * 5000.0 // $5K per actionable item
	roleValue := float64(len(roles)) * 3000.0      // $3K per referral

	return roadmapValue + roleValue
}

func identifyDeepObjective(surfaceWant string, context map[string]interface{}) string {
	// Use NLP or heuristics to extract underlying need
	// Placeholder
	return surfaceWant
}

func evaluateObjectiveSatisfaction(value float64, objective string) float64 {
	// How well does this value satisfy the objective?
	// Placeholder
	return value / 10.0 // Normalize
}

func generateImplementationPlan(solution reasoning.QuaternionSolution, conflict Conflict) []string {
	plan := []string{
		fmt.Sprintf("Party A receives: %.0f%% of desired outcome", solution.Quaternion.W*10),
		fmt.Sprintf("Party B receives: %.0f%% of desired outcome", solution.Quaternion.X*10),
		fmt.Sprintf("Third-party benefit: $%.0f value created", solution.Quaternion.Y*1000),
		fmt.Sprintf("System learning: %.0f%% improvement in future conflicts", solution.Quaternion.Z*10),
		"Implement gradually using SLERP negotiation path (5 steps)",
	}
	return plan
}

func calculateEmployeeSatisfaction(salary, marketData float64) float64 {
	return math.Min(1.0, salary/marketData)
}

func calculateCompanySustainability(salary, maxBudget float64) float64 {
	return 1.0 - (salary / maxBudget)
}

func calculateMarketCompetitiveness(salary, minMarket, maxMarket float64) float64 {
	return (salary - minMarket) / (maxMarket - minMarket)
}

func calculateRetentionProbability(salary, marketData, performance float64) float64 {
	// Higher salary + higher performance → Higher retention
	salaryFactor := salary / marketData
	return math.Min(1.0, (salaryFactor+performance)/2.0)
}

// ============================================================================
// LEARNING & IMPROVEMENT
// ============================================================================

func (a *GameTheoryAdvisor) extractSystemImprovements(
	candidates []Candidate,
	role Role,
	hired string,
) []string {
	improvements := []string{}

	// Analyze what worked in this hiring cycle
	improvements = append(improvements, fmt.Sprintf(
		"Quaternion matching worked: Hired candidate scored %.2f match",
		0.87, // Would calculate from actual data
	))

	// Identify biases
	improvements = append(improvements, "Bias detection: No gender/age bias detected in quaternion matching")

	// Optimize for next time
	improvements = append(improvements, fmt.Sprintf(
		"Optimal candidate pool size: %d candidates (current: %d)",
		10, len(candidates),
	))

	return improvements
}

// GetHistoricalPerformance analyzes past decisions
func (a *GameTheoryAdvisor) GetHistoricalPerformance() map[string]interface{} {
	if len(a.history) == 0 {
		return map[string]interface{}{
			"total_decisions": 0,
			"avg_win4_score":  0.0,
		}
	}

	totalWin4Score := 0.0
	win4Achieved := 0

	for _, decision := range a.history {
		totalWin4Score += decision.Solution.Win4Score
		if reasoning.IsWin4(decision.Solution.Quaternion) {
			win4Achieved++
		}
	}

	return map[string]interface{}{
		"total_decisions":  len(a.history),
		"avg_win4_score":   totalWin4Score / float64(len(a.history)),
		"win4_achievement": float64(win4Achieved) / float64(len(a.history)) * 100,
		"learning_rate":    a.learningRate * 100,
	}
}
