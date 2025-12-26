// Package reasoning - Example of proof-enhanced reasoning output
package reasoning

import (
	"encoding/json"
	"fmt"
)

// ExampleProofIntegration demonstrates how proof badges appear in reasoning
func ExampleProofIntegration() {
	engine := NewEngine()

	// Create a session
	session, _ := engine.NewSession("Analyze population patterns in downtown area")

	// Simulate the 4-phase workflow
	session.Analyze([]string{
		"Identified 3 key demographic clusters",
		"Found correlation with transit accessibility",
	})

	session.Synthesize([]string{
		"Optimal placement: near transit hubs",
		"Expected reach: 75% of target population",
	})

	session.Conclude("Recommend establishing community centers near subway stations A, B, and C")

	// Show formatted log
	fmt.Println("=== FORMATTED LOG ===")
	fmt.Println(session.GetThinkingLog())

	// Show JSON output (for WebSocket streaming)
	fmt.Println("\n=== JSON OUTPUT (for frontend) ===")
	for i, step := range session.Steps {
		stepJSON, _ := json.MarshalIndent(map[string]interface{}{
			"step":         i + 1,
			"phase":        step.Phase.String(),
			"description":  step.Description,
			"confidence":   step.Confidence,
			"proof_badge":  step.ProofBadge,
			"proof_detail": step.ProofDetail,
		}, "", "  ")
		fmt.Println(string(stepJSON))
	}
}

/*
EXPECTED OUTPUT:

=== FORMATTED LOG ===
Session session_xxx - analyze task
────────────────────────────────────────────────────────────
📥 [Intake] 70% - Receiving and classifying request
   🔬 Proof: QuaternionS³ - State encoded as unit quaternion on S³ manifold (||q|| = 1)
📥 [Intake] 80% - Classified as analyze task (cluster 5)
   🔬 Proof: QuaternionS³ - State encoded as unit quaternion on S³ manifold (||q|| = 1)
🔍 [Analysis] 80% - Identified 3 key demographic clusters
   🔬 Proof: DigitalRoots - Feature extraction O(1) - Vedic mathematics (53× speedup)
🔍 [Analysis] 80% - Found correlation with transit accessibility
   🔬 Proof: DigitalRoots - Feature extraction O(1) - Vedic mathematics (53× speedup)
🔧 [Synthesis] 85% - Optimal placement: near transit hubs
   🔬 Proof: MirzakhaniGeodesics - Geodesic flow on hyperbolic manifold (shortest path)
🔧 [Synthesis] 85% - Expected reach: 75% of target population
   🔬 Proof: MirzakhaniGeodesics - Geodesic flow on hyperbolic manifold (shortest path)
💡 [Insight] 90% - Formulating recommendation
   🔬 Proof: SATOrigami - 87.532% satisfaction via SLERP convergence (thermodynamic limit)
💡 [Insight] 95% - Recommend establishing community centers near subway stations A, B, and C
   🔬 Proof: SATOrigami - 87.532% satisfaction via SLERP convergence (thermodynamic limit)

=== JSON OUTPUT (for frontend) ===
{
  "step": 1,
  "phase": "Intake",
  "description": "Receiving and classifying request",
  "confidence": 0.7,
  "proof_badge": "QuaternionS³",
  "proof_detail": "State encoded as unit quaternion on S³ manifold (||q|| = 1)"
}
{
  "step": 2,
  "phase": "Intake",
  "description": "Classified as analyze task (cluster 5)",
  "confidence": 0.8,
  "proof_badge": "QuaternionS³",
  "proof_detail": "State encoded as unit quaternion on S³ manifold (||q|| = 1)"
}
... (and so on for all steps)

FRONTEND DISPLAY IDEAS:
1. Show proof badge as tooltip on hover
2. Clicking badge opens modal with full Lean proof
3. Visual indicator (🔬 badge) shows mathematical rigor
4. Link directly to GitHub proof file
5. Show proof file location: asymmetrica_proofs/AsymmetricaProofs/<badge>.lean
*/
