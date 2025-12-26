package cognition

import (
	"fmt"
	"math"
	"time"
)

// ============================================================================
// VISUALIZATION BUILDER - Generate data for frontend visualization
// ============================================================================
//
// Creates visualization-ready data structures for:
// - Concept graphs (D3.js force-directed layouts)
// - Regime timelines (progress visualization)
// - Digital root distributions (pie/bar charts)
// - Quality metrics (radar charts)
//
// ============================================================================

// VisualizationBuilder generates visualization data
type VisualizationBuilder struct {
	// No state needed - pure transformation functions
}

// NewVisualizationBuilder creates a new builder
func NewVisualizationBuilder() *VisualizationBuilder {
	return &VisualizationBuilder{}
}

// BuildVisualization creates complete visualization data from stream
func (vb *VisualizationBuilder) BuildVisualization(stream *ThoughtStream) *VisualizationData {
	if stream.LastState == nil {
		return &VisualizationData{
			Graph:        &ConceptGraph{Nodes: []*ConceptNode{}, Edges: []*Connection{}},
			Timeline:     &RegimeTimeline{Sessions: []*RegimeSession{}},
			Distribution: &DigitalRootDistribution{Clusters: []*ClusterInfo{}},
			Metrics:      &QualityMetrics{},
			GeneratedAt:  time.Now(),
		}
	}

	return &VisualizationData{
		Graph:        vb.BuildGraph(stream.LastState),
		Timeline:     vb.BuildTimeline(stream),
		Distribution: vb.BuildDistribution(stream.LastState),
		Metrics:      vb.CalculateMetrics(stream),
		GeneratedAt:  time.Now(),
	}
}

// BuildGraph creates concept graph for D3.js visualization
func (vb *VisualizationBuilder) BuildGraph(state *CognitiveState) *ConceptGraph {
	if state == nil || state.ConnectionGraph == nil {
		return &ConceptGraph{
			Nodes: []*ConceptNode{},
			Edges: []*Connection{},
		}
	}

	// Apply force-directed layout
	nodes := vb.layoutNodes(state.ConnectionGraph)

	return &ConceptGraph{
		Nodes: nodes,
		Edges: state.ConnectionGraph.Edges,
	}
}

// layoutNodes applies simple force-directed layout
func (vb *VisualizationBuilder) layoutNodes(graph *ConnectionGraph) []*ConceptNode {
	nodes := make([]*ConceptNode, 0, len(graph.Nodes))

	// Convert map to slice
	for _, node := range graph.Nodes {
		nodes = append(nodes, node)
	}

	// Apply circular layout as starting point
	centerX, centerY := 400.0, 300.0 // Canvas center
	radius := 200.0

	for i, node := range nodes {
		angle := 2 * math.Pi * float64(i) / float64(len(nodes))

		// Adjust radius based on digital root (create rings)
		ringRadius := radius * (1.0 + float64(node.DigitalRoot)*0.1)
		node.X = centerX + ringRadius*math.Cos(angle)
		node.Y = centerY + ringRadius*math.Sin(angle)
	}

	return nodes
}

// BuildTimeline creates regime progression timeline
func (vb *VisualizationBuilder) BuildTimeline(stream *ThoughtStream) *RegimeTimeline {
	timeline := &RegimeTimeline{
		Sessions: []*RegimeSession{},
	}

	// Extract regime transitions from recorded events
	if len(stream.RecordedEvents) == 0 {
		// No recordings - create single session from current state
		if stream.LastState != nil {
			timeline.Sessions = append(timeline.Sessions, &RegimeSession{
				Regime:    stream.CurrentRegime,
				StartTime: stream.StartTime,
				EndTime:   time.Now(),
				Duration:  time.Since(stream.StartTime).Seconds(),
				Progress:  stream.LastState.RegimeProgress,
			})
		}
		return timeline
	}

	// Build timeline from events
	var currentSession *RegimeSession
	for _, event := range stream.RecordedEvents {
		if event.EventType == EventRegimeShift && event.Delta != nil && event.Delta.RegimeChange != nil {
			// Close previous session
			if currentSession != nil {
				currentSession.EndTime = event.Timestamp
				currentSession.Duration = currentSession.EndTime.Sub(currentSession.StartTime).Seconds()
				timeline.Sessions = append(timeline.Sessions, currentSession)
			}

			// Start new session
			currentSession = &RegimeSession{
				Regime:    event.Delta.RegimeChange.To,
				StartTime: event.Timestamp,
				Progress:  0.0,
			}
		}

		// Update progress
		if currentSession != nil && event.CurrentState != nil {
			currentSession.Progress = event.CurrentState.RegimeProgress
		}
	}

	// Close final session
	if currentSession != nil {
		currentSession.EndTime = time.Now()
		currentSession.Duration = currentSession.EndTime.Sub(currentSession.StartTime).Seconds()
		timeline.Sessions = append(timeline.Sessions, currentSession)
	}

	// Validate 30/20/50 distribution
	vb.validateRegimeDistribution(timeline)

	return timeline
}

// validateRegimeDistribution checks if timeline matches 30/20/50 target
func (vb *VisualizationBuilder) validateRegimeDistribution(timeline *RegimeTimeline) {
	totalDuration := 0.0
	explorationDuration := 0.0
	optimizationDuration := 0.0
	stabilizationDuration := 0.0

	for _, session := range timeline.Sessions {
		totalDuration += session.Duration

		switch session.Regime {
		case RegimeExploration:
			explorationDuration += session.Duration
		case RegimeOptimization:
			optimizationDuration += session.Duration
		case RegimeStabilization:
			stabilizationDuration += session.Duration
		}
	}

	if totalDuration > 0 {
		expPct := (explorationDuration / totalDuration) * 100
		optPct := (optimizationDuration / totalDuration) * 100
		stabPct := (stabilizationDuration / totalDuration) * 100

		// Log if deviates significantly from 30/20/50
		if math.Abs(expPct-30) > 10 || math.Abs(optPct-20) > 10 || math.Abs(stabPct-50) > 10 {
			fmt.Printf("⚠️ Regime distribution deviation: %.1f%% / %.1f%% / %.1f%% (target: 30%% / 20%% / 50%%)\n",
				expPct, optPct, stabPct)
		}
	}
}

// BuildDistribution creates digital root cluster distribution
func (vb *VisualizationBuilder) BuildDistribution(state *CognitiveState) *DigitalRootDistribution {
	if state == nil || len(state.ActiveConcepts) == 0 {
		return &DigitalRootDistribution{
			Clusters: []*ClusterInfo{},
		}
	}

	// Count concepts per digital root
	clusterCounts := state.ClusterDistribution

	// Build cluster info
	clusters := make([]*ClusterInfo, 0)
	totalConcepts := len(state.ActiveConcepts)

	for root := uint8(0); root <= 9; root++ {
		count := clusterCounts[root]
		if count == 0 {
			continue
		}

		percentage := (float64(count) / float64(totalConcepts)) * 100

		// Find top concepts in this cluster
		topConcepts := vb.findTopConceptsInCluster(state.ActiveConcepts, root, 3)

		clusters = append(clusters, &ClusterInfo{
			DigitalRoot: root,
			Count:       count,
			Percentage:  percentage,
			TopConcepts: topConcepts,
		})
	}

	return &DigitalRootDistribution{
		Clusters: clusters,
	}
}

// findTopConceptsInCluster finds top N concepts in a digital root cluster
func (vb *VisualizationBuilder) findTopConceptsInCluster(concepts []*QuaternionConcept, digitalRoot uint8, n int) []string {
	// Filter by digital root
	filtered := make([]*QuaternionConcept, 0)
	for _, concept := range concepts {
		if concept.DigitalRoot == digitalRoot {
			filtered = append(filtered, concept)
		}
	}

	// Sort by confidence (simple bubble sort for small N)
	for i := 0; i < len(filtered)-1; i++ {
		for j := i + 1; j < len(filtered); j++ {
			if filtered[j].Confidence > filtered[i].Confidence {
				filtered[i], filtered[j] = filtered[j], filtered[i]
			}
		}
	}

	// Extract labels
	labels := make([]string, 0, n)
	for i := 0; i < n && i < len(filtered); i++ {
		label := vb.extractLabel(filtered[i])
		labels = append(labels, label)
	}

	return labels
}

// extractLabel gets human-readable label from concept
func (vb *VisualizationBuilder) extractLabel(concept *QuaternionConcept) string {
	if label, ok := concept.Data["label"].(string); ok {
		return label
	}
	if text, ok := concept.Data["text"].(string); ok {
		if len(text) > 30 {
			return text[:30] + "..."
		}
		return text
	}
	return fmt.Sprintf("Concept %s", concept.ID.String()[:8])
}

// CalculateMetrics computes quality metrics for session
func (vb *VisualizationBuilder) CalculateMetrics(stream *ThoughtStream) *QualityMetrics {
	if stream.LastState == nil {
		return &QualityMetrics{}
	}

	state := stream.LastState

	// Correctness: Based on confidence
	correctness := state.Confidence

	// Performance: Events per second
	duration := time.Since(stream.StartTime).Seconds()
	performance := 0.0
	if duration > 0 {
		performance = float64(stream.EventCount) / duration
	}

	// Reliability: Inverse of entropy (low entropy = reliable)
	reliability := 1.0 - state.Entropy

	// Synergy: Coherence as proxy for cascade amplification
	synergy := state.Coherence

	// Elegance: Regime progress (how well organized)
	elegance := state.RegimeProgress

	// Unified score: Harmonic mean of all 5 timbres
	unifiedScore := vb.calculateHarmonicMean([]float64{
		correctness,
		performance / 10.0,    // Normalize (assume 10 events/sec is excellent)
		reliability,
		synergy,
		elegance,
	})

	return &QualityMetrics{
		Correctness:  correctness,
		Performance:  performance,
		Reliability:  reliability,
		Synergy:      synergy,
		Elegance:     elegance,
		UnifiedScore: unifiedScore,
	}
}

// calculateHarmonicMean computes rigorous harmonic mean
func (vb *VisualizationBuilder) calculateHarmonicMean(values []float64) float64 {
	return HarmonicMean(values)
}

// BuildRegimeProgressBar creates data for progress bar
func (vb *VisualizationBuilder) BuildRegimeProgressBar(stream *ThoughtStream) map[string]interface{} {
	if stream.LastState == nil {
		return map[string]interface{}{
			"current_regime": string(stream.CurrentRegime),
			"progress":       0.0,
			"target":         vb.getRegimeTarget(stream.CurrentRegime),
		}
	}

	return map[string]interface{}{
		"current_regime": string(stream.CurrentRegime),
		"progress":       stream.LastState.RegimeProgress,
		"target":         vb.getRegimeTarget(stream.CurrentRegime),
		"elapsed":        time.Since(stream.StartTime).Seconds(),
	}
}

// getRegimeTarget returns target percentage for regime
func (vb *VisualizationBuilder) getRegimeTarget(regime Regime) float64 {
	switch regime {
	case RegimeExploration:
		return 0.30 // 30%
	case RegimeOptimization:
		return 0.20 // 20%
	case RegimeStabilization:
		return 0.50 // 50%
	default:
		return 0.33 // Equal split
	}
}

// BuildConnectionStrengthHistogram creates histogram of connection strengths
func (vb *VisualizationBuilder) BuildConnectionStrengthHistogram(state *CognitiveState) map[string]interface{} {
	if state == nil || state.ConnectionGraph == nil {
		return map[string]interface{}{
			"bins":  []int{},
			"labels": []string{},
		}
	}

	// Create 10 bins (0.0-0.1, 0.1-0.2, ..., 0.9-1.0)
	bins := make([]int, 10)

	for _, edge := range state.ConnectionGraph.Edges {
		binIndex := int(edge.Strength * 10)
		if binIndex >= 10 {
			binIndex = 9
		}
		bins[binIndex]++
	}

	labels := []string{
		"0.0-0.1", "0.1-0.2", "0.2-0.3", "0.3-0.4", "0.4-0.5",
		"0.5-0.6", "0.6-0.7", "0.7-0.8", "0.8-0.9", "0.9-1.0",
	}

	return map[string]interface{}{
		"bins":   bins,
		"labels": labels,
		"total_connections": len(state.ConnectionGraph.Edges),
	}
}

// BuildConfidenceOverTime creates time series of confidence
func (vb *VisualizationBuilder) BuildConfidenceOverTime(stream *ThoughtStream) map[string]interface{} {
	if len(stream.RecordedEvents) == 0 {
		return map[string]interface{}{
			"timestamps": []int64{},
			"values":     []float64{},
		}
	}

	timestamps := make([]int64, 0)
	values := make([]float64, 0)

	for _, event := range stream.RecordedEvents {
		if event.CurrentState != nil {
			timestamps = append(timestamps, event.Timestamp.Unix())
			values = append(values, event.CurrentState.Confidence)
		}
	}

	return map[string]interface{}{
		"timestamps": timestamps,
		"values":     values,
	}
}

// ExportForD3 creates D3.js-compatible JSON structure
func (vb *VisualizationBuilder) ExportForD3(viz *VisualizationData) map[string]interface{} {
	return map[string]interface{}{
		"graph": map[string]interface{}{
			"nodes": viz.Graph.Nodes,
			"links": viz.Graph.Edges,
		},
		"timeline": map[string]interface{}{
			"sessions": viz.Timeline.Sessions,
		},
		"distribution": map[string]interface{}{
			"clusters": viz.Distribution.Clusters,
		},
		"metrics": map[string]interface{}{
			"correctness":   viz.Metrics.Correctness,
			"performance":   viz.Metrics.Performance,
			"reliability":   viz.Metrics.Reliability,
			"synergy":       viz.Metrics.Synergy,
			"elegance":      viz.Metrics.Elegance,
			"unified_score": viz.Metrics.UnifiedScore,
		},
		"meta": map[string]interface{}{
			"generated_at": viz.GeneratedAt,
		},
	}
}
