// Package qos - Wave 3: EM Routing (Magnetoreception-Inspired Classification)
// Inspired by eagle cryptochrome magnetoreception
//
// Eagle Biology:
//   - Cryptochromes in retina detect Earth's magnetic field
//   - Quantum entanglement enables directional sensing
//   - Used for navigation, prey tracking, environmental awareness
//
// QOS Application:
//   - Documents have "EM signatures" (MICR ink, RFID tags, NFC chips, paper texture)
//   - Each signature encodes as quaternion "field" on S³
//   - Classification = finding nearest attractor on S³ manifold
//
// Eagle Prediction 2: EM routing = +10-20% classification accuracy
//   WHY: Documents cluster naturally by electromagnetic properties
//   - Checks: MICR ink (magnetic)
//   - IDs: RFID/NFC chips (EM field)
//   - Receipts: Thermal paper (conductivity)
//   - Invoices: Standard paper (dielectric)
//
// Foundation: M⁷⁹ manifold attractors from 187 days of research
package qos

import (
	"fmt"
	"math"
)

// DocumentType represents known document categories
type DocumentType int

const (
	DocUnknown DocumentType = iota
	DocCheck                // Bank check (MICR magnetic ink)
	DocID                   // ID card (RFID/NFC chip)
	DocReceipt              // Thermal receipt (conductive coating)
	DocInvoice              // Standard invoice (plain paper)
	DocContract             // Legal contract (watermark, special paper)
	DocManuscript           // Handwritten (ink absorption)
	DocPassport             // Passport (security features, chips)
	DocTicket               // Ticket (barcode, thermal/offset print)
)

// String returns document type name
func (d DocumentType) String() string {
	names := []string{
		"Unknown",
		"Check",
		"ID Card",
		"Receipt",
		"Invoice",
		"Contract",
		"Manuscript",
		"Passport",
		"Ticket",
	}
	if int(d) < len(names) {
		return names[d]
	}
	return "Unknown"
}

// EMSignature represents electromagnetic signature of a document
//
// Encoding Strategy:
//   - MagneticStrength → W component (scalar field intensity)
//   - RFIDPresence → X component (radio frequency detection)
//   - ConductivityProfile → Y component (thermal properties)
//   - DielectricConstant → Z component (paper material properties)
//
// This maps physical EM properties → S³ quaternion geometry!
type EMSignature struct {
	Type               DocumentType
	MagneticStrength   float32 // MICR ink magnetism [0, 1]
	RFIDPresence       float32 // RFID/NFC detection [0, 1]
	ConductivityProfile float32 // Thermal conductivity [0, 1]
	DielectricConstant float32 // Paper dielectric [0, 1]
	Signature          Quaternion // Encoded as quaternion on S³
}

// NewEMSignature creates EM signature from raw measurements
//
// Normalization:
//   - All inputs in [0, 1] range
//   - Signature projected to S³ (||Q|| = 1.0)
//
// WHY: Different document types have distinct EM fingerprints!
func NewEMSignature(docType DocumentType, magnetic, rfid, conductivity, dielectric float32) EMSignature {
	// Create quaternion from EM properties
	q := Quaternion{
		W: magnetic,    // Magnetic field strength
		X: rfid,        // RFID/NFC presence
		Y: conductivity, // Thermal conductivity
		Z: dielectric,  // Dielectric constant
	}

	// Normalize to S³
	q = q.Normalize()

	return EMSignature{
		Type:               docType,
		MagneticStrength:   magnetic,
		RFIDPresence:       rfid,
		ConductivityProfile: conductivity,
		DielectricConstant: dielectric,
		Signature:          q,
	}
}

// DocumentClassifier holds known document type attractors
//
// Attractor Database:
//   - Pre-computed quaternion for each document type
//   - Learned from training data (or defined a priori)
//   - Classification = nearest neighbor on S³
//
// WHY: Documents cluster by EM signature on S³ manifold!
type DocumentClassifier struct {
	Attractors map[DocumentType]Quaternion // Known document signatures
	Threshold  float32                     // Maximum distance for classification
}

// NewDocumentClassifier creates classifier with default attractors
//
// Default Attractors (a priori knowledge):
//   - Check: High magnetic (MICR ink), low RFID, medium conductivity, medium dielectric
//   - ID: Low magnetic, high RFID (chip), low conductivity, high dielectric
//   - Receipt: Low magnetic, low RFID, high conductivity (thermal), low dielectric
//   - Invoice: Low magnetic, low RFID, low conductivity, high dielectric (paper)
//   - Contract: Low magnetic, low RFID, low conductivity, very high dielectric (thick paper)
//   - Manuscript: Low magnetic, low RFID, medium conductivity (ink), medium dielectric
//   - Passport: Medium magnetic (security thread), high RFID (chip), low conductivity, high dielectric
//   - Ticket: Low magnetic, low RFID, medium conductivity (barcode), medium dielectric
//
// These are EDUCATED GUESSES - refine with real measurements!
func NewDocumentClassifier() *DocumentClassifier {
	attractors := map[DocumentType]Quaternion{
		// Check: MICR magnetic ink dominant
		DocCheck: NewEMSignature(DocCheck, 0.9, 0.1, 0.5, 0.5).Signature,

		// ID Card: RFID chip dominant
		DocID: NewEMSignature(DocID, 0.1, 0.9, 0.2, 0.7).Signature,

		// Receipt: Thermal conductivity dominant
		DocReceipt: NewEMSignature(DocReceipt, 0.1, 0.1, 0.9, 0.3).Signature,

		// Invoice: Standard paper (high dielectric)
		DocInvoice: NewEMSignature(DocInvoice, 0.1, 0.1, 0.2, 0.8).Signature,

		// Contract: Thick paper (very high dielectric)
		DocContract: NewEMSignature(DocContract, 0.1, 0.1, 0.2, 0.95).Signature,

		// Manuscript: Ink absorption (medium conductivity/dielectric)
		DocManuscript: NewEMSignature(DocManuscript, 0.1, 0.1, 0.5, 0.6).Signature,

		// Passport: Security features (magnetic thread + RFID)
		DocPassport: NewEMSignature(DocPassport, 0.5, 0.8, 0.2, 0.7).Signature,

		// Ticket: Barcode (medium conductivity)
		DocTicket: NewEMSignature(DocTicket, 0.1, 0.1, 0.5, 0.5).Signature,
	}

	return &DocumentClassifier{
		Attractors: attractors,
		Threshold:  0.5, // π/6 radians (~30° on S³) - tune empirically!
	}
}

// ClassifyByEMField classifies document using EM signature
//
// Algorithm:
//   1. Encode document EM properties → quaternion
//   2. Compute geodesic distance to each attractor
//   3. Return nearest attractor (if within threshold)
//
// Returns: (DocumentType, confidence, error)
//   - confidence: 1.0 - (distance/π) ∈ [0, 1]
//   - error: nil if classified, error if no match
//
// WHY: Nearest neighbor on S³ = natural classification!
// Geodesic distance preserves EM field geometry.
func (dc *DocumentClassifier) ClassifyByEMField(sig EMSignature) (DocumentType, float32, error) {
	var bestType DocumentType
	var bestDist float32 = float32(math.Pi) // Maximum possible distance on S³

	// Find nearest attractor
	for docType, attractor := range dc.Attractors {
		dist := GeodeticDistance(sig.Signature, attractor)
		if dist < bestDist {
			bestDist = dist
			bestType = docType
		}
	}

	// Check if within threshold
	if bestDist > dc.Threshold {
		return DocUnknown, 0.0, fmt.Errorf("no matching document type (min distance: %.4f > threshold: %.4f)",
			bestDist, dc.Threshold)
	}

	// Compute confidence (1.0 = perfect match, 0.0 = at threshold)
	confidence := 1.0 - (bestDist / dc.Threshold)

	return bestType, confidence, nil
}

// AttractorDistance computes distance matrix to all known types
//
// Returns: Map of DocumentType → geodesic distance
//
// Use Cases:
//   - Multi-label classification (top-K most likely types)
//   - Confidence calibration
//   - Attractor visualization
//
// WHY: Sometimes documents have mixed signatures (e.g., receipt with RFID loyalty card)
// Returning full distance profile enables probabilistic classification!
func (dc *DocumentClassifier) AttractorDistance(sig EMSignature) map[DocumentType]float32 {
	distances := make(map[DocumentType]float32)

	for docType, attractor := range dc.Attractors {
		distances[docType] = GeodeticDistance(sig.Signature, attractor)
	}

	return distances
}

// TypeDistance holds document type with distance and confidence
type TypeDistance struct {
	Type       DocumentType
	Distance   float32
	Confidence float32
}

// TopKTypes returns K most likely document types
//
// Useful for:
//   - Multi-label classification
//   - Confidence intervals
//   - A/B testing (try top 2 types)
//
// Returns: Sorted slice [(type1, conf1), (type2, conf2), ...]
func (dc *DocumentClassifier) TopKTypes(sig EMSignature, k int) []TypeDistance {
	// Compute all distances
	distances := dc.AttractorDistance(sig)

	// Convert to slice for sorting
	results := make([]TypeDistance, 0, len(distances))
	for docType, dist := range distances {
		conf := 1.0 - (dist / float32(math.Pi)) // Normalize to [0, 1]
		results = append(results, TypeDistance{
			Type:       docType,
			Distance:   dist,
			Confidence: conf,
		})
	}

	// Sort by distance (ascending)
	for i := 0; i < len(results)-1; i++ {
		for j := i + 1; j < len(results); j++ {
			if results[j].Distance < results[i].Distance {
				results[i], results[j] = results[j], results[i]
			}
		}
	}

	// Return top-K
	if k > len(results) {
		k = len(results)
	}
	return results[:k]
}

// VisualSignature extracts EM signature from image (visual proxy)
//
// Since we don't have actual EM sensors, we use VISUAL proxies:
//   - Magnetic ink: High saturation black (MICR E-13B font detection)
//   - RFID chip: Visible chip outline (edge detection)
//   - Thermal paper: Uniform texture (low variance)
//   - Standard paper: High texture variance
//
// This is APPROXIMATION - real EM sensors would be better!
// But for OCR preprocessing, visual proxies are sufficient.
//
// Future: Integrate with actual EM sensors (multispectral camera, RFID reader)
func VisualSignature(quaternions []Quaternion, width, height int) EMSignature {
	// Compute image statistics
	stats := ComputeImageStatistics(quaternions, width, height)

	// Estimate EM properties from visual features

	// Magnetic strength: High saturation dark pixels (MICR ink proxy)
	// MICR ink appears as very dark, high-contrast text
	magneticStrength := estimateMagneticFromContrast(quaternions, stats)

	// RFID presence: Edge density + local uniformity (chip outline)
	// RFID chips have visible rectangular outline with uniform interior
	rfidPresence := estimateRFIDFromEdges(quaternions, width, height, stats)

	// Conductivity: Texture uniformity (thermal paper has low variance)
	// Thermal receipts have very uniform, smooth texture
	conductivity := estimateConductivityFromTexture(quaternions, stats)

	// Dielectric: Mean brightness (paper thickness/quality proxy)
	// Thicker, higher-quality paper has higher reflectance
	dielectric := estimateDielectricFromBrightness(quaternions, stats)

	return NewEMSignature(DocUnknown, magneticStrength, rfidPresence, conductivity, dielectric)
}

// estimateMagneticFromContrast estimates magnetic ink from high-contrast dark regions
func estimateMagneticFromContrast(quaternions []Quaternion, stats Statistics) float32 {
	// Count very dark pixels (potential MICR ink)
	// MICR E-13B font has characteristic sharp, dark strokes
	darkThreshold := float32(0.2) // W component < 0.2 = very dark
	var darkCount int

	for _, q := range quaternions {
		if q.W < darkThreshold {
			darkCount++
		}
	}

	// Normalize to [0, 1]
	darkRatio := float32(darkCount) / float32(len(quaternions))

	// Magnetic ink typically 5-15% of check area
	// Map [0, 0.15] → [0, 1]
	magnetic := darkRatio / 0.15
	if magnetic > 1.0 {
		magnetic = 1.0
	}

	return magnetic
}

// estimateRFIDFromEdges estimates RFID presence from edge patterns
func estimateRFIDFromEdges(quaternions []Quaternion, width, height int, stats Statistics) float32 {
	// RFID chips have characteristic rectangular edge pattern
	// High edge density in localized region (chip outline)

	edges := DetectEdges(quaternions, width, height)

	// Find maximum local edge concentration
	windowSize := 32 // Look for 32×32 pixel chip regions
	maxLocalEdgeDensity := float32(0.0)

	for y := 0; y < height-windowSize; y += windowSize/2 {
		for x := 0; x < width-windowSize; x += windowSize/2 {
			var edgeSum float32
			var count int

			for dy := 0; dy < windowSize && y+dy < height; dy++ {
				for dx := 0; dx < windowSize && x+dx < width; dx++ {
					idx := (y+dy)*width + (x+dx)
					edgeSum += edges[idx]
					count++
				}
			}

			localDensity := edgeSum / float32(count)
			if localDensity > maxLocalEdgeDensity {
				maxLocalEdgeDensity = localDensity
			}
		}
	}

	// Normalize to [0, 1]
	// Typical RFID chip region has edge density ~2-3
	rfid := maxLocalEdgeDensity / 3.0
	if rfid > 1.0 {
		rfid = 1.0
	}

	return rfid
}

// estimateConductivityFromTexture estimates thermal conductivity from texture variance
func estimateConductivityFromTexture(quaternions []Quaternion, stats Statistics) float32 {
	// Thermal paper (receipts) has LOW texture variance (smooth, uniform)
	// Standard paper has HIGH texture variance (fiber structure visible)

	// Chromatic spread is inverse proxy for conductivity
	// Low spread = uniform thermal paper = high conductivity
	conductivity := 1.0 - stats.ChromaticSpread

	// Clamp to [0, 1]
	if conductivity < 0.0 {
		conductivity = 0.0
	}
	if conductivity > 1.0 {
		conductivity = 1.0
	}

	return conductivity
}

// estimateDielectricFromBrightness estimates dielectric constant from mean brightness
func estimateDielectricFromBrightness(quaternions []Quaternion, stats Statistics) float32 {
	// Thicker, higher-quality paper reflects more light (higher W component)
	// Mean distance from center relates to overall brightness distribution

	// Use W component of center as brightness proxy
	dielectric := stats.Center.W

	// Ensure [0, 1] range (should already be from normalization)
	if dielectric < 0.0 {
		dielectric = 0.0
	}
	if dielectric > 1.0 {
		dielectric = 1.0
	}

	return dielectric
}

// String returns human-readable EM signature
func (sig EMSignature) String() string {
	return fmt.Sprintf(
		"EMSignature{Type: %s, Magnetic: %.3f, RFID: %.3f, Conductivity: %.3f, Dielectric: %.3f, Q: %s}",
		sig.Type,
		sig.MagneticStrength,
		sig.RFIDPresence,
		sig.ConductivityProfile,
		sig.DielectricConstant,
		sig.Signature.String(),
	)
}

// TrainAttractor updates classifier with new training example
//
// Online Learning:
//   - Add new document type → attractor mapping
//   - Update existing attractor via exponential moving average
//
// Use Cases:
//   - Adapt to new document types
//   - Refine attractors based on real data
//   - Domain adaptation (different countries, languages)
//
// α = learning rate (default: 0.1 = 10% weight to new example)
func (dc *DocumentClassifier) TrainAttractor(docType DocumentType, sig EMSignature, alpha float32) {
	if alpha < 0.0 || alpha > 1.0 {
		alpha = 0.1 // Default learning rate
	}

	existing, exists := dc.Attractors[docType]

	if !exists {
		// New document type: add directly
		dc.Attractors[docType] = sig.Signature
	} else {
		// Update existing via SLERP (geodesic interpolation!)
		// This is exponential moving average ON S³!
		updated := SLERP(existing, sig.Signature, alpha)
		dc.Attractors[docType] = updated
	}
}

// SaveAttractors exports attractor database (for persistence)
//
// Returns: Map that can be serialized to JSON/YAML
//
// Use Cases:
//   - Save trained classifier
//   - Transfer learning (use attractors from one domain in another)
//   - Visualization (plot attractors on S³)
func (dc *DocumentClassifier) SaveAttractors() map[string][4]float32 {
	exported := make(map[string][4]float32)

	for docType, q := range dc.Attractors {
		exported[docType.String()] = [4]float32{q.W, q.X, q.Y, q.Z}
	}

	return exported
}

// LoadAttractors imports attractor database
//
// Inverse of SaveAttractors()
// Validates all quaternions are on S³ before loading
func (dc *DocumentClassifier) LoadAttractors(data map[string][4]float32) error {
	newAttractors := make(map[DocumentType]Quaternion)

	// Map string names back to DocumentType
	nameToType := map[string]DocumentType{
		"Check":      DocCheck,
		"ID Card":    DocID,
		"Receipt":    DocReceipt,
		"Invoice":    DocInvoice,
		"Contract":   DocContract,
		"Manuscript": DocManuscript,
		"Passport":   DocPassport,
		"Ticket":     DocTicket,
	}

	for name, components := range data {
		docType, ok := nameToType[name]
		if !ok {
			return fmt.Errorf("unknown document type: %s", name)
		}

		q := Quaternion{
			W: components[0],
			X: components[1],
			Y: components[2],
			Z: components[3],
		}

		// Validate
		if err := q.Validate(); err != nil {
			return fmt.Errorf("invalid quaternion for %s: %w", name, err)
		}

		newAttractors[docType] = q
	}

	// Atomic update (all or nothing)
	dc.Attractors = newAttractors
	return nil
}
