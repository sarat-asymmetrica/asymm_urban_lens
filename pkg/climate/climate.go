// Package climate provides climate analysis for urban research
// Supports IMD rainfall, temperature anomalies, monsoon patterns, urban heat islands
// Ported from Asymmetrica's Climate Engine for IIHS Urban Lens
package climate

import (
	"encoding/csv"
	"fmt"
	"io"
	"math"
	"os"
	"strconv"
	"strings"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// UNIVERSAL CONSTANTS
// ═══════════════════════════════════════════════════════════════════════════

const (
	GoldenRatio        = 1.618033988749895
	ThermodynamicLimit = 0.87532 // Universal attractor

	// Climate-specific
	BaselineTemp  = 14.0 // °C (Earth's average)
	AnomalyScale  = 10.0 // Max expected anomaly
	SeasonalScale = 2.0  // Seasonal variation amplitude
)

// ═══════════════════════════════════════════════════════════════════════════
// DATA STRUCTURES
// ═══════════════════════════════════════════════════════════════════════════

// DataPoint represents a single climate observation
type DataPoint struct {
	Timestamp time.Time
	Value     float64
	Anomaly   float64
	Location  string
	DataType  string
}

// TimeSeries holds a complete time series
type TimeSeries struct {
	Data     []DataPoint
	Metadata map[string]string
	Stats    Stats
}

// Stats contains statistical summary
type Stats struct {
	Mean          float64
	StdDev        float64
	Min           float64
	Max           float64
	Trend         float64 // per year
	Count         int
	MissingValues int
}

// CSVConfig defines how to parse a CSV file
type CSVConfig struct {
	DateColumn     int
	ValueColumn    int
	AnomalyColumn  int
	LocationColumn int
	SkipHeader     bool
	DateFormat     string
	DataType       string
}

// ═══════════════════════════════════════════════════════════════════════════
// PRESET CONFIGURATIONS (Indian/Urban Research)
// ═══════════════════════════════════════════════════════════════════════════

// TemperatureConfig for temperature datasets
func TemperatureConfig() CSVConfig {
	return CSVConfig{
		DateColumn:     0,
		ValueColumn:    1,
		AnomalyColumn:  2,
		LocationColumn: -1,
		SkipHeader:     true,
		DateFormat:     "2006-01-02",
		DataType:       "temperature",
	}
}

// IMDRainfallConfig for India Meteorological Department rainfall data
func IMDRainfallConfig() CSVConfig {
	return CSVConfig{
		DateColumn:     0,
		ValueColumn:    1,
		AnomalyColumn:  -1,
		LocationColumn: 2,
		SkipHeader:     true,
		DateFormat:     "2006-01",
		DataType:       "rainfall",
	}
}

// MonsoonConfig for monsoon pattern analysis
func MonsoonConfig() CSVConfig {
	return CSVConfig{
		DateColumn:     0,
		ValueColumn:    1,
		AnomalyColumn:  2,
		LocationColumn: 3,
		SkipHeader:     true,
		DateFormat:     "2006-01-02",
		DataType:       "monsoon",
	}
}

// UrbanHeatConfig for urban heat island analysis
func UrbanHeatConfig() CSVConfig {
	return CSVConfig{
		DateColumn:     0,
		ValueColumn:    1,
		AnomalyColumn:  2,
		LocationColumn: 3,
		SkipHeader:     true,
		DateFormat:     "2006-01-02 15:04",
		DataType:       "urban_heat",
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// CSV LOADER
// ═══════════════════════════════════════════════════════════════════════════

// LoadCSV reads a CSV file and returns structured time series
func LoadCSV(filepath string, config CSVConfig) (*TimeSeries, error) {
	file, err := os.Open(filepath)
	if err != nil {
		return nil, fmt.Errorf("failed to open file: %w", err)
	}
	defer file.Close()

	reader := csv.NewReader(file)
	reader.FieldsPerRecord = -1
	reader.TrimLeadingSpace = true

	var data []DataPoint
	lineNum := 0

	for {
		record, err := reader.Read()
		if err == io.EOF {
			break
		}
		if err != nil {
			continue // Skip bad lines
		}

		lineNum++
		if lineNum == 1 && config.SkipHeader {
			continue
		}

		point, err := parseRecord(record, config)
		if err != nil {
			continue
		}

		data = append(data, point)
	}

	if len(data) == 0 {
		return nil, fmt.Errorf("no valid data points found")
	}

	ts := &TimeSeries{
		Data: data,
		Metadata: map[string]string{
			"source":   filepath,
			"datatype": config.DataType,
			"loaded":   time.Now().Format(time.RFC3339),
		},
	}

	ts.Stats = ComputeStats(data)
	return ts, nil
}

func parseRecord(record []string, config CSVConfig) (DataPoint, error) {
	var point DataPoint

	if config.DateColumn >= len(record) {
		return point, fmt.Errorf("date column out of range")
	}

	dateStr := strings.TrimSpace(record[config.DateColumn])
	timestamp, err := time.Parse(config.DateFormat, dateStr)
	if err != nil {
		return point, err
	}
	point.Timestamp = timestamp

	if config.ValueColumn >= len(record) {
		return point, fmt.Errorf("value column out of range")
	}

	valueStr := strings.TrimSpace(record[config.ValueColumn])
	value, err := strconv.ParseFloat(valueStr, 64)
	if err != nil {
		return point, err
	}
	point.Value = value

	if config.AnomalyColumn >= 0 && config.AnomalyColumn < len(record) {
		anomalyStr := strings.TrimSpace(record[config.AnomalyColumn])
		if anomaly, err := strconv.ParseFloat(anomalyStr, 64); err == nil {
			point.Anomaly = anomaly
		}
	}

	if config.LocationColumn >= 0 && config.LocationColumn < len(record) {
		point.Location = strings.TrimSpace(record[config.LocationColumn])
	}

	point.DataType = config.DataType
	return point, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// STATISTICS
// ═══════════════════════════════════════════════════════════════════════════

// ComputeStats calculates statistical summary
func ComputeStats(data []DataPoint) Stats {
	if len(data) == 0 {
		return Stats{}
	}

	var sum, sumSq float64
	min := math.MaxFloat64
	max := -math.MaxFloat64

	for _, point := range data {
		val := point.Value
		sum += val
		sumSq += val * val
		if val < min {
			min = val
		}
		if val > max {
			max = val
		}
	}

	n := float64(len(data))
	mean := sum / n
	variance := (sumSq / n) - (mean * mean)
	stdDev := math.Sqrt(math.Abs(variance))
	trend := computeTrend(data)

	return Stats{
		Mean:   mean,
		StdDev: stdDev,
		Min:    min,
		Max:    max,
		Trend:  trend,
		Count:  len(data),
	}
}

func computeTrend(data []DataPoint) float64 {
	if len(data) < 2 {
		return 0.0
	}

	t0 := data[0].Timestamp
	var sumT, sumY, sumTY, sumT2 float64
	n := float64(len(data))

	for _, point := range data {
		t := point.Timestamp.Sub(t0).Hours() / (24.0 * 365.25)
		y := point.Value
		sumT += t
		sumY += y
		sumTY += t * y
		sumT2 += t * t
	}

	numerator := n*sumTY - sumT*sumY
	denominator := n*sumT2 - sumT*sumT

	if math.Abs(denominator) < 1e-10 {
		return 0.0
	}

	return numerator / denominator
}

// ═══════════════════════════════════════════════════════════════════════════
// QUATERNION ENCODING (S³ State Space)
// ═══════════════════════════════════════════════════════════════════════════

// Quaternion represents a point on S³
type Quaternion struct {
	W, X, Y, Z float64
}

// NewQuaternion creates a normalized quaternion
func NewQuaternion(w, x, y, z float64) Quaternion {
	q := Quaternion{W: w, X: x, Y: y, Z: z}
	return q.Normalize()
}

// Norm returns the magnitude
func (q Quaternion) Norm() float64 {
	return math.Sqrt(q.W*q.W + q.X*q.X + q.Y*q.Y + q.Z*q.Z)
}

// Normalize projects to unit sphere
func (q Quaternion) Normalize() Quaternion {
	n := q.Norm()
	if n < 1e-10 {
		return Quaternion{W: 1, X: 0, Y: 0, Z: 0}
	}
	return Quaternion{W: q.W / n, X: q.X / n, Y: q.Y / n, Z: q.Z / n}
}

// Dot product
func (q Quaternion) Dot(p Quaternion) float64 {
	return q.W*p.W + q.X*p.X + q.Y*p.Y + q.Z*p.Z
}

// SLERP - Spherical Linear Interpolation (geodesic path)
func SLERP(q0, q1 Quaternion, t float64) Quaternion {
	dot := q0.Dot(q1)
	if dot < 0 {
		q1 = Quaternion{W: -q1.W, X: -q1.X, Y: -q1.Y, Z: -q1.Z}
		dot = -dot
	}

	if dot > 0.9995 {
		return NewQuaternion(
			q0.W+t*(q1.W-q0.W),
			q0.X+t*(q1.X-q0.X),
			q0.Y+t*(q1.Y-q0.Y),
			q0.Z+t*(q1.Z-q0.Z),
		)
	}

	omega := math.Acos(dot)
	sinOmega := math.Sin(omega)
	scale0 := math.Sin((1-t)*omega) / sinOmega
	scale1 := math.Sin(t*omega) / sinOmega

	return NewQuaternion(
		scale0*q0.W+scale1*q1.W,
		scale0*q0.X+scale1*q1.X,
		scale0*q0.Y+scale1*q1.Y,
		scale0*q0.Z+scale1*q1.Z,
	)
}

// ═══════════════════════════════════════════════════════════════════════════
// CLIMATE STATE ENCODING
// ═══════════════════════════════════════════════════════════════════════════

// ClimateState represents encoded climate observation
type ClimateState struct {
	Q            Quaternion
	Anomaly      float64
	Month        int
	Year         int
	Regime       string
	Satisfaction float64
}

// Regime classification
type Regime int

const (
	RegimeExploration   Regime = 1 // R1: Extreme weather (30%)
	RegimeOptimization  Regime = 2 // R2: Transitions (20%)
	RegimeStabilization Regime = 3 // R3: Normal (50%)
)

func (r Regime) String() string {
	switch r {
	case RegimeExploration:
		return "R1-Extreme"
	case RegimeOptimization:
		return "R2-Transition"
	case RegimeStabilization:
		return "R3-Normal"
	default:
		return "Unknown"
	}
}

// EncodeAnomaly maps temperature/rainfall anomaly to quaternion
func EncodeAnomaly(anomaly float64, month, year int) Quaternion {
	w := math.Tanh(anomaly / AnomalyScale)
	seasonalPhase := 2.0 * math.Pi * float64(month) / 12.0
	x := SeasonalScale * math.Sin(seasonalPhase) / AnomalyScale
	yearPhase := 2.0 * math.Pi * float64(year) / GoldenRatio
	y := math.Cos(yearPhase) / GoldenRatio

	sumSq := w*w + x*x + y*y
	if sumSq >= 1.0 {
		scale := 1.0 / math.Sqrt(sumSq)
		w *= scale
		x *= scale
		y *= scale
		sumSq = w*w + x*x + y*y
	}
	z := math.Sqrt(1.0 - sumSq)

	return NewQuaternion(w, x, y, z)
}

// ClassifyRegime determines weather pattern regime
func ClassifyRegime(q Quaternion) Regime {
	absW := math.Abs(q.W)
	absX := math.Abs(q.X)
	absZ := math.Abs(q.Z)

	if absZ > absW && absZ > absX {
		return RegimeStabilization
	}
	if absW > absX {
		return RegimeExploration
	}
	return RegimeOptimization
}

// ComputeSatisfaction measures proximity to thermodynamic limit
func ComputeSatisfaction(q Quaternion) float64 {
	threshold := 0.5
	satisfied := 0.0

	if math.Abs(q.W) < threshold {
		satisfied += 1.0
	}
	if math.Abs(q.X) < threshold {
		satisfied += 1.0
	}
	if math.Abs(q.Y) < threshold {
		satisfied += 1.0
	}
	if math.Abs(q.Z-1.0) < threshold {
		satisfied += 1.0
	}

	return satisfied / 4.0
}

// ═══════════════════════════════════════════════════════════════════════════
// ANALYSIS ENGINE
// ═══════════════════════════════════════════════════════════════════════════

// Analyzer provides climate analysis capabilities
type Analyzer struct {
	TimeSeries *TimeSeries
	States     []ClimateState
}

// NewAnalyzer creates a climate analyzer
func NewAnalyzer() *Analyzer {
	return &Analyzer{}
}

// LoadData loads and encodes climate data
func (a *Analyzer) LoadData(filepath string, config CSVConfig) error {
	ts, err := LoadCSV(filepath, config)
	if err != nil {
		return err
	}
	a.TimeSeries = ts
	a.States = a.EncodeTimeSeries()
	return nil
}

// EncodeTimeSeries converts time series to quaternion sequence
func (a *Analyzer) EncodeTimeSeries() []ClimateState {
	if a.TimeSeries == nil {
		return nil
	}

	states := make([]ClimateState, len(a.TimeSeries.Data))
	for i, point := range a.TimeSeries.Data {
		month := int(point.Timestamp.Month())
		year := point.Timestamp.Year()

		q := EncodeAnomaly(point.Anomaly, month, year)
		regime := ClassifyRegime(q)
		satisfaction := ComputeSatisfaction(q)

		states[i] = ClimateState{
			Q:            q,
			Anomaly:      point.Anomaly,
			Month:        month,
			Year:         year,
			Regime:       regime.String(),
			Satisfaction: satisfaction,
		}
	}

	return states
}

// AnalyzeRegimes computes three-regime distribution
func (a *Analyzer) AnalyzeRegimes() (r1, r2, r3 float64) {
	if len(a.States) == 0 {
		return 0, 0, 0
	}

	var r1Count, r2Count, r3Count int
	for _, state := range a.States {
		switch state.Regime {
		case "R1-Extreme":
			r1Count++
		case "R2-Transition":
			r2Count++
		case "R3-Normal":
			r3Count++
		}
	}

	total := float64(len(a.States))
	return float64(r1Count) / total, float64(r2Count) / total, float64(r3Count) / total
}

// AverageSatisfaction computes mean satisfaction
func (a *Analyzer) AverageSatisfaction() float64 {
	if len(a.States) == 0 {
		return 0
	}

	sum := 0.0
	for _, state := range a.States {
		sum += state.Satisfaction
	}
	return sum / float64(len(a.States))
}

// PredictNext uses SLERP geodesic extrapolation
func (a *Analyzer) PredictNext(stepsAhead int) Quaternion {
	if len(a.States) < 2 {
		if len(a.States) == 1 {
			return a.States[0].Q
		}
		return NewQuaternion(1, 0, 0, 0)
	}

	q0 := a.States[len(a.States)-2].Q
	q1 := a.States[len(a.States)-1].Q
	t := 1.0 + float64(stepsAhead)*0.1

	return SLERP(q0, q1, t)
}

// GetAnalysisReport returns a formatted analysis report
func (a *Analyzer) GetAnalysisReport() map[string]interface{} {
	r1, r2, r3 := a.AnalyzeRegimes()
	avgSat := a.AverageSatisfaction()

	return map[string]interface{}{
		"data_type":      a.TimeSeries.Metadata["datatype"],
		"count":          a.TimeSeries.Stats.Count,
		"mean":           a.TimeSeries.Stats.Mean,
		"std_dev":        a.TimeSeries.Stats.StdDev,
		"min":            a.TimeSeries.Stats.Min,
		"max":            a.TimeSeries.Stats.Max,
		"trend_per_year": a.TimeSeries.Stats.Trend,
		"regime_r1":      r1,
		"regime_r2":      r2,
		"regime_r3":      r3,
		"satisfaction":   avgSat,
		"attractor_dist": math.Abs(avgSat - ThermodynamicLimit),
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// URBAN HEAT ISLAND ANALYSIS
// ═══════════════════════════════════════════════════════════════════════════

// HeatIslandResult represents urban heat island analysis
type HeatIslandResult struct {
	UrbanTemp      float64
	RuralTemp      float64
	Intensity      float64 // Urban - Rural
	Classification string  // "Weak", "Moderate", "Strong", "Severe"
	Regime         string
}

// AnalyzeHeatIsland computes urban heat island intensity
func AnalyzeHeatIsland(urbanTemp, ruralTemp float64) HeatIslandResult {
	intensity := urbanTemp - ruralTemp

	var classification string
	switch {
	case intensity < 2.0:
		classification = "Weak"
	case intensity < 4.0:
		classification = "Moderate"
	case intensity < 6.0:
		classification = "Strong"
	default:
		classification = "Severe"
	}

	q := EncodeAnomaly(intensity, int(time.Now().Month()), time.Now().Year())
	regime := ClassifyRegime(q)

	return HeatIslandResult{
		UrbanTemp:      urbanTemp,
		RuralTemp:      ruralTemp,
		Intensity:      intensity,
		Classification: classification,
		Regime:         regime.String(),
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// MONSOON ANALYSIS
// ═══════════════════════════════════════════════════════════════════════════

// MonsoonPhase represents monsoon cycle phase
type MonsoonPhase string

const (
	MonsoonPreOnset    MonsoonPhase = "Pre-Onset"
	MonsoonOnset       MonsoonPhase = "Onset"
	MonsoonActive      MonsoonPhase = "Active"
	MonsoonBreak       MonsoonPhase = "Break"
	MonsoonWithdrawal  MonsoonPhase = "Withdrawal"
	MonsoonPostMonsoon MonsoonPhase = "Post-Monsoon"
)

// ClassifyMonsoonPhase determines monsoon phase from date and rainfall
func ClassifyMonsoonPhase(month int, rainfall float64, avgRainfall float64) MonsoonPhase {
	ratio := rainfall / avgRainfall

	switch month {
	case 5:
		return MonsoonPreOnset
	case 6:
		if ratio > 0.8 {
			return MonsoonOnset
		}
		return MonsoonPreOnset
	case 7, 8:
		if ratio > 1.2 {
			return MonsoonActive
		} else if ratio < 0.5 {
			return MonsoonBreak
		}
		return MonsoonActive
	case 9:
		if ratio < 0.7 {
			return MonsoonWithdrawal
		}
		return MonsoonActive
	case 10, 11:
		return MonsoonPostMonsoon
	default:
		return MonsoonPostMonsoon
	}
}
