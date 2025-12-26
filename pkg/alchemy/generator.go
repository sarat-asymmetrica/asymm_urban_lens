// Package alchemy provides code and data generation capabilities for Urban Lens
// Ported from Asymmetrica's API/Component/Fullstack Alchemy engines
// Enables researchers to generate mock datasets, API schemas, and research tools
package alchemy

import (
	"encoding/json"
	"fmt"
	"math"
	"math/rand"
	"strings"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// CONSTANTS
// ═══════════════════════════════════════════════════════════════════════════

const (
	PHI         = 1.618033988749895
	PHI_INV     = 0.6180339887498949
	SACRED_SEED = 108
)

// Three-regime distribution
var ThreeRegime = [3]float64{0.30, 0.20, 0.50}

// Fibonacci sequence for rate limits and pagination
var Fibonacci = []int{1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144}

// ═══════════════════════════════════════════════════════════════════════════
// ENTITY SCHEMA (for API generation)
// ═══════════════════════════════════════════════════════════════════════════

// Field represents an entity field
type Field struct {
	Name       string   `json:"name"`
	Type       string   `json:"type"` // string, int, float, bool, date, json
	Required   bool     `json:"required"`
	Unique     bool     `json:"unique"`
	Tags       []string `json:"tags"` // searchable, filterable, sortable
	Default    string   `json:"default,omitempty"`
	Validation string   `json:"validation,omitempty"`
}

// Relation represents entity relationships
type Relation struct {
	Name       string `json:"name"`
	TargetType string `json:"target_type"`
	Type       string `json:"type"` // one-to-many, many-to-many, one-to-one
}

// EntitySchema defines an entity for API generation
type EntitySchema struct {
	Name        string     `json:"name"`
	PluralName  string     `json:"plural_name"`
	Description string     `json:"description"`
	Fields      []Field    `json:"fields"`
	Relations   []Relation `json:"relations,omitempty"`
	SoftDelete  bool       `json:"soft_delete"`
	Timestamps  bool       `json:"timestamps"`
	SacredSeed  int64      `json:"sacred_seed"`
}

// ═══════════════════════════════════════════════════════════════════════════
// RESEARCH DATA GENERATOR
// ═══════════════════════════════════════════════════════════════════════════

// DataGenerator creates deterministic mock research data
type DataGenerator struct {
	Seed   int64
	rng    *rand.Rand
	Locale string
}

// NewDataGenerator creates a generator with given seed
func NewDataGenerator(seed int64) *DataGenerator {
	return &DataGenerator{
		Seed:   seed,
		rng:    rand.New(rand.NewSource(seed)),
		Locale: "en_IN", // Default to Indian locale
	}
}

// DigitalRoot computes Vedic digital root
func DigitalRoot(n int64) int {
	if n == 0 {
		return 0
	}
	return 1 + int((n-1)%9)
}

// GenerateQuaternionID creates a unique quaternion-based ID
func (g *DataGenerator) GenerateQuaternionID() string {
	w := g.rng.Float64()
	x := g.rng.Float64()
	y := g.rng.Float64()
	z := g.rng.Float64()

	// Normalize to unit quaternion
	norm := math.Sqrt(w*w + x*x + y*y + z*z)
	w, x, y, z = w/norm, x/norm, y/norm, z/norm

	return fmt.Sprintf("q_%.3f_%.3f_%.3f_%.3f", w, x, y, z)
}

// ═══════════════════════════════════════════════════════════════════════════
// INDIAN CITY DATA (for urban research)
// ═══════════════════════════════════════════════════════════════════════════

// IndianCity represents city data
type IndianCity struct {
	Name       string  `json:"name"`
	State      string  `json:"state"`
	Population int64   `json:"population"`
	Area       float64 `json:"area_km2"`
	Latitude   float64 `json:"latitude"`
	Longitude  float64 `json:"longitude"`
	Tier       int     `json:"tier"` // 1, 2, or 3
}

var IndianCities = []IndianCity{
	{"Mumbai", "Maharashtra", 20411000, 603.4, 19.0760, 72.8777, 1},
	{"Delhi", "Delhi", 16787941, 1484.0, 28.7041, 77.1025, 1},
	{"Bangalore", "Karnataka", 8443675, 709.0, 12.9716, 77.5946, 1},
	{"Hyderabad", "Telangana", 6809970, 650.0, 17.3850, 78.4867, 1},
	{"Chennai", "Tamil Nadu", 4681087, 426.0, 13.0827, 80.2707, 1},
	{"Kolkata", "West Bengal", 4496694, 206.1, 22.5726, 88.3639, 1},
	{"Ahmedabad", "Gujarat", 5570585, 464.0, 23.0225, 72.5714, 1},
	{"Pune", "Maharashtra", 3124458, 331.0, 18.5204, 73.8567, 1},
	{"Jaipur", "Rajasthan", 3073350, 467.0, 26.9124, 75.7873, 1},
	{"Lucknow", "Uttar Pradesh", 2817105, 349.0, 26.8467, 80.9462, 2},
	{"Kanpur", "Uttar Pradesh", 2767031, 403.0, 26.4499, 80.3319, 2},
	{"Nagpur", "Maharashtra", 2405421, 227.4, 21.1458, 79.0882, 2},
	{"Indore", "Madhya Pradesh", 1994397, 530.0, 22.7196, 75.8577, 2},
	{"Bhopal", "Madhya Pradesh", 1798218, 463.0, 23.2599, 77.4126, 2},
	{"Visakhapatnam", "Andhra Pradesh", 1730320, 681.96, 17.6868, 83.2185, 2},
	{"Coimbatore", "Tamil Nadu", 1601438, 257.0, 11.0168, 76.9558, 2},
	{"Kochi", "Kerala", 677381, 94.88, 9.9312, 76.2673, 2},
	{"Mysore", "Karnataka", 920550, 128.42, 12.2958, 76.6394, 2},
	{"Shimla", "Himachal Pradesh", 169578, 35.34, 31.1048, 77.1734, 3},
	{"Gangtok", "Sikkim", 100286, 19.2, 27.3389, 88.6065, 3},
}

// GenerateCity returns a random Indian city
func (g *DataGenerator) GenerateCity() IndianCity {
	return IndianCities[g.rng.Intn(len(IndianCities))]
}

// GenerateCityByTier returns a city of specific tier
func (g *DataGenerator) GenerateCityByTier(tier int) IndianCity {
	var filtered []IndianCity
	for _, city := range IndianCities {
		if city.Tier == tier {
			filtered = append(filtered, city)
		}
	}
	if len(filtered) == 0 {
		return IndianCities[0]
	}
	return filtered[g.rng.Intn(len(filtered))]
}

// ═══════════════════════════════════════════════════════════════════════════
// CLIMATE DATA GENERATION
// ═══════════════════════════════════════════════════════════════════════════

// ClimateDataPoint for mock climate data
type ClimateDataPoint struct {
	Date        string  `json:"date"`
	Temperature float64 `json:"temperature"`
	Rainfall    float64 `json:"rainfall_mm"`
	Humidity    float64 `json:"humidity_percent"`
	AQI         int     `json:"aqi"`
	City        string  `json:"city"`
}

// GenerateClimateData creates mock climate time series
func (g *DataGenerator) GenerateClimateData(city string, days int) []ClimateDataPoint {
	data := make([]ClimateDataPoint, days)
	baseDate := time.Date(2024, 1, 1, 0, 0, 0, 0, time.UTC)

	// Base temperature varies by city latitude
	baseTemp := 25.0 + g.rng.Float64()*10

	for i := 0; i < days; i++ {
		date := baseDate.AddDate(0, 0, i)
		month := date.Month()

		// Seasonal variation
		seasonalOffset := 10 * math.Sin(2*math.Pi*float64(month)/12)

		// Daily variation
		dailyNoise := g.rng.NormFloat64() * 3

		temp := baseTemp + seasonalOffset + dailyNoise

		// Monsoon rainfall (June-September)
		var rainfall float64
		if month >= 6 && month <= 9 {
			rainfall = g.rng.ExpFloat64() * 50
		} else {
			rainfall = g.rng.ExpFloat64() * 5
		}

		// Humidity correlates with rainfall
		humidity := 40 + rainfall*0.5 + g.rng.Float64()*20
		if humidity > 100 {
			humidity = 100
		}

		// AQI (worse in winter due to inversions)
		baseAQI := 50
		if month >= 11 || month <= 2 {
			baseAQI = 150
		}
		aqi := baseAQI + g.rng.Intn(100)

		data[i] = ClimateDataPoint{
			Date:        date.Format("2006-01-02"),
			Temperature: math.Round(temp*10) / 10,
			Rainfall:    math.Round(rainfall*10) / 10,
			Humidity:    math.Round(humidity*10) / 10,
			AQI:         aqi,
			City:        city,
		}
	}

	return data
}

// ═══════════════════════════════════════════════════════════════════════════
// CENSUS DATA GENERATION
// ═══════════════════════════════════════════════════════════════════════════

// CensusRecord for mock census data
type CensusRecord struct {
	WardID           string  `json:"ward_id"`
	WardName         string  `json:"ward_name"`
	City             string  `json:"city"`
	Population       int64   `json:"population"`
	Households       int64   `json:"households"`
	MalePopulation   int64   `json:"male_population"`
	FemalePopulation int64   `json:"female_population"`
	LiteracyRate     float64 `json:"literacy_rate"`
	WorkerRate       float64 `json:"worker_participation_rate"`
	AvgHouseholdSize float64 `json:"avg_household_size"`
}

// GenerateCensusData creates mock census records
func (g *DataGenerator) GenerateCensusData(city string, wards int) []CensusRecord {
	records := make([]CensusRecord, wards)

	wardNames := []string{
		"Central", "North", "South", "East", "West",
		"Old City", "New Town", "Industrial", "Residential", "Commercial",
		"Lake View", "Garden", "Station Area", "University", "Market",
	}

	for i := 0; i < wards; i++ {
		population := int64(10000 + g.rng.Intn(90000))
		households := population / int64(3+g.rng.Intn(3))
		maleRatio := 0.48 + g.rng.Float64()*0.08

		wardName := wardNames[i%len(wardNames)]
		if i >= len(wardNames) {
			wardName = fmt.Sprintf("%s %d", wardName, i/len(wardNames)+1)
		}

		records[i] = CensusRecord{
			WardID:           fmt.Sprintf("%s-W%03d", strings.ToUpper(city[:3]), i+1),
			WardName:         wardName,
			City:             city,
			Population:       population,
			Households:       households,
			MalePopulation:   int64(float64(population) * maleRatio),
			FemalePopulation: int64(float64(population) * (1 - maleRatio)),
			LiteracyRate:     60 + g.rng.Float64()*35,
			WorkerRate:       30 + g.rng.Float64()*30,
			AvgHouseholdSize: float64(population) / float64(households),
		}
	}

	return records
}

// ═══════════════════════════════════════════════════════════════════════════
// SURVEY DATA GENERATION
// ═══════════════════════════════════════════════════════════════════════════

// SurveyResponse for mock survey data
type SurveyResponse struct {
	ResponseID       string                 `json:"response_id"`
	Timestamp        string                 `json:"timestamp"`
	RespondentAge    int                    `json:"respondent_age"`
	RespondentGender string                 `json:"respondent_gender"`
	Ward             string                 `json:"ward"`
	City             string                 `json:"city"`
	Responses        map[string]interface{} `json:"responses"`
}

// SurveyTemplate defines survey structure
type SurveyTemplate struct {
	Name      string           `json:"name"`
	Questions []SurveyQuestion `json:"questions"`
}

// SurveyQuestion defines a survey question
type SurveyQuestion struct {
	ID      string   `json:"id"`
	Text    string   `json:"text"`
	Type    string   `json:"type"` // likert, multiple_choice, numeric, text
	Options []string `json:"options,omitempty"`
	Min     int      `json:"min,omitempty"`
	Max     int      `json:"max,omitempty"`
}

// Built-in survey templates for urban research
var UrbanSurveyTemplates = map[string]SurveyTemplate{
	"quality_of_life": {
		Name: "Urban Quality of Life Survey",
		Questions: []SurveyQuestion{
			{ID: "qol_overall", Text: "Overall satisfaction with city life", Type: "likert"},
			{ID: "qol_safety", Text: "Feeling of safety in neighborhood", Type: "likert"},
			{ID: "qol_transport", Text: "Satisfaction with public transport", Type: "likert"},
			{ID: "qol_healthcare", Text: "Access to healthcare facilities", Type: "likert"},
			{ID: "qol_education", Text: "Quality of educational institutions", Type: "likert"},
			{ID: "qol_pollution", Text: "Concern about air pollution", Type: "likert"},
			{ID: "qol_water", Text: "Reliability of water supply", Type: "likert"},
			{ID: "qol_electricity", Text: "Reliability of electricity", Type: "likert"},
		},
	},
	"mobility": {
		Name: "Urban Mobility Survey",
		Questions: []SurveyQuestion{
			{ID: "mob_mode", Text: "Primary mode of transport", Type: "multiple_choice", Options: []string{"Walk", "Bicycle", "Two-wheeler", "Car", "Bus", "Metro", "Auto-rickshaw", "Other"}},
			{ID: "mob_commute_time", Text: "Daily commute time (minutes)", Type: "numeric", Min: 0, Max: 180},
			{ID: "mob_cost", Text: "Monthly transport expenditure (INR)", Type: "numeric", Min: 0, Max: 20000},
			{ID: "mob_satisfaction", Text: "Satisfaction with commute", Type: "likert"},
			{ID: "mob_safety", Text: "Feeling of safety during commute", Type: "likert"},
		},
	},
	"housing": {
		Name: "Housing Conditions Survey",
		Questions: []SurveyQuestion{
			{ID: "house_type", Text: "Type of dwelling", Type: "multiple_choice", Options: []string{"Apartment", "Independent house", "Slum", "Chawl", "PG/Hostel", "Other"}},
			{ID: "house_ownership", Text: "Ownership status", Type: "multiple_choice", Options: []string{"Owned", "Rented", "Government housing", "Other"}},
			{ID: "house_rooms", Text: "Number of rooms", Type: "numeric", Min: 1, Max: 10},
			{ID: "house_rent", Text: "Monthly rent/EMI (INR)", Type: "numeric", Min: 0, Max: 100000},
			{ID: "house_satisfaction", Text: "Satisfaction with housing", Type: "likert"},
		},
	},
}

// GenerateSurveyResponses creates mock survey responses
func (g *DataGenerator) GenerateSurveyResponses(templateName string, city string, count int) []SurveyResponse {
	template, ok := UrbanSurveyTemplates[templateName]
	if !ok {
		template = UrbanSurveyTemplates["quality_of_life"]
	}

	responses := make([]SurveyResponse, count)
	baseTime := time.Now().AddDate(0, -1, 0)

	genders := []string{"Male", "Female", "Other"}

	for i := 0; i < count; i++ {
		timestamp := baseTime.Add(time.Duration(g.rng.Intn(30*24)) * time.Hour)

		respData := make(map[string]interface{})
		for _, q := range template.Questions {
			switch q.Type {
			case "likert":
				respData[q.ID] = g.rng.Intn(5) + 1 // 1-5 scale
			case "multiple_choice":
				respData[q.ID] = q.Options[g.rng.Intn(len(q.Options))]
			case "numeric":
				respData[q.ID] = q.Min + g.rng.Intn(q.Max-q.Min+1)
			case "text":
				respData[q.ID] = "Sample response"
			}
		}

		responses[i] = SurveyResponse{
			ResponseID:       g.GenerateQuaternionID(),
			Timestamp:        timestamp.Format(time.RFC3339),
			RespondentAge:    18 + g.rng.Intn(62),
			RespondentGender: genders[g.rng.Intn(len(genders))],
			Ward:             fmt.Sprintf("Ward-%d", g.rng.Intn(50)+1),
			City:             city,
			Responses:        respData,
		}
	}

	return responses
}

// ═══════════════════════════════════════════════════════════════════════════
// API SCHEMA GENERATION
// ═══════════════════════════════════════════════════════════════════════════

// GenerateResearchAPISchema creates API schema for research entities
func GenerateResearchAPISchema() []EntitySchema {
	return []EntitySchema{
		{
			Name:        "Survey",
			PluralName:  "Surveys",
			Description: "Research survey definitions",
			Fields: []Field{
				{Name: "Title", Type: "string", Required: true, Tags: []string{"searchable"}},
				{Name: "Description", Type: "string", Tags: []string{"searchable"}},
				{Name: "TemplateType", Type: "string", Required: true, Tags: []string{"filterable"}},
				{Name: "City", Type: "string", Tags: []string{"filterable"}},
				{Name: "Status", Type: "string", Tags: []string{"filterable"}},
				{Name: "ResponseCount", Type: "int", Tags: []string{"sortable"}},
			},
			Relations:  []Relation{{Name: "responses", TargetType: "SurveyResponse", Type: "one-to-many"}},
			SoftDelete: true,
			Timestamps: true,
			SacredSeed: SACRED_SEED,
		},
		{
			Name:        "ClimateDataset",
			PluralName:  "ClimateDatasets",
			Description: "Climate time series datasets",
			Fields: []Field{
				{Name: "Name", Type: "string", Required: true, Tags: []string{"searchable"}},
				{Name: "City", Type: "string", Required: true, Tags: []string{"filterable"}},
				{Name: "DataType", Type: "string", Tags: []string{"filterable"}},
				{Name: "StartDate", Type: "date", Tags: []string{"sortable"}},
				{Name: "EndDate", Type: "date", Tags: []string{"sortable"}},
				{Name: "RecordCount", Type: "int", Tags: []string{"sortable"}},
			},
			SoftDelete: true,
			Timestamps: true,
			SacredSeed: SACRED_SEED,
		},
		{
			Name:        "CensusDataset",
			PluralName:  "CensusDatasets",
			Description: "Census data collections",
			Fields: []Field{
				{Name: "Name", Type: "string", Required: true, Tags: []string{"searchable"}},
				{Name: "City", Type: "string", Required: true, Tags: []string{"filterable"}},
				{Name: "Year", Type: "int", Required: true, Tags: []string{"filterable", "sortable"}},
				{Name: "WardCount", Type: "int", Tags: []string{"sortable"}},
				{Name: "TotalPopulation", Type: "int", Tags: []string{"sortable"}},
			},
			SoftDelete: true,
			Timestamps: true,
			SacredSeed: SACRED_SEED,
		},
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// EXPORT FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// ExportToJSON exports data to JSON string
func ExportToJSON(data interface{}) (string, error) {
	bytes, err := json.MarshalIndent(data, "", "  ")
	if err != nil {
		return "", err
	}
	return string(bytes), nil
}

// ExportToCSV exports data to CSV string (for climate/census data)
func ExportClimateToCSV(data []ClimateDataPoint) string {
	var sb strings.Builder
	sb.WriteString("date,temperature,rainfall_mm,humidity_percent,aqi,city\n")
	for _, d := range data {
		sb.WriteString(fmt.Sprintf("%s,%.1f,%.1f,%.1f,%d,%s\n",
			d.Date, d.Temperature, d.Rainfall, d.Humidity, d.AQI, d.City))
	}
	return sb.String()
}

// ExportCensusToCSV exports census data to CSV
func ExportCensusToCSV(data []CensusRecord) string {
	var sb strings.Builder
	sb.WriteString("ward_id,ward_name,city,population,households,male_pop,female_pop,literacy_rate,worker_rate,avg_household_size\n")
	for _, d := range data {
		sb.WriteString(fmt.Sprintf("%s,%s,%s,%d,%d,%d,%d,%.1f,%.1f,%.1f\n",
			d.WardID, d.WardName, d.City, d.Population, d.Households,
			d.MalePopulation, d.FemalePopulation, d.LiteracyRate, d.WorkerRate, d.AvgHouseholdSize))
	}
	return sb.String()
}
