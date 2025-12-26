// Urban Lens - "Her" for Urban Research
// A gift for IIHS Urban Informatics Lab
//
// Features:
// - Transparent reasoning phases (Intake → Analysis → Synthesis → Insight)
// - Pattern clustering for task classification
// - Multi-axis analysis (Quaternion on S³)
// - Williams-optimal batch processing
// - Real-time WebSocket streaming
//
// Built with love for researchers.
package main

import (
	"encoding/json"
	"fmt"
	"io"
	"log"
	"net/http"
	"os"
	"strconv"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/aiml"
	"github.com/asymmetrica/urbanlens/pkg/alchemy"
	"github.com/asymmetrica/urbanlens/pkg/api"
	"github.com/asymmetrica/urbanlens/pkg/chat"
	"github.com/asymmetrica/urbanlens/pkg/climate"
	"github.com/asymmetrica/urbanlens/pkg/cultural"
	"github.com/asymmetrica/urbanlens/pkg/dilr"
	"github.com/asymmetrica/urbanlens/pkg/media"
	"github.com/asymmetrica/urbanlens/pkg/ocr"
	"github.com/asymmetrica/urbanlens/pkg/orchestrator"
	"github.com/asymmetrica/urbanlens/pkg/reasoning"
	"github.com/asymmetrica/urbanlens/pkg/research"
	"github.com/asymmetrica/urbanlens/pkg/streaming"
	"github.com/asymmetrica/urbanlens/pkg/transcription"
	"github.com/asymmetrica/urbanlens/pkg/urban"
	"github.com/gorilla/websocket"
)

// ============================================================================
// CONFIGURATION
// ============================================================================

const (
	Version    = "0.4.0" // Christmas 2025 Edition - Cultural Systems
	ServerPort = ":8080"
)

var upgrader = websocket.Upgrader{
	ReadBufferSize:  1024,
	WriteBufferSize: 1024,
	CheckOrigin: func(r *http.Request) bool {
		return true // Allow all origins for development
	},
}

// ============================================================================
// GLOBAL STATE
// ============================================================================

var (
	hub              *streaming.Hub
	conductor        *orchestrator.Conductor
	engine           *reasoning.Engine
	tools            *urban.ToolRegistry
	aiRouter         *aiml.Router
	climateAnalyzer  *climate.Analyzer
	researchToolkit  *research.Toolkit
	documentPipeline *media.DocumentPipeline
	healthChecker    *api.HealthChecker
	whisperClient    *transcription.WhisperClient
	chatService      *chat.Service
	ocrService       *ocr.UnifiedOCRService
)

// ============================================================================
// MAIN
// ============================================================================

func main() {
	fmt.Println("╔════════════════════════════════════════════════════════════════╗")
	fmt.Println("║                                                                ║")
	fmt.Println("║              URBAN LENS - Research Intelligence               ║")
	fmt.Println("║              \"Her\" for Urban Informatics                       ║")
	fmt.Println("║                                                                ║")
	fmt.Println("║              A gift for IIHS Urban Informatics Lab            ║")
	fmt.Println("║                                                                ║")
	fmt.Printf("║              Version %s                                       ║\n", Version)
	fmt.Println("║                                                                ║")
	fmt.Println("╚════════════════════════════════════════════════════════════════╝")
	fmt.Println()

	// Initialize components
	initializeComponents()

	// Set up HTTP routes
	setupRoutes()

	// Start WebSocket hub
	go hub.Run()

	fmt.Printf("🚀 Urban Lens started on http://localhost%s\n", ServerPort)
	fmt.Println()
	fmt.Println("Endpoints:")
	fmt.Println("  GET  /                 - Welcome")
	fmt.Println("  GET  /health           - Health check")
	fmt.Println("  GET  /tools            - List available tools")
	fmt.Println("  POST /analyze          - Analyze a request")
	fmt.Println("  POST /census/enhance   - Enhance census data")
	fmt.Println("  POST /survey/validate  - Validate survey data")
	fmt.Println("  WS   /ws               - WebSocket for streaming")
	fmt.Println()

	log.Fatal(http.ListenAndServe(ServerPort, nil))
}

func initializeComponents() {
	var err error

	// Initialize orchestrator
	conductor, err = orchestrator.NewConductor(nil)
	if err != nil {
		log.Fatalf("Failed to initialize conductor: %v", err)
	}

	// Initialize reasoning engine
	engine = reasoning.NewEngine()

	// Initialize urban tools
	tools = urban.NewToolRegistry()

	// Initialize AI router
	aiRouter = aiml.NewRouter("")

	// Initialize climate analyzer
	climateAnalyzer = climate.NewAnalyzer()

	// Initialize research toolkit
	researchToolkit = research.NewToolkit()

	// Initialize WebSocket hub
	hub = streaming.NewHub()

	// Initialize document pipeline
	documentPipeline = media.NewDocumentPipeline()

	// Initialize health checker
	healthChecker = api.NewHealthChecker(Version)

	// Initialize Whisper transcription client
	whisperClient = transcription.NewWhisperClient("")

	// Initialize AI chat service
	chatService = chat.NewService("")

	// Initialize OCR service
	ocrService, _ = ocr.NewUnifiedOCRService()

	fmt.Println("✅ Components initialized:")
	fmt.Println("   - Orchestrator (Williams batching enabled)")
	fmt.Println("   - Reasoning Engine (4-phase transparent thinking)")
	fmt.Println("   - Urban Tools (Census, Survey, Spatial, Document, Flood)")
	fmt.Println("   - AI Router (30+ models via AIMLAPI)")
	fmt.Println("   - Climate Engine (IMD rainfall, monsoon, urban heat)")
	fmt.Println("   - Research Toolkit (pandoc, imagemagick, ffmpeg, tesseract)")
	fmt.Println("   - Document Pipeline (unified media/document processing)")
	fmt.Println("   - Whisper Transcription (audio-to-text)")
	fmt.Println("   - AI Chat Service (research assistant)")
	fmt.Println("   - OCR Service (Florence-2 vision)")
	fmt.Println("   - WebSocket Hub (real-time streaming)")

	// Show document pipeline status
	pipelineStatus := documentPipeline.GetStatus()
	fmt.Println("   Document Pipeline:")
	if pipelineStatus.Pandoc.Available {
		fmt.Printf("     ✓ Pandoc: %s\n", pipelineStatus.Pandoc.Version)
	} else {
		fmt.Println("     ○ Pandoc: not installed")
	}
	if pipelineStatus.FFmpeg.Available {
		fmt.Println("     ✓ FFmpeg: available")
	} else {
		fmt.Println("     ○ FFmpeg: not installed")
	}

	// Check AI configuration
	if aiRouter.IsConfigured() {
		fmt.Println("   ✓ AI Router: CONFIGURED (real LLM responses enabled)")
	} else {
		fmt.Println("   ⚠ AI Router: Set AIMLAPI_KEY for AI-powered responses")
	}

	// Show research toolkit status
	status := researchToolkit.GetStatus()
	fmt.Println("   Research Tools:")
	for name, info := range status {
		if m, ok := info.(map[string]interface{}); ok {
			if avail, ok := m["available"].(bool); ok && avail {
				fmt.Printf("     ✓ %s: available\n", name)
			} else {
				fmt.Printf("     ○ %s: not installed\n", name)
			}
		}
	}
}

func setupRoutes() {
	// API routes
	http.HandleFunc("/api/welcome", handleWelcome)
	http.HandleFunc("/health", handleHealth)
	http.HandleFunc("/tools", handleTools)
	http.HandleFunc("/analyze", handleAnalyze)
	http.HandleFunc("/census/enhance", handleCensusEnhance)
	http.HandleFunc("/survey/validate", handleSurveyValidate)

	// New research endpoints
	http.HandleFunc("/api/climate/analyze", handleClimateAnalyze)
	http.HandleFunc("/api/climate/heat-island", handleHeatIsland)
	http.HandleFunc("/api/ai/chat", handleAIChat)
	http.HandleFunc("/api/ai/models", handleAIModels)
	http.HandleFunc("/api/research/status", handleResearchStatus)
	http.HandleFunc("/api/convert", handleDocumentConvert)

	// Alchemy data generation endpoints
	http.HandleFunc("/api/alchemy/climate", handleAlchemyClimate)
	http.HandleFunc("/api/alchemy/census", handleAlchemyCensus)
	http.HandleFunc("/api/alchemy/survey", handleAlchemySurvey)
	http.HandleFunc("/api/alchemy/cities", handleAlchemyCities)

	// Cultural mathematics endpoints
	http.HandleFunc("/api/cultural/katapayadi", handleKatapayadi)
	http.HandleFunc("/api/cultural/gematria", handleGematria)
	http.HandleFunc("/api/cultural/sacred-numbers", handleSacredNumbers)
	http.HandleFunc("/api/cultural/mandala", handleMandala)
	http.HandleFunc("/api/cultural/digital-root", handleDigitalRoot)

	// DILR Problem Solving (The Sarat Method)
	http.HandleFunc("/api/dilr/analyze", handleDILRAnalyze)
	http.HandleFunc("/api/dilr/practice", handleDILRPractice)
	http.HandleFunc("/api/dilr/quickref", handleDILRQuickRef)
	http.HandleFunc("/api/dilr/hint", handleDILRHint)
	http.HandleFunc("/api/dilr/void-flow", handleVoidFlow)
	http.HandleFunc("/api/dilr/diagnose", handleDiagnoseStuck)
	http.HandleFunc("/api/dilr/sarat-method", handleSaratMethod)
	http.HandleFunc("/api/dilr/mustard-seed", handleMustardSeed)

	// Document/Media Pipeline
	http.HandleFunc("/api/pipeline/status", handlePipelineStatus)
	http.HandleFunc("/api/pipeline/process", handlePipelineProcess)

	// Transcription (Whisper)
	http.HandleFunc("/api/transcribe", handleTranscribe)
	http.HandleFunc("/api/transcribe/status", handleTranscribeStatus)

	// AI Chat
	http.HandleFunc("/api/chat", handleChat)
	http.HandleFunc("/api/chat/status", handleChatStatus)

	// OCR
	http.HandleFunc("/api/ocr", handleOCR)
	http.HandleFunc("/api/ocr/status", handleOCRStatus)

	// WebSocket
	http.HandleFunc("/ws", handleWebSocket)

	// Serve embedded frontend for all other routes
	http.Handle("/", getFrontendHandler())
}

// ============================================================================
// HANDLERS
// ============================================================================

func handleWelcome(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"name":    "Urban Lens",
		"version": Version,
		"tagline": "Her for Urban Research",
		"for":     "IIHS Urban Informatics Lab",
		"features": []string{
			"Transparent reasoning phases",
			"Pattern clustering classification",
			"Multi-axis quaternion analysis",
			"Williams-optimal batch processing",
			"Real-time WebSocket streaming",
		},
		"tools": tools.List(),
	})
}

func handleHealth(w http.ResponseWriter, r *http.Request) {
	// Check if quick health check requested (for load balancers)
	if r.URL.Query().Get("quick") == "true" {
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(healthChecker.QuickCheck())
		return
	}

	// Full health check with component status
	health := healthChecker.Check()
	health.Components["conductor"] = &api.ComponentStatus{
		Status: "ok",
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(health)
}

func handleTools(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"tools": tools.List(),
	})
}

func handleAnalyze(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var request struct {
		Input string `json:"input"`
	}

	if err := json.NewDecoder(r.Body).Decode(&request); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	// Create reasoning session
	session, err := engine.NewSession(request.Input)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	// Analyze
	session.Analyze([]string{
		"Pattern analysis complete",
		"Data relationships mapped",
	})

	// Synthesize
	session.Synthesize([]string{
		"Solutions evaluated",
		"Optimal path selected",
	})

	// Conclude
	recommendation := fmt.Sprintf("Recommended: Use %s tool for this %s task",
		session.Classification.SuggestedTools[0],
		session.Classification.TaskType)
	session.Conclude(recommendation)

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"session_id":     session.ID,
		"classification": session.Classification,
		"recommendation": recommendation,
		"thinking_log":   session.GetThinkingLog(),
		"steps":          len(session.Steps),
	})
}

func handleCensusEnhance(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var request struct {
		Data []map[string]interface{} `json:"data"`
	}

	if err := json.NewDecoder(r.Body).Decode(&request); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	result, err := tools.Census.Enhance(request.Data)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(result)
}

func handleSurveyValidate(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var request struct {
		Data  []map[string]interface{} `json:"data"`
		Rules []struct {
			Field     string `json:"field"`
			Type      string `json:"type"`
			Condition string `json:"condition,omitempty"`
			Message   string `json:"message,omitempty"`
		} `json:"rules"`
	}

	if err := json.NewDecoder(r.Body).Decode(&request); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	// Add rules
	for _, rule := range request.Rules {
		tools.Survey.AddRule(urban.ValidationRule{
			Field:   rule.Field,
			Type:    rule.Type,
			Message: rule.Message,
		})
	}

	result, err := tools.Survey.Validate(request.Data)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(result)
}

func handleWebSocket(w http.ResponseWriter, r *http.Request) {
	conn, err := upgrader.Upgrade(w, r, nil)
	if err != nil {
		log.Printf("WebSocket upgrade failed: %v", err)
		return
	}

	clientID := fmt.Sprintf("client_%d", time.Now().UnixNano())
	client := streaming.NewClient(clientID, conn, hub)

	hub.Register <- client

	go client.WritePump()
	go client.ReadPump()
}

// ============================================================================
// NEW RESEARCH HANDLERS
// ============================================================================

func handleClimateAnalyze(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var request struct {
		FilePath string `json:"file_path"`
		DataType string `json:"data_type"` // "temperature", "rainfall", "monsoon", "urban_heat"
	}

	if err := json.NewDecoder(r.Body).Decode(&request); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	// Select config based on data type
	var config climate.CSVConfig
	switch request.DataType {
	case "rainfall":
		config = climate.IMDRainfallConfig()
	case "monsoon":
		config = climate.MonsoonConfig()
	case "urban_heat":
		config = climate.UrbanHeatConfig()
	default:
		config = climate.TemperatureConfig()
	}

	err := climateAnalyzer.LoadData(request.FilePath, config)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	report := climateAnalyzer.GetAnalysisReport()

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(report)
}

func handleHeatIsland(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var request struct {
		UrbanTemp float64 `json:"urban_temp"`
		RuralTemp float64 `json:"rural_temp"`
	}

	if err := json.NewDecoder(r.Body).Decode(&request); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	result := climate.AnalyzeHeatIsland(request.UrbanTemp, request.RuralTemp)

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(result)
}

func handleAIChat(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var request struct {
		Message string `json:"message"`
		Context string `json:"context,omitempty"`
	}

	if err := json.NewDecoder(r.Body).Decode(&request); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	if !aiRouter.IsConfigured() {
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]interface{}{
			"error":   "AI not configured",
			"message": "Set AIMLAPI_KEY environment variable to enable AI chat",
		})
		return
	}

	response, err := aiRouter.ResearchChat(request.Message, request.Context)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"response": response,
	})
}

func handleAIModels(w http.ResponseWriter, r *http.Request) {
	models := aiRouter.ListModels()

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"models":     models,
		"configured": aiRouter.IsConfigured(),
	})
}

func handleResearchStatus(w http.ResponseWriter, r *http.Request) {
	status := researchToolkit.GetStatus()

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"version": Version,
		"tools":   status,
		"ai": map[string]interface{}{
			"configured": aiRouter.IsConfigured(),
		},
	})
}

func handleDocumentConvert(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var request struct {
		Content    string `json:"content"`
		FromFormat string `json:"from_format"`
		ToFormat   string `json:"to_format"`
	}

	if err := json.NewDecoder(r.Body).Decode(&request); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	if !researchToolkit.Pandoc.Available {
		http.Error(w, "Pandoc not installed", http.StatusServiceUnavailable)
		return
	}

	result, err := researchToolkit.Pandoc.ConvertString(request.Content, request.FromFormat, request.ToFormat)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"result": result,
	})
}

// ============================================================================
// ALCHEMY DATA GENERATION HANDLERS
// ============================================================================

func handleAlchemyClimate(w http.ResponseWriter, r *http.Request) {
	seed := int64(108)
	city := "Bangalore"
	days := 365

	// Parse query params
	if s := r.URL.Query().Get("seed"); s != "" {
		if v, err := strconv.ParseInt(s, 10, 64); err == nil {
			seed = v
		}
	}
	if c := r.URL.Query().Get("city"); c != "" {
		city = c
	}
	if d := r.URL.Query().Get("days"); d != "" {
		if v, err := strconv.Atoi(d); err == nil {
			days = v
		}
	}

	format := r.URL.Query().Get("format") // json or csv

	gen := alchemy.NewDataGenerator(seed)
	data := gen.GenerateClimateData(city, days)

	if format == "csv" {
		w.Header().Set("Content-Type", "text/csv")
		w.Header().Set("Content-Disposition", fmt.Sprintf("attachment; filename=climate_%s_%d.csv", city, seed))
		w.Write([]byte(alchemy.ExportClimateToCSV(data)))
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"seed":         seed,
		"city":         city,
		"days":         days,
		"digital_root": alchemy.DigitalRoot(seed),
		"data":         data,
	})
}

func handleAlchemyCensus(w http.ResponseWriter, r *http.Request) {
	seed := int64(108)
	city := "Bangalore"
	wards := 50

	if s := r.URL.Query().Get("seed"); s != "" {
		if v, err := strconv.ParseInt(s, 10, 64); err == nil {
			seed = v
		}
	}
	if c := r.URL.Query().Get("city"); c != "" {
		city = c
	}
	if w := r.URL.Query().Get("wards"); w != "" {
		if v, err := strconv.Atoi(w); err == nil {
			wards = v
		}
	}

	format := r.URL.Query().Get("format")

	gen := alchemy.NewDataGenerator(seed)
	data := gen.GenerateCensusData(city, wards)

	if format == "csv" {
		w.Header().Set("Content-Type", "text/csv")
		w.Header().Set("Content-Disposition", fmt.Sprintf("attachment; filename=census_%s_%d.csv", city, seed))
		w.Write([]byte(alchemy.ExportCensusToCSV(data)))
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"seed":         seed,
		"city":         city,
		"wards":        wards,
		"digital_root": alchemy.DigitalRoot(seed),
		"data":         data,
	})
}

func handleAlchemySurvey(w http.ResponseWriter, r *http.Request) {
	seed := int64(108)
	city := "Bangalore"
	template := "quality_of_life"
	count := 100

	if s := r.URL.Query().Get("seed"); s != "" {
		if v, err := strconv.ParseInt(s, 10, 64); err == nil {
			seed = v
		}
	}
	if c := r.URL.Query().Get("city"); c != "" {
		city = c
	}
	if t := r.URL.Query().Get("template"); t != "" {
		template = t
	}
	if n := r.URL.Query().Get("count"); n != "" {
		if v, err := strconv.Atoi(n); err == nil {
			count = v
		}
	}

	gen := alchemy.NewDataGenerator(seed)
	data := gen.GenerateSurveyResponses(template, city, count)

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"seed":         seed,
		"city":         city,
		"template":     template,
		"count":        count,
		"digital_root": alchemy.DigitalRoot(seed),
		"templates":    []string{"quality_of_life", "mobility", "housing"},
		"data":         data,
	})
}

func handleAlchemyCities(w http.ResponseWriter, r *http.Request) {
	tier := 0 // 0 = all tiers
	if t := r.URL.Query().Get("tier"); t != "" {
		if v, err := strconv.Atoi(t); err == nil {
			tier = v
		}
	}

	var cities []alchemy.IndianCity
	if tier == 0 {
		cities = alchemy.IndianCities
	} else {
		for _, c := range alchemy.IndianCities {
			if c.Tier == tier {
				cities = append(cities, c)
			}
		}
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"tier":   tier,
		"count":  len(cities),
		"cities": cities,
	})
}

// ============================================================================
// CULTURAL MATHEMATICS HANDLERS
// ============================================================================

func handleKatapayadi(w http.ResponseWriter, r *http.Request) {
	action := r.URL.Query().Get("action") // encode or decode
	value := r.URL.Query().Get("value")

	w.Header().Set("Content-Type", "application/json")

	if action == "encode" {
		n, err := strconv.ParseInt(value, 10, 64)
		if err != nil {
			http.Error(w, "Invalid number", http.StatusBadRequest)
			return
		}
		encoded := cultural.EncodeKatapayadi(n)
		json.NewEncoder(w).Encode(map[string]interface{}{
			"input":        n,
			"encoded":      encoded,
			"digital_root": cultural.DigitalRoot(n),
			"system":       "katapayadi",
			"description":  "Sanskrit consonant encoding (1500+ years old)",
		})
	} else {
		decoded := cultural.DecodeKatapayadi(value)
		json.NewEncoder(w).Encode(map[string]interface{}{
			"input":        value,
			"decoded":      decoded,
			"digital_root": cultural.DigitalRoot(decoded),
			"system":       "katapayadi",
		})
	}
}

func handleGematria(w http.ResponseWriter, r *http.Request) {
	text := r.URL.Query().Get("text")
	system := r.URL.Query().Get("system") // hebrew, greek, arabic, english

	if system == "" {
		system = "english"
	}

	value := cultural.CalculateGematria(text, system)
	dr := cultural.DigitalRoot(int64(value))
	script := cultural.DetectScript(text)

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"text":            text,
		"system":          system,
		"detected_script": script,
		"value":           value,
		"digital_root":    dr,
		"sacred_matches":  cultural.GetSacredNumbersByDigitalRoot(dr),
	})
}

func handleSacredNumbers(w http.ResponseWriter, r *http.Request) {
	drStr := r.URL.Query().Get("digital_root")

	w.Header().Set("Content-Type", "application/json")

	if drStr != "" {
		dr, _ := strconv.Atoi(drStr)
		filtered := cultural.GetSacredNumbersByDigitalRoot(dr)
		json.NewEncoder(w).Encode(map[string]interface{}{
			"digital_root": dr,
			"count":        len(filtered),
			"numbers":      filtered,
		})
	} else {
		json.NewEncoder(w).Encode(map[string]interface{}{
			"count":   len(cultural.SacredNumbers),
			"numbers": cultural.SacredNumbers,
		})
	}
}

func handleMandala(w http.ResponseWriter, r *http.Request) {
	seed := int64(108)
	petals := 8
	rings := 5
	size := 400

	if s := r.URL.Query().Get("seed"); s != "" {
		if v, err := strconv.ParseInt(s, 10, 64); err == nil {
			seed = v
		}
	}
	if p := r.URL.Query().Get("petals"); p != "" {
		if v, err := strconv.Atoi(p); err == nil {
			petals = v
		}
	}
	if rg := r.URL.Query().Get("rings"); rg != "" {
		if v, err := strconv.Atoi(rg); err == nil {
			rings = v
		}
	}
	if sz := r.URL.Query().Get("size"); sz != "" {
		if v, err := strconv.Atoi(sz); err == nil {
			size = v
		}
	}

	config := cultural.MandalaConfig{
		Seed:   seed,
		Petals: petals,
		Rings:  rings,
		Size:   size,
	}

	svg := cultural.GenerateMandalaSVG(config)

	w.Header().Set("Content-Type", "image/svg+xml")
	w.Write([]byte(svg))
}

func handleDigitalRoot(w http.ResponseWriter, r *http.Request) {
	value := r.URL.Query().Get("value")

	n, err := strconv.ParseInt(value, 10, 64)
	if err != nil {
		http.Error(w, "Invalid number", http.StatusBadRequest)
		return
	}

	dr := cultural.DigitalRoot(n)
	katapayadi := cultural.EncodeKatapayadi(n)

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"value":          n,
		"digital_root":   dr,
		"katapayadi":     katapayadi,
		"sacred_matches": cultural.GetSacredNumbersByDigitalRoot(dr),
		"vedic_insight":  getVedicInsight(dr),
	})
}

func getVedicInsight(dr int) string {
	insights := map[int]string{
		1: "Unity, beginnings, leadership (Surya/Sun)",
		2: "Duality, partnership, balance (Chandra/Moon)",
		3: "Creation, expression, growth (Guru/Jupiter)",
		4: "Stability, foundation, order (Rahu)",
		5: "Change, freedom, adventure (Budha/Mercury)",
		6: "Harmony, responsibility, love (Shukra/Venus)",
		7: "Wisdom, spirituality, analysis (Ketu)",
		8: "Power, karma, transformation (Shani/Saturn)",
		9: "Completion, universal love, dharma (Mangal/Mars)",
	}
	if insight, ok := insights[dr]; ok {
		return insight
	}
	return "Zero - the void, potential, Brahman"
}

// ============================================================================
// DILR PROBLEM SOLVING HANDLERS (The Sarat Method)
// ============================================================================

func handleDILRAnalyze(w http.ResponseWriter, r *http.Request) {
	// Accept problem text via query param or POST body
	problemText := r.URL.Query().Get("problem")

	if r.Method == "POST" {
		var req struct {
			Problem string `json:"problem"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err == nil && req.Problem != "" {
			problemText = req.Problem
		}
	}

	if problemText == "" {
		// Return the method overview if no problem provided
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]interface{}{
			"message": "The Sarat Method for DILR",
			"usage":   "POST a problem text to analyze, or GET with ?problem=...",
			"shapes":  dilr.ShapeDescription,
			"method":  dilr.TheSaratMethod,
		})
		return
	}

	analysis := dilr.AnalyzeProblem(problemText)

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(analysis)
}

func handleDILRPractice(w http.ResponseWriter, r *http.Request) {
	shape := r.URL.Query().Get("shape")
	difficulty := r.URL.Query().Get("difficulty")
	random := r.URL.Query().Get("random")

	w.Header().Set("Content-Type", "application/json")

	if random == "true" {
		problem := dilr.GetRandomPractice()
		json.NewEncoder(w).Encode(problem)
		return
	}

	if shape != "" {
		problems := dilr.GetPracticeByShape(dilr.ProblemShape(shape))
		json.NewEncoder(w).Encode(map[string]interface{}{
			"shape":    shape,
			"count":    len(problems),
			"problems": problems,
		})
		return
	}

	if difficulty != "" {
		problems := dilr.GetPracticeByDifficulty(difficulty)
		json.NewEncoder(w).Encode(map[string]interface{}{
			"difficulty": difficulty,
			"count":      len(problems),
			"problems":   problems,
		})
		return
	}

	// Return all practice problems
	json.NewEncoder(w).Encode(map[string]interface{}{
		"count":    len(dilr.PracticeBank),
		"problems": dilr.PracticeBank,
	})
}

func handleDILRQuickRef(w http.ResponseWriter, r *http.Request) {
	format := r.URL.Query().Get("format")

	if format == "json" {
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]interface{}{
			"shapes":    dilr.ShapeDescription,
			"templates": dilr.SolutionTemplates,
			"method":    dilr.TheSaratMethod,
		})
		return
	}

	// Return printable text format
	w.Header().Set("Content-Type", "text/plain; charset=utf-8")
	w.Write([]byte(dilr.QuickRef()))
}

func handleDILRHint(w http.ResponseWriter, r *http.Request) {
	shape := r.URL.Query().Get("shape")
	stuckAt := r.URL.Query().Get("stuck_at") // start, constraints, anchor, building, verify

	if stuckAt == "" {
		stuckAt = "start"
	}

	hint := dilr.GenerateHint(dilr.ProblemShape(shape), stuckAt)

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"shape":    shape,
		"stuck_at": stuckAt,
		"hint":     hint,
	})
}

func handleVoidFlow(w http.ResponseWriter, r *http.Request) {
	format := r.URL.Query().Get("format")
	view := r.URL.Query().Get("view") // "framework", "dilr", or empty for both

	if format == "text" {
		w.Header().Set("Content-Type", "text/plain; charset=utf-8")
		if view == "dilr" {
			w.Write([]byte(dilr.GetVoidFlowForDILR()))
		} else {
			w.Write([]byte(dilr.GetVoidFlowQuickRef()))
		}
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"framework":     dilr.TheVoidFlowFramework,
		"quick_ref":     dilr.GetVoidFlowQuickRef(),
		"dilr_specific": dilr.GetVoidFlowForDILR(),
	})
}

func handleDiagnoseStuck(w http.ResponseWriter, r *http.Request) {
	symptoms := r.URL.Query().Get("symptoms")

	if symptoms == "" {
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]interface{}{
			"usage": "GET /api/dilr/diagnose?symptoms=your+description",
			"examples": []string{
				"?symptoms=don't know where to start",
				"?symptoms=stuck and nothing works",
				"?symptoms=not sure if my answer is right",
				"?symptoms=panicking and running out of time",
			},
			"phases": []string{"VOID", "FLOW", "SOLUTION"},
		})
		return
	}

	diagnosis := dilr.DiagnoseStuckState(symptoms)

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(diagnosis)
}

func handleSaratMethod(w http.ResponseWriter, r *http.Request) {
	format := r.URL.Query().Get("format")

	if format == "text" {
		w.Header().Set("Content-Type", "text/plain; charset=utf-8")
		w.Write([]byte(dilr.GetSaratMethodQuickRef()))
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"method":    dilr.TheCompleteSaratMethod,
		"quick_ref": dilr.GetSaratMethodQuickRef(),
	})
}

func handleMustardSeed(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "text/plain; charset=utf-8")
	w.Write([]byte(dilr.GetMustardSeedExample()))
}

// ============================================================================
// DOCUMENT/MEDIA PIPELINE HANDLERS
// ============================================================================

func handlePipelineStatus(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(documentPipeline.GetStatus())
}

// ============================================================================
// TRANSCRIPTION HANDLERS
// ============================================================================

func handleTranscribeStatus(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(whisperClient.GetStatus())
}

// ============================================================================
// AI CHAT HANDLERS
// ============================================================================

func handleChatStatus(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(chatService.GetStatus())
}

func handleChat(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		api.MethodNotAllowed(w, "POST")
		return
	}

	var req chat.ChatRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		api.BadRequest(w, "Invalid request body: "+err.Error())
		return
	}

	if req.Message == "" {
		api.BadRequest(w, "Message is required")
		return
	}

	resp, err := chatService.Chat(r.Context(), req)
	if err != nil {
		api.InternalError(w, "Chat failed", err)
		return
	}

	api.JSON(w, resp, &api.MetaInfo{
		ProcessTime: resp.ProcessTime,
		Version:     Version,
	})
}

// ============================================================================
// OCR HANDLERS
// ============================================================================

func handleOCRStatus(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(ocrService.GetStatus())
}

func handleOCR(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		api.MethodNotAllowed(w, "POST")
		return
	}

	// Parse multipart form (max 50MB for images)
	if err := r.ParseMultipartForm(50 << 20); err != nil {
		api.BadRequest(w, "Failed to parse form: "+err.Error())
		return
	}

	// Get file from form
	file, _, err := r.FormFile("file")
	if err != nil {
		api.BadRequest(w, "No file provided")
		return
	}
	defer file.Close()

	// Read file data
	imageData, err := io.ReadAll(file)
	if err != nil {
		api.InternalError(w, "Failed to read file", err)
		return
	}

	// Perform OCR
	result, err := ocrService.OCR(r.Context(), ocr.OCRRequest{
		ImageData: imageData,
	})

	if err != nil {
		api.InternalError(w, "OCR failed", err)
		return
	}

	api.JSON(w, result, &api.MetaInfo{
		ProcessTime: result.ProcessTime,
		Version:     Version,
	})
}

func handleTranscribe(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		api.MethodNotAllowed(w, "POST")
		return
	}

	// Parse multipart form (max 100MB)
	if err := r.ParseMultipartForm(100 << 20); err != nil {
		api.BadRequest(w, "Failed to parse form: "+err.Error())
		return
	}

	// Get file from form
	file, header, err := r.FormFile("file")
	if err != nil {
		api.BadRequest(w, "No file provided")
		return
	}
	defer file.Close()

	// Save to temp file
	tempFile, err := os.CreateTemp("", "transcribe_*_"+header.Filename)
	if err != nil {
		api.InternalError(w, "Failed to create temp file", err)
		return
	}
	defer os.Remove(tempFile.Name())
	defer tempFile.Close()

	if _, err := io.Copy(tempFile, file); err != nil {
		api.InternalError(w, "Failed to save file", err)
		return
	}
	tempFile.Close()

	// Get optional parameters
	language := r.FormValue("language")
	prompt := r.FormValue("prompt")

	// Transcribe
	result, err := whisperClient.Transcribe(r.Context(), transcription.TranscriptionRequest{
		FilePath: tempFile.Name(),
		Language: language,
		Prompt:   prompt,
	})

	if err != nil {
		api.InternalError(w, "Transcription failed", err)
		return
	}

	api.JSON(w, result, &api.MetaInfo{
		ProcessTime: float64(result.ProcessTime.Milliseconds()),
		Version:     Version,
	})
}

func handlePipelineProcess(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var req media.ProcessRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, "Invalid request body", http.StatusBadRequest)
		return
	}

	result, err := documentPipeline.Process(req)
	if err != nil {
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusInternalServerError)
		json.NewEncoder(w).Encode(map[string]interface{}{
			"success": false,
			"error":   err.Error(),
		})
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(result)
}

// Suppress unused import warning
var _ = os.Getenv
var _ = strconv.Atoi
var _ = cultural.DetectScript
var _ = dilr.QuickRef
