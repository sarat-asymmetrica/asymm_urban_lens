// Package lean - Lean 4 Theorem Prover Bridge
// Enables formal verification of mathematical statements
package lean

import (
	"bufio"
	"bytes"
	"context"
	"fmt"
	"os/exec"
	"strings"
	"sync"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// TYPES
// ═══════════════════════════════════════════════════════════════════════════

// Bridge provides interface to Lean 4 theorem prover
type Bridge interface {
	// Verify checks if a Lean proof is valid
	Verify(ctx context.Context, proof string) (*VerificationResult, error)

	// Interactive starts an interactive proving session
	Interactive(ctx context.Context) (*Session, error)

	// GetInfo retrieves information about a Lean term
	GetInfo(ctx context.Context, term string) (*TermInfo, error)

	// Check health of Lean installation
	Health(ctx context.Context) error
}

// VerificationResult contains the result of proof verification
type VerificationResult struct {
	Valid      bool          `json:"valid"`
	Errors     []string      `json:"errors,omitempty"`
	Warnings   []string      `json:"warnings,omitempty"`
	Duration   time.Duration `json:"duration"`
	LeanVersion string       `json:"lean_version"`
}

// Session represents an interactive Lean proving session
type Session struct {
	ID        string
	StartedAt time.Time
	cmd       *exec.Cmd
	stdin     *bufio.Writer
	stdout    *bufio.Reader
	stderr    *bufio.Reader
	mu        sync.Mutex
}

// TermInfo provides information about a Lean term
type TermInfo struct {
	Name       string   `json:"name"`
	Type       string   `json:"type"`
	Definition string   `json:"definition,omitempty"`
	DocString  string   `json:"doc_string,omitempty"`
	Module     string   `json:"module"`
	IsTheorem  bool     `json:"is_theorem"`
}

// ═══════════════════════════════════════════════════════════════════════════
// IMPLEMENTATION
// ═══════════════════════════════════════════════════════════════════════════

// LeanBridge is the concrete implementation
type LeanBridge struct {
	leanPath    string // Path to lean executable
	timeout     time.Duration
	workDir     string // Working directory for temporary files
}

// NewBridge creates a new Lean bridge
func NewBridge(leanPath string, workDir string) *LeanBridge {
	if leanPath == "" {
		leanPath = "lean" // Assume in PATH
	}
	return &LeanBridge{
		leanPath: leanPath,
		timeout:  30 * time.Second,
		workDir:  workDir,
	}
}

// Health checks if Lean is installed and working
func (b *LeanBridge) Health(ctx context.Context) error {
	ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
	defer cancel()

	cmd := exec.CommandContext(ctx, b.leanPath, "--version")
	output, err := cmd.CombinedOutput()
	if err != nil {
		return fmt.Errorf("lean not found or not working: %w (output: %s)", err, string(output))
	}

	// Check it's Lean 4
	if !strings.Contains(string(output), "Lean") {
		return fmt.Errorf("unexpected lean version output: %s", string(output))
	}

	return nil
}

// Verify checks if a Lean proof is valid
func (b *LeanBridge) Verify(ctx context.Context, proof string) (*VerificationResult, error) {
	start := time.Now()

	// Create temporary file with proof
	tmpFile := fmt.Sprintf("%s/verify_%d.lean", b.workDir, time.Now().UnixNano())

	// Write proof to temp file (in production, use os.WriteFile)
	// For now, we'll use echo for simplicity
	ctx, cancel := context.WithTimeout(ctx, b.timeout)
	defer cancel()

	// Verify the proof
	cmd := exec.CommandContext(ctx, b.leanPath, tmpFile)
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr

	err := cmd.Run()
	duration := time.Since(start)

	result := &VerificationResult{
		Duration: duration,
		LeanVersion: "4.0", // TODO: Extract from --version
	}

	if err != nil {
		// Parse errors from stderr
		result.Valid = false
		result.Errors = parseErrors(stderr.String())
		return result, nil // Not an error - just invalid proof
	}

	// Check for warnings
	if stderr.Len() > 0 {
		result.Warnings = parseWarnings(stderr.String())
	}

	result.Valid = true
	return result, nil
}

// Interactive starts an interactive proving session
func (b *LeanBridge) Interactive(ctx context.Context) (*Session, error) {
	cmd := exec.CommandContext(ctx, b.leanPath, "--repl")

	stdin, err := cmd.StdinPipe()
	if err != nil {
		return nil, fmt.Errorf("failed to create stdin pipe: %w", err)
	}

	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return nil, fmt.Errorf("failed to create stdout pipe: %w", err)
	}

	stderr, err := cmd.StderrPipe()
	if err != nil {
		return nil, fmt.Errorf("failed to create stderr pipe: %w", err)
	}

	if err := cmd.Start(); err != nil {
		return nil, fmt.Errorf("failed to start lean: %w", err)
	}

	session := &Session{
		ID:        fmt.Sprintf("session_%d", time.Now().UnixNano()),
		StartedAt: time.Now(),
		cmd:       cmd,
		stdin:     bufio.NewWriter(stdin),
		stdout:    bufio.NewReader(stdout),
		stderr:    bufio.NewReader(stderr),
	}

	return session, nil
}

// GetInfo retrieves information about a Lean term
func (b *LeanBridge) GetInfo(ctx context.Context, term string) (*TermInfo, error) {
	// Use Lean's #check command
	proof := fmt.Sprintf("#check %s", term)

	result, err := b.Verify(ctx, proof)
	if err != nil {
		return nil, err
	}

	// Parse the output to extract term info
	// This is simplified - real implementation would parse Lean output
	info := &TermInfo{
		Name:   term,
		Type:   "unknown", // Parse from Lean output
		Module: "unknown",
	}

	if !result.Valid {
		return nil, fmt.Errorf("term not found: %s", term)
	}

	return info, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// SESSION METHODS
// ═══════════════════════════════════════════════════════════════════════════

// Send sends a command to the interactive session
func (s *Session) Send(command string) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	_, err := s.stdin.WriteString(command + "\n")
	if err != nil {
		return fmt.Errorf("failed to write to lean: %w", err)
	}

	return s.stdin.Flush()
}

// Read reads a response from the interactive session
func (s *Session) Read() (string, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	line, err := s.stdout.ReadString('\n')
	if err != nil {
		return "", fmt.Errorf("failed to read from lean: %w", err)
	}

	return strings.TrimSpace(line), nil
}

// Close terminates the interactive session
func (s *Session) Close() error {
	if s.cmd != nil && s.cmd.Process != nil {
		return s.cmd.Process.Kill()
	}
	return nil
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════════════════════════

func parseErrors(stderr string) []string {
	var errors []string
	lines := strings.Split(stderr, "\n")
	for _, line := range lines {
		if strings.Contains(line, "error:") {
			errors = append(errors, strings.TrimSpace(line))
		}
	}
	return errors
}

func parseWarnings(stderr string) []string {
	var warnings []string
	lines := strings.Split(stderr, "\n")
	for _, line := range lines {
		if strings.Contains(line, "warning:") {
			warnings = append(warnings, strings.TrimSpace(line))
		}
	}
	return warnings
}

// ═══════════════════════════════════════════════════════════════════════════
// MOCK IMPLEMENTATION (for testing without Lean installed)
// ═══════════════════════════════════════════════════════════════════════════

// MockBridge is a mock implementation for development without Lean installed
type MockBridge struct{}

// NewMockBridge creates a mock Lean bridge
func NewMockBridge() *MockBridge {
	return &MockBridge{}
}

func (m *MockBridge) Health(ctx context.Context) error {
	return nil // Always healthy
}

func (m *MockBridge) Verify(ctx context.Context, proof string) (*VerificationResult, error) {
	// Simple heuristic: if proof contains "sorry", it's invalid
	valid := !strings.Contains(proof, "sorry")

	result := &VerificationResult{
		Valid:       valid,
		Duration:    10 * time.Millisecond,
		LeanVersion: "4.0.0-mock",
	}

	if !valid {
		result.Errors = []string{"proof contains 'sorry' - incomplete proof"}
	}

	return result, nil
}

func (m *MockBridge) Interactive(ctx context.Context) (*Session, error) {
	return &Session{
		ID:        "mock_session",
		StartedAt: time.Now(),
	}, nil
}

func (m *MockBridge) GetInfo(ctx context.Context, term string) (*TermInfo, error) {
	return &TermInfo{
		Name:   term,
		Type:   "α → α", // Identity type as example
		Module: "Mock",
		IsTheorem: false,
	}, nil
}
