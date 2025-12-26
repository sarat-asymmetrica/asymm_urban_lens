// Package office provides HTTP bridge to Asymmetrica.Runtime
// Enables Urban Lens to process Office documents via the .NET runtime
package office

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"time"
)

// Bridge connects to Asymmetrica.Runtime for Office document processing
type Bridge struct {
	baseURL    string
	httpClient *http.Client
	available  bool
}

// NewBridge creates a new Office bridge
func NewBridge() *Bridge {
	b := &Bridge{
		baseURL: "http://localhost:5000",
		httpClient: &http.Client{
			Timeout: 120 * time.Second,
		},
	}
	b.available = b.checkHealth()
	return b
}

// NewBridgeWithURL creates a bridge with custom URL
func NewBridgeWithURL(baseURL string) *Bridge {
	b := &Bridge{
		baseURL: baseURL,
		httpClient: &http.Client{
			Timeout: 120 * time.Second,
		},
	}
	b.available = b.checkHealth()
	return b
}

// IsAvailable returns true if Asymmetrica.Runtime is reachable
func (b *Bridge) IsAvailable() bool {
	return b.available
}

// checkHealth checks if the runtime is available
func (b *Bridge) checkHealth() bool {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	req, err := http.NewRequestWithContext(ctx, "GET", b.baseURL+"/health", nil)
	if err != nil {
		return false
	}

	resp, err := b.httpClient.Do(req)
	if err != nil {
		return false
	}
	defer resp.Body.Close()

	return resp.StatusCode == http.StatusOK
}

// Refresh re-checks runtime availability
func (b *Bridge) Refresh() {
	b.available = b.checkHealth()
}

// KernelRequest represents a kernel execution request
type KernelRequest struct {
	Kernel string                 `json:"kernel"`
	Args   map[string]interface{} `json:"args"`
}

// KernelResponse represents a kernel execution response
type KernelResponse struct {
	Success bool                   `json:"success"`
	Result  map[string]interface{} `json:"result,omitempty"`
	Error   string                 `json:"error,omitempty"`
}

// RunKernel executes a kernel on Asymmetrica.Runtime
func (b *Bridge) RunKernel(ctx context.Context, kernel string, args map[string]interface{}) (*KernelResponse, error) {
	if !b.available {
		return nil, fmt.Errorf("Asymmetrica.Runtime not available at %s", b.baseURL)
	}

	reqBody := KernelRequest{
		Kernel: kernel,
		Args:   args,
	}

	jsonBody, err := json.Marshal(reqBody)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal request: %w", err)
	}

	req, err := http.NewRequestWithContext(ctx, "POST", b.baseURL+"/kernel/run", bytes.NewReader(jsonBody))
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}
	req.Header.Set("Content-Type", "application/json")

	resp, err := b.httpClient.Do(req)
	if err != nil {
		return nil, fmt.Errorf("request failed: %w", err)
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	var result KernelResponse
	if err := json.Unmarshal(body, &result); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	return &result, nil
}

// ProcessExcel processes an Excel file using Hermes kernel
func (b *Bridge) ProcessExcel(ctx context.Context, filePath string, config map[string]interface{}) (*KernelResponse, error) {
	args := map[string]interface{}{
		"inputFilePath": filePath,
		"config":        config,
	}
	return b.RunKernel(ctx, "Hermes", args)
}

// ProcessWord processes a Word document
func (b *Bridge) ProcessWord(ctx context.Context, filePath string) (*KernelResponse, error) {
	args := map[string]interface{}{
		"inputFilePath": filePath,
	}
	return b.RunKernel(ctx, "WordProcessor", args)
}

// ProcessPowerPoint processes a PowerPoint presentation
func (b *Bridge) ProcessPowerPoint(ctx context.Context, filePath string) (*KernelResponse, error) {
	args := map[string]interface{}{
		"inputFilePath": filePath,
	}
	return b.RunKernel(ctx, "PowerPointProcessor", args)
}

// ListKernels returns available kernels from the runtime
func (b *Bridge) ListKernels(ctx context.Context) ([]string, error) {
	if !b.available {
		return nil, fmt.Errorf("Asymmetrica.Runtime not available")
	}

	req, err := http.NewRequestWithContext(ctx, "GET", b.baseURL+"/kernels", nil)
	if err != nil {
		return nil, err
	}

	resp, err := b.httpClient.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var result struct {
		Kernels []string `json:"kernels"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, err
	}

	return result.Kernels, nil
}

// QueryGraph queries the knowledge graph
func (b *Bridge) QueryGraph(ctx context.Context, tag string) ([]map[string]interface{}, error) {
	if !b.available {
		return nil, fmt.Errorf("Asymmetrica.Runtime not available")
	}

	url := fmt.Sprintf("%s/graph/nodes?tag=%s", b.baseURL, tag)
	req, err := http.NewRequestWithContext(ctx, "GET", url, nil)
	if err != nil {
		return nil, err
	}

	resp, err := b.httpClient.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var nodes []map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&nodes); err != nil {
		return nil, err
	}

	return nodes, nil
}

// GetStatus returns bridge status for API
func (b *Bridge) GetStatus() map[string]interface{} {
	kernels := []string{}
	if b.available {
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()
		if k, err := b.ListKernels(ctx); err == nil {
			kernels = k
		}
	}

	return map[string]interface{}{
		"available":    b.available,
		"endpoint":     b.baseURL,
		"kernels":      kernels,
		"install_help": "Start Asymmetrica.Runtime: cd C:\\Projects\\ACE_Engine\\Asymmetrica.Runtime && .\\start.ps1",
	}
}
