// Package gpu - SPIR-V Kernel Loader
// Loads and manages GPU kernels for quaternion operations
package gpu

import (
	"fmt"
	"os"
	"path/filepath"
	"sync"
)

// Note: Embedded kernels disabled - using filesystem loading
// To embed kernels, move them to pkg/gpu/kernels/ and use:
// //go:embed kernels/*.spv
// var embeddedKernels embed.FS

// KernelLoader manages SPIR-V kernel loading
type KernelLoader struct {
	kernels map[string][]byte
	mu      sync.RWMutex
}

// KernelInfo describes a loaded kernel
type KernelInfo struct {
	Name        string `json:"name"`
	Size        int    `json:"size_bytes"`
	Description string `json:"description"`
	Available   bool   `json:"available"`
}

// AvailableKernels lists all known kernels
var AvailableKernels = map[string]string{
	"slerp_evolution":    "Spherical linear interpolation on S³ (50-100M ops/sec)",
	"sparse_matmul_core": "Sparse matrix multiplication for large datasets",
	"consciousness":      "Consciousness imaging kernel (tetrachromatic)",
	"dual_fovea":         "Eagle vision dual-fovea simulation",
	"tetrachromatic":     "4-channel color processing",
}

// NewKernelLoader creates a new kernel loader
func NewKernelLoader() *KernelLoader {
	return &KernelLoader{
		kernels: make(map[string][]byte),
	}
}

// LoadFromEmbedded loads kernels - currently uses filesystem
func (l *KernelLoader) LoadFromEmbedded() error {
	return l.loadFromFilesystem()
}

// loadFromFilesystem loads kernels from the kernels directory
func (l *KernelLoader) loadFromFilesystem() error {
	// Try to find kernels directory
	paths := []string{
		"kernels",
		"../kernels",
		"../../kernels",
	}

	var kernelDir string
	for _, p := range paths {
		if _, err := os.Stat(p); err == nil {
			kernelDir = p
			break
		}
	}

	if kernelDir == "" {
		return fmt.Errorf("kernels directory not found")
	}

	entries, err := os.ReadDir(kernelDir)
	if err != nil {
		return fmt.Errorf("failed to read kernels directory: %w", err)
	}

	for _, entry := range entries {
		if entry.IsDir() {
			continue
		}
		name := entry.Name()
		if filepath.Ext(name) != ".spv" {
			continue
		}

		data, err := os.ReadFile(filepath.Join(kernelDir, name))
		if err != nil {
			continue
		}

		kernelName := name[:len(name)-4]
		l.kernels[kernelName] = data
	}

	return nil
}

// LoadKernel loads a specific kernel by name
func (l *KernelLoader) LoadKernel(name string) ([]byte, error) {
	l.mu.RLock()
	if data, ok := l.kernels[name]; ok {
		l.mu.RUnlock()
		return data, nil
	}
	l.mu.RUnlock()

	// Try to load from filesystem
	paths := []string{
		fmt.Sprintf("kernels/%s.spv", name),
		fmt.Sprintf("../kernels/%s.spv", name),
		fmt.Sprintf("../../kernels/%s.spv", name),
	}

	for _, p := range paths {
		data, err := os.ReadFile(p)
		if err == nil {
			l.mu.Lock()
			l.kernels[name] = data
			l.mu.Unlock()
			return data, nil
		}
	}

	return nil, fmt.Errorf("kernel not found: %s", name)
}

// GetKernel returns a loaded kernel
func (l *KernelLoader) GetKernel(name string) ([]byte, bool) {
	l.mu.RLock()
	defer l.mu.RUnlock()
	data, ok := l.kernels[name]
	return data, ok
}

// ListKernels returns info about all loaded kernels
func (l *KernelLoader) ListKernels() []KernelInfo {
	l.mu.RLock()
	defer l.mu.RUnlock()

	var infos []KernelInfo
	for name, desc := range AvailableKernels {
		data, loaded := l.kernels[name]
		size := 0
		if loaded {
			size = len(data)
		}
		infos = append(infos, KernelInfo{
			Name:        name,
			Size:        size,
			Description: desc,
			Available:   loaded,
		})
	}
	return infos
}

// GetStatus returns kernel loader status
func (l *KernelLoader) GetStatus() map[string]interface{} {
	kernels := l.ListKernels()
	loaded := 0
	for _, k := range kernels {
		if k.Available {
			loaded++
		}
	}

	return map[string]interface{}{
		"kernels_loaded": loaded,
		"kernels_total":  len(AvailableKernels),
		"kernels":        kernels,
	}
}

// Global kernel loader instance
var globalKernelLoader *KernelLoader
var kernelLoaderOnce sync.Once

// GetKernelLoader returns the global kernel loader
func GetKernelLoader() *KernelLoader {
	kernelLoaderOnce.Do(func() {
		globalKernelLoader = NewKernelLoader()
		globalKernelLoader.loadFromFilesystem()
	})
	return globalKernelLoader
}
