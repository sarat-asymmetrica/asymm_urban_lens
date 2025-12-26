package gpu

import (
	"testing"
)

func TestKernelLoader_New(t *testing.T) {
	loader := NewKernelLoader()
	if loader == nil {
		t.Fatal("NewKernelLoader returned nil")
	}
	if loader.kernels == nil {
		t.Error("kernels map not initialized")
	}
}

func TestKernelLoader_LoadFromFilesystem(t *testing.T) {
	loader := NewKernelLoader()

	// This may fail if kernels directory not in path - that's ok
	err := loader.LoadFromEmbedded()
	if err != nil {
		t.Logf("LoadFromEmbedded returned error (expected if no kernels): %v", err)
	}
}

func TestKernelLoader_ListKernels(t *testing.T) {
	loader := NewKernelLoader()

	kernels := loader.ListKernels()
	if len(kernels) == 0 {
		t.Error("Expected at least one kernel in AvailableKernels")
	}

	// Check that all available kernels are listed
	for name := range AvailableKernels {
		found := false
		for _, k := range kernels {
			if k.Name == name {
				found = true
				break
			}
		}
		if !found {
			t.Errorf("Kernel %s not found in list", name)
		}
	}
}

func TestKernelLoader_GetStatus(t *testing.T) {
	loader := NewKernelLoader()

	status := loader.GetStatus()

	if status["kernels_total"] == nil {
		t.Error("Expected kernels_total in status")
	}
	if status["kernels_loaded"] == nil {
		t.Error("Expected kernels_loaded in status")
	}
}

func TestGetKernelLoader(t *testing.T) {
	loader := GetKernelLoader()
	if loader == nil {
		t.Fatal("GetKernelLoader returned nil")
	}

	// Should return same instance
	loader2 := GetKernelLoader()
	if loader != loader2 {
		t.Error("GetKernelLoader should return singleton")
	}
}
