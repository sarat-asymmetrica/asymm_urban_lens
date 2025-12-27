// Package lean - Test Helpers
// Shared helper functions for tests
package lean

// containsSubstring checks if substr is in s
func containsSubstring(s, substr string) bool {
	if len(s) == 0 || len(substr) == 0 {
		return false
	}

	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}
