// Package verification implements compilation verification and regression detection
//
// Build Runner: Execute compiler commands and capture output
// Author: Agent 4.1 (Dr. Liam O'Connor - Formal Verification, Oxford)
// Created: 2025-11-07
// Ported: 2025-12-26 (Urban Lens Integration)
package verification

import (
	"context"
	"fmt"
	"os/exec"
	"strings"
	"time"
)

// BuildRunner executes compiler commands
type BuildRunner struct {
	timeout time.Duration
}

// NewBuildRunner creates a build runner with specified timeout
func NewBuildRunner(timeout time.Duration) *BuildRunner {
	if timeout == 0 {
		timeout = 5 * time.Minute // Default 5 minute timeout
	}
	return &BuildRunner{
		timeout: timeout,
	}
}

// RunBuild executes build command and captures output
func (br *BuildRunner) RunBuild(
	ctx context.Context,
	projectPath string,
	language string,
) (*BuildOutput, error) {
	startTime := time.Now()

	// Create context with timeout
	buildCtx, cancel := context.WithTimeout(ctx, br.timeout)
	defer cancel()

	// Determine build command based on language
	var cmd *exec.Cmd
	switch strings.ToLower(language) {
	case "go", "golang":
		cmd = exec.CommandContext(buildCtx, "go", "build", "./...")
	case "rust":
		cmd = exec.CommandContext(buildCtx, "cargo", "check")
	case "typescript", "ts":
		cmd = exec.CommandContext(buildCtx, "tsc", "--noEmit")
	case "python", "py":
		// Python syntax check
		cmd = exec.CommandContext(buildCtx, "python", "-m", "py_compile")
	default:
		return nil, fmt.Errorf("unsupported language: %s", language)
	}

	// Set working directory
	cmd.Dir = projectPath

	// Capture combined output (stdout + stderr)
	output, err := cmd.CombinedOutput()

	duration := time.Since(startTime)

	// Determine success (exit code 0)
	exitCode := 0
	success := err == nil

	if err != nil {
		// Extract exit code if available
		if exitErr, ok := err.(*exec.ExitError); ok {
			exitCode = exitErr.ExitCode()
		} else {
			// Timeout or other error
			return nil, fmt.Errorf("build execution failed: %w", err)
		}
	}

	return &BuildOutput{
		ExitCode: exitCode,
		Stdout:   string(output), // Go build sends to stderr, but we capture combined
		Stderr:   string(output), // Both point to same for now
		Duration: duration,
		Success:  success,
	}, nil
}

// RunBuildWithRetry runs build with retries on transient failures
func (br *BuildRunner) RunBuildWithRetry(
	ctx context.Context,
	projectPath string,
	language string,
	maxRetries int,
) (*BuildOutput, error) {
	var lastErr error
	var output *BuildOutput

	for i := 0; i <= maxRetries; i++ {
		output, lastErr = br.RunBuild(ctx, projectPath, language)
		if lastErr == nil {
			return output, nil
		}

		// Check if error is retryable (not timeout)
		if ctx.Err() != nil {
			// Context cancelled/timed out - don't retry
			break
		}

		// Wait before retry (exponential backoff)
		if i < maxRetries {
			waitTime := time.Duration(1<<uint(i)) * time.Second
			select {
			case <-ctx.Done():
				return nil, ctx.Err()
			case <-time.After(waitTime):
				// Continue to next retry
			}
		}
	}

	return output, fmt.Errorf("build failed after %d retries: %w", maxRetries, lastErr)
}
