package verification

import (
	"bytes"
	"context"
	"fmt"
	"os/exec"
	"time"
)

// TestRunner executes test commands
type TestRunner struct {
	timeout  time.Duration
	verbose  bool
	parallel int
}

// NewTestRunner creates a new test runner
func NewTestRunner(timeout time.Duration, verbose bool, parallel int) *TestRunner {
	return &TestRunner{
		timeout:  timeout,
		verbose:  verbose,
		parallel: parallel,
	}
}

// RunTests executes test suite for the given language
func (tr *TestRunner) RunTests(
	ctx context.Context,
	projectPath string,
	language string,
	options TestOptions,
) (*TestOutput, error) {
	// Create context with timeout
	ctx, cancel := context.WithTimeout(ctx, tr.timeout)
	defer cancel()

	// Build command based on language
	cmd, err := tr.buildTestCommand(projectPath, language, options)
	if err != nil {
		return nil, err
	}

	// Capture output
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr

	// Run command
	startTime := time.Now()
	err = cmd.Run()
	duration := time.Since(startTime)

	// Build output
	output := &TestOutput{
		ExitCode: 0,
		Stdout:   stdout.String(),
		Stderr:   stderr.String(),
		Duration: duration,
		Success:  err == nil,
	}

	if err != nil {
		if exitErr, ok := err.(*exec.ExitError); ok {
			output.ExitCode = exitErr.ExitCode()
		} else {
			output.ExitCode = -1
		}
		// Non-zero exit doesn't mean error - tests might have failed
		// We parse output to determine actual test results
	}

	return output, nil
}

// buildTestCommand creates the appropriate test command for the language
func (tr *TestRunner) buildTestCommand(projectPath, language string, options TestOptions) (*exec.Cmd, error) {
	var cmd *exec.Cmd

	switch language {
	case "go":
		args := []string{"test", "./..."}
		if options.Verbose {
			args = append(args, "-v")
		}
		if options.Coverage {
			args = append(args, "-cover")
		}
		if options.Parallel > 0 {
			args = append(args, fmt.Sprintf("-parallel=%d", options.Parallel))
		}
		if options.FailFast {
			args = append(args, "-failfast")
		}
		if options.TestPattern != "" {
			args = append(args, "-run", options.TestPattern)
		}
		cmd = exec.Command("go", args...)
		cmd.Dir = projectPath

	case "rust":
		args := []string{"test"}
		if options.Verbose {
			args = append(args, "--verbose")
		}
		if options.TestPattern != "" {
			args = append(args, options.TestPattern)
		}
		cmd = exec.Command("cargo", args...)
		cmd.Dir = projectPath

	case "typescript", "javascript":
		args := []string{"test"}
		if options.Verbose {
			args = append(args, "--verbose")
		}
		if options.Coverage {
			args = append(args, "--coverage")
		}
		if options.TestPattern != "" {
			args = append(args, "--testNamePattern", options.TestPattern)
		}
		cmd = exec.Command("npm", args...)
		cmd.Dir = projectPath

	case "python":
		args := []string{}
		if options.Verbose {
			args = append(args, "--verbose")
		}
		if options.Coverage {
			args = append(args, "--cov")
		}
		if options.FailFast {
			args = append(args, "-x")
		}
		if options.TestPattern != "" {
			args = append(args, "-k", options.TestPattern)
		}
		cmd = exec.Command("pytest", args...)
		cmd.Dir = projectPath

	default:
		return nil, fmt.Errorf("unsupported language: %s", language)
	}

	return cmd, nil
}

// TestOptions controls test execution
type TestOptions struct {
	Verbose     bool
	Coverage    bool
	Parallel    int
	FailFast    bool
	TestPattern string
}

// TestOutput captures test execution
type TestOutput struct {
	ExitCode int
	Stdout   string
	Stderr   string
	Duration time.Duration
	Success  bool
}
