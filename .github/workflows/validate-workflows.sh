#!/bin/bash
# Workflow Validation Script
# Validates GitHub Actions workflow YAML files
# Generated: 2025-12-27

set -e

echo "🔍 Validating GitHub Actions Workflows..."
echo ""

WORKFLOWS_DIR=".github/workflows"
VALID_COUNT=0
INVALID_COUNT=0

# Function to validate YAML syntax
validate_yaml() {
    local file=$1
    local filename=$(basename "$file")

    echo "Checking: $filename"

    # Check if file exists
    if [ ! -f "$file" ]; then
        echo "  ❌ File not found: $file"
        ((INVALID_COUNT++))
        return 1
    fi

    # Check if file is not empty
    if [ ! -s "$file" ]; then
        echo "  ❌ File is empty: $file"
        ((INVALID_COUNT++))
        return 1
    fi

    # Basic YAML validation (check for required fields)
    if ! grep -q "^name:" "$file"; then
        echo "  ❌ Missing 'name:' field"
        ((INVALID_COUNT++))
        return 1
    fi

    if ! grep -q "^on:" "$file"; then
        echo "  ❌ Missing 'on:' trigger field"
        ((INVALID_COUNT++))
        return 1
    fi

    if ! grep -q "^jobs:" "$file"; then
        echo "  ❌ Missing 'jobs:' field"
        ((INVALID_COUNT++))
        return 1
    fi

    # Check for proper indentation (YAML requirement)
    if grep -q $'^\t' "$file"; then
        echo "  ⚠️ Warning: File contains tabs (use spaces for YAML)"
    fi

    # Check for common YAML errors
    if grep -q ': $' "$file"; then
        echo "  ⚠️ Warning: Potential trailing colon without value"
    fi

    echo "  ✅ Valid"
    ((VALID_COUNT++))
    return 0
}

# Find all workflow files
WORKFLOW_FILES=$(find "$WORKFLOWS_DIR" -name "*.yml" -o -name "*.yaml" 2>/dev/null || echo "")

if [ -z "$WORKFLOW_FILES" ]; then
    echo "❌ No workflow files found in $WORKFLOWS_DIR"
    exit 1
fi

echo "Found workflow files:"
echo "$WORKFLOW_FILES"
echo ""

# Validate each workflow file
for file in $WORKFLOW_FILES; do
    validate_yaml "$file"
    echo ""
done

# Summary
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "VALIDATION SUMMARY"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "✅ Valid workflows:   $VALID_COUNT"
echo "❌ Invalid workflows: $INVALID_COUNT"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

if [ $INVALID_COUNT -gt 0 ]; then
    echo ""
    echo "❌ Some workflows have errors. Please fix them before pushing."
    exit 1
fi

echo ""
echo "✅ All workflows validated successfully!"
echo ""
echo "Next steps:"
echo "1. Commit workflow files"
echo "2. Push to GitHub"
echo "3. Check Actions tab for first run"
echo ""
echo "To test locally:"
echo "  go test ./... -v"
echo "  go test ./... -coverprofile=coverage.out"
echo ""
