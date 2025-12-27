#!/bin/bash
# Pre-commit hook for Asymmetrica UrbanLens
# Runs quick quality checks before allowing commit
#
# Installation:
#   chmod +x scripts/pre-commit.sh
#   ln -s ../../scripts/pre-commit.sh .git/hooks/pre-commit
#
# Or with Git:
#   git config core.hooksPath scripts/
#
# Author: CI/CD Agent 2
# Date: 2025-12-27

set -e

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "🔍 ASYMMETRICA PRE-COMMIT QUALITY CHECK"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Counters
CHECKS_PASSED=0
CHECKS_FAILED=0
WARNINGS=0

# Function to print check result
print_check() {
    if [ $1 -eq 0 ]; then
        echo -e "${GREEN}✅${NC} $2"
        CHECKS_PASSED=$((CHECKS_PASSED + 1))
    else
        echo -e "${RED}❌${NC} $2"
        CHECKS_FAILED=$((CHECKS_FAILED + 1))
    fi
}

print_warning() {
    echo -e "${YELLOW}⚠️${NC} $1"
    WARNINGS=$((WARNINGS + 1))
}

# 1. Check for Go syntax errors
echo "1️⃣  Checking Go syntax..."
if go fmt ./... > /dev/null 2>&1; then
    print_check 0 "Go formatting OK"
else
    print_check 1 "Go formatting failed - run 'go fmt ./...'"
fi

# 2. Run stabilization tests (must pass 100%)
echo ""
echo "2️⃣  Running STABILIZATION tests (100% pass required)..."
if go test -run "Test.*Exhaustive" ./pkg/intelligence/ -timeout 30s > /tmp/precommit_test.log 2>&1; then
    print_check 0 "Stabilization tests passed (100%)"
else
    print_check 1 "Stabilization tests failed - see /tmp/precommit_test.log"
    echo "   Fix failing tests before committing"
fi

# 3. Check for common issues
echo ""
echo "3️⃣  Checking for common issues..."

# Check for TODO without issue reference
if git diff --cached --name-only | xargs grep -n "TODO" 2>/dev/null | grep -v "TODO(#[0-9])" > /dev/null; then
    print_warning "Found TODO without issue reference - consider adding issue number"
else
    print_check 0 "No orphaned TODOs"
fi

# Check for console.log in frontend (if exists)
if git diff --cached --name-only | grep -E "\.(js|ts|jsx|tsx)$" | xargs grep -n "console\.log" 2>/dev/null; then
    print_warning "Found console.log in code - remove before production"
else
    print_check 0 "No console.log found"
fi

# Check for debugger statements
if git diff --cached --name-only | xargs grep -n "debugger" 2>/dev/null; then
    print_check 1 "Found debugger statements - remove before committing"
else
    print_check 0 "No debugger statements"
fi

# Check for hardcoded credentials
CRED_PATTERNS="(password|secret|api_key|apikey|token|bearer).*=.*['\"]"
if git diff --cached | grep -iE "$CRED_PATTERNS" > /dev/null; then
    print_check 1 "Possible hardcoded credentials detected - use environment variables"
else
    print_check 0 "No hardcoded credentials detected"
fi

# 4. Run quick linting
echo ""
echo "4️⃣  Running quick linting..."
if command -v golangci-lint &> /dev/null; then
    if golangci-lint run --fast --timeout 30s > /dev/null 2>&1; then
        print_check 0 "Linting passed"
    else
        print_warning "Linting found issues - consider fixing before commit"
    fi
else
    print_warning "golangci-lint not installed - skipping"
fi

# 5. Check test coverage on changed files
echo ""
echo "5️⃣  Checking test coverage on changed files..."
CHANGED_FILES=$(git diff --cached --name-only --diff-filter=ACMR | grep "\.go$" | grep -v "_test\.go$" || true)

if [ -n "$CHANGED_FILES" ]; then
    # Get packages for changed files
    CHANGED_PACKAGES=$(echo "$CHANGED_FILES" | xargs -I {} dirname {} | sort -u | xargs -I {} echo "./{}")

    # Run coverage check
    if [ -n "$CHANGED_PACKAGES" ]; then
        go test -cover $CHANGED_PACKAGES > /tmp/coverage.txt 2>&1 || true

        # Check if coverage is reasonable (>70%)
        COVERAGE=$(grep "coverage:" /tmp/coverage.txt | awk '{print $5}' | sed 's/%//' | head -1)
        if [ -n "$COVERAGE" ]; then
            if (( $(echo "$COVERAGE >= 70.0" | bc -l) )); then
                print_check 0 "Test coverage OK (${COVERAGE}%)"
            else
                print_warning "Test coverage low (${COVERAGE}%) - aim for 70%+"
            fi
        else
            print_warning "Could not determine test coverage"
        fi
    fi
else
    echo "   No Go files changed - skipping coverage check"
fi

# 6. Verify commit message quality
echo ""
echo "6️⃣  Checking commit message..."
COMMIT_MSG_FILE="$1"
if [ -n "$COMMIT_MSG_FILE" ] && [ -f "$COMMIT_MSG_FILE" ]; then
    COMMIT_MSG=$(cat "$COMMIT_MSG_FILE")
    COMMIT_FIRST_LINE=$(echo "$COMMIT_MSG" | head -1)

    # Check length (conventional commits recommend 50 chars)
    if [ ${#COMMIT_FIRST_LINE} -gt 72 ]; then
        print_warning "Commit message first line is long (${#COMMIT_FIRST_LINE} chars) - consider shortening"
    else
        print_check 0 "Commit message length OK"
    fi

    # Check for conventional commit format
    if echo "$COMMIT_FIRST_LINE" | grep -qE "^(feat|fix|docs|style|refactor|test|chore|perf)(\(.+\))?:"; then
        print_check 0 "Conventional commit format"
    else
        print_warning "Consider using conventional commit format (feat:, fix:, etc.)"
    fi
else
    echo "   Commit message check skipped (not available in pre-commit)"
fi

# Summary
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 SUMMARY"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo -e "✅ Passed:   ${GREEN}${CHECKS_PASSED}${NC}"
echo -e "❌ Failed:   ${RED}${CHECKS_FAILED}${NC}"
echo -e "⚠️  Warnings: ${YELLOW}${WARNINGS}${NC}"
echo ""

if [ $CHECKS_FAILED -eq 0 ]; then
    echo -e "${GREEN}✨ All critical checks passed! Proceeding with commit...${NC}"
    echo ""
    exit 0
else
    echo -e "${RED}🚫 Critical checks failed! Fix issues before committing.${NC}"
    echo ""
    echo "To skip this check (NOT recommended):"
    echo "  git commit --no-verify"
    echo ""
    exit 1
fi
