#!/bin/bash
# ASYA Server Quick Start Script

set -e

echo "╔═══════════════════════════════════════════════════════════════╗"
echo "║                                                               ║"
echo "║                     ASYA - आस्या                              ║"
echo "║              The Conversation Engine                          ║"
echo "║                                                               ║"
echo "╚═══════════════════════════════════════════════════════════════╝"
echo ""

# Check if .env exists
if [ ! -f ".env" ]; then
    echo "⚠️  No .env file found. Creating from template..."
    cp ../../.env.example .env
    echo "✓ Created .env file"
    echo ""
    echo "Please edit .env and set your AIMLAPI_KEY, then run this script again."
    exit 1
fi

# Load environment
export $(cat .env | grep -v '^#' | xargs)

# Check if AIMLAPI_KEY is set
if [ -z "$AIMLAPI_KEY" ] || [ "$AIMLAPI_KEY" = "your_aimlapi_key_here" ]; then
    echo "⚠️  AIMLAPI_KEY not configured in .env"
    echo ""
    echo "The server will run but AI responses will be disabled."
    echo "Set AIMLAPI_KEY in .env to enable AI-powered conversations."
    echo ""
    read -p "Continue anyway? (y/n) " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        exit 1
    fi
fi

# Build
echo "🔨 Building ASYA..."
go build -o asya main.go
echo "✓ Build successful"
echo ""

# Run
echo "🚀 Starting ASYA server..."
echo ""
./asya
