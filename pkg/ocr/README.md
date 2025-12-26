# OCR Package - UrbanLens Research

Fast, cost-effective OCR for urban research documents using Microsoft Florence-2 on Modal A10G.

## Features

- **Florence-2 Integration**: Microsoft's vision-language model for OCR
- **40x Faster**: 0.3s vs 10s per page compared to traditional OCR
- **60x Cheaper**: $0.15 vs $6.00 per 1000 pages
- **93%+ Accuracy**: Acceptable for research documents
- **Batch Processing**: Process multiple documents efficiently

## Quick Start

```go
package main

import (
    "context"
    "fmt"

    "github.com/asymmetrica/urbanlens/pkg/ocr"
)

func main() {
    // Create OCR processor
    ocrProcessor, err := ocr.NewDocumentOCR(nil)
    if err != nil {
        panic(err)
    }

    // Check service health
    ctx := context.Background()
    if err := ocrProcessor.HealthCheck(ctx); err != nil {
        panic(err)
    }

    // Load image (policy document, census form, etc.)
    img, err := loadImageFromFile("policy_document.png")
    if err != nil {
        panic(err)
    }

    // Extract text
    result, err := ocrProcessor.ExtractTextFromImage(ctx, img)
    if err != nil {
        panic(err)
    }

    fmt.Printf("Extracted: %s\n", result.Text)
    fmt.Printf("Confidence: %.2f\n", result.Confidence)
    fmt.Printf("Cost: $%.6f\n", result.Cost)
}
```

## Batch Processing

For multiple documents (e.g., survey pages):

```go
// Load multiple images
images := []image.Image{
    loadImage("page1.png"),
    loadImage("page2.png"),
    loadImage("page3.png"),
}

// Batch extract
results, err := ocrProcessor.BatchExtract(ctx, images)
if err != nil {
    panic(err)
}

for i, result := range results {
    fmt.Printf("Page %d: %s\n", i+1, result.Text)
}
```

## Custom Configuration

Use a custom Florence-2 endpoint (e.g., self-hosted):

```go
config := &ocr.DocumentOCRConfig{
    Florence2URL: "http://localhost:8000",
}

ocrProcessor, err := ocr.NewDocumentOCR(config)
```

## Research Use Cases

### Policy Document Analysis
```go
// Extract text from policy PDFs
policyText, _ := ocrProcessor.ExtractTextFromImageBytes(ctx, pdfPageImage)
// Analyze policy language, find patterns
```

### Census Data Extraction
```go
// Process census forms
censusData, _ := ocrProcessor.BatchExtract(ctx, censusFormImages)
// Extract demographic data for analysis
```

### Survey Processing
```go
// OCR survey responses
surveyText, _ := ocrProcessor.ExtractTextFromImage(ctx, surveyImage)
// Convert handwritten/printed responses to structured data
```

### Urban Planning Documents
```go
// Extract text from architectural plans, zoning maps
planText, _ := ocrProcessor.ExtractTextFromImageBytes(ctx, planImage)
// Analyze urban development patterns
```

## Statistics

Track OCR usage and performance:

```go
// Get detailed statistics
fmt.Println(ocrProcessor.GetStats())

// Output:
// Florence-2 OCR Summary
// ═══════════════════════════════════════════════════
// Requests:     150 total, 148 success, 2 errors
// Characters:   45,230 extracted
// Duration:     45s total, 300ms avg/request
// Throughput:   3.29 pages/sec
// Cost:         $0.0225 estimated
// Model:        florence-2-base on Modal A10G
```

## Performance Comparison

| Metric | Florence-2 (Modal A10G) | Traditional OCR |
|--------|-------------------------|-----------------|
| Speed | 0.3s/page | 10s/page |
| Cost | $0.15/1K pages | $6.00/1K pages |
| Accuracy | 93%+ | 95%+ |
| GPU Required | Yes (handled by Modal) | No |
| Best For | Research, bulk processing | Critical documents |

## Architecture

```
UrbanLens Research Document
        ↓
    DocumentOCR
        ↓
   Florence2Client
        ↓
Modal A10G GPU (FastAPI)
        ↓
   florence-2-base model
        ↓
   Extracted Text
```

## Dependencies

- Florence-2 Modal endpoint (default: https://sarat-asymmetrica--florence2-ocr-fastapi-app.modal.run)
- Standard library (image, encoding/json, net/http)
- No additional Go dependencies

## Testing

Run tests:
```bash
cd pkg/ocr
go test -v
```

Run examples:
```bash
go test -v -run Example
```

## Future Enhancements

- [ ] PDF-to-image conversion (MuPDF integration)
- [ ] Language detection and multi-language support
- [ ] Table extraction from documents
- [ ] Layout analysis for complex documents
- [ ] Confidence-based quality filtering

## Notes

- OCR service requires internet connection (calls Modal endpoint)
- For offline use, deploy Florence-2 locally (see Modal deployment docs)
- Estimated costs are based on Modal A10G pricing
- Batch processing is more efficient than individual requests
