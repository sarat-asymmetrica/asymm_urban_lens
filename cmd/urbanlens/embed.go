package main

import (
	"embed"
	"io/fs"
	"net/http"
	"strings"
)

//go:embed all:frontend
var frontendFS embed.FS

// getFrontendHandler returns an HTTP handler for the embedded frontend
func getFrontendHandler() http.Handler {
	// Get the frontend subdirectory
	subFS, err := fs.Sub(frontendFS, "frontend")
	if err != nil {
		panic("failed to get frontend subdirectory: " + err.Error())
	}

	fileServer := http.FileServer(http.FS(subFS))

	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		path := r.URL.Path

		// API routes should not be handled by frontend
		if strings.HasPrefix(path, "/api/") ||
			strings.HasPrefix(path, "/ws") ||
			strings.HasPrefix(path, "/health") ||
			strings.HasPrefix(path, "/tools") ||
			strings.HasPrefix(path, "/analyze") ||
			strings.HasPrefix(path, "/census") ||
			strings.HasPrefix(path, "/survey") {
			http.NotFound(w, r)
			return
		}

		// Try to serve the file
		// For SPA, serve index.html for non-file routes
		if path == "/" {
			path = "/index.html"
		}

		// Check if file exists
		f, err := subFS.Open(strings.TrimPrefix(path, "/"))
		if err != nil {
			// File doesn't exist, serve index.html for SPA routing
			r.URL.Path = "/index.html"
		} else {
			f.Close()
		}

		fileServer.ServeHTTP(w, r)
	})
}
