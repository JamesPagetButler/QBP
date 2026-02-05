# QBP Interactive Proof Visualization — Makefile
#
# Targets:
#   make native    — Build with system gcc + raylib for dev testing
#   make wasm      — Build with emcc + raylib for browser deployment
#   make data      — Run export_data.py to generate JSON
#   make clean     — Remove build artifacts
#
# Prerequisites:
#   Native: cmake, gcc/clang, raylib (system install or RAYLIB_SRC)
#   WASM:   emsdk (activated), raylib source (RAYLIB_SRC)

# Optional: path to raylib source checkout
RAYLIB_SRC ?=

# Emscripten cmake toolchain (set by emsdk activation)
EMCMAKE ?= emcmake

.PHONY: native wasm data clean help

help:
	@echo "QBP Interactive Proof Visualization"
	@echo ""
	@echo "Targets:"
	@echo "  make native          Build native binary for dev testing"
	@echo "  make wasm            Build WASM for browser deployment"
	@echo "  make data            Generate data/proof_graph_01.json from Lean files"
	@echo "  make clean           Remove build/ and dist/"
	@echo ""
	@echo "Options:"
	@echo "  RAYLIB_SRC=/path     Path to raylib source (if not system-installed)"

native:
	@mkdir -p build/native
	cd build/native && cmake ../.. \
		$(if $(RAYLIB_SRC),-DRAYLIB_SRC=$(RAYLIB_SRC)) \
		-DCMAKE_BUILD_TYPE=Debug
	cd build/native && $(MAKE)
	@echo ""
	@echo "Built: build/native/qbp_proof_viz"
	@echo "Run:   ./build/native/qbp_proof_viz"

wasm:
	@mkdir -p build/wasm dist
	cd build/wasm && $(EMCMAKE) cmake ../.. \
		$(if $(RAYLIB_SRC),-DRAYLIB_SRC=$(RAYLIB_SRC)) \
		-DCMAKE_BUILD_TYPE=Release
	cd build/wasm && $(MAKE)
	@cp build/wasm/index.html build/wasm/index.js build/wasm/index.wasm dist/ 2>/dev/null || true
	@cp build/wasm/index.data dist/ 2>/dev/null || true
	@echo ""
	@echo "Built: dist/index.html"
	@echo "Serve: python3 -m http.server -d dist"

data:
	python3 export_data.py
	@echo "Generated data/proof_graph_01.json"

clean:
	rm -rf build dist
