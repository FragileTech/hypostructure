.PHONY: help build test lint mathlib-cache framework-build fixtures-build \
	erdos-build pde-build stokes-build template-build erdos-json erdos \
	ab stokes-json stokes web-data web-build web-test web-backend-test \
	web-frontend-test web

.DEFAULT_GOAL := build

PYTHON ?= python3
UV ?= uv
NPM ?= npm
UV_CACHE_DIR ?= /tmp/uv-cache

HYPOSTRUCTURE_DIR := hypostructure
ERDOS_DIR := examples/hypostructure_erdos_64_eg
ERDOS_TARGET := HypostructureErdos64EG.Official.StructuralProgram
AB_TARGET := HypostructureErdos64EG.AB.Execution
PDE_DIR := examples/hypostructure_pde
STOKES_DIR := examples/stokes
STOKES_TARGET := Stokes.Execution
TEMPLATE_DIR := examples/template
WEB_FRONTEND_DIR := web/frontend
WEB_NODE_STAMP := $(WEB_FRONTEND_DIR)/node_modules/.package-lock.json
WEB_RAW := generated/hypostructure/web/declarations.raw.json
WEB_SNAPSHOT := generated/hypostructure/web/snapshot.json
WEB_MANIFEST := generated/hypostructure/web/manifest.json
ERDOS_RUN := build/hypostructure/eg-official-run.json
AB_RUN := build/hypostructure/eg-ab-run.json
STOKES_RUN := build/hypostructure/stokes-run.json
WEB_HOST ?= 127.0.0.1
WEB_PORT ?= 8000
WEB_WORKERS ?= 1
WEB_THREADS ?= 4
WEB_TIMEOUT ?= 60

help:
	@printf '%s\n' \
	  'Hypostructure' \
	  '' \
	  '  make build          Build the framework and maintained examples' \
	  '  make test           Run the Hypostructure and web checks' \
	  '  make framework-build Build the reusable Hypostructure package' \
	  '  make fixtures-build Build Core, Graph, and PDE fixtures' \
	  '  make erdos-build    Build the graph/EG application' \
	  '  make pde-build      Build the PDE applications' \
	  '  make stokes-build   Build the linear Stokes application' \
	  '  make template-build Build the application template' \
	  '  make erdos-json     Export and validate the official EG proof run' \
	  '  make erdos          Compile and execute the sealed official EG proof' \
	  '  make ab             Run the framework on the Type-A/Type-B target' \
	  '  make stokes         Execute the sealed Stokes reduction and closure probe' \
	  '  make web-data       Regenerate Flask/React documentation data' \
	  '  make web-test       Test the Flask API and React application' \
	  '  make web            Build and serve the documentation site'

framework-build:
	cd $(HYPOSTRUCTURE_DIR) && lake build

fixtures-build: framework-build
	cd $(HYPOSTRUCTURE_DIR) && lake build Hypostructure.Fixtures

erdos-build: framework-build
	cd $(ERDOS_DIR) && lake build $(ERDOS_TARGET)

pde-build: framework-build
	cd $(PDE_DIR) && lake build

stokes-build:
	mkdir -p build/hypostructure
	cd $(STOKES_DIR) && lake build $(STOKES_TARGET)

template-build: framework-build
	cd $(TEMPLATE_DIR) && lake build

build: framework-build erdos-build pde-build stokes-build template-build

mathlib-cache:
	cd $(HYPOSTRUCTURE_DIR) && lake exe cache get
	cd $(ERDOS_DIR) && lake exe cache get
	cd $(PDE_DIR) && lake exe cache get
	cd $(STOKES_DIR) && lake exe cache get
	cd $(TEMPLATE_DIR) && lake exe cache get

lint:
	$(PYTHON) tools/check_hypostructure_imports.py --root .

erdos-json: framework-build
	mkdir -p build/hypostructure
	cd $(ERDOS_DIR) && lake build $(ERDOS_TARGET)
	@test -s $(ERDOS_RUN)
	$(PYTHON) tools/validate_hypostructure_run.py $(ERDOS_RUN)

erdos: erdos-json
	@cd $(ERDOS_DIR) && \
	  if lake env lean HypostructureErdos64EG/Official/ClosureProbe.lean \
	      > ../../build/hypostructure/eg-closure-audit.log 2>&1; then \
	    echo "EG closure audit: the strict ofDag% declaration closes."; \
	  elif grep -q "sealed compiler could not derive total execution closure" \
	      ../../build/hypostructure/eg-closure-audit.log; then \
	    echo "EG closure audit: certified reduction retains an exact residual."; \
	  else \
	    cat ../../build/hypostructure/eg-closure-audit.log; \
	    exit 1; \
	  fi

ab: framework-build
	mkdir -p build/hypostructure
	cd $(ERDOS_DIR) && lake build $(AB_TARGET)
	@test -s $(AB_RUN)
	$(PYTHON) tools/validate_hypostructure_run.py $(AB_RUN)

stokes-json: stokes-build
	@test -s $(STOKES_RUN)
	@$(PYTHON) -m json.tool $(STOKES_RUN) >/dev/null

stokes: stokes-json
	@cd $(STOKES_DIR) && \
	  if lake env lean Stokes/ClosureProbe.lean \
	      > ../../build/hypostructure/stokes-closure-audit.log 2>&1; then \
	    cat ../../build/hypostructure/stokes-closure-audit.log; \
	  elif grep -q "sealed compiler could not derive total execution closure" \
	      ../../build/hypostructure/stokes-closure-audit.log; then \
	    cat ../../build/hypostructure/stokes-closure-audit.log; \
	  else \
	    cat ../../build/hypostructure/stokes-closure-audit.log; \
	    exit 1; \
	  fi

web-data: framework-build erdos-json
	cd $(HYPOSTRUCTURE_DIR) && HYPOSTRUCTURE_WEB_DECLARATIONS_EXPORT=../$(WEB_RAW) lake env lean Hypostructure/Canonical/WebExport.lean
	$(PYTHON) tools/build_hypostructure_web_data.py --skip-declaration-export
	@test -s $(WEB_SNAPSHOT)
	@test -s $(WEB_MANIFEST)

$(WEB_NODE_STAMP): $(WEB_FRONTEND_DIR)/package.json $(WEB_FRONTEND_DIR)/package-lock.json
	cd $(WEB_FRONTEND_DIR) && $(NPM) ci

web-build: web-data $(WEB_NODE_STAMP)
	cd $(WEB_FRONTEND_DIR) && $(NPM) run build

web-backend-test: web-data
	UV_CACHE_DIR=$(UV_CACHE_DIR) $(UV) run python -m pytest -q \
	  tests/test_web_api.py tests/test_hypostructure_web_data.py

web-frontend-test: $(WEB_NODE_STAMP)
	cd $(WEB_FRONTEND_DIR) && $(NPM) run test
	cd $(WEB_FRONTEND_DIR) && $(NPM) run typecheck
	cd $(WEB_FRONTEND_DIR) && $(NPM) run build

web-test: web-backend-test web-frontend-test

test:
	UV_CACHE_DIR=$(UV_CACHE_DIR) $(UV) run python -m pytest -q \
	  tests/test_hypostructure_run_json.py \
	  tests/test_hypostructure_web_data.py \
	  tests/test_web_api.py
	$(MAKE) web-frontend-test

web: web-build
	UV_CACHE_DIR=$(UV_CACHE_DIR) $(UV) run gunicorn --preload \
	  --worker-class gthread --workers $(WEB_WORKERS) --threads $(WEB_THREADS) \
	  --timeout $(WEB_TIMEOUT) --bind $(WEB_HOST):$(WEB_PORT) \
	  'web.backend.app.main:create_app()'
