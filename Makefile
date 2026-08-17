.PHONY: help build test lint mathlib-cache framework-build erdos-build erdos typeii-paper-check \
        web web-install web-data web-build web-test

.DEFAULT_GOAL := help

PYTHON ?= python3

HYPOSTRUCTURE_DIR := hypostructure
ERDOS_DIR := proofs/hypostructure_erdos_64_eg
ERDOS_TARGET := HypostructureErdos64EG

NPM ?= npm
WEB_DIR := web
WEB_FRONTEND := $(WEB_DIR)/frontend
WEB_DATA := $(WEB_FRONTEND)/public/data/erdos-gyarfas.json \
            $(WEB_FRONTEND)/public/data/pages/original_erdos_64_proof.json
WEB_SOURCES := to_formalize/original_erdos_64_proof.tex \
               to_formalize/proof_setup.tex \
               to_formalize/type_I_residual_closure.tex \
               to_formalize/type_II_regularity.tex \
               to_formalize/original_erdos_64_proof.aux \
               to_formalize/proof_setup.aux \
               to_formalize/type_I_residual_closure.aux \
               to_formalize/type_II_regularity.aux
WEB_TOOLS := $(wildcard $(WEB_DIR)/tools/*.py) $(wildcard $(WEB_DIR)/tools/papers/*.py)

# The sealed-frontend run/export targets (`ab`, `ab-json`, `erdos-json`) drove
# `reduceDag%` and `ofDag%` over the authored Blueprint
# topology.  That topology is retired for the EG package root: it imports the
# problem presentation plus the framework-owned `Graph.Strategy.Spine`
# exact-ledger continuation surface directly.  Those export targets return only
# if the sealed frontend is restored as a checked framework component.

help:
	@printf '%s\n' \
	  'Hypostructure' \
	  '' \
	  '  make framework-build Build the reusable Hypostructure package' \
	  '  make erdos-build     Build the Erdős 64 problem presentation' \
	  '  make erdos           Check the end-to-end Erdős 64 theorem' \
	  '  make build           Build the framework and the EG application' \
	  '  make lint            Run the total-execution and canonical-ledger gates' \
	  '  make typeii-paper-check  Audit the consolidated Type II manuscript' \
	  '  make test            Build everything and run the gates' \
	  '  make mathlib-cache   Fetch prebuilt Mathlib artifacts' \
	  '' \
	  '  make web             Serve the interactive proof explorer' \
	  '  make web-data        Re-extract both proof diagrams and page maps from the manuscripts' \
	  '  make web-build       Produce the static site in web/frontend/dist' \
	  '  make web-test        Typecheck and test the explorer'

framework-build:
	cd $(HYPOSTRUCTURE_DIR) && lake build

erdos-build: framework-build
	cd $(ERDOS_DIR) && lake build $(ERDOS_TARGET)

erdos: erdos-build
	@tmp=$$(mktemp /tmp/hypostructure-erdos-final-XXXXXX.lean); \
	trap 'rm -f "$$tmp"' EXIT; \
	printf '%s\n' \
	  'import HypostructureErdos64EG' \
	  '' \
	  '#check HypostructureErdos64EG.erdos_64' \
	  'example : HypostructureErdos64EG.OfficialStatement :=' \
	  '  HypostructureErdos64EG.erdos_64' \
	  '#print axioms HypostructureErdos64EG.erdos_64' > "$$tmp"; \
	output=$$(cd $(ERDOS_DIR) && lake env lean "$$tmp" 2>&1); \
	status=$$?; \
	printf '%s\n' "$$output"; \
	if [ $$status -ne 0 ]; then \
	  printf '%s\n' 'make erdos failed: final theorem HypostructureErdos64EG.erdos_64 is not available at OfficialStatement.'; \
	  exit $$status; \
	fi; \
	if printf '%s\n' "$$output" | grep -q 'sorryAx'; then \
	  printf '%s\n' 'make erdos failed: final theorem or closure probe depends on sorryAx.'; \
	  exit 1; \
	fi

build: framework-build erdos-build

mathlib-cache:
	cd $(HYPOSTRUCTURE_DIR) && lake exe cache get
	cd $(ERDOS_DIR) && lake exe cache get

lint:
	$(PYTHON) $(HYPOSTRUCTURE_DIR)/scripts/check_total_execution.py
	$(PYTHON) $(HYPOSTRUCTURE_DIR)/scripts/check_quarantine.py
	$(PYTHON) .agents/skills/eg-proof-expansion/scripts/api_catalog.py check \
	  --repo-root .
	$(PYTHON) to_formalize/check_type_II_regularity.py

typeii-paper-check:
	$(PYTHON) to_formalize/check_type_II_regularity.py

test: build lint

# --- Interactive proof explorer (web/) -------------------------------------
# A static site; no backend and no Lean toolchain involved.

$(WEB_FRONTEND)/node_modules: $(WEB_FRONTEND)/package.json
	cd $(WEB_FRONTEND) && $(NPM) install
	@touch $@

web-install: $(WEB_FRONTEND)/node_modules

# The diagrams, statements and constants are read out of the manuscripts; the
# page each label lands on, out of the .aux files their PDFs were built with.
$(WEB_DATA) &: $(WEB_SOURCES) $(WEB_TOOLS)
	$(PYTHON) $(WEB_DIR)/tools/extract_proof_graph.py
	$(PYTHON) $(WEB_DIR)/tools/extract_page_map.py

web-data:
	$(PYTHON) $(WEB_DIR)/tools/extract_proof_graph.py
	$(PYTHON) $(WEB_DIR)/tools/extract_page_map.py
	$(PYTHON) $(WEB_DIR)/tools/test_extract_proof_graph.py

web: web-install $(WEB_DATA)
	cd $(WEB_FRONTEND) && $(NPM) run dev

web-build: web-install $(WEB_DATA)
	cd $(WEB_FRONTEND) && $(NPM) run build

web-test: web-install $(WEB_DATA)
	$(PYTHON) $(WEB_DIR)/tools/test_extract_proof_graph.py
	cd $(WEB_FRONTEND) && $(NPM) run typecheck && $(NPM) run test
