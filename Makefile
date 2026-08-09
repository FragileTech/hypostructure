.PHONY: help build test lint mathlib-cache framework-build erdos-build erdos

.DEFAULT_GOAL := help

PYTHON ?= python3

HYPOSTRUCTURE_DIR := hypostructure
ERDOS_DIR := proofs/hypostructure_erdos_64_eg
ERDOS_TARGET := HypostructureErdos64EG

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
	  '  make test            Build everything and run the gates' \
	  '  make mathlib-cache   Fetch prebuilt Mathlib artifacts'

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
	  '#check HypostructureErdos64EG.erdos_64_of_selectedContradiction' \
	  '#check HypostructureErdos64EG.erdos_64' \
	  'example : HypostructureErdos64EG.OfficialStatement :=' \
	  '  HypostructureErdos64EG.erdos_64' \
	  '#print axioms HypostructureErdos64EG.erdos_64_of_selectedContradiction' \
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

test: build lint
