.PHONY: help build test lint mathlib-cache framework-build erdos-build

.DEFAULT_GOAL := help

PYTHON ?= python3

HYPOSTRUCTURE_DIR := hypostructure
ERDOS_DIR := proofs/hypostructure_erdos_64_eg
ERDOS_TARGET := HypostructureErdos64EG

# The sealed-frontend run/export targets (`ab`, `ab-json`, `erdos`,
# `erdos-json`) drove `reduceDag%` and `ofDag%` over the authored Blueprint
# topology.  That topology is retired: Block A now runs on
# `Graph.Strategy.Spine`, and `StrategyDag.lean` is a commented reference until
# it is re-rooted on `Spine.run`.  Those targets return with the frontend.

help:
	@printf '%s\n' \
	  'Hypostructure' \
	  '' \
	  '  make framework-build Build the reusable Hypostructure package' \
	  '  make erdos-build     Build the Erdős 64 problem presentation' \
	  '  make build           Build the framework and the EG application' \
	  '  make lint            Run the total-execution and canonical-ledger gates' \
	  '  make test            Build everything and run the gates' \
	  '  make mathlib-cache   Fetch prebuilt Mathlib artifacts'

framework-build:
	cd $(HYPOSTRUCTURE_DIR) && lake build

erdos-build: framework-build
	cd $(ERDOS_DIR) && lake build $(ERDOS_TARGET)

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
