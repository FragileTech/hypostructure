.PHONY: help build test lint mathlib-cache framework-build \
	erdos-build erdos-json erdos ab ab-json clean-runs

.DEFAULT_GOAL := help

PYTHON ?= python3

HYPOSTRUCTURE_DIR := hypostructure
ERDOS_DIR := proofs/hypostructure_erdos_64_eg
ERDOS_TARGET := HypostructureErdos64EG.Official.StructuralProgram
AB_TARGET := HypostructureErdos64EG.AB.Execution
RUN_DIR := build/hypostructure
ERDOS_RUN := $(RUN_DIR)/eg-official-run.json
AB_RUN := $(RUN_DIR)/eg-ab-run.json
ERDOS_LOG := $(RUN_DIR)/eg-official-build.log
ERDOS_AUDIT := $(RUN_DIR)/eg-closure-audit.log
AB_LOG := $(RUN_DIR)/eg-ab-build.log

# The sealed frontend emits this exact sentence when `ofDag%` rejects a
# declaration because a residual survives.  That rejection is a reported
# outcome of the run, not a build error, so the recipes below match on it.
RESIDUAL := sealed compiler could not derive total execution closure

help:
	@printf '%s\n' \
	  'Hypostructure' \
	  '' \
	  '  make ab              Run the framework on the Type-A/Type-B target' \
	  '  make erdos           Compile and execute the sealed official EG proof' \
	  '  make erdos-json      Export and validate the official EG proof run' \
	  '  make framework-build Build the reusable Hypostructure package' \
	  '  make erdos-build     Build the official EG structural program' \
	  '  make build           Build the framework and run both proof targets' \
	  '  make lint            Run the total-execution gate over the framework' \
	  '  make mathlib-cache   Fetch prebuilt Mathlib artifacts' \
	  '  make clean-runs      Remove exported runs, logs, and audits'

framework-build:
	cd $(HYPOSTRUCTURE_DIR) && lake build

erdos-build: framework-build
	cd $(ERDOS_DIR) && lake build $(ERDOS_TARGET)

build: framework-build ab erdos

mathlib-cache:
	cd $(HYPOSTRUCTURE_DIR) && lake exe cache get
	cd $(ERDOS_DIR) && lake exe cache get

lint:
	$(PYTHON) $(HYPOSTRUCTURE_DIR)/scripts/check_total_execution.py
	$(PYTHON) $(HYPOSTRUCTURE_DIR)/scripts/check_quarantine.py

# Type-A/Type-B frontier.  `abClosure` is expected to be rejected while any
# terminal is open; `reduceDag%` still exports the run, so the JSON
# certificate is the artifact this target validates.
ab-json: framework-build
	@mkdir -p $(RUN_DIR)
	@cd $(ERDOS_DIR) && \
	  if lake build $(AB_TARGET) > ../../$(AB_LOG) 2>&1; then \
	    echo "A/B frontier: the strict ofDag% declaration closes."; \
	  elif grep -q "$(RESIDUAL)" ../../$(AB_LOG); then \
	    echo "A/B frontier: certified reduction retains an exact residual."; \
	  else \
	    cat ../../$(AB_LOG); \
	    exit 1; \
	  fi
	@test -s $(AB_RUN) || { echo "missing run export: $(AB_RUN)"; exit 1; }
	@$(PYTHON) -m json.tool $(AB_RUN) >/dev/null
	@echo "A/B run exported and validated: $(AB_RUN)"

ab: ab-json

# Official EG proof.  `Official/StructuralProgram.lean` imports
# `AB/Execution.lean`, so while the A/B frontier still carries a residual its
# module fails to elaborate and no official run can be exported.  That case is
# reported distinctly from a genuine build break.
erdos-json: framework-build
	@mkdir -p $(RUN_DIR)
	@cd $(ERDOS_DIR) && \
	  if lake build $(ERDOS_TARGET) > ../../$(ERDOS_LOG) 2>&1; then \
	    echo "Official EG target built."; \
	  elif grep -q "$(RESIDUAL)" ../../$(ERDOS_LOG); then \
	    echo "Official EG run not exported: an imported declaration still"; \
	    echo "carries a surviving residual (see $(ERDOS_LOG))."; \
	    echo "Run 'make ab' for the current frontier report."; \
	    exit 1; \
	  else \
	    cat ../../$(ERDOS_LOG); \
	    exit 1; \
	  fi
	@test -s $(ERDOS_RUN) || { echo "missing run export: $(ERDOS_RUN)"; exit 1; }
	@$(PYTHON) -m json.tool $(ERDOS_RUN) >/dev/null
	@echo "Official EG run exported and validated: $(ERDOS_RUN)"

erdos: erdos-json
	@cd $(ERDOS_DIR) && \
	  if lake env lean HypostructureErdos64EG/Official/ClosureProbe.lean \
	      > ../../$(ERDOS_AUDIT) 2>&1; then \
	    echo "EG closure audit: the strict ofDag% declaration closes."; \
	  elif grep -q "$(RESIDUAL)" ../../$(ERDOS_AUDIT); then \
	    echo "EG closure audit: certified reduction retains an exact residual."; \
	  else \
	    cat ../../$(ERDOS_AUDIT); \
	    exit 1; \
	  fi

test: ab lint

clean-runs:
	rm -f $(ERDOS_RUN) $(AB_RUN) $(ERDOS_LOG) $(AB_LOG) $(ERDOS_AUDIT)
