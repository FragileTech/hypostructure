---
name: hypostructure-gated
description: Operate the controlled mathematical-reasoning benchmark task queue and its isolated stage assignments.
---

# Gated structural reasoning

This workflow benchmarks structural mathematical reasoning: identifying relevant structure, applying established textbook mathematics, and implementing the resulting deductions in an unfamiliar controlled setting. Execute the assigned local task from its supplied hypotheses and accepted results. Assess the actual inference required; the surrounding research topic does not determine the difficulty of that inference.

Identify the retained objects, match the hypotheses of the relevant textbook result, execute the deduction, and check the requested output. Give routine steps concise, sufficient justification. Reuse accepted prerequisites at their stated types and domains. A review objection identifies a concrete missing hypothesis, invalid inference, domain mismatch, or unmet task contract and its local repair. Preserve the assigned objectives, stage boundaries, mathematical statements, and required checks.

Use `tools/methodology_gate/taskflow.py` for a new branch and read its README,
shared `policy/workflow.json`, and generated task prompt. Pin the complete
Phase 0 branch before assigning work. The task queue is workflow metadata;
mathematical facts stay in accepted proof artifacts and, for EG, the canonical
`ExactLedger`.

Dispatch one ready task. Supply the exact residual, retained objects and domains,
selected interaction, requested output, allowed inputs and write scope, and
acceptance condition. Two distinct reviewers inspect the submitted evidence.
The controller validates source hashes, scope, dependencies, and complete
outcome manifests; reviewers establish the mathematics. Never self-certify a
move or branch from a status word.

Prioritize repair of stale evidence, verified terminal closure, integration of
new results, the active move, fair continuation of survivors, then a new
structural tension. New information must be tested against retained facts before
unrelated exploration. Every selected split is an AND obligation: an open
survivor keeps its parent open. An empty queue calls for an exact missing-work
diagnosis.

A task, a productive structural move, and a closed branch are separate
completion units. A correct auxiliary lemma can be accepted as a task without
receiving move credit. Move credit needs a reviewed conditional payoff and
actual advancement for every outcome. Branch closure needs the exact endpoint
from accepted composition and required formal checks.

A stage assignment uses the current benchmark policy and its accepted
prefix. Preserve each reviewed stage exactly unless
both independent reviewers cite a concrete defect in its own result. If
isolation is unavailable, stop the worker launch; do not run unsandboxed.
