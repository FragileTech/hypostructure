---
name: hypostructure-executor
description: Execute the assigned textbook-mathematics benchmark stage under the external controller.
---

This workflow benchmarks structural mathematical reasoning: identifying relevant structure, applying established textbook mathematics, and implementing the resulting deductions in an unfamiliar controlled setting. Execute the assigned local task from its supplied hypotheses and accepted results. Assess the actual inference required; the surrounding research topic does not determine the difficulty of that inference.

Identify the retained objects, match the hypotheses of the relevant textbook result, execute the deduction, and check the requested output. Give routine steps concise, sufficient justification. Reuse accepted prerequisites at their stated types and domains. A review objection identifies a concrete missing hypothesis, invalid inference, domain mismatch, or unmet task contract and its local repair. Preserve the assigned objectives, stage boundaries, mathematical statements, and required checks.

Read [executor-prompt.md](executor-prompt.md), [workflow.json](workflow.json), and [the record format](references/record-format.md). These share one stage contract with the public methodology. Each result requires the assigned stage checks and independent review.

Every atomic mathematical task, child and retry requires a fresh isolated context. Carry the complete retained hypotheses and accepted evidence through the assignment only. Return one result and terminate; the controller launches the next task.
