# Document relocation audit

Task: `P0-window-94-verify-document-relocation`  
Pinned branch: `node144-window-32d32f9d19e7`  
Result: `SUBMITTED_RESULT` (submitted for controller review; no acceptance or closure asserted).  
Implementation status: `none`.

## Byte identities

All five supplied source-manifest hashes were recomputed from raw bytes and match. All ten relocation entries resolve to the declared archive hash: four workflow references and six manual references. Duplicate references do not constitute additional independent evidence.

| Repository path | Bytes | Recomputed SHA256 |
|---|---:|---|
| `audits/erdos-64-red-team/node144-residual-first/window-document-relocation-input.json` | 4527 | `7eb9b228642d6e718c595d19add9f866ad640c232e9aa43e66222bdb83a5bd75` |
| `repair_and_closure.md` | 165067 | `437e624d8a873808d02b470220ede27fb903da98750b998da1fae77defc52aab` |
| `tools/methodology_gate/evidence_snapshots/9b3ae2690229ca606e7bf75828fbe51e9171dea043a34b32394bd8db40aead0a` | 20526 | `9b3ae2690229ca606e7bf75828fbe51e9171dea043a34b32394bd8db40aead0a` |
| `tools/methodology_gate/evidence_snapshots/acd2eebe8a315723f4d5c6c7ee12b614d8c93d2260d96e303c088d7164ddfef6` | 163729 | `acd2eebe8a315723f4d5c6c7ee12b614d8c93d2260d96e303c088d7164ddfef6` |
| `tools/methodology_gate/policy/workflow.json` | 24104 | `c5a45123dfd5c1e625ff5977c9d8b27be727e8296f66c4bd58e1b49160908e56` |

The two archive files therefore preserve the original cited byte identities specified in the relocation input. This checks the supplied historical identity commitments, not a separately retrieved original checkout. The relocation input names the historical P3 source-separator, P4 edge-Menger-statement, and P5 terminal-significance references; their proof verdicts are carried forward unchanged. Their proof artifacts and the named backup are not additional declared inputs and were not re-proved or independently compared.

## Exhaustive differences and mathematical preservation

A recursive parsed-JSON comparison finds exactly two semantic differences in the workflow: replacement of `taskflow.worker_instruction` and addition of `taskflow.context_policy`. Restoring the former instruction and removing the new policy makes the parsed documents exactly equal, including every ordered array. The old instruction survives verbatim inside the expanded instruction. The new policy equals the assignment's context policy. The remaining textual differences are formatting; the full raw-text diff appears below.

For the manual, the entire byte difference is one insertion of four lines immediately after archived line 201: a blank line, the fresh-context paragraph, a blank line, and the worker-termination/review/admission paragraph (current lines 202–205). Removing precisely those lines reconstructs the archived bytes exactly. No existing manual text was removed or replaced. In particular, archived lines 418–435 correspond to current lines 422–439, and the cited Menger statement at archived line 431 is unchanged at current line 435.

The added text governs isolation, task scope, artifact transfer, independent fresh reviews, controller integration, stopping, retries and construction admission. It changes no accepted mathematical statement in the compared documents. Workflow `taskflow.units.move`, `taskflow.phase_tasks.3`, `taskflow.phase_descriptions.3` and `.5`, and the accepted-stage lock are unchanged. A Menger linkage–separator dichotomy without outcome consumers remains insufficient for branch reduction; reviewed productivity on the complete residual remains necessary. No historical proof verdict is reopened by this relocation.

Construction admission remains: before construction, every outcome must have a proved productive conditional payoff on the complete residual and a reviewed Phase 5 admission; prerequisite submoves finish before dependent construction. A successful build cannot supply missing admission evidence. A candidate, a local implication, an admitted reduction and a closed branch retain their separate evidentiary requirements.

## Instructions affecting the next assignment

There is a retained operational incompatibility if the following older instructions are treated as commands for one worker to continue beyond its assignment:

- Current manual line 433 (archived 429) tells the executor to repair a failed construction or select another admissible move.
- Current manual line 435 (archived 431) tells it to execute each survivor's continuation.
- Current manual line 439 (archived 435) tells it to enqueue children and continue until the queue is empty when branch closure is requested.
- The workflow's unchanged top-level `rule` describes selecting a move and continuing on each exact survivor; its stage-wide output specifications likewise cannot be read as authorization for a single worker to execute multiple atomic tasks.

For the next worker, the explicit current `taskflow.context_policy`, expanded worker instruction, manual lines 203–205, and assignment scope require one isolated task only. At a missing inference it must return `NEEDS_DECOMPOSITION` with immediate obligations and terminate; it cannot repair a child, select another move, or continue survivors itself. The controller handles subsequent dispatch and integration, with two independent fresh reviewer contexts. The older continuation requirements remain overall proof obligations, not permission to exceed a worker assignment. If fresh context or OS isolation is unavailable, the launch must stop with an execution failure. No next task is selected here.

This operational conflict is identified, not a changed mathematical rule or failed hash identity. No repair obligation or missing inference was encountered in the assigned document comparison.

## Preserved residual and limits

The selected `EGInput`, its graph and registered baseline, the literal post-[144] ledger, all domains and exclusions, and `K.selection` with both registered minimality orders remain as pinned. The witnesses within `K.typeBHandoff` and within `SameTokenTypeBHandoffEnvelopeStatement` retain their identities; no equality with class-audit or capacity-token witnesses is introduced. All accounts remain unchanged, including strict surplus, `2m = 3n + s`, the token and role accounts, coupled excess, geometric pattern bound, and the absence of a certified bound on pair demands per decorated handoff envelope. No proof, new move, mathematical progress, negative arm, implementation certificate, move closure or branch closure is claimed.

Side observations only: the relocation list contains repeated references, and its backup path is outside the declared reads. Neither observation is pursued.

## Exact textual differences

These unified diffs were generated directly from the hash-verified byte streams (UTF-8, preserving line endings). They include every changed line.

```diff
--- tools/methodology_gate/evidence_snapshots/9b3ae2690229ca606e7bf75828fbe51e9171dea043a34b32394bd8db40aead0a
+++ tools/methodology_gate/policy/workflow.json
@@ -8,41 +8,240 @@
     },
     "phase_zero": {
       "title": "Restore the exact residual",
-      "tasks": ["pin_source_revision", "state_endpoint", "identify_incoming_alternative", "register_retained_object", "check_inherited_premise", "record_minimality_or_import"],
+      "tasks": [
+        "pin_source_revision",
+        "state_endpoint",
+        "identify_incoming_alternative",
+        "register_retained_object",
+        "check_inherited_premise",
+        "record_minimality_or_import"
+      ],
       "gate": "Reconstruct the complete incoming state without hidden premises or guessed identifications; merged alternatives remain tagged.",
       "fast_path": "An already evidenced contradiction proceeds to integration and verification."
     },
     "phase_tasks": {
-      "1": ["record_prior_use", "state_prior_result", "identify_unused_interaction", "check_account_balance", "check_transport"],
-      "2": ["inspect_coordinate", "name_observable", "register_interaction", "compare_attempt", "state_unresolved_question"],
-      "3": ["relate_restrictions", "state_prospective_consequence", "justify_prospect", "compare_rival", "select_tension"],
-      "4": ["state_textbook_move", "match_prerequisite", "specify_output", "state_proposed_effect", "compare_attempt_fingerprint", "select_candidate"],
-      "5": ["define_outcome_payoff", "prove_conditional_inference", "specify_survivor_analysis", "check_prerequisite", "reject_cosmetic_payoff", "decompose_construction", "review_admission"],
-      "6": ["define_object", "prove_property", "prove_identification", "preserve_condition", "update_account", "establish_alternative", "check_coverage", "review_inference"],
-      "7": ["relate_new_and_retained", "prove_integrated_consequence", "reconcile_account", "revisit_blocked_move", "review_integration", "test_constraint", "test_compression", "test_quantity", "form_survivor", "record_advancement", "prove_refinement", "prove_coverage", "prove_recursive_decrease", "name_next_obligation"],
-      "8": ["review_terminal_implication", "check_transition", "check_handoff", "check_recursive_field", "check_formal_implementation", "check_composition", "synchronize_views"]
+      "1": [
+        "record_prior_use",
+        "state_prior_result",
+        "identify_unused_interaction",
+        "check_account_balance",
+        "check_transport"
+      ],
+      "2": [
+        "inspect_coordinate",
+        "name_observable",
+        "register_interaction",
+        "compare_attempt",
+        "state_unresolved_question"
+      ],
+      "3": [
+        "relate_restrictions",
+        "state_prospective_consequence",
+        "justify_prospect",
+        "compare_rival",
+        "select_tension"
+      ],
+      "4": [
+        "state_textbook_move",
+        "match_prerequisite",
+        "specify_output",
+        "state_proposed_effect",
+        "compare_attempt_fingerprint",
+        "select_candidate"
+      ],
+      "5": [
+        "define_outcome_payoff",
+        "prove_conditional_inference",
+        "specify_survivor_analysis",
+        "check_prerequisite",
+        "reject_cosmetic_payoff",
+        "decompose_construction",
+        "review_admission"
+      ],
+      "6": [
+        "define_object",
+        "prove_property",
+        "prove_identification",
+        "preserve_condition",
+        "update_account",
+        "establish_alternative",
+        "check_coverage",
+        "review_inference"
+      ],
+      "7": [
+        "relate_new_and_retained",
+        "prove_integrated_consequence",
+        "reconcile_account",
+        "revisit_blocked_move",
+        "review_integration",
+        "test_constraint",
+        "test_compression",
+        "test_quantity",
+        "form_survivor",
+        "record_advancement",
+        "prove_refinement",
+        "prove_coverage",
+        "prove_recursive_decrease",
+        "name_next_obligation"
+      ],
+      "8": [
+        "review_terminal_implication",
+        "check_transition",
+        "check_handoff",
+        "check_recursive_field",
+        "check_formal_implementation",
+        "check_composition",
+        "synchronize_views"
+      ]
     },
     "phase_descriptions": {
-      "1": {"title": "Account for used structure", "input": "Exact Phase 0 branch snapshot.", "output": "Per-object, per-use structural ledger, including resource balances and unresolved interactions.", "gate": "Every claimed earlier use has a cited result; reusable premises and finite resources are distinguished."},
-      "2": {"title": "Inventory unused structure", "input": "Exact residual and prior-use ledger.", "output": "Actual observables and unresolved interactions, including higher-order conjunctions; no technique selection.", "gate": "Each candidate is anchored in the retained object and unknown properties remain unknown."},
-      "3": {"title": "Select a structural tension", "input": "Unresolved interactions on the full residual.", "output": "One compatibility question, supported prospective payoff, serious rival comparison, and selected local aspect.", "gate": "The selection identifies an actual structural relation before choosing a method."},
-      "4": {"title": "Catalogue textbook moves", "input": "One selected structural tension.", "output": "Exact local mechanisms, prerequisites, complete outcomes, and attempt fingerprints.", "gate": "Missing prerequisites and exceptional cases remain explicit; no construction yet."},
-      "5": {"title": "Prove local payoffs and authorize", "input": "One candidate move with its outcomes.", "output": "For each outcome, an accepted conditional implication from the full branch to closure or a precise productive restriction.", "gate": "Every outcome has reviewed payoff evidence; prerequisite submoves finish before dependent construction."},
-      "6": {"title": "Execute one construction task", "input": "Pinned branch and authorized ready obligation.", "output": "One actual construction, inference, preservation, account update, or coverage proof on the retained objects.", "gate": "Evidence is tied to the actual witnesses and no missing inference is hidden."},
-      "7": {"title": "Integrate and continue survivors", "input": "Accepted new results plus all retained facts and accounts.", "output": "Integrated consequences, separate constraint/compression/quantity tests, exact survivors, and next local obligations.", "gate": "Every outcome closes with evidence or remains an explicit open residual; move credit also requires real payoff on every arm."},
-      "8": {"title": "Verify and synchronize", "input": "Accepted local work and every remaining branch obligation.", "output": "Exact endpoint proof or honest reduction theorem with synchronized formal and manuscript views.", "gate": "Closure is derived from complete AND-case coverage, current evidence, and the required implementation checks."}
-    },
-    "task_fields": ["id", "mode", "phase", "branch_revision", "move_id", "kind", "goal", "objects", "reads", "interaction", "parent_payoff", "depends_on", "allowed_write", "acceptance", "on_failure"],
-    "result_fields": ["status", "output", "evidence", "implementation_status", "first_missing_inference", "immediate_subobligations", "metadata"],
-    "metadata_fields": ["structural_use", "interaction", "changed_objects", "changed_accounts", "side_observations"],
-    "structural_use_fields": ["aspect", "object", "previous_use", "established", "unexploited"],
-    "interaction_fields": ["object", "ingredients", "relation", "known", "unresolved", "domains", "previous_use"],
-    "move_fields": ["id", "branch_revision", "source_outcome", "selected_conflict", "textbook_statement", "prerequisites", "construction_tasks", "conditional_payoff_tasks", "coverage_task", "outcomes"],
-    "worker_results": ["SUBMITTED_RESULT", "NEEDS_DECOMPOSITION", "BLOCKED_WITH_REASON", "COUNTEREXAMPLE_CANDIDATE"],
-    "priority": ["repair_required_evidence", "verify_terminal_closure", "integrate_new_result", "finish_active_move", "continue_survivor", "select_new_tension"],
-    "advancement": ["constraint_restriction", "quantitative_restriction", "actionable_obstruction", "reduction_or_compression", "closure"],
-    "closure_tests": ["constraint", "compression", "quantity"],
-    "worker_instruction": "Execute only this task on the pinned complete residual. Use applicable retained facts and the supplied evidence. Preserve object identities, domains, exclusions, minimality and accounts. Prove the requested inference on the conjunction. Expose the first missing inference as immediate subobligations. Record side observations without following them. Do not select a negative arm from failed search, change strategy without authorization, or mark a move or branch closed yourself."
+      "1": {
+        "title": "Account for used structure",
+        "input": "Exact Phase 0 branch snapshot.",
+        "output": "Per-object, per-use structural ledger, including resource balances and unresolved interactions.",
+        "gate": "Every claimed earlier use has a cited result; reusable premises and finite resources are distinguished."
+      },
+      "2": {
+        "title": "Inventory unused structure",
+        "input": "Exact residual and prior-use ledger.",
+        "output": "Actual observables and unresolved interactions, including higher-order conjunctions; no technique selection.",
+        "gate": "Each candidate is anchored in the retained object and unknown properties remain unknown."
+      },
+      "3": {
+        "title": "Select a structural tension",
+        "input": "Unresolved interactions on the full residual.",
+        "output": "One compatibility question, supported prospective payoff, serious rival comparison, and selected local aspect.",
+        "gate": "The selection identifies an actual structural relation before choosing a method."
+      },
+      "4": {
+        "title": "Catalogue textbook moves",
+        "input": "One selected structural tension.",
+        "output": "Exact local mechanisms, prerequisites, complete outcomes, and attempt fingerprints.",
+        "gate": "Missing prerequisites and exceptional cases remain explicit; no construction yet."
+      },
+      "5": {
+        "title": "Prove local payoffs and authorize",
+        "input": "One candidate move with its outcomes.",
+        "output": "For each outcome, an accepted conditional implication from the full branch to closure or a precise productive restriction.",
+        "gate": "Every outcome has reviewed payoff evidence; prerequisite submoves finish before dependent construction."
+      },
+      "6": {
+        "title": "Execute one construction task",
+        "input": "Pinned branch and authorized ready obligation.",
+        "output": "One actual construction, inference, preservation, account update, or coverage proof on the retained objects.",
+        "gate": "Evidence is tied to the actual witnesses and no missing inference is hidden."
+      },
+      "7": {
+        "title": "Integrate and continue survivors",
+        "input": "Accepted new results plus all retained facts and accounts.",
+        "output": "Integrated consequences, separate constraint/compression/quantity tests, exact survivors, and next local obligations.",
+        "gate": "Every outcome closes with evidence or remains an explicit open residual; move credit also requires real payoff on every arm."
+      },
+      "8": {
+        "title": "Verify and synchronize",
+        "input": "Accepted local work and every remaining branch obligation.",
+        "output": "Exact endpoint proof or honest reduction theorem with synchronized formal and manuscript views.",
+        "gate": "Closure is derived from complete AND-case coverage, current evidence, and the required implementation checks."
+      }
+    },
+    "task_fields": [
+      "id",
+      "mode",
+      "phase",
+      "branch_revision",
+      "move_id",
+      "kind",
+      "goal",
+      "objects",
+      "reads",
+      "interaction",
+      "parent_payoff",
+      "depends_on",
+      "allowed_write",
+      "acceptance",
+      "on_failure"
+    ],
+    "result_fields": [
+      "status",
+      "output",
+      "evidence",
+      "implementation_status",
+      "first_missing_inference",
+      "immediate_subobligations",
+      "metadata"
+    ],
+    "metadata_fields": [
+      "structural_use",
+      "interaction",
+      "changed_objects",
+      "changed_accounts",
+      "side_observations"
+    ],
+    "structural_use_fields": [
+      "aspect",
+      "object",
+      "previous_use",
+      "established",
+      "unexploited"
+    ],
+    "interaction_fields": [
+      "object",
+      "ingredients",
+      "relation",
+      "known",
+      "unresolved",
+      "domains",
+      "previous_use"
+    ],
+    "move_fields": [
+      "id",
+      "branch_revision",
+      "source_outcome",
+      "selected_conflict",
+      "textbook_statement",
+      "prerequisites",
+      "construction_tasks",
+      "conditional_payoff_tasks",
+      "coverage_task",
+      "outcomes"
+    ],
+    "worker_results": [
+      "SUBMITTED_RESULT",
+      "NEEDS_DECOMPOSITION",
+      "BLOCKED_WITH_REASON",
+      "COUNTEREXAMPLE_CANDIDATE"
+    ],
+    "priority": [
+      "repair_required_evidence",
+      "verify_terminal_closure",
+      "integrate_new_result",
+      "finish_active_move",
+      "continue_survivor",
+      "select_new_tension"
+    ],
+    "advancement": [
+      "constraint_restriction",
+      "quantitative_restriction",
+      "actionable_obstruction",
+      "reduction_or_compression",
+      "closure"
+    ],
+    "closure_tests": [
+      "constraint",
+      "compression",
+      "quantity"
+    ],
+    "worker_instruction": "You are a fresh worker assigned exactly one isolated mathematical problem. Execute only this task on the pinned complete residual. Use applicable retained facts and the supplied evidence. Preserve object identities, domains, exclusions, minimality and accounts. Prove the requested inference on the conjunction. Expose the first missing inference as immediate subobligations. Record side observations without following them. Do not select a negative arm from failed search, change strategy without authorization, or mark a move or branch closed yourself. The task goal is your only objective; the phase, branch endpoint and parent payoff supply context only. Do not execute adjacent tasks, repeat accepted work, start implementation to discover a payoff, or choose the next task. If the goal contains multiple unresolved inferences, return NEEDS_DECOMPOSITION with their immediate statements. Return one result artifact and terminate. The controller handles reviews, integration and the next fresh context.",
+    "context_policy": {
+      "unit": "One atomic mathematical problem per fresh context, in every phase including Phase 0, reviews and retries.",
+      "launch": "The controller launches a new ephemeral isolated worker for each assignment. Never resume, fork with conversation history, or reuse an earlier worker context.",
+      "inputs": "Supply the complete pinned residual and applicable retained hypotheses, exact object identities, accepted evidence declared for this task, one goal, one output artifact, acceptance criteria and a first-failure rule. Carry proof state through these artifacts only.",
+      "scope": "The worker solves only the assigned inference, construction, comparison or check. A phase containing several obligations uses several fresh contexts. The branch endpoint and parent payoff are context, not additional worker goals.",
+      "stop": "Return one result and terminate. At the first missing inference, return NEEDS_DECOMPOSITION with immediate subobligations. Only the controller may assign a child or next task in another fresh context.",
+      "review": "Two independent fresh reviewer contexts inspect the single result. Neither sees the other review. The controller alone accepts and integrates it before dispatching the next task.",
+      "admission": "Before construction, every outcome must have a proved productive conditional payoff on the complete residual and a reviewed Phase 5 admission. A successful build cannot supply missing admission evidence.",
+      "failure": "If fresh context or OS isolation is unavailable, stop the launch and report the execution failure. Never perform the proof in the controller conversation as a fallback."
+    }
   },
   "accepted_stage_rule": "An accepted stage is locked: never execute, reconstruct, reclassify, or re-review it during a later-stage repair. Carry its exact reviewed artifact forward. A later failure, missing source, changed source scope, validator error, or missing productive conflict cannot unlock it. Default repair_stage is the stage that failed. Only two independent reviewers may formally revoke acceptance by naming the same earlier stage and citing concrete evidence of a defect in that stage's own result; only then may repair move backward. A failed Stage 6 construction returns to Stage 5 authorization under the construction-failure rule.",
   "common_gates": [
```

```diff
--- tools/methodology_gate/evidence_snapshots/acd2eebe8a315723f4d5c6c7ee12b614d8c93d2260d96e303c088d7164ddfef6
+++ repair_and_closure.md
@@ -199,6 +199,10 @@
 An atomic task is complete when its exact output has accepted evidence. A structural move is productive only when *every* outcome has a reviewed structural payoff. A branch closes only when all reachable outcomes compose to its exact endpoint. These are three different statuses. New information that was already implied by `B` can make its description explicit without literally shrinking the model set; record the established consequence, not a fictitious witness in `B \ (B ∧ P)`.
 
 Each worker receives one task with a pinned branch revision, exact objects, allowed inputs and write scope, dependencies, acceptance evidence, and a first-failure rule. The controller chooses ready tasks in dependency order, prioritizing stale evidence repair, evidenced closure, integration, active construction, then fair continuation of survivors. An empty queue is a diagnosis, not a proof. Proposed mathematics, reviewed mathematics, and kernel-checked implementation are recorded separately. Mathematical acceptance needs actual proof evidence; a JSON status or passing schema check cannot establish an arbitrary implication.
+
+**Fresh context is mandatory for every atomic task in every phase.** A phase with several obligations is split into separate mathematical problems, each launched in a new isolated worker process. The worker receives the complete retained hypotheses and declared accepted evidence, one precise goal, one output artifact and one stopping condition. It receives no previous conversation, worker transcript or general instruction to finish the branch. The parent payoff explains the task; it does not authorize adjacent work. Context isolation must never discard mathematical conditioning or replace actual bound witnesses.
+
+The worker returns its single result and terminates. A missing inference produces `NEEDS_DECOMPOSITION` and the immediate child obligations; the worker cannot execute them itself. Two fresh independent reviewer contexts inspect the submitted result. Only the controller accepts and integrates it, then launches the next task in another fresh context. Retries also start fresh and receive only the exact defect and required evidence. Phase 6 requires a reviewed Phase 5 admission covering the productive conditional payoff of every outcome before construction starts. If isolation cannot be established, report an execution failure and stop the launch; do not continue the mathematics in the controller conversation.
 
 For EG formalization, preserve `ExactLedger`, `FactInputs`, `FactManifest`, and the sealed owner-local executor. The task queue never transports proof facts outside that canonical path. Repair the first defective decision while preserving unaffected accepted facts and closed siblings. A failed search does not select a negative mathematical arm; a split on a missing premise must analyze both arms with the successful prefix retained.
 
```

