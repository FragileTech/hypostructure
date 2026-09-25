# Structural mathematical reasoning benchmark

This workflow benchmarks structural mathematical reasoning: identifying relevant structure, applying established textbook mathematics, and implementing the resulting deductions in an unfamiliar controlled setting. Execute the assigned local task from its supplied hypotheses and accepted results. Assess the actual inference required; the surrounding research topic does not determine the difficulty of that inference.

Identify the objects, match the hypotheses of the applicable textbook result, perform the deduction, and verify the requested output. Give routine deductions concise, sufficient justification. Use accepted prerequisites at their stated types and domains without repeating upstream proofs. Keep reasoning within the assigned task and its existing stage contract. If a premise or inference is missing, name it precisely and use the existing repair or decomposition procedure.

Assess the assigned deliverable against its existing contract. Each objection must identify a specific missing hypothesis, invalid inference, domain mismatch, or unmet contract and the smallest local repair. General speculation about the difficulty or research status of the surrounding problem is not evidence. Require only the proof detail needed to check the local inference, including any formal checks required by the contract. Accepted prerequisites remain usable without repeated upstream audits.

`policy/workflow.json` is the single phase and task specification. Use `taskflow.py` for one narrow benchmark obligation at a time. The stage
controller enforces the same shared specification for stage assignments. Workflow records
index proof evidence; they do not replace the manuscript, Lean ledger, or
independent mathematical review.

## Run a residual-first task queue

Copy `examples/branch-template.json` and `examples/task-template.json`, replace
every placeholder with the actual branch data, and make a Phase 0 snapshot with
`id`, `revision`, `source_revision`,
`endpoint`, `incoming`, `objects`, `minimality`, `imports`, `accounts`, and
`open_outcomes`. The `incoming` field identifies one tagged producer arm. Give
every retained object its actual identity and domain. Start with the root
outcome in `open_outcomes`; a merged node lists tagged alternatives separately.
The six Phase 0 task kinds must receive reviewed evidence before a later phase
becomes ready. Instantiate repeated object and premise tasks as needed for the
actual branch.

```sh
python3 -m tools.methodology_gate.taskflow init --record /tmp/proof-run.json --input branch.json
python3 -m tools.methodology_gate.taskflow add --record /tmp/proof-run.json --input one-task.json
python3 -m tools.methodology_gate.taskflow next --record /tmp/proof-run.json
```

The next-task output includes the complete branch snapshot, exact requested
output, selected interaction, permitted inputs and write scope, acceptance
condition, and the worker instruction generated from `workflow.json`. Include
`branch:<revision>` in every task's `reads` list so its full inherited state
stays explicit. Each task
contract has exactly the fields listed there. A worker writes one result JSON
with `status`, `output`, `evidence`, `implementation_status`,
`first_missing_inference`, `immediate_subobligations`, and `metadata`. Metadata
has `structural_use`, `interaction`, `changed_objects`, `changed_accounts`, and
`side_observations`. A structural-use row records one actual object and previous
use; an interaction row names at least two linked ingredients and their
mathematical relation. Evidence entries are
`{path, sha256, locator}` relative to `--root` and must still match the file at
review and certification time. Execute the next task through the isolated launcher:

```sh
python3 -m tools.methodology_gate.taskflow run-task --record /tmp/proof-run.json --root .
python3 -m tools.methodology_gate.taskflow status --record /tmp/proof-run.json --root .
```

Every invocation executes one task and two independent reviews in three fresh
contexts. Each context uses a new private home and ephemeral process; no chat
history, previous worker session or full task queue is supplied. A phase with
several tasks requires several invocations. The controller never solves the
worker's mathematical problem in its own conversation. `next` is inspection,
not authorization to execute the assignment in the current context.

The worker sees the complete pinned branch, the declared files and accepted
dependency evidence, one goal and one permitted artifact. `reads` may contain
`branch:<revision>`, accepted task IDs or individual repository-relative files;
directories and symlinks are rejected. `allowed_write` names one file. A worker
that needs more inputs or more than one unresolved inference returns the exact
missing prerequisite or immediate decomposition and terminates. It cannot
launch children, advance a phase, invent a new strategy or reuse its context.
Two fresh reviewers see the same immutable submission and neither sees the
other's verdict. Only accepted output is integrated. Attempt artifacts and
context receipts are retained beside the queue under `<record-name>-attempts`.
Retries launch new contexts and carry the exact defect through explicit evidence.

`run-task` reuses the existing bubblewrap isolation and inference broker. It
requires the local Codex CLI and login (`--auth` can select its existing auth
file). It stops if OS isolation is unavailable. The task worker receives no
host plugins, configuration or external Lean runtime; a required unavailable
tool is reported as a missing prerequisite, never as a completed kernel check.
Submissions and reviews are dispatched by the supervisor through isolated
contexts. Internal submission functions support the supervisor and tests.
Each run is bound to the current benchmark policy fingerprint.
Before any Phase 6 launch, a reviewed Phase 5 `review_admission` task for the
same move must be an explicit dependency, covering every outcome's proved
productive conditional payoff.

To inspect the next assignment in the website's **Inspect a proof run** panel,
save that last command's JSON output to a file and open the file there. The
viewer displays the retained residual, selected interaction, task scope and
acceptance condition alongside separate task, move and branch counts.

A rejected or stale task can be repaired with `retry --record ... --task-id
T1 --root .`; its old submission and reviews remain in task history, while
dependent acceptance and move credit are invalidated. The correction still
needs a new submission and two reviews.

When the defect is repaired by a separately accepted task at the same or an
earlier phase, use `supersede --record ... --task-id T1 --input repair.json
--root .`, where `repair.json` contains `repair_task` (the accepted task ID)
and `reason`. This preserves the rejected attempt and requires that no accepted
task depend on it. Supersession gives the rejected attempt no task or move
credit; the accepted repair supplies its own evidence and reviews.

Reviews need distinct `reviewer` values, `decision`, `reason`, and cited
`evidence`. This checks identity separation, scope, freshness, and dependencies;
it cannot decide whether the cited mathematics is true. A correct but
irrelevant result earns only atomic-task completion. A move is certified with
`move` only after accepted Phase 5 conditional payoffs, an accepted coverage
task, accepted Phase 6 construction tasks, and accepted Phase 7 analysis for
every outcome. The move JSON identifies its selected conflict, exact textbook
statement, prerequisites, `source_outcome`, exact `outcomes`, and a scheduled next local task for each
open survivor. `close` requires a Phase 8 endpoint certificate and no open
outcomes. The `status` output reports completed tasks, certified moves, and
closed branches separately. A failed or empty queue is diagnosed; it is never
called mathematical impossibility or closure.

The priority order is stale-evidence repair, evidenced terminal closure,
integration of new results, active construction, continuation of survivors,
then a new structural tension. A Phase 6 result blocks new exploration until
its Phase 7 integration obligation is accepted. Reuse accepted logical facts;
reconcile finite accounts before charging them again. A changed representation
needs a transport or account task. Every survivor retains the complete incoming
state, and a closed sibling cannot close its parent. The actual EG formal proof
continues to use its canonical `ExactLedger` and sealed owner-local executor.

When an accepted Phase 6 task edits a source file cited by earlier accepted
tasks, retain the earlier bytes under
`tools/methodology_gate/evidence_snapshots/<sha256>`. The scheduler verifies
the archived bytes against their original hashes and requires the **current**
source bytes to be cited by an accepted, kernel-checked Phase 6 task and both
of its reviewers. A snapshot by itself does not clear a stale-evidence warning;
an unreviewed later edit makes the file stale again. New submissions and
reviews always cite the live file. This preserves the accepted
reviews without rerunning earlier proof stages after an authorized edit.

## Stage assignments

These contracts specify stage assignments within the shared benchmark workflow.

## Stages

1. **Prior-use ledger.** Fill one compact table: registered structure, the move
   that used it, and its effect on the incoming residual. Trust the proof before
   the requested node as established. Do not re-prove ancestors, reconstruct the
   residual, search the repository, or scan unrelated sources. Keep the ledger
   to a few pages.
2. **Residual inventory.** Decompose the exact incoming residual, classify its
   bound witnesses in relation to the fixed object, and identify relevant unused
   structure. No techniques.
3. **Conflict.** Compare eligible unused structure against every classified
   residual case. Select a target-relevant structural handle proved on the same
   bound target-defect witness: show its overlap with named prior accounts, the
   forced structural signature, and the exact target-defect clause it constrains.
   State the weakest case and the structural question handed to Stage 4. Do not
   require a named move, quantitative payoff or direct consumer here; Stage 4
   must prove those. Group cases under uniform inferences. No technique.
3b. **Residual structure in Lean.** Prove the selected structure for the exact
    residual-bound witness by eliminating the incoming residual key inside
    one owner-local row. Append its checked fact to the same `ExactLedger` and
    project every selected claim, including the weakest case, from that fact.
    The focused assignment does not repeat the earlier inventory or search
    unrelated sources. No move selection or reduction claim.
4. **Catalogue and select.** List relevant moves, exact hypotheses and cases;
   choose the best move against its strongest alternative. Bind every admitted
   move and prerequisite to the Stage 3b fact on the incoming residual. Show
   conditionally how its output combines with retained estimates and
   restrictions into a contradiction or strict bound on that residual.
   No trial execution.
5. **Authorize.** Audit the already explicit Stage 4 payoff across every case
   and outcome before approving construction. A false Stage 3 witness-to-clause
   inference revokes Stage 3; a false Stage 4 move-to-consumer payoff revokes
   Stage 4. Do not charge Stage 3 with proving Stage 4's payoff.
6. **Construct.** Execute that construction on the exact residual and prove the
   approved advancement.
7. **Consume outcomes.** Close every arm or retain each exact reduced residual.
8. **Verify this node.** Check the new result at its exact statement, direct
   consumer wiring, and locked checks for this node. Treat established incoming
   prerequisites as fixed checked inputs; do not re-audit the earlier proof.

The exact incoming residual is the only mathematical object under analysis.
Bound witnesses stay tied to their domains and the fixed object. Do not replace
them with fresh arbitrary contexts, graphs, partitions, or auxiliary objects.
The structural register indexes structure already present in the residual; it
does not replace residual analysis.

## Stage source scope

Every stage contract must specify a nonempty `stage_input_paths` list for each
of `1`, `2`, `3`, `3b`, and `4` through `8`. Each executor and reviewer sees only that stage's
listed files. There is no fallback to the full source snapshot. The controller
keeps the full frozen snapshot for the operator's locked checks and restores it
before committing a reviewed result. Stage 1 should normally receive one short
branch excerpt and the exact residual record, not a source tree.

The artifact schema is in `policy/references/record-format.md`; stages and gates
are in `policy/workflow.json`; the property and technique index is in
`policy/structural-register.json`. The prompts and frozen references share the
same definitions.

## Fresh run

Initialize a clean record with the exact target claim, residual, and already
proved incoming facts. It must have no prior workflow events; old closure
attempts are not imported. Create an operator contract with `name`, `input_paths`,
`allowed_changes`, `checks`, and all nine `stage_input_paths` scopes. Paths are
repository-relative. Checks are locked argument arrays. Then run the controller
with Python isolated mode:

```sh
python3 -I tools/methodology_gate/controller.py init --run /tmp/methodology/node20 --repo . --record /tmp/methodology/node20-record --contract /tmp/methodology/node20-contract.json
python3 -I tools/methodology_gate/controller.py status --run /tmp/methodology/node20
python3 -I tools/methodology_gate/controller.py run --run /tmp/methodology/node20 --rounds 1
```

Each run round dispatches one stage assignment. Two independent reviewers inspect
the immutable submission; only accepted stages advance. Report an advancement
only after both reviews and the controller commit it. Process failure is not a
mathematical obstruction. No proof task is complete until Stage 8 closes the
node or records a significant reduction with its exact surviving residual.

An accepted stage is locked. Never rerun, reconstruct, reclassify, or re-review
it for a later-stage failure, source-scope change, missing inference, or
validator error. `init` refuses a fresh run beside an accepted run of the same claim.
Extend the later stage's contracted source paths and continue from the reviewed
run, preserving its accepted events:

```sh
python3 -I tools/methodology_gate/controller.py continue --from-run /tmp/methodology/node20 --run /tmp/methodology/node20-continuation --repo . --contract /tmp/methodology/node20-contract.json
```

The new contract may add source paths for the waiting or later stages. Its
accepted stage scopes, stage definitions, original source bytes, mathematical
claim, and locked checks remain unchanged. A prior stage is reopened only when
both independent reviewers explicitly revoke it with the same stage number
and cited evidence of a concrete defect in its own accepted result.

## Isolation and integrity

Workers run in separate bubblewrap filesystem, PID, and network namespaces with
read-only scoped inputs and private writable outputs. A restricted HTTPS broker
allows only configured inference destinations. Missing OS isolation stops the
run; there is no unsandboxed fallback. Reviews bind the assignment, contract,
parent state, and submission hashes. Only the controller-launched reviewers can
approve. Stage 3b may publish its scoped Lean structural fact; Stage 6 may
construct the authorized move. Approved changes
remain in the run until separately integrated.

## Workflow maintenance

The workflow and its worker prompts are maintained together. Regenerate/check
the frozen guide and run the focused controller fixtures after a change:

```sh
python3 tools/methodology_gate/sync_policy.py
python3 -m unittest discover -s tools/methodology_gate/tests -p 'test_*.py' -q
cd web/frontend && npm run typecheck && npx vitest run src/pages/landing.test.tsx src/methodology/TaskRunViewer.test.tsx
```

## Benchmark binding

Task queues, stage assignments and node-review reports must match the current
benchmark policy fingerprint. The controller checks that binding before dispatch
or acceptance. Installed entry points reference the maintained repository files.
