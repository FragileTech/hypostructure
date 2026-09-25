# Structural reasoning record

This file specifies the existing isolated stage-runner record. New residual-first
task queues use `taskflow.py` and the `taskflow` section of `workflow.json`.
Their records index accepted evidence and do not replace a proof ledger.

`workflow.json` is the single stage definition. `structural-register.json` is the
shared structural classification. Records carry no workflow or record version.

## Retained state

Keep `claim`, `scope`, `root`, `facts`, `nodes`, `queue`, `methodology_sources`,
`status`, `events`, `evidence` and `semantic_review`. An evidence entry is
`{path, sha256, locator, proves}`;
paths are relative to the record, immutable, and hashed. Facts have exact
`statement`, `kind` (`standing`, `derived`, `case`) and evidence IDs.

A node has `id`, `parent`, full `residual`, `goal`, `facts`, `status`, `children`.
An open leaf belongs to `queue`; a closed leaf needs `certificate`. An expanded
node needs `refinement`, `coverage`, `consumption`, `continuation` evidence and
all verified children. A recursive reduction also needs `uses_descent: true`,
`descent` and `base_cases`. Every child inherits all parent facts and history.
New children require `reduction` with `from`, `kind` (`structural_exclusion`,
`quantitative_restriction`, `well_founded_descent`), `strictness`,
`excluded_structure`, `significance`, and `evidence`.

Keep the existing `implementation_chain` format when an implementation is
required. Metadata reconciliation is not mathematical progress. Existing checked
results remain reusable at their actual types. Missing or quarantined facts
remain obligations. Only independent review may change quarantine or certify
non-use. No separate checklist receipts duplicate stage approvals.

## One event per assignment

Append `{node, stage, result, evidence, inputs, artifact, reason}`. `result` is
`done` or `failed`; `inputs` is exactly `assignment.accepted_inputs`, the digests
of all still-valid earlier stage events. Artifact fields below are strict.
Evidence lists contain registered IDs. `reason` is required on a repair restart.
No executor may write `restart_stage` or `attempted_technique`: the controller
adds them from independent decisions. There is no `required_lemma`, diagnostic,
`construction_task` or old structural-plan progress channel.

An accepted stage is locked through all later failures and source-scope
repairs. A continuation carries its exact reviewed event forward; it must
never execute, reconstruct, reclassify or re-review that stage. Reopening a
prior accepted stage requires two independent `accepted_stage_revocation`
records naming the same stage and citing a concrete defect in its own result.

For `failed`, add `failure: {field, reason, retained_prefix, evidence}`. Only an
authorized stage 6 failure adds `attempt` and binds `artifact.authorization_binding`.
An incomplete stage may submit a partial artifact, but stage boundaries still
apply. A failed Stage 1–5 submission is an execution defect and must be rejected
for repair; it can never be accepted as a completed reasoning result. A failed
Stage 6 construction may be preserved as attempt history, but does not advance
the proof and invalidates its authorization. “No productive aspect/technique” is
never a proof conclusion or valid stopping point.

## Residual is the mathematical object

At every stage, use the exact node residual and its accepted facts as the entire
mathematical input. Enumerate its conjuncts, binders, constructor branches,
witnesses, types/domains, supports, realizations and links to the fixed current
object. The register indexes structure already present in this residual; it
does not replace its decomposition. Bound witnesses are not detached arbitrary
objects. Do not widen their quantifiers or add a fresh context, graph, partition
or auxiliary object unless a reviewed Stage 5 authorization and Stage 6 proof
construct it from the incoming residual.

## Stage artifacts

### 1. Prior-use ledger

`prior_uses` is one compact table. Rows are `{id, property_ids, structure, move,
effect_on_residual, evidence}`. Property IDs come from the shared register. Each
row names the specific structure already used, the move that used it, and the
restriction it imposed on this residual. `coverage_evidence` locates the short
branch excerpt used for the list. Empty `prior_uses` is allowed only when the
excerpt supports that no earlier move applies. This stage trusts all proof
obligations before the node; it does not re-prove ancestors, decompose the
residual, search the repository, or audit unrelated sources. Keep the table to
a few pages.

### 2. Inventory

`residual_components` is the exact component map, with entries `{id, kind,
exact_statement, binders_and_domains, current_object_link, evidence}`. Cover the
actual clauses, binders, witnesses and branches in the retained residual. Do not
add arbitrary objects or re-audit the prior proof.

`coordinates`: exactly one `{property_id, status, reason, evidence}` for every
registered coordinate. Status is present, absent, unresolved or not_applicable.

`aspects`: entries `{id, property_ids, statement, observable, object, prior_use,
unused_difference, facts, status, evidence}`. Property IDs must
be present; listed facts must be usable owner-local fact IDs. Use `facts: []`
when the aspect is supplied directly by the incoming residual; do not invent
an owner fact for it. Status is accounted,
partly_accounted or unaccounted. IDs stay stable across comparisons and retries.
Every present coordinate needs an aspect or accepted prior account.

`interactions`: entries `{aspect_ids, restriction, evidence}`, including relevant
higher-order interactions. `interaction_coverage_evidence` explains coverage.
`component_classifications` has exactly one entry per Stage 2 component:
`{component_id, classification, relation_to_fixed_objects, exhaustiveness,
remaining_obligation, cases, evidence}`. `cases` are nonempty entries
`{id, condition, established_consequence, status, evidence}`, where status is
forced, excluded, open or unresolved. Case conditions must be jointly exhaustive
for the component; every quantified witness relation that can change the proof
obligation is represented. No techniques, selected moves or construction
proposals belong in this artifact.

### 3. Structural conflict

`comparisons`: exactly one per eligible unused aspect, with `{aspect_id,
opposing_accounts, structural_conflict, consequence, affected_residual_clause,
structural_status, evidence}`. Opposing account IDs refer to Stage 1.
`structural_status` is `target_relevant` or `unsupported`. The selected aspect
must have an evidenced target-relevant inference and nonempty opposing accounts.
Stage 3 classifies structural relevance; it does not claim closure or significant
quantitative reduction.

`ranking`: all eligible aspect IDs in order. `selected_aspect` is first;
`strongest_alternative` is second or null if none. `selection_reason`, `evidence`
justify the comparison. `residual_case_assessments` has one row per eligible
aspect, each with `case_groups`. Every group has `case_ids` and
`{structural_conflict, consequence, affected_residual_clause, structural_status,
evidence}`. `structural_status` is `target_relevant` or `unsupported`. The groups
partition all Stage 2 case IDs for that aspect. Group cases only when the same
inference applies uniformly; do not expand a large aspect-by-case grid into
repetitive prose. Ranking is semantic reasoning, not a numerical score. No
target-relevant structure is a defect requiring repair, never a valid endpoint.

The selected aspect also has `structural_opportunity` with `bound_witness`,
`prior_account_ids`, `shared_structure`, `retained_restrictions`, `deduction`,
`affected_residual_clause`, `stage4_opportunity`, `weakest_case_id`,
`weakest_case_analysis`, and `evidence`. It identifies the exact overlap with
Stage 1 accounting on the same object and proves a new structural signature or
restriction on the actual target-defect witness and a named target-defect clause
or freedom. `stage4_opportunity` states what this handle gives Stage 4 to try to
exploit. It is not a reduction certificate: it need not name a move, quantify a
payoff, supply a before/after comparison, or identify a final consumer. Those
are required in Stage 4. An auxiliary restriction with no implication for a
target-defect clause does not qualify. Do not submit Stage 4 payoff fields such
as `expected_outcome`, `direct_consumer`, `before`, `after`, or
`payoff_composition` in this artifact; the validator rejects them. No move is
chosen.

### 3b. Checked structure on the incoming residual

`residual_binding` is the digest of the exact pre-3b node residual and retained
facts. `selected_aspect` matches the accepted Stage 3 choice.
`incoming_residual_key` identifies the ledger key carrying that exact residual;
`lean_inputs` lists only the residual key and other inherited keys actually
read by the owner-local proof. `ledger_row` names the row that eliminates the
residual's bound tuple and publishes the selected structure. `structure_fact_id`,
`structure_key`, `lean_declaration`, `bound_witness`, and `source_path` identify
one new derived fact on this node. `bound_witness` is copied exactly from the
accepted Stage 3 opportunity. `claim_projections` maps **every** selected
structural implication to `{claim, declaration, residual_clause, bound_witness,
evidence}`; each projection is a consequence of that one published fact on the
same bound tuple. `weakest_case_id` matches the accepted Stage 3 weakest case;
`evidence` locates the exact Lean statement and ledger row. The controller runs
the locked Lean check before independent review. The stage preserves the
incoming residual and all history. It does not choose a move or claim a
reduction. Earlier accepted inventories are neither repeated nor audited here.

### 4. Technique catalogue

`aspect_id`, `coverage_evidence`, and `techniques`: entries `{id, technique_id,
status, reason, evidence}`. Cover every registered family attached to the chosen
aspect; include other relevant textbook moves. Give variants distinct IDs.
`structure_fact_id` and `structure_binding` name the exact accepted Stage 3b
publication. Status is candidate, excluded, or missing_prerequisite. A candidate also supplies
`theorem`, `operation`, `object`, `output`, `dependency_step`, `history_comparison`,
`residual_case_ids`, `structure_fact_id`, and `prerequisites` entries
`{statement, witness_binding, derivation, evidence}`. Exact
quantifiers and domains belong in these statements. Every candidate names the
classified cases it actually covers and uses only their residual-bound objects.
The catalogue also supplies `selected_candidate_id`, `selection_reason`,
`strongest_alternative`, and `selection_evidence`. The selected candidate has
`payoff_composition` with `selected_output`, `prior_restrictions`,
`retained_estimates`, `derivation`, `resulting_conflict_or_bound`, `before`,
`after`, `weakest_case`, `direct_consumer`, and `evidence`. Show the exact
conditional calculation or structural incompatibility that combines the move's
output with previously established estimates and restrictions. The selected
move must already have a strict payoff on the full bound residual before Stage 5.
No trial construction belongs here.

### 5. Authorization

`residual_binding`: assignment.residual_binding. `aspect_id`, `candidate_id`,
`technique_id`, `operation`, `object`, `output` match the accepted catalogue.
`candidate_id` must equal Stage 4's `selected_candidate_id`.
Also `consumer`, `dependency_test`, `dependency_evidence`, `comparison`,
`comparison_evidence`, `weakest_outcome`, `coverage_evidence`, `payoff_evidence`,
`history_evidence`, `outcomes`.

Each outcome has `{case, condition, consumer, kind, evidence}`. `kind` permits
ONLY closure or significant_reduction. It also has `residual_case_ids`; the union
of these lists must cover every Stage 2 residual case. Closure additionally has `mechanism`
(constraint, compression, quantity) and `contradiction`. A significant reduction
additionally has `object`, `before`, `after`, `excluded_structure`, `significance`,
`remaining_residual`, `continuation`, `measure`, `reduction_kind` (structural_exclusion,
quantitative_restriction, well_founded_descent), and `strictness_evidence`.

Prove the implication from the specified output to this actual payoff; do not
assume the output is already constructed. A prerequisite lemma or a paid field
alone is insufficient. Every complementary outcome needs a productive payoff.
A repeated failed technique additionally needs `retry: {kind, change, evidence}`;
kind is new_proved_premise or corrected_construction, with substantive new proof.
A different technique may use the same still-unused property after review.

### 6. Construction

`authorization_binding`: assignment.construction_authorization.binding.
`output_evidence`, `application_evidence`, `preservation_evidence`, `outcomes`.
Each outcome has `{case, kind, evidence, application_evidence}`, matching the
approved case and kind. A reduction also names `child`, an actual node with the
exact authorized surviving residual and exclusion. Reuse unaffected previously
verified children when repairing a later decision; do not duplicate their proofs.
Every retained child must remain covered. All new edges require refinement,
coverage, locality, significant reduction and productive continuation.

### 7. Outcomes

`construction_binding`: digest of the accepted Stage 6 event.
`discharges`: map of every case name to actual complete discharge evidence IDs.
`account_updates` and `evidence`: proof of all structural and numerical updates.
The controller executes children before accepting their parent's outcome stage.

### 8. Verification

`outcome_binding`: digest of the accepted Stage 7 event. `statement_evidence`,
`implementation_evidence`, `wiring_evidence`, `artifact_evidence`.
Set `semantic_review` to the actual final audit evidence. Only the fully
verified root may set status complete. The controller runs locked checks and
required chain checks before both independent reviewers certify this stage.

## Review-directed repair

Each reviewer supplies `repair_stage` naming the defective decision and
`accepted_stage_revocation: null` for a current-stage repair. An earlier-stage
request requires `accepted_stage_revocation: {stage, defect, evidence}` with
the same stage number as `repair_stage`. A completed-stage acceptance uses its
own stage. Construction failure must return to Stage 5 or earlier, with an
evidenced revocation of the earlier authorization or reasoning stage.
The controller preserves earlier accepted artifacts and invalidates this stage
and all dependent approvals. Historical artifacts, failures and evidence are never
erased. Facts do not become accounted merely because a technique failed.
