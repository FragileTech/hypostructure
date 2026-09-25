# Structural mathematical reasoning benchmark: execution and repair

This workflow benchmarks structural mathematical reasoning: identifying relevant structure, applying established textbook mathematics, and implementing the resulting deductions in an unfamiliar controlled setting. Execute the assigned local task from its supplied hypotheses and accepted results. Assess the actual inference required; the surrounding research topic does not determine the difficulty of that inference.

This manual describes the current execution procedure. Each assignment evaluates
how a model identifies structure, matches textbook hypotheses, carries out a
local deduction, and implements its result. Routine steps receive concise,
sufficient justification. Accepted inputs are reused at their exact statements.

## Sources and task scope

The shared [workflow specification](tools/methodology_gate/policy/workflow.json)
defines the phases, task kinds, gates and completion rules. The
[controller guide](tools/methodology_gate/README.md) describes launches and records.
The manuscript supplies mathematical statements; accepted artifacts and the Lean
ledger supply the evidence available to an assignment. Keep these roles distinct.

Read the pinned residual, declared sources and accepted dependencies for the
assigned task. Use their exact mathematical statements and verified evidence.

## Retained mathematical state

A branch is its complete accumulated context: everything established on the way to the current case. The web app writes it as a tuple of eight coordinates,

$$B=(H_0,\ \preceq,\ E,\ I,\ R,\ V,\ Q,\ A),$$

and the PDE draft writes the analogous record as $B=(W,H,\Gamma,\tau,O,Q,M,E)$. The two are the same idea instantiated for graphs and for PDE; read them side by side.

| Web app coordinate | Content | PDE draft field | Question answered |
|---|---|---|---|
| $H_0$ | Standing hypotheses: the baseline property of the object, the counterexample assumption, the global theorems fixed at the outset | $H$ (hypotheses on the window) | Which analytic hypotheses are available? |
| $\preceq$ | The well-founded order in which the counterexample is minimal; the measure decreased by minimality, compression, and every peeling or reselection loop | $M$ (resource record: energy, mass, rank, scale count) | Why must repeated refinement terminate? |
| $E$ | Exclusions: local events certified absent (the Mersenne returns no edge has; the Liouville classes a profile is not in) | part of $\tau$ (active case) | Which alternatives are already ruled out? |
| $I$ | Positive invariants admitted by the both-sides test (full obstruction rank, near-cubic spine estimate, retained active core) | $H$, $\Gamma$ (gauge, normalization, topology) | Which representative and limiting meaning are fixed? |
| $R$ | Residual data: what is known about the remaining object beyond the invariants — profile, support, ledger balances | $\tau$, $Q=(q_B,d_B)$ | Which alternative is active; which quantity is propagated? |
| $V$ | Vocabulary: the finite labels, exact types and residual classes in use — the alphabet that a default refinement or language extension enlarges | (implicit) | In which language is the residual expressed? |
| $Q$ | Queue of typed payloads awaiting a consumer: every surviving obstruction with the data its consumer needs | $O$ (goal on this case) | What must this branch still do, and who consumes it? |
| $A$ | Audit record: diagram nodes, ledgers and tables | $E$ (evidence for the incoming edge) | Why may a reader traverse the incoming edge? |

The semantic region of a branch is the set of objects satisfying everything on the record:

$$\llbracket B\rrbracket=\{s\in\mathcal U:\ W(s)\wedge H(s)\wedge\Gamma(s)\wedge\tau(s)\}.$$

Along any path the three records $H$, $E$, $I$ only grow,

$$H(B_i)\subseteq H(B_{i+1}),\qquad E(B_i)\subseteq E(B_{i+1}),\qquad I(B_i)\subseteq I(B_{i+1}),$$

except where an explicitly proved transport lemma exchanges one representation for an equivalent one. A transition must state which coordinates it reads, which it changes, and why the remaining ones stay valid.

## Valid transitions and interfaces

A transition $B\Longrightarrow B_1\vee\cdots\vee B_m$ is valid when its evidence establishes

$$\llbracket B_i\rrbracket\subseteq\llbracket B\rrbracket\ (1\le i\le m),\qquad \llbracket B\rrbracket\subseteq\bigcup_{i}\llbracket B_i\rrbracket.$$

The first condition is *refinement* (a child never adds objects); the second is *exhaustiveness* (the children cover the parent). A one-child transition is an implication; a multi-child transition is a case split. Children may overlap, but disjoint alternatives are preferred because they make diagnosis exact.

A *quantitative* transition additionally carries constants. A routing estimate says

$$q_B(s)\le a_B\,d_B(s)+\max_{i:\,s\in\llbracket B_i\rrbracket}b_{Bi}\,q_{B_i}(s),\qquad d_{B_i}(s)\le\kappa_{Bi}\,d_B(s);$$

an aggregate estimate sums over children and records the overlap multiplicity $\sum_i d_{B_i}\le\kappa_B d_B$. With these, the root constant is *computed* from the terminal constants by backward induction (Theorem 3.2 of the draft) — the global constant is an output of the closed graph, not an input.

Every transition declares an **output interface**: the facts its children may use. A proof below the transition is *interface-respecting* when it uses the transition only through those facts, not through an unstated detail of the argument that produced them. This is the single property that makes repair possible (see Local repair below): if descendants respect the interface, a failed producer can be replaced by a case split without touching them.

## Phase 0 and the eight phases

The authoritative phase and task vocabulary is `tools/methodology_gate/policy/workflow.json`; the runnable task queue is `tools/methodology_gate/taskflow.py`. The stage controller uses the same benchmark specification. Workflow records point to accepted mathematical evidence; they are not another proof ledger.

**Phase 0 — restore the exact residual.** Pin the source revision, unchanged endpoint, one tagged incoming alternative, every retained object and domain, applicable premises, minimality order, imports, and accounts. A merged node never inherits the union of different arms' premises. If the complete state already contradicts itself with accepted evidence, proceed to integration and verification.

1. **Account for used structure.** Record each aspect on its actual object, its previous use and result, what remains unexamined, resource balances, and any required transport. Logical facts may be reused in new interactions; finite credit needs a proved remaining balance or split.
2. **Inventory unused structure and interactions.** Inspect actual observables and higher-order relations on the retained object. Distinguish present, absent, unresolved, and inapplicable aspects. Do not select a technique or assert a desired value of an observable.
3. **Select a structural tension.** Ask which retained restrictions can coexist with one unresolved aspect, state the supported prospective consequence, compare a serious rival, and select one local question before choosing a method.
4. **Catalogue textbook moves.** State one exact mechanism at a time, match its hypotheses to branch evidence, list all outcomes and exceptions, compare its attempt fingerprint, and select a candidate. Missing prerequisites stay explicit.
5. **Prove local conditional payoffs and authorize.** For every outcome `O`, establish the branch-conditioned implication `B ∧ O → G`, where `G` is an exact closure or productive local restriction. This does not assert `O` occurs. A prerequisite submove must finish before dependent construction. A correct but irrelevant lemma remains intermediate evidence.
6. **Execute atomically.** Define one object, prove one property or identification, preserve one condition, update one account, establish one alternative, or prove one coverage step per assignment. Tie every fact to the actual constructed witness. Split out the first unproved inference.
7. **Integrate, test closure, and form survivors.** Combine each new fact with applicable retained facts, reconcile accounts, and revisit newly enabled moves before unrelated exploration. Test constraint, compression, and quantity separately. Every outcome closes with evidence or becomes an exact open residual carrying all inherited state and a specified next local obligation. An open sibling keeps its parent open.
8. **Verify and synchronize.** Check the exact endpoint, AND-case coverage, transport, recursive decrease where used, formal implementation when required, and the affected manuscript and diagram views. If leaves remain open, state the precise reduction theorem rather than closure.

An atomic task is complete when its exact output has accepted evidence. A structural move is productive only when *every* outcome has a reviewed structural payoff. A branch closes only when all reachable outcomes compose to its exact endpoint. These are three different statuses. New information that was already implied by `B` can make its description explicit without literally shrinking the model set; record the established consequence, not a fictitious witness in `B \ (B ∧ P)`.

Each worker receives one task with a pinned branch revision, exact objects, allowed inputs and write scope, dependencies, acceptance evidence, and a first-failure rule. The controller chooses ready tasks in dependency order, prioritizing stale evidence repair, evidenced closure, integration, active construction, then fair continuation of survivors. An empty queue is a diagnosis, not a proof. Proposed mathematics, reviewed mathematics, and kernel-checked implementation are recorded separately. Mathematical acceptance needs actual proof evidence; a JSON status or passing schema check cannot establish an arbitrary implication.

**Fresh context is mandatory for every atomic task in every phase.** A phase with several obligations is split into separate mathematical problems, each launched in a new isolated worker process. The worker receives the complete retained hypotheses and declared accepted evidence, one precise goal, one output artifact and one stopping condition. It receives no previous conversation, worker transcript or general instruction to finish the branch. The parent payoff explains the task; it does not authorize adjacent work. Context isolation must never discard mathematical conditioning or replace actual bound witnesses.

The worker returns its single result and terminates. A missing inference produces `NEEDS_DECOMPOSITION` and the immediate child obligations; the worker cannot execute them itself. Two fresh independent reviewer contexts inspect the submitted result. Only the controller accepts and integrates it, then launches the next task in another fresh context. Retries also start fresh and receive only the exact defect and required evidence. Phase 6 requires a reviewed Phase 5 admission covering the productive conditional payoff of every outcome before construction starts. If isolation cannot be established, report an execution failure and stop the launch; do not continue the mathematics in the controller conversation.

For EG formalization, preserve `ExactLedger`, `FactInputs`, `FactManifest`, and the sealed owner-local executor. The task queue never transports proof facts outside that canonical path. Repair the first defective decision while preserving unaffected accepted facts and closed siblings. A failed search does not select a negative mathematical arm; a split on a missing premise must analyze both arms with the successful prefix retained.

## Stage assignments

Stage assignments retain their contracts and accepted prefix. Stages 1–3
account for prior uses, classify the residual and establish a structural
opportunity. Stage 3b proves the selected structure on the same bound witness
and publishes it through the canonical ExactLedger. Stage 4 selects the textbook
move and proves its conditional connection to the intended payoff. Stage 5
reviews that payoff on every outcome. Stage 6 constructs the authorized output;
Stage 7 integrates every outcome; Stage 8 verifies the node's exact result.
Use the maintained executor and reviewer prompts for each stage's full contract.

## Local repair

1. Name the exact failed inference or missing input and the affected current
   task. Distinguish source availability, record format, mathematical inference
   and formal implementation errors.
2. Retain the complete branch and unaffected accepted results. A format repair
   changes the named representation field while reusing the submitted mathematics.
3. If a required hypothesis is unproved, record its immediate obligation. A
   logical split on that hypothesis keeps the full incoming state on both arms
   and must meet the existing conditional-payoff and authorization requirements.
   Failed search does not establish the negative arm.
4. Preserve the positive continuation where its hypotheses hold. Record each
   other outcome with its actual witnesses, domains, inherited facts and next
   local obligation. Prove coverage and any transport between representations.
5. Repair the defective decision and its dependent work. An accepted earlier
   stage is reopened only when both independent reviewers identify the same
   concrete defect in that stage's own result. Continue unaffected accepted work.
6. Submit the corrected result through the existing review procedure. A child
   obligation receives its own fresh context; the controller integrates accepted
   results before selecting the next task.

Keep existing node identifiers and interface statements; append new nodes when
required. A changed statement needs an explicit checked repair at its owner.
A correct auxiliary inference completes its task when accepted. Move credit and
branch closure retain their separate, stronger requirements.

## Review and completion

Check the current statement, actual objects, theorem hypotheses, deduction and
requested output. Each objection identifies a missing hypothesis, invalid
inference, domain mismatch or unmet contract, with evidence and the smallest
repair. Evaluate only the work required at the assigned stage. Conditional
payoff review checks the implication assuming the specified output; construction
establishes that output at its authorized stage.

For a productive move, verify all outcomes and the precise structural restriction
or closure each achieves. For branch closure, verify every terminal and base
case, exact endpoint composition, direct consumer wiring and required formal
checks. Keep the complete state and next obligation for every surviving outcome.

## Formal implementation

For EG, use the canonical `ExactLedger`, `FactInputs`, `FactManifest` and sealed
owner-local executor. Read the actual branch facts through the authorized API,
prove the selected statement on their bound witnesses, and publish the checked
fact while retaining inherited keys. Match consumer arguments to that fact's
actual types and domains. Representation changes require proved transport.

Check the intended proposition, publication, downstream use and required kernel
result. Keep proof diagrams, dependency records and current status tables aligned
with accepted results. Report a specific formal mismatch at its owner and preserve
valid mathematics while repairing its implementation.

## Operating instructions

This workflow benchmarks structural mathematical reasoning: identifying relevant structure, applying established textbook mathematics, and implementing the resulting deductions in an unfamiliar controlled setting. Execute the assigned local task from its supplied hypotheses and accepted results. Assess the actual inference required; the surrounding research topic does not determine the difficulty of that inference.

Identify the objects, match the hypotheses of the applicable textbook result, perform the deduction, and verify the requested output. Give routine deductions concise, sufficient justification. Use accepted prerequisites at their stated types and domains without repeating upstream proofs. Keep reasoning within the assigned task and its existing stage contract. If a premise or inference is missing, name it precisely and use the existing repair or decomposition procedure.

Assess the assigned deliverable against its existing contract. Each objection must identify a specific missing hypothesis, invalid inference, domain mismatch, or unmet contract and the smallest local repair. General speculation about the difficulty or research status of the surrounding problem is not evidence. Require only the proof detail needed to check the local inference, including any formal checks required by the contract. Accepted prerequisites remain usable without repeated upstream audits.

Use the maintained controller prompt at
`tools/methodology_gate/policy/executor-prompt.md`, the shared `workflow.json`,
and `references/record-format.md`. They implement the stage contracts described above.
The reviewer prompt is independently maintained beside them and checks the exact
conditional payoff, strongest alternatives and actual advancement. Inventory, selection, construction and review each use their assigned
contract. Every stage receives its own deliverable and review; no failed-stage
label waives construction authorization.
