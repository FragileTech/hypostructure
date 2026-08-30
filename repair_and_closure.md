# Repair and closure in a structural-exhaustion proof

> **Methodology and repair-history document.** This file contains diagnoses, rejected moves, and
> proposed continuations; it is not the live Lean status authority. In particular, proposals after
> `[182]` and the candidate closures discussed for `[181]` are not implemented merely because they
> appear here. Current implementation status is recorded in
> [`Assembly_node_audit.md`](Assembly_node_audit.md), with the 2026-08-30 frontier summarized in
> [`EG_LEAN_COMPLIANCE_REMAINING.md`](EG_LEAN_COMPLIANCE_REMAINING.md).

An operating manual for repairing a structural-exhaustion proof when a step fails, and for choosing and executing the mathematical move that closes the residual branch the repair creates. It is written for two readers at once: a mathematician who has to decide whether a branch is closed, and a language model that has to propose the next step without losing the state.

Nothing here is new. Every rule is taken from the live sources in this repository, and every example is taken from the Erdős–Gyárfás manuscript or the Navier–Stokes and Stokes developments. The purpose of this document is to put the rules, the decision procedure, and the worked examples in one place and in the order in which they are actually used.

| Source | What it supplies | Where |
|---|---|---|
| The web app methodology page | The branch tuple, the both-sides test, the move table, the eight LLM failure modes, the repair rule, three worked repairs | `web/frontend/src/components/MethodologySection.tsx` (rendered at the site landing page, "The methodology") |
| The PDE methodology draft | The formal definitions (branch state, valid transition, exhausted graph), the closure theorems, the branch-preserving repair theorem, the Stokes instantiation | `to_formalize/llm_auditable_proof_architecture_draft.tex` |
| The Erdős–Gyárfás manuscript | The repairs actually performed (nodes [125]–[182]) and the lemmas that closed them | `to_formalize/erdos_64_proof.tex` |

The reference manual for the move vocabulary is `to_formalize/branch_closure_methodology_extended.tex` (tactics CT1–CT17, certificate alphabet C1–C5); the general methodology paper is `to_formalize/structural_exhaustion.tex`.

---

## Contents

1. [How to read this document and the proof](#1-how-to-read-this-document-and-the-proof)
2. [The unit of work is a branch, not a lemma](#2-the-unit-of-work-is-a-branch-not-a-lemma)
3. [What counts as a valid step](#3-what-counts-as-a-valid-step)
4. [The repair protocol, step by step](#4-the-repair-protocol-step-by-step)
5. [Choosing the move that closes the new residual](#5-choosing-the-move-that-closes-the-new-residual)
6. [Worked repairs](#6-worked-repairs)
7. [Closing an open node: the protocol applied to [182]](#7-closing-an-open-node-the-protocol-applied-to-182)
8. [Closing [181]: the protocol applied to the peeled target-defect demand residual](#8-closing-181-the-protocol-applied-to-the-peeled-target-defect-demand-residual)
9. [Anti-patterns and failure modes](#9-anti-patterns-and-failure-modes)
10. [Recording the repair](#10-recording-the-repair)
11. [The same discipline in Lean](#11-the-same-discipline-in-lean)
12. [Checklists](#12-checklists)
13. [Operating prompt for the executor](#13-operating-prompt-for-the-executor)
14. [Glossary and source map](#14-glossary-and-source-map)

---

## 1. How to read this document and the proof

### 1.1 Three authorities, three namespaces

Before repairing anything, fix what counts as evidence.

- **Mathematics.** The manuscript (`to_formalize/erdos_64_proof.tex` for Erdős–Gyárfás) is the sole authority for statements, hypotheses, alternatives, order of steps, and terminal behaviour.
- **Implementation.** Live Lean declaration types, bodies, key lists, call sites, and build results are the sole authority for what has been machine-checked. Comments, docstrings and `-- EG-NODE` annotations are search locators, never evidence.
- **Status.** The audit tables (`Assembly_node_audit.md`) are the sole authority for current implementation status, and only the tables — not their prose, and not older rows contradicted by the dated correction ledger.

The proof uses three integer namespaces that must never be confused (`rem:two-distinct-integer-scales` in the manuscript):

- `[k]` — a **diagram node**, a state or decision in the proof-dependency diagram. Nodes run [1]–[182] in the Erdős–Gyárfás proof.
- `inv N` — a **constraint-ledger invariant** (1–44), a fact with a place of introduction and places of consumption.
- Item numbers in the dependency table — bookkeeping rows, neither nodes nor invariants.

A `\label` such as `lem:exact-collision-test` is the stable identifier of a mathematical statement; a node number is the stable identifier of a position in the graph. A lemma can serve several nodes and a node can cite several lemmas.

### 1.2 What a structural-exhaustion proof is

The proof of a theorem $A(s)\Rightarrow T(s)$ is a finite rooted directed acyclic graph. Each node is a *branch state*; each edge is a *transition* that either proves a local estimate, refines the state, or splits it into exhaustive alternatives; each terminal proves the target on its region, usually by contradiction with the counterexample hypothesis. The graph is *structurally exhausted* when

1. the theorem hypothesis is contained in the root region,
2. every nonterminal node has a valid transition to all its children, and
3. every terminal has accepted evidence that its region satisfies $T$.

(Definition 2.4 of the PDE draft.) Soundness is then a two-line argument: route any $s$ with $A(s)$ from the root; exhaustiveness always gives a child containing $s$; finiteness and acyclicity give a terminal; the terminal gives $T(s)$.

Everything in this document follows from taking that picture literally. A failed step is not a hole in a linear argument; it is one node whose transition is not yet valid. The rest of the graph is untouched.

### 1.3 The adversary and the three currencies

The methodology views the minimal counterexample as an adversary that pays a cost every time it avoids the target. The proof settles the resulting account in one of three currencies (web app, "Philosophy"):

- **Compression.** The structure found admits a smaller object with the same relevant behaviour. Minimality forbids this.
- **Quantity.** The structure carries a numerical price — demands against capacities, deficits, entropy, rank. The proof tracks that price until the requirements exceed the budget.
- **Constraint.** One structural property is incompatible with the restrictions already recorded; the accumulated record leaves the object nothing to be.

When you choose a closing move (Section 5), you are choosing which currency the residual will be made to pay in.

---

## 2. The unit of work is a branch, not a lemma

### 2.1 The branch state

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

### 2.2 Why the separation matters

The PDE draft explains why the coordinates are kept apart: a bound can survive rescaling while a gauge choice does not; weak convergence in the energy space does not give the strong convergence a nonlinear term needs; a pressure statement is meaningful only modulo functions of time; a defect extraction may preserve the hypotheses yet consume critical mass or lower a scale rank. Recording each choice prevents a downstream step from consuming a stronger statement or more resource than its parent produced. In the graph proof the same happens with surplus, deficiency, entropy, rank, and boundary mass: these are distinct currencies unless a proved interface converts one into another.

### 2.3 Reading a branch before touching it

Treating a structural-exhaustion proof as a linear proof produces the following reading errors:

1. **Wrong semantic unit.** The unit is *incoming ledger state + branch condition + local lemma*, not the lemma statement. Do not ask whether a fact holds in every graph when the proof uses it only after a diamond selected the branch on which it holds.
2. **Erased routed residuals.** "The desired property fails" is not "the proof has failed." In this proof, failure usually *creates the next residual object*: a minimal overlap obstruction, a cold bounded configuration, a target-defect ledger entry, a decorated Type B handoff, a route-8 support.
3. **Dependencies inferred from citations.** A later theorem can be named as the *closure interface* for a residual without being an upstream hypothesis of the node that creates the residual. Converting routing references into reverse dependency arrows produces phantom circularities. Follow the directed graph and the "Requires" column, not the prose.
4. **Ignored conjunctions.** At node [37] a quotient is both context-universal (certified on the branch) and distinguished by a compatible context (the branch condition). Each conjunct alone is harmless; together they are an immediate contradiction. Always read the whole record.
5. **Anchoring on a first verdict.** After a methodological correction, rebuild from node [1]; do not keep the conclusion and look for replacement objections.

Positively: before proposing a repair at node $[k]$, write down $\llbracket B_{k-1}\rrbracket$ explicitly — the invariants established at earlier-or-equal nodes (the "Requires" cells), the exclusions, the active case predicate, and the residual data. Every later question is asked relative to that set.

---

## 3. What counts as a valid step

### 3.1 Valid transitions

A transition $B\Longrightarrow B_1\vee\cdots\vee B_m$ is valid when its evidence establishes

$$\llbracket B_i\rrbracket\subseteq\llbracket B\rrbracket\ (1\le i\le m),\qquad \llbracket B\rrbracket\subseteq\bigcup_{i}\llbracket B_i\rrbracket.$$

The first condition is *refinement* (a child never adds objects); the second is *exhaustiveness* (the children cover the parent). A one-child transition is an implication; a multi-child transition is a case split. Children may overlap, but disjoint alternatives are preferred because they make diagnosis exact.

A *quantitative* transition additionally carries constants. A routing estimate says

$$q_B(s)\le a_B\,d_B(s)+\max_{i:\,s\in\llbracket B_i\rrbracket}b_{Bi}\,q_{B_i}(s),\qquad d_{B_i}(s)\le\kappa_{Bi}\,d_B(s);$$

an aggregate estimate sums over children and records the overlap multiplicity $\sum_i d_{B_i}\le\kappa_B d_B$. With these, the root constant is *computed* from the terminal constants by backward induction (Theorem 3.2 of the draft) — the global constant is an output of the closed graph, not an input.

### 3.2 Output interfaces

Every transition declares an **output interface**: the facts its children may use. A proof below the transition is *interface-respecting* when it uses the transition only through those facts, not through an unstated detail of the argument that produced them. This is the single property that makes repair possible (Section 4): if descendants respect the interface, a failed producer can be replaced by a case split without touching them.

### 3.3 Kinds of transitions

The draft lists five recurring PDE transitions; the graph proof uses the same five under other names.

| Kind | PDE reading | Graph reading |
|---|---|---|
| Localization | Nested cylinders or frequency windows; every cutoff error recorded | Restrict to a connected admissible piece with negative net charge (node [57]) |
| Decomposition | Split velocity, pressure, profiles, scales, defects into named components; keep the remainder | Split the packing into hot/cold windows; split pairs into free/blocked |
| Estimate | Prove a local inequality with its constant, data dependence, and overlap multiplicity | A charging scheme with a no-overcount lemma |
| Compactness / rigidity | Change the state only in the topology actually obtained; record what transports to the limit | Finite-state repeat, exact-type comparison, minimality replacement |
| Decision | Exhaustive positive and negative cases; the negative case identifies a defect or a resource-decreasing successor | A diamond |

For each node a reader should be able to answer eight questions: what case is active; what inputs are available; which target quantity is controlled; which resource is retained or consumed; what new fact is proved; which result proves it; which alternatives leave the node; and where each alternative closes.

### 3.4 Admission: the both-sides test

A predicate $P$ may be introduced as a diamond only when *both* $P$ and $\neg P$ produce useful consequences:

> The positive side must feed an account, an estimate or a closure mechanism; the negative side must force something definite: a bounded residual, a first-failure witness, a structural obstruction, or a route to a named consumer. A predicate whose failure has no declared consequence is simply not part of the proof, however natural it may look.

In the repair setting the test is met almost automatically on the positive side (the old argument is the consumer of $P$), so the whole burden is on $\neg P$: it must be a *typed* fact that some move can consume. Section 5 is about finding that move.

### 3.5 Fixed inputs, then local steps only

The set of imported global theorems is fixed before the first step and never grows. Each is stated exactly, cited, and recorded in the dependency table as "imported" (for Erdős–Gyárfás: the Hegde–Sandeep–Shashank $P_{13}$-free theorem, and textbook facts cited at the point of use). Everything else is "proved here," drawn from the move vocabulary. A branch that would need a new global theorem to close is not closed; it is a defect, repaired by refining the case structure until it closes locally.

### 3.6 Leaf totality

The safety condition on the whole graph: every outcome a step returns lies either in a declared closure class or in the domain of another registered step. A branch without a consumer is caught by the architecture before anyone assesses the mathematics. This is what terminals, branch labels and "continue at [n]" arrows in the diagrams are for, and why an "open" node must still be a *named* node with a *typed* residual ([181], [182]) rather than a missing arrow.

### 3.7 One iteration of the method

From a state and its queue:

1. **Propose** an invariant, case split, budget, label, local test, exchange or candidate lemma.
2. **Admit** it only if both outcomes are productive, the resources it needs are present, and every surviving case has a declared route. No new global result enters here.
3. **Select** an admitted move whose prerequisites are in the current state or can be synthesised from it.
4. **Execute**: prove, review, or compute the local obligations *before* the proof state changes.
5. **Route**: close whatever closes; emit every surviving obstruction as a typed residual with a named consumer.
6. **Record** the branch tree, the invariant and exclusion ledgers, the dependencies and the residual queue.

A repair is one iteration of this loop, entered at step 1 with a very specific proposal: the predicate the failed step silently used.

---

## 4. The repair protocol, step by step

### 4.1 The rule

The web app states the rule once, and it is always the same:

> $H$ becomes a test at the step that used it. On the side where $H$ holds, the finished argument survives verbatim, now with its hypothesis stated. On the other side a new branch opens: it inherits the whole ledger accumulated up to that step, records $\neg H$ as one more positive fact about the counterexample, and is analysed on its own, with tools suited to $\neg H$, until it closes or routes into a row that is already closed. Existing step numbers are never reassigned; new steps are appended after the last existing one. Downstream, a consumer continues to cite the same interface theorem. Its statement is preserved while its proof routes through the new branch, so earlier results remain valid. Until the new branch closes, one has a precise weaker theorem: everything holds except on the named class where $\neg H$.

Diagrammatically:

```
BEFORE   [k-1] state ──► [k] step S (silently assumes H) ──► [k+1] ──► … ──► [m] closure

AFTER    [k-1] state ──► ⟨[k] does H hold?⟩ ──yes──► [k+1] step S (kept; H now stated) ──► … ──► [m] closure
                                   │                                                    (same statement, same citation)
                                   no: ¬H recorded
                                   ▼
                          [N+1] inherited ledger + ¬H
                                   │
                          [N+2] local analysis with tools suited to ¬H
                                   │
                          [N+3] closed on its own, or routed to an already-closed row
```

Solid: unchanged. Dashed (the `[N+i]` column): appended. The numbering itself records the history: in the Erdős–Gyárfás diagrams, [22]→[145], [19]→[125], [153]→[173] and [166]→[169] are repairs; contiguous continuations like [64]→[65] belong to the original design.

### 4.2 Why it is sound

The draft proves the rule as a theorem (Theorem 3.6, *branch-preserving repair*). Let $B$ be the last verified branch before a transition intended to establish $P$, and assume every descendant is interface-respecting. If the evidence for $P$ fails, replace the transition by

$$B\Longrightarrow B^+\vee B^-,\qquad \llbracket B^+\rrbracket=\llbracket B\rrbracket\cap\{P\},\quad \llbracket B^-\rrbracket=\llbracket B\rrbracket\cap\{\neg P\}.$$

Then (1) the replacement transition is valid independently of the failed evidence — the two sets refine $\llbracket B\rrbracket$ and cover it by excluded middle; (2) the entire former descendant graph remains valid, without alteration, below $B^+$, because on $B^+$ the predicate $P$ is part of the case definition, so every descendant receives exactly the interface it consumed; (3) the only new obligation is $B^-$; and (4) if the former graph closed $B^+$, the repaired graph satisfies the partial-closure inclusion

$$\{s:A(s)\wedge\neg T(s)\}\subseteq\bigcup_{L\ \text{open}}\llbracket L\rrbracket$$

with $B^-$ as its additional residual class (Theorem 3.5). Finally, *monotone closure* (Theorem 3.9): a repair partitions one region and leaves all other regions and their evidence unchanged, so closing or refining one open branch never reopens another.

This is why dependency information is diagnostic rather than destructive. It identifies the interface at which to insert the dichotomy and the continuation to attach to its positive arm; it does not mark a forward set of statements as invalid or treat a routed failure branch as an omitted case.

### 4.3 The ordered first-failure split

When the failed step asserted a conjunction $P=X_1\wedge\cdots\wedge X_m$, do not split on $P$ as a whole. Use the disjoint exhaustive split (Corollary 3.8):

$$\neg X_1,\qquad X_1\wedge\neg X_2,\qquad\ldots,\qquad X_1\wedge\cdots\wedge X_{m-1}\wedge\neg X_m,\qquad X_1\wedge\cdots\wedge X_m.$$

The former descendants sit on the last branch. Each new branch records *the first absent property*, which is far more information than "$\neg P$": it says which earlier properties are available and exactly which one fails. If some $X_i$ was already verified earlier, its branch is empty and closes immediately. `lem:scale-additivity` (node [170]) is this split in action: alternative (b) retains "the first failing coordinate" together with the scale, barrier, outside record, previously exposed prefix, and failing fibre — the manuscript adds explicitly that "no untyped negation of the additive conclusion is used as the input to node [172]."

### 4.4 The procedure

Given a step that has failed review, red-teaming, or formalization:

**Step 1 — Locate the first failing step, not the symptom.** Trace the objection upstream until you reach the earliest node whose transition is not valid on its literal incoming state. A failure found at [56] may be a hypothesis silently used at [19] (surplus regime) or at [22] (window realization). The Lean skill has the same rule: report the *first* failing label, not a node range or a downstream symptom.

**Step 2 — Name the hypothesis $H$ exactly.** Write the predicate the step used, as a proposition about the object on the current branch, with its quantifiers. Typical shapes: an independence assumption ("the coordinates are jointly realizable"), a regime condition ("$\sigma(G)=O(\sqrt n)$"), a boundary case ("$n\ge N_0$"), a compactness property absent from the state ("the witnesses stay in a fixed cylinder"). Then check whether $H$ is already on the record at an earlier-or-equal node. If it is, there is nothing to repair beyond citing it; if it is a conjunction, prepare the ordered split of 4.3.

**Step 3 — Insert the diamond.** The old step becomes "does $H$ hold?" Keep the continuation on the yes-arm *with $H$ stated as a hypothesis*. Keep every downstream interface theorem's *statement*; only its proof now routes through the diamond.

**Step 4 — Open $B^-$ with typed data.** The new branch inherits the entire ledger and adds $\neg H$ as a positive fact. Write down what $\neg H$ *gives*: a witness, a first failing coordinate, a fibre, a bounded object, a linear count, a repeated state, a vertex of high degree. This is the input to Section 5. A bare negation is not admissible as a branch state (failure mode "untyped residuals").

**Step 5 — Close or route $B^-$.** Apply Section 5. The outcome is one of: a terminal contradiction; a route into an already-closed row with a typed witness the row accepts; or an explicitly named open residual with its exact data (as at [181], [182]).

**Step 6 — Append and record.** Number the new nodes after the last existing one. Update the diagram, the dependency table (Failure route column), the constraint ledger, the per-lemma requirements table, the resilience appendix, and the audit table (Section 10). Check that no requirement is introduced at a strictly later node than where it is consumed.

**Step 7 — State the weaker theorem.** Until $B^-$ closes: "the theorem holds except on the class where $\neg H$," with that class described by its retained data. In the manuscript this is the sentence that accompanies node [181] and node [182].

### 4.5 Four kinds of repair

The repair is chosen to match the defect:

| Kind | What changes | Example |
|---|---|---|
| **Numerical** | Constants, enumerations or slack are recomputed; the branch structure is unchanged | `lem:curv-enum` gives $c_\Omega=\log_2(543958/111286)$; `rem:blocked-class-checks`(b) bounds the threshold at $1/81$ |
| **Structural** | A hypothesis, invariant, route, type or account is corrected *within the existing vocabulary* by a case split | The hot/cold split at [22]→[145]; the surplus test at [19]→[125]; the exact collision test at [173] |
| **Pattern-level** | A residual that keeps surviving is promoted to a reusable mechanism with a declared interface | Exit-(4) peeling `def:typeA-exit4-peeling` and the finite descent `lem:typeA-exit4-finite-descent` |
| **Language extension** | New descriptors and transitions for an obstruction the vocabulary cannot yet express | Navier–Stokes Type I: the branch state grew to carry observer witnesses and the "sparse branch" residual class entered the vocabulary |

Prefer the least invasive kind that actually matches the defect. A numerical repair applied to a structural defect hides the defect; a language extension applied to a numerical defect inflates the vocabulary.

### 4.6 Repairing an open node

An open node is a leaf that retains, as its residual, the exact negation of a lemma's *conclusion* on the lemma's retained input — "$\neg(\text{the five-way outcome exists})$," "$\neg\text{ConditionalFactorization}$." Retaining it is correct: it is honest, it keeps leaf totality, and it gives the precise weaker theorem of Step 7. But it is a temporary endpoint, and the both-sides test says why: its no-arm has no consumer. A diamond whose negative side is "the lemma does not hold" sits too high in the proof. The repair of an open node is therefore not "find a new idea"; it is to push the diamond down to the first *hypothesis* the lemma's proof consumes.

The procedure:

0. **Fix the object first (Rule 0, §4.8).** The residual is the data its producer typed — for [181], `def:typeA-peeled-demand-residual` (R1)–(R3); for [182], the three constructors of `PairUncoveredResidual`. Write it down verbatim before anything else, and work on it and nothing "equivalent" to it. Then **audit the consumer.** If the open node comes with an offered consumer ("closes if quantity $Z$ is small"), compute what the incoming ledger already forces about $Z$ before doing anything else. $Z$ is usually not free: ledgers define unpaid demand as demand minus paid, and no-overcount identities bound it from below. If the forced bound contradicts the needed bound, the consumer is vacuous, and the residual was produced by a diamond on the wrong hypothesis; relocate the work to that hypothesis (Section 8 does this for [181]).
1. **Write the intended proof as steps.** The manuscript usually says what the proof is meant to be ("identical to `lem:…` with $X$ in place of $Y$"; "by the same argument as node [k]"). Expand it into $X_1\wedge\cdots\wedge X_m$: each construction, each preservation claim, each cited lemma.
2. **Ask three questions of every step.**
   - *Ledger:* does it consume a fact that is on the branch where the original proof lived but not on *this* branch? (Cross-branch imports are the most common silent failure when a proof is transferred.)
   - *Object:* does it use a property of the original object that the transferred object lacks (paths versus connected subgraphs; 13 fixed offsets versus $s+1$ return offsets)?
   - *Fibre:* is it a construction whose output must stay in a class or conditional fibre (same $n$, $m$, profile, exposed coordinates)? That preservation is a separate obligation.
3. **The first step failing any question gets the diamond**, by the ordered first-failure split of 4.3. Its negation is typed by Section 5.1 — it always is, because a failed construction step hands you the reason it failed (a determined coordinate, a branching connector, an overlapping earlier support, a bounded system).
4. **Collapse shared obligations.** Several constructors of one open node usually reduce to the same one or two local lemmas (a "stays in the fibre" lemma, a cross-branch audit). Do the shared ones first.
5. **The old node keeps its number and becomes a decision;** its retained data is the input the new diamonds read; new nodes are appended after the last existing one.
6. **Stop when every no-arm has a consumer and every split passes §4.8.** Each diamond's arms must be properties of the residual's own object and must consume an inventory row; a diamond that only relocates the difficulty is removed, not kept. At that point the open node has been replaced by architecturally complete subgraph whose remaining content is a list of bounded local lemmas. Proving them is the Execute step; it may itself fail and recurse, but each recursion is on a smaller, typed object.

Section 7 performs this procedure on node [182] of the Erdős–Gyárfás proof, and Section 8 on node [181].

### 4.7 The residual structural inventory (mandatory before choosing a move)

A residual is closed by finding structure the counterexample cannot afford, not by re-running the moves that produced the residual. Before any move is chosen, the residual is inventoried against the methodology's property register (`web/frontend/src/structural-survey/data.ts`: properties A01–I06, techniques T01–T19, and the bindings that record which properties each closed EG node consumed). The inventory is a table with one row per property that is **present** in the residual object, and four columns:

1. *Present as* — the concrete observable in the residual (a number, set, order, family).
2. *Accounted upstream?* — the node or lemma that consumed it, or **not accounted**. A property is not accounted when the upstream node used it only globally (on $R$ or $G$) while the residual is local, or used only its existence and not its structure (an order, a family, a spectrum).
3. *Technique it enables* — from the register's `techniques` field for that property.
4. *Certificate it would return* — from the register's `certificate` field: what the move gives if it succeeds, and what typed residual it leaves if it fails.

The move to apply is the technique that evaluates the **largest amount of unaccounted structure**, measured by how many rows it touches and how much of the counterexample's freedom its certificate removes. Ties are broken toward the cheaper currency (constraint before compression before quantity).

Three things are not moves and are never entered in the inventory:

- **Re-application of an upstream move to the same property.** If a property row says "accounted at node [k]", the same technique on the same observable is finished; only a technique from the row's list that was *not* used, or the same technique on a property that was not accounted, counts.
- **Import of a closure theorem.** T18 evaluates I06 only for the imports fixed at the outset (`thm:p13free`, textbook facts). A theorem whose conclusion is the target is not an import.
- **Enumeration of the residual as a whole.** T17 evaluates I01/I03/I04/D10 only on a bounded configuration whose state is fully encoded and whose generator is part of the theorem. "Search all graphs up to the diameter bound" is not a bounded configuration.

The inventory is redone after every split: a split adds rows (the new typed data) and closes rows (the property is now the branch condition).

#### Worked inventory: the [181] residual, on the object it actually is

The object is $\mathcal B_{181}$ (`closure_proofs.md` §3.1): the conjunction of every fact on the path from the root, with the typed data (R1)–(R3) of `def:typeA-peeled-demand-residual` at the leaf. The register is read row by row against that state. "Accounted" names the upstream consumer; "unaccounted" means the row is present in the state and no step on the path evaluates it.

**Accounted rows (not to be re-applied, rule 16).** A01–A07, A09–A14 (order, density, cubic degrees, surplus, degeneracy, wedges, $R$–$W$ incidence, boundary deficit, cycle rank, sparsity, near-regularity): consumed by the spine estimate, `lem:stub-positive`, `lem:wedge-lower`, `lem:remainder-empty-internal-3-core`, the skeleton budget. B01, B05–B09: canonical decomposition, ports/receivers, response states, `lem:context-universality`, trace-basin minimality, the demand ledger (whose failure *is* the leaf). C01–C03, C05–C08, C10: channel spectra (`lem:typeA-spectral-pressure`), return sets, target-safety, theta/ear/cycle-space closures (invariants 31–33), $P_{13}$-freeness and diameter, remainder structure. D01, D03, D04, D06, D08–D10: window labels $C_s$, Type B fans, surplus matching/star, minimal overlap obstruction (cold), canonical ordering, skeleton reconstruction, bounded tables where bounded. E01–E03, E05, E06, E08, E09: lexicographic minimality, black box, deletion and contraction criticality (contraction criticality (removed)), replacement (I5), quotient distinguishability (the exit-(4) certificate), peelability ($\Lambda_4$), target defect. F01–F07, G01–G09, H01–H06, H08–H10, I02–I04: the response-rank block, the counting block (including Theorem 1.5), the charging block, the exact small-order rows.

**Unaccounted rows present in $\mathcal B_{181}$.**

| Row | How it is present in the state | Why unaccounted | Techniques (register) | Precondition present? |
|---|---|---|---|---|
| B02/B03/B04 (edge cuts beyond bridges, blocks, disjoint connections) | $G$ is bridgeless (`lem:bridgeless`); nothing on the path decides whether $G$ or a support has cyclic $2$-edge cuts, cut vertices, or $k$ disjoint connections between marked sets | the manuscript uses connectivity only through bridgelessness | T04, T10, T14 | yes: the state carries the cut structure implicitly; a split on it is on the object |
| A08 (degree-two chains) | receivers of internal degree $2$ adjacent to each other form maximal chains in $X$ | receivers are treated singly | T03, T04, T08 | yes |
| C04/F08 on this branch (arithmetic class, periodicity of the entries' channel lengths) | each peeled entry has actual channels $Q$ and connectors $\Gamma$ with lengths; their residues and increments are not on the path | serial-system arithmetic is applied only on the cold branch ([169]–[172]) | T08, T09, T16 | only if a serial system is exhibited on this branch (its own precondition, `def:serial-window-system`, is not yet verified here) |
| C09 (cardinality maximality of the packing) | $p_{13}$ is maximum | consumed only as "$R$ is $P_{13}$-free" | T06, T12, T15 | the swap-gain lemma (removed) needs long induced paths at two positions of one window: not known present |
| D05/D07 for entries (overlap of the basins of the loads of one receiver; equal responses among entries) | the $\ge4q(w)$ loads of a saturated receiver have basins containing traces that all end at $w$ — a concrete overlap hypergraph on $X$; peeled entries over a bounded alphabet of response states | overlap and symmetry rows are consumed only for corridors on the cold branch | T10, T16 | yes for the overlap (the traces are actual); the *consumers* ([169]–[172], [163]–[166]) have cold-branch hypotheses that must be checked, not assumed |
| E04 (safe suppression) | receivers of internal degree $2$ are suppressible inside $X$ | never used | T03, T05, T08 | yes, with the length-shift caveat |
| H07 (flow–cut on the demand network) | the demand ledger is a matching problem between entries and incidences; its failure ($\mathsf P_{\rm open}$ linear) is on the path, but the flow–cut structure of *why* it fails (the Hall obstruction: a set of entries whose essential incidences are too few) is not | the ledger records the unpaid count, not the obstructing set | T10, T14 | yes: König/Hall on the bipartite entry–incidence graph is a statement about the state as it stands |
| I06 (importable external theorem) | Bondy–Vince / Gao–Ma with exact hypotheses is citable (T18); the manuscript's appendix only *assumes* a derived input | not invoked | T18 | only where a subgraph with $\le2$ vertices of degree $<3$ is exhibited on the object |

**Selection (rule 17: precondition rows must be present).** The row with a present precondition, a closed consumer, and the largest structural content is **H07 with T14**: the demand ledger is a bipartite graph between the peeled entries and the boundary incidences (each entry adjacent to its essential incidences, $\ge2$ per entry, $\le2$ private), and $\mathsf P_{\rm open}\ge\varepsilon_{\rm press}\lvert R\rvert$ says the matching deficiency is linear. Hall's theorem (a textbook move, T14) then exhibits the obstruction as an object of the state: a set $S$ of entries whose neighbourhood $N(S)$ of incidences satisfies $\lvert N(S)\rvert<3\lvert S\rvert-\text{(deficiency)}$ — linearly many entries sharing few incidences. That is not a count; it is a *located* configuration: a set of supports and receivers whose essential incidences concentrate on few ports. Its consumer is the row D05 (overlap of the basins at those ports) with T10, whose closed rows are [169]–[172] once their hypotheses are verified on this branch — and that verification was done against the text: `lem:window-system-realizability` and `lem:serial-system-sumset` are stated on the *trivial neutral-configuration residual* of node [169] — dense packing ($\theta>\theta_{\rm win}$, the no-arm of [158]), every corridor terminal and neutral, $Q=E$, conditional fibres of barrier states — none of which is on $\mathcal B_{181}$, which is the sparse (large-budget) arm. So the D05/T10 consumers are **unavailable** on this branch; the overlap row is present but has no closed consumer here. The located Hall obstruction therefore stands with two candidate consumers whose preconditions must be exhibited on it before use: T18 (Gao–Ma, needs a subgraph with at most two vertices of degree $<3$) and B02–B04 (a small cut isolating the concentrated basins, needs the cut to be exhibited).

#### Worked inventory: the [182] constructor-1 residual

Residual object: the counterexample's own skeleton, a free pair $\pi$ with support $X_\pi$, its seed $T(p)\cup\Gamma(p)\cup T(q)\cup\Gamma(q)$, the baseline family $\mathcal I_{\rm spine}$, and the requirement that a switch inside the seed change $r_\pi$ while fixing the baseline word and earlier responses.

| Property | Present as | Accounted upstream? | Enables | Certificate |
|---|---|---|---|---|
| G05 additivity vs correlation | joint realizability of $\mathcal I_{\rm spine}\cup\{r_\pi\}$ | only through rank (`lem:mixed-sparse-spine-dependence`), which the manuscript itself says is insufficient | T10, T11, T12 | a product bound or an overlap obstruction |
| D09 gluing realizability | a switched piece re-glued into the fixed outside | **not accounted** | T05, T15, T16 | injective reconstruction (Theorem 4.2 supplies the switch) |
| F05 separation of testers | supports of $\mathcal I_{\rm spine}$ versus seeds of free pairs | **not accounted** — $\mathcal I_{\rm spine}$ is not even specified | T05, T10, T11 | disjoint supports ⇒ R2 |
| D05 overlap pattern of supports | $X_\pi\cap X_{\pi'}$ through shared seeds | `Overlaps` counts only off-seed overlap | T10, T15 | an ordering with private switching room ⇒ R3, or a minimal overlap obstruction (constructor 2) |
| B06/B07 boundaried type, contextual equivalence | the piece $H[X_\pi]$ and its response | the formal predicate compared *boundaries* (Theorem 4.1) | T05, T16 | compare responses on a fixed boundary |

**Selection.** F05 on the baseline family (T05: choose $\mathcal I_{\rm spine}$ with supports disjoint from the seeds of free pairs — a definition the manuscript has not yet made) closes R2 outright; D05 with T10 (order the family by a minimal overlap obstruction) is R3. Both are definitional choices inside the existing strategy, not new theorems.


---

### 4.8 Split admissibility: the residual must shrink

**Rule 0 — never restate the residual; the residual is the whole accumulation.** The residual at a node is the *conjunction of every fact established on the path from the root to that node*: the standing hypotheses of the branch (the near-cubic spine, the hot arm of [158], the large-budget arm, the density and entropy inequalities with their constants), every diamond taken (each exit tested and its outcome), every ledger identity, every object constructed on the way (windows, labels, receivers, traces, loads, tokens, absorbers, blockers), and the local graph facts. A sub-object of it — a pocket, a piece, a component, "a two-stub pocket with more than twelve vertices per stub" — is not the residual; it is a projection that has dropped most of the facts, and any statement about the projection ("it satisfies every local move", "no move reads it") is a statement about a different, easier-to-refute object. *Prohibitions:* (i) no step is stated about a sub-object; every step is a statement about the branch state, and the sub-object appears only as the part the move acts on; (ii) a move may use any fact on the accumulation, and the inventory must list the upstream quantitative facts (state counts, budgets, ranks, caps) as present rows, not only the local ones; (iii) declaring a projection unclosable, or writing a theorem about the projection and reporting that it cannot be proved, is forbidden — it is the escape hatch of §4.9 F1 in its most common form. Failure record: the [181] descent was reported as "a two-stub pocket with Mersenne data $k\ne m$ satisfies every local fact" — a claim about a pocket in isolation, made while the branch state carried the hot-branch state count, the density cap, the label algebra, the obstruction rank and the exit outcomes, none of which the pocket-in-isolation carries. The object you work on is the residual *as typed by its producer*: the entry, the support, the witness, the fibre, with every ledger fact attached. It is never "equivalent to" an inequality, a rate, a density, or a class of graphs with a few listed properties. Any such restatement is a weakening — it keeps a projection of the data and discards the rest — and a proof on the weakened object is a proof of something else. The failure record of this project: [181] arrives as a two-support entry $\xi$ with receiver, essential incidence core, declared deletion witness, trace basin, the exit-(4) peel just performed, and the reduced-rate test just failed, together with $\mathsf P_{\rm open}$, $\mathsf P^{+}_{\rm zero}$, silent loads and pockets; §8 of this guide records that object and the plan O7 on it; `closure_proofs.md` §3.1 nevertheless restated it as "a component with $\lvert X\rvert>7\defp(X)$" (Theorem 3.4, "equivalently") and everything after that was done on a generic subcubic $P_{13}$-free graph, which no local move can close (§4.8 last paragraph) *because the structure that closes it had been discarded*. Currency checks (§5.2) and rate computations are diagnostics to be run *after* the inventory, never a replacement for the residual; and "audit the consumer" (§4.6 step 0) means checking whether the consumer's hypothesis holds on the incoming residual, not re-deriving the consumer's quantity on a different object.


A dichotomy is not progress by itself. The progress invariant (§3.7) requires every transition to do one of three things, and a split that does none of them is inadmissible even if both arms are correct:

1. **Decrease a measure.** The arm's residual is smaller than its parent in a well-founded measure that the branch state already carries: fewer vertices in the configuration, fewer stubs, a smaller cut, a smaller rank or budget, a strictly smaller support. State the measure in the step.
2. **Route to a closed branch.** The arm's data coincides with the input of a node already closed (identification, §6.5), and the identification is proved, not asserted.
3. **Bound the arm.** The arm's data is a *finite* object (a bounded configuration, I01) with a finite table to check, and the table is written.

Two tests decide admissibility before the split is made:

- **Locality test.** The typed data of each arm must be a property of the *same* object the residual is about (the piece, the component, the support), readable from the branch state. An arm whose data is a constraint on the complement, the outside, the connectors, or "the rest of $G$" has moved the residual to a larger object; it has widened, not narrowed. Such a constraint may be *recorded* as a fact on the ledger, but it is not an arm.
- **Consumption test.** The step must name the structural row of the inventory (§4.7) that it consumes, and after the step that row must be *accounted*: its content is either used up (the object no longer has it) or turned into a number on the ledger. A step after which the same row is still on the unaccounted list has consumed nothing.

A split that fails both tests is the "splitting forever" failure: correct diamonds whose arms are all as hard as the parent. The record of it in this project: in the [181] descent, the doubling split (Step 9) and the parity split (Step 11) produced arms whose data — connector bands, connector distances, bipartiteness of $G-Z$ — lived in $G-Z$. They fail the locality test; neither decreased a measure of the piece; they were made anyway, and the residual grew. The gadget lemma (the gadget-closure lemma (removed)) later closed one of those arms, but it did so by a *minimality* move that was available before the splits and would have applied to the parent; the splits contributed nothing to it. 

What to do when the selected move needs a fact you cannot prove (rule 13 of §5.4) is therefore not "split on the fact" unconditionally: split on it only if the negated arm passes the locality test and consumes a row. If it does not, the selected move was wrong for this residual — go back to the inventory and select a move whose output is on the object itself, typically a minimality move (deletion, contraction, replacement, gadget closure: their output is a property of the configuration), an extremal-choice refinement (the packing, the counterexample, the cut are all *chosen*; a secondary criterion in the choice is a new local fact about the chosen object), or a well-founded recursion on the object (peel a sub-configuration off and recurse on the smaller remainder).

### 4.9 The executor's failure pattern, and what is forbidden because of it

This section is written from the record of one session on nodes [181]/[182] and names the actual mechanism of failure, not its symptoms. The mechanism has four parts, and each has a concrete prohibition.

**F1 — a private verdict of impossibility, then work spent justifying it.** The executor decided early that the residual could not be closed locally and from then on produced material that supported that verdict: limit theorems, "no-go" records, currency tables marked "exhausted", a search for a counter-model, an escalation to an upstream node. None of those is a move. *Prohibition:* a belief that a residual is unclosable has no standing and is not written down, not acted on, and not used to select the next step. The only outputs permitted at an open node are: an inventory row, a selected move with its precondition check, an executed step of that move with its typed arms, or a `False` leaf. Any sentence of the form "this cannot close because…", "every move returns a…", "the closure must come from…" is deleted from the work product and replaced by the next executed step.

**F2 — stopping at the first obstacle inside a move, with a meta-record instead of the next inventory.** Exit (2) was executed to its first obstacle (the two returns share a trace segment) and abandoned with the note "the arm is a theta, already accounted". An *accounted* row is a fact on the ledger, available for use; it is not a stop sign. The theta has three cycles with three known length expressions, a shared segment whose length is bounded by the trace, a return that decomposes as connector plus channel with the connector outside $X$ — every one of these is a present row for the next inventory. *Prohibition:* no move is left at an obstacle. When a step's arm lands on an accounted row, the next action is the inventory of that arm's object using the accounted fact as present data, and the next move on it. The move ends only at `False`, at a smaller typed object, or at a closed row — never at "accounted".

**F3 — changing the object when the current one gets hard.** The entry became a component; the piece became its complement; the pocket became the packing. Each switch felt like progress because the new object had fresh rows to list. *Prohibition:* the object of an open node is fixed by Rule 0 for the whole descent. A move is executed on that object to its end (F2) before any other object is inventoried. A row about a different object may be *recorded* as a ledger fact, never worked on.

**F4 — invoking the fallbacks before the method is exhausted, and treating instructions as hypotheses.** The user's fallbacks (a no-local-move theorem, finite certification of a bounded configuration, repair at an upstream node) were each invoked as soon as the current move stalled, and the instruction "close it locally with textbook moves" was treated as a conjecture to be refuted rather than as the specification of the work. *Prohibition:* a fallback may be invoked only when every technique in the register (T01–T19) and every minimality move has been executed end-to-end on the residual's object with a recorded terminal leaf for each, and the record of those executions is attached. Instructions from the user are ledger facts: they constrain the work and are not subject to the both-sides test. Enumeration of a residual is forbidden at any size unless the configuration is bounded by an explicit constant on the ledger *and* the table is the terminal certificate of a closed leaf; a search that would only produce a lower bound or a counter-model is never started.

**What replaces all four.** At an obstacle, write the obstacle's object and its present rows (including every accounted fact as data), select the technique that consumes the most of them with its preconditions present, and execute it. Repeat. The record of the descent is a sequence of executed steps ending in leaves; it contains no diagnosis.

**Instance, so that the rule is checkable.** At [181] after E3 the correct continuation was: object = the theta formed by the cycle $A=R_0+wh$ (length $2^k+1$) and the pocket cycle $C_0$ with shared segment $S\subseteq T_u$, $\lvert S\rvert=s$; present rows: $\lvert R_0\rvert=2^k$ (C01), $R_0=\Gamma_0\circ Q_0$ with $\Gamma_0$ outside $X$ (H07), $C_0$ inside $X$ with $\lvert C_0\rvert=2^{k'}+1+d_{12}\le\lvert X\rvert$ (I02), $S$ on the trace so $s\le\lvert T_u\rvert\le11$ (A07/I02), the third cycle $A\triangle C_0$ of length $2^k+2^{k'}+2+d_{12}-2s\notin\mathrm{Pow}$ (inv 31, as data); technique: T09 arithmetic on the three lengths with $s\le11$ and $d_{12}\le11$ — a finite arithmetic object — followed by the next inventory on whichever arm survives. That is what should have been written next, and was not.

## 5. Choosing the move that closes the new residual

This is the decision that requires judgement. The methodology does not remove the judgement; it constrains the search to a finite vocabulary and gives the order in which to try it.

### 5.1 First question: what does $\neg H$ give you?

Failure is data. Before looking at any move, write the residual's content in the vocabulary $V$: what object, what bound, what witness. The examples in the manuscript fall into a small number of shapes.

| The failed hypothesis $H$ | What $\neg H$ hands you | Manuscript instance |
|---|---|---|
| An asymptotic inequality "$X\le C\sqrt n$" used as a regime | An exact *large* quantity the residual already carries | [173]: failure of the exact collision gives $C\ge(n-73\lvert\mathcal P_{\rm hot}\rvert-4(\sigma_W-\sigma_R))/73$ — linearly many cold windows |
| A realization / independence sentence ("all states are realized"; "the product is target-complete") | A *first failing coordinate* with its fibre, plus a density or count above threshold | [158]: $\theta>\theta_{\rm win}+o(1)$; [170](b): the failing conditional fibre and its overlap support |
| An entropy cap "too many windows overflow" | A linear amount of mass that did *not* pay (cold mass) | [22]→[145]: hot-cap failure forces a linear cold count, then a stub excess |
| "The two representatives are distinguishable" | *Silence*: no compatible context distinguishes them — which is itself a compression licence | G3 of `lem:cold-bounded-germ-trichotomy` |
| "The corridor terminates within $Q$ states" | A repeated state (pigeonhole) | Repeat subcase of `lem:cold-corridor-first-failure` |
| "The support is subcubic" | A vertex $z$ with $d(z)\ge 4$, whose neighbours are all cubic because $V_{\ge4}$ is independent | [176]/[177] `lem:absorbed-germ-fan-data` |
| "The reduced-rate stage passes" | The exact stage accounting, the maximal demand ledger, the maximal absorption, the unique-window blocker partition | [181] `def:typeA-peeled-demand-residual` |
| "Every route-8 entry has at most one essential support" | A second essential support and its declared deletion witness | [124] `thm:typeA-two-carrier-nogo` |
| PDE: "the sequence is compact in $X$" | Concentration, escape of scale or centre, profile splitting, a nonzero defect measure, or loss of a pressure representative | Table `tab:ns-compactness-routes` of the draft |

If you cannot fill in the middle column, you have not yet understood the failure well enough to repair it. Go back to Step 2 of 4.4.

### 5.2 Second question: which currency?

Match the residual's content to the currency it can be made to pay in.

**Compression** — the residual contains a smaller object with the same relevant behaviour.
- Minimality and replacement: a deletion branch, or a replacement whose *context universality is proved before sizes are compared* (`lem:replacement`, `cor:uncompressible` = inv 8, the "contradiction lever").
- External-type compression: equal exact type licenses replacement; the first component on which two types differ is a defect and is routed as information.
- Refined minimality: when two competitors have the same $(|V|,|E|)$, extend the well-order (`lem:refined-minimality-swap`).
- Finite-state pumping: along a long chain of finitely typed states some type repeats; equal type lets the segment be removed.
- Entropy/compression squeeze: encode the class; if the code beats the skeleton budget the class has fewer than one element (`lem:blocked-graphs-compress`).

**Quantity** — the residual carries a numerical price.
- Charging scheme: demands $D$, payers $P$, canonical assignment $\pi$ with an explicit tie-break, certified capacities $c(p)$, and the elementary inequality $|D|=\sum_p|\pi^{-1}(p)|\le\sum_p c(p)$ — every symbol a separately proved local obligation.
- Local-to-global bookkeeping: local tests give local demands; demands are charged canonically; charges are compared with capacity. No global inequality is asserted directly.
- Backward rate computation: if a family of size $n$ forces $\ge an-b$ demands against supply $\le cn+d$ with $a>c$, then $(a-c)n\le b+d$; everything above $(b+d)/(a-c)$ closes by overload, and what lies below is a bounded family checked directly.
- Aggregate closure: a residual class forced to carry a linear deficit closes when its total capacity is sublinear (`prop:typeB-bridge-sublinear`, $M_B\le16\sigma(G)=o(|R|)$).
- Overload exhaustion: an overloaded payer yields a homogeneous family, a matching, a star or a chain — quantity converted back into structure.
- Injection: an explicit map from the demand class into the budget class (`lem:remainder-glue-injection`).
- Peeling loop with an integer measure that strictly decreases while every standing invariant is restored inside the peel lemma (`lem:typeA-exit4-finite-descent`, $\Lambda_4$).

**Constraint** — the residual is incompatible with the record.
- Direct target realization: the completion literally closes a power-of-two cycle (F1, G1, exit (1)/(2)).
- Contextual distinction: an outside context separates two responses, so the identification is not target-complete — a target-defective quotient, routed to the sparse exit or the exit-(4) ledger (F2, G2).
- Local rigidity: the surviving configurations cannot occur among the objects the count selects (`lem:symmetric-pair-endpoint`).
- Identification with an already-excluded case: the residual satisfies the defining conditions of an exit that the branch condition says is absent (`thm:typeA-two-carrier-nogo`).
- Rigidity closure by a fixed input: a classification or Liouville theorem fixed at the outset empties a named class (PDE).
- Arithmetic hit: after uncrossing into a serial system, the increment sumset contains an arithmetic progression long enough to hit a power of two at *full modulus* (`lem:serial-system-sumset`, `lem:system-increment-arithmetic`).
- Finite enumeration with explicit code (`lem:two-strand-check`, `Graph/TwoStrandEnumeration.lean`; `def:cold-same-interface-table`).

### 5.3 The selection table

Read the row that matches the residual's shape; try the candidate moves in the order listed; discharge the checks in the last column before declaring closure.

| Residual shape | Candidate moves, in order | Must check |
|---|---|---|
| A **bounded / finite** object (bounded support, bounded length, bounded configuration) | (1) Direct hit; (2) contextual distinction → target-defective quotient; (3) silent compression; (4) finite enumeration of what remains, then structural exclusion of the survivors | Exhaustiveness of hit/defect/compression; the enumeration is at the right parameters (window order 13, $\ell\le 40$); survivors are excluded by a *structural* fact, not by re-enumeration ([167]→[168]) |
| A **long chain** or corridor of finitely typed states | Finite-state pumping: read $Q+1$ states, two coincide; extract the exchange; route by hit / defect / compression | Existence of a first failure is *proved*, not assumed (the corridor either terminates within $M_{\rm cold}=Q_{\rm cold}+30$ vertices or repeats); equal-length ($\delta=0$) exchanges that escape the trichotomy are covered by a finite table |
| **Overlapping / nonadditive** supports (a product or independence sentence failed) | (1) Retain the first failing fibre with its full state; (2) minimal *connected* overlap obstruction; (3) uncross into a serial system; (4) sumset → arithmetic progression → full-modulus hit; (5) or periodic response class with a concrete exit | Connectivity of the minimal obstruction; each saving charged *once* to its minimal connected support (`rem:entropy-lives-here`); the arithmetic is at full modulus, not just the odd part |
| A **same-size competitor** the well-order cannot see | Refine the order lexicographically by a canonical invariant $\Phi$; exchange; show $\Phi$ strictly decreases | Every earlier use of minimality compares strictly smaller $(\lvert V\rvert,\lvert E\rvert)$ and so remains valid in the refined order (`lem:refined-minimality-swap`) |
| An **asymptotic side condition** ($n\ge N_0$, $\sigma\le C\sqrt n$) | Exactify: restate the collision as an integer inequality on the object; its failure is a structural residual, not a size condition | Each allowance is a bound on a quantity the residual carries exactly; the failure rearranges to something the next move consumes (linearly many cold windows) |
| A **discarded remainder** (an "extraction loss," an $o(n)$ that was dropped) | Charge it into an existing ledger with a no-overcount lemma; the loss becomes fan data / Type B charge / a peel | The receiving ledger's admission conditions hold (the two corridor incidences at $z$ are distinct connector tails); the charge is not also counted where it was discarded |
| Downstream **reads a cap only through one inequality** | Cap substitution: supply that one inequality from a different producer on the new branch; the continuation applies verbatim | "Nothing else in [25]–[64] reads the density cap" is verified by reading every consumer; any additional consumption (the private-carrier rate at [120]–[122]) gets its own diamond |
| A residual class that **survives but is small** | Aggregate closure: total capacity (member count × per-member capacity × multiplicity) is sublinear against a linear deficit | Currencies are not mixed; the linear deficit and the sublinear capacity are measured against the same $\lvert R\rvert$ |
| A **loop** with no obvious end (peel, reselect, re-run) | Define a nonnegative integer measure; prove each pass decreases it by one *and* restores every standing invariant | The measure is on the bookkeeping only ("the graph, the packed windows, the boundary profiles, the target-safety constraints, and all target-response quotients remain the same"); the charge update is exact ($1/4$-unit) |
| The residual **coincides with an excluded exit** | Identification: show the residual's data satisfy the defining conditions of an exit the branch says is absent | Every witness the exit requires is *declared* on the branch (`lem:typeA-deletion-witness-declared`), not reconstructed |
| **Linearly many bounded components** of a labelled class closed under relabeling | Orbit count: $\lvert\text{class}\rvert\ge\lvert R\rvert!/\lvert\mathrm{Aut}\rvert$; components give $\log\lvert\mathrm{Aut}\rvert\le K\log K+O(\lvert R\rvert)$; compare with the budget | $K$ is bounded (every component has a deficient vertex, or a $W$-edge, or $\ge4$ vertices); the state map being compared is invariant under the relabelings; the class is the one the budget counts (Part IV of `closure_proofs.md`) |
| **No bounded local test** sees anything wrong | Entropy / compression squeeze in the correct class | The class is the one the budget does not already charge (minimum degree $\ge3$, `rem:blocked-class-checks`(a)); a sanity family shows the threshold is not below what the route can give (1/81) |
| A **minimal counterexample with a bounded-degree region** and no arithmetic hit | Run *every* minimality move, not only the ones already on the branch: deletion (edge with both ends of degree $\ge4$), **contraction** (an edge whose ends share no degree-3 neighbour: contracting it gives a smaller graph with $\delta\ge3$, so a $2^k$-cycle of the contraction lifts to a $(2^k+1)$-cycle through the edge), replacement (a piece with a smaller representative) | The contracted graph must stay simple with $\delta\ge3$ (common neighbours of the edge must have degree $\ge4$); the lifted cycle must not be a cycle of the original (`closure_proofs.md` Theorem 18) |
| A **high-degree vertex** appears in a subcubic argument | Dichotomy on $J\cap V_{\ge4}=\varnothing$; use independence of $V_{\ge4}$ (node [10]) to force cubic neighbours; hand off as decorated fan data | The handoff's termination: the $A\to B\to A$ alternation consumes a finite token set once (`rem:typeA-typeB-stratification`) |
| PDE: **loss of compactness** | Concentration → retain core, normalize, consume critical mass; translation escape → recentre or prove local invisibility; scale escape → order scales, promote inner to a new core; profile splitting → mass decoupling; weak-to-strong failure → new charged defect; pressure/gauge defect → separate and close elliptically; terminal-time escape → endpoint estimate | Each edge preserves the normalization and the topology, gauge and resource data its successor consumes; each new core consumes a fixed amount of bounded resource (Theorems 3.3–3.4) |

### 5.4 Rules that constrain the choice

1. **Only branch-state facts, fixed inputs, and textbook material.** A move that needs a global result not among the inputs is not a closure; it is a defect. Refine the case structure instead.
2. **Prefer moves that make progress in a well-founded sense.** Every step outputs a closed branch or a *strictly smaller named residual* — smaller in size, in live exits, or in an explicitly monitored parameter. A lemma whose residual is not smaller, finite, charged or routed relocates the difficulty and counts as no progress.
3. **Prefer the cheapest currency first.** Direct hit and contextual distinction cost nothing; compression needs context-universality; charging needs a full scheme; entropy needs the right class. The manuscript's trichotomies are ordered this way (hit, defect, compression) for a reason.
4. **Separate currencies.** Deficiency, surplus, entropy, rank, boundary mass and concentration are distinct unless a proved interface converts one into another; an obstruction is paid once. Check the moves × budgets monotonicity table after any deletion, replacement, peel, charge transfer or hand-off.
5. **Keep both squeezes alive.** Outside the explicit residuals the contradiction is reached in two arithmetically independent forms: obstruction ($W_2\ge2.543|R|$ against $\le0.611|R|$, slack $4.1\times$) and net charge ($0.25|R|$ against $\tau_{\rm win}=0.2282|R|$, slack $\approx9.6\%$). Any repair to an estimate must keep demand $>$ supply in the form it feeds.
6. **Do not launder.** If a move's exhaustiveness is not proved on the retained fibre, the residual is retained under its exact negation, not renamed as a blocker, quotient, exit, or Type B witness. Node [182] is the model.
7. **Check forward references.** A required invariant introduced at a strictly later node is a forward-reference gap. For any result that produces the contradiction, confirm the chain inv 8 ← `cor:uncompressible` ← `lem:replacement` is intact and not circular with the result invoking it.
8. **Check the interface, not the prose.** The consumer of the closure must accept exactly the typed witness the move produces (a decorated handoff at [65] needs a heavy centre with separated connector tails; an exit-(4) peel needs a declared deletion witness).
9. **Never split on whether a lemma holds; split on the first hypothesis its proof consumes.** A diamond whose no-arm is "$\neg$(conclusion)" has no consumer. It is admissible only as a temporary honest endpoint — an open node — and Section 4.6 is the procedure for pushing it down to admissible diamonds.
10. **Enumerate the minimality moves before enumerating tools.** A minimal counterexample supports deletion, contraction, and replacement; check which of them the branch has already consumed before looking for a new tool. No lemma is added to the record for a move unless it is executed on the incoming residual.
11. **Inventory before moving.** No move is chosen for a residual until its structural inventory (§4.7) is written against the register. The move is the technique that evaluates the most unaccounted structure. Re-applying an upstream move to an accounted property, importing a closure theorem, or enumerating the whole residual are not moves.
12. **Relocation is not progress.** A step that removes a unit from one ledger and records it in another ledger with no payer (a peel, a deferral, a "routing record") has not closed, charged, or shrunk anything. It is admissible only if the receiving ledger has a consumer with capacity; otherwise it is the re-encoding failure of Section 9, and the residual it produces will be tautologically linear (Section 8.2).
13. **An unproved intermediate fact is a diamond, not a stop.** When the move you selected needs a fact $F$ about the residual that you cannot prove from the ledger (e.g. "the terminal spectrum of the piece is doubling"), $F$ becomes the hypothesis of the next split: the $F$ arm continues with the selected move, and the $\neg F$ arm is a new typed residual whose data is $\neg F$ itself — and $\neg F$ is usually the more structured side (a non-doubling spectrum is periodic; an unbounded object has a repeat; a non-Menger vertex has a small cut). Run the inventory of §4.7 on the $\neg F$ arm and select again — but only if the split passes the two admissibility tests of §4.8; if the $\neg F$ arm's data is not a property of the residual's own object, the selected move was wrong and the split must not be made. Stopping at "$F$ is needed" or looking for $F$ as an external theorem is the extrapolation failure of Section 9; the residual is closed only when every leaf is `False`, and the branch record shows which $F$ were split on (the [181] record, since removed).
14. **The recorded plan is binding.** When this guide (or the branch record) has fixed, for an open node, the typed object and the selected move with its step table (as §7 and §8 do), the work on that node is the execution of that plan. Any deviation — a different object, a different move, a reformulation "equivalent to" the node — is itself a repair of the plan and must be recorded as such, with the first failing step of the plan and the reason, *before* any work is done on the new object. Work that silently changes the object is off-protocol whatever it proves. (Failure record: `closure_proofs.md` left the O7 plan of §8.5 after Corollary 3.3 without recording a failing step.)
15. **A certificate of non-closure is not structure.** Typed residual data often includes records of what *failed*: an exit-(4) demand token $(q,S_0,S_1,Y,E)$ records that a quotient is target-defective by exhibiting an alternative realization $S_1$ and a hypothetical context $Y$; a routing record, a deferral, an "open unit" record the same kind of thing. Only the actual realization ($S_0$, the load $u$, its trace, its pocket) is a property of $G$. In the inventory, a certificate contributes *no* row of positive structure; it contributes only the fact that one method is closed off. Counting certificates (tokens per incidence) therefore counts nothing about $G$ beyond the count of the actual objects they are attached to. Failure record: the §4.7 inventory of [181] listed "nine tokens per boundary edge ⇒ nine channels with distinct forgotten lengths"; the channels are hypothetical, and Y3 of the O7 plan (§8.5) is unsound for the same reason.
16. **Never re-prove the residual; never re-apply an upstream move.** Once a node's residual is typed, the facts on its ledger are settled: the extremal choices already made (the packing, the counterexample, the ledger orderings), the upstream diamonds already taken, and the reasons upstream consumers failed are *inputs*, not work. The following are forbidden at an open node, each because it spends effort on the parent instead of the residual:
    - re-deriving, re-auditing or re-defining an upstream object (reading how the packing was chosen, re-checking a consumer's vacuity a second time, re-computing a rate) once its ledger fact is on the record;
    - refining an upstream extremal choice as the move for a downstream node (a secondary criterion on the packing is a repair of the node where the packing was chosen, not a closing move here);
    - re-applying an upstream move to an accounted row (Menger where the cut is already typed, contraction where I7 is already on the ledger, a count where the count is the residual);
    - writing "why this route cannot close" records as work products — one sentence in the inventory's *accounted* column is the whole record, and a limit theorem is written only when it is the terminal certificate the node will carry.
    The only admissible work at an open node is: inventory (§4.7), selection of a move that lands on a closed row or a smaller typed object (§4.8), and execution of that move. Failure record: at [181] this guide's author re-read the packing definition, re-audited the demand consumer, and wrote three no-go records after the residual had been typed, and closed nothing.
17. **Check the move's preconditions against the inventory before selecting it.** Every closing move has *target rows* (what it evaluates) and *precondition rows* (what must already be present for it to apply: internally disjoint returns for exit (2), a shared window for exit (3), a smaller representative with the same profile for exit (5), bounded size for a table). A move is admissible only if its precondition rows appear in the residual's inventory as *present*. Selecting a move by its target rows alone produces a diamond whose no-arm is "the precondition fails", which is typically an accounted row (a theta instead of two disjoint returns; a second window instead of a shared one) and therefore neither closes nor shrinks. Failure record: exit (2) was selected at [181] for its target rows (C01, D05/D06) while the residual did not carry disjointness; its no-arm was the theta closure of invariant 31, already accounted, and nothing moved.
18. **A move sold on a finite table must have its table computed before it is selected.** When the closing power of a move rests on "a linear supply against a fixed finite table" (overlap arithmetic, label relations, offset tables), the table is computed *at selection time*, and the move is admissible only if the table is restrictive enough to contradict the supply on the residual's actual parameters. Announcing the move first and computing the table afterwards is the F1 pattern in a new form. Failure record: a fundamental-cycle overlap move was selected at [181] as "linear supply versus fixed table" and announced as a reduction; computed, its table forbade $184$ of $1597$ patterns and contradicted nothing, and worse, its rows (cycles of the pocket avoid $\mathrm{Pow}$) were already accounted by I4, so it was a re-application of an accounted row (rule 16). It was deleted from the record.

### 5.5 A worked decision

Suppose red-teaming shows that a counting step assumed two families of coordinates were jointly realizable. Run the procedure:

- *What does $\neg H$ give?* A first coordinate at which the conditional fibre is larger than its declared relative size, together with the exposed prefix and the outside record.
- *Currency?* The failing fibre is a structure, not a number: constraint or compression, not quantity.
- *Table row?* "Overlapping / nonadditive supports."
- *Moves, in order.* Retain the fibre → minimal connected overlap obstruction → uncross → serial system → sumset arithmetic; on the additive arm, compression.
- *Checks.* Connectivity; charge once; full modulus; the class for the compression is near-cubic.

That is nodes [169]–[172] (Section 6.3). If instead the uncrossing's exhaustiveness cannot be proved on the retained fibre, stop at the last proved alternative and name the open residual — that is [178]–[182] (Section 6.7) — and then apply Section 4.6 to the intended proof, which is Section 7.

---

## 6. Worked repairs

Each repair below uses the same seven fields. This template is also the form in which a new repair should be written up.

> **What failed** · **The hypothesis exposed** · **The dichotomy inserted** · **What the residual carries** · **The closing move(s)** · **What was left untouched** · **Where it is recorded**

### 6.1 The small-order repair — nodes [173]–[177]

**What failed.** Node [56]'s net-charge collision was written with asymptotic allowances: $\sigma(G)\le C_{\rm sp}\sqrt n$ (node [19]), the configuration-extraction loss $B_{\rm cold}\sigma(G)$ (bounded arm of [153]), and the dyadic factor of the density cap. Read that way, the collision needs $n\ge N_0$, and $n<N_0$ would be a separate obligation.

**The hypothesis exposed.** "$n$ is large enough for the allowances." But the allowances are bounds on quantities the residual carries *exactly*: $\sigma_W$, $\sigma_R$, $|\mathcal P_{\rm hot}|$, $C=|\mathcal P_{\rm cold}|$, $|\mathcal G_{n,m}|$.

**The dichotomy inserted.** Node [173] decides the exact integer inequality on the object (`lem:exact-collision-test`):
$$15p_{13}+\sigma_W-\sigma_R<\tfrac14(n-13p_{13}),\qquad p_{13}=|\mathcal P_{\rm hot}|+C.$$
Yes: nodes [58]–[64] follow verbatim, with no condition on $n$.

**What the residual carries.** On failure, $C\ge\bigl(n-73|\mathcal P_{\rm hot}|-4(\sigma_W-\sigma_R)\bigr)/73$: linearly many cold windows, on the bounded arm of [153] whose cold mass was charged as the extraction loss.

**The closing moves.** *Exactification* turned a size condition into a structural residual. Then *charging into an existing ledger*: `lem:absorbed-germ-fan-data` splits on whether the first-failure support $J$ meets $V_{\ge4}(G)$. (i) $J$ subcubic → a genuine (F5) configuration, closed by the cold trichotomy chain (node [176]). (ii) $J$ contains $z$ with $d(z)\ge4$ → by node [10] all neighbours of $z$ are cubic, the corridor enters and leaves $z$ through distinct incidences, so the two segments are separated connector tails: decorated handoff fan data, entering Type B at [65] (node [177]). Conclusion: "the loss $B_{\rm cold}\sigma(G)$ of the bounded arm of node [153] is not a loss: every half-edge it discards is charged to the Type B ledger."

**What was left untouched.** Nodes [58]–[64] and everything below [65]. `rem:no-sufficient-order`: the reading $n\ge N_0$ of node [57] is never used; the theorem is proved for all orders.

**Where.** Dependency table item 53; `lem:exact-collision-test`, `lem:absorbed-germ-fan-data`; diagram Part V expands the no-edge of [173] in place.

*Lesson.* When a residual carries a quantity exactly, never bound it. The exact quantity is what the next move consumes.

### 6.2 The dense-packing residual — nodes [158]–[168]

**What failed.** `lem:p13-window-package` and `prop:p13-density` used the sentence "all target-complete window states are realized by labelled near-cubic skeletons" as if it were a theorem.

**The hypothesis exposed.** Realization of the joint window package by $\mathcal G_{n,m}$ with range $\ge2^{c_{13}p_{13}\log_2 n}$. "The exact finite reading … is a branch test, not an assertion: it holds or fails on the residual at hand."

**The dichotomy inserted.** Node [158] = `def:window-realization-test`. Yes: the hot/cold split [22] as written. No: the *dense-packing residual* [159], on which $2^{c_{13}p_{13}\log_2n}>|\mathcal G_{n,m}|$, i.e. $\theta>\theta_{\rm win}+o(1)$.

**What the residual carries.** A density above threshold — a number, so quantity first.

**The closing moves.** A chain of four further diamonds, each with a named consumer:
- [160]/[161] `lem:dense-deficiency-routing` — *cap substitution*. Decide $\tau(\theta)=15\theta/(1-13\theta)<1/4$ and, on that yes-arm, the private-carrier rate $\tau(\theta)<3/13$. On double-yes, [25]–[64] apply verbatim with the deficiency cap of [161] in place of the density cap [24], because "nodes [56]–[64] consume the density cap only through the inequality $\defp(R)-\sigma(R)<\tfrac14|R|$ … and nothing else in [25]–[64] reads the density cap." The route-8 subcontinuation reads one more thing (the private-carrier rate), so that gets its own decision.
- [162] `lem:dense-cold-pass` — the hot/cold pass runs unchanged because it uses only facts of the current residual, and the density sentence is not among them.
- [163] neutral equal-length terminal configuration → `lem:neutral-germ-symmetry` splits into the canonical-replacement case and the symmetric strand pair.
- [165]–[166] *refined minimality* (`lem:refined-minimality-swap`): order $(|V|,|E|,\Phi)$ with $\Phi$ the multiset of canonical boundaried pieces; exchanging $Q$ for its canonical representative $E\ne Q$ keeps $(|V|,|E|)$ and strictly decreases $\Phi$. Backward check: "Every earlier use of minimality in the proof compares graphs of strictly smaller $(|V|,|E|)$, which remain smaller in the refined order."
- [167] *finite enumeration* (`lem:two-strand-check`, `Graph/TwoStrandEnumeration.lean`, `survivors 13 40`): a strand pair closes cycles $\ell+d$ and $2\ell$; 96 of 533 configurations are hits; survivors are exactly $\ell\notin\mathrm{Pow}$, $\ell+d\notin\mathrm{Pow}$.
- [168] *structural exclusion* of the survivors (`lem:symmetric-pair-endpoint`): interior window vertices have one external stub, a symmetric pair needs two at each attachment, so pairs attach only at endpoints, while the extraction selects the $11\to9$ *interior* half-edges — survivors never occur among the selected half-edges.
- [164] *injection* (`lem:remainder-glue-injection`): $H\mapsto G[R:=H]$ embeds $\mathcal G(R)$ into $\mathcal G_{n,m}$, so demand $\le$ budget and [53] cannot be active.

**What was left untouched.** The yes-branch of [158] (the original hot/cold split and everything under it).

**Where.** Dependency table item 52; `rem:dense-residual-status`: "The dense regime therefore has no open node."

*Lessons.* (a) A realization or independence *sentence* is always a diamond. (b) When a continuation consumes an upstream bound through one inequality, say so explicitly and re-supply the inequality rather than re-proving the continuation. (c) Enumeration kills most of a finite family; a structural fact kills the rest. Do not enumerate twice.

### 6.3 Scale additivity, or where the entropy sentence lives — nodes [169]–[172]

**What failed.** After [165]–[168] the residual is $Q=E$: every corridor is terminal, neutral, and its own canonical representative. "No bounded local test sees anything wrong with such a graph." The manuscript's sentence "the product of the target-complete states on the distinct windows is therefore again target-complete" was carrying the whole load, and window completions can overlap.

**The hypothesis exposed.** Conditional independence across barriers, scales and windows: every conditional fibre has relative size $\le F_{a,b}/W_{a,b}$, so the savings $\gamma_{a,b}=\log_2(W_{a,b}/F_{a,b})$ add.

**The dichotomy inserted.** `lem:scale-additivity` (node [170]), in *ordered first-failure* form: (a) every conditional fibre satisfies the bound; or (b) at the first failing coordinate, retain the fixed scale, barrier, outside record, previously exposed prefix, and failing conditional fibre.

**What the residual carries.** On (b): a specific fibre with its full exposure context — a structure. On (a): a compression certificate.

**The closing moves.** (a) → *entropy squeeze* `lem:blocked-graphs-compress` (node [171]): $|\mathcal B(\mathcal P)|\le|\mathcal G_{n,m}|\,2^{-(c_{13}-o(1))p_{13}\log_2n}<1$ for $\theta>\theta_{\rm win}$; a class with fewer than one element is empty. (b) → `lem:barrier-failure-overlap` (cardinality-minimal *connected* overlap obstruction; connectivity proved by a component-concatenation contradiction) → `lem:window-system-realizability` (uncross into a serial window system) → `lem:serial-system-sumset` (sumsets of increments contain long arithmetic progressions) → `lem:system-increment-arithmetic` (node [172]: exact full-modulus lift and residue-specific central range test; a hit is a literal power-of-two cycle).

**Two checks the manuscript attaches** (`rem:blocked-class-checks`): (a) the class must be near-cubic — inside all labelled graphs with $m$ edges no compression by $c_{13}p_{13}\log_2n$ bits with $c_{13}>12$ is possible, so `def:blocked-class` carries a minimum-degree clause: "this is the structure not charged by $\binom{\binom n2}{m}$." (b) A forest window-incidence family exists only for $\theta\le1/81<\theta_{\rm win}$, so it does not contradict the lemma and shows the threshold cannot be lowered below $1/81$ by this route. And `rem:entropy-lives-here`: a failure of disjointness is charged *once* to its minimal connected completion support; no global completion is charged separately at each window that sees it.

**What was left untouched.** [165]–[168]; the yes-branch of [158].

**Where.** Dependency table item 54; `def:blocked-class`, `def:barrier-overlap-system`. In Lean, [172a] (the graph-derived overlap producer on the nonadditive arm) is one of the currently open residuals — the arithmetic core exists in `SerialSystemArithmetic.lean`, the graph construction does not yet.

*Lessons.* (a) When "nothing local is wrong," the only remaining currency is entropy, and the entropy step must be read in the class the budget does not already charge. (b) Sanity-check a compression constant against an explicit family. (c) An overlap is charged to its minimal connected support, exactly once.

### 6.4 Exit-(4) peeling as a well-founded loop — nodes [101], [123], [181]

**What failed.** The saturated-receiver charge summed all routed loads $\mathcal L(w)$ into the $3/7/11$ discharging estimate, including loads whose declared coordinate is used by a target-defective quotient. Those belong to another branch; counting them in both places double-charges.

**The hypothesis exposed.** "Every routed load is honest Type A charge."

**The dichotomy inserted.** Pattern-level: `def:typeA-exit4-peeling` introduces a peeling set $P_4(w)$, and `rem:typeA-exit4-peeling-use` makes it a *routing record*: "A load in $P_4(w)$ exits through the target-defect branch before the pure Type A charge is summed … Consequently `lem:typeA-exclusion` is invoked only after the target-defect alternative has been removed."

**What the residual carries.** After each peel, the same graph with one fewer unpeeled load and an exact $1/4$-unit charge update (`lem:typeA-exit4-peeling-charge`).

**The closing moves.** *Peeling loop with a decreasing integer* (`lem:typeA-exit4-finite-descent`, node [123]):
$$\Lambda_4=\sum_w\bigl|\mathcal L(w)\setminus P_4(w)\bigr|$$
decreases by one per peel, and "the operation changes only the bookkeeping ledger: the graph $G$, the packed $P_{13}$-windows, the boundary degree profiles, the target-safety constraints, and all target-response quotients remain the same." True two-support route-8 survivors close at [124] (6.5). If the reduced-rate test fails, the exact accounting is *published*, not discarded: `def:typeA-peeled-demand-residual` = node [181], whose definition states what it does *not* assume — "No sublinear bound on $\mathsf P_{\rm open}$, same-window two-blocker cap, or zero-signature excess bound is included in this definition."

**What was left untouched.** The discharging arithmetic (`lem:typeA-unsaturated-discharge`) on unpeeled loads; exits (1)–(3), (5)–(7).

**Where.** Dependency table items 42 and 56; `thm:large-budget-route8-only`. In Lean: `selectedRouteEightCensus` (Section 11).

*Lessons.* (a) A loop is admissible only with an explicit integer measure and an explicit invariant-preservation clause. (b) When a stage fails, publish its exact accounting as a named node with a definition that lists the bounds it does *not* contain. (c) A loop that terminates is not thereby a closure: the peel here relocates a quarter-unit of deficit to a ledger whose only consumer turns out to be vacuous (Section 8.2). Termination was proved; payment was not. Section 8 replaces the peel by an exclusion.

### 6.5 Identification with an excluded exit — node [124]

**What failed / what was needed.** The route-8 branch was reduced to a terminal two-support obstruction and needed a closing contradiction.

**The closing move.** *Identification* (`thm:typeA-two-carrier-nogo`). (T3) gives $|\mathcal C_{\rm ess}(\xi)|\ge2$; pick $c$. (T5) records the declared $c$-deletion witness (`lem:typeA-essential-deletion-witness`, `lem:typeA-deletion-witness-declared`). `lem:typeA-two-carrier-deletion-canonical` places the deletion quotient in the canonical family $\mathcal Q_4(w)$; `lem:typeA-carrier-deletion-exit` therefore realizes exit (4). But (T2) says $\xi$ is a *true* route-8 entry, so exits (1)–(7) are absent. Contradiction.

*Lesson.* The mathematical content of an identification closure is in proving the witnesses are *declared* on the branch, not in a new estimate. If a witness must be reconstructed, the closure is not yet valid.

### 6.6 Cold-corridor first failure — nodes [145]–[157]

**What failed.** The entropy cap on packed windows was stated flatly. A window pays its full entropy price only when the canonical package of independent coordinates behind it is live in the comparison being run.

**The hypothesis exposed.** Independently realizable coordinates. Windows with a live package (hot) pay; cold windows do not.

**The dichotomy inserted.** [22]: "does the live-hot entropy cap close?" Yes: the old overflow terminal. No: the cold branch, appended as [145]–[157], inheriting the spine estimate and every earlier invariant and adding "the hot cap failed."

**What the residual carries.** A linear amount of cold mass, then a stub excess, then corridors.

**The closing moves.** *Totalize a partial classification with an existence proof.* `lem:cold-corridor-first-failure` first proves a first failure always exists: either the successor boundary stub is reached within $Q_{\rm cold}+1$ states, so the corridor has at most $M_{\rm cold}=Q_{\rm cold}+30$ vertices (terminal subcase of F5), or two states coincide (repeat subcase of F5). Then five-way routing: (F1) power-of-two cycle; (F2) target-defective quotient → sparse exit or exit-(4) ledger; (F3) target-complete compression of a proper support; (F4) already-named Type B or route-8 handoff; (F5) cold bounded configuration. (F5) is killed by the *trichotomy* `lem:cold-bounded-germ-trichotomy`: G1 hit-realized; G2 hit-distinguished (target-defective quotient); G3 silent — "replacing the longer representative by the shorter one preserves the boundary degree profile and the target response against every context, creates no power-of-two cycle, and strictly decreases the support." Equal-length configurations escape the trichotomy and are covered by the finite `def:cold-same-interface-table`. Short self-returns are filtered by exact arithmetic (`lem:cold-short-self-return-filter`): sweeping the 13 offsets tests $[\ell,\ell+12]$, which avoids $\{4,8,16,32\}$ only for $\ell\in\{17,18,19\}$ when $\ell\le32$; the three survivors become explicit table rows.

**What was left untouched.** The hot-side terminal and every step from [25] onward.

*Lessons.* (a) Before routing a first failure, prove one exists. (b) Compute exception sets exactly and carry them as declared data. (c) Silence is a compression licence, not a dead end.

### 6.7 The honest open residual — nodes [178]–[182]

**What failed.** `prop:sparse-entropy-sandwich-with-blockers` treats spine coordinates and pair coordinates $r_\pi$ as jointly realized; but "the pair coordinates $r_\pi$ are functions of the graph whose supports $X_\pi$ share the spine routes, so their independence is not a consequence of label-injectivity, and the second alternative is a genuine residual."

**The dichotomies inserted.** [178] `lem:pair-failure-overlap` (conditional factorization → minimal connected pair overlap obstruction); [179] `lem:pair-system-realizability` (five outcomes: power-of-two cycle / target-defective quotient / smaller proper representative / same-token routed bottleneck → Type B fan data / serial demand system); [180] `lem:pair-system-increment-arithmetic`.

**What was not proved, and what was done about it.** "The covered arms implement the announced strategy, but the arguments below do not prove those implications on the retained conditional fibre. Their exact negations are therefore retained at the single open node [182]." And at [179]: failure "retains that return system and the negation of the displayed alternative at node [182]; it is not reclassified as any of alternatives (ii)–(iv)."

*Lesson.* This is the correct *interim* behaviour when a closing move's exhaustiveness cannot be established. The residual is the disjoint union of exactly three negated implications with their retained data; the public theorem is reduced accordingly; nothing is renamed. Compare with the failure mode "omitted difficult steps": the difference between a proof with an open node and a draft with a hidden gap is precisely that [182] exists, is typed, and has a definition.

It is also not the end of the procedure. Each retained negation is the negation of a lemma's *conclusion*, so by Section 4.6 the diamonds at [178]–[180] sit too high; Section 7 pushes them down to the first hypothesis each intended proof consumes and produces the concrete closure plan.

### 6.8 The three web-app repairs and the Stokes audit

- **Navier–Stokes Type I — a compactness claim on too small a state (language extension).** A lemma asserted the successor relation between retained concentration profiles was closed; the diagonal argument failed because a witness could be centred at a point escaping to infinity. The hypothesis exposed: the observer witnesses must stay in a fixed compact cylinder — a profile-only state cannot carry that. Repair: the step became a three-way test on covariant density and event balance; the zero-density chain sustained by a persistent root current became the new *sparse branch*, reduced through critical-shell accounting to an interscale-flux class shown empty. Steps [141]–[146] were re-typed within their numbers; the interface theorem "no infinite retained concentration chain" kept its statement.
- **Erdős–Gyárfás — an estimate missing a hypothesis (structural).** The hot/cold split above, [22]→[145]–[157].
- **Erdős–Gyárfás — a budget used outside its regime (structural).** The skeleton budget is valid only on a near-cubic spine. A surplus test $\sigma(G)=2m-3n=O(\sqrt n)$ was placed *before the budget's first use*; its no-side is the old main line; its yes-side is the surplus-pair accounting branch [125]–[144], whose output is exactly the near-cubic spine estimate the main line consumes. The main line now receives that estimate as an established hypothesis.
- **Stokes — the finite-energy kernel audit (draft, nodes [6]–[7]).** Curl and local heat estimates give smooth vorticity, but "equality of vorticity does not, by itself, identify velocity": an entire divergence-free, curl-free $L^2$ field could have been lost. The remark `stokes:rem:counterexample` exhibits $u=a(t)e_1$, $p=-a'(t)x_1$ to show a local curl argument alone cannot prove the theorem. The obligation is closed separately by an expanding-ball Caccioppoli argument on the finite-energy class (node [6]), and only then does the equation recover the harmonic pressure tail (node [8]). This is the PDE form of "representative stability": specify the representative that survives the transition, and audit the kernel that could have been dropped.

---

## 7. Closing an open node: the protocol applied to [182]

Sections 4–6 describe repairs that have already been made. This section and the next apply the protocol to the two nodes that are still open, so that the reader can see the procedure produce a plan rather than describe one after the fact. Nothing below is a proof; it is the output of Steps 1–5 of Section 4.4 and of the rule in Section 4.6, written to the point where each remaining item is a bounded local lemma with a named closing move and a typed failure route. Each item is marked *established* (already in the manuscript or the Lean tree), *transfers* (the window-system proof carries over verbatim), or *obligation* (must be proved; this is the work).

### 7.1 What [182] literally is

On the strict sparse branch (the survivor of the sparse surplus exits at [125], with $\Pi_{\rm free}$ the blocker-free pairs of `def:canonical-blocker-ledger`), the entropy count of `prop:sparse-entropy-sandwich-with-blockers` at [131] (and on the free side of [137]) is a branch test. On its failing arm the manuscript runs three lemmas and retains, at [182], the exact negation of whichever *conclusion* it could not establish:

| Constructor (Lean `PairUncoveredResidual`) | Retained input | Negated conclusion | Manuscript lemma |
|---|---|---|---|
| `factorization system failure` | the actual skeleton model of the pair set | `ConditionalFactorization` = `separated` $\wedge$ `concatenate` | `lem:pair-failure-overlap` ([178]) |
| `systemRealizability returns failure` | the exact pair-return package of a minimal connected overlap obstruction | one of the five uncrossing outcomes (i)–(v) exists | `lem:pair-system-realizability` ([179]) |
| `incrementArithmetic serial failure` | the graph-realized serial demand system | the full-modulus arithmetic arm or a routed periodic arm exists | `lem:pair-system-increment-arithmetic` ([180]) |

The manuscript is explicit about the status: "The covered arms implement the announced strategy, but the arguments below do not prove those implications on the retained conditional fibre." And about the intended proofs: `lem:pair-system-realizability` is "identical to `lem:window-system-realizability` with the response supports $X_\pi$ in place of completion supports and the port returns $T(p),T(q)$ in place of the window offsets," and [180] reuses `lem:serial-system-sumset` with $D_{\rm sp}$ in place of $D_{\rm sys}$.

### 7.2 The diagnosis

Each of [178]–[180] is a diamond on a *conclusion*: "does the implication hold on this fibre?" Its no-arm is $\neg(\text{conclusion})$, which no move consumes. That is the both-sides test failing on the negative side, and by Section 4.6 it means the diamond sits too high. Retaining the negation was the right thing to do *at the time* — it is honest and it keeps leaf totality — but it is a temporary endpoint, not a place to stop.

The protocol's instruction is mechanical: take the proof the manuscript says it intends, write it as a chain of steps $X_1\wedge\cdots\wedge X_m$, find the first step that does not go through on the pair objects or on the strict-branch ledger, and put the diamond there. Three questions locate that step (Section 4.6): does the step consume a fact that is not on *this* branch's ledger; does it use a property of the original object (window completions) that the transferred object (pair response supports) lacks; is it a construction whose output must stay in a fibre or class.

Running those questions over the three proofs gives the obligations below. They overlap heavily — which is the useful discovery: the three constructors do not need three separate theories.

### 7.3 Constructor 1: $\neg$`ConditionalFactorization`

**The definition, exactly** (`Graph/SparseEntropySandwich.lean`). A *skeleton* is a labelled graph on the same $n$ and $m$; the *conditional fibre* of a reference skeleton is the set of skeletons with the same outside code (edges outside the returns and all earlier-exposed coordinates). An exposure order of a family is *realizing* when, for every reference skeleton and every index $i$, the conditional values at $i$ — responses $r_{\pi_i}$ of skeletons in the fibre that agree with the reference on $\pi_1,\ldots,\pi_{i-1}$ — number at least two. Two pairs *overlap* when their response supports meet off both port-return seeds. Then

- `separated`: every pairwise non-overlapping family has a realizing order;
- `concatenate`: if two disjoint, mutually non-overlapping families each have a realizing order, their union has one.

**Ordered split** (Section 4.3): $\neg$`separated`, or `separated` $\wedge$ $\neg$`concatenate`.

**The intended proof of `separated`, as steps.** Fix a separated family, any order, any reference skeleton $H$, any index with pair $\pi=\{p,q\}$. One must exhibit a skeleton $H'$ in the same fibre, agreeing with $H$ on the earlier pairs, with $r_\pi(H')\neq r_\pi(H)$.

| Step | Content | Status | If it fails, $\neg X_i$ hands you | Route |
|---|---|---|---|---|
| S1 | There is a modification of $H$ supported inside $X_\pi\setminus(T(p)\cup\Gamma(p)\cup T(q)\cup\Gamma(q))$ that changes $r_\pi$ | **obligation O1** | $r_\pi$ is a function of the port returns and the outside code on this fibre: a *determined* coordinate with determination support inside $X_\pi$ | This is a rank dependence of a declared coordinate. `lem:target-rank-circuit` (the same alternatives as `lem:mixed-sparse-spine-dependence`): boundary-profile failure = blocker (d); context-universality failure = blocker (e); target-complete proper support = sparse exit (c). All three are excluded on $\Pi_{\rm free}$ and the strict branch. Closing move: **identification with excluded exits** (as at [124]). |
| S2 | The modification preserves $n$, $m$ and the boundary-degree profile of $X_\pi$ | part of O1 | every same-interface, same-size local piece has the same response | the response is determined by interface and size: same route as S1 |
| S3 | It preserves the outside code and every earlier response | **transfers** | an earlier support meets $X_\pi$ off the returns | contradicts `separated`'s hypothesis (immediate) |
| S4 | The result is a skeleton of the model (same class) | part of O1 | the modified piece leaves the class (degree $<3$, or a forbidden configuration) | choose the modification as an *exchange* of the off-return piece for a canonical same-interface piece; if none exists with a different response, S1's route |

So `separated` reduces to one local statement:

> **O1 (fibre-preserving response switch).** On the strict branch, for every $\pi\in\Pi$ and every skeleton $H$ of the model, either there is a skeleton $H'$ in the conditional fibre of $H$ that agrees with $H$ outside $X_\pi\setminus(\text{port returns of }p,q)$ and has $r_\pi(H')\ne r_\pi(H)$; or $r_\pi$ is determined by the port returns and the outside code on that fibre, with an inclusion-minimal determination support inside $X_\pi$.

O1 is a statement about one bounded connected subgraph. Its second alternative is a rank-circuit input, and the manuscript's caution is respected: nothing is derived from label-injectivity or from the absence of a named blocker; the switch is *constructed*, and its non-existence is *routed*.

**`concatenate` needs nothing new.** Order the left family first. For an index in the right family, the candidate $H'$ supplied by O1 differs from the reference only inside $X_\pi$ off the returns; by non-overlap every left support is disjoint from that region off the returns, so left responses are unchanged and the conditional values at the index are the same two values as in the right family's own order. The only content is O1's locality clause, which is why O1 must be stated with it.

**What closes constructor 1.** O1 proved $\Rightarrow$ `ConditionalFactorization` holds $\Rightarrow$ the constructor is empty (the diamond at [178] has an empty no-arm, Section 4.4 Step 2). O1's second alternative $\Rightarrow$ excluded exit $\Rightarrow$ contradiction. Either way the leaf closes; the open work is O1.

### 7.4 Constructor 2: no uncrossing outcome for the retained return package

The intended proof is `lem:window-system-realizability`. Its steps, with what changes for pairs:

| Step | Window version | Pair version and status | If it fails | Route |
|---|---|---|---|---|
| U1 | Choose the obstruction with fewest completion edges, then fewest intersections; orient completions from their root stubs | fewest support edges, then fewest intersections; orient $X_\pi$ from its first demand — **transfers** | — | — |
| U2 | Two intersecting completions: first and last common vertex bound two internally disjoint strands | Completions are paths; $X_\pi$ is a minimum-vertex connected subgraph containing four return paths, so off the returns it is a union of *connector* paths — **obligation O2**: prove the connectors are internally disjoint paths (a cycle or a chord inside a connector contradicts vertex-minimality) | a branching connector: three strands at one first-separation vertex | this is already outcome (iv): at an ambient-cubic separator the cubic-switch absorption `lem:typeA-cubic-switch-absorption`; at a high-degree separator the decorated handoff `lem:typeA-high-degree-handoff` / `def:same-token-routing-germs`, `lem:same-token-bottleneck-routing`. Add it as an explicit arm. |
| U3 | The uncrossed pairing preserves the boundary-degree profile and every previously exposed barrier state | must preserve the profile, the outside code and every earlier-exposed pair response — **obligation O3**, the same locality as O1: the uncrossing touches only $X_\pi\cup X_{\pi'}$ off the returns | an earlier-exposed support passes through the intersection off the returns | then three supports meet at the intersection: either the branching case of U2 (outcome (iv)) or the earlier pair overlaps $\pi$, so $\{\pi,\pi'\}$ was not the minimal obstruction — verify which, and route accordingly |
| U4 | Hit (i); distinguishing context (ii) by `lem:context-universality`; smaller (iii) by `lem:replacement`, `cor:uncompressible`; branching separator (iv); else equal-length neutral strands, identified by node [166] | Same trichotomy — **transfers** — except the last clause: [166] ($Q=E$) rests on `lem:refined-minimality-swap` (global: the order on $(\lvert V\rvert,\lvert E\rvert,\Phi)$ is the counterexample's order and transfers) *and* on `lem:neutral-germ-symmetry` / `lem:two-strand-check`, whose enumeration is at window order 13 and $\ell\le40$ — **obligation O4a (numerical)**: re-run the two-strand check with the pair parameters (return lengths $\le\ell_{\rm ret}$, offsets $0,\ldots,s$), or prove the endpoint argument of `lem:symmetric-pair-endpoint` for returns | a symmetric strand pair among the returns whose closing lengths avoid $\mathrm{Pow}$ | the survivors become explicit table rows (Section 6.6, self-return filter pattern) |
| U5 | Intersection graph has max degree 2; cyclic contradicts minimality; a path, cut at common subpaths, is the serial system | **transfers** | — | — |
| U6 | A cell longer than $D_{\rm sys}$ is read by cold cut-states from both ends; a repeat is an (F1)–(F5) exchange | uses `def:cold-corridor-first-failure`, `lem:cold-corridor-first-failure`, `lem:cold-increment-arithmetic` with $D_{\rm sp}=2M_{\rm cold}+2\ell_{\rm ret}$ — **obligation O4b (ledger audit)**: those lemmas assume `def:surviving-cold-branch`, a state under [22] on the near-cubic side; the strict branch hangs from [19]/[20]. Check every entry of their *Requires* cells against the strict-branch ledger. Either the cut-state machinery is definitional and its routing hypotheses (bridgelessness, absence of the named exits) are on the strict ledger, or the cell-shortening step must be restated on the strict branch with the sparse exits as the (F2) destination | a cross-branch import: a hypothesis of the cold routing lemma absent on the strict branch | this is a *forward/cross-branch reference gap* (rule 7); repair by restating the lemma on the strict ledger — a structural repair, no new mathematics expected |
| U7 | Every choice of one strand per cell closes a simple cycle (two distinct recorded stubs per interface) | the two port returns are the closing pieces; the interfaces use two distinct recorded incidences — **transfers**, with the endpoint incidences of the returns to be checked | — | — |
| U8 | Scale-spanning: otherwise the dependence is supported on a bounded end segment and is an (F5) row | same, with "all cycles through the two demands avoid the tested lengths for a bounded-end reason" — **transfers modulo O4b** (needs the cold table on the strict branch) | a bounded row | cold table (G1/G2/G3) |

So constructor 2 reduces to O2 (easy, vertex-minimality), O3 (the locality of O1 again), and O4 (a ledger audit plus one numerical re-enumeration). No step needs a new global theorem.

### 7.5 Constructor 3: neither arithmetic nor periodic outcome for the serial system

The intended proof is `lem:serial-system-sumset` followed by `lem:system-increment-arithmetic`.

| Step | Content | Status | If it fails | Route |
|---|---|---|---|---|
| A1 | Some increment value is *frequent* ($\ge2D_{\rm sp}^2$ copies); $g$ = gcd of the frequent values | **transfers** from scale-spanning — **obligation O5**: on the strict branch, "boundedly many nonzero cells" must again land in the bounded table | boundedly many nonzero cells | a bounded cold-table row (needs O4b) |
| A2 | The sumset contains $L+r+tg$ for $r\in\mathcal R$ and $t$ in a central range; $\lvert\mathcal R\rvert\ge\min\{s+1,g\}$ from the $s+1$ port-return offsets (the window version used 13 offsets) | **transfers** (Frobenius argument is parameter-free) | — | — |
| A3 | Arithmetic arm: $s+1\le g$ and $g-(s+1)<\operatorname{ord}_g(2)$, so a complete doubling orbit in the central range meets a realized residue: $2^k\equiv L+r\pmod g$ with $L+Cg\le2^k\le L+Tg$ — an actual simple cycle of length $2^k$ | **established** (Lean: `PairSerialArithmetic`, `Spectrum.exists_pow_realized`) | the doubling orbit $\{2^k\bmod g\}$ avoids every realized residue $L+r$ | the periodic arm, A4 |
| A4 | Periodic arm under avoidance: the residue of the route length from $x_0$ modulo $g$ is well defined and transported through every corridor, so target avoidance is a residue property; the finite state (cut-state $\times$ residue) repeats along the system; the segment between two equal states is an exchange | **obligation O6**: (a) pigeonhole on the finite state — cut-state alphabet $Q_{\rm cold}$ times $g$ residues — along the $s$ cells; (b) equal states give an interface-preserving exchange (the cold machinery's exchange lemma, `lem:cold-germ-extraction`, subject to O4b); (c) trichotomy on the pumped graph with actual witnesses | (a) fails only if $s\le Q_{\rm cold}\,g$: the system is bounded — but then A1 said otherwise; make the two bounds agree (numerical) | O5's bounded row |
| A5 | G2: a compatible context distinguishes the pumped graph from $G$ — the context is the witness, target-defective quotient, sparse exit (b); else G3: the pumped graph is a target-complete proper representative — sparse exit (c); at a same-token bottleneck — Type B entry | exhaustive by excluded middle; **obligation O6(c)** is to *construct* the destination objects (both contexts for G2; the smaller representative and its context-universality for G3; the complete same-token entry for Type B), which is what the repair plan asks for | — | (b) and (c) are refuted by the sparse surplus survivor of [125]; Type B is the continuation of [144] |

So constructor 3 reduces to O5 and O6, both resting on O4b.

### 7.6 The repaired graph

Node [182] keeps its number and becomes a decision whose input is the retained data of whichever constructor fired. New nodes are appended after [182]; the numbers below are a proposal and are chosen only to make the plan concrete.

| New node | Diamond | Yes-arm | No-arm (typed) | Consumer of the no-arm |
|---|---|---|---|---|
| [183] | O1: fibre-preserving response switch exists for the retained $\pi$ | constructor 1 is empty; [178]'s positive arm applies | a determined coordinate with a minimal determination support in $X_\pi$ | [184] |
| [184] | rank circuit on the determined coordinate: profile failure / context failure / proper support | — (each alternative is a blocker (d)/(e) or exit (c)) | none: all alternatives are excluded by $\Pi_{\rm free}$ and the strict survivor of [125] | terminal, incompatible with the retained exclusions |
| [185] | O2: connectors of the retained $X_\pi$ are internally disjoint paths | U2–U5 proceed | a branching connector at a first-separation vertex | outcome (iv): cubic-switch absorption or decorated handoff → [144]/[65] |
| [186] | O3: the uncrossing preserves the fibre and every earlier-exposed response | U4 proceeds | an earlier support through the intersection | [185]'s no-arm, or a smaller obstruction contradicting U1's minimality |
| [187] | O4a: the re-enumerated two-strand check at pair parameters leaves no surviving symmetric pair among the returns | identification of neutral strands | surviving lengths | explicit table rows (cold table pattern) |
| — | O4b is not a node: it is a per-lemma *Requires* audit of the cold-corridor imports against the strict-branch ledger | | | if a hypothesis is missing, restate the lemma on the strict branch (structural repair) |
| [188] | O5: a frequent increment exists | A2–A3 | boundedly many nonzero cells | bounded table row |
| [189] | A3: the doubling orbit meets a realized residue | power-of-two cycle: terminal | orbit avoidance data $(g,\mathcal R,L)$ | [190] |
| [190] | O6: repeat state along the system with an interface-preserving exchange, then G1/G2/G3/Type B on the pumped graph | terminal (hit), or exits (b)/(c) refuted by [125], or Type B → [144] | none once O6(b),(c) are proved | — |

Every no-arm has a consumer, so the repaired subgraph is architecturally complete in the sense of Section 3.6. The mathematical content is O1–O6.

### 7.7 What this establishes, and in what order to do the work

It does not prove [182]. It converts one opaque leaf into six local obligations, each a statement about a bounded connected subgraph or a finite arithmetic object, each with a named closing move and a typed failure route — which is exactly what the method promises to do with an open node, and exactly what the manuscript's own [178]–[180] left undone. The order of work is dictated by dependencies, not difficulty:

1. **O4b first** (cross-branch ledger audit of the cold-corridor imports). It is not new mathematics, but it may change the statement of U6, A4 and O5, and it is the most likely place for the window-to-pair transfer to have silently failed. Do it as a table: for each of `def:cold-corridor-first-failure`, `lem:cold-corridor-first-failure`, `lem:cold-germ-extraction`, `lem:cold-increment-arithmetic`, `lem:cold-bounded-germ-trichotomy`, list the Requires cell and mark each entry present/absent on the strict ledger.
2. **O1** (the switch lemma). It closes constructor 1 outright and is the locality clause that O3 reuses. It is one bounded-support lemma with a rank-circuit fallback.
3. **O2 and O5** (vertex-minimality; frequent increment). Short.
4. **O4a** (numerical re-enumeration at pair parameters). Mechanical; the code exists (`Graph/TwoStrandEnumeration.lean`) and needs new parameters.
5. **O6** (repeat-state exchange and the three destination witnesses). The only item with genuine constructive content beyond the window case.

### 7.8 The Lean shape

Each obligation is a `Decision` on the strict-branch ledger, appended to `Graph.Strategy.Spine.Key` with the next unused index (six vocabulary entries each, never renumbering). The three constructors of `PairUncoveredResidual` are the literal inputs read by the new rows: `factorization system failure` is consumed by the O1 row, `systemRealizability returns failure` by the O2/O3 rows, `incrementArithmetic serial failure` by the O5/O6 rows. Closures use the existing incompatibility of the retained exclusions (`selectedStrictSurplusBranch` already carries the sparse-exit survivor facts), or publish the Type B entry through the common `TypeBFanEntryStatement` — without adding a disjunct to it, which is the [177] mistake the repair plan records. No detached theorem carries an obligation's content; O1 is proved inside its row's sealed executor and published under its key.

---

## 8. Closing [181]: the protocol applied to the peeled target-defect demand residual

Node [181] is a different kind of open node from [182]. Its retained data is not a negated implication but an exact accounting state, and the manuscript offers a *consumer* for it: `cor:typeA-large-budget-closure-open-pressure` closes the branch if $\mathsf P_{\rm open}=o(\lvert R\rvert)$, refined by `prop:typeA-exit4-closure-from-zero-shadow` to $\mathsf P^{+}_{\rm zero}<\varepsilon_{\rm prim}\lvert R\rvert$. The protocol's first step at such a node is not to start proving the consumer's hypothesis; it is to audit the consumer against the ledger that produced the residual. Doing so here shows that the offered consumer is vacuous, relocates the obligation to the step that actually failed, and identifies the move that closes it. Every inequality used below is a displayed inequality of the manuscript; the only new content is putting them side by side.

### 8.1 What [181] literally is

The complete structural accounting of the counterexample at [181] — the node path with the arm taken at each diamond, every fact on the branch state by register category with its source and the technique that produced it, the upstream techniques with the properties each consumed, the typed leaf data, and the closure theorem whose hypotheses are exactly those facts — is `node_181_structure.md`. This section is the summary; that file is the record.


On the large-budget branch (near-cubic spine, $\theta\le\theta_{\rm win}+o(1)$, hence $\defp(R)-\sigma(R)\le\tau_{\rm win}\lvert R\rvert+o(\lvert R\rvert)$ with $\tau_{\rm win}=0.2282<\tfrac14$), the chain that ends at [181] is:

| Step | Statement | Source |
|---|---|---|
| Unified negative collection | $\tilde{\mathcal X}=\{X:\sigma(X)=0,\ \No(X)<0,\ \text{no Type B handoff}\}$, $\tilde D_A=\sum_{X\in\tilde{\mathcal X}}\bigl(\tfrac14\lvert V(X)\rvert-\defp(X)\bigr)$ | `def:typeA-unified-negative` |
| Deficit lower bound | $\tilde D_A\ \ge\ \tfrac14\lvert R\rvert-(\defp(R)-\sigma(R))-o(\lvert R\rvert)\ \ge\ (\tfrac14-\tau_{\rm win})\lvert R\rvert-o(\lvert R\rvert)$ | `lem:typeA-unified-deficit` |
| Entries and burden | $\tilde\Xi=\{(X,w,u,B_u)\}$ indexed by silent unpaid routed loads; $\tilde N=\lvert\tilde\Xi\rvert\ge4\tilde D_A$ | `def:typeA-unified-entries`, `lem:typeA-unified-burden` |
| Core | every entry has an essential-incidence core $\mathcal C_{\rm ess}(\xi)\subseteq\partial_EX$ with $\lvert\mathcal C_{\rm ess}(\xi)\rvert\ge2$; $\pi_{\mathcal X}(\xi)$ = number of *private* essential incidences | `lem:typeA-unified-carriers`, `def:typeA-route8-carriers` |
| Two-support reduction | if every entry had $\pi\ge3$, then $3\tilde N\le\defp(R)\le\tau_{\rm win}\lvert R\rvert$ against $\tilde N\ge12(\tfrac14-\tau_{\rm win})\lvert R\rvert$, impossible since $\tau_{\rm win}<3/13$; so a two-support entry ($\pi\le2$) exists | `prop:typeA-unified-reduction` |
| Route-8 two-support | terminal two-support obstruction, excluded at [124] | `thm:typeA-two-carrier-nogo` |
| Target-defect two-support | **peeled**: the load leaves the pure Type A sum, $\Lambda_4$ drops by one, the deficit drops by $\tfrac14$; "the witness serves only as a routing record" | `def:typeA-exit4-peeling`, `lem:typeA-exit4-discharge`, `lem:typeA-exit4-finite-descent` |
| Loop | repeat on the reduced ledger while $\tilde D_A^{P_4}\ge(\tfrac14-\tau_{\rm win})\lvert R\rvert-o(\lvert R\rvert)$ | `lem:typeA-peeling-reduced-reduction` |
| [181] | the reduced-rate test fails: $\tilde D_A^{P_4}<(\tfrac14-\tau_{\rm win})\lvert R\rvert-o(\lvert R\rvert)$, with $4\tilde D_A=4\tilde D_A^{P_4}+p_4$; the $p_4$ peeled entries carry the missing deficit; the $2/3$-demand ledger, absorbers and window blockers are run on the full $\tilde\Xi$ | `thm:large-budget-route8-only`, `def:typeA-peeled-demand-residual` |
| Offered consumer | closes if $\limsup\mathsf P_{\rm open}/\lvert R\rvert<\varepsilon_{\rm press}=12(\tfrac14-\tau_{\rm win})-\tau_{\rm win}=0.0337$; equivalently if $\mathsf P^{+}_{\rm zero}<\varepsilon_{\rm prim}\lvert R\rvert$ with $\varepsilon_{\rm prim}=0.0033$ | `prop:typeA-exit4-closure-from-open-pressure`, `prop:typeA-exit4-closure-from-zero-shadow` |

### 8.2 Step 1 — audit the consumer: the offered closure is vacuous on the branch

$\mathsf P_{\rm open}$ is not a free quantity. It is defined as the unpaid part of a demand of three incidences per entry, and the ledger's own no-overcount identity fixes it from below. On any branch where the type (A2) absorbers have routed (the branch of the corollary), `lem:typeA-pressure-absorber-no-overcount` gives

$$3\tilde N-\mathsf P_{\rm open}\ \le\ \defp(R).$$

Combine with the burden and the deficit bound:

$$\mathsf P_{\rm open}\ \ge\ 3\tilde N-\defp(R)\ \ge\ 12\tilde D_A-\defp(R)\ \ge\ 3\lvert R\rvert-13\defp(R)+12\sigma(R)-o(\lvert R\rvert)\ \ge\ \bigl(3-13\tau_{\rm win}\bigr)\lvert R\rvert-o(\lvert R\rvert).$$

And $3-13\tau_{\rm win}=12(\tfrac14-\tau_{\rm win})-\tau_{\rm win}=\varepsilon_{\rm press}$. So on the whole large-budget branch

$$\liminf_{\lvert R\rvert\to\infty}\frac{\mathsf P_{\rm open}}{\lvert R\rvert}\ \ge\ \varepsilon_{\rm press},$$

which is the negation of the corollary's hypothesis. Consequences, each a one-line corollary of the display:

1. `prop:typeA-exit4-closure-from-open-pressure`, `cor:typeA-large-budget-closure-open-pressure`, `prop:typeA-exit4-closure-from-window-blockers` and `prop:typeA-exit4-closure-from-zero-shadow` are true but vacuous: their hypotheses cannot hold on the branch they are stated for. Any lemma that proved one of those hypotheses would already be a proof of the contradiction by other means.
2. Since $\mathsf P_{\rm open}\le2p_{13}+\mathsf P^{+}_{\rm zero}$ (`lem:typeA-open-pressure-zero-shadow-excess`), the zero-signature excess is forced linear: $\mathsf P^{+}_{\rm zero}\ge\bigl(\varepsilon_{\rm press}-\tfrac{2\theta}{1-13\theta}\bigr)\lvert R\rvert-o(\lvert R\rvert)\ge\varepsilon_{\rm prim}\lvert R\rvert-o(\lvert R\rvert)$. The remark `rem:typeA-zero-shadow-numerics`, which says the residual satisfies $\mathsf P^{+}_{\rm zero}\ge0.217\,p_{13}$, is not describing a hard case; it is describing every case.
3. The same-window two-blocker cap (`def:typeA-same-window-open-blocker-cap`) is false on the branch, not merely unproved.
4. No bound on $\mathsf P_{\rm open}$ in any window-side currency can close [181]. The payer for the open units — boundary incidences, $\defp(R)\le15p_{13}+\sigma_W$ — is the same stub supply the demand side has already exhausted; a window's fifteen stubs *are* the incidences of the supports attached to it.

In the vocabulary of Section 9 (anti-patterns): the window-blocker accounting is a re-encoding. It relocated the unpaid demand into a new named quantity without changing the payer, and then asked for that quantity to be small. The methodology catches this with a one-line check: **before attacking an open node, compute what the incoming ledger already forces about the quantity its consumer needs; if the forced bound contradicts the needed bound, the consumer is vacuous, and the residual was produced by a diamond on the wrong hypothesis.** (Section 4.6, step 0.)

This is not a claim that the manuscript's ledger lemmas are wrong; every one of them is correct. It is the observation that the peeling loop plus the demand ledger cannot be completed into a proof by any bound on $\mathsf P_{\rm open}$, so the work must be relocated.

### 8.3 Step 2 — the hypothesis that actually failed

Read [123] again with the both-sides test. The pay rule is $H$: *every unified entry owns three private essential incidences* ($\pi_{\mathcal X}(\xi)\ge3$). On $H$ the branch closes numerically (two-support reduction). $\neg H$ is a two-support entry; it splits into route-8 (closed at [124] by identification with exit (4)) and target-defect. At a two-support target-defect entry the manuscript *peels*: it removes the load from the Type A sum and records a witness. That is not one of the closing moves of Section 5: the deficit $\tfrac14$ is neither paid, nor contradicted, nor handed to a ledger with capacity. It is moved to the exit-(4) ledger, whose only consumer is the vacuous corollary of 8.2. So the peel violates the progress invariant (Section 9, "re-encoding the difficulty"): the residual is relocated, not made smaller, charged, or routed.

What [181] therefore carries, stripped of the relocation, is a **linear family of two-support target-defect entries**. How many: with $N_3$ the entries having three private incidences, $3N_3\le\defp(R)\le\tau_{\rm win}\lvert R\rvert$, so the two-support entries number at least $\tilde N-N_3\ge\bigl(1-\tfrac{13}{3}\tau_{\rm win}\bigr)\lvert R\rvert-o(\lvert R\rvert)\approx0.011\lvert R\rvert\approx0.74\,p_{13}$. The exact constant is irrelevant; what matters is that the stub accounting shows *any* linear family of such entries defeats the count. So the closing move cannot be a count. It must be an exclusion: the analogue, for target-defect entries, of what [124] does for route-8 entries.

### 8.4 Step 3 — the residual's typed data and the currency check

A two-support target-defect entry $\xi=(X,w,u,B_u)$ carries:

- a support $X$, connected, subcubic, $P_{13}$-free, hence of diameter $\le11$ and $\lvert V(X)\rvert\le6142$ (the manuscript's own bound, §"Type A: low-deficiency $P_{13}$-free piece"); every boundary edge of $X$ goes to a packed window;
- a saturated receiver $w$ and a silent unpaid routed load $u$ with trace $T_u$ from $u$ to $w$, and the trace basin $B_u$;
- the core $\mathcal C_{\rm ess}(\xi)$ with $\lvert\mathcal C_{\rm ess}\rvert\ge2$ and at most two private members;
- the defect token $(q,S_0,S_1,Y,E)$: a trace-local quotient $q$ forgetting an internal $u$-supported coordinate $r$ (a trace, channel, connector-band or wedge coordinate — the coordinate types of `def:typeA-trace-basin` whose support contains an internal edge), two realizations $S_0$ (actual) and $S_1$ in the same boundary-degree fibre with $q(S_0)=q(S_1)$, and a compatible context $Y$ such that the lexicographically first event $E$ — a simple cycle or edge-rooted return through an internal edge of $B_u$ and an edge outside $X$ — has different target predicates in $S_0\oplus Y$ and $S_1\oplus Y$; by cut parity $E$ crosses $\partial X$ at two or more incidences of $\mathcal C_{\rm ess}$ (`lem:typeA-pressure-token-two-carriers`);
- for each $c\in\mathcal C_{\rm ess}(\xi)$, a $c$-deletion witness: a realization $S_c$ of $\rho_u(B_u)\vert_{\mathcal C\setminus\{c\}}$ and a context $Y_c$ whose event $E_c$ uses a coordinate with boundary-incidence support containing $c$. `lem:typeA-essential-deletion-witness` and `lem:typeA-deletion-witness-declared` are stated for route-8 entries, but their proofs use only inclusion-minimality of the core and the definition of $D$-restriction, both of which `lem:typeA-unified-carriers` supplies for target-defect entries. Restating them on the unified ledger is a structural repair with no new mathematics (a check, not an obligation).

Currency check (Section 5.2) for a linear family of such entries — a *diagnostic*, run after the inventory of §4.7 and never a substitute for the typed object above:

| Currency | Available on the branch? |
|---|---|
| Boundary incidences / net charge | Exhausted: this is the stub supply $\defp(R)\le\tau_{\rm win}\lvert R\rvert$ that the demand already overruns (8.2). |
| Entropy | Linear bit counts: no (they shift $\theta_{\rm win}$ by $O(1/\log n)$). **Relabeling entropy: yes.** $\mathcal G(R)$ is closed under relabeling of $V(R)$ and $R$ has at most $\defp(R)$ bounded components, so its orbit has $(1-\tau)\lvert R\rvert\log\lvert R\rvert$ bits; applied to the window-state map on near-cubic skeletons this sharpens the cap to $\theta^\ast=0.00803$, $\tau^\ast=0.1346$ and lowers the required charge per entry from $3$ incidences to $0.29$ (`closure_proofs.md`, Part IV). This was the currency the residual needed, and the first version of this table wrongly marked it exhausted. |
| Obstruction rank | Already forced full (`lem:full-rank`) and already paid in the entropy form; a target-defective quotient does not reduce rank (it "cannot witness a target-dependence"). |
| Compression | Exit (5): available if a smaller representative with the same exact response exists; a two-support target-defect entry is not itself a compression. |
| Constraint: hit, arithmetic, label relation | Exits (1)–(3): a return of Mersenne length through a port; two internally disjoint returns through one port with lengths summing to a power of two; a violated $P_{13}$ label relation $C_s$. |
| Support dependence, handoff | Exits (6), (7). |

So the closing move must produce, from the witnesses, one of exits (1)–(3), (5)–(7). That is exactly the shape of `thm:typeA-two-carrier-nogo`, whose proof produces exit (4) and then contradicts the *absence* of exit (4) in a true route-8 entry. For a target-defect entry exit (4) is present, so (T2) fails and the [124] proof cannot be reused as is: the first failing step of the transferred proof is (T2), and its negation is the entry's own definition. The method then says: go one level deeper into what the three witnesses give.

### 8.5 Step 4 — the replacement move: a two-support target-defect no-go (O7)

> **O7 (two-support target-defect no-go).** On the large-budget branch, let $\xi\in\tilde\Xi$ be a target-defect entry with $\pi_{\mathcal X}(\xi)\le2$, with defect token $(q,S_0,S_1,Y,E)$ and deletion witnesses $(S_c,Y_c,E_c)$ for $c\in\mathcal C_{\rm ess}(\xi)$. Then one of exits (1), (2), (3), (5), (6), (7) occurs at $w$ or at the window interfaces of $E$, $E_{c}$.

With O7 in place, [181] is empty: `prop:typeA-unified-reduction` yields a two-support entry; if route-8, [124]; if target-defect, O7. No peeling occurs, no reduced ledger is needed, and the corollary of 8.2 is never invoked.

**Intended proof of O7, as steps, with the failure route of each.** The three events $E,E_{c_1},E_{c_2}$ are simple cycles (add the root edge if edge-rooted) through the basin and the exterior, each with an alternative realization of the basin that changes its length to a power of two while keeping the boundary-degree profile and the coarse data.

| Step | Content | Fails when | Route |
|---|---|---|---|
| Y1 | The crossings of $E$, $E_{c_1}$, $E_{c_2}$ with $\partial X$ are completion-port, first-entry or packed-window interface incidences (`def:typeA-route8-carriers`); each event is therefore an anchored return through a port of a receiver of $X$, or a return through a window interface | — (definitional) | — |
| Y2 | Two of the three events pass through the *same* port or the same window and are internally disjoint as anchored paths | they share an internal segment, so their first separation is a branching vertex of the basin | at an ambient-cubic separator this is the cubic-switch configuration (`lem:typeA-cubic-switch-absorption`, exit (4) of type (Q4) — a *bounded* exchange, see Y4); at a high-degree separator it is the decorated handoff (`lem:typeA-high-degree-handoff`), exit (7) |
| Y3 | Arithmetic: with lengths $\ell,\ell'$ and the length shifts $\delta,\delta'$ supplied by $S_1,S_c$ (so that $\ell+\delta$ and $\ell'+\delta'$ are powers of two), the two returns through one port realize exit (1) (a Mersenne return) or exit (2) ($\ell+\ell'\in\mathrm{Pow}$), or through one window the label relation $C_s$ fails, exit (3) | all combinations of the three actual lengths and the three shifts avoid the powers of two and satisfy $C_s$ | the retained data is a finite arithmetic object: three lengths bounded by $\lvert V(X)\rvert+$ corridor bounds, three shifts, and window offsets in $\{0,\ldots,12\}$; this is the shape of `lem:cold-short-self-return-filter` and of `lem:typeA-singleton-shadow-table` — compute the exception set exactly and carry it as a table |
| Y4 | Any surviving table row is a bounded configuration (support $\le6142$ vertices, three declared events, alternative realizations); run hit / defect / compression on it: a hit is exit (1)–(3); a compression of the basin by the alternative realization (same response against every context, strictly smaller) is exit (5); a context-dependence delocalizing to a proper support or the whole graph is exit (6) | the configuration is neutral: no context distinguishes and no smaller representative exists | then the actual basin $B_u$ is its own canonical representative and $q$ was *not* target-defective — contradicting the token; so this arm is empty (this is the same "silence is a compression licence" step as G3 in `lem:cold-bounded-germ-trichotomy`, and it must be verified against `def:typeA-trace-basin`'s alternative (b)) |

**Failing step of this plan (recorded under rule 14).** Y1 and Y3 treat $E$, $E_{c_1}$, $E_{c_2}$ as returns of $G$ with actual lengths. They are not: each is a cycle of $S\oplus Y$ for a hypothetical context $Y$ and, for $E$, possibly a hypothetical realization $S_1$; only their $X$-parts in $S_0$ are actual. Exits (1)–(3) require actual returns, so Y3 cannot produce them from the tokens (rule 15). The plan is repaired by replacing the tokens with the actual objects they are attached to — the silent loads, their pockets, the actual returns of the port-return corollary (removed) and the packing — as in the corrected §4.7 inventory. Y3's failure arm was described as the only place where new work is required, and it is a finite computation of the same kind the manuscript already performs twice (the self-return filter and the singleton-signature table).

**Failure route of O7 as a whole.** If O7 fails at a specific entry, its no-arm carries a bounded object: the support, the basin, the three events and their alternative realizations. By the diameter bound this is a finite datum, so the terminal move is *default refinement then finite certification* (moves 10 and 15 of the web-app table): promote the type of the forgotten coordinate $r$ (trace-incidence / return / connector band / wedge — a four-letter alphabet from `def:typeA-trace-basin`) to a label, partition the residual by it, and certify each fibre by enumeration at the bounded parameters. An open leaf of the form "a bounded configuration that no local test sees" is exactly what the method calls a certificate of type finite check; it is a computation, not an open case.

### 8.6 The repaired graph

| Node | Change |
|---|---|
| [123] | Unchanged input (unified deficit, entry census). Its first step is `prop:typeA-unified-reduction`: a two-support entry exists or the branch closes numerically. Its second step is the route-8 / target-defect split, unchanged. |
| [124] | Unchanged: route-8 two-support → terminal obstruction → contradiction. |
| [181] | Keeps its number; becomes the decision **O7** on the retained two-support target-defect entry. Yes-arm: exits (1)–(3), (5)–(7), each an existing closed row. |
| [191]–[193] (proposed) | O7's proof steps Y2–Y4 as diamonds: [191] disjointness (no-arm → cubic switch / handoff); [192] arithmetic (no-arm → finite exception table); [193] table rows → hit / compression / dependence (no-arm empty by the token). |
| Deleted as closure devices | the peeling loop, the reduced ledger, the $2/3$-demand ledger, absorbers and window blockers *as consumers*. They may remain as bookkeeping, but nothing below [181] cites $\mathsf P_{\rm open}$ or $\mathsf P^{+}_{\rm zero}$ as a hypothesis. The corollaries of 8.2 are retired (replace, don't accrete). |

Every no-arm has a consumer; the mathematical content is O7.

### 8.7 What this establishes and the order of work

Established here: (i) the offered consumer of [181] is vacuous on its own branch (8.2, four displayed inequalities of the manuscript); (ii) the residual is, exactly, a linear family of two-support target-defect entries (8.3); (iii) every counting currency of the proof is exhausted for that family, so the closure is an exclusion (8.4); (iv) the exclusion is O7, a local statement about one bounded support, with a stepwise proof plan whose only nontrivial arm is a finite arithmetic table (8.5).

Not established here: O7 itself. It is a theorem about a bounded object with three declared near-miss events, and nothing in the method prevents proving it; the method has reduced [181] to it and told us which move family (constraint: exits (1)–(3)) it must land in.

Order of work:

0. (Optional, not a prerequisite for O7.) The relabeling-entropy cap (`closure_proofs.md` Theorem 1.5) sharpens $\tau_{\rm win}\to\tau^\ast=0.1346$; it changes constants, not the object or the move.
1. Record 8.2 in the audit (one row: the four propositions are vacuous on the branch). This stops any further effort on window-blocker bounds.
2. Restate `lem:typeA-essential-deletion-witness` and `lem:typeA-deletion-witness-declared` on the unified ledger (structural, no new mathematics).
3. Prove Y1–Y2 (definitional and structural).
4. Compute the Y3 exception table at the bounded parameters; if empty, O7 is proved.
5. If nonempty, run Y4 on each row; the last arm is empty by the token.

### 8.8 Plan repair under rule 14

Recorded after executing the O7 route with rules 15–17 in force.

- **First failing step of the O7 plan:** Y2/E3 — the second return through the port is not internally disjoint from the first; the no-arm is the theta closure, an accounted row. Under rule 17 exit (2) was inadmissible because disjointness was never a present row.
- **State of the [181] inventory:** every actual local row is accounted (target-safety, exits (1)–(3), theta/ear closures, I5, contraction criticality, pocket spectra); the unaccounted rows are certificates (rule 15) or global. The finite certification of two-attachment pockets is a lower bound on their size ($\ge17$ vertices; `closure_proofs.md`, search record), which is the wrong direction for closure. There is no admissible closing move at [181].
- **Consequence (§4.4 step 1):** [181] is a symptom. The information that would close it is discarded upstream, at the point where a silent load is reduced to one unit of unpaid count: `lem:typeA-silent-excess-count` counts $u$ and forgets that $u$ lies in a receiver-free cubic pocket $K_u$ (the pocket lemma (removed)) — a sub-support with its own boundary (its $m\ge2$ attachment edges to the trace) to which the Type A ledger itself applies.
- **Repair to record at that node (not at [181]):** the diamond "does the pocket of a silent load carry its own receivers?" — its yes-arm recurses the Type A ledger on the pocket with the trace vertices $b_i$ as receivers (well-founded: the pocket is a proper subgraph), and its no-arm is a pocket with no silent loads, which is rate-bounded by the ledger's own constant. This is the well-founded decomposition of `closure_proofs.md` Step 8, done on the manuscript's object instead of a projection of it, and it is the only move on the record whose arms both shrink the object. Executing it is work at the upstream node and is therefore outside the scope of [181]; it must be planned there first (rule 14).

### 8.9 The Lean shape

In `selectedRouteEightCensus` the `.right failedStage` arm currently runs `route8DemandLedgerDichotomy`, `route8DemandAbsorptionRow`, `route8WindowBlockersRow` and publishes `K .route8PeeledDemandResidual`. Under the repair that arm is replaced by a `Decision` on the two-support target-defect entry whose yes-arm closes through the existing exit incompatibilities and whose no-arm publishes the bounded configuration under a new key (next unused index, six vocabulary entries). `route8PeeledDemandResidual`, its rows, and `selectedLargeBudgetPressureCensus`'s residual output are deleted in the same change, not left as a parallel path. Nothing carries O7's content outside its row's sealed executor.

---

## 9. Anti-patterns and failure modes

### 9.1 The eight LLM failure modes and their disciplines

| Failure | What it looks like | Discipline |
|---|---|---|
| **Lost forward tracking** | An estimate, error term or residual is carried through many steps and quietly loosened, dropped, or applied under hypotheses that no longer hold; each step is locally plausible | Nothing is carried informally. Whatever a tool cannot absorb becomes a branch of its own, restated as a typed residual carrying the data its next consumer needs |
| **Extrapolation beyond standard material** | A branch relies on a theorem recalled from memory, a strengthening of a cited one, or a result the literature does not contain | Imports are fixed before step one and never grow. A branch needing a new global theorem is a defect, repaired by refining the case structure |
| **Omitted difficult steps** | "This structure should be impossible," "this cannot happen generically" | A branch closes only in one of a fixed finite list of certificate types; such phrases are prompts for stratification; an omitted step is a leaf without a certificate, detectable syntactically |
| **Unsupported global estimates** | A single counting, entropy or spectral inequality that resolves everything; hides an independence assumption, a double count, an absorbed boundary term | Inequalities enter only in ledger form $\lvert\mathcal D\rvert\le C\lvert\mathcal P\rvert$ from a canonical scheme with a bounded-multiplicity lemma; every ingredient is a named local claim |
| **Re-encoding the difficulty** | "One more lemma" whose statement restates the problem at another level | Progress invariant: every step outputs a closed branch or a strictly smaller named residual; an unconditional statement about all large objects is a new global theorem |
| **Untyped residuals** | "The object has none of the structures the tools require," treated as a reason to stop | Absence of a feature is a positive fact and is routed: it feeds a budget, strengthens an exclusion, creates a repetition payload, or triggers a language extension. An untyped residual is an invalid worksheet row |
| **Deferential agreement** | Accepting a supplied step whose hypotheses, quantifiers, branch state or output type do not match the obligation | Agreement has no formal status. A step enters only as a row with declared inputs and typed output; the response to a bad row is a typed reject, a named residual, or a routed payload |
| **Status-cue audit drift** | "Famous open problem, so the step must be wrong," or "must be right" | Status is context, not certificate or defect. An objection must name a failed schema, a missing import, a stale branch state, an unconsumed payload, an unregistered theorem, or a scope issue. "Open problem" is not a terminal |

### 9.2 Paper-level anti-patterns

- **Renaming an unproved residual as a closed row.** The remedy is [182]: keep the exact negation and its retained data.
- **Assuming independence.** "The overview above is an exhaustive sequence of alternatives, not an assumption that the local restrictions are probabilistically independent." Every product sentence is a diamond ([158], [170], [178]).
- **Double charging one saving.** An overlap is charged once to its minimal connected support; the compression is read in the class the budget does not already charge.
- **Sufficient-order conditions.** A residual that carries a quantity exactly must be decided on the object, not by "$n$ large."
- **Bounding a routed residual into nothing.** A remainder that is "$o(n)$ and discarded" is a residual with a consumer, not a loss (6.1).
- **Reading a structural-exhaustion proof as a linear proof.** All five reading errors of 2.3.
- **Treating a terminal as universal.** Target defect is a contradiction at [37] *because* the branch also carries a context-universal quotient; elsewhere it is a routed exit.
- **Using a routed-forward closure interface as an upstream hypothesis** and then announcing circularity.

### 9.3 What is not a repair

- Changing a constant so that the arithmetic works without checking the moves × budgets table.
- Weakening a lemma's statement so that its proof goes through, when downstream consumers read the stronger statement.
- Adding a hypothesis to an interface theorem's *statement* instead of to a diamond above it (this silently reopens every consumer).
- Deleting a correct paper fact because its current transport or proof is broken.
- Closing a branch with a sentence.

---

## 10. Recording the repair

A repair is not finished until the artifacts agree. Each has a distinct job; none is redundant.

| Artifact | What to update after a repair |
|---|---|
| **Proof-dependency diagram** | Replace the old step by a diamond; draw the yes-arm into the existing continuation; append the new nodes with fresh numbers; give every new terminal the right shape (solid = closed here; dashed = proxy for a closure drawn elsewhere); add "continue at [n]" arrows. Only the live state is drawn |
| **Diagram map and node-by-node audit table** | One row per new node: input, output, mathematical source |
| **Detailed dependency table** (Item · Node(s) · Node/theorem · Formal content · **Failure route** · Label) | A new item for the repair, whose *Failure route* cell names where each arm goes — this cell is what makes the leaf-totality check mechanical |
| **Constraint ledger** (invariants 1–44) | If $\neg H$ or a new closure becomes a reusable fact, give it an invariant number with "where introduced / where consumed / role." Ledger-invariant numbers and node numbers are separate namespaces |
| **Per-lemma requirements table** (Result · Stage · Node(s) · Requires · What it does · Role) | Every new lemma, with its Requires cell. Then run the check: every invariant in Requires is established at an earlier-or-equal node; a later one is a forward-reference gap |
| **Resilience appendix** (Node · Closing lemma · Closing condition · Slack · Redundant cover · Residual counterexample) | For each new closing cell, what survives if its lemma is false: all standing invariants plus the negation of the conclusion. "No leaf degrades to nothing" |
| **Monotone-hypothesis / moves × budgets table** | Re-check that each new deletion, replacement, peel, transfer or handoff preserves every account it touches |
| **Node audit table** (Lean) | Gate A/B/C verdicts for the row; the applicable CT(s); the manuscript label(s). Live status goes only in the two tables, never in prose |

What "closed" means depends on the gate. A branch is *architecturally* closed when its leaf has a consumer or certificate (checkable by structure). It is *mathematically* closed when the edge lemmas are correct (review). It is *mechanically* closed when the Lean term elaborates with no unfinished producer (Gate A), publishes the manuscript's proposition (Gate B), and uses only the canonical carrier (Gate C). Passing one gate never implies another; a row whose `Holds` proposition is weaker than the manuscript's lemma composes and closes, and Gate A cannot detect it.

---

## 11. The same discipline in Lean

The Lean framework (`hypostructure/Hypostructure/`) makes the branch state a type. `ExactLedger Domain residual factKeys` carries the active residual and the full list of established facts as *type indices*: a step invoked on a branch lacking its hypotheses is a type error, commits are append-only, and fact values are proof-irrelevant (every `Value` type is a subsingleton, so no side channel can be smuggled through a fact). The consequences for repair:

- **A residual is a non-`False` proposition in the codomain, never a `sorry`.** The EG tree has zero `sorry`/`admit`. Node [181] is the key `K .route8PeeledDemandResidual` returned by `selectedRouteEightCensus`; node [182] is `PairUncoveredResidual`, "the disjoint union of exactly three negated paper implications." The root boundary `selectedLedgerBoundary` returns a disjunction of the surviving semantic propositions; "None is definitionally `False`, so successful elaboration does not close them."
- **A diamond is `Decision.run`** and a `match` on `.left`/`.right`. Each arm receives a ledger extended by the yes-key or the no-key.
- **A closure is `.elim` on a `False` fact read back from the ledger**, or the framework's `closeIncompatible`/`runAndCloseIncompatible` followed by `elimClosed`. Example (node [124] inside [123]):

  ```lean
  | .left trueStage =>
      let closed := (route8UnifiedTerminalNoGoRow …).run trueStage (by simp [K_eq_iff, terminalFresh])
      exact (closed.get (K .route8TerminalNoGo)).down.elim
  ```

  and a pure-closure row (`selectedSpineSurplusEstimateCloses : … → False`) reads two facts and applies `Nat.not_lt_of_ge`.
- **A routed residual is a returned key list**, with the docstring saying what the row does *not* claim: "this wrapper does not claim `False` from `[181]` and does not absorb the earlier quotient or Type B residual decisions into node `[123]`."

The skill `.claude/skills/eg-proof-expansion/SKILL.md` is the Lean mirror of Section 4:

- *One label per turn.* Identify the single first failing label; copy its exact proposition, hypotheses, alternatives and strategy from the manuscript; do not infer a stronger prerequisite or a different strategy. Build the narrow target; report the first downstream failure; stop.
- *Never reassign; append.* Adding a key means six entries in `SpineVocabulary.lean` (`Holds`, `label`, `idx`, `ofIdx`, `name`, `LabelPins`); "give `idx` the next unused number and never renumber an existing key" — the audit name carries the index.
- *One carrier.* Read facts only through sealed `FactInputs.current`/`FactInputs.get`; publish only through a literal `FactManifest` and `AtomicCT.run`. No detached theorem, helper, wrapper, callback, side carrier or shim that carries the selected label's content; if one exists, inline it and let the downstream failure be loud.
- *Never weaken a correct fact because its transport is illegal.* Delete an illegal wrapper only while repairing the valid mathematical proof it transported.
- *Failure reports are table-driven.* Name the row as `Node [n]`, every manuscript label, the first exact proposition Lean does not establish (with its full formula), and one defect class: proof absent / statement weakened or strengthened / proved but not published / published under the wrong schema / published but not wired / illegal read-write or carrier / wrong branch ancestry / downstream interface mismatch.
- *Audit hygiene.* No changelog or narrative in `Assembly_node_audit.md`; live status lives in the two tables; run the static gates before and after.

---

## 12. Checklists

### 12.1 Before touching a branch

- [ ] I have identified the *first* failing node, not a downstream symptom.
- [ ] I have written $\llbracket B_{k-1}\rrbracket$: every invariant at an earlier-or-equal node, every exclusion, the active case, the residual data.
- [ ] I have read the whole conjunction of facts, not one lemma in isolation.
- [ ] I have followed the directed graph and the Requires column, not prose citations.
- [ ] I have checked whether a routed residual already covers what I think is missing.

### 12.2 Admitting a dichotomy

- [ ] $H$ is written as an exact proposition about the object on this branch, quantifiers included.
- [ ] $H$ is not already on the record (else cite it; if it is a conjunction, use the ordered split).
- [ ] The yes-arm is the old continuation with $H$ stated; no interface theorem's statement changed.
- [ ] $\neg H$ is typed: I can say what object, witness, fibre, count or bound it hands the next move.
- [ ] Both sides are productive (both-sides test).
- [ ] New nodes are appended after the last existing number.

### 12.3 Closing a residual

- [ ] The object being closed is the residual as typed by its producer, not a restatement (Rule 0, §4.8).
- [ ] Each split made on the way passes the locality and consumption tests of §4.8.

- [ ] I named the currency (compression / quantity / constraint) and the row of the selection table.
- [ ] The move uses only branch-state facts, fixed inputs, and textbook material.
- [ ] The move makes well-founded progress (strictly smaller named residual, or a certificate).
- [ ] Every witness the consumer requires is *declared* on the branch, not reconstructed.
- [ ] For charging: demands distinct, assignment total, tie-break explicit, capacities certified on this branch, multiplicity bounded, no currency mixed.
- [ ] For loops: integer measure, strict decrease, invariant preservation inside the peel lemma.
- [ ] For refined orders: every earlier use of minimality still compares smaller objects.
- [ ] For compression/entropy: the class is the one the budget does not already charge; each saving charged once.
- [ ] For exhaustive routings: exhaustiveness is *proved* on the retained fibre; otherwise the exact negation is retained as a named open node.
- [ ] Both independent squeezes still have positive slack.

### 12.4 Declaring a node closed

- [ ] The terminal has a certificate of a listed type (hit, defect, compression, capacity, rigidity, identification, enumeration, exact open residual).
- [ ] Diagram, dependency table (Failure route), constraint ledger, per-lemma requirements, resilience row, and audit table are updated and agree.
- [ ] No forward reference: every Requires entry is introduced at an earlier-or-equal node.
- [ ] (Lean) Gate A: elaborates with no tracer axiom. Gate B: the `Holds` proposition is the manuscript's statement. Gate C: canonical carrier only.
- [ ] The weaker theorem that holds until any remaining open node closes is stated.

### 12.5 Reopening an open node

- [ ] The residual is written as its producer typed it (Rule 0, §4.8), with every ledger fact attached; no "equivalent" reformulation is used as the object.
- [ ] The plan already recorded for the node (§7, §8) is the one being executed; any deviation is recorded as a repair of the plan with its first failing step (rule 14).
- [ ] The open node's residual is written as $\neg C$ for a named lemma's conclusion $C$ on a named retained input.
- [ ] The intended proof of $C$ is expanded into steps $X_1\wedge\cdots\wedge X_m$ (constructions, preservation claims, cited lemmas).
- [ ] For each step: ledger question (fact present on *this* branch?), object question (property of the transferred object?), fibre question (output stays in the class?).
- [ ] The first failing step is the new diamond; its negation is typed and has a consumer from the selection table.
- [ ] No upstream object was re-derived, no upstream extremal choice refined, no upstream move re-applied, no no-go record written (rule 16); all effort went to inventory, selection, execution.
- [ ] Every diamond passes the locality test and the consumption test of §4.8 and names the measure it decreases, the closed branch it routes to, or the finite table it leaves.
- [ ] The residual inventory (§4.7) is written: every present property, its upstream consumer or "not accounted", the technique it enables, the certificate.
- [ ] Shared obligations across constructors are identified and ordered (cross-branch audit first, shared local lemma second).
- [ ] The old node keeps its number and becomes the decision; new nodes are appended.
- [ ] The remaining content is a list of bounded local lemmas, each with a closing move and a failure route.

### 12.6 Auditing an offered consumer

- [ ] The consumer's hypothesis is written as a bound on a named quantity $Z$.
- [ ] $Z$'s definition is traced back to the ledger (demand, paid, unpaid); the no-overcount identity is written out.
- [ ] The lower bound the ledger forces on $Z$ is computed from the burden and deficit lemmas already on the branch.
- [ ] If forced lower bound $\ge$ needed upper bound: the consumer is vacuous; stop working on it; find the hypothesis $H$ whose failure produced the residual.
- [ ] Only after the inventory (§4.7): the currency table (Section 5.2) is filled in as a diagnostic; every exhausted currency is marked. The closing move is chosen from the inventory's selection, never from the currency table alone.

---

## 13. Operating prompt for the executor

Paste this verbatim at the start of any session that works on an open node. It is written in the second person because the failures it prevents were the executor's, recorded in §4.8, §4.9 and rules 14–18. It adds nothing to the method; it removes the executor's freedom to deviate from it.

> **Operating prompt — structural exhaustion on an open node.**
>
> You are executing the structural-exhaustion method on one open node of a proof that is already fixed. You are not here to be creative, to find a better route, to assess feasibility, or to decide what the residual "really" is. You obey the following, in order, and nothing else.
>
> 1. **Files.** You edit only the markdown documents named by the user (`repair_and_closure.md`, `closure_proofs.md`, `node_181_structure.md`, or whichever the user names). You never edit `to_formalize/erdos_64_proof.tex`. You never edit Lean files unless the user names a definition that is a bug and tells you to fix it. Anything you would change in the manuscript you write as a numbered item in `closure_proofs.md` §6.
>
> 2. **The object.** The residual is the node's data exactly as its producer typed it, together with every fact accumulated on the path from the root (Rule 0, §4.8). You copy that typed data from the manuscript's definition into the document before doing anything. You never replace it by an "equivalent" inequality, a class of graphs, a sub-object (a component, a pocket, a piece, a ball), or a projection of any kind. Every sentence you write about the residual is a sentence about the whole branch state. If you catch yourself writing "the residual is a graph with properties P, Q, R", stop and delete it.
>
> 3. **No added hypotheses.** You never introduce an assumption that is not on the ledger, not even inside a lemma, not even flagged. If a proof you are writing needs a fact that is not on the ledger, the proof is not written; you record the missing fact in the inventory as "not present" and move on. "Suppose additionally", "under the hypothesis that", "assume for now" do not appear in your output.
>
> 4. **Inventory before anything.** You list the register's properties (A01–I06) against the branch state: present or absent; if present, accounted by which upstream step or unaccounted; the techniques the register attaches; whether each technique's *precondition* rows are present (rule 17). Certificates of failure (tokens, witnesses, routing records) carry no positive structure (rule 15). Upstream quantitative facts (state counts, budgets, ranks, caps, packing cardinality) are rows, not background.
>
> 5. **Selection.** You select the technique that consumes the most unaccounted rows and whose precondition rows are present. If a move rests on a finite table, you compute the table first and select the move only if the table contradicts the supply on the residual's actual parameters (rule 18). You do not select a move because it looks like a known argument.
>
> 6. **Execution.** You execute the move on the whole branch state to its end: a `False` leaf, a smaller typed object with a named decreasing measure, or an identification with a closed row whose hypotheses you have checked clause by clause against the branch. An arm whose data lives on a different object than the residual's is not an arm (§4.8 locality test); an arm after which the same rows remain unaccounted consumed nothing (§4.8 consumption test). At an obstacle inside a move, you inventory the obstacle's object with every accounted fact as present data and continue; "accounted" is never a stop sign (§4.9 F2). You never leave a move at an obstacle with a note.
>
> 7. **Forbidden outputs.** You never write: why a route cannot work; that the residual is unclosable; a "limit" or "no-go" theorem; an assessment of whether the user's instruction is achievable; a proposal to search, enumerate, or brute-force; a proposal to repair an upstream node; a refinement of an upstream extremal choice; a re-derivation of an upstream fact; a re-application of an accounted row. If you have concluded privately that the task is impossible, that conclusion has no standing and is not written, not acted on, and not used to choose the next step (§4.9 F1). You do not invoke a fallback the user has named until every technique in the register has been executed to a leaf on the residual with the record attached (§4.9 F4).
>
> 8. **Claims.** You never call a step a reduction, a narrowing, or progress unless it has a closed arm or a named decreasing measure. If you discover that a step you recorded did neither, you delete it from the record and say so in one sentence; you do not leave it in and qualify it.
>
> 9. **Reporting.** Each report states, in this order and nothing more: the object (verbatim typed data), the rows consumed by the step, the arms with their closed/typed status and measures, and the next selected move with its precondition check. No diagnosis, no explanation of difficulty, no assessment of your own performance, no promises.
>
> 10. **Instructions.** The user's instructions are ledger facts: they constrain the work and are not hypotheses to test, negotiate, or route around. When an instruction conflicts with what you would prefer to do, the instruction wins without comment. When you are told you deviated, you fix the record first and explain second, in one sentence.

## 14. Glossary and source map

### 14.1 Terms

| Term | Meaning |
|---|---|
| Branch state | The complete accumulated context of a case: $B=(H_0,\preceq,E,I,R,V,Q,A)$, or $(W,H,\Gamma,\tau,O,Q,M,E)$ in the PDE draft |
| Semantic region $\llbracket B\rrbracket$ | The set of objects satisfying everything on the branch record |
| Valid transition | Refinement plus exhaustiveness of the children |
| Output interface | The facts a transition's children may use; descendants that use only these are interface-respecting |
| Diamond | An exhaustive decision node; in Lean, `Decision.run` |
| Residual | The typed data of an open or routed obligation; in Lean, a non-`False` proposition in a codomain |
| Consumer | The registered step or closure class that accepts a residual's typed payload |
| Leaf totality | Every outcome lies in a closure class or in the domain of a registered step |
| Both-sides test | A predicate is admitted as a split only if both arms are productive |
| Branch-preserving repair | Replacing a failed producer of $P$ by the split $P\vee\neg P$; descendants stay on $P$ |
| Ordered first-failure split | $\neg X_1,\ X_1\wedge\neg X_2,\ \ldots$ for a failed conjunction |
| Currency | Compression, quantity, or constraint — what the adversary pays |
| Charging scheme | Demands, payers, canonical assignment with tie-break, certified capacities |
| Progress invariant | Every step yields a closed branch or a strictly smaller named residual |
| Hit / defect / compression | The trichotomy for comparing two structures with the same interface |
| Exit (1)–(7), route 8 | The saturated Type A alternatives; route 8 is the residual with none of them |
| Type A / Type B | Subcubic receiver-load ledger / high-degree fan-safe ledger |
| Gate A / B / C | Mechanical composition / manuscript fidelity / framework compliance |

### 14.2 Source map

| Cited object | File | Location |
|---|---|---|
| Repair rule, `RepairDiagram`, three worked repairs | `web/frontend/src/components/MethodologySection.tsx` | lines ≈1516–1704 |
| Eight failure modes, four repair kinds | same | ≈1050–1280 |
| `PROOF_MOVES` (21 moves) | same | ≈148–415 |
| Three currencies, both-sides test, charging, compression | same | ≈680–870 |
| Branch tuple, iteration cycle, leaf totality | same | ≈1706–1830 |
| Def. branch state / valid transition / quantitative transition / exhausted graph | `to_formalize/llm_auditable_proof_architecture_draft.tex` | `def:branch-state`, `def:transition`, `def:quantitative-transition`, `def:closed-graph` |
| Protocol (structural-exhaustion loop) | same | `prot:loop` |
| Soundness, quantitative closure, first-failure compactness, resource termination, estimate principle | same | `thm:soundness` … `thm:structural-exhaustion-estimate` |
| Partial closure, branch-preserving repair, ordered first-failure, monotone closure | same | `thm:partial`, `thm:repair`, `cor:first-failure`, `thm:monotone` |
| Locality / representative stability / topological sufficiency | same | §4 |
| Compactness routes table | same | `tab:ns-compactness-routes` |
| Stokes graph and kernel audit | same | §5, `stokes:rem:counterexample`, `stokes:lem:finite-energy-kernel` |
| Architecture overview, "How the alternatives close" | `to_formalize/erdos_64_proof.tex` | `sec:architecture` (≈104–310) |
| Two integer namespaces | same | `rem:two-distinct-integer-scales` |
| Detailed dependency table (Failure route column) | same | ≈1220–1290 |
| Constraint ledger (inv 1–44) | same | ≈1290 |
| Per-lemma requirements and the forward-reference rule | same | ≈1519, rule at ≈1799 |
| Open node [182] | same | ≈4889–4985 |
| Short self-return filter | same | `lem:cold-short-self-return-filter` (≈6961) |
| Cold corridor first failure, trichotomy | same | `lem:cold-corridor-first-failure`, `lem:cold-bounded-germ-trichotomy` |
| Dense-packing residual [158]–[168] | same | ≈7456–7700 |
| Small-order repair [173]–[177] | same | ≈7701–7800 |
| Scale additivity [169]–[172] | same | ≈7801–8262 |
| Exit-(4) peeling and finite descent | same | `def:typeA-exit4-peeling`, `rem:typeA-exit4-peeling-use` (≈11552), `lem:typeA-exit4-finite-descent` |
| Two-carrier no-go [124] | same | `thm:typeA-two-carrier-nogo` |
| Peeled demand residual [181] | same | `def:typeA-peeled-demand-residual` (≈16830), `thm:large-budget-route8-only` |
| Resilience appendix, cross-check table, "No leaf degrades to nothing" | same | `app:resilience` (≈17456–17775) |
| Note on human–AI collaboration ("157 to 180 nodes") | same | ≈17780–17870 |
| CT1–CT17, certificate alphabet C1–C5 | `to_formalize/branch_closure_methodology_extended.tex` | Part II |
| Lean carrier and sealing | `hypostructure/Hypostructure/Core/Residual/ExactLedger.lean` | `RefinementSystem`, `FactSystem`, `value_subsingleton` |
| Node [123] routing, pure closure row | `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly.lean` | `selectedRouteEightCensus`, `selectedSpineSurplusEstimateCloses`, `selectedLedgerBoundary` |
| Lean workflow rules | `.claude/skills/eg-proof-expansion/SKILL.md` | whole file |
| Status gates and tables | `Assembly_node_audit.md` | "Status rubric," the two tables |
| Open Lean residuals and further defects | `EG_incomplete_nodes_repair_plan.md`, `EG_LEAN_COMPLIANCE_REMAINING.md` | [172a], [181], [182] |
| Nodes [178]–[182]: pair overlap system, lemmas, open node | `to_formalize/erdos_64_proof.tex` | `def:pair-overlap-system`, `lem:pair-failure-overlap`, `lem:pair-system-realizability`, `lem:pair-system-increment-arithmetic`, `lem:pair-count-or-arithmetic` (≈4889–5085) |
| `ConditionalFactorization`, `RealizingOrder`, `Overlaps`, conditional fibre | `hypostructure/Hypostructure/Graph/SparseEntropySandwich.lean` | ≈458–640 |
| `PairUncoveredResidual`, `PairSerialDemandSystem`, `PairSerialArithmetic`, `PairIncrementOutcome` | `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean` | ≈6335–6960 |
| [182] repair-plan prose | `EG_incomplete_nodes_repair_plan.md` | "Remaining obligation `[182]`" |
| Unified ledger, burden, cores, two-support reduction | `to_formalize/erdos_64_proof.tex` | `def:typeA-unified-negative`, `lem:typeA-unified-deficit`, `lem:typeA-unified-burden`, `lem:typeA-unified-carriers`, `prop:typeA-unified-reduction` (≈15003–15180) |
| Demand ledger, absorbers, window blockers, zero-signature, vacuous closures | same | `def:typeA-pressure-ledger`, `lem:typeA-pressure-ledger-no-overcount`, `def:typeA-pressure-absorbers`, `lem:typeA-pressure-absorber-no-overcount`, `prop:typeA-exit4-closure-from-open-pressure`, `lem:typeA-open-pressure-zero-shadow-excess`, `prop:typeA-exit4-closure-from-zero-shadow`, `rem:typeA-zero-shadow-numerics`, `def:typeA-same-window-open-blocker-cap` (≈15279–16560) |
| Exit-(4) peeling, finite descent, [181], large-budget theorem, vacuous corollary | same | `def:typeA-exit4-peeling`, `lem:typeA-exit4-discharge`, `lem:typeA-exit4-finite-descent`, `def:typeA-peeled-demand-residual`, `thm:large-budget-route8-only`, `cor:typeA-large-budget-closure-open-pressure` (≈11211, 11395, 16596–16960) |
| Route-8 carriers, deletion witnesses, two-carrier no-go | same | `def:typeA-route8-carriers`, `def:typeA-carrier-deletion-witness`, `lem:typeA-essential-deletion-witness`, `lem:typeA-deletion-witness-declared`, `thm:typeA-two-carrier-nogo` (≈11759–12430) |
| Diameter bound on Type A supports | same | §"Type A: low-deficiency $P_{13}$-free piece" (≈10142–10175) |
| Entropy cap and why linear counts are invisible to it | same | §"The admissible entropy cap", `def:Theta`, `prop:entropy-high-theta` (≈9653–9720) |

Line numbers drift; `\label`s, node numbers and Lean declaration names are the stable identifiers.
