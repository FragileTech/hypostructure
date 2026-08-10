# EG StrategyDag — fresh node audit

This audit is being reconstructed from two authorities only:

1. `original_erdos_64_proof.tex` for the mathematical statement and proof flow;
2. the Lean declarations and generated sealed report for the implementation.

Docstrings, `--` comments, node metadata notes, and prior versions of this audit
are treated as **intentionally misleading**: they are never read for meaning and
never establish that a declaration implements a paper object. The only evidence
is the manuscript and the Lean *code* — the type of a declaration, the body of a
proof, the fields of a structure, and the arguments actually passed at a
registration site. A row is changed from `⬜` only after its paper statement,
Lean type, literal predecessor, ledger traffic, terminals, and routing have been
inspected.

Every row below is self-contained: a reader tracking one row finds everything
about it in one place.  Each row carries six evidence bullets — **Paper fact**
(what the manuscript states), **What the Lean does** (the statement read off the
type), **What it should do** (the type that would match the paper), **Gap**,
**Ledger and residual**, **Transport and terminals** — followed by **Paper
objects at this row**, the table of every `\label` that row consumes against the
Lean declaration whose *type* states it, and **CT composition at this row**.

In the paper-object table an empty implementation cell means nothing in the tree
implements the object.  That emptiness is the point of the table: a comment
citing a label is not an implementation.

Columns:

- **Ledger** — all reads use the accumulated ledger, new facts are appended, and
  every predecessor fact remains available.
- **Transport** — no EG-specific carrier, result, residual, ledger, executor, or
  manual routing replaces framework-owned execution.
- **Residual** — the Strategy consumes the literal active predecessor residual.
- **Facts** — the implemented mathematical statement and exhaustive alternatives
  are exactly those in the paper; supplied fields do not count as derivations.

Legend: ✅ verified compliant · ❌ verified violation · ⬜ unreviewed

## Build status

### 2026-08-09 sealed total-closure core

- Core now represents a finite, total strategy as `ClosingProgram known` over
  the exact branch-local fact index.  Its constructors require trusted atomic
  CTs or exhaustive binary decisions, and every leaf must close through the
  reserved closure fact, incompatibility, impossibility, or emptiness.
- `ClosingDag.statement` is the single global elimination point.  It opens the
  framework-owned minimal-counterexample scope, interprets both arms of every
  decision, and derives the registered `Target.Statement` from the locally
  closed branches.  Applications cannot access the interpreter, scope opener,
  ledger constructors, decision runner, or private DAG representation.
- `Hypostructure.Fixtures.ClosingProgram` checks the complete path, including
  sibling-fact isolation, mandatory decision arms, callback rejection, private
  constructors, and a final theorem with no `sorryAx`.
- This phase supplies the problem-agnostic closure machinery only.  The EG
  `Problem.lean` registration and its typed `StrategyDag.lean` topology still
  need to be instantiated against this surface before `erdos_64` exists.

### 2026-08-09 cold endpoint correction and official theorem check

- The cold prefix consumes the surviving upstream ledger and appends the split
  cold facts through `K .coldBranchClosed`, then appends Core's reserved
  closure key by the canonical incompatibility between the incoming
  `K .coldTerminalResidual` fact and the new no-terminal fact.
- `lake build Hypostructure.Graph.Strategy.ColdCorridorRun
  Hypostructure.Graph.Strategy.SpineContinuationRun` is green.  The cold fixture
  audits the semantic facts, the reserved closure fact, exact chronological
  commits, fact uniqueness, and the concrete `closeIncompatible` reason.
- `make erdos` remains strict: it requires
  `HypostructureErdos64EG.erdos_64 : OfficialStatement` and prints its axioms.
  That declaration is not yet present.
- The cold quantitative route from hot failure through cold mass, stub excess,
  first-failure extraction, and positive bounded-germ production is now
  committed as ordinary ledger facts before `coldBranchClosed`.

### 2026-08-08 OOM repair and canonical endpoint check

The current working tree was repaired and checked through the canonical sealed
endpoint.  This note supersedes older build counts and every later statement
that says the frontend or `StrategyDag.lean` is retired, commented out, or not
executed.  Those statements are retained only as historical porting context.

- `make erdos-build` is green: the framework build completed all 8755 jobs and
  the Erdős application build completed all 8734 jobs.
- `lake build HypostructureErdos64EG.StrategyDag` is green.  The application
  endpoint is the active canonical `Spine.run`; no legacy `Blueprint` endpoint
  was restored.
- The former `SpineVocabulary` OOM came from reducing the executable
  `Fintype.card` instance for the full routed label product.  The framework now
  stores the paper's `Q_geom` as a registered natural together with an equality
  certificate to the declared routing alphabet.  The generic graph API proves
  `card_routingLabel` by product-cardinality laws and `ac_rfl`; it does not
  enumerate that alphabet.
- The concrete application derives its routing count from the paper's declared
  seven factors, proves the registered equality structurally, proves
  `Cap_hom(L_geom) ≤ 2^78` and `C_sp ≤ 2^85`, and uses the validated
  sufficiently-large threshold `2^512`.  The framework contains none of these
  application-specific values.
- No project-wide Lean memory cap and no namespace-wide `maxHeartbeats 0` was
  added.  The only new unbounded-product accommodation is elaboration depth in
  `Problem.lean`; finite enumeration work remains isolated in the generated
  `P13Barrier` certificate shards with finite heartbeat budgets.
- The P13 generator, not only its generated files, now emits the serial audit
  dependency chain and the finite budgets used by the checked shards.

This repair does not by itself re-audit any row's paper statement, exact-ledger
traffic, residual, or terminal.  The row matrix below is unchanged; its status
claims continue to require the row-specific evidence recorded there.

**The framework, the application and every fixture compile.**  Re-measured on
2026-08-06 after the row-32 port, in the working tree:

- `lake build` in `hypostructure/` — green, 8740 jobs, no failing target.  The
  earlier `TypeAReceiverNode` and `TypeBEnvelopeCharge` failures recorded here
  are resolved.
- `lake build` in `proofs/hypostructure_erdos_64_eg/` — green, 8712 jobs.
- The canonical `ExactLedger`, `FactManifest` and `ExactExecution` modules with
  all fifteen positive and negative enforcement fixtures — green; every
  `#guard_msgs` in the negative fixtures is intact.
- `Hypostructure.Graph.Strategy.SurplusRows`,
  `Hypostructure.Graph.Strategy.SurplusRun` and
  `Hypostructure.Fixtures.SurplusRun` — green.
- The Type A saturated exit chain, rows 12--15:
  `Hypostructure.Graph.VisibleReceiverEntry`,
  `Hypostructure.Graph.PortReturnExistence`,
  `Hypostructure.Graph.VisibleEntryQuotient`,
  `Hypostructure.Graph.AnchoredReturnCompletion`,
  `Hypostructure.Graph.CommonPortReturnCycle`,
  `Hypostructure.Graph.WindowLabelCollision`,
  `Hypostructure.Graph.Strategy.TypeAExitRun`, and the fixtures
  `Fixtures.TypeAVisibleEntry`, `Fixtures.TypeAExitOne`,
  `Fixtures.TypeAExitTwo`, `Fixtures.TypeAExitThree` — green.
- The API-catalog boundary check — `catalog is current`, after a refresh for the
  row-32 API additions (`Graph/SurplusBlockers.lean`,
  `Graph/CanonicalSupportSelection.lean`, `Graph/SparsePairResponse.lean`,
  `Graph/DeclaredRankQuotient.lean`, `Graph/SparseEntropySandwich.lean`) and the
  `CurvatureQuotient → DeclaredQuotient` replacement.

The build is intermittently flaky in a way worth recording: a truncated
dependency olean produces errors sited in unrelated files ("object file … does
not exist").  Re-running `lake build` clears it; such an error is never evidence
about a row.

The measurement below is the last full one and is retained for what it records
about the ported rows; it is stale as a claim about the tree.

**The framework and the application compile.**  Measured on 2026-08-05 in the
working tree, `make test` passes end to end:

- `lake build` in `hypostructure/` (8697 jobs);
- `lake build HypostructureErdos64EG` (8679 jobs);
- the canonical `ExactLedger`, `FactManifest` and `ExactExecution` modules and
  all fifteen positive/negative canonical-ledger fixtures;
- the total-execution gate (PASS, 1 production file), the canonical-ledger gate
  (PASS, 138 live modules, 306 quarantined), and the API-catalog boundary check
  (`catalog is current`).

The counts above include the rows 24--25 and 29 port: the three new generic
modules `Graph/TypeBDirectCycle.lean`, `Graph/TypeBRefinedSupport.lean` and
`Graph/TypeBFanIncidence.lean`, and the fixture
`Fixtures/TypeBFanWindowNode.lean`.  With row 29 ported, Part VII is wired: the
degree-four arm of node `[68]` now runs `[79]`, `[80]` and both halves of `[81]`
on the *same* row values as `[71]`/`[72]`, so rows 23, 24 and 25 are live at both
of their manuscript positions.  `#print axioms` on
`TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration`,
`TypeBRefinedSupport.typeBMaximalCompletion`,
`TypeBRefinedSupport.exists_overlapObstruction_of_not_hasDisjointChoice`,
`TypeBFanIncidence.degreeFourProfile`, `Spine.directCycleDichotomy`,
`Spine.b2AssignmentDichotomy`, `Spine.degreeFourProfileRow` and `Spine.run`
reports `propext`, `Classical.choice` and `Quot.sound` only.

They also include the row 11 port: the new generic module
`Graph/ReceiverRouting.lean`, the new induced-degree bridge
`Graph.FiniteObject.degree_induce_eq_internalDegree` in
`Graph/BoundaryDemand.lean`, and the fixture
`Fixtures/TypeAReceiverNode.lean`.  With row 11 ported, the Type A residual of
node `[63]` is no longer an exit of `Spine.run`: node `[88]` commits the
canonical receiver routing and the threshold algebra on it, and node `[89]`
splits into exact ledgers indexed by `typeASaturatedReceiverKeys` (row 12's
entry) and `typeAUnsaturatedReceiverKeys` (node `[90]`).  `#print axioms` on
`FiniteObject.degree_induce_eq_internalDegree`,
`FiniteObject.exists_traceTo_of_no_baseline_subsupport`,
`FiniteObject.traceTo_of_traceReceiver?_eq_some`,
`FiniteObject.isSome_traceReceiver?_of_traceTo`,
`FiniteObject.not_saturated_iff`, `FiniteObject.saturationThreshold_eq`,
`Spine.typeAReceiverRoutingRow`, `Spine.typeASaturationDichotomy` and
`Spine.run` reports `propext`, `Classical.choice` and `Quot.sound` only.

That port also changed the row-42 support facts: the packing carried by
`netChargeNegative`, `windowJoinPressure`, `negativeSupport` and
`typeALowSurplus` includes its own maximality, so node `[27]` stays instantiable
at the Type A support.  Row 42's evidence records why a bare packing was
unsound for row 11.  `Graph/ReceiverLoad.lean`'s dead receiver/load geometry — `Support`,
`RoutedLoad` with its arbitrary route function, `CanonicalRouting` with its
opaque `canonical : Prop`, the completion-port and anchored-return records, and
the load algebra on them — is deleted; the module is now only the registered
presentation record, reduced to the three parameters the live build reads.

No `sorry` occurs in `hypostructure/Hypostructure` or in the EG proof source.

**Correction — every status cell of an unbuilt row was reset.**  Nineteen rows
carried `✅` cells whose `Where` column named a declaration that does not exist
in the live tree: the legacy vertex ids `v8`–`v14`, `v21`, `v25`–`v28`,
`v31`–`v32`, `v36`–`v37`, `v39`, `v48`–`v50` and the legacy stage names
`ordered_surplus_activation`, `baseline_demand_accounting`,
`canonical_pair_response_accounting`, `canonical_capacity_token_accounting`,
`coupled_homogeneous_fibre_pressure`, `finite_bottleneck_classification`,
`homogeneous_bottleneck` and `ordered_witness_scan`.  All of them were
`Core.DichotomyData` or stage registrations in the deleted `Blueprint`
topology.  A ticked column is a claim about the current tree, so rows 12–19 and
30–36 were reset to `❌ ❌ ❌ ❌`; rows 30–33 have since been partly ported and
their Ledger, Transport and Residual cells are claims about
the exact surplus row chain rooted at `surplusAboveKeys`.  Row 15, which had been ticked in all four,
is included and carries its own correction note.  Rows 26–27 were reset by the
same correction and have since been ported; their cells below are claims about
`Spine.hybridEntry` and `Spine.bridgeFanMass`.  Row 28 now has the ordinary
Step 1 selected-entry charge fact, the B-ledger charge implication, the
remaining-core decision, and the clean-arm exclusion fact in the live generic
spine.  Rows 16 and 17 keep their
`Where` entries and are named exactly: `Spine.typeAExitFourDichotomy` is the
selected exit-`(4)` decision, while `Spine.typeAExitFiveDichotomy` now reads the
selected no-exit-`(4)` ledger fact and commits the selected exit-`(5)` yes/no
fact.  They are not route-8 `(R2)` generators.  Row 37's `Where` was the only
stale entry on a genuinely ported row and
now names `Spine.remainderNormalization`.

The rule this pass applied, and the one to keep applying: **a `✅` requires a
declaration that elaborates in the live tree and a target that builds.**  A
faithful description of deleted code is porting reference, not a passing
column.

**Correction — the earlier composed-spine failure was Block A's, not rows 41–42's.**
An earlier revision of this section recorded four composed-spine errors (a
`closeIncompatible`/`rankDropClosedKeys` key-index mismatch at `:649` and three
heartbeat exhaustions) and attributed them to rows 39–42's in-flight port,
because every error site named a rank-drop or net-charge declaration.  That
attribution was wrong.  The cause was in Block A: Row 9's
`barrierEnumerationDichotomy` proved `lem:variable-edge-budget` inline as a
four-step tactic block, and the elaboration cost of that block inside the
`run` term exhausted the heartbeat budget.  The `:649` "mismatch" was a
*consequence* — its reported type still contained an unsolved metavariable
(`?m.620`), the signature of a cascade from a timeout upstream, not a real
key-order disagreement.  Replacing that tactic block with a call to the
framework lemma `Graph.skeletonBudget_le_variableEdgeBudget` (see Row 9)
made the former composed spine build with no other change; this was verified by reverting the
Row 7 manifest fix independently and rebuilding, which still succeeds.  The
lesson for this document: an error *sited* in a row is not evidence the defect
*belongs* to that row, and elaboration-budget failures relocate freely.

The earlier parser, PDE packing-normalization, and rank-drop identifier errors
recorded here are fixed and must not be used as current evidence.

**The authored DAG is retired and the frontend is not rebuilt yet.**  The old
topology was the legacy `Blueprint` chain whose first ten nodes *were* Block A;
every later row was a continuation lambda passed into one of them, so the
legacy Block A was the skeleton the whole DAG hung from.  With Block A ported,
that skeleton was removed rather than kept beside the spine:

- `Official/Definition.lean`, `Official/Problem.lean`,
  `Official/StructuralProgram.lean`, `Official/ClosureProbe.lean`, the whole
  `AB/` directory, `Presentation.lean` and `OfficialStatement.lean` are
  **deleted**.  They built a `Core.ProblemDefinition` -- a registry of parallel
  capability lists resolved by *list position* -- which the canonical API
  replaces outright.
- `StrategyDag.lean` is a commented reference holding the retired topology
  verbatim, for the rows still to be ported.
- The sealed-frontend run/export targets (`make ab`, `make erdos`) are removed
  from the `Makefile` and return with the frontend.

Consequently there is currently **no executed run and no closure evidence** for
rows 11 onwards.  Every row outside Block A is unbuilt, not merely unverified;
the `Where` column of sections B--K names declarations that no longer
elaborate, and those sections are porting reference only.

The application is now exactly two files, `Problem.lean` and
`StrategyDag.lean`, plus the two inputs `Problem.lean` reads:
`WindowAlgebra.lean` (the registered window order, this problem's curvature
specializations, and the Hegde--Sandeep--Shashank axiom) and
`FiniteChecks/P13Barrier` (the audited finite table).

The canonical proof-expansion API is now a closed allowlist generated by
`.agents/skills/eg-proof-expansion/scripts/api_catalog.py`.  It excludes the
legacy residual ledger/query, `HasResidual`, capability stores/flows,
producer-specific ledgers, and direct proof-specific append/construction
primitives.  Existing source descriptions below that discuss those legacy
transports are historical row evidence, not permission to use them in a new or
repaired node.

The canonical audit surface is proof-free and ancestry-derived.  Initial
object-scope selection is accepted only from an exactly empty history; every
later transition proves refinement, so no committed fact can be archived or
dropped.  `ExactLedger.audit_complete` accounts for every branch fact,
`ExactLedger.audit_facts_unique` rules out duplicate semantic keys, and
`ExactLedger.audit_commits_nonempty` rules out empty commits.  The enforcement
fixtures also reject private history traversal, undeclared input reads,
missing requirements, duplicate publication, and omitted declared outputs.

No `sorry` occurs in `hypostructure/Hypostructure` or in the EG proof source,
and the only declared project axiom is
`HypostructureErdos64EG.p13Free_hasPowerOfTwoCycle`.  It moved out of the
framework in this change: the external theorem is an input to *this* problem,
not a law of the framework, so it is declared in `WindowAlgebra.lean` and
reaches the spine only through the `freeForcesTarget` field of the registered
`Spine.Data`.  Nothing in `Hypostructure.Graph` or `Hypostructure.Core` names
it.  `#print axioms spineData` also reports the `native_decide` axioms of the
`P13Barrier` certificate shards, as it did before.

## A. Entry spine

> **Block A has exactly one implementation, and the legacy one is gone.**
> The `Where` column below, and the whole of the **Row evidence** section for
> rows 1–10, describe the *previous* implementation on the legacy
> `Core.Residual.Ledger` stack.  That implementation has now been **deleted
> from the repository**, not quarantined: the `v0`–`v16` vertex ids do not
> resolve, the exported run it cites cannot be regenerated, and the
> declarations it names no longer exist.  Those rows are kept as a record of
> what was checked, and as prose about the mathematics; they are not a
> description of any code.
>
> The framework modules deleted in this change, all of them Block A's legacy
> and all of them superseded by the spine:
> `Core.Strategy.{CounterexampleReduction, TargetAlgebraReduction,
> MinimalSubobjectExclusion, CriticalModificationStructure,
> InterfaceReplacementStage, MinimalCounterexampleClosure,
> ObstructionPackingClosure, ObstructionPackingData, ObstructionPackingSemantics,
> ExactFiniteLocalAlgebra, ExactFiniteLocalAlgebraBitTable,
> ExactFiniteLocalAlgebraSemantics, ScaleThresholdDichotomy,
> ScaleThresholdDichotomySemantics, FiniteBarrierEnumeration,
> FiniteBarrierEnumerationSemantics, FiniteDensityBudget,
> FiniteDensityBudgetSemantics, SupportComplementNormalization,
> SupportComplementNormalizationSemantics, BoundaryDemandAccounting,
> BoundaryDemandAccountingSemantics}` and
> `Graph.Strategy.{CounterexampleReduction, CounterexampleLocalization,
> ObstructionPackingClosure, ScaleThresholdDichotomy, FiniteDensityBudget,
> MinimumDegreeBaseline, InducedPathPresentation,
> HegdeSandeepShashankPacking}`, together with
> `Graph.External.HegdeSandeepShashank`, `Graph.WindowCurvatureTypeB` and
> `Graph.Strategy.Official.Universal`.  Two row-41 support modules that
> depended on the deleted Block A layer, `Core.EntropyPackingBudget` and
> `Core.Strategy.FiniteStateCapacityTheorems`, were quarantined rather than
> deleted because their own row is unported.
>
> **The framework no longer names this problem.**  The order-generic curvature
> algebra stayed in `Graph.WindowCurvature`; everything fixed to `windowOrder =
> 13` or to the count `399` — the forbidden-difference lemmas, the label
> census, the packed code table and its relation — moved to the proof, into
> `HypostructureErdos64EG/WindowAlgebra.lean`.  So did the
> Hegde–Sandeep–Shashank axiom.  Both reach the spine as *problem inputs*,
> through fields of the registered `Spine.Data`.
>
> The block now lives in three files:
>
> | file | what it holds |
> |---|---|
> | `Graph/Strategy/SpineVocabulary.lean` | the `Data` record and the thirteen semantic keys with their `Holds` clauses |
> | `Graph/Strategy/SpineRows.lean` | the ten rows, each an `AtomicStrategy` or a `Decision` |
> | `Graph/Strategy/SpineAssembly.lean` | vocabulary-instantiated rows, closure instances, and exact key-index aliases; no custom result or continuation carrier |
>
> What is compiler-checked, rather than asserted here: `Spine.run` elaborates,
> so every row's prerequisites were present in the branch index when it ran;
> `complete_audit_facts` is `rfl`, so a completed block's audit is exactly its
> ten facts in commit order; and `complete_audit_accounts_for_every_fact`
> applies `ExactLedger.audit_complete`, so none of them was archived or
> dropped.  The framework builds green with no `sorry`.
>
> Two things the old rows did that the new ones do not.  No row writes a
> numeral: every constant is a field of `Spine.Data`, supplied by the
> presentation, and `399` is now `(legalCodeList data.windowOrder).length`
> rather than a type index.  And no fact carries data: `p₁₃` is
> `FiniteObject.windowPackingNumber`, an observable of the object, so the
> packing family never travels between rows —
> `FactSystem.value_subsingleton` makes carrying it unelaborable.

| # | Node | Where | Ledger | Transport | Residual | Facts |
|---|---|---|---|---|---|---|
| 1 | Minimal counterexample [1]–[4] | `openMinimalCounterexampleScope` at `K .selection` | ✅ | ✅ | ✅ | ✅ |
| 2 | Target algebra reduction [5]–[7] | `Spine.returnAvoidance` | ✅ | ✅ | ✅ | ✅ |
| 3 | Minimal subobject exclusion [8] | `Spine.noProperBaseline` | ✅ | ✅ | ✅ | ✅ |
| 4 | Critical modification structure [9]–[10] | `Spine.deletionCriticality` | ✅ | ✅ | ✅ | ✅ |
| 5 | Interface replacement closure [11]–[14] | `Spine.interfaceReplacement` | ✅ | ✅ | ✅ | ✅ |
| 6 | Induced-obstruction packing [15]–[17] | `Spine.obstructionPacking` | ✅ | ✅ | ✅ | ✅ |
| 7 | Exact finite local algebra [18] | `Spine.localAlgebra` | ✅ | ✅ | ✅ | ✅ |
| 8 | Non-near-cubic surplus split [19] | `Spine.surplusDichotomy` | ✅ | ✅ | ✅ | ✅ |
| 9 | Near-cubic finite enumeration [21] | `Spine.barrierEnumerationDichotomy`; `Graph.FiniteObject.WindowTargetPackage` | ✅ | ✅ | ✅ | ✅ |
| 10 | Hot/cold package split and finite window-density budget [22]–[24] | `Spine.coldWindowLedgerSplitRow`, `Spine.densityBudget` | ✅ | ✅ | ✅ | ✅ |

**Re-review of block A, against the source.**  Rows 1–10 were re-read
declaration by declaration against `original_erdos_64_proof.tex`, the Lean
types and bodies, and the exported run.  Every ticked column survives: the
selection order, the return-set equivalence, the subobject exclusion, both
criticality clauses, the three interface-replacement stages, the maximal
packing, the `399`-label denotation, the surplus comparison, the barrier
summary, and the density cap all state what the manuscript states, with no
application-supplied fact standing in for a derivation, no EG-specific
carrier, and no rewritten residual.  Spot checks that held exactly as written
include `criticalityNode` at `:116` and `slackIncompatibilityNode` at `:198`;
the three `StageNode.create` runs at `:333`/`:355`/`:493` and the single
inadmissible "CT7" comment at `:161`; `grep -c "CTAdapters.ct"` returning `0`
for both `CriticalModificationStructure.lean` and `InterfaceReplacement.lean`;
every `contract_field` list in the run export; `labels_enumeration` proved by
kernel `decide` and not `native_decide`; and safe/flat `543958`/`111286` at
slot `15·1+1 = 16` of the generated count arrays, whose difference is the
paper's `432672`.

Five errors were found and are corrected in place below.  Four are
bookkeeping; the first is not:

1. **Block A builds** — see **Build status** above.  `SpineRows`, the module
   holding all ten rows, compiles, so every ✅ in this block *is*
   compiler-confirmed.  An earlier revision of this item said the tree does not
   build, citing a parse error in `Core/Strategy/Dag.lean` and an unsolved goal
   in `PDE/.../PackingNormalization.lean`; both modules have since left this
   block's slice.  What previously failed was the former composed spine, on rows 41–42's
   in-flight port — outside Block A and recorded there.
2. **Row 9, Facts.**  "The continuation applies
   [`sum_edgeStratumCount_le_variableEdgeBudget`] to edge counts read from its
   residual" was false: `Graph/FiniteEdgeBudget.lean` is imported by no
   module, so `lem:variable-edge-budget` and `rem:budget-robustness` are
   unconsumed, not framework theorems on residual data.  Their paper-object
   rows are reclassified.  The row's own CT16 statement is unaffected by *this*
   finding, so it alone does not move Facts.  (Facts at rows 9 and 10 was
   separately failed by the missing dyadic scale factor found during rows
   41–42's port, and is now ✅ again with that factor restored — see the
   **Fixed and verified** paragraph in Row 10's **Gap**.  An earlier revision
   of this list asserted "Facts stays ✅" without that qualification and
   contradicted the summary table; the qualification is the fix.)
3. **Rows 3, 4, 5 — export edge ids off by one.**  The export has
   `e2 : v4→v5`, `e3 : v5→v6`, `e4 : v6→v7`, `e5 : v7→v2`; the three rows each
   cited the successor edge.  Row 2's `e2` and Row 6's `e5` were already
   right, so the document contradicted itself.  Fixed.
4. **Row 5 — invariant provenance.**  `erdosBaselineInvariant` /
   `erdosTargetInvariant` do not feed `interfaceReplacement`; that field
   proves its own invariants in `Graph/Strategy/CounterexampleReduction.lean`,
   and the EG-file pair was consumed at the registration Row 40 has since
   retired, so it is now consumed nowhere.  The row credited the
   application with more than it supplies.  Fixed.
5. **Row 9 — stale exported interface.**  The run still advertises a `profile`
   contract field for `finite_barrier_enumeration:0`; `Registration` has no
   such field.  Recorded at the row.

## B. Type A receiver ladder

> **Being ported.**  The rows in this section were implemented against the
> legacy `Blueprint` topology and its `Core.ProblemDefinition` registry.  Both
> are gone: the registry was deleted with `Official/Definition.lean` and the
> topology is now a commented reference in `StrategyDag.lean`.  Every Type A
> module of `Hypostructure.Graph` is quarantined, so each row is rebuilt
> against the live framework rather than re-imported.
>
> Row 11 is ported.  It runs on the Type A residual of node `[63]` that
> `Spine.run` already reaches, and its `Where` column names the live spine
> declarations.  Both of its exits — the saturated arm that enters row 12 and
> the unsaturated arm that enters node `[90]` — are exact ledgers indexed by
> their committed decision keys; the previous Type A low-surplus leaf is gone.
>
> Every theorem row 11 rests on has been checked with `#print axioms` and
> depends on `propext`, `Classical.choice` and `Quot.sound` alone — no
> `sorryAx`, and no `Lean.ofReduceBool`, so no `native_decide` result is
> load-bearing in it.
>
> Rows 16--19 are not implemented on the canonical Strategy DAG.  The former
> `Spine.runRouteEight` / `Spine.runSaturatedExits` path was removed because it
> selected an arbitrary auxiliary route-8 object instead of refining the exact incoming Type A
> tuple.  The next admissible implementation must first derive the manuscript's
> coordinate-specific Q1--Q4 response semantics for that retained tuple.

## C. Type B fan

> **Being ported.**  The rows in this section were implemented against the
> legacy `Blueprint` topology and its `Core.ProblemDefinition` registry.  Both
> are gone: the registry was deleted with `Official/Definition.lean` and the
> topology is now a commented reference in `StrategyDag.lean`.  Every Type B
> module of `Hypostructure.Graph` is quarantined, so each row is being rebuilt
> against the live framework rather than re-imported.
>
> **Most rows of this section are ported.**  Rows 20--27 and 29 have live spine
> declarations.  Row 28 now has ordinary Type B exclusion fact declarations and
> row adapters, but its full branch routing and strategy-module validation are
> still open.
>
> **Row 28 remains the Type B gap.**  `thm:branch-kill` (b) has the local
> `typeBExcluded` incompatibility, but the `[76]`/`[85]` excluded arm is not yet
> fully routed through a buildable strategy module.

>
> Three things about how rows 27 and 28 are built are worth recording, because
> each replaced an earlier attempt that was doing more than the manuscript asks.
>
> **Nothing is rebuilt that the branch already carries.**  Row 28 reads the
> strengthened B2 ledger fact -- `Spine.Key.typeBDisjointLedger`, committed
> after node `[74]`/`[82]` -- and takes the entries `A_h`, their carriers, their
> disjointness and their payment from `def:typeB-candidate-ledger`'s own
> `CandidateEntry` fields.  An earlier
> pass had invented a parallel envelope-and-block apparatus
> (`IsFanEnvelope`, `closedNeighbourhood`, `IsExcludedTypeBSupport`,
> `AssignedFans`, `BridgeResidualSupport`) and a second saturation node; all of
> it is deleted.  `CandidateEntry.pays` is the entry charge, and the claim in an
> earlier version of row 25's Gap that the entries carry no charge is withdrawn
> there.
>
> **Every fact is about the incoming residual.**  Both rows' facts are scoped by
> `∀ packing, IsWindowPacking → ∀ piece ⊆ remainderSupport packing, Connected →
> NegativeNetCharge → 0 < ambientSurplus`.  Nothing is stated of an arbitrary
> region of an arbitrary object.
>
> **No row declares a prerequisite it does not read.**  Row 27's manifest is
> `sourceFreeManifest` -- `Requires := []` -- because its content is the
> registered mass slack and the residual's own baseline.  Row 27's `Requires`
> had briefly named `highCentreNormalForm` after the clause that used it was
> deleted; that is corrected.
>
> The accounting itself avoids the manuscript's deletion step, and that is why it
> goes through without `def:typeB-ledger-carriers`' ordinary deficiency reserve.
> The manuscript proves `lem:typeB-bridge-deficit-bound` and Step 2 by deleting
> carriers and discharging the remainder, which forces the reserve because
> cutting carriers creates boundary deficits.  The same accounting runs in place,
> because the only vertices of an assigned Type B support above the baseline are
> its assigned centres: the Type A discharging calculation applies to the support
> itself with the centres (row 27) or the entry blocks (row 28) as an exceptional
> set -- `FiniteObject.card_le_scaled_deficiency_off` -- and no boundary deficit
> is ever created.
>
> One bookkeeping point the manuscript leaves implicit: its Step 1 display omits
> the centre's own `−α` as a vertex of the counted core, so a block is bounded
> below by `−α` rather than `0` and `Ĉh_B(X) ≥ −α|H_X|` is what the summation
> gives.  That is exactly the `+α|H_X|` on the other side of `(B-ledger)`, so the
> conclusion follows -- but only because the identity is carried as a fact.  At
> `k = 7`, `c = 1`, where `D_B = 0` exactly, `Ĉh_B(X) ≥ 0` would be false.
>
> Rows 23, 24, 25, 26, 27 and 28 are wired at *every* one of their manuscript
> positions.  The degree-four arm of `[68]` runs `[79]`'s profile and then the
> same row values at `[80]`, `[81]`, `[82]`, `[84]` and `[85]` that the heavy arm
> runs at `[71]`, `[72]`, `[74]`, `[75]` and `[76]`; neither a `Decision` nor an
> `AtomicCT` carries a predecessor, so nothing is re-registered and no row exists
> twice.  Row 27 is one executor at four cursors.
>
> **A registered-data defect was repaired here.**  `Spine.Data` declared
> `dischargeScale` *after* `fanCapSlack` and `highCentreDeficitSlack`, so the
> `dischargeScale` in those two types was an auto-bound implicit rather than the
> field: both obligations read `∀ {s}, …`, which is false, and
> `HypostructureErdos64EG.Problem` did not elaborate.  The field is now declared
> before its consumers.  This invalidated nothing that was proved -- the two
> slacks are hypotheses, not conclusions -- but it did mean rows 22 and 26 had no
> compiling presentation until the move.


| # | Node | Where | Ledger | Transport | Residual | Facts |
|---|---|---|---|---|---|---|
| 20 | Heavy-centre split [68] | `Spine.highCentreNormalForm`, `Spine.heavyCentreDichotomy` | ✅ | ✅ | ✅ | ✅ |

| 21 | Heavy-centre local dichotomy [69] | `Spine.heavyCentreLocalDichotomy` | ✅ | ✅ | ✅ | ✅ |
| 22 | Certificate-marked fan cap [70] | `Spine.fanCertificateCap` | ✅ | ✅ | ✅ | ✅ |
| 23 | Certificate labelling [71]/[80] | `Spine.fanCertificateDichotomy` | ✅ | ✅ | ✅ | ✅ |
| 24 | Direct-cycle removal [72] | `Spine.directCycleDichotomy` | ✅ | ✅ | ✅ | ✅ |
| 25 | B2 ledger [72]/[81] | `Spine.b2AssignmentDichotomy` | ✅ | ✅ | ✅ | ✅ |
| 26 | Hybrid B1 entry [74]/[82] | `Spine.hybridEntry` | ✅ | ✅ | ✅ | ✅ |
| 27 | Bridge fan-mass [73],[75],[83],[84] | residual-specific mass rows append selected certificate, overlap, and B2-exclusion facts; family aggregation remains | ✅ | ✅ | ✅ | ❌ |
| 28 | Bridge deficit [76]/[85] | `Spine.typeBSelectedFanCharge`, `Spine.typeBExclusionCharge`, `Spine.typeBExclusionDichotomy`, `Spine.typeBExcluded` | ✅ | ✅ | ✅ | ✅ |
| 29 | Degree-four fan profile [78],[79] | `Spine.degreeFourProfile` | ✅ | ✅ | ✅ | ✅ |
## D. Non-near-cubic surplus branch

> **Partly ported.**  Rows 30--36 now run live through the currently stated
> ledger facts, as
> `Graph/Strategy/SurplusRows.lean` installs the row declarations over the
> literal `surplusAboveKeys` ledger -- node `[19]`'s above arm, with its nine
> facts -- and the surplus block continues that exact cursor through
> `[125]`--`[144]`.  `Hypostructure/Fixtures/SurplusRun.lean` checks those exact
> key indices and audit invariants.  Their Ledger, Transport and Residual columns
> are backed by that compiling target, and so are the Facts columns of rows
> 30--35.  The block's exits are exact branch ledgers: the near-cubic route of
> `prop:single-graph-sparse-pressure-routing` (a), and, over each of the three
> geometric audits `class(t)` dispatches to, node `[144]`'s capped close and its
> bottleneck.
>
> `[144]` commits the positive failed-cap alternative as an ordinary ledger fact:
> `Graph.HomogeneousBottleneckPatternStatement`, derived in
> `Graph.homogeneousBottleneckPatternStatement_of_not_caps` and stored under
> `Spine.homogeneousBottleneckPattern`.  `Spine.bottleneckRoutingRow` now
> declares that key as an input and reads it with `FactInputs.get` before
> appending `Spine.bottleneckRouting`; the row no longer routes from a bare
> negated cap predicate.  The near-cubic outcome closes by the framework
> incompatibility between `Spine.surplusAbove` and `Spine.spineSurplusEstimate`;
> the bottleneck outcome remains ordinary ledger content on the same exact
> history, not a side object.
>
> The legacy `Graph/Strategy/SurplusAccounting.lean` is deleted as of row 35.  It
> was the retired CT9 → CT14 → CT10 → CT6 path of nodes `[140]`--`[143]`, it had
> already been orphaned -- it imported eight `Core.Strategy` modules that no
> longer exist, so it could not compile and nothing live could reach it -- and
> none of the rows below was ported from it.
>
> The generic modules the ported rows rest on are
> `Graph/ExcessPortFamily.lean` (`𝒫_exc` and `|𝒫_exc| = σ(G)`),
> `Graph/SparsePortActivation.lean` (`lem:sparse-port-activation` (a), (c), (d)),
> `Graph/BaselineSpineDemand.lean` (the cubic baseline and
> `lem:incremental-skeleton-room`), `Graph/CanonicalFibreLedger.lean` (the one
> implementation of both canonical ledgers), `Graph/SparsePairLedger.lean` (that
> ledger at the object's own pair schedule), `Graph/PrimitiveCarrier.lean`
> (`𝔘_sp(G)` and its supply), `Graph/PortResponseSupport.lean` (`Γ(p)` and
> `T(p) ∪ Γ(p)`), `Graph/SurplusBlockers.lean` (the six clause objects of
> `def:surplus-blockers` and the ledger at them),
> `Graph/CanonicalSupportSelection.lean` (the one implementation of
> "the lexicographically first minimum-vertex connected support containing …"),
> `Graph/SparsePairResponse.lean` (`X_π`, `∂X_π`, `r_π`, `X_Π`),
> `Graph/DeclaredRankQuotient.lean` (`def:admissible-rank-quotient` at an
> arbitrary declared coordinate family, of which `Graph/CurvatureTargetRank.lean`
> is now one instance) and `Graph/SparseEntropySandwich.lean` (the dependence
> dichotomy and the entropy sandwich).  None imports a `HypostructureErdos64EG`
> module and none writes a numeral of this presentation.
>
> The remaining prerequisite is not a new side channel: it must be a
> proof-agnostic graph constructor, consumed by a normal `factOnly`/`Decision`
> row, that turns the committed homogeneous pattern plus the existing active
> demand/response facts into the concrete routed bottleneck used by
> `lem:same-token-bottleneck-routing`.
>
> Rows 34--36 run live too, installed after node `[136]` on the same exact
> surplus cursor, so the block is nodes
> `[126]`--`[144]` end to end.  Their mathematics is
> `Graph/MatchingStar.lean` (`lem:same-token-matching-star`),
> `Graph/HomogeneousTokenCap.lean` (the role-fibre partition,
> `lem:same-token-homogeneous-extraction`, `Cap_hom` and `ψ`),
> `Graph/TokenLoadClosure.lean` (`lem:capacity-token-high-load` and
> `thm:tokenized-surplus-accounting-closure` in exact finite form) and
> `Graph/CapacityTokenLedger.lean` (`cor:homogeneous-same-token-caps-close`),
> with `Fixtures/HomogeneousTokenBottleneck.lean` evaluating the arithmetic at a
> concrete presentation.  Row 36's Ledger, Transport and Residual columns are
> backed by the compiling exact-ledger target; its Facts column remains open for
> the paper's final pattern-to-routed-bottleneck and Type B handoff split.
>
> There is **one ledger implementation and one pair representation** across the
> whole block.  `Graph/CanonicalFibreLedger.lean` is the single canonical
> ledger: `Π_blk`, `Π_free` and `ℓ_cap(t)` are its `assigned`, `unassigned` and
> `multiplicity`, and `lem:token-ledger-no-overcount` is its
> `card_assigned_eq_sum_multiplicity`, which rows 34--36 read rather than
> restate.  `TokenLoadClosure` defines no fibre and no load of its own; it adds
> only what the canonical ledger lacks -- the realized `L_max`, the high-load
> display, and the square-root closure.  A pair is a two-element `Finset` of
> demands everywhere, which is what `CanonicalFibreLedger.pairs` and
> `FiniteObject.portPairSchedule` produce, so `PatternFamily` is stated at that
> representation and the matching--star machinery applies to `[130]`'s own
> schedule.
>
> `CapacityTokenLedger.ofPortSchedule` presents the ledger at the object's own
> `portPairSchedule` and takes node `[130]`'s committed `|Π(𝒜₀)| = C(σ(G),2)` as
> an argument precisely so that a caller must have read it.  Every statement the
> rows commit is written out once -- in `Graph/CapacityTokenLedger.lean` for the
> abstract ledger and in `Graph/ObjectCapacityLedger.lean` for the object's own --
> and referenced by both the residual domain's value schema and the row that
> proves it, so the two cannot drift.
>
> Nothing about the token universe is quantified any more: node `[136]` builds
> the three-summand `𝔗_cap`, the four-case `Θ_cap` and
> `lem:capacity-token-supply`'s supply bound, and commits
> `Graph.ObjectCapacityLedger` at every declared presentation, so rows 34--36
> speak about *the* capacity ledger of the object.
> `prop:sparse-entropy-sandwich-with-blockers` is on the ledger too: row 32
> commits it (`Graph.entropySandwich`), and rows 33--36 read the free-pair charge
> off it instead of assuming it.
>
> `Hypostructure/Graph/SurplusPort.lean` is consumed now: `def:surplus-ports` is
> `FiniteObject.SurplusPort`, its shoulder set is `N_G(x(p)) ∖ {c(p)}`,
> `endpoint_degree_eq` spends node `[10]`'s independence, and `card_shoulders`
> gives a port `δ − 1` shoulders.

| # | Node | Where | Ledger | Transport | Residual | Facts |
|---|---|---|---|---|---|---|
| 30 | Ordered surplus activation [125]–[128] | `Spine.sparseSlackSurplus`, `Spine.activeSurplusFamily`, `Spine.sparsePortActivation`, `Spine.sparseSurplusSurvivor`, `Spine.activeSurplusDemands` (`SurplusRows`, `HomogeneousBottleneckRows`, exact surplus ledger) | ✅ | ✅ | ✅ | ✅ |
| 31 | Baseline demand accounting [129] | `Spine.baselineSpineDemand` (`SurplusRows`, exact surplus ledger) | ✅ | ✅ | ✅ | ✅ |
| 32 | Canonical pair-response [130]–[134] | `Spine.canonicalPairLedger`, `Spine.blockedPairRouting` ([132]), `Spine.sparsePairExitClosed` ([133]) (`SurplusRows`, exact surplus ledger) | ✅ | ✅ | ✅ | ✅ |
| 33 | Capacity-token accounting [134]–[136] | `Spine.sparseUpperEnvelope`, `Spine.capacityTokenLedger` (`SurplusRows`, exact surplus ledger) | ✅ | ✅ | ✅ | ✅ |
| 34 | Coupled homogeneous fibre pressure [137]–[143] | `Spine.coupledFibrePressure`, `Spine.sparsePressureDichotomy` (`HomogeneousBottleneckRows`, exact surplus ledger) | ✅ | ✅ | ✅ | ✅ |
| 35 | Finite bottleneck classification [139]–[143] | `Spine.windowClassDichotomy`, `Spine.remainderClassDichotomy`, `Spine.windowIncidenceAudit`, `Spine.remainderSurplusAudit`, `Spine.primitiveCarrierAudit` (`HomogeneousBottleneckRows`, exact surplus ledger) | ✅ | ✅ | ✅ | ✅ |
| 36 | Homogeneous bottleneck [144] | `Spine.homogeneousCapsDichotomy`, `Spine.homogeneousBottleneckPattern`, `Spine.bottleneckRouting`, `Spine.homogeneousBottleneck` (`HomogeneousBottleneckRows`, `SpineEndToEnd`, exact surplus ledger) | ✅ | ✅ | ✅ | ✅ |

## E. Remainder, rank, and net charge

> **Unbuilt.**  The rows in this section were implemented against the legacy
> `Blueprint` topology and its `Core.ProblemDefinition` registry.  Both are
> gone: the registry was deleted with `Official/Definition.lean` and the
> topology is now a commented reference in `StrategyDag.lean`.  Every `Where`
> entry below therefore names a declaration that does not currently elaborate,
> and no ticked column in this section is backed by a compiling target or an
> exported run.  The section is the porting reference for the rewrite, not a
> description of current code.


| # | Node | Where | Ledger | Transport | Residual | Facts |
|---|---|---|---|---|---|---|
| 37 | Support-complement normalization [25]–[27] | `Spine.remainderNormalization` (`SpineRows.remainderNormalizationRow`) | ✅ | ✅ | ✅ | ✅ |
| 38 | Boundary-demand accounting [28]–[29] | `Spine.boundaryDemand` (`SpineRows.boundaryDemandRow`) | ✅ | ✅ | ✅ | ✅ |
| 39 | Wedge lower bound [30] | `Spine.wedgeSupply` (`SpineRows.wedgeSupplyRow`) | ✅ | ✅ | ✅ | ✅ |
| 40 | Target-relative rank dichotomy [31]–[32] | `Spine.curvatureTargetRank`, `Spine.curvatureRankDichotomy` (`SpineRows`) | ✅ | ✅ | ✅ | ✅ |
| 41 | Full-rank finite-state capacity [47]–[56] | `Spine.forcedCurvatureCost`, `Spine.remainderEntropyDichotomy`, `Spine.entropyPackage`, `Spine.entropyCapDichotomy`, `Spine.lowEntropyLargeBudget` | ✅ | ✅ | ✅ | ✅ |
| 42 | Net-charge continuation [57]–[64] | `Spine.netChargeOrderDichotomy`, `Spine.netChargeCap`, `Spine.netChargeLocalization`, `Spine.netChargeDichotomy`, `Spine.negativeSupport`, `Spine.typeSplitDichotomy` | ✅ | ✅ | ✅ | ✅ |

## F. Cold-window corridor

> **Canonical port.** Rows 43--61 are in the canonical ledger surface:
> `Hypostructure/Graph/ColdCorridor.lean`,
> `Hypostructure/Graph/ColdFirstFailure.lean`,
> `Graph/Strategy/ColdCorridorRows.lean`, and
> `Graph/Strategy/ColdCorridorRun.lean`.  The cold Strategy code is a sequence
> of `factOnly` rows; each executor receives sealed `FactInputs`, reads
> prerequisites by exact key, and appends declared facts to the same
> `ExactLedger`.  The row declarations themselves name concrete `Spine.Key`
> manifests, with no `fact.down`/`PLift` adapter callbacks and no carrier
> installation layer.  The cold prefix appends ordinary cold facts through
> `K .coldBranchClosed`, then Core's reserved closure fact.
>
> **Carrier cleanup.** The cold Strategy slice no longer exports a side object
> for handoff routing, no longer exports a cold routing state object, and no
> longer orients germs through a proof-specific object.  Handoff is expressed as
> a predicate `Finset object.Vertex -> Prop` supplied by the incoming ledger.
> The F2, F4, extraction, and germ-routing facts quantify over the paper objects
> directly and never return an object as transport data.
> `Spine.runCold` is no longer callable from a ledger carrying only
> `selection` and `uncompressible`; its type now requires the surviving cold
> prefix facts, including the cold/collided window-density path,
> `largeBudgetResidual`,
> `negativeSupport`, `sparsePressureNearCubic`, `typeBExcluded`, and
> `route8TerminalNoGo`, together with the incoming terminal-leaf fact
> `coldTerminalResidual`.
>
> **Oval boundary.** Carrier-core information in the cold corridor is represented
> only by ordinary `Spine.Key` facts.  In particular `K .coldGermExtraction`
> now reads the first-failure ledger fact and extracts only from vertex supports
> of the current residual whose candidates are realized by current-object
> bounded germs; the disjoint subfamily is existential inside that local fact.
> `K .coldExchangeBound`, `K .coldWindowLedgerSplit`,
> `K .coldHotFailureMass`, `K .coldSelectedBranchExcess`,
> `K .coldAmbientCubicStubExcess`, and `K .coldPositiveGerm` record the
> quantitative chain as separate ordinary facts.  `K .coldGermRouted` records
> the target-defect routing conclusion after G1, G2, and G3 are read from the
> ledger.  `K .coldBranchClosed` records `ColdCorridor.NoTerminalColdResidual`
> by reading the local extraction fact, the positive-germ fact, the routed
> length-changing fact, and the same-interface table fact from the same ledger.
> `Spine.runCold` then closes the oval by `closeIncompatible` from the incoming
> `K .coldTerminalResidual` fact and the appended `K .coldBranchClosed` fact,
> adding Core's reserved closure fact to the same `ExactLedger`.  There is no
> wrapper, side theorem bundle, or payload.
>
> **Build surface.** The active cold fixtures are the signature, ledger,
> construction, short self-return, and cold-prefix audit fixtures.  The prefix
> is audited at whichever full residual ledger actually carries it.  PDE
> registry material is left untouched.

| # | Node / component | Where | Ledger | Transport | Residual | Facts |
|---|---|---|---|---|---|---|
| 43 | Corridor cut-state `T(J)` | `ColdCorridor.CutState`, `Presentation.state` (`Spine.coldCorridorState`) | ✅ | ✅ | ✅ | ✅ |
| 44 | Same-interface table | `ColdCorridor.TableRow`, `ColdCorridor.row_closed` (`Spine.coldSameInterfaceTable`) | ✅ | ✅ | ✅ | ✅ |
| 45 | (F1) producer | `ColdCorridor.Corridor.FirstFailureCycle` (`Spine.coldFailureCycle`) | ✅ | ✅ | ✅ | ✅ |
| 46 | (F2) producer | `ColdCorridor.Corridor.FirstFailureDefect` (`Spine.coldFailureDefect`) | ✅ | ✅ | ✅ | ✅ |
| 47 | (F3) producer | `ColdCorridor.Corridor.FirstFailureCompression` (`Spine.coldFailureCompression`) | ✅ | ✅ | ✅ | ✅ |
| 48 | (F4) producer | `ColdCorridor.Corridor.FirstFailureHandoff` (`Spine.coldFailureHandoff`) | ✅ | ✅ | ✅ | ✅ |
| 49 | (F4) membership | `ColdCorridor.Corridor.handoff_mem` (`Spine.coldFailureHandoff`) | ✅ | ✅ | ✅ | ✅ |
| 50 | First-failure routing | `ColdCorridor.Corridor.exists_firstFailure` (`Spine.coldFailureRouting`) | ✅ | ✅ | ✅ | ✅ |
| 51 | F5 exchange bound | `ColdCorridor.Corridor.exchange_card_le` (`Spine.coldExchangeBound`) | ✅ | ✅ | ✅ | ❌ |
| 51a | Hot/cold window split | `ColdCorridor.coldCount_add_hotCount` (`Spine.coldWindowLedgerSplit`) | ✅ | ✅ | ✅ | ✅ |
| 51b | Hot failure cold mass | `ColdCorridor.hotFailure_coldMass` (`Spine.coldHotFailureMass`) | ✅ | ✅ | ✅ | ✅ |
| 51c | Selected branch excess | `ColdCorridor.selectedBranchExcess_length` (`Spine.coldSelectedBranchExcess`) | ✅ | ✅ | ✅ | ✅ |
| 51d | Ambient-cubic stub excess | `ColdCorridor.branchExcess_ge_of_cubic` (`Spine.coldAmbientCubicStubExcess`) | ✅ | ✅ | ✅ | ✅ |
| 52 | `[155]` G1 realizing | `Spine.coldGermRealizedRow` | ✅ | ✅ | ✅ | ✅ |
| 53 | `[156]` G2 distinguishing | `Spine.coldGermDistinguishedRow` | ✅ | ✅ | ✅ | ✅ |
| 54 | `[157]` G3 neutral | `Spine.coldGermSilentRow` | ✅ | ✅ | ✅ | ✅ |
| 55 | Core dispatch (F1) | `Spine.runCold` row composition | ✅ | ✅ | ✅ | ✅ |
| 56 | Core dispatch (F3) | `Spine.runCold` row composition | ✅ | ✅ | ✅ | ✅ |
| 57 | (F4) dispatch arm | `ColdCorridor.Corridor.handoff_mem` (`Spine.coldHandoffTransfer`) | ✅ | ✅ | ✅ | ✅ |
| 58 | (F5) extraction | current-object support extraction (`Spine.coldGermExtraction`) | ✅ | ✅ | ✅ | ✅ |
| 58a | Positive germ production | `ColdCorridor.coldGerm_positive` (`Spine.coldPositiveGerm`) | ✅ | ✅ | ✅ | ✅ |
| 59 | (F5) G2 routing after G1/G2/G3 | `ColdCorridor.boundedGerm_not_survives` plus G2 target-defect route (`Spine.coldGermRouted`) | ✅ | ✅ | ✅ | ✅ |
| 60 | Registrations `atStage` | `Spine.runCold` row composition, no registration payload | ✅ | ✅ | ✅ | ✅ |
| 61 | Cold oval closure | `ColdCorridor.NoTerminalColdResidual` (`Spine.coldBranchClosed`) | ✅ | ✅ | ✅ | ✅ |

The cold rows are expressed as a canonical ledger prefix, ending in the ordinary
`Spine.Key` fact `coldBranchClosed` and Core's reserved closure fact; they are
not a custom terminal carrier.
The `[138]`
near-cubic arm must still rejoin the normalized spine at `[21]`, pass through
`[22]`--`[24]`, then execute the exhaustive `[145]` interface, `[146]` route-8
threshold, and `[148]` live-hot split before the cold corridor is the active
residual.

## G. Route-8 carrier closure

> **Ported, on the canonical ledger.**  The legacy `TypeARoute8Closure`,
> `TypeARoute8Stages` and `TypeARoute8Carriers` are quarantined and were not
> **Canonical boundary.**  The pure Graph Route 8 carrier, closure, and residual
> mathematics is consumed only through ordinary `Spine.Key` facts.  The route-8
> no arm now has an executable exact-ledger composition:
> `Spine.runRoute8FromExitSevenFree` commits `[109]` from the selected
> exit-seven-free cursor, and `Spine.runRoute8Tail` appends `[110]`--`[124]` in
> manuscript order.  The result is the ordinary fact `route8TerminalNoGo`; it is
> not a closure key, payload, carrier collection, or route-8 side object.  The
> remaining terminal gap is the downstream Core closure that will consume the
> cold corridor facts once Row 61 is finished.

## H. Rank-drop branch (Part III)

> **Ported.**  All of Part III is on the canonical `ExactLedger`, run by
> `Spine.run` against the literal rank-drop ledger: the Branch D entry
> `[33]`/`[35]`, the context-validity test `[36]`, the atom-compression test
> `[38]`, the delocalization-scope test `[41]`, the repair identity `[44]` and
> the global barrier `[45]`.  The figure's caption is *"every rank-drop branch
> terminates in a closed round node"*, and all four terminals close: `[37]`
> through `Core.Strategy.closeImpossible`, and `[39]`, `[42]` and `[46]` through
> `Core.Strategy.closeIncompatible` against the selection.  Branch D leaves no
> open leaf.


Figure `fig:proof-diagram-part-iii`, nodes `[35]`–`[46]`, is the yes arm of
row 40's decision `[32]`.  In the retired `Blueprint` topology that arm was
`(rankDrop := fun rankDropResidual => rankDropResidual)`, the identity, so
`Blueprint.compressionLinkedTargetRelativeRankDichotomy` receives `.root` as its
left subtree: **the whole of Part III is one leaf**, exported as terminal `t3`.
No vertex of the DAG carries any node in `[35]`–`[46]`.  The rows below record
that absence node by node, and where a framework declaration exists but is not
reached from this arm.

| # | Node | Where | Ledger | Transport | Residual | Facts |
|---|---|---|---|---|---|---|
| 68 | Branch D entry [33], [35] | `Spine.branchDependenceRow`, exact Branch-D ledger | ✅ | ✅ | ✅ | ✅ |
| 69 | Context-validity test [36]–[37] | `Spine.contextValidityDichotomy` + `closeImpossible`, exact Branch-D ledger | ✅ | ✅ | ✅ | ✅ |
| 70 | Proper-atom compression [38]–[39] | `Spine.atomCompressionDichotomy` + `closeIncompatible`, exact Branch-D ledger | ✅ | ✅ | ✅ | ✅ |
| 71 | Enlarged delocalization support [40]–[42] | `Spine.delocalizationScopeDichotomy` + `closeIncompatible`, exact Branch-D ledger | ✅ | ✅ | ✅ | ✅ |
| 72 | Whole-graph delocalization [43]–[45] | `Spine.globalBarrierRow`, exact Branch-D ledger | ✅ | ✅ | ✅ | ✅ |
| 73 | Rank-drop branch closed [46] | `closeIncompatible` appends `closed` on `rankDropClosedKeys` | ✅ | ✅ | ✅ | ✅ |

## Row evidence

> **Block A rows 1–10 are written against the live code.**  The pre-port
> registration architecture — `Core.Strategy.TargetAlgebraReduction`,
> `MinimalSubobjectExclusion`, `CriticalModificationStructure`,
> `ObstructionPackingData`, `ExactFiniteLocalAlgebra`, `ScaleThresholdDichotomy`,
> and the `CTAdapters.ct1` / `ct9` / `ct14` / `ct16` executions they ran through
> — is **deleted**.  The live Block A is nine declarations in
> `Graph/Strategy/SpineRows.lean`: seven `factOnly` `AtomicStrategy` rows and two
> `Decision`s, instantiated in `Graph/Strategy/SpineAssembly.lean`.  **No Block A row
> executes a CT at all.**  Where a row's evidence names a deleted module, that
> text is historical and is marked as such at the row.

**Block A compliance sweep (constants, duplication, ledger API).**  Read off the
live code, not the row prose:

- **Hardcoded constants: none.**  Across the ten rows, the thirteen `Holds`
  clauses, and the Block A instantiations, no numeric literal occurs other than
  `0`, `1` and `2`, and each of those is structural rather than tunable: the
  curvature step indices of `C₁`/`C₂`/`Ω₂` (`Safe 1`, `Safe 2`), the base of the
  entropy exponents, and the `2` of the degree-sum handshake.  Every threshold,
  order, rate and scale is a field of the registered `Spine.Data`
  (`threshold`, `windowOrder`, `windowRate`, `surplusScale`, …), and the
  relations between those fields are registered as *proof obligations*
  (`three_le_threshold`, `fanCapSlack`, `joinSlack`, `bridgeMassSlack`) rather
  than as asserted values.  The manuscript's `399`, `543958`, `432672`,
  `111286`, `118.108581006…` and `θ_win` appear nowhere in Block A.
- **Fact traffic is exclusively the framework API.**  Every read is
  `FactInputs.get` on an exact key — `selection` ×4, `noProperBaseline`,
  `barrierCap`, `surplusAtOrBelow` — and every write is a `.cons (key := …)`
  entry in the declared production bundle, committed by the framework runner.
  Grepping the three spine modules for `ExactLedger.root`, `.append`,
  `.publishFact`, `.refine`, `.initializeScope`, `FactInputs.ofLedger` and
  `exactLedgerInternal%` returns nothing, and no row inspects a key index,
  entry list, producer, depth or execution position.  The two dichotomies commit
  through `Decision.run`, so the arm not taken is absent from the taken branch's
  type-level index.
- **Duplication and reimplementation: three defects found, all fixed in this
  change.**  (1) Row 9 re-proved a framework combinatorial bound inline; it now
  calls `Graph.skeletonBudget_le_variableEdgeBudget`.  (2) Row 7 declared a
  prerequisite it never read; its manifest is now `Requires := []`.  (3)
  `Spine.run` took the target's isomorphism invariance as a **hypothesis**,
  although the graph layer already proves it
  (`Graph.hasCycleWithLength_iff_of_iso`, packaged as
  `Graph.minimumDegreeCycleTargetInvariant`); a caller could therefore supply a
  mathematical fact the framework owns.  It is now derived, by the new
  `Spine.spineTargetInvariant`, and `run`'s parameter is gone.  No other Block A
  row re-derives a fact an earlier row committed: the repeated `avoidsOf` /
  `minimalOf` arguments at rows 2, 3, 5 and 6 are *projections* of the single
  `selection` fact, not re-derivations of it.
- **Unregistered facts: none remain.**  After the `targetInvariant` fix, the
  only things Block A accepts from outside are the registered `Spine.Data`, the
  target `T` with its identification `targetPredicate`, and the framework's
  `OpenedScope`.  Every `encode` / `avoidsOf` / `minimalOf` argument at the
  spine-assembly instantiations is a pure projection or injection of a fact *value*
  (`fun _input fact => fact.down.1`, `fun _input value => ⟨value⟩`) and carries
  no mathematics — `FactSystem.value_subsingleton` makes a data-carrying fact
  unelaborable, so this is enforced rather than conventional.  The one external
  mathematical input is `Data.freeForcesTarget`, the cited Hegde–Sandeep–Shashank
  law, which the manuscript itself cites and which enters at the manuscript's own
  interface as the project's single declared axiom.



### Row 1 — Minimal counterexample `[1]`–`[4]`

- **Paper fact.** `def:counterexample` fixes the branch condition: `G` is a counterexample when `\delta(G)\ge3` and `R_e(G)\cap\Mers=\varnothing` for every oriented edge. Immediately after `def:dyadic-safe` the manuscript writes: "we assume that a counterexample exists and choose one, denoted `G`, lexicographically minimal by `(|V(G)|,|E(G)|)`", and sets `n=|V(G)|`, `m=|E(G)|`. Nodes `[1]`–`[4]` are exactly that: an arbitrary finite simple graph, the counterexample test, the "not a counterexample" terminal `[3]`, and the selection `[4]`.
- **What the Lean does.** The vertex is compiled by `Core.Strategy.Dag.minimalCounterexampleStep`, which is `minimalCounterexampleRecipe reduction.selection data.targetDecidable stateOf continuation`. `minimalCounterexampleRecipe` builds a `Strategy.TargetAvoidingContinuation` whose `Target` is `T.Predicate (residualOf stage).object` and whose decider is `data.targetDecidable`; on the `.target` terminal `certify` returns the target proof, on the `.avoiding` terminal it runs `selectedMinimalStage`. `selectedMinimalStage` forms `AvoidingContext.ofBranch ⟨input.object, input.baseline, input.branchState⟩ avoids` and takes `Classical.choice (initial.exists_minimalCounterexample selection.progress stateOf)`. `Core.AvoidingContext.exists_minimalCounterexample` has type: given an `AvoidingContext P Target`, a `Progress P` and a state initializer, `Nonempty (MinimalCounterexampleContext P Target progress)`; its body sets `IsCounterexample G := P.Baseline G ∧ ¬ Target G`, uses `progress.wellFounded_smaller.has_min` on `{G | IsCounterexample G}` and discharges `minimal` by `minimalG H ⟨baselineH, avoidsH⟩ smaller`. The order is *supplied*, not derived: `Graph.Strategy.minimumDegreeCycleCounterexampleReduction` sets `selection := Core.MinimalCounterexampleSelectionData.ofProgress (CanonicalProgress.progress …)`, and the canonical instance is `Graph.lexicographicProgress` with `Measure := LexicographicSize = Nat × Nat`, `lt := Prod.Lex (· < ·) (· < ·)`, `measure := FiniteObject.lexicographicSize = (object.vertexCount, object.edgeCount)`, `wellFounded := wellFounded_lt.prod_lex wellFounded_lt`. `P.Baseline` at this problem is `Graph.MinimumDegreeAtLeast erdosReceiverLoadProfile.baselineDegree`, and `baselineDegree := 3`; `T.Predicate` is `Graph.HasCycleWithLength Core.DyadicLength.PowerOfTwoLength`, with `PowerOfTwoLength length := ∃ exponent : Fin (length+1), 2 ≤ exponent.1 ∧ length = 2 ^ exponent.1`.
- **What it should do.** Select, from the class of objects satisfying `Baseline ∧ ¬Target`, one that is minimal for the well-founded order whose measure is `(|V|,|E|)` ordered lexicographically, and expose it as the object every later vertex argues about; and close the complementary arm (`Target` already holds) as a proof of the registered statement. That is `MinimalCounterexampleContext P T.Predicate (lexicographicProgress …)` produced from an arbitrary `ProblemInput`.
- **Gap.** none. The measure, its order and its well-foundedness are all the manuscript's `(|V(G)|,|E(G)|)`; the counterexample predicate is `Baseline G ∧ ¬ Target G` with `Baseline = MinimumDegreeAtLeast 3` and `Target = HasCycleWithLength PowerOfTwoLength`, so `IsCounterexample` is `def:counterexample` after `lem:return-equivalence` is applied in the other direction. One presentational difference, not a gap in the fact: node `[2]` is drawn as a two-clause test, while the Lean decides only the target clause — `\delta(G)\ge3` is carried as `ProblemInput.baseline` on every input rather than being decided, which is what makes the statement "for every input satisfying the baseline". **Facts passes.**
- **Ledger and residual.** Reads the stable residual `residualOf stage : Strategy.ProblemInput P`. Appends `MinimalSelectionEvidence`, a one-field record holding the selected `MinimalCounterexampleContext`, through `Residual.StageNode.create`, wrapped in `MinimalSelectionStage`, which is a `Ledger.Extension` and so retains the literal predecessor. This is the one vertex in the whole DAG that *moves* the stable residual: the `HasResidual (MinimalSelectionStage …) (ProblemInput P)` instance re-points it at `⟨context.G, context.baseline, context.state⟩`. Everything downstream therefore reads the selected minimal object, not the original input. `MinimalSelectionStage.contextQuery` and `.activeResidualQuery` are the two typed reads exposed; `MinimalSelectionStage.avoids` re-derives `¬ T.Predicate (residualOf selected).object` from the stored context.
- **Transport and terminals.** Core owns everything: the classical decision (`Strategy.TargetAvoidingContinuation.asContract`), the well-ordering selection, and the ledger extension. The application supplies only `progress`, `targetDecidable` and `initialState` — exactly the three `contract_field`s the JSON records for `minimal_counterexample_selection:0`; `targetDecidable` is `Classical.propDecidable` installed by `SealedDag.minimalCounterexampleDefinition`, and `initialState` is `fun _object => ()`. In the export `v3` carries `e0 : v3 → t0`, `kind: output`, `output: target`, `status: closed`, terminal `t0` with `kind: target`, `reason: "minimal-counterexample target arm"` — that is node `[3]`. The avoiding arm is `e1 : v3 → v4`, `kind: sequence`, `status: active`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:counterexample` | def | `Core.AvoidingContext.exists_minimalCounterexample` (its `IsCounterexample := P.Baseline G ∧ ¬ Target G`)<br>`HypostructureErdos64EG.Baseline`<br>`Graph.not_hasCycleWithLength_iff_returnLengthSets_disjoint` (the return-set form, consumed at Row 2) | no CT — Core `minimalCounterexampleRecipe` |
| `def:dyadic-safe` | def | | |

**CT composition at this row.** No CT. The Core recipe is `Core.Strategy.Dag.minimalCounterexampleRecipe`, which composes a `Strategy.TargetAvoidingContinuation` (a classical two-terminal decision, not a CT search) with `Core.AvoidingContext.exists_minimalCounterexample` on the registered `Core.Progress`. The reference table's "CounterexampleReduction | CT1" attributes CT1 to this row; CT1 belongs to Row 2 only. Nothing here searches a schedule, so no CT adapter is invoked; the selection is a well-ordering argument and its cost is a single registered work unit (`StrategyKey.registeredWork = 1`).

---

### Row 2 — Target algebra reduction `[5]`–`[7]`

- **Paper fact.** `def:mersenne-return-set` defines `R_e(G)=\{r:\text{there is a simple path of length }r\text{ from }v\text{ to }u\text{ in }G-e\}` for an oriented edge `e=uv`, and `\Mers=\{2^j-1:j\ge2\}=\{3,7,15,31,\ldots\}`. `lem:return-equivalence` states: "`G` contains a cycle of length `2^j` if and only if there is an oriented edge `e` such that `2^j-1\in R_e(G)`. Hence `G` has no power-of-two cycle if and only if `R_e(G)\cap\Mers=\varnothing` for every oriented edge `e`." Its proof deletes one edge of a dyadic cycle and, conversely, restores the root edge onto the return path. `lem:two-path-criterion` is the companion gluing statement: internally disjoint `P,Q` with common endpoints give a simple cycle of length `|P|+|Q|`. Node `[6]` is the "Mersenne return exists?" test and `[7]` the "power-of-two cycle" terminal.
- **What the Lean does.**  `Spine.returnAvoidanceRow`
  (`Graph/Strategy/SpineRows.lean`), a `factOnly` `AtomicStrategy`:
  `Requires := [selection]`, `Produces := [returnAvoidance]`, installed at
  `SpineAssembly.lean`.  It reads the selection fact with `FactInputs.get`,
  projects its avoidance half, and transports it through
  `Graph.not_hasCycleWithLength_iff_returnLengthSets_disjoint data.LengthOK`,
  committing `∀ dart, Disjoint (returnLengthSet object dart)
  (shiftedAcceptedSet data.LengthOK)`.
- **What it should do.**  Restate node `[1]`'s avoidance in the return-set form
  `lem:return-equivalence` gives, so later nodes argue about `R_e(G)` rather
  than about cycles.
- **Gap.**  None.  `lem:return-equivalence` is a framework theorem about
  `LengthOK` and is applied, not restated: the row contains no equivalence proof
  of its own.  `Mers` is not written anywhere — the accepted set is
  `data.LengthOK`, and the shift is the framework's `shiftedAcceptedSet`.
- **Ledger and residual.**  One read by exact key, one production, residual
  unchanged; `Produces ++ known` retains every earlier key.
- **Transport and terminals.**  No CT, no carrier, no routing.  Node `[7]`'s
  terminal is not this row's: it is closed before the scope opens, on the arm
  node `[1]` does not take.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:return-equivalence` | lem | `Graph.not_hasCycleWithLength_iff_returnLengthSets_disjoint` | framework theorem, applied here |
| `def:mersenne-return-set` | def | `Graph.returnLengthSet`<br>`Graph.shiftedAcceptedSet` | framework definitions at `data.LengthOK` |
| `lem:two-path-criterion` | lem | (inside the equivalence's own proof) | not a separate row obligation |

**CT composition at this row.**  None.  A `factOnly` `AtomicStrategy`; the CT1
certificate machinery earlier revisions described is deleted.

### Row 3 — Minimal subobject exclusion `[8]`

- **Paper fact.** `lem:no-proper-core`: "Every proper subgraph `H\subsetneq G` satisfies `\delta(H)\le2`." Proof: a proper subgraph with `\delta(H)\ge3` has no power-of-two cycle, because every cycle of `H` is a cycle of `G`; it would be a smaller counterexample. Node `[8]` is "no proper subgraph with minimum degree 3".
- **What the Lean does.**  `Spine.noProperBaselineRow`, a `factOnly`
  `AtomicStrategy`: `Requires := [selection]`,
  `Produces := [noProperBaseline]`, installed in `SpineAssembly.lean`.  It reads
  the selection fact once and uses *both* halves — avoidance and minimality —
  composing them through `Graph.cycleProperSubgraphTargetMonotone`: a proper
  subgraph meeting the baseline is strictly smaller, so minimality gives it the
  target, monotonicity carries that target up to the ambient object, and
  avoidance refutes it.  The committed fact is
  `∀ subgraph : Graph.ProperSubgraph object,
  ¬ Graph.MinimumDegreeAtLeast data.threshold subgraph.value`.
- **What it should do.**  State `lem:no-proper-core` at the registered
  baseline, derived from node `[1]`'s minimality rather than assumed.
- **Gap.**  None.  Both halves come from the one `selection` fact; nothing is
  re-selected and no minimality is re-established.  The manuscript's `δ(H) ≤ 2`
  is the negation of `MinimumDegreeAtLeast data.threshold` at the registered
  `threshold`, so the `3` of the paper is `data.threshold` and appears nowhere.
- **Ledger and residual.**  One read by exact key, one production, residual
  unchanged.
- **Transport and terminals.**  No CT, no carrier, no routing, no terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:no-proper-core` | lem | `Graph.Strategy.Spine.noProperBaselineRow`<br>`Graph.cycleProperSubgraphTargetMonotone`<br>`Graph.ProperSubgraph` | derived here from the `selection` fact |

**CT composition at this row.**  None.  A `factOnly` `AtomicStrategy`.

### Row 4 — Critical modification structure `[9]`–`[10]`

- **Paper fact.** `lem:deletion-critical`: "Every edge of `G` has at least one endpoint of degree `3`. In particular, the set `V_{\ge4}(G)` is independent." Proof: if `xy` had `d_G(x),d_G(y)\ge4`, then `\delta(G-xy)\ge3` and every cycle of `G-xy` is a cycle of `G`, so `G-xy` is a counterexample with one fewer edge, contradicting edge-minimality. Node `[9]` is the first clause, node `[10]` the second.
- **What the Lean does.**  `Spine.deletionCriticalityRow`, a `factOnly`
  `AtomicStrategy` with a two-key production:
  `Requires := [noProperBaseline]`,
  `Produces := [tightEndpoint, slackIndependent]` (`pairManifest`), installed at
  `SpineAssembly.lean`.  Node `[9]` is proved by contradiction: if some dart had
  both endpoints strictly above the threshold, then
  `Graph.minimumDegreeDeletionCriticalityProfile data.threshold
  |>.baseline_of_not_critical` gives the edge-deleted object the baseline, and
  `Graph.ProperSubgraph.deleteEdge` presents it as a proper subgraph — which the
  required `noProperBaseline` fact has just excluded.  Node `[10]` is then
  derived *from node `[9]`* inside the same executor, by matching on the tight
  alternative at the dart `⟨(left, right), adjacent⟩`.
- **What it should do.**  Prove both clauses of `lem:deletion-critical`, the
  second from the first, on the registered baseline.
- **Gap.**  None.  Neither clause is registered, and the one-edge degree
  accounting is the framework profile's, not the row's.  The manuscript's
  "equivalently" is the literal derivation of the second production from the
  first: `slackIndependent`'s proof consumes `tight`, so the two facts are not
  independently asserted.
- **Ledger and residual.**  One read by exact key; both productions are declared
  in the manifest, so omitting either would fail to elaborate.  Residual
  unchanged.
- **Transport and terminals.**  No CT, no carrier, no routing, no terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:deletion-critical` (clause 1, `[9]`) | lem | `Graph.Strategy.Spine.Holds .tightEndpoint`<br>`Graph.DeletionCriticalityProfile.baseline_of_not_critical`<br>`Graph.ProperSubgraph.deleteEdge` | derived here by contradiction against `noProperBaseline` |
| `lem:deletion-critical` (clause 2, `[10]`) | lem | `Graph.Strategy.Spine.Holds .slackIndependent` | derived here *from* clause 1, as the manuscript derives it |

**CT composition at this row.**  None.  A `factOnly` `AtomicStrategy` with a
two-key production.

### Row 5 — Interface replacement closure `[11]`–`[14]`

- **Paper fact.** `def:boundaried-gluing` fixes `T`-boundaried graphs and `X\oplus_TY`; `def:atom` fixes an atom as a connected `T`-boundaried subgraph occurring as one side of `G=X\oplus_TY`, proper when `X\ne G`; `def:boundary-degree-profile` fixes `\mathbf d_\partial(X)=(d_X(v_t))_{t\in T}` and states "two boundaried states with different boundary degree profiles are never eligible to be identified by a target-complete quotient"; `def:obstruction-profile` fixes `\profile_T(X)=\{Y\in\Ctx_T:X\oplus_TY\text{ contains a power-of-two cycle}\}` and `X'\preceq_TX` as `\profile_T(X')\subseteq\profile_T(X)`; `def:target-complete-quotient` requires an identification to preserve "(a) the boundary degree profile `\mathbf d_\partial(X)`; and (b) the target predicate after gluing `X` to every `T`-boundaried context". `lem:degree-profile-fibres`: if `\mathbf d_\partial(X_1)\ne\mathbf d_\partial(X_2)` then no target-complete quotient identifies `X_1` and `X_2`. `lem:context-universality`: coordinates identified in a target-complete quotient "have the same target response against every `T`-boundaried context `Y`". `lem:replacement`: for `G=X\oplus_TY` with `X` a proper atom and `X'` satisfying (i) `X'\preceq_TX`, (ii) `\mathbf d_\partial(X')=\mathbf d_\partial(X)`, (iii) `X'` has no internal power-of-two cycle, (iv) every internal vertex of `X'` has degree at least `3`, (v) `X'` strictly smaller in the same lexicographic order — "Then `G` was not minimal. Consequently no such replacement exists in `G`." `cor:uncompressible`: "No proper atom of `G` admits a nontrivial target-complete compression", plus the second assertion that a non-target-complete identification cannot be used as a replacement.
- **What the Lean does.** `Core.Strategy.InterfaceReplacement.Profile` is a supplied record: `semantics : Core.SemanticEquivalence P`, `targetInvariant`, `assembly : Core.AtomContextAssembly P semantics`, `Signature : assembly.Interface → Type`, `signature : Atom interface → Signature interface`. Over it Core defines `Profile.TargetComplete source replacement` as a two-field `Prop`: `signature_eq : signature replacement = signature source` (clause (a)) and `contextUniversal : ∀ context, compatible source context → compatible replacement context → (T.Predicate (assemble replacement context) ↔ T.Predicate (assemble source context))` (clause (b)); and `Profile.ObstructionProfileLE source replacement := ∀ context, compatible source context → compatible replacement context → T.Predicate (assemble replacement context) → T.Predicate (assemble source context)` — the one-way `\preceq_T`. `TargetComplete.obstructionProfileLE` derives the second from the first. `Profile.StrictReplacement ctx site` bundles `replacement : assembly.Replacement ctx.G site`, `signature_eq`, `obstruction_le`, `baseline : P.Baseline (assembly.replace replacement)`, `smaller : progress.Smaller (assembly.replace replacement) ctx.G`. `Profile.Compression` is the same with `complete : TargetComplete …` in place of the signature/obstruction pair, and `Compression.toStrictReplacement` converts it. `strictReplacementImpossible ctx site : ¬ Nonempty (StrictReplacement ctx site)` is the load-bearing proof: from `smaller` and `baseline` it gets `ctx.target_of_smaller` — the *minimality kernel* forces the strictly smaller baseline object to have the target — then applies `obstruction_le` at the literal extracted context `assembly.context ctx.G site` (compatibility from `assembly.extractedCompatible` and `replacement.compatible`) to obtain the target on `assemble (atom ctx.G site) (context ctx.G site)`, and closes with `ctx.avoids ((targetInvariant.target_iff (assembly.reconstruct ctx.G site)).mp sourceTarget)`. `Profile.registration ctx` sets `signatureAt := fun site => signature (atom ctx.G site)`, `signatureAt_eq := rfl`, and proves `mismatchRejected : ∀ site replacement, signature replacement.atom ≠ signature (atom ctx.G site) → ¬ TargetComplete (atom ctx.G site) replacement.atom` by `fun different complete => different complete.signature_eq`. `universalReplacement` emits `contextUniversal := fun complete => complete.contextUniversal` (a re-packaging of the hypothesis field, exactly as the manuscript's proof of `lem:context-universality` is "This is precisely the meaning of target-completeness"), `noStrictReplacement := strictReplacementImpossible`, `noCompression` via `Compression.toStrictReplacement`. `uncompressible` adds `defective := fun notUniversal complete => notUniversal complete.contextUniversal`, again a re-packaging. On the Graph side `Graph.Strategy.InterfaceReplacement.assemblyWithPresentation` sets `Interface := Graph.Boundary`, `Site := Graph.ProperBoundariedAtom`, `Atom := Graph.BoundaryPiece`, `Context := Graph.OutsideContext`, `compatible := fun _ _ => True`, `assemble := Graph.glue`, and `reconstruct := ⟨atom.decomposition.reconstructionIso⟩`; `profileWithPresentation` sets `Signature := fun boundary => ULift (BoundaryDegreeProfile boundary)` and `signature := fun piece => ULift.up piece.boundaryDegreeProfile`, where `BoundaryPiece.boundaryDegreeProfile piece := fun vertex => piece.pack.degree (.inl vertex)` and `BoundaryDegreeProfile boundary := boundary.Vertex → Nat`. `Graph.ProperBoundariedAtom object` has fields `decomposition : OwnedDecomposition object`, `connected : decomposition.piece.graph.Connected`, `proper : decomposition.IsProperSide`, and `IsProperSide decomposition := ¬ (Function.Surjective decomposition.pieceIntoAmbient ∧ decomposition.pieceImage.graph = object.graph)`, with `piece_lexicographicallySmaller` deriving strict progress from properness. The EG registration passes `interfaceReplacement := InterfaceReplacement.profileWithPresentation (MinimumDegreeAtLeast k) BranchState baselineInvariant Presentation presentation targetInvariant`, with `targetInvariant.target_iff` proved by `hasCycleWithLength_iff_of_iso`.
- **What it should do.** At the selected `ctx.G`, for every proper connected boundaried atom site: reject every replacement piece with the same boundary-degree vector whose obstruction profile is contained in the source's, which preserves the baseline and strictly decreases the registered order; state that a boundary-degree mismatch already blocks target-completeness; state that target-complete identifications agree against every compatible context; and retain all three as hereditary facts every later residual can read.
- **Gap.** none. The Lean's `signature` is the manuscript's `\mathbf d_\partial`, `ObstructionProfileLE` is `\preceq_T` (and `compatible ≡ True` in the Graph assembly, so the quantifier really is over all boundaried contexts, i.e. `\Ctx_T`), `Site = ProperBoundariedAtom` carries `def:atom`'s connectedness and properness, and `assemble = glue` is `def:boundaried-gluing`'s `\oplus_T`. Hypothesis (iii) of `lem:replacement` ("`X'` contains no internal power-of-two cycle") is absent from `StrictReplacement`, but it is subsumed: `\profile_T` as the manuscript defines it already counts cycles internal to the atom, so `X'\preceq_TX` alone gives the wholly-inside-`X'` case, and `obstruction_le` in the Lean quantifies over the full assembled object's target for the same reason. Hypothesis (iv) ("every internal vertex of `X'` has degree at least `3`") is carried by `baseline : P.Baseline (assembly.replace replacement)`, which at this problem is `3 ≤ (glue replacement.atom (context ctx.G site)).minDegree` and so constrains internal and boundary degrees together — a stronger clause than (iv) alone, in the direction that makes the exclusion weaker but the *paper's* conclusion still available, since (ii) plus (iv) is exactly what the manuscript uses to conclude `\delta(G')\ge3`. Two proof bodies (`contextUniversal`, `defective`) only re-package their hypothesis fields; the manuscript's proofs of `lem:context-universality` and of the second half of `cor:uncompressible` are the same re-packaging. **Facts passes.**
- **Ledger and residual.** Reads `Strategy.CounterexampleReduction.contextAfterCritical reduction context`, the selected-context query preserved across all four preceding extensions. `closure previous` appends three entries in order: `InterfaceSupportStage` (the pointwise `Registration`), `ContextUniversalStage` (`UniversalReplacement`), `UncompressibleStage` (`Uncompressible`), each a `Ledger.Extension` with `interfaceSupport_previous`, `contextUniversal_previous`, `uncompressible_previous` all `rfl` — the literal predecessor is retained at every step. The residual is unchanged. `ClosurePayload` collapses the three at one stage and `closurePayloadQuery` publishes it; the stage-shape-free consumer interface is `ExactClosureQueries`, which the compiler hands to `coldBranchAggregationRecipe` (as `exactClosure`) and to the compression-linked rank recipe, and `ClosurePayload.noCompressionCandidate` / `noNeutralCompressionFrame` are the two forms downstream branches actually apply.
- **Transport and terminals.** Core owns all three nodes; Graph supplies only the assembly and the signature. The application supplies the single `contract_field` the JSON records for `interface_replacement_closure:0`, `interfaceReplacement` — realized by `Graph.Strategy.InterfaceReplacement.profileWithPresentation` inside `Graph.Strategy.minimumDegreeCycleCounterexampleReduction`. Both invariants that entry point needs are proved *there*, in Graph coordinates, not supplied by the application: `Graph/Strategy/CounterexampleReduction.lean:93`–`:115` builds `baselineInvariant` (`:94`) by `FiniteObject.minDegree_eq_of_isomorphic` and `targetInvariant` (`:105`) by `hasCycleWithLength_iff_of_iso`, both inside the `interfaceReplacement` field itself before it calls `profileWithPresentation` at `:113`. (`HypostructureErdos64EG.Official.erdosBaselineInvariant` and `erdosTargetInvariant` exist and prove the same two statements from the same two framework theorems, but they are *not* consumed here: their only call site is `compressionLinkedTargetRelativeRankWithPresentation` at `Official/Definition.lean:452`–`:454`, the registration Row 40 retired — that registration is no longer in the live build, so the pair is now consumed nowhere.) So the application contributes nothing at all to this row beyond the presentation it already registered. In the export `v7` has no output edge: `e4 : v6 → v7` in, `e5 : v7 → v2` out, both `kind: sequence`, `status: active`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:boundaried-gluing` | def | `Graph.Boundary`<br>`Graph.BoundaryPiece`<br>`Graph.glue` | no CT |
| `def:atom` | def | `Graph.ProperBoundariedAtom`<br>`Graph.OwnedDecomposition.IsProperSide` | no CT |
| `def:boundary-degree-profile` | def | `Graph.BoundaryPiece.boundaryDegreeProfile`<br>`Graph.BoundaryDegreeProfile` | no CT |
| `def:obstruction-profile` | def | `Core.Strategy.InterfaceReplacement.Profile.ObstructionProfileLE` | no CT |
| `def:target-complete-quotient` | def | `Core.Strategy.InterfaceReplacement.Profile.TargetComplete` | no CT |
| `lem:target-complete-quotient-composition` | lem | | |
| `lem:degree-profile-fibres` | lem | `Core.Strategy.InterfaceReplacement.Profile.Registration.mismatchRejected`<br>`Core.Strategy.InterfaceReplacement.Profile.registration` | no CT |
| `lem:context-universality` | lem | `Core.Strategy.InterfaceReplacement.Profile.UniversalReplacement.contextUniversal`<br>`Core.Strategy.InterfaceReplacement.Profile.Uncompressible.defective` | no CT |
| `lem:replacement` | lem | `Core.Strategy.InterfaceReplacement.Profile.StrictReplacement`<br>`Core.Strategy.InterfaceReplacement.strictReplacementImpossible`<br>`Core.Strategy.InterfaceReplacement.Profile.UniversalReplacement.noStrictReplacement` | no CT |
| `def:target-complete-compression` | def | `Core.Strategy.InterfaceReplacement.Profile.Compression`<br>`Core.Strategy.InterfaceReplacement.Profile.Compression.toStrictReplacement` | no CT |
| `cor:uncompressible` | cor | `Core.Strategy.InterfaceReplacement.Profile.Uncompressible`<br>`Core.Strategy.InterfaceReplacement.uncompressible`<br>`Core.Strategy.InterfaceReplacement.ClosurePayload.noCompressionCandidate` | no CT |
| `def:target-rank` | def | | |
| `lem:independent-target-entropy` | lem | `Core.FiniteEntropy.two_pow_le_card_ambient_of_realizes`<br>`Graph.LabelledOn.two_pow_le_card_of_realized` | stated, not applied — see the note |

`lem:target-complete-quotient-composition` and `def:target-rank` are in the same manuscript subsection as `[11]`–`[14]` but are consumed at the rank-drop branch (nodes `[31]`–`[45]`), outside rows 1–8; nothing in the tree states either as a type. `lem:independent-target-entropy` is placed here because it closes the same subsection; the two declarations state its inequality generically, but neither is applied anywhere in `hypostructure` or `examples`. Row 32's entropy sandwich needs the composition of this lemma with `lem:skeleton-dominates` **at the `m`-edge stratum** — `2^k ≤ Graph.skeletonBudget object` — and neither declaration reaches that stratum: `two_pow_le_card_ambient_of_realizes` bounds by the whole finite ambient and `two_pow_le_card_of_realized` by `Nat.card (LabelledOn n)`, the labelled graphs on `[n]` before the edge count is fixed. That stratum-level composition is the one open interface of row 32's **Gap**.

---

**CT composition at this row.** No CT, correcting the reference table, which lists this strategy as CT7. `Core/Strategy/InterfaceReplacement.lean` contains no `CTAdapters.ct*` call; the only occurrence of "CT7" in the file is inside a comment at `:161`, which is inadmissible evidence. The recipe is three `StageNode.create` runs (`:333`, `:355`, `:493`) chained into one closure: registration, then `UniversalReplacement`, then `Uncompressible`. Each stage is a derivation over the registered assembly rather than a bounded search, so a CT adapter would have nothing to schedule; what the three-stage chain buys is that `noStrictReplacement` at stage two is available as a literal predecessor fact to the compression elimination at stage three, instead of both being re-derived from the ambient context.

### Row 6 — Induced-obstruction packing `[15]`–`[17]`

- **Paper fact.** `thm:p13free` (Hegde–Sandeep–Shashank, cited): "Every `P_{13}`-free graph of minimum degree at least `3` contains a cycle whose length is a power of two." `cor:p13-exists`: "The minimal counterexample `G` contains an induced `P_{13}`", proved by contradiction against the counterexample condition. The prose that follows fixes `p_{13}` as "the maximum size of a vertex-disjoint family of induced copies of `P_{13}` in `G`" and `\theta=p_{13}/n`; the branch table records that "a vertex-disjoint induced-`P_{13}` family is chosen maximal" and that "every unchosen induced window meets the packing". Node `[15]` is the freeness test, `[16]` the HSS terminal, `[17]` the maximal packing.
- **What the Lean does.**  `Spine.obstructionPackingRow`, a `factOnly`
  `AtomicStrategy`: `Requires := [selection]`, `Produces := [maximalPacking]`,
  installed in `SpineAssembly.lean`.  `cor:p13-exists` is proved by
  contradiction: were the object free of induced windows of the registered
  order, `Graph.FiniteObject.inducedPathFree_of_forall_not_inducesWindow` would
  make it window-free and `data.freeForcesTarget` — the registered
  Hegde–Sandeep–Shashank law — would give it the target, which the selection
  fact refutes.  The packing itself is
  `object.exists_windowPacking_card_eq data.windowOrder`, positivity is
  `windowPackingNumber_pos` against the exhibited window, and *maximality is
  derived, not assumed*: `exists_mem_not_disjoint_of_card_eq` shows a window
  disjoint from every member could be added, contradicting attainment.
- **What it should do.**  Commit `cor:p13-exists`, the positive packing number,
  and a family attaining it whose maximality is proved.
- **Gap.**  None.  The external law enters only as the registered
  `Data.freeForcesTarget` field, at the manuscript's own interface, and
  `data.windowOrder` stands for `13` throughout — no order is written.  The
  family never leaves the row: what the ledger records is the *number*
  `object.windowPackingNumber data.windowOrder`, an observable of the object,
  together with the statement that some family attains it.  This is what makes
  the packing safe to quantify over downstream without transporting a `Finset`,
  and it is enforced rather than conventional —
  `FactSystem.value_subsingleton` makes a data-carrying fact unelaborable.
- **Ledger and residual.**  One read by exact key, one production, residual
  unchanged.
- **Transport and terminals.**  No CT, no carrier, no routing.  Node `[16]`'s
  HSS terminal is not reachable here: the row proves its arm is empty.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `thm:p13free` (Hegde–Sandeep–Shashank) | thm | `Graph.Strategy.Spine.Data.freeForcesTarget` | registered presentation input; the project's one declared axiom, `HypostructureErdos64EG.p13Free_hasPowerOfTwoCycle` |
| `cor:p13-exists` | cor | `Graph.FiniteObject.inducedPathFree_of_forall_not_inducesWindow` | derived here by contradiction against `selection` |
| maximal packing (`[17]`) | prose | `Graph.FiniteObject.exists_windowPacking_card_eq`<br>`Graph.FiniteObject.windowPackingNumber_pos`<br>`Graph.FiniteObject.exists_mem_not_disjoint_of_card_eq` | maximality derived from attainment, not assumed |

**CT composition at this row.**  None.  A `factOnly` `AtomicStrategy`.

### Row 7 — Exact finite local algebra `[18]`

> **Live-code correction (this change): the row declared a prerequisite it never
> read.**  `Spine.localAlgebraRow` is the live node `[18]`.  Its manifest
> declared `Requires := [maximalPacking]`, but its executor never called
> `FactInputs.get` on that key — the fact it commits is
> `legalCodeList_length` together with `curvatureTwo_eq_true_iff`, both theorems
> about `data.windowOrder` alone.  `Holds .localAlgebra` takes `_object`: the
> statement ignores the residual entirely, so there was no dependency to
> declare.  Declaring one used the manifest to express paper order, which the
> row order in `SpineAssembly` already expresses, and asserted a prerequisite the
> row does not have.  The row now uses a new `sourceFreeManifest` with
> `Requires := []` (legal — `List.Nodup []` holds, and `producesNonempty`
> constrains only `Produces`), and the spine-assembly instantiation drops the key and
> its freshness argument.  Ledger, Transport, Residual and Facts are unaffected:
> the row commits the same fact, from the same theorems, through the same runner.


- **Paper fact.** Node `[18]` is "`P_{13}` label algebra: `399` labels; relations `C_s`; curvature `\Omega_2`". The manuscript defines the attachment label `S(x)=\{i:xv_i\in E(G)\}\subseteq\{0,\ldots,12\}`, shows a label is legal iff `|i-j|\notin\{2,6\}` for all `i,j\in S` (because `(j-i)+2\in\{4,8\}` are the only dyadic closing lengths available), and sets `\labels=\{S\subseteq\{0,\ldots,12\}: S\ne\varnothing\text{ and }|i-j|\notin\{2,6\}\ \forall i,j\in S\}`. `lem:labels`: "`|\labels|=399`. The distribution by size is `13,60,122,122,63,17,2` for sizes `1,\ldots,7`", proved by direct enumeration. `lem:curv-enum` introduces `\Omega_2(S,A,T)` as the two-step curvature test `C_1(S,A)C_1(A,T)(1-C_2(S,T))` and counts `543958`, `432672`, `111286`, giving `c_\Omega=\log_2(543958/111286)`; the counts and `c_\Omega` belong to node `[21]`, only `\Omega_2` itself is named at `[18]`.
- **What the Lean does.**  `Spine.localAlgebraRow`, a `factOnly`
  `AtomicStrategy`: `Requires := []`, `Produces := [localAlgebra]`, installed at
  `SpineAssembly.lean`.  The committed fact is the conjunction of
  `Graph.WindowCurvature.legalCodeList_length data.windowOrder` — the legal-label
  enumeration has exactly as many entries as there are legal labels — and
  `Graph.WindowCurvature.curvatureTwo_eq_true_iff`, which characterizes `Ω₂` as
  `Safe 1 source middle ∧ Safe 1 middle target ∧ ¬ Safe 2 source target`.  Both
  are framework theorems about `data.windowOrder`, quoted; the row proves
  nothing itself.
- **What it should do.**  Commit `lem:labels`' enumeration identity and the
  definition of `Ω₂`, at the registered window order, without writing the
  manuscript's counts.
- **Gap.**  None.  The manuscript's `399` is the *computed length* of
  `legalCodeList data.windowOrder` at the manuscript's own order; it is not
  written in the row, in the clause, or in the `Data`.  The legality condition
  is derived from the registered dyadic target rather than listed —
  `forbiddenGaps_zero : forbiddenGaps windowOrder 0 = {2, 6}` is a theorem, not
  a definition — so the paper's `|i−j| ∉ {2,6}` is a consequence, not an input.
  `lem:curv-enum`'s three counts and `c_Ω` belong to node `[21]`, not here.
- **Ledger and residual.**  No read; one production; residual unchanged.  See
  the live-code correction above for why `Requires` is empty: the fact is a
  theorem about the presentation and `Holds .localAlgebra` ignores the object,
  so there is no prerequisite to declare.
- **Transport and terminals.**  No CT, no carrier, no routing, no terminal.
  The deleted `Core.Strategy.ExactFiniteLocalAlgebra` registration, its CT9/CT16
  composition, the `LabelDenotation` bijection and the `native_decide` row
  shards that earlier revisions of this row described are all gone from this row's
  slice; the audited `P13Barrier` table now reaches the spine only through
  `Data`, and the row consumes none of it.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:labels` | lem | `Graph.WindowCurvature.legalCodeList_length`<br>`Graph.WindowCurvature.Labels`<br>`Graph.WindowCurvature.Legal`<br>`Graph.WindowCurvature.forbiddenGaps` | quoted at `data.windowOrder`; the `399` and the size distribution are computed, not written |
| `Ω₂` (node `[18]`'s named relation) | def | `Graph.WindowCurvature.curvatureTwo`<br>`Graph.WindowCurvature.curvatureTwo_eq_true_iff` | quoted |
| `lem:curv-enum` | lem | | node `[21]`, not this row |

**CT composition at this row.**  None.  A `factOnly` `AtomicStrategy` with no
prerequisite.

### Row 8 — Non-near-cubic surplus split `[19]`

- **Paper fact.** Node `[19]` is the diamond "non-near-cubic surplus? `\sigma(G)>C_{\rm sp}\sqrt n`". `def:surplus-ports` fixes the quantity: `|\mathcal P_{\rm exc}|=\sum_{h\in H}(d_G(h)-3)=\sigma(G)` with `H=V_{\ge4}(G)`. `def:near-cubic-spine` is the complementary arm: "every lexicographically minimal counterexample surviving to the entropy/net-charge spine satisfies `m=\frac32 n+O(\sqrt n)`, `\sigma(G)=O(\sqrt n)`", and it records that "this estimate is supplied by `prop:nonnear-cubic-sharp-overload-routing` before either the normalized skeleton budget … or the fan-mass estimate … is invoked". The strict arm enters node `[20]`, the surplus-pair accounting branch, whose exhaustion is `prop:nonnear-cubic-sharp-overload-routing` (outcomes: near-cubic spine estimate, a sparse surplus exit, or decorated Type B fan data).
- **What the Lean does.**  `Spine.surplusDichotomy`
  (`Graph/Strategy/SpineRows.lean`), a two-arm `Decision` — not a CT and not a
  `factOnly` row in the spine assembly.  It branches on
  the decidable comparison

  ```
  if above : data.surplusThreshold current.object.vertexCount <
      current.object.degreeSurplus data.threshold
  ```

  committing `surplusAbove` on the strict side and `surplusAtOrBelow` on the
  other, the latter from `Nat.le_of_not_lt`.  `Decision.run` commits exactly one
  arm, so the sibling key is absent from the taken branch's type-level index.
  `Data.surplusThreshold size = data.surplusScale * Core.ceilSqrt size`: the
  registered coefficient against the framework's own ceiling square root.
- **What it should do.**  Split node `[19]` exhaustively on
  `σ(G)` against `C_sp·√n`, carrying a *proved* inequality on each arm so
  `def:near-cubic-spine` is retained rather than assumed downstream.
- **Gap.**  None.  The split is exhaustive by `Nat` trichotomy and each arm
  commits its own proved inequality.  `object.degreeSurplus data.threshold` is
  `2m − δn`, which on the standing baseline `δ(G) ≥ δ` equals
  `Σ_{h ∈ V_{>δ}}(d(h) − δ)` — `def:surplus-ports` — and the `Nat` truncation is
  inert for the same reason.  Only the *coefficient* `surplusScale` is
  registered.  No later row turns the square-root threshold into a finite
  linear contradiction by inserting an order cutoff; the generic Residual C
  consumer retains the exact window-join-pressure complement instead.  No
  decimal and no `C_sp` value occurs.
- **Ledger and residual.**  No read: both sides of the comparison are
  observables of the active object.  One arm committed, residual unchanged, the
  other arm's key absent from this branch.
- **Transport and terminals.**  No CT, no carrier, no routing helper.  The
  strict arm is the exact ledger indexed by `surplusAboveKeys` and is where
  node `[20]`'s surplus-pair accounting chain begins; the at-or-below arm
  continues into node `[21]`.  Neither is a paper terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:surplus-ports` | def | `Graph.FiniteObject.degreeSurplus` | `2m − δn`, equal to the paper's `σ(G)` on the standing baseline |
| node `[19]` split | dia | `Graph.Strategy.Spine.surplusDichotomy`<br>`Graph.Strategy.Spine.Holds .surplusAbove`<br>`Graph.Strategy.Spine.Holds .surplusAtOrBelow` | exhaustive `Decision`; both arms carry a proved inequality |
| `def:near-cubic-spine` | def | `Graph.Strategy.Spine.Data.surplusThreshold` | the exact square-root threshold is carried on the at-or-below arm |
| `prop:nonnear-cubic-sharp-overload-routing` | pro | | node `[20]`, on the `surplusAbove` exit — outside Block A |

**CT composition at this row.**  None.  A `Decision` over the canonical ledger;
the CT14 aggregate-member comparison earlier revisions described is deleted.

### Row 9 — Near-cubic finite enumeration `[21]`

- **Paper fact.** Node `[21]` is "finite enumeration: `c_Ω`, `c₁₃`".
  `lem:curv-enum` states three integer counts over the `399` legal labels —
  `|{(S,A,T) : C₁(S,A)=C₁(A,T)=1}| = 543958`,
  `|{(S,A,T) : Ω₂(S,A,T)=1}| = 432672`, hence `111286` curvature-flat locally
  safe wedges — and derives
  `c_Ω = log₂(543958/111286) = 2.28922315244…`.  The same node carries the
  `91`-barrier package constant `c₁₃ = 118.108581006…`, the sum over the `91`
  ordered pairs `(a,b)` with `a,b ≥ 1`, `a+b ≤ 14` of the flatness costs
  `log₂(W_{a,b}/F_{a,b})`, where `W_{a,b}` counts locally safe triples with
  `C_a(S,A)=C_b(A,T)=1` and `F_{a,b}` those that stay safe under
  `C_{a+b}(S,T)=1` (`lem:p13-window-package`).  The node also carries the
  edge-count budget lemmas `lem:variable-edge-budget`
  (`≤ |I|·max_{m∈I} C(C(n,2),m)`, log-loss `≤ 2 log₂ n`) and
  `lem:near-cubic-budget` (`log₂ C(C(n,2),m) = (3/2) n log₂ n + O(n) +
  O(√n log n)` when `m = (3/2)n + O(√n)`), scoped by
  `rem:near-cubic-budget-scope` and `rem:budget-robustness`.
- **What the Lean does.** Node `[21]` is now the fact-only atomic row
  `Graph.Strategy.Spine.barrierEnumerationRow`. Its manifest requires the
  predecessor's `localAlgebra` fact and produces exactly
  `windowPackageSeparated`; the value of that legacy-named key is now
  `BarrierEnumerationStatement`, not the later independent-window package.
  The sealed executor reads `inputs.current` and `inputs.get localAlgebra`,
  keeps the current residual definitionally unchanged, and derives the two
  registered rates and the aggregate safe/flat inequality from the public
  certified table. The retired `Core.Strategy.FiniteBarrierEnumeration`
  module and its `Profile`/`Summary`/`RateLedger` are **deleted**; the finite
  enumeration itself is now the audited table `FiniteChecks.P13Barrier`.
  `Spine.Data.windowBarrier` exposes its complete semantic relation, all `91`
  accepted `(a,b)` rows, and both certified count columns through Core's
  `BarrierPresentation`; `windowRate_eq_barrier` identifies the registered
  rate with the aggregate floor computed from that table.  The presentation
  also carries closed proofs that the flat product is positive and that the
  safe product dominates it, so Core derives
  `2 ^ windowRate * flatProduct ≤ safeProduct` without an application-owned
  numeric premise.  `data.windowOrder` remains the registered path order.
  Node `[22]` remains the separate `barrierEnumerationDichotomy`, branching on
  the decidable comparison

  ```
  if overflow : Graph.skeletonBudget current.object <
      2 ^ (data.windowRate * Graph.dyadicScaleCount current.object *
        hot.card)
  ```

  Node `[22]` first reads the selected maximal packing from the literal ledger,
  defines `hot` by filtering for the singleton `WindowTargetPackage` at the
  selected-scale rate and `cold` by the complementary filter, and proves the
  two membership equivalences, disjointness, and exhaustive partition.  It
  commits that same partition with `barrierOverflow` on the strict side and
  with `barrierCap` on the other.  Every symbol is an
  observable of the literal active residual object — `skeletonBudget`,
  `dyadicScaleCount`, `windowPackingNumber` — or a registered `Data` field;
  no numeral appears in the row, and `399`/`543958`/`432672`/`111286` occur
  nowhere in it.
- **What it should do.** Publish the finite `c_Ω`/`c₁₃` computation as
  one ordinary fact, then pass that exact ledger to node `[22]`. The later
  independent multi-scale package must be proved only after its stated
  sparse-exit and near-cubic hypotheses are present.
- **Gap.** Node `[21]` itself has no mathematical or residual gap. Existing
  downstream code still consumes the legacy key as `WindowPackageStatement`;
  those consumers now fail to elaborate and must be rewired to a distinct
  later package fact. In particular, the old direct path into node `[22]` must
  first run `finiteBarrierEnumeration` on its literal predecessor.

  Node `[22]`'s live demand exponent is
  `windowRate · dyadicScaleCount object · hot.card`, which is the
  manuscript's `c₁₃ |P_hot| log₂ n`: `windowRate` is a per-window cost *per dyadic
  scale*, so the scale factor is required for the statement to be the paper's.
  It was missing until this change and is now present in all three clauses;
  see the **Fixed and verified** paragraph in Row 10's **Gap** for the
  correction and its verification.

  The cap arm carries `lem:variable-edge-budget` / `rem:budget-robustness`, but
  proves none of it: `stable` is a one-line call to
  `Graph.skeletonBudget_le_variableEdgeBudget`.  **Corrected in this change.**
  The row previously re-derived that bound inline as a four-step tactic block
  (`Finset.le_sup` for the stratum, `Finset.card_pos` for the family, then
  `Nat.le_mul_of_pos_left`), which put reusable graph combinatorics inside a
  Strategy and relied on an unstated definitional identification of
  `skeletonBudget object` with `edgeStratumCount n m`.  Both halves now live in
  the framework modules that own them: `Graph.edgeStratumCount_le_variableEdgeBudget`
  (`Graph/FiniteEdgeBudget.lean`, the pointwise companion to the summed
  `sum_edgeStratumCount_le_variableEdgeBudget`), and
  `Graph.skeletonBudget_eq_edgeStratumCount` plus
  `Graph.skeletonBudget_le_variableEdgeBudget` (`Graph/SkeletonBudget.lean`,
  which now imports `FiniteEdgeBudget` so the identification is *stated* rather
  than left to unfolding).  This also removed the elaboration cost that was
  breaking the spine assembly; see the correction in **Build status**.  **Correction to a previous
  revision:** `Graph/FiniteEdgeBudget.lean` is no longer an unimported island.
  It is imported by `Graph/Strategy/SpineVocabulary.lean:7` and by
  `Hypostructure.lean:67`, and `Graph.edgeStratumCount` /
  `Graph.variableEdgeBudget` are consumed by this row's cap arm and by the
  `.barrierCap` clause itself.  `lem:variable-edge-budget` and
  `rem:budget-robustness` are therefore **consumed**, not stated-and-unreachable
  as this document previously recorded.  The summed form
  `sum_edgeStratumCount_le_variableEdgeBudget` is not a row obligation here:
  the row proves the pointwise bound it needs directly, and no call site uses
  the sum.
- **Ledger and residual.** `barrierEnumerationRow` uses `factOnly` and
  `AtomicCT.run`; its output index is exactly
  `windowPackageSeparated :: known`, and `inputs.current` is unchanged.
  Node `[22]` then uses `Decision.run` against that literal output, so the
  sibling key is absent from the selected
  branch's type-level index entirely — `barrierOverflowKeys` and the cap-side
  index are disjoint at `.barrierCap`/`.barrierOverflow`.  The row reads
  `current.object` and publishes through the framework runner; it appends no
  residual change (`Refines` is the identity here, a fact-only step) and drops
  nothing, so every earlier key remains indexed. The node reads
  `maximalPacking` through `ExactLedger.get`; its demand and budget remain
  observables of the active object.
- **Transport and terminals.**  No EG-specific carrier, executor, or routing.
  The arms are `Decision`'s own two branches, taken at
  the spine assembly. The overflow arm leaves Block A as
  the exact ledger indexed by `barrierOverflowKeys`; the cap arm continues into
  node `[22]`–`[24]`. Neither arm is a paper terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:curv-enum` | lem | `FiniteChecks.P13Barrier` (audited table)<br>`Graph.Strategy.Spine.Data.windowRate` | finite table, projected through the registered `Data`; the three integer counts are the table's, not a row theorem |
| `lem:p13-window-package` | lem | `Graph.Strategy.Spine.Holds .barrierCap`<br>`Graph.Strategy.Spine.barrierEnumerationDichotomy`<br>`Graph.dyadicScaleCount` | the demand `2 ^ (rate · scaleCount · p)` stated and decided at this row |
| `lem:skeleton-dominates` | lem | `Graph.skeletonBudget`<br>`Graph.PackedWindowRealization.card_skeleton` | the closed-form binomial the demand is compared against |
| `lem:variable-edge-budget` | lem | `Graph.edgeStratumCount`<br>`Graph.variableEdgeBudget` | consumed — proved inline on the cap arm (`stable`) and carried in the `.barrierCap` clause |
| `rem:budget-robustness` | rem | `Graph.variableEdgeBudget` | consumed — the cap arm's family-quantified conjunct is exactly this robustness statement |
| `lem:near-cubic-budget` | lem | `Core.FiniteEntropy.choose_le_exp_bound`<br>`Core.FiniteEntropy.pow_self_le_three_pow_mul_factorial`<br>`Graph.exponent_le_dyadicScaleCount_succ_mul_edgeCount` | exact framework form, consumed at Row 10 |
| `rem:near-cubic-budget-scope` | rem | `Graph.two_mul_edgeCount_le_of_degreeSurplus_le`<br>`Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount` | consumed at Row 10 |

The Lean uses exact finite inequalities in place of the paper's logarithmic
asymptotics, so no asymptotic estimate enters as executable data, and the
statement is uniform in the object's order, edge count, baseline, and surplus
threshold.

**CT composition at this row.**  None.  This row is a bare `Decision` over the
canonical `ExactLedger`; the CT16 execution this document previously described
belonged to the deleted `Core.Strategy.FiniteBarrierEnumeration` module.  The
finite enumeration that CT16 used to perform at run time is now the
precomputed audited `P13Barrier` table, so there is no work budget, no closed-code
computation, and no `properSupport`/`mismatch` terminal to discharge.

**Validation.**  `lake build Hypostructure.Graph.Strategy.SpineRows` succeeds.
With the scale-factor correction as the only delta against `1e39f3a`,
`lake build Hypostructure.Graph.Strategy.SpineAssembly` also succeeds,
together with the canonical API modules and all fifteen positive/negative
enforcement fixtures (8573 jobs).  The earlier `Validation` paragraph here
described a parse error in `Core/Strategy/Dag.lean` and an unsolved goal in
`PDE/.../PackingNormalization.lean`; both modules are gone from this row's
slice and that paragraph is retired.  See **Build status** for the one
currently-failing target, which is rows 41–42's in-flight port and does not
touch this row.

### Row 10 — Finite window-density budget `[22]`–`[24]`

- **Paper fact.** Node `[22]` decides "`P₁₃` packing density too large?"; its
  yes-arm is the terminal `[23]` "`P₁₃` window entropy overflow"; its no-arm is
  `[24]`, `θ ≤ θ_win + o(1)` with
  `θ_win := 1.5/118.108581006 = 0.01270017798…`, and in the high-entropy branch
  of `prop:two-budget` the sharper `θ ≤ 0.01198542083… + o(1)`.
  `prop:p13-density` proves both by comparing
  `(118.108581006 - o(1)) p₁₃ log₂ n ≤ (3/2) n log₂ n + o(n log n)` and, in the
  high-entropy branch, `((1-13θ)/10) + 118.108581006 θ ≤ 1.5 + o(1)`
  (`eq:feasibility`), and concludes `|R| ≥ 0.83489768623… n - o(n)` and
  `15θ/(1-13θ) ≤ τ_win = 0.22817486846… < 1/4`.
  `lem:skeleton-dominates` supplies the ambient count
  `|𝒢_{n,m}| = C(C(n,2), m)` and `lem:state-count-comparison` the comparison
  step `|S| ≤ |G|`, equivalently `K ≤ log₂|G|`.
- **What the Lean does.**  The node is `Graph.Strategy.Spine.densityBudgetRow`
  (`Graph/Strategy/SpineRows.lean`), a `factOnly` `AtomicStrategy` over the
  canonical ledger — not a CT.  The retired
  `Core.Strategy.FiniteDensityBudget` and `Graph/Strategy/FiniteDensityBudget.lean`
  modules, with their `Profile`, `CT14.Spec`, `CapLedger`, `CapResidual`,
  `OverflowResidual` and `labelledSkeletonRegistration`, are **deleted**.
  Its manifest is

  ```
  Requires := [barrierCap, surplusAtOrBelow]
  Produces := [densityCap]
  ```

  instantiated in `Graph/Strategy/SpineAssembly.lean` as
  `densityBudgetRow (K .barrierCap) (K .surplusAtOrBelow) (K .densityCap)`.
  The executor reads both prerequisites by semantic key through
  `FactInputs.get` — never by producer, position, or depth — takes the
  minimum-degree handshake `δ n ≤ 2m` from the standing baseline via
  `Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount`, and applies

  ```
  Graph.two_mul_exponent_le_scale_mul_edgeBudget object
    (data.windowRate * Graph.dyadicScaleCount object *
      object.windowPackingNumber data.windowOrder)
    data.threshold (data.surplusThreshold object.vertexCount)
  ```

  to conclude
  `2·(rate · scaleCount · p) ≤ (scaleCount + 1)·(δ n + T(n))`, which it commits
  as `densityCap`.  The conversion theorem is generic: it quantifies over an
  arbitrary `exponent` and contains no EG name, label, or constant.
- **What it should do.**  Convert node `[21]`'s retained demand and node
  `[19]`'s at-or-below surplus fact into `[24]`'s cap
  `θ ≤ θ_win + o(1)` with `θ_win = 1.5/118.108581006…`, on the surviving arm,
  with the right-hand side the count of the labelled skeleton class the demand
  is realized in.
- **Gap.**  None on the row's own statement.  The right-hand side is
  `Graph.skeletonBudget object`, the closed-form binomial `C(C(n,2), m)`, which
  `Graph.PackedWindowRealization.card_skeleton` identifies with
  `Nat.card (Skeleton n m)` by `rfl` — `lem:skeleton-dominates` applied
  directly to a closed count, so no separate realization map is needed and
  `demand_le_skeletonBudget`'s injective-`realize` route is legitimately
  unconsumed for this presentation.  `nearCubic` is not a free hypothesis a
  caller must rediscover: it is the node-`[19]` `surplusAtOrBelow` fact, read
  from the ledger by declared requirement.

  **Fixed and verified — the dyadic scale factor.**  Until this change the
  committed cap was weaker than `prop:p13-density` by a whole `⌊log₂ n⌋ + 1`
  factor.  `data.windowRate` is `FiniteChecks.P13Barrier.windowRate`, which
  evaluates to `118` and is the manuscript's `c₁₃ = 118.108581006…` — a
  per-window cost *per dyadic scale*.  `lem:p13-window-package`'s demand is
  therefore `118·(log₂ n)·p₁₃` bits, i.e. `2 ^ (rate · scaleCount · p)` states,
  but node `[21]` stated `2 ^ (rate · p)` and this node converted that weaker
  demand.  The resulting cap was `θ ≲ 1.5·log₂ n / 118`, which bounds nothing
  as `n` grows, and it is what blocked `[56]`'s `τ_win < 1/4` and `[60]`'s
  terminal.

  The factor is now restored in all three clauses of
  `Graph/Strategy/SpineVocabulary.lean`: `.barrierCap` reads
  `2 ^ (windowRate · dyadicScaleCount object · windowPackingNumber) ≤
  skeletonBudget object`, `.barrierOverflow` its strict negation on the same
  demand, and `.densityCap`
  `2·(windowRate · dyadicScaleCount object · windowPackingNumber) ≤
  (dyadicScaleCount object + 1)·(δn + T(n))`.  Both row signatures were widened
  to match — `barrierEnumerationDichotomy`'s `encodeCap`/`encodeOverflow` and
  the decidable comparison it branches on, and this row's `capOf`/`encode` and
  the `exponent` it passes to the conversion theorem.  No new hypothesis,
  registration field, or callback was introduced: `Graph.dyadicScaleCount
  object` is an observable of the residual object, and
  `two_mul_exponent_le_scale_mul_edgeBudget` was already stated for an
  arbitrary `exponent`, so it absorbed the stronger demand unchanged.
  Dividing through, `densityCap` is now
  `θ = p/n ≤ (δ/2)(1 + 1/log₂ n)/rate + O(T/n) → 1.5/118.108581006… = θ_win`:
  the manuscript's cap, in exact `Nat` form, with the paper's `o(1)` realized
  exactly as the `(scaleCount + 1)/scaleCount` factor and the `T(n)` term.
  **Facts passes at rows 9 and 10.**

  Verified by elaboration: with this change as the only delta against
  `1e39f3a`, `lake build Hypostructure.Graph.Strategy.SpineAssembly` succeeds,
  as do the canonical API modules and all fifteen
  positive/negative enforcement fixtures (8573 jobs).  The misleading
  `2 ^ (rate · p)` / `2 · rate · p` docstrings on both rows were rewritten to
  the scaled statement in the same change.

  **Still outside the tree, by convention.**  Neither `θ_win = 0.01270017798…`
  nor the high-entropy `0.01198542083…` nor `τ_win` nor the `|R|` bound occurs
  as a decimal anywhere in the Lean.  This is the framework's standing
  convention — exact `Nat` inequalities and residual-derived tables instead of
  asymptotic numerals — and is uniform across every row's numeric caps, not a
  gap specific to this node.  The high-entropy branch of `prop:two-budget`
  remains unstated at this row: it needs a second summand
  `((n - 13 p₁₃)/10)·log₂ n` added to the window exponent and compared against
  the *same* skeleton budget, whose own entropy witness
  (`lem:independent-target-entropy` on the window/remainder joint family) is
  `prop:two-budget`'s data and is not defined until after the packing.  It is
  correctly a later row's obligation, not this one's.
- **Ledger and residual.**  The row is `factOnly`: it consumes the literal
  active predecessor passed to it, changes no residual (the `Refines` obligation
  is the identity), and appends exactly `[densityCap]` through the
  framework-owned runner, so `Produces ++ known` retains every earlier key and
  nothing is archived or rebased.  Both prerequisites are fetched by
  `FactInputs.get` on exact keys; `distinctRequired` discharges
  `requiresUnique` on `barrierCap ≠ surplusAtOrBelow`.  `barrierCap` is on this
  branch's prefix because the row runs only on node `[21]`'s cap arm, and
  `surplusAtOrBelow` because it runs only on node `[19]`'s at-or-below arm —
  both are type-level facts of the index, not runtime checks.
- **Transport and terminals.**  No EG-specific carrier, executor, residual,
  or routing; execution is the framework runner and the only application input
  is the registered `Spine.Data`.  The row has no terminal: it is a fact-only
  step, entered from node `[21]`'s cap arm and continuing into node `[25]`–`[27]`
  (`remainderNormalization`).  The paper's terminal `[23]` is reached on the
  *other* side of node `[21]`'s decision, at `barrierOverflowKeys`, and is Row
  9's arm rather than this row's.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `prop:p13-density` | pro | `Graph.two_mul_exponent_le_scale_mul_edgeBudget`<br>`Graph.exponent_le_dyadicScaleCount_succ_mul_edgeCount`<br>`Graph.Strategy.Spine.Holds .densityCap` | exact `Nat` conclusion, committed as `densityCap` |
| `lem:skeleton-dominates` | lem | `Graph.skeletonBudget`<br>`Graph.PackedWindowRealization.Skeleton`<br>`Graph.PackedWindowRealization.card_skeleton` | consumed as the closed-form count; `card_skeleton` identifies it with `Nat.card (Skeleton n m)` by `rfl` |
| `def:near-cubic-spine` | def | `Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount`<br>`Graph.two_mul_edgeCount_le_of_degreeSurplus_le` | the handshake half from the standing baseline, the surplus half from the `surplusAtOrBelow` ledger fact |
| `lem:state-count-comparison` | lem | `Graph.LabelledOn.card_realized_le`<br>`Graph.PackedWindowRealization.demand_le_skeletonBudget` | unconsumed — needed only if the budget were registered through an explicit realization instead of the closed-form binomial |
| `prop:two-budget` (high-entropy branch) | pro | | not stated at this row; see **Gap** |
| `eq:feasibility` | eq | | not stated at this row; see **Gap** |

**CT composition at this row.**  None.  This row is a `factOnly`
`AtomicStrategy` over the canonical `ExactLedger`; the CT14 comparison this
document previously described belonged to the deleted
`Core.Strategy.FiniteDensityBudget` module.  Because the demand/budget
comparison is now decided once at node `[21]` (Row 9's `Decision`), this node
performs no enumeration, aggregation, or capacity routing — it converts one
retained inequality into another and commits it, which is exactly one fact and
needs no CT machinery.

### Row 11 — Saturated receiver `[89]` (ported: `Spine.typeAReceiverRouting`, `Spine.typeASaturationDichotomy`)

- **Paper fact.** Node `[89]` asks "some receiver has `L(w) ≥ 4q(w)`?".
  `def:typeA-support` fixes `X` as a connected admissible support with
  `σ(X) = 0`; since `G` has minimum degree at least `3`, that gives
  `d_G(v) = 3` for every `v ∈ V(X)`, so `X` is subcubic and its deficient
  vertices are exactly those of internal degree at most `2`.
  `def:typeA-receiver-load` fixes the objects: a *receiver* is `w ∈ V(X)` with
  `d_X(w) ≤ 2` and `q(w) = 3 − d_X(w)`, which — because every vertex has
  ambient degree exactly `3` — is also the number of ambient edges from `w` to
  `G − X`; for a cubic `u`, `T_u` is the lexicographically first path in `X`
  that starts at `u`, stays in `X₃` until its last edge, and ends at a
  receiver, `r(u)` is that terminal receiver, and
  `L(w) = |{u ∈ V(X) : d_X(u) = 3, r(u) = w}|`.  A receiver is *saturated*
  when `L(w) ≥ 4q(w)` and *unsaturated* when `L(w) ≤ 4q(w) − 1`.
  `lem:typeA-receiver-loads` proves `r(u)` is defined and unique for every
  degree-`3` vertex: the empty internal `3`-core condition means no component of
  `X₃` is closed under all three incident edges of its vertices, so each
  component has an edge to a receiver, and the fixed tie-breaking rule then
  makes `r(u)` a function.  `lem:typeA-threshold-algebra` computes the raw
  thresholds: `ch(w) = q(w) − ¼`, each routed load costs `¼`, so the largest
  load with nonnegative final charge is `L ≤ 4q(w) − 1` and the first value
  that leaves the branch is `H_j = 4q(w) = 4(j+1)`, hence `H₀ ≤ 4`, `H₁ ≤ 8`,
  `H₂ ≤ 12`; after the saturated branch is eliminated every receiver in
  `𝓡_j(X)` satisfies `L(w) ≤ H_j − 1`.  The yes arm is node `[93]`, the no arm
  is node `[90]` and its `3/7/11` discharging at `[91]`.
- **What the Lean does.**  Two rows of `Spine.run`, on the Type A residual of
  node `[63]`.

  `SpineRows.typeAReceiverRoutingRow` is node `[88]`.  It requires
  `remainderNormalized` and produces `typeAReceiverRouting`, whose statement is,
  at every maximal packing and every subregion `X` of its remainder with
  `ambientSurplus X δ = 0`: (i) every `u ∈ X` with `internalDegree X u = δ` has
  `traceReceiver? X δ u = some w` for a `w` with `IsReceiver X δ w`, and (ii)
  every receiver `w` satisfies `s·q(w) = s·(δ − 1 − d_X(w) + 1)` and
  `s·q(w) ≤ s·δ`.  Clause (i) is `lem:typeA-receiver-loads` and clause (ii) is
  `lem:typeA-threshold-algebra`.

  `SpineRows.typeASaturationDichotomy` is node `[89]`.  It is a `Decision` on
  the cursor node `[88]` leaves, reading `typeALowSurplus` through
  `ExactLedger.get`, and produces exactly one of
  `typeASaturatedReceiver` — `∃` a maximal packing and a connected,
  negative-net-charge, zero-surplus piece `X` of its remainder, and a receiver
  `w` of `X` with `Saturated X δ s w` — or `typeAUnsaturatedReceivers` —
  `∀` such packing, piece and receiver, `1 + L(w) ≤ s·q(w)`.  The second is
  `L(w) ≤ 4q(w) − 1` written without subtraction, i.e. node `[90]`.

  The mathematics is `Graph.FiniteObject`'s new receiver-routing API
  (`Hypostructure/Graph/ReceiverRouting.lean`), which is parametric in the
  object, the support, the baseline `threshold` and the scale:
  `IsReceiver`, `missingPorts` (`q(w)`), `TraceTo` (a path in the support that
  stays at full internal degree until its last edge and ends at a receiver),
  `traceReceiver?` (*the* routing — the first receiver the source traces to in
  the object's own `orderedVertices` schedule, returned as an `Option`, so an
  unrouted source is not silently routed anywhere), `routedLoad` (`L(w)`, the
  fibre of that routing over `w` among the full vertices of `X`) and
  `Saturated` (`s·q(w) ≤ L(w)`).  `exists_traceTo_of_no_baseline_subsupport` is
  `lem:typeA-receiver-loads`: if no subregion of the support meets the baseline
  and no internal degree exceeds it, every full vertex traces to a receiver.
  Its proof is the manuscript's — the region a full vertex reaches through full
  vertices would otherwise keep the whole baseline inside itself, and
  `degree_induce_eq_internalDegree` (new, in `Graph/BoundaryDemand.lean`) turns
  that pointwise bound into `MinimumDegreeAtLeast` on the induced object.
  `not_saturated_iff`, `saturationThreshold_eq` and `saturationThreshold_le`
  are `lem:typeA-threshold-algebra`.
- **What it should do.** Exactly this.  Both nodes of the row are implemented
  and both arms of `[89]` are committed.
- **Gap.** None on the mathematics of `[88]` and `[89]`.  Three notes, none of
  them a gap in this row.

  (a) The empty internal `δ`-core hypothesis of `lem:typeA-receiver-loads` is
  *inherited*, not assumed: node `[27]` (`remainderNormalized`) proves that no
  subregion of the remainder of a **maximal** packing meets the baseline.
  The Type A fact chain therefore carries maximality through
  `netChargeNegative`, `netChargeNonNegative`, `windowJoinPressure`,
  `negativeSupport` and `typeALowSurplus`; a bare `IsWindowPacking` would not
  suffice, because a regular object with the empty packing can have a nonempty
  internal core.

  (b) `traceReceiver?` realizes the manuscript's "fixed lexicographic
  tie-breaking rule among these receiver-reaching paths" as *the first receiver
  in the object's own vertex schedule that the source traces to*.  Everything
  `[88]` and `[89]` state is independent of which fixed rule is used —
  `lem:typeA-receiver-loads`' own proof only asks that one exists — but
  `def:typeA-visible-load` at node `[93]` speaks of the trace `T_u` itself, so
  row 12 needs the canonical *path*, not only its endpoint.  Recorded in row
  12's Gap.

  (c) Node `[89]`'s yes arm does not consume `typeAReceiverRouting`: the
  decision is an excluded middle on a statement about the object, exactly as
  the manuscript's diamond is.  The routing fact is committed on both arms and
  is what makes `L(w)` a complete assignment; it is read by node `[90]`'s
  discharging and by the exits of rows 12–19, none of which are ported.
  **Facts therefore holds.**
- **Ledger and residual.** Two steps on the one canonical
  `Core.Residual.ExactLedger`, at the residual `Spine.run` was opened on.
  Node `[88]` is `factOnly`/`AtomicCT.run`, so its output index is
  definitionally `typeAReceiverRouting :: typeALowSurplusKeys` and every
  earlier fact stays in the type; node `[89]` is `Decision.run`, so the arm not
  taken is absent from the taken branch's index — `typeASaturatedReceiverKeys`
  and `typeAUnsaturatedReceiverKeys` differ in exactly one entry and neither
  contains the other's, which `Fixtures/TypeAReceiverNode.lean` checks.  The
  residual is unchanged: both steps are fact-only and their `refines` is
  equality.  Node `[88]` reads `remainderNormalized` by exact semantic key
  through `FactInputs.get` and the standing baseline off the residual
  (`inputs.current.baseline`), never from a fact; node `[89]` reads
  `typeALowSurplus` through `ExactLedger.get` at the decision boundary.  No
  support, packing, receiver or routing travels: every clause is quantified
  over the object the residual carries, which is what makes the facts
  refinement-stable.  `typeAUnsaturatedReceivers_audit_facts` in `SpineAssembly`
  pins the unsaturated exit's audit to its exact thirty facts in commit order,
  and both exits carry `audit_complete` and `audit_facts_unique`.
- **Transport and terminals.** No EG-specific carrier, result, residual,
  ledger, executor or routing helper exists at this row: the rows are
  `AtomicStrategy` and `Decision` values in `Hypostructure.Graph.Strategy`,
  quantified over the keys they commit, and the mathematics is in
  `Hypostructure.Graph`, parametric in the baseline and the scale.  Neither arm
  of `[89]` is a terminal — the saturated arm is node `[93]`'s entry (row 12)
  and the unsaturated arm is node `[90]`'s (unported) — so both are exact branch
  ledgers indexed by the committed saturation key.  The previous Type A
  low-surplus leaf is deleted; there is no second path to the Type A residual.

  The legacy apparatus this row replaces is deleted rather than shimmed.
  `Graph/ReceiverLoad.lean` kept a `Support`/`FullVertex`/`ReceiverVertex`
  geometry, a `RoutedLoad` whose only field was an **arbitrary** function
  `FullVertex → ReceiverVertex`, a `CanonicalRouting` whose canonicality was an
  opaque `canonical : Prop` discarded by `toRoutedLoad`, `CompletionPort`,
  `AnchoredReturn`, `ReceiverEntryChannel`, `ReceiverEntryReturn`, and the
  load/saturation algebra on top of them.  Every one of its dependents is
  quarantined, so all of it was dead in the live build; it is removed.  What
  remains in that module is only the registered presentation record
  `LoadCapacityProfile`, reduced to the three parameters the live build reads
  (`baselineDegree`, `loadMultiplier`, `remainderEntropyThresholdDenominator`).
  Its two rational side conditions `dischargeRate_gt` and `dischargeRate_le`
  are also removed: they were framework-side constraints written in Type B fan
  constants (`5`, `9`, `3`) with manuscript labels in their docstrings, and no
  live declaration consumed them.  Rows 26–29 are now ported, and the constraints
  the fan ledger actually needs were registered where they are consumed: they are
  `Data.fanCapSlack`, `Data.highCentreDeficitSlack` and `Data.bridgeMassSlack`,
  each a comparison between already-registered numbers rather than a rational
  side condition.  `Problem.lean` drops the two discharged fields with them.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeA-support` | def | `Spine.Key.typeALowSurplus`'s schema (connected, negative net charge, `σ(X) = 0` piece of the remainder of a maximal packing)<br>`Graph.FiniteObject.internalDegree` | no CT |
| `def:typeA-receiver-load` | def | `Graph.FiniteObject.IsReceiver`<br>`Graph.FiniteObject.missingPorts`<br>`Graph.FiniteObject.IsFullDegree`<br>`Graph.FiniteObject.TraceTo`<br>`Graph.FiniteObject.traceReceiver?`<br>`Graph.FiniteObject.routedLoad`<br>`Graph.FiniteObject.Saturated` | no CT |
| `lem:typeA-receiver-loads` | lem | `Graph.FiniteObject.exists_traceTo_of_no_baseline_subsupport`<br>`Graph.FiniteObject.isSome_traceReceiver?_of_traceTo`<br>`Graph.FiniteObject.traceTo_of_traceReceiver?_eq_some`<br>`Graph.FiniteObject.isReceiver_of_traceTo` | no CT |
| `def:internal-3-core` | def | `Spine.Key.remainderNormalized`'s second clause, read at every subregion | no CT |
| `lem:typeA-threshold-algebra` | lem | `Graph.FiniteObject.saturationThreshold_eq`<br>`Graph.FiniteObject.saturationThreshold_le`<br>`Graph.FiniteObject.not_saturated_iff` | no CT |
| `lem:typeA-saturated-handoff` | lem | | the loop over exits 1–8; rows 12–19 and 62–67 |

**CT composition at this row.**  No CT.  Node `[88]` is
`Core.Strategy.factOnly` run by `AtomicCT.run`; node `[89]` is
`Core.Strategy.Decision.run`.  Neither arm closes, so no closure runner is
involved.  The finite enumeration a CT would add is not wanted here: the
routing is a definition of the framework, not a search result, and the
threshold algebra is an exact integer identity.


**Immediate continuation repair.**  The no arm at `[90]` no longer survives as
an inert continuation.  `Spine.typeAUnsaturatedDischarge` reads exactly
`typeAReceiverRouting` and `typeAUnsaturatedReceivers`, applies
`FiniteObject.unsaturatedDischarge`, and appends
`typeAUnsaturatedDischarge`.  Core then appends `closed` from that fact and the
retained `typeALowSurplus` negative support.  No support, route, or receiver is
carried outside the canonical ledger.

### Row 12 — Visible receiver-entry returns `[93]`

- **Paper fact.** Node `[93]` is a dichotomy on the already selected Type A
  support `X`: either some saturated receiver of `X` has a completion port
  carrying `s` visible receiver-entry returns, or no saturated receiver of `X`
  has such a port.  The yes arm enters `lem:typeA-visible-entry` and exits
  `(1)`--`(7)`.  The no arm is `lem:typeA-silent-excess-count`, whose
  subtraction-free form is
  `|X| ≤ Σ_w |silentExcess(X,w)| + s * def⁺(X)`.
- **What the Lean does.** `Spine.typeAVisibleEntryDichotomy` reads the exact
  canonical `(packing, component, X)` selected at nodes `[61]`, `[62]`, and
  `[89]`.  It decides only whether a saturated receiver of that `X` satisfies
  `ExitFour.VisibleFourUnpeeledAt X threshold scale receiver ∅`.  The yes arm
  constructs one actual `ExitFour.VisibleFourUnpeeledPackage` and commits it
  with the same packing, component, receiver, negative-net-charge proof, and
  zero-surplus proof.  It does not search for another support.

  On the no arm, the rejected existential is instantiated at every saturated
  receiver of the same `X`.  The row reads `typeAReceiverRouting` by exact key
  and applies
  `VisibleEntry.card_le_sum_silentExcess_add_positiveDeficiency`, proving the
  support-wide bound.  It also retains node `[89]`'s saturated receiver and
  derives `ExitFour.SilentUnpeeledExcessAt ... ∅` from
  `visibleFourUnpeeled_or_silentUnpeeledExcess`.  Thus `[94]` carries both the
  global count and the concrete same-support silent state needed by the later
  saturated-load routing.

  `Spine.typeAVisibleEntryClauseRow` reads the exact yes-arm package and commits
  only graph facts already proved by the compiled prefix: canonical response
  coordinate ownership for each selected load; the piece-channel and context
  connector length identities; completeness of the selected-germ and germ-pair
  schedules; and the first-separator `SeparatesAt` and list-head identities.
  The row does not assert Q1 semantic classification and does not construct a
  `DecoratedHandoff.Separation`.

  On the no arm, `Spine.typeASaturatedHandoffSilentFromFirstExcessRow` reads the
  committed `typeAVisibleFirstExcess` fact with `FactInputs.get` and appends the
  ordinary ledger fact `typeASaturatedHandoffSilent` for the same selected
  support, receiver, and empty peeling set.  The row produces no carrier and
  uses the saturated-after-empty theorem only inside the declared fact.
- **What it should do.** This is the maximal paper-valid prefix currently
  available.  The support-local receiver quantifier matches
  `lem:typeA-visible-entry`, and its universal negation matches the hypothesis
  of `lem:typeA-silent-excess-count`.  The exact selected residual is preserved
  on both arms.
- **Gap.** The shared realization theorem that evaluates the selected declared
  response coordinates in the registered boundary context is still missing.
  Therefore the compiled package/germ facts do not yet prove clause (Q1) of
  `def:typeA-exit4-family`, and a surviving first separator is not yet an actual
  exit-(7) `Separation`.  These are downstream implementation bugs; this row no
  longer claims them.  **Facts does not pass yet.**
- **Ledger and residual.** One canonical `ExactLedger` is used throughout.
  The dichotomy reads `typeAReceiverRouting` and `typeASaturatedReceiver` with
  `ExactLedger.get`; the package prefix reads `typeAVisibleEntry` through
  `FactInputs.get`; the no-arm silent-handoff row reads
  `typeAVisibleFirstExcess` through `FactInputs.get`.  Every output prepends one
  semantic key to the literal incoming `known`.
  `Fixtures/TypeAVisiblePackageLedger.lean` checks the
  manifest, freshness, retained incoming key, complete audit, and nonempty
  commits without importing `SpineAssembly`.
  `Fixtures/TypeASelectedResidualWiring.lean` additionally instantiates the
  exact `[62]`, `[89]`, `[93]/[94]`, unsaturated-discharge, and exit-(1)--(3)
  interfaces without any continuation wrapper.
- **Transport and terminals.** The split is Core `Decision`; the compiled
  package prefix and the no-arm silent-handoff publication are `factOnly`.
  No custom result carrier, history wrapper, native decision, table computation,
  or reconstructed residual appears.  The yes arm continues to node `[95]`; the
  no arm now carries the committed silent fact required by the paper's silent
  routing, while the downstream route-8/exit-free continuation remains to be
  composed.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeA-visible-load` | def | `Graph.VisibleEntry.ReceiverEntryReturn`<br>`Graph.VisibleEntry.VisibleFor`<br>`Graph.VisibleEntry.visibleLoadsAt` | standalone Graph |
| `lem:typeA-port-return` | lem | `Graph.VisibleEntry.exists_anchoredReturn_of_mem_completionPorts`<br>`Spine.typeAPortReturn` | fact-only row |
| `[93]` support-local split | decision | `Spine.typeAVisibleEntryDichotomy` | Core `Decision` |
| `[94]` silent selected state | row | `Spine.typeASaturatedHandoffSilentFromFirstExcessRow` | fact-only row |
| canonical four-return package | def/lem | `Graph.ExitFour.VisibleFourUnpeeledPackage`<br>`Graph.ExitFour.visibleFourUnpeeledPackage` | standalone Graph |
| `lem:typeA-silent-excess-count` | lem | `Graph.VisibleEntry.card_le_sum_silentExcess_add_positiveDeficiency` | standalone Graph |
| selected silent state | lem | `Graph.ExitFour.visibleFourUnpeeled_or_silentUnpeeledExcess` | standalone Graph |
| compiled response/germ prefix | lem | `Spine.typeAVisibleEntryClauseRow`<br>`Graph.ExitFour.VisibleFourUnpeeledPackage.germSchedule`<br>`Graph.ExitFour.VisibleFourUnpeeledPackage.germPairSchedule` | fact-only row |
| Q1 semantic realization | missing | no registered realization theorem yet | open bug |
| separator-to-exit-7 production | missing | no actual `Separation` constructor from this prefix yet | open bug |

**CT composition at this row.** The only framework recipes are one
support-local `Decision` and fact-only semantic publication.  The finite path,
return, response-coordinate, germ, and germ-pair schedules are graph-derived;
no row enumerates an independent table or authors a coordinate reading.

### Row 13 — Exit 1: Mersenne return `[95]`

- **Paper fact.** Exit (1) of `def:typeA-saturated-exits`: *"an anchored return
  through a completion port of `w` has length in `Mers`"*.  The proof of
  `lem:typeA-visible-entry` asks it of the port node `[93]` fixed — *"Fix a port
  `\vec e=(w,h)` carrying four visible receiver-entry returns […] If one return
  has length in `Mers`, `lem:return-equivalence` gives a power-of-two cycle; this
  is exit (1)"* — and `lem:return-equivalence` is the closure: *"if
  `2^j−1 ∈ R_e(G)`, then `e` together with the corresponding simple return path
  gives a simple cycle of length `2^j`"*.  `lem:typeA-exits-discharged` records
  the disposition: *"Exit (1) gives an edge-rooted Mersenne return, hence a
  power-of-two cycle by `lem:return-equivalence`"*, so exit (1) is one of the
  closed exits and cannot remain as a negative-charge Type A discharging case.
- **What the Lean does.**  `Spine.typeAExitOneDichotomy` (`SpineRows.lean`) is a
  `Core.Strategy.Decision` on the canonical `ExactLedger`.  It requires node
  `[93]`'s key by `FactKeys.Has typeAVisibleEntry known` and reads it with
  `ExactLedger.get`, so the question elaborates only on the branch that entered
  the saturated exit chain.  It destructures the exact
  `(packing, component, piece, receiver, package)` committed at `[93]` and
  decides whether an `AnchoredReturn` through `package.outside` has accepted
  shifted length.  Both keys retain that same tuple and package; the no arm is
  the literal universal denial only for that fixed port.  `Spine.runExitOne`
  (`TypeAExitRun.lean`) runs the
  decision and closes the yes arm with Core's `closeIncompatible` against
  `Key.returnAvoidance`; the `Incompatible` instance's whole content is
  `Graph.VisibleEntry.not_shiftedCycleLength_of_returnLengthSets_disjoint`.
  `Spine.runExitChain` composes that runner with nodes `[97]` and `[99]`, so the
  exit list is walked in the manuscript's order on one immutable prefix; rows 14
  and 15 call this row's runner rather than repeating its decision.
- **What it should do.**  This is what it does.  The alternative is asked of the
  port fixed by `lem:typeA-visible-entry`, and the
  conversion to the target goes through
  `Graph.VisibleEntry.AnchoredReturn.toEdgeRootedReturn` at the dart `(w,h)`.
- **Gap.**  None.  The alternative no longer implies the registered target
  outright: it is a statement about a named port of a named saturated receiver of
  a Type A support, and the *closure* — not the alternative — is where
  `lem:return-equivalence` turns it into the cycle the residual denies.  The
  legacy `exitOneSplit`, whose `Nonempty (RootedReturn (object input))` was
  literally the target predicate node `[6]` reduced, is gone with the rest of the
  `Blueprint` topology.  The only other Lean that ever enumerated the saturated
  exits — `Graph.ReceiverExhaustion.Exit`, with its six constructors merging
  exits (3), (5) and (6) and leaving (4), (7), (8) as type parameters, and
  `TypeAReceiverClosure.target_of_exit` — is in `quarantine.txt` and imported by
  no live module, so no second reading of exit (1) survives.

  Row 13 commits no fact outside its two declared keys.  The three lemmas of
  `Graph/AnchoredReturnCompletion.lean` are framework statements about an
  arbitrary object and an arbitrary length predicate, consumed inside the row's
  own proof and inside the `Incompatible` instance; none of them is a statement
  about the residual's object, so none of them is a ledger entry withheld from
  the index.  The slice calls no `ExactLedger.root`, `append`, `publishFact`,
  `refine` or `initializeScope`, carries no second `…Ledger` type, and names no
  producer, row number or execution position.

  What this row does *not* do is decide which of the four visible returns
  realizes exit (1); `def:typeA-saturated-exits` quantifies anchored returns, not
  visible ones, so the node states the definition's own alternative and the
  visible family is carried by node `[93]`'s clause rather than re-derived here.
- **Ledger and residual.**  One canonical `ExactLedger`.  The row reads node
  `[93]`'s fact by exact key off the literal incoming cursor — no producer, no
  predecessor depth, no re-selection — and commits exactly one of the two arms
  through `Decision.run`.  `Decision` preserves the residual, so the Type A
  residual node `[63]` selected is retained definitionally; the closed arm
  appends only Core's reserved closure key, which the vocabulary cannot spell.
- **Transport and terminals.**  No CT: the row is a Core `Decision` and the
  closure is `Core.Strategy.closeIncompatible`, not a registered `closeLeft`.
  The closed arm's index is `closed :: typeAExitOneReturn :: known`; the no arm's
  is `typeAExitOneFree :: known`, which still carries `typeAVisibleEntry` and
  therefore hands node `[97]` the same port.  Neither arm's index contains the
  other's key, and neither contains node `[93]`'s sibling
  `typeAVisibleFirstExcess`.  `Fixtures/TypeAExitOne.lean` checks each of those,
  the presence of the closure key on the closed arm and its absence on the free
  arm, and `audit_complete` / `audit_facts_unique` / `audit_commits_nonempty` on
  both.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeA-saturated-exits` (1) | def | `Spine.Key.typeAExitOneReturn` / `Spine.Key.typeAExitOneFree` (value schemas in `SpineVocabulary.lean`), decided by `Spine.typeAExitOneDichotomy` | no CT |
| `lem:return-equivalence` at a port | lem | `Graph.VisibleEntry.AnchoredReturn.toEdgeRootedReturn`<br>`Graph.VisibleEntry.hasCycleWithLength_of_anchoredReturn`<br>`Graph.VisibleEntry.not_shiftedCycleLength_of_returnLengthSets_disjoint` | standalone, `Graph/AnchoredReturnCompletion.lean` |
| `lem:typeA-exits-discharged` | lem | `Spine.typeAExitOneReturnClosed` (`Incompatible`), spent by `Spine.runExitOne` | first consumed here, as the disposition of exit (1); it is equally the disposition of rows 14–19 |

**CT composition at this row.**  No CT, and none is wanted.  The row decides one
alternative of a fixed exit list and its closure is an identity of two committed
statements: nothing is enumerated, bounded, or retained, so a CT would add a
finite search that the manuscript does not perform.  The composition is
`Decision.run` followed by `closeIncompatible`, both framework-owned; the row
contributes the alternative and the two schema bridges, which are the identity
on `PLift`.

**Immediate continuation repair.**  The `[93]` yes ledger is now consumed by
`runExitOne` before the existential Residual-C tail is hidden by the chapter
continuation.  The only new branch facts are `typeAExitOneReturn` or
`typeAExitOneFree`; the first closes against the inherited `returnAvoidance`,
and the second is the exact cursor of `[97]`.  Nodes `[97]` and later are not
executed by this repair.

### Row 14 — Exit 2: power-of-two theta `[97]`

- **Paper fact.** Exit (2) of `def:typeA-saturated-exits`: *"two anchored
  receiver-entry returns through one completion port are internally
  vertex-disjoint as anchored paths and their lengths sum to a power of two"*.
  `lem:typeA-common-port-return-cycle` is its discharge: two anchored returns
  through the same port `⃗e = (w,h)` are both simple `h ⤳ w` paths in `G − wh`,
  so they share both endpoints; internal disjointness is then exactly the
  hypothesis of `lem:two-path-criterion`, their union is a simple cycle of
  length `|P₁| + |P₂|`, and *"in particular, if `|P₁|+|P₂| ∈ Pow`, then `G`
  contains a dyadic cycle"*.  `lem:typeA-exits-discharged` lists exit (2) among
  the closed exits for that reason.  The returns are the *receiver-entry*
  returns `def:typeA-visible-load` defines (`P = Γ ∘ Q`), and the clause names
  one completion port of the saturated receiver — not the object at large, and
  not a port qualified by node `[93]`'s visible count, which clause (2) does not
  mention.
- **What the Lean does.**  `Spine.typeAExitTwoDichotomy` (`SpineRows`) reads
  node `[93]`'s exact
  `(packing, component, piece, receiver, VisibleFourUnpeeledPackage)` and
  decides `VisibleEntry.ExitTwoThrough object piece data.LengthOK receiver
  package.outside`.  Both arms retain that same tuple and package; no support,
  receiver, or port is quantified afresh.
  `Graph.VisibleEntry.ExitTwoThrough` is
  `∃ first second : ReceiverEntryReturn object support receiver outside,
  InternallyDisjoint first.toAnchoredReturn second.toAnchoredReturn ∧
  LengthOK (|P₁| + |P₂|)`, and `InternallyDisjoint` is "the only vertices the
  two anchored paths share are the port's own two ends".  The no arm is the
  same configuration with the test denied at the inherited port, which is the
  exact cursor handed to exit (3) at node `[99]`.

  The row consumes node `[93]`'s fact by exact key through
  `[FactKeys.Has typeAVisibleEntry known]` and `ExactLedger.get`, so it does not
  elaborate on a history that has not entered the saturated exit chain, and it
  reconstructs no cursor.  `Spine.typeAExitTwo` and `Spine.runExitTwo`
  (`TypeAExitRun`) install and run it after node `[95]`'s free arm;
  `Spine.runExitChain` walks `[95]` then `[97]` on one immutable prefix.
- **What it should do.**  This is what it does.  The three things the old
  registration was missing are all present: the pair is anchored at a
  *completion port of the receiver the branch selected*, the returns are the
  receiver-entry returns of `def:typeA-visible-load` rather than arbitrary
  paths of the object, and the bridge from two `AnchoredReturn`s through one
  port to a `CommonEndpointsCycle` —
  `Graph.VisibleEntry.commonEndpointsCycle` — is proved rather than assumed.
- **Gap.**  `none`.  `Graph/CommonPortReturnCycle.lean` proves
  `lem:typeA-common-port-return-cycle` outright:
  `two_le_length_of_avoidsPort` supplies the nondegeneracy from the port alone
  (its two ends are adjacent, so a length-zero return would identify them, and
  a length-one return would be the deleted port edge), the two `IsPath` fields
  and `InternallyDisjoint` supply the criterion's disjointness in its own
  orientation, and `CommonEndpointsCycle.target` — `lem:two-path-criterion`,
  the row-2 object — closes the cycle at length `|P₁| + |P₂|`.  Nothing writes
  a power of two: the side condition is `data.LengthOK` of the sum.
  **Facts passes.**
- **Ledger and residual.**  The row reads only the accumulated ledger: node
  `[93]`'s visible-entry fact by exact key, and the current object through
  `current.object`.  Nothing is recomputed from the root input, and the
  residual is unchanged — a `Decision` is a fact-only step, so
  `RefinementSystem.Refines` is the identity and every earlier key stays in the
  output index.  Both arms retain the whole prefix: `typeAExitTwoFreeKeys` still
  contains `selection`, `returnAvoidance`, `typeAVisibleEntry` and
  `typeAExitOneFree`, which is what lets node `[99]` be asked under both
  alternatives already denied.
- **Transport and terminals.**  No CT; the recipe is `Core.Strategy.Decision`,
  and the closure is `Core.Strategy.closeIncompatible` against the registered
  `Spine.typeAExitTwoThetaClosed :
  Incompatible … (K .selection) (K .typeAExitTwoTheta)`.  That instance is the
  only closure content and it reads the two committed statements and nothing
  else: node `[1]`'s selection says the object carries no accepted cycle, and
  `hasCycleWithLength_of_exitTwoThrough` turns the exit fact into one.  No row
  performs the closure, no payload crosses between the arms, and the arm not
  taken is absent from the taken branch's key index
  (`Fixtures/TypeAExitTwo.lean` checks both directions).  The closed arm carries
  the distinguished closure key; the free arm does not, so it is an open
  residual, exactly as `lem:typeA-exits-discharged` leaves it.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:typeA-common-port-return-cycle` | lem | `Graph.VisibleEntry.commonEndpointsCycle`<br>`Graph.VisibleEntry.hasCycleWithLength_of_commonPortReturns` | no CT |
| `def:typeA-saturated-exits` (2) | def | `Graph.VisibleEntry.ExitTwoThrough`<br>`Graph.VisibleEntry.hasCycleWithLength_of_exitTwoThrough`<br>`Spine.typeAExitTwoDichotomy` | no CT |
| `lem:two-path-criterion` | lem | `Graph.CommonEndpointsCycle.target` | consumed here as the gluing step; it is a row-2 object |
| `def:typeA-visible-load` | def | `Graph.VisibleEntry.ReceiverEntryReturn`<br>`Graph.VisibleEntry.AnchoredReturn`<br>`Graph.VisibleEntry.completionPorts` | supplied by row 12 |
| `lem:typeA-exits-discharged` | lem | `Spine.typeAExitTwoThetaClosed` | the disposition of exit (2): a closed exit |

**CT composition at this row.**  No CT.  The manuscript performs no search
here: exit (2) is a property of a pair of returns at a fixed port, and its
discharge is one gluing identity, so there is nothing to enumerate, bound,
certify or retain and a CT would add a finite search the paper does not do.
The composition is `Decision.run` followed by `closeIncompatible`, both
framework-owned; the row contributes the alternative and the two schema
bridges, which are the identity on `PLift`.

### Row 15 — Exit 3: P13 label collision `[99]`

- **Paper fact.** Exit (3) of `def:typeA-saturated-exits`: "a shared `P₁₃`
  window violates the corresponding legal-label relation `C_s`".
  `lem:typeA-visible-entry` states the test: "if two traces pass through a common
  `P₁₃` window, their labels are governed by the relations `C_s` of
  `lem:labels`; failure of the corresponding `C_s` test is the stated label
  collision, which is exit (3)", and `lem:typeA-unpeeled-visible-routing` repeats
  it verbatim for the unpeeled loads.  `lem:typeA-exits-discharged` discharges
  it: "Exit (3) is precisely failure of the legal `P₁₃` label relation from
  `lem:labels`; by definition of the relation, it creates a target event or a
  target-defective local state", and lists exit (3) among the closed exits.
  `lem:labels` (node `[18]`, row 7) defines the attachment label
  `S(x) = {i : x vᵢ ∈ E(G)}`, and, for `s ≥ 0`, `C_s(S,T) = 1` iff
  `s + 2 + |i − j| ∉ Pow` for all `i ∈ S`, `j ∈ T` — "an outside path of length
  `s` between vertices carrying labels `S, T` is safe through the induced path
  `P` precisely when `C_s(S,T) = 1`".
- **What the Lean does.**  `Spine.typeAExitThreeDichotomy` (`SpineRows.lean`) is
  a Core `Decision` on the vocabulary keys `typeAExitThreeCollision` and
  `typeAExitThreeFree`.  It **reads node `[93]`'s `typeAVisibleEntry` by exact
  key** through `ExactLedger.get`, so neither arm is vacuous and the exit is
  asked only on a branch that entered the saturated exit list.  Both arms retain
  the exact packing, canonical component, support, receiver, and visible package
  inherited from `[93]`; the tested proposition itself is
  `LabelCollision current.object data.windowOrder data.LengthOK packing`, with
  `LabelCollisionFree` its literal negation.  Thus clause (3) uses the selected
  packing while preserving, rather than discarding, the ancestry needed by the
  following row.

  `Graph/WindowLabelCollision.lean` is the new generic module.
  `attachmentLabel` is `S(x)` read at a `Graph.TypeBDirectCycle.Presentation`;
  `LabelCollision` is the manuscript's configuration — two outside vertices
  attached to one packed window, a simple connector between them avoiding that
  window, and two attachment coordinates whose
  `Graph.WindowCurvature.closingLength` is accepted;
  `labelCollision_iff_not_safe` proves that clause *is*
  `¬ Graph.WindowCurvature.Safe s S T` at the registered dyadic target, so the
  alternative is `lem:labels`' own relation rather than a second copy of it;
  `connectorCycle`/`connectorCycle_isCycle` build the simple cycle
  `x p_i P p_j y Q x`, whose length `connectorCycle_length` shows to be the
  manuscript's `s + 2 + |i − j|`; and
  `hasCycleWithLength_of_labelCollision` is the closure.

  The run is `Spine.runExitThree` in `Graph/Strategy/TypeAExitRun.lean`, and
  `Spine.runExitChain` walks `[95] → [97] → [99]` on one immutable prefix,
  retaining the literal `typeAExitThreeFree` ledger on this row's no arm.  It
  does not append any `[101]+` key.  The yes arm closes through
  `Core.Strategy.closeIncompatible` against the `selection` fact, registered as
  `Spine.typeAExitThreeCollisionClosed`.
  `Fixtures/TypeAExitThree.lean` checks the row at the spine's own vocabulary.
- **What it should do.**  Exactly this: state the alternative as failure of
  `C_s` at a window shared by the branch's packing, and close the yes arm by the
  cycle the relation is defined by.  A stricter reading of `[99]` would quantify
  over the window shared by two *canonical traces* at the `[89]` receiver rather
  than over the branch's packing, but the manuscript's own discharge of exit (3)
  is the local label test, and the branch the row is asked on is node `[93]`'s
  — read by exact key — so the exit is asked where the manuscript asks it.
- **Gap.**  `none`.  The alternative is the manuscript's relation, proved
  identical to `WindowCurvature.Safe` rather than restated; the closure builds
  the manuscript's own cycle at the manuscript's own length; and no numeral,
  forbidden-gap set, or window order is written anywhere in the row or in the
  generic module.  **Facts passes.**

  One target fact is registered rather than derived: `Data.degenerateClosureRejected`,
  `¬ LengthOK 2`.  It is the exact analogue of `Data.quadrilateralAccepted`, and
  it is the manuscript reading its own target — the legality derivation of
  `lem:labels` counts two *distinct* attachments (`1 ≤ j − i`), so the degenerate
  closing length `closingLength 0 0 = 2` is not a cycle.  The presentation
  discharges it by `decide`; no row states it.
- **Ledger and residual.**  The row reads one fact by exact key
  (`typeAVisibleEntry`) and commits exactly one, on the literal incoming cursor.
  The residual is unchanged: the exit is a fact-only decision on the object the
  branch was handed, and the packing it quantifies over is the configuration's,
  not a recomputation.  The closed arm appends only Core's reserved closure key,
  which the vocabulary cannot spell.
- **Transport and terminals.**  No CT: the row is a Core `Decision` and the
  closure is `Core.Strategy.closeIncompatible`, not a registered `closeLeft`.
  The closed arm's index is `closed :: typeAExitThreeCollision :: known`; the no
  arm's is `typeAExitThreeFree :: known`, which still carries
  `typeAVisibleEntry`, `typeAExitOneFree` and `typeAExitTwoFree`.  This is the
  current canonical boundary; no row manufactures the missing exit-(4) entry.
  Neither arm's index contains the other's key.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `C_s` at a realized window (`lem:labels`, node `[18]`) | lem | `Graph.WindowLabelCollision.attachmentLabel`<br>`Graph.WindowLabelCollision.LabelCollision`<br>`Graph.WindowLabelCollision.labelCollision_iff_not_safe` | no CT; the relation itself is row 7's `Graph.WindowCurvature.Safe`, consumed here |
| exit (3)'s closure (`lem:typeA-exits-discharged`) | lem | `Graph.WindowLabelCollision.connectorCycle`<br>`Graph.WindowLabelCollision.connectorCycle_isCycle`<br>`Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision`<br>`Spine.typeAExitThreeCollisionClosed` | no CT |

No `\label` of this range is *first* consumed here: exit (3) is clause (3) of
`def:typeA-saturated-exits` (row 12), its disposition is
`lem:typeA-exits-discharged` (row 13), and the label algebra it tests is
`lem:labels`, node `[18]`, which belongs to row 7.  The two rows above record
where those three are realized *at this node*.

**CT composition at this row.**  No CT.  The recipe is Core's `Decision` with
`closeIncompatible`, the same one rows 13 and 14 use.  The row decides the
collision predicate on the configuration node `[93]` committed; its yes arm
closes through the Graph-owned cycle construction and its no arm remains the
exact exit-`(3)`-free cursor.  No adapter, carrier, or routing helper is invoked
at this vertex, and no `[101]+` fact is asserted before the missing shared
response realization exists.

### Row 16 — Exit 4: target-defective quotient `[101]`

- **Paper fact.** Exits (1)--(8) are the saturated Type A receiver exits.  Exit (4) is the target-defective quotient exit; its canonical quotient family has Q1--Q4 before the route-8 branch and Q5 only after the selected exit-8 ledger residual supplies the additional Q5 facts.  A member of the pre-route Q1--Q4 family is a genuine boundary-degree-preserving coordinate identification, and exit (4) requires two same-fibre realizations plus a compatible outside context distinguishing their target responses.  In the visible branch of `lem:typeA-unpeeled-visible-routing`, the target-defective quotient's declared routed-load support contains at least one of the four selected visible unpeeled loads.
- **What the Lean does.** `ExitFour.ReceiverClause` and `ExitFour.ReceiverFamily` retain the four pre-route clause tags, the declared coordinate family, the routed-load coordinate map, the structural generation predicate, and its base/identified subset laws.  Q5 is not included in this pre-route family.  `ExitFour.Witness` records a generated family member, a supported unpeeled load, same-boundary realizations, and a literal `Response.TargetDefect`.  `Spine.typeAExitFourDichotomy` reads the exact `[99]` no-arm fact from the incoming `ExactLedger`, asks only about that selected packing/component/piece/receiver/package, and commits either `typeAExitFour` with a witness supporting one of the package's selected visible loads or `typeAExitFourFree` with the corresponding negation.  `Spine.typeAExitFourPeelingStepRow` reads that committed `typeAExitFour` fact with `FactInputs.get` and appends `typeAExitFourPeeled`, the node `[102]` peeling update.  `Spine.typeAExitFourRetestDichotomy` then reads `typeAExitFourPeeled` and commits either the existing `typeASaturatedExitEntry` fact for the enlarged peeling set or `typeAExitFourReceiverDischarged` with the cleared nonnegative receiver-charge inequality.  `Spine.typeAExitFourFiniteDescentRow` reads the current `typeASaturatedExitEntry` fact and commits `typeAExitFourFiniteDescent`, a finite descent theorem for arbitrary current `P₄(w)`.  `Spine.typeASaturatedHandoffSplitDichotomy` then reads that same exact current `typeASaturatedExitEntry` fact and commits either `typeASaturatedHandoffVisible` with a current `VisibleFourUnpeeledPackage` or `typeASaturatedHandoffSilent` with `SilentUnpeeledExcessAt` for the same current `P₄(w)`.  The corresponding selected exit-`(4)` decisions then commit either `typeASaturatedHandoffExitFour` or `typeASaturatedHandoffExitFourFree`; the free fact is the exact same-residual predecessor for node `[103]`.
- **What it should do.** Complete the remaining paper saturated-handoff classification by instantiating the committed finite descent with the real terminal alternatives: closed exits (1)--(3), (5), (6), exit-(7) decorated Type B handoff, exit-(8) route-8 residual, or final unsaturated receiver charge.  Repeated exit-(4) facts must stay inside the mathematical peeling certificate; exposed terminal outcomes must be committed once as ledger facts.
- **Gap.** The `[101]` selected visible decision, `[102]` charge publication, immediate retest, finite arbitrary-peeling descent fact, current-state visible/silent saturated-handoff split, and selected current-state exit-`(4)`/no-exit-`(4)` decisions are present and validated.  Exits `(5)`, `(6)`, `(7)`, and the route-8 no arm are now represented by ordinary ledger decisions/rows downstream; the remaining global gap is not a replacement carrier here but the final branch join after the cold oval closure.  The deleted `ReceiverFamily.Defective` used `entry.state (base \ identified)` and modeled coordinate identification as deletion from an authored state function; that surrogate remains absent, as required.
- **Ledger and residual.** The visible `[101]` row appends one fact to the existing ledger via Core `Decision.run`; the yes and no arms keep the full prior prefix including `[93]`, `[95]`, `[97]`, and `[99]`.  On the yes arm, `[102]` appends `typeAExitFourPeeled` via `factOnly`/`AtomicCT.run`, while retaining the committed `[101]` witness, and then appends exactly one retest fact by `Decision.run`.  When the retest remains saturated, `typeAExitFourFiniteDescent` is appended by `factOnly`/`AtomicCT.run` on that same ledger, the current saturated handoff split appends exactly one of `typeASaturatedHandoffVisible` or `typeASaturatedHandoffSilent`, and the current selected exit-`(4)` decision appends exactly one of `typeASaturatedHandoffExitFour` or `typeASaturatedHandoffExitFourFree`.  All arms retain the complete incoming residual prefix.
- **Transport and terminals.** Core owns the history/refinement mechanics: `Decision.run` over exact keys for `[101]`, one `factOnly` commit for `[102]`, one `Decision.run` for the peeled-residual retest, one `factOnly` commit for `typeAExitFourFiniteDescent`, one `Decision.run` for the current-state saturated handoff split, and one `Decision.run` for current exit-`(4)` occurrence.  No branch payload, side channel, wrapper, or custom transport is used.  Terminal facts are not fabricated by this row.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | Status |
|---|---|---|---|
| Q1--Q4 structural family | def | `Graph.ExitFour.ReceiverClause`, `Graph.ExitFour.ReceiverFamily` | structural metadata only |
| literal fixed-piece response | obstruction | `Graph.AtomResponse.CoordinateSystem.not_exists_literalGluingTargetDefect` | proves this realization cannot distinguish coordinates |
| genuine target-defective member | def | `Graph.ExitFour.Witness` | present structurally |
| selected-load peeling witness | def | `Spine.typeAExitFour` schema requires `witness.load` in the selected package list | present in source |
| node `[101]` decision | Strategy | `Spine.typeAExitFourDichotomy` | validated |
| node `[102]` charge publication | Strategy | `Spine.typeAExitFourPeelingStepRow`, key `typeAExitFourPeeled` | validated |
| node `[102]` retest | Strategy | `Spine.typeAExitFourRetestDichotomy`, keys `typeASaturatedExitEntry` / `typeAExitFourReceiverDischarged` | validated |
| arbitrary exit-(4) finite descent | Graph + Strategy | `Graph.ExitFour.terminal_or_unsaturated_from`, `Spine.typeAExitFourFiniteDescentRow`, key `typeAExitFourFiniteDescent` | validated |
| arbitrary `P₄(w)` visible/silent split | Strategy | `Spine.typeASaturatedHandoffSplitDichotomy`, keys `typeASaturatedHandoffVisible` / `typeASaturatedHandoffSilent` | validated |
| arbitrary `P₄(w)` exit-(4) occurrence | Strategy | `Spine.typeASaturatedHandoffVisibleExitFourDichotomy`, `Spine.typeASaturatedHandoffSilentExitFourDichotomy`, keys `typeASaturatedHandoffExitFour` / `typeASaturatedHandoffExitFourFree` | validated |

**CT composition at this row.** Core `Decision.run` on the exact incoming `typeAExitThreeFree` ledger, followed on the yes arm by `factOnly`/`AtomicCT.run` from `typeAExitFour` to `typeAExitFourPeeled`, then Core `Decision.run` on `typeAExitFourPeeled`; on the still-saturated arm, `factOnly`/`AtomicCT.run` commits `typeAExitFourFiniteDescent` from the exact `typeASaturatedExitEntry` ledger fact, followed by Core `Decision.run` for `typeASaturatedHandoffVisible` versus `typeASaturatedHandoffSilent`, then Core `Decision.run` for `typeASaturatedHandoffExitFour` versus `typeASaturatedHandoffExitFourFree` on the same exact selected state.

### Row 17 — Exit 5: target-complete compression `[103]`

- **Paper fact.** After the exact selected receiver survives exit (4), a nontrivial target-complete response compression is tested on that same response state.  The yes arm is exit (5); the no arm is the exact same residual with exit (5) absent, which is the predecessor for exit (6).
- **What the Lean does.** `Spine.typeAExitFiveDichotomy` reads `typeASaturatedHandoffExitFourFree` from the incoming `ExactLedger`, preserving the selected packing, maximal packing proof, canonical component, support, receiver, current peeling set, saturation proof, and the selected no-exit-(4) visible or silent clause.  It then decides only the paper compression predicate `∃ support, Graph.Strategy.InterfaceReplacement.CompressibleSupport (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object support` for that same current object.  The yes arm commits `typeAExitFive` with the complete selected predecessor tuple plus the compression support; the no arm commits `typeAExitFiveFree` with the same tuple plus the negation.  The stale duplicate keys `typeAExitFiveCompression` and `typeAExitFiveTraceLevel` were removed.
- **What it should do.** The selected `typeAExitFive` arm must close by reading the already-ledgered `uncompressible` fact and the selected compression support.  The `typeAExitFiveFree` arm must be the sole predecessor for exit `(6)`.
- **Gap.** Node `[103]` is implemented and validated as a selected ledger decision, and node `[104]` closes the yes arm by Core's `closeIncompatible`.  The next open step is exit `(6)` from the selected `typeAExitFiveFree` ledger.
- **Ledger and residual.** The row appends exactly one fact to the incoming branch by Core `Decision.run`.  Both arms retain the full prefix, including `[61]`, `[62]`, receiver routing, saturation, visible/silent handoff state, finite descent, and `typeASaturatedHandoffExitFourFree`.  The yes arm then appends `closed` by reading the existing `uncompressible` fact from that same ledger prefix.  No auxiliary route-8 witness is quantified and no residual fact is dropped.
- **Transport and terminals.** Transport is Core-owned: the `typeAExitFive`
  decision runs only after the selected no-exit-(4) ledger fact, commits either
  `typeAExitFive` or `typeAExitFiveFree`, and the yes arm closes with
  `closeIncompatible` from `uncompressible` and `typeAExitFive`.  The no arm
  remains open for exit `(6)`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | Status |
|---|---|---|---|
| selected no-exit-(4) predecessor | ledger fact | `Spine.typeASaturatedHandoffExitFourFree` | validated |
| target-complete proper-support compression | Graph predicate | `Graph.Strategy.InterfaceReplacement.CompressibleSupport` | reused |
| node `[103]` decision | Strategy | `Spine.typeAExitFiveDichotomy`, keys `typeAExitFive` / `typeAExitFiveFree` | validated |
| node `[104]` compression closure | Core closure | `SpineAssembly.typeAExitFiveClosed`, `closeIncompatible` | validated |
| stale route-8/global [103] keys | deleted surface | `typeAExitFiveCompression`, `typeAExitFiveTraceLevel` | removed |

**CT composition at this row.** Core `Decision.run` over the exact incoming
`typeASaturatedHandoffExitFourFree` ledger, producing either `typeAExitFive ::
known` or `typeAExitFiveFree :: known`.  The `TypeAExitRun.typeAExitFive`
decision is used on both visible and silent no-exit-(4) ledgers.  The
`typeAExitFive` arm is closed immediately by Core `closeIncompatible`, using
the already-inherited `uncompressible` fact and the just-committed selected
compression fact.

### Row 18 — Exit 6: response delocalization `[105]`

- **Paper fact.** The exact selected response equality is tested for
  delocalization after exits `(4)` and `(5)` fail.  If it delocalizes, the
  enlarging support is either proper, where `lem:proper-smearing` gives a
  proper-support replacement, or global, where `lem:no-silent-global-smearing`
  gives a strictly smaller closed representative.  Both arms close at `[106]`.
- **What the Lean does.** `Spine.typeAExitSixDichotomy` reads the incoming
  `typeAExitFiveFree` fact by `ExactLedger.get` and commits exactly one of
  `typeAExitSix` or `typeAExitSixFree`.  The fact schemas preserve the selected
  packing, canonical component, piece, receiver, peeling set, saturated state,
  no-exit-`(4)` witness and no-exit-`(5)` predicate.  The yes arm stores a
  `PresentedEntry` with a `Route8.Delocalization`; it is not an arbitrary
  auxiliary route-8 object.  `Spine.typeAExitSixScopeDichotomy` then reads
  `typeAExitSix` and applies the graph-owned `Delocalization.localize`, committing
  either `typeAExitSixProper` or `typeAExitSixGlobal`.
- **Gap.** None for nodes `[105]` and `[106]`.  The surviving no arm is the
  selected `typeAExitSixFree` ledger fact, which is the required predecessor
  for exit `(7)` at `[107]`.
- **Ledger and residual.** Both decisions are Core `Decision.run` steps on the
  literal incoming ledger.  No residual is rebuilt, no sibling facts are merged,
  and all previous facts remain in the exact index.  `SpineAssembly` runs this
  chain after both the visible and silent `typeAExitFiveFree` branches.
- **Transport and terminals.** The proper and global scope facts close by Core
  `closeIncompatible`, reading `selection` plus the just-committed
  `typeAExitSixProper` or `typeAExitSixGlobal`.  The closure proof is
  `not_globalBarrierReading`, the same graph/minimality refutation used by the
  earlier delocalization block.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | Status |
|---|---|---|---|
| selected no-exit-(5) predecessor | ledger fact | `Spine.typeAExitFiveFree` | validated |
| exit-(6) delocalization witness | graph datum | `Graph.Route8.Delocalization` on a selected `PresentedEntry` | reused |
| node `[105]` decision | Strategy decision | `Spine.typeAExitSixDichotomy`, keys `typeAExitSix` / `typeAExitSixFree` | validated |
| node `[106]` scope split | Strategy decision | `Spine.typeAExitSixScopeDichotomy`, keys `typeAExitSixProper` / `typeAExitSixGlobal` | validated |
| proper/global closure | Core closure | `instIncompatibleTypeAExitSixProper`, `instIncompatibleTypeAExitSixGlobal`, `closeIncompatible` | validated |

**CT composition at this row.** Core `Decision.run` over the exact
`typeAExitFiveFree` ledger, followed on the yes arm by Core `Decision.run` over
the exact `typeAExitSix` ledger.  The scope arms append `closed` through
`closeIncompatible`; the no arm appends `typeAExitSixFree` and continues.

### Row 19 — Exit 7: decorated handoff fan `[107]`

- **Paper fact.** A surviving first separator from the exact selected response data produces the decorated Type B handoff after exits (4)--(6) fail.
- **What the Lean does.** `Spine.typeAExitSevenDichotomy` reads the exact
  `typeAExitSixFree` ledger fact and decides the paper predicate
  `HandoffProduced` on the same selected packing and support.  The produced arm
  commits `typeAExitSevenProduced`; the no arm commits `typeAExitSevenFree`.
  `Spine.typeAExitSevenHandoffRow` then reads `selection`, `uncompressible`,
  and `typeAExitSevenProduced` with `FactInputs.get`, proves the produced
  envelope admissible, and appends only `typeAExitSevenHandoff`.
- **Gap.** None for the row-local facts.  The produced handoff fact is ordinary
  ledger state; the global proof still needs the later branch join after cold
  closure.
- **Ledger and residual.** `Spine.runTypeAExitSevenDecision` runs the decision
  from `typeAExitSixFreeKeys`.  `Spine.runTypeAExitSevenHandoff` runs the
  produced-arm handoff commit from `typeAExitSevenProducedKeys`.  Both retain
  the full incoming residual and append facts monotonically through Core
  `Decision.run` or `AtomicCT.run`; no support carrier or route payload is
  introduced.
- **Transport and terminals.** The no arm is the exact predecessor consumed by
  `Spine.runRoute8FromExitSevenFree`; the produced arm is a Type B handoff fact,
  not a terminal.  Terminal dispatch remains a later framework closure/join.

### Row 20 — Heavy-centre split `[68]` (ported: `Spine.highCentreNormalForm`, `Spine.heavyCentreDichotomy`)

- **Paper fact.**  Node `[68]` carries two things.  First the standing law
  `lem:heavy-neighbourhood-normal-form`: at a high centre `h` — `d_G(h) ≥ 4`,
  i.e. strictly above the baseline — (a) every vertex of `N_G(h)` has degree
  three, (b) `G[N_G(h)]` is a matching, since `hxyzh` would be a `4`-cycle, and
  (c) two nonadjacent neighbours of `h` have no common neighbour outside `{h}`,
  since `hxzyh` would be a `4`-cycle.  Then the split proper: does some Type B
  fan centre have `d_G(h) > 4`?  The yes-arm enters `[69]`
  (`cor:heavy-center-local-dichotomy`, `d_G(h) ≥ 5`); the no-arm enters `[78]`,
  where every high centre the support carries has degree exactly four
  (`cor:degree-four-local-activation`).
- **What the Lean does.**  Two live rows on the Type B residual of node `[64]`.
  `Spine.highCentreNormalFormRow` (`SpineRows.lean`) declares
  `Requires := [selection, tightEndpoint]`, `Produces := [highCentreNormalForm]`,
  and its executor calls `Graph.normalForm` once per high centre.
  `Spine.heavyCentreDichotomy` is a `Decision` on `typeBHighSurplus` producing
  `typeBHeavyCentre` on the left and `typeBDegreeFourCentres` on the right.
  `Graph/HighCentreNormalForm.lean` is the mathematics: `Graph.IsHighCentre` is
  `threshold < object.degree centre`, `Graph.NormalForm` is the three-field
  `Prop`-structure whose fields are (a), (b) and (c) verbatim, and
  `Graph.normalForm` derives it from the tight-endpoint law, target avoidance
  and `Data.quadrilateralAccepted`.  Parts (b) and (c) are both instances of the
  single `Graph.not_quadrilateral`.
- **What it should do.**  This is what it does.  The scan domain is the Type B
  support carried by the incoming `[64]` fact, not the ambient vertex set, and
  the split is on the degree of a centre *of that support*.
- **Gap.**  None.  Two notes.  (1) The normal form is stated of the object, at
  every high centre at once, rather than at a named centre: that is what the
  manuscript proves, and a centre is data, which no fact may carry.  (2)
  `Graph.NormalForm.noCommonNeighbourOutside` keeps the manuscript's
  nonadjacency hypothesis even though the quadrilateral argument does not use
  it, so the lemma consumed downstream is the manuscript's own.
- **Ledger and residual.**  Both rows run through `AtomicCT.run` on the literal
  Type B ledger, so the residual is unchanged and every earlier fact stays in
  the output index.  The normal form is committed on the shared prefix, before
  the split, which is why `[69]` and `[78]` both carry it.  The `Decision`
  commits only the arm taken: `typeBHeavyCentreKeys` and `typeBDegreeFourKeys`
  differ in exactly one entry, so neither arm can read the other's.
  `heavyCentreDichotomy` reads `typeBHighSurplus` by exact key through
  `ExactLedger.get` and takes the branch on a `Prop`, so no centre is extracted
  to build it.  The no-arm is committed positively — every high centre of every
  Type B support has degree exactly `δ + 1` — which is node `[78]`'s entry
  condition; it quantifies over supports rather than naming one, for the same
  reason node `[64]`'s own fact does.
- **Transport and terminals.**  Core owns execution: `factOnly` for the normal
  form, `Decision.run` for the split, `AtomicCT.run` for both.  Neither arm
  closes — `[68]` certifies nothing — so the branch continues as exact ledgers
  indexed by `typeBHeavyCentreKeys` and `typeBDegreeFourKeys`; the
  `typeBHighSurplus` cursor is no longer where the branch stops.
  `typeBHeavyCentre_audit_facts` and `typeBDegreeFourCentres_audit_facts` pin
  each arm's twenty-eight facts in commit order by `rfl`, and the two
  `_audit_accounts_for_every_fact` theorems certify through
  `ExactLedger.audit_complete` that nothing was archived, rebased or dropped.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:heavy-neighbourhood-normal-form` | lem | `Graph.NormalForm`<br>`Graph.normalForm`<br>`Graph.not_quadrilateral` | no CT; consumed by `Spine.highCentreNormalFormRow`; also required at rows 21, 26, 27 |
| `def:heavy-center-triangular-port` (high centre) | def | `Graph.IsHighCentre` | no CT; the port types themselves are row 21 |

`Data.quadrilateralAccepted : LengthOK 4` is the one new registered law.  It is
where "`G` contains no power-of-two cycle" enters the normal form, at its own
interface: the only thing (b) and (c) ask of the accepted set is that it
contains `4`.  The EG presentation discharges it with
`Core.DyadicLength.powerOfTwoLength_four`.  Nothing about a graph is registered
and no node writes a numeral.

**CT composition at this row.**  No CT.  The normal form is a `factOnly`
atomic Strategy and the split is a `Decision`; both are lowered by
`AtomicCT.run` against the one canonical `ExactLedger`.


### Row 21 — Heavy-centre local dichotomy `[69]` (ported: `Spine.heavyCentreLocalDichotomy`)

- **Paper fact.**  Node `[69]` is `cor:heavy-center-local-dichotomy`: at a heavy
  centre `h` of degree `k ≥ 5`, either two open ports at `h` are fan-compatible
  in the sense of `def:fan-compatible-open-ports` (`x ∉ s(q)`, `y ∉ s(p)`,
  `s(p) ∩ s(q) = ∅`), or at least `k − 2` ports at `h` are triangular
  (`lem:heavy-center-triangular-alternative`) — in particular three, since
  `k ≥ 5`.  The proof of the second alternative is "`|U| ≤ 2` because
  `G[N_G(h)]` is a matching and a matching has no clique of size `3`, so the
  number of triangular ports is at least `k − |U| ≥ k − 2`".
- **What the Lean does.**  `Spine.heavyCentreLocalDichotomyRow` declares
  `Requires := [highCentreNormalForm]`, `Produces := [typeBLocalDichotomy]`, and
  its executor calls `Graph.heavyCentreLocalDichotomy` at every heavy centre,
  then `Graph.three_le_triangularEndpoints_card` for the "in particular".
  `Graph/HighCentrePorts.lean` is the mathematics.  `Graph.IsShoulder` is `s(p)`
  in membership form — a neighbour of the endpoint other than the centre;
  `Graph.IsTriangularPort` is `e_p^* ∈ E(G)` as "two adjacent shoulders" and
  `Graph.IsOpenPort` its negation, matching
  `def:heavy-center-triangular-port`'s two clauses.  `Graph.FanCompatible` is a
  seven-field `Prop`-structure: the definition's three conditions plus the two
  openness hypotheses and endpoint distinctness.
  `Graph.fanCompatible_of_endpoints_nonadjacent` is
  `lem:same-center-open-port-compatibility`, and
  `Graph.triangularEndpoints_card_of_no_compatible_pair` is
  `lem:heavy-center-triangular-alternative`, both proved from the normal form.
- **What it should do.**  This is what it does.  The node is an *alternative*,
  not an observation, and it is recorded as a disjunction of the manuscript's
  two clauses rather than as a count.
- **Gap.**  None.  Two notes.  (1) The fact is stated at every heavy centre of
  the object at once rather than at a named one, because a centre is data and no
  fact may carry it; the arm the row runs on already establishes that one
  exists.  (2) The counting step goes through
  `Graph.openEndpoints_card_add_triangularEndpoints_card`, which is the exact
  statement that open and triangular ports partition `N_G(h)`, so `k − |U|` is
  an identity rather than an estimate.
- **Ledger and residual.**  The row runs through `AtomicCT.run` on the literal
  heavy-arm ledger, so the residual is unchanged and every earlier fact stays in
  the output index.  It reads `highCentreNormalForm` by exact key through
  `FactInputs.get` — the fact node `[68]` committed on the shared prefix — and
  reads nothing else.  It deliberately does *not* declare
  `typeBHeavyCentre` in `Requires`: the statement quantifies over heavy centres
  and consumes no witness, so declaring it would be a false dependency.
  `3 ≤ threshold` comes from `Data.three_le_threshold`, not from a numeral at
  the node.
- **Transport and terminals.**  Core owns execution: `factOnly` lowered by
  `AtomicCT.run`.  The node has no terminal and does not close.
  The ledger indexed by `typeBLocalDichotomyKeys` replaces the
  `typeBHeavyCentreKeys` cursor, which is no longer where the heavy arm stops.
  `typeBLocalDichotomy_audit_facts`
  pins the arm's twenty-nine facts in commit order by `rfl`, and
  `typeBLocalDichotomy_audit_accounts_for_every_fact` certifies through
  `ExactLedger.audit_complete` that nothing was archived, rebased or dropped.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:surplus-ports` (shoulder pair `s(p)`) | def | `Graph.IsShoulder` | no CT |
| `def:heavy-center-triangular-port` | def | `Graph.IsTriangularPort`<br>`Graph.IsOpenPort` | no CT; also consumed at row 29 |
| `def:fan-compatible-open-ports` | def | `Graph.FanCompatible` | no CT |
| `lem:same-center-open-port-compatibility` | lem | `Graph.fanCompatible_of_endpoints_nonadjacent` | no CT; consumed by the alternative below |
| `lem:heavy-center-triangular-alternative` | lem | `Graph.triangularEndpoints_card_of_no_compatible_pair`<br>`Graph.card_le_two_of_pairwise_adj` | no CT |
| `cor:heavy-center-local-dichotomy` | cor | `Graph.heavyCentreLocalDichotomy`<br>`Graph.three_le_triangularEndpoints_card` | no CT; consumed by `Spine.heavyCentreLocalDichotomyRow` |

The manuscript's excess selector is deliberately not modelled: it chooses
`d_G(h) − 3` of the incident ports, but every statement at this row is about
*all* ports at `h`, which is what the local dichotomy argues about.

`lem:compatible-pair-fan-closure` and `cor:compatible-pair-typeB-routing`, which
the manuscript credits to `[69]` and `[72]`, are consumed at row 25 and are not
implemented; they are recorded there, not here.

**CT composition at this row.**  No CT.  The row is a `factOnly` atomic
Strategy lowered by `AtomicCT.run` against the one canonical `ExactLedger`.


### Row 22 — Certificate-marked fan cap `[70]` (ported: `Spine.fanCertificateCap`)

- **Paper fact.**  Node `[70]` carries the fan-safe graph `𝔽safe_h` of
  `def:typeB-fan-safe`, the `P₁₃` certificate graph of `def:marked-typeB-fan`,
  and the certificate-marked cap.  The provable content is `lem:fan-certificate`:
  in the `P₁₃`-label projection with adjacency `C₂(S,T) = 1`, the clique number
  is at most `8`; every clique containing a non-singleton label has size at most
  `7`; consequently every certificate-marked Type B fan has `d_G(h) ≤ 8`.  The
  proof takes one representative per label, observes that `C₂(S_i,S_j) = 1`
  forbids cross-differences `0`, `4`, `12`, so the representatives are distinct
  and independent in the difference graph `D` on `{0,…,12}`, and computes
  `α(D) = 2 + 2 + 2 + 2 = 8` from `D`'s components `0-4-8-12-0`, `1-5-9`,
  `2-6-10`, `3-7-11`.  `rem:fan-finite` records that this cap is a label-packing
  consequence, not a free parameter.
- **What the Lean does.**  `Spine.fanCertificateCapRow` declares
  `Requires := []`, `Produces := [fanCertificateCap]`, and its executor returns
  `Graph.FanCertificateLabelling.degree_le_fanPackingCap`.
  `Graph/FanCertificate.lean` is the mathematics.  The manuscript's `D` is
  `Graph.WindowCurvature.FanIndependent`: coordinates are non-adjacent when
  `¬ ForbiddenGap 2 (dist i j)`, i.e. when the wedge `u — h — v` closes no
  accepted cycle of length `4 + d`.  `fanPackingCap order` is `α(D)`, the
  `Finset.sup` of the cards of fan-independent sets.
  `card_le_fanPackingCap` is the first sentence, by the manuscript's own
  representative argument; `forbiddenGap_two_zero` (`closingLength 2 0 = 4`, and
  the quadrilateral is accepted) is the manuscript's "since `C₂(S,S) = 0`" and
  is what makes the representatives distinct.
  `card_le_one_add_fanPackingCapAvoiding` is the second sentence.
  `Graph.FanCertificateLabelling` is `def:marked-typeB-fan`'s `S_h : N(h) → 𝓛`
  with its legality and pairwise-`C₂` fields.
- **What it should do.**  This is what it does, and it does it without naming a
  constant.  **No `8` occurs anywhere.**  The cap is computed from the
  registered window order and the registered target, which is precisely
  `rem:fan-finite`'s claim.  Verified against the manuscript by evaluation at
  the registered order: `(Finset.range 13).filter (ForbiddenGap 2) = {0, 4, 12}`
  — the manuscript's "difference is `4` or `12`", plus the `0` that forces
  distinctness — and `fanPackingCap 13 = 8`, its `α(D)`.
- **Gap.**  The row's fact is the cap alone.  The five-clause fan-safe relation
  of `def:typeB-fan-safe` is *not* committed: clause (ii) is the label-curvature
  condition the cap runs on and is present as `WindowCurvature.Safe 2`, but
  clauses (i), (iii), (iv) and (v) — no `2^j − 2` return in `G − h`, the
  identification is not target-defective, no target-complete compression, no
  delocalization — are conditions on the decorated envelope, consumed at rows
  26–28, and this row neither states nor uses them.  They are recorded at those
  rows.  The `≤ 7` refinement is proved
  (`card_le_one_add_fanPackingCapAvoiding`) but is not itself a ledger fact,
  because nothing at this row consumes it; row 23 (`[71]`) is where it is spent.
- **Ledger and residual.**  The row runs through `AtomicCT.run` on the literal
  ledger, so the residual is unchanged and every earlier fact stays in the
  output index.  It reads no prerequisite: the cap is a theorem about the
  registered label algebra and the object's own degree, so `Requires := []` is
  the honest declaration — the same shape node `[18]`'s `localAlgebra` uses.
  The labelling is data, so the fact quantifies over every fan-certificate
  labelling rather than carrying one.
- **Transport and terminals.**  Core owns execution: `factOnly` lowered by
  `AtomicCT.run`.  The node has no terminal.  Because an `AtomicCT` carries no
  predecessor parameter, the *one* executor value `Spine.fanCertificateCap` runs
  after both arms of node `[68]` — the heavy arm after `[69]`, and the
  degree-four arm — which is exactly the manuscript's placement of `[70]` and
  the reason the legacy export had two vertices (`v43`, `v45`) for one
  registration.  The exact successors are indexed by `typeBHeavyFanCapKeys`
  and `typeBDegreeFourFanCapKeys`.  `typeBHeavyFanCap_audit_facts` and
  `typeBDegreeFourFanCap_audit_facts` pin each arm's facts in commit order by
  `rfl`, and the two `_audit_accounts_for_every_fact` theorems certify through
  `ExactLedger.audit_complete` that nothing was archived, rebased or dropped.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:marked-typeB-fan` (the labelling `S_h`) | def | `Graph.FanCertificateLabelling` | no CT |
| `lem:fan-certificate`, clique bound | lem | `Graph.WindowCurvature.card_le_fanPackingCap`<br>`Graph.WindowCurvature.FanIndependent`<br>`Graph.WindowCurvature.fanPackingCap`<br>`Graph.WindowCurvature.forbiddenGap_two_zero` | no CT |
| `lem:fan-certificate`, non-singleton refinement | lem | `Graph.WindowCurvature.card_le_one_add_fanPackingCapAvoiding`<br>`Graph.WindowCurvature.fanClosedNeighbourhood`<br>`Graph.WindowCurvature.fanPackingCapAvoiding` | no CT; unconsumed until row 23 |
| `lem:fan-certificate`, fan-degree cap | lem | `Graph.FanCertificateLabelling.degree_le_fanPackingCap`<br>`Graph.FanCertificateLabelling.label_inj` | no CT; consumed by `Spine.fanCertificateCapRow` |
| `rem:fan-finite` | rem | the derivation of `fanPackingCap` itself | no CT |
| `def:typeB-fan-safe` clause (ii) | def | `Graph.WindowCurvature.Safe 2` | no CT; clauses (i), (iii)–(v) are at rows 26–28 |

`lem:fan-certificate`'s closed-neighbourhood charge statement — every
certificate-closed marked fan with `c − (11−k)/4 ≤ 0` has nonnegative
closed-neighbourhood charge — is the `def:typeB-assigned-ledger` half of the
lemma and belongs with the B2 ledger at row 25; it is not implemented and is
recorded there.

**CT composition at this row.**  No CT.  The row is a `factOnly` atomic
Strategy lowered by `AtomicCT.run` against the one canonical `ExactLedger`.


### Row 23 — Certificate labelling `[71]`/`[80]` (ported: `Spine.fanCertificateDichotomy`)

- **Paper fact.**  Nodes `[71]` and `[80]` ask the same question at two
  positions: *is a certificate labelling present?*  `def:marked-typeB-fan`
  supplies both answers.  A Type B fan is **certificate-marked** when the
  fan-certificate labelling `S_h : N(h) → 𝓛` is part of the assigned support
  data; the yes-arm continues to the B2 ledger `[72]`/`[81]`.  A high-degree
  centre *assigned to a Type B support* but not certificate-marked is a
  **fan-certificate residual center**: it "is included in the Type B
  bridge-residual mass of `def:typeB-residual-mass` and is not used in the
  certificate-closed local discharging step", so the no-arm routes to the
  fan-mass node `[75]`/`[84]`.
- **What the Lean does.**  `Spine.fanCertificateDichotomy` is a `Decision`
  producing `fanCertificateMarked` on the left and `fanCertificateResidual` on
  the right.  The left fact is "every centre of every Type B support that is a
  high centre carries a `Graph.FanCertificateLabelling`"; the right is its exact
  complement, "some centre of some Type B support is a high centre carrying
  none".  The branch is taken by `by_cases` on the left `Prop`, and the arm not
  taken supplies the other arm's clause through `push_neg`.
- **What it should do.**  This is what it does.
- **Gap.**  None.  One scope note, which is the substance of this row.  The
  quantifiers run over **the centres of a Type B support**, not over the
  object's high centres at large.  That is `def:marked-typeB-fan`'s own wording
  — "assigned to a Type B support" — and the distinction is not cosmetic: a
  high centre lying in no Type B support is *not* a fan-certificate residual
  centre, and scoping the question to the ambient vertex set would charge Type B
  bridge-residual mass for centres Type B never assigned.  This is the same
  scope error the legacy row 20 was failed for, and it is not repeated here.
- **Ledger and residual.**  The `Decision` runs on the literal `[70]` ledger, so
  the residual is unchanged and every earlier fact stays in the output index.
  It reads no prerequisite fact: the question is a `Prop` about the object and
  the branch is taken classically, so nothing is consumed and nothing is
  declared.  The two arms differ in exactly one entry —
  `typeBCertificateMarkedKeys` and `typeBCertificateResidualKeys` share the
  whole `[70]` prefix — so neither arm can read the other's, and the retained
  `fanCertificateCap` of node `[70]` remains available to both, which is what
  lets the marked arm conclude `d_G(h) ≤ α(D)` at every assigned centre without
  re-proving it.
- **Transport and terminals.**  Core owns execution: `Decision.run`.  Neither
  arm closes — `[71]` certifies nothing.  The residual arm is the exit
  `typeBCertificateResidual`; the marked arm is **no longer an exit**, because
  rows 24 and 25 now continue on it, so the marked cursor is not retained as a
  terminal leaf beside the new successors.  Its audit theorems moved with it:
  the three indices that now terminate this arm are pinned by
  `typeBDirectCycleClosed_audit_facts`, `typeBB2Choice_audit_facts`
  and `typeBOverlapObstruction_audit_facts`, each of which still lists the
  marked arm's whole prefix, and every exit's
  `_audit_accounts_for_every_fact` certifies through
  `ExactLedger.audit_complete` that nothing was archived, rebased or dropped.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:marked-typeB-fan`, certificate-marked | def | `Graph.FanCertificateLabelling`<br>key `Spine.Key.fanCertificateMarked` | no CT; the labelling itself is row 22's |
| `def:marked-typeB-fan`, fan-certificate residual center | def | key `Spine.Key.fanCertificateResidual` | no CT; consumed by the fan-mass row 27 |

**Both positions are wired.**  `[71]` and `[80]` are one registration at two
positions, and because a `Decision` carries no predecessor, the *same*
`fanCertificateDichotomy` value runs after the degree-four cursor.  With row 29
ported it does: Part VII places `[79]` between `[78]` and `[80]`, so the
degree-four arm now runs `[70]`'s cap, then `[79]`'s profile, then this row at
`[80]`, whose two indices are `degreeFourMarkedKeys` and
`degreeFourResidualKeys`.  Nothing is re-registered and no second copy of the row
exists; the fixture `Fixtures.TypeBFanWindowNode` installs the one value at both
cursors, and checks by `simp` that `typeBHeavyCentre` is absent from the
degree-four indices and `typeBDegreeFourCentres` from the heavy ones, so the two
positions cannot read each other.

The manuscript's `≤ 7` refinement
(`WindowCurvature.card_le_one_add_fanPackingCapAvoiding`, proved at row 22) is
the bound `[71]`'s marked arm spends when a fan label is non-singleton.  It is
available in the framework and is not itself a ledger fact: row 25's B2 question
is a simultaneous-choice statement over the carrier families, and it consumes the
cap through the entry arithmetic rather than by re-reading the label count.

**CT composition at this row.**  No CT.  The row is a `Decision` lowered by
`Decision.run` against the one canonical `ExactLedger`.


### Row 24 — Direct-cycle removal `[72]` (ported: `Spine.directCycleDichotomy`)

- **Paper fact.**  Node `[72]` is one diamond with two halves; this row is the
  structural half.  `def:closed-fan-window-pair` fixes the closed label
  `S(u) = {a_u, b_u}` of a same-window supported cubic-closed neighbour of a
  Type B fan centre and the interlacing length
  `L_×(u,v) = 4 + (a_v − a_u) + (b_v − b_u)`;
  `def:direct-cycle-free-closed-pair` is the conjunction (a)
  `b_u − a_u, b_v − a_v ∉ {2,6}`, (b) `|x − y| ∉ {0,4,12}` for `x ∈ S(u)`,
  `y ∈ S(v)`, (c) `L_×(u,v) ∉ {8,16}` when defined.
  `lem:typeB-direct-fan-window-cycles` builds a power-of-two cycle from each
  negation — (a) `u p_{a_u} P p_{b_u} u` of length `(b_u − a_u) + 2 ∈ {4,8}`;
  (b) `u h v p_y P p_x u` of length `4 + |x − y| ∈ {4,8,16}`; (c)
  `u p_{a_u} P p_{a_v} v p_{b_v} P p_{b_u} u` of length `L_×(u,v)` — and
  `lem:typeB-two-window-cycles` builds `u p_i P p_j v q_b Q q_a u` of length
  `4 + |i−j| + |a−b|` when `|i−j| + |a−b| ∈ {0,4,12}`.  Both lemmas' standing
  side conditions are that `u, v` lie outside the window support and that
  distinct packed windows are vertex-disjoint.
- **What the Lean does.**  `Spine.directCycleDichotomy` is a `Decision` on the
  literal certificate-marked cursor, producing `typeBDirectCycle` on the left and
  `typeBDirectCycleFree` on the right. It reads the selected Type B fact by its
  exact `typeBHighSurplus` key, retaining the same maximal packing and the same
  member of `canonicalPieces (remainderSupport packing)`. The decision is only
  whether a high centre of that selected component carries a
  `TypeBDirectCycle.DirectCycleConfiguration`; the complementary fact records
  `DirectCycleFree` at every high centre of that same component. No arbitrary
  second support or packing is quantified.
  `DirectCycleConfiguration` is the disjunction of the four displays,
  `SameWindowAttachment`, `CrossWindowWedge`, `InterlacedWindowPair`,
  `TwoWindowPair`, each binding a `TypeBDirectCycle.Presentation` whose support
  lies in the packing, the outside vertices, their adjacency to the centre, their
  freeness from the window coordinates, the attachment coordinates, and the
  arithmetic side condition.  The left arm **closes**: the registered
  `instIncompatibleDirectCycle` derives `HasCycleWithLength data.LengthOK` from
  the configuration through
  `hasCycleWithLength_of_directCycleConfiguration` and collides it with the
  selection's own avoidance, so `closeIncompatible` appends the reserved closure
  key on `typeBDirectCycleClosedKeys`.
- **What it should do.**  This is what it does.
- **Gap.**  None.  **Facts passes**, and two things are worth recording.

  *No constant is written.*  Each arithmetic side condition is stated as
  `data.LengthOK` of the length of the cycle its own display builds:
  `LengthOK ((b − a) + 2)` for (a), `LengthOK (4 + |x − y|)` for (b),
  `LengthOK L_×` for (c), `LengthOK (4 + |i−j| + |a−b|)` for the two-window
  case.  At the registered power-of-two target and the registered window order
  those readings are *exactly* the manuscript's `{2,6}` and `{0,4,12}` — inside a
  window of order `13` the only accepted values of `(b − a) + 2` are `4` and `8`,
  and of `4 + |x − y|` are `4`, `8` and `16` — so nothing is weakened and no set
  appears in the source.  The retired legacy row registered `4, 8, 16` as an
  `AcceptedLengths` record discharged `by decide` at the EG site; the ported row
  needs no such record and adds no `Data` field.

  *Two hypotheses became theorems.*  The legacy witnesses *assumed* the packed
  windows disjoint (`windows_disjoint` was a field of the concrete witness).
  Here `Presentation` is derived from the packing's own `InducesWindow` clause by
  `Presentation.exists_of_inducesWindow` — the induced path embedding composed
  with `induceEmbedding`, with `pathGraph_adj` supplying the displayed edges and
  the embedding's injectivity the distinctness — and the two-window
  vertex-disjointness is read off `IsWindowPacking`'s own second clause inside
  `hasCycleWithLength_of_twoWindowPair`.  Only the manuscript's genuinely
  positive side condition, `u, v ∉ W`, is a binder.
- **Ledger and residual.**  The `Decision` runs on the literal ledger the marked
  arm of `[71]` produced, so the residual is unchanged and every earlier fact
  stays in the output index. It reads `typeBHighSurplus` with `ExactLedger.get`;
  this is the selected support and packing established upstream, not a recreated
  object-level existential.
  The closure step is the only read, and it reads by key: `closeIncompatible`
  fetches `selection` and `typeBDirectCycle` with `ExactLedger.get` at the
  framework-owned closure boundary.  Ledger passes.
- **Transport and terminals.**  Core owns execution: `Decision.run`, and
  `closeIncompatible` for the terminal.  Graph supplies the cycle constructions
  (`Graph.TypeBDirectCycle`), the spine supplies the row, and the EG application
  supplies nothing at all — the closure is a framework instance on the spine's
  own keys, not a target injection passed in at a registration site.  The two
  output indices are `typeBDirectCycleClosedKeys` and
  `typeBDirectCycleFreeKeys`; they share the whole marked-arm prefix, so neither
  arm can read the other's, and `typeBDirectCycleClosed_audit_facts` pins the
  closed arm's facts in commit order by `rfl` — closure entry first, then the
  direct-cycle fact, then the whole `[71]` history unchanged.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:closed-fan-window-pair` | def | `TypeBDirectCycle.Presentation`<br>`TypeBDirectCycle.Presentation.exists_stretch` | no CT |
| `def:direct-cycle-free-closed-pair` | def | `TypeBDirectCycle.DirectCycleFree`<br>`TypeBDirectCycle.DirectCycleConfiguration`<br>key `Spine.Key.typeBDirectCycleFree` | no CT |
| `lem:typeB-direct-fan-window-cycles` | lem | `TypeBDirectCycle.hasCycleWithLength_of_sameWindowAttachment`<br>`TypeBDirectCycle.hasCycleWithLength_of_crossWindowWedge`<br>`TypeBDirectCycle.hasCycleWithLength_of_interlacedWindowPair` | no CT |
| `lem:typeB-two-window-cycles` | lem | `TypeBDirectCycle.hasCycleWithLength_of_twoWindowPair` | no CT |

`def:closed-fan-window-pair` is no longer empty.  The closed label is not a
declaration of its own — `S(u) = {a_u, b_u}` is the pair of attachment
coordinates bound by each configuration — but the window presentation the
definition is stated against, and the stretch `p_i P p_j` whose length is
`|i − j|`, both are, and both are *derived* from the packing rather than posited.
`L_×` likewise appears as the length argument of the interlaced display rather
than as a definition, which is the only form in which it is used.

The two lemmas are the paper objects a proof obligation of the run actually
reaches: `instIncompatibleDirectCycle` calls
`hasCycleWithLength_of_directCycleConfiguration`, which is the four-way `rcases`
onto them, and that call is what makes `typeBDirectCycleClosed` a closed
terminal rather than a retained leaf.

**CT composition at this row.**  No CT.  A `Decision` lowered by `Decision.run`
against the one canonical `ExactLedger`, followed by
`Core.Strategy.closeIncompatible` on the arm the test takes.  A CT chain would
add nothing: the closing content is a single implication from a decidable
disjunction to an accepted cycle, and the framework's registered-incompatibility
path carries it with the contradiction recorded in the closure entry's own
`reason`.

### Row 25 — Selected B2 decision `[72]`/`[81]` (`Spine.b2AssignmentDichotomy`)

- **Paper fact.** For the connected assigned Type B support selected upstream,
  the finite candidate families at its assigned high centres either admit one
  pairwise-disjoint choice, or a minimal nonempty subfamily has no such choice.
  The latter is the minimal overlap obstruction of
  `def:typeB-overlap-obstruction`.
- **What the Lean does.** `b2AssignmentDichotomy` runs on the literal
  `typeBDirectCycleFree` cursor and reads that fact with `ExactLedger.get`. The
  fact retains one maximal packing and one member of
  `canonicalPieces (remainderSupport packing)`; `piece` is definitionally that
  component's `pieceSupport`. The row calls
  `TypeBRefinedSupport.b2_or_overlap object threshold dischargeScale packing
  piece` exactly once. Its left arm appends `typeBB2Choice`, retaining the same
  packing, maximality proof, component membership, negative net charge, positive
  surplus, and `HasDisjointChoice ... (centres ... piece)`. Its right arm appends
  `typeBOverlapObstruction`, retaining the same tuple and the current-arity
  `Nonempty (OverlapObstruction ... packing piece)`.
- **Gap.** None for this finite decision. It does not claim the later maximal
  post-ledger core theorem, Type B exclusion, or fan-mass estimate. Those
  successors remain open and must consume these exact ledgers when implemented;
  the obsolete universal `RefinedSupportAssignment` path has been removed rather
  than adapted.
- **Ledger and residual.** Both arms append one semantic fact to the same
  incoming `ExactLedger`; every earlier fact, including
  `typeBDirectCycleFree`, remains in the exact index. No support, packing, or
  component is reselected, and the residual is unchanged.
- **Transport and terminals.** Core owns the split through `Decision.run`.
  Neither arm closes at this node, and no custom result or payload transports
  the witnesses. The immediate indices are `typeBB2ChoiceKeys` and
  `typeBOverlapObstructionKeys`; the fixture checks branch separation at both
  `[72]` and `[81]`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| finite candidate families | definition | `TypeBRefinedSupport.candidateFamily`, `centres` | generic graph API |
| disjoint-carrier B2 choice | proposition | `TypeBRefinedSupport.HasDisjointChoice`, key `Spine.Key.typeBB2Choice` | generic graph API / `Decision` arm |
| minimal overlap obstruction | structure | `TypeBRefinedSupport.OverlapObstruction`, key `Spine.Key.typeBOverlapObstruction` | generic graph API / `Decision` arm |
| finite exhaustive split | theorem | `TypeBRefinedSupport.b2_or_overlap`, `Spine.b2AssignmentDichotomy` | generic theorem / framework `Decision` |
| maximal post-ledger continuation | later theorem | | not claimed at this row; downstream open |

**CT composition at this row.** No CT. One `Decision.run` reads the selected
support fact from the canonical ledger and commits exactly one of the two facts.

### Row 25a — Immediate B2 disjoint-ledger handoff

- **Paper fact.** On the successful arm of the finite B2 choice, clauses
  B2(a)--(c) are the literal simultaneous candidate selection, pairwise carrier
  and reserve disjointness, and the exact common-scale partition of the same
  augmented ledger.  Clause B2(d) adds the maximal post-ledger condition: every
  actual connected component of the remaining core has no high centre, and
  actual exit-`(7)` decorated handoff productions on those components are
  covered by the grouped decorated envelope processed in the same canonical
  step.
- **What the Lean does.** `Spine.disjointPostLedgerComponentsRow` is one `factOnly`
  `AtomicStrategy`.  It reads exactly `typeBB2Choice`, `selection`,
  `uncompressible`, and
  `remainderNormalized` through `FactInputs.get`, constructs one
  `TypeBRefinedSupport.DisjointLedger` from the already selected
  `HasDisjointChoice`, commits `exactAugmentedLedgerRefinement`, and applies
  `TypeBPostLedgerCore.postLedgerCoreHygiene` to every member of
  `Connected.order object ledger.remainingCore`.  Each `PostLedgerComponent`
  includes `noHighCentre`, proved from `ledger.noHighCentre_remaining` on that
  same component.  The same `typeBDisjointLedger` value also proves grouped
  handoff coverage: for any finite family of actual
  `TypeBMaximalCompletion.ComponentExitSeven` productions on the remaining
  components, `TypeBMaximalCompletion.groupedOfComponentExitSeven` supplies the
  canonical `DecoratedHandoff.GroupedEnvelopes`, with the envelope cores exactly
  the selected post-ledger components and the grouped centre set exactly the
  surviving separators of those productions.  The deterministic
  `Data.typeABPresentation` reads only the registered threshold, window order,
  discharge scale, and target.  Empty internal core and hereditary Type A
  uncompressibility for component hygiene are derived from the same
  remainder-normalization fact; decorated-handoff admissibility reads the
  already committed `uncompressible` ledger fact.
- **What it should do.** This: the Type B row publishes the exact selected
  disjoint ledger and the component facts obtained from that ledger.
- **Gap.** None for the Type B facts committed by this row.  The downstream
  Type B exclusion/branch-kill consumer is still row 28; it must read this
  strengthened `typeBDisjointLedger` fact rather than re-prove or wrap B2.
- **Ledger and residual.** The row appends only `typeBDisjointLedger` to the
  literal B2-success `ExactLedger`.  Its value retains the same packing and
  `CanonicalPiece`, the constructed mathematical disjoint ledger, the exact
  refinement, all component hygiene, and the grouped exit-`(7)` coverage theorem
  derived from actual component productions.  The residual is unchanged.
- **Transport and terminals.** `factOnly` supplies equality refinement and the
  ordinary atomic commit.  There is no component iterator commit, payload,
  result type, standalone residual, terminal, or separate B2(d) routing claim.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| B2(a)--(c) selected ledger | structure/theorem | `TypeBRefinedSupport.DisjointLedger`<br>`DisjointLedger.exactAugmentedLedgerRefinement` | generic graph API |
| inherited component hygiene | theorem | `TypeBPostLedgerCore.postLedgerCoreHygiene` | generic graph API |
| Type B no-high-centre maximal-core clause | theorem | `TypeBRefinedSupport.DisjointLedger.noHighCentre_remaining`<br>`TypeBPostLedgerCore.PostLedgerComponent.noHighCentre` | generic graph API |
| grouped decorated handoff coverage | theorem | `TypeBMaximalCompletion.ComponentExitSeven`<br>`TypeBMaximalCompletion.groupedOfComponentExitSeven`<br>`DecoratedHandoff.GroupedEnvelopes` | consumed inside `Spine.disjointPostLedgerComponentsRow` |
| single ledger handoff | semantic fact / row | `Spine.Key.typeBDisjointLedger`<br>`Spine.disjointPostLedgerComponentsRow` | `factOnly` atomic Strategy |

**CT composition at this row.** No CT.  One fact-only atomic Strategy appends
the complete B2 ledger handoff as one semantic fact.  It does not create a
grouped handoff side carrier; the grouped envelope theorem is part of the
`typeBDisjointLedger` value read from the exact ledger downstream.

### Row 26 — Hybrid B1 entry `[74]`/`[82]` (ported: `Spine.hybridEntry`)

- **Paper fact.**  `def:typeB-hybrid-incidence` sets `c = c_W + c_M + c_I`,
  `I_W = 2c_W + c_M`, `I_N = c_M + 2c_I`, and
  `D_N(𝔉) = max{0, D_B(𝔉) − ½I_W(𝔉)}`.
  `lem:typeB-multiclosed-budget` gives `4 ≤ k ≤ 8`, the exactness of the `2c`
  distinct packed-window incidences, and `D_B ≤ ½·2c − ¾`.
  `lem:typeB-hybrid-incidence-budget` proves the `2c` non-`h` incidences
  pairwise disjoint — if `z` were shared, `u−h−v−z−u` is a `4`-cycle — and gives
  total capacity `½I_W + ½I_N = c`, paying `D_B` with slack `(11−k)/4 ≥ ¾`.
  `lem:typeB-hybrid-B1` packages this as the B1 alternative, and
  `prop:fan-closed-port-typeB-routing` (b) is that two fan-closed ports already
  make `D_B` positive.
- **What the Lean does.**  `Spine.hybridEntry` is the one value
  `SpineRows.hybridEntryRow (K .selection) (K .fanCertificateCap)
  (K .fanCertificateMarked) (K .typeBHybridEntry)`, an `AtomicStrategy` with
  `Requires := [selection, fanCertificateCap, fanCertificateMarked]` and
  `Produces := [typeBHybridEntry]`.  It runs after the B2 cursor at `[74]` and
  after the degree-four B2 cursor at `[82]`; `AtomicCT` has no predecessor
  parameter, so those are two positions of one executor and nothing is
  registered twice.  The committed fact is five clauses at every assigned high
  centre of every connected assigned Type B support, quantified over the fan
  envelope and the packed-window union because both are fan data:
  the carriers are pairwise distinct
  (`TypeBHybridIncidence.endpoints_not_shared`, which spends
  `Data.quadrilateralAccepted` and the selection's own avoidance);
  `I_W + I_N = (δ−1)·c`
  (`TypeBHybridIncidence.windowIncidences_add_nonWindowIncidences`);
  `2·s·D_B ≤ s·(I_W + I_N)` (`TypeBHybridIncidence.hybridCapacity_pays`);
  `D_N ≤ s·I_N` (`TypeBHybridIncidence.nonWindowCredit_ge_demand`); and
  `2 ≤ c → 0 < s·D_B`
  (`TypeBHybridIncidence.positive_deficit_of_two_le_closedCount`).
- **What it should do.**  This.  The manuscript's `2c` is `(δ−1)·c` at the
  registered baseline, its `k ≤ 8` is `Data.fanCapSlack` against the label
  algebra's own packing number, and its `(11−k)/4 ≥ ¾` is
  `Data.highCentreDeficitSlack`.  No numeral is written at the row.
- **Gap.**  None outstanding for the row's own statement.  Two things are worth
  recording rather than left implicit.

  The first is `lem:typeB-hybrid-B1`'s shape.  The lemma is a four-way
  alternative — direct power-of-two cycle; target-defective quotient,
  target-complete compression, or delocalization; or the disjoint hybrid entry.
  The row does **not** reproduce the alternation, and this is correct rather
  than a weakening: the direct-cycle arm *is* node `[72]`/`[81]`, which the
  branch has already taken and closed, so the cursor carries
  `typeBDirectCycleFree`; and the manuscript's own reason for discarding the
  middle three is admissibility (`lem:typeB-exclusion`, Step 1: "because `X` is
  admissible, the fan-window data cannot realize a target cycle,
  target-defective quotient, target-complete compression, or delocalization"),
  which is the standing `uncompressible`/`returnAvoidance` history this index
  already carries.  What survives is the hybrid entry, and the row proves it
  unconditionally at every marked centre — the strongest of the four disjuncts.

  The second is that `typeBDirectCycleFree` is *not* declared in the manifest.
  The manuscript states the budget lemma under "none of the direct-cycle
  conclusions occurs", but its proof of the incidence disjointness uses only the
  quadrilateral exclusion, and no other clause reads it.  The fact is on this
  branch's index because the row runs after `[72]`; declaring it would be a
  false dependency.
- **Ledger and residual.**  `Core.Strategy.factOnly` lowered by `AtomicCT.run`.
  The residual is unchanged, so `Refines` is equality, and the output index is
  definitionally `Produces ++ known` — the incoming ancestry is retained in
  full and every earlier fact stays indexed.  The three prerequisites are read
  by `FactInputs.get` on exact keys, and all three are genuinely consumed:
  `selection` supplies the avoidance, `fanCertificateCap` the degree cap and
  `fanCertificateMarked` the labelling.  No producer, depth or position is
  named.
- **Transport and terminals.**  No terminal.  The cursor continues into row 28
  at `[76]` and `[85]`, whose excluded arm closes the branch and whose
  complementary arm is the positive-deficit fan this row pays.  The exact
  `typeBHybridEntryKeys` and `degreeFourHybridEntryKeys` audits pin the two
  indices by `rfl`, and
  `Fixtures.TypeBBridgeNode` installs the same executor value at both.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeB-hybrid-incidence` | def | `TypeBHybridIncidence.windowIncidences`<br>`TypeBHybridIncidence.nonWindowIncidences`<br>`TypeBHybridIncidence.nonWindowDemand` | consumed by `Spine.hybridEntry` |
| `lem:typeB-multiclosed-budget` | lem | `TypeBFanIncidence.closedCount_le_degree`<br>`TypeBHybridIncidence.card_nonHubIncidences`<br>`TypeBHybridIncidence.windowIncidences_add_nonWindowIncidences` | consumed by `Spine.hybridEntry` |
| `lem:typeB-hybrid-incidence-budget` | lem | `TypeBHybridIncidence.endpoints_not_shared`<br>`TypeBHybridIncidence.hybridCapacity_pays`<br>`TypeBHybridIncidence.nonWindowCredit_ge_demand` | consumed by `Spine.hybridEntry` |
| `lem:typeB-hybrid-B1` | lem | `Spine.hybridEntryRow` | consumed by `Spine.hybridEntry` |
| `prop:fan-closed-port-typeB-routing` (b) | pro | `TypeBHybridIncidence.positive_deficit_of_two_le_closedCount` | consumed by `Spine.hybridEntry` |
| `prop:typeB-bridge-reduction` | pro | | |
| `lem:typeB-postledger-core-hygiene` | lem | | |

`prop:typeB-bridge-reduction` and `lem:typeB-postledger-core-hygiene` are empty:
both are the *post-ledger core* half of node `[74]`, and both are inputs of
row 28's Step 2 rather than of the local payment.  They are recorded again there,
where they are owed.

**CT composition at this row.**  No CT.  One `factOnly` `AtomicStrategy`, run by
the framework-owned `AtomicCT.run` at two cursors.  The manuscript's
`½I_W + ½I_N = c ≥ D_B + (11−k)/4` is an aggregation, but it aggregates over a
*fan*, which is local data the row already holds; there is no family to enumerate
and no residual to restrict, so a demand/capacity CT would add a stage without
adding a comparison.

### Row 27 — Bridge fan-mass `[73]`,`[75]`,`[83]`,`[84]` (ported: `Spine.bridgeFanMass`)

- **Paper fact.** Certificate residuals, minimal overlap obstructions, and B2
  exclusion residuals retain their selected support and receive the local
  centre-envelope estimate used by `lem:typeB-bridge-deficit-bound` before
  family aggregation.
- **What the Lean does.** Three ordinary keys are now distinct:
  `fanCertificateResidualMass`, `typeBOverlapObstructionMass`, and
  `typeBExclusionResidualMass`. Their `factOnly` rows require exactly the
  corresponding residual key, read it with `FactInputs.get`, retain its
  selected witnesses in the proposition, instantiate
  `TypeBEnvelopeCharge.envelopeNegativePart_le`, and append the new fact to
  the same `ExactLedger`.
- **What it should do.** Continue from these selected-residual facts to the
  canonical-family sum, route-8-core extraction, and the final
  `M_B <= 16 sigma(G)` comparison without returning to the universal
  `typeBBridgeMass` package.
- **Gap.** The selected per-residual publication is kernel checked. The family
  aggregation and route-8 extraction still use the old generic mass key and
  must be migrated before this row is complete.
- **Ledger and residual.** Each row has one required residual key and one fresh
  produced mass key. `AtomicCT.run` yields `Produces ++ known`; no upstream
  fact is removed and no sibling history is merged.
- **Transport and terminals.** Fact-only equality refinement. No terminal at
  this row.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| selected certificate residual mass | fact | `fanCertificateResidualMassRow` | `factOnly`, reads `fanCertificateResidual` |
| selected overlap obstruction mass | fact | `typeBOverlapObstructionMassRow` | `factOnly`, reads `typeBOverlapObstruction` |
| selected B2 exclusion residual mass | fact | `typeBExclusionResidualMassRow` | `factOnly`, reads `typeBExclusionResidual` |
| centre-envelope bound | lemma | `TypeBEnvelopeCharge.envelopeNegativePart_le` | instantiated inside each row |

**CT composition at this row.** Three residual-specific `factOnly` rows. The
old parameterized `bridgeFanMassRow` is not consumed by these residual
branches.

### Row 28 — Bridge deficit `[76]`/`[85]` (`Spine.typeBSelectedFanCharge`, `Spine.typeBExclusionCharge`, `Spine.typeBExclusionDichotomy`)

- **Paper fact.**  `lem:typeB-exclusion`: for a connected admissible support
  carrying high-degree surplus, with no fan-certificate residual centre,
  admitting B2, and containing neither an admissible route-8 residual profile nor
  an admissible positive-deficit Type B fan-window residual,
  `defp(X) − σ(X) ≥ ¼|V(X)|`, so `No(X) ≥ 0`.  Step 1 is the closed-neighbourhood
  charge; Step 2 sums the disjoint B2 entries and discharges the post-ledger
  core.  `prop:typeB-bridge-reduction` is the same conclusion stated directly.
  `thm:branch-kill` is the branch-closure theorem these nodes feed, jointly with
  `[123]`.
- **What the Lean does.**  The live Type B vocabulary now has ordinary semantic
  keys `typeBSelectedFanCharge`, `typeBExclusionCharge`,
  `typeBExcluded`, and `typeBExclusionResidual`.  `SpineRows.typeBSelectedFanChargeRow` is a
  `factOnly` row requiring `fanCertificateMarked`, `typeBHybridEntry`, and
  `typeBDisjointLedger`; its executor reads all three with `FactInputs.get` and
  appends the selected-entry charge fact for the same canonical B2 ledger:
  every selected entry is a canonical candidate and
  `0 ≤ ledger.selectedEntryPayment₂`.  `SpineRows.typeBExclusionChargeRow`
  then requires `typeBDisjointLedger` and `typeBSelectedFanCharge`, reads both
  with `FactInputs.get`, and appends the B-ledger implication using
  `TypeBEnvelopeCharge.nonNegativeNetCharge_of_disjointLedger_remainingCore_nonneg_of_selectedEntryPayment₂_nonnegative`.
  `Spine.typeBExclusionDichotomy` is a `Decision.run` split whose implementation
  reads the exact incoming `typeBDisjointLedger`, computes that ledger's
  remaining-core charge, and either publishes the impossible `typeBExcluded`
  arm or publishes `typeBExclusionResidual` carrying the same ledger witness.
  There is no universal remaining-core fact, detached consumer, wrapper, or
  side ledger.
- **What it should do.**  This row should append exactly the local selected-entry
  charge fact, the B-ledger charge implication, and the clean-arm closure fact
  on the incoming exact ledger.  The surviving arm should carry exactly
  `typeBExclusionResidual` over the same exact prefix, and the clean arm should
  close through Core's `Impossible` mechanism.
- **Gap.**  No row-local gap remains in the generic Type B spine surface.  The
  row consumes the strengthened `typeBDisjointLedger` rather than `typeBB2Choice`,
  as Step 2 spends the full B2 ledger, including B2(d)'s post-ledger core and
  grouped handoff coverage.  The validation for this claim is:
  `lake build Hypostructure.Graph.TypeBEnvelopeCharge`,
  `lake build Hypostructure.Graph.Strategy.SpineVocabulary`,
  `lake build Hypostructure.Graph.Strategy.SpineRows`,
  `lake build Hypostructure.Graph.Strategy.SpineAssembly`,
  `lake build Hypostructure.Graph.Strategy.SpineContinuationRun`, and
  `lake build HypostructureErdos64EG`
  from `proofs/hypostructure_erdos_64_eg`, plus
  `python3 .agents/skills/eg-proof-expansion/scripts/api_catalog.py check --repo-root .`.

  **Facts passes.**  Two notes.

  `thm:branch-kill` (a) — the Type A half, `lem:typeA-exclusion` — is **not**
  committed and is not this row's: it is node `[86]` in section E, and the Type A
  branch of this spine still ends at the `[89]`/`[90]` leaves.  Nor is `[123]`,
  `thm:large-budget-route8-only`, which is section F.  The theorem's conclusion
  is a conjunction of the two local halves plus `[123]`, and only the Type B half
  is owned here.

  Step 2's remaining hypotheses — `chosen = ∅` and `PostLedgerCore` — are read
  from the committed disjoint ledger; the dichotomy either closes the exact
  ledger or stores its negative-charge witness as the residual arm.
- **Ledger and residual.**  Certified for this row.  The selected-entry charge
  and charge implication are fact-only; the exclusion decision consumes them
  from the incoming ledger.  All four leave
  the residual unchanged and append ordinary `Spine.Key` facts to the incoming
  exact prefix.  The heavy and degree-four closed/residual row-28 key indices
  have `ExactLedger.audit_complete` and `ExactLedger.audit_facts_unique`
  witnesses, so the audit proof is read from the ledger itself rather than from
  a hard-coded fact list.
- **Transport and terminals.**  Certified for this row.  The Type B clean arm
  has the `Impossible` instance needed to append the reserved closure key after
  `typeBExcluded`; Core owns that closure step.  The surviving arm is the
  exact ledger key `typeBExclusionResidual`.  No Type B closure wrapper, custom
  route payload, or side ledger is present.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeB-assigned-ledger`, `(B-ledger)` | def | `TypeBEnvelopeCharge.augmentedLedger`<br>`TypeBEnvelopeCharge.augmentedLedger_add_card_centres`<br>`TypeBEnvelopeCharge.nonNegativeNetCharge_of_augmentedLedger_nonneg` | consumed by `SpineRows.typeBExclusionChargeRow` |
| `def:typeB-candidate-ledger`, B2(a) | def | `TypeBRefinedSupport.CandidateData`<br>`TypeBRefinedSupport.CandidateData.IsCandidate`<br>`TypeBRefinedSupport.DisjointLedger.entry_isCandidate`<br>`Spine.Key.typeBSelectedFanCharge`<br>`SpineRows.typeBSelectedFanChargeRow` | ordinary ledger fact |
| `lem:typeB-exclusion` (Step 1 selected-entry charge) | lem | `Spine.Key.typeBSelectedFanCharge`<br>`SpineRows.typeBSelectedFanChargeRow` | ordinary ledger fact, read by Step 2 |
| `lem:typeB-exclusion` (Step 2) | lem | `TypeBEnvelopeCharge.nonNegativeNetCharge_of_disjointLedger_remainingCore_nonneg_of_selectedEntryPayment₂_nonnegative`<br>`SpineRows.typeBExclusionChargeRow`<br>`Spine.typeBExclusionDichotomy` | ordinary ledger facts |
| `prop:typeB-bridge-reduction` | pro | `Spine.Key.typeBExclusionCharge`<br>`Spine.Key.typeBExcluded` | ordinary ledger facts |
| `lem:typeB-postledger-core-hygiene` | lem | `TypeBPostLedgerCore.PostLedgerComponent` inside `typeBDisjointLedger` | available through the ledger |
| `def:typeB-multiclosed-residual` | def | `Spine.Key.typeBExclusionResidual` | no arm of the dichotomy |
| `thm:branch-kill` (b), Type B | thm | `Spine.typeBExclusionDichotomy`<br>`Spine.Key.typeBExcluded`<br>`Spine.instImpossibleTypeBExcluded` | clean arm is an impossible ledger fact; residual arm remains an ordinary decision fact |
| `thm:branch-kill` (a), Type A | thm | | |

The Step 1 row does not rebuild the candidate entries already carried by B2; it
reads the selected ledger through the incoming exact ledger and commits the
selected-entry charge theorem as an ordinary `Spine.Key` fact.

**CT composition at this row.**  Built.  The row is three framework-owned steps:
one `factOnly` `AtomicStrategy` for `typeBSelectedFanCharge`, one `factOnly`
`AtomicStrategy` for the charge implication, and one `Decision.run` that reads
the committed disjoint ledger and publishes either the impossible
`typeBExcluded` fact or the ledger-backed residual.  Step 2's aggregation is over
the assigned centres whose disjointness is B2's own.  The clean arm closes through
Core's impossible-fact path; the no arm remains the ordinary
`typeBExclusionResidual` key produced by `Decision.run`.


### Row 29 — Degree-four fan profile `[78]`,`[79]` (ported: `Spine.degreeFourProfile`)

- **Paper fact.**  `[78]` is the degree-four branch `d_G(h) = 4`, the no arm of
  `[68]`, whose local content is `cor:degree-four-local-activation`: at a high
  centre with `d_G(h) = 4`, either (i) two open ports at `h` are fan-compatible,
  or (ii) at least two ports at `h` are triangular.  The proof is the
  heavy-centre one: if two open endpoints are nonadjacent then
  `lem:same-center-open-port-compatibility` gives (i); otherwise the open set `U`
  is a clique, `lem:heavy-neighbourhood-normal-form` makes `G[N_G(h)]` a matching
  so `|U| ≤ 2`, and `4 − |U| ≥ 2` ports are not open, hence triangular.  `[79]`
  is the profile: *centre surplus `1`, `0 ≤ c ≤ 4`, `D_B = c − 7/4`*, where `c`
  is the cubic-closed neighbour count and `D_B = c − (11−k)/4` is the
  closed-neighbour deficit of `def:typeB-multiclosed-residual`; the fan is
  certificate-closed when `D_B ≤ 0`, which at `k ≤ 7` reads `c ≤ 1` and at
  `k = 8` reads `c = 0`.
- **What the Lean does.**  `Spine.degreeFourProfile` is a fact-only
  `AtomicStrategy` whose manifest requires `highCentreNormalForm` and produces
  `typeBDegreeFourProfile`.  The committed fact says: at every centre of the
  object with `degree centre = threshold + 1`, the activation dichotomy holds —
  either a fan-compatible open pair exists or
  `δ − 1 ≤ |triangularEndpoints|` — the centre surplus is `1`, and for every
  envelope the cubic-closed count is at most `δ + 1` and the scaled deficit is
  `s·c − s·δ + (δ + 2)`.

  The activation half is `Graph.heavyCentreLocalDichotomy`, *the same theorem row
  21 uses*: it needs only the normal form, so nothing is re-proved for the
  degree-four case.  What differs is what the degree buys afterwards — row 21
  spends `k ≥ δ + 2` through `three_le_triangularEndpoints_card`, and here
  `k = δ + 1` gives `δ − 1` by arithmetic, which is the manuscript's
  `4 − |U| ≥ 2` at its own baseline.  The three profile readings are
  `Graph.TypeBFanIncidence.degreeFourProfile`.
- **What it should do.**  This is what it does.
- **Gap.**  None.  **Facts passes.**  Four notes, the first three answering the
  legacy row's three recorded failures.

  *The profile is now what the node commits.*  The legacy `degreeFourProfileScan`
  scanned a triangular-port count — alternative (ii) of `[78]`, not `[79]` — and
  `ScanData` had no field in which a conclusion could travel, so the proved
  `degreeFourFanProfile` was reachable from no node.  Here the profile *is* the
  fact: it is in `Produces`, so omitting it would fail to elaborate.

  *`[78]` is not a missing vertex.*  It needs no registration of its own: node
  `[68]`'s no arm already commits `typeBDegreeFourCentres`, the positive
  statement that every high centre any Type B support carries sits exactly at
  `δ + 1`.  That fact is `[78]`, and this row runs on the branch carrying it.

  *The scan no longer runs on both arms.*  The legacy blueprint rejoined the two
  arms of `[68]` (`v43 → v41` and `v45 → v41`) and ran the degree-four scan on
  the heavy path too.  This row runs only after the degree-four cursor:
  `typeBDegreeFourProfileKeys` contains `typeBDegreeFourCentres` and not
  `typeBHeavyCentre`, and the fixture checks that separation by `simp`.

  *No constant is written.*  `D_B = c − (δ − (k+1)·α)`, carried at the scale `s`
  as the integer `s·c − s·δ + (k+1)`.  At the registered `δ = 3`, `s = 4` and
  `k = 4` that is the manuscript's `c − 7/4`; the `7/4`, the `11` of `(11−k)/4`
  and the `α = 1/4` appear nowhere in the source, and because every comparison is
  integral nothing rounds.
- **Ledger and residual.**  The row runs on the literal ledger node `[70]`'s cap
  left on the degree-four arm, and the residual is unchanged (a fact-only step).
  It reads `highCentreNormalForm` by semantic key through `FactInputs.get` and
  reads nothing else — the profile arithmetic is about the object's own degrees.
  It does *not* declare `typeBDegreeFourCentres` as a requirement, because the
  executor does not consume it: the fact is stated at every centre of degree
  `δ + 1` directly, so a declared requirement would be a false dependency.  Its
  presence on the branch is what makes the fact *about* the Type B supports, and
  that is a property of the cursor rather than of the manifest.  The legacy
  failure mode is gone: the old read was `residualOf stage`, which could not tell
  which arm of `[68]` it was on.  Ledger passes.
- **Transport and terminals.**  Core owns execution: `factOnly` and
  `AtomicCT.run`, with `rowManifest` declaring the one requirement and the one
  production.  Graph supplies `TypeBFanIncidence` and the activation theorem.  No
  terminal — `[79]` is a profile, not a decision.  With this row in place Part VII
  is wired: the degree-four arm runs `[70]`, `[79]`, `[80]`, then `[81]`'s two
  halves, so the degree-four fan-cap cursor is replaced by the four exact
  successor ledgers `degreeFourCertificateResidual`,
  `degreeFourDirectCycleClosed`, `degreeFourB2Choice` and
  `degreeFourOverlapObstruction`, each with its
  `_audit_facts` pinned by `rfl` and its `_audit_accounts_for_every_fact`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `cor:degree-four-local-activation` | cor | `Graph.heavyCentreLocalDichotomy`<br>key `Spine.Key.typeBDegreeFourProfile`, first clause | no CT; the same theorem row 21 consumes |
| `def:typeB-multiclosed-residual` | def | `TypeBFanIncidence.IsCubicClosed`<br>`TypeBFanIncidence.closedNeighbours`<br>`TypeBFanIncidence.closedCount`<br>`TypeBFanIncidence.scaledDeficit`<br>`TypeBFanIncidence.IsCertificateClosed`<br>`TypeBFanIncidence.not_isCertificateClosed_iff` | no CT |
| `[79]`, the profile itself | — | `TypeBFanIncidence.degreeFourProfile`<br>`TypeBFanIncidence.closedCount_le_degree`<br>`TypeBFanIncidence.surplus_eq_one` | no CT |
| `def:triangular-fan-core` | def | | row 26: the activation's second alternative is a *count* of triangular ports, and the shoulder-pair core is what `[82]`'s hybrid entry spends |
| `lem:triangular-shoulder-completion` | lem | | row 26 |
| `lem:triangular-port-return` | lem | | row 26 |
| `lem:triangular-first-landing` | lem | | row 26 |
| `lem:triangular-cross-shoulder` | lem | | row 26 |
| `prop:triangular-port-typeB-routing` | pro | | row 26 |
| `def:fan-closed-port` | def | | row 26 |
| `prop:fan-closed-port-typeB-routing` | pro | | row 26 |

The triangular-completion chain is deliberately empty here and is not silently
dropped.  `cor:degree-four-local-activation` states its routing claims as
consequences of `cor:compatible-pair-typeB-routing` and
`prop:fan-closed-port-typeB-routing`, and those are what turn two triangular
ports into two *fan-closed* ports with `D_B ≥ 1/4`.  This row commits the
activation alternative and the profile; the routing that converts alternative
(ii) into fan-closed incidence data belongs to node `[74]`/`[82]`, row 26.  That
is the manuscript's own division — Part VII's panel puts the profile at `[79]`
and the payment at `[82]` — and the deficit identity committed here is exactly
what the payment consumes.

**CT composition at this row.**  No CT.  One fact-only `AtomicStrategy` lowered
by `AtomicCT.run` against the one canonical `ExactLedger`.  The row proves a
conjunction about every degree-`δ+1` centre at once; there is no enumeration for
a CT to own, because a centre is data and the fact quantifies rather than
selecting one — which is also why the legacy `OrderedWitnessScan` was the wrong
shape for it.

### Row 30 — Ordered surplus activation `[125]`–`[128]` (ported: `Spine.sparseSlackSurplus`, `Spine.activeSurplusFamily`, `Spine.sparsePortActivation`, `Spine.sparseSurplusSurvivor`, `Spine.activeSurplusDemands`)

- **Paper fact.** `[125]` is the sparse-pressure survivor: a minimal
  counterexample past `[19]` for which none of the five sparse surplus exits of
  `def:named-surplus-exits` occurs.  `[126]` is `lem:sparse-slack-surplus`:
  `σ(G) = n - 6 - 2λ` and `m = (3/2)n + (1/2)σ(G)`.  `[127]` is
  `lem:sparse-excess-port-extraction`: `|𝒫_exc| = σ(G)`, and for every
  `p = (h,x) ∈ 𝒫_exc`, `d_G(h) ≥ 4`, `d_G(x) = 3` and `N_G(x) = {h, a_p, b_p}`
  with `a_p, b_p ≠ h` distinct.  `[128]` is `lem:sparse-port-activation`: each
  selected port carries `T(p) = {x, a_p, b_p}`; a simple `x`–`h` path
  `R_p ⊆ G - hx`; if `p` is open, the lexicographically first `Q_p ⊆ G - x`
  joining `a_p` to `b_p` of length `2^{j(p)} - 1` with `j(p) ≥ 2`; if `p` is
  triangular, the triangle `x a_p b_p x` together with `R_p`.
  `lem:surviving-active-family` concludes `𝒜₀ := 𝒫_exc` with `|𝒜₀| = σ(G)`.
- **What the Lean does.** Three fact-only rows of
  `Hypostructure/Graph/Strategy/SurplusRows.lean`, installed at the spine's own
  keys and checked over the literal ledger indexed by `surplusAboveKeys`.
  `sparseSlackSurplusRow` commits `2m = δn + σ(G)` — `lem:sparse-slack-surplus`
  cleared of division and of the abbreviation `λ = 2n − 3 − m` — from the
  standing baseline read off the residual (`Requires := []`).
  `activeSurplusFamilyRow` reads node `[10]`'s `slackIndependent` entry and
  commits `(excessPorts δ).card = degreeSurplus δ` together with, at every
  selected port, `δ < d(c(p))`, `d(x(p)) = δ` and `|s(p)| = δ − 1`.  The count is
  `FiniteObject.card_excessPorts` of the new
  `Hypostructure/Graph/ExcessPortFamily.lean`, which builds `𝒫_exc` as the first
  `d(h) − δ` entries of the object's own ordered neighbour list at each high
  centre and sums the disjoint per-centre blocks to `ambientSurplus`; the port
  clauses are `SurplusPort.endpoint_degree_eq` and `SurplusPort.card_shoulders`.
  `sparsePortActivationRow` reads the `selection` entry and commits, at every
  selected port carrying a shoulder pair, clause (b) — a simple `x(p)`–`c(p)`
  path of `G − c(p)x(p)` whose first edge after `x(p)` is one of the two
  shoulders — clause (c) — a simple `a_p`–`b_p` path of `G` avoiding `x(p)` whose
  restored length is accepted — and clause (d), the triangle of a triangular
  port.  Clause (c) is `SurplusPort.openPortWitness_of_minimal` of
  `Hypostructure/Graph/SparsePortActivation.lean`, which reads the port as a
  `TightVertexSuppression.Configuration` and spends the framework's own
  `singleSuppressionWitness_of_minimal`: minimality gives the suppressed object
  an accepted cycle, avoidance forces it through the inserted shoulder chord,
  and the reconstruction returns the path.

  Clause (b) is `SurplusPort.portReturn_of_minimal` of the same module on the
  new `Hypostructure/Graph/Contraction.lean`, which carries `lem:bridgeless`.
  `EdgeContraction.hasReturn_of_minimal` assumes the ordered edge has no return
  and contracts it — `FiniteObject.contractEdge` deletes the head and
  transplants its remaining incidences onto the tail, the irreflexivity guard of
  `SimpleGraph.fromRel` discarding the contracted edge itself.  Without a return
  the two endpoints have no common neighbour, since a common neighbour is a
  triangle on the edge and a triangle is a return; so `degree_contracted_of_ne_tail`
  gives every other vertex its source degree and `degree_contracted_tail` gives
  the merged vertex `d(tail) + d(head) − 2`, the contracted edge counted once at
  each end.  The contraction has one vertex fewer, so minimality supplies it an
  accepted cycle.  That cycle meets the tail in two incidences, each an original
  tail edge or a transplanted head edge: a mixed pair splices along the rest of
  the cycle into the return itself (`false_of_mixed_incidences`), so the two
  agree, and `certificateOfPullback` reads the cycle back into the source along
  the inclusion or along `merge`, the injective map that sends the tail to the
  head — contradicting avoidance.  The port supplies the degree hypothesis from
  its own `centre_high` and the standing baseline, and the first edge of the
  return is a shoulder because the endpoint's only other incidence is the
  deleted port edge.  `#print axioms` on
  `EdgeContraction.hasReturn_of_minimal` and
  `SurplusPort.portReturn_of_minimal` reports `propext`, `Classical.choice` and
  `Quot.sound` only, and
  `Hypostructure/Fixtures/OfficialEdgeContractionGraph.lean` checks the
  contraction's adjacency, its vertex drop, both degree readings, the
  minimum-degree preservation and both forms of `lem:bridgeless` at the type
  level.
- **What it should do.** Nothing further.  Every paper object of `[125]`--`[128]`
  is committed, and each is proved from a fact the branch already carries.
- **Gap.** None.

  `[125]`'s entry now carries a second conjunct, `∀ support, ¬
  ReplacementSupport`: `lem:replacement`'s proper-support obstruction at the same
  selection, proved by `Spine.not_globalBarrierReading` from the selection
  entry's own avoidance and minimality.  It is committed here rather than
  assumed at node `[132]`, which is the node that spends it.

  `def:named-surplus-exits` is a five-clause inductive, `Graph.SparseSurplusExit`,
  and `[125]`'s survivor hypothesis is *derived* rather than assumed:
  `Graph.survives_of_selection` refutes each clause where the manuscript refutes
  it -- (a) by the selection's avoidance, (b) by
  `DeclaredQuotient.targetComplete_of_identified`, (c) by node `[11]`--`[14]`'s
  `cor:uncompressible` entry, (d) by the selection's minimality against the
  delocalization coordinate's transfer, and (e) by
  `lem:suppressed-family-critical-cycle`, which
  `TightVertexSuppression.CompatibleFamily.suppressedFamilyExpansion` already
  proved and which nothing had been reading.  Clause (c) is stated at
  `CompressibleSupport`, the *target-complete* two-way notion the manuscript
  names, not at the one-way `ReplacementSupport`; the two differ exactly in
  whether the outside-context clause is an implication or an equivalence, and
  the weaker one would have made the survivor a stronger surrogate.

  No exhaustive dichotomy is written at `[125]`, and none is owed: the
  manuscript's `[125]` is a survivor *hypothesis*, and at a selected minimal
  counterexample the complementary arm is refuted outright rather than routed.
  A `Decision` there would carry an uninhabited side.

  `Γ(p)` itself is `SurplusPort.responseSupport`, a function of the object and
  the port: its two hypotheses are node `[128]`'s own clauses, not parameters,
  so nothing about it is supplied.  `SurplusPort.canonicalReturn` is the
  manuscript's "lexicographically first" `R_p` -- the head of the framework's
  length-major path schedule -- and it takes `Nonempty (PortReturn …)`, the
  committed proposition, because `SimpleGraph.Reachable` *is*
  `Nonempty (Walk …)`.  Neither witness can fail to exist: no return path would
  make `c(p)x(p)` a bridge, which `EdgeContraction.hasReturn_of_minimal`
  refutes, and no suppression path would give the suppressed object no accepted
  cycle, which minimality refutes.  Clause (b) is existential in the manuscript
  -- the choice lives in its proof and is read back by clause (d) -- so the row
  commits existence, which is exact.

  `activeSurplusDemandsRow` reads node `[128]`'s entry **whole**.  All three of
  its clauses are canonical data of an active demand and are exactly what
  `responseSupport` needs, so projecting out clause (b) would have dropped
  `Γ(p)`, which `def:active-surplus-demands` requires.
- **Ledger and residual.** The predecessor is the literal `surplusAboveKeys`
  ledger of node `[19]`'s above arm — nine facts, including `selection` and
  `slackIndependent`, both of which this block reads by exact key through
  `FactInputs.get`.  Each row is `factOnly`, so its refinement is
  `RefinementSystem.refl` and the residual is unchanged; `AtomicCT.run` appends
  each row's declared productions to the incoming index, and the output index is
  `sparseActivationKeys surplusAboveKeys`.  No row calls `ExactLedger.root`,
  `append`, `publishFact`, `refine`, `initializeScope` or `FactInputs.ofLedger`.
  Ledger and Residual pass.
- **Transport and terminals.** Core's `AtomicCT.run` owns the commit, the index
  extension and the work accounting; the rows own only their manifests and their
  proofs.  Nothing is transported outside the ledger, no payload channel exists,
  and the block is nonbranching, so it declares no terminal.
  `Hypostructure/Fixtures/SurplusRun.lean` runs the block on the spine's own
  `surplusAboveKeys` cursor and checks `audit_complete`, `audit_facts_unique`
  and `audit_commits_nonempty` on the result.  That fixture builds:
  `runSparseActivation` was missing the `FactKeys.Has (K .uncompressible)`
  instance parameter node `[125]`'s survivor row reads, so the block did not
  elaborate at all; `surplusAboveKeys` carries `uncompressible`, so declaring
  the requirement is all that was owed and the exact surplus ledger discharges it.
  Transport passes.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:named-surplus-exits` | def | `Graph.SparseSurplusExit`, `Graph.SurvivesSparseExits`, `Graph.survives_of_selection`; `lem:replacement`'s proper-support obstruction at the same selection, via `Spine.not_globalBarrierReading` | standalone (`sparseSurplusSurvivorRow`) |
| `lem:sparse-slack-surplus` | lem | `Spine.sparseSlackSurplusRow` | standalone |
| `lem:sparse-excess-port-extraction` | lem | `FiniteObject.card_excessPorts`, `FiniteObject.SurplusPort.endpoint_degree_eq`, `FiniteObject.SurplusPort.card_shoulders` | standalone |
| `lem:bridgeless` | lem | `EdgeContraction.hasReturn_of_minimal` | standalone |
| `lem:sparse-port-activation` | lem | `FiniteObject.SurplusPort.portReturn_of_minimal`, `FiniteObject.SurplusPort.openPortWitness_of_minimal`, `FiniteObject.SurplusPort.triangle_of_shoulders_adj` | standalone |
| `def:active-surplus-demands` | def | `Graph.ActiveSurplusDemands` | standalone (`activeSurplusDemandsRow`) |
| `lem:suppressed-family-critical-cycle` | lem | `TightVertexSuppression.CompatibleFamily.suppressedFamilyExpansion`, `Graph.SurvivesSparseExits.suppression_arithmetic`, `Graph.SurvivesSparseExits.suppression_chords_nonempty` | standalone |
| `lem:surviving-active-family` | lem | `Graph.surviving_active_family` | standalone (`activeSurplusDemandsRow`) |

`lem:sparse-port-activation`'s cell covers all four clauses.  Clause (b) is
committed existentially because that is how the manuscript states it; its
lexicographic choice is `SurplusPort.canonicalReturn`, which `Γ(p)` uses.  `lem:bridgeless` is not a label this row's own
statement consumes; it is the prerequisite of clause (b)'s proof, and it is
listed because this row is where the framework acquires it.
`lem:surviving-active-family` is now stated about the *active* family: its
exit-freeness clause is the survivor fact, its cardinality is `card_excessPorts`
read from `[127]`, and its canonical-data clause is clause (b) read from
`[128]`.  `activeSurplusDemandsRow` proves nothing again -- it commits the family
those three facts already are.

**CT composition at this row.** No CT: five atomic fact-only Strategies run in
the manuscript's order by `AtomicCT.run` against one immutable prefix.  The
manuscript's own ordering is a dependency chain, not an enumeration — `[127]`
consumes node `[10]` and `[128]` consumes the selection — so there is nothing
for a scan or a resource comparison to buy at this node.

### Row 31 — Baseline demand accounting `[129]` (ported: `Spine.baselineSpineDemand`)

- **Paper fact.** `def:baseline-spine-demand`: with `N = C(n,2)`,
  `m₀ = ⌈(3/2)n⌉` and `B₀(n) = log₂ C(N, m₀)`, a family `ℐ_spine` of declared
  target coordinates is a baseline spine demand with deficit `E_spine(n)` when
  `ℐ_spine` is independently target-testable and `|ℐ_spine| ≥ B₀(n) −
  E_spine(n)`.  Its two numerical inputs are `lem:exact-cubic-baseline-budget`
  (`B₀(n) = (3/2)n log₂ n + O(n)`) and `lem:incremental-skeleton-room`
  (`log₂ C(N,m) − log₂ C(N,m₀) ≤ s log₂ n` for `m = m₀ + s ≤ 2n − 2`).
  `def:spine-lower-bound-deficits` records the lower-bound deficit packages.
- **What the Lean does.** `baselineSpineDemandRow` of `SurplusRows.lean`, run
  after the five activation rows.  It commits five statements about the
  residual's own object, every one with the logarithms cleared, all from
  `Hypostructure/Graph/BaselineSpineDemand.lean`:

  1. `lem:incremental-skeleton-room` on the manuscript's own envelope,
     `C(N, m₀+s) ≤ C(N, m₀)·n^s` for `m₀ + s ≤ 2n − 2`
     (`incremental_skeleton_room`), proved from the one-step identity
     `C(N,k+1)(k+1) = C(N,k)(N−k)` and `C(n,2) ≤ n·m₀`;
  2. that estimate spent at the object's own edge count,
     `skeletonBudget object ≤ C(N,m₀)·n^(m − m₀)`
     (`skeletonBudget_le_cubicBaselineBudget_mul_pow`);
  3. `lem:exact-cubic-baseline-budget` in both directions,
     `C(N,m₀) ≤ (2n)^{m₀}` (`cubicBaselineBudget_le_pow`) and
     `(n−1)^{m₀} ≤ C(N,m₀)·(2(δ+1))^{m₀}`
     (`pow_pred_le_cubicBaselineBudget_mul`).  The first is the manuscript's
     `C(N,m) ≤ (eN/m)^m` with `e` replaced by Stirling's own `⌈e⌉` from
     `Core.FiniteEntropy.pow_self_le_three_pow_mul_factorial`; the second is its
     product estimate `C(N,k) ≥ (N/k)^k` through
     `Nat.pow_sub_le_descFactorial`.  Their logarithms are
     `m₀(log₂ n − log₂(2(δ+1))) ≤ B₀(n) ≤ m₀(log₂ n + 1)`, which at
     `m₀ = ⌈δn/2⌉` is `B₀(n) = (δ/2)n log₂ n + O(n)` — the manuscript's display
     at the registered baseline.  The lower direction carries the manuscript's
     own nonemptiness hypothesis `2m₀ ≤ N`, below which the baseline stratum is
     empty and `B₀(n)` has no lower bound at all;
  4. `def:baseline-spine-demand` itself, as `Graph.IsBaselineSpineDemand`: a
     family `ℐ_spine` of declared target coordinates that is independently
     target-testable (`Core.TargetRank.targetRank system = family.card`) and
     satisfies `|ℐ_spine| ≥ B₀(n) − E_spine(n)`, committed as
     `C(N,m₀) ≤ 2^(|ℐ_spine| + E_spine)`.  The commitment is universal over the
     coordinate type, the family and the admissible quotient system, and
     existential in nothing: `isBaselineSpineDemand_of_package` turns any
     surviving family carrying a package's `L` coordinates into a baseline spine
     demand.  `E_spine(n)` is this node's **output** `Graph.spineDeficit n δ L =
     cubicBaselineExponent n δ − L`, computed from the object's own order and
     the package, with `cubicBaselineExponent n δ = m₀·(log₂ n + 2)` the bit
     form of clause 3's upper half at the object's own dyadic scale count;
  5. `def:spine-lower-bound-deficits`, as the three package lower bounds
     `windowPackageBound` (`L_win = c₁₃·p₁₃·log₂ n`),
     `highEntropyPackageBound` (`+ |R|·log₂ n / d`) and
     `curvaturePackageBound` (`+ K·|R|`), at the registered `windowRate`,
     `entropyDenominator` and `curvatureCost`, together with the ordering
     `D_{he+Ω} ≤ D_he ≤ D_win` of their deficits.  The entropy term rounds
     down, which is the safe direction for a lower bound and is where the
     manuscript's `−o(n)` goes.

  `m₀` is `cubicBaselineEdgeCount n δ = ⌈δn/2⌉`, the least edge count a
  `δ`-regular object can carry; the only registered inputs are `2 ≤ δ` from
  `Data.three_le_threshold` and the three package rates.  No decimal of
  `def:spine-lower-bound-deficits` — `c₁₃ = 118.108581006`, `K`, `θ_he` —
  occurs anywhere: each is the registered rate the presentation already carries
  for its own node.  The row declares `Requires := []`, which is honest: every
  clause is a theorem about the residual object's two counting observables and
  the registered rates, so declaring a prerequisite would claim a dependency the
  proof does not have.
- **What it should do.** This.
- **Gap.** None.  The universal future-family schema has been removed.
  `baselineSpineDemandRow` now requires the exact
  `windowPackageSeparated` key, reads its `WindowPackageStatement`, selects the
  residual object's maximal packing, and commits a concrete
  `FiniteObject.BaselineWindowDemand`.  That object fixes the packing, bit
  family, declared quotient system, full-rank equation,
  `IsBaselineSpineDemand`, computed `spineDeficit`, and the proved linear bound
  `spineDeficit ≤ data.surplusScale * object.vertexCount`.  The high-surplus entry
  now executes node `[21]` first; failure of the complete target package is a
  distinct `windowPackageCold` cursor.  No theorem hypothesis or callback
  remains in the committed baseline fact.
- **Ledger and residual.** `factOnly` over the row-30 stage: the predecessor is
  the literal ledger the five activation rows left, refinement is
  `RefinementSystem.refl`, the residual is unchanged, and `AtomicCT.run` appends
  the single production to the incoming index while retaining every earlier key.
  The row calls none of `ExactLedger.root`, `append`, `publishFact`, `refine`,
  `initializeScope` or `FactInputs.ofLedger`, and reads the object only through
  `FactInputs.current`.  Ledger and Residual pass.
- **Transport and terminals.** As row 30: Core owns the commit and the
  accounting, the row owns its manifest and its proof, the operation is
  nonbranching and declares no terminal, and
  `Hypostructure/Fixtures/SurplusRun.lean` checks `audit_complete`,
  `audit_facts_unique` and `audit_commits_nonempty` on the result.  The five
  clauses are one production, not five: they are the conjunction
  `def:baseline-spine-demand` is fixed by, and there is no payload channel
  beside it.  Transport passes.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:baseline-spine-demand` | def | `Graph.IsBaselineSpineDemand`, `Graph.isBaselineSpineDemand_of_package`, `Graph.cubicBaselineExponent`, `Graph.spineDeficit` | standalone |
| `lem:exact-cubic-baseline-budget` | lem | `Graph.cubicBaselineBudget_le_pow`, `Graph.pow_pred_le_cubicBaselineBudget_mul`, `Graph.cubicBaselineBudget_le_two_pow` | standalone |
| `lem:incremental-skeleton-room` | lem | `Graph.incremental_skeleton_room` | standalone |
| `def:spine-lower-bound-deficits` | def | `Graph.windowPackageBound`, `Graph.highEntropyPackageBound`, `Graph.curvaturePackageBound`, `Graph.spineDeficit_le_of_le` | standalone |

`lem:incremental-skeleton-room` and `lem:exact-cubic-baseline-budget` are listed
here rather than at row 32 because `[129]` is the node that commits them; the
manuscript files both at `[131]`, where they are consumed.
`def:baseline-spine-demand`'s independent target-testability is
`Core.TargetRank.targetRank_eq_card_iff_survives`, the framework's own rank
apparatus, not a second notion of independence built for this node.

**CT composition at this row.** No CT: one atomic fact-only Strategy.  The
manuscript's `[129]` fixes a baseline rather than comparing two resources, so
there is no demand family to enumerate and nothing for CT5 to decide.  The three
lower-bound packages are not alternatives either — they are three admissible
readings of the same `E_spine`, ordered by inclusion of their coordinate
supplies, so no `Decision` is owed and none is written.

### Row 32 — Canonical pair-response `[130]`–`[134]` (ported: `Spine.canonicalPairLedger`, `Spine.blockedPairRouting`, `Spine.sparsePairExitClosed`)

- **Paper fact.** `[130]` splits `Π(𝒜₀) = C(𝒜₀,2)` into free and blocked pairs;
  `def:sparse-pair-response` attaches to `π = {p,q}` the lexicographically first
  minimum-vertex connected `X_π ⊇ T(p) ∪ Γ(p) ∪ T(q) ∪ Γ(q)`, its boundary
  `∂X_π`, and the declared coordinate `r_π`.  `[131]` is
  `prop:sparse-entropy-sandwich` and its blocked refinement
  `prop:sparse-entropy-sandwich-with-blockers`.  `[132]` is
  `lem:sparse-pair-dependence-exit`.  `def:surplus-blockers` fixes the closed
  clause list (a)–(f), `def:canonical-sparse-blocker-order` totally orders the
  blockers, `def:canonical-blocker-ledger` (`[134]`) sets `Φ_can(π) = B_π` to the
  least one and defines `Π_blk`, `Π_free`, and
  `lem:canonical-blocker-ledger-no-overcount` proves
  `|Π_blk| = |𝔉_can| = Σ_{B ∈ ℬ_can} μ(B)`.
- **What the Lean does.** `canonicalPairLedgerRow` of `SurplusRows.lean`, run
  after node `[129]` and reading the row-30 `activeSurplusFamily` entry.  It
  commits `|Π(𝒜₀)| = C(σ(G),2)` — `FiniteObject.card_portPairSchedule`, the
  unordered pairs of the excess selector counted through the same
  `card_excessPorts` row 30 committed — and then, at every
  `FiniteObject.DemandActivation`, the whole of `[130]`–`[134]`:
  - `def:surplus-blockers` **instantiated**.  `Graph/SurplusBlockers.lean`
    declares `Blocker`, one constructor per clause (a)–(f) carrying that clause's
    own witness, and `blockers π` is the genuine `Finset` `𝖡𝗅𝗄(π)` assembled from
    the six clauses.  `Blocks kind π` is "`π` carries a blocker object of that
    clause", and `exists_blocks_iff_blockers_nonempty` is the definition's own
    closing paragraph as a theorem: a pair is charged exactly when it exhibits a
    finite-capacity object, never for want of a closure.  Clauses (a), (b) and
    (c) intersect the demands' own `T(p) ∪ Γ(p)`, `R_p` and `{a_p, b_p, x(p)}`,
    whose items are vertices and edge-incidences — the first two summands of
    `𝔘_sp(G)`, which is why the primitive carrier is what they charge to.
  - `def:canonical-blocker-ledger` at that set.  `Φ_can` is
    `CanonicalFibreLedger.canonicalLabel` at
    `SameTokenBlockerRoles.canonicalBlockerOrder`, the clause order (a)–(f), and
    the two identities — the split `|Π_blk| + |Π_free| = |Π(𝒜₀)|` and the
    no-overcount `|Π_blk| = Σ_B μ(B)` — are `SparsePairLedger`'s, read at the
    instantiated relation.  Nothing is re-proved: `DemandActivation.chargedPairs`
    is `FiniteObject.chargedPairs` at `Blocks`.
  - `def:sparse-pair-response`.  `Graph/SparsePairResponse.lean` builds `X_π` as
    `CanonicalSupport.select?` — the framework's single implementation of
    "the lexicographically first connected subgraph with the minimum possible
    number of vertices containing …", new in
    `Graph/CanonicalSupportSelection.lean` — at the seed
    `T(p) ∪ Γ(p) ∪ T(q) ∪ Γ(q)`, which is the *same* declared support clause (a)
    intersects.  `∂X_π` is `SupportAtom.cutBoundary`, the literal cut boundary.
    `r_π` is the (D7) base coordinate of `def:declared-coordinate-signature`
    labelled `π` and supported on `X_π`; `X_Π` is the same selection at the union
    of the `X_π`, and the manuscript's "viewed by restriction to its declared
    support" is `support_restrict_pairCoordinate`.  `card_pairFamily` gives
    `|ℛ_Π| = |Π|`.
  `lem:sparse-pair-dependence-exit` is **not** in this fact.  It is a disjunction
  about the object, so it is node `[132]`'s own branch:
  - **Node `[132]`**, `Spine.blockedPairRouting` /
    `blockedPairRoutingDichotomy`, a `Decision`.  The test is the manuscript's
    own exit alternative, and it is a property of the object, so the split is
    the excluded middle on it and nothing is assumed to make it exhaustive:
    `SurvivesSparseExits ∧ ∀ support, ¬ ReplacementSupport`.  Both conjuncts are
    what `blockerSeparation_of_reducing`'s last two cases spend — the
    delocalization exit of `def:named-surplus-exits` and `lem:replacement`'s
    proper-support obstruction — and both are exits in the manuscript's sense.
    `Graph/DeclaredRankQuotient.lean` splits `def:admissible-rank-quotient` into
    `AttemptedQuotient` — the quotient the proof *tries*, whose two representative
    clauses are conditional on target-completeness, because that is what the
    definition says — and `DeclaredQuotient`, the admissible one.
    `AttemptedQuotient.route` is the manuscript's four-case analysis in its own
    order: boundary-degree separation, context separation, proper replacement,
    smaller closed representative.
  - The **blocker arm** commits `canonicalBlockerRoute`:
    `blockerSeparation_of_reducing` and
    `prop:sparse-pair-independence-dichotomy`'s
    `targetRank_eq_card_of_exitFree`, **with no hypothesis left**.  The arm's own
    verdict discharges both, so a rank-reducing attempted determination exhibits
    the blocker of type (d) or (e) as concretely separated realizations, and the
    declared family attains full target rank — independent target-testability in
    the sense of `def:target-rank`.  This is the arm the canonical blocker
    ledger `[134]` and everything downstream of it runs on.
  - The **exit arm** commits `sparsePairExit` and is **node `[133]`**, *"sparse
    surplus exit closes"*.  It collides with node `[125]`'s entry, which now
    carries both conjuncts, and `Spine.sparsePairExitClosed` is the `Incompatible`
    instance read off the two committed statements — neither node knows the other
    exists.  Core's own `closeIncompatible` appends the canonical closure key, so
    the arm is the closed ledger indexed by `sparsePairExitKeys` and nothing
    downstream runs.
  - `prop:sparse-entropy-sandwich-with-blockers`, `prop:sparse-entropy-sandwich`
    and `cor:sparse-pair-entropy-saturation` are `entropySandwich` and its two
    readings, with the logarithms cleared exactly as
    `def:baseline-spine-demand` already clears them:
    `2^{|ℐ_spine|+|Π_free|} ≤ C(N,m)` and `C(N,m₀) ≤ 2^{|ℐ_spine|+E}` give
    `2^{|Π_free|} ≤ 2^{E}·n^{m−m₀}`, whose logarithm is the manuscript's
    `|Π_free| ≤ E_spine(n) + (½σ(G)+1) log₂ n` because `m − m₀ ≤ ½σ(G) + 1` is the
    branch's own slack.  The saturation corollary is that bound at the full
    schedule, rewritten to `C(σ(G),2)` through `card_portPairSchedule`.
  `Graph/CurvatureTargetRank.lean` was rewritten rather than extended:
  `CurvatureQuotient` is now the `DeclaredQuotient` instance at the raw internal
  wedges and `curvatureQuotientSystem` is `declaredQuotientSystem` at that family,
  so there is one admissible-quotient structure in the tree and `localize` is
  proved once.
- **What it should do.** This.
- **Gap.** None.  `MixedSpinePairDemand` contains the concrete mixed family,
  exact target-rank equation, exact entropy count, multiplicative sandwich and
  linear sandwich.  Node `[131]` commits that object; node `[136]` preserves it
  in `CertifiedObjectCapacityLedger`, so downstream pressure rows read the
  proved count rather than an implication antecedent.
- **Ledger and residual.** `factOnly` over the row-31 stage for `[130]`:
  refinement is `RefinementSystem.refl`, the residual is unchanged, the row reads
  `activeSurplusFamily` by exact key through `FactInputs.get`, and `AtomicCT.run`
  appends the single production to the incoming index.  Node `[132]` is a
  `Decision` over that stage: `Decision.run` appends exactly one arm's key to the
  same immutable prefix, so the arm not taken is absent from the taken arm's
  index and the token ledger cannot be levied on a branch whose dependence was
  settled by an exit.  Ledger and Residual pass.
- **Transport and terminals.** Core owns the commit, the accounting, the branch
  and the closure; the rows own their manifests and their proofs.  Node `[133]`
  is a terminal that closes: the closure key is appended by Core's
  `closeIncompatible` from two committed facts, not asserted by a row.  Transport
  passes.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:sparse-pair-response` | def | `Graph.CanonicalSupport.select?`<br>`FiniteObject.DemandActivation.pairSupport`, `.pairSeed`, `.pairBoundary`, `.familySupport`<br>`FiniteObject.DemandActivation.pairCoordinate`, `.pairFamily` | standalone |
| `lem:sparse-pair-dependence-exit` | lem | `Spine.blockedPairRoutingDichotomy` (node `[132]`, a `Decision`)<br>blocker arm: `Graph.blockerSeparation_of_reducing`<br>exit arm: `Spine.sparsePairExitClosed` with `Core.Strategy.closeIncompatible` (node `[133]`) | standalone |
| `prop:sparse-pair-independence-dichotomy` | pro | `Graph.survives_of_exitFree`<br>`Graph.targetRank_eq_card_of_exitFree`, on node `[132]`'s blocker arm | standalone |
| `cor:sparse-pair-entropy-saturation` | cor | `Graph.entropySandwich` at the full schedule, through `FiniteObject.card_portPairSchedule` | standalone |
| `lem:exact-cubic-baseline-budget` | lem |  | committed at row 31 |
| `lem:incremental-skeleton-room` | lem | `Graph.incremental_skeleton_room` | standalone |
| `lem:mixed-sparse-spine-dependence` | lem | `Graph.AttemptedQuotient.route`<br>`Graph.blockerSeparation_of_reducing` | standalone |
| `prop:sparse-entropy-sandwich` | pro | `Graph.entropySandwich_of_unblocked` | standalone |
| `prop:sparse-entropy-sandwich-with-blockers` | pro | `Graph.entropySandwich` | standalone |
| `def:surplus-blockers` | def | `Graph.FiniteObject.Blocker` (clauses (a)–(f))<br>`Graph.FiniteObject.DemandActivation.blockers`, `.Blocks`<br>`Graph.SameTokenBlockerRoles.BlockerKind` | standalone |
| `def:canonical-sparse-blocker-order` | def | `Graph.SameTokenBlockerRoles.canonicalBlockerOrder` | standalone |
| `def:canonical-blocker-ledger` | def | `FiniteObject.DemandActivation.chargedPairs`, `.freePairs`, `.multiplicity` | standalone |
| `lem:canonical-blocker-ledger-no-overcount` | lem | `FiniteObject.DemandActivation.card_chargedPairs_eq_sum_multiplicity` | standalone |
| `def:admissible-rank-quotient` (as consumed here) | def | `Graph.AttemptedQuotient`, `Graph.DeclaredQuotient` | standalone; shared with rows 20/69 |

`def:surplus-blockers`' cell now names the clause *objects*, not only the clause
alphabet: `Blocker` has one constructor per clause and no other, which is the
definition's "the blocker must be an object explicitly listed above".

**CT composition at this row.** No CT: one atomic fact-only Strategy and one
`Decision`.

`[130]` is drawn as a diamond but is a *partition*, not a branch, and the
manuscript is explicit about it: `def:canonical-blocker-ledger` defines
`Π_blk` and `Π_free` as a disjoint decomposition of the one schedule
`Π(𝒜₀)` in the one object, and `lem:capacity-token-high-load` at node `[137]`
proves its display by reading **both** sides at once — *"The canonical ledger
gives the disjoint partition `C(𝒜₀,2) = Π_free ⊔ Π_blk`.  By
`prop:sparse-entropy-sandwich-with-blockers`, `|Π_free| ≤ …`.  By
`lem:token-ledger-no-overcount`, `|Π_blk| = Σ ℓ_cap(t) ≤ L_max|𝔗_cap|`."*  That
is why the figure has `[131]` → `[137]` (*"free pairs"*) **and** `[136]` →
`[137]`.  A `Decision` at `[130]` would put the two charges on sibling branches
with disjoint key indices, and `[137]`'s own proof could then never read both.
So the count is a fibre identity, and `[130]` is a fact.

`[132]` is a branch and is one here.  `lem:sparse-pair-dependence-exit` is a
disjunction about the object — *"either `G` has a sparse surplus exit …, or some
`π ∈ Π` has a sparse surplus blocker of type (d) or (e)"* — and
`prop:nonnear-cubic-sharp-overload-routing` (b) carries *"a sparse surplus exit
occurs"* as a live outcome of the whole branch.  Its exit arm is the terminal
`[133]`.

### Row 33 — Capacity-token accounting `[134]`–`[136]` (ported: `Spine.sparseUpperEnvelope`, `Spine.capacityTokenLedger`)

- **Paper fact.** `lem:sparse-upper-envelope` proves `m ≤ 2n − 2` for the minimal
  counterexample, from `lem:no-proper-core` (`G − v` is `2`-degenerate, since
  every proper subgraph has a vertex of degree at most `2`) and
  `lem:deletion-critical` (some vertex has degree exactly `3`).
  `def:primitive-sparse-blocker-carrier` builds
  `𝔘_sp(G) = V(G) ⊔ I_E(G) ⊔ 𝒫_exc` with `I_E(G) = {(e,v) : e ∈ E(G), v ∈ e}`;
  `lem:primitive-carrier-supply` proves `|𝔘_sp(G)| = n + 2m + σ(G) ≤ 6n`.
  `def:capacity-token-ledger` builds `𝔗_cap = 𝔗_prim ⊔ 𝔗_R ⊔ 𝔗_W` and the
  four-case assignment `Θ_cap(π)` with load `ℓ_cap(t) = |Θ_cap^{-1}(t)|`;
  `lem:capacity-token-supply` gives `|𝔗_cap| ≤ 8n + σ(G)`;
  `lem:token-ledger-no-overcount` gives `|Π_blk| = Σ_{t} ℓ_cap(t)`;
  `def:same-token-patterns` defines the token-fibre graph `H_t`.
- **What the Lean does.** `capacityTokenLedgerRow` of `SurplusRows.lean`, with
  `Requires := [canonicalPairLedger, noProperBaseline, tightEndpoint,
  surplusAbove]` and `Produces := [sparseUpperEnvelope, capacityTokenLedger]`.
  All four reads are spent and both productions are the manuscript's.

  **`lem:sparse-upper-envelope` is proved, not carried.**
  `Graph/SparseUpperEnvelope.lean` is new and proof-agnostic.  It counts inside
  an explicit support without `Sym2` and without division: `localIncidences S`
  is the *ordered* adjacent pairs inside `S`, so `card_localIncidences` is the
  induced handshake `|localIncidences S| = Σ_{v ∈ S} d_S(v)` and
  `card_localIncidences_erase` is the exact deletion identity
  `|localIncidences S| = |localIncidences (S − v)| + 2 d_S(v)`.
  `card_localIncidences_le_of_degenerate` is then the degeneracy count itself,
  by the degeneracy order: a `k`-degenerate graph on `N ≥ k+1` vertices
  satisfies `|localIncidences| + k(k+1) ≤ 2kN`, which is `e ≤ kN − C(k+1,2)`
  cleared of subtraction; the base of the order is `N = k+1`, where the bound is
  `localDegree_add_one_le_card`, "no vertex is its own neighbour".
  `edgeCount_add_two_le_of_noProperBaseline` is the manuscript's own proof:
  `noProperBaseline` makes every nonempty part of `G − v` a proper induced
  subgraph — `ProperSubgraph.ofInducedSupport` — hence one missing the baseline,
  hence one carrying a vertex of degree at most `δ − 1`, so `G − v` is
  `(δ − 1)`-degenerate; putting the tight vertex back adds its own `δ`.

  The result is stated at the *registered* baseline, `m + 2 ≤ (δ − 1)·n`, which
  at the manuscript's `δ = 3` is exactly `m ≤ 2n − 2`.  The manuscript's shape is
  false above the registered baseline — a `4`-regular graph has `m = 2n` — so
  the coefficient is `δ − 1` and no numeral is written.  The tight vertex is not
  assumed either: the branch's own node-`[19]` entry gives
  `surplusThreshold(n) < σ(G)`, so `σ(G) > 0`, so `2m > δn ≥ 0`
  (`edgeCount_pos_of_degreeSurplus_pos`), so an edge exists
  (`exists_dart_of_edgeCount_pos`), and `lem:deletion-critical` puts one of its
  two ends exactly at the baseline.

  **Both supply displays are now unconditional.** `𝔘_sp(G)` is the literal
  three-summand `Finset.disjSum` of the vertex set, the incidence family and the
  excess selector, the incidence count being the handshake `|I_E(G)| = 2m`.
  `card_primitiveCarrier_le` concludes at `FiniteObject.primitiveCarrierSupply`,
  which is `3(δ − 1)n` — the manuscript's `6n` at its own `δ = 3` — because
  `n + 2m + σ(G) = 4m − (δ − 1)n` spent against the envelope just proved gives
  `3(δ − 1)n − 8`.  `card_capacityTokens_le` concludes at
  `FiniteObject.capacityTokenSupply`, which is that plus `2n`, the manuscript's
  `8n`; its two ingredients are the exact form
  `|𝔗_cap| + 2(order−1)p = |𝔘_sp(G)| + δ·order·p + σ(G)`
  (`card_capacityTokens_add_internalMass`, the manuscript's
  `|𝔗_cap| = |𝔘_sp(G)| + 15p₁₃ + σ(G)`) and the internal-mass comparison
  `δ·order + 2 ≤ 4·order`, the manuscript's `15 ≤ 2·13`, now registered as
  `Data.joinSlack` beside `fanCapSlack` and `highCentreDeficitSlack` because it
  relates the registered baseline to the registered window order and nothing
  else.  `order·p ≤ n` is *derived* from the packing, not assumed.

  `𝔗_cap` is `Graph/CapacityTokenUniverse.lean`'s `capacityTokens`: the four
  constructors of `CapacityToken` are the manuscript's three summands with `𝔗_W`
  split into its two declared halves, and `CapacityToken.subtype` is `sub(t)` in
  the alphabet `def:same-token-blocker-roles` already declares.  `𝔗_R` is
  `remainderSurplusTokens`, one token per surplus unit of a remainder vertex, with
  `|𝔗_R| = σ_R`.  The two halves of `𝔗_W` are
  `Graph/WindowJoinIdentity.lean`'s `windowRemainderIncidences` and
  `crossWindowIncidences`, so a window–remainder edge contributes one token and a
  cross-window edge one token at each of its two window ends.

  `Θ_cap` is `Graph/CapacityTokenAssignment.lean`'s `capacityCharge`, the four
  cases in the manuscript's order, built from `Φ_can(π)` — the canonical first
  member of `def:surplus-blockers`' own `𝖡𝗅𝗄(π)`, by the same enumeration idiom
  `Graph/CanonicalSupportSelection` uses for "the lexicographically first …" —
  together with that blocker's declared support `supp(B)` and its primitive
  carrier `κ(B)`, both read clause by clause.  Case (c) carries the manuscript's
  cohort `𝒫_v`, the canonical pair order, the rank `rk_v(π)` and
  `j(π) = 1 + (rk_v(π) mod (d_G(v) − δ))`.  `Θ_cap` lands in `𝔗_cap`
  (`capacityCharge_mem_capacityTokens`) — the modulus is what keeps the third
  case's index inside the vertex's own range and `κ(B) ∈ 𝔘_sp(G)`
  (`carrier_mem_primitiveCarrier`) what keeps the fourth in the primitive
  summand.  Being a function into `Option`, it is single-valued by construction,
  and `canonicalLabel_eq_capacityCharge` shows the canonical ledger's declared
  order recovers it.

  `lem:token-ledger-no-overcount` is therefore
  `Graph/CanonicalFibreLedger`'s own fibre identity read at `Θ_cap`
  (`card_chargedPairs_eq_sum_load`), the *same*
  `card_chargedPairs_eq_sum_multiplicity` row 32 uses, now at the manuscript's own
  token universe instead of a quantified alphabet; nothing is re-implemented.  It
  is committed with the clause that makes it read at the whole blocked family
  (`chargedPairs_eq_of_blocked`), whose antecedents are the manuscript's own: the
  pair is blocked, and its canonical blocker has a primitive carrier.

  `def:same-token-patterns` is `tokenFibre`: `H_t` is the charge's own fibre, a
  family of two-element subsets of `𝒜₀`, and `e(H_t) = ℓ_cap(t)` is
  `card_tokenFibre_eq_pairMultiplicity`.

  **The third production is the ledger's existence, in ∀-form.** The row commits
  that at *every* `Graph.CapacityPresentation object data.windowOrder` — every
  valid packing of induced windows, every `DemandActivation`, every
  `CarrierPresentation` and every role reading `ρ_t` — the object's own charge is
  a `Graph.ObjectCapacityLedger` (`Graph.objectCapacityLedgerExists`).  Nothing
  is selected, so the commitment is a property of the object and not of a choice
  the node made.  The three obligations are the branch's own: node `[130]`'s pair
  count, read by exact key from `canonicalPairLedger`; `𝔗_cap ≠ ∅`
  (`capacityTokens_nonempty`), which is the primitive summand containing the
  vertex the branch's own positive surplus exhibits; and
  `lem:capacity-token-supply` in the unconditional form above.  The entropy
  budget is taken at the free side's own count with `sandwich := le_refl`, which
  is the sharpest reading of `prop:sparse-entropy-sandwich-with-blockers` and the
  only one that assumes no budget nobody supplied.
- **What it should do.** This.
- **Gap.** None.  Both displayed supply bounds are unconditional, the envelope
  they are spent against is proved here and committed as its own fact, and the
  bundled form nodes `[137]`–`[144]` read is discharged at every presentation.
  `rem:surplus-pair-sharp-frontier` remains unstated, as it was: its no-loss
  claim ranges over the exact frontier these rows build but the manuscript
  states it as a remark, not as a lemma with a proof to port.
- **Ledger and residual.** `factOnly` over the row-32 stage: refinement is
  `RefinementSystem.refl`, the residual is unchanged, all four prerequisites are
  read by exact key through `FactInputs.get` — `canonicalPairLedger`,
  `noProperBaseline`, `tightEndpoint`, `surplusAbove`, every one of them on the
  immutable node-`[19]` prefix — and `AtomicCT.run` appends the two productions
  while retaining the literal ancestry.  Ledger and Residual pass.
- **Transport and terminals.** Core owns the commit and the accounting; no EG
  code selects a token, an assignment, a partition or a terminal.  The new
  `Graph/SparseUpperEnvelope.lean` mentions no EG name, no paper label as a
  value and no unexplained constant, and quantifies over its baseline.  The
  operation is nonbranching and declares no terminal.  Transport passes.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:sparse-upper-envelope` | lem | `FiniteObject.localDegree`, `FiniteObject.localIncidences`, `FiniteObject.card_localIncidences`, `FiniteObject.card_localIncidences_erase`, `FiniteObject.card_localIncidences_le_of_degenerate`, `FiniteObject.edgeCount_add_two_le_of_noProperBaseline`, `FiniteObject.edgeCount_add_two_le` | standalone; from the row-3 and row-4 facts |
| `def:primitive-sparse-blocker-carrier` | def | `FiniteObject.primitiveCarrier`, `FiniteObject.incidences` | standalone |
| `lem:primitive-carrier-supply` | lem | `FiniteObject.card_primitiveCarrier`, `FiniteObject.primitiveCarrierSupply`, `FiniteObject.card_primitiveCarrier_le` | standalone |
| `def:window-remainder-surplus-split` | def | `FiniteObject.ambientSurplus`, `FiniteObject.crossWindowIncidences`, `FiniteObject.ambientSurplus_windowSupport_add_remainderSupport` | standalone |
| `lem:exact-window-join-identity` | lem | `FiniteObject.exact_window_join_identity` | standalone |
| `def:capacity-token-ledger` | def | `FiniteObject.CapacityToken`, `FiniteObject.capacityTokens`, `FiniteObject.remainderSurplusTokens`, `FiniteObject.capacityCharge` (with `canonicalBlocker`, `Blocker.declaredSupport`, `Blocker.carrier`, `remainderCohort`, `remainderRank`)<br>`Graph.CapacityPresentation`, `Graph.ObjectCapacityLedger`, `Graph.ObjectCapacityLedger.ofCapacityCharge`, `Graph.objectCapacityLedgerExists` | standalone |
| `lem:capacity-token-supply` | lem | `FiniteObject.card_capacityTokens_add_internalMass`, `FiniteObject.capacityTokenSupply`, `FiniteObject.card_capacityTokens_le`, `FiniteObject.capacityTokens_nonempty` | standalone |
| `lem:token-ledger-no-overcount` | lem | `FiniteObject.card_chargedPairs_eq_sum_load`, `FiniteObject.chargedPairs_eq_of_blocked` | standalone |
| `def:same-token-patterns` | def | `FiniteObject.tokenFibre`, `FiniteObject.card_tokenFibre_eq_pairMultiplicity` | standalone |
| `rem:surplus-pair-sharp-frontier` | rem |  |  |

`rem:surplus-pair-sharp-frontier`'s cell is empty: its no-loss claim ranges over
the exact frontier the three preceding rows now build, but the manuscript states
it as a remark and it is not proved.

`lem:sparse-upper-envelope` is filed here because this is where the proof first
needs it, and it is proved from the facts rows 3 and 4 already commit rather
than re-derived: `noProperBaseline` and `tightEndpoint` are reads, not
hypotheses.  It is a `[8]`–`[9]` consequence living at `[136]`, which is exactly
how the manuscript spends it.

**CT composition at this row.** No CT: one atomic fact-only Strategy.  The
manuscript's `[134]`–`[136]` is a supply count, a charge and a fibre identity; a
CT4 assignment and a CT9 fibre partition would decide nothing that
`Graph/CanonicalFibreLedger`'s single-valued charge does not already decide.
The envelope is a counting induction over the object's own vertex set, which is
a theorem rather than an execution, so it too owes no CT.


### Row 34 — Coupled homogeneous fibre pressure `[137]`–`[143]` (ported: `Spine.coupledFibrePressure`, `Spine.sparsePressureDichotomy`)

- **Paper fact.** `[137]` is the coupled single-graph high-load test.
  `lem:capacity-token-high-load` states
  `C(s,2) ≤ E_spine(n) + ((1/2)σ(G) + 1) log₂ n + L_max |𝔗_cap|` with
  `L_max := max_t ℓ_cap(t)`.  `def:same-token-blocker-roles` defines
  `ρ_t(π) = (type(B_π), class(t), sub(t))`, bounds the alphabet by
  `|𝔕_st| ≤ 6(2+1+3) = 36 =: Q_st`, and gives the fibre partition
  `ℓ_cap(t) = Σ_{r ∈ 𝔕_st} ℓ(t,r)`.  `lem:exact-surplus-pair-charge-partition`
  makes the whole pair schedule an exact disjoint union
  `C(𝒜₀,2) = Π_free ⊔ ⨆_C ⨆_{t ∈ 𝔗_C} ⨆_r Π_{t,r}`;
  `thm:sharp-classwise-homogeneous-token-budget` (a)–(e) reads the class split
  `B_W + B_R + B_P = |Π_blk| ≥ N_*(G)`, the class supplies
  `S_W + S_R + S_P ≤ 8n + σ(G)`, the classwise cap `B_C ≤ Cap_hom(L_C)S_C`, the
  budget inequality it sums to, and the forced pattern of size
  `ψ(N_*(G)/(Q_st(8n+σ(G))))`; `cor:quantified-homogeneous-class-overload`
  quantifies the overload `Ω_C = (B_C − A_C)_+` against `D_exc`;
  `cor:coupled-single-graph-overload-budget` and
  `cor:numerical-single-graph-budget` evaluate all three classes at the same
  `n, p₁₃, σ_W, σ_R` — this is what *coupled* means — and define
  `D_all = (N_*(G) − A_all)_+` with the slot count `36(4n + 15p₁₃ + 3σ(G))`;
  `prop:single-graph-sparse-pressure-routing` makes the node a branch: if the
  three geometric caps hold then `σ(G) ≤ R_L(n)` and the branch routes to
  `[138]`, otherwise `D_all > 0` and the forced role-homogeneous pattern's token
  class routes to `[140]`, `[142]` or `[143]`; and no graph remains at `[137]`.
  `thm:sharp-surplus-overload-audit` is the same accounting at the six subtypes
  `RW, WW, R, V, I, P`, and `cor:spine-lower-bound-surplus-estimates` converts
  the `[138]` lower-bound packages into the surplus estimate on the near-cubic
  route.
- **What the Lean does.** Two declarations of
  `Graph/Strategy/HomogeneousBottleneckRows.lean`.

  `coupledFibrePressureRow` is a `factOnly` Strategy with
  `Requires := [canonicalPairLedger, capacityTokenLedger]` and
  `Produces := [roleFibrePartition, fibrePressure]`.  Every read is spent.
  Node `[130]`'s pair count fixes `Π(𝒜₀)`; node `[136]`'s capacity-token ledger
  is what makes the high-load production provable at all, because that production
  is *existential* in the object's own ledger.  Nothing is quantified over a presentation nobody built: node `[136]`
  commits the ledger at **every** `Graph.CapacityPresentation`, so this row reads
  it at the presentation its own statement is quantified over rather than at one
  it chose.

  `sparsePressureDichotomy` is a `Decision` on
  `Graph.SparsePressureCapped`, producing `sparsePressureNearCubic` on the arm
  where every capacity ledger of the object respects the geometric caps and
  `sparsePressureOverload` on its complement.  The arm not taken is absent from
  the taken arm's key index: the three geometric class audits `[140]`, `[142]`,
  `[143]` and node `[144]` run only on the overload arm, while the capped arm is
  a separate exact ledger.  On the capped arm,
  `spineSurplusEstimateRow` reads the concrete certified ledger and commits the
  actual inequality `σ(G) ≤ C_sp⌈√n⌉`; the same shared theorem is read by
  `homogeneousSpineSurplusEstimateRow` on node `[144]`'s caps arm.  Both facts
  close against the incoming strict `surplusAbove` entry through Core's
  `closeIncompatible`.

  The mathematics is in two new proof-agnostic `Graph` modules.
  `Graph/GrainedTokenBudget.lean` proves the whole accounting once over an
  arbitrary finite grouping `grain` of the token universe, so the three classes
  and the six subtypes are two instances of one theorem family:
  `choose_two_eq_free_add_sum_roleFibre` is
  `lem:exact-surplus-pair-charge-partition`; `sum_grainLoad`,
  `sum_grainTokens_card`, `forcedDemand_le_blocked`,
  `grainLoad_le_of_no_homogeneous` and `forcedDemand_le_coupledCapacity` are
  `thm:sharp-classwise-homogeneous-token-budget` (a)–(d);
  `coupledExcess_le_sum_grainOverload`, `exists_grainOverload_ge` and
  `coupledExcess_le_grainOverload` are
  `cor:quantified-homogeneous-class-overload` (a), (b), (d);
  `coupledExcess_le_sum_roleFibreExcess` and `exists_overloaded_roleFibre` are
  `cor:coupled-single-graph-overload-budget` (a)–(c); `coupledCapacity_eq` and
  `slotCount_eq` are `cor:numerical-single-graph-budget`'s exact identities;
  `exists_forced_pattern` is `lem:capacity-token-high-load` with
  `cor:forced-homogeneous-same-token-scale`,
  `thm:sharp-classwise-homogeneous-token-budget` (e) and
  `thm:sharp-surplus-overload-audit` (d); `sparsePressureBound`,
  `demand_le_sparsePressureBound` and `sparsePressureAlternative` are
  `prop:single-graph-sparse-pressure-routing`; and
  `TokenLoad.demand_le_of_package` is
  `cor:spine-lower-bound-surplus-estimates` in exact finite form.

  `Graph/ObjectCapacityLedger.lean` fixes what node `[136]` commits.
  `CapacityPresentation` is `def:capacity-token-ledger`'s own declared data — a
  valid packing of induced windows, `def:active-surplus-demands`' activation,
  `def:declared-coordinate-signature`'s coordinate and shoulder-chord
  presentation, and `def:same-token-blocker-roles`' role reading — and
  `ObjectCapacityLedger` is *indexed* by it, with the token universe, the
  declared token order, `sub(t)` and the eligibility all derived from the
  presentation rather than carried as fields.  A ledger therefore cannot present
  a token universe that is not the object's own `𝔗_cap`: the abstract-token
  reading is not expressible.  Its four remaining fields are node `[130]`'s pair
  count, `𝔗_cap ≠ ∅`, the free-side entropy sandwich, and
  `lem:capacity-token-supply`'s supply bound, and `ofCapacityCharge` builds it
  from row 33's own `FiniteObject.capacityTokens`, `capacityTokenOrder`,
  `Charges` and `CapacityToken.subtype`, so nothing about the token universe is
  re-declared here.  The four statements `RoleFibrePartitionStatement`,
  `FibrePressureStatement`, `SparsePressureCapped` and
  `SparsePressureOverloadStatement` each quantify over the presentation as well
  as over the ledger — `∀` on the two tested halves, `∃` on the two exhibited
  ones — and are written out once and referenced both by the residual domain's
  value schema and by the row that proves them.  `sparsePressureRouting` is the
  exhaustiveness of the branch, and its two arms are the two cases of the
  excluded middle on `SparsePressureCapped`, so nothing is assumed to make the
  split exhaustive.

  Every manuscript display with a division is written multiplicatively —
  `ℓ(t,r) ≥ B_C/(Q_st S_C)` is `B_C ≤ Q_st · S_C · ℓ(t,r)` — and `(x)_+` is
  `Nat` subtraction, so no rounding convention is introduced.  `Q_st` is
  `Fintype.card SameTokenBlockerRoles.Role` and `L_geom` is
  `SameTokenBlockerRoles.geometricPatternBound` at a routing-label count; no
  numeral is written.
- **What it should do.** This is what it does.
- **Gap.** None.  Node `[136]`'s interface obligation is discharged: row 33
  commits `∀ declared : Graph.CapacityPresentation object data.windowOrder,
  Nonempty (Graph.ObjectCapacityLedger object data.threshold data.windowOrder
  declared)`, so this row's `∃`-productions are witnessed at the presentation
  they are stated at and its `∀`-tested half ranges over the same presentations.
  `Graph/Strategy/SurplusRun.lean` elaborates end to end, and
  `Hypostructure/Fixtures/SurplusRun.lean` runs the whole block over node
  `[19]`'s literal above-arm ledger.
- **Ledger and residual.** The fact-only row is `factOnly` over the
  node-`[136]` stage: the refinement is `RefinementSystem.refl`, the residual is
  unchanged, the three prerequisites are read by exact key through
  `FactInputs.get`, and `AtomicCT.run` appends the three productions while
  retaining the literal ancestry.  The branch is a `Decision` against that same
  literal ledger, so both arms extend one immutable prefix and neither can see
  the other's key.  Ledger and Residual pass.
- **Transport and terminals.** No EG code: the row lives in the framework's
  `Graph.Strategy` namespace, quantified over the residual domain's fact system
  and over the keys it produces, and the two new `Graph` modules mention no EG
  name, no paper label as a value and no unexplained constant.  The row
  transports nothing outside the one `ExactLedger`, names no producer or
  execution position, and the branch is the framework's own `Decision`, so the
  arm not taken leaves no key behind.  Transport passes.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:capacity-token-high-load` | lem | `CapacityTokenLedger.exists_forced_pattern`, `TokenLoad.exists_multiplicity_ge` | standalone |
| `cor:forced-homogeneous-same-token-scale` | cor | `CapacityTokenLedger.exists_roleFibre_pattern`, `PatternFamily.exists_matching_or_star_of_patternThreshold` | standalone |
| `cor:coupled-single-graph-overload-budget` | cor | `CapacityTokenLedger.coupledCapacity`, `coupledExcess`, `coupledExcess_le_sum_roleFibreExcess`, `exists_overloaded_roleFibre` | standalone |
| `cor:numerical-single-graph-budget` | cor | `CapacityTokenLedger.coupledCapacity_eq`, `slotCount_eq` | standalone |
| `prop:single-graph-sparse-pressure-routing` | pro | `CapacityTokenLedger.sparsePressureBound`, `demand_le_sparsePressureBound`, `sparsePressureAlternative`, `Graph.sparsePressureRouting`, `Spine.sparsePressureDichotomy` | standalone |
| `thm:tokenized-surplus-accounting-closure` | the | `TokenLoad.le_one_add_of_quadratic_le`, `TokenLoad.demand_le_of_bounded_load` | standalone (row 36) |
| `def:same-token-blocker-roles` | def | `SameTokenBlockerRoles.Role`, `card_role`, `card_tokenSubtype_eq_sum_classFibres`, `PatternFamily.roleFibre`, `CapacityTokenLedger.load_eq_sum_roleFibre` | standalone |
| `lem:exact-surplus-pair-charge-partition` | lem | `CapacityTokenLedger.choose_two_eq_free_add_sum_roleFibre` | standalone |
| `thm:sharp-classwise-homogeneous-token-budget` | the | `CapacityTokenLedger.sum_grainLoad`, `sum_grainTokens_card`, `forcedDemand_le_blocked`, `grainLoad_le_of_no_homogeneous`, `forcedDemand_le_coupledCapacity`, `exists_forced_pattern`, `classwise_split` | standalone |
| `cor:quantified-homogeneous-class-overload` | cor | `CapacityTokenLedger.grainOverload`, `coupledExcess_le_sum_grainOverload`, `exists_grainOverload_ge`, `coupledExcess_le_grainOverload` | standalone |
| `thm:sharp-surplus-overload-audit` | the | `CapacityTokenLedger.subtype_split`, `sum_grainLoad`, `sum_grainTokens_card`, `exists_forced_pattern` at `subtype` | standalone |
| `cor:spine-lower-bound-surplus-estimates` | cor | `TokenLoad.demand_le_of_package`, `Graph.surplus_le_of_package` | standalone |

`thm:tokenized-surplus-accounting-closure` is filed here because `[137]` is
where the manuscript invokes it, but the declarations that state it are read at
row 36 inside `cor:homogeneous-same-token-caps-close`; the column-4 entry is
row 36's.  `thm:sharp-classwise-homogeneous-token-budget` and
`thm:sharp-surplus-overload-audit` share their declarations because
`GrainedTokenBudget` proves them once over an arbitrary grouping and the two
theorems are the class and subtype instances.

**CT composition at this row.** None: one atomic fact-only Strategy and one
`Decision`.  The manuscript's `[137]` is an accounting identity followed by an
exhaustive two-way test, and the framework already owns both — `AtomicCT.run`
for the commit and `Decision.run` for the split — so registering a CT would
decide nothing that is not already decided.

### Row 35 — Finite bottleneck classification `[139]`–`[143]` (ported: `Spine.windowClassDichotomy`, `Spine.remainderClassDichotomy`, `Spine.windowIncidenceAudit`, `Spine.remainderSurplusAudit`, `Spine.primitiveCarrierAudit`)

- **Paper fact.** `[139]` and `[141]` are the two binary class tests —
  "token in `𝔗_W`?" and "token in `𝔗_R`?" — and `[140]`, `[142]`, `[143]` are the
  three geometric audits they dispatch to, one per token class:
  window-incidence, remainder-surplus, primitive-carrier.
  `prop:single-graph-sparse-pressure-routing` (b) is the dispatch itself,
  *"according to the class of the token, `G` is routed to node `[140]`, `[142]`,
  or `[143]`"*.  `lem:same-token-matching-star` supplies the combinatorics:
  `e(H) ≤ ν(H)(2Δ(H) − 1)`, hence "if `K ≥ 1` and `H` contains neither a matching
  of size `K` nor a star of size `K`, then `e(H) ≤ (K−1)(2K−3)`".
  `lem:same-token-homogeneous-extraction` refines a same-token `K`-pattern to a
  role-homogeneous one.  `def:homogeneous-token-charge` fixes `ψ(x)` — the least
  integer `k ≥ 0` with `x ≤ k(2k−1)` — and the cap charge
  `Cap_hom(L) := Q_st(L−1)(2L−3)`; `cor:quantitative-homogeneous-overload` is its
  quantitative form, `K_hom(G) ≥ ψ(N_*(G)/(Q_st(8n+σ(G))))`.
  `def:same-token-routing-germs` defines the routing support `Z(π;t,r)`, the
  connector germs from the primitive carrier of `t` to `T(p)` or `T(q)`, the
  *first separator*, the parallel case, and the finite routing-label alphabet of
  cardinality `Q_geom`, from which `thm:homogeneous-overload-geometric-closure`
  takes `L_geom = Q_geom + 1`.
- **What the Lean does.** Five declarations of
  `Graph/Strategy/HomogeneousBottleneckRows.lean`, and the block is now a branch
  rather than a single implication.

  `windowClassDichotomy` and `remainderClassDichotomy` are nodes `[139]` and
  `[141]`: two `Decision`s on `Graph.SparsePressureOverloadInClass` at
  `.windowIncidence` and at `.remainderSurplus`.  Each test is the excluded
  middle on a property of the object, so no fact is consumed to decide it and
  nothing is assumed to make the split exhaustive.  The arms are four distinct
  keys — `windowClassOverload`, `windowClassAbsent`, `remainderClassOverload`,
  `remainderClassAbsent` — so the arm not taken is absent from the taken arm's
  key index.

  `windowIncidenceAudit` and `remainderSurplusAudit` are nodes `[140]` and
  `[142]`: two instantiations of one `classAuditRow`, at `.windowIncidence` and
  `.remainderSurplus`.  Each produces its class's `Graph.ClassAuditStatement`
  together with `Graph.QuantitativeOverloadStatement`.  `Requires := []` is the
  honest declaration: both productions are theorems about the object, and an
  unread key would claim a dependency the executor does not have.  What places
  each audit at its class is the DAG — the arm it runs on carries that class's
  verdict — not a hypothesis inside it.

  `primitiveCarrierAudit` is node `[143]`, the fall-through, and the only one of
  the three that owes a derivation.  It reads `sparsePressureOverload`,
  `windowClassAbsent` and `remainderClassAbsent` by exact key and spends all
  three in `Graph.overloadClassExhaustive`: `class(t)` has three values, so
  failing both tests puts the overloading token in `𝔗_prim`.  It therefore
  produces its own class verdict `primitiveClassOverload` beside the audit and
  the scale.

  **The audits are verdicts, not implications.**  `ClassAuditStatement` is stated
  at `Graph.ObjectCapacityLedger` — the object's own capacity-token ledger, whose
  token universe is pinned to `𝔗_cap` and whose existence node `[136]` commits at
  every `Graph.CapacityPresentation` since row 33 was finished.  The retired
  statement quantified instead over an arbitrary `Token` type with an arbitrary
  order, subtype and eligibility, so it said nothing about the branch's object;
  that reading is now not expressible.

  **`L_geom` is one number, registered rather than quantified.**  The bound is
  `SameTokenRoutingGerms.patternBound` at
  `RoutingLabel data.BoundaryProfile data.WindowLabel`: `Fintype.card` of the
  set `ρ_t` lands in, plus one, at the two alphabets the presentation
  registers.  The manuscript's *"These
  labels form a finite set; denote its cardinality by `Q_geom`"* is a statement
  about the registered declared-coordinate signature, not about any one object,
  so the alphabet is a `Data` field beside the window order — and it has to be,
  because quantifying it at the node puts `[140]`--`[144]` at the wrong
  threshold: at an empty alphabet `L_geom` degenerates to `1`, and a
  `1`-matching is a single edge.  A presentation builds the type with
  `SameTokenRoutingGerms.RoutingLabel` at its own two declared alphabets, which
  is what `Problem.lean` does; no numeral is written and no `Nat` parameter
  stands in for `Q_geom`.

  `cor:quantitative-homogeneous-overload` is
  `CapacityTokenLedger.exists_homogeneous_pattern_of_share` read at the object:
  a share `q` that the `Q_st|𝔗_cap|` slots must absorb is realized by some role
  fibre, `PatternFamily.patternThreshold_mono` carries `ψ` across, and the
  pattern `cor:forced-homogeneous-same-token-scale` produces has at least `ψ(q)`
  edges.  The display is multiplicative, so no division and no rounding
  convention is introduced, and the denominator is the manuscript's because the
  ledger carries `lem:capacity-token-supply`.

  `PatternFamily.card_le_capCharge` is the manuscript's sentence: it charges each
  of the `Q_st` role fibres by `card_le_of_no_matching_no_star` and sums
  `card_eq_sum_roleFibre`.  `Cap_hom` is
  `SameTokenBlockerRoles.homogeneousCapCharge`, definitionally
  `PatternFamily.capCharge (Fintype.card Role)`.  `ψ` is
  `PatternFamily.patternThreshold`, defined by the manuscript's characterizing
  property rather than its closed form, with `le_patternThreshold_mul` and
  `patternThreshold_le` as its two halves.
- **What it should do.** This.
- **Gap.** One, and it is row 36's to close: the routing germs of `Z(π;t,r)` are
  not constructed anywhere, so `lem:same-token-bottleneck-routing` — stated at
  row 36 — is never applied.  `Graph/SameTokenRoutingGerms.lean` supplies
  everything around it: `routingSupport` generates `Z(π;t,r)` as the (D8) product
  of the six declared entries, `RoutingGerm` is the declared connector germ from
  the primitive carrier of `t` to a selected port support, `firstSeparator`,
  `Parallel` and `parallel_or_firstSeparator` are the germ dichotomy, and
  `exists_same_routingLabel` is the opening pigeonhole.  What is missing is the
  extraction of two germs from the two same-label demands the pigeonhole
  produces.

  `cor:quantitative-homogeneous-overload`'s two asymptotic tails — the `A√n` and
  `αn` consequences (a) and (b), each stated "for `n` sufficiently large in terms
  of `A` and `C_E`" — are not stated.  They are consequences of the displayed
  bound at the branch that supplies those rates, in the same way row 32 leaves
  the asymptotic tail of `prop:sparse-entropy-sandwich` to row 45.  The displayed
  bound itself, which is what the manuscript spends here, is committed.
- **Ledger and residual.** `factOnly` over the arm each audit runs on: refinement
  is `RefinementSystem.refl`, the residual is unchanged, and `AtomicCT.run`
  appends the productions while retaining the literal ancestry.  Node `[143]`'s
  three prerequisites are read by exact key through `FactInputs.get`, all three
  on its own immutable prefix.  The two dichotomies are `Decision`s against the
  literal node-`[137]` overload ledger, so all three arms extend one immutable
  prefix and none can see another's key.  Ledger and Residual pass.
- **Transport and terminals.** `[140]`, `[142]` and `[143]` are now three arms a
  router selected, not three instances of one universally quantified statement:
  the exact successor ledgers are the near-cubic, window-bottleneck,
  remainder-bottleneck and primitive-bottleneck branches, and
  `Hypostructure/Fixtures/SurplusRun.lean` checks that each arm carries its own
  verdict and audit and that the window arm's index omits the other two audits.
  No EG code, no payload, no terminal, no routing helper: the branch is the
  framework's own `Decision`.  **Transport passes.**

  What is *not* a gap, and was in the retired implementation: the coarse code is
  the manuscript's own alphabet rather than an ordered vertex pair, the capacity
  is `Cap_hom` rather than a uniform constant, and the matching--star bound is
  proved rather than asserted —
  `Fixtures.HomogeneousTokenBottleneck.matching_star_sharp` computes that it is
  attained with equality at the triangle, so the coefficients `(L−1)(2L−3)` carry
  no slack, and `patternThreshold_three` computes `ψ(3) = 2` against both halves
  of its minimality.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `prop:single-graph-sparse-pressure-routing` (b), the class dispatch | pro | `Graph.SparsePressureOverloadInClass`, `Graph.overloadClassExhaustive`<br>`Spine.windowClassDichotomy`, `Spine.remainderClassDichotomy` | standalone; the routing half is row 34's |
| `lem:same-token-matching-star` | lem | `PatternFamily.card_le_matching_mul_two_mul_degree_sub_one`, `PatternFamily.card_le_of_no_matching_no_star`, `PatternFamily.exists_matching_or_star_of_lt_card` | standalone |
| `lem:same-token-homogeneous-extraction` | lem | `PatternFamily.exists_homogeneous_matching`, `PatternFamily.exists_homogeneous_star`, `PatternFamily.exists_large_roleFibre` | standalone |
| `def:homogeneous-token-charge` | def | `PatternFamily.capCharge`, `PatternFamily.patternThreshold`, `PatternFamily.le_patternThreshold_mul`, `PatternFamily.patternThreshold_le`, `PatternFamily.patternThreshold_mono`, `SameTokenBlockerRoles.homogeneousCapCharge`, `SameTokenBlockerRoles.homogeneousCapCharge_eq_capCharge` | standalone |
| `cor:quantitative-homogeneous-overload` | cor | `CapacityTokenLedger.exists_homogeneous_pattern_of_share`<br>`Graph.QuantitativeOverloadStatement`, `Graph.quantitativeOverloadStatement` | standalone; the displayed bound only |
| `cor:forced-same-token-scale` | cor | `PatternFamily.exists_matching_or_star_of_patternThreshold` | standalone (row 34) |
| `def:same-token-routing-germs` | def | `SameTokenRoutingGerms.routingCoordinate`, `.routingSupport`, `.routingSupport_eq`<br>`.RoutingGerm`, `.GermPair`, `.GermPair.dichotomy`, `.commonPrefix`, `.Diverges`, `.firstSeparator`, `.EnteredTogether`, `.Parallel`, `.parallel_or_firstSeparator`<br>`.PortStatus`, `.portStatus`, `.chordSetFlag`, `.pairDemands`, `.RoutingLabel`, `.pairRoutingLabel`, `.labelBound`, `.patternBound`, `.geometricLabelBound`, `.geometricPatternBound`, `.exists_same_routingLabel`, `.exists_same_pairRoutingLabel` | standalone |
| the three audits `[140]`, `[142]`, `[143]` | — | `Graph.ClassAuditStatement`, `Graph.classAuditStatement`<br>`Spine.classAuditRow`, `Spine.primitiveCarrierAuditRow` | standalone |

`cor:forced-same-token-scale` is filed here because it quantifies the same
pattern caps, but the declaration that states it is consumed at row 34 inside
`cor:forced-homogeneous-same-token-scale`; the column-4 entry is row 34's.  Both
halves of `def:homogeneous-token-charge` are present.
`def:same-token-routing-germs`' cell names the *whole* definition, not only its
label alphabet: `Z(π;t,r)`, the germs, the first separator and the parallel case
are all declared, which is why `L_geom` is a counted quantity here.

**CT composition at this row.** None: two `Decision`s and three atomic fact-only
Strategies.  The manuscript's `[139]`--`[143]` is a two-step case split on
`class(t)` followed by one combinatorial audit run at each class, and the
framework already owns both — `Decision.run` for the splits and `AtomicCT.run`
for the commits — so registering a CT would decide nothing that is not already
decided.  The retired `Graph.Strategy.SurplusAccounting.bottleneck` registration,
which composed CT9 → CT14 → CT10 → CT6, is this row's old path and is deleted in
this change; its whole module was already orphaned, importing eight
`Core.Strategy` modules that no longer exist, so nothing live could reach it.

### Row 36 — Homogeneous bottleneck `[144]` (ported: `Spine.homogeneousCapsDichotomy`, `Spine.homogeneousBottleneckPattern`, `Spine.bottleneckRouting`, `Spine.homogeneousBottleneck`)

- **Paper fact.** `[144]` is `thm:homogeneous-overload-geometric-closure` with
  `lem:same-token-bottleneck-routing`,
  `cor:homogeneous-same-token-caps-close` and
  `prop:nonnear-cubic-sharp-overload-routing`.
  `lem:same-token-bottleneck-routing`: if a role-homogeneous same-token matching
  or star in `H_{t,r}` has more than `Q_geom` edges, then "(a) a sparse surplus
  exit occurs; or (b) the support produces a decorated Type B handoff fan
  envelope, hence is routed to the Type B fan ledger".  With
  `L_geom := Q_geom + 1`, `thm:homogeneous-overload-geometric-closure` concludes
  that every role-homogeneous same-token `L_geom`-matching or `L_geom`-star in
  the three token classes realizes one of those two, and that on the subbranch
  where sparse exits are absent and all decorated Type B handoff data have been
  routed into the Type B fan ledger, the fixed caps `L_W = L_R = L_P = L_geom`
  hold, whence `σ(G) = O(√n)` and `m = (3/2)n + O(√n)`.
  `cor:homogeneous-same-token-caps-close` is the implication from clauses
  (a),(b),(c) to `σ(G) = O(√n)`, its proof forming
  `M₀ := max{Cap_hom(L_W), Cap_hom(L_R), Cap_hom(L_P)}`, using the role-fibre
  partition `ℓ_cap(t) = Σ_r ℓ(t,r) ≤ Q_st(L−1)(2L−3)`, and invoking
  `thm:tokenized-surplus-accounting-closure`.
  `prop:nonnear-cubic-sharp-overload-routing` is the exhaustive outcome:
  "(a) `G` satisfies the near-cubic spine estimate `σ(G) = O(√n)`; (b) a sparse
  surplus exit occurs; or (c) a role-homogeneous same-token bottleneck produces
  decorated Type B fan data and is routed to the Type B fan ledger."
- **What the Lean does.** Declarations in
  `Graph/ObjectCapacityLedger.lean` and
  `Graph/Strategy/HomogeneousBottleneckRows.lean` implement the live part of the
  node.  The node is a branch and its ledger flow and paper conclusions are
  exact.

  `homogeneousCapsDichotomy` is `[144]`'s test: a `Decision` on
  `Graph.HomogeneousCapsHold`, the subbranch hypothesis itself — *no* capacity
  token of the object, at *any* declared presentation, supports a
  role-homogeneous same-token `L_geom`-matching or `L_geom`-star.  It is a
  property of the object, so the split is the excluded middle on it
  (`Graph.homogeneousCapsRouting`) and nothing is assumed to make it exhaustive.
  The two arms are two keys, `homogeneousCapsHold` and
  `homogeneousBottleneckPattern`, so neither can read the other.

  `homogeneousBottleneckRow` runs on the caps arm and closes the branch with
  `prop:nonnear-cubic-sharp-overload-routing` (a).  Its production is
  `Graph.HomogeneousCapsCloseStatement`, four conjuncts at the object's own
  `Graph.ObjectCapacityLedger` and at every declared presentation:
  `ℓ_cap(t) ≤ M₀` at every token, `|Π_blk| ≤ M₀|𝔗_cap|`,
  `σ(G) ≤ 1 + 2M₀ + ⌊√(2E + 2M₀·scale)⌋`, and the edge-count half
  `2m ≤ δn + (1 + 2M₀ + ⌊√(2E + 2M₀·scale)⌋)`.

  **Nothing is a parameter any more.**  `M₀` is `Cap_hom(L_geom)` at the
  registered routing-label alphabet — `SameTokenRoutingGerms.patternBound` at
  `Data.RoutingLabel`, which is `Fintype.card` of the alphabet plus one — so the
  manuscript's `max{Cap_hom(L_W), Cap_hom(L_R), Cap_hom(L_P)}` is that one
  number, exactly as the theorem's `L_W = L_R = L_P = L_geom` says.  Registering
  the alphabet is what makes the test the manuscript's: quantified over
  alphabets, `[144]` would split at `L_geom = 1` — "every role fibre is empty" —
  instead of at `Q_geom + 1`.
  `scale` is `lem:capacity-token-supply`'s own bound, carried by the ledger
  (`tokens_card_le`), not supplied.  And clauses (a),(b),(c) are *facts a
  predecessor established*: the caps arm's own key.  Both reads are spent — the
  caps fact discharges the clauses, and node `[126]`'s `lem:sparse-slack-surplus`
  turns `σ(G) = O(√n)` into `m = (3/2)n + O(√n)` through `2m = δn + σ(G)`.

  `Graph/SameTokenBottleneckRouting.lean` is new and states *and applies*
  `lem:same-token-bottleneck-routing`.  Two of the manuscript's three proof
  steps are discharged there in its own order.  `exists_routed_demands` is the
  step after the pigeonhole -- *"if `𝓜` is a star, choose the two noncentral
  endpoints of `π₁` and `π₂`; if `𝓜` is a matching, choose an endpoint from each
  edge; in both cases we obtain two distinct selected surplus demands"* -- with
  both readings discharged at the pattern `cor:forced-same-token-scale`
  produces: a matching's two edges are disjoint, and a star's two edges share
  only the centre.  `RoutedBottleneck` is the routed configuration
  `def:same-token-routing-germs` declares -- the two germs, their first
  separator, the switch support's reading and the two separated tails -- and
  `RoutedBottleneck.outcome` is the lemma at it.

  The bottleneck arm of `[144]` now carries the failed-cap alternative as a
  positive ordinary fact, not as a raw negation:
  `Graph.HomogeneousBottleneckPatternStatement` states that some certified
  capacity-token ledger has a token and role supporting a role-homogeneous
  same-token `L_geom`-matching or `L_geom`-star.  The theorem
  `Graph.homogeneousBottleneckPatternStatement_of_not_caps` proves this from
  the failed `Graph.HomogeneousCapsHold` test, and
  `Spine.homogeneousCapsDichotomy` appends it as
  `Spine.homogeneousBottleneckPattern`.

  `Spine.bottleneckRoutingRow` now declares
  `Spine.homogeneousBottleneckPattern` as a prerequisite and reads it by
  `FactInputs.get`.  Together with `selection`, `uncompressible`, and
  `sparseSurplusSurvivor`, also read by exact key, it is passed to
  the row's local proof before it commits `Graph.BottleneckRoutingStatement`
  and `Graph.TypeBHandoffStatement`, the
  universal readings of `thm:homogeneous-overload-geometric-closure` at every
  declared routed bottleneck of the object.

  `ρ_t` is built.  `def:same-token-routing-germs`' routing label is
  `SameTokenRoutingGerms.pairRoutingLabel`, the seven coordinates in the
  definition's own order, **every one of them a function of the pair**: the
  pair's two demands `p, q` are its own two members in the object's enumeration
  order (`pairDemands`, the same idiom `canonicalBlocker` uses), so the two port
  statuses are `T(p)`'s and `T(q)`'s through `portStatus` — which is
  `lem:sparse-port-activation`'s own open/triangular dichotomy on the ports' own
  shoulders — and the two boundary-degree profiles are theirs.  `sub(t)` is the
  token's constructor and the suppressed-chord flag is `chordSetFlag` on the
  pair's canonical blocker, true exactly on clause (f).  The role and the two
  alphabet readings are the declared maps the signature and the `P₁₃` labelling
  supply.

  Reading the profiles off the pair is what makes the label load-bearing:
  `lem:same-token-bottleneck-routing` spends a collision for exactly two
  consequences — *"the same blocker type"*, carried by the role because
  `def:same-token-blocker-roles` makes `r = (type(B_π), class(t), sub(t))`, and
  *"the same boundary-degree fibre"* — the token and its subtype being free
  inside `Π_{t,r}`.  `exists_same_pairRoutingLabel` is the manuscript's
  pigeonhole at that label, so `Q_geom` is the cardinality of the set `ρ_t`
  lands in.  `Data` registers the two declared alphabets and `Problem.lean`
  supplies them.

  The absorbed classification is spelled out, not parameterised.  Its third
  alternative — *"context-universality holds only after adjoining a larger
  connected support"* — is `SameTokenRoutingGerms.Delocalizes`, which is exactly
  `SparseSurplusExit.delocalization`'s own data, and
  `sparseSurplusExit_of_delocalizes` turns it into that exit.  A free
  proposition here would be satisfiable by `True` and would make the whole
  absorbed case vacuous; it is not one.

  **The absorbed classification is a sparse surplus exit, and at a survivor it
  cannot occur.**  `sparseSurplusExit_of_absorbed` discharges all three of its
  readings where `def:named-surplus-exits` puts them, and none of the three is a
  route invented here.  *Target-defect* is **refuted, not converted**:
  `lem:context-universality` enters as the ledger invariant recorded in
  `Graph/ColdFirstFailure.lean` — *"every identification survives every
  compatible outside context"* — which is the manuscript's
  *"Thus the parallel case is impossible in a
  survivor."*  *Target-complete* is clause (c) by
  `sparseSurplusExit_of_targetComplete`.  *Delocalization* is clause (d) by its
  own constructor.

  `RoutedBottleneck.typeBHandoff` is then the manuscript's own conclusion,
  *"Thus every surviving separated case enters the Type B fan ledger"*: node
  `[125]`'s standing survival fact refutes the absorbed case outright, so the
  separator survives, `d_G(z) ≥ 4`, and the separated tails are admissible
  decorated Type B handoff fan data.

  All three absorbed alternatives are now accounted for.
  `sparseSurplusExit_of_delocalizes` is clause (d) by its own constructor, and
  `sparseSurplusExit_of_targetComplete` is clause (c): every one of
  `CompressibleSupport`'s seven fields is present and none is assumed —
  connectedness and properness are `S_z`'s own witnesses, the replacement is the
  reading's compressed realization, its profile is the atom's own by the
  reading's registration, the strict decrease is
  `SwitchReading.lexicographicallySmaller` derived from the reading's descent
  exactly as `ColdCorridor.BoundedGerm` derives it from its increment, and the
  context clause is the target-completeness read against the atom's own piece
  because `baseIsPiece` says the realization before the identification *is* that
  piece.

  Nothing else in the routed configuration is a free parameter either.
  `RoutedBottleneck` no longer carries the object's avoidance, its
  uncompressibility or the window-freeness of the germs' support: the first two
  are **read from the ledger** by `bottleneckRoutingRow`, whose
  `Requires := [selection, uncompressible]` are both spent — the node-`[1]`--`[4]`
  selection entry supplies `dyadicSafe`, and node `[11]`--`[14]`'s
  `cor:uncompressible` entry supplies the admissibility clause *at the ledger's
  own predicate* — and the third is pinned to `Graph.InducedPathFree` at the
  registered window order rather than left as a predicate a caller could take to
  be `True`.  So the arm's `bottleneckRouting` fact is the manuscript's first
  assertion with no assumption behind it.  Its three steps are each already owned
  and are composed rather than rebuilt: the opening pigeonhole is
  `exists_same_routingLabel_of_geometricPatternBound` at the counted alphabet;
  the germ dichotomy is `DecoratedHandoff`'s `absorbed_or_surviving`; and the
  reading of each configuration is `DecoratedHandoff.Absorbed` — target-defective,
  target-complete on a proper support, or complete only after adjoining a larger
  connected support, which are the manuscript's quotient, compression and
  delocalization exits — against `four_le_degree_of_surviving` (`d_G(z) ≥ 4`),
  `envelopeOfSeparation` and `admissible_of_envelope`.  `bottleneckRouting`
  concludes: absorbed, or the separator survives with degree at least `4` and its
  separated tails are an admissible decorated Type B handoff fan envelope.  The
  separated half of the argument is the *same* configuration Type A exit `(7)` is
  made of, so it is read off `Graph/DecoratedHandoffEnvelope.lean`, not
  duplicated at the token.

  `Fixtures.HomogeneousTokenBottleneck` still evaluates the arithmetic at a
  presentation with three active demands whose blocked set is the triangle, and
  `Hypostructure/Fixtures/SurplusRun.lean` checks that `[144]`'s two arms are
  disjoint — the caps arm carries `homogeneousCapsHold` and the near-cubic close,
  the bottleneck arm carries neither — and that the block is *entered* by the
  spine: the fixture checks that node `[19]`'s above-arm ledger is the one
  continued through `[125]`--`[144]`, while every sibling arm keeps its own exact
  branch index.
- **What it should do.** Split on the fixed homogeneous caps.  The caps arm
  proves the near-cubic estimate and closes against the incoming
  `surplusAbove` fact.  The complementary arm records the positive homogeneous
  pattern and publishes the manuscript's routed bottleneck facts as ordinary
  ledger entries.  Every upstream fact remains in the same exact history; row
  36 does not introduce any side object or separate result.
- **Gap.** None for the near-cubic arm: `SpineAssembly` registers
  `surplusAbove` and `spineSurplusEstimate` as incompatible ordinary keys, so
  `closeIncompatible` closes that oval outcome on the same residual.  The
  bottleneck arm is ledger content as well: `homogeneousBottleneckPattern` is
  the positive failed-cap fact, and `bottleneckRouting` is appended after
  reading `selection`, `uncompressible`, `sparseSurplusSurvivor`, and
  `homogeneousBottleneckPattern` by exact key.

  What is *not* a gap, and was in the retired implementation: the census is the
  token ledger rather than `V(G)` — `boundedMembers` used to be the vertex set,
  giving `n·M₀` where the paper has `M₀|𝔗_cap|` — and `boundedLowerMass` is
  `ℓ_cap(t)` rather than `(d(v)−3)(σ−1)`, so the identity the closure spends is
  `|Π_blk| = Σ_t ℓ_cap(t)` rather than the unrelated `σ(σ−1)`.  The `Nat.sqrt`
  step is the same correct argument it always was, applied to the manuscript's
  own inequality.
- **Ledger and residual.** `factOnly` over the caps arm: refinement is
  `RefinementSystem.refl`, the residual is unchanged, both prerequisites are read
  by exact key through `FactInputs.get` — the arm's own caps fact and node
  `[126]`'s slack identity, both on the immutable prefix — and `AtomicCT.run`
  appends the production while retaining the literal ancestry.  The near-cubic
  production then closes by the framework incompatibility between
  `surplusAbove` and `spineSurplusEstimate`.  The bottleneck
  arm's `bottleneckRoutingRow` reads `selection`, `uncompressible`,
  `sparseSurplusSurvivor`, and the positive `homogeneousBottleneckPattern` by
  exact key before appending `bottleneckRouting`.  The dichotomy is a `Decision`
  against that same literal ledger, so both arms extend one immutable prefix.
  Ledger and Residual pass.
- **Transport and terminals.** `[144]`'s outcomes are arms, not conjuncts:
  the exact successor ledgers are the near-cubic route of
  `prop:single-graph-sparse-pressure-routing` (a), and, over each of the three
  geometric audits, the capped close and the bottleneck.  No EG code, no payload,
  no routing helper, no closing callback; the branch is the framework's own
  `Decision`, and the arm not taken leaves no key behind.  Transport passes.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:same-token-bottleneck-routing` | lem | `SameTokenRoutingGerms.exists_same_routingLabel_of_patternBound`, `.exists_routed_demands`, `.RoutedBottleneck`, `.RoutedBottleneck.outcome`, `.bottleneckRouting`<br>`DecoratedHandoff.absorbed_or_surviving`, `.Absorbed`, `.four_le_degree_of_surviving`, `.envelopeOfSeparation`, `.admissible_of_envelope`<br>committed by `Graph.BottleneckRoutingStatement`, `Graph.TypeBHandoffStatement`; positive forced pattern committed by `Graph.HomogeneousBottleneckPatternStatement`, `Graph.homogeneousBottleneckPatternStatement_of_not_caps` | standalone and committed by `Spine.bottleneckRoutingRow` |
| `thm:homogeneous-overload-geometric-closure` | the | first assertion: `Graph.BottleneckRoutingStatement`, `Graph.bottleneckRoutingStatement`, committed on the bottleneck arm<br>second assertion: `Graph.HomogeneousCapsHold`, `Graph.HomogeneousCapsCloseStatement`, `Graph.homogeneousCapsCloseStatement`, `CapacityTokenLedger.caps_close_at_geometricBound` | standalone |
| `cor:homogeneous-same-token-caps-close` | cor | `CapacityTokenLedger.caps_close`, `TokenLoad.card_assigned_le_mul_of_multiplicity_le`, `TokenLoad.demand_le_of_bounded_load`, `TokenLoad.le_one_add_of_quadratic_le` | standalone |
| `cor:same-token-pattern-caps-close` | cor | `PatternFamily.card_le_of_no_matching_no_star`, `TokenLoad.demand_le_of_bounded_load` | standalone |
| `prop:nonnear-cubic-sharp-overload-routing` | pro | `Graph.homogeneousCapsRouting`, `Spine.homogeneousCapsDichotomy`, `Spine.bottleneckRoutingRow`, exact surplus branch ledgers | standalone; the caps and positive-pattern arms are exact |

`thm:homogeneous-overload-geometric-closure` now carries the cap-close
assertion and the universal routed-bottleneck reading.  The failed-cap arm also
commits the positive homogeneous pattern fact at the counted
`L_geom = Q_geom + 1`.  `Spine.bottleneckRoutingRow` consumes that pattern
together with the inherited survivor and uncompressibility facts and proves
the two universal routing statements.  No
concrete routed-bottleneck existence claim is part of those statements.  The
exhaustiveness of the ledger arms is the excluded middle on the caps, which is
a property of the object and not an invented proposition.

**CT composition at this row.** None: one `Decision` and one atomic fact-only
Strategy.  The manuscript's `[144]` is an exhaustive test followed by an
arithmetic closure, and the framework already owns both — `Decision.run` for the
split and `AtomicCT.run` for the commit.  The retired
`Core.Strategy.HomogeneousBottleneck` registration composed nine CT stages, five
of which were vacuous as registered; it and `Fixtures/HomogeneousBottleneck.lean`
were already gone, and `Graph.HomogeneousBottleneckStatement` — the last piece of
that path, the version quantified over an arbitrary token universe — is deleted
in this change together with the `presented` adapter that only it used.

### Row 37 — Support-complement normalization `[25]`–`[27]`

- **Paper fact.** `sec:remainder` fixes `W = ⋃_{P∈𝒫} V(P)` and `R = G − W` and
  asserts three things about it.  `[25]`/`[26]`: `R` is *large*,
  `|R| ≥ 0.83489768623… n − o(n)`, cited from the near-cubic window-only part of
  `prop:p13-density` (node `[24]`, row 10); equivalently `|R| = (1 − 13θ)n − o(n)`
  with `|W| = 13p₁₃` and `θ = p₁₃/n`.  `[26]`: "by the maximality of `𝒫`, the
  graph `R` contains no induced `P₁₃`, since any such copy would extend `𝒫`;
  hence every component of `R` is `P₁₃`-free".  `[27]`: "no component of `R`
  contains a subgraph of minimum degree at least `3`" — proved by passing
  `H ⊆ R` with `δ(H) ≥ 3` to `G[V(H)]`, which is `P₁₃`-free, and applying
  `thm:p13free` to get a power-of-two cycle of `G`.  `def:internal-3-core` names
  the negated conclusion: the internal `3`-core of `X` is empty iff no nonempty
  subgraph of `X` has minimum internal degree at least `3`.
- **What the Lean does.** `SupportComplementNormalization.Profile.execution` is
  `profile.obstruction.throughAvoidance.compose profile.core.execution`, where
  `throughAvoidance = (partition.execution.compose mass.execution).compose
  obstruction.execution`; the four adapters are `CTAdapters.ct9`, `ct14`, `ct1`,
  `ct6` in that order.  The profile is built by `Profile.ofRegistrationAt` from
  the single registration
  `NormalizationRank.inducedPathSupportComplementRegistration`.  Read off that
  registration's fields: `AmbientItem := ULift object.Vertex`,
  `ambientSupport := liftedVertices object`, `cover residual window :=
  (InducedPathMaximalPacking.support object order window).toList.map ULift.up`,
  and `Failure residual complement piece := HasInternalCore object baseline
  (SupportComponents.Connected.members object (supportOfComplement object
  complement) piece.down)`, where `HasInternalCore object baseline support :=
  ∃ core ⊆ support, core.Nonempty ∧ baseline ≤ (object.induce core).minDegree`.
  The compiler reads the selected packing and the surviving row-10 density cap
  from typed queries on the literal predecessor.  The cap is a
  `FiniteDensityBudget.CapLedger` required by `StrategyKey.requirements` and
  retained inside the sealed `NormalizedSupportCapability`; it is not a
  registration field.  The cover size is residual data: the graph registration
  sets `coverCard := presentation.order.read`, and
  `InducedPathMaximalPacking.support_card` proves the actual support has that
  size.  Core's `covered_card_eq_sum_cover_length` proves the disjoint-union
  cardinality from packing compatibility and structural cover laws.
  `ExactLedger` therefore publishes `partitionExact`, `selectedUniform`, and
  `complementExact`: `selectedCount + complementCount = ambientCount`,
  `selectedCount = coverCard * packingCount`, and
  `coverCard * packingCount + complementCount = ambientCount`.  For the graph
  registration these are exactly `|W| = 13p₁₃` and `|R| + 13p₁₃ = n`, with
  `13` read from the residual presentation rather than hardcoded in Core.

  The qualitative declarations are
  `NormalizationRank.exactInducedPathComponent_free`, whose conclusion is
  `Graph.InducedPathFree ((presentation.object.read …).induce (members … piece))
  (presentation.order.read …)` under the hypothesis
  `exact.output.fst.snd.terminal = .avoiding`; and
  `NormalizationRank.exactInducedPathComponent_emptyInternalCore`, whose
  conclusion is `¬ HasInternalCore … (members … piece)` under
  `exact.output.snd.terminal = .activeLedger` plus scheduled membership of the
  piece.  The `[27]` derivation is Core-owned: the registration's
  `failureForcesTarget` takes a failing piece plus CT1's avoidance of every
  complement-supported occurrence, extracts `core` with
  `baseline ≤ (object.induce core).minDegree`, and calls
  `presentation.componentFreeForcesTarget` — the manuscript's `thm:p13free`
  route, not minimality.  `componentFreeForcesTarget` is the generic graph
  presentation's HSS bridge already audited at row 6.  CT14's lower mass is
  computed internally from the same packing and cover; no application-supplied
  mass theorem enters the CT.
- **What it should do.** This is now the implementation: normalize the literal
  packing support, publish the exact partition and uniform-cover identities,
  retain the inherited density-cap ledger, prove maximality gives componentwise
  induced-`P₁₃`-freeness, and prove every remainder component has empty
  internal `3`-core.
- **Gap.** None at this row.  The displayed decimal is the paper's evaluation
  of the row-10 density bound, not a fresh constant introduced at normalization.
  Lean retains that exact upstream cap beside the stronger exact identity
  `|R| + 13p₁₃ = n`; no decimal or proof-specific constant is hardcoded here.
- **Ledger and residual.** The compiler builds the profile with
  `Profile.ofRegistrationAt registration current packingQuery`.  The packing,
  row-10 cap, graph, and order are all read through predecessor ledger/residual
  queries; no exact-predecessor unfolding reconstructs them.  CT9's extension is
  `Ledger.Extension Previous execution.Output`; CT14 runs on
  `partition.AfterPartition`, CT1 on `ObstructionProfile.AfterMass`, CT6 on
  `CoreProfile.AfterAvoidance`, each the literal extension of the previous.
  `Profile.ExactOutput` retains the four predecessor equalities
  (`partitionPrevious`, `massPrevious`, `obstructionPrevious`, `corePrevious`),
  and `RoutedResidual.normalized` carries the complete output plus all four
  terminal equalities.  `ExactLedger.summary`, `partitionExact`,
  `selectedUniform`, and `complementExact` are queries over that literal CT
  output.  `ExactLedger.comap` and the bundled `CapLedger.comap` preserve them
  through later stages.  Predecessor and residual are retained.  The ledger
  now also publishes `ExactLedger.complementMembership`, the exact CT9
  characterization of the remainder fibre as ambient membership together with
  failure of selected-support membership.  Row 38 receives this complete
  `ExactLedger`, so it can query the theorem without dropping any prior fact.
- **Transport and terminals.** Execution is the four canonical adapters composed
  by `CTExecution.compose`; the application supplies only the inert structural
  registration.  In particular, `coverNodup`, `coverSupported`, and
  `cover_card` describe the registered cover but do not supply the desired
  union theorem.  Core derives that theorem, the CT14 aggregate
  impossibility (`coveredComplement_length`) and the CT1 hit impossibility
  (`packing_no_free_occurrence`) rather than accepting them as registration
  fields.  In the export `v21` is `support_complement_normalization:0`, kind
  `operation`, with an empty `components` list; its incoming edge is `e77`
  (`v15 → v21`, output `right`, "Density-cap residual", status conditional) and
  its sole outgoing edge is the sequence edge `e21` (`v21 → v20`).

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `W = ⋃_{P∈𝒫}V(P)`, `|W|=13p₁₃` | construction / identity | `SupportComplementNormalization.ExactLedger.summary`<br>`SupportComplementNormalization.ExactLedger.selectedUniform`<br>`SupportComplementNormalization.Profile.selectedCount_eq_coverCard_mul_packingCount`<br>`InducedPathMaximalPacking.support_card` | CT9; packing is a predecessor-ledger query |
| `R=G-W`, `|R|+13p₁₃=n` | construction / identity | `SupportComplementNormalization.ExactLedger.complement`<br>`SupportComplementNormalization.ExactLedger.partitionExact`<br>`SupportComplementNormalization.ExactLedger.complementExact` | CT9; exact successor ledger |
| row-10 density cap used for largeness of `R` | inherited theorem | `FiniteDensityBudget.CapLedger` in `NormalizedSupportCapability.densityCap` | predecessor ledger query; no recomputation |
| componentwise induced-`P₁₃`-freeness | theorem | `NormalizationRank.exactInducedPathComponent_free` | CT1 after CT9→CT14 |
| `def:internal-3-core` | def | `NormalizationRank.HasInternalCore`<br>`NormalizationRank.exactInducedPathComponent_emptyInternalCore`<br>`TypeABCertificate.EmptyInternalThreeCore` | CT9→CT14→CT1→CT6; restated as a clause of `def:admissible` at row 41 |

Nodes `[25]`–`[26]` anchor no `\label` of their own: the size clause is cited
from `prop:p13-density`, whose dependency-table node is `[24]` (row 10), and the
`P₁₃`-freeness clause is the maximality of the packing chosen at `[17]` (row 6).

**CT composition at this row.** Four adapters, in the order the code composes
them: `CT9 → CT14 → CT1 → CT6`.  The reference table's "CT1, CT6, CT9, CT14" is
the alphabetical set and is corrected here from the nesting of `.compose` in
`Profile.execution`.  CT9 cuts the ambient vertex schedule into the
packing-covered fibre and its complement and decides bounded-versus-overloaded;
CT14 compares the derived lower mass `n − |covered|` against CT9's own
complement cardinality and decides aggregate-versus-capacity; CT1 searches the
occurrence schedule *restricted* to occurrences whose cover lies entirely in
that complement and decides hit-versus-avoiding; CT6 scans the component
schedule of the complement in order and decides
first-failure-versus-active-ledger.  The composition is what makes `[27]`
derivable at all: CT6's failure datum is an internal core, and the target
implication it feeds needs CT1's avoidance certificate for the *same*
complement.  A single CT would have to rebuild one of the two carriers from the
stable residual — precisely what `PartitionProfile.complementAtPrevious` and the
retained predecessor equalities exist to prevent.

### Row 38 — Boundary-demand accounting `[28]`–`[29]`

- **Paper fact.** `[28]` is `def:deficiency-surplus`:
  `def⁺(X) = Σ_{v∈V(X)} max{0, 3 − d_X(v)}` with the degree taken *inside* `X`,
  and `σ(X) = Σ_{v∈V(X)} max{0, d_G(v) − 3}`; the manuscript stresses that
  "positive deficiency, not signed cubic charge, measures external degree
  demand".  `def:window-remainder-surplus-split` fixes `σ_W` and `σ_R` as that
  quantity read at the packed windows and at the remainder.  `[29]` is
  `lem:stub-positive`: `def⁺(R) ≤ e(R,W) ≤ 15p₁₃ + o(n)`, hence
  `def⁺(R) − σ_R ≤ 15p₁₃ + o(n)`, and normalized
  `(def⁺(R) − σ_R)/|R| ≤ 15θ/(1 − 13θ) + o(1)`.  Its proof has three steps: the
  pointwise demand bound `max{0,3−d_R(v)} ≤ e_v` summed to `def⁺(R) ≤ e(R,W)`,
  using only `δ(G) ≥ 3`; the per-window capacity count — an induced `P₁₃` has
  exactly its `12` path edges, so it exports `13·3 − 2·12 = 15` cubic exits plus
  its own surplus, giving `e(R,W) ≤ Σ_{P∈𝒫}(15 + σ(P)) = 15p₁₃ + σ_W`; and
  `σ_W ≤ σ(G)`, "since the windows are vertex-disjoint and surplus is
  nonnegative", after which `def:near-cubic-spine`'s `σ(G) = O(√n) = o(n)` gives
  the displayed `o(n)`.  `lem:surplus-aware-window-stub` is the first two steps
  alone, and the manuscript is explicit that they need no near-cubic hypothesis.
- **What the Lean does.** One atomic Strategy, `Spine.boundaryDemandRow`,
  installed as `Spine.boundaryDemand` and run by `AtomicCT.run` after nodes
  `[25]`–`[27]`.  Its manifest requires `[remainderNormalized, surplusAtOrBelow]`
  and produces `[boundaryDemand, stubSupply]`, both checked by `rfl`.  It reads
  the standing baseline off the residual — `inputs.current.baseline` composed
  with `minDegree_le_degree` — and never from a fact.

  `boundaryDemand` is `lem:surplus-aware-window-stub`, committed as the
  manuscript's chain with both links kept, at every window packing of the
  registered order:

  `def⁺(R) ≤ e(R,W)`  and  `e(R,W) + 2(order−1)·p ≤ δ·order·p + σ_W`.

  The first link is
  `Graph.FiniteObject.positiveDeficiency_le_boundaryIncidence`, the manuscript's
  pointwise argument summed.  The second is
  `Graph.FiniteObject.boundaryIncidence_add_internal_mass_le`, the cut budget on
  its own — invariant 23's window stub capacity — assembled from the degree
  split `Σ_{w∈W} d(w) = δ|W| + σ_W`, the internal mass
  `2(order−1)·p ≤ Σ_{w∈W} d_W(w)` of `internal_mass_windowSupport`, and
  `boundaryIncidence_remainderSupport_eq`, which is the manuscript's own move of
  counting the cut on the window side and using it on the remainder side.

  `stubSupply` is `lem:stub-positive` proper, at every such packing:

  `def⁺(R) + 2(order−1)·p ≤ δ·order·p + T(n)`.

  It is `positiveDeficiency_add_internal_mass_le_degreeSurplus` — the chain with
  `σ_W` replaced by the object's own `σ(G)` through the new
  `Graph.FiniteObject.ambientSurplus_le_degreeSurplus` — composed with the
  node-`[19]` at-or-below arm `surplusAtOrBelow`, read by exact key through
  `FactInputs.get`.  `ambientSurplus_le_degreeSurplus` is the manuscript's
  `σ_W ≤ σ(G)`: surplus is a sum of nonnegative vertex-local terms, so it is
  monotone in the region, and at the whole object it *is* the `degreeSurplus`
  observable the node-`[19]` split compares, by the handshake
  `Σ_v (d(v) − δ) = 2m − δn`.  There is no second surplus notion.
- **What it should do.** This is the implementation.  At the manuscript's own
  presentation — `δ = 3`, `order = 13`, so `δ·order = 39 = 13·3` and
  `2(order−1) = 24 = 2·12` — the capacity link is equivalent (both directions,
  by `omega`) to `e(R,W) ≤ 15p₁₃ + σ_W`, and `stubSupply` to
  `def⁺(R) ≤ 15p₁₃ + T(n)`.  `T` is the registered scale threshold of node
  `[19]`, which is the spine's exact stand-in for the manuscript's
  `σ(G) = O(√n) = o(n)`: where the manuscript writes `o(n)`, the ledger carries
  the exact bound the branch actually proved.  Neither numeral appears in any
  spine module; `δ`, `order`, `p`, and `T` are read from the registered `Data`
  and the object.
- **Gap.** None at this row.  Two manuscript displays are deliberately *not*
  committed here, for reasons that are themselves facts about the statements:

  *The normalized form* `(def⁺(R) − σ_R)/|R| ≤ 15θ/(1 − 13θ) + o(1)` is a
  division by `|R|` together with an `o(1)`; it needs `|R| > 0` and a rational
  carrier, and it is the same normalization step the manuscript performs after
  this node.

  *The surplus-adjusted form* `def⁺(R) − σ_R ≤ 15p₁₃ + σ_W − σ_R` is the first
  display with `σ_R` subtracted from both sides, so over `ℤ` it carries no new
  content.  Over `ℕ` it would carry *less*: truncated subtraction sends
  `def⁺(R) − σ_R` to `0` exactly when the net charge is negative, which is the
  case the downstream collision at node `[60]`
  (`¼|R| ≤ def⁺(R) − σ(R) ≤ τ_win|R| + o(|R|)`) exists to rule out.  Committing
  a truncated net charge here would silently weaken that collision, so the
  signed quantity belongs to the node that introduces a signed carrier
  (`lem:netcharge-superadd`, `[56]`/`[58]`), not to this one.
- **Ledger and residual.** The row consumes the literal active predecessor and
  reads both its prerequisites by exact semantic key; the `surplusAtOrBelow`
  requirement is the type-level reason node `[29]` cannot be reached on the
  node-`[19]` above arm, which is exactly the manuscript's "Assume
  `def:near-cubic-spine`".  A branch that left at `[19]` has no
  `surplusAtOrBelow` in its key index, so this row does not elaborate there.
  The output index is definitionally `Produces ++ known`, so every earlier fact
  stays indexed and queryable.  It is a fact-only step: the residual is
  unchanged and the refinement is equality, so no object, packing, or count
  travels.  `complete_audit_facts` pins the audit of a completed block to the
  full key index, in commit order, by `rfl`.
- **Transport and terminals.** Execution is `factOnly` through the framework's
  one `AtomicCT.run`; no adapter chain, registration, capability record,
  terminal, or payload.  The row is nonbranching — two facts on one arm — and
  names no producer, predecessor depth, or execution position.  `#print axioms`
  on `boundaryDemandRow`, `ambientSurplus_le_degreeSurplus`,
  `boundaryIncidence_add_internal_mass_le`,
  `positiveDeficiency_add_internal_mass_le_degreeSurplus` and `Spine.run`
  reports `[propext, Classical.choice, Quot.sound]` and nothing else.
- **Retired with this row.** The legacy CT4→CT14 registration
  (`Core.Strategy.BoundaryDemandAccounting`,
  `NormalizationRank.boundaryDemand`) is quarantined and not revived.  Its
  registered quantities were all ambient — the demand schedule was `V(G)` rather
  than `V(R)`, the weight used `d_G` rather than the internal degree and was
  therefore identically zero on this residual, and no per-window capacity
  existed — so nothing from it is reused.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | Realization |
|---|---|---|---|
| `def⁺(X) = Σ_v max{0, δ − d_X(v)}` | def | `Graph.FiniteObject.positiveDeficiency` | region-relative, at `internalDegree` |
| `σ(X) = Σ_v max{0, d_G(v) − δ}` | def | `Graph.FiniteObject.ambientSurplus` | `σ_W` and `σ_R` are this at the two regions |
| `e(R,W)` | def | `Graph.FiniteObject.boundaryIncidence` | counted from inside a region |
| `def⁺(R) ≤ e(R,W)` | lem | `Graph.FiniteObject.positiveDeficiency_le_boundaryIncidence` | first clause of `Spine.Key.boundaryDemand`; uses only `δ(G) ≥ δ` |
| `e(R,W) ≤ 15p₁₃ + σ_W` (invariant 23) | lem | `Graph.FiniteObject.boundaryIncidence_add_internal_mass_le` | second clause of `Spine.Key.boundaryDemand` |
| the cut is one number from either side | lem | `Graph.FiniteObject.boundaryIncidence_remainderSupport_eq` | window-side count used on the remainder side |
| `Σ_{w∈W} d_W(w) ≥ 2(order−1)p` | lem | `Graph.FiniteObject.internal_mass_windowSupport` | the `2·12` of an induced copy, per window |
| `σ_W ≤ σ(G)` | lem | `Graph.FiniteObject.ambientSurplus_le_degreeSurplus` | monotone in the region; at the object it is `degreeSurplus` by the handshake |
| `def⁺(R) ≤ 15p₁₃ + o(n)` (`lem:stub-positive`, invariant 24) | lem | `Graph.FiniteObject.positiveDeficiency_add_internal_mass_le_degreeSurplus` | committed as `Spine.Key.stubSupply` with the node-`[19]` ceiling for `o(n)` |
| `def:near-cubic-spine` as the lemma's hypothesis | assumption | `Spine.Key.surplusAtOrBelow` in `Requires` | type-level: unreachable on the `[19]` above arm |

**CT composition at this row.** None.  The reference table's `CT4 → CT14`
described the retired path, in which an application-supplied registration handed
a demand schedule and a capacity rate to an assignment stage and an aggregator.
Both stages are sums of vertex-local counts over a region, which is what the
theorems above are; no capability, member schedule, label, or terminal is
involved.  The row is a single `factOnly` Strategy through `AtomicCT.run`.

### Row 39 — Wedge lower bound `[30]`

- **Paper fact.** `[30]` is `lem:wedge-lower`.  For a component `C` of the
  packed-window remainder, with `W₂(C) = Σ_{v∈V(C)} C(d_C(v), 2)` the internal
  length-two wedges and `def⁺(C)` the positive deficiency of
  `def:deficiency-surplus`, the manuscript proves
  `W₂(C) ≥ 3|V(C)| − 2def⁺(C)` by the degree count: writing `n_i` for the
  number of vertices of internal degree `i`, `|V(C)| = Σ n_i`,
  `def⁺(C) = 3n₀+2n₁+n₂` and `W₂(C) = Σ C(i,2)n_i`, so
  `W₂(C) − (3|V(C)| − 2def⁺(C)) = 3n₀ + n₁ + Σ_{i≥3}(C(i,2) − 3)n_i ≥ 0`.
  "Summing over the connected components `C` of `R`, and using `Σ_C|V(C)| = |R|`
  and `Σ_C def⁺(C) = def⁺(R)` (within a component `d_C = d_R`, so the
  per-component deficiencies add up to `def⁺(R)`)" gives
  `W₂(R) ≥ 3|R| − 2def⁺(R)`.  The lemma is then stated *for* its "in
  particular": substituting the deficiency ceiling of `cor:stub-boundary-supply`,
  `def⁺(R) ≤ (τ_win+o(1))|R|` with `τ_win = 0.22817486846…`, yields
  `W₂(R) ≥ ω_win|R| − o(|R|)` with `ω_win = 3 − 2τ_win = 2.54365026308…`, and the
  sharper high-entropy cap `0.21296321056…` yields `ω = 2.57407357888…`.  This is
  invariant 28, the manuscript's **demand floor** of the final collision; node
  `[30]`'s `Requires` cell is "inv 21, 28; `cor:stub-boundary-supply`".
- **What the Lean does.** One atomic Strategy,
  `Graph.Strategy.Spine.wedgeSupplyRow`, installed at the spine's own keys as
  `Spine.wedgeSupply` and run by `AtomicCT.run` immediately after node
  `[28]`–`[29]`.  Its manifest is `pairManifest`: it requires the single key
  `boundaryDemand` and produces the two keys `wedgeSupply` and
  `curvatureDemandFloor`, checked by `#print`-level `rfl` against
  `manifest.Requires = [K .boundaryDemand]` and
  `manifest.Produces = [K .wedgeSupply, K .curvatureDemandFloor]`.

  `wedgeSupply` is the lemma proper.  Its value schema, in
  `SpineVocabulary.Holds`, is: for every window packing of the registered order
  and every region `X ⊆ R` of its remainder,

  `δ·|X| ≤ W₂(X) + 2·def⁺(X)`,

  with `W₂` the new `Graph.FiniteObject.internalWedgeCount` — `Σ_{v∈X}
  C(d_X(v),2)` at the *internal* degree `Graph.FiniteObject.internalDegree`
  already used by node `[28]`–`[29]` — and `def⁺` the existing
  `Graph.FiniteObject.positiveDeficiency`.  The proof is
  `Graph.FiniteObject.baseline_mul_card_le_internalWedgeCount_add_two_mul_positiveDeficiency`,
  which sums the per-vertex clause
  `baseline_le_choose_two_add_two_mul_deficit` over the region; that clause is
  the manuscript's own `3n₀ + n₁ + Σ_{i≥3}(C(i,2)−3)n_i` read one vertex at a
  time, with slack `3`, `1`, `0` at internal degrees `0`, `1`, `2` and
  `C(d,2)−3` above them.  Its only hypothesis is `3 ≤ δ`, taken from
  `Data.three_le_threshold`.

  `curvatureDemandFloor` is the lemma's "in particular".  Its value schema is:
  for every window packing of the registered order,

  `δ·|R| + 2·(2(order−1)·p) ≤ W₂(R) + 2·(δ·(order·p) + σ_W)`,

  where the two doubled terms are literally the two sides of the committed
  `boundaryDemand` fact.  The executor reads that fact by exact key through
  `FactInputs.get`, instantiates `wedgeSupply` at `X = R` by
  `Finset.Subset.refl`, and discharges the substitution with `omega`.
- **What it should do.** This is the implementation.  Both displayed
  inequalities of `lem:wedge-lower` are instances of the one committed
  `wedgeSupply` clause: the componentwise bound at a component of `R`, and its
  sum over the components at `R` itself.  Nothing has to know what a component
  is, and no component decomposition of the remainder is built: the manuscript
  needs `d_C = d_R` inside a component only to reconcile its two ways of
  computing the same number, and stating the count at every region computes it
  once.  Where the manuscript substitutes the asymptotic ceiling
  `def⁺(R) ≤ (τ_win+o(1))|R|`, the row substitutes the exact ceiling the ledger
  actually carries.  At the manuscript's own presentation — `δ = 3`,
  `order = 13`, so `δ·order = 39` and `2(order−1) = 24` — the committed clause is
  equivalent (both directions, by `omega`) to
  `W₂(R) ≥ 3|R| − 2(15p₁₃ + σ_W)`, which is exactly
  `W₂(R) ≥ 3|R| − 2def⁺(R)` with `def⁺(R) ≤ 15p₁₃ + σ_W` from
  `cor:stub-boundary-supply`'s parent lemma.  No numeral appears in any spine
  module; `δ`, `order` and `p` are read from the registered `Data` and the
  object.
- **Gap.** None at this row.  The remaining distance to the manuscript's
  displayed `2.543·|R|` is the two asymptotic estimates the *manuscript* takes
  after this point — `σ(G) = O(√n) = o(n)` from `def:near-cubic-spine` and
  `θ ≤ θ_win + o(1)` from `prop:p13-density`, which together turn
  `15p₁₃ + σ_W` into `(τ_win+o(1))|R|`.  Both are asymptotic statements about a
  family of objects, not facts about the selected one, and the spine holds their
  exact finite antecedents already: `surplusAtOrBelow` (`σ(G) ≤ T(n)`) and
  `densityCap`.  Their normalization is a downstream specialization and is not
  attempted here.
- **Ledger and residual.** The row consumes the literal active predecessor
  handed to it — the `ExactLedger` indexed by
  `[boundaryDemand, remainderNormalized, densityCap, barrierCap,
  surplusAtOrBelow, localAlgebra, maximalPacking, uncompressible, tightEndpoint,
  slackIndependent, noProperBaseline, returnAvoidance, selection]` — and its
  output index is definitionally `Produces ++ known`, so every earlier fact stays
  indexed and queryable.  It is a fact-only step: the residual is unchanged and
  the refinement is equality, so no object, packing, region, or count travels.
  `Spine.completedKeys` carries `wedgeSupply` and `curvatureDemandFloor`
  ahead of `boundaryDemand`, and `complete_audit_facts` pins the audit of a
  completed block to exactly that index, in commit order, by `rfl`.
  `complete_audit_accounts_for_every_fact` is `ExactLedger.audit_complete` on the
  same ledger.  Nothing is archived, rebased, or dropped.
- **Transport and terminals.** Execution is `factOnly` through the framework's
  one `AtomicCT.run`; there is no adapter chain, no registration, no capability
  record, no terminal, and no payload.  The row is nonbranching — it produces
  two facts on one arm — and it names no producer, predecessor depth, or
  execution position: it is quantified over the keys it consumes and produces
  and would run after any canonical cursor whose index carries `boundaryDemand`.
  `#print axioms` on `Spine.run`, `complete_audit_facts`,
  `complete_audit_accounts_for_every_fact`, `wedgeSupplyRow` and the graph
  theorem reports `[propext, Classical.choice, Quot.sound]` and nothing else.
- **Retired with this row.** The legacy path is deleted, not shimmed.
  `Graph/WedgeLowerBound.lean`'s whole-object surrogate
  (`wedgeCount`, `deficiencyAt`,
  `baseline_mul_vertexCount_le_wedgeCount_add_two_mul_deficiencyAt` and its
  `2k−3` sharp variant, which no manuscript statement asks for) and its CT14
  member-schedule carrier (`wedgePairs`, `WedgeCoordinate`, `wedgeFinset`,
  `wedgeSchedule`, `wedgeSchedule_card`) are gone; the module now states
  `lem:wedge-lower` at a region and nothing else.  The module was a quarantine
  rescue at the root and is now imported by `SpineVocabulary` on its own merit.
  `SpineRows.criticalityManifest` — a shared two-output manifest carrying a
  node-specific name — is renamed `pairManifest`.  The registrations that the
  retired path fed (`Core.Strategy.LocalSupplyLowerBound`,
  `Graph.Strategy.NormalizationRank.componentLocalSupply`) were already
  quarantined by rows 37–38 and are not revived.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | Realization |
|---|---|---|---|
| `W₂(X) = Σ_{v∈X} C(d_X(v),2)` | def | `Graph.FiniteObject.internalWedgeCount` | region-relative, at the internal degree of node `[28]` |
| `def⁺(X)` (`def:deficiency-surplus`) | def | `Graph.FiniteObject.positiveDeficiency` | inherited from node `[28]`; not restated |
| `W₂(C) ≥ 3\|V(C)\| − 2def⁺(C)`, componentwise | lem | `Graph.FiniteObject.baseline_mul_card_le_internalWedgeCount_add_two_mul_positiveDeficiency` | committed as `Spine.Key.wedgeSupply`, at every region of `R` |
| `W₂(R) ≥ 3\|R\| − 2def⁺(R)`, summed over components | lem | the same theorem at `X = R` | the same fact; no component decomposition is built |
| the degree count `3n₀+n₁+Σ_{i≥3}(C(i,2)−3)n_i ≥ 0` | proof | `Graph.FiniteObject.baseline_le_choose_two_add_two_mul_deficit` | per-vertex; summed by `Finset.sum_le_sum` |
| `3 ≤ δ` is the exact threshold the count needs | proof | `Graph.FiniteObject.baseline_one_insufficient`<br>`Graph.FiniteObject.baseline_two_insufficient` | derived here, not copied |
| `W₂(R) ≥ ω_win\|R\| − o(\|R\|)` (invariant 28, demand floor) | lem | `Spine.Key.curvatureDemandFloor` | the exact ceiling of `[29]` substituted for `def⁺(R)`; the `o(1)` normalization is downstream |

**CT composition at this row.** None.  The reference table's `CT14` described
the retired path, in which an application-supplied registration handed a
pointwise law to a member-schedule aggregator; the aggregation it performed is
`Finset.sum_le_sum` over the region, which is one line of the theorem and needs
no capability, member schedule, label, or terminal.  The row is a single
`factOnly` Strategy through `AtomicCT.run`.

### Row 40 — Target-relative rank dichotomy `[31]`–`[32]`

- **Paper fact.** `[31]` is `def:curvature-target-rank`.  For an atom `C`,
  `𝒲₂(C)` is the set of raw internal length-two curvature tests; a subfamily
  `𝒜 ⊆ 𝒲₂(C)` *survives* an admissible rank quotient `q` when `q` is
  label-injective on `𝒜` (`def:exact-response-profile`), and survives the
  admissible quotient system when it survives every *functional* admissible
  rank quotient; `r_Ω(C)` is the maximum size of a surviving subfamily, and
  `r_Ω(R)` is the same for the raw atom curvature tests of the remainder.
  An admissible rank quotient (`def:admissible-rank-quotient`) is a quotient
  `q : ρ_T^ex(X) → Q` of the exact response profile of a connected support `X`
  carrying the family, with `T = {v ∈ V(X) : v incident with an edge of G−X}`,
  which preserves the boundary degree profile and is target-complete against
  all `T`-boundaried contexts (`def:target-complete-quotient`: an identification
  is allowed only inside a fixed boundary-degree fibre and only when no context
  creates a power-of-two cycle from one side and not the other); which, if
  `X ⊊ G` and it is rank-reducing, is represented by a strictly smaller proper
  representative (`def:proper-quotient-representative`); and which, if `X = G`,
  is label-injective unless represented by a strictly smaller admissible closed
  representative (`def:closed-quotient-representative`).
  `lem:target-rank-circuit` is stated for this system: if `ℐ ⊆ 𝒜` is maximal
  among surviving subfamilies and `a ∈ 𝒜 ∖ ℐ`, then some `ℬ ⊆ ℐ` makes
  `(a, ℬ)` a target-dependence (`def:curvature-target-dependence`) — "in
  particular, if no proper target-dependence exists among the coordinates of
  `𝒜`, then the whole family survives every functional admissible rank quotient
  and is independently target-testable".  Its proof is three steps: maximality
  makes `ℐ ∪ {a}` fail to survive some `q`, `ℐ` survives `q` so the failure
  involves `a`, and functionality supplies the finite `ℬ` and the `φ` with
  `q(a) = φ((q(b))_{b∈ℬ})`.
  `[32]` is the decision `r_Ω(R) < W₂(R) − o(W₂)`: yes is `[33]`, Branch D,
  entered with the extracted dependence; no is `[34]`, Residual B, the
  full-rank residual `lem:full-rank` is stated on at `[47]`.
- **What the Lean does.** One atomic Strategy and one decision on the canonical
  ledger, run immediately after node `[30]`, over a *constructed* quotient
  system — `r_Ω` is a `Nat`, not a quantifier.

  `Graph.FiniteObject.internalWedgeFamily` is `𝒲₂(X)`: a raw test is a centre
  together with an unordered pair of two of its neighbours inside the region,
  which is clause (D4) of `def:declared-coordinate-signature` and is the only
  clause node `[31]` ranks over.  `internalWedgeFamily_card` proves the family
  has exactly `internalWedgeCount = W₂(X)` members, the number node `[30]`
  bounds from below, and `FiniteObject.internalWedgeSupport` is a test's
  declared support.

  `Graph.CurvatureQuotient Baseline Target object region` is
  `def:admissible-rank-quotient` at that family, clause by clause.  It is no
  longer a structure of its own: since row 32 it is an abbreviation for
  `Graph.DeclaredQuotient` — the same definition at an *arbitrary* declared
  coordinate family, in `Graph/DeclaredRankQuotient.lean` — instantiated at the
  raw internal wedges, so every field named below and the routing `localize` are
  proved once and shared with the sparse pair-response family of `[132]`.  Its
  `support` is the connected determination support `Z` with `connected` and
  `carries`; its realizations are `BoundaryPiece (SupportAtom.boundary object
  support)`, the boundaried graphs that can occupy `Z`'s place at `Z`'s own cut
  interface `SupportAtom.cutBoundary` — which is literally `T` — and that is
  what `def:curvature-target-dependence` means by a realization.  `fibrewise`
  and `contextUniversal` are `def:target-complete-quotient` (a) and (b), stated
  at `BoundaryPiece.boundaryDegreeProfile` and at `Graph.glue` against every
  `OutsideContext`.  `properRepresentative` is the proper clause: the
  manuscript says "the five defining properties of a proper representative are
  exactly the five hypotheses of the replacement lemma `lem:replacement` for
  the support `Z`", so the clause *is*
  `InterfaceReplacement.ReplacementSupport`, the hypothesis
  `InterfaceReplacement.not_replacementSupport` refutes at a minimal
  counterexample.  `closedRepresentative` is the closed clause: a strictly
  smaller graph meeting the baseline with `profile_∅(H) ⊆ profile_∅(G)`, which
  at an empty boundary is `Target H → Target G` — the manuscript's own reading
  ("a dyadic cycle in `H` would add the corresponding empty-context target
  event to `profile_∅(H)`, impossible because `profile_∅(G)` contains no such
  event").  The scope split between the two clauses is the framework's own
  `SupportAtom.classifyScope`.

  `Graph.FiniteObject.curvatureQuotientSystem` — `declaredQuotientSystem` at
  this family — is the system `def:functional-rank-quotient` closes with — "the
  admissible quotient system used to compute target-rank consists only of
  admissible rank quotients that are functional on the coordinate family under
  discussion" — so membership is exactly *admissible* (a `CurvatureQuotient`)
  *and functional*.
  `Graph.FiniteObject.curvatureTargetRank` is `r_Ω`: the maximum size of a
  subfamily surviving every member, and
  `curvatureTargetRank_le_internalWedgeCount` is `r_Ω(X) ≤ W₂(X)`.

  Node `[31]` is `Spine.curvatureTargetRankRow`, requiring the single key
  `curvatureDemandFloor` — the manuscript's `[30] → [31]` edge, which is an
  ordering and not a consumption: `def:curvature-target-rank`'s attainment and
  `lem:target-rank-circuit` hold at every object, and node `[30]`'s bound is
  spent at `[47]` — and producing `curvatureTargetRank`.  Its value schema
  is: at every window packing of the registered order, there is a subfamily of
  `𝒲₂(R)` that survives the system, has exactly `r_Ω(R)` members, and on which
  every raw test left outside is target-dependent.  The proof is
  `Core.TargetRank.exists_independent_attaining` — attainment (the empty
  subfamily survives, so the maximum is over a nonempty collection) followed by
  `exists_dependence_of_maximal`, the manuscript's three-step circuit argument
  verbatim.

  Node `[32]` is `Spine.curvatureRankDichotomy`, run through the framework's
  `Decision.run`.  The implementation follows the last paragraph of
  `lem:full-rank`: it tests the exact rank loss `r_Ω(R) < W₂(R)`.  The yes arm commits
  `curvatureRankDrop`: the packing, the strict inequality, and a proper
  target-dependence of the system.  That dependence is *read*, not recomputed:
  the decision reads node `[31]`'s committed fact off the incoming ledger by
  exact key with `ExactLedger.get`, takes the maximal surviving subfamily it
  attains, and applies `Core.TargetRank.exists_dependence_of_attaining` to it —
  an allowance subtracted from `W₂(R)`, which *is* the number of raw tests,
  leaves a bound below the family's own size, and that is
  `lem:target-rank-circuit`'s hypothesis.  The no arm commits `curvatureFullRank`,
  `r_Ω(R) = W₂(R)` at every packing; the reverse inequality is the generic
  `curvatureTargetRank_le_internalWedgeCount` theorem.  The two arms are the
  two halves of one excluded middle, so they are exhaustive and mutually
  exclusive by construction, and neither is readable on the other's branch.

  `Graph.DeclaredQuotient.localize` is `lem:curvature-dependence-routing` for
  an admissible quotient: the manuscript's target-defect case cannot arise —
  an admissible quotient is target-complete by definition, which is what
  `fibrewise` and `contextUniversal` record — so a rank-reducing member falls,
  by the scope of its determination support, into a replacement of a proper
  support or a smaller closed representative.  It is proved here and consumed
  at `[33]`/`[35]`–`[46]`, where those two are refuted by
  `not_replacementSupport` and by the selection's own minimality.
- **What it should do.** This is now the implementation.  Every object node `[31]`
  and `[32]` name is constructed: the coordinate family, its declared supports,
  the determination support and its interface, the realizations, both
  target-completeness clauses, both representative clauses, the system, the
  rank, the circuit extraction, and the comparison.  No field is supplied by a
  registration, no clause is quantified away, and no alternative is added,
  dropped, reordered, or weakened.
- **Gap.** None at this row.  Two conventions, both the ones rows 37–39 already
  use, and neither of them a substitution for a paper statement.  First, no
  packing may travel on the ledger, so each fact quantifies over packings
  rather than naming the one node `[15]`–`[17]` selected: node `[31]` and the
  full-rank arm say "at every maximal packing" and the rank-drop arm says "at
  some", which is what makes the two arms complementary; the manuscript's own
  packing is one of them, so its drop takes the yes arm and its full rank is
  bounded by the no arm.  Second, `[32]` is the one comparison of the spine
  whose manuscript form still carries an asymptotic term after the exact
  substitutions of `[29]`–`[30]`.  Lean does not register an arbitrary
  pointwise surrogate for that asymptotic notation: the manuscript's own proof
  eliminates every strict rank loss, obtains `r_Ω(R) = W₂(R)`, and only then
  weakens that equality to the displayed all-but-`o(W₂)` statement.  Thus no
  rank allowance and no numeral appears in the problem presentation or node.
  Three statements of `def:curvature-target-rank`'s neighbourhood belong to
  later rows and are not committed here: the exact-code equality with the full
  target code and the `2^{|𝒜|}` state realization of `def:target-rank`, which
  the definition retains "on the surviving hot residual entering node `[47]`";
  `lem:full-rank` itself; and the refutation of the two alternatives
  `localize` produces, which is Branch D.
- **Ledger and residual.** Node `[31]` consumes the literal active predecessor
  handed to it, the `ExactLedger` indexed by `[wedgeSupply,
  curvatureDemandFloor, boundaryDemand, remainderNormalized, densityCap,
  barrierCap, surplusAtOrBelow, localAlgebra, maximalPacking, uncompressible,
  tightEndpoint, slackIndependent, noProperBaseline, returnAvoidance,
  selection]`, and its output index is definitionally `Produces ++ known`.
  Node `[32]` commits one arm against that same immutable prefix through
  `Decision.run`, so both arms see every earlier fact and neither sees the
  other's.  Both are fact-only: the residual is unchanged, the refinement is
  equality, and nothing travels — no packing, family, quotient, support,
  realization, or subfamily, each being quantified inside the fact it belongs
  to.  `Spine.completedKeys` is the seventeen-key full-rank index and
  `curvatureRankDropKeys` the seventeen-key Branch-D index differing in exactly
  the arm taken; `complete_audit_facts` and `curvatureRankDrop_audit_facts` pin
  both audits to those indices in commit order, by `rfl`, and
  `complete_audit_accounts_for_every_fact` and
  `curvatureRankDrop_audit_accounts_for_every_fact` are
  `ExactLedger.audit_complete` on them.  Nothing is archived, rebased, or
  dropped.
- **Transport and terminals.** `factOnly` through the framework's one
  `AtomicCT.run` for `[31]`, and the framework's `Decision.run` for `[32]`.
  There is no adapter chain, no registration, no capability record, no contract
  field, no terminal, and no payload; no CT10, CT15 or CT16 is involved.
  The Branch-D successor is the exact ledger indexed by
  `curvatureRankDropKeys`; the spine's retained cursors are node `[19]`, node
  `[21]`, node `[32]`-yes, and completion on Residual B.  Neither row names a
  producer, a predecessor depth, or an execution position: both are quantified
  over the keys they consume and produce.  `#print axioms` on `Spine.run`,
  `curvatureRankDichotomy`, both audit theorems, `curvatureTargetRank`,
  `DeclaredQuotient.localize` and every `Core.TargetRank` theorem reports
  `[propext, Classical.choice, Quot.sound]` and nothing else.
- **Retired with this row.** The legacy path is deleted, not shimmed.
  `Core.Strategy.TargetRelativeRankDichotomy`,
  `Graph.Strategy.NormalizationRank` and the registration
  `Official.compressionLinkedTargetRelativeRankDichotomy` that fed `v18` are
  gone from the live build.  `Core/AdmissibleQuotient.lean` is **deleted**: it
  modelled `def:admissible-rank-quotient` as a two-case disjunction with no
  support, no context, no functionality, no survival and no system, and a
  "rank" that was the cardinality of one map's image;
  `Core.TargetRank` and `Graph.CurvatureTargetRank` replace it, and there is no
  shim.  Row 32 continued that replacement rather than adding beside it: the
  quotient structure moved to `Graph/DeclaredRankQuotient.lean` at an arbitrary
  declared coordinate family and `CurvatureQuotient` became its instance, so the
  tree still holds exactly one `def:admissible-rank-quotient`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | Realization |
|---|---|---|---|
| `def:declared-coordinate-signature` (D4) | def | `Graph.FiniteObject.InternalWedge`<br>`Graph.FiniteObject.internalWedgeFamily`<br>`Graph.FiniteObject.internalWedgeSupport` | the raw curvature coordinates and their declared supports — the only clause node `[31]` ranks over |
| `𝒲₂(R)` and `\|𝒲₂(R)\| = W₂(R)` | def | `Graph.FiniteObject.internalWedgeFamily_card` | ties the family to node `[30]`'s count |
| `def:boundaried-gluing`, `def:atom` | def | `Graph.Boundary`, `Graph.BoundaryPiece`, `Graph.OutsideContext`, `Graph.glue`<br>`InterfaceReplacement.SupportAtom.boundary`, `.cutBoundary` | inherited; `cutBoundary` is the manuscript's `T` |
| `def:boundary-degree-profile` | def | `Graph.BoundaryPiece.boundaryDegreeProfile` | inherited |
| `def:exact-response-profile` | def | `Core.TargetRank.RankQuotient`<br>`.LabelInjectiveOn`, `.RankReducingOn` | a quotient's labelling of the declared coordinates and its response at a realization |
| `def:target-complete-quotient` | def | `Graph.DeclaredQuotient.fibrewise`<br>`Graph.DeclaredQuotient.contextUniversal` | clauses (a) and (b), at `boundaryDegreeProfile` and at `glue` against every `OutsideContext` |
| `def:proper-quotient-representative` | def | `InterfaceReplacement.ReplacementSupport` | the manuscript's own identification of its five properties with `lem:replacement`'s five hypotheses |
| `def:closed-quotient-representative` | def | `Graph.DeclaredQuotient.closedRepresentative` | strictly smaller, baseline, `profile_∅(H) ⊆ profile_∅(G)` read at the empty context |
| `def:admissible-rank-quotient` | def | `Graph.DeclaredQuotient` (`Graph.CurvatureQuotient` is its instance at the raw wedges) | all four clauses; the proper/closed split is `SupportAtom.classifyScope`; the *attempted* reading, with the representative clauses conditional on target-completeness, is `Graph.AttemptedQuotient` |
| `def:functional-rank-quotient` | def | `Core.TargetRank.RankQuotient.Determines`<br>`Core.TargetRank.RankQuotient.FunctionalOn`<br>`Graph.FiniteObject.declaredQuotientSystem` (`curvatureQuotientSystem` is its instance) | the rank axiom, and the closing sentence that the system consists only of functional admissible quotients |
| `def:curvature-target-rank` | def | `Graph.FiniteObject.curvatureTargetRank`<br>`Core.TargetRank.QuotientSystem.Survives`<br>`Core.TargetRank.targetRank`<br>`Graph.FiniteObject.curvatureTargetRank_le_internalWedgeCount` | `r_Ω(R)` as a `Nat` |
| `def:curvature-target-dependence` | def | `Core.TargetRank.Dependence` | the pair, its determination against every realization, its properness, and the rank-reducing admissible quotient witnessing it |
| `lem:target-rank-circuit` | lem | `Core.TargetRank.exists_dependence_of_maximal`<br>`Core.TargetRank.exists_independent_attaining`<br>`Core.TargetRank.exists_dependence_of_targetRank_lt`<br>`Core.TargetRank.targetRank_eq_card_of_no_dependence` | proved, including the "in particular"; committed as `Spine.Key.curvatureTargetRank` and consumed by the yes arm of `[32]` |
| `lem:curvature-dependence-routing` | lem | `Graph.DeclaredQuotient.localize`<br>`Graph.AttemptedQuotient.route` | proved: the target-defect case cannot arise for an *admissible* quotient, and the other two are the scope split of the determination support; `route` is the same analysis for an attempted one, where the defect case is the blocker of `def:surplus-blockers` (d)/(e); consumed at `[33]`/`[35]`–`[46]` and at `[132]` |
| `def:target-rank`, `lem:independent-target-entropy`, `rem:rank-coordinate-entropy-interface` | def, lem, rem | | the `2^{\|𝒜\|}` state realization and the entropy interface are consumed at `[18]`→`[22]` and at `[47]`, not here |

**CT composition at this row.** None.  The retired path composed `CT10 → CT15 →
CT16` — an exhaustive classification of an observation table, a rank-and-charge
tally over a coordinate schedule, and a closed-code equality — around a
registration whose `Response` was a constant, whose `classOf` was the identity
on vertices, and whose `capacity` was defined as the charge total the tally
computed, making the comparison vacuous.  None of that structure is needed: the
rank is a maximum over subfamilies of a constructed system, the circuit
extraction is three steps of logic, and the branch is one `Decision`.  Both
rows go through the framework's one `AtomicCT.run` and its one `Decision.run`.

### Row 41 — Full-rank finite-state capacity `[47]`–`[56]`

- **Paper fact.** On Residual B, the full-rank and wedge facts give the forced
  curvature cost. `prop:two-budget` distinguishes the high-entropy calculation
  from low entropy, but every surviving case is passed to the same
  large-budget Residual C. The dominant-local-type and independent-translate
  conclusions are optional strengthening on one low-entropy subcase; the
  later closure is explicitly robust to omitting that strengthening.
- **Live implementation.** `forcedCurvatureCost` is appended first.
  `remainderEntropyDichotomy` is the exact high/low comparison. The high arm
  builds `entropyPackageDemand` and either closes the strict skeleton overflow
  or appends `largeBudgetResidual`. The low arm appends
  `largeBudgetResidual` directly with `lowEntropyLargeBudgetRow`, preserving
  the low-entropy witness and the entire incoming ledger.
- **Deleted illegal refinement.** The finite radius-two dominance predicates,
  their six semantic keys, their decisions, and their rows have been removed.
  They were an exhaustive finite classification, but no theorem identified it
  with the manuscript's asymptotic local-type-vector bit-content condition.
  The implementation now proves only the common conclusion actually consumed
  downstream, so it neither evaluates a type table nor asserts an unproved
  equivalence.
- **Residual C consumption.** The Residual C row chain is polymorphic in the
  literal tail `known` of `residualCKeys known`. It appends the generic
  localization theorem and performs the exact finite net-charge sign decision.
  The negative arm appends a connected negative support. The nonnegative arm
  appends the exact inequality of `cor:global-window-join-pressure`. Every
  production is through `AtomicCT.run` or `Decision.run`; no residual is
  reconstructed or rebased.
- **Removed cutoff.** `largeOrderExponent`, `largeOrderResidual`,
  `smallOrderResidual`, `netDeficiencyCap`, the application proof of the
  512-bit threshold, and the specialized cap row are deleted. Indices
  43–45 and 145–150 remain unused; existing key indices are not renumbered.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `cor:forced-curvature-cost` | corollary | `Spine.forcedCurvatureCost` | `AtomicStrategy` |
| `def:remainder-entropy` | definition | `Graph.RemainderClass`, `Graph.AtLeastEntropyRate` | symbolic finite class |
| `prop:two-budget` high/low split | proposition | `Spine.remainderEntropyDichotomy` | `Decision` |
| common low-entropy continuation | routing | `Spine.lowEntropyLargeBudget` | `AtomicStrategy` |
| `eq:entropy-cap` | equation | `Spine.entropyCapDichotomy` | high arm only; `Decision` |
| Residual C | residual | key `largeBudgetResidual`, `residualCKeys known` | dependent exact-ledger index |

### Row 42 — Net-charge continuation `[57]`–`[64]`

- **Paper fact.** The canonical support decomposition is exact on vertex count,
  assigned surplus, and positive deficiency. Hence a remainder of negative net
  charge has a connected negative piece. On the complementary nonnegative arm,
  the density cap and surplus-aware stub supply contradict one another for all
  sufficiently large orders, exactly as `prop:negative-net-charge` prescribes.
- **Node `[60]`.** `netChargeOrderDichotomy` decides the paper's
  sufficiently-large regime at the registered `spineScale = C_sp`. The
  surviving `netChargeLarge` ledger is passed directly to `netChargeCapRow`.
  That row reads exactly `densityCap`, `stubSupply`, and `netChargeLarge`, applies
  `FiniteObject.strictCap_of_densityCap_of_sufficientlyLarge` followed by
  `negativeNetCharge_of_stubSupply_of_strictCap`, and appends `netChargeCap`.
  There is no enlarged scale, retained-reserve margin, or intermediate margin
  fact. The `netChargeNonNegative` sign arm is then eliminated against this cap
  at the canonical maximum packing.
- **Node `[61]`.** `netChargeLocalizationRow` publishes the generic consequence
  of `lem:netcharge-superadd`. On the negative sign arm,
  `negativeSupportRow` reads exactly `netChargeNegative` and
  `netChargeLocalization`. It keeps the selected maximal packing from the sign
  decision, applies localization to that same remainder, and appends the actual
  component together with its membership in `canonicalPieces` and the
  `NegativeNetCharge` proof of its definitionally recovered `pieceSupport`.
  Subset and connectivity are derived from that membership only where a later
  branch consumes them. No Type B bridge reserve or later charge estimate is
  smuggled into this node.
- **Exhaustiveness and routing.** Both refinements are ordinary excluded middle
  on their exact propositions. The small-order arm is eliminated only by the
  canonical endpoint's explicit sufficiently-large premise. No table,
  `native_decide`, finite-order cap, isolated residual, or second ledger is
  introduced. The surviving node-`[61]` ledger continues through the existing
  exhaustive Type A / Type B split at `[62]`.
- **Ledger.** Starting from `residualCKeys known`, the live order arm appends
  `netChargeLarge`; node `[60]` appends `netChargeCap`; localization appends
  `netChargeLocalization`; the sign decision appends `netChargeNegative`; and
  node `[61]` appends `negativeSupport`. Thus the exact surviving prefix is
  `negativeSupport :: netChargeNegative :: netChargeLocalization ::
  netChargeCap :: netChargeLarge :: largeBudgetResidual :: known`, with the
  literal high- or low-entropy ancestry retained as `known`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:canonical-decomp` | definition | `FiniteObject.canonicalPieces`, `pieceSupport` | generic graph API |
| `lem:netcharge-superadd` | lemma | `FiniteObject.exists_canonicalPiece_negativeNetCharge`, `Spine.netChargeLocalization` | generic graph API / `AtomicStrategy` |
| sufficiently-large net-cap predicate and cutoff | definition / lemma | `FiniteObject.SufficientlyLargeForNetCap`, `netCapCutoff`, `sufficientlyLargeForNetCap_of_cutoff` | generic graph API; symbolic arithmetic |
| sufficiently-large routing | routing | `Spine.netChargeOrderDichotomy` | exhaustive `Decision`; facts `netChargeLarge` / `netChargeSmall` |
| exact strict cap from density | lemma | `FiniteObject.strictCap_of_densityCap_of_sufficientlyLarge` | generic graph API |
| `prop:negative-net-charge` total-remainder conclusion | proposition | `FiniteObject.negativeNetCharge_of_stubSupply_of_strictCap`, `Spine.netChargeCap` | generic graph API / `AtomicStrategy` |
| net-charge sign split | routing | `Spine.netChargeDichotomy` | `Decision` |
| node `[60]` nonnegative-arm contradiction | incompatibility | `Spine.instIncompatibleNetChargeCapNonNegative` | sealed `Incompatible`; canonical maximum packing |
| node `[61]` support arm | proposition | `Spine.negativeSupport` | `AtomicStrategy` reading the existing localization fact |
| node `[62]` Type A / Type B split | routing | `Spine.typeSplitDichotomy` | exact `Decision`; no continuation payload |

### Row 43 — Corridor cut-state `T(J)` `[145]`–`[157]`

- **Paper fact.** `def:cold-corridor-first-failure` fixes, for an initial
  segment `J` of a cold return corridor, `T(J)` as its two active boundary
  interfaces and defines the *cold corridor state* as the finite two-boundary
  cut-state obtained from `\rho_{T(J)}^{ex}(J)` "by retaining exactly the
  boundary-degree profile, the two active boundary half-edges, the cold-window
  offsets met at the two interfaces, and the declared local coordinates of
  `def:declared-coordinate-signature` whose support is contained in the bounded
  active interface".  It adds two claims about that retention.  First, "it is
  not the full labelled prefix", and yet "after excluding (F2), equality of cold
  corridor states is equality for every target-response coordinate used by the
  local replacement".  Second, "since the boundary has size two and the retained
  window and local-coordinate labels are finite, the set of possible cold
  corridor states is bounded by a constant `Q_cold` depending only on the fixed
  declared signature", after which `M_cold := Q_cold + 30`,
  `B_cold := 15(1+3(2^{M_cold+2}-1))`, `D_cold := M_cold B_cold + 1`.
  `def:declared-coordinate-signature` generates the coordinates by clauses
  (D1)–(D8), the last of which closes the family under finite products, labelled
  copies, restrictions and quotient images, "with support equal to the union of
  the supports of the entries used".
- **What the Lean does.** `Graph.ColdCorridor.DeclaredSignature` registers the
  signature: the finite alphabets `Clause`, `Generator`, `Value`, `Label` of the
  generating clauses (D1)–(D7), the cut-state bound `degreeBound` the local
  target algebra imposes, and the window order.  Clause (D8) is not a field —
  it is `Graph.ColdCorridor.Generated`, an inductive whose `gen` constructor is
  a generating coordinate and whose other four constructors are (D8)'s own
  products, labelled copies, restrictions and quotient images.
  `Presentation.support` gives every declared coordinate the union of the
  supports of the entries used, and `Presentation.reading` evaluates it from
  exactly those entries.
  `Graph.ColdCorridor.CutState` has four fields and no fifth: `boundaryDegrees`,
  `halfEdges`, `offsets`, and `declared`, the last being
  `(clause) → Generator clause → Option Value` — `some` of the value when the
  coordinate's support lies inside the active interface, `none` when it leaves.
  `Presentation.state` is that retention at a segment.  `CutState.equivProduct`
  carries `Fintype` and `DecidableEq` onto it, and
  `stateBound S = Fintype.card (CutState S)` is `Q_cold`, a function of the
  registered signature alone with no graph in it.
  `Presentation.reading_eq_of_state_eq` is the completeness claim: two segments
  with equal states agree at *every* declared coordinate whose support lies in
  the active interface, derived (D8) coordinates included, by induction on the
  generation.  `Presentation.generatorValue_eq_of_state_eq` is its generating
  case and also returns the second conclusion the retention needs — that the
  other segment keeps the coordinate too.
  `Presentation.exists_state_eq_of_stateBound_lt` is the boundedness claim:
  `Q_cold + 1` segments cannot have pairwise distinct states.
  The corridor those segments are segments *of* is built here too, so none of
  this is about an empty interface.  `IsBoundaryStub` is "the edges from `K` to
  ambient-cubic cold windows"; `boundaryStubs` is the manuscript's
  `h₁,…,h_m`, ordered by the object's own enumeration of vertex pairs, with
  `mem_boundaryStubs_iff` and `boundaryStubs_nodup`; `successorIndex` is the
  cyclic successor `hᵢ ↦ hᵢ₊₁` with `h_{m+1} = h₁`, and
  `successorIndex_injective` is "each boundary stub is the successor of at most
  one selected half-edge".  `Corridor` carries `lem:bridgeless`'s `m ≥ 2` as the
  field `twoStubs`, the selected branch-excess half-edge as `entry`, and the
  inside connection as `connected`; `Corridor.inside` is "the lexicographically
  first simple path joining the outside endpoint of `hᵢ` to the outside endpoint
  of `hᵢ₊₁`", selected by `Graph.FinitePathSelection.selectOfReachable` on the
  induced subgraph on `K` — the framework's own canonical schedule, not a
  choice made here.  `Corridor.Segment` is the initial segments `J`,
  `Corridor.activeInterface` is `T(J)`, and `activeInterface_card_le` bounds it
  uniformly.  `Corridor.eq_of_entry_eq` and `Corridor.eq_of_successorStub_eq`
  are the definition's two closing sentences: each selected half-edge has
  exactly one corridor, and each stub is the successor of at most one.
  `Corridor.presentation` turns a corridor into a `Presentation`, and
  `Corridor.CorridorState.exists_repeated_state`,
  `Corridor.CorridorState.reading_eq_of_state_eq` and
  `Corridor.activeInterface_card_le` are the three cut-state theorems read
  there, so the pigeonhole `lem:cold-corridor-first-failure` reaches (F5)'s
  repeat subcase by is a statement about the prefixes of a real corridor.  What a
  `Presentation` still receives from outside is `supp_X(r)` and `val_X(r)` —
  which is correct: a clause's coordinates are read by the owner of that
  clause's data, and the signature fixes only which coordinates exist and the
  cut-state only what is retained of them.
  `interfaceBudget S = 2·order + 2·2`, `exchangeBound = stateBound +
  interfaceBudget`, `stubExcess threshold S = threshold·order − 2(order−1)`,
  `overlapBound = stubExcess·(1 + threshold·(2^{exchangeBound+2} − 1))`,
  `extractionDenominator = exchangeBound·overlapBound + 1` are `M_cold`,
  `B_cold`, `D_cold` with the manuscript's `30` read as the two window
  interfaces plus the two boundary stubs and its `15` read as the external-stub
  numerator of `lem:cold-window-stub-excess`; no numeral is written.
  `Presentation.contextEquivalent_of_state_eq` is the paragraph's closing
  sentence: `FirstFailureResponse` names the (F2) discrepancy — same cut-state,
  different exact target response against some compatible context — and with it
  excluded, two segments with equal states are context-equivalent for the local
  replacement.  `firstFailureResponse_of_not_contextEquivalent` is the converse
  reading — "that discrepancy is recorded as a first failure of type (F2)" —
  and **both** directions are committed, so at a repeated state the
  manuscript's dichotomy is exhaustive in the ledger and not only in the
  module: either the responses agree, or (F2) has occurred.
  The signature itself is registered once, complete, by
  `Graph.ColdCorridor.declaredSignature`.  `SignatureClause` has **thirty-two**
  constructors — every kind the manuscript names in clauses (D1)–(D7), in its
  own order: (D1) boundary-degree entries; (D2) edge-rooted return data,
  completion-port data, first-entry receivers, connector lengths, receiver-entry
  channels and the Mersenne return tests; (D3) window labels, legal-label
  relations, packed-window incidences and cross-window incidence data; (D4) raw
  curvature coordinates; (D5) canonical traces, trace-incidence coordinates,
  connector-band constraints, cross-port theta constraints, silent-basin
  response coordinates and carrier restrictions; (D6) fan centers, fan-safe
  pairs, certificate labels, closed fan-window pairs, hybrid incidence entries,
  candidate ledger entries, overlap demands, decorated handoff fan response
  coordinates and decorated handoff-arm coordinates; (D7) selected surplus
  ports, canonical port returns, open-port suppression paths, triangular-port
  response triangles and sparse surplus-pair response coordinates.
  `SignatureClause.mem_all` makes "no other local response coordinate is
  available to a quotient" a type-level fact, and
  `Fixtures/ColdCorridorSignature.lean` checks the per-clause counts
  `1, 6, 4, 1, 6, 9, 5` and the total `32` by `decide`, so a kind added,
  dropped, or moved between clauses fails the build.
  A coordinate is the manuscript's own tuple: `Coordinate` carries `supp_X(r)`
  as a subset of the bounded active interface and `ι` as its label, so no arity
  is invented anywhere.  `interfaceWidth order = 2·order + 2·2` is the
  manuscript's bounded interface, checked to be `30` at order thirteen; every
  index is bounded by it rather than by the graph, which is why `Q_cold` is a
  constant.  "Their labelled subcoordinates" of (D5) is not a thirty-third kind:
  (D8) already generates the labelled copies and restrictions of every entry of
  (D1)–(D7).
- **What it should do.** Exactly this: retain the four items, be complete for
  the local replacement despite retaining no (D8) coordinate, and be bounded by
  a constant of the signature.
- **Gap.** none.  The signature is the manuscript's complete one — all
  thirty-two kinds of (D1)–(D7), with (D8) as the framework's closure — so
  `Q_cold` is the cardinality of the manuscript's own cut-state and `M_cold`,
  `B_cold`, `D_cold` are its values.  Nothing is registered as a placeholder,
  and the corridor the cut-state is taken along is constructed rather than
  assumed, so no theorem here is vacuous.  `lem:bridgeless` enters as the named
  field `twoStubs`: it is a theorem about the selected object with its own place
  in the manuscript, not part of this definition, and it is cited where the
  definition cites it.  The constants are defined and proved here and consumed
  by the later cold facts: Row 50 reads the exchange bound, and the germ,
  extraction and closure rows consume the cold bounds through the ledgered
  facts.  **Facts passes.**
- **Ledger and residual.** `Spine.coldCorridorStateRow` is a `factOnly` atomic
  Strategy with `Requires := [coldWindowLedgerSplit]` and `Produces :=
  [coldCorridorState]`.  It reads the hot/cold partition appended at node
  `[22]`; it cannot be published on a detached object or before entering that
  literal residual.  The
  committed statement has three clauses: the retention's completeness, the
  `Q_cold` pigeonhole, and *both* directions of the (F2) sentence — the second
  direction was proved but unregistered until the registered-fact review, which
  left the manuscript's dichotomy at a repeated state half-stated on the
  ledger.  Its
  cut-state clauses are signature theorems, but their ledger fact is specialized
  to and stores the incoming cold residual rather than being published
  source-free.  The residual is unchanged: `factOnly` supplies
  `RefinementSystem.refl`, the equality refinement.  The committed statement is
  `Spine.Holds .coldCorridorState`, quantified over *every*
  `ColdCorridor.Presentation` of the object's corridor segments, so no corridor
  construction travels with the fact — a corridor is data, and no fact can carry
  data.
- **Transport and terminals.** `Graph.ColdCorridor` owns the mathematics;
  `Spine.coldCorridorStateRow` owns the concrete `K .coldCorridorState`
  manifest and the commit.  `Spine.runCold` only composes it with Row 44 through
  `AtomicCT.run` against one immutable prefix.  There is no terminal at this
  row: it produces a fact and returns the ledger.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:declared-coordinate-signature` | def | `ColdCorridor.DeclaredSignature`<br>`ColdCorridor.Generated`<br>`ColdCorridor.declaredSignature`<br>`ColdCorridor.SignatureClause`<br>`ColdCorridor.Coordinate` | no CT — registered data |
| `def:cold-corridor-first-failure` | def | `ColdCorridor.IsBoundaryStub`<br>`ColdCorridor.boundaryStubs`<br>`ColdCorridor.successorIndex`<br>`ColdCorridor.Corridor`<br>`ColdCorridor.Corridor.inside`<br>`ColdCorridor.Corridor.activeInterface`<br>`ColdCorridor.Corridor.presentation`<br>`ColdCorridor.CutState`<br>`ColdCorridor.Presentation.state`<br>`ColdCorridor.Presentation.contextEquivalent_of_state_eq`<br>`ColdCorridor.stateBound`<br>`ColdCorridor.exchangeBound`<br>`ColdCorridor.overlapBound`<br>`ColdCorridor.extractionDenominator` | no CT — `Spine.coldCorridorStateRow` |

The corridor construction, the cut-state and the constant clauses of
`def:cold-corridor-first-failure` are all consumed here; its (F1)–(F4) clause
list is Rows 45–48's and its `M_cold` bound is Row 51's.
`def:declared-coordinate-signature` is first consumed here, and Row 44 reads the
same registration.

**CT composition at this row.** No CT.  Both clauses are theorems about a
registered finite signature: one is an induction over the generation of a
declared coordinate, the other a pigeonhole on `Fintype.card`.  A CT would add
nothing — there is no response algebra to compare, no schedule to search, and
no residual to restrict.

### Row 44 — Same-interface table `[157]`

- **Paper fact.** `def:cold-same-interface-table` defines a finite table whose
  *rows are equal-length cold bounded germs and the short self-return exceptions
  of* `lem:cold-short-self-return-filter`, each row recording (T1) the two
  boundary vertices and their boundary-degree profile, (T2) the two terminal
  cold-window stubs and their offsets in `{0,…,12}`, (T3) the exact response
  profile generated by `def:declared-coordinate-signature`, and (T4) the target
  truth value of every compatible completion represented by that exact profile.
  A row is *realizing*, *distinguishing*, or *neutral*.
  `lem:cold-same-interface-table` then closes every row: realizing gives a
  dyadic cycle, handoff transfers the charge, distinguishing gives a
  target-defective quotient, and neutral gives a proper-support target-complete
  quotient forbidden by `cor:uncompressible`.
  `lem:cold-short-self-return-filter` supplies the exceptional rows: for
  `1 \le \ell \le 39` the smear interval `[\ell,\ell+12]` avoids `{4,8,16,32}`
  only for `\ell \in \{17,18,19,33,34,35,36,37,38,39\}`, and for
  `1 \le \ell \le 32` only for `\ell \in \{17,18,19\}`.
- **What the Lean does.** `Graph.ColdCorridor.Record` has exactly five fields,
  one per recorded clause: `boundaryDegrees` (T1), `stubs` and `offsets` (T2),
  `state` (T3), and `truth` (T4).  `Record.equivProduct` carries `Fintype` onto
  it and `tableBound S = Fintype.card (Record S)` is the manuscript's "the table
  is finite because the support size, boundary size, window labels, and declared
  coordinate labels are bounded" — a clause of the committed fact, not merely a
  definition beside it.
  `Graph.ColdCorridor.TableRow S Baseline Target object Handoff` is a row at a
  proper connected support of the object.  It `extends
  ColdCorridor.BoundedGerm S Baseline Target object`, which is
  `def:cold-bounded-germ` itself and is the local germ shape Rows 52–54 use for the
  length-changing germs: `support`/`connected`/`proper` give
  the germ's own boundary piece `Q[x,y]` through
  `Strategy.InterfaceReplacement.SupportAtom.properAtom`, `canonical` is the
  second same-interface representative `E`, `sameProfile` is the inherited
  boundary-degree profile, and `record` is the finite same-interface table
  record containing (T1)–(T4), including the target-response truth profile.  A
  row adds exactly two clauses to the germ.  `equalLength`
  is `def:cold-bounded-germ`'s `δ = 0` — `BoundedGerm.increment` is the increment
  `δ := |E| − |Q[x,y]|` in `Int`, `increment_eq_zero` proves it vanishes on
  every row, and the row's committed fact says so, which is what makes a row a
  row — `baseline` is the standing
  hypothesis at the
  replacement, and `admissible` is `def:admissible-rank-quotient` spent
  exactly where `lem:cold-same-interface-table` spends it — a row that is not
  handed off and whose two representatives *are* target-completely identified
  has a strictly smaller proper representative in the sense of
  `def:proper-quotient-representative`.
  `TableRow.Realizing`, `TableRow.Distinguishing` and `TableRow.Neutral` are the
  three-way classification: realizing is the target at the germ's own completion
  in `G`, distinguishing is `Graph.Response.TargetDefect` between the two
  representatives, neutral is neither.
  `ColdCorridor.row_closed` is `lem:cold-same-interface-table`.  It takes the
  target's isomorphism invariance and the two facts the manuscript's proof
  spends — the selected object avoids the target, and no proper support of it
  admits a target-complete compression — and returns `¬ Realizing ∧ (Handoff ∨
  Distinguishing)`.  A realizing row would hand the object the target it avoids,
  through `TableRow.target_of_realizing` and the decomposition's
  `reconstructionIso`; a row that is neither handed off nor distinguishing is a
  `Strategy.InterfaceReplacement.CompressibleSupport` of its own support, built
  field by field by `TableRow.compressibleSupport_of_not_distinguishing`, which
  node `[14]` has excluded.  `Handoff` is a graph-local support predicate
  supplied to the row theorem by the already-closed ledger context, never a
  field a row may choose, so no row escapes by naming its own.
  `ColdCorridor.SelfReturn` is the table's *second* row family, the short
  self-return exceptions.  It carries the outside length `\ell`, the row it
  contributes, and the smear itself — "smearing over the window offsets tests
  the whole interval `[\ell,\ell+12]`" is the field `smear`, which says every
  accepted length the interval tests is realized in the object through the
  corresponding cold-window offset.  `SelfReturn.surviving` then *proves*, from
  the selection's own avoidance, that the length is one of the filter's
  surviving exceptions rather than assuming it; `SelfReturn.target_of_not_surviving`
  is its contrapositive, the manuscript's "all other short self-returns realize
  a dyadic cycle".  `ColdCorridor.selfReturn_closed` is
  `lem:cold-same-interface-table`'s "in particular" at that family: the length
  survives *and* the row is closed.
  `ColdCorridor.SurvivesSmear`, `exists_accepted_of_not_survivesSmear`,
  `survivingLengths` and `mem_survivingLengths_iff` are
  `lem:cold-short-self-return-filter` itself: the surviving condition, the "all
  other short self-returns realize a dyadic cycle" clause, and the computed
  surviving set with its characterization.  The manuscript's two lists are *checked*, not
  written: `Fixtures/ColdCorridorShortSelfReturn.lean` evaluates
  `survivingLengths PowerOfTwoLength 12 39 = [17,18,19,33,34,35,36,37,38,39]` and
  `survivingLengths PowerOfTwoLength 12 32 = [17,18,19]` by `decide`.  No
  declaration in `Hypostructure.Graph` contains either list.
- **What it should do.** Exactly this: record (T1)–(T4) in a finite type,
  classify a row three ways, and close every row against the two facts the
  branch already carries.
- **Gap.** none.  Both of `def:cold-same-interface-table`'s row families are
  present and both are closed: the equal-length cold bounded germs are
  `TableRow`, closed by `row_closed`, and the short self-return exceptions are
  `SelfReturn`, closed by `selfReturn_closed` after their lengths are proved to
  survive the filter.  The manuscript's exceptional sets `{17,18,19,33,…,39}`
  and `{17,18,19}` are computed, not written.  The corridor these rows are read
  along is constructed at Row 43 (`ColdCorridor.Corridor`), so the table is
  about real prefixes of a real corridor.  **Facts passes.**
- **Ledger and residual.** `Spine.sameInterfaceTableRow` is a `factOnly` atomic
  Strategy with `Requires := [selection, uncompressible]` and
  `Produces := [coldSameInterfaceTable]`.  The committed statement now has four
  clauses, not two: the row closure, the self-return closure, the table's own
  finiteness `tableBound = Fintype.card (Record S)`, and `δ = 0` on every row.
  The last two were theorems no fact mentioned until the registered-fact review;
  they are `def:cold-same-interface-table`'s finiteness claim and
  `def:cold-bounded-germ`'s equal-length condition, so leaving them off the
  ledger left two of the definition's own clauses unregistered.  Both prerequisites are read by exact
  semantic key through sealed `FactInputs.get`; neither producer, predecessor
  depth, nor execution position is named.  Those two are exactly the facts the
  manuscript's proof spends and the only two it spends.  The residual is
  unchanged — `RefinementSystem.refl` — and the committed statement is
  `Spine.Holds .coldSameInterfaceTable`, quantified over every handoff ledger and
  every row, so no germ, support, or table travels with the fact.
- **Transport and terminals.** `Graph.ColdCorridor` owns the mathematics;
  `Spine.sameInterfaceTableRow` owns the concrete `K .selection`,
  `K .uncompressible`, and `K .coldSameInterfaceTable` manifest and the commit.
  `Spine.runCold` runs it after Row 43 against one immutable prefix.  A branch
  that has not proved node `[14]` still fails at the row manifest because the
  sealed inputs cannot supply `K .uncompressible`.  No terminal at this row.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:cold-bounded-germ` | def | `ColdCorridor.BoundedGerm` (`canonical`, `sameProfile`, `record`)<br>`ColdCorridor.TableRow` (`equalLength`, `admissible`)<br>`BoundedGerm.increment`<br>`TableRow.increment_eq_zero` | no CT |
| `def:cold-same-interface-table` | def | `ColdCorridor.Record`<br>`ColdCorridor.tableBound`<br>`ColdCorridor.TableRow`<br>`TableRow.Realizing`, `TableRow.Distinguishing`, `TableRow.Neutral` | no CT |
| `lem:cold-same-interface-table` | lem | `ColdCorridor.row_closed`<br>`TableRow.compressibleSupport_of_not_distinguishing`<br>`TableRow.target_of_realizing` | no CT — `Spine.sameInterfaceTableRow` |
| `lem:cold-short-self-return-filter` | lem | `ColdCorridor.SurvivesSmear`<br>`ColdCorridor.exists_accepted_of_not_survivesSmear`<br>`ColdCorridor.survivingLengths`<br>`ColdCorridor.mem_survivingLengths_iff`<br>`ColdCorridor.SelfReturn`<br>`SelfReturn.surviving`<br>`SelfReturn.target_of_not_surviving`<br>`ColdCorridor.selfReturn_closed` | no CT — checked in `Fixtures.ColdCorridorShortSelfReturn` |

`def:cold-bounded-germ` is consumed here only in its equal-length case, which is
the case the table is about; its length-changing case is
`lem:cold-bounded-germ-trichotomy`'s and belongs to Rows 52–54.  The neutral-row
clause of `lem:cold-same-interface-table` is also what Row 59 would need.

**CT composition at this row.** No CT.  The closure is a case split on a
three-way classification whose two closable branches are discharged by facts
already on the ledger — the selection's avoidance and node `[14]`'s
uncompressibility.  There is no schedule to search, no response table to build,
and no budget to spend, so a CT would only interpose machinery between a fact
and its consequence.


### Row 45 — (F1) producer `[154]`, `[155]`

- **Paper fact.** `def:cold-corridor-first-failure` (F1): "a compatible
  completion through a cold-window offset realizes a power-of-two cycle".
  `lem:cold-corridor-first-failure` (i): "case (F1) is a dyadic cycle in `G`",
  and its proof says "the displayed completion is literally a cycle of
  power-of-two length in `G`, impossible in a counterexample".
- **What the Lean does.** `Graph.ColdCorridor.Window` is the placed cold window:
  the `order` positions of an induced window, injective, with consecutive
  positions adjacent.  `Window.segment` is the walk along it between two
  offsets, with `segment_length` its step count.
  `Corridor.prefixWalk` maps the corridor's own inside path into the ambient
  object along `induceEmbedding`.  `Corridor.displayedCompletion` is the
  manuscript's completion, built and not supplied: the window position the entry
  stub lands on, the stub itself, the corridor prefix, the return adjacency, and
  the window segment back between the two offsets — a closed walk of
  `object.graph` at the entry position.
  `Corridor.FirstFailureCycle` is clause (F1): some pair of offsets, with a stub
  adjacency and a return adjacency, makes that walk a cycle of accepted length.
  `Corridor.hasCycleWithLength_of_firstFailureCycle` is clause (i): the
  completion *is* an accepted cycle of the object, so the certificate is the walk
  itself and nothing is transported.
  `Spine.coldFailureCycleRow` commits the consequence: node `[1]`'s avoidance
  denies the object any accepted cycle, so (F1) never occurs.
- **What it should do.** Exactly this: display the completion, ask it to be an
  accepted cycle, and close the alternative against the selection.
- **Gap.** none.  **Facts passes.**
- **Ledger and residual.** `coldFailureCycleRow` is `factOnly` with
  `Requires := [selection]`, `Produces := [coldFailureCycle]`; the avoidance is
  read by exact semantic key through sealed `FactInputs.get`, and the residual is
  unchanged (`RefinementSystem.refl`).  The committed statement is quantified
  over every component, corridor, window order, window and segment, so no
  corridor or window travels with the fact.
- **Transport and terminals.** `Graph.ColdFirstFailure` owns the mathematics;
  the row owns the concrete `K .coldFailureCycle` commit.  `Spine.runCold` runs
  it third, after the cut-state and the table, against one immutable prefix.  No
  terminal at this row.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:cold-corridor-first-failure` (F1) | def | `ColdCorridor.Window`<br>`ColdCorridor.Window.segment`<br>`ColdCorridor.Corridor.prefixWalk`<br>`ColdCorridor.Corridor.displayedCompletion`<br>`ColdCorridor.Corridor.FirstFailureCycle` | no CT — `Spine.coldFailureCycleRow` |
| `lem:cold-corridor-first-failure` (i) | lem | `ColdCorridor.Corridor.hasCycleWithLength_of_firstFailureCycle` | standalone |

**CT composition at this row.** No CT.  The clause is a decidable predicate over
a finite offset schedule and its elimination is the identity on a walk; a CT
would interpose machinery between a constructed cycle and its certificate.

### Row 46 — (F2) producer `[154]`, `[156]`

- **Paper fact.** The first-failure F2 alternative says two corridor prefixes
  with the same displayed data have different target response against some
  compatible outside context.  The routing statement is target-defect, not an
  ambient cycle.
- **What the Lean does.** `FirstFailureDefect` is the corridor discrepancy
  itself.  The row commits the target-complete denial and the F2-free
  context-equivalence consequence.  Both are stated directly over the corridor,
  presentation, index, and boundary-piece map.
- **Gap.** none for carrier cleanup.  The row has no side object and no branch
  hypothesis.
- **Ledger and residual.** `coldFailureDefectRow` is `factOnly` with
  `Requires := [coldCorridorState]` and `Produces := [coldFailureDefect]`.
  The state fact is read by `FactInputs.get`; residual unchanged.
- **Transport and terminals.** No transport payload and no terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:cold-corridor-first-failure` (F2) | def | `ColdCorridor.Corridor.FirstFailureDefect` | no CT — `Spine.coldFailureDefectRow` |
| `lem:context-universality` | lem | `ColdCorridor.Corridor.not_targetComplete_of_firstFailureDefect`<br>`ColdCorridor.Corridor.contextEquivalent_of_not_firstFailureDefect`<br>`Graph.Response.notTargetComplete_of_targetDefect` | standalone |

**CT composition at this row.** No CT.

### Row 47 — (F3) producer `[154]`, `[157]`

- **Paper fact.** The first-failure F3 alternative is a target-complete
  compression by a strictly smaller proper representative, forbidden by
  `cor:uncompressible`.
- **What the Lean does.** `FirstFailureCompression` carries the two prefixes and
  the compression clauses.  `FirstFailureCompression.not_occurs` eliminates the
  case using the ledger's uncompressibility fact.
- **Gap.** none.
- **Ledger and residual.** `coldFailureCompressionRow` is `factOnly` with
  `Requires := [uncompressible]` and `Produces := [coldFailureCompression]`.
  The requirement is read by `FactInputs.get`; residual unchanged.
- **Transport and terminals.** No transport payload and no terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:cold-corridor-first-failure` (F3) | def | `ColdCorridor.Corridor.FirstFailureCompression`<br>`ColdCorridor.Corridor.FirstFailureCompression.Occurs` | no CT — `Spine.coldFailureCompressionRow` |
| `lem:cold-corridor-first-failure` (iii) | lem | `ColdCorridor.Corridor.FirstFailureCompression.compressibleSupport`<br>`ColdCorridor.Corridor.FirstFailureCompression.elim`<br>`ColdCorridor.Corridor.FirstFailureCompression.not_occurs` | standalone |

**CT composition at this row.** No CT.

### Row 48 — (F4) producer `[154]`, `[156]`

- **Paper fact.** The corridor first enters a declared Type B handoff support or
  the route-8 support already recorded upstream.
- **What the Lean does.** `FirstFailureHandoff` is a predicate over a ledger
  supplied support predicate `Handoff : Finset object.Vertex -> Prop`.  It
  records that the current head lies in such a support and no earlier head did.
- **Gap.** none for carrier cleanup.  The old handoff object is gone; the row
  quantifies over the support predicate and returns only a proposition.
- **Ledger and residual.** `coldFailureHandoffRow` is `factOnly` with
  `Requires := [coldCorridorState]` and `Produces := [coldFailureHandoff]`.
  The requirement is read by `FactInputs.get`; residual unchanged.
- **Transport and terminals.** No handoff object travels on the row output.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:cold-corridor-first-failure` (F4) | def | `ColdCorridor.Corridor.FirstFailureHandoff` | no CT — `Spine.coldFailureHandoffRow` |
| `lem:cold-corridor-first-failure` (iv) | lem | `ColdCorridor.Corridor.handoff_mem` | standalone |

**CT composition at this row.** No CT.

### Row 49 — (F4) membership `[156]`

- **Paper fact.** The F4 charge is sent to a support already present in the
  upstream ledger; it is not closed inside the corridor.
- **What the Lean does.** `Corridor.handoff_mem` extracts
  `∃ support, Handoff support ∧ corridor.head segment ∈ support` from the F4
  fact.  No envelope, subtype payload, or routing object is returned by a row.
- **Gap.** none for carrier cleanup.
- **Ledger and residual.** This membership is contained in the F4 fact itself;
  the later transfer row reads the F4 key directly.
- **Transport and terminals.** No terminal and no payload.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:cold-corridor-first-failure` (iv), membership | lem | `ColdCorridor.Corridor.handoff_mem` | standalone |

**CT composition at this row.** No CT.

### Row 50 — First-failure routing facts `[154]`

- **Paper fact.** Every cold return corridor has a first failure: terminal
  corridor inside the cold bound or a repeated state after `Q_cold + 1` states.
- **What the Lean does.** `coldFailureRoutingRow` commits the existence
  dichotomy as the single ordinary fact `K .coldFailureRouting`.
- **Gap.** none for carrier cleanup.  The row no longer defines or transports a
  cold-branch object.
- **Ledger and residual.** `factOnly` with `Requires := [coldCorridorState]` and
  `Produces := [coldFailureRouting]`; residual unchanged.
- **Transport and terminals.** No terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:cold-corridor-first-failure`, existence | lem | `ColdCorridor.Corridor.exists_firstFailure` | no CT — `Spine.coldFailureRoutingRow` |

**CT composition at this row.** No CT.

### Row 51 — Terminal-F5 residual `[154]`

- **Paper fact.** The finite first-failure exchange bound, the hot/cold window
  split, hot-failure cold mass, selected branch-excess identity, and
  ambient-cubic stub-excess inequality are each facts used by the cold
  quantitative ledger.
- **What the Lean does.** These are separate ordinary ledger facts:
  `coldExchangeBoundRow`, `coldWindowLedgerSplitRow`,
  `coldHotFailureMassRow`, `coldSelectedBranchExcessRow`, and
  `coldAmbientCubicStubExcessRow`.  Each appends exactly one `Spine.Key` fact.
  Node `[22]` now creates the partition itself from the selected maximal
  packing.  The later split row reads `barrierCap` and forwards that exact
  partition together with the spine estimate and sparse-pressure facts.  It
  never substitutes `hot = ∅` and `cold = packing`.  The hot-failure mass row
  then reads that exact
  split together with `densityCap`, `spineSurplusEstimate`, and
  `sparsePressureNearCubic`; and the
  ambient-cubic stub-excess row reads `spineSurplusEstimate` and
  `sparsePressureNearCubic`.  These are ordinary upstream keys, not a cold
  carrier.
- **Gap.** The former fabricated partition has been removed.  The first
  downstream failure is now exposed honestly in `coldHotFailureMassRow`: the
  manuscript's quantitative hot-failure estimate
  `windowRate * hot.card ≤ surplusScale * vertexCount` has not yet been
  derived from the live-package classification.  That next mathematical fact
  must be implemented before rows `[150]` onward elaborate; it may not be
  restored by choosing the hot family to be empty.
- **Ledger and residual.** The full residual remains the same `ExactLedger`
  cursor.  `coldWindowLedgerSplit` requires the node-`[22]` no-arm key
  `barrierCap`, together with `windowPackageSeparated`, `maximalPacking`,
  `spineSurplusEstimate`, and `sparsePressureNearCubic`;
  `coldHotFailureMass` requires `coldWindowLedgerSplit`, `densityCap`,
  `spineSurplusEstimate`, and `sparsePressureNearCubic`, and
  `coldAmbientCubicStubExcess` requires `coldSelectedBranchExcess`,
  `spineSurplusEstimate`, and `sparsePressureNearCubic`.  Later F5 rows append
  facts on top of the same ledger.
- **Transport and terminals.** No separate terminal object.

**CT composition at this row.** No CT.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| exchange bound | lem | `ColdCorridor.Corridor.exchange_card_le` | no CT — `Spine.coldExchangeBoundRow` |
| hot/cold split | lem | `ColdCorridor.coldCount_add_hotCount` | no CT — `Spine.coldWindowLedgerSplitRow` |
| hot failure cold mass | lem | `ColdCorridor.hotFailure_coldMass` | no CT — `Spine.coldHotFailureMassRow` |
| selected branch excess | def/lem | `ColdCorridor.selectedBranchExcess_length` | no CT — `Spine.coldSelectedBranchExcessRow` |
| ambient-cubic stub excess | lem | `ColdCorridor.branchExcess_ge_of_cubic` | no CT — `Spine.coldAmbientCubicStubExcessRow` |

### Row 52 — `[155]` G1 realizing

- **Paper fact.** A realizing bounded germ would close a dyadic cycle in the
  selected object, contradicting the selection fact.
- **What the Lean does.** `coldGermRealizedRow` reads `selection` with
  `FactInputs.get` and commits that no bounded germ is realizing, plus the
  trichotomy statement used by later routing.
- **Gap.** none.
- **Ledger and residual.** `Requires := [selection]`,
  `Produces := [coldGermRealized]`; residual unchanged.
- **Transport and terminals.** No payload.

**CT composition at this row.** No CT.

### Row 53 — `[156]` G2 distinguishing

- **Paper fact.** A distinguishing germ gives a target-incomplete quotient in
  every immutable profile fibre.
- **What the Lean does.** `coldGermDistinguishedRow` reads the exact
  `coldWindowLedgerSplit` appended at node `[22]` and commits the current-object
  germ theorem on that same residual.  `coldGermRoutedRow` reads this theorem
  directly from the ledger.
- **Gap.** none for carrier cleanup.  This is a semantic fact, not a closure by
  itself.
- **Ledger and residual.** `Requires := [coldWindowLedgerSplit]`, `Produces :=
  [coldGermDistinguished]`; the step is fact-only and preserves the residual.
- **Transport and terminals.** No payload and no terminal.

**CT composition at this row.** No CT.

### Row 54 — `[157]` G3 neutral

- **Paper fact.** A neutral length-changing germ gives a target-complete
  compression, forbidden by uncompressibility; the increment arithmetic facts
  are recorded at the same row.
- **What the Lean does.** `coldGermSilentRow` reads `uncompressible` with
  `FactInputs.get` and commits the neutral exclusion plus the arithmetic clauses.
- **Gap.** none.
- **Ledger and residual.** `Requires := [uncompressible]`,
  `Produces := [coldGermSilent]`; residual unchanged.
- **Transport and terminals.** No payload.

**CT composition at this row.** No CT.

### Row 55 — Core dispatch (F1) `[155]`

- **Paper fact.** F1 is already excluded by the selection fact.
- **What the Lean does.** No separate dispatcher is exported.  The proof is the
  ledger composition: Row 45 appends the F1 exclusion, and later rows read the
  exact prefix.
- **Gap.** none for carrier cleanup.
- **Ledger and residual.** One immutable ledger prefix.
- **Transport and terminals.** No side dispatcher.

**CT composition at this row.** No CT.

### Row 56 — Core dispatch (F3) `[157]`

- **Paper fact.** F3 is already excluded by uncompressibility.
- **What the Lean does.** No separate dispatcher is exported.  Row 47 appends
  the F3 exclusion, and later rows retain that fact in the same ledger.
- **Gap.** none for carrier cleanup.
- **Ledger and residual.** One immutable ledger prefix.
- **Transport and terminals.** No side dispatcher.

**CT composition at this row.** No CT.

### Row 57 — (F4) dispatch arm `[156]`

- **Paper fact.** The F4 arm transfers to a support already recorded upstream.
- **What the Lean does.** `coldHandoffTransferRow` reads `coldFailureHandoff`
  and `route8TerminalNoGo` by exact key and commits the membership theorem for
  every supplied handoff predicate.  The detached `typeBExcluded`
  prerequisite has been removed; the Type-B clean arm closes through Core's
  impossible-fact path.  No handoff object is constructed or returned.
- **Gap.** none for carrier cleanup.
- **Ledger and residual.** `Requires := [coldFailureHandoff,
  route8TerminalNoGo]`, `Produces := [coldHandoffTransfer]`; residual
  unchanged.
- **Transport and terminals.** Ledger fact only; no terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:cold-corridor-first-failure` (iv), transfer | lem | `ColdCorridor.Corridor.handoff_mem` | no CT — `Spine.coldHandoffTransferRow` |

**CT composition at this row.** No CT.

### Row 58 — (F5) extraction `[153]`, `[154]`

- **Paper fact.** After first-failure routing, the remaining F5 branch-excess
  incidences form current-object bounded-germ candidates, and greedy extraction
  gives a vertex-disjoint subfamily at the manuscript's constant
  `D_cold = M_cold B_cold + 1`.
- **What the Lean does.** `coldGermExtractionRow` reads `coldFailureRouting`,
  `coldExchangeBound`, and `coldAmbientCubicStubExcess` by `FactInputs.get`,
  then commits `ColdCorridor.ColdGermExtractionLocal` for the current object's
  bounded-germ candidate families.  The input family is constrained by
  `ColdCorridor.CandidateGermFamily`, overlap is tested on literal current
  supports, and the extracted disjoint subfamily is an existential conclusion
  of the fact.  No arbitrary `Germ` type, disjoint-family carrier, or theorem
  bundle is exported as the ledger fact.
- **Gap.** none for carrier cleanup.
- **Ledger and residual.** `Requires := [coldFailureRouting,
  coldExchangeBound, coldAmbientCubicStubExcess]`,
  `Produces := [coldGermExtraction]`; residual unchanged.
- **Transport and terminals.** No payload.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:cold-corridor-first-failure` (F5 entry) | lem | `ColdCorridor.Corridor.exists_firstFailure` | read from `K .coldFailureRouting` |
| `lem:cold-germ-extraction` | lem | `ColdCorridor.CandidateGermFamily`<br>`ColdCorridor.ExtractedGermFamily`<br>`ColdCorridor.ColdGermExtractionLocal`<br>`ColdCorridor.coldGermExtractionLocal` | no CT — `Spine.coldGermExtractionRow` |

**CT composition at this row.** No CT.

### Row 58a — Positive germ production `[153]`

- **Paper fact.** The quantitative chain makes the extracted cold-germ family
  nonempty.
- **What the Lean does.** Positivity is the final conjunct of
  `ExtractedGermFamily`, produced existentially by the current-object
  `ColdGermExtractionLocal` fact stored at Row 58.  The former standalone
  universal `coldPositiveGermRow` was deleted from the executable chain: it
  accepted caller-supplied arithmetic objects and its ledger reads were unused.
- **Gap.** none; there is no separate positive-germ node.
- **Ledger and residual.** No additional commit.  Consumers obtain positivity
  from `K .coldGermExtraction` on the same residual.
- **Transport and terminals.** No separate transport or terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| positive extracted germ | lem | `ColdCorridor.ExtractedGermFamily` | stored inside `K .coldGermExtraction` |

**CT composition at this row.** No CT.

### Row 59 — (F5) G2 routing after G1/G2/G3 `[157]`

- **Paper fact.** Once G1 and G3 are excluded, a length-changing bounded germ is
  distinguishing, and G2 routes that distinguishing germ to the target-defect
  exit.
- **What the Lean does.** `coldGermRoutedRow` reads `coldGermRealized`,
  `coldGermDistinguished`, and `coldGermSilent` by `FactInputs.get`.  It first
  applies `ColdCorridor.boundedGerm_not_survives`, then reads the committed G2
  fact to publish the corresponding `Response.TargetComplete` failure as part
  of `K .coldGermRouted`.
- **Gap.** none for carrier cleanup.  The fact is ledger-native and local to
  the current object; it is a routing fact, not the framework closure key.
- **Ledger and residual.** `Requires := [coldGermRealized,
  coldGermDistinguished, coldGermSilent]`, `Produces := [coldGermRouted]`;
  residual unchanged.
- **Transport and terminals.** No payload.  Not a Core closure.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:cold-bounded-germ-trichotomy`, G2 remainder | lem | `ColdCorridor.boundedGerm_not_survives`<br>`BoundedGerm.not_targetComplete_of_distinguishing` through `K .coldGermDistinguished` | no CT — `Spine.coldGermRoutedRow` |

**CT composition at this row.** No CT.

### Row 60 — Registrations `atStage` `[145]`–`[157]`

- **Paper fact.** The manuscript orders the cold alternatives; it does not
  require an application-owned registration payload.
- **What the Lean does.** `Spine.runCold` composes the rows directly and
  requires the surviving cold prefix keys in `known`.  Those prefix facts are
  also consumed at the row that spends them: the node `[22]` split is already
  present in the incoming `known` list and is read by the cold rows.  Its
  producer additionally requires `barrierCap`, so the cold corridor can only
  descend from the no-arm cursor of the framework `Decision` at `[22]`;
  density and near-cubic spine facts at the hot/cubic mass rows, sparse/negative
  and large-budget survivor facts at first-failure routing and branch closure,
  and Type B/route-8 closure facts at the handoff-transfer row.  Each row
  prerequisite is checked by the exact key index, and each row appends only its
  declared production.  The run file no longer passes `encode`, `fact.down`, or
  `PLift` wrapper callbacks; the row declarations already publish concrete
  `Spine.Key` facts.
- **Gap.** The root assembly still needs the positive node-`[21]` package
  publication wired into the entropy-package continuation. After correcting
  node `[21]`, its legacy-named `windowPackageSeparated` key carries only the
  certified finite enumeration. The cold split no longer treats that fact as
  a `WindowPackageStatement`: it reads the enumeration only to enforce literal
  ancestry from `[21]`, reads `barrierCap` from `[22]`, and derives its packing
  and hot/cold arithmetic from the current residual's existing facts. A
  distinct later package fact is still required by the entropy-package
  continuation, where the manuscript's discharged sparse exits and
  near-cubic estimate are available.
- **Ledger and residual.** One `ExactLedger` is threaded through the block.
- **Transport and terminals.** No registration object, no side dispatcher.

**CT composition at this row.** No CT.

### Row 61 — Cold oval closure `[145]`–`[157]`

- **Paper fact.** The cold branch should terminate at the paper's oval once all
  alternatives have been routed.
- **What the Lean does.** `coldBranchClosedRow` reads `coldPositiveGerm`,
  `coldGermExtraction`, `coldGermRouted`, `coldSameInterfaceTable`,
  `largeBudgetResidual`, `negativeSupport`, and `sparseSurplusSurvivor` with
  `FactInputs.get` and appends the ordinary fact `K .coldBranchClosed`.  The fact is
  `ColdCorridor.NoTerminalColdResidual` on the current residual: the extraction
  fact turns any terminal candidate family into a positive extracted subfamily,
  `coldGermRouted` closes its length-changing member, and the same-interface
  table fact closes equal-length table/self-return rows.  `Spine.runCold`
  then reads the incoming `K .coldTerminalResidual` fact at the closure boundary
  and appends Core's reserved closure key by `closeIncompatible` against the
  new `K .coldBranchClosed` fact.
- **Gap.** none for carrier cleanup.
- **Ledger and residual.** `Requires := [coldPositiveGerm,
  coldGermExtraction, coldGermRouted, coldSameInterfaceTable,
  largeBudgetResidual, negativeSupport, sparseSurplusSurvivor]`,
  `Produces := [coldBranchClosed]`; residual
  unchanged.  `Spine.runCold` requires both `K .coldTerminalResidual` and the
  upstream `K .coldWindowLedgerSplit` in the incoming
  key index and returns `closed :: coldBranchClosed :: coldGermRouted ::
  coldPositiveGerm :: coldGermExtraction :: ... :: known`, preserving the
  incoming residual and all upstream facts.  The fixture
  `runCold_closure_reason` checks that the closure entry is exactly
  `AutomaticClosureReason.incompatibleFacts (name .coldTerminalResidual)
  (name .coldBranchClosed)`.
- **Transport and terminals.** Ledger facts only.  The no-terminal statement
  is an ordinary key, and the terminal oval is the framework-owned closure key
  appended from incompatible ordinary facts.  No wrapper, side theorem bundle,
  custom handoff, result carrier, or unproduced positive residual is present.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| cold terminal oval | thm | `ColdCorridor.noTerminalColdResidual_of_routing` | `Spine.coldBranchClosedRow` |

**CT composition at this row.** No CT.

### Trailing note — deleted stale fixtures

The stale non-PDE cold aggregation fixtures are no longer source artifacts of
the EG proof.  They exercised obsolete side channels rather than ledger facts.
The PDE registry files are left untouched by request.

### Row 62 — `[109]` route-8 arm placement

`Spine.route8ResidualRow` now has the correct ledger shape: its manifest
requires the finite descent fact, the selected silent-residual fact, and the
no-exit `(4)`, `(5)`, `(6)`, and `(7)` facts, then appends only
`route8Residual`.  The full residual is carried by the `ExactLedger` prefix; the
new fact is not a transport wrapper and does not replace or erase any upstream
fact.  `Spine.route8ResidualProfileRow` is the next node `[110]`: it reads
`route8Residual` by `FactInputs.get` and appends only
`route8ResidualProfile`, the receiver-exposed silent-core residual profile.
No indexed route-8 collection, carrier census, basin family transport, or
secondary route-8 object is introduced.  The graph-owned
`Graph.Route8.TraceBasin` definitions now formalize the canonical trace-basin
selection from the ambient graph, selected support, receiver, and routed load;
they are not a ledger carrier and are consumed only through ordinary spine
facts.  `Spine.runRoute8FromExitSevenFree` starts at the exact
`typeAExitSevenFreeKeys` ledger, requires the upstream facts the row consumes as
`FactKeys.Has` instances, appends this residual fact, and passes the same ledger
ancestry to `Spine.runRoute8Tail`.

### Row 63 — `[111]`–`[113]` selected residual burden and deficit bound

Node `[111]` is now the ledger fact `route8GlobalSqueeze`.  Its row reads the
exact `[110]` `route8ResidualProfile` and the existing `largeBudgetResidual`
fact with `FactInputs.get`, then appends only `route8GlobalSqueeze`.  Nodes
`[112]` and `[113]` are committed together by
`route8BurdenAndDeficitRow`: the manifest reads `route8GlobalSqueeze` and the
already committed selected silent-excess burden fact `typeAVisibleFirstExcess`,
then appends both `route8BasinBurden` and `route8LargeBudgetDeficit` in one
nonempty `factOnly` commit.  No route-8 collection object, carrier package, or
secondary transport channel is introduced; the full residual prefix remains in
the `ExactLedger`.  `Spine.runRoute8Tail` executes these commits after `[110]`
on the same exact ledger prefix.

### Row 64 — `[114]`–`[116]` carrier core

Node `[114]` is now the ledger fact `route8CarrierCore`.  Its row reads exactly
the selected `[113]` fact `route8LargeBudgetDeficit` with `FactInputs.get` and
appends the concrete graph-entry carrier-core fact for
`Graph.Route8.PresentedEntry object`.  The row no longer introduces arbitrary
`Target`, `Carrier`, `Coordinate`, `boundary`, `carrierSupply`, `car`, or
`state` binders.  It fixes the target to
`Graph.HasCycleWithLength data.LengthOK`, fixes carriers to
`Sym2 object.Vertex` through `PresentedEntry.toEntry`, and obtains all prior
mathematical input from the ledger.  Core's finite
`EssentialCarrier.Profile` then supplies the minimal complete carrier core,
proves it is contained in the entry's own carrier supply, and proves every
selected carrier has a deletion target defect plus a forgotten coordinate that
uses it.  No `Route8.Entry` wrapper, carrier census object, secondary
collection, or custom transport channel is committed to the ledger.

Nodes `[115]`--`[116]` are now the ledger fact
`route8SmallCoreCollapse`.  Its row reads `route8CarrierCore` with
`FactInputs.get` and appends the raw carrier-core form of
`lem:typeA-one-terminal-collapse` for the same concrete presented-entry
schema.  A zero/one essential-carrier core makes the internal-crossing
forgetting quotient equal to the core restriction, so the selected alternatives
fire when the residual supplies that local minimality input.  This is the
paper's small-core exit `(4)`--`(7)` mechanism.  The row does not introduce
arbitrary carrier or coordinate data, a route-8 collection wrapper, or a
secondary transport channel; it appends only the next `Spine.Key` fact.  The
same route-8 tail runner then continues to the paper-prescribed
two-carrier/private-carrier split.

### Row 65 — `[117]`–`[122]` indexed private-carrier census

Node `[117]` is now the ledger fact `route8TwoCarrierReduction`.  Its row reads
`route8SmallCoreCollapse` with `FactInputs.get` and appends the raw indexed-core
form of `prop:typeA-route8-carrier-reduction` over the residual's concrete
carrier type `Sym2 object.Vertex`: if the entries, essential cores, carrier
supply, burden/deficit inequality, and registered rate inequality are supplied
by prior ledger facts, then some indexed entry is two-carrier.  The row no
longer quantifies over an arbitrary carrier type.  The graph theorem counts
private carriers directly as finite subsets of each indexed core, proves the
private sets disjoint, and applies the integer census squeeze.  It does not use
a carrier census object or a route-8 collection wrapper.

Node `[118]` is now the ledger fact `route8CarrierDeletionWitnesses`.  Its row
reads `route8TwoCarrierReduction` with `FactInputs.get` and appends the raw
carrier-core form of `lem:typeA-essential-deletion-witness` and
`lem:typeA-deletion-witness-declared` for a concrete
`Graph.Route8.PresentedEntry object`.  Whenever the current residual supplies a
selected two-carrier indexed core and identifies that core with the canonical
essential carrier core of that presented entry, every essential carrier has the
deletion target-defect and a declared forgotten coordinate whose carrier
support contains it.  This is a fact appended to the same incoming ledger; no
terminal-entry object, route-8 collection wrapper, arbitrary coordinate family,
or side carrier is committed.

Nodes `[119]`--`[122]` are now committed together by
`route8PrivateCarrierContradictionRow`.  The manifest reads
`route8CarrierDeletionWitnesses` with `FactInputs.get` and appends exactly two
facts: `route8PrivateCarrierBudget` for the no-two-carrier branch's
`(threshold + 1)·N_basin ≤ supply` private-carrier budget, and
`route8NoTwoCarrierContradiction` for the contradiction with the selected
burden/deficit and registered rate inequalities.  Both facts are stated over
the concrete carrier type `Sym2 object.Vertex`; the row no longer introduces an
arbitrary `Carrier`.  The graph proof counts private carriers as finite subsets
of the selected indexed essential-core family and spends the same integer
census as node `[117]`; it does not create a route-8 collection object,
carrier census payload, or secondary transport channel.  The route-8 tail
runner keeps the full incoming ledger ancestry and continues directly into the
pressure-descent row `[123]`.

### Row 66 — `[123]` pressure descent

Node `[123]` is now the ledger fact `route8PressureDescent`.  Its row reads
the existing finite exit-`(4)` descent theorem `typeAExitFourFiniteDescent` and
the route-`8` no-two-carrier contradiction fact
`route8NoTwoCarrierContradiction` with `FactInputs.get`, then appends their
semantic join as a single ordinary ledger fact.  This matches the paper's join
node: the target-defect side is handled by the finite `Λ₄` descent already
committed in the Type A branch, while the route-`8` no-two-carrier side is
closed by the private-carrier budget contradiction.  A surviving branch after
`[123]` is therefore precisely the terminal two-carrier route-`8` obstruction
to be discharged at `[124]`.

The row does not create a route-`8` collection, terminal-entry payload, wrapper
runner, or custom transport.  It only reads previously committed facts from the
same `ExactLedger` prefix and appends `route8PressureDescent`, preserving the
full residual ancestry.  The next commit in `Spine.runRoute8Tail` is the
terminal no-go fact `[124]`.

### Row 67 — `[124]` terminal two-carrier no-go

Node `[124]` is now the ledger fact `route8TerminalNoGo`.  Its row reads the
same-branch `route8PressureDescent` fact from `[123]` and the
`route8CarrierDeletionWitnesses` fact from `[118]` with `FactInputs.get`, then
appends the terminal Q5 no-go fact for the concrete presented-entry schema.
The graph theorem `Graph.Route8.terminalTwoCarrierNoGoFacts` is instantiated
only at `presented.toEntry (Graph.HasCycleWithLength data.LengthOK)`: a
selected two-carrier deletion witness, a generated carrier-deletion Q5 clause,
and the no-exit-`(4)` fact of the same residual produce `False` via the existing
`ExitFour.Witness.carrierDeletion_contradicts_noExitFour` theorem.

The row does not construct a `Route8.Data`, carrier collection, route-8 entry
payload, custom cursor, wrapper runner, or side channel.  It appends exactly one
new fact to the existing `ExactLedger` prefix, preserving the full residual
ancestry from `[109]` through `[123]`.  Ledger/Reads are repaired through
`[124]`; `Spine.runRoute8FromExitSevenFree` now provides the executable ledger
path from the selected no-arm cursor to `route8TerminalNoGoKeys`.  Terminal
dispatch remains the framework closure consumer of the committed no-go fact
rather than a separate transport object.
