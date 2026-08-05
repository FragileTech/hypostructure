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
splits into `Result.typeASaturatedReceiver` (row 12's entry) and
`Result.typeAUnsaturatedReceivers` (node `[90]`).  `#print axioms` on
`FiniteObject.degree_induce_eq_internalDegree`,
`FiniteObject.exists_traceTo_of_no_baseline_subsupport`,
`FiniteObject.traceTo_of_traceReceiver?_eq_some`,
`FiniteObject.isSome_traceReceiver?_of_traceTo`,
`FiniteObject.not_saturated_iff`, `FiniteObject.saturationThreshold_eq`,
`Spine.typeAReceiverRoutingRow`, `Spine.typeASaturationDichotomy` and
`Spine.run` reports `propext`, `Classical.choice` and `Quot.sound` only.

That port also changed four facts of row 42 and one of row 41: the packing
`netDeficiencyCap`, `netChargeNonNegative`, `netChargeNegative`,
`windowJoinPressure`, `negativeSupport` and `typeALowSurplus` speak about now
carries its own maximality, so node `[27]` stays instantiable at the Type A
support.  Row 42's evidence records why the previous shape was unsound for row
11.  `Graph/ReceiverLoad.lean`'s dead receiver/load geometry — `Support`,
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
topology.  A ticked column is a claim about the current tree, so rows 12–19,
26–28 and 30–36 are now `❌ ❌ ❌ ❌`; row 15, which had been ticked in all four,
is included and carries its own correction note.  Rows 16 and 17 keep their
`Where` entries but they are named exactly: `Spine.typeAExitFourDichotomy` and
`Spine.typeAExitFiveDichotomy` are live, and they are the route-8 `(R2)`
*absence* generators of `def:typeA-true-route8-residual`, not the `[101]`/`[102]`
peel ledger or the `[103]`/`[104]` compression contradiction those rows are
about.  Row 37's `Where` was the only stale entry on a genuinely ported row and
now names `Spine.remainderNormalization`.

The rule this pass applied, and the one to keep applying: **a `✅` requires a
declaration that elaborates in the live tree and a target that builds.**  A
faithful description of deleted code is porting reference, not a passing
column.

**Correction — the earlier `SpineRun` failure was Block A's, not rows 41–42's.**
An earlier revision of this section recorded four `SpineRun` errors (a
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
makes `SpineRun` build with no other change; this was verified by reverting the
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
> | `Graph/Strategy/SpineRun.lean` | the composition, its three-exit `Result`, and the audit theorems |
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
| 9 | Near-cubic finite enumeration [21] | `Spine.windowPackageDichotomy`, `Spine.barrierEnumerationDichotomy` | ✅ | ✅ | ✅ | ✅ |
| 10 | Finite window-density budget [22]–[24] | `Spine.densityBudget` | ✅ | ✅ | ✅ | ✅ |

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
   block's slice.  What does not build is `SpineRun`, on rows 41–42's
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
> the unsaturated arm that enters node `[90]` — are `Spine.Result`
> constructors; the `Spine.Result.typeALowSurplus` exit they replace is gone.
>
> Every theorem row 11 rests on has been checked with `#print axioms` and
> depends on `propext`, `Classical.choice` and `Quot.sound` alone — no
> `sorryAx`, and no `Lean.ofReduceBool`, so no `native_decide` result is
> load-bearing in it.
>
> Every other `Where` entry below still names a declaration that does not
> elaborate, and no ticked column in those rows is backed by a compiling
> target.


| # | Node | Where | Ledger | Transport | Residual | Facts |
|---|---|---|---|---|---|---|
| 11 | Saturated receiver [89] | `Spine.typeAReceiverRouting`, `Spine.typeASaturationDichotomy` (`SpineRows`, run in `SpineRun.run`) | ✅ | ✅ | ✅ | ✅ |
| 12 | Visible receiver-entry returns [93] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |
| 13 | Exit 1: Mersenne return [95] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |
| 14 | Exit 2: power-of-two theta [97] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |
| 15 | Exit 3: P13 label collision [99] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |
| 16 | Exit 4: target-defective quotient [101] | `Spine.typeAExitFourPeelDichotomy`, `Spine.typeAPeeledCharge`, `Spine.typeAExitFourDichotomy` over `Graph/ExitFourPeeling.lean` (`Route8Rows`/`Route8Run`, run in `Spine.runRouteEight`) — the peel ledger is built; the alternative is the exit-(4) *conclusion*, not the quotient | ✅ | ✅ | ✅ | ❌ |
| 17 | Exit 5: target-complete compression [103] | `Spine.typeAExitFiveDichotomy`, `Spine.typeAExitFiveRealizationDichotomy`, `Spine.typeAExitFiveCompressionClosed` (`Route8Rows`/`Route8Run`, run in `Spine.runRouteEight`, checked in `Fixtures/Route8ExitFive.lean`) | ✅ | ✅ | ✅ | ✅ |
| 18 | Exit 6: response delocalization [105] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |
| 19 | Exit 7: decorated handoff fan [107] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |

> **Rows 16 and 17, ported with the route-8 ladder segment.**  Nodes `[101]`
> and `[103]` run as live `Decision`s in `Spine.runRouteEight`, ahead of the
> `[109]` placement.
>
> Row 16's yes arm is now the manuscript's peel-and-return, not a terminal:
> `Graph/ExitFourPeeling.lean` owns `def:typeA-exit4-peeling`'s `ℒ(w)`, `P₄(w)`
> and `L₄(w)`, proves `lem:typeA-exit4-peeling-charge` (the remaining charge
> `q(w) − ¼ − ¼L₄(w)` is nonnegative exactly when the peeled residual is
> unsaturated), `lem:typeA-exit4-discharge` (one adjoined load drops `L₄(w)` by
> exactly one) and the finite descent `lem:typeA-exit4-residual-routing` opens,
> and `Spine.typeAPeeledCharge` commits its output — the receiver retested at
> node `[89]`.  What the arm still *reads* rather than proves is the exit-(4)
> occurrence itself: `𝒬₄(w)`'s clauses (Q1)–(Q4) need the receiver's declared
> coordinates of node `[93]`, so the decision splits on
> `lem:typeA-unpeeled-visible-routing`/`lem:typeA-unpeeled-silent-routing`'s
> exit-(4) conclusion instead of on the quotient.  That is row 16's remaining
> `❌` in Facts.
>
> Row 17 is the manuscript's own dichotomy in `lem:typeA-exits-discharged`:
> *"if the compression is realized by a smaller proper atom, it contradicts
> hereditary target-uncompressibility; if it occurs only at the trace-basin
> response level, it is exactly failure alternative (b) and therefore is not an
> admissible route-8 residual."*  `Spine.typeAExitFiveRealizationDichotomy`
> splits on realization; the realized arm carries `lem:replacement`'s
> `CompressibleSupport` and **closes** against node `[14]`'s `uncompressible`
> through `closeIncompatible`; the response-level arm records alternative (b)
> and, lacking `typeAExitFiveFree`, cannot enter the route-8 arm.
> `Fixtures/Route8ExitFive.lean` checks both halves of that sentence on the
> Type A residual of node `[63]` that `Spine.run` already reaches: the realized
> arm's index carries the compression fact *and* Core's closure entry with every
> incoming fact retained, `RoutedTask.dispatchFor` returns `closed` on it for
> every task list, and its audit is complete, duplicate-free and has no empty
> commit; the response-level arm carries neither the closure entry nor
> `typeAExitFiveFree`.  Every theorem row 17 rests on has been checked with
> `#print axioms` and depends on `propext`, `Classical.choice` and `Quot.sound`
> alone.
>
> Row 17's four columns are about node `[103]` itself, which is entered from
> node `[101]`'s no arm inside `Spine.runRouteEight`.  That block is not yet
> attached to `Spine.run`, because the path `[93]`--`[99]` from node `[89]` is
> rows 12--15, which are unbuilt; that is those rows' gap, recorded there.

## C. Type B fan

> **Being ported.**  The rows in this section were implemented against the
> legacy `Blueprint` topology and its `Core.ProblemDefinition` registry.  Both
> are gone: the registry was deleted with `Official/Definition.lean` and the
> topology is now a commented reference in `StrategyDag.lean`.  Every Type B
> module of `Hypostructure.Graph` is quarantined, so each row is being rebuilt
> against the live framework rather than re-imported.
>
> Rows 20--25 and 29 are ported.  They run on the Type B residual of node
> `[64]` that `Spine.run` already reaches, and their `Where` columns name the
> live spine declarations.
>
> Every theorem the ported rows rest on has been checked with `#print axioms`
> and depends on `propext`, `Classical.choice` and `Quot.sound` alone -- no
> `sorryAx`, and no `Lean.ofReduceBool`, so no `native_decide` result is
> load-bearing anywhere in Section C.
>
> Rows 23, 24 and 25 are wired at *both* of their manuscript positions.  With
> row 29 ported, the degree-four arm of `[68]` runs `[79]`'s profile and then the
> same three row values at `[80]` and `[81]` that the heavy arm runs at `[71]`
> and `[72]`; a `Decision` carries no predecessor, so nothing is re-registered
> and no row exists twice.
>
> Every other `Where` entry below still names a declaration that does not
> elaborate, and no ticked column in those rows is backed by a compiling
> target.


| # | Node | Where | Ledger | Transport | Residual | Facts |
|---|---|---|---|---|---|---|
| 20 | Heavy-centre split [68] | `Spine.highCentreNormalForm`, `Spine.heavyCentreDichotomy` | ✅ | ✅ | ✅ | ✅ |

| 21 | Heavy-centre local dichotomy [69] | `Spine.heavyCentreLocalDichotomy` | ✅ | ✅ | ✅ | ✅ |
| 22 | Certificate-marked fan cap [70] | `Spine.fanCertificateCap` | ✅ | ✅ | ✅ | ✅ |
| 23 | Certificate labelling [71]/[80] | `Spine.fanCertificateDichotomy` | ✅ | ✅ | ✅ | ✅ |
| 24 | Direct-cycle removal [72] | `Spine.directCycleDichotomy` | ✅ | ✅ | ✅ | ✅ |
| 25 | B2 ledger [72]/[81] | `Spine.b2AssignmentDichotomy` | ✅ | ✅ | ✅ | ✅ |
| 26 | Hybrid B1 entry [74]/[82] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |
| 27 | Bridge fan-mass [73],[75] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |
| 28 | Bridge deficit [76]/[85] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |
| 29 | Degree-four fan profile [78],[79] | `Spine.degreeFourProfile` | ✅ | ✅ | ✅ | ✅ |
## D. Non-near-cubic surplus branch

> **Unbuilt; groundwork started.**  The rows in this section were implemented
> against the legacy `Blueprint` topology and its `Core.ProblemDefinition`
> registry.  Both are gone, so every `Where` entry below names a declaration
> that does not currently elaborate and **no ticked column in this section is
> backed by a compiling target** — read the whole block as `❌ ❌ ❌ ❌`.  The
> legacy `Graph/Strategy/SurplusAccounting.lean` is quarantined and is reference
> only; nothing may import it.
>
> What does exist live is `Hypostructure/Graph/SurplusPort.lean`:
> `def:surplus-ports` as `FiniteObject.SurplusPort`, its shoulder set
> `N_G(x(p)) ∖ {c(p)}`, `endpoint_degree_eq` (the endpoint of a port sits
> exactly at the baseline, which is node `[10]`'s independence consumed rather
> than re-proved) and `card_shoulders` (a port has `δ − 1` shoulders; at the
> manuscript's `δ = 3` that is the shoulder pair `{a_p, b_p}`).  The module is
> generic in the threshold and writes no numeral.  It is not yet consumed by any
> row, so it changes no status cell.
>
> The entry residual for this block is `Spine.Result.surplusAbove`, which is
> live and carries nine facts.  But node `[125]` is the *survivor* of the five
> sparse surplus exits of `def:named-surplus-exits`, so rows 30--36 cannot be
> written until those exits are branch alternatives that close.  Four of the
> five already have their machinery: (a) is `returnAvoidance` on the branch,
> (b) is `Graph.CurvatureQuotient.targetComplete_of_identified` and
> `Graph.Response.contextEquivalent_or_targetDefect` from row 69, (c) is
> `uncompressible` on the branch with
> `InterfaceReplacement.not_replacementSupport` from row 70, and (d) is
> `Graph.CurvatureQuotient.localize` with `Spine.not_globalBarrierReading` from
> rows 71--73.  Only (e), `lem:suppressed-family-critical-cycle`, has no live
> support, and it is the remaining prerequisite together with `[128]`'s
> activation bundle.


| # | Node | Where | Ledger | Transport | Residual | Facts |
|---|---|---|---|---|---|---|
| 30 | Ordered surplus activation [125]–[128] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |
| 31 | Baseline demand accounting [129] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |
| 32 | Canonical pair-response [130]–[134] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |
| 33 | Capacity-token accounting [134]–[136] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |
| 34 | Coupled homogeneous fibre pressure [137]–[143] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |
| 35 | Finite bottleneck classification [140]–[143] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |
| 36 | Homogeneous bottleneck [144] | *unbuilt* — no live declaration | ❌ | ❌ | ❌ | ❌ |

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
| 41 | Full-rank finite-state capacity [47]–[56] | `Spine.windowPackageDichotomy`, `Spine.forcedCurvatureCost`, `Spine.remainderEntropyDichotomy`, `Spine.entropyPackage`, `Spine.entropyCapDichotomy`, `Spine.orderThresholdDichotomy`, `Spine.netDeficiencyCap` (`SpineRows`) | ✅ | ✅ | ✅ | ✅ |
| 42 | Net-charge continuation [57]–[64] | `Spine.netChargeLocalization`, `Spine.netChargeDichotomy`, `Spine.windowJoinPressure`, `Spine.negativeSupport`, `Spine.typeSplitDichotomy` (`SpineRows`) | ✅ | ✅ | ✅ | ✅ |

## F. Cold-window corridor

> **Unbuilt.**  The rows in this section were implemented against the legacy
> `Blueprint` topology and its `Core.ProblemDefinition` registry.  Both are
> gone: the registry was deleted with `Official/Definition.lean` and the
> topology is now a commented reference in `StrategyDag.lean`.  Every `Where`
> entry below therefore names a declaration that does not currently elaborate,
> and no ticked column in this section is backed by a compiling target or an
> exported run.  The section is the porting reference for the rewrite, not a
> description of current code.
>
> **Rows 43--50 are the exception.**  They have been ported to the canonical
> ledger and are out of the legacy stack entirely: their mathematics is
> `Hypostructure/Graph/ColdCorridor.lean` and
> `Hypostructure/Graph/ColdFirstFailure.lean`, their rows are
> `Graph/Strategy/ColdCorridorRows.lean`, and all seven facts are committed by
> `Graph/Strategy/ColdCorridorRun.lean` against the one
> `Core.Residual.ExactLedger`.  Five fixtures check them:
> `ColdCorridorSignature` (the thirty-two generating kinds and their per-clause
> counts), `ColdCorridorLedger` (the `73` and `78` thresholds and the `15`/`13`
> stub counts), `ColdCorridorShortSelfReturn` (the two exceptional length sets),
> `ColdCorridorConstruction` (the corridor apparatus is inhabited) and
> `ColdCorridorRun` (the block runs end to end and its audit is `rfl`).  Every
> module is in the build closure of `Hypostructure.lean`.  Rows 51 onwards are
> still the legacy reference.
>
> **Registered-fact review.**  Rows 43--50 were re-read against the manuscript
> for two specific defects, and both were found and fixed.
>
> *An unregistered fact.*  `SurvivingColdBranch`'s clause (ii) was written as
> `ContextEquivalent ∨ TargetDefect`, which excluded middle proves outright: the
> field posed as `def:surviving-cold-branch` (ii) and constrained nothing.  It
> now carries the branch's own `Identified` relation and says every
> identification the branch makes is context-universal, which is the
> manuscript's clause; `not_identified_of_firstFailureDefect` spends it, and
> Row 46 commits that.
>
> *Four facts proved but never registered.*  `def:cold-same-interface-table`'s
> finiteness (`tableBound`), `def:cold-bounded-germ`'s `δ = 0`
> (`increment_eq_zero`), `def:cold-skeleton-excess`'s `|𝓔_br(P)| = b(P)`
> (`selectedBranchExcess_length`), and the converse half of the (F2) sentence
> (`firstFailureResponse_of_not_contextEquivalent`) were theorems that no fact
> mentioned.  All four are now clauses of the committed facts at Rows 43, 44 and
> 50.
>
> *Reimplementation removed.*  Four declarations were pure forwarders or
> definitional restatements and are gone: `interfaceWidth_pos`,
> `mem_declaredSignature_clause`, `branchExcessOf_ambientCubic` (a `rfl` whose
> docstring claimed a count), and `handoffExit_unique` (the same content as the
> committed `exists_unique_handoff`).  Three corridor-level forwarders of
> presentation theorems were also removed, and the two dead `tauBelow_*`
> coefficient lemmas were replaced by `tauBelow_quarter` and
> `tauBelow_routeEight`, which state the manuscript's comparisons and are
> evaluated at `s = 15` by `Fixtures.ColdCorridorLedger`.
>
> *What remains unspent, deliberately.*  `extractionDenominator` (`D_cold`) is
> defined and proved but has no consumer until Row 51; `firstFailureHandoffExit`
> returns an envelope, which is data, so Row 49's transfer is an elimination of
> Row 48's committed fact rather than a fact of its own; and no `Corridor` value
> is constructed from the EG packing yet, so the committed facts are true and
> non-vacuous as statements but the corridor they quantify over is supplied at
> Row 50's own producer, which is not part of these rows.
>
> *Two inputs that are hypotheses by design, and are cited where the manuscript
> cites them.*  `Corridor.twoStubs` is `lem:bridgeless` — "no such component has
> only one boundary stub, since that unique boundary edge would be a bridge of
> `G`" — a theorem about the selected object with its own place in the
> manuscript, so `def:cold-corridor-first-failure` receives it rather than
> proving it.  `TableRow.admissible` is `def:admissible-rank-quotient`, spent
> exactly where `lem:cold-same-interface-table` spends it on a neutral row.
> Both are fields of the construction, so a caller can only build a corridor or
> a table row where they hold.
>
> *The block is shared.*  `Graph/Strategy/ColdCorridorRun.lean` now also carries
> rows 52--54's germ rows, and `runCold` composes ten rows rather than seven.
> The seven of rows 43--50 are unchanged; `Fixtures.ColdCorridorRun` checks
> their presence on the ledger by membership rather than by position, so it does
> not break as later rows land.
>
> **Rows 57--61 are ported too.**  Their mathematics is
> `Hypostructure/Graph/ColdBranchClosure.lean`: `lem:hot-failure-cold-mass` as
> one subtraction-free inequality across `𝒫 = 𝒫_hot ⊔ 𝒫_cold` with every
> `log₂ n` cancelled; `lem:cold-germ-extraction`'s greedy independence, proved
> for an arbitrary finite family and symmetric overlap relation, with the
> manuscript's division by `Δ+1` cleared into
> `|𝒢_cand| ≤ N_germ·(Δ+1)`; the positivity that makes the (F5) arm
> unreachable; and `thm:cold-branch-quantitative-closure`, total and with no
> `Option`.  That module uses no framework plumbing at all — only Mathlib
> `Finset`/`Nat` and the cold-corridor mathematics — and the three rows that
> commit it use only `factOnly`, `rowManifest`, `FactKey`, `FactInputs.get` and
> `AtomicCT.run`, all catalogued.
>
> Row 60 is satisfied structurally rather than by a new declaration: in the
> canonical port there is no registration field that routes.  `Spine.runCold`
> composes the rows, each row's `Requires` is discharged by instance resolution
> against the incoming index, and the branch analysis is the composition — which
> is exactly what that row's **What it should do** asked for.
>
> **Registered-fact review, rows 57--61.**  The same two-defect pass was run on
> them, and one defect was found.
>
> *An unregistered fact, with a dead forwarder attached.*  The committed
> extraction clause stated the *generic* greedy bound at an arbitrary degree,
> while `lem:cold-germ-extraction`'s own statement — at maximum degree
> `M_cold·B_cold`, covering `D_cold`-fold — was proved as
> `ColdCorridor.coldGermExtraction` and committed nowhere; that theorem was
> consequently a forwarder nothing called.  The clause now *is* the manuscript's
> statement, phrased with `exchangeBound`, `overlapBound` and
> `extractionDenominator`, so the paper's `D_cold` is what the ledger carries and
> both declarations are load-bearing.  This also spends
> `extractionDenominator`, which the rows 43--50 review had recorded as defined
> but unconsumed.
>
> *No reimplementation.*  The greedy bound is not a re-proof of live framework
> code: the only prior one is
> `Core.Finite.ColdCorridor.supportPacking_card_bound`, in a quarantined module,
> so this is its port rather than a second copy.  Every other declaration in
> `ColdBranchClosure.lean` is referenced.
>
> *A second defect: G2 was assumed rather than routed.*  The committed closure
> first carried a hypothesis `branch.Identified germ.piece germ.canonical` that
> nothing could produce, so the fact never fired.  The first repair replaced
> `def:surviving-cold-branch` (ii) with a germ-level field `noGermDefect : ∀
> germ, ¬ germ.Distinguishing` — which fired, but **assumed the conclusion of
> the manuscript's own chain** instead of deriving it.  `lem:cold-bounded-germ-
> trichotomy` G2 reads "the induced quotient is target-defective, so it is
> routed to the sparse exit or exit-(4) ledger", and clause (ii) forbids those;
> collapsing that into an assumption is exactly the kind of shortcut this review
> exists to catch.
>
> The chain is now complete and every step is the manuscript's.  Clause (ii)
> stays abstract — no identification the branch makes is target-defective — and
> `SurvivingColdBranch.germIdentified` supplies the missing link:
> `def:cold-bounded-germ` defines a germ as "two same-interface `x`--`y`
> representatives", and the local replacement of
> `lem:cold-same-interface-table` is the quotient identifying them, so a germ
> *is* an identification.  `SurvivingColdBranch.noGermDefect` is now a
> **theorem**: a distinguishing germ separates its identified pair against a
> compatible outside context, and clause (ii) says no identification the branch
> makes is so separated.
>
> The same abstract clause is what Row 46 spends, so one reading of
> `def:surviving-cold-branch` (ii) now serves both rows.
>
> *The orientation, made structural.*  `lem:cold-bounded-germ-trichotomy` says
> "no length-changing cold bounded germ survives", and
> `lem:cold-increment-arithmetic` orients the germ so that `δ ≥ 0`.  The closure
> first proved only the `δ < 0` reading, because `BoundedGerm` records one
> occurrence — its `support` — and the other representative abstractly, and G3's
> replacement only shrinks the object where the *longer* representative occurs.
> `def:cold-bounded-germ` is explicit that both representatives are strands
> between the same two interfaces of `G`, so each occurs at a support;
> `ColdCorridor.OrientedGerm` records both, and `OrientedGerm.not_survives`
> closes the germ whichever one is longer.  The manuscript's orientation is now
> what it is in the manuscript — a choice of which representative to call `E` —
> rather than a hypothesis the formalization needed, and the committed clause
> asks only `δ ≠ 0`.
>
> The review of *that* fix caught one more thing.  `OrientedGerm` first carried
> `swapped : backward.increment = − forward.increment` as a field, which is both
> an assumed fact and weaker than it looked: it constrains the two increments
> only jointly.  The structure now carries the exchange — each reading's
> occurrence against the other's second representative — and
> `OrientedGerm.swapped` is a **theorem** derived from it.
>
> The review of *that* correction, in turn, found the accompanying docstring
> overclaiming: the exchange fields equate *sizes*, which is what the increment
> argument consumes, and not the boundary pieces, which sit at different
> interfaces and would need an interface correspondence to compare.  The
> docstring now says exactly that, and records why the closure does not need
> more — `backward` is a genuine germ of the object in its own right, so
> `not_survives` is sound whatever else relates the two readings.  The claim that
> the fields make the two readings "the same germ" was removed rather than left
> standing.
>
> *What the closure does and does not claim.*  `coldBranch_closed` is the
> routing half of `thm:cold-branch-quantitative-closure`: given a germ, every
> family is impossible.  It does not prove that a germ *exists*, and does not
> need to — a branch with no germ has no terminal residual either, so the
> absence of a germ closes the branch rather than leaving it open.  The
> quantitative chain (`hotFailure_coldMass`, `coldGermExtraction`,
> `coldGerm_nonempty`) is committed for what the manuscript uses it for — the
> germ family is *linearly* many — not as an existence obligation.
> The theorem's other two arms, "the route-8 carrier inequality closes
> `θ < 1/78`" and "the live-hot entropy comparison closes", belong to the
> route-8 rows 62--67 and the entropy rows and are not part of rows 57--61.
>
> *What is registered rather than derived, and why that is not a fabrication.*
> `c_hot` and `θ_win` have no registered value, and deliberately so: the
> committed mass bound is quantified over *every* rate, so it holds whatever
> `c_hot` is, and nothing in the ledger depends on a number nobody has pinned.
> The same applies to the `o(n)` slack terms and to the subcubic ball count
> `1 + 3(2^{M_cold+2} − 1)` behind `B_cold`, which enters as the extraction's
> degree hypothesis.  Registering a made-up `c_hot` would be the defect this
> review exists to catch, not the fix for it.


| # | Node / component | Where | Ledger | Transport | Residual | Facts |
|---|---|---|---|---|---|---|
| 43 | Corridor cut-state `T(J)` | `ColdCorridor.CutState`, `Presentation.state` (`Spine.coldCorridorState`) | ✅ | ✅ | ✅ | ✅ |
| 44 | Same-interface table | `ColdCorridor.TableRow`, `ColdCorridor.row_closed` (`Spine.coldSameInterfaceTable`) | ✅ | ✅ | ✅ | ✅ |
| 45 | (F1) producer | `ColdCorridor.Corridor.FirstFailureCycle` (`Spine.coldFailureCycle`) | ✅ | ✅ | ✅ | ✅ |
| 46 | (F2) producer | `ColdCorridor.Corridor.FirstFailureDefect` (`Spine.coldFailureDefect`) | ✅ | ✅ | ✅ | ✅ |
| 47 | (F3) producer | `ColdCorridor.Corridor.FirstFailureCompression` (`Spine.coldFailureCompression`) | ✅ | ✅ | ✅ | ✅ |
| 48 | (F4) producer | `ColdCorridor.Corridor.FirstFailureHandoff` (`Spine.coldFailureHandoff`) | ✅ | ✅ | ✅ | ✅ |
| 49 | (F4) handoff exit | `ColdCorridor.Corridor.handoffExit` (`Spine.coldFailureHandoff`) | ✅ | ✅ | ✅ | ✅ |
| 50 | Core classified state | `ColdCorridor.Corridor.exists_firstFailure` (`Spine.coldFailureRouting`) | ✅ | ✅ | ✅ | ✅ |
| 51 | Terminal-F5 residual | `ColdCorridor.BoundedGerm`, `Corridor.exchange_card_le` (`Spine.coldFailureRoutingRow` + the three germ rows) | ✅ | ✅ | ✅ | ✅ |
| 52 | [155] G1 realizing | `Spine.coldGermRealizedRow` | ✅ | ✅ | ✅ | ✅ |
| 53 | [156] G2 distinguishing | `Spine.coldGermDistinguishedRow` | ✅ | ✅ | ✅ | ✅ |
| 54 | [157] G3 neutral | `Spine.coldGermSilentRow` | ✅ | ✅ | ✅ | ✅ |
| 55 | Core dispatch (F1) | `Spine.runCold` — (F1) is committed at row 45, the dispatch is row composition | ✅ | ✅ | ✅ | ✅ |
| 56 | Core dispatch (F3) | `Spine.runCold` — (F3) is committed at row 47, the dispatch is row composition | ✅ | ✅ | ✅ | ✅ |
| 57 | (F4) dispatch arm | `ColdCorridor.Corridor.handoffExit_mem` (`Spine.coldHandoffTransfer`) | ✅ | ✅ | ✅ | ✅ |
| 58 | (F5) `.isFalse` arm | `ColdCorridor.exists_independent_card_le_mul`, `hotFailure_coldMass` (`Spine.coldGermExtraction`) | ✅ | ✅ | ✅ | ✅ |
| 59 | (F5) `.neutral` arm | `ColdCorridor.boundedGerm_not_survives` (`Spine.coldBranchClosed`) | ✅ | ✅ | ✅ | ✅ |
| 60 | Registrations `atStage` | `Spine.runCold` — the routing is row composition, not a registration field | ✅ | ✅ | ✅ | ✅ |
| 61 | `classifiedStateForcesTarget` | `ColdCorridor.coldBranch_no_terminal_survivor` (`Spine.coldBranchClosed`) | ✅ | ✅ | ✅ | ✅ |

## G. Route-8 carrier closure

> **Ported, on the canonical ledger.**  The legacy `TypeARoute8Closure`,
> `TypeARoute8Stages` and `TypeARoute8Carriers` are quarantined and were not
> re-imported: the block is rebuilt on the live framework as
> `Graph/Route8Carrier.lean`, `Graph/Route8Closure.lean`,
> `Graph/Route8Residual.lean`, the rows of `Graph/Strategy/Route8Rows.lean`,
> the run `Spine.runRouteEight` in `Graph/Strategy/Route8Run.lean`, and the
> fixture `Fixtures/Route8Run.lean`, which runs the whole block on the Type A
> residual of node `[63]` that `Spine.run` reaches.  Every `Where` entry below
> names a declaration that elaborates, and every ticked column is backed by a
> compiling target.
>
> **Every clause is a registered fact.**  `Graph.Route8.Data` is *data only* --
> the collection's supports `𝒳` with their per-support readings, the indexed
> family `Ξ(𝒳)` and the support each entry lives on, the ambient boundary
> supply, and the registered scales.  Each clause the manuscript attaches to a
> route-8 residual is a proposition on the canonical ledger under its own key:
> (R2) for exit `(4)` is node `[101]`'s no arm (`typeAExitFourFree`), (R2)/(R4)
> for exit `(5)` is node `[103]`'s no arm (`typeAExitFiveFree`), and the four
> readings `[111]`--`[113]` cites travel with the existential node `[109]`
> commits, because they depend on the collection and no fact may carry data.
> The only propositions inside the data are its own well-formedness: a declared
> coordinate is recorded by a simple cycle, an entry's support is one of the
> collection's, and an entry's cut lies inside the collection's supply.
>
> **The arm hangs off the exit ladder.**  `Spine.runRouteEight` runs node
> `[101]` and node `[103]` as `Decision`s before the `[109]` placement, so the
> route-8 arm is entered only on their no arms and the exit absences are *read*
> by nodes `[116]` and `[124]` rather than assumed.  Their yes arms leave the
> block: `[101]`'s to the manuscript's target-defect peel and `[103]`'s to the
> uncompressibility contradiction, both of which are rows 16 and 17's and
> unbuilt.  The block uses only these two absences -- exits `(1)`, `(2)`, `(3)`,
> `(6)` and `(7)` are not needed by any step of Figure 9 -- so the block's
> theorem is *weaker in hypotheses* than the manuscript's (R2) and implies it.
>
> **What the arm is entered with, and what it proves.**  Node `[109]`'s fact
> carries exactly the four readings the manuscript cites at this point, and
> nothing else:
>
> * `lem:typeA-silent-excess-count` (node `[94]`) — `Data.SilentExcessCount`;
> * `lem:typeA-reduced-silent-residual` (node `[94]`) — `Data.BasinAssignment`;
> * `def:typeA-large-budget-deficit`'s own clause, which is the *definition* of
>   carrying the deficit — `Data.LargeBudgetDeficit`;
> * the registered rate condition `τ_win < 3/13`, which `cor:stub-boundary-supply`
>   and the near-cubic spine estimate of node `[29]` supply — `Data.Rate`.
>
> Every step the manuscript *proves* between nodes `[111]` and `[124]` is proved
> here: `lem:typeA-route8-burden` itself (`burden_of_silentExcess`, the paper's
> own summation over `𝒳` with the indexed pairs counted fibrewise), the node-
> `[113]` substitution, `lem:typeA-carrier-cut-parity`,
> `lem:typeA-one-terminal-collapse`, `lem:typeA-essential-deletion-witness`,
> `lem:typeA-deletion-witness-declared`,
> `prop:typeA-route8-carrier-reduction`, `thm:typeA-two-carrier-nogo` and
> `prop:typeA-route8-closure-from-nogo`.  `D_A(𝒳)` is the manuscript's sum
> `∑_{X∈𝒳}(¼|V(X)| − def⁺(X))`, not a free number: `Data.deficiency` is that
> `Finset.sum`.


| # | Node / component | Where | Ledger | Transport | Residual | Facts |
|---|---|---|---|---|---|---|
| 62 | [109] route-8 arm placement | `Spine.route8Placement` behind `Spine.typeAExitFourDichotomy` and `Spine.typeAExitFiveDichotomy`, run by `Spine.runRouteEight` | ✅ | ✅ | ✅ | ✅ |
| 63 | [111]–[113] collection, burden, deficit bound | `Spine.route8Burden` (`Route8.Data.burden_of_silentExcess`, `Route8.deficit_le_basins`) | ✅ | ✅ | ✅ | ✅ |
| 64 | [114]–[116] carrier core | `Spine.route8CarrierCore` (`Route8.Data.two_le_alpha`) | ✅ | ✅ | ✅ | ✅ |
| 65 | [117]–[122] private-carrier census | `Spine.route8Census` (`Route8.Data.Reduced.twoCarrierEntry`) | ✅ | ✅ | ✅ | ✅ |
| 66 | [123] pressure descent | `Spine.route8Descent` | ✅ | ✅ | ✅ | ✅ |
| 67 | [124] terminal two-carrier no-go | `Spine.route8Closed` (`Route8.Data.no_twoCarrierEntry`), closed by `closeIncompatible` | ✅ | ✅ | ✅ | ✅ |

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
| 68 | Branch D entry [33], [35] | `Spine.branchDependenceRow`, run in `SpineRun.run` | ✅ | ✅ | ✅ | ✅ |
| 69 | Context-validity test [36]–[37] | `Spine.contextValidityDichotomy` + `closeImpossible`, run in `SpineRun.run` | ✅ | ✅ | ✅ | ✅ |
| 70 | Proper-atom compression [38]–[39] | `Spine.atomCompressionDichotomy` + `closeIncompatible`, run in `SpineRun.run` | ✅ | ✅ | ✅ | ✅ |
| 71 | Enlarged delocalization support [40]–[42] | `Spine.delocalizationScopeDichotomy` + `closeIncompatible`, run in `SpineRun.run` | ✅ | ✅ | ✅ | ✅ |
| 72 | Whole-graph delocalization [43]–[45] | `Spine.globalBarrierRow`, run in `SpineRun.run` | ✅ | ✅ | ✅ | ✅ |
| 73 | Rank-drop branch closed [46] | `Spine.Result.rankDropClosed` via `closeIncompatible`, run in `SpineRun.run` | ✅ | ✅ | ✅ | ✅ |

## Row evidence

> **Block A rows 1–10 are written against the live code.**  The pre-port
> registration architecture — `Core.Strategy.TargetAlgebraReduction`,
> `MinimalSubobjectExclusion`, `CriticalModificationStructure`,
> `ObstructionPackingData`, `ExactFiniteLocalAlgebra`, `ScaleThresholdDichotomy`,
> and the `CTAdapters.ct1` / `ct9` / `ct14` / `ct16` executions they ran through
> — is **deleted**.  The live Block A is nine declarations in
> `Graph/Strategy/SpineRows.lean`: seven `factOnly` `AtomicStrategy` rows and two
> `Decision`s, composed in `Graph/Strategy/SpineRun.lean`.  **No Block A row
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
  (`three_le_threshold`, `netChargeRate`, `largeOrder_dominates_surplus`) rather
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
  `SpineRun` instantiations is a pure projection or injection of a fact *value*
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
  `SpineRun.lean:113`.  It reads the selection fact with `FactInputs.get`,
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
  `Produces := [noProperBaseline]`, installed at `SpineRun.lean:119`.  It reads
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
  `SpineRun.lean:127`.  Node `[9]` is proved by contradiction: if some dart had
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
| `lem:independent-target-entropy` | lem | `Core.FiniteEntropy.two_pow_le_card_ambient_of_realizes`<br>`Graph.LabelledOn.two_pow_le_card_of_realized` | unconsumed — no call site |

`lem:target-complete-quotient-composition` and `def:target-rank` are in the same manuscript subsection as `[11]`–`[14]` but are consumed at the rank-drop branch (nodes `[31]`–`[45]`), outside rows 1–8; nothing in the tree states either as a type. `lem:independent-target-entropy` is placed here because it closes the same subsection; the two declarations state its inequality generically, but neither is applied anywhere in `hypostructure` or `examples`.

---

**CT composition at this row.** No CT, correcting the reference table, which lists this strategy as CT7. `Core/Strategy/InterfaceReplacement.lean` contains no `CTAdapters.ct*` call; the only occurrence of "CT7" in the file is inside a comment at `:161`, which is inadmissible evidence. The recipe is three `StageNode.create` runs (`:333`, `:355`, `:493`) chained into one closure: registration, then `UniversalReplacement`, then `Uncompressible`. Each stage is a derivation over the registered assembly rather than a bounded search, so a CT adapter would have nothing to schedule; what the three-stage chain buys is that `noStrictReplacement` at stage two is available as a literal predecessor fact to the compression elimination at stage three, instead of both being re-derived from the ambient context.

### Row 6 — Induced-obstruction packing `[15]`–`[17]`

- **Paper fact.** `thm:p13free` (Hegde–Sandeep–Shashank, cited): "Every `P_{13}`-free graph of minimum degree at least `3` contains a cycle whose length is a power of two." `cor:p13-exists`: "The minimal counterexample `G` contains an induced `P_{13}`", proved by contradiction against the counterexample condition. The prose that follows fixes `p_{13}` as "the maximum size of a vertex-disjoint family of induced copies of `P_{13}` in `G`" and `\theta=p_{13}/n`; the branch table records that "a vertex-disjoint induced-`P_{13}` family is chosen maximal" and that "every unchosen induced window meets the packing". Node `[15]` is the freeness test, `[16]` the HSS terminal, `[17]` the maximal packing.
- **What the Lean does.**  `Spine.obstructionPackingRow`, a `factOnly`
  `AtomicStrategy`: `Requires := [selection]`, `Produces := [maximalPacking]`,
  installed at `SpineRun.lean:150`.  `cor:p13-exists` is proved by
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
> composition in `SpineRun` already expresses, and asserted a prerequisite the
> row does not have.  The row now uses a new `sourceFreeManifest` with
> `Requires := []` (legal — `List.Nodup []` holds, and `producesNonempty`
> constrains only `Produces`), and the `SpineRun` instantiation drops the key and
> its freshness argument.  Ledger, Transport, Residual and Facts are unaffected:
> the row commits the same fact, from the same theorems, through the same runner.


- **Paper fact.** Node `[18]` is "`P_{13}` label algebra: `399` labels; relations `C_s`; curvature `\Omega_2`". The manuscript defines the attachment label `S(x)=\{i:xv_i\in E(G)\}\subseteq\{0,\ldots,12\}`, shows a label is legal iff `|i-j|\notin\{2,6\}` for all `i,j\in S` (because `(j-i)+2\in\{4,8\}` are the only dyadic closing lengths available), and sets `\labels=\{S\subseteq\{0,\ldots,12\}: S\ne\varnothing\text{ and }|i-j|\notin\{2,6\}\ \forall i,j\in S\}`. `lem:labels`: "`|\labels|=399`. The distribution by size is `13,60,122,122,63,17,2` for sizes `1,\ldots,7`", proved by direct enumeration. `lem:curv-enum` introduces `\Omega_2(S,A,T)` as the two-step curvature test `C_1(S,A)C_1(A,T)(1-C_2(S,T))` and counts `543958`, `432672`, `111286`, giving `c_\Omega=\log_2(543958/111286)`; the counts and `c_\Omega` belong to node `[21]`, only `\Omega_2` itself is named at `[18]`.
- **What the Lean does.**  `Spine.localAlgebraRow`, a `factOnly`
  `AtomicStrategy`: `Requires := []`, `Produces := [localAlgebra]`, installed at
  `SpineRun.lean:156`.  The committed fact is the conjunction of
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
  `factOnly` row — taken at `SpineRun.lean` in the `run` body.  It branches on
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
  registered, deliberately: node `[56]` needs to know the threshold is a
  square-root scale in order to spend `σ(G) = O(√n) = o(n)`, and
  `Data.surplusThreshold_sublinear` derives that from
  `largeOrder_dominates_surplus`, itself a registered obligation in the
  presentation's own arithmetic.  No decimal and no `C_sp` value occurs.
- **Ledger and residual.**  No read: both sides of the comparison are
  observables of the active object.  One arm committed, residual unchanged, the
  other arm's key absent from this branch.
- **Transport and terminals.**  No CT, no carrier, no routing helper.  The
  strict arm leaves Block A as `Result.surplusAbove` at `surplusAboveKeys` and
  is where node `[20]`'s surplus-pair accounting chain begins; the at-or-below
  arm continues into node `[21]`.  Neither is a paper terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:surplus-ports` | def | `Graph.FiniteObject.degreeSurplus` | `2m − δn`, equal to the paper's `σ(G)` on the standing baseline |
| node `[19]` split | dia | `Graph.Strategy.Spine.surplusDichotomy`<br>`Graph.Strategy.Spine.Holds .surplusAbove`<br>`Graph.Strategy.Spine.Holds .surplusAtOrBelow` | exhaustive `Decision`; both arms carry a proved inequality |
| `def:near-cubic-spine` | def | `Graph.Strategy.Spine.Data.surplusThreshold`<br>`Graph.Strategy.Spine.Data.surplusThreshold_sublinear` | carried on the at-or-below arm; the sublinearity is derived from `largeOrder_dominates_surplus` |
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
- **What the Lean does.**  The node is
  `Graph.Strategy.Spine.barrierEnumerationDichotomy`
  (`Graph/Strategy/SpineRows.lean`), a two-arm `Decision` over the canonical
  ledger — not a CT.  The retired `Core.Strategy.FiniteBarrierEnumeration`
  module and its `Profile`/`Summary`/`RateLedger` are **deleted**; the finite
  enumeration itself is now the audited table `FiniteChecks.P13Barrier`,
  projected into the registered `Spine.Data` as `data.windowRate` and
  `data.windowOrder` and reaching the node only through those fields.
  The row branches on the decidable comparison

  ```
  if overflow : Graph.skeletonBudget current.object <
      2 ^ (data.windowRate * Graph.dyadicScaleCount current.object *
        current.object.windowPackingNumber data.windowOrder)
  ```

  committing `barrierOverflow` on the strict side and `barrierCap` on the
  other, with the cap arm's second conjunct proved inline.  Every symbol is an
  observable of the literal active residual object — `skeletonBudget`,
  `dyadicScaleCount`, `windowPackingNumber` — or a registered `Data` field;
  no numeral appears in the row, and `399`/`543958`/`432672`/`111286` occur
  nowhere in it.
- **What it should do.**  State `lem:p13-window-package`'s demand
  `c₁₃ · p₁₃ · log₂ n` bits against `lem:skeleton-dominates`' budget
  `C(C(n,2), m)`, decide the two exhaustive alternatives of node `[22]`, and
  carry `lem:variable-edge-budget` on the surviving cap arm so the retained
  bound does not depend on the exact `m`.
- **Gap.**  None.  The demand exponent is
  `windowRate · dyadicScaleCount object · windowPackingNumber`, which is the
  manuscript's `c₁₃ p₁₃ log₂ n`: `windowRate` is a per-window cost *per dyadic
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
  breaking `SpineRun`; see the correction in **Build status**.  **Correction to a previous
  revision:** `Graph/FiniteEdgeBudget.lean` is no longer an unimported island.
  It is imported by `Graph/Strategy/SpineVocabulary.lean:7` and by
  `Hypostructure.lean:67`, and `Graph.edgeStratumCount` /
  `Graph.variableEdgeBudget` are consumed by this row's cap arm and by the
  `.barrierCap` clause itself.  `lem:variable-edge-budget` and
  `rem:budget-robustness` are therefore **consumed**, not stated-and-unreachable
  as this document previously recorded.  What remains genuinely unconsumed is
  only the *summed* form `sum_edgeStratumCount_le_variableEdgeBudget`: the row
  proves the pointwise bound it needs directly, and no call site uses the sum.
- **Ledger and residual.**  `Decision.run` commits exactly one arm's key
  against the literal incoming stage, so the sibling key is absent from this
  branch's type-level index entirely — `barrierOverflowKeys` and the cap-side
  index are disjoint at `.barrierCap`/`.barrierOverflow`.  The row reads
  `current.object` and publishes through the framework runner; it appends no
  residual change (`Refines` is the identity here, a fact-only step) and drops
  nothing, so every earlier key remains indexed. The node requires no upstream
  fact: its demand and budget are both observables of the active object.
- **Transport and terminals.**  No EG-specific carrier, executor, or routing.
  The arms are `Decision`'s own two branches, taken at
  `Graph/Strategy/SpineRun.lean:579`. The overflow arm leaves Block A as
  `Result.barrierOverflow` at `barrierOverflowKeys`; the cap arm continues into
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
`lake build Hypostructure.Graph.Strategy.SpineRun` also succeeds (8618 jobs),
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

  instantiated at `Graph/Strategy/SpineRun.lean:166` as
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
  `1e39f3a`, `lake build Hypostructure.Graph.Strategy.SpineRun` succeeds
  (8618 jobs), as do the canonical API modules and all fifteen
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
  *other* side of node `[21]`'s decision, as `Result.barrierOverflow`, and is
  Row 9's arm rather than this row's.

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
  Before this change the Type A fact chain did not carry that maximality —
  `netDeficiencyCap` onwards existentially quantified a bare
  `IsWindowPacking` — so the inheritance the row-42 evidence claimed was not
  available, and the hypothesis is genuinely necessary: a `δ`-regular object
  with the empty packing satisfies every clause `typeALowSurplus` used to
  carry, and its own vertex set is then a nonempty internal `δ`-core.  The
  maximality clause is now carried by `netDeficiencyCap`, `netChargeNegative`,
  `netChargeNonNegative`, `windowJoinPressure`, `negativeSupport` and
  `typeALowSurplus`; see rows 41 and 42.

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
  refinement-stable.  `typeAUnsaturatedReceivers_audit_facts` in `SpineRun`
  pins the unsaturated exit's audit to its exact thirty facts in commit order,
  and both exits carry `audit_complete` and `audit_facts_unique`.
- **Transport and terminals.** No EG-specific carrier, result, residual,
  ledger, executor or routing helper exists at this row: the rows are
  `AtomicStrategy` and `Decision` values in `Hypostructure.Graph.Strategy`,
  quantified over the keys they commit, and the mathematics is in
  `Hypostructure.Graph`, parametric in the baseline and the scale.  Neither arm
  of `[89]` is a terminal — the saturated arm is node `[93]`'s entry (row 12)
  and the unsaturated arm is node `[90]`'s (unported) — so both are
  `Spine.Result` exits, `Result.typeASaturatedReceiver` and
  `Result.typeAUnsaturatedReceivers`.  The `Result.typeALowSurplus` exit they
  replace is deleted; there is no second path to the Type A residual.

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
  live declaration consumed them.  When rows 26–29 are ported, whichever
  constraint the fan ledger actually needs is to be registered where it is
  consumed.  `Problem.lean` drops the two discharged fields with them.

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


### Row 12 — Visible receiver-entry returns `[93]`

- **Paper fact.** Node `[93]` asks "some port has four visible receiver-entry
  returns?".  `def:typeA-visible-load` defines an anchored return through
  `\vec e = (w,h)` as a simple path `P : h ⤳ w` in `G - wh`; it is a
  receiver-entry return when `P = Γ ∘ Q` with `Γ` from `h` to a receiver `r`
  having all internal vertices outside `X`, and `Q` a simple `r ⤳ w` path inside
  `X`; and it is *visible for* a routed cubic `u` with `r(u) = w` when `T_u` is a
  subpath of `Q`, or `Q` is the lexicographically first channel assigned to the
  terminal receiver edge of `T_u`.  `lem:typeA-first-entry` proves the first
  entry of an anchored return is a receiver; `lem:typeA-entry-budget` bounds the
  distinct first-entry edges by `Σ_{r ≠ w} q(r)`; `lem:typeA-port-return` gives
  every completion port at least one anchored return.  The yes-arm is
  `lem:typeA-visible-entry` — four visible receiver-entry returns force one of
  exits (1)–(7) of `def:typeA-saturated-exits` — refined by
  `lem:typeA-unpeeled-visible-routing`.  The no-arm is `[94]`, "visible-first
  excess: `S_sil^exc(X) ≥ 4 D_A(X)`", built from `def:typeA-excess-basin` and
  quantified by `lem:typeA-silent-excess-count`,
  `lem:typeA-reduced-silent-residual`, `lem:typeA-silent-excess` and
  `lem:typeA-unpeeled-silent-routing` (exits (4)–(8)).
- **What the Lean does.**  `VisibleReturnSaturation presentation object profile
  threshold` is
  `∀ certificate : TypeACertificate presentation object,
   ∃ (port : CompletionPort ⟨certificate.common.support⟩ profile)
     (loads : Finset (…FullVertex profile)),
   threshold ≤ loads.card ∧
   ∀ load ∈ loads, ∃ returnData : ReceiverEntryReturn port,
     load.1 ∈ returnData.channel.path.support`.
  `CompletionPort` is `(receiver, outside, adjacent, outside_mem)`;
  `ReceiverEntryReturn port` bundles `anchored : AnchoredReturn port`, an
  `entry` receiver, a `connector` walk with
  `connector_supported_only_at_end`, and a
  `channel : ReceiverEntryChannel entry port.receiver`.  `AnchoredReturn` carries
  `firstEntry`, `firstEntry_mem` and `firstEntry_receiver` as *fields*, so
  `lem:typeA-first-entry` is assumed, not proved.  `VisibleLoadLedger` — the
  only place `visible`/`silent` loads are named — has fields
  `visible : FullVertex → Prop`, `visible_correct : Prop` and
  `silent_correct : Prop`; the last two are opaque propositions with no content,
  and the record is not used by this node.  `visibleReturnSplit` registers
  `ofAlternative` with neither `closeLeft` nor `closeRight`; the registration
  site passes `threshold := fun _ => erdosReceiverLoadProfile.loadMultiplier`,
  i.e. `4`.  The `∃ returnData` is per load and unconstrained: the same return
  may witness all four loads, and the only link between a load and a return is
  `load.1 ∈ returnData.channel.path.support`.
- **What it should do.**  The alternative has to be attached to the receiver `w`
  selected at `[89]`, quantify over that receiver's own completion ports, demand
  four *distinct* receiver-entry returns through one port, and define visibility
  as "the canonical trace `T_u` is a subpath of the channel `Q`" — which
  presupposes a canonical trace map (row 11).  Its no-arm has to carry `[94]`'s
  inequality `S_sil^exc(X) ≥ 4 D_A(X)`.
- **Gap.**  The predicate is again `∀ certificate` (vacuous with no
  certificate); the port is existentially chosen over all completion ports of the
  support rather than being a port of the `[89]` receiver; the four returns are
  not required to be distinct; and visibility is replaced by membership of the
  load vertex in the channel's support, which neither mentions `T_u` nor the
  canonical channel order.  Nothing in the right arm carries `[94]`'s excess
  bound: the payload is exactly `PLift (¬ VisibleReturnSaturation …)`.
  **Facts therefore fails.**

  The prerequisite this row inherits from row 11 is **supplied**.
  `def:typeA-visible-load` asks whether the canonical trace `T_u` is a subpath
  of the channel `Q`, so the row needs the trace *path*, not only its endpoint.
  `Graph.FiniteObject.tracePath?` is that path: the first path of the object's
  own `Graph.FinitePathSelection.pathSchedule` from `u` to a given receiver
  that satisfies `Graph.FiniteObject.IsTracePath`.  It is asked exactly at the
  receiver `traceReceiver?` returns, so `T_u` and `r(u)` are one routing rather
  than two, and `isSome_tracePath?_of_traceTo` says a routed vertex always has
  one.  What this row still has to add is the rest of
  `def:typeA-visible-load` — the anchored return through a completion port
  (`Graph.EdgeRootedReturn` is already exactly that shape at the dart `(w,h)`),
  the receiver-entry channel and the `P = Γ ∘ Q` decomposition, and the
  visibility test itself.  The manuscript's visibility is a disjunction whose
  second clause — "`Q` is the lexicographically first channel assigned to the
  terminal receiver edge of `T_u`" — does not fix which assignment is meant;
  porting this row has to settle that reading against the manuscript before
  either arm of `[93]` can be committed, because dropping the clause weakens
  the yes arm and strengthens the no arm at once.
- **Ledger and residual.**  `DichotomyData` reads only `ProblemInput`; the port,
  the returns and the loads are all rebuilt from `input.object` rather than from
  the receiver the `[89]` arm selected.  The stable residual is retained by the
  framework extension.
- **Transport and terminals.**  No CT: Core `DichotomyData`, no registered
  closure on either side.  The export shows `v25` (`dichotomy:5`) entered by
  `e54` from `v24`, leaving by `e42` `v25 → v26` (`left`, "Four visible returns")
  and `e53` `v25 → v34` (`right`, "Visible-first excess"); both conditional, no
  terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeA-visible-load` | def | `Graph.ReceiverLoad.CompletionPort`<br>`Graph.ReceiverLoad.AnchoredReturn`<br>`Graph.ReceiverLoad.ReceiverEntryReturn` | no CT |
| `lem:typeA-first-entry` | lem | | |
| `lem:typeA-entry-budget` | lem | | |
| `lem:typeA-port-return` | lem | | |
| `lem:typeA-visible-entry` | lem | | |
| `lem:typeA-unpeeled-visible-routing` | lem | | |
| `def:typeA-saturated-exits` | def | | first consumed here, as the yes-arm's target list; its clauses are also the alternatives at rows 13–19 |
| `def:typeA-excess-basin` | def | | |
| `lem:typeA-silent-excess-count` | lem | | |
| `lem:typeA-reduced-silent-residual` | lem | | |
| `lem:typeA-silent-excess` | lem | | |
| `lem:typeA-unpeeled-silent-routing` | lem | | |

`Graph.ReceiverExhaustion.Exit` is the only type in the tree that enumerates
saturated-receiver alternatives, but it has six constructors, merges exits (3),
(5) and (6) into a single `closed : T.Predicate input.object`, and leaves exits
(4), (7), (8) as arbitrary type parameters `Step`, `Handoff`, `Residual`; it is
referenced only by `TypeAReceiverClosure.target_of_exit`, which has no call
site.  It therefore does not state `def:typeA-saturated-exits` and the cell is
empty.

**CT composition at this row.**  No CT.  The Core recipe is
`DichotomyData.ofAlternative`, the same one rows 11 and 13–19 use.  This row's
stage decides only the visible/silent split and registers *no* closure, so both
arms are conditional continuations: the left enters the exit chain at row 13,
the right enters the duplicated exit chain at row 16's `v34`.  Nothing about the
split is executed or retained — the classification is `Classical.propDecidable`
on a proposition over `ProblemInput` — so `[94]`'s quantitative excess has no
stage in which to be recorded.

### Row 13 — Exit 1: Mersenne return `[95]`

- **Paper fact.** Exit (1) of `def:typeA-saturated-exits`: "an anchored return
  through a completion port of `w` has length in `Mers`".  In the proof of
  `lem:typeA-visible-entry` it is one of the four visible returns through the
  fixed port `\vec e = (w,h)`; `lem:return-equivalence` then yields the
  power-of-two cycle.  `lem:typeA-exits-discharged` records the outcome for the
  whole exit list: exits (1)–(3), (5) and (6) close inside the Type A analysis,
  exit (4) peels exactly one routed load, exit (7) is transferred to Type B.
- **What the Lean does.**  `exitOneSplit` registers `ofAlternative` on
  `fun input => Nonempty (rootedReturn.RootedReturn (object input))`, where
  `rootedReturn := Graph.RootedReturnTargetAlgebra.shifted PowerOfTwoLength` and
  `RootedReturn profile object = EdgeRootedReturn object profile.ReturnLengthOK`,
  a structure `(dart, path : (graph.deleteEdges {dart.edge}).Walk dart.snd dart.fst,
  isPath, length_ok)`.  The dart ranges over every dart of the whole object.
  `closeLeft` is
  `fun input witness => closure input
   ((rootedReturn.target_iff_hasRootedReturn (object input)).mpr witness.down)`,
  a direct transport along the registered biconditional.
- **What it should do.**  The alternative has to be
  `∃ anchoredReturn : AnchoredReturn port, ReturnLengthOK anchoredReturn.path.length`
  for a completion port `port` of the receiver fixed at `[89]`, with the
  conversion to the target going through
  `AnchoredReturn.toEdgeRootedReturn` (which exists and takes exactly that data).
- **Gap.**  The registered alternative is `HasEdgeRootedReturn object
  (ShiftedCycleLength PowerOfTwoLength)`, which by
  `RootedReturnTargetAlgebra.target_iff_hasRootedReturn` is *equivalent* to
  `HasCycleWithLength PowerOfTwoLength object` — the registered target itself,
  and the very predicate node `[6]` reduced.  The selected minimal
  counterexample already carries `¬ Target`, so the left arm is refuted by the
  residual the branch has carried since `[4]` and the node decides nothing.  No
  port, no receiver and no anchoring appear in the type, and
  `AnchoredReturn.toEdgeRootedReturn` is not used here.
  **Facts therefore fails.**
- **Ledger and residual.**  `DichotomyData` on `ProblemInput`; the return is
  searched in `input.object`, not in the completion port the predecessor arm
  produced.  Stable residual retained.
- **Transport and terminals.**  No CT: Core `DichotomyData` with a registered
  `closeLeft`.  The export shows `v26` (`dichotomy:6`) entered by `e42` from
  `v25`, leaving by `e26` `v26 → t5` (`left`, closed, "Target cycle") and `e41`
  `v26 → v27` (`right`, conditional, "No Mersenne return").

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:typeA-exits-discharged` | lem | | first consumed here, as the disposition of exit (1); it is equally the disposition of rows 14–19 |

**CT composition at this row.**  No CT.  The Core recipe is
`DichotomyData.ofAlternative`.  This row's stage decides whether an accepted
edge-rooted return exists and registers `closeLeft`, so its yes-arm is closed by
the runner from the registered target transport and its no-arm is a conditional
edge into row 14.  There is no execution to compose: the decision is
`Classical.propDecidable` on a `Nonempty` proposition, and the closure is a
one-line transport, so nothing is enumerated, bounded, or retained.

### Row 14 — Exit 2: power-of-two theta `[97]`

- **Paper fact.** Exit (2): "two anchored receiver-entry returns through one
  completion port are internally vertex-disjoint as anchored paths and their
  lengths sum to a power of two".  `lem:typeA-common-port-return-cycle` proves
  that two anchored returns through the *same* port `\vec e = (w,h)` share the
  endpoints `h` and `w`, so internal disjointness makes their union a simple
  cycle of length `|P₁| + |P₂|`; "in particular, if `|P₁|+|P₂| ∈ Pow`, then `G`
  contains a dyadic cycle".
- **What the Lean does.**  `exitTwoSplit` registers `ofAlternative` on
  `fun input => ∃ pair : Graph.CommonEndpointsCycle (object input),
   CycleLengthOK (pair.forward.length + pair.backward.length)`.
  `CommonEndpointsCycle` is `(ends : Vertex × Vertex, forward, backward :
  Walk ends.1 ends.2, forward_isPath, backward_isPath, internallyDisjoint,
  nondegenerate)` — an arbitrary internally disjoint pair of paths anywhere in
  the object.  `closeLeft` is
  `fun input witness => closure input ⟨witness.down.choose.target CycleLengthOK
  witness.down.choose_spec⟩`, i.e. the generic two-path criterion.
- **What it should do.**  The alternative has to be
  `∃ (port : CompletionPort …) (P₁ P₂ : AnchoredReturn port), internally disjoint ∧
  CycleLengthOK (P₁.path.length + P₂.path.length)`, together with the missing
  bridge turning two `AnchoredReturn`s through one port into a
  `CommonEndpointsCycle` — the content of `lem:typeA-common-port-return-cycle`
  beyond `lem:two-path-criterion`.
- **Gap.**  No port, no receiver-entry structure and no anchoring: the pair is
  quantified over the whole object, so the alternative implies
  `HasCycleWithLength PowerOfTwoLength` and is again refuted by the selected
  counterexample's target avoidance.  No declaration converts two
  `AnchoredReturn`s through one `CompletionPort` into a `CommonEndpointsCycle`.
  **Facts therefore fails.**
- **Ledger and residual.**  `DichotomyData` on `ProblemInput`; the pair is
  searched in `input.object`.  Stable residual retained.
- **Transport and terminals.**  No CT: Core `DichotomyData` with `closeLeft`.
  The export shows `v27` (`dichotomy:7`) entered by `e41` from `v26`, leaving by
  `e27` `v27 → t6` (`left`, closed, "Target cycle") and `e40` `v27 → v28`
  (`right`, conditional, "No accepted theta").

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:typeA-common-port-return-cycle` | lem | | |

`Graph.CommonEndpointsCycle.target` states `lem:two-path-criterion`, a row-2
object, and is what this node's `closeLeft` calls; nothing states the
port-anchored strengthening that is `lem:typeA-common-port-return-cycle`, so the
cell is empty.

**CT composition at this row.**  No CT.  The Core recipe is
`DichotomyData.ofAlternative`.  This row's stage decides whether an internally
disjoint path pair of accepted total length exists and registers `closeLeft`, so
its yes-arm closes and its no-arm is a conditional edge into row 15.  As at
row 13 there is no executed search: `Classical.propDecidable` classifies an
existential over `CommonEndpointsCycle`, and no enumeration, capacity or code
comparison is involved.

### Row 15 — Exit 3: P13 label collision `[99]`

> **Correction — this row is unbuilt, and its four `✅` cells were wrong.**  The
> evidence below describes `v28` (`dichotomy:8`), a `Core.DichotomyData`
> registration in the legacy `Blueprint` topology.  That topology and its
> `Core.ProblemDefinition` registry are deleted, `Graph/TypeBClosure.lean` and
> `Graph/TypeBMarkedFan.lean` are quarantined, and no live declaration states
> `[99]`.  The mathematics recorded below was faithful *at the time it was
> read*, which is why the row's `Facts` cell had been ticked; but a column is a
> claim about the current tree, and nothing here compiles.  All four cells are
> now `❌`.  The description is retained as the porting reference — in
> particular `hasCycleWithLength_of_illegalLabel` is the closure the ported row
> will need, and node `[18]`'s `localAlgebra` fact is already live to supply
> `lem:labels`.

- **Paper fact.** Exit (3): "a shared `P₁₃` window violates the corresponding
  legal-label relation `C_s`".  In `lem:typeA-exits-discharged` this is
  "precisely failure of the legal `P₁₃` label relation from `lem:labels`; by
  definition of the relation, it creates a target event or a target-defective
  local state".  `lem:labels` (node `[18]`, row 7) fixes the legal attachment
  labels as the nonempty subsets of `{0,…,12}` avoiding gaps `2` and `6`.
- **What the Lean does.**  `IllegalWindowLabel packing` is
  `∃ window ∈ packing.selected, ∃ (outside : Vertex) (a b : TypeBMarkedFan.Index),
   a ≠ b ∧ graph.Adj outside ((windowOfPacking window).coordinate a.val) ∧
   graph.Adj outside ((windowOfPacking window).coordinate b.val) ∧
   (∀ t ≤ 12, outside ≠ (windowOfPacking window).coordinate t) ∧
   ¬ TypeBMarkedFan.IsLegal {a, b}`.
  `windowOfPacking` maps an `InducedPathMaximalPacking.Window object 13` to a
  `TypeBClosure.Window` by `coordinate index := window ⟨min index 12, _⟩`, and
  `windowOfPacking_isPacked` proves the two `IsPacked` fields from
  `window.map_adj_iff` (edges) and `window.injective` (distinctness) — a
  derivation, not a supplied field.  `closeLeft` destructs the witness and
  applies `TypeBClosure.hasCycleWithLength_of_illegalLabel accepted
  (windowOfPacking_isPacked window) distinct lower upper windowFree illegal`;
  `accepted` is `acceptedCycleLengths`, whose three fields are `by decide` proofs
  that `4`, `8`, `16` satisfy `PowerOfTwoLength`.  The registration passes
  `packing := fun input => Graph.InducedPathMaximalPacking.maximalProfile
  input.object 13`, a deterministic function of the object.
- **What it should do.**  The alternative has to say that an outside vertex
  attaches to a packed window at two positions whose gap violates the legal
  relation, and its closure has to produce the dyadic cycle — which is what the
  type says.  A stricter reading of `[99]` would quantify over the window shared
  by two canonical traces at the `[89]` receiver rather than over all selected
  windows, but the manuscript's own discharge of exit (3) is the local label
  test.
- **Gap.**  `none`.  The illegal-label attachment produces a `4`- or `8`-cycle
  through the window, which the registered target accepts, and every ingredient
  of the closure is derived from the packing embedding.  **Facts passes.**
- **Ledger and residual.**  `DichotomyData` reads only `ProblemInput`, and the
  packing is recomputed as `maximalProfile input.object 13` rather than read from
  the row-6 packing capability.  Because `maximalProfile` is a deterministic
  function of the object and the object is the preserved active input, the
  recomputation is a canonical reconstruction of the same selection rather than
  a branch fact re-derived from the wrong evidence; the existing Ledger verdict
  is unchanged.
- **Transport and terminals.**  No CT: Core `DichotomyData` with `closeLeft`;
  Graph owns `hasCycleWithLength_of_illegalLabel` and the packing selection.  The
  export shows `v28` (`dichotomy:8`) entered by `e40` from `v27`, leaving by
  `e28` `v28 → t7` (`left`, closed, "Label/target collision") and `e39`
  `v28 → v29` (`right`, conditional, "No label collision").

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|

No `\label` of this range is first consumed here: exit (3) is clause (3) of
`def:typeA-saturated-exits` (row 12), its disposition is
`lem:typeA-exits-discharged` (row 13), and the label algebra it tests is
`lem:labels`, node `[18]`, which belongs to row 7.

**CT composition at this row.**  No CT.  The Core recipe is
`DichotomyData.ofAlternative`.  This row's stage decides the illegal-attachment
predicate on the canonical maximal packing and registers `closeLeft`, so its
yes-arm closes through the Graph-owned cycle construction and its no-arm is a
conditional edge into row 16.  The packing itself is produced by
`InducedPathMaximalPacking.maximalProfile`, a Graph selection, not by a CT; no
adapter is invoked at this vertex.

### Row 16 — Exit 4: target-defective quotient `[101]`

- **Paper fact.** Exit (4): "a quotient in the canonical exit-(4) family
  `𝒬₄(w)` of `def:typeA-exit4-family` is target-defective".  It is the
  *target-defect peeling* exit: `def:typeA-exit4-peeling` gives the receiver its
  routed loads `ℒ(w) = {u : r(u) = w}`, a peeling set `P₄(w) ⊆ ℒ(w)` with no
  load listed twice, and the residual load `L₄(w) = L(w) − |P₄(w)|`;
  `lem:typeA-exit4-peeling-charge` gives the remaining charge
  `q(w) − ¼ − ¼·L₄(w)`, nonnegative once `L₄(w) ≤ 4q(w) − 1`;
  `lem:typeA-exit4-discharge` says one adjoined unpeeled load is again a peeling
  set and reduces the deficit by exactly `¼`; and
  `lem:typeA-exit4-residual-routing` says that while `L₄(w) ≥ 4q(w)` the
  unpeeled loads realize an exit, the exit-(4) case enlarging the peeling set by
  one.  The arm returns to node `[89]`.
- **What the Lean does.** `Graph/ExitFourPeeling.lean` owns the ledger:
  `ExitFour.routedLoads` is `ℒ(w)` — the set whose cardinality
  `FiniteObject.routedLoad` already is, tied to it by `routedLoad_eq_card` —
  `ExitFour.residualLoad` is `L₄(w)`, and `ExitFour.SaturatedAfter` is
  `FiniteObject.Saturated` read at the residual.
  `ExitFour.not_saturatedAfter_iff` is `lem:typeA-exit4-peeling-charge` cleared
  of the quarter: the remaining charge is nonnegative exactly when the peeled
  residual is unsaturated.  `ExitFour.residualLoad_insert` is
  `lem:typeA-exit4-discharge`: adjoining an unpeeled load drops `L₄(w)` by
  exactly one.  `ExitFour.exists_unsaturated_peeling` is the descent
  `lem:typeA-exit4-residual-routing` opens, by induction on `L₄(w)`.
  `Spine.typeAExitFourPeelDichotomy` is node `[101]`, and its yes arm runs
  `Spine.typeAPeeledCharge`, which commits that every receiver has a peeling set
  leaving it unsaturated — the receiver retested at node `[89]` — and leaves the
  block as `Route8Result.peeled`.  The no arm continues down the ladder.
- **What it should do.** The alternative should name the quotient of the
  response state — an identification of declared coordinates preserving the
  boundary-degree profile, belonging to one of (Q1)–(Q5) — together with the
  outside context distinguishing it.
- **Gap.** The peel-and-return is now the manuscript's, and so is every step of
  its ledger.  What the decision splits on is the exit-(4) *conclusion* of
  `lem:typeA-unpeeled-visible-routing` and `lem:typeA-unpeeled-silent-routing` —
  "the peeling set can be enlarged by one unpeeled load" — rather than on the
  quotient itself, because (Q1)–(Q4) of `def:typeA-exit4-family` are built from
  the receiver's declared coordinates of node `[93]`, which is row 12's and
  unbuilt.  Clause (Q5) *is* built: `Route8.Data.ExitFour`, decided by
  `Spine.typeAExitFourDichotomy` on the same node.  **Facts therefore fails**,
  on the definition of the alternative alone.
- **Ledger and residual.** `Decision.run` for the split; `rowManifest` for the
  peel row, which reads the peel step by exact key.  Residual unchanged.
- **Transport and terminals.** No terminal: the yes arm is
  `Route8Result.peeled`, carrying `typeAExitFourPeel` and `typeAPeeledCharge`,
  which is the manuscript's return edge `[102] → [89]`.  The earlier revision
  closed this arm instead; that is corrected.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeA-exit4-peeling` | def | `Graph.ExitFour.routedLoads`<br>`Graph.ExitFour.residualLoad`<br>`Graph.ExitFour.insert_subset_routedLoads` | standalone |
| `lem:typeA-exit4-peeling-charge` | lem | `Graph.ExitFour.not_saturatedAfter_iff` | standalone |
| `lem:typeA-exit4-discharge` | lem | `Graph.ExitFour.residualLoad_insert` | standalone |
| `lem:typeA-exit4-residual-routing` | lem | `Graph.ExitFour.exists_unsaturated_peeling` (the descent); its exit-(4) reading is node `[101]`'s alternative | standalone |
| `def:typeA-exit4-family` (Q5) | def | `Graph.Route8.Data.ExitFour`, decided by `Spine.typeAExitFourDichotomy` | standalone |
| `def:typeA-exit4-family` (Q1)–(Q4) | def |  | *(node `[93]`'s declared coordinates; row 12)* |
| `rem:typeA-exit4-peeling-use` | rem | `Spine.typeAPeeledCharge` — peeled loads leave before the pure Type A charge is summed | standalone |

**CT composition at this row.** None.  A `Decision` and one fact-only Strategy;
the manuscript's loop back to `[89]` is the descent inside
`exists_unsaturated_peeling`, which is why no cycle appears in the DAG.

### Row 17 — Exit 5: target-complete compression `[103]`

- **Paper fact.** Exit (5): "the response data give a nontrivial target-complete
  response compression; when this compression is realized by a smaller proper
  atom, it is a target-complete compression in the sense of `lem:replacement`".
  `lem:typeA-exits-discharged` closes it in two cases: *"If the compression is
  realized by a smaller proper atom, it contradicts hereditary
  target-uncompressibility (`cor:uncompressible`); if it occurs only at the
  trace-basin response level, it is exactly failure alternative (b) in
  `def:typeA-trace-basin` and therefore is not an admissible route-8
  residual."*
- **What the Lean does.** `Spine.typeAExitFiveDichotomy` is node `[103]`: it
  splits on whether some indexed entry's internal-forgetting reading `ρ°_𝒞`
  agrees with its core reading, which is alternative (b) — a nontrivial
  target-complete quotient of the trace-basin response.  Its no arm is
  `Route8.TraceSurviving`, the (R2) reading nodes `[116]` and `[124]` consume.
  Its yes arm runs `Spine.typeAExitFiveRealizationDichotomy`, the manuscript's
  own second case split: the realized arm commits
  `∃ support, InterfaceReplacement.CompressibleSupport …` and is **closed** by
  `closeIncompatible` against node `[14]`'s `uncompressible` through the
  `Incompatible` instance `Spine.typeAExitFiveCompressionClosed`; the
  response-level arm commits that no proper support realizes it, and — lacking
  `typeAExitFiveFree` — cannot enter the route-8 arm, which is precisely "not an
  admissible route-8 residual".
- **What it should do.** This.
- **Gap.** None.  Both cases of the manuscript's sentence are implemented, and
  the closing one closes against a ledger fact rather than an assumption.  The
  reading level is the trace-basin response, which is where
  `def:typeA-trace-basin`'s alternative (b) lives; the receiver's general
  response data of node `[93]` is row 12's and is not needed by either case.
  The realization test is taken on the object — *does any proper support carry
  `lem:replacement`'s compression* — rather than on the particular quotient the
  yes arm committed.  That is the manuscript's split with the weaker premise on
  the closing side and the stronger conclusion on the other: the realized arm
  closes on a compression that genuinely exists, and the response-level arm
  carries `¬ ∃ support, CompressibleSupport …`, which entails that *this*
  compression is not realized by a smaller proper atom.  The split is
  exhaustive, so no branch of exit (5) is left unaccounted for.
  Node `[103]` is entered from node `[101]`'s no arm inside
  `Spine.runRouteEight`, which is not yet attached to `Spine.run`: the path
  `[93]`--`[99]` from node `[89]` is rows 12--15 and is unbuilt.  That is those
  rows' gap and is recorded there; row 17 elaborates against any incoming index
  that carries node `[14]`'s `uncompressible`, and `Fixtures/Route8ExitFive.lean`
  runs it on the Type A residual of node `[63]` that `Spine.run` does reach.
- **Ledger and residual.** Two `Decision.run`s, so the residual is unchanged and
  each arm commits its own fact against the one immutable prefix; the closure is
  Core's `closeIncompatible` reading node `[14]` and node `[103]` by exact key.
  The block requires `uncompressible` on the incoming index, so a branch that has
  not proved node `[14]` does not elaborate.  Nothing upstream is dropped:
  `Fixtures.Route8ExitFive.closed_arm_retains_every_incoming_fact` and
  `…trace_level_arm_retains_every_incoming_fact` show every incoming key is still
  in the arm's exact index.
- **Transport and terminals.** `Route8Result.exitFiveClosed` carries the closure
  key, and `Fixtures.Route8ExitFive.closed_arm_dispatches_closed` shows
  `RoutedTask.dispatchFor` returns `closed` on that index for every task list, so
  the terminal is the framework router's and not the row's.
  `Route8Result.exitFiveTraceLevel` leaves the block open, as the manuscript's
  alternative (b) does: `…trace_level_arm_is_not_closed` and
  `…trace_level_arm_has_no_exit_five_absence` show it carries neither the closure
  entry nor `typeAExitFiveFree`, so it is neither a closed terminal nor an
  admissible route-8 residual.  The closed arm's audit is complete,
  duplicate-free and free of empty commits.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeA-saturated-exits` exit (5) | def | `Spine.typeAExitFiveDichotomy` | standalone |
| `def:typeA-trace-basin` alternative (b) | def | `Graph.Route8.Data.SurvivingTrace`<br>`Graph.Route8.TraceSurviving` | standalone |
| `lem:replacement` compression | lem | `Graph.Strategy.InterfaceReplacement.CompressibleSupport` | standalone |
| `cor:uncompressible` | cor | node `[14]`'s `uncompressible` fact, read by `Spine.typeAExitFiveCompressionClosed` | standalone |
| `lem:typeA-exits-discharged` exit-(5) case | lem | `Spine.typeAExitFiveRealizationDichotomy` with `closeIncompatible`<br>`Spine.typeAExitFiveCompressionClosed`<br>checked in `Fixtures.Route8ExitFive` | standalone |

**CT composition at this row.** None.  Two `Decision`s and Core's closure.

### Row 18 — Exit 6: response delocalization `[105]`

- **Paper fact.** Exit (6): "the equality of responses delocalizes to a proper
  support or to the whole graph".  `def:typeA-trace-basin` clause (c): an
  equality among coordinates of `ρ_u(B_u)` becomes target-complete only after
  adjoining a larger connected support `Z ⊋ B_u`, *either with `Z ⊊ G` or with
  `Z = G`*.  `lem:typeA-exits-discharged` excludes the first by
  `lem:proper-smearing` and the second by `lem:no-silent-global-smearing`.
- **What the Lean does.**  Nothing.  There is no live declaration for node
  `[105]`: the spine vocabulary has no exit-`(6)` key — its `Key` enumeration
  carries `typeAExitFour…` and `typeAExitFive…` but nothing for exit `(6)` — no
  `Decision` names the node, and no fixture reaches it.  The only code that
  mentions the alternative is `Strategy.TypeAReceiverExhaustion.exitSixSplit`
  with `ResponseDelocalization`, which is **quarantined** (listed in
  `hypostructure/quarantine.txt`, imported by no live module), and the
  `typeAExitSix` slot of the commented-out legacy `Blueprint` topology in
  `StrategyDag.lean`, which does not elaborate.  Neither is evidence about the
  current proof.
- **What it should do.**  The alternative has to name two response coordinates,
  their equality, and a support `Z` strictly containing the basin at which that
  equality first becomes target-complete, split into the two cases `Z ⊊ G` and
  `Z = G`, with the two exclusions applied respectively.  Both arms close, so
  the node contributes two closure entries and no continuation — exit `(6)` is a
  *closed* exit in `def:typeA-saturated-exits`.
- **Gap.**  The whole row.  It is entered from node `[103]`'s no arm, which
  exists (`typeAExitFiveFree`, row 17), so the predecessor is available; what is
  missing is the node itself and everything under it.  A port has to supply, as
  generic framework declarations: the enlarging support `Z ⊋ B_u` and the
  coordinate equality that first becomes target-complete at it; the `Z ⊊ G` /
  `Z = G` split; and the two exclusions, which are nodes `[40]`–`[43]` of
  row 40 — so it may only *read* them by exact key, never restate them.  The
  earlier revision of this entry described the quarantined
  `ResponseDelocalization` predicate as though it were running, and reported a
  nesting defect against exit (5) on that basis; both claims are withdrawn as
  statements about code that is not in the build.
- **Ledger and residual.**  None — no ledger step exists at this node.  When
  ported it is fact-only: the alternative is a property of the object, so the
  residual is unchanged and the node is a `Decision` against the immutable
  prefix, with the two closures appended by Core rather than by a row.
- **Transport and terminals.**  None.  The `v31`/`e37`/`t10` vertex and edge
  identifiers recorded in the earlier revision belong to the retired legacy
  `Blueprint` DAG, which is a comment in `StrategyDag.lean`; there is no live
  topology in which they exist.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|

No `\label` of this range is first consumed here: exit (6) is clause (6) of
`def:typeA-saturated-exits` (row 12) and clause (c) of `def:typeA-trace-basin`
(row 16), its disposition is `lem:typeA-exits-discharged` (row 13), and the two
exclusions it invokes, `lem:proper-smearing` and
`lem:no-silent-global-smearing`, are nodes `[40]`–`[43]`, which belong to
row 40.

**CT composition at this row.**  None, and none is expected: like rows 16 and
17 this is a `Decision` on a property of the object followed by Core's closure,
with the two exclusions read from row 40 by exact key.

### Row 19 — Exit 7: decorated handoff fan `[107]`

- **Paper fact.** Exit (7): "a high-degree decorated handoff fan envelope is
  produced"; it is the Type B handoff exit, and by `lem:typeA-exits-discharged`
  the branch "is reclassified as a decorated handoff fan envelope and leaves the
  Type A charge calculation", with the envelope of `def:decorated-fan-envelope`
  and admissibility from `lem:decorated-fan-admissibility`,
  `lem:decorated-envelope-no-double-count` and
  `lem:window-handoff-center-accounting`.  `def:typeA-trace-basin` clause (d)
  produces it from two declared outside connector germs with the same
  boundary-degree image having a surviving first separator, routed by
  `lem:typeA-continuation-routing`, which by
  `lem:typeA-cubic-switch-absorption` has ambient degree at least `4` and is
  handed over by `lem:typeA-high-degree-handoff`.
  `rem:typeA-typeB-stratification` records that this whole block uses no
  conclusion of `lem:typeB-exclusion` — only the handoff interface.
- **What the Lean does.**  Nothing.  There is no live declaration for node
  `[107]`: the spine vocabulary has no exit-`(7)` key, no `Decision` names the
  node, and no fixture reaches it.  The declarations the earlier revision
  described — `Strategy.TypeAReceiverExhaustion.exitSevenSplit` and
  `Graph.TypeABCertificate`'s `DecoratedHandoffEnvelope` /
  `TypeAB.DecoratedHandoffData` — are **quarantined**; the only live module that
  imported `TypeABCertificate`, `Graph.TypeAReceiverClosure`, is quarantined
  too, so nothing in the build reaches any of it.  The `typeAExitSeven` slot in
  `StrategyDag.lean` is inside the commented-out legacy topology.
- **What it should do.**  The alternative has to be existential in the
  certificate, produce the envelope out of the two connector germs and their
  surviving first separator at the `[89]` receiver, and carry the envelope's
  admissibility and no-double-count accounting so the Type B branch can consume
  it.
- **Gap.**  The whole row, and it is the only exit in the range whose arm is not
  a terminal: exit `(7)` *hands the branch to Type B*, so a port must land on the
  Type B entry as a fact the Type B rows read by exact key, not on an open leaf.
  `rem:typeA-typeB-stratification` constrains how: the handoff may use only the
  interface objects, never a conclusion of `lem:typeB-exclusion`, so the envelope
  and its admissibility have to be available to Type A without importing the Type
  B exclusion argument.  The earlier revision's defect analysis — that the
  predicate is vacuous on an object with no Type A certificate, and that its
  centers are unrelated to the receiver — was a correct reading of the
  quarantined predicate, but it is not a statement about the current proof and is
  withdrawn as such.
- **Ledger and residual.**  None — no ledger step exists at this node.  When
  ported, the envelope is data about the object, so the residual is unchanged and
  the handoff is a fact on the shared prefix.
- **Transport and terminals.**  None.  The `v32`/`e36`/`t11` identifiers and the
  `branch_endpoint` / `accumulated_strategy_residual` shapes recorded in the
  earlier revision are from the retired legacy `Blueprint` DAG and its sealed
  report; neither exists in the live spine.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:decorated-fan-envelope` | def |  | *(only the quarantined `Graph.TypeAB.DecoratedHandoffData`; nothing live)* |
| `lem:decorated-envelope-no-double-count` | lem | | |
| `lem:window-handoff-center-accounting` | lem | | |
| `lem:typeA-continuation-routing` | lem | | |
| `lem:typeA-cubic-switch-absorption` | lem | | |
| `lem:typeA-high-degree-handoff` | lem | | |
| `lem:decorated-fan-admissibility` | lem | | |
| `rem:typeA-typeB-stratification` | rem | | placed here as the closest row: it is a remark about the whole `[89]`–`[109]` block and about this row's handoff in particular |

**CT composition at this row.**  None yet.  This is the one exit in the range
whose yes arm neither closes nor stays in Type A, so a port has to decide
whether the envelope's admissibility and no-double-count accounting are proved
by a CT or by generic `Graph` lemmas read as facts; the no arm is the edge into
node `[109]`, which row 17's no arm already reaches through
`Spine.runRouteEight`.

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
  closes — `[68]` certifies nothing — so `Spine.Result` gains the two exits
  `typeBHeavyCentre` and `typeBDegreeFourCentres` and loses the
  `typeBHighSurplus` leaf, which is no longer where the branch stops.
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
  `Spine.Result.typeBLocalDichotomy` replaces the `typeBHeavyCentre` exit, which
  is no longer where the heavy arm stops.  `typeBLocalDichotomy_audit_facts`
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
  registration.  `Spine.Result` now exits at `typeBHeavyFanCap` and
  `typeBDegreeFourFanCap`.  `typeBHeavyFanCap_audit_facts` and
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
  rows 24 and 25 now continue on it, so `Result.typeBCertificateMarked` was
  deleted rather than kept beside the new exits.  Its audit theorems moved with
  it: the three indices that now terminate this arm are pinned by
  `typeBDirectCycleClosed_audit_facts`, `typeBDisjointAssignment_audit_facts`
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
  `typeBDirectCycleFree` on the right.  The left fact is "some connected assigned
  Type B support of some packing carries a high centre with a
  `TypeBDirectCycle.DirectCycleConfiguration`"; the right is the universally
  quantified complement, `TypeBDirectCycle.DirectCycleFree` at every high centre
  of every such support over every packing.  The branch is `by_cases` on the left
  `Prop`, and the arm not taken supplies the other arm's clause directly (no
  `push_neg` is needed: `DirectCycleFree` *is* the negation).
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
  key and the exit is `Result.typeBDirectCycleClosed`.
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
  arm of `[71]` produced, so the residual is unchanged (a fact-only step) and
  every earlier fact stays in the output index.  It reads no prerequisite fact:
  the question is a `Prop` about the object and its packed windows and the branch
  is taken classically, so nothing is consumed and nothing is declared — a
  declared requirement the executor does not read would be a false dependency.
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

### Row 25 — B2 ledger `[72]`/`[81]` (ported: `Spine.b2AssignmentDichotomy`)

- **Paper fact.**  The global half of node `[72]`, and node `[81]` asking the
  same question on the degree-four branch.  (B2) of
  `def:typeB-bridge-statements`: for a connected assigned Type B support `X` with
  no fan-certificate residual centre, the high-degree fan centres of `X` admit a
  canonical refined ledger in the sense of `def:typeB-candidate-ledger` — (a) a
  certificate-closed centre is assigned `A_h ⊆ N(h) \ H_X` with
  `ch_X(h) + Σ_{v ∈ A_h} ch_X(v) ≥ 0` and no carrier assigned to two centres;
  (b) each positive-deficit centre carries its hybrid B1 entry, whose window and
  non-window half-credits are disjoint from the ordinary deficiency reserve;
  (c) all entries are mutually disjoint refinements of `Ĉh_B(X)`; (d) the ledger
  is maximal for the support assignment.  Carriers are enumerated by
  `def:typeB-ledger-carriers`: a non-centre vertex, an assigned centre, a
  packed-window incidence of capacity `½`, a non-window fan incidence of capacity
  `½`, an internal/mixed reserve block.  Failure of the disjoint-carrier part
  produces a *minimal* Type B overlap obstruction
  (`lem:typeB-bridge-to-overlap`, `def:typeB-overlap-obstruction`), and absence
  of any obstruction gives the maximal disjoint ledger
  (`lem:typeB-maximal-completion`).
- **What the Lean does.**  `Spine.b2AssignmentDichotomy` is a `Decision` on the
  literal direct-cycle-free cursor, producing `typeBDisjointAssignment` on the
  left and `typeBOverlapObstruction` on the right.  The left fact is "every
  connected assigned Type B support of every packing carries a
  `TypeBRefinedSupport.RefinedSupportAssignment`" — a demand family drawn from
  the support's assigned centres, a `HasDisjointChoice`, and `IsMaximal`.  The
  right fact is "some such support carries a
  `TypeBRefinedSupport.OverlapObstruction`" — a nonempty demand family with no
  disjoint choice *every proper nonempty subfamily of which has one*.

  Both arms are theorems, not a proposition and its negation.  The split is
  `by_cases` on the *obstruction* existential; the yes arm of the paper's
  question is then derived, support by support, by
  `TypeBRefinedSupport.typeBMaximalCompletion` — which is
  `lem:typeB-maximal-completion` — and the no arm carries the obstruction the
  minimization in `exists_overlapObstruction_of_not_hasDisjointChoice` builds,
  which is `lem:typeB-bridge-to-overlap`: among the nonempty subfamilies whose
  disjoint choice fails, one of least cardinality is minimal by construction,
  and `hasDisjointChoice_mono` is what makes the restriction to a subfamily
  meaningful.

  `CandidateEntry` carries `assigned`, `assigned_adjacent`, `assigned_subset`,
  `assigned_notCentre`, `chosen`, `chosen_owned` and the paying field `pays`.
  `carriers` is the disjoint sum of the vertex carriers (`insert hub assigned`)
  and the chosen incidences, so `Disjoint` over `Carrier object` is
  simultaneously the manuscript's "no carrier is assigned to two different fan
  centres" and its disjointness of the half-incidence entries;
  `hub_ne_of_disjoint_carriers` reads the centre half of that back.
- **What it should do.**  This is what it does.
- **Gap.**  None.  **Facts passes.**  Three notes.

  *The failed legacy row is not what is here.*  The retired `b2Split` payload was
  `∃ profile, 2 ≤ profile.closedCount` — a local count at one centre, with the
  window and envelope free `Finset` fields of the binder, containing no
  `Disjoint`, no carrier, no candidate entry and no maximality.  That is why the
  legacy row's Facts column was `❌`.  The ported row asks the simultaneous-choice
  question the manuscript asks, and the negative arm is the overlap obstruction
  rather than a bare negation.

  *Charges are scaled integers.*  `ch_X(v) = δ_X^+(v) − α` and
  `ch_X(h) = −(d_G(h) − δ) − α` at `α = 1/s`, and a chosen incidence carries
  `½`; `pays` is that inequality cleared of denominators at `2s`, exactly as
  `Graph.NegativeNetCharge` clears at `s`.  No reciprocal appears, nothing
  rounds, and `α = 1/4` is never written — the discharge scale is
  `data.dischargeScale`.  Clauses (a) and (b) are the one inequality at
  `chosen = ∅` and at `chosen ≠ ∅` respectively.

  *What clause (b) defers.*  The *content* of the hybrid B1 entry — the split of
  `D_B` into the window credit `½I_W` and the remaining non-window demand `D_N`
  — is `lem:typeB-hybrid-B1`, which is node `[74]`/`[82]`, row 26.  Row 25 asks
  only whether the entries can be chosen disjointly, which is what the
  manuscript's node `[72]`/`[81]` diamond asks; the entry's *existence* at a
  positive-deficit centre is a binder of `HasDisjointChoice`, not an assumption
  this row makes about the graph, and row 26 is what will supply it.
- **Ledger and residual.**  The `Decision` runs on the literal ledger row 24's
  free arm produced, so the residual is unchanged and every earlier fact stays in
  the output index — including `typeBDirectCycleFree`, which is why the local
  fan-window ledger's completeness is *available* here rather than re-proved.
  The row declares no requirement, for the same reason rows 23 and 24 declare
  none: the branch is taken classically on a `Prop` about the object, and
  `typeBMaximalCompletion` consumes no ledger fact, so declaring one would be a
  false dependency.  The legacy row's failure mode is gone: the old read was
  through `residualOf stage`, which yielded only `ProblemInput` and therefore
  could not even express the `Residual object` the B2 machinery wanted; the
  ported row states B2 over the packing and support the spine's own facts already
  quantify over.  Ledger passes.
- **Transport and terminals.**  Core owns execution: `Decision.run`.  Neither arm
  closes — `[72]`'s second half certifies nothing — so `Spine.Result` gains the
  two exits `typeBDisjointAssignment` (the entry of `[74]`/`[82]`) and
  `typeBOverlapObstruction` (the entry of `[73]`/`[83]`, which the manuscript
  routes to the fan-mass node `[75]`/`[84]`).  The two indices differ in exactly
  one entry; `typeBDisjointAssignment_audit_facts` and
  `typeBOverlapObstruction_audit_facts` pin both in commit order by `rfl`, and
  the fixture `Fixtures.TypeBFanWindowNode` checks by `simp` that neither key
  appears in the other's index.  No EG-specific declaration exists at this row.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeB-ledger-carriers` | def | `TypeBRefinedSupport.Carrier`<br>`TypeBRefinedSupport.CandidateEntry.carriers` | no CT |
| `def:typeB-candidate-ledger` | def | `TypeBRefinedSupport.CandidateEntry`<br>`TypeBRefinedSupport.HasDisjointChoice`<br>`TypeBRefinedSupport.IsMaximal` | no CT |
| `def:typeB-bridge-statements`, (B2) | def | `TypeBRefinedSupport.RefinedSupportAssignment`<br>key `Spine.Key.typeBDisjointAssignment` | no CT; the B1 half is row 26 and the bridge-residual classification row 27 |
| `def:typeB-overlap-obstruction` | def | `TypeBRefinedSupport.OverlapObstruction`<br>key `Spine.Key.typeBOverlapObstruction` | no CT |
| `lem:typeB-bridge-to-overlap` | lem | `TypeBRefinedSupport.exists_overlapObstruction_of_not_hasDisjointChoice`<br>`TypeBRefinedSupport.hasDisjointChoice_or_overlapObstruction`<br>`TypeBRefinedSupport.hasDisjointChoice_mono` | no CT |
| `lem:typeB-maximal-completion` | lem | `TypeBRefinedSupport.typeBMaximalCompletion` | no CT |
| `lem:typeB-global-local-reflection` | lem | | consumed at row 27, not here |
| `prop:typeB-global-local-bridge` | pro | | consumed at row 27, not here |
| `def:typeB-window-incidence-profile` | def | | row 26 |
| `def:fan-closed-port` | def | | row 26 |
| `prop:fan-closed-port-typeB-routing` | pro | | row 26 |
| `def:typeB-multiclosed-residual` | def | | row 29 supplies `[79]`'s profile |

Both lemmas of this row are *reached by the run*: the arm the branch takes calls
either `typeBMaximalCompletion` or the minimization, so neither is a faithful
implementation without a call site — which is what the eleven-row table of the
retired legacy row recorded, and what is now false of these two.  The remaining
empty cells are deliberate: they are other nodes' paper objects, listed so a
reader tracking node `[72]` sees what this row does *not* claim.

**Both positions are wired.**  `[72]` and `[81]` are one row at two positions,
and because a `Decision` carries no predecessor, the same `directCycleDichotomy`
and `b2AssignmentDichotomy` values run after the degree-four cursor.  With row 29
ported they do: `[81]` is entered on `degreeFourMarkedKeys` and exits at
`degreeFourDirectCycleClosedKeys`, `degreeFourDisjointAssignmentKeys` and
`degreeFourOverlapObstructionKeys` — the last two being the entries of `[82]` and
`[83]`.  All three carry `[79]`'s profile fact, which is what lets `[82]` read the
closed-neighbour deficit without re-deriving it.  The fixture installs both rows
at both cursors.

**CT composition at this row.**  No CT.  A `Decision` lowered by `Decision.run`
against the one canonical `ExactLedger`.  No CT decides B2 either, and the reason
is structural rather than a gap: `HasDisjointChoice` is a simultaneous choice with
a disjointness side condition over a finite family, so there is no enumeration,
capacity comparison or descent for a CT to own — the mathematics is the
minimization that turns its failure into a minimal obstruction, and that is a
theorem the row calls, not an aggregation the framework performs.

### Row 26 — Hybrid B1 entry `[74]`/`[82]` (`ordered_witness_scan:2`, exported as `v48`)

- **Paper fact.**  `def:typeB-hybrid-incidence` sets `c = c_W + c_M + c_I`,
  `I_W = 2c_W + c_M`, `I_N = c_M + 2c_I`, and
  `D_N(𝔉) = max{0, D_B(𝔉) - ½ I_W(𝔉)}`.
  `lem:typeB-multiclosed-budget` gives `4 ≤ k ≤ 8` with `c ≥ 2` for `k ≤ 7` and
  `c ≥ 1` for `k = 8`, the exactness of the `2c` distinct packed-window
  incidences, and `D_B(𝔉) ≤ ½·2c - ¾`.
  `lem:typeB-hybrid-incidence-budget` proves the `2c` non-`h` incidences
  pairwise disjoint (if `z` were shared, `u-h-v-z-u` is a `4`-cycle) and gives
  total capacity `½I_W + ½I_N = c`, paying `D_B` with slack `(11-k)/4 ≥ ¾`.
  `lem:typeB-hybrid-B1` packages this as the B1 alternative: a positive-deficit
  residual either contains a direct power-of-two cycle; or realizes a
  target-defective quotient, a target-complete compression, or a proper/global
  delocalization; or has a disjoint hybrid entry of capacity at least `D_B(𝔉)`.
  Node `[74]` is `prop:typeB-bridge-reduction`: with B2 and no fan-certificate
  residual centre, `defp(X) - σ(X) ≥ ¼|V(X)|`, using
  `lem:typeB-postledger-core-hygiene` to decompose the post-ledger core into
  admissible Type A components.
- **What the Lean does.**  `hybridEntryScan` is a `Core.ScanData P` with
  `Item input = Graph.TypeBFanClosedPorts.Profile (object input)`,
  `schedule input = Graph.TypeBProfileSchedule.profileCandidates (object input)`,
  and `witness input profile = Graph.TypeBProfileSchedule.IsHybridEligible profile`.
  `IsHybridEligible profile` unfolds to `2 ≤ profile.closedCount` — the same
  proposition that row 25's left payload existentially quantifies.  `ScanData`
  has no conclusion field, so the node appends the first eligible profile and
  nothing else.
- **What it should do.**  The node would have to append the conclusion of
  `TypeBProfileSchedule.hybridEntry_of_isHybridEligible`, whose type is
  `(profile : Profile object) → (ledger : LoadCapacityProfile) → IsHybridEligible profile →
   profile.closedNeighbourDeficit ledger ≤ profile.hybridCapacity ledger ∧
   profile.hybridNonWindowDemand ledger ≤ profile.nonWindowCredit ∧
   ((object.degree profile.marked.fan.hub : ℚ) + 1) * ledger.dischargeRate - 1 ≤ profile.closedNeighbourDeficit ledger ∧
   5 * ledger.dischargeRate - 1 ≤ profile.closedNeighbourDeficit ledger ∧
   0 < profile.closedNeighbourDeficit ledger`,
  together with the disjointness step
  `TypeBFanClosedPorts.Profile.incidences_endpoint_injective`
  (which uses `NormalForm.noCommonNeighbourOutside`, i.e. the four-cycle
  exclusion) and the remaining three arms of B1 — direct cycle, target-defective
  quotient, target-complete compression, proper/global delocalization — as a
  four-way alternative rather than a one-sided scan.
- **Gap.**  The recorded reason for this row, "no B1 charge theorem", is
  inaccurate and I correct it: the charge theorem exists and is stated
  correctly.  `hybridEntry_of_isHybridEligible` derives `D_B ≤ ½I_W + D_N` and
  `D_N ≤ ½I_N` from `windowCredit_add_nonWindowCredit`, `Marked.highDegree`,
  `Marked.degree_le_eight`, and the recorded rate constraints
  `one_lt_five_mul_dischargeRate` and `nine_mul_dischargeRate_le_three`; the
  incidence counts `windowIncidenceTotal = 2c_W + c_M` and
  `nonWindowIncidenceTotal = c_M + 2c_I` are derived from filtered finsets, with
  `card_incidences : incidences.card = 2 * closedCount` and
  `card_windowIncidences`/`card_nonWindowIncidences` matching `I_W` and `I_N`.
  The verdict nevertheless stands, for a sharper reason: `ScanData` is a
  five-field record with no proposition to carry a conclusion, so none of that
  arithmetic enters the run — the node appends "some profile has `2 ≤ c`" and
  the whole of `lem:typeB-hybrid-B1` is proved beside the ledger.  A second
  difference is that B1 is a four-way alternative and the node is a one-sided
  scan: the target-defect, compression, and delocalization arms have no
  representation at `v48`.  **Facts therefore fails.**

  **Entry point moved (row 25 port).**  This row's predecessor is no longer the
  legacy `v47` left arm.  Node `[74]`/`[82]` is now entered on the key index
  `Spine.typeBDisjointAssignmentKeys`, whose head is
  `Spine.Key.typeBDisjointAssignment` and which carries
  `typeBDirectCycleFree` and the whole certificate-marked history beneath it.
  Node `[82]`, its second position, is entered on
  `Spine.degreeFourDisjointAssignmentKeys`, which additionally carries `[79]`'s
  `typeBDegreeFourProfile` — the closed-neighbour deficit identity this row's
  payment consumes, available as a committed fact rather than re-derived.  Every
  declaration this row's `Where` column names is still quarantined and still does
  not elaborate, so nothing here is repaired; the port targets are the two live
  indices above.
- **Ledger and residual.**  `liftScan`/`scanRecipe` re-index through
  `residualOf stage` and seal the contract with `certify := fun _ _ => none`;
  the predecessor and residual are retained.  The read is `residualOf`, so the
  `PLift (∃ profile, 2 ≤ profile.closedCount)` witness appended one stage
  earlier at `v47` is invisible here, and the node re-derives the same
  proposition from the graph.  Ledger fails.
- **Transport and terminals.**  Core's `Strategy.OrderedWitnessScan` owns the
  enumeration.  Graph supplies `profileCandidates` and its `nodup` proof.  The
  export shows `v47 → v48` (`e64`) and `v48 → v39` (`e70`); no terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeB-hybrid-incidence` | def | `TypeBFanClosedPorts.Profile.windowIncidenceTotal`<br>`TypeBFanClosedPorts.Profile.nonWindowIncidenceTotal`<br>`TypeBFanClosedPorts.Profile.hybridNonWindowDemand` | unconsumed — no call site |
| `lem:typeB-multiclosed-budget` | lem | `TypeBFanClosedPorts.Profile.card_incidences`<br>`TypeBFanClosedPorts.Profile.incidences_endpoint_injective`<br>`TypeBMarkedFan.Marked.degree_mem_window` | unconsumed — no call site |
| `lem:typeB-hybrid-incidence-budget` | lem | `TypeBProfileSchedule.hybridEntry_of_isHybridEligible`<br>`TypeBFanClosedPorts.Profile.incidences_endpoint_injective` | unconsumed — no call site |
| `lem:typeB-hybrid-B1` | lem | `TypeBOverlapObstruction.hybridEntry` | unconsumed — no call site |
| `lem:typeB-postledger-core-hygiene` | lem | `TypeBPostLedgerCore.postLedgerCoreHygiene`<br>`TypeBPostLedgerCore.postLedgerCoreHygieneInContext` | unconsumed — no call site |
| `prop:typeB-bridge-reduction` | pro | | |

The declarations named in `TypeBHybridLedger.lean` all open
`namespace Hypostructure.Graph.TypeBFanClosedPorts.Profile`, which is why they
are qualified as `TypeBFanClosedPorts.Profile.*` above.
`lem:typeB-multiclosed-budget` is a five-clause conjunction and only two of its
clauses have a type: `card_incidences` is "exactly `2c` distinct incidences" and
`incidences_endpoint_injective` its distinctness proof; the `c ≥ 2 / c ≥ 1`
split by `k` and the bound `D_B ≤ ½·2c - ¾` have no declaration, so the cell
lists what exists and no more.  `prop:typeB-bridge-reduction` is empty: no
declaration has `defp(X) - σ(X) ≥ ¼|V(X)|` under the hypotheses "B2 holds and
`X` has no fan-certificate residual centre" as its type — the nearest is the
fourth disjunct of `TypeBExclusion.typeBExclusion`, recorded at row 28.

**CT composition at this row.**  No CT.  A registered `ordered_witness_scan:2`
lowered by `Core.Strategy.Dag.liftScan → scanRecipe`, with
`certify := fun _ _ => none`.  This row is where the absence of a CT costs the
most: `lem:typeB-hybrid-incidence-budget` is a capacity aggregation
(`½I_W + ½I_N = c ≥ D_B + (11-k)/4`) of exactly the shape CT5 performs, and
`hybridEntry_of_isHybridEligible` already proves it.  A CT5 stage with
`required := closedNeighbourDeficit` and `capacity := hybridCapacity` over the
incidence family would put that inequality on the ledger; the registered
`ScanData` has no `required`/`capacity` pair and no proposition, so it cannot.

### Row 27 — Bridge fan-mass `[73]`,`[75]` (`baseline_demand_accounting:1`, exported as `v49` and `v50`)

- **Paper fact.**  `def:typeB-residual-mass` sets
  `No_-(X) = max{0, -No(X)}`, `M_B(𝒳_B) = Σ_X No_-(X)`,
  `S_B(𝒳_B) = Σ_X Σ_{h ∈ H_X} (d_G(h) - 3)`, and records `S_B ≤ 2σ(G)` from the
  at-most-twice occurrence convention (ordinary role and grouped-envelope role).
  `lem:typeB-bridge-deficit-bound` proves
  `No_-(X) ≤ 8 Σ_{h ∈ H_X}(d_G(h) - 3)` through the envelope estimate
  `(k - 3 + ¼) + c/4 ≤ 5k/4 - 11/4 ≤ 8(k-3)`, valid for `k ≥ 4` since it is
  equivalent to `27k ≥ 85`.  `lem:decorated-envelope-deficit-bound` is the same
  bound for grouped decorated envelopes, and
  `lem:typeB-bridge-with-route8-core` and
  `lem:decorated-envelope-with-route8-core` extract a route-8 non-window core
  into `D_A` first.  `prop:typeB-bridge-sublinear` concludes
  `M_B(𝒳_B) ≤ 8 S_B(𝒳_B) ≤ 16 σ(G) = O(√n) = o(|R|)`.
- **What the Lean does.**  `fanMassAccounting` is a
  `Core.Strategy.BaselineDemandAccounting.Registration Residual` with
  `Site residual = (object residual).Vertex`,
  `Witness residual _ = (object residual).Vertex`,
  `family` the vertex/neighbour enumeration,
  `Active residual vertex = Graph.TypeBFanMass.IsChargedCentre (object residual) vertex`,
  `Supports residual vertex witness = ((object residual).graph.Adj vertex witness ∧ (object residual).degree witness = baselineDegree residual)`,
  `contribution residual vertex _ = (object residual).degree vertex - baselineDegree residual`,
  and — decisively —
  `required residual = (object residual).degreeSurplus (baselineDegree residual)`
  and
  `capacity residual = (object residual).degreeSurplus (baselineDegree residual)`.
  `required` and `capacity` are syntactically the same term, so the CT5 demand
  comparison `required ≤ capacity` is `Nat.le_refl` at every input and decides
  nothing.  `IsChargedCentre object hub` is
  `IsFanCertificateResidual object hub ∨ IsB2Failure object hub`, with
  `IsB2Failure object hub = (4 ≤ object.degree hub ∧ (overlapPartners object hub).Nonempty)`
  and `overlapPartners` defined through `fanEnvelope`, which is a
  degree-derived vertex set of the ambient graph, not the assigned envelope of
  any Type B support.  `contribution`, `required`, and `capacity` are all
  supplied as natural-number degree observables; no rational charge, no
  `negativePart`, and no factor `8` or `16` occurs in the registration.
- **What it should do.**  The statements of record are
  `TypeBBridgeResidual.Residual.negativePart_le_eight_surplus :
   (∀ h ∈ residual.centers, NormalForm object h) →
   residual.negativePart profile ≤ 8 * residual.surplus + max 0 (-residual.residualCoreCharge profile)`
  and
  `TypeBFanMass.fanResidualMass_le_sixteen_globalSurplus :
   (∀ v, 3 ≤ object.degree v) → normal → discharged →
   fanResidualMass object profile ≤ 16 * globalSurplus object`.
  The node's `required` would have to be the residual mass
  `fanResidualMass object profile` and its `capacity` the surplus budget
  `16 * globalSurplus object`, over an `Active` family drawn from
  `fanMassResiduals object`, so that the CT5 comparison is the manuscript's
  inequality rather than an identity.
- **Entry point moved (row 25 port).**  The fan-mass row's two positions are
  entered on live indices now.  `[73]`/`[83]` is
  `Spine.typeBOverlapObstructionKeys`, headed by
  `Spine.Key.typeBOverlapObstruction`, whose value is a *minimal*
  `TypeBRefinedSupport.OverlapObstruction` — so the minimality
  `lem:typeB-global-local-reflection` needs arrives as a committed fact rather
  than being re-derived; `[75]` on the certificate-residual side is
  `Spine.typeBCertificateResidualKeys`.  Node `[84]`, the degree-four fan-mass
  route, is entered on `Spine.degreeFourOverlapObstructionKeys` from `[83]` and on
  `Spine.degreeFourResidualKeys` from `[80]`'s no arm.  Everything the `Where`
  column below names is still quarantined and still does not elaborate.
- **Gap.**  `required = capacity` makes the accounting tautological: the node
  compares `σ(G)` with `σ(G)`.  Neither the factor `8` of
  `lem:typeB-bridge-deficit-bound` nor the factor `16` of
  `prop:typeB-bridge-sublinear` nor the `≤ 2σ(G)` occurrence bound of
  `def:typeB-residual-mass` is expressible in the fields that are registered,
  and the two theorems that do state them are reachable from no node.  The one
  non-trivial content of the registration is `Active = IsChargedCentre`, which
  does implement clauses (i) and (ii) of the bridge-residual classification —
  but decided on ambient degree and ambient `fanEnvelope` overlap rather than on
  an assigned support.  **Facts therefore fails.**
- **Ledger and residual.**  `BaselineDemandAccounting.Profile` reads its object
  through `current : Query Previous (fun _ => Residual)`, defaulting to
  `Query.residual`; `spec` and `family` are formed by
  `profile.current.read previous` and `current.dependentMap`, so the whole
  demand family is a function of `residualOf`.  The literal predecessor stage is
  retained by the CT5 ledger extension.  As above, the assigned Type B support
  produced by `[65]` and the B2 failure recorded one stage earlier at `v47` are
  not readable; `IsB2Failure` is recomputed from ambient degrees.  Ledger fails.
- **Transport and terminals.**  Core owns the aggregation and the ledger
  extension through CT5; the application supplies `Site`, `Witness`, `family`,
  `Active`, `Supports`, `contribution`, `required`, `capacity` and the three
  decidability instances.  The registration is placed twice, so the export has
  two vertices: `v50` (`v40 → v50` `e68`, "No certificate labelling";
  `v50 → v39` `e72`) and `v49` (`v47 → v49` `e65`, "B2 disjointness fails";
  `v49 → v39` `e71`).  Both export `components: []`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeB-residual-mass` | def | `TypeBFanMass.fanResidualMass`<br>`TypeBFanMass.fanSurplusMass`<br>`TypeBFanMass.fanCenterOccurrences` | unconsumed — no call site |
| `lem:typeB-bridge-deficit-bound` | lem | `TypeBBridgeResidual.Residual.negativePart_le_eight_surplus`<br>`TypeBBridgeResidual.Residual.envelopeAllowance_le_eight_surplus` | unconsumed — no call site |
| `lem:typeB-bridge-with-route8-core` | lem | | |
| `lem:decorated-envelope-deficit-bound` | lem | | |
| `lem:decorated-envelope-with-route8-core` | lem | | |
| `prop:typeB-bridge-sublinear` | pro | `TypeBBridgeResidual.typeBBridgeSublinear_globalSurplus`<br>`TypeBFanMass.fanResidualMass_le_sixteen_globalSurplus` | unconsumed — no call site |
| `rem:typeB-status` | rem | | |

The three grouped-decorated-envelope objects are empty because no declaration
takes a grouped envelope: `Graph.DecoratedFan.Certificate` is a single hub with
arms, and there is no type for the core–centre incidence component
`𝔜_𝔠`, its counted core `Y*_𝔠`, or its centre-token sum `ω(𝔠)`.
`rem:typeB-status` is commentary on the same classification and is placed here,
the closest row, with nothing implementing it.  The only declaration of this
group that the run touches is `TypeBFanMass.IsChargedCentre`, which is not
itself a labelled paper object — it is the union of clauses (i) and (ii) of
`def:typeB-bridge-statements` (row 25).

**CT composition at this row.**  **CT5**, one stage, and the only CT in the
range.  Read from the code rather than the reference table:
`Core.Strategy.BaselineDemandAccounting.execution` is
`CTAdapters.ct5 accounting` with no `.compose`, so the reference table's
`BaselineDemandAccounting | CT5` is confirmed and needs no correction.
`Profile.spec : CT5.Spec Previous` re-indexes `budget`, `Site`, `Witness`,
`Active`, `Supports`, `contribution`, `required`, `capacity` through
`profile.current.read`, and `Profile.capability` adds the dependent enumeration
and the three decidability instances.  CT5 then aggregates `contribution` over
the `Active` sites supported by the family and compares the total against
`capacity`, appending the outcome as a ledger extension.  A single CT is the
right shape for a mass estimate and nothing is lost by not composing further —
what is lost is that both sides of the comparison are the same term, so the one
stage decides an identity rather than `M_B ≤ 16σ(G)`.

### Row 28 — Bridge deficit `[76]`/`[85]` (`ordered_witness_scan:3`, exported as `v39`)

- **Paper fact.**  Nodes `[76]` and `[85]` close the Type B branch: Type B
  cannot carry the linear deficit outside two-carrier route 8, once the fan-mass
  residual is sublinear.  The operative content is `lem:typeB-exclusion` — for a
  connected admissible support carrying high-degree surplus, with no
  fan-certificate residual centre, admitting B2, and containing neither an
  admissible route-8 residual profile nor an admissible positive-deficit fan,
  `defp(X) - σ(X) ≥ ¼|V(X)|`, so `No(X) ≥ 0`; consequently a Type B support
  with `No(X) < 0` and no route-8 or positive-deficit residual witnesses failure
  of B2.  Its Step 1 is the closed-neighbourhood charge
  `ch_X(h) + Σ_{u ∈ N(h)} ch_X(u) ≥ (11-k)/4 - c = -D_B(𝔉_h) ≥ 0`.
  `thm:branch-kill` is the branch-closure theorem these nodes feed, jointly with
  `[123]`.
- **What the Lean does.**  `bridgeDeficitScan` is a `Core.ScanData P` with
  `Item input = (object input).Vertex`,
  `schedule input = (object input).orderedVertices`, and
  `witness input vertex = (baselineDegree input ≤ (object input).degree vertex)`.
  At the registered `baselineDegree = 3` this reads `3 ≤ deg v`, which is the
  standing baseline predicate `MinimumDegreeAtLeast 3` restricted to one vertex
  — a fact already carried on the residual since row 1.  The scan therefore
  succeeds at the first vertex of `orderedVertices` and appends nothing new.
  No charge, deficit, surplus, or `No(X)` term occurs in the type.
- **What it should do.**  The statement of record is
  `TypeBExclusion.typeBExclusion`, whose conclusion is the four-way alternative
  `(∃ h ∈ residual.centers, 0 < deficit ∧ deficit ≤ hybridCapacity) ∨ SharedCarrier residual ∨ residual.residualCoreCharge ledger < 0 ∨ ((∀ h ∈ residual.centers, object.degree h ≤ 8 ∧ IsCertificateClosed … ∧ (residual.closedFanCount h : ℤ) ≤ closedCountCap … ∧ 0 ≤ fanEntryCharge …) ∧ 0 ≤ residual.netCharge ledger ∧ (residual.core.card : ℚ) * ledger.dischargeRate ≤ residual.totalDeficiency - residual.surplus)`
  — the last conjunct being `¼|V(X)| ≤ defp(X) - σ(X)`.  The node would have to
  append that alternative on the assigned support and route its route-8 disjunct
  to `[77]`.
- **Gap.**  The registered witness is the minimum-degree baseline restated per
  vertex; it carries no part of `lem:typeB-exclusion`.
  `TypeBExclusion.typeBExclusion` exists and states the correct alternative, and
  is reachable from no node of the export.  **Facts therefore fails.**
- **Ledger and residual.**  `liftScan`/`scanRecipe`; predecessor and residual
  retained, `certify := fun _ _ => none`.  The node is the join of four arms —
  the closed direct-cycle terminal, the B1 scan, and both fan-mass vertices —
  and reads none of them: `residualOf` gives only `ProblemInput`, so the scan
  runs the same degree test whichever arm reached it.  Ledger fails.
- **Transport and terminals.**  Core's `Strategy.OrderedWitnessScan` owns
  execution.  The export shows four incoming edges `t21 → v39` (`e69`),
  `v48 → v39` (`e70`), `v49 → v39` (`e71`), `v50 → v39` (`e72`), and one
  outgoing autoroute `v39 → v24` (`e73`, label "Route-8 cores to the Type A
  ledger", `scope: sibling`, `relation: literal_residual`,
  `selection.rule: deepest_most_restrictive`, destination `v24` at depth 16).
  The Type B branch therefore has no terminal of its own: instead of closing at
  `[76]`/`[85]` and handing route-8 cores to `[77]`, it re-enters the Type A
  saturated-receiver dichotomy `v24` (`[89]`).

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:typeB-exclusion` | lem | `TypeBExclusion.typeBExclusion` | unconsumed — no call site |
| `thm:branch-kill` | thm | | |

`thm:branch-kill` spans `[76]`, `[85]` and `[123]`; `[123]` is outside this
range, and no declaration states the combined closure, so the cell is empty at
the row that consumes it first.

**CT composition at this row.**  No CT.  A registered `ordered_witness_scan:3`
lowered by `Core.Strategy.Dag.liftScan → scanRecipe`, with
`certify := fun _ _ => none`.  The node is also the four-way join of the branch,
but a scan recipe performs no join semantics: `liftScan` reads only
`residualOf stage`, so the four incoming arms are indistinguishable to it.  The
outgoing `autoroute` is a separate Core mechanism, not a CT — the export's
`bridge_provenance` names `Ledger.extend_previous`,
`Ledger.residualOf_extend` and `HaltingProgram.snoc_previous` as the framework
lemmas, and `BridgeCertificate.residual_eq` as the relation witness.

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
  halves, so `Result.typeBDegreeFourFanCap` is **deleted** and replaced by the
  four exits `degreeFourCertificateResidual`, `degreeFourDirectCycleClosed`,
  `degreeFourDisjointAssignment` and `degreeFourOverlapObstruction`, each with its
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

### Row 30 — Ordered surplus activation `[125]`–`[128]`

- **Paper fact.** `[125]` is the sparse-pressure survivor: a minimal
  counterexample past `[19]` for which none of the five sparse surplus exits
  of `def:named-surplus-exits` occurs — "(a) a direct dyadic contradiction …
  (b) a target-defective quotient … (c) a nontrivial target-complete
  compression of a proper atom … (d) a proper or global delocalization
  coordinate … (e) an open-port suppression cycle whose chord set violates
  the arithmetic conclusion".  `[126]` is `lem:sparse-slack-surplus`:
  `σ(G) = n - 6 - 2λ` and `m = (3/2)n + (1/2)σ(G)`, on the envelope
  `m ≤ 2n-2`.  `[127]` is `lem:sparse-excess-port-extraction`:
  `|𝒫_exc| = σ(G)`, and for every `p = (h,x) ∈ 𝒫_exc`, `d_G(h) ≥ 4`,
  `d_G(x) = 3` and `N_G(x) = {h, a_p, b_p}` with `a_p, b_p ≠ h` distinct.
  `[128]` is `lem:sparse-port-activation`: each selected port carries
  `T(p) = {x, a_p, b_p}`; a simple `x`–`h` path `R_p ⊆ G - hx` whose first
  edge after `x` is `xa_p` or `xb_p`; if `p` is open, the lexicographically
  first `Q_p ⊆ G - x` joining `a_p` to `b_p` of length `2^{j(p)} - 1` with
  `j(p) ≥ 2`; if `p` is triangular, the triangle `x a_p b_p x` together with
  `R_p`.  `def:active-surplus-demands` is the bundle `(p, T(p), R_p, Γ(p))`
  not removed by an exit, and `lem:surviving-active-family` concludes
  `𝒜₀ := 𝒫_exc` with `|𝒜₀| = σ(G)`.
- **What the Lean does.**
  `Graph.Strategy.SurplusAccounting.orderedSurplusActivation
  (object : Residual → Graph.FiniteObject) (baselineDegree : Residual → Nat)
  : Core.Strategy.OrderedSurplusActivation.Registration Residual`.  Every
  field is supplied, none derived: `Index := fun residual => (object
  residual).Vertex`; `order := fun residual => vertices (object residual)`
  (the whole declared vertex scan); `FailureData := fun _ _ => Unit`;
  `Failure := fun residual centre => baselineDegree residual < (object
  residual).degree centre ∧ ∃ endpoint, (object residual).graph.Adj centre
  endpoint ∧ (object residual).degree endpoint ≠ baselineDegree residual`;
  `failureData := fun _ _ _ => ()`;
  `failureDecidable := fun _ _ => Classical.propDecidable _`;
  `contribution := fun residual centre => (object residual).degree centre -
  baselineDegree residual`; and `accounting := activeSurplusAccounting object
  baselineDegree`, itself all supplied: `Site := Vertex`,
  `Witness := fun residual _ => Vertex`, `family := { indices := vertices …,
  fibres := neighbours … }`, `Active := fun residual vertex => baselineDegree
  residual < degree vertex`, `Supports := fun residual vertex witness =>
  Adj vertex witness ∧ degree witness = baselineDegree residual`,
  `contribution := degree vertex - baselineDegree residual`, and
  `required = capacity = (object residual).degreeSurplus (baselineDegree
  residual)` — syntactically the same term on both sides of CT5's resource
  comparison.  At the registration site
  (`/home/guillem/structural_exhaustion/examples/hypostructure_erdos_64_eg/HypostructureErdos64EG/Official/Definition.lean`)
  the arguments are `object := fun input => input.object` and
  `baselineDegree := fun _ => erdosReceiverLoadProfile.baselineDegree`, which
  is the literal `3` of `Problem.lean`.  No theorem in
  `/home/guillem/structural_exhaustion/hypostructure/Hypostructure/Graph/Strategy/SurplusAccounting.lean`
  constrains this registration.
- **What it should do.** The CT6 half would have to enumerate `𝒫_exc`, not
  `V(G)`: an `Index` of type `Σ h : Vertex, {x // Adj h x}` restricted to
  `4 ≤ d(h)`, with `FailureData` carrying `T(p)`, a `Walk x h` in `G - hx`,
  and either a `Walk a_p b_p` in `G - x` of Mersenne length or a triangle
  certificate — i.e. `lem:sparse-port-activation`'s four clauses as the data
  of an index, not `Unit`.  `Failure` would have to name one of
  `def:named-surplus-exits`'s five conclusions, so that "no failure over the
  whole order" is the survivor hypothesis of `lem:surviving-active-family`.
  A theorem of type `(activePorts residual).card = (object
  residual).degreeSurplus (baselineDegree residual)` together with
  `∀ p, 4 ≤ degree p.centre ∧ degree p.cubic = 3 ∧ N(p.cubic) = {p.centre,
  a, b}` would state `[127]`.
- **Gap.** `Failure` is not an exit of `def:named-surplus-exits`; it is the
  negation of a fact `[9]`–`[10]` already proved and appended by row 4
  (`SlackIncompatibilityLedger`: carriers of `4 ≤ degree` are pairwise
  nonadjacent, so every neighbour of a higher-degree centre sits at the
  baseline), so no index of the order can satisfy it and the ordered
  exhaustion certifies nothing.  `FailureData` is `Unit`, so even a firing
  index would produce no `T(p)`, `R_p`, `Q_p`, or `Γ(p)`: `[128]` is absent
  entirely.  `[127]` is absent as a statement; the only port-shaped object,
  `CanonicalAccounting.activePorts`, is `Σ vertex, Fin (degree vertex -
  baselineDegree)` — a numeral, with no cubic endpoint `x` and hence no
  `a_p`, `b_p`.  `[126]`'s `m ≤ 2n-2` and `σ = n-6-2λ` do not occur.  The
  CT5 half proves `X ≤ X`.  **Facts therefore fails.**
- **Ledger and residual.** `Core.Strategy.OrderedSurplusActivation.Profile`
  has fields `registration` and `current : Query Previous (fun _ =>
  Residual)`; `Dag.orderedSurplusActivationRecipe` constructs it as
  `{ registration, current }` with the compiler's query, so every read goes
  through the accumulated stage's `HasResidual Stage (ProblemInput P)`.
  `activitySpec` and `activityOrder` read via `profile.current.read` and
  `current.dependentMap`.  `execution` is `(CTAdapters.ct6
  activity).compose (CTAdapters.ct5 accounting)`, and the CT5 profile is
  `{ registration := profile.registration.accounting, current :=
  profile.current.preserve }` over `ActivityStage := Ledger.Extension
  Previous (CTAdapters.ct6 profile.activityCapability).Output`, i.e. the
  literal CT6 extension with the CT6 entry retained beneath it.  The
  incoming residual is the literal `above` arm of `v0`.  Ledger and Residual
  pass.  Separately: the registration's only inputs are `input.object` and
  the constant `3`, so
  `ScaleThresholdDichotomy.AboveResidual.threshold_lt_load` — the strict
  surplus fact that defines this branch — sits on the ledger and is unread
  by every row in 30–36.
- **Transport and terminals.** CT6 and CT5 own the scan, the ledger
  extensions, the work bound (`workCoefficient = workDegree = Fintype.card
  Unit`, `workBound` by `Nat.le_succ`), and the terminal; Graph supplies only
  the inert `Registration`, and the application supplies only `object` and
  `baselineDegree`.  The operation is nonbranching.  The export has the
  incoming conditional output edge `e18 : v0 → v14` (`output: above`) and the
  single outgoing sequence edge `e8 : v14 → v13`.  `v14` is exported with
  `kind: operation` and `components: []`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:named-surplus-exits` | def |  |  |
| `lem:sparse-slack-surplus` | lem |  |  |
| `lem:sparse-excess-port-extraction` | lem |  |  |
| `lem:sparse-port-activation` | lem |  |  |
| `def:active-surplus-demands` | def |  |  |
| `lem:surviving-active-family` | lem |  |  |

`def:named-surplus-exits` is also the survivor hypothesis of rows 32, 35 and
36; it is placed here because `[125]` is its first consuming node.
`lem:surviving-active-family` is also read at row 31, where `[129]` restates
`𝒜₀ = 𝒫_exc`; the manuscript's own dependency ledger files it at
`[125]`–`[128]`, so it is placed here.

**CT composition at this row.** `OrderedSurplusActivation.execution` is
`(CTAdapters.ct6 activity).compose (CTAdapters.ct5 accounting)`, so the code
order is **CT6 → CT5**, not the CT5 → CT6 of the reference table.  CT6 runs
the ordered exhaustion over `activityOrder` and decides whether any index
satisfies `Failure`, producing `FailureData` at the first hit; CT5 then runs
the resource comparison of `required` against `capacity` over CT6's exact
extension.  The composition buys the ordering: CT5's demand family is built
from `profile.current.preserve` over `ActivityStage`, so the surplus account
is taken on the object the scan just traversed rather than on an
independently queried one, which a bare CT5 could not express.  As
registered neither stage decides anything — CT6's `Failure` is refuted by
row 4's appended ledger entry, and CT5's `required` and `capacity` are the
same term.

### Row 31 — Baseline demand accounting `[129]`

- **Paper fact.** `[129]` carries two statements.
  `lem:surviving-active-family` (row 30): for a survivor, `𝒜₀ := 𝒫_exc` is a
  finite family of active surplus demands with `|𝒜₀| = σ(G)`.
  `def:baseline-spine-demand`: with `N = C(n,2)`, `m₀ = ⌈(3/2)n⌉` and
  `B₀(n) = log₂ C(N, m₀)`, a family `ℐ_spine` of declared target coordinates
  is a baseline spine demand with deficit `E_spine(n)` when `ℐ_spine` is
  independently target-testable and `|ℐ_spine| ≥ B₀(n) - E_spine(n)`.
  `def:spine-lower-bound-deficits` records the lower-bound deficit packages
  that feed the later surplus estimates.  The hypothesis used downstream is
  `E_spine(n) ≤ C_E n`.
- **What the Lean does.**
  `Graph.Strategy.SurplusAccounting.baselineDemand (object) (baselineDegree)
  : Core.Strategy.BaselineDemandAccounting.Registration Residual`, every
  field supplied: `budget := countingBudget` (`Nat`, `≤`, `+`,
  `ceiling := id`); `Site := fun residual => (object residual).Vertex`;
  `Witness := fun _ _ => Unit`; `family := { indices := vertices (object
  residual), fibres := fun _ => Core.Finite.Enumeration.singleton () }`;
  `Active := fun _ _ => True`; `Supports := fun _ _ _ => True`;
  `contribution := fun residual _ _ => baselineDegree residual`;
  `required := fun residual => baselineDegree residual * (object
  residual).vertexCount`; `capacity := fun residual => baselineDegree
  residual * (object residual).vertexCount`;
  `activeDecidable := fun _ _ => isTrue trivial`;
  `supportsDecidable := fun _ _ _ => isTrue trivial`.  `required` and
  `capacity` are the same term, so CT5's comparison is `3n ≤ 3n`.  The
  registration site passes `fun input => input.object` and
  `fun _ => erdosReceiverLoadProfile.baselineDegree`.  No theorem mentions
  this registration.
- **What it should do.** To state `def:baseline-spine-demand` the CT5 `Site`
  would have to be a declared target coordinate (not a vertex), `Active`
  would have to be independent target-testability of that coordinate,
  `capacity` would have to be `B₀(n) = log₂ C(C(n,2), ⌈3n/2⌉)` or a
  `Nat`/`ℚ` surrogate for it, and `required` would have to be `|ℐ_spine|`,
  so that the CT5 verdict is exactly `|ℐ_spine| ≥ B₀(n) - E_spine(n)` with
  `E_spine` an output of the stage.  `lem:surviving-active-family` would
  need `Active := fun residual site => site ∈ 𝒫_exc` and a theorem
  `(family residual).card = degreeSurplus (baselineDegree residual)`.
- **Gap.** `Active := True` makes the demand family all of `V(G)`, not
  `𝒫_exc`; `|𝒜₀| = σ(G)` is not stated at this node.  There is no declared
  target coordinate, no independent target-testability, no `B₀(n)`, no
  `E_spine(n)`, and no `O(n)` bound on a deficit; no binomial coefficient,
  logarithm, or `log₂ n` term occurs anywhere in
  `/home/guillem/structural_exhaustion/hypostructure/Hypostructure/Graph/Strategy/SurplusAccounting.lean`.
  `def:spine-lower-bound-deficits` has no counterpart.  What is proved is
  `3n ≤ 3n`.  **Facts therefore fails.**
- **Ledger and residual.** `BaselineDemandAccounting.Profile` has
  `registration` and `current`; `Dag.baselineDemandAccountingRecipe` builds
  `{ registration, current }` with the compiler's query.  `spec` reads each
  field through `profile.current.read previous`, and `family` is
  `profile.current.dependentMap fun _ residual =>
  profile.registration.family residual`.  `execution` is the single
  `CTAdapters.ct5 profile.capability`, whose output is appended over the
  literal row-30 stage as a `Ledger.Extension`.  Ledger and Residual pass.
- **Transport and terminals.** Core's CT5 owns the dependent enumeration,
  the resource comparison, the ledger entry, the work bound and the
  terminal.  The application supplies `object` and `baselineDegree` and
  nothing else.  The operation is nonbranching; the export has
  `e9 : v13 → v12` as its only outgoing edge, and `v13` carries
  `components: []`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:baseline-spine-demand` | def |  |  |
| `def:spine-lower-bound-deficits` | def |  |  |

`def:baseline-spine-demand` is read again at row 32 (as the `E_spine(n)`
term of the entropy sandwich) and at row 34 (as the `E_spine(n)` term of the
high-load alternative); `[129]` is its first consuming node.

**CT composition at this row.** The strategy composes a single **CT5**:
`BaselineDemandAccounting.execution accounting := CTAdapters.ct5 accounting`,
and `Profile.execution` is that same call on `profile.capability`.  CT5
enumerates the dependent family `family`, filters by `Active`, checks
`Supports` on each witness, sums `contribution` in `budget`, and decides
`required ≤ capacity`, appending the verdict and its terminal.  There is
nothing for a composition to buy here: this row is the degenerate case of
row 30's second half, run over the identical vertex scan, and its verdict is
`3n ≤ 3n`.

### Row 32 — Canonical pair-response `[130]`–`[134]`

- **Paper fact.** `[130]` splits `Π(𝒜₀) = C(𝒜₀,2)` into free and blocked
  pairs.  `def:sparse-pair-response` attaches to `π = {p,q}` the
  lexicographically first minimum-vertex connected `X_π ⊇ T(p) ∪ Γ(p) ∪ T(q)
  ∪ Γ(q)`, its boundary `∂X_π`, and the declared coordinate `r_π` of
  `ρ^ex_{∂X_π}(X_π)` whose label is `π`, whose support is `X_π`, and whose
  value is the exact target-response data of `p` and `q` inside `X_π`.
  `[131]` is `prop:sparse-entropy-sandwich`:
  `C(|𝒜₀|,2) ≤ E_spine(n) + ((1/2)σ(G) + 1) log₂ n`, and its blocked
  refinement `prop:sparse-entropy-sandwich-with-blockers`:
  `|Π_free| ≤ E_spine(n) + ((1/2)σ(G) + 1) log₂ n`.  Their inputs are
  `lem:exact-cubic-baseline-budget` (`B₀(n) = (3/2) n log₂ n + O(n)`),
  `lem:incremental-skeleton-room` (`log₂ C(N,m) - log₂ C(N,m₀) ≤ s log₂ n`
  for `m = m₀ + s ≤ 2n-2`), `lem:mixed-sparse-spine-dependence` (the union
  `ℐ_spine ∪ {r_π}` is independently target-testable unless an exit or a
  blocker occurs), `prop:sparse-pair-independence-dichotomy` and
  `cor:sparse-pair-entropy-saturation`.  `[132]` is
  `lem:sparse-pair-dependence-exit`: if `{r_π : π ∈ Π}` does not survive
  every admissible rank quotient, then either a sparse surplus exit occurs
  or some `π` has a blocker of type (d) or (e).  `def:surplus-blockers`
  fixes the closed clause list: "(a) a vertex or edge-incidence contained in
  both declared demand supports; (b) a common vertex or common
  edge-incidence of the two canonical return paths `R_p` and `R_q`; (c) a
  common shoulder endpoint or shared cubic buffer vertex among `{a_p, b_p,
  x(p), a_q, b_q, x(q)}`; (d) a boundary-degree-profile coordinate …;
  (e) a target-response coordinate witnessing a target-defective quotient,
  target-complete compression, or delocalization event; (f) an arithmetic
  chord-set obstruction … the concrete set `𝒮` of added shoulder chords",
  with the explicit proviso "A pair is not declared blocked merely because
  the proof has not found a closure".
  `def:canonical-sparse-blocker-order` totally orders the blockers,
  `def:canonical-blocker-ledger` (`[134]`) sets `Φ_can(π) = B_π` to the least
  one and defines `Π_blk`, `Π_free`, and
  `lem:canonical-blocker-ledger-no-overcount` proves
  `|Π_blk| = |𝔉_can| = Σ_{B ∈ ℬ_can} μ(B)`.
- **What the Lean does.**
  `Graph.Strategy.SurplusAccounting.CanonicalAccounting.pairResponse
  (object) (baselineDegree) :
  Core.Strategy.CanonicalPairResponseAccounting.Registration Residual`.
  Supplied fields: `Pair residual := { pair : PortIndex × PortIndex //
  pair.1 < pair.2 }`, over `PortIndex := Fin (activePorts residual).card`
  and `ActivePort := Σ vertex, Fin ((object residual).degree vertex -
  baselineDegree residual)`; `pairSchedule := (completePairs …).toEnumeration`;
  `IntendedPair := fun _ _ => True`, and `pairSchedule_exact`'s proof is
  `⟨fun _ => trivial, fun _ => (completePairs …).complete pair⟩`, i.e. it
  proves membership against a predicate that is `True`.
  `Dependent := dependent object baselineDegree`, where
  `dependent residual pair := (object residual).graph.Adj (leftVertex …
  pair) (rightVertex … pair)` and `leftVertex`/`rightVertex` are the host
  vertices `(activePorts.get pair.1.1).1` and `(activePorts.get pair.1.2).1`.
  `AdmittedDependent := Dependent` with `dependent_exact := fun _ _ => rfl`.
  `BlockerKind residual := (object residual).Vertex × (object
  residual).Vertex`; `CanonicalBlocker pair kind := pairRole pair =
  Role.blocked kind`, where `pairRole := if Adj left right then Role.blocked
  (left, right) else Role.freeAnchor`;
  `blocker_exact := dependent_iff_canonicalBlocker`, whose proof re-derives
  the `if` from itself (`simp [adjacent, Role.blocked]` one way, `rw [free]`
  and `simp` the other); `role_freeAnchor_exact := pairRole_freeAnchor_exact`,
  proved by `by_cases adjacent` and `dif_pos`/`dif_neg`;
  `role_blocked_exact := fun _ _ _ => rfl`.  All three "exactness"
  obligations are re-packagings of the definition of `pairRole`.
  `pairCharge := fun _ _ => unitCharge` (`= Fintype.card Unit = 1`),
  `pairCapacity := fun residual => (pairSchedule residual).card`, and
  `roleCapacity := fun residual _ => (pairSchedule residual).card`.
- **What it should do.** `BlockerKind` would have to be an inductive with
  the six constructors of `def:surplus-blockers`, each carrying its concrete
  witness (a vertex or edge-incidence in both declared supports; a shared
  vertex or incidence of `R_p` and `R_q`; a shared shoulder or buffer
  vertex; a boundary-degree-profile coordinate; a target-response
  coordinate; a chord set `𝒮`).  `Dependent` would be failure of `{r_π}` to
  survive every admissible rank quotient of `ρ^ex_{∂X_Π}(X_Π)`, so
  `blocker_exact` would be the content of `lem:sparse-pair-dependence-exit`
  rather than an identity.  `CanonicalBlocker` would be minimality in
  `def:canonical-sparse-blocker-order`, and a separate theorem of type
  `(pairSchedule.values.filter Dependent).length = Σ_B μ(B)` would state
  `lem:canonical-blocker-ledger-no-overcount`.  `roleCapacity` would carry
  `E_spine(n) + ((1/2)σ + 1) log₂ n` on the free-anchor role, so that CT9's
  verdict is `[131]`.
- **Gap.** `Dependent` is graph adjacency of two host vertices.  None of the
  six blocker types occurs; there is no `X_π`, no `∂X_π`, no declared
  coordinate `r_π`, no return path, no shoulder, no chord set, no
  boundary-degree profile, and no rank quotient.  Worse, this `Dependent` is
  uninhabited on the branch: `ActivePort`'s second component is
  `Fin (degree vertex - baselineDegree)`, so both host vertices have degree
  above the baseline `3`; `def:surplus-ports`' own `H = V_{≥4}` independence
  (row 4's appended slack-incompatibility entry) makes two such vertices
  nonadjacent, and two ports at one vertex give `left = right`, which
  `SimpleGraph.Adj` refuses.  Hence `Π_blk = ∅` and `Π_free = Π(𝒜₀)` by
  construction, and the `[130]` split is decided before it is taken.
  `pairCharge = 1` against `pairCapacity = |pairSchedule|` makes CT15's
  comparison `C(σ,2) ≤ C(σ,2)`, and `roleCapacity` is the same constant for
  every role, so CT9's comparison is equally trivial; `[131]`'s entropy
  bound is absent, and with it `lem:exact-cubic-baseline-budget`,
  `lem:incremental-skeleton-room` and `lem:mixed-sparse-spine-dependence`.
  The one thing that does match is the pair *schedule*: `completePairs` is
  the `<`-subtype of `completePortIndices.product completePortIndices`, so
  its cardinality is `C(σ(G), 2) = |Π(𝒜₀)|`.  **Facts therefore fails.**
- **Ledger and residual.**
  `Dag.canonicalPairResponseAccountingRecipe` builds
  `CanonicalPairResponseAccounting.Profile` as `{ registration }`, so
  `current` takes its default `Query.residual` and every read is of the
  accumulated stage's stable residual.  `pairQuery` and `completeRoleQuery`
  are `residualQuery.dependentMap`s.
  `AfterDependence := Ledger.Extension Previous dependenceExecution.Output`;
  `currentAfterDependence`, `inheritedPairs` and `inheritedRoles` are
  `Query.preserve`, so CT9 receives exactly the schedules CT15 saw, indexed
  by CT15's literal extension.  `execution := dependenceExecution.compose
  roleExecution`, and `dependenceOutput`/`roleOutput` project the two
  payloads out of the single retained composed entry, the second at
  `Ledger.extend stage.previous output.fst`.  Ledger and Residual pass.
- **Transport and terminals.** CT15 owns the dependence decision, CT9 the
  role partition; both terminals are read back through
  `dependenceTerminal` / `roleTerminal` (`Query.map` on the retained
  output), not chosen by the application.  Graph supplies only the
  registration.  The operation is nonbranching; the export has
  `e10 : v12 → v11` as its only outgoing edge and `components: []` on `v12`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:sparse-pair-response` | def |  |  |
| `lem:sparse-pair-dependence-exit` | lem |  |  |
| `prop:sparse-pair-independence-dichotomy` | pro |  |  |
| `cor:sparse-pair-entropy-saturation` | cor |  |  |
| `lem:exact-cubic-baseline-budget` | lem |  |  |
| `lem:incremental-skeleton-room` | lem |  |  |
| `lem:mixed-sparse-spine-dependence` | lem |  |  |
| `prop:sparse-entropy-sandwich` | pro |  |  |
| `prop:sparse-entropy-sandwich-with-blockers` | pro |  |  |
| `def:surplus-blockers` | def |  |  |
| `def:canonical-sparse-blocker-order` | def |  |  |
| `def:canonical-blocker-ledger` | def |  |  |
| `lem:canonical-blocker-ledger-no-overcount` | lem |  |  |

`def:surplus-blockers` is read again at rows 33 (via `supp(B_π)` in the
token rule) and 34 (via `type(B_π)` in the role triple);
`prop:sparse-entropy-sandwich-with-blockers` is read again at rows 33 and 34
as the `|Π_free|` term.  `[130]`–`[132]` are their first consuming nodes.

**CT composition at this row.**
`CanonicalPairResponseAccounting.Profile.execution` is
`dependenceExecution.compose roleExecution`, i.e. **CT15 → CT9** — the
reverse of the reference table's CT9 → CT15.  CT15 decides
`TargetDependent := Dependent` coordinate by coordinate over `pairQuery` and
charges `pairCharge` against `pairCapacity`, appending its verdict and
terminal.  CT9 then partitions the same coordinates by `label := roleOf` into
the role alphabet `Role (BlockerKind residual)` and compares each fibre
against `roleCapacity`.  The composition buys the fact that the role
partition runs on CT15's own decided coordinates: `inheritedPairs` and
`inheritedRoles` are `Query.preserve` of the CT15-side queries rather than
fresh residual reads, and `roleSpec` is indexed by `AfterDependence`.  A bare
CT9 has no dependence decision of its own and would have to be handed the
free/blocked split as data.  As registered both comparisons are tautologies
and the split is constantly `freeAnchor`.

### Row 33 — Capacity-token accounting `[134]`–`[136]`

- **Paper fact.** `def:primitive-sparse-blocker-carrier` builds
  `𝔘_sp(G) = V(G) ⊔ I_E(G) ⊔ 𝒫_exc` with `I_E(G) = {(e,v) : e ∈ E(G), v ∈ e}`
  and a carrier map `κ(B)` by cases on the six blocker types;
  `lem:primitive-carrier-supply` proves `|𝔘_sp(G)| = n + 2m + σ(G) ≤ 6n`.
  `def:capacity-token-ledger` (`[134]`–`[136]`) builds
  `𝔗_cap = 𝔗_prim ⊔ 𝔗_R ⊔ 𝔗_W`, `𝔗_prim := 𝔘_sp(G)`,
  `𝔗_R := {(v,j) : v ∈ R, 1 ≤ j ≤ d_G(v)-3}` (so `|𝔗_R| = σ_R`), and `𝔗_W`
  the window–remainder edge tokens together with both endpoint tokens of
  each cross-window edge; and it defines `Θ_cap(π)` by four cases — least
  window–remainder edge in `supp(B_π)`, else least cross-window edge and the
  least of its two endpoint tokens, else the least high-degree remainder
  vertex `v` with rank `j(π) = 1 + (rk_v(π) mod (d_G(v)-3))`, else `κ(B_π)`
  — with token load `ℓ_cap(t) := |Θ_cap^{-1}(t)|`.
  `lem:capacity-token-supply` gives `|𝔗_cap| = |𝔘_sp(G)| + σ_R + e(R,W) +
  2e_×(W) = |𝔘_sp(G)| + 15p₁₃ + σ(G) ≤ 8n + σ(G)`.
  `lem:token-ledger-no-overcount` gives
  `|Π_blk| = Σ_{t ∈ 𝔗_cap} ℓ_cap(t)`, hence `|Π_blk| ≤ M₀(8n + σ(G))` when
  every load is at most `M₀`.  `def:same-token-patterns` defines the
  token-fibre graph `H_t` with `V(H_t) = 𝒜₀` and
  `E(H_t) = Π_t = Θ_cap^{-1}(t)`.  `rem:surplus-pair-sharp-frontier` records
  that this bookkeeping has no disjointness loss: free pairs are charged by
  the sandwich, blocked pairs get one canonical blocker and one token, and
  the fibres partition `Π_blk`.
- **What the Lean does.**
  `Graph.Strategy.SurplusAccounting.CanonicalAccounting.capacityToken
  (object) (baselineDegree) :
  Core.Strategy.CanonicalCapacityTokenAccounting.Registration Residual`.
  Supplied fields: `Demand := Pair` (all `C(σ,2)` index pairs of row 32,
  free ones included); `Token := PortIndex` — the active-port index type, of
  size `σ(G)`; `demands := pairSchedule`; `tokens := fun residual =>
  (completePortIndices residual).toEnumeration`;
  `Eligible := fun residual demand token => token = selectedToken residual
  demand` with `selectedToken residual pair := pair.1.1`, the pair's smaller
  port index; `demandWeight := fun _ _ => unitCharge`;
  `tokenCapacity := fun residual token => (object residual).degree
  (portVertex residual token)`; `required := fun residual => (pairSchedule
  residual).card`; `roleOf := pairRole`; `Label := Option Token × Role`;
  `labelOf := fun _ token role => (token, role)`;
  `labelCapacity (some token, _) := (object residual).degree (portVertex
  residual token)` and `labelCapacity (none, _) := (pairSchedule
  residual).card`; `aggregateLabel := Role`;
  `memberAggregateLabel := fun _ label => label.2`.  No theorem constrains
  this registration.  Since `Eligible` names exactly one token per demand,
  CT4's search has a unique candidate; CT9's label is
  `labelOf (assignedPayer? demand) (roleOf demand)`, and CT14 compares the
  fibre count of each label against `labelCapacity`, i.e. for each active
  port `t` the number of pairs whose smaller index is `t` against
  `d_G(v_t)`.
- **What it should do.** `Token` would have to be a three-summand type
  `𝔘_sp(G) ⊕ 𝔗_R ⊕ 𝔗_W` — carrying `I_E(G)` and the window/remainder split —
  with `tokens` an enumeration of it and a theorem
  `(tokens residual).card ≤ 8 * vertexCount + degreeSurplus 3`.  `Eligible`
  would have to be the graph of `Θ_cap`, defined only on blocked demands and
  by the four-case rule (including the rank `j(π)`), so that CT4's generated
  assignment *is* `Θ_cap` and CT9's fibre count *is* `ℓ_cap(t)`.
  `tokenCapacity` would be `M₀`, not `d_G(v)`, and `required` would be
  `|Π_blk|`, not `|Π(𝒜₀)|`.  `lem:token-ledger-no-overcount` would be a
  theorem of type `(demands.values.filter Dependent).length = Σ_t
  (partition.count t)`, and `def:same-token-patterns` would need `Token` to
  index a graph on `𝒜₀` rather than a bare label.
- **Gap.** The token universe is the active-port index set, not `𝔗_cap`:
  there is no `𝔘_sp`, no `I_E(G)`, no remainder/window split, no `p₁₃`, and
  no rank arithmetic.  `Eligible` is "pay at your own left endpoint",
  defined for every demand, so the assignment is not `Θ_cap` and the fibre
  counts are not `ℓ_cap`.  `tokenCapacity` is a raw graph degree, so the
  CT14 verdict compares `σ - 1 - t` against `d_G(v_t)` — an inequality with
  no counterpart in the manuscript.  `required = C(σ,2)` counts all pairs,
  so CT4's feasibility test is about `|Π(𝒜₀)|` and not `|Π_blk|`, which is
  empty here anyway by row 32's gap.  Neither `|𝔘_sp| ≤ 6n` nor
  `|𝔗_cap| ≤ 8n + σ(G)` nor the partition identity is stated, and
  `rem:surplus-pair-sharp-frontier`'s no-loss claim has nothing to range
  over.  **Facts therefore fails.**
- **Ledger and residual.**
  `Dag.canonicalCapacityTokenAccountingRecipe` builds the profile as
  `{ registration }`, so `current` is `Query.residual` over the accumulated
  stage.  `demandQuery` and `tokenQuery` are `residualQuery.dependentMap`s;
  `AfterAssignment := Ledger.Extension Previous assignmentExecution.Output`
  and `assignmentResult := Query.latest`; `ct9Items`, `ct9Labels` and
  `fibreSpec.label` all read `assignmentResult.read stage` and its
  `result.stage.previous`, and `fibreSpec.label` calls
  `assignedPayerQuery.read stage demand`, so the fibre label is CT4's
  *generated* payer, not a supplied assignment.  `partitionQuery` and
  `aggregateMembers` likewise read CT9's own outcome and label schedule.
  `execution := assignmentExecution.compose (fibreExecution.compose
  aggregateExecution)`, with all three payloads projected from the one
  composed entry.  The predecessor is the literal row-32 stage.  Ledger and
  Residual pass.
- **Transport and terminals.** CT4 owns the assignment and its four
  terminals (`missingPayer`, `overloadedFibre`, `c4`, `capacity`), CT9 the
  fibre partition and its `overloaded`/`bounded` terminals, CT14 the
  labelled aggregate.  No EG code selects a token, an assignment, a
  partition, a total, or a terminal.  The operation is nonbranching; the
  export has `e11 : v11 → v10` as its only outgoing edge, `components: []`
  on `v11`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:primitive-sparse-blocker-carrier` | def |  |  |
| `lem:primitive-carrier-supply` | lem |  |  |
| `def:capacity-token-ledger` | def |  |  |
| `lem:capacity-token-supply` | lem |  |  |
| `lem:token-ledger-no-overcount` | lem |  |  |
| `def:same-token-patterns` | def |  |  |
| `rem:surplus-pair-sharp-frontier` | rem |  |  |

`lem:capacity-token-supply` is read again at row 34 (as the denominator
`8n + σ(G)` of the high-load bound); `lem:token-ledger-no-overcount` at rows
34 and 36 (as `|Π_blk| ≤ M₀|𝔗_cap|`); `def:same-token-patterns` at row 34
(as the fibre graph the roles partition).  `[136]` is their first consuming
node.  Node `[135]`'s window-join labels
(`def:window-remainder-surplus-split`, `lem:exact-window-join-identity`,
`lem:surplus-aware-window-stub`, `cor:global-window-join-pressure`) belong to
the manuscript's window/remainder block and are audited outside this range;
nothing in this row's Lean implements them either.

**CT composition at this row.**
`CanonicalCapacityTokenAccounting.Profile.execution` is
`assignmentExecution.compose (fibreExecution.compose aggregateExecution)`,
so the code order is **CT4 → CT9 → CT14**, not the reference table's
CT9 → CT4 → CT14.  CT4 scans `demandQuery` against `tokenQuery` and
generates the first-eligible demand → token assignment, deciding
`missingPayer` / `overloadedFibre` / `c4` / `capacity` against
`tokenCapacity` and `required`.  CT9 then fibres the same demands by
`labelOf (assignedPayer? demand) (roleOf demand)` and compares each fibre
against `labelCapacity`.  CT14 aggregates those fibre counts by
`memberAggregateLabel`.  The composition is what makes the fibre label
depend on the *generated* assignment: `fibreSpec.label` reads
`assignedPayerQuery`, which projects CT4's own outcome, so a bare CT9 would
have to be handed the token map as supplied data and the ledger would carry
an assignment nobody derived.

### Row 34 — Coupled homogeneous fibre pressure `[137]`–`[143]`

- **Paper fact.** `[137]` is the coupled single-graph high-load test.
  `lem:capacity-token-high-load` states
  `C(s,2) ≤ E_spine(n) + ((1/2)σ(G) + 1) log₂ n + L_max |𝔗_cap|` with
  `L_max := max_t ℓ_cap(t)`, hence
  `L_max ≥ max{0, (1/4)σ(G)² - C_E n - ((1/2)σ+1)log₂ n} / (8n + σ(G))` for
  the full active family.  `cor:forced-homogeneous-same-token-scale`,
  `cor:coupled-single-graph-overload-budget`,
  `cor:numerical-single-graph-budget` and
  `prop:single-graph-sparse-pressure-routing` make the test *coupled*: all
  three token classes are evaluated at the same `n, p₁₃, σ_W, σ_R`; if
  `D_all = 0` the branch routes to `[138]`, otherwise
  `thm:tokenized-surplus-accounting-closure` — "Suppose also that the
  capacity-token ledger satisfies `ℓ_cap(t) ≤ M₀` … Then `σ(G) = O(√n)`" —
  splits the forced load into the window-incidence, remainder-surplus and
  primitive-carrier classes and routes to `[140]`, `[142]` or `[143]`.
  `def:same-token-blocker-roles` defines `ρ_t(π) = (type(B_π), class(t),
  sub(t))` with `type ∈ {a,…,f}`, `class ∈ {W,R,P}`,
  `sub ∈ {RW,WW,R,V,I,P}`, bounds the alphabet by
  `|𝔕_st| ≤ 6(2+1+3) = 36 =: Q_st`, and gives the fibre partition
  `ℓ_cap(t) = Σ_{r ∈ 𝔕_st} ℓ(t,r)`.
  `lem:exact-surplus-pair-charge-partition`,
  `thm:sharp-classwise-homogeneous-token-budget`,
  `cor:quantified-homogeneous-class-overload` and
  `thm:sharp-surplus-overload-audit` supply the exact charge partition, the
  classwise budget and the six-subtype load audit behind that split, and
  `cor:spine-lower-bound-surplus-estimates` converts the `[138]`
  lower-bound packages into the surplus estimate on the near-cubic route.
- **What the Lean does.**
  `Graph.Strategy.SurplusAccounting.CanonicalAccounting.fibrePressure
  (object) (baselineDegree) :
  Core.Strategy.CoupledHomogeneousFibrePressure.Registration Residual`.
  Supplied fields: `Item := Pair`, `Token := PortIndex`,
  `Role := Sum ((object residual).Vertex × (object residual).Vertex) Unit`,
  `Label := Option Token × Role`, `items := pairSchedule`,
  `labelOf := itemLabel := fun residual pair => (some (selectedToken residual
  pair), pairRole residual pair)`, `fibreCapacity := labelCapacity`.
  CT13 layer: `Payer := PortIndex`, `Obstruction := Role`,
  `Resource := PortIndex`, `payers := (completePortIndices …).toEnumeration`,
  `tierTwo := fun residual _ => (completePortIndices …).toEnumeration`,
  `Eligible := fun residual payer => baselineDegree residual < (object
  residual).degree (portVertex residual payer)`,
  `obstructionCost := fun residual _ => (pairSchedule residual).card`,
  `payerResource := fun _ payer => payer`, `charge := tokenCapacity`,
  `demand := fun residual => (pairSchedule residual).card`, and
  `obstructions := obstructionSchedule`, whose `fallbackDefault` is
  `Role.freeAnchor` and whose `remaining` is `completeBlockerKinds.values.map
  Role.blocked` (every ordered vertex pair).  CT14 layer:
  `Member := Label`, `AggregateLabel := Role`,
  `members := (completeLabels …).toEnumeration`,
  `memberLowerMass := labelCapacity`,
  `memberCapacity := fun residual label => some (labelCapacity residual
  label)`, `memberLabel := fun _ label => some label.2`.  `memberLowerMass`
  and `memberCapacity` are the same function, so the aggregate comparison
  holds with equality on every label.  `Eligible` holds for every payer,
  because `ActivePort`'s second component is `Fin (degree vertex -
  baselineDegree)` and a port index can only name a vertex with positive
  surplus — the file's own `baselineDegree_lt_degree_of_mem_pairSupport`
  derives exactly this from `(portAt … index).2.isLt` and `omega`.  No
  theorem constrains this registration.
- **What it should do.** `Token` would be `𝔗_cap` and `labelOf` would be
  `(Θ_cap π, ρ_t(π))` with `Role := Graph.SameTokenBlockerRoles.Role`, so
  that CT9's fibres are the `Π_{t,r}` and `memberLowerMass` is `ℓ(t,r)`.
  `memberCapacity` would be a bound independent of the fibre — `M₀`, or the
  right-hand side of `lem:capacity-token-high-load` — so that CT14's verdict
  is the high-load alternative rather than an identity.  `demand` would be
  `C(s,2)` and `obstructionCost` would carry
  `E_spine(n) + ((1/2)σ + 1) log₂ n`, so that the CT13/CT14 reconciliation
  computes `L_max |𝔗_cap|` and decides `D_all > 0`.  Three distinct
  `Obstruction` values `W`, `R`, `P` evaluated at shared `n, p₁₃, σ_W, σ_R`
  would make the test coupled.
- **Gap.** `memberLowerMass = memberCapacity`, so the stage's aggregate
  comparison is an identity and decides nothing; there is no `D_all`, no
  `L_max`, no `|𝔗_cap|`, no `E_spine(n)`, no `log₂ n`, and no coupling of
  three classes at shared parameters.  `Role` is `Sum (Vertex × Vertex)
  Unit` — one blocked role per ordered vertex pair plus a free anchor — not
  `𝔕_st`; the role map `ρ_t` and the fibres `Π_{t,r}` do not exist.  The
  manuscript's alphabet *is* declared, in
  `/home/guillem/structural_exhaustion/hypostructure/Hypostructure/Graph/SameTokenBlockerRoles.lean`,
  as `Role := { blocker : BlockerKind, token : TokenSubtype }` with
  `BlockerKind` a six-constructor inductive
  (`sharedDeclaredSupport`, `sharedReturnSupport`, `sharedLocalBuffer`,
  `boundaryProfile`, `targetResponse`, `arithmeticChordSet`), `TokenSubtype`
  a six-constructor inductive (`boundaryWindow`, `crossWindow`,
  `remainderSurplus`, `primitiveVertex`, `primitiveIncidence`,
  `primitivePort`), `TokenClass` a three-constructor inductive, and
  `tokenClass : TokenSubtype → TokenClass` sending
  `boundaryWindow, crossWindow ↦ windowIncidence`,
  `remainderSurplus ↦ remainderSurplus`,
  `primitiveVertex, primitiveIncidence, primitivePort ↦ primitiveCarrier`;
  `card_role : Fintype.card Role = Fintype.card BlockerKind * Fintype.card
  TokenSubtype` and `card_tokenSubtype_eq_sum_classFibres` give the
  manuscript's `6 · (2+1+3)`.  That alphabet is never used as a role: its
  only consumer in code is `sameTokenRoleBound := Fintype.card
  Graph.SameTokenBlockerRoles.Role` inside `homogeneousCapCharge`, i.e. as a
  numeric capacity constant in row 36.  `Eligible` is true for every payer,
  so the CT13 tier-one selection is unconstrained.
  `lem:exact-surplus-pair-charge-partition`,
  `thm:sharp-classwise-homogeneous-token-budget`,
  `cor:quantified-homogeneous-class-overload`,
  `thm:sharp-surplus-overload-audit` and
  `cor:spine-lower-bound-surplus-estimates` have no counterpart anywhere in
  the tree.  **Facts therefore fails.**
- **Ledger and residual.**
  `Dag.coupledHomogeneousFibrePressureRecipe` builds
  `{ registration, current }` with the compiler's query.
  `execution := overloadExecution.compose (reconciliationExecution.compose
  pressureExecution)`; each stage is indexed by the previous literal
  `Ledger.Extension` and the three payloads are projected from the single
  composed entry, with `composed_eq` proving the projection is the actual
  run.  The predecessor is the literal row-33 stage.  Ledger and Residual
  pass.
- **Transport and terminals.** CT9 owns the fibre partition, CT13 the payer
  and fallback selection and the reconciliation, CT14 the aggregate
  comparison and its terminal.  Graph supplies the registration and the
  `CT13.ObstructionSchedule` value; the application supplies `object` and
  `baselineDegree`.  The operation is nonbranching; the export has
  `e12 : v10 → v9` as its only outgoing edge, `components: []` on `v10`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:capacity-token-high-load` | lem |  |  |
| `cor:forced-homogeneous-same-token-scale` | cor |  |  |
| `cor:coupled-single-graph-overload-budget` | cor |  |  |
| `cor:numerical-single-graph-budget` | cor |  |  |
| `prop:single-graph-sparse-pressure-routing` | pro |  |  |
| `thm:tokenized-surplus-accounting-closure` | the |  |  |
| `def:same-token-blocker-roles` | def | `SameTokenBlockerRoles.Role`<br>`SameTokenBlockerRoles.card_role`<br>`SameTokenBlockerRoles.card_tokenSubtype_eq_sum_classFibres` | CT9→CT14→CT10→CT6→CT3→CT6→CT1→CT5→CT14 (row 36) |
| `lem:exact-surplus-pair-charge-partition` | lem |  |  |
| `thm:sharp-classwise-homogeneous-token-budget` | the |  |  |
| `cor:quantified-homogeneous-class-overload` | cor |  |  |
| `thm:sharp-surplus-overload-audit` | the |  |  |
| `cor:spine-lower-bound-surplus-estimates` | cor |  |  |

`def:same-token-blocker-roles` is filed here because `[139]`–`[143]` is its
first consuming node span, but the only declaration that reaches the run is
`Role`, and it reaches it at row 36 as `Fintype.card Role` inside
`homogeneousTokenCap`, not as a role at this row; the column-4 chain is
therefore row 36's.  `thm:tokenized-surplus-accounting-closure` is read
again at row 36, where `cor:homogeneous-same-token-caps-close` invokes it.
`cor:spine-lower-bound-surplus-estimates` and
`thm:sharp-surplus-overload-audit` are filed at the closest row: the former
belongs to terminal `[138]`, reached from `[137]`, and the latter to the
subtype audit that `[137]`–`[143]` performs; neither has a node of its own
in rows 30–36.

**CT composition at this row.**
`CoupledHomogeneousFibrePressure.Profile.execution` is
`overloadExecution.compose (reconciliationExecution.compose
pressureExecution)`, i.e. **CT9 → CT13 → CT14**, matching the reference
table.  CT9 fibres `items` by `labelOf` and compares each fibre against
`fibreCapacity`, deciding `overloaded` or `bounded`.  CT13 then works over
that extension: it walks `obstructions` (an `ObstructionSchedule` with a
`fallbackDefault` and a `remaining` list), selects an eligible `Payer` per
obstruction from `payers`, falls through to `tierTwo` when tier one is
exhausted, and reconciles `charge` against `obstructionCost` and `demand`
by `payerResource` up to `resourceDecidableEq`.  CT14 finally aggregates
`memberLowerMass` against `memberCapacity` over `members`, grouped by
`memberLabel`.  The composition buys the reconciliation step between a fibre
partition and an aggregate verdict — CT13 is the only stage that can spend a
payer against an obstruction, and it needs CT9's partition to know which
fibres are overloaded.  As registered there is nothing to reconcile:
`Eligible` admits every payer and `memberLowerMass` and `memberCapacity` are
the same function.

### Row 35 — Finite bottleneck classification `[140]`–`[143]`

- **Paper fact.** `[140]`, `[142]` and `[143]` are three separate geometric
  audits, one per token class — window-incidence, remainder-surplus,
  primitive-carrier — each asking whether the class supports a
  role-homogeneous same-token matching or star.
  `lem:same-token-matching-star` supplies the combinatorics:
  `e(H) ≤ ν(H)(2Δ(H) - 1)`, hence "if `K ≥ 1` and `H` contains neither a
  matching of size `K` nor a star of size `K`, then `e(H) ≤ (K-1)(2K-3)`".
  `lem:same-token-homogeneous-extraction` refines a same-token `K`-pattern
  to a role-homogeneous one of size `⌈K/Q_st⌉`.
  `def:homogeneous-token-charge` fixes `ψ(x)` and the cap charge
  `Cap_hom(L) := Q_st(L-1)(2L-3)`, "the uniform token load allowed by
  charging each of the at most `Q_st` role fibres separately when no
  role-homogeneous same-token `L`-matching or `L`-star occurs at that
  token"; `cor:quantitative-homogeneous-overload` and
  `cor:forced-same-token-scale` are its quantitative forms.
  `def:same-token-routing-germs` defines the routing support `Z(π;t,r)`, the
  connector germs from the primitive carrier of `t` to `T(p)` or `T(q)`, the
  *first separator* (the last vertex of the maximal common initial segment
  before the germs leave through two distinct next incidences), the parallel
  case, and the finite routing-label alphabet of cardinality `Q_geom`.
- **What the Lean does.**
  `Graph.Strategy.SurplusAccounting.CanonicalAccounting.bottleneck (object)
  (baselineDegree) :
  Core.Strategy.FiniteBottleneckClassification.Registration Residual`.
  Supplied fields, in four groups.  Pattern/pressure:
  `PatternItem := Pair`, `CoarseCode := Role`,
  `patternItems := pairSchedule`, `completeCoarseCodes := completeRoles`,
  `coarseCodeOf := pairRole`, `PressureLabel := Role`,
  `pressureCapacity := fun residual _ => some (pairSchedule residual).card`
  (the same number for every code), `pressureLabel := fun _ role => some
  role`.  Classification: `Datum := Pair`, `SemanticTag := Role`,
  `Promotion := Role`, `data := pairSchedule`, `classOf := pairRole`,
  `Direct := fun _ role => role = Role.freeAnchor`,
  `promote := fun _ role => role`.  Separator:
  `SeparatorIndex := PortIndex`, `SeparatorData := fun _ _ => Unit`,
  `separatorOrder := (completePortIndices residual).toEnumeration`,
  `SeparatorFailure := fun residual token => baselineDegree residual <
  (object residual).degree (portVertex residual token)`,
  `separatorFailureData := fun _ _ _ => ()`,
  `separatorContribution := fun residual token => (object residual).degree
  (portVertex residual token) - baselineDegree residual`.  The only cap
  arithmetic in the tree is
  `homogeneousCapCharge (patternBound : Nat) : Nat := sameTokenRoleBound *
  ((patternBound - 1) * (2 * patternBound - 3))` with
  `sameTokenRoleBound := Fintype.card Graph.SameTokenBlockerRoles.Role`, and
  `geometricPatternBound (baselineDegree : Nat) : Nat := baselineDegree + 1`;
  both are plain `Nat` computations with no hypotheses and no theorem
  attached, consumed only by row 36's `boundedCapacity`.  No theorem
  constrains this registration.
- **What it should do.** `CoarseCode` would be the token class `{W, R, P}`
  (or `Graph.SameTokenBlockerRoles.TokenClass`), so the CT9 partition is the
  three-way class split and the audits `[140]`, `[142]`, `[143]` are three
  distinct fibres.  `pressureCapacity` would be `Cap_hom(L_geom)` per class,
  not `|pairSchedule|` uniformly.  `SeparatorIndex` would range over pairs
  of routing germs in `Z(π;t,r)`, `SeparatorFailure` would say that two
  germs with the same routing label first separate at a vertex `z`, and
  `SeparatorData` would carry `z`, the common prefix and the two tails, so
  that `separatorContribution` bounds the germ count by `Q_geom` and a
  firing index yields `4 ≤ d_G(z)` and a decorated fan envelope.  Separate
  theorems of type `e(H) ≤ ν(H) * (2 * Δ(H) - 1)` and
  `¬ HasMatching K H → ¬ HasStar K H → e(H) ≤ (K-1)*(2K-3)` would state
  `lem:same-token-matching-star`, and one of type
  `HasMatching K H → ∃ r, HasMatching (K / Q_st) (H.roleFibre r)` would
  state `lem:same-token-homogeneous-extraction`.
- **Gap.** There is one class, not three: `CoarseCode = Role = Sum (Vertex ×
  Vertex) Unit`, and `Direct` is the Boolean free/blocked test of row 32,
  which is constantly `freeAnchor` on this branch.  `pressureCapacity` is a
  single constant for every code, so the CT14 pressure verdict carries no
  class information.  `SeparatorFailure` holds for *every* index by the
  construction of `ActivePort` (the same fact the file proves for row 34's
  `Eligible`), so the CT6 ordered scan reports a failure at the first port
  and its `SeparatorData` is `Unit`: there is no germ, no common prefix, no
  first separator, no `Q_geom`, and no `4 ≤ d_G(z)`.  "Separator" here
  restates the port's own defining condition.  `lem:same-token-matching-star`
  and `lem:same-token-homogeneous-extraction` have no counterpart: no
  matching, star, matching number, or maximum degree is defined anywhere in
  `/home/guillem/structural_exhaustion/hypostructure/Hypostructure/Graph/Strategy/SurplusAccounting.lean`;
  `homogeneousCapCharge` computes `Cap_hom(L)` but asserts nothing, so the
  implication that would license it is missing.  **Facts therefore fails.**
- **Ledger and residual.**
  `FiniteBottleneckClassification.Profile.execution` is
  `collisionExecution.compose (pressureExecution.compose
  (classificationExecution.compose separatorExecution))`; the stages are
  built over `AfterCollision`, `AfterPressure`, `AfterClassification`, each
  a literal `Ledger.Extension`, and the four payloads are projected from the
  single composed output with `composed_eq : composed = profile.execution.run
  live.previous` proving the projection is the actual run.  The predecessor
  is the literal row-34 stage.  Ledger and Residual pass.
- **Transport and terminals.** CT9, CT14, CT10 and CT6 own the partition,
  the labelled pressure comparison, the classification and the ordered
  separator scan; each terminal is read back rather than chosen.  Graph
  supplies only the registration.  The operation is nonbranching; the export
  has `e13 : v9 → v8` as its only outgoing edge, `components: []` on `v9`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:same-token-matching-star` | lem |  |  |
| `lem:same-token-homogeneous-extraction` | lem |  |  |
| `def:homogeneous-token-charge` | def | `SurplusAccounting.homogeneousCapCharge` | CT9→CT14→CT10→CT6→CT3→CT6→CT1→CT5→CT14 (row 36) |
| `cor:quantitative-homogeneous-overload` | cor |  |  |
| `cor:forced-same-token-scale` | cor |  |  |
| `def:same-token-routing-germs` | def |  |  |

`def:homogeneous-token-charge` is filed here because the caps it defines are
what the three audits `[140]`, `[142]`, `[143]` produce, but the only
declaration that computes it, `homogeneousCapCharge`, is consumed at row 36
through `homogeneousTokenCap` in `boundedCapacity`; the column-4 chain is
therefore row 36's.  Only `Cap_hom(L)` is computed — the definition's `ψ(x)`
has no counterpart.  `cor:quantitative-homogeneous-overload` and
`cor:forced-same-token-scale` are filed at the closest row: they quantify the
same pattern caps and have no node of their own in the figure.

**CT composition at this row.**
`FiniteBottleneckClassification.Profile.execution` is
`collisionExecution.compose (pressureExecution.compose
(classificationExecution.compose separatorExecution))`, i.e.
**CT9 → CT14 → CT10 → CT6** — the reference table's CT9 → CT6 → CT10 → CT14
has the last three reversed.  CT9 partitions `patternItems` by
`coarseCodeOf` into `completeCoarseCodes`.  CT14 then compares, per coarse
code, the fibre mass against `pressureCapacity`, grouped by `pressureLabel`.
CT10 classifies each `Datum` by `classOf` into `SemanticTag`, splitting on
`Direct` and applying `promote` to the rest.  CT6 finally runs an ordered
scan over `separatorOrder`, stopping at the first `SeparatorFailure` and
emitting `separatorFailureData` with `separatorContribution` as its work.
The composition buys two orderings a single CT could not: the classification
runs *after* a pressure verdict, so `Direct` is decided on a fibre already
known to be within or over capacity, and the separator scan runs *after* the
classification, so a firing index is attributable to a class.  As registered
neither ordering carries information — one class, a uniform capacity, and a
`SeparatorFailure` that is true at every index.

### Row 36 — Homogeneous bottleneck `[144]`

- **Paper fact.** `[144]` is `thm:homogeneous-overload-geometric-closure`
  with `lem:same-token-bottleneck-routing`,
  `cor:homogeneous-same-token-caps-close` and
  `prop:nonnear-cubic-sharp-overload-routing`.
  `lem:same-token-bottleneck-routing`: if a role-homogeneous same-token
  matching or star in `H_{t,r}` has more than `Q_geom` edges, then "(a) a
  sparse surplus exit occurs; or (b) the support produces a decorated Type B
  handoff fan envelope, hence is routed to the Type B fan ledger".  With
  `L_geom := Q_geom + 1`, `thm:homogeneous-overload-geometric-closure`
  concludes that every role-homogeneous same-token `L_geom`-matching or
  `L_geom`-star in the window-incidence, remainder-surplus, or
  primitive-carrier classes realizes one of those two, and that on the
  subbranch where sparse exits are absent and all decorated Type B handoff
  data have been routed into the **Type B fan ledger**, the fixed caps
  `L_W = L_R = L_P = L_geom` hold, whence `σ(G) = O(√n)` and
  `m = (3/2)n + O(√n)`.  `cor:homogeneous-same-token-caps-close` is the
  implication from clauses (a),(b),(c) — no token in `𝔗_W` / `𝔗_R` /
  `𝔗_prim` supports a role-homogeneous same-token `L`-matching or `L`-star —
  to `σ(G) = O(√n)`, its proof forming `M₀ := max{Cap_hom(L_W),
  Cap_hom(L_R), Cap_hom(L_P)}`, using the role-fibre partition
  `ℓ_cap(t) = Σ_r ℓ(t,r) ≤ Q_st(L-1)(2L-3)`, and invoking
  `thm:tokenized-surplus-accounting-closure`;
  `cor:same-token-pattern-caps-close` is the same closure stated for pattern
  rather than role caps.  `prop:nonnear-cubic-sharp-overload-routing` is the
  exhaustive outcome: "(a) `G` satisfies the near-cubic spine estimate
  `σ(G) = O(√n)`; (b) a sparse surplus exit occurs; or (c) a
  role-homogeneous same-token bottleneck produces decorated Type B fan data
  and is routed to the Type B fan ledger."
- **What the Lean does.** The registered value is
  `Graph.Strategy.SurplusAccounting.homogeneousBottleneck
  (LengthOK := PowerOfTwoLength) (lengthDecidable := fun _ => inferInstance)`,
  which is `homogeneousBottleneckOfLowerBound` at
  `object := fun input => input.object`,
  `baselineDegree := fun input => (Graph.Strategy.minimumDegreeThresholdQuery
  …).read input`, `minimumDegree :=
  Graph.Strategy.minimumDegreeThresholdQuery_le_minDegree`, and
  `cycleToTarget := fun _ cycle => cycle`.  In that registration `Item`,
  `HomogeneityCode`, `CapacityLabel`, `Datum`, `LocalClass`, `Promotion`,
  `LocalIndex`, `AdmissibilityField`, `SupportSite`, `BoundedMember` and
  `BoundedLabel` are all `(object residual).Vertex`, and `items`, `data`,
  `localOrder`, `admissibilityOrder`, `supportFamily.indices`,
  `boundedMembers` are all `vertices (object residual)`.  Five stages are
  supplied so as to be uninhabited or trivial:
  `LocalFailure v := (object residual).degree v < baselineDegree residual`
  and `AdmissibilityFailure` identically, both discharged by
  `localFailureScheduled` / `admissibilityFailureScheduled` whose bodies are
  `have lower := (minimumDegree residual).trans (minDegree_le_degree v);
  omega`; `Representative := Unit` with
  `responseSystem := unitResponseSystem`,
  `ResponseCandidate := ResponseRow := Unit`,
  `ResponseAdmissible := ResponseStrictlySmaller := fun _ _ _ => True`, and
  `responseDefectScheduled := fun _ _ _ _ _ defect => (defect rfl).elim`;
  `supportRequired := fun _ => countingBudget.zero` with
  `SupportActive := True`; and `ExceptionalCandidate := fun _ => Empty` with
  `exceptionalImpossible := some ⟨fun _ impossible => nomatch impossible⟩`.
  `TargetCandidate := Graph.CycleCertificate (object residual) LengthOK`,
  `outcomeCandidates := (cycleCertificates …).map Sum.inl …`,
  `RealizesTarget := fun _ _ => True`,
  `targetOfRealization := fun residual certificate _ => cycleToTarget
  residual ⟨certificate⟩`.  The substantive stage is the final CT14:
  `boundedLowerMass := fun residual vertex => ((object residual).degree
  vertex - baselineDegree residual) * ((object residual).degreeSurplus
  (baselineDegree residual) - 1)` and
  `boundedCapacity := fun residual _vertex => some (homogeneousTokenCap
  (baselineDegree residual))`, where
  `homogeneousTokenCap k := 2 * homogeneousCapCharge (k + 1)`.  Three
  theorems have content.
  `homogeneousBottleneckOfLowerBound_boundedLoad` has type
  `(…).boundedLoad residual = (object residual).degreeSurplus
  (baselineDegree residual) * ((object residual).degreeSurplus
  (baselineDegree residual) - 1)`, proved by `sum_map_mul_right` and
  `sum_vertexSurplus`, the latter going through
  `DegreeSurplusLedger.total_derive` and `total_eq_edge_mass_sub_baseline`.
  `homogeneousBottleneckOfLowerBound_boundedCap` has type
  `(…).boundedCap residual = (object residual).vertexCount *
  homogeneousTokenCap (baselineDegree residual)`.
  `degreeSurplus_le_of_homogeneousCaps (target) (baseline cap : Nat)
  (capped : target.degreeSurplus baseline * (target.degreeSurplus baseline -
  1) ≤ target.vertexCount * cap) : target.degreeSurplus baseline ≤ 1 +
  Nat.sqrt (cap * target.vertexCount)`, proved by `Nat.le_sqrt` and `omega`;
  `homogeneousBottleneckOfLowerBound_degreeSurplus_le_of_bounded` rewrites
  the two identities into a supplied hypothesis `boundedLoad ≤ boundedCap`
  and applies it; `boundedRoute_degreeSurplus_le` takes a supplied equality
  `registered : profile.registration = homogeneousBottleneckOfLowerBound …`
  and a `witness : profile.RoutedResidual semantics previous .bounded`, and
  its body is `rw [registered]` on `Profile.bounded_load_le_cap`.
  `globalSurplus_le_of_homogeneousCaps`,
  `globalSurplusOf_le_of_homogeneousCaps` and the two positive-part variants
  restate the same conclusion after
  `NearCubicSpine.globalSurplusOf_eq_degreeSurplus`.
- **What it should do.** `BoundedMember` would be `𝔗_cap`,
  `boundedMembers` an enumeration of it, and `boundedLowerMass t` would be
  `ℓ_cap(t)` — the CT9 fibre count of row 33's `Θ_cap` — with a theorem
  `boundedLoad = |Π_blk|` in place of the current `boundedLoad = σ(σ-1)`,
  and a theorem `boundedCap ≤ M₀ * (8 * vertexCount + degreeSurplus 3)`.
  The cap `boundedCapacity t = M₀` would have to be *derived* from
  `lem:same-token-bottleneck-routing`: a theorem whose hypotheses are the
  absence of a role-homogeneous same-token `L_geom`-matching and
  `L_geom`-star in each of the three classes and whose conclusion is
  `∀ t, ℓ_cap t ≤ Cap_hom L_geom`.  `ExceptionalCandidate` would carry the
  four non-cycle exits of `def:named-surplus-exits` (target-defective
  quotient, target-complete compression, proper/global delocalization,
  chord-set arithmetic), and the `structured` arm would route to the Type B
  fan ledger — the subgraph rooted at `v42` — so that all three alternatives
  of `prop:nonnear-cubic-sharp-overload-routing` are realized.
- **Gap.** Three distinct failures.  First, the cap is supplied, not
  derived: `boundedCapacity` is the constant `homogeneousTokenCap
  (baselineDegree)` on every member, and nothing in the tree proves
  `ℓ_cap(t) ≤ M₀` — no matching, star, `L_geom`, or `Q_geom` occurs, so
  `lem:same-token-bottleneck-routing`, the whole content of the audit that
  establishes the hypothesis, is absent, and with it
  `cor:same-token-pattern-caps-close`.  Second, the ledger is the wrong one:
  `BoundedMember` is `V(G)`, so `boundedCap = n · M₀` where the paper has
  `M₀|𝔗_cap|` with `|𝔗_cap| ≤ 8n + σ(G)`; and
  `boundedLowerMass v = (d(v)-3)(σ-1)`, giving `boundedLoad = σ(σ-1)`, which
  is never proved equal to `|Π_blk|` or to `Σ_t ℓ_cap(t)`.  The surviving
  arithmetic (`σ(σ-1) ≤ n·cap ⟹ σ ≤ 1 + √(cap·n)`) is a correct `Nat.sqrt`
  argument, but its hypothesis is a CT14 route condition rather than clauses
  (a),(b),(c) of `cor:homogeneous-same-token-caps-close`, and it omits that
  corollary's route through `thm:tokenized-surplus-accounting-closure` — the
  entropy term `E_spine(n) + ((1/2)σ+1)log₂ n` never appears.  Third, the
  exhaustive outcome of `prop:nonnear-cubic-sharp-overload-routing` is not
  realized: alternative (b) is implemented only as exit (a) of
  `def:named-surplus-exits`, since `TargetCandidate` is
  `Graph.CycleCertificate object PowerOfTwoLength` and
  `ExceptionalCandidate` is `Empty`; and alternative (c) does not reach the
  Type B fan ledger — in
  `/home/guillem/structural_exhaustion/examples/hypostructure_erdos_64_eg/HypostructureErdos64EG/StrategyDag.lean`
  the `structured` continuation is `fun residual => residual.autoroute …`,
  realized in the export as `e16 : v8 → v16`, and `v16` is
  `finite_barrier_enumeration:0`, the near-cubic enumeration, not the Type B
  fan subgraph (`v42`, `v44`, `v43`, `v40`, reached from `v23`'s `type_B`
  output by `e74`).  **Facts therefore fails.**
- **Ledger and residual.** `HomogeneousBottleneck.Profile.execution` is the
  right-associated composition
  `(CTAdapters.ct9 collisionCapability).compose ((CTAdapters.ct14
  codeCapacityCapability).compose ((CTAdapters.ct10
  classificationCapability).compose ((CTAdapters.ct6
  localFailureCapability).compose ((CTAdapters.ct3
  responseCapability).compose ((CTAdapters.ct6
  admissibilityCapability).compose ((CTAdapters.ct1
  outcomeCapability).compose ((CTAdapters.ct5 supportCapability).compose
  (CTAdapters.ct14 boundedCapability))))))))`, each stage built over the
  previous `Ledger.Extension` (`AfterCollision`, `AfterCodeCapacity`,
  `AfterClassification`, `AfterLocalFailure`, `AfterResponse`,
  `AfterAdmissibility`, `AfterOutcome`, `AfterSupport`), and every
  downstream query obtained by `Query.preserve` from the single
  `residualQuery`.  `Profile.bounded_load_le_cap` reads the certificate off
  the composed run.  The predecessor is the literal row-35 stage.  Ledger
  and Residual pass.
- **Transport and terminals.** All nine CTs, the terminal elimination and
  the ledger extensions are Core-owned; Graph supplies the registration and
  fixes the cycle injection itself (`homogeneousBottleneck` passes
  `fun _ cycle => cycle`, `homogeneousBottleneckOr` passes
  `fun _ cycle => Or.inl cycle`), so the application supplies no
  target-closing callback.  `v8` is exported with `kind: operation` and four
  outgoing edges: `e14 : v8 → t1` (`output: target`, closed, reason
  "homogeneous-bottleneck target output"), `e15 : v8 → t2`
  (`output: exceptional`, closed — vacuous, since `ExceptionalCandidate` is
  `Empty` and `exceptionalImpossible` is registered), and the two autoroutes
  `e16 : v8 → v16` and `e17 : v8 → v16`.  Both surviving arms land on the
  same vertex.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:same-token-bottleneck-routing` | lem |  |  |
| `thm:homogeneous-overload-geometric-closure` | the |  |  |
| `cor:homogeneous-same-token-caps-close` | cor |  |  |
| `cor:same-token-pattern-caps-close` | cor |  |  |
| `prop:nonnear-cubic-sharp-overload-routing` | pro |  |  |

`cor:homogeneous-same-token-caps-close` is filed here rather than at its
ledger node `[138]` because `[144]` is where its hypotheses are meant to be
discharged.  Its cell is empty deliberately:
`SurplusAccounting.degreeSurplus_le_of_homogeneousCaps` and
`homogeneousBottleneck_degreeSurplus_le_of_bounded` derive
`σ ≤ 1 + √(cap·n)` from an *aggregate* hypothesis `σ(σ-1) ≤ n·cap`, not from
clauses (a),(b),(c) about role-homogeneous matchings and stars, so no
declaration's type states the corollary.  `cor:same-token-pattern-caps-close`
is filed at the closest row for the same reason.

**CT composition at this row.** `HomogeneousBottleneck.Profile.execution`
composes nine stages,
**CT9 → CT14 → CT10 → CT6 → CT3 → CT6 → CT1 → CT5 → CT14**, right-associated;
the reference table lists the set `{CT1, CT3, CT5, CT6, CT9, CT10, CT14}`
and does not record that CT6 and CT14 each appear twice.  CT9 partitions
`items` by `homogeneityCodeOf` against `homogeneityCapacity`; CT14 compares
each code's mass against `codeCapacity` grouped by `codeLabel`; CT10
classifies `data` by `classOf`, splitting on `Direct` and applying
`promote`; the first CT6 scans `localOrder` for a `LocalFailure`; CT3 runs
the response system, testing `ResponseAdmissible` and
`ResponseStrictlySmaller` over `responseCandidates` and `responseRows`; the
second CT6 scans `admissibilityOrder` for an `AdmissibilityFailure`; CT1
scans `outcomeCandidates` and decides the target or exceptional outcome; CT5
runs the support accounting of `supportRequired` against `supportCapacity`;
the final CT14 compares `boundedLowerMass` against `boundedCapacity` over
`boundedMembers`.  Under the registered presentation five of the nine are
vacuous — the two CT6 failure scans (`degree v < baselineDegree`, impossible
under `minimumDegree`), CT3's unit response system with
`ResponseAdmissible = True`, and CT5's support step with
`supportRequired = 0` — so what the composition actually buys is its last
two live stages: CT1 scans the accepted-cycle certificate schedule and
closes the target arm `e14 : v8 → t1`, and the final CT14 produces the
`.bounded` route whose certificate `Profile.bounded_load_le_cap` feeds
`boundedRoute_degreeSurplus_le` to give
`degreeSurplus ≤ 1 + Nat.sqrt (homogeneousTokenCap · vertexCount)`.  That
last step is the only place in rows 30–36 where a CT verdict is turned into
a mathematical conclusion rather than restated; no single CT could produce
it, because the route condition is a terminal of the ninth stage over a
ledger the first eight built.

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
  `SpineRun.completedKeys` carries `wedgeSupply` and `curvatureDemandFloor`
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
  `def:admissible-rank-quotient` at that family, clause by clause.  Its
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

  `Graph.FiniteObject.curvatureQuotientSystem` is the system
  `def:functional-rank-quotient` closes with — "the admissible quotient system
  used to compute target-rank consists only of admissible rank quotients that
  are functional on the coordinate family under discussion" — so membership is
  exactly *admissible* (a `CurvatureQuotient`) *and functional*.
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
  `Decision.run`.  The test is `r_Ω(R) < W₂(R) − rankDefect(W₂(R))`, with
  `rankDefect` the registered `o(W₂)` of `Spine.Data`.  The yes arm commits
  `curvatureRankDrop`: the packing, the strict inequality, and a proper
  target-dependence of the system.  That dependence is *read*, not recomputed:
  the decision reads node `[31]`'s committed fact off the incoming ledger by
  exact key with `ExactLedger.get`, takes the maximal surviving subfamily it
  attains, and applies `Core.TargetRank.exists_dependence_of_attaining` to it —
  an allowance subtracted from `W₂(R)`, which *is* the number of raw tests,
  leaves a bound below the family's own size, and that is
  `lem:target-rank-circuit`'s hypothesis.  The no arm commits `curvatureFullRank`,
  `W₂(R) − rankDefect(W₂(R)) ≤ r_Ω(R)` at every packing.  The two arms are the
  two halves of one excluded middle, so they are exhaustive and mutually
  exclusive by construction, and neither is readable on the other's branch.

  `Graph.CurvatureQuotient.localize` is `lem:curvature-dependence-routing` for
  an admissible quotient: the manuscript's target-defect case cannot arise —
  an admissible quotient is target-complete by definition, which is what
  `fibrewise` and `contextUniversal` record — so a rank-reducing member falls,
  by the scope of its determination support, into a replacement of a proper
  support or a smaller closed representative.  It is proved here and consumed
  at `[33]`/`[35]`–`[46]`, where those two are refuted by
  `not_replacementSupport` and by the selection's own minimality.
- **What it should do.** This is the implementation.  Every object node `[31]`
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
  substitutions of `[29]`–`[30]`, and `o(W₂)` is registered as `Data.rankDefect`
  exactly as `[19]`'s `o(n)` is registered as `Data.surplusThreshold`; no
  numeral appears at either node.
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
  to.  `SpineRun.completedKeys` is the seventeen-key full-rank index and
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
  `Spine.Result` grows a fourth constructor, `curvatureRankDrop`, carrying the
  Branch-D ledger; the spine's exits are now node `[19]`, node `[21]`, node
  `[32]`-yes, and completion on Residual B.  Neither row names a producer, a
  predecessor depth, or an execution position: both are quantified over the
  keys they consume and produce.  `#print axioms` on `Spine.run`,
  `curvatureRankDichotomy`, both audit theorems, `curvatureTargetRank`,
  `CurvatureQuotient.localize` and every `Core.TargetRank` theorem reports
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
  shim.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | Realization |
|---|---|---|---|
| `def:declared-coordinate-signature` (D4) | def | `Graph.FiniteObject.InternalWedge`<br>`Graph.FiniteObject.internalWedgeFamily`<br>`Graph.FiniteObject.internalWedgeSupport` | the raw curvature coordinates and their declared supports — the only clause node `[31]` ranks over |
| `𝒲₂(R)` and `\|𝒲₂(R)\| = W₂(R)` | def | `Graph.FiniteObject.internalWedgeFamily_card` | ties the family to node `[30]`'s count |
| `def:boundaried-gluing`, `def:atom` | def | `Graph.Boundary`, `Graph.BoundaryPiece`, `Graph.OutsideContext`, `Graph.glue`<br>`InterfaceReplacement.SupportAtom.boundary`, `.cutBoundary` | inherited; `cutBoundary` is the manuscript's `T` |
| `def:boundary-degree-profile` | def | `Graph.BoundaryPiece.boundaryDegreeProfile` | inherited |
| `def:exact-response-profile` | def | `Core.TargetRank.RankQuotient`<br>`.LabelInjectiveOn`, `.RankReducingOn` | a quotient's labelling of the declared coordinates and its response at a realization |
| `def:target-complete-quotient` | def | `Graph.CurvatureQuotient.fibrewise`<br>`Graph.CurvatureQuotient.contextUniversal` | clauses (a) and (b), at `boundaryDegreeProfile` and at `glue` against every `OutsideContext` |
| `def:proper-quotient-representative` | def | `InterfaceReplacement.ReplacementSupport` | the manuscript's own identification of its five properties with `lem:replacement`'s five hypotheses |
| `def:closed-quotient-representative` | def | `Graph.CurvatureQuotient.closedRepresentative` | strictly smaller, baseline, `profile_∅(H) ⊆ profile_∅(G)` read at the empty context |
| `def:admissible-rank-quotient` | def | `Graph.CurvatureQuotient` | all four clauses; the proper/closed split is `SupportAtom.classifyScope` |
| `def:functional-rank-quotient` | def | `Core.TargetRank.RankQuotient.Determines`<br>`Core.TargetRank.RankQuotient.FunctionalOn`<br>`Graph.FiniteObject.curvatureQuotientSystem` | the rank axiom, and the closing sentence that the system consists only of functional admissible quotients |
| `def:curvature-target-rank` | def | `Graph.FiniteObject.curvatureTargetRank`<br>`Core.TargetRank.QuotientSystem.Survives`<br>`Core.TargetRank.targetRank`<br>`Graph.FiniteObject.curvatureTargetRank_le_internalWedgeCount` | `r_Ω(R)` as a `Nat` |
| `def:curvature-target-dependence` | def | `Core.TargetRank.Dependence` | the pair, its determination against every realization, its properness, and the rank-reducing admissible quotient witnessing it |
| `lem:target-rank-circuit` | lem | `Core.TargetRank.exists_dependence_of_maximal`<br>`Core.TargetRank.exists_independent_attaining`<br>`Core.TargetRank.exists_dependence_of_targetRank_lt`<br>`Core.TargetRank.targetRank_eq_card_of_no_dependence` | proved, including the "in particular"; committed as `Spine.Key.curvatureTargetRank` and consumed by the yes arm of `[32]` |
| `lem:curvature-dependence-routing` | lem | `Graph.CurvatureQuotient.localize` | proved: the target-defect case cannot arise for an admissible quotient, and the other two are the scope split of the determination support; consumed at `[33]`/`[35]`–`[46]` |
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

- **Paper fact.** `[47]` is Residual B, `lem:full-rank`: `r_Ω(R) ≥ W₂(R) − o(W₂)`.
  `[48]` is `cor:forced-curvature-cost`: `c_Ω r_Ω(R) ≥ K_win|R| − o(|R|)` with
  `K_win = c_Ω ω_win`, sharpening to `K = c_Ω ω = 5.89262883286…` on the
  high-entropy branch; its whole proof is "this follows from `lem:full-rank`,
  `lem:wedge-lower` and the definitions of `K_win` and `K`", and
  `rem:curvature-provenance` separates the two ingredients — the routing supplies
  the *independence* of the cost, the finite enumeration `lem:curv-enum` supplies
  its *value* `c_Ω = log₂(543958/111286) = 2.28922315244…`.  `[49]` is
  `def:remainder-entropy`: `η(R) = log₂|𝒢(R)|/|R|` for the class `𝒢(R)` of
  labelled simple graphs on `V(R)` satisfying the remainder constraints already
  imposed on the branch, used symbolically — "no enumeration of labelled graphs
  is prescribed, and only `|𝒢(R)|` is ever consumed".  `[50]` is the decision
  `η(R) ≥ (1/10)log₂ n`, whose no arm carries `lem:dominant-type` and
  `rem:cheap-regime-link`.  `[51]` is the high-entropy branch of
  `prop:two-budget` (a), where the remainder's realized states number at least
  `2^{η(R)|R|} ≥ n^{|R|/10}`; `lem:translates-independent` and
  `rem:positive-fraction` belong to its low-entropy sibling (b).  `[52]` is the
  window-plus-remainder accounting, `eq:feasibility`.  `[53]` is the decision
  "remaining non-curvature budget `< K|R|`?", which by `def:Theta` is exactly
  `eq:entropy-cap`; `[54]` is its closed terminal `prop:entropy-high-theta`,
  reached from `[52]` and from `[53]`-yes, with `rem:entropy-argument-order`
  fixing that entropy is applied only after rank forcing and `rem:closure-robust`
  recording that the closure outside the explicit residuals needs neither the
  exact `c_Ω` nor the precise rank fraction.  `[55]` is Residual C, the
  large-budget branch `θ ≤ θ_win + o(1)`, with `def:canonical-decomp` and
  `def:admissible`.  `[56]` is
  `Δ_net(R) = (def⁺(R) − σ_R)/|R| ≤ τ_win + o(1)`, `τ_win = 15θ_win/(1 − 13θ_win)
  = 0.22817486846… < 1/4`.
- **What the Lean does.** The row is five canonical-ledger steps on the spine's
  own `ExactLedger`, run by `Spine.run` after the node-`[34]` full-rank residual.
  `[47]`–`[48]` is `SpineRows.forcedCurvatureCostRow`, a `factOnly` step
  requiring `curvatureDemandFloor` and `curvatureFullRank` and producing
  `forcedCurvatureCost`; its body performs the manuscript's own substitution —
  `Nat.sub_le_iff_le_add` turns `W₂(R) − o(W₂) ≤ r_Ω(R)` into
  `W₂(R) ≤ r_Ω(R) + o(W₂)`, that replaces the wedge supply in node `[30]`'s
  demand floor, and `Nat.mul_le_mul_left` applies the registered cost to both
  sides.  `[49]`–`[50]` is `SpineRows.remainderEntropyDichotomy`, a `Decision`
  on `Graph.AtLeastEntropyRate n d order threshold |R|`, which is
  `n^{|R|} ≤ |𝒢(R)|^d` — `def:remainder-entropy` exponentiated by `d·|R|`, so no
  logarithm, division, or rounding is written.  `𝒢(R)` is
  `Graph.RemainderClass order threshold |R|`, the labelled graphs on `|R|`
  vertices carrying exactly node `[27]`'s two clauses (no induced window of the
  registered order, no subregion meeting the registered baseline), and
  `|𝒢(R)|` is `Nat.card` of it; no enumeration exists.  `[51]`–`[52]` is
  `SpineRows.entropyPackageRow` on the high arm, producing
  `entropyPackageDemand`: the joint window/remainder/curvature demand raised to
  the `d`-th power, with the high arm's `n^{|R|} ≤ |𝒢(R)|^d` substituted for its
  remainder factor.  `[53]` is `SpineRows.entropyCapDichotomy`, a `Decision`
  comparing that joint demand against `Graph.skeletonBudget` — the same budget
  node `[21]` compared the window package against.  `[56]` is
  `SpineRows.netDeficiencyCapRow`, requiring `stubSupply` and producing
  `netDeficiencyCap`: node `[29]`'s ceiling multiplied through by the registered
  discharge scale, with the packing eliminated by the object's own
  `Graph.FiniteObject.remainderSupport_card_add_eq` (`|R| + order·p = n`).  The
  packing it commits is the one node `[17]` selected, and since row 11 the fact
  carries its **maximality** as well — `maximalPacking`'s own last clause, read
  through `packingOf` — so `[27]` stays instantiable at every subregion of the
  remainder for the rest of the run.  See row 42's correction bullet.
  Three registered constants are new, all in `Problem.lean`'s `spineData` and
  none written at a node: `curvatureCost` is
  `Core.Finite.CertifiedTableAggregation.binaryRowRateFloor` of the audited
  `P13Barrier.certifiedTable` at its length-`1` connector row — the row whose
  certified safe and flat counts are `lem:curv-enum`'s own `543958` and
  `111286` — `entropyDenominator` is the presentation's
  `remainderEntropyThresholdDenominator`, and `dischargeScale` is its
  `loadMultiplier`.
- **What it should do.** `[54]` should be a *closed* terminal.  Its closure is
  `prop:entropy-high-theta`: the window package, the remainder bits, and the
  forced-curvature bits form one independently target-testable coordinate
  family, so the states they realize cannot outnumber the labelled near-cubic
  skeletons (`lem:independent-target-entropy` with `lem:skeleton-dominates`).
  Node `[53]`'s yes arm is exactly the statement that they do outnumber them, so
  the two are incompatible and the arm closes.
- **What it should do.** Nothing further: every node of the row is implemented,
  and `[54]` is the closed terminal the manuscript draws.
- **Gap.** None on the mathematics.  `[54]` closes, and so does the identical
  terminal `[23]` of rows 9--10, through one realization:

  * `Graph.PackedWindowRealization.SeparatedFamily` is `lem:p13-window-package`'s
    coordinate family, carrying the manuscript's own *selection* as its
    hypotheses — `separated` (distinct coordinates read disjoint vertex sets) and
    `sourcesOutside` (the testers are rooted outside the package).  Separation is
    not proved of every scale: the package "uses `⌊log₂ n⌋ − O(1)` separated
    dyadic scales", and the colliding ones are the `O(1)` the selection discards.
  * `adj_realize_iff` reads the package back coordinate by coordinate, which is
    the manuscript's "the tester for one window does not change the label state
    assigned to another packed window"; `realize_injective` and
    `card_state_pi` give the product, so `log₂` turns it into the paper's *sum*
    of the 91 barrier rates.
  * `card_state_pi_le_skeletonBudget` is `lem:skeleton-dominates` at `𝒢_{n,m}`
    rather than `𝒢_n`: the coordinates occupy their own `slots`, the completion
    to the ambient edge count is drawn from a `pool` disjoint from them and
    depends only on how many edges are still needed, so it carries no
    information and never has to be injective — `filled_eq_inter` recovers the
    package by intersecting with the slots.
  * Node `[21]`'s selection is `SpineRows.windowPackageDichotomy`, a `Decision`
    with both arms retained: the separated arm commits the realization, the
    collided arm leaves the block as `Result.windowPackageCollided`.
  * `Spine.instIncompatibleEntropyCap` is then `prop:entropy-high-theta` —
    node `[53]`'s yes arm demands strictly more states than there are skeletons,
    the realization says it does not — and `closeIncompatible` appends the
    residual domain's distinguished closure key.  `Spine.instIncompatibleWindowPackage`
    does the same for `[23]`.  **Facts therefore holds.**

  Two smaller items, neither affecting what is committed.  `curvatureCost` reads
  the audited table's rate *floor*, so the registered `c_Ω` is
  `⌊log₂(543957/111286)⌋` against the manuscript's `2.28922315244…`; the rounding
  is downward, so the forced cost node `[48]` states is no larger than the real
  one, and `rem:closure-robust` records that the closure outside the explicit
  residuals holds for every nonnegative value.  And `[50]`'s no arm carries only
  the entropy inequality: `lem:dominant-type` and `lem:translates-independent`,
  which `prop:two-budget` (b) uses to extract a positive linear rank in the
  structurally repetitive sub-case, are not implemented — `prop:two-budget`'s own
  routing sends every low-entropy branch forward unchanged, and that is what the
  Lean does.

  **`[56]` and the numeral `τ_win < 1/4` — now proved.**  Node `[24]`'s demand
  carries its per-dyadic-scale factor again (see rows 9–10), so the cap it
  converts to is the manuscript's `θ ≤ θ_win + o(1)` rather than a `log₂ n`
  weaker one.  Spending it is `SpineRows.netDeficiencyCapRow`: the packing
  number is eliminated against node `[29]`'s ceiling, the slack is cleared at
  the registered order exponent, and what comes out is the manuscript's own
  `A·p₁₃ + s·o(n) < n` with `A = s·(δ·order − 2(order−1)) + order`, the `73` of
  `cor:global-window-join-pressure`.  So `[56]` commits `N₀(R) < 0` outright —
  the whole remainder already carries negative net charge — which is exactly why
  the manuscript's node `[60]` is a vacuous terminal.

  Two numbers enter, both the presentation's own and neither a numeral written
  at a node.  `Data.netChargeRate` is `τ_win < ¼` cleared of denominators, a
  comparison between the registered baseline, window order, discharge scale,
  order exponent and audited rate; `Data.largeOrder_dominates_surplus` is the
  registered order against the square of the coefficient the collision carries
  against the surplus.  `Data.surplusThreshold_sublinear` *derives*
  `σ(G) = O(√n) = o(n)` from the second through `Core.mul_ceilSqrt_le`, so no
  decimal, no intermediate product, and no evaluated table value appears in any
  proof.  Node `[55]`'s diamond is the manuscript's own "for all sufficiently
  large `n`", made explicit with both arms retained — the same device node
  `[19]` already uses for its registered `o(n)` threshold — and its small-order
  arm leaves the block as `Result.smallOrderResidual`, the finite residue the
  manuscript's asymptotic statements do not address.

- **Ledger and residual.** Every step is on the one canonical
  `Core.Residual.ExactLedger` at the residual `Spine.run` was opened on.  The
  fact-only rows are appended by `AtomicCT.run`, so the output index is
  definitionally `Produces ++ known` and every earlier fact stays in the type;
  the two diamonds are `Decision.run`, so the arm not taken is absent from the
  taken branch's index.  The residual is unchanged throughout — every step is a
  fact-only step whose `refines` is equality — and no packing, class, or support
  travels: every clause is quantified over the maximal packings of the object
  the residual carries.  The new indices are `forcedCurvatureCostKeys`,
  `remainderEntropyHighKeys`, `entropyPackageKeys`, `remainderEntropyLowKeys`,
  `entropyCapActiveKeys` and `largeBudgetKeys`, each one key on top of its
  predecessor.  Prerequisites are discharged by instance resolution against the
  incoming index, so a row asking for a fact the branch has not proved does not
  elaborate.  **Ledger ✅, Residual ✅.**
- **Transport and terminals.** No CT adapter and no registration: the row is
  five `AtomicStrategy`/`Decision` steps composed by the framework's own
  `AtomicCT.run` and `Decision.run` inside `Spine.run`.  Facts are read only by
  `FactInputs.get` inside an executor and by `ExactLedger.get` at the
  framework-owned decision boundary.  Nothing is transported outside the
  ledger, and no payload, terminal, or audit channel carries mathematics.  The
  two node-`[54]` exits are `Result.entropyPackage` and
  `Result.entropyCapActive`; neither appends the distinguished closure key,
  because neither is proved uninhabited (see **Gap**).  Node `[55]`, Residual C,
  is `largeBudgetResidual`, and the run continues from it into row 42.
  **Transport ✅.**

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:full-rank` | lem | `Spine.Key.curvatureFullRank` (row 40) | consumed at `[47]` by `SpineRows.forcedCurvatureCostRow` as a ledger fact, read by exact key |
| `cor:forced-curvature-cost` | cor | `Spine.Key.forcedCurvatureCost`<br>`SpineRows.forcedCurvatureCostRow` | no CT — one fact-only spine row |
| `rem:curvature-provenance` | rem | `Spine.Data.curvatureCost` | the registered value; the independence is `lem:full-rank`'s |
| `lem:curv-enum` | lem | `FiniteChecks.P13Barrier.certifiedTable` at the length-`1` connector row, through `Core.Finite.CertifiedTableAggregation.binaryRowRateFloor` | the audited finite table |
| `def:remainder-entropy` | def | `Graph.RemainderClass`<br>`Graph.remainderStateCount`<br>`Graph.AtLeastEntropyRate` | no CT |
| `lem:skeleton-dominates` | lem | `Graph.LabelledOn.card_range_le_card`<br>`Graph.remainderStateCount_le_card_labelledOn` | available; unconsumed at this row — see **Gap** |
| `lem:dominant-type` | lem | | not implemented; `prop:two-budget` (b) |
| `rem:cheap-regime-link` | rem | | |
| `lem:translates-independent` | lem | | not implemented; `prop:two-budget` (b) |
| `rem:positive-fraction` | rem | | |
| `prop:two-budget` | pro | `Spine.Key.remainderEntropyHigh`, `Spine.Key.remainderEntropyLow`<br>`SpineRows.remainderEntropyDichotomy` | branch (a) and the (b)/(c) routing; (b)'s rank extraction is not implemented |
| `rem:forced-cost-role` | rem | | |
| `eq:feasibility` | equation | `Spine.Key.entropyPackageDemand`<br>`SpineRows.entropyPackageRow` | the demand side, exactly |
| `eq:entropy-cap` | equation | `Spine.Key.entropyCapActive`<br>`SpineRows.entropyCapDichotomy` | the comparison; its closure is the gap |
| `def:Theta` | def | | the threshold is not written: `[53]` compares the two integers `Θ(n)` is defined to separate |
| `prop:entropy-high-theta` | pro | | not proved — see **Gap** |
| `rem:entropy-argument-order` | rem | | respected by construction: `[48]` precedes `[50]` in the ledger index |
| `rem:closure-robust` | rem | | recorded against `Spine.Data.curvatureCost`'s rounding |
| `def:canonical-decomp` | def | `Graph.FiniteObject.canonicalPieces`<br>`Graph.FiniteObject.sum_canonicalPieces` | consumed at `[57]`–`[58]`, row 42 |
| `def:admissible` | def | `Graph.SupportComponents.Connected.ConnectedOn` with `Spine.Key.remainderNormalized` | consumed at `[61]`, row 42 |
| `lem:netcharge-superadd` | lem | `Graph.FiniteObject.nonNegativeNetCharge_of_forall_pieces` | consumed at `[58]`, row 42 |

**CT composition at this row.** **None.**  The row composes no CT adapter: it
is five atomic canonical-ledger steps.  `[47]`–`[48]`, `[52]` and `[56]` are
`factOnly` strategies run by `AtomicCT.run`; `[50]` and `[53]` are
`Decision.run`.  Every one of them declares a nonempty-output `FactManifest`,
receives only sealed `FactInputs`, and returns exactly `manifest.Produces`.
The mathematics is Core's and Graph's — `Graph.RemainderEntropy`,
`Graph.SkeletonBudget`, `Graph.WindowRemainder`, `Core.Finite.CertifiedTableAggregation` —
and none of it names this problem.

### Row 42 — Net-charge continuation `[57]`–`[64]`

- **Paper fact.** `[57]` carries the large-budget net cap of `[56]`.  `[58]` is
  `def:net-charge`: for an admissible support `X`,
  `N₀(X) = def⁺(X) − σ(X) − ¼|V(X)|`.  `[59]` is the decision `N₀(R) ≥ 0?`,
  answered by `lem:netcharge-superadd`:
  `Σ_i N₀(X_i) = def⁺(R) − σ(R) − ¼|R|` over the connected admissible supports
  of `def:canonical-decomp`, "consequently, if `def⁺(R) − σ(R) − ¼|R| < −ε|R|` …
  then some connected support `X_i` has `N₀(X_i) < 0`".  Its proof is the three
  exact sums the decomposition supplies — `Σ|V(X_i)| = |R|`,
  `Σσ(X_i) = σ(R)`, and `Σdef⁺(X_i) = def⁺(R)`, the last because
  `d_{X_i}(u) = d_R(u)` inside a connected component.  `[60]` is the net-cap
  contradiction: `¼|R| ≤ def⁺(R) − σ(R) ≤ τ_win|R| + o(|R|)` with `τ_win < ¼`;
  `cor:global-window-join-pressure` is the exact accounting form of the same
  arm — if every connected admissible support has nonnegative net charge then
  `σ_W − σ_R ≥ (n − 73p₁₃)/4` — and `rem:window-join-pressure-meaning` reads it
  back as a linear excess of window surplus over remainder surplus.  `[61]` is
  `prop:negative-net-charge`: choose a connected admissible support `X` with
  `N₀(X) < 0`.  `[62]` splits on whether `X` carries high-degree surplus, to
  `[63]` Type A and `[64]` Type B.
- **What the Lean does.** The row is four canonical-ledger steps continuing
  `Spine.run` from node `[55]`.  `[57]`–`[58]` is
  `SpineRows.netChargeLocalizationRow`, producing `netChargeLocalization`:
  at every maximal packing, a remainder of negative net charge has a subset that
  is connected in the object and has negative net charge.  Its body is one
  application of `Graph.FiniteObject.exists_connected_negativeNetCharge`, whose
  proof is the manuscript's own — the contrapositive of
  `nonNegativeNetCharge_of_forall_pieces`, which is the three exact sums
  `sum_pieceSupport_card`, `sum_ambientSurplus_canonicalPieces` and
  `sum_positiveDeficiency_canonicalPieces` over
  `Graph.FiniteObject.canonicalPieces`, `def:canonical-decomp`'s connected
  components.  The deficiency sum is the only clause with content, and
  `internalDegree_pieceSupport` is exactly `d_{X_i}(u) = d_R(u)`: a neighbour
  that stays in the region is joined by an edge of the induced graph, so it
  lies in the same component.  `def:net-charge` is
  `Graph.FiniteObject.NegativeNetCharge` and `NonNegativeNetCharge`, the two
  halves of the subtraction-free integer comparison
  `s·def⁺(X) < |V(X)| + s·σ(X)` the signed definition reduces to after
  multiplying by the registered scale — no rounding, and the `¼` never appears
  as a rational.  `[59]` is `SpineRows.netChargeDichotomy`, a `Decision`
  producing `netChargeNonNegative` or `netChargeNegative`; its excluded middle
  is taken over the packings that are maximal, which is where the manuscript's
  `R = G − W` lives, so the negative arm carries the maximality forward.  `[60]` is
  `SpineRows.windowJoinPressureRow` on the nonnegative arm, requiring
  `netChargeNonNegative` and `boundaryDemand` and producing
  `windowJoinPressure`; its body composes
  `lem:surplus-aware-window-stub`'s two links, scales by the discharge scale,
  and eliminates the packing with `remainderSupport_card_add_eq`, leaving
  `n + s·σ_R + s·2(order−1)p ≤ s·δ·order·p + s·σ_W + order·p`, which at the
  registered values is `σ_W − σ_R ≥ (n − 73p₁₃)/4`.  `[61]` is
  `SpineRows.negativeSupportRow`, requiring `netChargeNegative` and
  `netChargeLocalization` and producing `negativeSupport`.  `[62]` is
  `SpineRows.typeSplitDichotomy`, a `Decision` on the *selected* support's own
  assigned surplus, producing `typeALowSurplus` or `typeBHighSurplus`; the
  decision is taken on a `Prop`, so no witness is extracted to build the branch
  and the arm not taken supplies the other arm's clause.
- **What it should do.** Nothing further: every node of the row is implemented,
  and `[60]` is the closed terminal the manuscript draws.
- **Gap.** None on the mathematics.  `[60]` closes: node `[56]` proves that the
  whole remainder already carries negative net charge, node `[59]`'s yes arm
  says it does not, and `Spine.instIncompatibleNetCharge` registers that
  collision — the manuscript's `¼|R| ≤ def⁺(R) − σ(R) ≤ τ_win|R| + o(|R|)` with
  `τ_win < ¼` — so `Core.Strategy.closeIncompatible` appends the residual
  domain's distinguished closure key the moment the branch test takes the arm.
  `cor:global-window-join-pressure` is committed on that arm first, because the
  manuscript states it there; the arm then closes.  **Facts therefore holds.**

  **Correction, made by row 11's port.**  An earlier revision of this bullet
  recorded as a design note that what `[61]` keeps of `def:admissible` is the
  two clauses the decomposition supplies — connected piece, negative charge —
  and that the inherited clauses "are readable on the same branch at every
  subregion rather than carried", naming `remainderNormalized` for
  componentwise window-freeness and the empty internal core.  That was wrong
  as stated.  `remainderNormalized` is quantified over packings that are
  *maximal*, and the packing `[56]`–`[62]` carried was a bare
  `IsWindowPacking`: the maximality was used inside
  `netDeficiencyCapRow` and then dropped, so nothing downstream could
  instantiate `[27]` at the piece.  The clause is not decorative — a
  `δ`-regular object with the empty packing satisfies every clause `[63]`'s
  fact carried, and its own vertex set is then a nonempty internal `δ`-core, so
  row 11's `lem:typeA-receiver-loads` is false without it.

  The four facts of this row now carry the maximality of their packing:
  `netChargeNonNegative` takes it as a hypothesis, and `netChargeNegative`,
  `negativeSupport` and `typeALowSurplus` carry it as a conjunct.  `[59]`'s
  decision is correspondingly taken over the maximal packings, which is also
  where the manuscript's `R = G − W` lives.  Row 11 then reads `[27]` at its
  support and the inheritance is literal.  The remaining inherited clauses are
  unchanged: hereditary target-uncompressibility from `uncompressible`, the
  window-supplied deficient boundary from `boundaryDemand`.  Contextual
  dyadic-safety (`def:dyadic-safe`) is the one clause no spine fact carries;
  neither arm of `[62]` consumes it.

  `typeBHighSurplus` deliberately does **not** carry the maximality: no ported
  Type B row consumes it, and adding it would have re-shaped rows 20–25's row
  signatures for no current use.  A Type B row that needs `def:admissible`'s
  inherited clauses has to reinstate the conjunct on that arm of
  `typeSplitDichotomy` first; the clause is available there, since
  `negativeSupport` carries it.
- **Ledger and residual.** Four steps on the same canonical `ExactLedger`, on the
  unchanged residual.  `netChargeLocalization`'s manifest requires nothing —
  `lem:netcharge-superadd` holds at every region of every object, so no
  prerequisite is manufactured to place it, and its position is fixed by the
  ledger index alone.  The other three read their prerequisites by exact
  semantic key through `FactInputs.get`; `[62]` reads `negativeSupport` through
  `ExactLedger.get` at the decision boundary.  No support, packing, or component
  schedule travels: `[61]`'s and `[62]`'s facts are existential statements about
  the object, which is what makes them refinement-stable and what keeps the
  selected support out of the ledger.  The new indices are
  `netDeficiencyCapKeys`, `netChargeLocalizationKeys`, `windowJoinPressureKeys`,
  `negativeSupportKeys`, `typeALowSurplusKeys` and `typeBHighSurplusKeys`.
  **Ledger ✅, Residual ✅.**
- **Transport and terminals.** No CT adapter and no registration — two
  `factOnly` strategies and two `Decision`s, composed by `AtomicCT.run` and
  `Decision.run` inside `Spine.run`.  The three exits are
  `Result.windowJoinPressure` (node `[60]`, *closed* — its index is
  `closed :: windowJoinPressureKeys`), `Result.typeALowSurplus` (node
  `[63]`) and `Result.typeBHighSurplus` (node `[64]`); the Type A and Type B
  residuals are where the local analysis of `sec:local-analysis` continues, and
  neither can read the other's arm or either arm of `[59]` it did not take.
  `Spine.typeALowSurplus_audit_facts` states the full twenty-six-name audit of
  the Type A exit, and `typeALowSurplus_audit_accounts_for_every_fact`,
  `typeBHighSurplus_audit_accounts_for_every_fact` and
  `windowJoinPressure_audit_accounts_for_every_fact` certify through
  `ExactLedger.audit_complete` that each exit's fact index is exactly what its
  chronological commits produced.  **Transport ✅.**

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:canonical-decomp` | def | `Graph.FiniteObject.canonicalPieces`<br>`Graph.FiniteObject.pieceSupport`<br>`Graph.FiniteObject.sum_canonicalPieces` | no CT — the connected components of `Graph.SupportComponents.Connected`, with the surplus assignment being the partition itself |
| `def:net-charge` | def | `Graph.FiniteObject.NegativeNetCharge`<br>`Graph.FiniteObject.NonNegativeNetCharge` | no CT |
| `lem:netcharge-superadd` | lem | `Graph.FiniteObject.sum_pieceSupport_card`<br>`Graph.FiniteObject.sum_ambientSurplus_canonicalPieces`<br>`Graph.FiniteObject.sum_positiveDeficiency_canonicalPieces`<br>`Graph.FiniteObject.internalDegree_pieceSupport`<br>`Graph.FiniteObject.nonNegativeNetCharge_of_forall_pieces` | no CT — consumed at `[58]` by `SpineRows.netChargeLocalizationRow` |
| `prop:negative-net-charge` | pro | `Graph.FiniteObject.exists_connected_negativeNetCharge`<br>`Spine.Key.negativeSupport`<br>`SpineRows.negativeSupportRow` | no CT |
| `cor:global-window-join-pressure` | cor | `Spine.Key.windowJoinPressure`<br>`SpineRows.windowJoinPressureRow` | no CT — consumed at `[60]`, with both links of `lem:surplus-aware-window-stub` discharged from the ledger |
| `rem:window-join-pressure-meaning` | rem | | |
| `def:admissible` | def | `Graph.SupportComponents.Connected.ConnectedOn` | the two clauses the decomposition supplies; the inherited ones are read on the same branch — see **Gap** |

Nodes `[63]` and `[64]` anchor no `\label` of their own: the diagram routes them
into Parts VIII and VI, whose labels belong to rows 11–29.

**CT composition at this row.** **None**, in agreement with the reference
table's "no CT (Core ledger strategy)".  Execution is four atomic
canonical-ledger steps: `AtomicCT.run` for `[57]`–`[58]` and `[61]`,
`Decision.run` for `[59]` and `[62]`.  Because `[59]` and `[62]` are
`Decision`s, their alternatives are exhaustive by excluded middle on one
integer comparison and one equality, and each arm's key is absent from its
sibling's index.


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
  definition cites it.  The constants are defined and proved here but not yet
  *spent*: their consumers are Row 50's exchange bound and Row 51's schedule
  bound, neither ported.  **Facts passes.**
- **Ledger and residual.** `Spine.coldCorridorStateRow` is a `factOnly` atomic
  Strategy with `Requires := []` and `Produces := [coldCorridorState]`.  The
  committed statement has three clauses: the retention's completeness, the
  `Q_cold` pigeonhole, and *both* directions of the (F2) sentence — the second
  direction was proved but unregistered until the registered-fact review, which
  left the manuscript's dichotomy at a repeated state half-stated on the
  ledger.  Its
  requirement list is empty because neither clause depends on anything an
  earlier node proved — both are theorems about the registered signature — and
  the framework runner still appends the production to the incoming index while
  retaining the literal ancestry, so every earlier fact of the branch stays in
  the output type.  The residual is unchanged: `factOnly` supplies
  `RefinementSystem.refl`, the equality refinement.  The committed statement is
  `Spine.Holds .coldCorridorState`, quantified over *every*
  `ColdCorridor.Presentation` of the object's corridor segments, so no corridor
  construction travels with the fact — a corridor is data, and no fact can carry
  data.
- **Transport and terminals.** `Graph.ColdCorridor` owns the mathematics;
  `Spine.coldCorridorStateRow` owns nothing but the commit.  The row is run by
  `Spine.runCold`, which composes it with Row 44 through `AtomicCT.run` against
  one immutable prefix.  There is no terminal at this row: it produces a fact
  and returns the ledger.

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
  `def:cold-bounded-germ` itself and is the carrier Rows 52–54 use for the
  length-changing germs: `support`/`connected`/`proper` give
  the germ's own boundary piece `Q[x,y]` through
  `Strategy.InterfaceReplacement.SupportAtom.properAtom`, `canonical` is the
  second same-interface representative `E`, `sameProfile` is the inherited
  boundary-degree profile, and `record`/`record_truth` are (T1)–(T4) with (T4)'s
  own specification.  A row adds exactly two clauses to the germ.  `equalLength`
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
  node `[14]` has excluded.  `Handoff` is a *parameter*, an arbitrary predicate
  on supports supplied by whoever owns the already-closed ledger, never a field
  a row may choose, so no row escapes by naming its own.
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
  `Spine.sameInterfaceTableRow` owns nothing but the commit.  `Spine.runCold`
  runs it after Row 43 against one immutable prefix, and its instance
  requirements `FactKeys.Has selection known` and `FactKeys.Has uncompressible
  known` mean a branch that has not proved node `[14]` does not elaborate.  No
  terminal at this row.

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
  the row owns the commit.  `Spine.runCold` runs it third, after the cut-state
  and the table, against one immutable prefix.  No terminal at this row.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:cold-corridor-first-failure` (F1) | def | `ColdCorridor.Window`<br>`ColdCorridor.Window.segment`<br>`ColdCorridor.Corridor.prefixWalk`<br>`ColdCorridor.Corridor.displayedCompletion`<br>`ColdCorridor.Corridor.FirstFailureCycle` | no CT — `Spine.coldFailureCycleRow` |
| `lem:cold-corridor-first-failure` (i) | lem | `ColdCorridor.Corridor.hasCycleWithLength_of_firstFailureCycle` | standalone |

**CT composition at this row.** No CT.  The clause is a decidable predicate over
a finite offset schedule and its elimination is the identity on a walk; a CT
would interpose machinery between a constructed cycle and its certificate.

### Row 46 — (F2) producer `[154]`, `[156]`

- **Paper fact.** `def:cold-corridor-first-failure` (F2): "two prefixes with the
  same displayed boundary data have different target response **against some
  compatible outside context**".  `lem:cold-corridor-first-failure` (ii): "case
  (F2) is a target-defective quotient, hence belongs to the sparse exit or to
  the exit-(4) ledger", proved by "the actual quotient is valid only for the
  current outside context and fails for another compatible context.  By
  `lem:context-universality`, this is not target-complete".
- **What the Lean does.** `Corridor.FirstFailureDefect` is *not* a second
  object: it is `def:cold-corridor-first-failure`'s own recorded discrepancy,
  `Presentation.FirstFailureResponse`, read at the two segments — same cold
  corridor state, and `Graph.Response.TargetDefect` between their readings.
  `TargetDefect` is `∃ outside : OutsideContext boundary, ¬ (Target (glue left
  outside) ↔ Target (glue right outside))`, so the distinguishing context is
  quantified over *all* compatible outside contexts of the shared interface and
  is not collapsed to one ambient evaluation.
  `Corridor.not_targetComplete_of_firstFailureDefect` is
  `lem:context-universality`: the identification is not target-complete in any
  immutable profile fibre, which is exactly "target-defective quotient".
  `Corridor.contextEquivalent_of_not_firstFailureDefect` is its other half, the
  one `lem:cold-same-interface-table`'s neutral row consumes: with the
  discrepancy excluded, two prefixes carrying the same state are
  context-equivalent.
  `ColdCorridor.not_identified_of_firstFailureDefect` is clause (ii)'s routing
  against the branch: `def:surviving-cold-branch` (ii) says every
  identification the branch makes is context-universal, so an (F2) discrepancy
  is not one of them.  That clause of the branch was previously written as
  `ContextEquivalent ∨ TargetDefect`, which excluded middle proves outright and
  which therefore constrained nothing; it now carries the branch's own
  `Identified` relation and is real.
  `Spine.coldFailureDefectRow` commits all three.
- **What it should do.** Exactly this: quantify the compatible outside context,
  deny target-completeness, and record the (F2)-free consequence.
- **Gap.** none.  The gap the previous implementation had — evaluating the
  ambient truth value of an induced subobject once, so that a differing pair
  meant an (F1) cycle — is gone: no ambient evaluation occurs, the context is a
  `Graph.OutsideContext` of the shared boundary, and the conclusion is a denial
  of target-completeness rather than a cycle.  **Facts passes.**
- **Ledger and residual.** `coldFailureDefectRow` is `factOnly` with
  `Requires := [coldCorridorState]`, `Produces := [coldFailureDefect]`.  It reads
  the cut-state fact by exact key; all three clauses are theorems about the
  presentation that fact is about.  The third — that an (F2) discrepancy is not
  one of the branch's identifications — is quantified over every
  `SurvivingColdBranch`, so no row supplies one.  Residual unchanged.
- **Transport and terminals.** `Graph.ColdFirstFailure` owns the mathematics.
  `Spine.runCold` runs it fourth.  No terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:cold-corridor-first-failure` (F2) | def | `ColdCorridor.Corridor.FirstFailureDefect` | no CT — `Spine.coldFailureDefectRow` |
| `lem:context-universality` | lem | `ColdCorridor.Corridor.not_targetComplete_of_firstFailureDefect`<br>`ColdCorridor.Corridor.contextEquivalent_of_not_firstFailureDefect`<br>`Graph.Response.notTargetComplete_of_targetDefect` | standalone |
| `lem:cold-corridor-first-failure` (ii) | lem | `ColdCorridor.not_identified_of_firstFailureDefect` | standalone |

`lem:context-universality` is first consumed here.  Its routing target — the
sparse exit and the exit-(4) ledger — is clause (ii) of
`def:surviving-cold-branch`, recorded at Row 50.

**CT composition at this row.** No CT.  The clause is a denial of
target-completeness given a separating context, which is one application of
`Response.notTargetComplete_of_targetDefect`; CT7 compares response *tables*, and
there is no table here, only a single separation.

### Row 47 — (F3) producer `[154]`, `[157]`

- **Paper fact.** `def:cold-corridor-first-failure` (F3): "two prefixes have the
  same exact target response against every outside context and **one gives a
  strictly smaller proper representative**".  `lem:cold-corridor-first-failure`
  (iii): "case (F3) is a target-complete compression of a proper support",
  because "context-universality holds and the displayed representative is
  strictly smaller while preserving the boundary-degree profile and the exact
  target response.  Thus it satisfies `def:proper-quotient-representative` and is
  forbidden by `lem:replacement`, `cor:uncompressible`".
- **What the Lean does.** `Corridor.FirstFailureCompression` carries the
  *pair*.  `stage` is the later prefix, `candidate` the earlier one, `earlier`
  is `candidate < stage` along the corridor, and `sameState` is the equality of
  their cold corridor states — which is what makes them same-interface.  The
  remaining fields are `def:proper-quotient-representative` clause by clause:
  `replacement` is the candidate's own boundary piece at the stage's interface,
  `sameProfile` preserves the boundary-degree profile, `baseline` keeps the
  standing hypothesis, `smaller` is the strict lexicographic decrease, and
  `contextUniversal` is equality of target response against *every* outside
  context.
  `FirstFailureCompression.compressibleSupport` reads those fields off as a
  `Strategy.InterfaceReplacement.CompressibleSupport` at the stage's own support
  — nothing is rebuilt and no existential is invented — and
  `FirstFailureCompression.elim` / `not_occurs` close it against node `[14]`.
  `Spine.coldFailureCompressionRow` commits that (F3) never occurs.
- **What it should do.** Exactly this: relate the two prefixes, with the
  candidate's piece as the smaller representative and the state equality doing
  the same-interface work.
- **Gap.** none.  The gap the previous implementation had — a bare existential
  over boundary pieces at the later prefix's support, with the two
  corridor-state conjuncts inert — is gone: `candidate` is a field, `earlier`
  and `sameState` are used to type and justify the replacement, and the
  conversion to `CompressibleSupport` is by projection.  **Facts passes.**
- **Ledger and residual.** `coldFailureCompressionRow` is `factOnly` with
  `Requires := [uncompressible]`, `Produces := [coldFailureCompression]`.  Node
  `[14]`'s exclusion is read by exact key; nothing else is consumed.  Residual
  unchanged.
- **Transport and terminals.** `Graph.ColdFirstFailure` owns the mathematics.
  `Spine.runCold` runs it fifth.  No terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:cold-corridor-first-failure` (F3) | def | `ColdCorridor.Corridor.FirstFailureCompression`<br>`ColdCorridor.Corridor.FirstFailureCompression.Occurs` | no CT — `Spine.coldFailureCompressionRow` |
| `lem:cold-corridor-first-failure` (iii) | lem | `ColdCorridor.Corridor.FirstFailureCompression.compressibleSupport`<br>`ColdCorridor.Corridor.FirstFailureCompression.elim`<br>`ColdCorridor.Corridor.FirstFailureCompression.not_occurs` | standalone |

`def:proper-quotient-representative` and `cor:uncompressible` are the
interface-replacement rows' objects; this row consumes them through
`CompressibleSupport` and node `[14]`'s committed fact.

**CT composition at this row.** No CT.  The clause is a record whose fields are
already the compression's clauses, and its elimination is one application of the
node-`[14]` fact.  `InterfaceReplacement` composes CT7 upstream, at the row that
proved `uncompressible`; re-entering it here would prove the same thing twice.

### Row 48 — (F4) producer `[154]`, `[156]`

- **Paper fact.** `def:cold-corridor-first-failure` (F4): "the corridor first
  enters a declared Type B handoff envelope or the route-8 carrier support
  already recorded in the branch state".  `lem:cold-corridor-first-failure`
  (iv): "the corridor has reached precisely one of the declared interfaces of
  `def:decorated-fan-envelope` or the route-8 carrier support, so the charge is
  transferred to the already existing Type B or route-8 ledger".
- **What the Lean does.** `Corridor.HandoffEnvelopes` is the declared interfaces
  the branch has recorded: an envelope type, a declared support per envelope,
  and pairwise disjointness of those supports.
  `Corridor.FirstFailureHandoff` is clause (F4) with "first" encoded: the
  prefix's head lies in some declared support, *and* no earlier prefix's head
  lies in any of them.
  `Corridor.exists_unique_handoff` is clause (iv)'s "precisely one" — disjoint
  supports make the envelope unique, so it is a theorem and not a convention.
  `Spine.coldFailureHandoffRow` commits it, quantified over every ledger.
- **What it should do.** Exactly this, with the ledger supplied by the branch.
- **Gap.** none.  The gap the previous implementation had — the schedule was
  literally `Enumeration.empty` on the executing branch, so (F4) could never
  fire — is impossible here: the ledger is universally quantified in the
  committed statement, so the fact holds at *every* ledger the branch might
  carry, including every nonempty one, and no row manufactures one.
  **Facts passes.**
- **Ledger and residual.** `coldFailureHandoffRow` is `factOnly` with
  `Requires := [coldCorridorState]`, `Produces := [coldFailureHandoff]`.
  Residual unchanged.
- **Transport and terminals.** `Graph.ColdFirstFailure` owns the mathematics.
  `Spine.runCold` runs it sixth.  The (F4) transfer itself is Row 49.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:cold-corridor-first-failure` (F4) | def | `ColdCorridor.Corridor.HandoffEnvelopes`<br>`ColdCorridor.Corridor.FirstFailureHandoff` | no CT — `Spine.coldFailureHandoffRow` |
| `lem:cold-corridor-first-failure` (iv) | lem | `ColdCorridor.Corridor.exists_unique_handoff` | standalone |

`def:decorated-fan-envelope` supplies the declared interfaces this row tests;
it lies outside the `[145]`–`[157]` range and belongs to the Type B rows, so the
ledger enters here as the parameter the manuscript says it is — "already
recorded in the branch state".

**CT composition at this row.** No CT.  The clause is a first-entry test against
a supplied finite family and its routing is a uniqueness argument from
disjointness.

### Row 49 — (F4) handoff exit `[156]`

- **Paper fact.** `lem:cold-corridor-first-failure` (iv), the transfer clause:
  the (F4) charge is moved to the already existing Type B or route-8 ledger and
  is not closed at the corridor.
- **What the Lean does.** `Corridor.handoffExit` produces, from an (F4)
  occurrence, a value of
  `{envelope : ledger.Envelope // corridor.head segment ∈ ledger.support envelope}`
  — the declared envelope the corridor entered, carrying its own membership and
  nothing else.  `handoffExit_mem` is that membership and
  Row 48's committed `exists_unique_handoff` already says that envelope is the
  only declared interface the corridor reached, so nothing restates it here.  `Spine.firstFailureHandoffExit` is the same value read at a
  `SurvivingColdBranch`'s own recorded ledger, which is where the charge
  actually goes.
- **What it should do.** Exactly this, *and* be reachable from the (F4) arm.
- **Gap.** none.  The previous implementation's exit was never constructed on
  any branch; this one is the elimination of the (F4) clause the row above
  commits, and `ColdCorridor.firstFailureHandoffExit` takes the branch's own
  `handoffEnvelopes` field, so the transfer target is the recorded envelope
  family and not a manufactured one.  Nothing is closed at the corridor: the exit carries an
  envelope, not a target proof.  **Facts passes.**
- **Ledger and residual.** The exit is a consequence of the (F4) fact rather
  than a fact of its own — it carries an envelope, which is data, and no fact may
  carry data.  What the ledger records is the uniqueness statement of Row 48.
- **Transport and terminals.** No CT.  The carrier is the subtype above; the
  branch's `HandoffEnvelopes` is the framework-side destination.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:cold-corridor-first-failure` (iv), transfer | lem | `ColdCorridor.Corridor.handoffExit`<br>`ColdCorridor.Corridor.handoffExit_mem`<br>`ColdCorridor.firstFailureHandoffExit` | standalone |

**CT composition at this row.** No CT.  The transfer is a projection of the
(F4) occurrence onto the envelope it named.

### Row 50 — Core classified state `[154]`

- **Paper fact.** `lem:cold-corridor-first-failure`: "for every
  `\epsilon \in \mathcal E_{br}`, the cold return corridor of `\epsilon` has a
  first failure", routed by (i)–(v).  The existence half is proved by following
  initial segments: if the successor stub is reached before `Q_cold+1` states are
  read the whole corridor has at most `M_cold = Q_cold + 30` vertices, otherwise
  two of the `Q_cold+1` states are equal and the first equality gives the repeat
  subcase of (F5).  The branch hypothesis is `def:surviving-cold-branch` (i)–(vi).
  `def:cold-window-ledger` fixes `c_hot`, `\theta_{win} = 3/(2c_{hot})`,
  `\tau(\theta) = 15\theta/(1-13\theta)` with `\tau(\theta) < 1/4 \iff \theta <
  1/73` and `\tau(\theta) < 3/13 \iff \theta < 1/78`, and splits
  `\mathcal P = \mathcal P_{hot} \sqcup \mathcal P_{cold}` with
  `C := |\mathcal P_{cold}|`.  `def:cold-skeleton-excess` sets
  `b(P) := \max\{0, s(P)-2\}` after naming the first two lexicographic stubs the
  transit stubs, and `lem:cold-window-stub-excess` gives
  `b(\mathfrak S_{cold}) \ge 13C - o(n)`.
- **What the Lean does.**
  `Corridor.statesRead` is the number of cold corridor states a corridor reads,
  one per initial segment.  `Corridor.TerminalCorridor` is (F5)'s first subcase —
  the successor stub is reached inside `Q_cold` states — and
  `Corridor.RepeatedState` its second.
  `Corridor.exists_firstFailure` is the existence half, proved as the
  manuscript's own dichotomy: a `by_cases` on `statesRead ≤ Q_cold`, with the
  negative branch sampling `Q_cold + 1` distinct segments and applying
  `Presentation.exists_state_eq_of_stateBound_lt`.  **(F5) is not defined as the
  complement of the other four clauses**, so the conclusion is a theorem about
  the corridor's length and not a tautology.
  `Corridor.exchange_card_le` is "`M_cold` is a uniform upper bound for the
  number of vertices in a first-failure cold exchange": in the terminal subcase
  the corridor's states plus the manuscript's `30 = 2·order + 2·2` fit inside
  `exchangeBound`.
  `ColdCorridor.TauBelow`, `tauBelow_iff`, `tauBelow_quarter` and
  `tauBelow_routeEight` are `def:cold-window-ledger`'s comparisons, cleared of
  denominators: `τ(θ) < 1/4` is `(5s − 2)·p < n` and `τ(θ) < 3/13` is
  `(16s − 6)·p < 3n`, at an arbitrary external-stub count `s`.
  `Fixtures.ColdCorridorLedger` evaluates them at the manuscript's own
  `s = δ·order − 2(order−1) = 15`, where they become `73·p < n` and `78·p < n`;
  so `73` and `78` are checked consequences of the registered baseline and
  window order and appear in no definition.  `isHot`, `coldWindows`, `hotWindows`, `coldCount` and
  `coldCount_add_hotCount` are the hot/cold split: hotness is *decided* by the
  two clauses the manuscript gives (the full canonical package is present, and
  its coordinates are distinct), and `𝒫 = 𝒫_hot ⊔ 𝒫_cold` is a partition
  theorem.
  `branchExcessOf`, `selectedBranchExcess` and `selectedBranchExcess_length` are
  `def:cold-skeleton-excess`: `b(P) = s(P) − 2` and the selected half-edges are
  the stubs with the two transit stubs dropped, with `|𝓔_br(P)| = b(P)` proved.
  At the registered baseline and order, `s(P) = δ·order − 2(order − 1)` — the
  same expression node `[28]` compares — and `branchExcessOf` of it *is* `b(P)`
  by definition, so no lemma restates that; `Fixtures.ColdCorridorLedger`
  evaluates both to the manuscript's `15` and `13`.
  `branchExcess_ge_of_cubic` is `lem:cold-window-stub-excess`
  subtraction-free.
  `ColdCorridor.SurvivingColdBranch` is `def:surviving-cold-branch`, with the
  branch's own `Identified` relation so that clause (ii) constrains something,
  and with `germIdentified` recording that a bounded germ's two representatives
  are one of those identifications — which is what `def:cold-bounded-germ` says
  a germ is.  That pair of fields is what lets `SurvivingColdBranch.noGermDefect`
  be a *theorem*: G2's routing is derived from clause (ii) rather than assumed
  as a separate exclusion.
  Of the four routing clauses only (F2)'s and (F4)'s are theorems against the
  branch record, because only those two are not proved anywhere earlier: (F1)
  and (F3) are committed at Rows 45 and 47 from the selection's own target
  avoidance and from `cor:uncompressible`, so restating them against
  `SurvivingColdBranch` would prove the same theorem twice.  The three
  declarations that did — `not_firstFailureCycle`, `not_firstFailureCompression`
  and the `firstFailure_routed` conjunction that packaged them with
  `exists_firstFailure` — had no consumer and are deleted.
  `Spine.coldFailureRoutingRow` commits the existence dichotomy, the `M_cold`
  bound, the hot/cold partition and the stub-excess inequality.
- **What it should do.** Exactly this: prove existence from the pigeonhole,
  record the hot/cold ledger, and count the branch excess.
- **Gap.** none.  The three gaps the previous implementation had are closed:
  exhaustiveness is no longer by construction (`f5` was the complement of the
  other four, making the lemma a tautology) but a case split on the corridor's
  length against `Q_cold`; the hot/cold split of `def:cold-window-ledger` is
  present and decided, so the cold family is named rather than the whole
  packing; and the stub count is `b(P) = s(P) − 2` at the registered baseline
  and order with an explicit `o(n)` slack term in `branchExcess_ge_of_cubic`
  rather than an exact fully-cubic identity.  `def:surviving-cold-branch` is a
  named structure, and the branch clauses each row actually spends are read from
  the canonical ledger instead — node `[1]`'s avoidance for (F1) and node
  `[14]`'s uncompressibility for (F3) — which is stronger than assuming them.
  **Facts passes.**
- **Ledger and residual.** `coldFailureRoutingRow` is `factOnly` with
  `Requires := [coldCorridorState]`, `Produces := [coldFailureRouting]`.  The
  cut-state fact is read by exact key; the five committed clauses are theorems
  about the corridor and the registered signature — the existence dichotomy, the
  `M_cold` bound, the hot/cold partition, `|𝓔_br(P)| = b(P)`, and the stub
  excess.  The fourth was proved but unregistered until the registered-fact
  review.  Residual unchanged.
- **Transport and terminals.** `Graph.ColdFirstFailure` owns the mathematics;
  `Spine.runCold` runs this row last, so the block's output index is the
  incoming one with seven cold facts on top.  No terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:cold-window-ledger` | def | `ColdCorridor.TauBelow`<br>`ColdCorridor.tauBelow_iff`<br>`ColdCorridor.tauBelow_quarter`<br>`ColdCorridor.tauBelow_routeEight`<br>`ColdCorridor.isHot`, `ColdCorridor.isHot_iff`<br>`ColdCorridor.coldWindows`, `ColdCorridor.hotWindows`<br>`ColdCorridor.coldCount`<br>`ColdCorridor.coldCount_add_hotCount` | no CT |
| `def:surviving-cold-branch` | def | `ColdCorridor.SurvivingColdBranch` | no CT |
| `def:cold-skeleton-excess` | def | `ColdCorridor.branchExcessOf`<br>`ColdCorridor.selectedBranchExcess`<br>`ColdCorridor.selectedBranchExcess_length` | no CT |
| `lem:cold-window-stub-excess` | lem | `ColdCorridor.branchExcess_ge_of_cubic`<br>checked at `s = 15`, `b(P) = 13` in `Fixtures.ColdCorridorLedger` | standalone |
| `lem:cold-corridor-first-failure` | lem | `ColdCorridor.Corridor.statesRead`<br>`ColdCorridor.Corridor.TerminalCorridor`<br>`ColdCorridor.Corridor.RepeatedState`<br>`ColdCorridor.Corridor.exists_firstFailure`<br>`ColdCorridor.Corridor.exchange_card_le` | no CT — `Spine.coldFailureRoutingRow` |

The routing clauses (i)–(iv) are consumed at Rows 45–49; the existence half and
the two ledgers are this row's.

**CT composition at this row.** No CT.  Every step is a finite search, a
cardinality argument, or a partition count: the existence half is a `by_cases`
plus `Fintype.exists_ne_map_eq_of_card_lt`, the hot/cold split is
`Finset.card_filter_add_card_filter_not`, and the stub excess is one
multiplication inequality.  Nothing compares responses here — that happened at
Rows 46 and 47 — so no CT participates.


### Row 51 — Terminal-F5 residual `[154]`

- **Paper fact.** `lem:cold-corridor-first-failure` (v), terminal subcase: "the
  whole corridor has bounded size and two boundary interfaces … the support
  carries two same-interface representatives … Thus it is a cold bounded germ",
  feeding `lem:cold-germ-extraction` rather than closing anything.  The bound is
  `M_cold = Q_cold + 30` vertices.  `def:cold-bounded-germ` fixes what the
  residual must be: "a finite boundaried support with two boundary interfaces
  `x, y` and two same-interface `x`-`y` representatives `Q[x,y]` and `E`", where
  "in a terminal corridor these representatives are the two bounded completion
  strands between the same interfaces; in a repeated-state corridor one
  representative is the actual corridor segment and the other is the canonical
  representative determined by the repeated cold corridor state", carrying the
  inherited boundary degree profile, `P13`-window labels and target-response
  profile, with increment `\delta := |E| - |Q[x,y]|`, *length-changing* if
  `\delta \ne 0` and *equal-length* if `\delta = 0`.
- **What the Lean does.** The residual is `ColdCorridor.BoundedGerm
  data.coldSignature (MinimumDegreeAtLeast threshold) (HasCycleWithLength
  LengthOK) object`, and it is the definition itself: the proper support with
  its own boundary piece `Q[x,y]`, the second same-interface representative
  `canonical`, `sameProfile` for the inherited boundary-degree profile, `record`
  and `record_truth` for the `P13`-window labels and the target-response
  profile, and `BoundedGerm.increment` for `\delta` in `Int`.  The
  length-changing/equal-length dichotomy is `BoundedGerm.LengthChanging` with
  `not_lengthChanging_iff`, committed at Row 54.
  The boundedness is Row 50's: `coldFailureRouting`'s second clause is
  `Corridor.exchange_card_le`, `corridor.statesRead + interfaceBudget S ≤
  exchangeBound S`, which is `M_cold = Q_cold + 30` with the additive `30`
  supplied by `interfaceBudget` and never written as a numeral; the two boundary
  interfaces are bounded by `Corridor.activeInterface_card_le`.  The
  terminal/repeated split that produces the two representatives is
  `Corridor.TerminalCorridor` / `Corridor.RepeatedState`, the two arms of
  `Corridor.exists_firstFailure`, also committed at Row 50.
- **What it should do.** Exactly this.  The residual is not closed here — the
  three arms of `lem:cold-bounded-germ-trichotomy` at Rows 52--54 close it, and
  `lem:cold-germ-extraction` at Row 58 counts it.
- **Gap.** `none`.  **Facts passes.**  The legacy
  `ColdBranchFailureRouting.storedTerminalF5GermFacts` — a conjunction of a
  schedule-cardinality bound with an equality of two ambient `Bool`s, carrying no
  support and computing no `\delta`, and with no occurrence outside its own
  definition — is retired: `Graph.Strategy.ColdBranchFailureRouting` is
  quarantined together with the three modules that depended on it.
- **Ledger and residual.** No fact carries a germ: `BoundedGerm` is *data*, and
  every clause about it is quantified over every germ of the residual's own
  object.  The bound and the split are read from the `coldFailureRouting` fact
  committed at Row 50; the three closure arms are the `coldGermRealized`,
  `coldGermDistinguished` and `coldGermSilent` facts of Rows 52--54.  All five
  sit on one immutable prefix, so a germ statement proved at any of them is
  readable at every later cursor of the branch.
- **Transport and terminals.** `Graph.ColdCorridor` owns the germ and the bound;
  `Graph.ColdFirstFailure` owns the terminal/repeated dichotomy.  There is no
  terminal at this row — the residual is handed on, which is what the manuscript
  says of the terminal subcase.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:cold-bounded-germ` | def | `ColdCorridor.BoundedGerm`<br>`BoundedGerm.increment`<br>`BoundedGerm.LengthChanging`<br>`BoundedGerm.not_lengthChanging_iff`<br>`Corridor.exchange_card_le`<br>`Corridor.activeInterface_card_le` | no CT — `Spine.coldFailureRoutingRow`, `Spine.coldGermRealizedRow`, `Spine.coldGermDistinguishedRow`, `Spine.coldGermSilentRow` |

The definition is carried here and *spent* at Rows 52--54; `ColdCorridor.TableRow`
is the same structure with `\delta = 0` and `def:admissible-rank-quotient`
added, so Row 44's equal-length half and this row's length-changing half share
one carrier and one increment.

**CT composition at this row.** No CT.  The germ is a structure, its bound is an
inequality on a `Fintype.card`, and its two representatives come from a case
split on the corridor's own length.  There is nothing to enumerate, schedule or
certify.

### Row 52 — `[155]` G1 realizing

- **Paper fact.** `lem:cold-bounded-germ-trichotomy` states that no
  length-changing cold bounded germ survives, and splits every such germ into
  G1, G2, G3, exhaustive "by whether a compatible completion realizes a dyadic
  hit, distinguishes dyadic truth without realization in `G`, or never
  distinguishes the two representatives".  G1, *hit-realized*: "some compatible
  live completion and window offset close a dyadic cycle.  This contradicts the
  counterexample condition", proved by "the completed representative plus the
  relevant window segment is a cycle whose length is a power of two".
- **What the Lean does.** `Graph.ColdCorridor.BoundedGerm S Baseline Target
  object` is `def:cold-bounded-germ` itself: the support with its connectedness
  and properness, the second same-interface representative `canonical`, the
  inherited boundary-degree profile `sameProfile`, the standing baseline, and
  the `(T1)`--`(T4)` recording `record`/`record_truth` that the definition's
  "inherited boundary degree profile, `P₁₃`-window labels, and target-response
  profile" names.  `BoundedGerm.increment` is `δ := |E| − |Q[x,y]|` in `Int`;
  nothing stores it, so no germ may declare a length change it does not have.
  `BoundedGerm.Realizing` is `Target (glue germ.piece germ.atom.outside)`.
  `Spine.coldGermRealizedRow` is a `factOnly` atomic Strategy with
  `Requires := [selection]` and `Produces := [coldGermRealized]`.  Its two
  committed clauses are `∀ germ, ¬ germ.Realizing`, proved by
  `BoundedGerm.target_of_realizing` against the selection's own avoidance, and
  `∀ germ, germ.Realizing ∨ germ.Distinguishing ∨ germ.Neutral`, which is
  `BoundedGerm.trichotomy`.
- **What it should do.** Exactly this.  `target_of_realizing` transports the
  germ's own completion to the ambient object along the decomposition's
  `reconstructionIso`, which is the manuscript's "the completed representative
  plus the relevant window segment is a cycle whose length is a power of two"
  read at the germ's own site.
- **Gap.** `none`.  **Facts passes.**
- **Ledger and residual.** The row reads node `[1]`'s `selection` by exact
  semantic key through `FactInputs.get` and commits `coldGermRealized` into the
  same indexed `ExactLedger`; `factOnly` supplies `RefinementSystem.refl`, so
  the residual is unchanged.  The statement is quantified over *every*
  `BoundedGerm` of the residual's own object, so no germ construction travels
  with the fact.
- **Transport and terminals.** `Graph.ColdCorridor` owns the mathematics and the
  row owns nothing but the commit.  There is no terminal at this row: G1 is
  proved never to occur, and the branch continues.  The row is run by
  `Spine.runCold` through `AtomicCT.run` against one immutable prefix.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:cold-bounded-germ` | def | `ColdCorridor.BoundedGerm`<br>`BoundedGerm.increment`<br>`BoundedGerm.LengthChanging`<br>`BoundedGerm.atom`<br>`BoundedGerm.piece` | no CT — `Spine.coldGermRealizedRow` |
| `lem:cold-bounded-germ-trichotomy` | lem | `BoundedGerm.Realizing`<br>`BoundedGerm.Distinguishing`<br>`BoundedGerm.Neutral`<br>`BoundedGerm.trichotomy`<br>`BoundedGerm.target_of_realizing` | no CT — `Spine.coldGermRealizedRow` |

`def:cold-bounded-germ` is first *carried* here.  Row 51 consumes its terminal
subcase and Row 44 its equal-length one: `ColdCorridor.TableRow` is now literally
`BoundedGerm` with `δ = 0` and `def:admissible-rank-quotient` added, so the two
halves of the definition share one carrier and the increment is the same
declaration on both.  The trichotomy is recorded here because its G1 arm is the
first of the three consumed; its G2 arm is Row 53's and its G3 arm Row 54's.

**CT composition at this row.** No CT.  Both clauses are theorems about the germ
itself: one transports a completion along the decomposition's reconstruction
isomorphism, the other is the excluded middle on two predicates.  A CT would add
nothing — there is no response algebra to schedule and no residual to restrict.

### Row 53 — `[156]` G2 distinguishing

- **Paper fact.** `lem:cold-bounded-germ-trichotomy` G2, *hit-distinguished*:
  "some compatible outside context distinguishes the two representatives by
  dyadic truth value **without already realizing the cycle in the current
  graph**.  The induced quotient is target-defective, so it is routed to the
  sparse exit or exit-(4) ledger", proved by "the two local responses agree in
  the actual quotient but disagree in a compatible context.  By
  `lem:context-universality`, such an identification is not target-complete".
- **What the Lean does.** `BoundedGerm.Distinguishing` is
  `Graph.Response.TargetDefect Target germ.piece germ.canonical`, an *actual*
  `Graph.OutsideContext` of the germ's own interface separating the two
  representatives' target values — not a scheduled coordinate family and not a
  pair of ambient `Bool`s.  `Spine.coldGermDistinguishedRow` is a `factOnly`
  atomic Strategy with `Requires := []` and
  `Produces := [coldGermDistinguished]`, committing
  `∀ germ, ∀ (Profile : Type) (profile : BoundaryPiece germ.atom.interface →
  Profile), germ.Distinguishing → ¬ Graph.Response.TargetComplete profile Target
  germ.piece germ.canonical`, proved by
  `BoundedGerm.not_targetComplete_of_distinguishing`: the separating context
  already denies the all-context clause of `def:target-complete-quotient`.
- **What it should do.** Exactly this.  The conclusion is drawn in *every*
  immutable profile fibre, which is what makes it a statement about the
  quotient rather than about one chosen profile, and it is the same shape node
  `[156]` already commits for the (F2) discrepancy at Row 49.  No cycle is
  claimed: the manuscript is explicit that G2 distinguishes "without already
  realizing the cycle in the current graph", and what the germ is routed to is
  the defect exit.
- **Gap.** `none`.  **Facts passes.**
- **Ledger and residual.** The row reads nothing, and `Requires := []` is the
  honest declaration: target-defectiveness of a distinguished germ is a theorem
  about the germ's own two representatives, and the branch facts are spent by
  the other two arms.  The framework runner still appends the production to the
  incoming index while retaining the literal ancestry, so every earlier fact of
  the branch stays in the output type; `factOnly` supplies the equality
  refinement.
- **Transport and terminals.** `Graph.Response` owns target-completeness and its
  defect; `Graph.ColdCorridor` owns the germ.  No terminal: the row records the
  routing, and the exits it routes to are the branch's own.

**Paper objects at this row.**

No manuscript object is first consumed here.  The G2 arm of
`lem:cold-bounded-germ-trichotomy` is recorded at Row 52;
`lem:context-universality`, which G2's proof invokes, lies outside the
`[145]`--`[157]` range and is `Graph.Response.TargetComplete`'s own
context-universality clause.

**CT composition at this row.** No CT.  What a CT would buy here is a response
comparison across a *scheduled* family of contexts, and the manuscript does not
ask for one: G2's hypothesis is the existence of a single distinguishing
compatible context, which `Response.TargetDefect` is, and its conclusion is the
failure of a two-clause conjunction at that one witness.

### Row 54 — `[157]` G3 neutral

- **Paper fact.** `lem:cold-bounded-germ-trichotomy` G3, *silent*: "no compatible
  outside context and no relevant scale distinguishes the two representatives.
  Then replacing the longer representative by the shorter one preserves the
  boundary degree profile and the target response against every context, creates
  no dyadic cycle, and strictly decreases the support.  This is a nontrivial
  target-complete compression of a proper support", forbidden by
  `lem:replacement` and `cor:uncompressible`.  The "longer/shorter" is supplied
  by `lem:cold-increment-arithmetic`, which exhausts the finite arithmetic of the
  increment `δ ≥ 0`: (a) `1 ≤ δ ≤ 12` gives overlapping blocks
  `[L+jδ, L+jδ+12]` whose union is an interval — G1 if it spans a
  dyadic scale, otherwise a bounded germ type handled by the trichotomy;
  (b) `δ ≥ 13` with the doubling orbit hitting one of the thirteen smear
  residues gives G1; (c) `δ ≥ 13` avoiding them gives a periodic carrier
  on the odd part, G2 if target-visible and G3 if target-invisible;
  (d) `δ = 0` sends the equal-length switch to the finite same-interface
  table.  For odd `δ`, `ord_δ(2) > δ − 13` forces case (b), and for even
  `δ = 2^a u` the criterion applies to the odd part after the transient `k < a`.
- **What the Lean does.** `Spine.coldGermSilentRow` is a `factOnly` atomic
  Strategy with `Requires := [uncompressible]` and
  `Produces := [coldGermSilent]`.  Its six committed clauses are:
  1. G3 itself, `∀ germ, germ.increment < 0 → ¬ germ.Neutral`, by
     `BoundedGerm.compressibleSupport_of_not_distinguishing` against node
     `[14]`'s exclusion.  Every clause of
     `InterfaceReplacement.CompressibleSupport` is present: `sameProfile` is the
     preserved boundary-degree profile, `baseline` the standing baseline, the
     failure of `Distinguishing` the target response against every context, and
     the strict decrease is
     `BoundedGerm.lexicographicallySmaller_of_increment_neg` — the shorter
     representative has strictly fewer internal vertices, so `glue_vertexCount`
     makes its completion strictly smaller than the object, which
     `reconstructionIso` identifies with the germ's own completion.
  2. Case (d), `BoundedGerm.not_lengthChanging_iff`: this is
     `def:cold-bounded-germ`'s own dichotomy — "length-changing if `δ ≠ 0`,
     equal-length if `δ = 0`" — and it says a germ fails to be length-changing
     exactly when its two representatives have the same internal size, which is
     `TableRow`'s `equalLength` clause.  So the germs that are *not*
     length-changing are exactly the rows of `def:cold-same-interface-table`,
     closed at Row 44: "the equal-length switch belongs to the finite
     same-interface cold table".
  3. Case (a), `ColdCorridor.exists_not_survivesSmear_of_mem_interval`: for
     `0 < δ ≤ smear + 1` the blocks `[L+jδ, L+jδ+smear]` cover the interval
     `[L, L + Nδ + smear]`, so an accepted length in that interval makes one
     block fail the smear filter — the offset that closes the cycle, G1.
  4. Case (b), `ColdCorridor.exists_not_survivesSmear_of_pow_congruent`: a power
     of two congruent to a smear residue and at least as large is attained by the
     block of the corresponding number of homogeneous copies, so if it is
     accepted that block fails the filter, G1.
  5. The hit criterion, `ColdCorridor.exists_hit_of_orderOf_lt`: with
     `smear + 1 ≤ δ` the `smear + 1` residues `L, …, L+smear` are distinct
     classes, the doubling orbit contributes `orderOf (2 : ZMod δ)` distinct
     classes because `pow_injOn_Iio_orderOf` makes it injective below the order,
     and an orbit exceeding the complement cannot avoid them.
  6. The even transient, `ColdCorridor.pow_mod_of_le`:
     `2^k % (2^a·u) = 2^a·(2^(k−a) % u)` for `k ≥ a`, the exact reduction to the
     odd modulus past the bounded transient.
  Case (c) is the trichotomy's own exhaustiveness and is committed at Row 52.
- **What it should do.** Exactly this.  Unlike the equal-length rows of
  `def:cold-same-interface-table`, the descent is the increment's own and no
  appeal to `def:admissible-rank-quotient` is made or needed, which is why
  `BoundedGerm` carries no `admissible` field and `TableRow` does.
- **Gap.** `none`.  **Facts passes.**  One qualification must be recorded: the
  germ is *oriented* as the manuscript orients it in
  `lem:cold-increment-arithmetic` — the support carries the longer
  representative and `canonical` the shorter, so `δ < 0` and "replacing the
  longer representative by the shorter one" is a replacement at this support.
  A germ whose support carries the shorter representative is the same germ at
  the other site, and it is that site's `BoundedGerm` the clause applies to.
- **Ledger and residual.** The row reads node `[14]`'s `uncompressible` by exact
  semantic key through `FactInputs.get` and commits `coldGermSilent` into the
  same indexed `ExactLedger`; `factOnly` supplies the equality refinement.  The
  arithmetic clauses quantify over the increment, the base length, the copy
  count and the exponent, and mention the smear only as
  `data.coldSignature.windowOrder − 1`, so the manuscript's `12` and `13` are
  the registered window order and no numeral is written.
- **Transport and terminals.** `Graph.ColdCorridor` owns both the germ's
  compression and the increment arithmetic; the row owns nothing but the commit.
  No terminal: G3 is proved never to occur.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:cold-increment-arithmetic` | lem | `ColdCorridor.exists_block_of_mem_interval`<br>`ColdCorridor.exists_not_survivesSmear_of_mem_interval`<br>`ColdCorridor.exists_block_of_pow_congruent`<br>`ColdCorridor.exists_not_survivesSmear_of_pow_congruent`<br>`ColdCorridor.exists_hit_of_injective`<br>`ColdCorridor.exists_hit_of_orderOf_lt`<br>`ColdCorridor.pow_mod_of_le`<br>`BoundedGerm.not_lengthChanging_iff` | no CT — `Spine.coldGermSilentRow` |

`lem:cold-increment-arithmetic` is placed at the closest row: it is the lemma
that decides which of G1/G2/G3 a length-changing germ falls into, and its case
(c) is what produces a G3 germ at all.  Its case (d) routes to
`def:cold-same-interface-table`, recorded at Row 44.

**CT composition at this row.** No CT.  The G3 clause is a replacement
certificate assembled from fields the germ already carries, and the remaining
five are arithmetic on `Nat` with the accepted-length predicate as a parameter.
There is no enumeration to schedule, no response algebra to compare, and no
residual to restrict; `Graph.ColdIncrementArithmetic` mentions no window,
corridor, germ, or graph at all.

### Row 55 — Core dispatch (F1) `[155]`

- **Paper fact.** `lem:cold-corridor-first-failure` (i) together with
  `lem:cold-bounded-germ-trichotomy` G1: an (F1) first failure is a dyadic cycle
  in `G`, which contradicts the counterexample condition and closes the branch.
- **What the Lean does.** Nothing at this row, and that is the port.  In the
  canonical spine there is no dispatch field: the (F1) fact is committed once, at
  Row 45, as `∀ corridor window segment, ¬ corridor.FirstFailureCycle window
  LengthOK segment`, read off node `[1]`'s `selection`; and the trichotomy's G1
  arm is committed once, at Row 52, as `∀ germ, ¬ germ.Realizing`.  What the
  legacy `LedgerProfile.outcome` did — match a stored `f1Owners` partition and
  return `Sum.inr (PLift.up target)` — is replaced by `Spine.runCold` composing
  the rows through `AtomicCT.run`: the (F1) clause is on the ledger, and any
  later row that needs it reads it by exact key.
- **What it should do.** Exactly this.  The legacy row's own **What it should
  do** asked for "read the stored (F1) partition off the entry just written, and
  on a nonempty partition return the target"; with the fact on the canonical
  ledger there is no partition to scan and no payload to return — the target
  cannot occur, which is strictly what the manuscript claims.
- **Gap.** `none`.  **Facts passes.**  The legacy path is retired:
  `Graph.Strategy.ColdBranchAggregation` and
  `Core.Strategy.ColdBranchAggregation` are quarantined, so
  `storedF1ForcesTarget`, `LedgerProfile.outcome` and the `Sum`-typed `Outcome`
  payload are out of the build.  This removes the audit's own former complaint
  that "the target lives in the payload type": there is no payload type.
- **Ledger and residual.** One immutable prefix, no second scan.  `AtomicCT.run`
  appends each row's production to the incoming index while retaining the
  literal ancestry, so Row 45's clause is in the type of every later cursor.
- **Transport and terminals.** No terminal.  `.targetClosed` was the legacy
  arm's name for a terminal the export never showed as closed; the ported branch
  closes at Row 61 instead, and closes to `False` rather than to a target
  payload.

**Paper objects at this row.**

No manuscript object is first consumed here.  Clause (i) of
`lem:cold-corridor-first-failure` is recorded at Row 50 and the G1 arm of
`lem:cold-bounded-germ-trichotomy` at Row 52.

**CT composition at this row.** No CT and no recipe.  The dispatch *is* the row
composition, which is the same structural answer Row 60 gives: each row's
`Requires` is discharged by instance resolution against the incoming index, so
the order is checked by the elaborator rather than chosen by a registration
field.

### Row 56 — Core dispatch (F3) `[157]`

- **Paper fact.** `lem:cold-corridor-first-failure` (iii): an (F3) first failure
  is a target-complete compression of a proper support, forbidden by
  `lem:replacement` and `cor:uncompressible`; the case is therefore impossible on
  the surviving branch.
- **What the Lean does.** Nothing at this row, for the same reason as Row 55.
  The (F3) fact is committed once, at Row 47, as `∀ corridor presentation index
  support, ¬ FirstFailureCompression.Occurs …`, proved by
  `FirstFailureCompression.not_occurs` against node `[14]`'s `uncompressible`
  read from the ledger; and the trichotomy's G3 arm is committed once, at Row 54.
  There is no `Option`, no `False.elim` into a `none`-carrying capability, and no
  `noBaselineProperSubgraph` supplied at a registration site.
- **What it should do.** Exactly this.
- **Gap.** `none`.  **Facts passes.**  The legacy row recorded a real defect —
  the *Official* registration's `inducedPathFamilyCapability` never read
  `storedF3OwnersQuery`, so an (F3) owner fell through to `none`.  That defect
  cannot be expressed in the port: `coldFailureCompression` is a declared
  production of `coldFailureCompressionRow` and the exact heterogeneous result
  type makes omitting it fail to elaborate.
- **Ledger and residual.** As Row 55: one prefix, `uncompressible` read by exact
  key at Row 47, nothing re-derived here.
- **Transport and terminals.** No terminal.

**Paper objects at this row.**

No manuscript object is first consumed here.  Clause (iii) of
`lem:cold-corridor-first-failure` is recorded at Row 50;
`def:proper-quotient-representative`, `lem:replacement` and `cor:uncompressible`,
which the exclusion consumes, lie outside the `[145]`–`[157]` range.

**CT composition at this row.** No CT and no recipe; see Row 55.

### Row 57 — (F4) dispatch arm `[156]`

- **Paper fact.** `lem:cold-corridor-first-failure` (iv) transfers the charge to
  the existing Type B or route-8 ledger, and `def:surviving-cold-branch` (iv)–(v)
  is the branch hypothesis that "no Type B bridge or handoff residual remains
  outside its ledger" and "no Type A route-8 residual remains outside
  `thm:large-budget-route8-only`".
- **What the Lean does.** `Spine.coldHandoffTransferRow` commits that the
  corridor's head lies in the declared support of the envelope
  `Corridor.handoffExit` names — `handoffExit_mem` — for *every*
  `HandoffEnvelopes`.  It is a parameter of the committed statement, so it
  is the branch's own recorded one, and the row cannot be discharged against an
  emptiness produced at a call site.
- **What it should do.** Consume the stored (F4) entry and hand it to the
  recorded ledger, under the branch fact that any such residual is already
  inside that ledger.
- **Gap.** none.  The gap the previous implementation had — the arm discharged
  an owner that the compiler's own `Enumeration.empty` had already made
  impossible, and on the `handoffRequired := true` route returned `none` and
  left the residual open — cannot arise: there is no schedule to manufacture,
  the ledger is universally quantified, and the committed statement is the
  transfer itself rather than an `Option`.  **Facts passes.**
- **Ledger and residual.** `factOnly` with
  `Requires := [coldFailureHandoff]`, `Produces := [coldHandoffTransfer]`; the
  (F4) fact is read by exact key through sealed `FactInputs.get`.  Residual
  unchanged.
- **Transport and terminals.** `Graph.ColdFirstFailure` owns the exit;
  `Spine.runCold` runs the row after the (F4) producer.  No terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:cold-corridor-first-failure` (iv), transfer | lem | `ColdCorridor.Corridor.handoffExit`<br>`ColdCorridor.Corridor.handoffExit_mem` | no CT — `Spine.coldHandoffTransferRow` |

**CT composition at this row.** No CT.  The transfer is a projection of the
(F4) occurrence onto the envelope it named; nothing is searched or compared.

### Row 58 — (F5) `.isFalse` arm `[153]`, `[154]`

- **Paper fact.** `lem:hot-failure-cold-mass`: on `def:surviving-cold-branch`, if
  the live-hot entropy comparison does not close then
  `C \ge (\theta - \theta_{win})n - o(n)`.  `lem:cold-germ-extraction`: the cold
  skeleton with branch excess `b` contains a pairwise vertex-disjoint family of
  candidate cold bounded germs of size `N_{germ} \ge b/D_{cold} - o(n)`, proved
  by bounding each germ by `M_cold` vertices, bounding the number of candidate
  germs meeting a fixed subcubic vertex by `B_cold`, and applying greedy
  independence in the intersection graph of maximum degree `M_cold B_cold`.
  `thm:cold-branch-quantitative-closure` then observes that the bound is
  positive for large `n`, "hence at least one bounded candidate germ is present
  on every remaining branch".
- **What the Lean does.**
  `ColdCorridor.hotFailure_coldMass` is the mass bound with every `log₂ n`
  cancelled: given the partition `𝒫 = 𝒫_hot ⊔ 𝒫_cold` and the hot comparison
  that has *not* closed, `hotRate·|𝒫| ≤ hotRate·C + (skeletonRate·n + slack)` —
  the cold count carries everything the hot budget could not.  Subtraction-free,
  no rational, no rounding.
  `ColdCorridor.exists_independent_card_le_mul` is the greedy extraction, and it
  is the manuscript's own argument: take a member, discard it and everything it
  overlaps, recurse.  Stated for an arbitrary finite family and symmetric
  overlap relation of maximum degree `Δ`, with the conclusion
  `|family| ≤ |independent|·(Δ+1)` — the manuscript's division by `Δ+1`,
  cleared.  `ColdCorridor.coldGermExtraction` instantiates it at
  `Δ = M_cold·B_cold`, so the covering constant is exactly
  `D_cold = extractionDenominator`, and *that* is the form the row commits: the
  generic bound is the lemma, the manuscript's statement is the fact.
  `ColdCorridor.coldGerm_nonempty` is the positivity: a positive candidate count
  forces a positive disjoint count, so the (F5) partition is never empty.
  `Spine.coldGermExtractionRow` commits all three.
- **What it should do.** Make the arm unreachable: a proof that the surviving
  partition is nonempty, obtained by instantiating the germ packing over the
  family schedule and combining it with a linear lower bound on the cold family.
- **Gap.** none.  The gap the previous implementation had — the germ-packing
  declarations existed but "grep finds no occurrence of any of them outside
  `InducedPathCold.lean`", so nothing excluded an empty F5 partition — is
  closed: the greedy bound is proved here, the manuscript's `D_cold` form of it
  is what the row commits, and the positivity that makes the arm unreachable is
  a clause of the same fact.  The registered-fact review corrected one thing
  here: the committed clause first stated the generic bound at an arbitrary
  degree, leaving `lem:cold-germ-extraction`'s own statement proved but
  unregistered and its theorem a dead forwarder; the clause is now the
  manuscript's, at `M_cold·B_cold` and `D_cold`.
  Three inputs are quantified rather than pinned, and none is a fabricated
  value: the `o(n)` slack terms, the rates `c_hot` and the near-cubic `3/2`, and
  the subcubic ball count `1 + 3(2^{M_cold+2} − 1)` behind `B_cold`.  Each
  appears as a universally quantified parameter of the committed clause, so the
  fact holds whatever they are and nothing on the ledger depends on a number
  nobody has pinned — the opposite of a placeholder.  **Facts passes.**
- **Ledger and residual.** `factOnly` with
  `Requires := [coldFailureRouting]`, `Produces := [coldGermExtraction]`.
  Residual unchanged.
- **Transport and terminals.** `Graph.ColdBranchClosure` owns the mathematics
  and uses no framework plumbing at all — only Mathlib `Finset`/`Nat` and the
  cold-corridor definitions.  `Spine.runCold` runs the row.  No terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:hot-failure-cold-mass` | lem | `ColdCorridor.hotFailure_coldMass` | no CT — `Spine.coldGermExtractionRow` |
| `lem:cold-germ-extraction` | lem | `ColdCorridor.IndependentFor`<br>`ColdCorridor.exists_independent_card_le_mul` (the greedy bound)<br>`ColdCorridor.coldGermExtraction` (at `M_cold·B_cold`, covering `D_cold`)<br>`ColdCorridor.coldGerm_nonempty` | standalone — ports the quarantined `Core.Finite.ColdCorridor.supportPacking_card_bound` |

**CT composition at this row.** No CT.  The extraction is a greedy induction on
a `Finset` and the mass bound is one inequality; neither searches a schedule nor
compares responses.

### Row 59 — (F5) `.neutral` arm `[157]`

- **Paper fact.** `lem:cold-bounded-germ-trichotomy` G3 and
  `lem:cold-same-interface-table`'s neutral-row clause: a neutral germ or row
  yields a proper-support target-complete quotient, which
  `def:admissible-rank-quotient` admits only with a strictly smaller proper
  representative, forbidden by `lem:replacement` and `cor:uncompressible`.
  "Hence no neutral row survives either."
- **What the Lean does.** `ColdCorridor.boundedGerm_not_survives` runs the
  trichotomy and closes two of its three branches from facts *already on the
  ledger*: rows 52 and 54 committed "no germ is realizing" and "no
  length-changing germ is neutral" at nodes `[155]` and `[157]`, and this
  theorem reads them back by key rather than re-deriving them from the
  selection's avoidance and `cor:uncompressible`.  What survives is G2, and the
  conclusion is `germ.Distinguishing`.
- **What it should do.** Bind the neutrality certificate, build the germ's
  compression, and eliminate — rather than discard the certificate and return
  `none`.
- **Gap.** none.  The certificate is not discarded: `Neutral` is one of the
  three cases of `BoundedGerm.trichotomy` and the neutral case is *eliminated*
  against the committed row-54 fact.  There is no `none` arm.
  The registered-fact review corrected the *other* branch of that trichotomy
  here: G2's exclusion was briefly a field of `SurvivingColdBranch`, which
  assumed the conclusion of `lem:cold-bounded-germ-trichotomy` G2's own routing
  ("the induced quotient is target-defective, so it is routed to the sparse exit
  or exit-(4) ledger", both forbidden by clause (ii)).  It is now
  `SurvivingColdBranch.noGermDefect`, a theorem: the germ's pair is identified
  (`germIdentified`), a distinguishing germ separates it against a compatible
  outside context, and clause (ii) forbids exactly that.  **Facts passes.**
- **Ledger and residual.** The row that commits it, `Spine.coldBranchClosedRow`,
  is `factOnly` with
  `Requires := [coldGermRealized, coldGermSilent, selection, uncompressible]`;
  all four are read by exact key.  The last two entered when the table-row
  family was added to the committed closure — `row_closed` spends node `[1]`'s
  avoidance and node `[14]`'s uncompressibility.  Residual unchanged.
- **Transport and terminals.** No CT and no discarded payload.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:cold-bounded-germ-trichotomy` G2, routed | lem | `ColdCorridor.SurvivingColdBranch.germIdentified`<br>`ColdCorridor.SurvivingColdBranch.noGermDefect` | standalone |

The G3 arm of `lem:cold-bounded-germ-trichotomy` is recorded at Row 52, the
increment arithmetic that produces a G3 germ at Row 54, and the neutral-row
clause of `lem:cold-same-interface-table` at Row 44; this row is where the three
meet, and G2's routing is derived here.

**CT composition at this row.** No CT.  The previous implementation invoked CT7
here and threw its counted payload away; the port does not invoke it, because
the neutral case is closed by a committed fact rather than by a generated
certificate, and the manuscript's own argument is the trichotomy plus
`cor:uncompressible`.

### Row 60 — Registrations `atStage` `[145]`–`[157]`

- **Paper fact.** `thm:cold-branch-quantitative-closure` fixes what the branch
  boundary must deliver: on `def:surviving-cold-branch`, either the route-8
  carrier inequality closes `\theta < 1/78`, or the live-hot entropy comparison
  closes, or hot failure produces a cold family whose branch excess yields a
  bounded germ, and that germ is routed to a dyadic cycle, a target-defective
  quotient or exit-(4) route, a Type B handoff already in its ledger, a route-8
  closure, or a target-complete compression.
- **What the Lean does.** Nothing, and that is the point.  There is no
  registration in the port: `Spine.runCold` composes the rows, each row's
  `Requires` is discharged by instance resolution against the incoming key
  index, and the order in which the branch's results are consulted is the
  composition itself.  No application-supplied field performs a dispatch, no
  `FamilyCapability` is returned, and no `CT7.generateCounted` call sits inside
  a registration field.
- **What it should do.** Supply only graph semantics, with the branch analysis
  owned by the executor.
- **Gap.** none.  The gap the previous implementation had — "the routing is
  registration code", with every decision after the family scan performed by an
  application-supplied field — is structural, and the port removes the structure
  that caused it.  The `Where` column names `Spine.runCold` because that is what
  replaced the four `atStage` registrations.  **Facts passes.**
- **Ledger and residual.** `runCold` threads one `ExactLedger` through the rows
  and returns it; the residual is unchanged throughout, since every cold row is
  `factOnly`.
- **Transport and terminals.** `AtomicCT.run` owns each append; the composition
  owns the order.  No terminal at any cold row.

**Paper objects at this row.**

No manuscript object is first consumed here; every object the composition orders
is recorded at the row that consumes it.

**CT composition at this row.** No CT, and none is hidden in a registration
field — which is the difference from the previous implementation.

### Row 61 — `classifiedStateForcesTarget` `[145]`–`[157]`

- **Paper fact.** `thm:cold-branch-quantitative-closure`: "No terminal cold
  branch survives after the near-cubic spine estimate has been supplied", with
  every alternative of `tab:cold-branch-ledger` forbidden on
  `def:surviving-cold-branch`; the closing sentence of its proof is "Each is
  forbidden in `def:surviving-cold-branch`.  Hence the cold branch has no
  terminal survivor."
- **What the Lean does.** `ColdCorridor.coldBranch_no_terminal_survivor`
  concludes `False` from a surviving cold branch, a length-changing bounded
  germ, and the branch's own identification of that germ's two representatives:
  the germ is distinguishing, so the identification is a target-defective
  quotient, and `def:surviving-cold-branch` (ii) says the branch carries none.
  `Spine.coldBranchClosedRow` commits it.
- **What it should do.** Be total — no `Option`, every arm returning a target or
  eliminating `False` — for the germ families the theorem routes.  The
  theorem's other two arms, "the route-8 carrier inequality closes
  `\theta < 1/78`" and "the live-hot entropy comparison closes", are the
  route-8 rows' and the entropy rows'; this row owns the third arm's routing.
  It does not owe a proof that a germ *exists*: a branch with no germ has no
  terminal residual either, so the absence of a germ closes the branch rather
  than leaving it open.
- **Gap.** none.  The gap the previous implementation had — the field was
  `Option`-valued and took the `none` escape on four arms, so the branch did not
  close — is gone: the committed statement is that the situation is impossible,
  and there is no `Option` anywhere in it.  What the theorem needs beyond the
  ledger is the branch record's clause (ii), the manuscript's own hypothesis for
  this theorem, quantified in the committed fact.
  The registered-fact review corrected one thing here, and it was the difference
  between closing and not closing: the committed statement first carried a
  hypothesis `branch.Identified germ.piece germ.canonical` that nothing in the
  development can produce, so the fact could never fire.  Clause (ii) is now
  stated at germs — where the cold branch's identifications actually live — and
  the closure follows from the germ and the branch alone.  **Facts passes.**
- **Ledger and residual.** `factOnly` with
  `Requires := [coldGermRealized, coldGermSilent, selection, uncompressible]`,
  `Produces := [coldBranchClosed]`; all four are read by exact key.  The
  committed statement has three clauses: the trichotomy leaves G2, a branch that
  reaches a length-changing germ — *in either orientation*, via
  `ColdCorridor.OrientedGerm` — contradicts clause (ii), and every row of
  `def:cold-same-interface-table` — the equal-length germs and the short
  self-return exceptions — is handed off rather than retained.  That is the
  manuscript's three germ families, with `δ ≠ 0` the only hypothesis on the
  first, as `lem:cold-bounded-germ-trichotomy` states it.  Residual unchanged.
- **Transport and terminals.** No CT.  There is no `Terminal.familyScan`
  equivalent in the port: the cold block returns a ledger, and the closure is a
  fact on it.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `thm:cold-branch-quantitative-closure` | thm | `ColdCorridor.boundedGerm_not_survives`<br>`ColdCorridor.coldBranch_no_terminal_survivor`<br>`ColdCorridor.OrientedGerm` (both occurrences, exchanged)<br>`OrientedGerm.swapped`, `OrientedGerm.not_survives`<br>`ColdCorridor.coldBranch_closed` (the three germ families) | no CT — `Spine.coldBranchClosedRow` |

**CT composition at this row.** No CT.  The closure is a case split on the germ
trichotomy whose branches are discharged by facts already on the ledger.


### Trailing note — the `v17` node range

The vertex note is wrong, and it belongs to no single row.
`generated/hypostructure/web/proof-runs/erdos.json` gives `dag.nodes[17]`
(`id: "v17"`, `cold_branch_aggregation:0`) the authored and resolved label
`"Nodes [145]–[164] cold-branch closure"` and the note `"Execute the complete
cold-window ledger and return the literal node-[164] ledger residual for the
enclosing continuation."`  The manuscript has 157 nodes: the Part XI panel of
`fig:proof-diagram-part-xi` runs `[145]` to `[157]`, the theorem-index row reads
`[145]--[157]`, and no node above `[157]` exists anywhere in
`original_erdos_64_proof.tex`.  Nothing is being closed at a node `[158]`–`[164]`.

The `164` originates in a parallel, unwired Lean chain:
`Core/Strategy/ColdBranchAggregation.lean` declares twenty stages `Stage145`
through `Stage164`, each a `Core.Residual.Ledger.Extension` or a
`Core.Residual.Decision.Stage` with no cold-specific content, bundled by
`Prefix160`/`Inputs` and executed by `Profile.execution` with
`checks = work = Fintype.card Phase = 20`.  That chain is consumed only by
`Graph/Strategy/ColdBranchPreludeAggregation.lean`,
`Fixtures/ColdBranchPreludeAggregation.lean` and
`PDE/Strategy/Registry/RankAndCold.lean`; grep finds no occurrence of
`ColdBranchPreludeAggregation`, `ColdBranchAggregation.Inputs` or
`ColdBranchAggregation.Profile` in `examples/hypostructure_erdos_64_eg`.  The EG
cold vertex runs `LedgerProfile.execution` instead, whose `Terminal` is
`familyScan | targetClosed`.  The current sealed run
`build/hypostructure/eg-ab-run.json` carries the corrected label
`"Cold-window corridor closure"` with `note: null`, and
`Graph/Strategy/FiniteDensityBudget.lean:500` names the overflow arm
`[145]`--`[157]`; the `[145]`–`[164]` claim survives only in the generated web
run.

### Row 62 — `[109]` route-8 arm placement

- **Paper fact.** `def:typeA-saturated-exits` exit `(8)` is the one saturated
  alternative that does not close.  `def:typeA-silent-core-residual` names the
  residual it produces; `def:typeA-true-route8-residual` adds (R1)–(R4), of which
  (R2) is the absence of exits `(1)`–`(7)` at the saturated receiver and (R4) is
  the target-complete-minimal basin; and `def:typeA-large-budget-deficit` makes
  the collection *carry* the large-budget deficit.
- **What the Lean does.** Three `Decision`s, in the manuscript's order.  Node
  `[101]`, `Spine.typeAExitFourDichotomy`, splits on whether some indexed entry
  realizes `Route8.Data.ExitFour` — clause (Q5) of `def:typeA-exit4-family`; its
  no arm commits `Route8.ExitFourFree`, which is (R2) for exit `(4)`.  Node
  `[103]`, `Spine.typeAExitFiveDichotomy`, splits on alternative (b) of
  `def:typeA-trace-basin` — a nontrivial target-complete quotient of the
  trace-basin reading, which is exit `(5)` — and its no arm commits
  `Route8.TraceSurviving`.  Node `[109]`, `Spine.route8Placement`, then runs on
  those two no arms and splits on
  `∃ residual : Graph.Route8.Data …, residual.LargeBudget`, the burden, the
  large-budget deficit and the registered rate.  `Route8.Data` itself is data
  only: the index of `Ξ(𝒳)`, the presented entries (support, declared
  coordinates, the target event each coordinate is recorded by, and the reading
  that retains a coordinate set), the ambient boundary supply, the discharge
  scale, the private-carrier threshold, `D_A(𝒳)` and `|R|`.  The carrier
  vocabulary is not stored: `car` is the set of cut edges of the entry's support
  that a coordinate's event crosses, and the entry's supply is the support's own
  cut `cutEdges`.
- **What it should do.** This.
- **Gap.** None at this row.  The block consumes exactly two of the seven
  absences of (R2), because only those two are spent by Figure 9; the remaining
  five belong to rows 13–15, 18 and 19 and sit *above* this segment when they are
  built, so nothing here assumes them and nothing here has to be revisited when
  they land.  The four readings the arm is entered with are the manuscript's own
  citations at `[111]`--`[113]`, and they are listed at row 63.
- **Ledger and residual.** Three `Decision.run`s against the canonical
  `ExactLedger`.  Each arm carries a different key index, so a branch that took
  the exit-`(4)` peel or the exit-`(5)` compression cannot read any route-8 fact,
  and a branch with no large-budget collection carries none either.  The residual
  is unchanged throughout: the block proves theorems about the object it was
  handed.
- **Transport and terminals.** `Spine.runRouteEight` returns `Route8Result` with
  four constructors: `.exitFour` and `.exitFive` leave the block on the ladder's
  yes arms, `.free` on node `[109]`'s complementary arm, and `.closed` on the arm
  that runs rows 63–67 and appends Core's closure key.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeA-silent-core-residual` | def | `Graph.Route8.Data` | standalone |
| `def:typeA-true-route8-residual` (R2), (R4) | def | `Graph.Route8.ExitFourFree`<br>`Graph.Route8.TraceSurviving`<br>`Graph.Route8.Data.SurvivingTrace`<br>`Graph.Route8.Data.ExitFour` | standalone |
| `def:typeA-large-budget-deficit` | def | `Graph.Route8.Data.LargeBudget` (the four readings the manuscript cites at `[111]`--`[113]`) | standalone |
| `def:declared-coordinate-signature` | def | `Graph.Route8.PresentedEntry` (the event and the carrier support it crosses) | standalone |

**CT composition at this row.** None.  Three `Decision`s; the block that follows
is five fact-only Strategies composed by `AtomicCT.run`.

### Row 63 — `[111]`–`[113]` collection, burden, deficit bound

- **Paper fact.** `def:typeA-large-budget-deficit` sums `¼|V(X)| − def⁺(X)` over
  the collection and calls it *carrying* the large-budget deficit when
  `D_A ≥ (¼ − τ_win)|R| − o(|R|)`.  `lem:typeA-route8-burden` is
  `N_basin(𝒳) ≥ 4·D_A(𝒳)`, and its proof is: *"For each `X ∈ 𝒳` ...
  `lem:typeA-silent-excess-count` applies to `X` and gives
  `S_sil^exc(X) ≥ 4(¼|V(X)| − def⁺(X))`.  By `lem:typeA-reduced-silent-residual`,
  every unpaid silent excess vertex counted by `S_sil^exc(X)` has a
  target-complete-minimal trace basin unless one of exits (4)--(7) occurs.  Those
  exits are absent by hypothesis.  Counting the resulting indexed pairs `(u,B_u)`
  and summing the displayed inequality over `X ∈ 𝒳` proves the bound."*  Node
  `[113]` then spends the burden against the large-budget clause.
- **What the Lean does.** `Route8.Data` carries the collection's supports `𝒳`
  with their per-support readings `deficiencyAt` (`¼|V(X)| − def⁺(X)`) and
  `silentExcessAt` (`S_sil^exc(X)`), and each indexed entry records the support
  it lives on.  `Data.deficiency` is the manuscript's sum
  `∑_{X ∈ 𝒳} deficiencyAt X`.  `Data.burden_of_silentExcess` is the manuscript's
  proof, line for line: `Finset.mul_sum` distributes the discharge scale over the
  sum, `Finset.sum_le_sum` applies `SilentExcessCount` and then
  `BasinAssignment` per support, and `Finset.card_eq_sum_card_fiberwise` counts
  the indexed pairs `(u, B_u)` by the support they live on, which is exactly
  "counting the resulting indexed pairs and summing over `X ∈ 𝒳`".
  `Spine.route8Burden` then **reads the node-`[109]` fact by exact key** and
  publishes `∃ residual, residual.Reduced`: the collection with the burden
  substituted into the large-budget bound, `|R| ≤ N_basin + discharge·def⁺(R)`,
  through `Route8.deficit_le_basins`.  That single reading is what node `[122]`'s
  census collides with the rate condition.
- **What it should do.** This.
- **Gap.** None.  The two node-`[94]` lemmas the manuscript cites are the
  readings the arm is entered with — they are clauses of the node-`[109]` fact,
  on the ledger, named for the lemmas they are — and the burden itself is no
  longer among them: it is derived here as the manuscript derives it.  When node
  `[94]` is built, those two readings become facts it produces and this row does
  not change.
- **Ledger and residual.** `rowManifest (K .route8Residual) (K .route8Burden)`:
  one prerequisite, read with `FactInputs.get`, one production, residual
  unchanged.
- **Transport and terminals.** No terminal.  `route8Closed` requires this fact by
  exact key and would not elaborate before it.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeA-large-budget-deficit` | def | `Graph.Route8.Data.deficiency` (the sum)<br>`Graph.Route8.Data.LargeBudgetDeficit` | standalone |
| `lem:typeA-silent-excess-count` | lem | `Graph.Route8.Data.SilentExcessCount` (node `[94]`'s reading, cited) | standalone |
| `lem:typeA-reduced-silent-residual` | lem | `Graph.Route8.Data.BasinAssignment` (node `[94]`'s reading, cited) | standalone |
| `lem:typeA-route8-burden` | lem | `Graph.Route8.Data.burden_of_silentExcess` | standalone |
| node `[113]`'s bound | — | `Graph.Route8.Data.BasinDeficit`<br>`Graph.Route8.deficit_le_basins`<br>`Graph.Route8.Data.Reduced.of_largeBudget` | standalone |

**CT composition at this row.** None; a fact-only Strategy with one declared
prerequisite.

### Row 64 — `[114]`–`[116]` carrier core

- **Paper fact.** `def:typeA-route8-carriers` defines `∂_E X`, the ambient
  carrier of a declared coordinate, the `D`-restriction retaining exactly the
  `u`-supported coordinates `r` with `car_ξ(r) ⊆ D`, `𝒞_ess(ξ)` as the canonical
  inclusion-minimal target-complete carrier set, and `α_𝒳(ξ) = |𝒞_ess(ξ)|`.
  `lem:typeA-carrier-cut-parity`: a surviving mixed internal target event's
  declared support contains at least two distinct carriers of `𝒞_ess(ξ)`.
  `lem:typeA-one-terminal-collapse`: `α ≤ 1` makes `ρ°_𝒞` a target-complete
  quotient, which target-complete-minimality turns into one of exits `(4)`–`(7)`,
  so `α ≥ 2` on a true route-8 residual.
- **What the Lean does.** `Route8.Entry` owns the `D`-restriction
  (`retained D = coordinates.filter (car · ⊆ D)`), and `Complete D` is
  `Response.ContextEquivalent Target (restriction D) full`; `essentialCore` is
  `Core.Finite.EssentialCarrier.Profile.core` at that predicate, and
  `alpha = essentialCore.card`.  `essentialCore_subset_carriers` proves the core
  draws only on the entry's own supply.  `PresentedEntry.two_le_card_car` is cut
  parity: `Graph.CutParity.two_le_card_crossingEdges` at the support's cut,
  applied to the coordinate's own simple cycle.
  `Entry.retained_sdiff_eq_of_alpha_le_one` then shows that a core of at most one
  carrier retains no crossing coordinate, so `ρ°_𝒞` *is* the core reading, and
  `Route8.Data.two_le_alpha` collides that with the entry's `SurvivingTrace`
  clause — which is exactly (R2)+(R4).  `Spine.route8CarrierCore` commits
  `∀ residual, ∀ index ∈ entries, SurvivingTrace index → 2 ≤ alpha index`.
- **What it should do.** This.
- **Gap.** None.  `lem:typeA-internal-quotient-mixed` is not needed as a separate
  statement: in the presented model a declared coordinate's event is a simple
  cycle of the object, and `PresentedEntry.Crossing` — meets the support and
  leaves it — is the manuscript's mixed internal event.
- **Ledger and residual.** `sourceFreeManifest`: the collapse is a theorem about
  every route-8 residual of the object, so the honest `Requires` is empty and the
  row consumes no clause.
- **Transport and terminals.** No terminal.  `route8Closed` requires this fact by
  exact key.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeA-route8-carriers` | def | `Graph.Route8.Entry.retained`<br>`Graph.Route8.Entry.restriction`<br>`Graph.Route8.Entry.Complete`<br>`Graph.Route8.Entry.essentialCore`<br>`Graph.Route8.Entry.alpha`<br>`Graph.Route8.cutEdges` | standalone |
| `lem:typeA-carrier-cut-parity` | lem | `Graph.CutParity.two_le_card_crossingEdges`<br>`Graph.Route8.two_le_card_crossingCarriers`<br>`Graph.Route8.PresentedEntry.two_le_card_car` | standalone |
| `lem:typeA-internal-quotient-mixed` | lem | *(absorbed: `PresentedEntry.Crossing` is the mixed internal event)* | standalone |
| `lem:typeA-one-terminal-collapse` | lem | `Graph.Route8.Entry.retained_sdiff_eq_of_alpha_le_one`<br>`Graph.Route8.Entry.collapse_of_alpha_le_one`<br>`Graph.Route8.Data.two_le_alpha` | standalone |

**CT composition at this row.** None.  The legacy revision spent CT5 on a
first-hit deficit scan whose budget comparison decided nothing (`required` and
`capacity` were both zero); the carrier core is Core's own
`EssentialCarrier.Profile`, so no enumeration executor is needed.

### Row 65 — `[117]`–`[122]` private-carrier census

- **Paper fact.** An essential carrier is *private* for `ξ` when it is essential
  for no other indexed entry; `π_𝒳(ξ)` counts them and `ξ` is two-carrier when
  `π_𝒳(ξ) ≤ 2`.  `prop:typeA-route8-carrier-reduction`: if no entry is
  two-carrier then every entry has `π ≥ 3`, private sets of distinct entries are
  disjoint, so `3N_basin ≤ Σ_X |∂_E X| ≤ def⁺(R) ≤ τ_win|R| + o(|R|)`, colliding
  with the burden because `τ_win < 3/13`; hence a two-carrier entry exists.
- **What the Lean does.** `Route8.Collection.privateCarriers` filters the entry's
  core by "essential for no other indexed entry"; `privateCarriers_disjoint`
  proves distinct entries' private sets disjoint; `card_mul_le_ambient` turns a
  per-entry floor into `floor·|Ξ(𝒳)| ≤ |ambient|` through `Finset.card_biUnion`.
  `Route8.census_contradiction` is the integer collision of the node-`[113]`
  bound, that budget, and the rate condition
  `((threshold + 1)·discharge + 1)·supply < (threshold + 1)·|R|`, which at the
  manuscript's threshold `2` and discharge `4` is `13·τ_win|R| < 3|R|`.  No
  numeral is written anywhere.  `Collection.exists_twoCarrier` derives the floor
  `threshold + 1` from the negation of the two-carrier condition, so no caller
  supplies it.  `Spine.route8Census` commits
  `∀ residual, Reduced residual → TwoCarrierEntry residual`, and
  `TwoCarrierEntry` is node `[122]`'s output: an indexed entry with (T4).  Its
  companions (T2) and (T3) are the ledger facts of nodes `[101]`/`[103]` and
  `[116]`, so the package carries only what the census itself establishes.
- **What it should do.** This.
- **Gap.** None.  The census runs over `Ξ(𝒳)` — the collection's own indexed
  entries — and not over a whole vertex schedule, which is what the legacy
  revision over-counted against.
- **Ledger and residual.** `sourceFreeManifest`: the census is an implication
  about every route-8 residual, so the row consumes no clause; the reduced
  residual it applies to is node `[113]`'s fact, read at node `[124]`.
- **Transport and terminals.** No terminal.  The `.capacity`/`.aggregate` split
  of the legacy CT14 stage is gone; what nodes `[119]`–`[121]` assert is the
  census inequality itself, and it is proved rather than routed.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeA-route8-carriers` (privacy clause) | def | `Graph.Route8.Collection.privateCarriers`<br>`Graph.Route8.Collection.privateCount`<br>`Graph.Route8.Collection.TwoCarrier`<br>`Graph.Route8.Data.TwoCarrier` | standalone |
| `prop:typeA-route8-carrier-reduction` | pro | `Graph.Route8.Collection.privateCarriers_disjoint`<br>`Graph.Route8.Collection.card_mul_le_ambient`<br>`Graph.Route8.census_contradiction`<br>`Graph.Route8.Collection.exists_twoCarrier`<br>`Graph.Route8.Data.Reduced.twoCarrierEntry` | standalone |
| `rem:route8-carrier-margin` | rem | `Graph.Route8.Data.Rate` (the registered rate condition) | standalone |

**CT composition at this row.** None; a fact-only Strategy.

### Row 66 — `[123]` pressure descent

- **Paper fact.** The node-`[123]` row: the remaining large-budget Type A
  target-defect/route-8 ledger either peels a target-defect load by exit `(4)` or
  forces a two-carrier route-8 entry; target-defect two-carrier entries decrease
  `Λ₄`, and the terminal non-peeling case enters node `[124]`.
- **What the Lean does.** `Spine.route8Descent` **reads node `[122]`'s census by
  exact key** and commits two clauses of every route-8 residual: the routing —
  a reduced collection forces a two-carrier entry, which is the entry node `[124]`
  is entered with — and the descent's own measure, that
  peeling an entry off the active set strictly decreases it
  (`Finset.card_erase_lt_of_mem`).  That measure is why the manuscript's loop back
  to `[89]` is a terminating recursion rather than a cycle in the DAG.
- **What it should do.** This.  On a residual where exit `(4)` is *present* the
  manuscript's `Λ₄` accounting is what runs; that ledger is node `[101]`'s, and it
  is row 16's.
- **Gap.** None at this row: the branch this block is on carries `¬ ExitFour` at
  every indexed entry, so the peel arm is empty and the descent enters `[124]`
  with the census's package.  The exit-`(4)` peel ledger of
  `lem:typeA-exit4-discharge` remains rows 16's and is unbuilt.
- **Ledger and residual.** `rowManifest (K .route8Census) (K .route8Descent)`;
  the residual is unchanged.
- **Transport and terminals.** No terminal.  The legacy revision spent CT12's
  well-founded recursion here and branched on `ExitFour` at the *residual* rather
  than at the chosen entry; both clauses are now stated at the entry.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeA-exit4-family` | def | `Graph.Route8.Data.ExitFour` (clause (Q5)) | standalone |
| `def:typeA-exit4-peeling` | def | *(rows 16's; the non-peeling case is what this row routes)* |  |
| `lem:typeA-exit4-finite-descent` | lem | `Finset.card_erase_lt_of_mem`, as the descent measure | standalone |
| `thm:large-budget-route8-only` | thm | this row's routing clause with row 67's terminal | standalone |

**CT composition at this row.** None.  The recursion the legacy stage carried is
not entered: (R2) makes the peel branch empty, so the descent is immediate.

### Row 67 — `[124]` terminal two-carrier no-go

- **Paper fact.** `def:typeA-terminal-two-carrier` is a pair `(𝒳, ξ)` with (T1)
  a large-budget route-8 collection, (T2) a true route-8 residual entry, (T3)
  `α_𝒳(ξ) ≥ 2`, (T4) `π_𝒳(ξ) ≤ 2`, and (T5) the `c`-deletion witness recorded
  for every `c ∈ 𝒞_ess(ξ)`.  `thm:typeA-two-carrier-nogo`: no such pair exists.
  Its proof takes `c` from (T3); (T4)+(T5) give `q_{ξ,c} ∈ 𝒬₄(w)` by
  `lem:typeA-two-carrier-deletion-canonical` and make it target-defective by
  `lem:typeA-carrier-deletion-exit`, which is exit `(4)`; (T2) denies exit `(4)`.
  `prop:typeA-route8-closure-from-nogo` closes the arm.
- **What the Lean does.** `Spine.route8Closed` reads **five** facts by exact key
  — `.route8Burden`, `.route8CarrierCore`, `.route8Descent`,
  `.typeAExitFourFree` and `.typeAExitFiveFree` — and commits
  `¬ ∃ residual, residual.LargeBudget`, the negation of node `[109]`'s fact.
  (T1) is node `[113]`'s reduced collection, (T2) is nodes `[101]` and `[103]`'s
  exit absences, (T3) is node `[116]`'s carrier core, (T4) is the two-carrier
  entry node `[123]` routed, and (T5) is **derived**:
  `Entry.deletion_targetDefect` proves from inclusion-minimality of the core and
  completeness of the core that every `c ∈ 𝒞_ess(ξ)` has a separating outside
  context, and `Entry.exists_forgotten_coordinate` proves that the coordinate
  such a witness forgets has `c` in its carrier support.
  `Data.exitFour_of_twoCarrier` assembles the two-carrier reading, the declared
  carrier support and the separation into `Data.ExitFour` — which *is* clause
  (Q5) of `def:typeA-exit4-family`, carrying exactly the three data that clause
  names — and `Data.no_twoCarrierEntry` collides it with node `[101]`'s absence.
- **What it should do.** This.
- **Gap.** None.  No clause of the refutation is supplied: the witness is proved,
  its declared carrier support is proved, the passage from witness to exit `(4)`
  is the definition of `ExitFour` as (Q5) generates it, and the absence it
  collides with is a ledger fact of node `[101]` rather than a field.
- **Ledger and residual.** Five declared prerequisites, all read with
  `FactInputs.get`; one production; the residual unchanged.
- **Transport and terminals.** The closure is not a row's assertion: node `[109]`
  committed `∃ residual, LargeBudget residual` and node `[124]` commits its
  negation, and Core's `closeIncompatible` derives the closure entry from the two
  committed statements through the `Incompatible` instance
  `Spine.route8ResidualClosed`.  `Fixtures.Route8Run` certifies that the block
  runs on the node-`[63]` Type A residual, that the audit is complete, that its
  facts are unique, and that all eight of the block's facts are present.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:typeA-carrier-deletion-witness` | def | `Response.TargetDefect` at the deletion quotient | standalone |
| `lem:typeA-essential-deletion-witness` | lem | `Graph.Route8.Entry.deletion_targetDefect` | standalone |
| `lem:typeA-deletion-witness-declared` | lem | `Graph.Route8.Entry.exists_forgotten_coordinate` | standalone |
| `lem:typeA-two-carrier-deletion-canonical` | lem | `Graph.Route8.Data.ExitFour` (clause (Q5))<br>`Graph.Route8.Data.exitFour_of_twoCarrier` | standalone |
| `lem:typeA-carrier-deletion-exit` | lem | `Graph.Route8.Data.exitFour_of_twoCarrier` | standalone |
| `def:typeA-terminal-two-carrier` | def | `Graph.Route8.Data.TwoCarrierEntry` (T4) with `route8CarrierCore` (T3), `typeAExitFourFree`/`typeAExitFiveFree` (T2) and `route8Burden` (T1) | standalone |
| `thm:typeA-two-carrier-nogo` | thm | `Graph.Route8.Data.no_twoCarrierEntry` | standalone |
| `prop:typeA-route8-closure-from-nogo` | pro | `Spine.route8ClosedRow`<br>`Spine.route8ResidualClosed` + `Core.Strategy.closeIncompatible` | standalone |

**CT composition at this row.** None.  The whole block is five fact-only
Strategies and three `Decision`s, composed by `AtomicCT.run` and closed by Core.

### Row 68 — Branch D entry `[33]`, `[35]`

- **Paper fact.** `[33]` is the yes arm of `[32]` and `[35]` is the same box
  redrawn as the entry of Part III, so the two carry one statement: Branch D,
  the rank-reducing curvature dependence.  `lem:target-rank-circuit`: if
  `ℐ ⊆ 𝒜` is maximal among subfamilies surviving every functional admissible
  rank quotient and `a ∈ 𝒜 ∖ ℐ`, then some `ℬ ⊆ ℐ` makes `(a, ℬ)` a
  target-dependence in the sense of `def:curvature-target-dependence`.
  `lem:curvature-dependence-routing` opens its proof on that dependence:
  *"Choose a determination certificate with inclusion-minimal connected support.
  The certificate has an admissible quotient `q` and a finite support set
  `𝒫`."*  Clause (a) of `def:curvature-target-dependence` makes the
  certificate's support a connected `T`-boundaried support carrying `{a} ∪ ℬ`;
  clause (b) makes `q` a functional admissible rank quotient of its exact
  response profile; and the definition's closing sentence fixes what
  inclusion-minimal means — no proper connected subsupport carries a proper
  target-dependence.  That certificate, not the bare inequality, is what `[36]`,
  `[38]` and `[40]` route, and `[40]` is where its minimality is spent.
- **What the Lean does.** `Spine.branchDependenceRow` is one atomic Strategy.
  Its manifest requires `curvatureRankDrop` and produces `branchDependence`; its
  executor reads the drop by exact key through `FactInputs.get`, unpacks
  `Core.TargetRank.Dependence.witness` — which names the member of the
  manuscript's own system that realizes the dependence together with its rank
  reduction on `𝒲₂(R)` — and unpacks membership in
  `FiniteObject.curvatureQuotientSystem`, which *is* the existence of a
  `Graph.CurvatureQuotient`.  The dependence's determined coordinate `a`, its
  determiners `ℬ`, its properness `a ∉ ℬ` and the determination itself are
  carried along, so what the row assembles is a *determination certificate* in
  the sense of `def:curvature-target-dependence`; `Spine.DeterminationCertificate`
  is that tuple, clause by clause.  It then performs the manuscript's own
  choice: the supports carrying such a certificate form a finite family of
  `Finset`s, `Finset.exists_min_image` picks one of minimum cardinality, and a
  proper subset is strictly smaller (`Finset.card_lt_card`), so that support is
  inclusion-minimal.  The committed fact is
  `∃ packing, IsWindowPacking ∧ ∃ q : CurvatureQuotient (MinimumDegreeAtLeast δ)
  (HasCycleWithLength LengthOK) object (remainderSupport packing),
  DeterminationCertificate … q ∧ ∀ smaller ⊂ q.support, no determination
  certificate lives on that subsupport`.
  `SpineRun.run` runs the row on the `.left` arm of `curvatureRankDichotomy`, so
  the literal predecessor is the rank-drop ledger and nothing is restarted.
- **What it should do.** Exactly that: turn the committed dependence into the
  inclusion-minimal determination certificate the branch routes -- with the
  dependence pair `(a, ℬ)` on it, because Branch D is a rank-reducing
  *dependence* and "some rank-reducing quotient exists" is a different, weaker
  statement -- without re-deriving the dependence, re-selecting a packing, or
  re-quantifying over the ambient graph.
- **Gap.** none.  `Graph.CurvatureQuotient` is `def:admissible-rank-quotient` at
  the raw curvature tests: its `support`/`connected`/`carries` fields are clause
  (a), its `fibrewise`/`contextUniversal` fields are
  `def:target-complete-quotient`, and its `properRepresentative` and
  `closedRepresentative` fields are the two representative clauses the scope
  split forces.  `curvatureQuotientSystem.Member` is the manuscript's own
  system, so the certificate produced here is a member of it and not a weaker
  surrogate.  The rank reduction the row commits is literally the
  `RankReducingOn` clause of the dependence's witness, transported along
  `toRankQuotient_label`, which is `rfl`.  One deliberate strengthening, stated
  because it is one: the definition's minimality clause reads "no proper
  connected subsupport carries a proper target-dependence *with the same
  determined coordinate*", and the support chosen here is of minimum size among
  all that carry *any* determination certificate, so it rules out every
  determined coordinate at once and implies the definition's clause.
  Connectedness needs no separate clause: a subsupport carrying a certificate
  carries a `CurvatureQuotient`, whose `connected` field is that hypothesis.
  One clause of `lem:target-rank-circuit` is deliberately *not* restated here
  and is not missing: its conclusion is `ℬ ⊆ ℐ` against the maximal surviving
  subfamily, and node `[31]`'s own fact already reads `∃ independent ⊆ 𝒲₂(R),
  Survives ↑independent ∧ independent.card = r_Ω ∧ ∀ test ∉ independent,
  ∃ determiners ⊆ ↑independent, Dependence`.  `curvatureTargetRank` is in
  `curvatureRankDropKeys` and therefore in this row's output index, so `ℐ` and
  the containment are visible on Branch D by exact key rather than duplicated
  into `[33]`.  **All four columns pass.**
- **Ledger and residual.** The row is `factOnly`, so its `refines` obligation is
  `RefinementSystem.refl`: Branch D argues about the same selected object.  The
  incoming index is `curvatureRankDropKeys` and the output index is
  `branchDependenceKeys = branchDependence :: curvatureRankDropKeys`; every
  earlier fact is still in the type, and no entry is archived or rebased.
- **Transport and terminals.** No terminal.  The only transport is the exact key
  `curvatureRankDrop` read through sealed `FactInputs`; the row names no
  producer, no predecessor depth and no execution position, and it is the same
  executor for any cursor whose index carries its requirement.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `def:curvature-target-dependence` | def | `Spine.DeterminationCertificate` is the tuple `𝔠 = (X, T, q, 𝒫)`: clause (a) is the quotient's `support`/`connected`/`carries`, (b) is `remainderQuotient`, (c) is `RankQuotient.Determines` with the properness clause, (d) is `carries`.  Its minimality clause is the second conjunct of this row's committed fact | standalone; the pair `(a, ℬ)` comes from `Core.TargetRank.Dependence`, whose `determined`, `supported`, `proper` and `witness` fields are the remaining clauses |
| `lem:target-rank-circuit` | lem | `Core.TargetRank.exists_dependence_of_attaining`, `Core.TargetRank.exists_independent_attaining` | standalone; consumed at `[31]`/`[32]` and unpacked here |
| `lem:curvature-dependence-routing` | lem | `Graph.CurvatureQuotient.localize` | standalone; its case analysis is the scope split `SupportAtom.classifyScope`, and this row supplies the inclusion-minimal certificate it is applied to |
| `def:admissible-rank-quotient` | def | `Graph.CurvatureQuotient` | standalone |
| `def:functional-rank-quotient` | def | `Core.TargetRank.RankQuotient.FunctionalOn`, `Core.TargetRank.QuotientSystem` | standalone |

**CT composition at this row.** None.  The row is a fact-only atomic Strategy
run by `AtomicCT.run`; it inherits the composition that produced its
prerequisite and adds no adapter.

### Row 69 — Context-validity test `[36]`–`[37]`

- **Paper fact.** The diamond `[36]` is captioned "valid against every outside
  context?", and the no arm is the terminal `[37]`, a target-defective quotient —
  case (i) of `lem:curvature-dependence-routing`.  What is being decided is the
  eligibility condition of `def:target-complete-quotient` — *"two coordinates may
  be identified only inside a fixed boundary-degree fibre and only when no
  context `Y ∈ Ctx_T` creates a power-of-two cycle from one coordinate and not
  the other"* — that is, both of its clauses, and failing either is
  target-defective: the manuscript says so of the context clause in that
  definition (*"an identification failing this context-universal test is
  target-defective"*) and of the fibre clause in the sparse-exit routing (*"a
  non-fibrewise quotient is target-defective"*).  Its invariant table attributes
  invariant 6 to `[36]` **and** `[37]` with failure mode "otherwise
  target-defective", which is the same statement in its own bookkeeping.  Three
  lemmas supply the node.  `lem:context-universality`: a target-complete
  identification works against every context, and failure against one context is
  target-defectiveness.  `lem:degree-profile-fibres`: boundaried states with
  different boundary degree profiles are never eligible to be identified by a
  target-complete quotient.  `lem:separated-testers`: any quotient identifying
  two wedge tests is either context-universal or target-defective, which is the
  exhaustiveness `[36]` splits on.  The figure draws `[37]` as a closed round
  node: an admissible quotient is target-complete by
  `def:admissible-rank-quotient`, so the defective alternative is realized by no
  certificate.
- **What the Lean does.** `Spine.contextValidityDichotomy` is a `Decision` run by
  `Decision.run` against the ledger row 68 leaves.  Its alternative is the
  manuscript's own excluded middle on target-completeness, decided without
  looking at why the certificate was chosen: `by_cases` on *"every pair of
  readings of a certificate's support that carries the same quotient value at
  every declared raw curvature test shares a boundary-degree profile and is
  context-equivalent"*.  The yes arm commits that as `contextUniversal`.  The no
  arm pushes the negation through, splits on the fibre clause, and — where the
  all-context clause is what failed — calls
  `Graph.Response.contextEquivalent_or_targetDefect` to exhibit the separating
  context, committing `contextDefect`:
  `∃ packing, IsWindowPacking ∧ ∃ q, ∃ left right, Identified q left right ∧
  (profile ≠ ∨ Response.TargetDefect (HasCycleWithLength LengthOK) left right)`.
  The two disjuncts are the two ways the manuscript calls a quotient
  target-defective, not a third alternative.
  `SpineRun.run` matches both arms.  On the defect arm it calls
  `Core.Strategy.closeImpossible` at the `Impossible` instance
  `instImpossibleContextDefect`, whose contradiction is
  `Spine.not_contextDefect`; the branch therefore ends with Core's reserved
  closure key and the audit reason `impossibleFact contextDefect`.
- **What it should do.** Exactly that: a real two-way branch on the manuscript's
  eligibility test, with the separating witness exhibited on the no arm, and the
  no arm closed rather than left open or made unreachable.
- **Gap.** none.  `Graph.CurvatureQuotient.targetComplete_of_identified` is the
  two clauses of `def:target-complete-quotient` read off an admissible quotient
  — `fibrewise` is `lem:degree-profile-fibres` and `contextUniversal` is
  `lem:context-universality` — and both halves are consumed by
  `not_contextDefect`, one per disjunct of the defect.  That is the manuscript's
  reason `[37]` is closed: a target-defective identification is by definition not
  target-complete, so it is not made by an admissible quotient.  The branch test
  itself spends none of this, which is why `[36]` is a genuine decision and
  `[37]` a genuine closed terminal rather than an unreachable one.  The yes arm
  is not a dead entry either: `Spine.TargetCompleteAt` is the clause it commits,
  and node `[38]` reads `contextUniversal` by exact key and carries that clause
  onto the certificate it routes, which is what makes case (ii) a
  *target-complete* compression rather than a bare rank reduction.  **All four
  columns pass.**
- **Ledger and residual.** `Decision.run` commits against one immutable prefix,
  so both arms see everything the block and row 68 proved and neither sees the
  other's key: the yes index is `contextUniversal :: branchDependenceKeys` and
  the no index is `contextDefect :: branchDependenceKeys`.  The residual is
  unchanged on both arms — the branch is a fact-only decision about the same
  selected object.  The closure entry is appended by the framework on top of the
  no arm, giving `contextDefectKeys = closed :: contextDefect ::
  branchDependenceKeys`; `contextDefect_audit_facts` pins that audit, and
  `contextDefect_audit_accounts_for_every_fact` certifies through
  `ExactLedger.audit_complete` that every entry is accounted for by a
  chronological commit.
- **Transport and terminals.** `[37]` is the terminal, and it closes: the branch
  publishes Core's `closureFactName`, which no row can spell, carrying
  `AutomaticClosureReason.impossibleFact` naming this fact and nothing else.
  `[36]`'s yes arm is not a terminal and is not an exit either: it is the
  residual node `[38]` is stated on, and `SpineRun.run` continues straight into
  the atom-compression test on it, so `contextUniversalKeys` names an
  intermediate index rather than a `Spine.Result` constructor.  No payload,
  query, or route channel carries a mathematical fact on either arm.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:context-universality` | lem | `Graph.CurvatureQuotient.targetComplete_of_identified` (second component); `Graph.Response.ContextEquivalent`, `Graph.Response.TargetDefect` | standalone; consumed by `not_contextDefect` against the context disjunct of `[37]` |
| `lem:degree-profile-fibres` | lem | `Graph.CurvatureQuotient.targetComplete_of_identified` (first component); `Graph.Response.profile_ne_not_targetComplete` | standalone; consumed by `not_contextDefect` against the fibre disjunct of `[37]` |
| `lem:separated-testers` | lem | `Graph.Response.contextEquivalent_or_targetDefect` | standalone; consumed by the no arm.  This is the lemma's closing sentence, the clause `[36]` needs.  Its opening sentence — a tester separating the two wedge coordinates is supported in the complement of `B̄_r(u) ∪ B̄_r(v)` — is not a separate declaration: in the framework a tester is an `OutsideContext` sharing only the labelled interface with the support, so being supported in the complement is the gluing model itself and not a theorem about balls |
| `def:target-complete-quotient` | def | `Graph.CurvatureQuotient.fibrewise`, `Graph.CurvatureQuotient.contextUniversal` | standalone |
| `def:curvature-target-dependence` | def | `Core.TargetRank.Dependence` | the identified pair `[36]` tests is the certificate's own, supplied by row 68 |

**CT composition at this row.** None.  The node is a branch decision composed by
`Decision.run` and closed by `Core.Strategy.closeImpossible`; no CT is invoked
and no adapter is written.


### Row 70 — Proper-atom compression `[38]`–`[39]`

- **Paper fact.** `[38]` asks whether the context-universal determination is
  target-complete with a smaller proper representative already at support `C`.
  The yes arm is the terminal `[39]`, proper atom compression — case (ii) of
  `lem:curvature-dependence-routing`: *"if it holds for every outside context
  already with support `C`, then `q` is a target-complete rank-reducing quotient
  of the proper atom `C`.  Since `q` is admissible,
  `def:admissible-rank-quotient` supplies a strictly smaller proper
  representative.  Thus this case is a nontrivial target-complete compression of
  `C`"*, and `cor:uncompressible` forbids it.  The no arm is node `[40]`.
- **What the Lean does.** `Spine.atomCompressionDichotomy` is a `Decision` run by
  `Decision.run` against the ledger row 69's yes arm leaves.  It reads
  `branchDependence` by exact key, and its alternative is the excluded middle on
  the node's own yes arm: *"some determination certificate on the remainder has
  its support inside `C`"*.  The yes arm commits `atomCompression`.  On the no
  arm the certificate Branch D was entered with cannot have support inside `C`
  — otherwise it would witness the yes arm — so the row commits
  `delocalizedSupport`, which carries `C ⊂ Z` for
  `Z = Spine.delocalizationSupport`, proved by
  `remainderSupport_ssubset_delocalizationSupport`.  Both arms carry
  `Spine.TargetCompleteAt`, read from node `[36]`'s yes arm by exact key: the
  determination this node asks about is the target-complete one, and neither arm
  re-derives that.  `SpineRun.run` matches both
  arms; on the yes arm it calls `Core.Strategy.closeIncompatible` at the
  `Incompatible` instance `instIncompatibleAtomCompression`, whose contradiction
  is `Spine.not_branchDCertificate`.
- **What it should do.** Exactly that: split on whether the determination is
  certified without leaving `C`, close the compression terminal against the
  selected minimal counterexample, and hand the complementary arm the enlarged
  support node `[40]` is stated on.
- **Gap.** none.  The closure is the manuscript's own two exclusions and no
  other: `Graph.CurvatureQuotient.localize` is the scope split of
  `def:admissible-rank-quotient` — a rank-reducing admissible quotient at a
  proper support supplies a `ReplacementSupport`, and at the closed support a
  strictly smaller admissible closed representative — and
  `InterfaceReplacement.not_replacementSupport` (`lem:replacement`, hence
  `cor:uncompressible`) refutes the first while the selection's own minimality
  and avoidance refute the second.  Both halves of the `selection` fact are
  spent, so the terminal closes against the object the block selected rather
  than against itself.  **All four columns pass.**
- **Ledger and residual.** `Decision.run` commits against one immutable prefix,
  so neither arm sees the other's key: the yes index is
  `atomCompression :: contextUniversalKeys` and the no index is
  `delocalizedSupport :: contextUniversalKeys`.  The residual is unchanged on
  both arms.  The closure entry is appended on top of the yes arm, giving
  `atomCompressionKeys = closed :: atomCompression :: contextUniversalKeys`.
- **Transport and terminals.** `[39]` is a terminal and it closes: the branch
  publishes Core's `closureFactName` carrying
  `AutomaticClosureReason.incompatibleFacts` naming `selection` and
  `atomCompression`.  `atomCompression_audit_accounts_for_every_fact` certifies
  through `ExactLedger.audit_complete` that the audit accounts for the whole
  branch index.  No payload, query or route channel carries a fact.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:curvature-dependence-routing`, case (ii) | lem | `Graph.CurvatureQuotient.localize`, proper branch | standalone; consumed by `Spine.not_determinationCertificate` |
| `def:admissible-rank-quotient`, proper clause | def | `Graph.CurvatureQuotient.properRepresentative` | standalone |
| `lem:replacement` | lem | `Graph.Strategy.InterfaceReplacement.not_replacementSupport` | standalone; consumed here |
| `cor:uncompressible` | cor | `Graph.Strategy.InterfaceReplacement.not_compressibleSupport`, and the `uncompressible` fact of nodes `[11]`--`[14]` | standalone; the compression is excluded through the replacement lemma it weakens to |
| `def:proper-quotient-representative` | def | `Graph.Strategy.InterfaceReplacement.ReplacementSupport` | standalone |

**CT composition at this row.** None.  The node is a branch decision composed by
`Decision.run` and closed by `Core.Strategy.closeIncompatible`.

### Row 71 — Enlarged delocalization support `[40]`–`[42]`

- **Paper fact.** `[40]` is case (iii)'s entry: *"otherwise it holds for every
  outside context but only once additional structure outside `C` is adjoined;
  taking an inclusion-minimal connected such support yields a connected
  `Z ⊋ C`"*.  `[41]` asks whether `Z ⊊ G`.  The yes arm is the terminal `[42]`,
  `lem:proper-smearing`: *"Regard `Z` as a boundaried graph … Since `Z ⊊ G`, it
  is a proper boundaried support.  If the dependence fails against some outside
  `∂Z`-context, it is target-defective.  If it succeeds against every outside
  context, it is a nontrivial target-complete compression of the proper support
  `Z`, forbidden by `cor:uncompressible`."*  The no arm is node `[43]`.
- **What the Lean does.** Node `[40]` is committed by row 70's no arm as
  `delocalizedSupport`, which carries the certificate, the fact that it reaches
  outside `C`, and `C ⊂ Z`.  `Spine.delocalizationScopeDichotomy` is a
  `Decision` reading that fact by exact key, splitting on the excluded middle of
  its own yes arm: *"some vertex lies outside `Z`"*.  The yes arm commits
  `properDelocalization`; the no arm turns the failed existential into
  `∀ vertex, vertex ∈ Z` and commits `globalDelocalization`.  `SpineRun.run`
  matches both; on the yes arm it calls `closeIncompatible` at
  `instIncompatibleProperDelocalization`, whose contradiction is
  `Spine.not_branchDCertificate`.
- **What it should do.** Exactly that: record the enlarged connected support,
  split on whether it is proper in `G`, and close the proper case.
- **Gap.** none.  `lem:proper-smearing`'s two alternatives are the two the
  framework's admissibility already carries: an admissible quotient cannot be
  target-defective (`CurvatureQuotient.contextUniversal`, which is why row 69's
  terminal is uninhabited), so the proper case is the compression, refuted by
  `not_replacementSupport` through `Graph.CurvatureQuotient.localize`.  The
  inclusion-minimality `[40]` asks of `Z` is row 68's committed clause: the
  certificate's support admits no proper subsupport carrying a determination
  certificate.  **All four columns pass.**
- **Ledger and residual.** The yes index is
  `properDelocalization :: delocalizedSupportKeys`, the no index is
  `globalDelocalization :: delocalizedSupportKeys`, both against one immutable
  prefix, and the residual is unchanged.  The closure gives
  `properDelocalizationKeys = closed :: properDelocalization ::
  delocalizedSupportKeys`.
- **Transport and terminals.** `[42]` is a terminal and it closes, with
  `AutomaticClosureReason.incompatibleFacts` naming `selection` and
  `properDelocalization`; `properDelocalization_audit_accounts_for_every_fact`
  certifies the audit is complete.  `[40]` is not a terminal.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:curvature-dependence-routing`, case (iii) | lem | `Spine.delocalizationSupport` with `remainderSupport_ssubset_delocalizationSupport` | standalone |
| `lem:proper-smearing` | lem | `Graph.CurvatureQuotient.localize` at a proper support, refuted by `InterfaceReplacement.not_replacementSupport`; the target-defect alternative is excluded by `Graph.CurvatureQuotient.contextUniversal` | standalone; consumed by `Spine.not_determinationCertificate` |
| `def:curvature-target-dependence`, minimality | def | the second conjunct of row 68's `branchDependence` | standalone |

**CT composition at this row.** None.

### Row 72 — Whole-graph delocalization `[43]`–`[45]`

- **Paper fact.** `[43]` is the case `Z = G`: the dependence delocalizes to the
  whole graph and the quotient is a closed exact-profile quotient.  `[44]` is
  `lem:smearing-support-repair`: a delayed compensation component with `p`
  boundary leaves, `s` internal vertices, cycle rank `β` and surplus `σ`
  satisfies `s = p − 2 + 2β − σ`.  `[45]` is the barrier
  `lem:no-silent-global-smearing` raises: *"any attempted rank-reducing quotient
  is either target-defective, represented by a strictly smaller admissible
  closed representative, or exact on the raw curvature labels"*.
- **What the Lean does.** `Spine.globalBarrierRow` is one atomic Strategy whose
  manifest requires `globalDelocalization` and produces `repairIdentity` and
  `globalBarrier`.  `repairIdentity` is `Graph.OneThreeRepair.Component.identity`
  — the manuscript's own derivation from the handshake identity and the
  cycle-rank formula — stated at every `1`--`3` repair network up to surplus.
  `globalBarrier` applies `Graph.CurvatureQuotient.localize` to the certificate,
  committing the manuscript's own disjunction: a proper-support replacement, or
  a strictly smaller admissible closed representative meeting the baseline and
  transferring the target back to `G`.
- **What it should do.** Exactly that: record the whole-graph case, the repair
  identity, and the two readings the closed clause of
  `def:admissible-rank-quotient` leaves.
- **Gap.** none for the three nodes.  One presentational difference, stated
  because it is one: `[44]`'s fact is quantified over the class of `1`--`3`
  repair networks rather than over the delayed compensation components of this
  particular `Z`, in the same way node `[18]`'s window algebra is a property of
  the registered order rather than of the selected object.  That is what makes
  it transport along a refinement for free; the manuscript's own statement is
  the identity, and it is committed in full.  `repairIdentity` is the one Branch
  D fact no later node reads, and that matches the manuscript: `[44]` is a box
  on the path to `[46]`, and `lem:no-silent-global-smearing`'s proof closes the
  whole-graph case from the closed-representative clause and minimality without
  using the repair identity.  Every other Branch D fact is read by exact key —
  `branchDependence` and `contextUniversal` at `[38]`, `delocalizedSupport` at
  `[41]`, `globalDelocalization` at `[44]`/`[45]`, and each terminal fact by the
  framework's own closure runner.  **All four columns pass.**
- **Ledger and residual.** The row is `factOnly`, so `refines` is
  `RefinementSystem.refl`.  The output index is
  `repairIdentity :: globalBarrier :: globalDelocalization ::
  delocalizedSupportKeys`; every earlier fact stays in the type.
- **Transport and terminals.** No terminal at this row — `[45]` feeds `[46]`.
  The only transport is the exact key `globalDelocalization` read through sealed
  `FactInputs`.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:smearing-support-repair` | lem | `Graph.OneThreeRepair.Component.identity` | standalone; committed as `[44]`'s fact |
| `def:repair-network-terms` | def | `Graph.OneThreeRepair.Component` — its `boundaryDegree`, `internalDegreeThree` and `connected` fields are the definition's clauses, and `internal`, `surplus`, `cycleRank` are its `s`, `σ`, `β` | standalone |
| `lem:no-silent-global-smearing` | lem | `Graph.CurvatureQuotient.localize`, committed as `[45]`'s disjunction | standalone |
| `def:admissible-rank-quotient`, closed clause | def | `Graph.CurvatureQuotient.closedRepresentative` | standalone |
| `def:closed-quotient-representative` | def | the second disjunct of `[45]`'s fact: strictly smaller, meets the baseline, and transfers the target | standalone |

**CT composition at this row.** None.  The row is a fact-only atomic Strategy
run by `AtomicCT.run`.

### Row 73 — Rank-drop branch closed `[46]`

- **Paper fact.** `[46]` is Part III's terminal: the rank-drop branch is closed.
  `lem:no-silent-global-smearing` finishes it — *"`G_q` is a strictly smaller
  counterexample, contradicting the lexicographic minimality of `G`"* — and the
  figure's caption states the invariant the whole diagram maintains: *"Every
  rank-drop branch terminates in a closed round node."*
- **What the Lean does.** `SpineRun.run` calls `Core.Strategy.closeIncompatible`
  on the ledger row 72 leaves, at the `Incompatible` instance
  `instIncompatibleGlobalBarrier`.  Its contradiction is
  `Spine.not_globalBarrierReading`, which consumes the disjunction node `[45]`
  *stored* rather than recomputing it: `Graph.CurvatureQuotient.localize` is
  applied once, in the row that commits `[45]`, and the terminal reads the
  result back by exact key.  The replacement reading is refuted by
  `InterfaceReplacement.not_replacementSupport`, and the closed-representative
  reading by the selection's own minimality and avoidance — the representative
  is strictly smaller and meets the baseline, so the selection forces it to have
  an accepted cycle, which it transfers back to `G`, contradicting the
  selection's avoidance.  The exit is `Spine.Result.rankDropClosed`.
- **What it should do.** Exactly that, and leave no open leaf on the arm.
- **Gap.** none.  The manuscript's third alternative — *"exact on the raw
  curvature labels"* — is not a separate arm here and is not missing: it is the
  negation of the rank reduction the certificate carries, so a certificate
  witnessing it does not exist, which is exactly what
  `def:admissible-rank-quotient`'s closed clause says when it demands
  label-injectivity unless a smaller closed representative exists.
  `CurvatureQuotient.closedRepresentative` takes the rank reduction as its
  hypothesis for that reason.  **All four columns pass.**
- **Ledger and residual.** `rankDropClosedKeys = closed :: repairIdentity ::
  globalBarrier :: globalDelocalization :: delocalizedSupportKeys`, so the
  terminal's index is Branch D's whole history with Core's reserved closure key
  on top.  `rankDropClosed_audit_facts` pins the seven most recent entries and
  `rankDropClosed_audit_accounts_for_every_fact` certifies through
  `ExactLedger.audit_complete` that the audit accounts for the entire branch.
- **Transport and terminals.** This is the terminal.  The closure entry carries
  `AutomaticClosureReason.incompatibleFacts` naming `selection` and
  `globalBarrier`, and no row can spell `closureFactName`.  With `[37]`, `[39]`
  and `[42]` also closed, Branch D has no open leaf: every exit of
  `Spine.Result` on this arm carries the closure key.

**Paper objects at this row.**

| Paper object | Kind | Lean declaration | CT / standalone |
|---|---|---|---|
| `lem:no-silent-global-smearing` | lem | `Spine.not_determinationCertificate`, closed branch | standalone |
| `def:closed-quotient-representative` | def | `Graph.CurvatureQuotient.closedRepresentative`'s conclusion | standalone |
| minimality of `G` | — | the `selection` fact of nodes `[1]`--`[4]`, both halves | standalone; read by exact key at the closure |

**CT composition at this row.** None.  The terminal is the framework's own
closure runner.


## Non-node EG documentation inventory

This inventory covers EG-specific
claims in the problem, presentation, official/AB registrations, execution
modules, and finite-check modules that do not belong to one audit row.

## Summary

All 73 rows have been reviewed against `original_erdos_64_proof.tex` and the
Lean code, with docstrings and prior audit prose excluded as evidence.  Each
row carries its own paper-object table and CT-composition note.

The two counts below are recomputed from the section tables above, which are
the authority.  They replace an earlier pair of counts written before the
canonical-ledger rewrite; those were stale in both directions — they omitted
every ported row and included rows 15 and 52, whose declarations are gone.

**All four columns** pass at **55 rows**: 1–11, 20–25, 29, 37–73.  These are
the ported rows: Block A, the Type B fan through node `[72]`/`[81]` with the
degree-four profile, the Type A entry split of nodes `[88]`/`[89]`, the
remainder/rank/net-charge continuation, the cold-window corridor, the route-8
carrier closure and Part III.  Each is backed by a declaration that elaborates
and a target that builds.

**Facts** passes at exactly the same 55 rows.  There is no longer a row whose
mathematics is exact but whose transport is not: the canonical-ledger rewrite
removed the detached-CT registrations that used to separate the two lists.

**The 18 open rows** are 12–19, 26–28 and 30–36 — the Type A saturated-exit
ladder below node `[93]`, the Type B bridge rows `[73]`–`[76]`, and the
non-near-cubic surplus branch `[125]`–`[144]`.  All are `❌ ❌ ❌ ❌`: none has a
live declaration, and the descriptions in their evidence sections are porting
reference for the legacy `Blueprint` code, not claims about the current tree.

**Part III (rows 68–73).**  Nodes `[35]`–`[46]` have no vertex at all: the
rank-drop arm of `[32]` is the identity continuation, so `Blueprint.compression‑
LinkedTargetRelativeRankDichotomy` receives `Blueprint.root` and the branch is
exported as the single closed terminal `t3`.  Of the manuscript's three
alternatives, only case (ii) — the proper-atom compression of `[38]`/`[39]` —
has a mechanism (row 70), and it is a universal exclusion rather than a branch.
Two Part III statements are formalized generically and never reached from this
arm: `Graph.OneThreeRepair.Component.identity` is `[44]`'s repair identity
`s = p − 2 + 2β_Z − σ_Z` with no call site under `proofs/`, and
`Core.AdmissibleQuotient.not_rankReducing_of_excluded` is `[45]`'s case-(c)
conclusion, consumed only by `Graph/TypeBOverlapObstruction.lean`.
`lem:target-rank-circuit`, `lem:curvature-dependence-routing`,
`lem:separated-testers`, `lem:proper-smearing` and `def:repair-network-terms`
have no declaration of any kind.

**Paper objects.**  261 `\label`s fall in the audited node ranges.  103 have a
Lean declaration whose type states them; **158 cells are empty**.  A recurring
third case is recorded in column 4 as `unconsumed — no call site`: the
declaration exists and is faithful, and nothing in the run reaches it —
`lem:wedge-lower`, `netCharge_eq_sum_components`,
`exists_exactInducedPathComponent_negativeSupport`, `card_skeleton`,
`demand_le_skeletonBudget`, the `CutParity` group, and seven whole Type B
modules are in it.

**Corrections made during this pass.**  Row 7's recorded Facts failure was
refuted: `LabelDenotation` proves the `Fin 399` bijection onto
`WindowCurvature.Labels` and `Official/Problem.lean` consumes it, and `Ω₂`
exists as `curvatureTwo`.  Row 37's recorded reason was too broad: `[26]` and
`[27]` are stated exactly and the gap is the `|W| = 13p₁₃` clause.  Row 26's
recorded reason was wrong: the B1 charge theorem exists.  Fourteen vertex ids
in the tables above were stale — exits 4–7's second copies are `v34`–`v37`,
and the whole Type B block is shifted by +2.
