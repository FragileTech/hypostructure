# Handoff: close the cold branch

State at handoff: tree green, unchanged this session. No edits were made — this
session was diagnosis only, and it corrects the previous handoff on two points.

## Corrections to the previous handoff

**The eight-field table was right, and both "substantive" marks were wrong.**
`noTargetDefect` is not proved in `ColdBranchClosure.lean`; it occurs there only
as `branch.noTargetDefect …`, a field read off a hypothesis. The docstring's
"G2 is derived, not assumed" is true of `SurvivingColdBranch.noGermDefect`,
which derives G2-for-germs *from* that field — not of the field itself.
`Corridor.HandoffEnvelopes` has no producer either. Neither needs one:

| field | source | kind |
|---|---|---|
| `noTargetCycle` | `.selection` first component (`SpineVocabulary.lean:1493`) | ledger read |
| `noCompression` | `.uncompressible` (`:1515`) | ledger read |
| `Identified` | the germ relation | choice |
| `germIdentified` | immediate at that choice | trivial |
| `noTargetDefect` | `.coldCorridorState` third clause (`:1856`–`:1861`) — *"after excluding (F2), equality of cold corridor states is equality for every target-response coordinate"* — with (F2) excluded by `.coldFailureDefect` | ledger read |
| `handoffEnvelopes` | clauses (iii)–(v) say no residual remains outside its ledger, so `Envelope := Empty` | forced by the clause |
| `surplusBound`, `spineEstimate` | `object.degreeSurplus data.threshold`, `le_refl` | trivial |

Eight of eight are ledger reads or forced. The branch record is pure wiring.

**`coldBranchClosed` is already proved and committed** (`ColdCorridorRows.lean:631`,
run at `ColdCorridorRun.lean:255`). Its clause 2 quantifies the branch
(`SpineVocabulary.lean:2299`), so no row manufactures one. That is why the
corridor returns an open ledger: the fact is true but not contradictory.

## Landed this session

`ColdCorridor.lean:1187` — `BoundedGerm.record_truth` **deleted**. It read

```lean
record_truth : ∀ outside, record.truth = true ↔ Target (glue canonical outside)
```

i.e. the canonical representative's target truth is constant across *every*
completion. No germ of a cycle target satisfies that, so `BoundedGerm` was an
effectively uninhabited type — which is why nothing in the tree ever built one,
and why every attempt to construct a germ turns into invented machinery.

`def:cold-bounded-germ` (tex:6629) states no such invariant. It says the germ
"**carries** the inherited boundary degree profile, `P₁₃`-window labels, and
target-response profile", and `Record S` is exactly that tuple; `Fintype (Record S)`
is the only use the definition makes of it (*"only finitely many germ types"*).
The semantic content of (T4) lives at `.coldCorridorState`, where the branch
reads it, not in a structure field.

`record_truth` was referenced nowhere, so the deletion is local. Tree green:
`HypostructureErdos64EG` 8729 jobs, `api_catalog.py check` current.

**Do not re-add it, and do not replace it with a conditional.** An intermediate
attempt made it `∀ outside, completionState outside = record.state → …` with
`completionState` a new field; that is worse — the germ chooses its own
antecedent, so the field can be made vacuous. That is a hypothesis smuggled in
as data and the skill forbids it explicitly.

## The remaining gap

`ColdFirstFailure.lean:858`, the section headed **"(v) case (F5) is a cold
bounded germ"**, contains no declaration — nine lines of prose, then
`end Routing`. The (F5) → `BoundedGerm` constructor is missing. Consequently:

- `BoundedGerm` (`ColdCorridor.lean:1187`), `OrientedGerm`
  (`ColdBranchClosure.lean:363`) and `SurvivingColdBranch`
  (`ColdFirstFailure.lean:674`) are **never constructed anywhere in the tree** —
  every occurrence of all three is a binder or a field projection;
- `coldGerm_positive` (`ColdBranchClosure.lean:257`) is proved but is committed
  only in implication form (`ColdCorridorRows.lean:616` commits
  `fun … cover positive => coldGerm_nonempty cover positive`), with nothing
  supplying the antecedent;
- every one of the thirteen cold `Holds` branches (`SpineVocabulary.lean:1815`–`2321`)
  is universally quantified, so no two cold facts are `Incompatible`.

`BranchState` is `Unit` (`Problem.lean:85`) and must stay so: the germ is
derived from the incoming residual, not supplied by the problem.

## The job

### 1. `Corridor.firstFailureGerm` — `Graph/ColdCorridor.lean` or `ColdFirstFailure.lean`

From a corridor, presentation, and an (F5) first failure, build the
`BoundedGerm`. Eight fields, all from material already present:

- `support` — the first-failure cold exchange: the whole terminal corridor in
  the `TerminalCorridor` subcase, the span between the two equal states in the
  `RepeatedState` subcase. `corridor.inside` and `RepeatedState`'s two segments
  give both; the size bound is `Corridor.exchange_card_le` (already proved), and
  the interface bound is `Corridor.activeInterface_card_le`.
- `connected` ← `corridor.connected`; `proper` ← the exchange is proper.
- `canonical` — "the canonical representative determined by the repeated cold
  corridor state". Needs the cut-state → representative map; this is what
  `def:cold-corridor-first-failure`'s cut state exists for.
- `record` — carried data, free: `presentation.state` supplies the `state`
  component and the rest are the corridor's own retained items.
- `sameProfile`, `baseline` — the two real obligations. The excision must
  preserve the boundary-degree profile (`boundary object support` is
  `cutBoundary`, so the excised vertices must not be boundary-adjacent) and must
  keep `MinimumDegreeAtLeast 3` on the glued result. Cut-state equality is what
  supplies the first: `CutState.boundaryDegrees` (`:1099`) is retained precisely
  so that a splice at equal states is profile-preserving.

**The `OrientedGerm` pairing is a soundness guard — do not bypass it.** With
`record_truth` gone, a *degenerate* germ is constructible: take the span's piece
and let `canonical` be that piece plus a disjoint `K₄`. `sameProfile` holds (the
`K₄` touches no boundary vertex), `baseline` holds (every `K₄` vertex has degree
3), and `increment = +4 ≠ 0`. That germ closes nothing. What rejects it is
`OrientedGerm` (`ColdBranchClosure.lean:363`), which needs **both** readings with
`exchangedPiece`/`exchangedCanonical` pinning each side's internal count against
the other's — the `+4` reading requires a real `−4` reading at the same boundary
degrees and still min-degree-3, which cannot be fabricated. Any constructor that
produces a germ without satisfying both readings has closed nothing.

Then `OrientedGerm` from the two readings (`forward`/`backward` with
`exchangedPiece`/`exchangedCanonical`), and the candidate family as one germ per
selected branch-excess half-edge — `selectedBranchExcess`
(`ColdFirstFailure.lean:762`) indexed over `coldWindows`. That indexing is what
makes `coldGerm_positive`'s `stubExcess` and `candidateLoss` *hold* rather than
be assumed.

### 2. New key `coldGermPresent` — `SpineVocabulary.lean`

idx **145** (144, `canonicalBlockerRoute`, is the highest in use). Six entries:
`Holds` branch, `label`, `idx`, `ofIdx`, `name`, `LabelPins`. Statement:

```
∃ branch : SurvivingColdBranch data.coldSignature
    (MinimumDegreeAtLeast data.threshold) (HasCycleWithLength data.LengthOK) object,
  ∃ germ : OrientedGerm … object, germ.forward.increment ≠ 0
```

### 3. `coldGermPresentRow` — `ColdCorridorRows.lean`

Requires `.selection`, `.uncompressible`, `.coldCorridorState`,
`.coldFailureDefect`, `.coldFailureRouting`, `.coldGermExtraction`,
`.spineSurplusEstimate`. Produces `.coldGermPresent`. Body: the branch record
from the table above, the germ from step 1.

### 4. The closure — `ColdCorridorRun.lean`

```lean
noncomputable instance coldBranchIncompatible :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .coldGermPresent)
      (K (data := data) .coldBranchClosed) where
  contradiction := fun _input present closed =>
    let ⟨branch, germ, lengthChanging⟩ := present.down
    closed.down.2.1 branch germ lengthChanging
```

`runCold` ends in `closeIncompatible`; `coldKeys` gains `FactSystem.closureKey`.
Template: `sparsePairExitClosed`, `SurplusRun.lean:115`.

### 5. The hot/cold `Decision` — `StrategyDag.lean`

Still absent. Add it where the live-hot entropy comparison is set up; cold arm →
`runCold` → the closure above, hot arm carries the entropy count. `runCold` needs
only `[FactKeys.Has (K .selection)]` and `[FactKeys.Has (K .uncompressible)]`, so
entry is free. `runCold` is currently called from nothing but
`Fixtures/ColdCorridorRun.lean:56`.

## Then: the last hypothesis in `[131]`

Unchanged from the previous handoff. `canonicalPairLedger`'s entropy clause in
`SpineVocabulary.lean` / `SurplusRows.lean` still reads

```
∀ spineCount freeCount deficit,
  2 ^ (spineCount + freeCount) ≤ skeletonBudget object →
  cubicBaselineBudget … ≤ 2 ^ (spineCount + deficit) →
  2 ^ freeCount ≤ …
```

Both hypotheses come off together once the hot arm exists: the first from the hot
arm's own fact (step 5), the second from `[129]` — `IsBaselineSpineDemand.demand`
(`Graph/BaselineSpineDemand.lean:486`) is character-for-character that
inequality. Do them in one edit; a half-done restructure leaves the clause in a
shape whose decoders do not exist, which broke the tree once already.

## Also still open

`[107]`'s exit-`(7)` handoff should enter `runTypeBFanLedger`
(`Strategy/SpineRun.lean`) the same way `[144]`'s three bottleneck arms now do.
The ledger takes only `selection` and `fanCertificateCap`, and
`fanCertificateCap` is `sourceFreeManifest`, so any branch can enter.

## Audit

`EG_STRATEGYDAG_AUDIT.md` marks rows 52–61 ✅ on all four columns, including
row 59 (`boundedGerm_not_survives`) and row 61
(`coldBranch_no_terminal_survivor`). Those cells do not reflect the gap above.
Rewrite them from fresh evidence in the same change that closes the branch.

## Working rule

No hypotheses. Every "assume" in the manuscript is either another branch or a
contrapositive. Read facts from the ledger. The residual is the minimal
counterexample: existence is granted and is what gets contradicted, never
proved. No new mathematics — wire it.
