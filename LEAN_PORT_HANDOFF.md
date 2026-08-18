# Erdős–Gyárfás Lean port — handoff (state as of 2026-08-18)

This document is the complete handoff for whoever continues the Lean port of
`to_formalize/original_erdos_64_proof.tex` into the Hypostructure framework.
It records the methodology, the exact current state, how to verify it, and —
for every remaining open producer — what it is, what exists, and the concrete
steps to close it.

---

## 0. Ground rules (do not deviate)

1. **The manuscript is the sole authority.** Translate node by node of the
   proof-dependency diagram (Parts I–XII, nodes `[1]`–`[180]`), never invent an
   alternative proof, never weaken/strengthen/reorder facts, never add
   hypotheses or axioms. When the paper is underspecified, choose the reading
   closest to its strategy that closes the branch (simplest if several).
2. **Only the ExactLedger API.** Facts are read with `FactInputs.get` /
   `ExactLedger.get`, published by `factOnly` rows run with `AtomicCT.run`
   (`Produces ++ known`), branches are `Decision.run` (exactly one sibling key
   is published), closures are `closeImpossible`/`closeIncompatible` +
   `.elimClosed` with live `Impossible`/`Incompatible` instances or a direct
   `False` from `history.get`. No callbacks, no `FactKey`-parametrised rows,
   no `decode`/`encode`, no side carriers, no data threaded outside the ledger.
   Fact values are data-free (`FactSystem.value_subsingleton`).
3. **Methodology when something is missing:** never assert it. Either the
   missing property is decided by a `Decision.run` (both arms become branches
   and the "no" arm is a named residual to be closed/routed later), or the
   accounting is refined (charge a structure that was overcounted/uncharged),
   or a compression/minimality argument is applied. Routing a residual into an
   existing branch is a legal closure. See Parts XII/V/X of the manuscript for
   the pattern (nodes `[158]`–`[180]` were all created this way).
4. **Replace, don't accrete.** Porting a row deletes the old path in the same
   change; no shims, no two live paths, no aliases, no numerals outside the
   registered presentation data (`Data`/`Presentation` fields).
5. **Loud producers.** Anything not yet ported is an *unknown identifier* at
   its Assembly call site (`selectedXxx history`), named after the node, with a
   comment stating the exact missing lemma; the audit row says the same. That
   is the only acceptable "open" state — no `sorry`, no stubs.
6. **Audit tables.** `Assembly_node_audit.md` mirrors every node/lemma; run
   `python3 .agents/skills/eg-proof-expansion/scripts/audit_tables.py check`
   (13-column rows; the only accepted failure is the pre-existing manuscript
   label-order debt `lem:remainder-empty-internal-3-core`).

## 1. Layout

- Library: `hypostructure/Hypostructure/**` (`lake build` from `hypostructure/`).
  Spine vocabulary/keys/statements: `Graph/Strategy/SpineVocabulary.lean`
  (six registration sites per key: constructor, `Holds`, `label`, `idx`,
  `ofIdx`, `name` + a `LabelPins` example). Rows: `Graph/Strategy/SpineRows.lean`,
  `ColdCorridorRows.lean`, `HomogeneousBottleneckRows.lean`, `SurplusRows.lean`,
  `Route8Rows.lean`; closure instances: `BranchDClosure.lean`,
  `EntropyClosure.lean`, `TypeBClosure.lean`, `TypeAExitRun.lean`.
- Assembly (the DAG): `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly.lean`
  (~4k lines). Entry: `selectedLedgerClosure` → `selectedSurplusDichotomy` →
  `selectedStrictSurplusBranch` (`[19]` yes) / `selectedNearCubicBranch`.
  Wrappers are index-polymorphic over the ledger (`{known}` + `FactKeys.Has`
  instances + freshness autoParams discharged at the concrete arms with
  `by simp [K_eq_iff]`).
- Manuscript + PDF: `to_formalize/original_erdos_64_proof.tex` (rebuild with
  `latexmk -pdf -interaction=nonstopmode`). Web app: `web/` (regenerate with
  `python3 web/tools/extract_proof_graph.py`, `extract_page_map.py`, tests
  `python3 web/tools/test_extract_proof_graph.py`, `npm run typecheck/test/build`
  in `web/frontend`).
- Memory notes: `~/.claude/projects/-home-guillem-hypostructure/memory/`.

## 2. Verification commands (always under the lock)

```bash
LOCK=/home/guillem/.claude/jobs/1bed3e55/tmp/lake.lock   # any path works; use one lock for all agents
cd hypostructure && flock $LOCK lake build                # full library must be clean
cd proofs/hypostructure_erdos_64_eg && flock $LOCK timeout 3000 lake env lean -DmaxErrors=3000 \
  HypostructureErdos64EG/Assembly.lean 2>&1 | grep "error" | grep -v "Unknown identifier"   # must be empty
# the remaining lines with "Unknown identifier `selectedXxx`" are the open producers
python3 .agents/skills/eg-proof-expansion/scripts/audit_tables.py check
```

Parallel agents in the same tree: every build/elab under `flock`; shared files
(Assembly.lean, audit md, SpineRows/SpineVocabulary/…) edited only by anchored
python scripts run under the same lock (never Edit/Write tools); disjoint
regions per agent; verify the merged tree afterwards.

## 3. What is done (verified 2026-08-18)

Full library builds; Assembly has zero non-loud errors; audit checks pass. Ported and closed:

- Parts I–IV: `[1]`–`[19]`, `[21]` (+ realization decision `[158]`), `[22]`–`[24]`,
  cold branch `[145]`–`[157]`, `[25]`–`[31]`, `[32]`→`[33]`–`[46]` (Branch D closed),
  `[34]`→`[47]`–`[56]`.
- Part V: `[57]` = exact collision decision (`[173]`; no sufficient-order
  condition), `[58]`–`[62]`, absorbed-germ residual `[174]`–`[177]` (routing;
  Type B handoff producer open, §5.9).
- Type A `[63]`–`[109]` (exits 1–7; visible-lane `[109]` open, §5.7), route-8
  `[110]`–`[122]` (deficit as all-pieces `thm:branch-kill`; census; `[117]`
  two-carrier decision; `[118]` entry-kind split), Type B `[64]`–`[85]` on the
  common assigned-centre ledger, `[144]`→Type B bottleneck rows.
- Strict branch `[125]`–`[144]`, with `[131]`/`[137]` no-arms → `[178]`–`[180]`.
- Dense residual `[159]`–`[169]`: deficiency decision `[160]`/`[161]`, dense pass
  `[162]`, symmetry decision `[163]`, canonical-realization operator + `[165]`
  smaller-swap closure, `[167]` two-strand enumeration, `[168]` endpoint stub
  structure, `[169]` blocked class (`Graph/BlockedClass.lean`).
- `[164]` all-cold comparison closed by the remainder glue injection
  (`Graph/RemainderGlue.lean`).

## 4. Key library modules added in this port

`Graph/SubcubicReach.lean`, `ColdGermFamily.lean`, `CurvatureTargetRank.lean`
(rank facts + circuit), `RemainderGlue.lean`, `RemainderEntropy.lean` (glued
class), `Route8Census.lean`, `Route8Deficit.lean`, `ExitFourFamily.lean`,
`TwoStrandEnumeration.lean`, `WindowStubStructure.lean`,
`SerialSystemArithmetic.lean` (`Spectrum`, `System.spectrum`,
`exists_pow_realized`), `BlockedClass.lean`, `CanonicalRealization.lean`
(`CanonicalPiece`, `Precedes`, `canonicalRepresentative`,
`cutStateRepresentative`, `swap_smaller_counterexample`),
`SparsePressureLedger.lean`, `TypeBCanonicalB2.lean`, `TypeBEnvelopeCharge.lean`,
`Strategy/BranchDClosure.lean`, `EntropyClosure.lean`, `TypeBClosure.lean`.

## 5. Open producers and how to close each

Format: **producer** — node(s) — paper — what exists — steps.

### 5.1 `selectedDenseSameSizeCanonicalSwap` — `[166]` (2 sites)
Paper: `lem:refined-minimality-swap`: a neutral germ whose canonical
representative `E ≠ Q` has the same size ⇒ the swap is a same-size
counterexample ⇒ excluded by refining `[4]`'s lexicographic minimality to
`(n, m, Φ)`, `Φ` = multiset of canonical-order ranks of the atoms' pieces.
Exists: `CanonicalRealization` (`Precedes` well-founded/total,
`toCanonical_eq_or_precedes`, `glue_swap_*`), decision `canonicalSwapSizeDichotomy`
(`K .coldCanonicalSwapSmaller`/`SameSize`), smaller arm closed.
Steps: (1) `Graph/Progress.lean`: extend `lexicographicProgress` to
`(vertexCount, edgeCount, Φ)` (Dershowitz–Manna/lex on the atom multiset), keep
`(n,m)`-smaller ⇒ smaller so all `MinimalCounterexampleContext` consumers
(~15 modules) stay valid; (2) prove the paper's invariance clause: the swap
happens inside one atom of the canonical decomposition, whose stubs and window
labels are unchanged, so `Φ` strictly decreases (needs: canonical packing and
decomposition are unchanged by the swap — state it at the germ's atom);
(3) close the same-size arm from `K .selection` (refined) — index-polymorphic
`False`.

### 5.2 `selectedScaleAdditivityDichotomy` — `[170]`→`[171]`/`[172]` (2 sites)
Paper: `lem:scale-additivity`, `lem:blocked-graphs-compress`, `def:barrier-overlap-system`,
`lem:barrier-failure-overlap`, `def:serial-window-system`,
`lem:window-system-realizability`, `lem:serial-system-sumset`,
`lem:system-increment-arithmetic`.
Exists: `BlockedClass.lean` (`𝓑(𝒫)`, `G ∈ 𝓑`, `card 𝓑 ≤ budget`),
`SerialSystemArithmetic.lean` (`System`, `System.spectrum`, `Spectrum.exists_pow_realized`),
`ColdIncrementArithmetic.lean` (doubling-orbit criterion), `CanonicalRealization`.
Missing object: the `[18]` label algebra **with responses on skeletons** — the
barrier state `(S,A,T)` of a window at a dyadic scale as a function of a
labelled skeleton (`Graph/PackedWindowRealization.lean` `Skeleton`), its
a-priori range `W_{a,b}` and surviving set `F_{a,b}` (registered presentation
data, `app:curv-code`).
Steps: (1) define barrier states on `Skeleton n m` and the conditional fibres
of `def:barrier-overlap-system`; (2) `[170]` `Decision.run`: additivity ⇒
`[171]` encoding bound `card 𝓑 ≤ budget·2^{-(c₁₃-o(1))p log n} < 1` for
`θ>θ_win` (contradiction with `G ∈ 𝓑`); non-additive ⇒ `[172]`: minimal
same-scale overlap obstruction (`lem:barrier-failure-overlap`), uncrossing to a
serial window system via `cutStateRepresentative` (`lem:window-system-realizability`
(i)–(v): dyadic hit / G2 / G3 / Type A/B interface / serial system), multi-generator
Frobenius filling (`lem:serial-system-sumset`, `g = gcd`, `C_sys`) into
`System.spectrum`, then `exists_pow_realized` ⇒ dyadic hit (`K .selection`) or
periodic carrier routed as G2 (`instImpossibleContextDefect`) / G3
(`K .replacementExclusion`) / Type A/B interfaces.

### 5.3 `selectedSparsePairSerialSystem` — `[178]`–`[180]` (2 sites)
Paper: `def:pair-overlap-system`, `lem:pair-failure-overlap`,
`lem:pair-system-realizability`, `lem:pair-system-increment-arithmetic`,
`lem:pair-count-or-arithmetic`. Same shape as 5.2 with surplus-pair responses
(`def:sparse-pair-response` `val_X(r_π)` as functions of the graph, `SurplusRows`,
`HomogeneousBottleneckRows`, `SparsePressureLedger`). Closures: `K .selection`,
`K .sparseSurplusSurvivor` (exits (b)/(c)), `K .replacementExclusion`,
Type B envelope `K .typeBFanEnvelope`. Arithmetic core shared: `exists_pow_realized`.

### 5.4 `selectedRouteEightTrueTwoCarrierEntry` — `[118]`–`[124]` (2 sites)
Paper: `def:typeA-route8-carriers`, `def:typeA-true-route8-residual`,
`lem:typeA-carrier-cut-parity`, `lem:typeA-one-terminal-collapse`,
`def:typeA-carrier-deletion-witness`, `lem:typeA-essential-deletion-witness`,
`lem:typeA-deletion-witness-declared`, `lem:typeA-two-carrier-deletion-canonical`,
`lem:typeA-carrier-deletion-exit`, `def:typeA-terminal-two-carrier`,
`thm:typeA-two-carrier-nogo`, `prop:typeA-route8-closure-from-nogo`.
Exists: `Route8.terminalTwoCarrierNoGo`, `carrierDeletion_contradicts_noExitFour`,
`instIncompatibleRoute8TerminalResidualNoGo`/`instImpossibleLargeBudgetRoute8Closed`
(`TypeAExitRun.lean`), `Route8Census`, `[118]` split (`route8EntryKindDichotomy`).
**Soundness note:** `Route8.PresentedEntry.ofTraceBasin` uses `state := fun _ => piece basin`
and `Value := PUnit`, so essential cores are empty and "two-carrier" is vacuous
(the `[119]`–`[122]` closure was only exercised on a dead arm). Steps: (1) replace
`state`/`Value` by the non-degenerate carrier reading `ρ_u(B_u)` realized as
`CanonicalPiece.cutStateRepresentative` (profile-preserving canonical piece);
(2) with real essential carriers, build the declared deletion witnesses and the
exit-(4) receiver family (`ExitFourFamily`), feed `terminalTwoCarrierNoGo`;
(3) close `[124]` at both sites; re-check `[119]`–`[122]` are non-vacuous.

### 5.5 `[123]` — done except two named leaves
Built (`Graph/Route8Pressure.lean`, rows `route8PeelingDescentRow`,
`route8PeelingOutcomeDichotomy`; keys `route8PeelingDescent`/`route8PeelingSaturated`):
peeled census `Ξ^{P₄}`, stage rate `D̃_A^{P₄}`, `exists_twoCarrierEntry_peeled`
(`lem:typeA-peeling-reduced-reduction`), `TargetDefectAt`
(`lem:typeA-pressure-is-exit4-peel`), `PeelChain`, `descent_of_census`
(`thm:large-budget-route8-only` by strong induction on `Λ₄`). On the `[118]`
target-defect arm: true stage → 5.4's producer; saturated →
**`selectedRouteEightPeelingSaturatedStage`**: needs `lem:typeA-exit4-peeling-charge`'s
exact `¼` discharge per peeled load so the peeled deficit is the whole remaining
negative mass and `[56]`'s cap contradicts `¬StageRate`. The two non-census
entry sites (Type B mass `selectedTypeBRoute8Continuation`, `[102]` retest) end at
**`selectedLargeBudgetPressureCensus`**: run the census rows there
(all-pieces classification `route8PieceClassificationDichotomy`, deficit row
with `[88]` routing, rate row) — those ledgers lack `K .route8SmallCoreCollapse`
/`K .typeAReceiverRouting`, so run the rows that publish them first (they are
arm-independent) or restate the census on the facts present. Dead old chain
(`route8PressureDescentRow`, `route8TerminalNoGoRow`, `largeBudgetRoute8ClosedRow`,
key `route8PressureDescent`) still to delete (replace-don't-accrete).

### 5.6 `selectedRouteEightUnclassifiedPiece` — `[111]`–`[113]` classification no-arm
Paper: `thm:branch-kill` all-pieces form; a negative piece that is neither
silent-first Type A nor a bridge-residual Type B: visible-first Type A pieces
close by `lem:typeA-visible-entry` (needs 5.7's separation reading), non-bridge
Type B pieces by `prop:typeB-bridge-reduction` per piece. Steps: state the
per-piece Type A visible-lane closure and the per-piece Type B chain
(`TypeBCanonicalB2`, `heavyCentreLocalDichotomy`) as rows over the piece, close
the arm.

### 5.7 `selectedTypeAVisibleRouteEightImpossible` — visible-lane `[109]`
Paper: `lem:typeA-visible-entry`, `lem:typeA-continuation-routing`,
`lem:typeA-cubic-switch-absorption`, `lem:typeA-high-degree-handoff`.
Exists: `TypeAExitSevenGermSchedule.firstSeparator`, `DecoratedHandoff.Separation`,
`SwitchReading`, `Surviving`, `four_le_degree_of_surviving`, `envelopeOfSeparation`.
Missing: `SwitchReading`'s `state reduced` as a genuinely smaller realization —
now `CanonicalRealization.cutStateRepresentative`. Steps: build the switch
reading from the operator; then `four_le_degree_of_surviving` + `envelopeOfSeparation`
contradict `K .typeAExitSevenFree`, or route to the decorated Type B entry.

### 5.8 `selectedRouteEightBudgetEdge` — rate-fails corner
Statement: every packed window hot at the exact skeleton budget and the
private-carrier rate `τ<3/13` still failing — the `(⌊log₂n⌋+1)/⌊log₂n⌋` slack
against `rem:route8-carrier-margin`'s 1.1% margin (nonempty for `n ≲ 2^170`).
Steps: replace the dyadic-scale count reading of the budget by the exact skeleton
count (`skeletonBudget = C(C(n,2),m)`, `lem:near-cubic-budget`) in the rate row so
the log-factor slack disappears (as `[173]` did for `[56]`); if a genuine corner
remains, branch it and route to the dense pass (`selectedAbsorbedGermResidual`).

### 5.9 `selectedAbsorbedGermTypeBHandoff` (`[177]`→`[65]`), `selectedTypeBRoutedEnvelope` (`[144]`→`[65]`)
Paper: decorated handoff fan data enters Type B `[65]`/`[66]` on the bare
envelope (`def:decorated-fan-envelope`, `def:marked-typeB-fan`,
`lem:typeA-high-degree-handoff`). Exists: `K .absorbedGermFanData`,
`K .typeBFanEnvelope`, `TypeBAssignedCentres`/`TypeBAssignedLedgerWith` (decorated
`σ=0` reading), `selectedTypeBDecoratedContinuation` (stated on the Type A `[108]`
residual). Steps: restate the Type B entry rows `[65]`–`[67]` on the envelope
facts they actually use (the `[67]`+ rows read `remainderNormalized`,
`largeBudgetResidual`, `negativeSupport`, absent on these arms — run the
arm-independent `[25]`–`[27]` normalization there if the paper's node order
allows, or state the entry on the bare envelope), then call the common chain;
no duplication.

### 5.10 `selectedCubicBottleneckSeparator` — `[144]` cubic reading
Statement: `d_G(z)=3` reading of the routed bottleneck: internal switch reading;
closing from `K .sparseSurplusSurvivor` needs the switch reading presented as an
admissible `DeclaredQuotient` / baseline `ReplacementSupport` (the premises
`TypeBHandoffStatement` quantifies over). Steps: build the switch reading's
quotient from `cutStateRepresentative` (as in 5.7), refute delocalization by
minimality, target-defect by `K .sparseSurplusSurvivor` (exit (b)), compression
by `K .replacementExclusion`.

## 6. Cross-cutting notes

- `skeletonBudget` is `C(C(n,2),m)` (all labelled graphs). Where the paper's
  entropy step is used (`[171]`), the class must be the near-cubic one —
  `BlockedClass.NearCubicSkeleton` (built); its count is bounded by the budget.
- The one shared object of 5.1/5.4/5.7/5.10 and the uncrossings of 5.2/5.3 is
  `CanonicalRealization.cutStateRepresentative` — built; use it, do not
  re-derive canonical pieces elsewhere.
- Interior-unit accounting: `[152]`–`[153]` still charge `13` units per window;
  `lem:symmetric-pair-endpoint` says only the `(order−2)(δ−2)` interior stubs
  (`9` units) are asymmetric. `K .coldWindowStubStructure` is on the ledger; the
  refactor of `coldExternalStubCount`/`selectedStubs`/`ColdMassLinear`/`densitySlack`
  is pending (changes no closure today because `[168]` is closed structurally).
- After each round: full build, Assembly elaboration, audit check, then
  regenerate the web app (`web/tools/…`) so the site matches the manuscript.
