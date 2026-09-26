import Hypostructure.Graph.Statements.TypeA

/-!
# Statements: RouteEight

Proof-agnostic statement definitions of the minimum-degree cycle spine:
route-8 statements: the large-budget residual, census, peeling descent, window shadows and the terminal no-go.
Every registered constant is an explicit `Parameters` argument; this module
imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u v

/-- The selected silent-core residual profile at exit `(8)`.  It exposes the
same selected saturated residual state as `[109]`, with the selected receiver
and current peeling set in scope for later semantic facts, and asserts that no
decorated handoff fan is produced. -/
abbrev SilentCoreResidualProfile (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  SelectedNoExitSixReceiverWith data object
    (fun packing piece _receiver _peeled =>
      ¬ HandoffProduced data object packing piece)

/-- The exact component predicate used by node `[111]` to form `𝒳_A`.

`SilentFirst` is the absence of the visible-overload lane (exits `(1)`--`(3)`),
and every unpaid silent load is already an indexed target-complete-minimal trace
basin entry, which is the absence of exits `(4)`--`(7)`.  This predicate defines
the route-`8` collection; it contains no numerical burden from `[112]`. -/
abbrev Route8Survives (data : Parameters) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (component : Graph.SupportComponents.Connected.Component object
      (object.remainderSupport packing)) : Prop :=
  let piece := object.pieceSupport (object.remainderSupport packing) component
  object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
    object.ambientSurplus piece data.threshold = 0 ∧
    Graph.Route8Deficit.SilentFirst object piece data.threshold
      data.dischargeScale ∧
    ∀ receiver : object.Vertex,
      receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
        data.threshold data.dischargeScale →
      ∀ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
          data.dischargeScale receiver,
        Graph.Route8.TraceBasin.Route8Entry object piece data.threshold
            data.LengthOK receiver load ∧
          ¬ ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
              receiver ∅,
            witness.load = load

/-- The canonical component collection `\tilde{\mathcal X}` of
`def:typeA-unified-negative`. -/
noncomputable def route8UnifiedComponents (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Finset (Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))) := by
  classical
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  exact (object.canonicalPieces support).filter fun component =>
    let piece := object.pieceSupport support component
    object.ambientSurplus piece data.threshold = 0 ∧
      object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
      ¬ HandoffProduced data object packing piece

/-- The unified indexed collection `\tilde\Xi` used by the implemented burden
identity: saturated receivers and their visible-first unpaid excess loads on
the supports in `\tilde{\mathcal X}`.  The silent subfamily is a strict
filter of this collection; keeping the two notions separate is essential at
nodes `[184]`--`[185]`. -/
noncomputable def route8UnifiedEntries (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Finset (Graph.Route8Census.Index object) :=
  Graph.Route8Census.entriesOfComponents object
    (canonicalWindowPacking data object) (route8UnifiedComponents data object)
    data.threshold data.dischargeScale

/-- The `[113]`-tested quotient-freeness of the unified census
(`def:typeA-trace-basin` (b) at every unified entry's selected basin): the
plain trace-response quotient occurs at no entry.  It is decided by a
`Decision`; the no arm retains its literal negation. -/
def Route8QuotientFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (∀ index ∈ route8UnifiedEntries data object,
      ∀ basin : Finset object.Vertex,
        Graph.Route8.TraceBasin.select? object index.1 data.threshold
            index.2.1 index.2.2 = some basin →
          ¬ ∃ retained,
            Graph.Route8.TraceBasin.TraceResponseQuotient object index.1
              data.threshold data.LengthOK index.2.1 index.2.2 basin retained) ∧
    -- the same clause-(b) state at every candidate extracted core of the
    -- bridge pieces (`lem:typeB-bridge-with-route8-core`'s deleted regions):
    -- on the free arm every negative no-handoff core of a deleted region is
    -- exactly a member of `route8ExtractedCores`.
    ∀ component ∈ (object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object))).filter
          fun component =>
            object.NegativeNetCharge
                (object.pieceSupport
                  (object.remainderSupport (canonicalWindowPacking data object))
                  component)
                data.threshold data.dischargeScale ∧
              0 < object.ambientSurplus
                (object.pieceSupport
                  (object.remainderSupport (canonicalWindowPacking data object))
                  component)
                data.threshold,
      let deleted := object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object))
          component \
        Graph.TypeBRefinedSupport.centres object data.threshold
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component)
      ∀ core ∈ (object.canonicalPieces deleted).image
          (object.pieceSupport deleted),
        object.NegativeNetCharge core data.threshold data.dischargeScale →
        ¬ HandoffProduced data object (canonicalWindowPacking data object)
          core →
        ∀ receiver ∈ object.receivers core data.threshold,
          ∀ load ∈ Graph.VisibleEntry.excessBasinReduced object core
              data.threshold data.dischargeScale receiver ∅,
            ∀ basin : Finset object.Vertex,
              Graph.Route8.TraceBasin.select? object core data.threshold
                  receiver load = some basin →
                ¬ ∃ retained,
                  Graph.Route8.TraceBasin.TraceResponseQuotient object core
                    data.threshold data.LengthOK receiver load basin retained

/-- **`def:typeA-pressure-ledger` with `lem:typeA-pressure-ledger-no-overcount`
and `lem:typeA-pressure-records-canonical`**, on the unified collection: a
2/3-demand ledger over `Ξ̃` pinning every minimal entry that holds at least
`δ` private essential incidences (clause (L1); a minimal entry below that
bound is the terminal two-support obstruction, closed on the other arm of
the dichotomy), chosen maximizing first `N₃`, then `N₂`; its assigned
incidences satisfy the raw no-overcount `3N₃ + 2N₂ ≤ e(R, W)` and the defect
form `3Ñ ≤ e(R, W) + 𝖯_ext`; and every target-defect entry left in
`Ξ₂ ∪ Ξ_res` carries its canonical actual or profile demand record. -/
noncomputable def route8DemandCore (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Graph.Route8Census.Index object → Finset (Sym2 object.Vertex) :=
  Graph.Route8Census.core object data.threshold data.LengthOK

/-- The literal clause-(L1) predicate on one member of the unified entry
family.  Naming the predicate fixes the canonical carrier-count interface
once; later rows read it rather than re-elaborating an extensionally equal
filter under a different local decision procedure. -/
abbrev Route8DemandPinnedAt (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (index : Graph.Route8Census.Index object) : Prop :=
  letI : DecidableEq object.Vertex := Graph.Route8.vertexDecEq object
  Graph.Route8.TraceBasin.TargetCompleteMinimal object index.1 data.threshold
      data.LengthOK index.2.1 index.2.2
      (Graph.Route8Census.basin object data.threshold index) ∧
    data.threshold ≤ Graph.Route8.indexedPrivateCoreCount
      (route8UnifiedEntries data object) (route8DemandCore data object) index

noncomputable def route8DemandPinned (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Finset (Graph.Route8Census.Index object) := by
  classical
  exact (route8UnifiedEntries data object).filter
    (Route8DemandPinnedAt data object)

/-- Membership in the named pinned family is exactly clause (L1), with no
change of entry family or carrier core. -/
theorem mem_route8DemandPinned (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (index : Graph.Route8Census.Index object) :
    index ∈ route8DemandPinned data object ↔
      index ∈ route8UnifiedEntries data object ∧
        Route8DemandPinnedAt data object index := by
  classical
  simp only [route8DemandPinned, Finset.mem_filter]

noncomputable section

section Route8DemandLedgerRecord

variable (data : Parameters) (object : Graph.FiniteObject.{u})

attribute [local instance] Graph.Route8.vertexDecEq

/-- The literal demand-ledger data.  Its fields are exactly clauses (L1)--(L5);
packaging them prevents kernel reduction of the finite vertex schedule when a
later row merely reads the already committed ledger. -/
structure Route8DemandLedgerRecord where
  partition : Graph.DemandPartition.Partition
    (route8UnifiedEntries data object) (route8DemandCore data object)
  pinned : Graph.DemandPartition.Partition.Pinned
        (route8DemandPinned data object)
        (Graph.Route8.indexedPrivateCoreCarriers
          (route8UnifiedEntries data object) (route8DemandCore data object))
        partition
  maximal : ∀ Q : Graph.DemandPartition.Partition
          (route8UnifiedEntries data object) (route8DemandCore data object),
        Graph.DemandPartition.Partition.Pinned
          (route8DemandPinned data object)
          (Graph.Route8.indexedPrivateCoreCarriers
            (route8UnifiedEntries data object) (route8DemandCore data object)) Q →
        Q.three.card ≤ partition.three.card ∧
          (Q.three.card = partition.three.card →
            Q.two.card ≤ partition.two.card)
  rawNoOvercount : 3 * partition.three.card + 2 * partition.two.card ≤
        object.boundaryIncidence
          (object.remainderSupport (canonicalWindowPacking data object))
  defectNoOvercount : 3 * (route8UnifiedEntries data object).card ≤
        object.boundaryIncidence
          (object.remainderSupport (canonicalWindowPacking data object)) +
          partition.externalDefect
  records : ∀ index ∈ partition.two ∪ partition.residual,
        Graph.Route8.TraceBasin.TraceLocalTargetDefect object index.1
            data.threshold data.LengthOK index.2.1 index.2.2
            (Graph.Route8Census.basin object data.threshold index) →
          Graph.Route8.TraceBasin.CanonicalDemandRecord object
            (Graph.Route8Census.basin object data.threshold index)
            data.LengthOK

/-- The exact ledger fact is the existence of the record above. -/
abbrev Route8DemandLedgerStatement : Prop :=
  Nonempty (Route8DemandLedgerRecord data object)

end Route8DemandLedgerRecord

end

/-- **`def:typeA-unified-negative`**, on the literal active remainder.

The component filter is exactly
`σ(X) = 0`, `N₀(X) < 0`, and no decorated Type B handoff.  The natural-number
summand is the discharge-cleared value `s·δ(X) = |V(X)| - s·def⁺(X)`; its
strict positivity is recorded for every member, exactly as in the definition.
No large-budget lower bound, entry classification, carrier theorem, or peeling
invariant is part of this schema. -/
abbrev Route8UnifiedNegative (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let unified := route8UnifiedComponents data object
  ∃ collection : Finset (Finset object.Vertex),
    collection = unified.image (object.pieceSupport support) ∧
      (∀ piece ∈ collection,
        object.ambientSurplus piece data.threshold = 0 ∧
          object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          ¬ HandoffProduced data object packing piece ∧
          0 < piece.card -
            data.dischargeScale * object.positiveDeficiency piece data.threshold) ∧
      ∃ scaledDeficit : Nat,
        scaledDeficit =
          ∑ piece ∈ collection,
            (piece.card -
              data.dischargeScale * object.positiveDeficiency piece data.threshold)

/-- The exact route-8/target-defect classification of one unified entry.

The selected trace basin is either target-complete-minimal, with the canonical
exit-(4) family absent, or alternative (a) is the sole surviving failure and
its load has the canonical exit-(4) witness.  The common lower bound
`alpha >= 2` is `lem:typeA-unified-carriers`. -/
abbrev Route8UnifiedEntryFacts (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (index : Graph.Route8Census.Index object) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let basin := Graph.Route8Census.basin object data.threshold index
  let entry := (Graph.Route8Census.presented object data.threshold data.LengthOK
    index).toEntry (Graph.HasCycleWithLength data.LengthOK)
  Graph.Route8.TraceBasin.select? object index.1 data.threshold index.2.1
      index.2.2 = some basin ∧
    2 ≤ entry.alpha ∧
    (Graph.Route8.TraceBasin.TargetCompleteMinimal object index.1
          data.threshold data.LengthOK index.2.1 index.2.2 basin ∨
      (Graph.Route8.TraceBasin.TraceLocalTargetDefect object index.1
          data.threshold data.LengthOK index.2.1 index.2.2 basin ∧
        (¬ ∃ retained,
          Graph.Route8.TraceBasin.TraceResponseQuotient object index.1
            data.threshold data.LengthOK index.2.1 index.2.2 basin retained) ∧
        ¬ Graph.Route8.TraceBasin.TraceDelocalization object index.1
          data.threshold data.LengthOK index.2.1 index.2.2 basin ∧
        ¬ Graph.Route8.TraceBasin.TraceSurvivingSeparator object index.1
          data.threshold data.LengthOK index.2.1 index.2.2 basin ∧
        ∃ witness : Graph.ExitFour.Witness
            (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold data.dischargeScale
            index.2.1 ∅,
          witness.load = index.2.2))

/-- **`lem:typeA-unified-deficit`** (node `[123]`): the unified collection
carries the whole large-budget deficit, cleared of denominators. -/
abbrev Route8UnifiedDeficitFact (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let components := route8UnifiedComponents data object
  support.card ≤
    Graph.TypeBEnvelopeCharge.route8Deficit object support data.threshold
        data.dischargeScale components +
      data.dischargeScale * (Graph.Route8Census.supply object packing).card +
      data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount

/-- **`def:typeA-unified-entries` with `lem:typeA-unified-carriers` and
`def:typeA-pressure-ledger`** (node `[123]`): the exact per-entry census. -/
abbrev Route8UnifiedEntryCensusFact (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ index ∈ route8UnifiedEntries data object,
    Route8UnifiedEntryFacts data object index

/-- **`lem:typeB-bridge-with-route8-core`'s canonical collection `𝒜_X`** (the
appendix rows for nodes `[74]`/`[76]`/`[85]`: "after any route-8 non-window
core is extracted into `D_A`"), on the literal active remainder.

For every negative positive-surplus canonical piece `X`, the deleted region
`X ∖ centres(X)` — the piece with its high centres deleted, the region
discharged by `Graph.TypeBBridgeMass.bridge_mass_of_centre_deletion` — is
decomposed into its own canonical connected components, and the collection
keeps exactly the components carrying `def:typeA-unified-negative`'s clauses at
the extracted core: `σ = 0`, `N₀ < 0`, no decorated Type B handoff, and every
indexed entry of the core in the quotient-free lane (the `[104]` calibration's
plain trace-response-quotient state occurs at no entry; a component carrying a
profile-record entry is not a route-8 core and stays with the bridge
residual). -/
noncomputable def route8ExtractedCores (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Finset (Finset object.Vertex) := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  exact ((object.canonicalPieces support).filter fun component =>
      object.NegativeNetCharge (object.pieceSupport support component)
          data.threshold data.dischargeScale ∧
        0 < object.ambientSurplus (object.pieceSupport support component)
          data.threshold).biUnion
    fun component =>
      let deleted := object.pieceSupport support component \
        Graph.TypeBRefinedSupport.centres object data.threshold
          (object.pieceSupport support component)
      ((object.canonicalPieces deleted).image
          (object.pieceSupport deleted)).filter fun core =>
        object.ambientSurplus core data.threshold = 0 ∧
          object.NegativeNetCharge core data.threshold data.dischargeScale ∧
          ¬ HandoffProduced data object packing core ∧
          ∀ receiver ∈ object.receivers core data.threshold,
            ∀ load ∈ Graph.VisibleEntry.excessBasinReduced object core
                data.threshold data.dischargeScale receiver ∅,
              ∀ basin : Finset object.Vertex,
                Graph.Route8.TraceBasin.select? object core data.threshold
                    receiver load = some basin →
                  ¬ ∃ retained,
                    Graph.Route8.TraceBasin.TraceResponseQuotient object core
                      data.threshold data.LengthOK receiver load basin retained

/-- **`def:typeA-unified-entries` at the extracted cores**: the indexed entries
`(Y, w, u)` of the members of `𝒜_X` — every receiver of the core with each of
its unpaid excess loads at the empty peeling, exactly the loads
`Graph.TypeBBridgeMass.bridge_mass_of_centre_deletion`'s staged discharge of
the deleted region counts. -/
noncomputable def route8ExtractedEntries (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Finset (Graph.Route8Census.Index object) := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (route8ExtractedCores data object).biUnion fun core =>
    (object.receivers core data.threshold).biUnion fun receiver =>
      (Graph.VisibleEntry.excessBasinReduced object core data.threshold
        data.dischargeScale receiver ∅).image
        fun load => (core, receiver, load)

/-- **`def:typeA-unified-entries` with `lem:typeA-unified-carriers` at the
extracted route-8 cores** (node `[123]`): the exact per-entry census, in the
same schema as the unified collection's own census. -/
abbrev Route8ExtractedEntryCensusFact (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ index ∈ route8ExtractedEntries data object,
    Route8UnifiedEntryFacts data object index

/-- **`D_A(𝒜_X)` summed over the bridge pieces**
(`lem:typeB-bridge-with-route8-core` / `lem:decorated-envelope-with-route8-core`:
"Summing over `Y ∈ 𝒜_X` gives the route-8 core contribution `−D_A(𝒜_X)`"):
the cleared route-8 deficit of the extracted cores, in `route8Deficit`'s own
summand shape. -/
noncomputable def route8ExtractedDeficit (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Nat :=
  ∑ core ∈ route8ExtractedCores data object,
    (core.card -
      data.dischargeScale * object.positiveDeficiency core data.threshold)

/-- The Type B bridge allowance of the stage-rate test of
`thm:large-budget-route8-only`: the two-role allowance `2·F·s·T(n)`. -/
noncomputable abbrev route8StageSlack (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Nat :=
  2 * (data.bridgeMassFactor * data.dischargeScale *
    data.surplusThreshold object.vertexCount)

/-- The terminal stage of the deterministic procedure of
`thm:large-budget-route8-only` on the unified census: the recorded peel chain
at which the procedure stops (a stage where the reduced-rate test fails, or a
stage passing the test with a true two-support entry).  The manuscript runs one
deterministic procedure, so its terminal stage is fixed once and for all; node
`[123]` decides the rate test at exactly this chain. -/
noncomputable def route8DescentChain (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    List (Graph.Route8Census.Index object) :=
  Classical.epsilon fun chain =>
    Graph.Route8Pressure.StageOutcome object (canonicalWindowPacking data object)
      (route8UnifiedEntries data object) (route8UnifiedComponents data object)
      data.threshold data.dischargeScale (route8StageSlack data object)
      data.LengthOK chain

/-- **Node `[123]`, yes**: the reduced-rate test passes at the terminal stage of
the descent (`thm:large-budget-route8-only`: the stage then carries a true
two-support route-8 entry, the input of node `[124]`). -/
noncomputable abbrev Route8StageRateStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.Route8Pressure.StageRate object (canonicalWindowPacking data object)
    data.threshold data.dischargeScale (route8StageSlack data object)
    (route8DescentChain data object).toFinset

/-- **Node `[123]`, no (failed reduced rate)**: the exact negation of
`Route8StageRateStatement` at the same terminal stage.  Its peel chain and
stage accounting are the node-`[123]` descent fact
`Route8PeelingDescentStatement`; this arm is routed to node `[181]`, it is not
a contradiction. -/
noncomputable abbrev Route8StageRateFailedFact (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ¬ Route8StageRateStatement data object

open scoped Classical in
/-- **`def:typeA-pressure-absorbers` with
`lem:typeA-pressure-absorber-no-overcount`**, on the committed maximal
2/3-demand ledger: the demand units `𝒰_press` of the unpaid classes carry a
type-(A1)/(A2) absorption — a single-use assignment of fresh boundary
incidences of the **same support as the owning entry** to the absorbed units,
disjoint from every ledger assignment, together with a disjoint type-(A2)
dependence set; with
the type-(A2) set held, no fresh single-use assignment absorbs more units —
whose open remainder `𝖯_open = |𝒰_press ∖ 𝒰_abs|` satisfies the
subtraction-free display `3Ñ ≤ e(R, W) + B_dep + 𝖯_open`, the manuscript's
`3Ñ − 𝖯_open ≤ def⁺(R) + B_dep`. -/
noncomputable def Route8DemandAbsorptionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let entries := route8UnifiedEntries data object
  let core := Graph.Route8Census.core object data.threshold data.LengthOK
  let pinned := entries.filter fun index =>
    Graph.Route8.TraceBasin.TargetCompleteMinimal object index.1 data.threshold
        data.LengthOK index.2.1 index.2.2
        (Graph.Route8Census.basin object data.threshold index) ∧
      data.threshold ≤
        Graph.Route8.indexedPrivateCoreCount entries core index
  ∀ P : Graph.DemandPartition.Partition entries core,
    Graph.DemandPartition.Partition.Pinned pinned
        (Graph.Route8.indexedPrivateCoreCarriers entries core) P →
      (∀ Q : Graph.DemandPartition.Partition entries core,
        Graph.DemandPartition.Partition.Pinned pinned
          (Graph.Route8.indexedPrivateCoreCarriers entries core) Q →
        Q.three.card ≤ P.three.card ∧
          (Q.three.card = P.three.card → Q.two.card ≤ P.two.card)) →
      3 * P.three.card + 2 * P.two.card ≤
          object.boundaryIncidence
            (object.remainderSupport (canonicalWindowPacking data object)) →
      3 * entries.card ≤
          object.boundaryIncidence
            (object.remainderSupport (canonicalWindowPacking data object)) +
            P.externalDefect →
      ∃ (A : Graph.DemandPartition.Absorption P
            (Graph.Route8Census.Index object × Nat))
        (dep : Finset (Graph.Route8Census.Index object × Nat)),
        A.absorbed ⊆ P.demandUnits ∧
        (∀ υ ∈ A.absorbed, A.absorber υ ∈
          Graph.Route8Census.supply object
            (canonicalWindowPacking data object)) ∧
          (∀ υ ∈ A.absorbed,
            A.absorber υ ∈ Graph.Route8.cutEdges object υ.1.1) ∧
          dep ⊆ P.demandUnits ∧
          Disjoint A.absorbed dep ∧
          dep = ∅ ∧
          (∀ B : Graph.DemandPartition.Absorption P
              (Graph.Route8Census.Index object × Nat),
            B.absorbed ⊆ P.demandUnits →
            (∀ υ ∈ B.absorbed, B.absorber υ ∈
              Graph.Route8Census.supply object
                (canonicalWindowPacking data object)) →
            (∀ υ ∈ B.absorbed,
              B.absorber υ ∈ Graph.Route8.cutEdges object υ.1.1) →
            Disjoint B.absorbed dep →
            B.absorbed.card ≤ A.absorbed.card) ∧
          3 * entries.card ≤
            object.boundaryIncidence
              (object.remainderSupport (canonicalWindowPacking data object)) +
              dep.card + (P.demandUnits \ (A.absorbed ∪ dep)).card

open scoped Classical in
/-- Maximal same-support absorption rules out the unused-incidence
certificate (O2) on every remaining open demand unit. -/
noncomputable def Route8OpenBoundarySaturatedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let entries := route8UnifiedEntries data object
  let core := Graph.Route8Census.core object data.threshold data.LengthOK
  let pinned := entries.filter fun index =>
    Graph.Route8.TraceBasin.TargetCompleteMinimal object index.1 data.threshold
        data.LengthOK index.2.1 index.2.2
        (Graph.Route8Census.basin object data.threshold index) ∧
      data.threshold ≤
        Graph.Route8.indexedPrivateCoreCount entries core index
  ∀ P : Graph.DemandPartition.Partition entries core,
    Graph.DemandPartition.Partition.Pinned pinned
        (Graph.Route8.indexedPrivateCoreCarriers entries core) P →
      (∀ Q : Graph.DemandPartition.Partition entries core,
        Graph.DemandPartition.Partition.Pinned pinned
          (Graph.Route8.indexedPrivateCoreCarriers entries core) Q →
        Q.three.card ≤ P.three.card ∧
          (Q.three.card = P.three.card → Q.two.card ≤ P.two.card)) →
      3 * P.three.card + 2 * P.two.card ≤
          object.boundaryIncidence
            (object.remainderSupport (canonicalWindowPacking data object)) →
      3 * entries.card ≤
          object.boundaryIncidence
            (object.remainderSupport (canonicalWindowPacking data object)) +
            P.externalDefect →
      ∃ (A : Graph.DemandPartition.Absorption P
            (Graph.Route8Census.Index object × Nat))
        (dep : Finset (Graph.Route8Census.Index object × Nat)),
        A.absorbed ⊆ P.demandUnits ∧
        (∀ υ ∈ A.absorbed, A.absorber υ ∈
          Graph.Route8Census.supply object
            (canonicalWindowPacking data object)) ∧
          (∀ υ ∈ A.absorbed,
            A.absorber υ ∈ Graph.Route8.cutEdges object υ.1.1) ∧
          dep ⊆ P.demandUnits ∧
          Disjoint A.absorbed dep ∧
          dep = ∅ ∧
          (∀ B : Graph.DemandPartition.Absorption P
              (Graph.Route8Census.Index object × Nat),
            B.absorbed ⊆ P.demandUnits →
            (∀ υ ∈ B.absorbed, B.absorber υ ∈
              Graph.Route8Census.supply object
                (canonicalWindowPacking data object)) →
            (∀ υ ∈ B.absorbed,
              B.absorber υ ∈ Graph.Route8.cutEdges object υ.1.1) →
            Disjoint B.absorbed dep →
            B.absorbed.card ≤ A.absorbed.card) ∧
          3 * entries.card ≤
            object.boundaryIncidence
              (object.remainderSupport (canonicalWindowPacking data object)) +
              dep.card + (P.demandUnits \ (A.absorbed ∪ dep)).card ∧
          ∀ unit ∈ P.demandUnits \ (A.absorbed ∪ dep),
            ∀ carrier : Sym2 object.Vertex,
              carrier ∈ Graph.Route8.cutEdges object unit.1.1 →
              (∀ index ∈ P.three ∪ P.two, carrier ∉ P.assigned index) →
              ∃ other ∈ A.absorbed, A.absorber other = carrier

open scoped Classical in
/-- **`def:typeA-open-window-blocker` with
`lem:typeA-open-window-blocker-count`**, on the committed ledger and
absorption.  For every open demand unit this stores the complete blocker pair:
an actual available carrier edge of its owner and the packed window containing
the edge's endpoint outside the remainder.  Thus the carrier/window
correlation is retained rather than projected to a window label.  The open
demand is exactly the window-blocker load partition
`𝖯_open = Σ_P B_open(P)`.  The concrete lexicographic blocker choice is a
classical witness, as everywhere in this lane. -/
noncomputable def Route8WindowBlockersStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let entries := route8UnifiedEntries data object
  let core := Graph.Route8Census.core object data.threshold data.LengthOK
  let pinned := entries.filter fun index =>
    Graph.Route8.TraceBasin.TargetCompleteMinimal object index.1 data.threshold
        data.LengthOK index.2.1 index.2.2
        (Graph.Route8Census.basin object data.threshold index) ∧
      data.threshold ≤
        Graph.Route8.indexedPrivateCoreCount entries core index
  ∀ P : Graph.DemandPartition.Partition entries core,
    Graph.DemandPartition.Partition.Pinned pinned
        (Graph.Route8.indexedPrivateCoreCarriers entries core) P →
      (∀ Q : Graph.DemandPartition.Partition entries core,
        Graph.DemandPartition.Partition.Pinned pinned
          (Graph.Route8.indexedPrivateCoreCarriers entries core) Q →
        Q.three.card ≤ P.three.card ∧
          (Q.three.card = P.three.card → Q.two.card ≤ P.two.card)) →
      3 * P.three.card + 2 * P.two.card ≤
          object.boundaryIncidence
            (object.remainderSupport (canonicalWindowPacking data object)) →
      3 * entries.card ≤
          object.boundaryIncidence
            (object.remainderSupport (canonicalWindowPacking data object)) +
            P.externalDefect →
      ∀ (A : Graph.DemandPartition.Absorption P
            (Graph.Route8Census.Index object × Nat))
        (dep : Finset (Graph.Route8Census.Index object × Nat)),
        A.absorbed ⊆ P.demandUnits →
        (∀ υ ∈ A.absorbed, A.absorber υ ∈
          Graph.Route8Census.supply object
            (canonicalWindowPacking data object)) →
        dep ⊆ P.demandUnits →
        Disjoint A.absorbed dep →
        ∃ carrier : Graph.Route8Census.Index object × Nat →
            Sym2 object.Vertex,
          ∃ blocker : Graph.Route8Census.Index object × Nat →
              Finset object.Vertex,
            (∀ υ ∈ P.demandUnits \ (A.absorbed ∪ dep),
              carrier υ ∈ core υ.1 ∧
                ∃ inside ∈ carrier υ, ∃ outside ∈ carrier υ,
                  inside ∈ object.remainderSupport
                      (canonicalWindowPacking data object) ∧
                    outside ∉ object.remainderSupport
                      (canonicalWindowPacking data object) ∧
                    outside ∈ blocker υ ∧
                    blocker υ ∈ canonicalWindowPacking data object) ∧
            (P.demandUnits \ (A.absorbed ∪ dep)).card =
              ∑ window ∈ canonicalWindowPacking data object,
                ((P.demandUnits \ (A.absorbed ∪ dep)).filter
                  fun υ => blocker υ = window).card

noncomputable section

section Route8UnpaidExitFourRecords

variable (data : Parameters) (object : Graph.FiniteObject.{u})

attribute [local instance] Graph.Route8.vertexDecEq

/-- **The no-witness arm of the maximal-ledger reduction.**  This is the
existing `route8UnifiedTrueTwoCarrierEntry` fact schema, named explicitly so
the decision row can state its two arm types without normalizing the complete
`Holds` registry. -/
structure Route8UnifiedTrueTwoCarrierEntryRecord where
  index : Graph.Route8Census.Index object
  indexMem : index ∈ route8UnifiedEntries data object
  twoCarrier : Graph.Route8.IndexedTwoCarrierCore
        (route8UnifiedEntries data object) (route8DemandCore data object)
        (data.threshold - 1) index
  entryFacts : Route8UnifiedEntryFacts data object index
  minimal : letI : DecidableEq object.Vertex := object.vertices.decEq
    Graph.Route8.TraceBasin.TargetCompleteMinimal object index.1
        data.threshold data.LengthOK index.2.1 index.2.2
        (Graph.Route8Census.basin object data.threshold index)
  noExitFour : ¬ ∃ witness : Graph.ExitFour.Witness
          (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold
          data.dischargeScale index.2.1 ∅,
        witness.load = index.2.2

abbrev Route8UnifiedTrueTwoCarrierEntryStatement : Prop :=
  Nonempty (Route8UnifiedTrueTwoCarrierEntryRecord data object)

/-- A maximal pinned `2/3`-demand ledger on the unified entries
(`def:typeA-pressure-ledger`): clause (L1) pins every minimal entry holding
`δ` private essential incidences, and among such ledgers the lexicographic
maximum of `(N₃, N₂)` is taken. -/
abbrev Route8MaximalDemandPartition
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object)) :
    Prop :=
  Graph.DemandPartition.Partition.Pinned (route8DemandPinned data object)
      (Graph.Route8.indexedPrivateCoreCarriers
        (route8UnifiedEntries data object) (route8DemandCore data object)) P ∧
    ∀ Q : Graph.DemandPartition.Partition
        (route8UnifiedEntries data object) (route8DemandCore data object),
      Graph.DemandPartition.Partition.Pinned (route8DemandPinned data object)
          (Graph.Route8.indexedPrivateCoreCarriers
            (route8UnifiedEntries data object) (route8DemandCore data object)) Q →
        Q.three.card ≤ P.three.card ∧
          (Q.three.card = P.three.card → Q.two.card ≤ P.two.card)

/-- **(168.1) of `thm:typeA-unpaid-exit4-reduction`** (node `[181]`): every
unpaid entry `ξ ∈ Ξ₂(P) ∪ Ξ_res(P)` of a maximal ledger has at most `δ − 1`
(the manuscript's two) private essential incidences. -/
abbrev Route8UnpaidTwoCarrierStatement : Prop :=
  ∀ P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object),
    Route8MaximalDemandPartition data object P →
      ∀ index ∈ P.two ∪ P.residual,
        Graph.Route8.IndexedTwoCarrierCore
          (route8UnifiedEntries data object) (route8DemandCore data object)
          (data.threshold - 1) index

/-- **Node `[181]`, yes (outcome (i) of `thm:typeA-unpaid-exit4-reduction`)**:
some unpaid entry of a maximal ledger has no exit-`(4)` witness. -/
abbrev Route8UnpaidWitnessFreeStatement : Prop :=
  ∃ P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object),
    Route8MaximalDemandPartition data object P ∧
      ∃ index ∈ P.two ∪ P.residual,
        ¬ ∃ witness : Graph.ExitFour.Witness
            (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold
            data.dischargeScale index.2.1 ∅,
          witness.load = index.2.2

/-- **Node `[181]`, no = node `[183]` (outcome (ii), (168.2))**: the exact
negation of `Route8UnpaidWitnessFreeStatement` -- every unpaid entry of every
maximal ledger carries its canonical exit-`(4)` witness. -/
abbrev Route8UnpaidExitFourResidualStatement : Prop :=
  ∀ P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object),
    Route8MaximalDemandPartition data object P →
      ∀ index ∈ P.two ∪ P.residual,
        ∃ witness : Graph.ExitFour.Witness
            (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold
            data.dischargeScale index.2.1 ∅,
          witness.load = index.2.2

end Route8UnpaidExitFourRecords

end

open scoped Classical in
/-- **`lem:typeA-unified-visible-ownership`** (node `[184]`).

This statement leaves the unified entry family unchanged.  It records the
strict structural exhaustion of its silent ownership profile: every indexed
load belongs to the actual visible-load family at its own support and
receiver, and the filtered silent subfamily therefore has cardinality zero. -/
noncomputable def Route8UnifiedVisibleResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let entries := route8UnifiedEntries data object
  (∀ index ∈ entries,
      index.2.2 ∈ Graph.VisibleEntry.visibleLoads object index.1
        data.threshold index.2.1) ∧
    (entries.filter fun index =>
      index.2.2 ∉ Graph.VisibleEntry.visibleLoads object index.1
        data.threshold index.2.1).card = 0

open scoped Classical in
/-- **`lem:typeA-unified-visible-overload`** (node `[185]`).

The entry family is still the literal unified visible-first excess family.
For every entry, its receiver has a canonical visible-four package at the
empty peeling.  Equivalently, the subfamily whose receiver has no overloaded
completion port is empty. -/
noncomputable def Route8UnifiedVisibleOverloadStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let entries := route8UnifiedEntries data object
  (∀ index ∈ entries,
      Nonempty (Graph.ExitFour.VisibleFourUnpeeledPackage index.1
        data.threshold data.dischargeScale index.2.1 ∅)) ∧
    (entries.filter fun index =>
      ¬ Graph.ExitFour.VisibleFourUnpeeledAt index.1 data.threshold
        data.dischargeScale index.2.1 ∅).card = 0

open scoped Classical in
/-- The exact visible history retained at node `[185]`.

The first conjunct keeps the literal node-`[123]` peel chain and its stage
accounting.  The second exposes the selected node-`[93]` support, receiver and
*current* peeling set from `typeAExitSevenFree`; node `[184]` removes its
silent alternative, so the surviving package is at that same peeling set.
For every Q1 origin pair, the two distinct loads, scheduled graph returns and
`VisibleFor` certificates are the objects already owned by that package.  Its
pairwise target-completeness is read from the original exit-`(4)`-free fact,
not postulated for a different quotient. -/
noncomputable def Route8UnifiedVisibleHistoryStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (∃ chain : List (Graph.Route8Census.Index object),
    Graph.Route8Pressure.PeelChain object (canonicalWindowPacking data object)
        (route8UnifiedEntries data object) data.threshold data.dischargeScale
        (route8StageSlack data object) data.LengthOK chain ∧
      Graph.Route8Pressure.StageAccounting object
        (canonicalWindowPacking data object) (route8UnifiedEntries data object)
        (route8UnifiedComponents data object) data.threshold
        data.dischargeScale (route8StageSlack data object) chain ∧
      ¬ Graph.Route8Pressure.StageRate object
          (canonicalWindowPacking data object) data.threshold
          data.dischargeScale (route8StageSlack data object) chain.toFinset) ∧
    SelectedNoExitSixReceiverWith data object
      (fun packing piece receiver peeled =>
        ¬ HandoffProduced data object packing piece ∧
          ¬ Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
            data.dischargeScale receiver peeled ∧
          ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
              data.threshold data.dischargeScale receiver peeled,
            (¬ ∃ witness : Graph.ExitFour.Witness
                (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
                data.dischargeScale receiver peeled,
              ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                  data.threshold data.dischargeScale receiver package.outside
                  peeled,
                witness.load = load) ∧
              ∀ pair : package.Q1OriginPair,
                pair.leftReturn ∈
                    (Graph.VisibleEntry.ReceiverEntryReturn.schedule object
                      piece receiver package.outside).values ∧
                  Graph.VisibleEntry.VisibleFor object piece data.threshold
                    pair.leftReturn pair.left.1 ∧
                  pair.rightReturn ∈
                    (Graph.VisibleEntry.ReceiverEntryReturn.schedule object
                      piece receiver package.outside).values ∧
                  Graph.VisibleEntry.VisibleFor object piece data.threshold
                    pair.rightReturn pair.right.1 ∧
                  Graph.Response.TargetComplete
                    Graph.BoundaryPiece.boundaryDegreeProfile
                    (Graph.HasCycleWithLength data.LengthOK)
                    (Graph.ExitFour.visibleResponsePiece pair.leftResponseCoordinate)
                    (Graph.ExitFour.visibleResponsePiece pair.rightResponseCoordinate))

open scoped Classical in
/-- **`lem:typeA-unified-joint-balance`** (node `[186]`).

This is the simultaneous, subtraction-free accounting of the literal
visible-overload residual.  It does not choose a new graph, entry family, or
support.  The witnesses are the peel chain and the committed maximal demand
partition/absorption already supplied at node `[181]`; `unused` is exactly
the slack between the unified deficit and the full entry count. -/
noncomputable def Route8JointBalanceStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let entries := route8UnifiedEntries data object
  let components := route8UnifiedComponents data object
  let core := route8DemandCore data object
  let supply := Graph.Route8Census.supply object packing
  let bridgeAllowance := data.bridgeMassFactor * data.dischargeScale *
    data.surplusThreshold object.vertexCount
  Route8UnifiedVisibleOverloadStatement data object ∧
    (∀ component ∈ components,
      let piece := object.pieceSupport support component
      ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        object.routedLoads piece data.threshold receiver ⊆
          Graph.VisibleEntry.visibleLoads object piece data.threshold receiver) ∧
    (∀ component ∈ components,
      let piece := object.pieceSupport support component
      ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        ∀ peeled : Finset object.Vertex,
          ¬ Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
            data.dischargeScale receiver peeled) ∧
    ∃ chain : List (Graph.Route8Census.Index object),
      Graph.Route8Pressure.PeelChain object packing entries data.threshold
          data.dischargeScale (2 * bridgeAllowance) data.LengthOK chain ∧
        Graph.Route8Pressure.StageAccounting object packing entries components
          data.threshold data.dischargeScale (2 * bridgeAllowance) chain ∧
        ∃ P : Graph.DemandPartition.Partition entries core,
          Graph.DemandPartition.Partition.Pinned
              (route8DemandPinned data object)
              (Graph.Route8.indexedPrivateCoreCarriers entries core) P ∧
            (∀ Q : Graph.DemandPartition.Partition entries core,
              Graph.DemandPartition.Partition.Pinned
                  (route8DemandPinned data object)
                  (Graph.Route8.indexedPrivateCoreCarriers entries core) Q →
                Q.three.card ≤ P.three.card ∧
                  (Q.three.card = P.three.card →
                    Q.two.card ≤ P.two.card)) ∧
            ∃ A : Graph.DemandPartition.Absorption P
                (Graph.Route8Census.Index object × Nat),
              A.absorbed ⊆ P.demandUnits ∧
                (∀ unit ∈ A.absorbed, A.absorber unit ∈ supply) ∧
                (∀ unit ∈ A.absorbed,
                  A.absorber unit ∈ Graph.Route8.cutEdges object unit.1.1) ∧
                (∀ B : Graph.DemandPartition.Absorption P
                    (Graph.Route8Census.Index object × Nat),
                  B.absorbed ⊆ P.demandUnits →
                    (∀ unit ∈ B.absorbed, B.absorber unit ∈ supply) →
                    (∀ unit ∈ B.absorbed,
                      B.absorber unit ∈
                        Graph.Route8.cutEdges object unit.1.1) →
                    B.absorbed.card ≤ A.absorbed.card) ∧
                ∃ unused : Nat,
                  let peeled := chain.toFinset
                  let deficit := Graph.TypeBEnvelopeCharge.route8Deficit object
                    support data.threshold data.dischargeScale components
                  let openUnits := P.demandUnits \ A.absorbed
                  peeled.card ≤ deficit ∧
                    deficit ≤ entries.card ∧
                    entries.card = deficit + unused ∧
                    support.card ≤ deficit +
                      data.dischargeScale * supply.card + bridgeAllowance ∧
                    3 * entries.card ≤ supply.card + openUnits.card ∧
                    3 * support.card ≤
                      (3 * data.dischargeScale + 1) * supply.card +
                        3 * bridgeAllowance + openUnits.card ∧
                    data.threshold * support.card ≤
                      (data.threshold * data.dischargeScale + 1) * supply.card +
                        data.threshold * (2 * bridgeAllowance) +
                        data.threshold * peeled.card ∧
                    3 * entries.card =
                      (3 * P.three.card + 2 * P.two.card) +
                        P.demandUnits.card ∧
                    P.demandUnits.card =
                      A.absorbed.card + openUnits.card ∧
                    3 * P.three.card + 2 * P.two.card + A.absorbed.card ≤
                      supply.card

/-- Node `[111]`, `def:typeA-large-budget-deficit`: extract the canonical
collection `𝒳_A` of Type A pieces all of whose saturated receivers survive in
the route-`8` residual, and name its deficit.  The value below is the cleared
quantity `s · D_A(𝒳_A)`, with `s = data.dischargeScale`; it is exactly
`Graph.TypeBEnvelopeCharge.route8Deficit` on the component collection.  The
basin burden and the large-budget lower bound belong to `[112]` and `[113]` and
are deliberately absent here. -/
abbrev Route8GlobalSqueeze (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  ∃ collection : Finset (Finset object.Vertex),
    collection = routeEight.image (object.pieceSupport support) ∧
      ∃ scaledDeficit : Nat,
        scaledDeficit =
          Graph.TypeBEnvelopeCharge.route8Deficit object support
            data.threshold data.dischargeScale routeEight

/-- Node `[112]`, `lem:typeA-route8-burden`, cleared by the registered scale.

`basinCount` is exactly
`Σ_{X ∈ 𝒳_A} Σ_w |𝒰_X(w)|`; membership in `Route8Survives` supplies the
selected target-complete-minimal basin attached to every indexed unpaid silent
load.  The final inequality is therefore
`s · D_A(𝒳_A) ≤ N_basin(𝒳_A)`.  The large-budget lower bound belongs only to
node `[113]`. -/
abbrev Route8BasinBurden (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  ∃ basinCount : Nat,
    basinCount =
      ∑ component ∈ routeEight,
        ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers object
            (object.pieceSupport support component) data.threshold
            data.dischargeScale,
          (Graph.VisibleEntry.silentExcess object
            (object.pieceSupport support component) data.threshold
            data.dischargeScale receiver).card ∧
      ∃ scaledDeficit : Nat,
        scaledDeficit =
          Graph.TypeBEnvelopeCharge.route8Deficit object support
            data.threshold data.dischargeScale routeEight ∧
          scaledDeficit ≤ basinCount

/-- Node `[113]`, `def:typeA-large-budget-deficit`, in exact finite form.

The paper's inequality
`D_A(𝒳_A) ≥ (1/4 - τ_win)|R| - o(|R|)` is cleared by the registered discharge
scale `s`: `|R| ≤ s D_A(𝒳_A) + s |∂R| + o(|R|)`.  The first summand below is
exactly `s D_A(𝒳_A)`, `boundaryIncidence` is the finite stub supply defining
`τ_win`, and the registered Type B bridge allowance is the explicit finite
representative of the sublinear term.  The canonical packing and
`Route8Survives` filter are definitionally the collection fixed at `[111]`; no
upstream burden fact is republished inside this key.

The manuscript's later unified-demand correction observes that this fact does
not follow merely from `LargeBudgetResidual`: target-defect Type A supports may
carry the missing mass.  Consequently node `[113]` is tested exactly, and its
complement is routed to node `[123]` rather than being fabricated. -/
abbrev Route8LargeBudgetDeficit (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  support.card ≤
    Graph.TypeBEnvelopeCharge.route8Deficit object support
        data.threshold data.dischargeScale routeEight +
      data.dischargeScale * object.boundaryIncidence support +
      data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount

/-- Node `[114]`: every indexed entry of the selected canonical route-`8`
collection passes to the essential carrier core of its graph-derived
trace-basin reading.  The quantifiers below are the actual `(X,w,u,B_u)`
indices of `[111]`--`[112]`; no arbitrary `PresentedEntry` can be supplied by a
caller.  The large-budget inequality remains available from the literal
`[113]` ledger ancestry and is not republished inside this key. -/
abbrev Route8CarrierCore (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  ∀ component ∈ routeEight,
    let piece := object.pieceSupport support component
    ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
        data.threshold data.dischargeScale,
      ∀ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
          data.dischargeScale receiver,
        let index : Graph.Route8Census.Index object := (piece, receiver, load)
        let presented := Graph.Route8Census.presented object data.threshold
          data.LengthOK index
        (presented.toEntry
          (Graph.HasCycleWithLength data.LengthOK)).CarrierCoreFacts

/-- Node `[114]`, `def:typeA-true-route8-residual`, on the exact collection
selected at `[111]`.

The first conjunct is clause (R3), the literal admissible silent-core profile
already committed at `[110]`.  For every actual `(X,w,u,B_u)` index, membership
in `saturatedReceivers` exposes (R1); `SilentFirst` records the absence of the
visible exits (1)--(3); and `TargetCompleteMinimal` at the canonical selected
basin records both the absence of the trace-response exits (4)--(7) and (R4).
The carrier-core fact committed immediately before this one stays in the
incoming ledger and is not republished here. -/
abbrev Route8TrueResidual (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  SilentCoreResidualProfile data object ∧
    ∀ component ∈ routeEight,
      let piece := object.pieceSupport support component
      Graph.Route8Deficit.SilentFirst object piece data.threshold
          data.dischargeScale ∧
        ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
            data.threshold data.dischargeScale,
          object.IsReceiver piece data.threshold receiver ∧
            object.Saturated piece data.threshold data.dischargeScale receiver ∧
            ∀ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
                data.dischargeScale receiver,
              let index : Graph.Route8Census.Index object :=
                (piece, receiver, load)
              let basin := Graph.Route8Census.basin object data.threshold index
              Graph.Route8.TraceBasin.select? object piece data.threshold
                    receiver load = some basin ∧
                Graph.Route8.TraceBasin.TargetCompleteMinimal object piece
                    data.threshold data.LengthOK receiver load basin ∧
                  ¬ ∃ witness : Graph.ExitFour.Witness
                      (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                      receiver ∅,
                    witness.load = load

/-- Node `[114]`, `lem:typeA-carrier-cut-parity`, at the exact indexed entries
selected by `[111]` and restricted to their canonical essential carrier cores.

`CoordinateEvent` is the graph-derived simple cycle obtained by adjoining the
root edge to an edge-rooted return (and is already a simple cycle when the
event began as one).  The two edge hypotheses below are therefore the paper's
literal mixed-event hypothesis: one event edge has both ends in `B_u`, and one
event edge has an end outside `X`.  Membership in `retained essentialCore` is
exactly survival in `rho_u(B_u)|_{C_ess(xi)}`.  The conclusion counts the
distinct boundary incidences recorded by the coordinate that lie in
`C_ess(xi)`; it makes no assertion about non-mixed coordinates. -/
abbrev Route8CarrierCutParity (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  ∀ component ∈ routeEight,
    let piece := object.pieceSupport support component
    ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
        data.threshold data.dischargeScale,
      ∀ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
          data.dischargeScale receiver,
        let index : Graph.Route8Census.Index object := (piece, receiver, load)
        let basin := Graph.Route8Census.basin object data.threshold index
        let presented := Graph.Route8Census.presented object data.threshold
          data.LengthOK index
        let entry := presented.toEntry
          (Graph.HasCycleWithLength data.LengthOK)
        ∀ coordinate ∈ entry.retained entry.essentialCore,
          ∀ event : Graph.Route8.CoordinateEvent object,
            presented.event? coordinate = some event →
              (∃ left right : object.Vertex,
                s(left, right) ∈ event.walk.edges ∧
                  left ∈ basin ∧ right ∈ basin) →
              (∃ left right : object.Vertex,
                s(left, right) ∈ event.walk.edges ∧
                  (left ∉ piece ∨ right ∉ piece)) →
              2 ≤ (entry.car coordinate ∩ entry.essentialCore).card

/-- Node `[115]`, yes arm, on the literal collection selected at `[111]`.
There is an actual `(X,w,u,B_u)` entry whose canonical essential incidence
core has cardinality at most one. -/
abbrev Route8SmallCoreEntry (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
    letI : DecidableEq object.Vertex := object.vertices.decEq
    let packing := canonicalWindowPacking data object
    let support := object.remainderSupport packing
    let routeEight : Finset
        (Graph.SupportComponents.Connected.Component object support) := by
      classical
      exact (object.canonicalPieces support).filter
        (Route8Survives data object packing)
    ∃ component ∈ routeEight,
      let piece := object.pieceSupport support component
      ∃ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        ∃ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
            data.dischargeScale receiver,
          let index : Graph.Route8Census.Index object := (piece, receiver, load)
          ((Graph.Route8Census.presented object data.threshold data.LengthOK index).toEntry
            (Graph.HasCycleWithLength data.LengthOK)).alpha ≤ 1

/-- Node `[115]`, no arm, on the same literal collection.  This is the exact
negation of `Route8SmallCoreEntry` after the inherited `[114]` fact has been
kept in the monotone ledger. -/
abbrev Route8NoSmallCoreEntry (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
    letI : DecidableEq object.Vertex := object.vertices.decEq
    let packing := canonicalWindowPacking data object
    let support := object.remainderSupport packing
    let routeEight : Finset
        (Graph.SupportComponents.Connected.Component object support) := by
      classical
      exact (object.canonicalPieces support).filter
        (Route8Survives data object packing)
    ∀ component ∈ routeEight,
      let piece := object.pieceSupport support component
      ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        ∀ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
            data.dischargeScale receiver,
          let index : Graph.Route8Census.Index object := (piece, receiver, load)
          ¬ ((Graph.Route8Census.presented object data.threshold data.LengthOK index).toEntry
            (Graph.HasCycleWithLength data.LengthOK)).alpha ≤ 1

/-- Node `[116]`: for the selected small-core entry, the exact trace-basin
failure alternatives corresponding, in order, to exits `(4)`--`(7)`. -/
abbrev Route8SmallCoreCollapse (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
    letI : DecidableEq object.Vertex := object.vertices.decEq
    let packing := canonicalWindowPacking data object
    let support := object.remainderSupport packing
    let routeEight : Finset
        (Graph.SupportComponents.Connected.Component object support) := by
      classical
      exact (object.canonicalPieces support).filter
        (Route8Survives data object packing)
    ∃ component ∈ routeEight,
      let piece := object.pieceSupport support component
      ∃ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        ∃ load ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
            data.dischargeScale receiver,
          let index : Graph.Route8Census.Index object := (piece, receiver, load)
          let basin := Graph.Route8Census.basin object data.threshold index
          ((Graph.Route8Census.presented object data.threshold data.LengthOK index).toEntry
              (Graph.HasCycleWithLength data.LengthOK)).alpha ≤ 1 ∧
            (Graph.Route8.TraceBasin.TraceLocalTargetDefect object piece
                data.threshold data.LengthOK receiver load basin ∨
              (∃ retained,
                Graph.Route8.TraceBasin.TraceResponseQuotient object piece
                  data.threshold data.LengthOK receiver load basin retained) ∨
              Graph.Route8.TraceBasin.TraceDelocalization object piece
                data.threshold data.LengthOK receiver load basin ∨
              Graph.Route8.TraceBasin.TraceSurvivingSeparator object piece
                data.threshold data.LengthOK receiver load basin)

/-- Node `[118]`: the actual selected two-support census entry together with
the declared deletion witnesses forced by its canonical essential core.

The presented reading, entry family, core family, and selected index are all
the graph-owned `Route8Census` data of the active object.  This is clause (T5)
of `def:typeA-terminal-two-carrier`; no arbitrary presentation or abstract
index family can be supplied by a caller. -/
abbrev Route8CarrierDeletionWitnesses (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  let entries := Graph.Route8Census.entriesOfComponents object packing routeEight
    data.threshold data.dischargeScale
  ∃ index ∈ entries,
    let presented := Graph.Route8Census.presented object data.threshold
      data.LengthOK index
    let entry := presented.toEntry (Graph.HasCycleWithLength data.LengthOK)
    Graph.Route8Census.CollectionTwoCarrierEntry object packing routeEight
        data.threshold data.dischargeScale data.LengthOK index ∧
      Graph.Route8.TwoCarrierDeletionWitnesses (Target :=
        Graph.HasCycleWithLength data.LengthOK) entry.carriers
        entry.coordinates entry.car entry.state entries
        (Graph.Route8Census.core object data.threshold data.LengthOK)
        (data.threshold - 1) index

/-- Nodes `[119]`--`[120]`: the selected private-carrier budget stage on the
same route-`8` residual. -/
abbrev Route8PrivateCarrierBudget (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  let entries := Graph.Route8Census.entriesOfComponents object packing routeEight
    data.threshold data.dischargeScale
  data.threshold * entries.card ≤
    (Graph.Route8Census.supply object packing).card

/-! ## Key statements

The statement each vocabulary key of this family publishes, stated over the
registered parameters and the selected object. -/

/-- The exact negation, retained as the tested residual state
(`def:typeA-two-terminal-pressure-records`' profile lane). -/
noncomputable abbrev Route8QuotientResidualStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ Route8QuotientFreeStatement data object

/-- The exact complement of node `[113]`.  The corrected large-budget
argument must send this arm to the unified target-defect/route-`8` peeling
ledger; it may not infer the route-`8`-only lower bound from the large-budget
branch marker. -/
noncomputable abbrev Route8LargeBudgetDeficitFailsStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- The corrected manuscript's unified-demand arm: the route-8-only
  -- collection does not carry the displayed lower bound, so node `[123]`
  -- must retain the target-defect entries and peel them.
  ¬ Route8LargeBudgetDeficit data object

/-- Nodes `[111]`--`[113]` and `[120]`: the object-level census of the
extracted Type A collection `𝒳_A` — the deficit `|R| ≤ N_basin + s·|∂R|`
(`lem:typeA-route8-burden` in `def:typeA-large-budget-deficit`) and the
private-carrier rate `((δ+1)s+1)·|∂R| < (δ+1)·|R|` (`τ < 3/13`), at the fixed
maximal packing. -/
noncomputable abbrev Route8CensusStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- The two census readings, with the carrier convention of
  -- `def:typeA-terminal-two-carrier`: a two-carrier entry has at most
  -- `δ − 1` (the manuscript's two) private essential carriers, so the
  -- no-two-carrier bound is `δ` per entry and the rate is `τ < δ/(δs+1)`.
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  Graph.Route8Census.CollectionDeficit object packing routeEight
      data.threshold data.dischargeScale
      (data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount) ∧
    Graph.Route8Census.Rate object packing data.threshold data.dischargeScale
      (data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount)

/-- The later unified-demand deficit reading used at node `[123]`,
`|R| ≤ N_basin + s·|∂R| + F·s·T(n)` — `def:typeA-large-budget-deficit` with
`lem:typeA-route8-burden` and the Type B bridge mass of
`prop:typeB-bridge-sublinear` (`o(|R|)`, the registered `F·s·T(n)`). -/
noncomputable abbrev Route8DeficitStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  Graph.Route8Census.Deficit object (canonicalWindowPacking data object)
    data.threshold data.dischargeScale
    (data.bridgeMassFactor * data.dischargeScale *
      data.surplusThreshold object.vertexCount)

/-- Node `[120]`: the private-carrier rate reading of the census alone,
`((δ+1)s+1)·|∂R| + (δ+1)·F·s·T(n) < (δ+1)·|R|` (`τ < 3/13` with the
`o(|R|)` allowance, `rem:route8-carrier-margin`), read from the arm's density
fact. -/
noncomputable abbrev Route8RateStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  Graph.Route8Census.Rate object (canonicalWindowPacking data object)
    data.threshold data.dischargeScale
    (data.bridgeMassFactor * data.dischargeScale *
      data.surplusThreshold object.vertexCount)

/-- The complement of the rate reading on an arm whose density fact does
not decide it (`3/13 ≤ τ`): the manuscript's delicate density interval
(row 2 of the cold-branch ledger), carried as its own branch. -/
noncomputable abbrev Route8RateFailsStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ Graph.Route8Census.Rate object (canonicalWindowPacking data object)
    data.threshold data.dischargeScale
    (data.bridgeMassFactor * data.dischargeScale *
      data.surplusThreshold object.vertexCount)

/-- `thm:branch-kill`'s all-pieces classification: every negative piece of
the canonical decomposition is silent-first when it has no ambient surplus,
and is a Type B bridge component when it has positive surplus.  This is not
node `[111]`, whose sole output is `route8GlobalSqueeze`. -/
noncomputable abbrev Route8PiecesClassifiedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `thm:branch-kill`'s all-pieces classification, exactly as stated: at a
  -- negative zero-surplus piece, an exit-(4) witness for a routed load,
  -- the route-8 residual profile — per saturated receiver, every unpaid
  -- silent-excess and overloaded-port visible load is a route-8 entry or
  -- realizes the exit-(5) plain response quotient (cased), the exact
  -- per-load conclusion `K .typeAExclusion`'s arm 2 delivers
  -- (`lem:typeA-reduced-silent-residual`, `rem:unified-covers-exit4`) —
  -- or a produced decorated Type B handoff; at a negative positive-surplus
  -- piece, the Type B bridge component pair.
  Graph.Route8Deficit.PieceClassification object
    (Graph.HasCycleWithLength data.LengthOK)
    (fun piece =>
      ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        (∀ load ∈ Graph.VisibleEntry.silentExcess object piece
            data.threshold data.dischargeScale receiver,
          Graph.Route8.TraceBasin.Route8Entry object piece data.threshold
              data.LengthOK receiver load ∨
            ∃ basin : Finset object.Vertex,
              Graph.Route8.TraceBasin.select? object piece data.threshold
                  receiver load = some basin ∧
                ∃ retained,
                  Graph.Route8.TraceBasin.TraceResponseQuotient object
                    piece data.threshold data.LengthOK receiver load basin
                    retained) ∧
          ∀ outside ∈ Graph.VisibleEntry.completionPorts object piece
              receiver,
            data.dischargeScale ≤
              (Graph.VisibleEntry.visibleLoadsAt object piece
                data.threshold receiver outside).card →
            ∀ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                data.threshold data.dischargeScale receiver outside ∅,
              Graph.Route8.TraceBasin.Route8Entry object piece
                  data.threshold data.LengthOK receiver load ∨
                ∃ basin : Finset object.Vertex,
                  Graph.Route8.TraceBasin.select? object piece
                      data.threshold receiver load = some basin ∧
                    ∃ retained,
                      Graph.Route8.TraceBasin.TraceResponseQuotient object
                        piece data.threshold data.LengthOK receiver load
                        basin retained)
    (fun piece =>
      HandoffProduced data object (canonicalWindowPacking data object) piece)
    (fun piece =>
      -- `def:typeB-bridge-statements` at the piece: the B2 disjoint ledger
      -- with strictly negative remaining scaled core charge, or a minimal
      -- overlap obstruction (`K .typeBBridgeReduction`'s dichotomy; the
      -- post-ledger hygiene and grouped coverage stay on that key and are
      -- not republished here).
      (∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
          data.threshold data.dischargeScale
          (canonicalWindowPacking data object) piece
          (Graph.TypeBRefinedSupport.centres object data.threshold piece),
        ledger.ExactAugmentedLedgerRefinement ∧
          ¬ (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
            Graph.TypeBRefinedSupport.scaledCoreCharge object
              data.threshold data.dischargeScale piece vertex) ∨
        Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
          data.threshold data.dischargeScale
          (canonicalWindowPacking data object) piece
          (Graph.TypeBRefinedSupport.centres object data.threshold piece)))
    (canonicalWindowPacking data object) data.threshold data.dischargeScale

/-- The number of actual demand units equals the external demand defect. -/
noncomputable abbrev Route8DemandUnitCountStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object),
    P.demandUnits.card = P.externalDefect

/-- The actual corridor/window cycle witnessing a recorded shadow hit. -/
noncomputable abbrev WindowShadowHitCycleStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ (window : SimpleGraph.pathGraph data.windowOrder ↪g object.graph)
    (x y : object.Vertex) (a b : Fin data.windowOrder)
    (corridor : object.graph.Walk x y),
    corridor.IsPath →
    (∀ i : Fin data.windowOrder, window i ∉ corridor.support) →
    object.graph.Adj (window a) x → object.graph.Adj y (window b) →
    s(x, window a) ≠ s(y, window b) →
    b.1 ∈ Graph.WindowAttachmentShadow.shadow data.LengthOK
      data.windowOrder corridor.length a.1 →
    ∃ cycle : object.graph.Walk (window a) (window a),
      cycle.IsCycle ∧
        cycle.length = corridor.length + 2 + Nat.dist a.1 b.1 ∧
        data.LengthOK cycle.length

/-- Selection excludes every recorded shadow hit on the same object. -/
noncomputable abbrev WindowShadowHitExcludedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ (window : SimpleGraph.pathGraph data.windowOrder ↪g object.graph)
    (x y : object.Vertex) (a b : Fin data.windowOrder)
    (corridor : object.graph.Walk x y),
    corridor.IsPath →
    (∀ i : Fin data.windowOrder, window i ∉ corridor.support) →
    object.graph.Adj (window a) x → object.graph.Adj y (window b) →
    s(x, window a) ≠ s(y, window b) →
    b.1 ∉ Graph.WindowAttachmentShadow.shadow data.LengthOK
      data.windowOrder corridor.length a.1

/-- Exact singleton-label safety interpretation of an attachment signature. -/
noncomputable abbrev WindowShadowSignatureStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ support : Finset object.Vertex,
    object.InducesWindow data.windowOrder support →
    ∀ (s : Nat) (a b : Fin data.windowOrder),
      b.1 ∈ Graph.WindowAttachmentShadow.shadow data.LengthOK
          data.windowOrder s a.1 ↔
        ¬ Graph.WindowCurvature.Safe s {a} {b}

/-- The singleton forbidden-distance tail of the window attachment table. -/
noncomputable abbrev WindowShadowSingletonTailStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ support : Finset object.Vertex,
    object.InducesWindow data.windowOrder support →
    ∀ s : Nat, data.windowOrder + 5 ≤ s →
      (Graph.WindowAttachmentShadow.forbiddenDistances
        data.LengthOK data.windowOrder s).card ≤ 1

/-- Node `[117]`, yes: some indexed route-8 entry of `𝒳_A` has at most `δ`
private essential carriers (`prop:typeA-route8-carrier-reduction`). -/
noncomputable abbrev Route8TwoCarrierEntryStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  ∃ index ∈ Graph.Route8Census.entriesOfComponents object packing routeEight
      data.threshold data.dischargeScale,
    Graph.Route8Census.CollectionTwoCarrierEntry object packing routeEight
      data.threshold data.dischargeScale data.LengthOK index

/-- Node `[117]`, no: every indexed route-8 entry has more than `δ` private
essential carriers. -/
noncomputable abbrev Route8NoTwoCarrierEntryStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  ∀ index ∈ Graph.Route8Census.entriesOfComponents object packing routeEight
      data.threshold data.dischargeScale,
    ¬ Graph.Route8Census.CollectionTwoCarrierEntry object packing routeEight
      data.threshold data.dischargeScale data.LengthOK index

/-- Node `[118]`, `thm:large-budget-route8-only`'s two-carrier split: the
selected two-carrier entry is a *true route-8 entry* — its load has no
exit-`(4)` witness at its own receiver (exits `(1)`--`(7)` absent there,
`def:typeA-true-route8-residual`). -/
noncomputable abbrev Route8TrueTwoCarrierEntryStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `def:typeA-true-route8-residual` at the selected two-carrier entry: no
  -- exit-`(4)` witness for its load at its receiver (`Graph.ExitFour.Witness`
  -- with the empty peeling: the load is a routed load of the receiver).
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  ∃ index ∈ Graph.Route8Census.entriesOfComponents object packing routeEight
      data.threshold data.dischargeScale,
    Graph.Route8Census.CollectionTwoCarrierEntry object packing routeEight
      data.threshold data.dischargeScale data.LengthOK index ∧
    ¬ ∃ witness : Graph.ExitFour.Witness (Graph.HasCycleWithLength data.LengthOK)
        index.1 data.threshold data.dischargeScale index.2.1 ∅,
      witness.load = index.2.2

/-- Node `[123]`, `thm:large-budget-route8-only`'s procedure on the object-level
census: from the empty peeling, target-defect peels
(`lem:typeA-pressure-is-exit4-peel`, `lem:typeA-exit4-finite-descent`) reach the
terminal stage `route8DescentChain`: its peel chain is recorded, its exact
stage accounting holds, and it either passes the rate test with a true
two-carrier entry of the peeled ledger or fails the rate test
(`Graph.Route8Pressure.StageOutcome`). -/
noncomputable abbrev Route8PeelingDescentStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  Graph.Route8Pressure.StageOutcome object (canonicalWindowPacking data object)
    (route8UnifiedEntries data object) (route8UnifiedComponents data object)
    data.threshold data.dischargeScale (route8StageSlack data object)
    data.LengthOK (route8DescentChain data object)

/-- The component collection `𝒳_A` of node `[111]`: the canonical pieces all
of whose saturated receivers survive in the route-`8` residual. -/
noncomputable def route8SurvivorComponents (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Finset (Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))) := by
  classical
  exact (object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object))).filter
    (Route8Survives data object (canonicalWindowPacking data object))

/-- **Node `[124]`, `lem:typeA-carrier-deletion-exit`** on a canonical
component collection `𝒳`: every indexed entry of `Ξ(𝒳)` with at most `δ − 1`
(the manuscript's two) private essential incidences carries the canonical
exit-`(4)` witness of its load (clause Q5 of `def:typeA-exit4-family`, through
the carrier-deletion quotient of `lem:typeA-two-carrier-deletion-canonical`).
`thm:typeA-two-carrier-nogo` is this fact against the absent exit `(4)`. -/
noncomputable abbrev Route8TwoCarrierExitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (components : Finset (Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object)))) : Prop :=
  letI : DecidableEq object.Vertex := Graph.Route8.vertexDecEq object
  ∀ index ∈ Graph.Route8Census.entriesOfComponents object
      (canonicalWindowPacking data object) components data.threshold
      data.dischargeScale,
    Graph.Route8.IndexedTwoCarrierCore
        (Graph.Route8Census.entriesOfComponents object
          (canonicalWindowPacking data object) components data.threshold
          data.dischargeScale)
        (Graph.Route8Census.core object data.threshold data.LengthOK)
        (data.threshold - 1) index →
      ∃ witness : Graph.ExitFour.Witness
          (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold
          data.dischargeScale index.2.1 ∅,
        witness.load = index.2.2

end Hypostructure.Graph.Strategy.Spine
