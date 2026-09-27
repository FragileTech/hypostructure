import Hypostructure.Graph.Statements.CanonicalTypeA

/-!
# Statements: TypeA

Proof-agnostic statement definitions of the Type A branch of the
minimum-degree cycle spine: the Type A/Type B split, receiver routing,
saturation, visible entry, the eight saturated exits and the exit-(4) descent.

Every statement is about the one selected counterexample `G` and about the
objects of `G` the ledger has already fixed (`Statements/CanonicalTypeA.lean`):
the canonical packing `P₀`, the node-`[61]` negative support `X₀`, the
node-`[89]` saturated receiver, the node-`[93]` visible receiver and its
overloaded port, the exit-chain receiver, the canonical witnessed peeling
sequence and its terminal set `P₄(w)`, and the canonical exit-`(6)`
delocalization.  An object is pinned in the positive form
`∃ x, obj = some x ∧ Q x`, which is false (never vacuous) when the object is
absent.  Every registered constant is an explicit `Parameters` argument; this
module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u v

/-- Exit `(6)` at a state: some eligible load of the receiver has a selected
trace basin at which an equality of declared coordinates of `ρ_u(B_u)` becomes
target-complete only after adjoining a larger connected support
(`def:typeA-trace-basin` (c), identified with exit `(6)` by
`lem:typeA-reduced-silent-residual`). -/
def ExitSixDelocalizes (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (peeled : Finset object.Vertex) : Prop :=
  ∃ load : object.Vertex,
    EligibleLoadAt data object piece receiver peeled load ∧
      ∃ basin : Finset object.Vertex,
        Graph.Route8.TraceBasin.select? object piece data.threshold
            receiver load = some basin ∧
          Graph.Route8.TraceBasin.TraceDelocalization object piece
            data.threshold data.LengthOK receiver load basin

/-- The complete node-`[94]` certificate at its exact support and selected
receiver.  This is deliberately support- and receiver-indexed: carrying only
an unindexed existential through the shared visible/silent exit chain loses
the identity needed when node `[184]` speaks about the unified entry family. -/
def SilentExitOriginAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex) : Prop :=
  (∀ otherReceiver : object.Vertex,
      object.IsReceiver piece data.threshold otherReceiver →
        object.Saturated piece data.threshold data.dischargeScale
          otherReceiver →
        ¬ Graph.ExitFour.VisibleFourUnpeeledAt piece data.threshold
          data.dischargeScale otherReceiver ∅) ∧
    object.Saturated piece data.threshold data.dischargeScale receiver ∧
    Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
      data.dischargeScale receiver ∅ ∧
    piece.card ≤
      (∑ other ∈ object.receivers piece data.threshold,
        (Graph.VisibleEntry.silentExcess object piece data.threshold
          data.dischargeScale other).card) +
        data.dischargeScale * object.positiveDeficiency piece data.threshold

/-- The literal exit-`(4)`-free alternative at one selected receiver and
peeling set.  On the visible arm, retain the Q1 semantic conclusion for the
same selected package, as well as the original no-witness statement. -/
def ExitFourFreeAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (peeled : Finset object.Vertex) : Prop :=
  (∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
      data.dischargeScale receiver peeled,
    (¬ ∃ witness : Graph.ExitFour.Witness
        (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
        data.dischargeScale receiver peeled,
      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
          data.threshold data.dischargeScale receiver package.outside peeled,
        witness.load = load) ∧
    ∀ pair : package.Q1OriginPair,
      Graph.Response.TargetComplete Graph.BoundaryPiece.boundaryDegreeProfile
        (Graph.HasCycleWithLength data.LengthOK)
        (Graph.ExitFour.visibleResponsePiece pair.leftResponseCoordinate)
        (Graph.ExitFour.visibleResponsePiece pair.rightResponseCoordinate)) ∨
  (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
      data.dischargeScale receiver peeled ∧
    ¬ ∃ witness : Graph.ExitFour.Witness
        (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
        data.dischargeScale receiver peeled,
      witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
        data.dischargeScale receiver peeled)

/-- Exit `(4)` at one selected receiver and peeling set
(`lem:typeA-exit4-residual-routing`): a canonical target-defective quotient of
`def:typeA-exit4-family` whose declared routed-load support contains an unpeeled
load of the lane the state lies in — one of the four selected visible unpeeled
loads when a completion port carries four visible unpeeled returns
(`lem:typeA-unpeeled-visible-routing`), a load of the residual excess `E₄(w)`
otherwise (`lem:typeA-unpeeled-silent-routing`).  The two lanes are exclusive
and, at a saturated state, exhaustive, so this is one predicate of the state,
not a branch. -/
def ExitFourAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (peeled : Finset object.Vertex) : Prop :=
  (∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
      data.dischargeScale receiver peeled,
    ∃ witness : Graph.ExitFour.Witness
        (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
        data.dischargeScale receiver peeled,
      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
          data.threshold data.dischargeScale receiver package.outside peeled,
        witness.load = load) ∨
  (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
      data.dischargeScale receiver peeled ∧
    ∃ witness : Graph.ExitFour.Witness
        (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
        data.dischargeScale receiver peeled,
      witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
        data.dischargeScale receiver peeled)


/-- Exit `(5)` at a state: some eligible load has a selected trace basin with
a target-complete compression (`def:typeA-saturated-exits` (5)). -/
def ExitFiveAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (peeled : Finset object.Vertex) : Prop :=
  ∃ load : object.Vertex,
    EligibleLoadAt data object piece receiver peeled load ∧
      ∃ basin : Finset object.Vertex,
        Graph.Route8.TraceBasin.select? object piece data.threshold receiver
            load = some basin ∧
          Graph.Route8.TraceBasin.TraceTargetCompleteCompression object piece
            data.threshold data.LengthOK receiver load basin

/-! ## The objects of `G` the Type A chain is about -/

/-- A fact about the node-`[61]` negative support `X₀` of `G`. -/
abbrev AtTypeASupport (data : Parameters) (object : Graph.FiniteObject.{u})
    (fact : Finset object.Vertex → Prop) : Prop :=
  ∃ piece, canonicalNegativePiece data object = some piece ∧ fact piece

/-- A fact about the node-`[93]` visible receiver of `X₀` and its overloaded
completion port at the empty peeling set. -/
abbrev AtVisiblePort (data : Parameters) (object : Graph.FiniteObject.{u})
    (fact : Finset object.Vertex → object.Vertex → object.Vertex → Prop) : Prop :=
  AtTypeASupport data object fun piece =>
    ∃ receiver, canonicalVisibleReceiverAt data object piece = some receiver ∧
      ∃ port, canonicalOverloadedPortAt data object piece receiver ∅ = some port ∧
        fact piece receiver port

/-- A fact about the exit-chain receiver of `X₀` (nodes `[101]`--`[109]`). -/
abbrev AtExitReceiver (data : Parameters) (object : Graph.FiniteObject.{u})
    (fact : Finset object.Vertex → object.Vertex → Prop) : Prop :=
  AtTypeASupport data object fun piece =>
    ∃ receiver, canonicalExitReceiverAt data object piece = some receiver ∧
      fact piece receiver

/-- A fact about the terminal state `(X₀, w, P₄(w))`: the terminal receiver
`w` of `X₀` (`canonicalTerminalReceiverAt`, the receiver of the node-`[89]`
retest after peeling) at its canonical terminal peeling set
(`def:typeA-exit4-peeling`, `lem:typeA-exit4-finite-descent`). -/
abbrev AtTerminalState (data : Parameters) (object : Graph.FiniteObject.{u})
    (fact : Finset object.Vertex → object.Vertex → Finset object.Vertex → Prop) :
    Prop :=
  AtTypeASupport data object fun piece =>
    ∃ receiver, canonicalTerminalReceiverAt data object piece = some receiver ∧
      fact piece receiver (canonicalTerminalPeeled data object piece receiver)

/-- A fact about the overloaded completion port of the terminal state
(node `[93]` asked again after peeling, `lem:typeA-unpeeled-visible-routing`). -/
abbrev AtPeeledVisiblePort (data : Parameters) (object : Graph.FiniteObject.{u})
    (fact : Finset object.Vertex → object.Vertex → object.Vertex → Prop) :
    Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    ∃ port, canonicalOverloadedPortAt data object piece receiver peeled = some port ∧
      fact piece receiver port

/-- Two facts pinned to the same guarded object are about one object. -/
theorem canonicalPin_merge {α : Type*} {object : Option α} {first second : α → Prop}
    (left : ∃ x, object = some x ∧ first x)
    (right : ∃ x, object = some x ∧ second x) :
    ∃ x, object = some x ∧ first x ∧ second x := by
  obtain ⟨x, hx, fx⟩ := left
  obtain ⟨y, hy, sy⟩ := right
  rw [hx] at hy
  cases hy
  exact ⟨x, hx, fx, sy⟩

/-! ## The cumulative saturated exit states -/

/-- The state after exit `(4)` fails: saturated and exit-`(4)`-free. -/
abbrev ExitFourFreeStateAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (peeled : Finset object.Vertex) : Prop :=
  Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
      receiver peeled ∧
    ExitFourFreeAt data object piece receiver peeled

/-- The state after exits `(4)` and `(5)` fail. -/
abbrev NoExitFiveAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (peeled : Finset object.Vertex) : Prop :=
  ExitFourFreeStateAt data object piece receiver peeled ∧
    ¬ ExitFiveAt data object piece receiver peeled

/-- The state after exits `(4)`--`(6)` fail. -/
abbrev NoExitSixAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (peeled : Finset object.Vertex) : Prop :=
  NoExitFiveAt data object piece receiver peeled ∧
    ¬ ExitSixDelocalizes data object piece receiver peeled

/-- The terminal Type A state after exits `(4)`--`(6)` have failed, with one
more clause about the state.  The support's zero surplus (node `[63]`) is
restated with the state, as at d2ded0e, because the route-`8` residual and the
decorated handoff read it together with the state. -/
abbrev SelectedNoExitSixReceiverWith (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (extra : (piece : Finset object.Vertex) → object.Vertex →
      Finset object.Vertex → Prop) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    object.ambientSurplus piece data.threshold = 0 ∧
    NoExitSixAt data object piece receiver peeled ∧
      extra piece receiver peeled

/-! ## The canonical exit-`(4)` peeling sequence -/

/-- `ExitFourAt` is exactly the existence of the canonical exit-`(4)` witness
specification. -/
theorem exitFourAt_iff_exists_witnessSpec (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    ExitFourAt data object piece receiver peeled ↔
      ∃ witness, ExitFourWitnessSpec data object piece receiver peeled witness := by
  constructor
  · rintro (⟨package, witness, load, member, equal⟩ | ⟨silent, witness, member⟩)
    · exact ⟨witness, Or.inl ⟨package, load, member, equal⟩⟩
    · exact ⟨witness, Or.inr ⟨silent, member⟩⟩
  · rintro ⟨witness, ⟨package, load, member, equal⟩ | ⟨silent, member⟩⟩
    · exact Or.inl ⟨package, witness, load, member, equal⟩
    · exact Or.inr ⟨silent, witness, member⟩

/-- Without an exit-`(4)` witness at the empty set the canonical sequence never
moves: the terminal peeled set is empty. -/
theorem canonicalTerminalPeeled_eq_empty_of_none (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex)
    (none : canonicalExitFourWitnessAt data object piece receiver ∅ = none) :
    canonicalTerminalPeeled data object piece receiver = ∅ := by
  classical
  have fixed : canonicalPeelStep data object piece receiver
      (canonicalPeel data object piece receiver 0) =
        canonicalPeel data object piece receiver 0 := by
    rw [canonicalPeel_zero]
    unfold canonicalPeelStep
    split
    · rw [none]
    · rfl
  exact canonicalPeel_stable data object piece receiver fixed _ (Nat.zero_le _)

/-- At the terminal peeled set a saturated receiver has no exit-`(4)` witness:
one would strictly enlarge the fixed point. -/
theorem canonicalTerminalPeeled_witness_eq_none (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex)
    (saturated : Graph.ExitFour.SaturatedAfter piece data.threshold
      data.dischargeScale receiver
      (canonicalTerminalPeeled data object piece receiver)) :
    canonicalExitFourWitnessAt data object piece receiver
      (canonicalTerminalPeeled data object piece receiver) = none := by
  classical
  have fixed := canonicalTerminalPeeled_step data object piece receiver
  cases found : canonicalExitFourWitnessAt data object piece receiver
      (canonicalTerminalPeeled data object piece receiver) with
  | none => rfl
  | some witness =>
      exfalso
      unfold canonicalPeelStep at fixed
      rw [if_pos saturated, found] at fixed
      have card := congrArg Finset.card fixed
      simp only [Graph.ExitFour.Witness.nextPeeled, Finset.card_cons] at card
      omega

/-- The first step of the canonical sequence peels the canonical witness of the
empty set. -/
theorem canonicalPeel_one_of_some (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex)
    (saturated : Graph.ExitFour.SaturatedAfter piece data.threshold
      data.dischargeScale receiver ∅)
    {witness : Graph.ExitFour.Witness (Graph.HasCycleWithLength data.LengthOK)
      piece data.threshold data.dischargeScale receiver ∅}
    (found : canonicalExitFourWitnessAt data object piece receiver ∅ = some witness) :
    canonicalPeel data object piece receiver 1 = witness.nextPeeled := by
  classical
  rw [canonicalPeel_succ, canonicalPeel_zero]
  unfold canonicalPeelStep
  rw [if_pos saturated, found]

/-! ## The canonical exit-`(6)` delocalization -/

/-- The `∃`-body of `ExitSixDelocalizes` (node `[105]` yes,
`K .typeAExitSix`): an eligible load, its selected trace basin, and a
delocalization at that basin. -/
def ExitSixLoadSpec (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (peeled : Finset object.Vertex) (pair : object.Vertex × Finset object.Vertex) :
    Prop :=
  EligibleLoadAt data object piece receiver peeled pair.1 ∧
    Graph.Route8.TraceBasin.select? object piece data.threshold receiver
        pair.1 = some pair.2 ∧
      Graph.Route8.TraceBasin.TraceDelocalization object piece data.threshold
        data.LengthOK receiver pair.1 pair.2

theorem exitSixDelocalizes_iff_exists_spec (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    ExitSixDelocalizes data object piece receiver peeled ↔
      ∃ pair, ExitSixLoadSpec data object piece receiver peeled pair := by
  constructor
  · rintro ⟨load, eligible, basin, selected, delocalizes⟩
    exact ⟨(load, basin), eligible, selected, delocalizes⟩
  · rintro ⟨⟨load, basin⟩, eligible, selected, delocalizes⟩
    exact ⟨load, eligible, basin, selected, delocalizes⟩

/-- A delocalization at the selected basin of one load. -/
abbrev ExitSixDelocalization (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (pair : object.Vertex × Finset object.Vertex) : Type (u + 2) :=
  Graph.Route8.Delocalization (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK)
    (Graph.Route8.PresentedEntry.ofTraceBasin object piece pair.2 data.threshold
      data.LengthOK receiver pair.1)
    pair.2

/-- **The canonical exit-`(6)` delocalization** of a state: the
`Classical.choose` of the `ExitSixDelocalizes` existential (its load and
basin) with the chosen delocalization there.  Node `[106]` splits on the
enlarging support of exactly this delocalization (d2ded0e
`TypeAExitSixScopeDichotomy` opened the one delocalization of the
`K .typeAExitSix` state). -/
noncomputable def canonicalExitSixDelocalizationAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    Option (Σ pair : object.Vertex × Finset object.Vertex,
      ExitSixDelocalization data object piece receiver pair) := by
  classical
  exact if h : ∃ pair, ExitSixLoadSpec data object piece receiver peeled pair then
    some ⟨Classical.choose h, Classical.choice (Classical.choose_spec h).2.2⟩
  else none

theorem canonicalExitSixDelocalizationAt_spec {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    {receiver : object.Vertex} {peeled : Finset object.Vertex}
    (six : ExitSixDelocalizes data object piece receiver peeled) :
    ∃ delocalization,
      canonicalExitSixDelocalizationAt data object piece receiver peeled =
        some delocalization := by
  classical
  have h := (exitSixDelocalizes_iff_exists_spec data object piece receiver
    peeled).mp six
  unfold canonicalExitSixDelocalizationAt
  rw [dif_pos h]
  exact ⟨_, rfl⟩

/-! ## Key statements

The statement each vocabulary key of this family publishes: the paper's node
statement instantiated at `G` and at the objects of `G` fixed upstream. -/

/-- Node `[62]`, no arm — node `[63]`, Type A: the node-`[61]` negative
support `X₀` carries no assigned high-degree surplus, `σ(X₀) = 0`. -/
noncomputable abbrev TypeALowSurplusStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTypeASupport data object fun piece =>
    object.ambientSurplus piece data.threshold = 0

/-- Node `[62]`, yes arm — node `[64]`, Type B: `σ(X₀) > 0`. -/
noncomputable abbrev TypeBHighSurplusStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTypeASupport data object fun piece =>
    0 < object.ambientSurplus piece data.threshold

/-- Node `[86]`: the Type A support.  `σ(X₀) = 0`, so its negative net charge
`N₀(X₀) = def⁺(X₀) − |V(X₀)|/s < 0` reads `s·def⁺(X₀) < |V(X₀)|`. -/
noncomputable abbrev TypeASupportStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTypeASupport data object fun piece =>
    data.dischargeScale * object.positiveDeficiency piece data.threshold <
      piece.card

/-- Node `[87]`: `X₀` is induced-`P_windowOrder`-free, every two of its
vertices have an internal path of length at most `windowOrder - 2`, and the
subcubic breadth-first bound gives `1 + threshold * (2^(windowOrder - 2) - 1)`
vertices (diameter at most `11`, at most `6142` vertices at the registered
values). -/
noncomputable abbrev TypeABoundedSupportStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTypeASupport data object fun piece =>
    Graph.InducedPathFree (object.induce piece) data.windowOrder ∧
      (∀ left ∈ piece, ∀ right ∈ piece,
        ∃ path : object.graph.Walk left right,
          path.IsPath ∧
            (∀ vertex ∈ path.support, vertex ∈ piece) ∧
            path.length ≤ data.windowOrder - 2) ∧
      piece.card ≤ 1 + data.threshold * (2 ^ (data.windowOrder - 2) - 1)

/-- The routing and threshold algebra of one zero-surplus support
(`lem:typeA-receiver-loads`, `lem:typeA-threshold-algebra`): every vertex
spending the whole baseline inside the support is routed by the canonical
trace to a receiver, and a receiver of internal degree `δ − 1 − j` has
`q(w) = j + 1`, so its saturation threshold is `H_j = s·(j+1) ≤ s·δ`. -/
def ZeroSurplusRoutingAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) : Prop :=
  (∀ vertex ∈ piece,
    object.internalDegree piece vertex = data.threshold →
    ∃ receiver : object.Vertex,
      object.traceReceiver? piece data.threshold vertex = some receiver ∧
        object.IsReceiver piece data.threshold receiver) ∧
    (∀ receiver : object.Vertex,
      object.IsReceiver piece data.threshold receiver →
      data.dischargeScale *
            object.missingPorts piece data.threshold receiver =
          data.dischargeScale *
            (data.threshold - 1 -
              object.internalDegree piece receiver + 1) ∧
        data.dischargeScale *
            object.missingPorts piece data.threshold receiver ≤
          data.dischargeScale * data.threshold)

/-- Node `[88]`: the routing and threshold algebra of the Type A support `X₀`
(`def:typeA-receiver-load`, `lem:typeA-receiver-loads`,
`lem:typeA-threshold-algebra`).  For the manuscript's baseline and discharge
scale the thresholds are `H₀ ≤ 4`, `H₁ ≤ 8`, `H₂ ≤ 12`. -/
noncomputable abbrev TypeAReceiverRoutingStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  AtTypeASupport data object fun piece =>
    ZeroSurplusRoutingAt data object piece

/-- Node `[89]`, yes arm: some receiver of `X₀` is saturated,
`L(w) ≥ s·q(w)`.  Its canonical choice is the receiver `w₀` of `X₀`. -/
noncomputable abbrev TypeASaturatedReceiverStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTypeASupport data object fun piece =>
    ∃ receiver, canonicalSaturatedReceiverAt data object piece = some receiver ∧
      SaturatedReceiverSpec data object piece receiver

/-- Node `[89]`, no arm — node `[90]`: every receiver of `X₀` is unsaturated,
`L(w) ≤ s·q(w) − 1`, in the subtraction-free form `1 + L(w) ≤ s·q(w)`. -/
noncomputable abbrev TypeAUnsaturatedReceiversStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTypeASupport data object fun piece =>
    ∀ receiver : object.Vertex,
      object.IsReceiver piece data.threshold receiver →
      1 + object.routedLoad piece data.threshold receiver ≤
        data.dischargeScale * object.missingPorts piece data.threshold receiver

/-- Node `[91]`: the `3/7/11` discharging conclusion
(`lem:typeA-unsaturated-discharge`) at `X₀`, `|V(X₀)| ≤ s·def⁺(X₀)`. -/
noncomputable abbrev TypeAUnsaturatedDischargeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTypeASupport data object fun piece =>
    piece.card ≤
      data.dischargeScale * object.positiveDeficiency piece data.threshold

/-- The three alternatives of `lem:typeA-exclusion`'s "Consequently" clause at
one negative zero-surplus support (via `lem:density-mersenne`): an exit-`(4)`
witness for a routed load (iii), an admissible silent-core residual profile
(iv) — obtained from a saturated receiver (def 10790), which exists, and at
every saturated receiver, every unpaid silent-excess load and every
selected visible unpeeled load of an overloaded port is a route-`8` entry or
realizes the trace-response quotient — or a produced decorated handoff (ii). -/
def TypeAExclusionTrichotomy (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) : Prop :=
  (∃ receiver : object.Vertex,
      object.IsReceiver piece data.threshold receiver ∧
        Nonempty (Graph.ExitFour.Witness
          (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
          data.dischargeScale receiver ∅)) ∨
    ((∃ receiver : object.Vertex,
        receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale) ∧
      ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        (∀ load ∈ Graph.VisibleEntry.silentExcess object piece
            data.threshold data.dischargeScale receiver,
          Graph.Route8.TraceBasin.Route8Entry object piece
            data.threshold data.LengthOK receiver load ∨
            ∃ basin : Finset object.Vertex,
              Graph.Route8.TraceBasin.select? object piece
                  data.threshold receiver load = some basin ∧
                ∃ retained,
                  Graph.Route8.TraceBasin.TraceResponseQuotient object
                    piece data.threshold data.LengthOK receiver load
                    basin retained) ∧
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
                      basin retained) ∨
    SeparatorHandoffAt data object piece

/-- `lem:typeA-exclusion` (via `lem:density-mersenne`) at the canonical pieces
of `G`'s fixed packing `P₀`: every negative zero-surplus canonical piece of
`R(P₀)` carries an exit-`(4)` witness for a routed load, an admissible
silent-core residual profile, or a produced decorated handoff.  The consumer
is `thm:branch-kill`'s classification of exactly these pieces
(`K .route8PiecesClassified`). -/
noncomputable abbrev TypeAExclusionStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ component ∈ object.canonicalPieces (canonicalRemainder data object),
    object.NegativeNetCharge
        (object.pieceSupport (canonicalRemainder data object) component)
        data.threshold data.dischargeScale →
      object.ambientSurplus
          (object.pieceSupport (canonicalRemainder data object) component)
          data.threshold = 0 →
      TypeAExclusionTrichotomy data object
        (object.pieceSupport (canonicalRemainder data object) component)

/-- `lem:typeA-port-return` at `X₀`: every completion port of every receiver
of `X₀` carries an anchored return (`lem:bridgeless`). -/
noncomputable abbrev TypeAPortReturnStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTypeASupport data object fun piece =>
    ∀ receiver : object.Vertex,
      object.IsReceiver piece data.threshold receiver →
      ∀ outside ∈ Graph.VisibleEntry.completionPorts object piece receiver,
        Nonempty (Graph.VisibleEntry.AnchoredReturn object receiver outside)

/-- Node `[93]`, yes arm: some saturated receiver of `X₀` has a completion port
carrying `s` visible receiver-entry returns (`lem:typeA-visible-entry`).  Its
canonical choice is the visible receiver of `X₀`. -/
noncomputable abbrev TypeAVisibleEntryStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTypeASupport data object fun piece =>
    ∃ receiver, canonicalVisibleReceiverAt data object piece = some receiver ∧
      VisibleReceiverSpec data object piece receiver

/-- Node `[93]`, no arm: no saturated receiver of `X₀` has such a port. -/
noncomputable abbrev TypeANoVisibleEntryStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTypeASupport data object fun piece =>
    ∀ receiver : object.Vertex,
      object.IsReceiver piece data.threshold receiver →
      object.Saturated piece data.threshold data.dischargeScale receiver →
      ¬ Nonempty (Graph.ExitFour.VisibleFourUnpeeledPackage piece
        data.threshold data.dischargeScale receiver ∅)

/-- Node `[94]`, `lem:typeA-silent-excess-count` at `X₀` and its node-`[89]`
saturated receiver `w₀`: the visible-first excess is silent and carries the
whole excess, `|V(X₀)| ≤ S_sil^exc(X₀) + s·def⁺(X₀)`, and `w₀` has silent
unpeeled excess. -/
noncomputable abbrev TypeAVisibleFirstExcessStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTypeASupport data object fun piece =>
    ∃ receiver, canonicalSaturatedReceiverAt data object piece = some receiver ∧
      SilentExitOriginAt data object piece receiver

/-- Exit `(3)` through one completion port (`def:typeA-saturated-exits` (3),
tex 10811; `lem:typeA-visible-entry`, tex 11216-11219: "if two traces pass
through a common `P₁₃` window, their labels are governed by the relations
`C_s` ...; failure of the corresponding `C_s` test is the stated label
collision"): two distinct receiver-entry returns through the port meet a common
packed window of `P₀` — a vertex of each return attaches to the window — and the
two attachment points, joined by a window-avoiding connector of length `s`,
fail `C_s`: the closing length `s + 2 + |i − j|` is accepted. -/
def ExitThreeThrough (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver outside : object.Vertex) : Prop :=
  ∃ first second : Graph.VisibleEntry.ReceiverEntryReturn object piece receiver
      outside,
    first ≠ second ∧
    ∃ presentation : Graph.TypeBDirectCycle.Presentation object data.windowOrder,
      presentation.support ∈ canonicalWindowPacking data object ∧
      ∃ source ∈ first.toAnchoredReturn.path.support,
        ∃ target ∈ second.toAnchoredReturn.path.support,
          ∃ connector : object.graph.Walk source target,
            connector.IsPath ∧
              (∀ z ∈ connector.support, ∀ t < data.windowOrder,
                z ≠ presentation.coordinate t) ∧
              ∃ sourceIndex ∈ Graph.WindowLabelCollision.attachmentLabel
                  presentation source,
                ∃ targetIndex ∈ Graph.WindowLabelCollision.attachmentLabel
                    presentation target,
                  data.LengthOK (Graph.WindowCurvature.closingLength
                    connector.length (Nat.dist sourceIndex.1 targetIndex.1))

/-- Exit `(3)` at a port is a label collision of `P₀`. -/
theorem labelCollision_of_exitThreeThrough {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    {receiver outside : object.Vertex}
    (exit : ExitThreeThrough data object piece receiver outside) :
    Graph.WindowLabelCollision.LabelCollision object data.windowOrder
      data.LengthOK (canonicalWindowPacking data object) := by
  obtain ⟨_first, _second, _distinct, presentation, member, source, _sourceMem,
    target, _targetMem, connector, path, avoids, sourceIndex, sourceLabel,
    targetIndex, targetLabel, accepted⟩ := exit
  exact ⟨presentation, member, source, target, connector, path, avoids,
    sourceIndex, sourceLabel, targetIndex, targetLabel, accepted⟩

/-- Node `[95]`, yes arm — exit `(1)`: an anchored return through the
overloaded port of the visible receiver has length in `Mers`. -/
noncomputable abbrev TypeAExitOneReturnStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtVisiblePort data object fun _piece receiver port =>
    ∃ return' : Graph.VisibleEntry.AnchoredReturn object receiver port,
      Graph.ShiftedCycleLength data.LengthOK return'.path.length

/-- Node `[95]`, no arm: no anchored return through that port has length in
`Mers`. -/
noncomputable abbrev TypeAExitOneFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtVisiblePort data object fun _piece receiver port =>
    ∀ return' : Graph.VisibleEntry.AnchoredReturn object receiver port,
      ¬ Graph.ShiftedCycleLength data.LengthOK return'.path.length

/-- Node `[97]`, yes arm — exit `(2)` at the overloaded port of the visible
receiver (`lem:typeA-common-port-return-cycle`). -/
noncomputable abbrev TypeAExitTwoThetaStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtVisiblePort data object fun piece receiver port =>
    Graph.VisibleEntry.ExitTwoThrough object piece data.LengthOK receiver port

/-- Node `[97]`, no arm. -/
noncomputable abbrev TypeAExitTwoFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtVisiblePort data object fun piece receiver port =>
    ¬ Graph.VisibleEntry.ExitTwoThrough object piece data.LengthOK receiver port

/-- Node `[99]`, yes arm — exit `(3)` at the overloaded port of the visible
receiver: two of its receiver-entry returns fail `C_s` at a common packed
window of `P₀`. -/
noncomputable abbrev TypeAExitThreeCollisionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtVisiblePort data object fun piece receiver port =>
    ExitThreeThrough data object piece receiver port

/-- Node `[99]`, no arm: the exact negation at the same port. -/
noncomputable abbrev TypeAExitThreeFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtVisiblePort data object fun piece receiver port =>
    ¬ ExitThreeThrough data object piece receiver port

/-- Nodes `[100]` (and `[100]` after peeling): the label collision of exit
`(3)` closes a cycle of accepted length in `G` (`lem:labels`, tex 6661;
`lem:typeA-exits-discharged`: "by definition of the relation, it creates a
target event").  The degenerate closure of length `2` is not accepted. -/
noncomputable abbrev TypeAExitThreeCycleStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.HasCycleWithLength data.LengthOK object

/-- **The shared entry of nodes `[101]`--`[102]`**
(`lem:typeA-exit4-residual-routing`): the exit-chain receiver of `X₀` is
saturated at the empty peeling set.  The visible lane enters from node `[99]`,
the silent lane from node `[94]`. -/
noncomputable abbrev TypeASaturatedExitEntryStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtExitReceiver data object fun piece receiver =>
    Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
      receiver ∅

/-- `lem:typeA-exit4-finite-descent` at `G`: the canonical witnessed peeling
sequence of the exit-chain receiver stops at its terminal set `P₄(w)`, a fixed
point of the peeling step, inside the routed loads, all of whose loads carry
exit-`(4)` witnesses.  The recompute-`L₄` retest (tex 1095) is asked on the
ledger at the terminal sets (`typeAExitFourRetestDichotomy`); the per-stage
answers before the terminal set are the definition of the canonical step
(`canonicalPeelStep`), not a published fact. -/
noncomputable abbrev TypeAExitFourFiniteDescentFact (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtExitReceiver data object fun piece receiver =>
    canonicalPeelStep data object piece receiver
        (canonicalTerminalPeeled data object piece receiver) =
      canonicalTerminalPeeled data object piece receiver ∧
    canonicalTerminalPeeled data object piece receiver ⊆
      object.routedLoads piece data.threshold receiver ∧
    Graph.ExitFour.PeeledByWitnesses (Graph.HasCycleWithLength data.LengthOK)
      piece data.threshold data.dischargeScale receiver
      (canonicalTerminalPeeled data object piece receiver)

/-- Node `[101]`, yes arm — exit `(4)` at the entry state: a canonical
target-defective quotient supports an unpeeled load of the state's lane. -/
noncomputable abbrev TypeASaturatedHandoffExitFourStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtExitReceiver data object fun piece receiver =>
    ExitFourAt data object piece receiver ∅

/-- Node `[101]`, no arm: the exact negation at the entry state. -/
noncomputable abbrev TypeAExitFourAbsentStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtExitReceiver data object fun piece receiver =>
    ¬ ExitFourAt data object piece receiver ∅

/-- Node `[102]` (`lem:typeA-exit4-discharge`): the canonical exit-`(4)`
witness of the entry state is peeled; the peeled set is the first step of the
canonical sequence, it stays inside the routed loads, and the residual load
drops by one. -/
noncomputable abbrev TypeAExitFourPeeledStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtExitReceiver data object fun piece receiver =>
    ∃ witness, canonicalExitFourWitnessAt data object piece receiver ∅ =
        some witness ∧
      canonicalPeel data object piece receiver 1 = witness.nextPeeled ∧
      witness.nextPeeled ⊆ object.routedLoads piece data.threshold receiver ∧
      Graph.ExitFour.residualLoad piece data.threshold receiver
          witness.nextPeeled + 1 =
        Graph.ExitFour.residualLoad piece data.threshold receiver ∅

/-! ### Node `[102]` → `[89]`: the recompute-`L₄` retest and the second pass

After the peel, node `[89]` is asked again with the residual loads `L₄`: is
some receiver of `X₀` still saturated after its canonical peeling sequence has
stopped (`lem:typeA-saturated-handoff`)?  Yes: the terminal receiver `w` and
its terminal set `P₄(w)` go through node `[93]` again — exits `(1)`--`(3)` at
the overloaded port of `P₄(w)` on the visible lane
(`lem:typeA-unpeeled-visible-routing`), the residual excess `E₄(w)` on the
silent lane (`lem:typeA-unpeeled-silent-routing`) — and then node `[101]`,
where the terminal set is exit-`(4)`-free.  No: every receiver of `X₀` is
unsaturated after peeling (node `[90]`), and node `[91]` is the charge bound of
`lem:typeA-exit4-peeling-charge` on the unpeeled loads. -/

/-- Node `[102]` → `[89]`, yes arm: the terminal receiver of `X₀` is saturated
at its terminal set, `L₄(w) ≥ s·q(w)`. -/
noncomputable abbrev TypeAPeeledSaturatedReceiverStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
      receiver peeled

/-- Node `[102]` → `[89]`, no arm — node `[90]` after peeling: every receiver of
`X₀` is unsaturated after its canonical peeling sequence, `L₄(w) ≤ s·q(w) − 1`,
in the subtraction-free form. -/
noncomputable abbrev TypeAExitFourReceiverDischargedStatement
    (data : Parameters) (object : Graph.FiniteObject.{u}) : Prop :=
  AtTypeASupport data object fun piece =>
    ∀ receiver : object.Vertex,
      object.IsReceiver piece data.threshold receiver →
      1 + Graph.ExitFour.residualLoad piece data.threshold receiver
          (canonicalTerminalPeeled data object piece receiver) ≤
        data.dischargeScale * object.missingPorts piece data.threshold receiver

/-- Node `[91]` after peeling (`lem:typeA-exit4-peeling-charge` with
`lem:typeA-unsaturated-discharge` on the unpeeled loads): the remaining
receiver charge is nonnegative, so
`|V(X₀)| ≤ s·def⁺(X₀) + Σ_w |P₄(w)|` — the peeled loads have left the pure
Type A charge calculation through exit `(4)`. -/
noncomputable abbrev TypeAPeeledUnsaturatedDischargeStatement
    (data : Parameters) (object : Graph.FiniteObject.{u}) : Prop :=
  AtTypeASupport data object fun piece =>
    piece.card ≤
      data.dischargeScale * object.positiveDeficiency piece data.threshold +
        ∑ receiver ∈ object.receivers piece data.threshold,
          (canonicalTerminalPeeled data object piece receiver).card

/-- Node `[93]` after peeling, yes arm: the terminal state has an overloaded
completion port carrying `s` visible unpeeled receiver-entry returns. -/
noncomputable abbrev TypeAPeeledVisibleEntryStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    Nonempty (Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
      data.dischargeScale receiver peeled)

/-- Node `[93]` after peeling, no arm: the exact negation at the same state. -/
noncomputable abbrev TypeAPeeledNoVisibleEntryStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    ¬ Nonempty (Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
      data.dischargeScale receiver peeled)

/-- Node `[94]` after peeling (`lem:typeA-unpeeled-silent-routing`): with no
overloaded port at the terminal state, the residual excess `E₄(w)` is
nonempty and silent. -/
noncomputable abbrev TypeAPeeledSilentExcessStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
      data.dischargeScale receiver peeled

/-- Node `[95]` after peeling, yes arm — exit `(1)` at the overloaded port of
the terminal state. -/
noncomputable abbrev TypeAPeeledExitOneReturnStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtPeeledVisiblePort data object fun _piece receiver port =>
    ∃ return' : Graph.VisibleEntry.AnchoredReturn object receiver port,
      Graph.ShiftedCycleLength data.LengthOK return'.path.length

/-- Node `[95]` after peeling, no arm. -/
noncomputable abbrev TypeAPeeledExitOneFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtPeeledVisiblePort data object fun _piece receiver port =>
    ∀ return' : Graph.VisibleEntry.AnchoredReturn object receiver port,
      ¬ Graph.ShiftedCycleLength data.LengthOK return'.path.length

/-- Node `[97]` after peeling, yes arm — exit `(2)` at the same port. -/
noncomputable abbrev TypeAPeeledExitTwoThetaStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtPeeledVisiblePort data object fun piece receiver port =>
    Graph.VisibleEntry.ExitTwoThrough object piece data.LengthOK receiver port

/-- Node `[97]` after peeling, no arm. -/
noncomputable abbrev TypeAPeeledExitTwoFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtPeeledVisiblePort data object fun piece receiver port =>
    ¬ Graph.VisibleEntry.ExitTwoThrough object piece data.LengthOK receiver port

/-- Node `[99]` after peeling, yes arm — exit `(3)` at the same port. -/
noncomputable abbrev TypeAPeeledExitThreeCollisionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtPeeledVisiblePort data object fun piece receiver port =>
    ExitThreeThrough data object piece receiver port

/-- Node `[99]` after peeling, no arm. -/
noncomputable abbrev TypeAPeeledExitThreeFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtPeeledVisiblePort data object fun piece receiver port =>
    ¬ ExitThreeThrough data object piece receiver port

/-- Node `[101]`, no arm, at the terminal state — the input of exits
`(5)`--`(8)`: the terminal receiver is saturated at its terminal set, which is
exit-`(4)`-free.  On node `[101]`'s first no arm `P₄(w) = ∅`; after the retest
the terminal set is a fixed point of the peeling step. -/
noncomputable abbrev TypeASaturatedHandoffExitFourFreeStatement
    (data : Parameters) (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    ExitFourFreeStateAt data object piece receiver peeled

/-- Node `[103]`, yes arm — exit `(5)` at the terminal state. -/
noncomputable abbrev TypeAExitFiveStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    ExitFourFreeStateAt data object piece receiver peeled ∧
      ExitFiveAt data object piece receiver peeled

/-- Node `[103]`, no arm. -/
noncomputable abbrev TypeAExitFiveFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    NoExitFiveAt data object piece receiver peeled

/-- Node `[105]`, yes arm — exit `(6)` at the terminal state. -/
noncomputable abbrev TypeAExitSixStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    NoExitFiveAt data object piece receiver peeled ∧
      ExitSixDelocalizes data object piece receiver peeled

/-- Node `[105]`, no arm. -/
noncomputable abbrev TypeAExitSixFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    NoExitSixAt data object piece receiver peeled

/-- Node `[106]`, proper scope: the enlarging support `Z` of the canonical
exit-`(6)` delocalization misses a vertex of `G`. -/
noncomputable abbrev TypeAExitSixProperScopeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    ∃ delocalization,
      canonicalExitSixDelocalizationAt data object piece receiver peeled =
        some delocalization ∧
      ∃ vertex, vertex ∉ delocalization.2.quotient.support

/-- Node `[106]`, whole-graph scope: the exact negation, `Z = V(G)`. -/
noncomputable abbrev TypeAExitSixGlobalScopeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    ∃ delocalization,
      canonicalExitSixDelocalizationAt data object piece receiver peeled =
        some delocalization ∧
      ∀ vertex, vertex ∈ delocalization.2.quotient.support

/-- Node `[106]`, proper scope: `lem:proper-smearing` makes the proper
enlarging support `Z` a replacement support. -/
noncomputable abbrev TypeAExitSixProperStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    ∃ delocalization,
      canonicalExitSixDelocalizationAt data object piece receiver peeled =
        some delocalization ∧
      Graph.Strategy.InterfaceReplacement.ReplacementSupport
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object
        delocalization.2.quotient.support

/-- Node `[106]`, global scope: `lem:no-silent-global-smearing` gives the
canonical exit-`(6)` delocalization of the terminal state covers `V(G)`, and
that delocalization's own closed representative is strictly smaller. -/
noncomputable abbrev TypeAExitSixGlobalStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    ∃ delocalization,
      canonicalExitSixDelocalizationAt data object piece receiver peeled =
        some delocalization ∧
      ∃ covers : ∀ vertex, vertex ∈ delocalization.2.quotient.support,
        -- the delocalization's own closed representative, not a free graph
        let representative :=
          Classical.choose (delocalization.2.closedRepresentative covers)
        representative.LexicographicallySmaller object ∧
          Graph.MinimumDegreeAtLeast data.threshold representative ∧
            (Graph.HasCycleWithLength data.LengthOK representative →
              Graph.HasCycleWithLength data.LengthOK object)

/-- Node `[107]`, yes arm — exit `(7)` at the terminal state where exits
`(4)`--`(6)` failed: an eligible load of the terminal receiver has a surviving
first separator (`ExitSevenAt`, `lem:typeA-high-degree-handoff`). -/
noncomputable abbrev TypeAExitSevenHandoffStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  SelectedNoExitSixReceiverWith data object
    (fun piece receiver peeled => ExitSevenAt data object piece receiver peeled)

/-- Node `[107]`, no arm — node `[109]`, the route-`8` residual: the exact
negation at the same terminal state. -/
noncomputable abbrev TypeAExitSevenFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  SelectedNoExitSixReceiverWith data object
    (fun piece receiver peeled => ¬ ExitSevenAt data object piece receiver peeled)

/-- Node `[108]` — "returns to Type B handoff": the exit-`(7)` separation of
the terminal state is the canonical separation of `X₀`
(`canonicalHandoffSeparationAt`), and `lem:typeA-high-degree-handoff` builds
its decorated handoff fan envelope (`def:decorated-fan-envelope`) at the
registered high-degree set and the exit-`(3)` absorbing clause of `P₀`. -/
noncomputable abbrev TypeAExitSevenEnvelopeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    object.ambientSurplus piece data.threshold = 0 ∧
    (∃ separated, canonicalHandoffSeparationAt data object piece = some separated ∧
      separated.1.1 = receiver ∧
      EligibleLoadAt data object piece receiver peeled separated.1.2) ∧
    ∃ envelope, canonicalHandoffEnvelopeAt data object piece
        (handoffHighDegree data object)
        (handoffAbsorbing data object (canonicalWindowPacking data object)) =
      some envelope

end Hypostructure.Graph.Strategy.Spine
