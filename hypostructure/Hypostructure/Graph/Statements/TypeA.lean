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

/-- The loads of a saturated state that exits `(5)`--`(8)` test: the selected
visible unpeeled loads of the overloaded port when no exit-`(4)` witness
supports one of them, or the loads of the silent residual excess when no
exit-`(4)` witness supports one of those (`lem:typeA-unpeeled-visible-routing`,
`lem:typeA-unpeeled-silent-routing`). -/
abbrev EligibleLoadAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (peeled : Finset object.Vertex) (load : object.Vertex) : Prop :=
  (∃ package :
        Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
          data.dischargeScale receiver peeled,
      (¬ ∃ witness : Graph.ExitFour.Witness
          (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
          data.dischargeScale receiver peeled,
        ∃ selected ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
            data.threshold data.dischargeScale receiver package.outside
            peeled,
          witness.load = selected) ∧
        load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
          data.threshold data.dischargeScale receiver package.outside
          peeled) ∨
    (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
        data.dischargeScale receiver peeled ∧
      (¬ ∃ witness : Graph.ExitFour.Witness
          (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
          data.dischargeScale receiver peeled,
        witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
          data.dischargeScale receiver peeled) ∧
      load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
        data.dischargeScale receiver peeled)

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

/-- A fact about the terminal state `(X₀, w, P₄(w))` of the canonical
witnessed exit-`(4)` peeling sequence (`def:typeA-exit4-peeling`,
`lem:typeA-exit4-finite-descent`). -/
abbrev AtTerminalState (data : Parameters) (object : Graph.FiniteObject.{u})
    (fact : Finset object.Vertex → object.Vertex → Finset object.Vertex → Prop) :
    Prop :=
  AtExitReceiver data object fun piece receiver =>
    fact piece receiver (canonicalTerminalPeeled data object piece receiver)

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
more clause about the canonical packing and the state.  The support's zero
surplus (node `[63]`) is restated with the state, as at d2ded0e, because the
route-`8` collection (`route8UnifiedComponents`) and the decorated handoff read
it together with the state. -/
abbrev SelectedNoExitSixReceiverWith (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (extra : (packing : Finset (Finset object.Vertex)) →
      (piece : Finset object.Vertex) → object.Vertex →
      Finset object.Vertex → Prop) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    object.ambientSurplus piece data.threshold = 0 ∧
    NoExitSixAt data object piece receiver peeled ∧
      extra (canonicalWindowPacking data object) piece receiver peeled

/-- The same terminal state, with a clause about the packing and support. -/
abbrev SelectedNoExitSixWith (data : Parameters) (object : Graph.FiniteObject.{u})
    (extra : (packing : Finset (Finset object.Vertex)) →
      Finset object.Vertex → Prop) : Prop :=
  SelectedNoExitSixReceiverWith data object
    fun packing piece _receiver _peeled => extra packing piece

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

/-- Node `[88]`: the routing and threshold algebra of a Type A support.
`lem:typeA-receiver-loads` — every vertex spending the whole baseline inside
the support is routed by the canonical trace to exactly one receiver — and
`lem:typeA-threshold-algebra` — a receiver of internal degree `δ − 1 − j` has
`q(w) = j + 1`, so its saturation threshold is `H_j = s·(j+1)`, never above
`s·δ`.  For the manuscript's baseline and discharge scale this is
`H₀ ≤ 4`, `H₁ ≤ 8`, `H₂ ≤ 12`. -/
noncomputable abbrev TypeAReceiverRoutingStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[88]`.  Stated at every zero-surplus subregion of the remainder
  -- `R₀` of G's fixed packing `P₀`, as node `[27]` is stated at every
  -- subregion of `R₀`:
  -- a support is data and cannot travel, so what the ledger records is the
  -- statement about all of them.
  --
  -- `def:typeA-support` is `def:admissible` with `σ(X) = 0`; the two
  -- clauses below are `def:typeA-receiver-load`'s own consequences at such
  -- a support.
  (∀ piece : Finset object.Vertex,
      piece ⊆ object.remainderSupport (canonicalWindowPacking data object) →
      object.ambientSurplus piece data.threshold = 0 →
      -- `lem:typeA-receiver-loads`: `r(u)` is defined for every vertex of
      -- internal degree `δ`, and it is a receiver.  Uniqueness is the
      -- routing being a function of `u`.
      (∀ vertex ∈ piece,
        object.internalDegree piece vertex = data.threshold →
        ∃ receiver : object.Vertex,
          object.traceReceiver? piece data.threshold vertex = some receiver ∧
            object.IsReceiver piece data.threshold receiver) ∧
        -- `lem:typeA-threshold-algebra`: `H_j = s·q(w) = s·(j+1) ≤ s·δ`.
        (∀ receiver : object.Vertex,
          object.IsReceiver piece data.threshold receiver →
          data.dischargeScale *
                object.missingPorts piece data.threshold receiver =
              data.dischargeScale *
                (data.threshold - 1 -
                  object.internalDegree piece receiver + 1) ∧
            data.dischargeScale *
                object.missingPorts piece data.threshold receiver ≤
              data.dischargeScale * data.threshold))


/-- Node `[89]`, yes arm: some receiver of `X₀` is saturated,
`L(w) ≥ s·q(w)`.  Its canonical choice is the receiver `w₀` of `X₀`. -/
noncomputable abbrev TypeASaturatedReceiverStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtTypeASupport data object fun piece =>
    ∃ receiver, SaturatedReceiverSpec data object piece receiver

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

/-- Node `[86]`, `lem:typeA-exclusion` (via `lem:density-mersenne`), at the
minimal counterexample: every negative zero-surplus canonical piece of a
maximal packing's remainder carries an exit-`(4)` witness for a routed load,
an admissible silent-core residual profile, or a produced decorated Type B
handoff. -/
noncomputable abbrev TypeAExclusionStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[86]`, `lem:typeA-exclusion` via `lem:density-mersenne`, stated
  -- at the minimal counterexample the branch carries, exactly at the
  -- paper's generality: over every connected admissible sub-support of
  -- its own maximal-packing remainders — "every admissible subcubic
  -- P₁₃-free target-safe boundaried piece", so the same fact serves the
  -- canonical pieces at `K .route8PiecesClassified` and the post-ledger
  -- core components of the Type B bridge pieces.  A negative zero-surplus
  -- piece leaves through the target-defect exit, the silent-core residual
  -- profile, or the decorated handoff.
  (∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    (∀ window : Finset object.Vertex,
      object.InducesWindow data.windowOrder window →
      ∃ member ∈ packing, ¬ Disjoint window member) →
    ∀ piece : Finset object.Vertex,
      piece ⊆ object.remainderSupport packing →
      Graph.SupportComponents.Connected.ConnectedOn object piece →
      object.NegativeNetCharge piece data.threshold data.dischargeScale →
      object.ambientSurplus piece data.threshold = 0 →
      ((∃ receiver : object.Vertex,
          object.IsReceiver piece data.threshold receiver ∧
            Nonempty (Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
              data.dischargeScale receiver ∅)) ∨
        (∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
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
        SeparatorHandoffAt data object piece) ∧
      -- The additive per-load publication
      -- (`lem:typeA-reduced-silent-residual` with the exit-(7) routing of
      -- `lem:typeA-exits-discharged`): at every saturated receiver, each
      -- unpaid silent-excess load and each selected visible unpeeled load
      -- of an overloaded completion port realizes the four-way split the
      -- executor derives before collapsing — the exit-(4) witness, the
      -- route-8 entry, the exit-(5) trace-response quotient, or the
      -- exit-(7) surviving separator whose recorded envelope is the
      -- produced decorated handoff.
      (∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        (∀ load ∈ Graph.VisibleEntry.silentExcess object piece
            data.threshold data.dischargeScale receiver,
          (∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) piece
              data.threshold data.dischargeScale receiver ∅,
            witness.load = load) ∨
            Graph.Route8.TraceBasin.Route8Entry object piece
              data.threshold data.LengthOK receiver load ∨
            (∃ basin : Finset object.Vertex,
              Graph.Route8.TraceBasin.select? object piece
                  data.threshold receiver load = some basin ∧
                ∃ retained,
                  Graph.Route8.TraceBasin.TraceResponseQuotient object
                    piece data.threshold data.LengthOK receiver load
                    basin retained) ∨
            ((∃ basin : Finset object.Vertex,
                Graph.Route8.TraceBasin.TraceSurvivingSeparator object
                  piece data.threshold data.LengthOK receiver load
                  basin) ∧
              SeparatorHandoffAt data object piece)) ∧
        ∀ outside ∈ Graph.VisibleEntry.completionPorts object piece
            receiver,
          data.dischargeScale ≤
            (Graph.VisibleEntry.visibleLoadsAt object piece
              data.threshold receiver outside).card →
          ∀ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
              data.threshold data.dischargeScale receiver outside ∅,
            (∃ witness : Graph.ExitFour.Witness
                (Graph.HasCycleWithLength data.LengthOK) piece
                data.threshold data.dischargeScale receiver ∅,
              witness.load = load) ∨
              Graph.Route8.TraceBasin.Route8Entry object piece
                data.threshold data.LengthOK receiver load ∨
              (∃ basin : Finset object.Vertex,
                Graph.Route8.TraceBasin.select? object piece
                    data.threshold receiver load = some basin ∧
                  ∃ retained,
                    Graph.Route8.TraceBasin.TraceResponseQuotient object
                      piece data.threshold data.LengthOK receiver load
                      basin retained) ∨
              ((∃ basin : Finset object.Vertex,
                  Graph.Route8.TraceBasin.TraceSurvivingSeparator object
                    piece data.threshold data.LengthOK receiver load
                    basin) ∧
                SeparatorHandoffAt data object piece)))


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
    ∃ receiver, VisibleReceiverSpec data object piece receiver

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

/-- Node `[99]`, yes arm — exit `(3)`: a shared window of `P₀` violates its
legal-label relation. -/
noncomputable abbrev TypeAExitThreeCollisionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtVisiblePort data object fun _piece _receiver _port =>
    Graph.WindowLabelCollision.LabelCollision object data.windowOrder
      data.LengthOK (canonicalWindowPacking data object)

/-- Node `[99]`, no arm. -/
noncomputable abbrev TypeAExitThreeFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtVisiblePort data object fun _piece _receiver _port =>
    ¬ Graph.WindowLabelCollision.LabelCollision object data.windowOrder
      data.LengthOK (canonicalWindowPacking data object)

/-- **The shared entry of nodes `[101]`--`[107]`**
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
exit-`(4)` witnesses. -/
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

/-- Node `[102]` → `[89]`, the retest after the peel, yes arm: the receiver is
still saturated at the terminal set `P₄(w)`, which is exit-`(4)`-free; exits
`(5)`--`(8)` are asked there.  On the node-`[101]` no arm `P₄(w) = ∅`. -/
noncomputable abbrev TypeASaturatedHandoffExitFourFreeStatement
    (data : Parameters) (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    ExitFourFreeStateAt data object piece receiver peeled

/-- Node `[102]` → `[89]`, no arm: the receiver is unsaturated at `P₄(w)`, so
its remaining receiver charge is nonnegative
(`lem:typeA-exit4-peeling-charge`, `lem:typeA-saturated-handoff`). -/
noncomputable abbrev TypeAExitFourReceiverDischargedStatement
    (data : Parameters) (object : Graph.FiniteObject.{u}) : Prop :=
  AtTerminalState data object fun piece receiver peeled =>
    ¬ Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
        receiver peeled ∧
      1 + Graph.ExitFour.residualLoad piece data.threshold receiver peeled ≤
        data.dischargeScale * object.missingPorts piece data.threshold receiver

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

/-- Node `[106]`, global scope: `lem:no-silent-global-smearing` gives a
strictly smaller closed representative. -/
noncomputable abbrev TypeAExitSixGlobalStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ representative : Graph.FiniteObject.{u},
    representative.LexicographicallySmaller object ∧
      Graph.MinimumDegreeAtLeast data.threshold representative ∧
        (Graph.HasCycleWithLength data.LengthOK representative →
          Graph.HasCycleWithLength data.LengthOK object)

/-- Nodes `[107]` yes / `[108]` — exit `(7)`: at the terminal state where exits
`(4)`--`(6)` failed, `X₀` produces a decorated handoff at a surviving first
separator (`lem:typeA-high-degree-handoff`). -/
noncomputable abbrev TypeAExitSevenHandoffStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  SelectedNoExitSixWith data object
    (fun _packing piece => SeparatorHandoffAt data object piece)

/-- Node `[107]`, no arm — node `[109]`, the route-`8` residual: at the same
terminal state `X₀` produces no decorated handoff. -/
noncomputable abbrev TypeAExitSevenFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  SelectedNoExitSixWith data object
    (fun _packing piece => ¬ SeparatorHandoffAt data object piece)

/-- Node `[109]`, silent provenance: the route-`8` residual state sits at the
node-`[94]` silent origin. -/
abbrev SelectedSilentExitSevenFree (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  SelectedNoExitSixReceiverWith data object
    (fun _packing piece receiver _peeled =>
      ¬ SeparatorHandoffAt data object piece ∧
        SilentExitOriginAt data object piece receiver)

/-- Node `[109]`, visible provenance: the exact negation at the same state. -/
noncomputable abbrev TypeAExitEightNotSilentStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  SelectedNoExitSixReceiverWith data object
    (fun _packing piece receiver _peeled =>
      ¬ SeparatorHandoffAt data object piece ∧
        ¬ SilentExitOriginAt data object piece receiver)

end Hypostructure.Graph.Strategy.Spine
