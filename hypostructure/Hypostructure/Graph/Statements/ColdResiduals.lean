import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.ColdEqualStates

/-!
# Statements: the residuals returned at `[153]`, `[162]` and `[54]`

Structural exhaustion at the three nodes where the paper asserts a fact about
G that it does not construct (`lean-vs-paper-discrepancies.md`, "Returned
residuals").  Each node is an exact decision at G's pinned objects:

* `[153]` (`lem:cold-corridor-first-failure` (ii), tex 7265-7270): G's cut
  states along each retained cold corridor are pairwise distinct up to the
  first failure (`ColdCutStatesDistinctStatement`), or the explicitly
  constructed first equal-state pair of one retained corridor of G, with the
  boundary-degree separation of G's two readings and the equal capped degrees
  of its glue vertices (`ColdRepeatedStateResidualStatement`);
* `[162]` (`lem:dense-cold-pass`, tex 7692-7694), on the distinct-states arm:
  every retained corridor of G whose first failure is a heavy centre strictly
  before its terminal segment is still terminal
  (`ColdHeavyEntryTerminalStatement`), or the explicitly constructed
  retained corridor of G whose first failure is a heavy centre `z` of G
  strictly before its terminal segment and which reads more than `Q_cold`
  states (`ColdDenseHeavyEntryResidualStatement`);
* `[54]` (`prop:entropy-high-theta`, tex 9919-9921): the paper's joint
  realization inequality `RS(R₀)·2^{rate·s·p₁₃}·2^F ≤ B` at G
  (`EntropyJointRealizationStatement`), or the explicitly constructed
  configuration at G where it fails (`AllColdEntropyResidualStatement`).

Every statement is about G (`object`) and G's canonical objects only.  This
module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-! ## `[153]`: distinct cut states, or the first equal-state pair -/

/-- **(★) at G** (`lem:cold-corridor-first-failure` (ii), read at G): along
G's retained corridor of every eligible half-edge `ε`, the pinned cut states
(`coldCutStatePresentation`, identity index) of the segments up to any segment
before which no (F1)--(F5) event occurs are pairwise distinct.  Since the
segments with no earlier event are exactly those up to the first failure, this
is "pairwise distinct up to the first failure". -/
def ColdCutStatesDistinctStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (occurrence : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (first : (coldOccurrenceCorridorAt data object occurrence epsilon).Segment),
    (∀ earlier : (coldOccurrenceCorridorAt data object occurrence epsilon).Segment,
      earlier.1 < first.1 →
        ¬ ColdFirstFailureEvent data object
          (coldOccurrenceCorridorAt data object occurrence epsilon)
          (coldOccurrencePresentationAt data object occurrence epsilon)
          (coldOccurrenceIndexAt data object occurrence epsilon)
          (coldOccurrenceIncidence data object occurrence epsilon)
          (ColdDeclaredHandoffSupport data object) earlier) →
    ∀ left right : (coldOccurrenceCorridorAt data object occurrence epsilon).Segment,
      left.1 < right.1 → right.1 ≤ first.1 →
        (coldOccurrencePresentationAt data object occurrence epsilon).state
            (coldOccurrenceIndexAt data object occurrence epsilon left) ≠
          (coldOccurrencePresentationAt data object occurrence epsilon).state
            (coldOccurrenceIndexAt data object occurrence epsilon right)

/-- The pinned objects of `[153]`'s residual: an occurrence of G's retained
first-failure data (a subsingleton), an eligible half-edge `ε` of G, and two
segments of G's retained corridor of `ε`. -/
abbrev ColdRepeatWitness (data : Parameters) (object : Graph.FiniteObject.{u}) :=
  Σ' occurrence : ColdFirstFailureOccurrenceData data object,
    Σ' epsilon : ColdEligibleHalfEdge data object,
      (coldOccurrenceCorridorAt data object occurrence epsilon).Segment ×
        (coldOccurrenceCorridorAt data object occurrence epsilon).Segment

/-- The occurrence of a `[153]` witness. -/
abbrev ColdRepeatWitness.occurrence {data : Parameters} {object : Graph.FiniteObject.{u}}
    (witness : ColdRepeatWitness data object) : ColdFirstFailureOccurrenceData data object :=
  witness.1

/-- The half-edge `ε` of a `[153]` witness. -/
abbrev ColdRepeatWitness.epsilon {data : Parameters} {object : Graph.FiniteObject.{u}}
    (witness : ColdRepeatWitness data object) : ColdEligibleHalfEdge data object :=
  witness.2.1

/-- The earlier segment of the first equal-state pair. -/
abbrev ColdRepeatWitness.left {data : Parameters} {object : Graph.FiniteObject.{u}}
    (witness : ColdRepeatWitness data object) :
    (coldOccurrenceCorridorAt data object witness.occurrence witness.epsilon).Segment :=
  witness.2.2.1

/-- The later segment of the first equal-state pair. -/
abbrev ColdRepeatWitness.right {data : Parameters} {object : Graph.FiniteObject.{u}}
    (witness : ColdRepeatWitness data object) :
    (coldOccurrenceCorridorAt data object witness.occurrence witness.epsilon).Segment :=
  witness.2.2.2

/-- **The configuration of `[153]`'s residual at a witness**, read at G.

On G's retained corridor `C_ε` (`coldOccurrenceCorridorAt`, in its outside
component of `G − X_cold`, length `|C_ε| = inside.length`), with G's pinned cut
states (`coldCutStateSequence`):

* `left < right` with equal states, and no equal pair before `right` (the
  first equal-state pair);
* no (F1)--(F5) event at any segment before `right`;
* G's two readings of `J_right` on `∂J_right` -- the retained `J_left` reading
  and `J_right` itself -- have different boundary-degree profiles;
* the glue vertices `head left` and `head right` carry the same
  boundary-degree entry of the cut state, i.e. the same G-degree capped at the
  signature bound `D`.

(F2) does not fire at `right`: it is decided at G
(`Graph.ColdCorridor.Corridor.not_firstFailureDefect`), so the first failure at
`right` is the (F5) repeat and the pair is the repeat subcase of the
first-failure exchange.  No outside context other than G's own surroundings is
read. -/
def ColdRepeatedStateSpecAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (left right : (coldOccurrenceCorridorAt data object occurrence epsilon).Segment) :
    Prop :=
  ∃ _outside : Graph.ColdCorridor.IsOutsideComponent object
      (coldCorridorWindows data object)
      (coldOccurrenceComponentAt data object occurrence epsilon),
    left.1 < right.1 ∧
    (coldOccurrencePresentationAt data object occurrence epsilon).state
        (coldOccurrenceIndexAt data object occurrence epsilon left) =
      (coldOccurrencePresentationAt data object occurrence epsilon).state
        (coldOccurrenceIndexAt data object occurrence epsilon right) ∧
    (∀ earlierLeft earlierRight :
        (coldOccurrenceCorridorAt data object occurrence epsilon).Segment,
      earlierLeft.1 < earlierRight.1 → earlierRight.1 < right.1 →
        (coldOccurrencePresentationAt data object occurrence epsilon).state
            (coldOccurrenceIndexAt data object occurrence epsilon earlierLeft) ≠
          (coldOccurrencePresentationAt data object occurrence epsilon).state
            (coldOccurrenceIndexAt data object occurrence epsilon earlierRight)) ∧
    (∀ earlier : (coldOccurrenceCorridorAt data object occurrence epsilon).Segment,
      earlier.1 < right.1 →
        ¬ ColdFirstFailureEvent data object
          (coldOccurrenceCorridorAt data object occurrence epsilon)
          (coldOccurrencePresentationAt data object occurrence epsilon)
          (coldOccurrenceIndexAt data object occurrence epsilon)
          (coldOccurrenceIncidence data object occurrence epsilon)
          (ColdDeclaredHandoffSupport data object) earlier) ∧
    (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
        ((coldOccurrenceCorridorAt data object occurrence epsilon).prefixSupport
          right.1)
        ((coldOccurrenceCorridorAt data object occurrence epsilon).prefixSupport
          left.1)).boundaryDegreeProfile ≠
      (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
        ((coldOccurrenceCorridorAt data object occurrence epsilon).prefixSupport
          right.1)
        ((coldOccurrenceCorridorAt data object occurrence epsilon).prefixSupport
          right.1)).boundaryDegreeProfile ∧
    ((coldOccurrencePresentationAt data object occurrence epsilon).state
        (coldOccurrenceIndexAt data object occurrence epsilon left)).boundaryDegrees =
      ((coldOccurrencePresentationAt data object occurrence epsilon).state
        (coldOccurrenceIndexAt data object occurrence epsilon right)).boundaryDegrees ∧
    min (object.degree
        ((coldOccurrenceCorridorAt data object occurrence epsilon).head left))
        data.coldSignature.degreeBound =
      min (object.degree
        ((coldOccurrenceCorridorAt data object occurrence epsilon).head right))
        data.coldSignature.degreeBound

/-- The configuration of `[153]`'s residual at a witness
(`ColdRepeatedStateSpecAt` at its pinned objects). -/
def ColdRepeatedStateSpec (data : Parameters) (object : Graph.FiniteObject.{u})
    (witness : ColdRepeatWitness data object) : Prop :=
  ColdRepeatedStateSpecAt data object witness.occurrence witness.epsilon witness.left
    witness.right

/-- **G's canonical `[153]` residual witness**: `some` witness satisfying
`ColdRepeatedStateSpec` (a canonical choice among them), or `none`. -/
noncomputable def coldRepeatWitness? (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Option (ColdRepeatWitness data object) := by
  classical
  exact if exists_ : ∃ witness, ColdRepeatedStateSpec data object witness then
    some (Classical.choose exists_) else none

theorem coldRepeatWitness?_spec {data : Parameters} {object : Graph.FiniteObject.{u}}
    {witness : ColdRepeatWitness data object}
    (pinned : coldRepeatWitness? data object = some witness) :
    ColdRepeatedStateSpec data object witness := by
  classical
  unfold coldRepeatWitness? at pinned
  split at pinned
  · cases pinned; exact Classical.choose_spec ‹_›
  · cases pinned

theorem coldRepeatWitness?_eq_some {data : Parameters} {object : Graph.FiniteObject.{u}}
    (exists_ : ∃ witness, ColdRepeatedStateSpec data object witness) :
    ∃ witness, coldRepeatWitness? data object = some witness := by
  classical
  unfold coldRepeatWitness?
  rw [dif_pos exists_]
  exact ⟨_, rfl⟩

/-- **The residual of `[153]`: G's first equal-state pair with its excision
data, constructed**, read at G's canonical witness `coldRepeatWitness?`. -/
def ColdRepeatedStateResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ witness, coldRepeatWitness? data object = some witness ∧
    ColdRepeatedStateSpec data object witness

/-! ## `[162]`: heavy entries before the terminal segment -/

/-- **The heavy-entry test of `[162]` at G**: every retained corridor of G whose
first failure is an (F4) entry into a heavy centre of G at a segment strictly
before its terminal segment is still terminal (reads at most `Q_cold` states). -/
def ColdHeavyEntryTerminalStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (occurrence : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (first : (coldOccurrenceCorridorAt data object occurrence epsilon).Segment),
    (∀ earlier : (coldOccurrenceCorridorAt data object occurrence epsilon).Segment,
      earlier.1 < first.1 →
        ¬ ColdFirstFailureEvent data object
          (coldOccurrenceCorridorAt data object occurrence epsilon)
          (coldOccurrencePresentationAt data object occurrence epsilon)
          (coldOccurrenceIndexAt data object occurrence epsilon)
          (coldOccurrenceIncidence data object occurrence epsilon)
          (ColdDeclaredHandoffSupport data object) earlier) →
    ColdFirstFailureHandoffAt object
      (coldOccurrenceCorridorAt data object occurrence epsilon)
      (ColdDeclaredHandoffSupport data object) first →
    first.1 < (coldOccurrenceCorridorAt data object occurrence epsilon).inside.1.length →
    (coldOccurrenceCorridorAt data object occurrence epsilon).TerminalCorridor
      data.coldSignature

/-- The pinned objects of `[162]`'s residual: an occurrence of G's retained
first-failure data, an eligible half-edge `ε` of G, a segment of G's retained
corridor of `ε`, and a vertex of G. -/
abbrev ColdHeavyEntryWitness (data : Parameters) (object : Graph.FiniteObject.{u}) :=
  Σ' occurrence : ColdFirstFailureOccurrenceData data object,
    Σ' epsilon : ColdEligibleHalfEdge data object,
      (coldOccurrenceCorridorAt data object occurrence epsilon).Segment × object.Vertex

/-- The occurrence of a `[162]` witness. -/
abbrev ColdHeavyEntryWitness.occurrence {data : Parameters}
    {object : Graph.FiniteObject.{u}} (witness : ColdHeavyEntryWitness data object) :
    ColdFirstFailureOccurrenceData data object :=
  witness.1

/-- The half-edge `ε` of a `[162]` witness. -/
abbrev ColdHeavyEntryWitness.epsilon {data : Parameters}
    {object : Graph.FiniteObject.{u}} (witness : ColdHeavyEntryWitness data object) :
    ColdEligibleHalfEdge data object :=
  witness.2.1

/-- The (F4) first-failure segment of a `[162]` witness. -/
abbrev ColdHeavyEntryWitness.first {data : Parameters}
    {object : Graph.FiniteObject.{u}} (witness : ColdHeavyEntryWitness data object) :
    (coldOccurrenceCorridorAt data object witness.occurrence witness.epsilon).Segment :=
  witness.2.2.1

/-- The heavy centre of G of a `[162]` witness. -/
abbrev ColdHeavyEntryWitness.centre {data : Parameters}
    {object : Graph.FiniteObject.{u}} (witness : ColdHeavyEntryWitness data object) :
    object.Vertex :=
  witness.2.2.2

/-- **The configuration of `[162]`'s residual at a witness.**  On G's retained
corridor `C_ε` with G's pinned cut states:

* the first failure is the segment `first`, an (F4) event: `head first` is the
  vertex `centre` of G with `d_G(centre) > δ` (a heavy handoff centre of G), and
  no earlier segment has any (F1)--(F5) event;
* the pinned cut states of the segments up to `first` are pairwise distinct,
  so `first < Q_cold`;
* `first` is strictly before the terminal segment, and the corridor is not
  terminal: `Q_cold ≤ |C_ε|`. -/
def ColdDenseHeavyEntrySpecAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (first : (coldOccurrenceCorridorAt data object occurrence epsilon).Segment)
    (centre : object.Vertex) : Prop :=
  (coldOccurrenceCorridorAt data object occurrence epsilon).head first = centre ∧
    data.threshold < object.degree centre ∧
    ColdFirstFailureHandoffAt object
      (coldOccurrenceCorridorAt data object occurrence epsilon)
      (ColdDeclaredHandoffSupport data object) first ∧
    (∀ earlier : (coldOccurrenceCorridorAt data object occurrence epsilon).Segment,
      earlier.1 < first.1 →
        ¬ ColdFirstFailureEvent data object
          (coldOccurrenceCorridorAt data object occurrence epsilon)
          (coldOccurrencePresentationAt data object occurrence epsilon)
          (coldOccurrenceIndexAt data object occurrence epsilon)
          (coldOccurrenceIncidence data object occurrence epsilon)
          (ColdDeclaredHandoffSupport data object) earlier) ∧
    (∀ left right : (coldOccurrenceCorridorAt data object occurrence epsilon).Segment,
      left.1 < right.1 → right.1 ≤ first.1 →
        (coldOccurrencePresentationAt data object occurrence epsilon).state
            (coldOccurrenceIndexAt data object occurrence epsilon left) ≠
          (coldOccurrencePresentationAt data object occurrence epsilon).state
            (coldOccurrenceIndexAt data object occurrence epsilon right)) ∧
    first.1 < Graph.ColdCorridor.stateBound data.coldSignature ∧
    first.1 < (coldOccurrenceCorridorAt data object occurrence epsilon).inside.1.length ∧
    Graph.ColdCorridor.stateBound data.coldSignature ≤
      (coldOccurrenceCorridorAt data object occurrence epsilon).inside.1.length ∧
    ¬ (coldOccurrenceCorridorAt data object occurrence epsilon).TerminalCorridor
      data.coldSignature

/-- The configuration of `[162]`'s residual at a witness
(`ColdDenseHeavyEntrySpecAt` at its pinned objects). -/
def ColdDenseHeavyEntrySpec (data : Parameters) (object : Graph.FiniteObject.{u})
    (witness : ColdHeavyEntryWitness data object) : Prop :=
  ColdDenseHeavyEntrySpecAt data object witness.occurrence witness.epsilon witness.first
    witness.centre

/-- **G's canonical `[162]` residual witness**. -/
noncomputable def coldHeavyEntryWitness? (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Option (ColdHeavyEntryWitness data object) := by
  classical
  exact if exists_ : ∃ witness, ColdDenseHeavyEntrySpec data object witness then
    some (Classical.choose exists_) else none

theorem coldHeavyEntryWitness?_spec {data : Parameters} {object : Graph.FiniteObject.{u}}
    {witness : ColdHeavyEntryWitness data object}
    (pinned : coldHeavyEntryWitness? data object = some witness) :
    ColdDenseHeavyEntrySpec data object witness := by
  classical
  unfold coldHeavyEntryWitness? at pinned
  split at pinned
  · cases pinned; exact Classical.choose_spec ‹_›
  · cases pinned

theorem coldHeavyEntryWitness?_eq_some {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (exists_ : ∃ witness, ColdDenseHeavyEntrySpec data object witness) :
    ∃ witness, coldHeavyEntryWitness? data object = some witness := by
  classical
  unfold coldHeavyEntryWitness?
  rw [dif_pos exists_]
  exact ⟨_, rfl⟩

/-- **The residual of `[162]`: a non-terminal corridor of G whose first failure
is a heavy centre, constructed**, read at G's canonical
witness `coldHeavyEntryWitness?`. -/
def ColdDenseHeavyEntryResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ witness, coldHeavyEntryWitness? data object = some witness ∧
    ColdDenseHeavyEntrySpec data object witness

/-! ## `[54]`: the joint realization inequality -/

/-- **The outer room of `G` at `R₀`**: `C(C(n,2) − C(|R₀|,2), m − e(G[R₀]))`, the
number of ways to place `G`'s `m − e(G[R₀])` edges not inside the remainder
`R₀ = R(P₀)` of the fixed packing on the pairs not inside `R₀`. -/
noncomputable def remainderOuterRoom (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Nat :=
  (object.vertexCount.choose 2 -
      (object.remainderSupport (canonicalWindowPacking data object)).card.choose 2).choose
    (object.edgeCount -
      object.internalEdgeCount (object.remainderSupport (canonicalWindowPacking data object)))

/-- **The joint realization inequality of `prop:entropy-high-theta` at G**
(tex 9921): the remainder states of `R₀`, the window package of the `p₁₃`
windows of `P₀` and the forced obstruction bits of node `[48]` fit the labelled
skeleton budget of G's class: `RS(R₀)·2^{rate·s·p₁₃}·2^F ≤ B`. -/
def EntropyJointRealizationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  remainderStates data object (canonicalWindowPacking data object) *
      2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
        (canonicalWindowPacking data object).card) *
      2 ^ forcedObstructionBits data object ≤
    Graph.skeletonBudget object

/-- **The residual of `[54]`: the configuration at G where the joint
realization fails, constructed.**  At G's fixed packing `P₀` and remainder
`R₀ = R(P₀)`:

* the package of `P₀` overflows the labelled skeleton budget of G's class, in
  aggregate form (no state map, no class member): `B < 2^{b_P·p}` or
  `B < retainedCode P₀` (equivalent, with `lem:skeleton-dominates`, to
  `¬ WindowFamilyRealized P₀`, `Contracts.Spine.unretained_package_overflow`);
* the remainder glue on disjoint supports: `RS(R₀) · room ≤ B`, with
  `room = C(C(n,2) − C(|R₀|,2), m − e(G[R₀]))` the outer room of G at `R₀`;
* the forced bits of `[48]`: `F ≤ c_Ω·r_Ω(R₀)`;
* the window package and the forced bits do not fit the outer room:
  `room < 2^{rate·s·p₁₃}·2^F`;
* `[53]` is active: `B < 2^{rate·s·p₁₃}·RS(R₀)·2^F`;
* the joint realization inequality fails:
  `¬ RS(R₀)·2^{rate·s·p₁₃}·2^F ≤ B`. -/
def AllColdEntropyResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (Graph.skeletonBudget object <
      2 ^ (windowPackageBits data object * (canonicalWindowPacking data object).card) ∨
    Graph.skeletonBudget object <
      retainedCode data object (canonicalWindowPacking data object)) ∧
  remainderStates data object (canonicalWindowPacking data object) *
      remainderOuterRoom data object ≤ Graph.skeletonBudget object ∧
  remainderOuterRoom data object =
    (object.vertexCount.choose 2 -
        (object.remainderSupport (canonicalWindowPacking data object)).card.choose 2).choose
      (object.edgeCount -
        object.internalEdgeCount
          (object.remainderSupport (canonicalWindowPacking data object))) ∧
  forcedObstructionBits data object ≤
    data.curvatureCost *
      remainderCurvatureTargetRank data object (canonicalWindowPacking data object) ∧
  remainderOuterRoom data object <
    2 ^ (data.windowRate * data.separatedScaleCount object.vertexCount *
          (canonicalWindowPacking data object).card) *
      2 ^ forcedObstructionBits data object ∧
  Graph.skeletonBudget object <
    jointPackageDemand data object * 2 ^ forcedObstructionBits data object ∧
  ¬ EntropyJointRealizationStatement data object

end Hypostructure.Graph.Strategy.Spine
