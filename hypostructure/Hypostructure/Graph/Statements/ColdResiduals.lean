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
  constructed first equal-state pair of one retained corridor of G, with its
  separating path context and its boundary-degree separation
  (`ColdRepeatedStateResidualStatement`);
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

/-- **The residual of `[153]`: G's first equal-state pair, constructed.**

For one eligible half-edge `ε` of G, on G's retained corridor `C_ε`
(`coldOccurrenceCorridorAt`, in its outside component of `G − X_cold`), with
G's pinned cut states:

* segments `left < right` with equal states, and no equal pair before `right`
  (the first equal-state pair);
* no (F1)--(F5) event at any segment before `right` -- in particular no
  terminal (F5) and no heavy-centre (F4) event;
* the (F2) clause at `right` (so `right` is `ε`'s first failure, and it is
  (F2));
* the separating context `prefixContext` (a path of `2^(right+2) − right`
  edges with fresh interior, glued at `head right` and at the entry foot): with
  `piece J_right` it closes an accepted cycle, with the `J_left` reading
  `retainedPiece J_right J_left` it closes none;
* the two readings have different boundary-degree profiles on `∂J_right`
  (`head right` loses its corridor edge), so the pair is a profile separation
  and not a same-fibre defect of any declared coordinate. -/
def ColdRepeatedStateResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (occurrence : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (outside : Graph.ColdCorridor.IsOutsideComponent object
      (coldCorridorWindows data object)
      (coldOccurrenceComponentAt data object occurrence epsilon))
    (left right : (coldOccurrenceCorridorAt data object occurrence epsilon).Segment),
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
    ColdFirstFailureDefectAt data object
      (coldOccurrenceCorridorAt data object occurrence epsilon)
      (coldOccurrencePresentationAt data object occurrence epsilon)
      (coldOccurrenceIndexAt data object occurrence epsilon) right ∧
    Graph.HasCycleWithLength data.LengthOK
      (Graph.glue
        (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
          ((coldOccurrenceCorridorAt data object occurrence epsilon).prefixSupport
            right.1))
        (Graph.ColdEqualStates.prefixContext outside
          (coldOccurrenceCorridorAt data object occurrence epsilon) right)) ∧
    ¬ Graph.HasCycleWithLength data.LengthOK
      (Graph.glue
        (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
          ((coldOccurrenceCorridorAt data object occurrence epsilon).prefixSupport
            right.1)
          ((coldOccurrenceCorridorAt data object occurrence epsilon).prefixSupport
            left.1))
        (Graph.ColdEqualStates.prefixContext outside
          (coldOccurrenceCorridorAt data object occurrence epsilon) right)) ∧
    (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
        ((coldOccurrenceCorridorAt data object occurrence epsilon).prefixSupport
          right.1)
        ((coldOccurrenceCorridorAt data object occurrence epsilon).prefixSupport
          left.1)).boundaryDegreeProfile ≠
      (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
        ((coldOccurrenceCorridorAt data object occurrence epsilon).prefixSupport
          right.1)
        ((coldOccurrenceCorridorAt data object occurrence epsilon).prefixSupport
          right.1)).boundaryDegreeProfile

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

/-- **The residual of `[162]`: a long corridor of G through a heavy centre,
constructed.**

For one eligible half-edge `ε` of G, on G's retained corridor `C_ε` with G's
pinned cut states:

* the first failure is the segment `first`, an (F4) event: `head first` is a
  vertex `z` of G with `d_G(z) > δ` (a heavy handoff centre of G), and no
  earlier segment has any (F1)--(F5) event;
* the pinned cut states of the segments up to `first` are pairwise distinct,
  so `first < Q_cold`;
* `first` is strictly before the terminal segment, and the corridor is not
  terminal: it reads more than `Q_cold` states (`Q_cold ≤ |C_ε|`). -/
def ColdDenseHeavyEntryResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (occurrence : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (first : (coldOccurrenceCorridorAt data object occurrence epsilon).Segment)
    (centre : object.Vertex),
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

* the window package of `P₀` is not retained (`¬ WindowFamilyRealized P₀`);
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
  ¬ WindowFamilyRealized data object (canonicalWindowPacking data object) ∧
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
