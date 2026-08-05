import Hypostructure.Core.Strategy.FactOnlyStrategy
import Hypostructure.Core.Strategy.MinimalCounterexampleScope
import Hypostructure.Graph.RootedReturn
import Hypostructure.Graph.Minimality
import Hypostructure.Graph.DeletionCriticality
import Hypostructure.Graph.MinimumDegreeCycleTarget
import Hypostructure.Graph.FiniteEdgeBudget
import Hypostructure.Graph.SkeletonBudget
import Hypostructure.Graph.WindowPacking
import Hypostructure.Graph.WindowRemainder
import Hypostructure.Graph.BoundaryDemand
import Hypostructure.Graph.WindowInternalMass
import Hypostructure.Graph.WindowCurvatureCode
import Hypostructure.Graph.Strategy.InterfaceReplacement

/-!
# The minimum-degree cycle spine: fact vocabulary

The entry spine of a minimum-degree cycle problem proves a fixed sequence of
theorems about one selected minimal counterexample.  This module names them as
the closed semantic vocabulary of that residual domain, so each is a fact of
the one canonical `ExactLedger` rather than a payload, summary, or wrapper.

Nothing here is specialized to one manuscript.  The baseline threshold and the
accepted cycle-length predicate are parameters, so the same vocabulary serves
any minimum-degree cycle problem; a problem supplies its threshold through its
own presentation and never spells a numeral at a node.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

/-- **The registered data of a minimum-degree cycle spine.**

Every number the spine ever compares comes from this record, and a row is
forbidden to write one.  A problem supplies the record from its own
presentation; the manuscript's `3`, `13`, `399`, and window rate are its
values, not the framework's.

The one numeral that does appear below is the `3` of `three_le_threshold`, and
it is not a presentation constant: it is `⌈e⌉` from Stirling's bound
(`Core.FiniteEntropy.pow_self_le_three_pow_mul_factorial`), the constant that
makes the skeleton budget's `m !` pay for the density cap.  A presentation
whose baseline is below it does not reach node `[22]`. -/
structure Data where
  /-- The registered minimum-degree baseline `δ`. -/
  threshold : Nat
  /-- Stirling's `⌈e⌉` against the registered baseline; see the note above. -/
  three_le_threshold : 3 ≤ threshold
  /-- The accepted cycle lengths the counterexample must avoid. -/
  LengthOK : Nat → Prop
  /-- The order of the induced obstruction window.  For `thm:p13free` this is
  the induced-path order; nothing here knows its value. -/
  windowOrder : Nat
  windowOrder_pos : 0 < windowOrder
  /-- The cited external closure law.  An object meeting the baseline with no
  induced window of the registered order has an accepted cycle.  This is the
  only place a result outside the manuscript enters the spine, and it enters at
  the manuscript's own interface. -/
  freeForcesTarget : ∀ object : Graph.FiniteObject.{u},
    Graph.MinimumDegreeAtLeast threshold object →
    Graph.InducedPathFree object windowOrder →
    Graph.HasCycleWithLength LengthOK object
  /-- The registered scale threshold `C_sp·⌈√n⌉`, as a function of the order. -/
  surplusThreshold : Nat → Nat
  /-- The registered per-window barrier rate of the finite enumeration. -/
  windowRate : Nat

/-- The problem this spine argues about: a minimum-degree baseline at the
registered threshold, with the problem's own presentation attached. -/
abbrev problem (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :
    Core.Problem.{u + 1, v} :=
  Graph.problemWithPresentation (Graph.MinimumDegreeAtLeast data.threshold)
    BranchState Presentation presentation

/-- The registered progress order: vertex count, then edge count. -/
abbrev progress (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :
    Core.Progress.{u + 1, v, 0}
      (problem BranchState Presentation presentation data) :=
  (Graph.CanonicalProgress.progress
    (P := problem BranchState Presentation presentation data))

/-- The semantic facts the entry spine proves.

Each constructor is one manuscript statement.  A key determines exactly one
value schema, so two unrelated facts cannot impersonate one another. -/
inductive Key where
  /-- Nodes `[1]`--`[4]`: the selected object avoids the target and every
  strictly smaller baseline object does not. -/
  | selection
  /-- Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted
  accepted set at every oriented edge.  This is the return-set form of target
  avoidance, the standing invariant the rest of the spine consumes. -/
  | returnAvoidance
  /-- Node `[8]`: no proper subgraph satisfies the baseline. -/
  | noProperBaseline
  /-- Node `[9]`: every oriented edge has an endpoint exactly at the
  threshold. -/
  | tightEndpoint
  /-- Node `[10]`: vertices strictly above the threshold are pairwise
  nonadjacent. -/
  | slackIndependent
  /-- Nodes `[11]`--`[14]`: no proper atom admits a nontrivial target-complete
  compression (`cor:uncompressible`). -/
  | uncompressible
  /-- Nodes `[15]`--`[17]`: the object carries a maximal vertex-disjoint family
  of induced windows, and the family is nonempty. -/
  | maximalPacking
  /-- Node `[18]`: the local label algebra of the registered window order is
  exactly enumerated and its curvature relation is decided (`lem:labels`). -/
  | localAlgebra
  /-- Node `[19]`, above arm: the degree surplus exceeds the registered scale
  threshold. -/
  | surplusAbove
  /-- Node `[19]`, at-or-below arm: `def:near-cubic-spine` in exact finite
  form. -/
  | surplusAtOrBelow
  /-- Node `[21]`, cap arm: the packing's entropy demand fits inside the
  labelled skeleton budget, which is itself stable under a variable edge
  count. -/
  | barrierCap
  /-- Node `[21]`, overflow arm: the demand exceeds the budget. -/
  | barrierOverflow
  /-- Nodes `[22]`--`[24]`: `prop:p13-density`, the linear cap on the packing
  in the object's own dyadic scale. -/
  | densityCap
  /-- Nodes `[25]`--`[27]`: the remainder of a maximal packing carries no
  window and no subgraph meeting the baseline (`sec:remainder`). -/
  | remainderNormalized
  /-- Nodes `[28]`--`[29]`: the remainder's positive deficiency is supplied by
  its boundary incidences (`lem:surplus-aware-window-stub`). -/
  | boundaryDemand
  deriving DecidableEq

/-- The value schema of each spine fact, stated of the *object* alone.

Every spine fact is a statement about the selected graph, never about the
branch state carried beside it.  Making that explicit is what lets a fact
transport along a refinement by a rewrite: refinement is object equality.

`localAlgebra` is the one clause that does not mention the object: the window
algebra is a property of the registered order, and saying so is what makes it
transport for free. -/
def Holds (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :
    Key → Graph.FiniteObject.{u} → Prop
  | .selection, object =>
      (¬ Graph.HasCycleWithLength data.LengthOK object ∧
        ∀ smaller : Graph.FiniteObject.{u},
          (progress BranchState Presentation presentation data).Smaller
            smaller object →
          Graph.MinimumDegreeAtLeast data.threshold smaller →
          Graph.HasCycleWithLength data.LengthOK smaller)
  | .returnAvoidance, object =>
      (∀ dart : object.graph.Dart,
        Disjoint (Graph.returnLengthSet object dart)
          (Graph.shiftedAcceptedSet data.LengthOK))
  | .noProperBaseline, object =>
      (∀ subgraph : Graph.ProperSubgraph object,
        ¬ Graph.MinimumDegreeAtLeast data.threshold subgraph.value)
  | .tightEndpoint, object =>
      (∀ dart : object.graph.Dart,
        object.degree dart.fst = data.threshold ∨
          object.degree dart.snd = data.threshold)
  | .slackIndependent, object =>
      (∀ left right : object.Vertex,
        data.threshold < object.degree left →
        data.threshold < object.degree right →
        ¬ object.graph.Adj left right)
  | .uncompressible, object =>
      (∀ support : Finset object.Vertex,
        ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object support)
  | .maximalPacking, object =>
      (0 < object.windowPackingNumber data.windowOrder ∧
        ∃ packing : Finset (Finset object.Vertex),
          object.IsWindowPacking data.windowOrder packing ∧
            packing.card = object.windowPackingNumber data.windowOrder ∧
            ∀ support : Finset object.Vertex,
              object.InducesWindow data.windowOrder support →
              ∃ member ∈ packing, ¬ Disjoint support member)
  | .localAlgebra, _object =>
      ((Graph.WindowCurvature.legalCodeList data.windowOrder).length =
          (Graph.WindowCurvature.Labels data.windowOrder).card ∧
        ∀ source middle target : Graph.WindowCurvature.Label data.windowOrder,
          Graph.WindowCurvature.curvatureTwo source middle target = true ↔
            Graph.WindowCurvature.Safe 1 source middle ∧
              Graph.WindowCurvature.Safe 1 middle target ∧
              ¬ Graph.WindowCurvature.Safe 2 source target)
  | .surplusAbove, object =>
      (data.surplusThreshold object.vertexCount <
        object.degreeSurplus data.threshold)
  | .surplusAtOrBelow, object =>
      (object.degreeSurplus data.threshold ≤
        data.surplusThreshold object.vertexCount)
  | .barrierCap, object =>
      (2 ^ (data.windowRate * object.windowPackingNumber data.windowOrder) ≤
          Graph.skeletonBudget object ∧
        ∀ family : Finset Nat, object.edgeCount ∈ family →
          Graph.skeletonBudget object ≤
            Graph.variableEdgeBudget object.vertexCount family)
  | .barrierOverflow, object =>
      (Graph.skeletonBudget object <
        2 ^ (data.windowRate * object.windowPackingNumber data.windowOrder))
  | .densityCap, object =>
      (2 * (data.windowRate * object.windowPackingNumber data.windowOrder) ≤
        (Graph.dyadicScaleCount object + 1) *
          (data.threshold * object.vertexCount +
            data.surplusThreshold object.vertexCount))
  | .remainderNormalized, object =>
      -- Quantified over every maximal packing, so no family has to travel from
      -- the row that produced one: the statement is about all of them.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ support : Finset object.Vertex,
          support ⊆ object.remainderSupport packing →
          ¬ object.InducesWindow data.windowOrder support ∧
            ¬ Graph.MinimumDegreeAtLeast data.threshold
              (object.induce support))
  | .boundaryDemand, object =>
      -- `lem:surplus-aware-window-stub`, subtraction-free:
      --   `def⁺(R) + 2(order−1)·p ≤ δ·order·p + σ_W`,
      -- i.e. `def⁺(R) ≤ e(R,W) ≤ (δ·order − 2(order−1))·p + σ_W`, which at the
      -- registered presentation is `def⁺(R) ≤ 15p₁₃ + σ_W`.  No near-cubic
      -- hypothesis, and the statement holds at every packing, so none travels.
      (∀ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing →
        object.positiveDeficiency (object.remainderSupport packing)
              data.threshold +
            2 * (data.windowOrder - 1) * packing.card ≤
          data.threshold * (data.windowOrder * packing.card) +
            object.ambientSurplus (Graph.FiniteObject.windowSupport packing)
              data.threshold)

/-- Audit names.  They are diagnostics; every routing and lookup decision
compares exact keys. -/
def name : Key → Lean.Name
  | .selection => `Hypostructure.Graph.Strategy.Spine.selection
  | .returnAvoidance => `Hypostructure.Graph.Strategy.Spine.returnAvoidance
  | .noProperBaseline => `Hypostructure.Graph.Strategy.Spine.noProperBaseline
  | .tightEndpoint => `Hypostructure.Graph.Strategy.Spine.tightEndpoint
  | .slackIndependent => `Hypostructure.Graph.Strategy.Spine.slackIndependent
  | .uncompressible => `Hypostructure.Graph.Strategy.Spine.uncompressible
  | .maximalPacking => `Hypostructure.Graph.Strategy.Spine.maximalPacking
  | .localAlgebra => `Hypostructure.Graph.Strategy.Spine.localAlgebra
  | .surplusAbove => `Hypostructure.Graph.Strategy.Spine.surplusAbove
  | .surplusAtOrBelow => `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow
  | .barrierCap => `Hypostructure.Graph.Strategy.Spine.barrierCap
  | .barrierOverflow => `Hypostructure.Graph.Strategy.Spine.barrierOverflow
  | .densityCap => `Hypostructure.Graph.Strategy.Spine.densityCap
  | .remainderNormalized =>
      `Hypostructure.Graph.Strategy.Spine.remainderNormalized
  | .boundaryDemand => `Hypostructure.Graph.Strategy.Spine.boundaryDemand

/-- The value schema at a residual: the object-level statement, read at the
residual's own object. -/
def Value (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u})
    (k : Key)
    (input : Core.Strategy.ProblemInput
      (problem BranchState Presentation presentation data)) : Type :=
  PLift (Holds BranchState Presentation presentation data k input.object)

theorem name_injective : Function.Injective name := by
  intro left right same
  cases left <;> cases right <;> simp_all [name]

/-- The spine's closed fact vocabulary.  Every value depends on the residual
only through its object, so transport along a refinement is a rewrite. -/
def vocabulary (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :
    FactVocabulary.{u + 1, v, 0, 0}
      (problem BranchState Presentation presentation data) where
  Key := Key
  keyDecidableEq := inferInstance
  name := name
  name_injective := name_injective
  name_ne_closure := by intro key; cases key <;> decide
  Value := Value BranchState Presentation presentation data
  -- Every spine fact is `PLift` of a proposition, so its value type has at
  -- most one inhabitant: the fact is the statement, and the graph it speaks
  -- about is the residual's.
  value_subsingleton := fun _ _ => ⟨fun left right => by
    cases left; cases right; rfl⟩
  transport := fun {_key} {_new _old} refinement value =>
    ⟨by rw [show _new.object = _old.object from refinement]; exact value.down⟩

/-- The spine's sole `FactSystem`.  It is a definition rather than an
instance because the registered `Data` is a parameter of the spine, not of the
problem; a caller installs it with `letI` for the run it is compiling. -/
noncomputable def factSystem
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :
    FactSystem
      (Core.Strategy.ProblemInput
        (problem BranchState Presentation presentation data)) :=
  problemInputFactSystem
    (vocabulary BranchState Presentation presentation data)

/-- The exact semantic keys, as callers name them. -/
abbrev key (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u})
    (k : Key) :
    @FactKey _ _ (factSystem BranchState Presentation presentation data) :=
  FactVocabulary.WithClosure.fact k

end Hypostructure.Graph.Strategy.Spine
