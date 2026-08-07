import Hypostructure.Graph.SeparatedPackageSkeleton
import Hypostructure.Graph.SparseEntropySandwich
import Hypostructure.Graph.DeclaredCoordinateSignature

namespace Hypostructure.Graph

open Hypostructure

universe u

namespace FiniteObject

variable (object : FiniteObject.{u})

/-- A binary coordinate extracted from the certified multi-scale window
package.  Its label records the bit of the package and its declared support is
the packed-window support. -/
abbrev WindowTargetCoordinate (bits : Nat) :=
  DeclaredSignature.Coordinate object.Vertex (Fin bits)

noncomputable def windowTargetCoordinate {bits : Nat}
    (support : Finset object.Vertex) (bit : Fin bits) :
    object.WindowTargetCoordinate bits :=
  .base .windowLabel bit support

noncomputable def windowTargetFamily (bits : Nat)
    (support : Finset object.Vertex) :
    Finset (object.WindowTargetCoordinate bits) := by
  classical
  exact Finset.univ.image (object.windowTargetCoordinate support)

/-- The support projection carried by the finite object, with its canonical
decidable equality made explicit.  Keeping this projection in the package API
prevents downstream strategy rows from manufacturing typeclass plumbing. -/
noncomputable def windowTargetSupport {bits : Nat} :
    object.WindowTargetCoordinate bits → Finset object.Vertex := by
  letI := object.vertices.decEq
  exact DeclaredSignature.Coordinate.support

theorem card_windowTargetFamily (bits : Nat)
    (support : Finset object.Vertex) :
    (object.windowTargetFamily bits support).card = bits := by
  classical
  rw [windowTargetFamily, Finset.card_image_iff.mpr]
  · simp
  · intro left _ right _ equality
    simp only [windowTargetCoordinate,
      DeclaredSignature.Coordinate.base.injEq] at equality
    exact equality.2.1

/-- The declared family used by the mixed sparse-spine count: the selected
window coordinates and one labelled response coordinate for every free pair.
The sum tags make the union disjoint, exactly as the manuscript's labelled
copies clause (D8) requires. -/
abbrev MixedTargetCoordinate (bits : Nat) :=
  Sum (object.WindowTargetCoordinate bits) (PairCoordinate object)

noncomputable def mixedTargetFamily (bits : Nat)
    (windowSupport : Finset object.Vertex)
    (pairs : Finset (PairCoordinate object)) :
    Finset (object.MixedTargetCoordinate bits) := by
  classical
  exact (object.windowTargetFamily bits windowSupport).image Sum.inl ∪
    pairs.image Sum.inr

noncomputable def mixedTargetSupport {bits : Nat} :
    object.MixedTargetCoordinate bits → Finset object.Vertex := by
  letI := object.vertices.decEq
  exact Sum.elim object.windowTargetSupport
    DeclaredSignature.Coordinate.support

theorem card_mixedTargetFamily (bits : Nat)
    (windowSupport : Finset object.Vertex)
    (pairs : Finset (PairCoordinate object)) :
    (object.mixedTargetFamily bits windowSupport pairs).card =
      bits + pairs.card := by
  classical
  rw [mixedTargetFamily, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_iff.mpr Sum.inl_injective.injOn,
      object.card_windowTargetFamily,
      Finset.card_image_iff.mpr Sum.inr_injective.injOn]
  · exact Finset.disjoint_left.mpr fun value left right => by
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp left
      obtain ⟨_, _, equality⟩ := Finset.mem_image.mp right
      cases equality

/-- The complete mathematical object exported by the multi-scale window
package: its concrete packing, declared coordinates, exact support map, full
target rank, and realization in the object's exact edge stratum. -/
structure WindowTargetPackage
    (Baseline : FiniteObject.{u} → Prop) (LengthOK : Nat → Prop)
    (order : Nat) (packing : Finset (Finset object.Vertex)) (bits : Nat) : Prop where
  valid : object.IsWindowPacking order packing
  fullRank :
    Core.TargetRank.targetRank
        (object.declaredQuotientSystem Baseline
          (Graph.HasCycleWithLength LengthOK)
          (object.windowTargetFamily bits (object.windowSupport packing))
          object.windowTargetSupport) = bits
  exactEntropy : 2 ^ bits ≤ skeletonBudget object
  /-- `lem:independent-target-entropy` for the package after adjoining any
  independently target-testable sparse pair family.  This is the positive arm
  selected at node `[21]`; failure belongs to that node's cold arm and is never
  turned into a downstream hypothesis. -/
  mixedEntropy : ∀ pairs : Finset (PairCoordinate object),
    Core.TargetRank.targetRank
        (object.declaredQuotientSystem Baseline
          (Graph.HasCycleWithLength LengthOK)
          (object.mixedTargetFamily bits (object.windowSupport packing) pairs)
          object.mixedTargetSupport) =
      (object.mixedTargetFamily bits
        (object.windowSupport packing) pairs).card →
    2 ^ (bits + pairs.card) ≤ skeletonBudget object

/-- A concrete baseline demand extracted from one declared window package.
Unlike the old strategy-level conversion schema, this object fixes the family,
the quotient system, its exact rank, and the deficit consumed downstream. -/
structure BaselineWindowDemand
    (Baseline : FiniteObject.{u} → Prop) (LengthOK : Nat → Prop)
    (baselineDegree order deficitScale : Nat) : Type u where
  packing : Finset (Finset object.Vertex)
  bits : Nat
  package : object.WindowTargetPackage Baseline LengthOK order packing bits
  demand : IsBaselineSpineDemand
    (object.declaredQuotientSystem Baseline
      (Graph.HasCycleWithLength LengthOK)
      (object.windowTargetFamily bits (object.windowSupport packing))
      object.windowTargetSupport)
    object.vertexCount baselineDegree
    (spineDeficit object.vertexCount baselineDegree bits)
  /-- The paper's actual `E_spine(n) <= C_E n` certificate.  It travels with
  the concrete family, so no downstream entropy or token row can turn it into
  an antecedent. -/
  deficitBound :
    spineDeficit object.vertexCount baselineDegree bits ≤
      deficitScale * object.vertexCount

/-- The actual mixed object counted at node `[131]`: the concrete spine family
from node `[129]` together with the response coordinates indexed by the
activation's unblocked pairs. -/
structure MixedSpinePairDemand
    (Baseline : FiniteObject.{u} → Prop) (LengthOK : Nat → Prop)
    (baselineDegree order deficitScale : Nat)
    {Coordinate Chord : Type u}
    (baseline : object.BaselineWindowDemand Baseline LengthOK baselineDegree order
      deficitScale)
    (activation : object.DemandActivation Coordinate Chord) : Prop where
  fullRank :
    Core.TargetRank.targetRank
        (object.declaredQuotientSystem Baseline
          (Graph.HasCycleWithLength LengthOK)
          (object.mixedTargetFamily baseline.bits
            (object.windowSupport baseline.packing)
            (activation.pairFamily (activation.freePairs baselineDegree)))
          object.mixedTargetSupport) =
      (object.mixedTargetFamily baseline.bits
        (object.windowSupport baseline.packing)
        (activation.pairFamily (activation.freePairs baselineDegree))).card
  exactEntropy :
    2 ^ (baseline.bits + (activation.freePairs baselineDegree).card) ≤
      skeletonBudget object
  sandwich :
    2 ^ (activation.freePairs baselineDegree).card ≤
      2 ^ (spineDeficit object.vertexCount baselineDegree baseline.bits) *
        object.vertexCount ^
          (object.edgeCount -
            cubicBaselineEdgeCount object.vertexCount baselineDegree)
  linearSandwich :
    (activation.freePairs baselineDegree).card ≤
      spineDeficit object.vertexCount baselineDegree baseline.bits +
        (Nat.log2 object.vertexCount + 1) *
          (object.edgeCount -
            cubicBaselineEdgeCount object.vertexCount baselineDegree)

/-- Read a full-rank window package as the concrete baseline demand with its
computed deficit.  There is no supplied theorem or callback: both clauses are
the package's rank equation and the generic exact cubic-budget inequality. -/
noncomputable def baselineWindowDemandOfPackage
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {baselineDegree order deficitScale : Nat} (baseline : 2 ≤ baselineDegree)
    {packing : Finset (Finset object.Vertex)} {bits : Nat}
    (package : object.WindowTargetPackage Baseline LengthOK order packing bits)
    (deficitBound : spineDeficit object.vertexCount baselineDegree bits ≤
      deficitScale * object.vertexCount) :
    object.BaselineWindowDemand Baseline LengthOK baselineDegree order
      deficitScale where
  packing := packing
  bits := bits
  package := package
  demand := {
    independent := by
      rw [package.fullRank, object.card_windowTargetFamily]
    demand := by
      simpa [object.card_windowTargetFamily] using
        cubicBaselineBudget_le_two_pow_add_spineDeficit
          object.vertexCount baseline bits }
  deficitBound := deficitBound

/-- Build node `[131]`'s mixed count from the concrete node-`[129]` package
and the exit-free facts already present on the incoming residual.  The entropy
inequality is the package's positive node-`[21]` arm; the sandwich is then the
paper's exact cancellation argument. -/
theorem mixedSpinePairDemand
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {baselineDegree order deficitScale : Nat} {Coordinate Chord : Type u}
    (two_le : 2 ≤ baselineDegree)
    (above : cubicBaselineEdgeCount object.vertexCount baselineDegree ≤
      object.edgeCount)
    (baseline : object.BaselineWindowDemand Baseline LengthOK baselineDegree order
      deficitScale)
    (activation : object.DemandActivation Coordinate Chord)
    (rank : Core.TargetRank.targetRank
        (object.declaredQuotientSystem Baseline
          (Graph.HasCycleWithLength LengthOK)
          (object.mixedTargetFamily baseline.bits
            (object.windowSupport baseline.packing)
            (activation.pairFamily (activation.freePairs baselineDegree)))
          object.mixedTargetSupport) =
      (object.mixedTargetFamily baseline.bits
        (object.windowSupport baseline.packing)
        (activation.pairFamily (activation.freePairs baselineDegree))).card) :
    object.MixedSpinePairDemand Baseline LengthOK baselineDegree order deficitScale
      baseline activation := by
  let pairs := activation.pairFamily (activation.freePairs baselineDegree)
  have entropyBits :
      2 ^ (baseline.bits + pairs.card) ≤ skeletonBudget object :=
    baseline.package.mixedEntropy pairs rank
  have pairCard : pairs.card = (activation.freePairs baselineDegree).card :=
    activation.card_pairFamily _
  refine {
    fullRank := rank
    exactEntropy := by simpa [pairs, pairCard] using entropyBits
    sandwich := ?_
    linearSandwich := ?_ }
  · apply entropySandwich object two_le above
    · simpa [pairs, pairCard] using entropyBits
    · have demand := baseline.demand.demand
      rw [object.card_windowTargetFamily] at demand
      exact demand
  · let deficit := spineDeficit object.vertexCount baselineDegree baseline.bits
    let slack := object.edgeCount -
      cubicBaselineEdgeCount object.vertexCount baselineDegree
    have exponential := entropySandwich object two_le above
      (by simpa [pairs, pairCard] using entropyBits) (by
        have demand := baseline.demand.demand
        rw [object.card_windowTargetFamily] at demand
        exact demand)
    have baseBound : object.vertexCount ≤
        2 ^ (Nat.log2 object.vertexCount + 1) :=
      le_of_lt (by simpa [Nat.log2_eq_log_two] using
        Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) object.vertexCount)
    have raised : object.vertexCount ^ slack ≤
        (2 ^ (Nat.log2 object.vertexCount + 1)) ^ slack :=
      Nat.pow_le_pow_left baseBound slack
    rw [← Nat.pow_mul] at raised
    have powers :
        2 ^ (activation.freePairs baselineDegree).card ≤
          2 ^ (deficit + (Nat.log2 object.vertexCount + 1) * slack) := by
      calc
        _ ≤ 2 ^ deficit * object.vertexCount ^ slack := exponential
        _ ≤ 2 ^ deficit *
            2 ^ ((Nat.log2 object.vertexCount + 1) * slack) :=
          Nat.mul_le_mul_left _ raised
        _ = _ := by rw [← pow_add]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp powers

end FiniteObject

end Hypostructure.Graph
