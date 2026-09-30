import Hypostructure.Graph.Statements.Parameters

/-!
# Canonical objects of G: the sparse-surplus declared family

The sparse-surplus exits of `def:named-surplus-exits` (tex 2754-2772) are
tested "for any selected surplus demand, any selected pair of surplus demands,
or any baseline spine coordinate used in the entropy sandwich".  Clause (b) is
therefore a statement about **G's own declared coordinates**.  This module
names them as functions of the selected counterexample `G`:

* `canonicalPairActivation data G` -- the canonical pair-response activation
  (`pairResponseActivation`) of the port data of nodes `[127]`/`[128]`
  (`K .activeSurplusDemands`, a proposition, so the activation does not depend
  on any proof);
* `canonicalBaselineSpineFamily data G` -- the `Classical.choose` of node
  `[129]`'s existential (`BaselineSpineDemandStatement`'s spine family, whose
  body is `BaselineSpineFamilySpec`);
* `sparseDeclaredFamily` / `sparseDeclaredSupport` -- the declared sparse
  family: every selected demand `p` with support `T(p) ∪ Γ(p)`, every scheduled
  pair's response coordinate `r_π` with support `X_π`, and every coordinate of
  the canonical spine family;
* `DeclaredSparseSurplusExit` / `DeclaredSparseSurvivor` -- the named exits and
  their negation at that family.

**Design.**  A guarded object is `Option`-valued
(`if h : ∃ x, Spec x then some (Classical.choose h) else none`) with `_spec`,
`_spec_of_eq_some` and `_eq_none_iff`; downstream statements pin it with
`∃ x, obj = some x ∧ Q x`, which is false (never vacuously true) when the
object does not exist.  The declared family is total: when an upstream object
does not exist it contributes no coordinates (a missing spine family declares
no spine coordinate), which makes exits harder, never trivially available.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

noncomputable section

attribute [local instance 10] Classical.propDecidable

/-- A declared coordinate family of `G`: its coordinate type, the finite family
and each coordinate's declared support. -/
structure DeclaredCoordinateFamily (object : Graph.FiniteObject.{u}) :
    Type (u + 1) where
  Coordinate : Type u
  family : Finset Coordinate
  coordinateSupport : Coordinate → Finset object.Vertex

/-- The family with no coordinates. -/
def DeclaredCoordinateFamily.empty (object : Graph.FiniteObject.{u}) :
    DeclaredCoordinateFamily object where
  Coordinate := PEmpty
  family := ∅
  coordinateSupport := fun coordinate => nomatch coordinate

/-- The canonical pair-response activation of `G`. -/
def canonicalPairActivation (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Option (object.DemandActivation object.PairCoordinate
      (object.Vertex × object.Vertex)) :=
  if active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold then
    some (Graph.pairResponseActivation active)
  else none

theorem canonicalPairActivation_eq (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold) :
    canonicalPairActivation data object =
      some (Graph.pairResponseActivation active) := by
  unfold canonicalPairActivation
  rw [dif_pos active]

theorem canonicalPairActivation_eq_none_iff (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    canonicalPairActivation data object = none ↔
      ¬ Graph.ActiveSurplusDemands
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
        data.threshold := by
  unfold canonicalPairActivation
  by_cases h : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold
  · rw [dif_pos h]; exact ⟨(fun e => by cases e), fun n => absurd h n⟩
  · rw [dif_neg h]; exact ⟨fun _ => h, fun _ => rfl⟩

/-- `def:baseline-spine-demand` at node `[129]`, at one declared family. -/
abbrev BaselineSpineFamilySpec (data : Parameters)
    (object : Graph.FiniteObject.{u}) (Coordinate : Type u)
    (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex) : Prop :=
  (∀ declared : Graph.DeclaredQuotient
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object family
      coordinateSupport,
    declared.toRankQuotient.FunctionalOn ↑family →
      declared.toRankQuotient.LabelInjectiveOn ↑family) ∧
    Nonempty (Graph.BaselineCodeRealization object family) ∧
    Graph.cubicBaselineBudget object.vertexCount data.threshold ≤
      2 ^ (family.card + Graph.spineDeficit object.vertexCount
        data.threshold family.card) ∧
    Graph.spineDeficit object.vertexCount data.threshold family.card ≤
      data.surplusScale * object.vertexCount

def canonicalBaselineSpineFamily (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Option (DeclaredCoordinateFamily object) :=
  if h : ∃ (Coordinate : Type u) (family : Finset Coordinate)
      (coordinateSupport : Coordinate → Finset object.Vertex),
      BaselineSpineFamilySpec data object Coordinate family coordinateSupport then
    some ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
      Classical.choose (Classical.choose_spec (Classical.choose_spec h))⟩
  else none

theorem canonicalBaselineSpineFamily_spec_of_eq_some (data : Parameters)
    (object : Graph.FiniteObject.{u}) {spine : DeclaredCoordinateFamily object}
    (selected : canonicalBaselineSpineFamily data object = some spine) :
    BaselineSpineFamilySpec data object spine.Coordinate spine.family
      spine.coordinateSupport := by
  unfold canonicalBaselineSpineFamily at selected
  split at selected
  · next h =>
      cases selected
      exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))
  · cases selected

theorem canonicalBaselineSpineFamily_spec (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (h : ∃ (Coordinate : Type u) (family : Finset Coordinate)
      (coordinateSupport : Coordinate → Finset object.Vertex),
      BaselineSpineFamilySpec data object Coordinate family coordinateSupport) :
    ∃ spine, canonicalBaselineSpineFamily data object = some spine ∧
      BaselineSpineFamilySpec data object spine.Coordinate spine.family
        spine.coordinateSupport := by
  unfold canonicalBaselineSpineFamily
  rw [dif_pos h]
  exact ⟨_, rfl,
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))⟩

theorem canonicalBaselineSpineFamily_eq_none_iff (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    canonicalBaselineSpineFamily data object = none ↔
      ¬ ∃ (Coordinate : Type u) (family : Finset Coordinate)
        (coordinateSupport : Coordinate → Finset object.Vertex),
        BaselineSpineFamilySpec data object Coordinate family coordinateSupport := by
  unfold canonicalBaselineSpineFamily
  by_cases h : ∃ (Coordinate : Type u) (family : Finset Coordinate)
      (coordinateSupport : Coordinate → Finset object.Vertex),
      BaselineSpineFamilySpec data object Coordinate family coordinateSupport
  · rw [dif_pos h]; exact ⟨(fun e => by cases e), fun n => absurd h n⟩
  · rw [dif_neg h]; exact ⟨fun _ => h, fun _ => rfl⟩

/-- The spine coordinates the survival clause reads: the canonical `[129]`
family, or no coordinate when `[129]`'s family does not exist. -/
def canonicalSpineCoordinates (data : Parameters)
    (object : Graph.FiniteObject.{u}) : DeclaredCoordinateFamily object :=
  (canonicalBaselineSpineFamily data object).getD
    (DeclaredCoordinateFamily.empty object)

/-- The declared sparse coordinates. -/
abbrev SparseDeclaredCoordinate (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Type u :=
  (object.Vertex × object.Vertex) ⊕
    (object.PairCoordinate ⊕ (canonicalSpineCoordinates data object).Coordinate)

def sparseDeclaredFamily (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Finset (SparseDeclaredCoordinate data object) := by
  classical
  exact match canonicalPairActivation data object with
    | some activation =>
        (object.excessPorts data.threshold).image Sum.inl ∪
          ((activation.pairFamily (object.portPairSchedule data.threshold)).image
              (Sum.inr ∘ Sum.inl) ∪
            (canonicalSpineCoordinates data object).family.image
              (Sum.inr ∘ Sum.inr))
    | none =>
        (canonicalSpineCoordinates data object).family.image (Sum.inr ∘ Sum.inr)

def sparseDeclaredSupport (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    SparseDeclaredCoordinate data object → Finset object.Vertex := by
  classical
  exact fun coordinate => match coordinate with
    | .inl demand =>
        ((canonicalPairActivation data object).map
          fun activation => activation.declaredSupport demand).getD ∅
    | .inr (.inl pair) => Graph.DeclaredSignature.Coordinate.support pair
    | .inr (.inr spine) =>
        (canonicalSpineCoordinates data object).coordinateSupport spine

theorem pairFamily_subset_sparseDeclaredFamily (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold)
    (coordinate : object.PairCoordinate)
    (member : coordinate ∈ (Graph.pairResponseActivation active).pairFamily
      (object.portPairSchedule data.threshold)) :
    (Sum.inr (Sum.inl coordinate) : SparseDeclaredCoordinate data object) ∈
      sparseDeclaredFamily data object := by
  classical
  unfold sparseDeclaredFamily
  rw [canonicalPairActivation_eq data object active]
  simp only [Finset.mem_union, Finset.mem_image, Function.comp_apply]
  exact Or.inr (Or.inl ⟨coordinate, member, rfl⟩)


/-- **The named sparse surplus exits of G** (`def:named-surplus-exits`), at G's
declared sparse family. -/
abbrev DeclaredSparseSurplusExit (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.SparseSurplusExit (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
    (sparseDeclaredFamily data object) (sparseDeclaredSupport data object)

/-- **G survives the sparse surplus exits** of its declared sparse family. -/
abbrev DeclaredSparseSurvivor (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.SurvivesSparseExits (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
    (sparseDeclaredFamily data object) (sparseDeclaredSupport data object)

end

end Hypostructure.Graph.Strategy.Spine
