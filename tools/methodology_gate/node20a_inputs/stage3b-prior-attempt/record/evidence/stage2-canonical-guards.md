```lean

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
```

```lean
inductive SparseSurplusExit (Baseline Target : FiniteObject.{u} → Prop)
    (LengthOK : Nat → Prop) (object : FiniteObject.{u}) {Coordinate : Type w}
    (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex) : Prop
  /-- (a) a direct dyadic contradiction: an accepted cycle. -/
  | dyadic (cycle : Graph.HasCycleWithLength LengthOK object)
  /-- (b) a target-defective quotient, as `lem:context-universality` defines
  it, among the family's own coordinates read on G's own pieces. -/
  | targetDefect
      (defect : ResidualTargetDefect Target object family coordinateSupport)
  /-- (c) a nontrivial target-complete compression of a proper atom, recorded
  at the one-way `ReplacementSupport` strength used by `lem:replacement`. -/
  | compression (support : Finset object.Vertex)
      (replacement : ReplacementSupport Baseline Target object support)
  /-- (d) a proper or global delocalization coordinate: a strictly smaller
  representative meeting the baseline whose target transfers back. -/
  | delocalization (representative : FiniteObject.{u})
      (smaller : representative.LexicographicallySmaller object)
      (baseline : Baseline representative)
      (transfer : Target representative → Target object)
  /-- (e) an open-port suppression cycle whose chord set violates the arithmetic
  conclusion of `lem:suppressed-family-critical-cycle`: the lifted length
  `2^j + |𝒮|` is accepted, where that lemma concludes it is not. -/
  | suppressionChord (tvs : TightVertexSuppression.CompatibleFamily object)
      (certificate : Graph.CycleCertificate tvs.suppressed LengthOK)
      (violates : LengthOK (certificate.walk.length +
        (tvs.usedChords certificate.walk).card))

/-- **A graph survives the sparse surplus exits** of its declared family when
```