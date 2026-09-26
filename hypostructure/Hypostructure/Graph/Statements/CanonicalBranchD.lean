import Hypostructure.Graph.Statements.CanonicalTypeA

/-!
# Canonical objects: the Branch D determination certificate

Proof-agnostic canonical objects of the selected residual `G` for Branch D
(nodes `[19]`, `[21]`/`[33]`/`[35]`, `[24]`--`[29]`;
`lem:curvature-dependence-routing`, `lem:target-rank-circuit`,
`lem:full-rank`, tex ~9160--9368).  This module imports no strategy, row or
vocabulary module.

## Design (shared by every `Statements/Canonical*` module)

A fact value is data-free (`FactSystem.value_subsingleton`), so an object that
an upstream key only asserts with `∃` is named downstream as a canonical
function of `G`: `Classical.choose` of *that upstream statement's* `∃`-body at
`G`.  A guarded object is `Option`-valued,

  `if h : ∃ x, Spec data G x then some (Classical.choose h) else none`,

with `_spec` (existence gives `some x` with `Spec x`), `_spec_of_eq_some` and
`_eq_none_iff`.  A downstream statement pins the object as
`∃ x, obj data G = some x ∧ Q x`; when the upstream existence fails this is
false, never vacuously true, and the complementary arm
`∃ x, obj data G = some x ∧ ¬ Q x` is its exact complement under the upstream
fact.  No statement ever quantifies over "all `x` with `obj = some x`".

## The objects

* `curvatureRankDropTest?` — the determined test of node `[19]`
  (`CurvatureRankDropStatement`), at the canonical packing its statement pins.
* `branchCertificate?` — node `[21]`'s inclusion-minimal determination
  certificate (`BranchDependenceStatement`), with its packing pinned to
  `canonicalWindowPacking` (node `[19]`'s packing) and its determined test pinned
  to `curvatureRankDropTest?`.  This is exactly the witness the pre-refactor
  row `branchDependenceRow` (d2ded0e `SpineRows/BranchDependence.lean`) built:
  it `rcases`ed node `[19]`'s witness, kept its `packing` and `test`, and chose
  the minimal certificate for that test; `contextValidityDichotomy` (d2ded0e
  `SpineRows/ContextValidityDichotomy.lean`) then split on the nested
  `Classical.choose` of that same fact.  Nodes `[24]`--`[29]` read its
  `quotient` and `quotient.support`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- The `∃ test`-body of node `[19]` (`CurvatureRankDropStatement`, tex ~9368
`lem:full-rank`, rank-drop arm) at the canonical packing it pins. -/
def CurvatureRankDropTestSpec (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (test : object.InternalWedge (canonicalRemainder data object)) : Prop :=
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let family := object.internalWedgeFamily support
  object.IsWindowPacking data.windowOrder packing ∧
    packing.card = object.windowPackingNumber data.windowOrder ∧
    remainderCurvatureTargetRank data object packing <
        remainderWedgeSupply object packing ∧
    test ∈ family ∧
      ∃ determiners : Set (object.InternalWedge support),
        determiners ⊆ ↑family ∧ determiners.Finite ∧
          test ∉ determiners ∧
            ∃ declared : Graph.DeclaredQuotient
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object family
              (Graph.FiniteObject.internalWedgeSupport
                (region := support)),
              declared.toRankQuotient.FunctionalOn ↑family ∧
                declared.toRankQuotient.RankReducingOn ↑family ∧
                  declared.toRankQuotient.Determines test determiners

/-- Node `[19]` is literally the existence of its canonical-packing test. -/
theorem curvatureRankDrop_iff_exists_testSpec (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    CurvatureRankDropStatement data object ↔
      ∃ test, CurvatureRankDropTestSpec data object test := by
  constructor
  · rintro ⟨packing, rfl, valid, card, drop, test, member, rest⟩
    exact ⟨test, valid, card, drop, member, rest⟩
  · rintro ⟨test, valid, card, drop, member, rest⟩
    exact ⟨_, rfl, valid, card, drop, test, member, rest⟩

/-- **The determined test of node `[19]`**: `Classical.choose` of node
`[19]`'s `∃ test` at the canonical packing. -/
noncomputable def curvatureRankDropTest? (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Option (object.InternalWedge (canonicalRemainder data object)) := by
  classical
  exact if h : ∃ test, CurvatureRankDropTestSpec data object test then
    some (Classical.choose h) else none

theorem curvatureRankDropTest?_spec (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (h : ∃ test, CurvatureRankDropTestSpec data object test) :
    ∃ test, curvatureRankDropTest? data object = some test ∧
      CurvatureRankDropTestSpec data object test := by
  classical
  refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
  simp [curvatureRankDropTest?, h]

theorem curvatureRankDropTest?_spec_of_eq_some (data : Parameters)
    (object : Graph.FiniteObject.{u})
    {test : object.InternalWedge (canonicalRemainder data object)}
    (eq : curvatureRankDropTest? data object = some test) :
    CurvatureRankDropTestSpec data object test := by
  classical
  unfold curvatureRankDropTest? at eq
  split at eq
  · next h =>
      cases eq
      exact Classical.choose_spec h
  · cases eq

theorem curvatureRankDropTest?_eq_none_iff (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    curvatureRankDropTest? data object = none ↔
      ¬ ∃ test, CurvatureRankDropTestSpec data object test := by
  classical
  unfold curvatureRankDropTest?
  split <;> simp_all

/-- The data of one determination certificate at the canonical packing
(`def:curvature-target-dependence`'s tuple `(X, T, q, 𝒫)` with its determined
test). -/
structure BranchCertificateData (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Type (u + 2) where
  test : object.InternalWedge (canonicalRemainder data object)
  determiners : Set (object.InternalWedge (canonicalRemainder data object))
  quotient : remainderQuotient data object (canonicalWindowPacking data object)
  supportData : Finset (object.InternalWedge (canonicalRemainder data object))

/-- The `∃`-body of node `[21]` (`BranchDependenceStatement`) at the canonical
packing, for the test node `[19]` fixed: a determination certificate with
inclusion-minimal connected support among certificates of the same test
(`lem:curvature-dependence-routing`, tex ~9204). -/
def BranchCertificateSpec (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (certificate : BranchCertificateData data object) : Prop :=
  let packing := canonicalWindowPacking data object
  curvatureRankDropTest? data object = some certificate.test ∧
    object.IsWindowPacking data.windowOrder packing ∧
    packing.card = object.windowPackingNumber data.windowOrder ∧
    remainderCurvatureTargetRank data object packing <
        remainderWedgeSupply object packing ∧
    DeterminationCertificate data object packing certificate.test
        certificate.determiners certificate.quotient certificate.supportData ∧
      ∀ smaller : Finset object.Vertex,
        smaller ⊂ certificate.quotient.support →
          ∀ narrower : remainderQuotient data object packing,
            narrower.support = smaller →
              ∀ narrowerDeterminers narrowerSupportData,
                ¬ DeterminationCertificate data object packing certificate.test
                  narrowerDeterminers narrower narrowerSupportData

/-- **The Branch D certificate**: `Classical.choose` of node `[21]`'s
certificate at the canonical packing and node `[19]`'s test. -/
noncomputable def branchCertificate? (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Option (BranchCertificateData data object) := by
  classical
  exact if h : ∃ certificate, BranchCertificateSpec data object certificate then
    some (Classical.choose h) else none

theorem branchCertificate?_spec (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (h : ∃ certificate, BranchCertificateSpec data object certificate) :
    ∃ certificate, branchCertificate? data object = some certificate ∧
      BranchCertificateSpec data object certificate := by
  classical
  refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
  simp [branchCertificate?, h]

theorem branchCertificate?_spec_of_eq_some (data : Parameters)
    (object : Graph.FiniteObject.{u})
    {certificate : BranchCertificateData data object}
    (eq : branchCertificate? data object = some certificate) :
    BranchCertificateSpec data object certificate := by
  classical
  unfold branchCertificate? at eq
  split at eq
  · next h =>
      cases eq
      exact Classical.choose_spec h
  · cases eq

theorem branchCertificate?_eq_none_iff (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    branchCertificate? data object = none ↔
      ¬ ∃ certificate, BranchCertificateSpec data object certificate := by
  classical
  unfold branchCertificate?
  split <;> simp_all

/-- A canonical certificate is a witness of node `[21]` (at the canonical
packing), so the pinned object is the one `BranchDependenceStatement`
asserts. -/
theorem branchDependence_of_branchCertificateSpec (data : Parameters)
    (object : Graph.FiniteObject.{u})
    {certificate : BranchCertificateData data object}
    (spec : BranchCertificateSpec data object certificate) :
    BranchDependenceStatement data object := by
  obtain ⟨_, valid, card, drop, certified, minimal⟩ := spec
  exact ⟨_, valid, card, drop, certificate.test, certificate.determiners,
    certificate.quotient, certificate.supportData, certified, minimal⟩

/-- The connected determination support `Z` of the canonical certificate,
read by nodes `[24]`--`[28]` (`quotient.support`). -/
noncomputable def branchCertificateSupport? (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Option (Finset object.Vertex) :=
  (branchCertificate? data object).map fun certificate =>
    certificate.quotient.support

end Hypostructure.Graph.Strategy.Spine
