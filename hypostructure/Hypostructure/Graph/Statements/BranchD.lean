import Hypostructure.Graph.Statements.CanonicalBranchD
import Hypostructure.Graph.RepairNetwork

/-!
# Branch D statements at the one certificate of `G`, nodes `[33]`--`[46]`

Every Branch D fact is about the selected residual `G` and about the one
determination certificate node `[21]` fixes on it: `branchCertificate? data G`
(`CanonicalBranchD`), the inclusion-minimal certificate at the canonical packing
`P₀` for node `[19]`'s determined test.  Each statement pins it in the positive
form `∃ c, branchCertificate? data G = some c ∧ Q c`; the certificate's packing,
test, determiners and minimality are node `[21]`'s ledger fact and are not
copied.  The decisions `[36]`, `[38]`, `[41]` split on a predicate of that one
`c`, so their two arms are exact complements about the same certificate.

This module imports no strategy, row or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- Nodes `[33]` and `[35]` (`lem:curvature-dependence-routing`, tex 9204:
"choose a determination certificate with inclusion-minimal connected
support"): at the canonical packing `P₀`, node `[19]`'s determined test has a
determination certificate whose connected support is inclusion-minimal among
certificates of that test.  This is the `∃`-body `branchCertificate?`
chooses. -/
noncomputable abbrev BranchDependenceStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ certificate, BranchCertificateSpec data object certificate

/-- The determination a certificate makes is valid in every context of G
(`lem:context-universality`, tex 6106, stated about G): every two readings of G
at the certificate's support `Z` that it identifies have the same
power-of-two-cycle response in G's own rest `G − Z`
(`ActualContext.actualGlue`). -/
def CertificateContextUniversal (data : Parameters)
    {object : Graph.FiniteObject.{u}}
    (certificate : BranchCertificateData data object) : Prop :=
  ∀ left right : Finset object.Vertex,
    Identified certificate.quotient left right →
      (Graph.HasCycleWithLength data.LengthOK
          (Graph.ActualContext.actualGlue object certificate.quotient.support left) ↔
        Graph.HasCycleWithLength data.LengthOK
          (Graph.ActualContext.actualGlue object certificate.quotient.support right))

/-- Node `[36]`, yes arm: the certificate of `G` is valid in every context of
G.  This is the arm G takes: the test is decided at G (node `[12]`). -/
noncomputable abbrev ContextUniversalStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ certificate, branchCertificate? data object = some certificate ∧
    CertificateContextUniversal data certificate

/-- Node `[36]`, no arm — the terminal `[37]` (case (i) of
`lem:curvature-dependence-routing`, tex 9220), stated about G: the exact
complement at the same certificate — some two readings of G at its support `Z`
that it identifies are separated by G's own rest `G − Z`.  **Empty at G**
(Lean improvement: `[36]`'s defect arm is empty at G): no reading of G closes a
power-of-two cycle in `G − Z` (node `[12]`), so the terminal `[37]` closes
against node `[12]`. -/
noncomputable abbrev ContextDefectStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ certificate, branchCertificate? data object = some certificate ∧
    ∃ left right : Finset object.Vertex,
      Identified certificate.quotient left right ∧
        ¬ (Graph.HasCycleWithLength data.LengthOK
            (Graph.ActualContext.actualGlue object certificate.quotient.support left) ↔
          Graph.HasCycleWithLength data.LengthOK
            (Graph.ActualContext.actualGlue object certificate.quotient.support right))

/-- Node `[38]`, yes arm — the terminal `[39]` (case (ii), tex 9224): the
certificate's support lies in the proper atom `C = R(P₀)`, so its rank-reducing
target-complete quotient has a strictly smaller proper representative: a
replacement `X'` of the support (G's boundary-degree profile, the baseline and
no power-of-two cycle in `glue X' (G − Z)`, strictly smaller). -/
noncomputable abbrev AtomCompressionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ certificate, branchCertificate? data object = some certificate ∧
    certificate.quotient.support ⊆ canonicalRemainder data object ∧
      Graph.Strategy.InterfaceReplacement.ReplacementSupport
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object
        certificate.quotient.support

/-- Node `[40]` (case (iii)'s entry, tex 9228): the certificate's support
reaches outside `C = R(P₀)`, so the connected support it needs strictly
enlarges `C`. -/
noncomputable abbrev DelocalizedSupportStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ certificate, branchCertificate? data object = some certificate ∧
    ¬ certificate.quotient.support ⊆ canonicalRemainder data object ∧
      canonicalRemainder data object ⊂
        delocalizationSupport data object (canonicalWindowPacking data object)
          certificate.quotient

/-- Node `[41]`, yes arm — the terminal `[42]` (`lem:proper-smearing`,
tex 9264): the certificate's support `Z` is proper in `G`, so its rank
reduction yields a strictly smaller proper representative of `Z`: a
replacement `X'` with G's boundary-degree profile at `Z`, the baseline and no
power-of-two cycle in `glue X' (G − Z)`. -/
noncomputable abbrev ProperDelocalizationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ certificate, branchCertificate? data object = some certificate ∧
    (∃ vertex, vertex ∉ certificate.quotient.support) ∧
      Graph.Strategy.InterfaceReplacement.ReplacementSupport
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object
        certificate.quotient.support

/-- Node `[43]`: the certificate's support is the whole graph, `Z = G`. -/
noncomputable abbrev GlobalDelocalizationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ certificate, branchCertificate? data object = some certificate ∧
    ∀ vertex, vertex ∈ certificate.quotient.support

/-- The original coordinate supports of the dependence
(`def:repair-network-terms`, tex 9280): the declared supports of the determined
test, of its determiners and of the certificate's declared support data. -/
noncomputable def certificateCoordinateSupport {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (certificate : BranchCertificateData data object) :
    Finset object.Vertex := by
  classical
  exact object.vertexFinset.filter fun vertex =>
    ∃ test, (test = certificate.test ∨ test ∈ certificate.determiners ∨
        test ∈ certificate.supportData) ∧
      vertex ∈ Graph.FiniteObject.internalWedgeSupport test

/-- What remains of the certificate's support `Z` after deleting the original
coordinate supports; its connected components, each with one boundary leaf per
edge leaving it (`Graph.RepairNetwork.network`), are the *delayed compensation
components* of `def:repair-network-terms`. -/
noncomputable def delayedCompensationRegion {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (certificate : BranchCertificateData data object) :
    Finset object.Vertex := by
  classical
  exact certificate.quotient.support \ certificateCoordinateSupport certificate

/-- Node `[44]`, `lem:smearing-support-repair` (tex 9297): every delayed
compensation component of the certificate's support satisfies
`s = p − 2 + 2β − σ`. -/
noncomputable abbrev RepairIdentityStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ certificate, branchCertificate? data object = some certificate ∧
    ∀ component : Graph.RepairNetwork.RegionComponent
        (delayedCompensationRegion certificate),
      Graph.RepairNetwork.RepairIdentity
        (delayedCompensationRegion certificate) component

/-- Node `[45]`, `lem:no-silent-global-smearing` (tex 9323): the certificate's
quotient `q` is a whole-graph (`Z = G`) quotient that is not label-injective on
`𝒲₂(R₀)`, and the strictly smaller admissible closed representative of that
`q` -- the closed clause of `def:admissible-rank-quotient` (tex 6035-6040) read
at this certificate's support and rank reduction -- exists: a strictly smaller
baseline graph `H` with `profile_∅(H) ⊆ profile_∅(G) = ∅`, i.e. with no
power-of-two cycle. -/
noncomputable abbrev GlobalBarrierStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ certificate, branchCertificate? data object = some certificate ∧
    (∀ vertex, vertex ∈ certificate.quotient.support) ∧
    ¬ Set.InjOn certificate.quotient.label
      ↑(remainderCurvatureTests object (canonicalWindowPacking data object)) ∧
    ∃ representative : Graph.FiniteObject.{u},
      representative.LexicographicallySmaller object ∧
        Graph.MinimumDegreeAtLeast data.threshold representative ∧
          ¬ Graph.HasCycleWithLength data.LengthOK representative

end Hypostructure.Graph.Strategy.Spine
