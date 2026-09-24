import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[70]`: the certificate-marked fan-degree cap

`lem:fan-certificate`, and `rem:fan-finite` as the observation about it.  A
fan-certificate labelling sends the neighbours of a high centre to legal window
labels that are pairwise `C₂`-compatible; the manuscript proves that such a
family has size at most `α(D) = 2 + 2 + 2 + 2 = 8`, so a certificate-marked fan
has `d_G(h) ≤ 8`.

Nothing here writes `8`.  `D` is `ForbiddenGap 2` read as a relation on the
window's own coordinates -- the differences whose wedge `u — h — v` closes an
accepted cycle of length `4 + d` -- and the bound is
`Graph.WindowCurvature.fanPackingCap`, its independence number, computed from
the registered window order and the registered target.  `rem:fan-finite` is
exactly the claim that this is a structural consequence of the label algebra
rather than a free parameter, and that is what the derivation makes true.

The label-algebra inequality is universal in the labelling, but the paper's
node is not an object-wide assertion detached from the active branch.  The row
therefore reads `K .typeBFanEntry`, retains its packing, canonical piece and
assigned centres verbatim, and publishes the conditional cap on exactly that
support. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def fanCertificateCapRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.fanCertificateCap
    { Requires := [K .typeBFanEntry]
      Produces := [K .fanCertificateCap]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let entry := (inputs.get (K .typeBFanEntry)).down
      .cons (key := K .fanCertificateCap)
        (show Value BranchState Presentation presentation data
            .fanCertificateCap inputs.current from
          ⟨by
            change TypeBFanCertificateCapStatement data inputs.current.object
            unfold TypeBFanCertificateCapStatement
            rcases entry with canonical | absorbed | sameToken
            · apply Or.inl
              obtain ⟨packing, valid, maximal, component, present, centres,
                assigned, _nonempty, _high⟩ := canonical
              exact ⟨packing, valid, maximal, component, present, centres,
                assigned, fun _centre _member marking =>
                  marking.degree_le_fanPackingCap⟩
            · apply Or.inr
              apply Or.inl
              refine ⟨absorbed, ?_⟩
              intro germ centre witness marking
              exact marking.degree_le_fanPackingCap
            · apply Or.inr
              apply Or.inr
              obtain ⟨packing, valid, maximal, core, envelope, coreEq, nonempty⟩ :=
                sameToken
              exact ⟨packing, valid, maximal, core, envelope, coreEq, nonempty,
                fun _centre _member marking =>
                  marking.degree_le_fanPackingCap⟩⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
