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

/-! ## Nodes `[99]`/`[94]` → `[101]`: the shared saturated exit entry

`lem:typeA-exit4-residual-routing`: *"let `w` be a saturated Type A receiver
with a peeling set `P₄(w)`; if `L₄(w) ≥ 4q(w)`, then the unpeeled routed loads
at `w` realize one of exits (1)--(8)"*.  Figure 8 draws one segment
`[101]`--`[107]` with two entries — node `[99]`'s no arm
(`lem:typeA-unpeeled-visible-routing` after exits `(1)`--`(3)` are denied) and
node `[94]` (`lem:typeA-unpeeled-silent-routing`) — and this hypothesis is what
both commit: the selected saturated receiver at the empty peeling set
(`P₄(w) = ∅`, `L₄(w) = L(w)`, `saturatedAfter_empty`), which is
`def:typeA-exit4-peeling`'s witnessed peeling set trivially.  Each entry row
reads only its own lane's predecessor fact by exact key. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeAVisibleExitEntryRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeAVisibleExitEntry
    { Requires := [K .typeAExitThreeFree]
      Produces := [K .typeASaturatedExitEntry]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeASaturatedExitEntry)
        (show Value BranchState Presentation presentation data
            .typeASaturatedExitEntry inputs.current from ⟨by
          classical
          obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, _package, _labelFree⟩ :=
            (inputs.get (K .typeAExitThreeFree)).down
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          exact ⟨packing, canonical, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, ∅, Finset.empty_subset _,
            (Graph.ExitFour.saturatedAfter_empty piece data.threshold
              data.dischargeScale receiver).mpr saturated,
            Graph.ExitFour.peeledByWitnesses_empty _ piece data.threshold
              data.dischargeScale receiver⟩⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
