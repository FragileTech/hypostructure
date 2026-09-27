import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Certificate

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Nodes `[72]`/`[81]`: B2 disjointness holds?**  The decision reads the
direct-cycle-free fact (`K .typeBDirectCycleFree`) and splits at its Type B
support `X`: the assigned centres of `X` admit a disjoint choice of candidate
entries at `P₀` (`def:typeB-bridge-statements` B2), or, in the positive form of
`lem:typeB-bridge-to-overlap`, `X` carries a minimal overlap obstruction
(`[73]`/`[83]`). -/
noncomputable def b2AssignmentDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .typeBDirectCycleFree) known]
    (choiceFresh : K .typeBB2Choice ∉ known)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known) :
    Decision (K .typeBB2Choice) (K .typeBOverlapObstruction) previous :=
  Decision.run previous (K .typeBB2Choice) (K .typeBOverlapObstruction)
    `Hypostructure.Graph.Strategy.Spine.b2AssignmentDichotomy
    (Classical.choice (show Nonempty
        ((K .typeBB2Choice).At current ⊕ (K .typeBOverlapObstruction).At current) from by
      rcases Contracts.TypeB.b2_split
          (ExactLedger.get previous (K .typeBDirectCycleFree)).down with holds | holds
      · exact ⟨.inl ⟨holds⟩⟩
      · exact ⟨.inr ⟨holds⟩⟩))
    choiceFresh obstructionFresh

/-- **Node `[81]` (degree-four arm): `c ≤ 1`, or `c ≥ 2` with B2 disjoint
ledger?**  The decision reads the direct-cycle-free fact
(`K .typeBDirectCycleFree`) and splits at its Type B support `X`: every assigned
centre has at most one cubic-closed neighbour or the assigned centres admit a B2
disjoint choice (`[82]`), or some centre has `c ≥ 2` and `X` carries a minimal
overlap obstruction (`[83]`). -/
noncomputable def degreeFourLedgerDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .typeBDirectCycleFree) known]
    (ledgerFresh : K .typeBDegreeFourLedger ∉ known)
    (overlapFresh : K .typeBDegreeFourOverlap ∉ known) :
    Decision (K .typeBDegreeFourLedger) (K .typeBDegreeFourOverlap) previous :=
  Decision.run previous (K .typeBDegreeFourLedger) (K .typeBDegreeFourOverlap)
    `Hypostructure.Graph.Strategy.Spine.degreeFourLedgerDichotomy
    (Classical.choice (show Nonempty
        ((K .typeBDegreeFourLedger).At current ⊕
          (K .typeBDegreeFourOverlap).At current) from by
      rcases Contracts.TypeB.degreeFourLedger_split
          (ExactLedger.get previous (K .typeBDirectCycleFree)).down with holds | holds
      · exact ⟨.inl ⟨holds⟩⟩
      · exact ⟨.inr ⟨holds⟩⟩))
    ledgerFresh overlapFresh

end Hypostructure.Graph.Strategy.Spine
