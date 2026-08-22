import Hypostructure.Graph.Strategy.SpineRows

/-!
# Type B terminals

The closure registrations of the Type B branch (Part VI/VII of the manuscript),
on the live vocabulary.  Node `[74]`/`[82]` — "B2 holds: bridge reduction gives
`N₀(X) ≥ 0` outside route 8", `prop:typeB-bridge-reduction` — closes against
the negative support selected at node `[61]`: the exclusion decision publishes
the exact support-indexed nonnegative-charge conclusion as `K .typeBExcluded`,
and the terminal reads it back together with the negative-support hypothesis
retained by that value.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[74]`/`[82]` closes.**  `prop:typeB-bridge-reduction`: with no
fan-certificate residual centre and the refined B2 ledger, the selected Type B
support has `def⁺(X) − σ(X) ≥ ¼|V(X)|`, i.e. `N₀(X) ≥ 0`, against its selection
as a negative support at node `[61]`.  The exclusion decision commits the
nonnegative theorem; this terminal derives exactly the resulting contradiction. -/
noncomputable instance instImpossibleTypeBExcluded :
    Impossible (Input BranchState Presentation presentation data)
      (K .typeBExcluded) where
  contradiction := fun residual excluded => by
    obtain ⟨_packing, _valid, _maximal, canonicalPiece, _centres, assigned,
      nonnegative⟩ := excluded.down
    have negative : residual.object.NegativeNetCharge canonicalPiece.vertices
        data.threshold data.dischargeScale := by
      rcases assigned with ⟨negative, _, _⟩ | ⟨negative, _, _⟩ <;> exact negative
    exact (residual.object.not_negativeNetCharge_iff canonicalPiece.vertices
      data.threshold data.dischargeScale).mpr nonnegative negative

end Hypostructure.Graph.Strategy.Spine
