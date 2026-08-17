import Hypostructure.Graph.Strategy.SpineRows

/-!
# Type B terminals

The closure registrations of the Type B branch (Part VI/VII of the manuscript),
on the live vocabulary.  Node `[74]`/`[82]` — "B2 holds: bridge reduction gives
`N₀(X) ≥ 0` outside route 8", `prop:typeB-bridge-reduction` — closes against
the negative support selected at node `[61]`: the exclusion decision of
`[76]`/`[85]` derives the contradiction from the B-ledger charge implication and
commits it as `K .typeBExcluded`, whose statement is that contradiction; the
terminal reads it back.
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
as a negative support at node `[61]`.  The exclusion decision commits exactly
that contradiction. -/
noncomputable instance instImpossibleTypeBExcluded :
    Impossible (Input BranchState Presentation presentation data)
      (K .typeBExcluded) where
  contradiction := fun _residual excluded => excluded.down

end Hypostructure.Graph.Strategy.Spine
