import Hypostructure.Graph.ColdCorridor
import Hypostructure.Graph.GConstructedPiece

/-!
# The cold G2 test read on the pieces constructed from G

`lem:cold-bounded-germ-trichotomy` (G2, *hit-distinguished*): "some compatible outside
context distinguishes the two representatives by target truth value".  The context
stays G's own surroundings `G − Z`, and the second representative `E = germ.canonical`
is a piece constructed from G at the germ's support (`GConstructedPiece`).
`DistinguishingAt germ P` is the test at any constructed piece `P`;
`germ.Distinguishing` is the test at `E` (`distinguishing_iff_at`).

* it is exactly the target response of the constructed piece in `G − Z`
  (`distinguishingAt_iff_response`), since `Q[x,y]` glued into `G − Z` is G;
* at a minimal G it holds at every fold of two interior vertices of the support that
  share no neighbour (`distinguishingAt_fold`): G2 is inhabited at every germ whose
  support has such a pair.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.ColdCorridor.BoundedGerm

open Hypostructure
open Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}} {S : DeclaredSignature}
variable {Baseline Target : FiniteObject.{u} → Prop}
variable (germ : BoundedGerm S Baseline Target object)

/-- **G2 at a constructed representative**: `Q[x,y]` and the piece `P` constructed from G
at the germ's support have different target truth in G's own surroundings `G − Z`. -/
def DistinguishingAt (P : GConstructedPiece object germ.support) : Prop :=
  ¬ (Target (glue germ.piece germ.atom.outside) ↔
    Target (glue P.toPiece germ.atom.outside))

/-- G2 at the germ's own second representative is `DistinguishingAt` at `E`. -/
theorem distinguishing_iff_at : germ.Distinguishing ↔ germ.DistinguishingAt germ.canonical :=
  Iff.rfl

/-- **At a target-avoiding G, G2 at a constructed piece is its target response in
`G − Z`.** -/
theorem distinguishingAt_iff_response {LengthOK : Nat → Prop}
    (germ : BoundedGerm S Baseline (HasCycleWithLength LengthOK) object)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (P : GConstructedPiece object germ.support) :
    germ.DistinguishingAt P ↔ P.response LengthOK := by
  have notOwn : ¬ HasCycleWithLength LengthOK (glue germ.piece germ.atom.outside) :=
    fun realizing => avoids (germ.target_of_realizing
      (cycleTargetInterface LengthOK).isomorphismInvariant realizing)
  unfold DistinguishingAt GConstructedPiece.response
  constructor
  · intro distinguishing
    by_contra silent
    exact distinguishing (iff_of_false notOwn silent)
  · intro response same
    exact notOwn (same.mpr response)

/-- **G2 is inhabited by the folds** (Lean improvement): at a minimal target-avoiding G,
the fold of two distinct interior vertices of the germ's support that share no
neighbour distinguishes the two representatives in `G − Z`. -/
theorem distinguishingAt_fold {LengthOK : Nat → Prop} {k : Nat}
    (germ : BoundedGerm S Baseline (HasCycleWithLength LengthOK) object)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (two : 2 ≤ k) (baseline : MinimumDegreeAtLeast k object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast k H → HasCycleWithLength LengthOK H)
    (keep remove : Strategy.InterfaceReplacement.SupportAtom.PieceInternal object
      germ.support)
    (different : keep ≠ remove)
    (noCommon : ∀ common, ¬ object.IsCommonNeighbor keep.1 remove.1 common) :
    germ.DistinguishingAt (GConstructedPiece.fold keep remove different noCommon) :=
  (germ.distinguishingAt_iff_response avoids _).mpr
    (GConstructedPiece.response_fold_of_minimal two baseline minimal keep remove
      different noCommon)

end Hypostructure.Graph.ColdCorridor.BoundedGerm
