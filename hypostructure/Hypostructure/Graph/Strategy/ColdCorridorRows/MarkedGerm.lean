import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdMarkedGerm

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[157]`: the marked neutral germ against the table's compression clause

`lem:cold-same-interface-table` closes a row that is not handed off by a
strictly smaller proper representative (`def:admissible-rank-quotient`).  Read
at G's marked neutral equal-length germ `(Q, E)`, with `E = Q` (node `[166]`):
the support is a subcubic (F5) candidate, so it is not handed off, and the
replacement `glue E (G − Z)` is isomorphic to G, so it is not strictly smaller.
The compression clause has no witness at the marked germ. -/
@[reducible] noncomputable def coldMarkedGermUncompressedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldMarkedGermUncompressed
    { Requires := [K .coldAbsorbedNeutralConfiguration,
        K .coldCanonicalReplacementTrivial]
      Produces := [K .coldMarkedGermUncompressed]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldMarkedGermUncompressed)
        ⟨Contracts.Spine.coldMarkedGermUncompressed_of_trivial data.toParameters
          inputs.current.object
          (inputs.get (K .coldAbsorbedNeutralConfiguration)).down
          (inputs.get (K .coldCanonicalReplacementTrivial)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
