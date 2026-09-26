import Hypostructure.Graph.Strategy.SpineRows.Basic
import Hypostructure.Graph.Contracts.Spine.BranchD

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

/-! ## Node `[35]`: separated testers

`lem:separated-testers`.  Let corresponding internal wedges be centred in
vertex-disjoint isomorphic rooted radius-`r` balls.  If an exact owned
decomposition has those two balls as its piece side, every internal vertex of
its outside context lies in the complement of both balls.  Thus any outside
context distinguishing the represented wedges is supported there.  For an
attempted quotient identifying their labels, excluded middle on context
equivalence gives precisely the paper's concluding alternative: every
identified pair is context-universal, or an identified pair has a concrete
target-defect context.

This is a source-free Type-A row: all objects occur in the proposition and the
proof reads only `inputs.current`.  The row introduces no proof-specific data
carrier and appends its sole output to the literal `ExactLedger`. -/
@[reducible] noncomputable def separatedTestersRow
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
    factOnly `Hypostructure.Graph.Strategy.Spine.separatedTesters
      (sourceFreeManifest (K .separatedTesters))
      (fun inputs =>
        .cons (key := K .separatedTesters)
          ⟨Contracts.Spine.separatedTesters data.toParameters inputs.current.object⟩
          .nil)

end Hypostructure.Graph.Strategy.Spine
