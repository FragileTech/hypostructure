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

/-! ## Nodes `[33]` and `[35]`: minimal curvature-dependence support

The rank-drop arm already contains a concrete proper determination.  Following
`lem:curvature-dependence-routing`, this row chooses, for its fixed determined
coordinate, a certificate whose connected declared support is inclusion-minimal.
All candidates are local mathematical objects; the sole proof-data input and
output are the exact-ledger facts named in the manifest.

Part III of the manuscript repeats the Branch-D state of node `[33]` verbatim
at node `[35]`, with the incoming edge labelled `from [33]`.  Hence `[35]`
does not publish a second `branchDependence` fact.  It does, however, carry the
separate labelled fact `lem:separated-testers`; `separatedTestersRow` below
appends exactly that fact before node `[36]` tests the same certificate. -/
@[reducible] noncomputable def branchDependenceRow
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
    factOnly `Hypostructure.Graph.Strategy.Spine.branchDependence
      (rowManifest (K .curvatureRankDrop) (K .branchDependence)
        (by key_fresh))
      (fun inputs =>
        .cons (key := K .branchDependence)
          ⟨Contracts.Spine.branchDependence_of_curvatureRankDrop data.toParameters
            inputs.current.object (inputs.get (K .curvatureRankDrop)).down⟩
          .nil)

end Hypostructure.Graph.Strategy.Spine
