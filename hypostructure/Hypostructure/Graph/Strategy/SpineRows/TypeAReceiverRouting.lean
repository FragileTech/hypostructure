import Hypostructure.Graph.Strategy.SpineRows.Basic

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

/-! ## Node `[88]`: the routing and threshold algebra of a Type A support

`def:typeA-support` is `def:admissible` with `σ(X) = 0`.  Since the object meets
the baseline everywhere, a support of zero assigned surplus has every vertex at
degree exactly `δ`, so its internal degrees never exceed `δ`: the vertices split
into *receivers* of internal degree below `δ` and *full* vertices at `δ`, and
`q(w) = δ − d_X(w)` is also the number of ambient edges leaving `w`.

Two manuscript statements live here.

`lem:typeA-receiver-loads` says the canonical trace `r(u)` is defined for every
full `u` and lands on a receiver.  Its hypothesis is the empty internal
`δ`-core, and that is *inherited*, not assumed: node `[27]` proves that no
subregion of the remainder of a maximal packing meets the baseline, and the
support is such a subregion.  `exists_traceTo_of_no_baseline_subsupport` is the
argument the manuscript gives — the region a full vertex reaches through full
vertices would otherwise keep the whole baseline inside itself.

`lem:typeA-threshold-algebra` says a receiver of internal degree `δ − 1 − j`
has `q(w) = j + 1`, hence saturation threshold `H_j = s·(j+1)`, never above
`s·δ`.  At the manuscript's `δ = 3`, `s = 4` that is `H₀ ≤ 4`, `H₁ ≤ 8`,
`H₂ ≤ 12`.

The support is data and cannot travel, so the fact is stated at every Type A
support of the object at once, exactly as node `[27]` is stated at every
subregion. -/
@[reducible] noncomputable def typeAReceiverRoutingRow
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAReceiverRouting
    (rowManifest (K .remainderNormalized) (K .typeAReceiverRouting)
      (by simp [K_eq_iff]))
    (fun inputs =>
      let normalized := (inputs.get (K .remainderNormalized)).down
      .cons (key := K .typeAReceiverRouting)
        ⟨by
          classical
          intro packing valid maximal piece inside surplus
          -- `σ(X) = 0` against the standing baseline: every vertex of the
          -- support sits exactly at `δ`, so no internal degree exceeds it.
          have capped : ∀ vertex ∈ piece,
              inputs.current.object.internalDegree piece vertex ≤
                data.threshold := by
            intro vertex member
            have exact : inputs.current.object.degree vertex = data.threshold := by
              -- The standing baseline, read off the residual rather than from
              -- a fact.
              have nonneg : data.threshold ≤ inputs.current.object.degree vertex :=
                le_trans inputs.current.baseline
                  (inputs.current.object.minDegree_le_degree vertex)
              have summand :
                  inputs.current.object.degree vertex - data.threshold = 0 :=
                Nat.eq_zero_of_le_zero
                  (surplus ▸ Finset.single_le_sum
                    (f := fun other =>
                      inputs.current.object.degree other - data.threshold)
                    (fun _ _ => Nat.zero_le _) member)
              omega
            exact exact ▸
              inputs.current.object.internalDegree_le_degree piece vertex
          -- Node `[27]` on the support: no subregion of it meets the baseline.
          have noCore : ∀ inner : Finset inputs.current.object.Vertex,
              inner ⊆ piece →
              ¬ Graph.MinimumDegreeAtLeast data.threshold
                (inputs.current.object.induce inner) := fun inner contained =>
            (normalized packing valid maximal inner (contained.trans inside)).2
          refine ⟨fun vertex member full => ?_, fun receiver isReceiver => ?_⟩
          · obtain ⟨target, trace⟩ :=
              inputs.current.object.exists_traceTo_of_no_baseline_subsupport
                piece data.threshold noCore member (le_of_eq full.symm)
            obtain ⟨found, routed⟩ :=
              Option.isSome_iff_exists.mp
                (inputs.current.object.isSome_traceReceiver?_of_traceTo trace)
            exact ⟨found, routed,
              inputs.current.object.isReceiver_of_traceTo
                (inputs.current.object.traceTo_of_traceReceiver?_eq_some routed)⟩
          · exact ⟨inputs.current.object.saturationThreshold_eq piece
              data.threshold data.dischargeScale isReceiver.2,
              inputs.current.object.saturationThreshold_le piece data.threshold
                data.dischargeScale receiver⟩⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
