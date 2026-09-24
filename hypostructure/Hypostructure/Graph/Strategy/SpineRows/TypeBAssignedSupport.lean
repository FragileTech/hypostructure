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

/-! ## Node `[69]`: the heavy-centre local dichotomy

`cor:heavy-center-local-dichotomy`.  At a heavy centre `h` -- degree at least
two above the baseline, `d_G(h) ≥ 5` at the manuscript's `δ = 3` -- either two
open ports at `h` are fan-compatible in the sense of
`def:fan-compatible-open-ports`, or at least `d_G(h) − 2` ports at `h` are
triangular, and in particular three are.

The manuscript's argument is `Graph.heavyCentreLocalDichotomy`: the open
endpoints are pairwise adjacent, because a nonadjacent pair would be
fan-compatible by `lem:same-center-open-port-compatibility`; part (b) of the
normal form makes `G[N_G(h)]` a matching, which has no clique of size three, so
at most two endpoints are open; and every remaining port is triangular.  The
"in particular three" is `Graph.three_le_triangularEndpoints_card`, the only
place the *heaviness* of the centre is spent, and it spends it exactly as the
manuscript does: `k − 2 ≥ 3`.

The first atomic row below reads the normal form and publishes
`lem:same-center-open-port-compatibility`.  The second reads that registered
fact together with the same normal form and selected heavy support; the latter
fixes the carrier on which the corollary is published. -/

/-! ## Nodes `[64]`--`[65]`, `[68]`, `[69]` on the common Type B fan entry

Node `[62]`'s yes arm enters `[64]` with an admissible support `X` carrying
assigned surplus (`K .typeBHighSurplus`).  `def:canonical-decomp` assigns every
surplus unit `d_G(h) − 3` of a high centre `h ∈ V_{≥4}(G) ∩ V(R)` to the piece
containing `h`, so `σ(X) = Σ_{h ∈ X}(d_G(h) − δ)` and `σ(X) > 0` says `X` has a
high centre: node `[65]`'s *assigned support* is `X` with its own high centres as
fan centres, each with the canonical fan `N_G(h)` used by the ordinary Type B
calculation.  This lane invents no handoff arms; the decorated envelope data
belong only to the `[66]` input from Type A exit `(7)`.  Node `[67]` is
`lem:heavy-neighbourhood-normal-form`
(`highCentreNormalFormRow`, stated of the object).  Node `[68]` asks whether some
assigned fan centre is heavy — degree above the high-centre degree `δ + 1` — and
`[69]` is `cor:heavy-center-local-dichotomy` at every heavy fan centre.  The
ordinary entry and the decorated exit-`(7)` handoff both publish
`K .typeBFanEntry`, so the degree split below is the single manuscript decision
on their common assigned-centre support. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBAssignedSupportRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBAssignedSupport
    { Requires := [K .typeBHighSurplus]
      Produces := [K .typeBAssignedSupport, K .typeBFanEntry]
      requiresUnique := by simp
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let typeB := (inputs.get (K .typeBHighSurplus)).down
      -- `σ(X) = Σ_{v ∈ X}(d_G(v) − δ) > 0` forces a vertex above the baseline:
      -- otherwise every summand is zero.
      let highCentre : ∀ packing component,
          inputs.current.object.IsWindowPacking data.windowOrder packing →
          0 < inputs.current.object.ambientSurplus
            (inputs.current.object.pieceSupport
              (inputs.current.object.remainderSupport packing) component)
            data.threshold →
          ∃ centre ∈ inputs.current.object.pieceSupport
              (inputs.current.object.remainderSupport packing) component,
            Graph.IsHighCentre inputs.current.object data.threshold centre := by
        intro packing component _valid positive
        classical
        by_contra none
        push Not at none
        have zero : inputs.current.object.ambientSurplus
            (inputs.current.object.pieceSupport
              (inputs.current.object.remainderSupport packing) component)
            data.threshold = 0 := by
          unfold Graph.FiniteObject.ambientSurplus
          refine Finset.sum_eq_zero fun vertex member => ?_
          have := none vertex member
          simp only [Graph.IsHighCentre, not_lt] at this
          omega
        omega
      .cons (key := K .typeBAssignedSupport)
        (show Value BranchState Presentation presentation data
            .typeBAssignedSupport inputs.current from
          ⟨by
            obtain ⟨packing, valid, maximal, component, present, charge, positive⟩ :=
              typeB
            exact ⟨packing, valid, maximal, component, present, charge, positive,
              highCentre packing component valid positive⟩⟩)
        (.cons (key := K .typeBFanEntry)
          (show Value BranchState Presentation presentation data
              .typeBFanEntry inputs.current from
            ⟨by
              classical
              apply Or.inl
              obtain ⟨packing, valid, maximal, component, present, charge, positive⟩ :=
                typeB
              obtain ⟨centre, member, high⟩ := highCentre packing component valid positive
              refine ⟨packing, valid, maximal, component, present,
                Graph.TypeBRefinedSupport.centres inputs.current.object data.threshold
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport packing) component),
                Or.inl ⟨charge, positive, rfl⟩, ?_, ?_⟩
              · exact ⟨centre, Graph.TypeBRefinedSupport.mem_centres.2 ⟨member, high⟩⟩
              · intro vertex vertexMem
                exact (Graph.TypeBRefinedSupport.mem_centres.1 vertexMem).2⟩)
          .nil))
    0 0

end Hypostructure.Graph.Strategy.Spine
