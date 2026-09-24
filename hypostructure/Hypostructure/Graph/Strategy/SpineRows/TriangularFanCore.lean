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

/-! ## Node `[79]`: the triangular fan core

`def:triangular-fan-core` is the paper's source-normal-form construction at a
heavy centre.  A nonempty selected family of triangular ports determines its
two shoulders at each endpoint, the induced core vertex set, and the four
declared completion-edge classes.  This row reads only the already committed
heavy-centre normal form.  In particular it does not assert that a shoulder
has a completion edge; that is the following manuscript lemma. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def triangularFanCoreRow :
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
    `Hypostructure.Graph.Strategy.Spine.triangularFanCore
    { Requires := [K .highCentreNormalForm]
      Produces := [K .triangularFanCore]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let normal := (inputs.get (K .highCentreNormalForm)).down
      .cons (key := K .triangularFanCore)
        (show Value BranchState Presentation presentation data
            .triangularFanCore inputs.current from
          ⟨by
            change TriangularFanCoreStatement data inputs.current.object
            intro centre centreHeavy ports portsNonempty triangular
            classical
            let shoulders : inputs.current.object.Vertex →
                Finset inputs.current.object.Vertex := fun endpoint =>
              (inputs.current.object.orderedNeighbors endpoint).toFinset.erase centre
            let core : Finset inputs.current.object.Vertex :=
              insert centre (ports ∪ ports.biUnion shoulders)
            let completion : inputs.current.object.Vertex →
                inputs.current.object.Vertex →
                  inputs.current.object.Vertex → Prop :=
              fun endpoint shoulder target =>
                endpoint ∈ ports ∧ shoulder ∈ shoulders endpoint ∧
                  inputs.current.object.graph.Adj shoulder target ∧
                    target ≠ endpoint ∧ target ∉ shoulders endpoint
            let central : inputs.current.object.Vertex →
                inputs.current.object.Vertex →
                  inputs.current.object.Vertex → Prop :=
              fun endpoint shoulder target =>
                completion endpoint shoulder target ∧ target = centre
            let crossTriangular : inputs.current.object.Vertex →
                inputs.current.object.Vertex →
                  inputs.current.object.Vertex → Prop :=
              fun endpoint shoulder target =>
                completion endpoint shoulder target ∧
                  ∃ other ∈ ports,
                    other ≠ endpoint ∧ target ∈ shoulders other
            let outside : inputs.current.object.Vertex →
                inputs.current.object.Vertex →
                  inputs.current.object.Vertex → Prop :=
              fun endpoint shoulder target =>
                completion endpoint shoulder target ∧ target ∉ core ∧
                  ¬ inputs.current.object.graph.Adj centre target
            refine ⟨shoulders, core, completion, central, crossTriangular, outside,
              ?_, ?_, ?_, ?_, ?_, ?_⟩
            · intro endpoint endpointMem
              have triangularMem := triangular endpointMem
              have centreEndpoint :=
                (Graph.mem_triangularEndpoints_iff.mp triangularMem).1
              have centreHigh : Graph.IsHighCentre inputs.current.object
                  data.threshold centre := by
                exact Nat.lt_trans (Nat.lt_succ_self data.threshold) centreHeavy
              have endpointDegree :=
                (normal centre centreHigh).neighbourTight centreEndpoint
              have centreMember : centre ∈
                  (inputs.current.object.orderedNeighbors endpoint).toFinset := by
                simpa [inputs.current.object.mem_orderedNeighbors_iff] using
                  centreEndpoint.symm
              have neighbourCard :
                  (inputs.current.object.orderedNeighbors endpoint).toFinset.card =
                    inputs.current.object.degree endpoint := by
                rw [List.toFinset_card_of_nodup
                  (inputs.current.object.orderedNeighbors_nodup endpoint),
                  inputs.current.object.orderedNeighbors_length endpoint]
              refine ⟨?_, ?_, ?_⟩
              · intro vertex
                simp [shoulders, Graph.IsShoulder,
                  inputs.current.object.mem_orderedNeighbors_iff, and_comm]
              · rw [show shoulders endpoint =
                    (inputs.current.object.orderedNeighbors endpoint).toFinset.erase
                      centre from rfl,
                  Finset.card_erase_of_mem centreMember, neighbourCard,
                  endpointDegree, data.threshold_eq_three]
              · obtain ⟨left, right, leftShoulder, rightShoulder, chord⟩ :=
                  (Graph.mem_triangularEndpoints_iff.mp triangularMem).2
                refine ⟨left, right, ?_, ?_, chord.ne, chord⟩
                · simpa [shoulders, Graph.IsShoulder,
                    inputs.current.object.mem_orderedNeighbors_iff, and_comm] using
                    leftShoulder
                · simpa [shoulders, Graph.IsShoulder,
                    inputs.current.object.mem_orderedNeighbors_iff, and_comm] using
                    rightShoulder
            · intro vertex
              simp [core]
            · intro endpoint shoulder target
              rfl
            · intro endpoint shoulder target
              rfl
            · intro endpoint shoulder target
              rfl
            · intro endpoint shoulder target
              rfl⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
