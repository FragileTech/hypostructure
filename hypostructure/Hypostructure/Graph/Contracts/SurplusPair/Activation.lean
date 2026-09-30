import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.PrimitiveCarrier
import Hypostructure.Graph.SparsePairLedger
import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.SparseEntropySandwich
import Hypostructure.Graph.CapacityTokenAssignment
import Hypostructure.Graph.SparseUpperEnvelope
import Hypostructure.Graph.ObjectCapacityLedger
import Hypostructure.Graph.Induced

/-!
# Contract lemmas: the sparse-surplus setup `[126]`--`[129]`

`lem:sparse-slack-surplus`, `lem:sparse-excess-port-extraction`,
`lem:sparse-port-activation`, `lem:surviving-active-family` and
`def:baseline-spine-demand`, each stated over a finite object at the
registered baseline with the paper's assumptions as explicit hypotheses.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- Node `[126]`, `lem:sparse-slack-surplus`, cleared of division:
`2m = δn + σ(G)` at the baseline. -/
theorem sparseSlackSurplus_of_baseline
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object) :
    SparseSlackSurplusStatement data object := by
  have handshake : data.threshold * object.vertexCount ≤ 2 * object.edgeCount :=
    Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount object
      data.threshold fun vertex =>
        le_trans atBaseline (object.minDegree_le_degree vertex)
  unfold SparseSlackSurplusStatement Graph.FiniteObject.degreeSurplus
  omega

/-- Node `[127]`, `lem:sparse-excess-port-extraction` with the family half of
`lem:surviving-active-family`: at the baseline with slack vertices pairwise
nonadjacent (node `[10]`), the excess selector has `σ(G)` members and each port
has a centre above the baseline, an endpoint at it, and `δ − 1` shoulders. -/
theorem activeSurplusFamily_of_slackIndependent
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (independent : SlackIndependentStatement data object) :
    ActiveSurplusFamilyStatement data object := by
  have baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    fun vertex => le_trans atBaseline (object.minDegree_le_degree vertex)
  exact ⟨object.card_excessPorts baseline, fun _pair member =>
    ⟨Graph.FiniteObject.centre_high_of_mem_excessPorts member,
      (object.surplusPortOfMem member).endpoint_degree_eq baseline independent,
      (object.surplusPortOfMem member).card_shoulders baseline independent⟩⟩

/-- Node `[128]`, `lem:sparse-port-activation` (a)--(d): at the selected
minimal counterexample, every port with a shoulder pair carries its return
path `R_p`, an open port carries the single-port suppression witness `Q_p`, and
a triangular port carries its triangle. -/
theorem sparsePortActivation_of_selection
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (selection : SelectionStatement BranchState Presentation presentation data
      object)
    (suppressionWitness : SingleOpenPortSuppressionWitnessStatement data object) :
    SparsePortActivationStatement data object :=
  fun _pair member left right shoulders distinct =>
    ⟨(object.surplusPortOfMem member).portReturn_of_minimal
        shoulders atBaseline selection.1 selection.2,
      fun openPort => suppressionWitness
        ((object.surplusPortOfMem member).configuration
          shoulders distinct openPort)
        (object.surplusPortOfMem member).centre_high,
      fun adjacent =>
        (object.surplusPortOfMem member).triangle_of_shoulders_adj
          (shoulders left |>.2 (Or.inl rfl))
          (shoulders right |>.2 (Or.inr rfl)) adjacent⟩

/-- Node `[125]`, `def:active-surplus-demands` with
`lem:surviving-active-family`: at the cubic baseline, the extracted and
activated excess ports carry the canonical port data of every active demand.
Exit-freeness is the separate node-`[125]` survivor fact. -/
theorem activeSurplusDemands_of_activation
    (cubic : data.threshold = 3)
    (family : ActiveSurplusFamilyStatement data object)
    (activation : SparsePortActivationStatement data object) :
    ActiveSurplusDemandsStatement data object :=
  Graph.surviving_active_family family.1
    (by
      classical
      intro pair member
      have cardAt := family.2 pair member |>.2.2
      have cardTwo : (object.surplusPortOfMem member).shoulders.card = 2 := by
        simpa [cubic] using cardAt
      obtain ⟨left, right, distinct, description⟩ := Finset.card_eq_two.mp cardTwo
      refine ⟨left, right, ?_, distinct⟩
      intro vertex
      rw [description]
      simp)
    activation

end Hypostructure.Graph.Contracts.SurplusPair
