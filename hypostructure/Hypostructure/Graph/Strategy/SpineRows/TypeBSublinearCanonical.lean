import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.SublinearCanonical
import Hypostructure.Graph.Contracts.TypeB.SublinearGaps
import Hypostructure.Graph.Contracts.TypeB.SublinearFlow
import Hypostructure.Graph.Contracts.TypeB.SublinearLanding

/-! G audit of `TypeBSublinearOutcome`: the failed sublinear hypotheses in G's
canonical form (keys 8300--8302), published on the negative arm of node `[187]`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- G audit: the tested hypotheses are their canonical arms. -/
@[reducible] noncomputable def typeBSublinearCanonicalFormRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBSublinearCanonicalForm
    { Requires := [K .typeBSublinearResidual]
      Produces := [K .typeBSublinearCanonicalForm]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun _ =>
      .cons (key := K .typeBSublinearCanonicalForm)
        ⟨Contracts.TypeB.typeBSublinearCanonicalForm⟩ .nil)

/-- G audit (Lean improvement): the absorbed-core inclusion is decided at G. -/
@[reducible] noncomputable def groupedAbsorbedCoreSubsetRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.groupedAbsorbedCoreSubset
    { Requires := [K .typeBSublinearResidual]
      Produces := [K .groupedAbsorbedCoreSubset]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun _ =>
      .cons (key := K .groupedAbsorbedCoreSubset)
        ⟨Contracts.TypeB.groupedAbsorbedCoreSubset⟩ .nil)

/-- G audit: the grouped centres of G are high. -/
@[reducible] noncomputable def groupedCentresHighRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.groupedCentresHigh
    { Requires := [K .typeBSublinearResidual, K .cubicBaseline]
      Produces := [K .groupedCentresHigh]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .groupedCentresHigh)
        ⟨Contracts.TypeB.groupedCentresHigh
          (data := data.toParameters) (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1⟩ .nil)

/-- G audit: the degree clause of the handoff clauses is empty. -/
@[reducible] noncomputable def handoffDegreeClauseEmptyRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.handoffDegreeClauseEmpty
    { Requires := [K .typeBSublinearResidual]
      Produces := [K .handoffDegreeClauseEmpty]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .handoffDegreeClauseEmpty)
        ⟨Contracts.TypeB.handoffDegreeClauseEmpty
          (data := data.toParameters) (object := inputs.current.object)⟩ .nil)

/-- G audit: canonical routing is total on the pieces of the remainder. -/
@[reducible] noncomputable def pieceRoutingTotalRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pieceRoutingTotal
    { Requires := [K .typeBSublinearResidual, K .remainderNormalized]
      Produces := [K .pieceRoutingTotal]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pieceRoutingTotal)
        ⟨Contracts.TypeB.pieceRoutingTotal
          (data := data.toParameters) (object := inputs.current.object)
          (inputs.get (K .remainderNormalized)).down⟩ .nil)

/-- G audit: the incidence payment of the cover arm. -/
@[reducible] noncomputable def coverPaymentRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coverPayment
    { Requires := [K .typeBSublinearResidual]
      Produces := [K .coverPayment]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coverPayment)
        ⟨Contracts.TypeB.coverPayment
          (data := data.toParameters) (object := inputs.current.object)⟩ .nil)

/-- G audit (gap H05): a load failure is a saturated receiver. -/
@[reducible] noncomputable def loadFailureSaturatedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.loadFailureSaturated
    { Requires := [K .typeBSublinearResidual]
      Produces := [K .loadFailureSaturated]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .loadFailureSaturated)
        ⟨Contracts.TypeB.loadFailureSaturated
          (data := data.toParameters) (object := inputs.current.object)⟩ .nil)

/-- G audit (gaps H06, H07): the Hall violator of the cover network is a window
port. -/
@[reducible] noncomputable def unpaidAbsorbedWindowPortRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.unpaidAbsorbedWindowPort
    { Requires := [K .typeBSublinearResidual, K .cubicBaseline]
      Produces := [K .unpaidAbsorbedWindowPort]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .unpaidAbsorbedWindowPort)
        ⟨Contracts.TypeB.unpaidAbsorbedWindowPort
          (data := data.toParameters) (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (fun vertex => le_trans inputs.current.baseline
            (inputs.current.object.minDegree_le_degree vertex))⟩ .nil)

/-- G audit: receiverPortsAreWindowStubs. -/
@[reducible] noncomputable def receiverPortsAreWindowStubsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.receiverPortsAreWindowStubs
    { Requires := [K .typeBSublinearResidual]
      Produces := [K .receiverPortsAreWindowStubs]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .receiverPortsAreWindowStubs)
        ⟨Contracts.TypeB.receiverPortsAreWindowStubs
          (data := data.toParameters) (object := inputs.current.object)⟩ .nil)

/-- G audit: saturatedReceiverBasin. -/
@[reducible] noncomputable def saturatedReceiverBasinRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.saturatedReceiverBasin
    { Requires := [K .typeBSublinearResidual]
      Produces := [K .saturatedReceiverBasin]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .saturatedReceiverBasin)
        ⟨Contracts.TypeB.saturatedReceiverBasin
          (data := data.toParameters) (object := inputs.current.object)⟩ .nil)

/-- G audit: loadFlowValue. -/
@[reducible] noncomputable def loadFlowValueRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.loadFlowValue
    { Requires := [K .typeBSublinearResidual]
      Produces := [K .loadFlowValue]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .loadFlowValue)
        ⟨Contracts.TypeB.loadFlowValue
          (data := data.toParameters) (object := inputs.current.object)⟩ .nil)

/-- G audit: coverFlowValue. -/
@[reducible] noncomputable def coverFlowValueRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coverFlowValue
    { Requires := [K .typeBSublinearResidual, K .cubicBaseline]
      Produces := [K .coverFlowValue]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coverFlowValue)
        ⟨Contracts.TypeB.coverFlowValue
          (data := data.toParameters) (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1⟩ .nil)

/-- G audit: pieceSizeProfile. -/
@[reducible] noncomputable def pieceSizeProfileRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pieceSizeProfile
    { Requires := [K .typeBSublinearResidual, K .remainderNormalized]
      Produces := [K .pieceSizeProfile]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pieceSizeProfile)
        ⟨Contracts.TypeB.pieceSizeProfile
          (data := data.toParameters) (object := inputs.current.object)
          (inputs.get (K .remainderNormalized)).down⟩ .nil)

/-- G audit: bridgePieceMassDichotomy. -/
@[reducible] noncomputable def bridgePieceMassDichotomyRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.bridgePieceMassDichotomy
    { Requires := [K .typeBSublinearResidual, K .remainderNormalized]
      Produces := [K .bridgePieceMassDichotomy]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .bridgePieceMassDichotomy)
        ⟨Contracts.TypeB.bridgePieceMassDichotomy
          (data := data.toParameters) (object := inputs.current.object)
          (inputs.get (K .remainderNormalized)).down⟩ .nil)

/-- G audit: traceIntoCentreStructure. -/
@[reducible] noncomputable def traceIntoCentreStructureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.traceIntoCentreStructure
    { Requires := [K .typeBSublinearResidual, K .highCentreNormalForm]
      Produces := [K .traceIntoCentreStructure]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .traceIntoCentreStructure)
        ⟨Contracts.TypeB.traceIntoCentreStructure
          (data := data.toParameters) (object := inputs.current.object)
          (inputs.get (K .highCentreNormalForm)).down⟩ .nil)

/-- G audit: traceIntoAbsorbedStructure. -/
@[reducible] noncomputable def traceIntoAbsorbedStructureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.traceIntoAbsorbedStructure
    { Requires := [K .typeBSublinearResidual, K .cubicBaseline]
      Produces := [K .traceIntoAbsorbedStructure]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .traceIntoAbsorbedStructure)
        ⟨Contracts.TypeB.traceIntoAbsorbedStructure
          (data := data.toParameters) (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (fun vertex => le_trans inputs.current.baseline
            (inputs.current.object.minDegree_le_degree vertex))⟩ .nil)

/-- G audit: the exact decomposition of the failed hypotheses. -/
@[reducible] noncomputable def typeBSublinearFailureArmsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBSublinearFailureArms
    { Requires := [K .typeBSublinearResidual, K .cubicBaseline, K .remainderNormalized]
      Produces := [K .typeBSublinearFailureArms]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBSublinearFailureArms)
        ⟨Contracts.TypeB.typeBSublinearFailureArms
          (data := data.toParameters) (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .remainderNormalized)).down
          (inputs.get (K .typeBSublinearResidual)).down⟩ .nil)

end Hypostructure.Graph.Strategy.Spine
