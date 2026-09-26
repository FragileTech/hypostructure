import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- The concrete sparse-exit route supplied by (F2). -/
theorem coldFailureDefectRoutes
    (data : Data.{u}) (object : Graph.FiniteObject.{u}) :
    ColdFailureDefectRoutesStatement data.toParameters object := by
      intro windows component corridor presentation index left right
      intro failure
      classical
      let support := corridor.prefixSupport right.1
      let reduced :=
        Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece
          object support (corridor.prefixSupport left.1)
      let full :=
        Graph.Strategy.InterfaceReplacement.SupportAtom.piece object support
      let family : Finset (ULift.{u} (Fin 2)) := Finset.univ
      let coordinateSupport : ULift.{u} (Fin 2) →
          Finset object.Vertex := fun _ => ∅
      let attempt : Graph.AttemptedQuotient
          (Coordinate := ULift.{u} (Fin 2))
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK)
          object family coordinateSupport :=
        { support := support
          connected := corridor.prefixSupport_connectedOn right.1
          carries := by
            intro coordinate member vertex vertexMember
            simp [coordinateSupport] at vertexMember
          Label := ULift.{u + 1} Unit
          Value := ULift.{u + 1} Unit
          label := fun _ => ULift.up ()
          value := fun _ _ => ULift.up ()
          properRepresentative := by
            intro _proper _reducing complete
            exfalso
            obtain ⟨outside, separates⟩ := failure.2
            apply separates
            exact (complete reduced full
              (by intro coordinate member; rfl)).2 outside
          closedRepresentative := by
            intro _closed _reducing complete
            exfalso
            obtain ⟨outside, separates⟩ := failure.2
            apply separates
            exact (complete reduced full
              (by intro coordinate member; rfl)).2 outside }
      have reducing : ¬ Set.InjOn attempt.label ↑family := by
        intro injective
        have equal : ULift.up (0 : Fin 2) = ULift.up 1 :=
          injective (by simp [family]) (by simp [family]) rfl
        have downEqual : (0 : Fin 2) = 1 := congrArg ULift.down equal
        omega
      have identified : attempt.Identifies reduced full := by
        intro coordinate member
        rfl
      exact .targetDefect family coordinateSupport attempt reducing
        reduced full identified failure.2

/-- The F2-free context-equivalence conclusion on the same two prefixes. -/
theorem coldFailureDefectEquivalent
    (data : Data.{u}) (object : Graph.FiniteObject.{u}) :
    ColdFailureDefectEquivalentStatement data.toParameters object := by
      intro windows component corridor presentation index left right
        excluded same
      classical
      intro outside
      by_contra distinguishes
      exact excluded ⟨same, ⟨outside, distinguishes⟩⟩

/-- The complete local content of (F2), assembled from the two sealed fields
before it is packaged in the dependent exact-ledger output. -/
theorem coldFailureDefectFact
    (data : Data.{u}) (object : Graph.FiniteObject.{u}) :
    ColdFailureDefectStatement data.toParameters object :=
  { routes := coldFailureDefectRoutes data object
    equivalent := coldFailureDefectEquivalent data object }

set_option maxHeartbeats 1600000 in
/-- Node `[153]`, (F2): register the concrete sparse-exit route and the
F2-free context equivalence on the current object. -/
@[reducible] noncomputable def coldFailureDefectRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureDefect
    { Requires := []
      Produces := [K .coldFailureDefect, K .coldFailureDefectRoute]
      requiresUnique := by simp
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      let failureDefect := coldFailureDefectFact data inputs.current.object
      .cons (key := K .coldFailureDefect) ⟨failureDefect⟩
        (.cons (key := K .coldFailureDefectRoute)
          ⟨coldFailureDefectRoutes data inputs.current.object⟩ .nil))

/-- Node `[153]`, (F1): the selected residual contains no target cycle. -/
@[reducible] noncomputable def coldFailureCycleRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureCycle
    { Requires := [K .selection]
      Produces := [K .coldFailureCycle]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selected := (inputs.get (K .selection)).down
      .cons (key := K .coldFailureCycle)
        ⟨by
          intro windows component corridor order window segment failure
          exact selected.1
            (Graph.ColdCorridor.Corridor.hasCycleWithLength_of_firstFailureCycle
              failure)⟩
        .nil)

/-- Node `[153]`, (F3): uncompressibility excludes a smaller proper
representative on the current residual. -/
@[reducible] noncomputable def coldFailureCompressionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureCompression
    { Requires := [K .uncompressible]
      Produces := [K .coldFailureCompression]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let uncompressible := (fun support compressible => (inputs.get (K .uncompressible)).down support
        (Graph.Strategy.InterfaceReplacement.replacementSupportOfCompressibleSupport _ _ _ _
          compressible))
      .cons (key := K .coldFailureCompression)
        ⟨by
          intro windows component corridor presentation index support
          exact Graph.ColdCorridor.Corridor.FirstFailureCompression.not_occurs
            uncompressible⟩
        .nil)

/-- Node `[153]`, (F4): a declared Type-B/route-8 support is returned to
the already-declared handoff ledger. -/
@[reducible] noncomputable def coldFailureHandoffRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureHandoff
    { Requires := []
      Produces := [K .coldFailureHandoff]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun _inputs =>
      .cons (key := K .coldFailureHandoff)
        ⟨by
          intro windows component corridor Handoff segment failure
          exact Graph.ColdCorridor.Corridor.handoff_mem failure⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
