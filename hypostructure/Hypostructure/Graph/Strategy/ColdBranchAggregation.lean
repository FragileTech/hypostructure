import Hypostructure.Core.Minimality
import Hypostructure.Core.Strategy.ColdBranchAggregation
import Hypostructure.Graph.InducedPathCold
import Hypostructure.Graph.Strategy.ColdBranchF2Closure
import Hypostructure.Graph.Strategy.ColdBranchGermClosure
import Hypostructure.Graph.Strategy.ObstructionPackingClosure
import Hypostructure.Graph.Strategy.SurplusAccounting

/-!
# Graph registration for cold-corridor aggregation

This adapter gives the existing Core cold strategy the graph meaning of one
exact induced-path packing.  It derives the exterior branch schedule, return
paths, finite response states, and F1--F5 event families from the public graph
presentation and the compiler-owned packing.  It supplies no classification,
terminal, route, or ledger value.
-/

namespace Hypostructure.Graph.Strategy.ColdBranchAggregation

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Graph.InducedPathCold

universe uResidual uVertex uClosure uAmbient uBranch uMeasure uPrevious

theorem storedF2Target
    {Previous : Type uPrevious}
    {object : Graph.FiniteObject.{uVertex}} {order : Nat}
    (profile : Graph.InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (decideTarget : ∀ candidate,
      Decidable (Graph.HasCycleWithLength CycleLengthOK candidate))
    {Handoff : Type uVertex}
    (handoffItems : Core.Finite.Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (stage : (canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
      (Graph.HasCycleWithLength CycleLengthOK) decideTarget handoffItems
      handoffSupport).ClassifiedStateStage Previous)
    (owner :
      let family := canonicalFamilyProducer profile CycleLengthOK
        cycleLengthDecidable (Graph.HasCycleWithLength CycleLengthOK)
        decideTarget handoffItems handoffSupport
      family.FailureOwner (family.storedClassificationQuery stage) .f2) :
    Graph.HasCycleWithLength CycleLengthOK object := by
  have defect := Graph.Strategy.ColdBranchF2Closure.storedF2Defect
    (Previous := Previous) (profile := profile) CycleLengthOK
    cycleLengthDecidable decideTarget handoffItems handoffSupport stage owner
  dsimp only at defect
  -- The germ of this owner: every completion below is `object.induce` at one
  -- retained prefix support, so a dyadic cycle in it is a dyadic cycle of
  -- `object` along `FiniteObject.induceEmbedding`.
  have transport : ∀ prefixStage : ReturnStage owner.1.1.1.1 owner.1.1.1.2,
      Graph.HasCycleWithLength CycleLengthOK
          (germCompletion owner.1.1.1.1 owner.1.1.1.2 prefixStage) →
        Graph.HasCycleWithLength CycleLengthOK object := by
    intro prefixStage cycled
    rcases cycled with ⟨certificate⟩
    let support : Finset object.Vertex :=
      (returnPrefixSupport owner.1.1.1.1 owner.1.1.1.2 prefixStage).toFinset
    exact ⟨certificate.mapHom (object.induceEmbedding support).toHom
      (object.induceEmbedding support).injective⟩
  by_contra noCycle
  exact defect (iff_of_false
    (fun cycled => noCycle (transport _ cycled))
    (fun cycled => noCycle (transport _ cycled)))

noncomputable def inducedPathFamilyCapability
    {Residual : Type uResidual} {Target : Residual → Prop}
    {Previous : Type (max uResidual uVertex)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{uResidual, uVertex}
        Residual Target)
    (current : Core.Residual.Query Previous fun _ => Residual)
    (packing : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation).occurrences
            (current previous))
        ((Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation).conflict
            (current previous)))
    {Handoff : Residual → Type uVertex}
    (handoffItems : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Handoff (current previous)))
    (handoffSupport : (residual : Residual) → Handoff residual →
      Finset (presentation.object residual).Vertex)
    (handoffAbsent : Option (PLift (∀ previous,
      (handoffItems previous).values = [])))
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (cycleForcesTarget : ∀ residual : Residual,
      Graph.HasCycleWithLength CycleLengthOK
          (presentation.object residual) →
        Target residual) :
    Core.Strategy.ColdBranchAggregation.FamilyCapability Previous
      (fun previous => Target (current previous)) := by
  classical
  let graphProfile :=
    Graph.Strategy.ObstructionPackingClosure.inducedPathProfileQueryAt
      presentation current packing
  let decideCycle : ∀ candidate : Graph.FiniteObject.{uVertex},
      Decidable (Graph.HasCycleWithLength CycleLengthOK candidate) :=
    fun _ => Classical.propDecidable _
  exact {
    Owner := fun previous =>
      AmbientCubicScheduledExteriorBranch (graphProfile previous)
    family := graphProfile.dependentMap fun previous activePacking =>
      canonicalFamilyProducer activePacking CycleLengthOK
        cycleLengthDecidable (Graph.HasCycleWithLength CycleLengthOK)
        decideCycle (handoffItems previous)
        (handoffSupport (current previous))
    storedF1ForcesTarget := fun previous stage owner =>
      cycleForcesTarget (current previous)
        (Graph.Strategy.ColdBranchGermClosure.storedF1Target
          (graphProfile previous) CycleLengthOK cycleLengthDecidable
          (Graph.HasCycleWithLength CycleLengthOK) decideCycle
          (handoffItems previous)
          (handoffSupport (current previous)) stage owner)
    classifiedStateForcesTarget := fun previous stage =>
      match ((canonicalFamilyProducer (graphProfile previous)
          CycleLengthOK cycleLengthDecidable
          (Graph.HasCycleWithLength CycleLengthOK) decideCycle
          (handoffItems previous)
          (handoffSupport (current previous))).storedF2OwnersQuery
          stage).values with
      | owner :: _ =>
          some (PLift.up (cycleForcesTarget (current previous)
            (storedF2Target (graphProfile previous) CycleLengthOK
              cycleLengthDecidable decideCycle (handoffItems previous)
              (handoffSupport (current previous)) stage owner)))
      | [] =>
      match ((canonicalFamilyProducer (graphProfile previous)
          CycleLengthOK cycleLengthDecidable
          (Graph.HasCycleWithLength CycleLengthOK) decideCycle
          (handoffItems previous)
          (handoffSupport (current previous))).storedF4OwnersQuery
          stage).values with
      | owner :: _ =>
          match handoffAbsent with
          | some absent =>
              (Graph.Strategy.ColdBranchFailureRouting.storedF4Impossible_of_emptyHandoff
                (graphProfile previous) CycleLengthOK cycleLengthDecidable
                (Graph.HasCycleWithLength CycleLengthOK) decideCycle
                (handoffItems previous)
                (handoffSupport (current previous))
                (absent.down previous) stage owner).elim
          | none => none
      | [] =>
      match (canonicalF5Focus (Previous := Previous)
          (graphProfile previous) CycleLengthOK cycleLengthDecidable
          (Graph.HasCycleWithLength CycleLengthOK) decideCycle
          (handoffItems previous)
          (handoffSupport (current previous))).select stage |>.value with
      | .isFalse _ => none
      | .isTrue active =>
          let generated := (_root_.Hypostructure.CT7.generateCounted
              (canonicalF5CT7Capability (Previous := Previous)
                (graphProfile previous) CycleLengthOK
                cycleLengthDecidable
                (Graph.HasCycleWithLength CycleLengthOK) decideCycle
                (handoffItems previous)
                (handoffSupport (current previous)))
              (Core.Residual.Focus.ActiveView.of stage active)).value
          match generated.terminal, generated.outcome with
          | _, .realization certificate =>
              some (PLift.up (cycleForcesTarget (current previous)
                (canonicalF5G1Target (graphProfile previous)
                  CycleLengthOK cycleLengthDecidable
                  (Graph.HasCycleWithLength CycleLengthOK) decideCycle
                  (handoffItems previous)
                  (handoffSupport (current previous))
                  (Core.Residual.Focus.ActiveView.of stage active)
                  certificate)))
          | _, .distinguishing residual =>
              some (PLift.up (cycleForcesTarget (current previous)
                (Graph.Strategy.ColdBranchF2Closure.canonicalF5G2Target
                  (profile := graphProfile previous) CycleLengthOK
                  cycleLengthDecidable decideCycle
                  (handoffItems previous)
                  (handoffSupport (current previous))
                  (Core.Residual.Focus.ActiveView.of stage active)
                  residual)))
          | _, .neutral _ => none }

/-- Disjunctive-target registration.  The cold corridor still tests the dyadic
truth value -- that is what `lem:cold-bounded-germ-trichotomy` compares -- and
the extra disjuncts are reached only at the conclusion, through the canonical
left injection.

Consumes `ColdBranchGermClosure.storedF1DisjunctiveTarget` at
`Graph/Strategy/ColdBranchGermClosure.lean:78`: that theorem is by definition
`Or.inl (storedF1Target …)`, which is exactly the composite this
specialization hands to `inducedPathFamilyCapability`, so the (F1) arm is the
already-proved disjunctive closure and not a second statement.  The same
identity relates `canonicalF5G1DisjunctiveTarget`
(`Graph/InducedPathCold.lean:3179`) to the CT7 `realization` arm. -/
noncomputable def inducedPathDisjunctiveFamilyCapability
    {Residual : Type uResidual} {Target : Residual → Prop}
    {Previous : Type (max uResidual uVertex)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{uResidual, uVertex}
        Residual Target)
    (current : Core.Residual.Query Previous fun _ => Residual)
    (packing : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation).occurrences (current previous))
        ((Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation).conflict (current previous)))
    {Handoff : Residual → Type uVertex}
    (handoffItems : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Handoff (current previous)))
    (handoffSupport : (residual : Residual) → Handoff residual →
      Finset (presentation.object residual).Vertex)
    (handoffAbsent : Option (PLift (∀ previous,
      (handoffItems previous).values = [])))
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Rest : Graph.FiniteObject.{uVertex} → Prop)
    (disjunctForcesTarget : ∀ residual : Residual,
      (Graph.HasCycleWithLength CycleLengthOK
            (presentation.object residual) ∨
          Rest (presentation.object residual)) →
        Target residual) :
    Core.Strategy.ColdBranchAggregation.FamilyCapability Previous
      (fun previous => Target (current previous)) :=
  inducedPathFamilyCapability presentation current packing
    handoffItems handoffSupport handoffAbsent CycleLengthOK
    cycleLengthDecidable
    (fun residual cycle => disjunctForcesTarget residual (Or.inl cycle))

noncomputable def inducedPathDisjunctiveMinimalFamilyCapability
    {Residual : Type uResidual} {Target : Residual → Prop}
    {Previous : Type (max uResidual uVertex)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{uResidual, uVertex}
        Residual Target)
    (current : Core.Residual.Query Previous fun _ => Residual)
    (packing : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation).occurrences (current previous))
        ((Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation).conflict (current previous)))
    {Handoff : Residual → Type uVertex}
    (handoffItems : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Handoff (current previous)))
    (handoffSupport : (residual : Residual) → Handoff residual →
      Finset (presentation.object residual).Vertex)
    (handoffAbsent : Option (PLift (∀ previous,
      (handoffItems previous).values = [])))
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Rest : Graph.FiniteObject.{uVertex} → Prop)
    (disjunctForcesTarget : ∀ residual : Residual,
      (Graph.HasCycleWithLength CycleLengthOK
            (presentation.object residual) ∨
          Rest (presentation.object residual)) →
        Target residual)
    (noBaselineProperSubgraph : (previous : Previous) →
      ∀ subgraph :
        Graph.ProperSubgraph (presentation.object (current previous)),
        ¬ ((presentation.object (current previous)).minDegree ≤
            subgraph.value.minDegree)) :
    Core.Strategy.ColdBranchAggregation.FamilyCapability Previous
      (fun previous => Target (current previous)) := by
  classical
  let graphProfile :=
    Graph.Strategy.ObstructionPackingClosure.inducedPathProfileQueryAt
      presentation current packing
  let decideCycle : ∀ candidate : Graph.FiniteObject.{uVertex},
      Decidable (Graph.HasCycleWithLength CycleLengthOK candidate) :=
    fun _ => Classical.propDecidable _
  exact {
    Owner := fun previous =>
      AmbientCubicScheduledExteriorBranch (graphProfile previous)
    family := graphProfile.dependentMap fun previous activePacking =>
      canonicalFamilyProducer activePacking CycleLengthOK
        cycleLengthDecidable (Graph.HasCycleWithLength CycleLengthOK)
        decideCycle (handoffItems previous)
        (handoffSupport (current previous))
    storedF1ForcesTarget := fun previous stage owner =>
      disjunctForcesTarget (current previous)
        (Or.inl (Graph.Strategy.ColdBranchGermClosure.storedF1Target
          (graphProfile previous) CycleLengthOK cycleLengthDecidable
          (Graph.HasCycleWithLength CycleLengthOK) decideCycle
          (handoffItems previous)
          (handoffSupport (current previous)) stage owner))
    classifiedStateForcesTarget := fun previous stage =>
      match ((canonicalFamilyProducer (graphProfile previous)
          CycleLengthOK cycleLengthDecidable
          (Graph.HasCycleWithLength CycleLengthOK) decideCycle
          (handoffItems previous)
          (handoffSupport (current previous))).storedF2OwnersQuery
          stage).values with
      | owner :: _ =>
          some (PLift.up (disjunctForcesTarget (current previous)
            (Or.inl (storedF2Target (graphProfile previous) CycleLengthOK
              cycleLengthDecidable decideCycle (handoffItems previous)
              (handoffSupport (current previous)) stage owner))))
      | [] =>
      match ((canonicalFamilyProducer (graphProfile previous)
          CycleLengthOK cycleLengthDecidable
          (Graph.HasCycleWithLength CycleLengthOK) decideCycle
          (handoffItems previous)
          (handoffSupport (current previous))).storedF3OwnersQuery
          stage).values with
      | owner :: _ =>
          (Graph.Strategy.ColdBranchGermClosure.storedF3Impossible
            (graphProfile previous) CycleLengthOK cycleLengthDecidable
            (Graph.HasCycleWithLength CycleLengthOK) decideCycle
            (handoffItems previous)
            (handoffSupport (current previous))
            (noBaselineProperSubgraph previous) stage owner).elim
      | [] =>
      match ((canonicalFamilyProducer (graphProfile previous)
          CycleLengthOK cycleLengthDecidable
          (Graph.HasCycleWithLength CycleLengthOK) decideCycle
          (handoffItems previous)
          (handoffSupport (current previous))).storedF4OwnersQuery
          stage).values with
      | owner :: _ =>
          match handoffAbsent with
          | some absent =>
              (Graph.Strategy.ColdBranchFailureRouting.storedF4Impossible_of_emptyHandoff
                (graphProfile previous) CycleLengthOK cycleLengthDecidable
                (Graph.HasCycleWithLength CycleLengthOK) decideCycle
                (handoffItems previous)
                (handoffSupport (current previous))
                (absent.down previous) stage owner).elim
          | none => none
      | [] =>
      match (canonicalF5Focus (Previous := Previous)
          (graphProfile previous) CycleLengthOK cycleLengthDecidable
          (Graph.HasCycleWithLength CycleLengthOK) decideCycle
          (handoffItems previous)
          (handoffSupport (current previous))).select stage |>.value with
      | .isFalse _ => none
      | .isTrue active =>
          let generated := (_root_.Hypostructure.CT7.generateCounted
              (canonicalF5CT7Capability (Previous := Previous)
                (graphProfile previous) CycleLengthOK
                cycleLengthDecidable
                (Graph.HasCycleWithLength CycleLengthOK) decideCycle
                (handoffItems previous)
                (handoffSupport (current previous)))
              (Core.Residual.Focus.ActiveView.of stage active)).value
          match generated.terminal, generated.outcome with
          | _, .realization certificate =>
              some (PLift.up (disjunctForcesTarget (current previous)
                (Or.inl (canonicalF5G1Target (graphProfile previous)
                  CycleLengthOK cycleLengthDecidable
                  (Graph.HasCycleWithLength CycleLengthOK) decideCycle
                  (handoffItems previous)
                  (handoffSupport (current previous))
                  (Core.Residual.Focus.ActiveView.of stage active)
                  certificate))))
          | _, .distinguishing residual =>
              some (PLift.up (disjunctForcesTarget (current previous)
                (Or.inl (Graph.Strategy.ColdBranchF2Closure.canonicalF5G2Target
                  (profile := graphProfile previous) CycleLengthOK
                  cycleLengthDecidable decideCycle
                  (handoffItems previous)
                  (handoffSupport (current previous))
                  (Core.Residual.Focus.ActiveView.of stage active)
                  residual))))
          | _, .neutral _ => none }

/-- Stage-polymorphic cold registration whose F4 schedule is supplied by the
exact upstream handoff-support capability.  The registration fixes only the
Graph interpretation of one support as a vertex finset; it contains no
support schedule and cannot reconstruct one from the stable residual. -/
noncomputable def inducedPathLedgerRegistration
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    {progress : Core.Progress P}
    {replacement : Core.Strategy.InterfaceReplacement.Profile
      (P := P) (T := T) progress}
    (presentation :
      Graph.Strategy.InducedPathPresentation
        (Core.Strategy.ProblemInput P)
        (fun input => T.Predicate input.object))
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (cycleForcesTarget : ∀ input : Core.Strategy.ProblemInput P,
      Graph.HasCycleWithLength CycleLengthOK
          (presentation.object input) →
        T.Predicate input.object) :
    Core.Strategy.ColdBranchAggregation.LedgerRegistration
      P T progress replacement
        (Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation)
        (fun input => Finset (presentation.object input).Vertex) where
  atStage := fun _exact current _activeObject packing handoffItems
      handoffAbsent =>
    inducedPathFamilyCapability presentation current packing handoffItems
      (fun _input support => support) handoffAbsent
      CycleLengthOK cycleLengthDecidable cycleForcesTarget

/-- Graph-native adapter from the exact coupled-pressure item fibre to the
cold corridor.  The corridor scans the producer's **items**, not a decoded
vertex set: `CanonicalAccounting.pairSupport` is handed over as the decoding
function, so an (F4) hit names the literal CT9-selected pressure pair it
entered and keeps its membership in the producer schedule.  Neither the
problem definition nor the cold registration supplies a second schedule. -/
noncomputable def inducedPathPressureLedgerRegistration
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    {progress : Core.Progress P}
    {replacement : Core.Strategy.InterfaceReplacement.Profile
      (P := P) (T := T) progress}
    (presentation :
      Graph.Strategy.InducedPathPresentation
        (Core.Strategy.ProblemInput P)
        (fun input => T.Predicate input.object))
    (baselineDegree : Core.Strategy.ProblemInput P → Nat)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (cycleForcesTarget : ∀ input : Core.Strategy.ProblemInput P,
      Graph.HasCycleWithLength CycleLengthOK
          (presentation.object input) →
        T.Predicate input.object) :
    Core.Strategy.ColdBranchAggregation.LedgerRegistration
      P T progress replacement
        (Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation)
        ((Graph.Strategy.SurplusAccounting.CanonicalAccounting.fibrePressure
          (fun input => presentation.object input) baselineDegree).Item) where
  atStage := fun _exact current _activeObject packing handoffItems
      handoffAbsent =>
    inducedPathFamilyCapability presentation current packing
      (Handoff := fun input => ULift.{uVertex}
        ((Graph.Strategy.SurplusAccounting.CanonicalAccounting.fibrePressure
          (fun input => presentation.object input) baselineDegree).Item
            input))
      (handoffItems.map fun _previous schedule =>
        schedule.map ULift.up ULift.up_injective (Classical.decEq _))
      (fun input item =>
        Graph.Strategy.SurplusAccounting.CanonicalAccounting.pairSupport
          (fun input => presentation.object input) baselineDegree
          input item.down)
      (handoffAbsent.map fun absent =>
        PLift.up fun previous => by
          show (handoffItems previous).values.map ULift.up = []
          rw [absent.down previous]
          rfl)
      CycleLengthOK cycleLengthDecidable cycleForcesTarget

/-- Pressure-handoff adapter for the full disjunctive graph target.  It reads
the same packing and handoff ledgers as the compatibility constructor, but
all cold response tables are evaluated against `cycle ∨ Rest`. -/
noncomputable def inducedPathDisjunctivePressureLedgerRegistration
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    {progress : Core.Progress P}
    {replacement : Core.Strategy.InterfaceReplacement.Profile
      (P := P) (T := T) progress}
    (presentation :
      Graph.Strategy.InducedPathPresentation
        (Core.Strategy.ProblemInput P)
        (fun input => T.Predicate input.object))
    (baselineDegree : Core.Strategy.ProblemInput P → Nat)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Rest : Graph.FiniteObject.{uVertex} → Prop)
    (disjunctForcesTarget : ∀ input : Core.Strategy.ProblemInput P,
      (Graph.HasCycleWithLength CycleLengthOK
            (presentation.object input) ∨
          Rest (presentation.object input)) →
        T.Predicate input.object) :
    Core.Strategy.ColdBranchAggregation.LedgerRegistration
      P T progress replacement
        (Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation)
        ((Graph.Strategy.SurplusAccounting.CanonicalAccounting.fibrePressure
          (fun input => presentation.object input) baselineDegree).Item) where
  atStage := fun _exact current _activeObject packing handoffItems
      handoffAbsent =>
    inducedPathDisjunctiveFamilyCapability presentation current packing
      (Handoff := fun input => ULift.{uVertex}
        ((Graph.Strategy.SurplusAccounting.CanonicalAccounting.fibrePressure
          (fun input => presentation.object input) baselineDegree).Item
            input))
      (handoffItems.map fun _previous schedule =>
        schedule.map ULift.up ULift.up_injective (Classical.decEq _))
      (fun input item =>
        Graph.Strategy.SurplusAccounting.CanonicalAccounting.pairSupport
          (fun input => presentation.object input) baselineDegree
          input item.down)
      (handoffAbsent.map fun absent =>
        PLift.up fun previous => by
          show (handoffItems previous).values.map ULift.up = []
          rw [absent.down previous]
          rfl)
      CycleLengthOK cycleLengthDecidable Rest disjunctForcesTarget

noncomputable def inducedPathDisjunctiveMinimalPressureLedgerRegistration
    {Baseline : Graph.FiniteObject.{uVertex} → Prop}
    {BranchState : Graph.FiniteObject.{uVertex} → Type uBranch}
    {Presentation : Type} {presentationValue : Presentation}
    {T : Core.Target (Graph.problemWithPresentation Baseline BranchState
      Presentation presentationValue)}
    {progress : Core.Progress (Graph.problemWithPresentation Baseline BranchState
      Presentation presentationValue)}
    {replacement : Core.Strategy.InterfaceReplacement.Profile
      (P := Graph.problemWithPresentation Baseline BranchState Presentation
        presentationValue) (T := T) progress}
    (subobjectProfile : Core.Minimality.SubobjectMinimalityProfile
      (P := Graph.problemWithPresentation Baseline BranchState Presentation
        presentationValue)
      T.Predicate progress Graph.ProperSubgraph)
    (subobjectValue : ∀ {source : Graph.FiniteObject.{uVertex}}
      (subgraph : Graph.ProperSubgraph source),
      subobjectProfile.toAmbient subgraph = subgraph.value)
    (baselineMonotone : ∀ {source value : Graph.FiniteObject.{uVertex}},
      Baseline source → source.minDegree ≤ value.minDegree → Baseline value)
    (presentation :
      Graph.Strategy.InducedPathPresentation
        (Core.Strategy.ProblemInput (Graph.problemWithPresentation Baseline
          BranchState Presentation presentationValue))
        (fun input => T.Predicate input.object))
    (objectIsInput : ∀ input, presentation.object input = input.object)
    (baselineDegree : Core.Strategy.ProblemInput
      (Graph.problemWithPresentation Baseline BranchState Presentation
        presentationValue) → Nat)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Rest : Graph.FiniteObject.{uVertex} → Prop)
    (disjunctForcesTarget : ∀ input : Core.Strategy.ProblemInput
        (Graph.problemWithPresentation Baseline BranchState Presentation
          presentationValue),
      (Graph.HasCycleWithLength CycleLengthOK
            (presentation.object input) ∨
          Rest (presentation.object input)) →
        T.Predicate input.object) :
    Core.Strategy.ColdBranchAggregation.LedgerRegistration
      (Graph.problemWithPresentation Baseline BranchState Presentation
        presentationValue)
      T progress replacement
        (Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation)
        ((Graph.Strategy.SurplusAccounting.CanonicalAccounting.fibrePressure
          (fun input => presentation.object input) baselineDegree).Item) where
  atStage := fun exact current activeObject packing handoffItems
      handoffAbsent =>
    inducedPathDisjunctiveMinimalFamilyCapability presentation current packing
      (Handoff := fun input => ULift.{uVertex}
        ((Graph.Strategy.SurplusAccounting.CanonicalAccounting.fibrePressure
          (fun input => presentation.object input) baselineDegree).Item
            input))
      (handoffItems.map fun _previous schedule =>
        schedule.map ULift.up ULift.up_injective (Classical.decEq _))
      (fun input item =>
        Graph.Strategy.SurplusAccounting.CanonicalAccounting.pairSupport
          (fun input => presentation.object input) baselineDegree
          input item.down)
      (handoffAbsent.map fun absent =>
        PLift.up fun previous => by
          show (handoffItems previous).values.map ULift.up = []
          rw [absent.down previous]
          rfl)
      CycleLengthOK cycleLengthDecidable Rest disjunctForcesTarget
      (fun previous => by
        have objectEq :
            presentation.object (current previous) =
              (exact.context previous).G :=
          (objectIsInput (current previous)).trans
            (activeObject previous)
        rw [objectEq]
        intro subgraph degreeBound
        refine (Core.Minimality.deriveNoSubobjectBaseline subobjectProfile
          (exact.context previous)).excludes subgraph ?_
        rw [subobjectValue subgraph]
        exact baselineMonotone (exact.context previous).baseline
          degreeBound)

/-- Build the existing Core cold profile from exact live Graph queries.  The
packing is projected once into its induced-path profile, while the handoff
supports are read from their own predecessor capability.  The resulting
family query stays indexed by the literal active stage and is the only family
consumed by Core's F1--F5 execution. -/
noncomputable def inducedPathLedgerProfile
    {Residual : Type uResidual} {Target : Residual → Prop}
    {Previous : Type (max uResidual uVertex)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{uResidual, uVertex}
        Residual Target)
    (packing : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation).occurrences
            (Core.Residual.residualOf previous))
        ((Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation).conflict
            (Core.Residual.residualOf previous)))
    (packing_nonempty : Core.Residual.Query Previous fun previous =>
      (packing previous).selected ≠ [])
    (barrierSummary : Core.Residual.Query Previous fun _ =>
      Core.Strategy.FiniteBarrierEnumeration.Summary)
    (overflow :
      Core.Strategy.ColdBranchAggregation.OverflowLedger Previous)
    (Closure : Previous → Type uClosure)
    (closure : Core.Residual.Query Previous Closure)
    {Handoff : Residual → Type uVertex}
    (handoffItems : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Handoff (Core.Residual.residualOf previous)))
    (handoffSupport : (residual : Residual) → Handoff residual →
      Finset (presentation.object residual).Vertex)
    (handoffAbsent : Option (PLift (∀ previous,
      (handoffItems previous).values = [])))
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (cycleForcesTarget : ∀ residual : Residual,
      Graph.HasCycleWithLength CycleLengthOK
          (presentation.object residual) →
        Target residual) :
    Core.Strategy.ColdBranchAggregation.LedgerProfile
      Previous Residual Target
        (Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation) := by
  let current : Core.Residual.Query Previous fun _ => Residual :=
    Core.Residual.Query.residual
  let familyCapability := inducedPathFamilyCapability presentation current
    packing handoffItems handoffSupport handoffAbsent CycleLengthOK
    cycleLengthDecidable cycleForcesTarget
  exact {
    Owner := familyCapability.Owner
    family := familyCapability.family
    current := current
    storedF1ForcesTarget := familyCapability.storedF1ForcesTarget
    classifiedStateForcesTarget := familyCapability.classifiedStateForcesTarget
    packing := packing
    packing_nonempty := packing_nonempty
    barrierSummary := barrierSummary
    overflow := overflow
    Closure := Closure
    closure := closure }

/-- Build the Core cold profile with the full disjunctive graph target used by
the live proof.  This differs from the compatibility constructor only in the
predicate passed to the graph-owned family; every residual, packing, overflow,
handoff, and closure query is the same incoming query. -/
noncomputable def inducedPathDisjunctiveLedgerProfile
    {Residual : Type uResidual} {Target : Residual → Prop}
    {Previous : Type (max uResidual uVertex)}
    [Core.Residual.HasResidual Previous Residual]
    (presentation :
      Graph.Strategy.InducedPathPresentation.{uResidual, uVertex}
        Residual Target)
    (packing : Core.Residual.Query Previous fun previous =>
      Core.Strategy.ObstructionPackingClosure.Packing
        ((Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation).occurrences (Core.Residual.residualOf previous))
        ((Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation).conflict (Core.Residual.residualOf previous)))
    (packing_nonempty : Core.Residual.Query Previous fun previous =>
      (packing previous).selected ≠ [])
    (barrierSummary : Core.Residual.Query Previous fun _ =>
      Core.Strategy.FiniteBarrierEnumeration.Summary)
    (overflow : Core.Strategy.ColdBranchAggregation.OverflowLedger Previous)
    (Closure : Previous → Type uClosure)
    (closure : Core.Residual.Query Previous Closure)
    {Handoff : Residual → Type uVertex}
    (handoffItems : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Handoff (Core.Residual.residualOf previous)))
    (handoffSupport : (residual : Residual) → Handoff residual →
      Finset (presentation.object residual).Vertex)
    (handoffAbsent : Option (PLift (∀ previous,
      (handoffItems previous).values = [])))
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Rest : Graph.FiniteObject.{uVertex} → Prop)
    (disjunctForcesTarget : ∀ residual : Residual,
      (Graph.HasCycleWithLength CycleLengthOK
            (presentation.object residual) ∨
          Rest (presentation.object residual)) →
        Target residual) :
    Core.Strategy.ColdBranchAggregation.LedgerProfile
      Previous Residual Target
        (Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
          presentation) := by
  let current : Core.Residual.Query Previous fun _ => Residual :=
    Core.Residual.Query.residual
  let familyCapability := inducedPathDisjunctiveFamilyCapability presentation
    current packing handoffItems handoffSupport handoffAbsent CycleLengthOK
    cycleLengthDecidable Rest disjunctForcesTarget
  exact {
    Owner := familyCapability.Owner
    family := familyCapability.family
    current := current
    storedF1ForcesTarget := familyCapability.storedF1ForcesTarget
    classifiedStateForcesTarget := familyCapability.classifiedStateForcesTarget
    packing := packing
    packing_nonempty := packing_nonempty
    barrierSummary := barrierSummary
    overflow := overflow
    Closure := Closure
    closure := closure }

end Hypostructure.Graph.Strategy.ColdBranchAggregation
