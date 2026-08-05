import Hypostructure.Graph.AtomResponse
import Hypostructure.Graph.TypeAReceiverClosure



namespace Hypostructure.Graph.Strategy.TypeAReceiverExhaustion

open Hypostructure
open Hypostructure.Graph.ReceiverLoad

universe u v uAmbient uBranch uVertex




def TraceTo (object : Graph.FiniteObject.{v}) (baselineDegree : Nat)
    (support : Finset object.Vertex) (member candidate : object.Vertex) :
    Prop :=
  ∃ walk : object.graph.Walk member candidate,
    ∀ vertex ∈ walk.support, vertex ≠ candidate →
      vertex ∈ support ∧
        Graph.Strategy.NormalizationRank.supportIncidence object support
            vertex = baselineDegree


noncomputable def canonicalReceiver
    (object : Graph.FiniteObject.{v}) (baselineDegree : Nat)
    (support : Finset object.Vertex) (member : object.Vertex) :
    object.Vertex := by
  classical
  exact (object.orderedVertices.find? fun candidate =>
      decide (candidate ∈ support ∧
        Graph.Strategy.NormalizationRank.supportIncidence object support
            candidate < baselineDegree ∧
        TraceTo object baselineDegree support member candidate)).getD member


noncomputable def receiverLoadLedger {Residual : Type u}
    (object : Residual → Graph.FiniteObject.{v})
    (baselineDegree : Residual → Nat) :
    Core.Strategy.LocalSupplyLowerBound.Registration.{u, max u v, v, v}
      Residual (fun residual => ULift.{u} (object residual).Vertex) where
  Member := fun residual => (object residual).Vertex
  Label := fun residual => (object residual).Vertex
  members := fun _ complement =>
    complement.map ULift.down (fun left right equality =>
      ULift.ext left right equality)
      (Classical.decEq _)
  requiredMass := fun residual complement member =>
    baselineDegree residual -
      Graph.Strategy.NormalizationRank.supportIncidence (object residual)
        (Graph.Strategy.NormalizationRank.supportOfComplement
          (object residual) complement) member
  observedSupply := fun residual complement member =>
    Graph.Strategy.NormalizationRank.boundaryIncidence (object residual)
      (Graph.Strategy.NormalizationRank.supportOfComplement
        (object residual) complement) member
  defectCorrection := fun residual _ member =>
    baselineDegree residual - (object residual).degree member
  surplus := fun residual _ member =>
    (object residual).degree member - baselineDegree residual
  label := fun residual complement member =>
    canonicalReceiver (object residual) (baselineDegree residual)
      (Graph.Strategy.NormalizationRank.supportOfComplement
        (object residual) complement) member
  labelDecidableEq := fun residual => (object residual).vertices.decEq
  pointwise := by
    intro residual complement member
    have split :=
      Graph.Strategy.NormalizationRank.supportIncidence_add_boundaryIncidence
        (object residual)
        (Graph.Strategy.NormalizationRank.supportOfComplement
          (object residual) complement) member
    omega



def TargetCompleteCompression
    (presentation : Graph.TypeAB.Presentation.{uVertex})
    (object : Graph.FiniteObject.{uVertex}) : Prop :=
  ∃ certificate : Graph.TypeAB.TypeACertificate presentation object,
    ∃ smaller : Finset object.Vertex,
      smaller.Nonempty ∧
        smaller ⊂ certificate.common.support ∧
          Graph.TypeAB.Baseline presentation (object.induce smaller) ∧
            (presentation.Target (object.induce smaller) →
              presentation.Target object)

/-- A window of the residual's own maximal induced-path packing, read as a
`TypeBClosure.Window`.

`InducedPathMaximalPacking.Window` is a graph embedding of the path graph;
`TypeBClosure.Window` is the coordinate function the label algebra of
`lem:labels` is stated on.  This connects the two framework carriers so exit (3)
can be stated about the *packed* windows the packing producer selected, instead
of quantifying over every coordinate function. -/
noncomputable def windowOfPacking
    {object : Graph.FiniteObject.{uVertex}}
    (window : Graph.InducedPathMaximalPacking.Window object 13) :
    Graph.TypeBClosure.Window object where
  coordinate := fun index => window ⟨min index 12, by omega⟩

/-- A packing window really is packed: its displayed edges are the path graph's,
transported by the embedding, and its thirteen vertices are distinct because the
embedding is injective. -/
theorem windowOfPacking_isPacked {object : Graph.FiniteObject.{uVertex}}
    (window : Graph.InducedPathMaximalPacking.Window object 13) :
    (windowOfPacking window).IsPacked where
  step := by
    intro index lt
    have adjacency : (SimpleGraph.pathGraph 13).Adj ⟨min index 12, by omega⟩
        ⟨min (index + 1) 12, by omega⟩ := by
      simp [SimpleGraph.pathGraph, Nat.le_of_lt lt]
      omega
    simpa [windowOfPacking] using window.map_adj_iff.mpr adjacency
  distinct := by
    intro index le other le' equal
    have finEq : (⟨min index 12, by omega⟩ : Fin 13) =
        ⟨min other 12, by omega⟩ :=
      window.injective (by simpa [windowOfPacking] using equal)
    rw [Fin.mk.injEq] at finEq
    omega


def IllegalWindowLabel {object : Graph.FiniteObject.{uVertex}}
    (packing : Graph.InducedPathMaximalPacking.Profile object 13) : Prop :=
  ∃ window ∈ packing.selected,
    ∃ (outside : object.Vertex) (a b : Graph.TypeBMarkedFan.Index),
      a ≠ b ∧
        object.graph.Adj outside
          ((windowOfPacking window).coordinate a.val) ∧
        object.graph.Adj outside
          ((windowOfPacking window).coordinate b.val) ∧
        (∀ t ≤ 12, outside ≠ (windowOfPacking window).coordinate t) ∧
        ¬ Graph.TypeBMarkedFan.IsLegal {a, b}


noncomputable def exitThreeSplit
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    {CycleLengthOK : Nat → Prop}
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject.{uVertex})
    (packing : (input : Core.Strategy.ProblemInput P) →
      Graph.InducedPathMaximalPacking.Profile (object input) 13)
    (accepted : Graph.TypeBClosure.AcceptedLengths CycleLengthOK)
    (closure : ∀ input : Core.Strategy.ProblemInput P,
      Graph.HasCycleWithLength CycleLengthOK (object input) →
        T.Predicate input.object) :
    Core.DichotomyData.{uAmbient, uBranch, 0} P T :=
  Core.DichotomyData.ofAlternative
    (fun input => IllegalWindowLabel (packing input))
    { name := "Exit 3: P13 label collision"
      note := ""
      tags := ["type-a", "node-99", "exit-3"] }
    { name := "Label/target collision"
      note := "" }
    { name := "No label collision"
      note := "" }
    (closeLeft := some ⟨fun input witness => by
      obtain ⟨window, _selected, outside, a, b, distinct, lower, upper,
        windowFree, illegal⟩ := witness.down
      exact closure input
        (Graph.TypeBClosure.hasCycleWithLength_of_illegalLabel accepted
          (windowOfPacking_isPacked window)
          distinct lower upper windowFree illegal)⟩)


def ResponseDelocalization
    (presentation : Graph.TypeAB.Presentation.{uVertex})
    (object : Graph.FiniteObject.{uVertex}) : Prop :=
  ∃ (certificate : Graph.TypeAB.TypeACertificate presentation object)
      (smaller : Finset object.Vertex),
    smaller.Nonempty ∧ smaller ⊂ certificate.common.support ∧
      Graph.TypeAB.Baseline presentation (object.induce smaller)


noncomputable def exitSixSplit
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    {LengthOK : Nat → Prop}
    (presentation : Graph.TypeAB.Presentation.{uVertex})
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject.{uVertex})
    (targetIsCycle : ∀ candidate : Graph.FiniteObject.{uVertex},
      presentation.Target candidate ↔
        Graph.HasCycleWithLength LengthOK candidate)
    (closure : ∀ input : Core.Strategy.ProblemInput P,
      Graph.HasCycleWithLength LengthOK (object input) →
        T.Predicate input.object) :
    Core.DichotomyData.{uAmbient, uBranch, 0} P T :=
  Core.DichotomyData.ofAlternative
    (fun input => ResponseDelocalization presentation (object input))
    { name := "Exit 6: response delocalization"
      note := ""
      tags := ["type-a", "node-105", "exit-6"] }
    { name := "Delocalization branch closes"
      note := "" }
    { name := "No delocalization"
      note := "" }
    (closeLeft := some ⟨fun input witness => by
      obtain ⟨certificate, smaller, nonempty, proper, baseline⟩ := witness.down
      exact closure input
        (TypeAReceiverClosure.hasCycleWithLength_of_properBaselineSubsupport
          certificate targetIsCycle nonempty proper baseline)⟩)


def DecoratedHandoffEnvelope
    (presentation : Graph.TypeAB.Presentation.{uVertex})
    (object : Graph.FiniteObject.{uVertex}) : Prop :=
  ∀ certificate : Graph.TypeAB.TypeACertificate presentation object,
    ∃ centers : Finset object.Vertex,
      centers.Nonempty ∧
        Nonempty (Graph.TypeAB.DecoratedHandoffData presentation object
          certificate.common.support centers)

/-- **`def:typeA-receiver-load`'s saturated receiver.**

`L(w) ≥ 4q(w)`, with `L(w)` the number of full-load members whose canonical
trace ends at `w` and `4q(w)` the raw threshold `H_j` of
`lem:typeA-threshold-algebra` (`TypeAReceiverClosure.threshold`).  Both sides are
computed from the object's own data through `canonicalReceiver`; the support is
existentially quantified as in the exit predicates. -/
noncomputable def SaturatedReceiver
    (presentation : Graph.TypeAB.Presentation.{uVertex})
    (object : Graph.FiniteObject.{uVertex})
    (profile : LoadCapacityProfile) : Prop :=
  ∀ (certificate : Graph.TypeAB.TypeACertificate presentation object)
      (routing : RoutedLoad (object := object) profile
        ⟨certificate.common.support⟩),
    ∃ receiver :
        (⟨certificate.common.support⟩ : Support object).ReceiverVertex profile,
      routing.saturated receiver


noncomputable def saturatedReceiverSplit
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    (presentation : Graph.TypeAB.Presentation.{uVertex})
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject.{uVertex})
    (profile : Core.Strategy.ProblemInput P → LoadCapacityProfile)
    (baseline : ∀ input : Core.Strategy.ProblemInput P,
      presentation.baselineDegree = (profile input).baselineDegree)
    (scale : ∀ input : Core.Strategy.ProblemInput P,
      presentation.dischargeScale = (profile input).loadMultiplier) :
    Core.DichotomyData.{uAmbient, uBranch, 0} P T :=
  Core.DichotomyData.ofAlternative
    (fun input => SaturatedReceiver presentation (object input) (profile input))
    { name := "Saturated receiver"
      note := ""
      tags := ["type-a", "node-89"] }
    { name := "Saturated receiver present"
      note := "" }
    { name := "Unsaturated Type A charge closes"
      note := "" }
    (closeRight := some ⟨fun input witness => by
      classical
      obtain ⟨certificate, inner⟩ := not_forall.mp witness.down
      obtain ⟨routing, unsaturated⟩ := not_forall.mp inner
      exact absurd trivial fun _ =>
        TypeAReceiverClosure.certificate_unsaturated_impossible certificate
          routing (fun receiver => by
            have notSaturated := not_exists.mp unsaturated receiver
            exact (routing.saturated_or_unsaturated receiver).resolve_left
              notSaturated)
          (baseline input) (scale input)⟩)


def VisibleReturnSaturation
    (presentation : Graph.TypeAB.Presentation.{uVertex})
    (object : Graph.FiniteObject.{uVertex})
    (profile : LoadCapacityProfile) (threshold : Nat) : Prop :=
  ∀ certificate : Graph.TypeAB.TypeACertificate presentation object,
    ∃ (port : CompletionPort
          (⟨certificate.common.support⟩ : Support object) profile)
        (loads : Finset
          ((⟨certificate.common.support⟩ : Support object).FullVertex profile)),
      threshold ≤ loads.card ∧
        ∀ load ∈ loads, ∃ returnData : ReceiverEntryReturn port,
          load.1 ∈ returnData.channel.path.support




noncomputable def visibleReturnSplit
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    (presentation : Graph.TypeAB.Presentation.{uVertex})
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject.{uVertex})
    (profile : Core.Strategy.ProblemInput P → LoadCapacityProfile)
    (visibleThreshold : Core.Strategy.ProblemInput P → Nat) :
    Core.DichotomyData.{uAmbient, uBranch, 0} P T :=
  Core.DichotomyData.ofAlternative
    (fun input =>
      VisibleReturnSaturation presentation (object input) (profile input)
        (visibleThreshold input))
    { name := "Visible receiver-entry returns"
      note := ""
      tags := ["type-a", "node-93"] }
    { name := "Four visible returns"
      note := "" }
    { name := "Visible-first excess"
      note := "" }




noncomputable def exitOneSplit
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    {CycleLengthOK : Nat → Prop}
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject.{uVertex})
    (rootedReturn : Graph.RootedReturnTargetAlgebra CycleLengthOK)
    (closure : ∀ input : Core.Strategy.ProblemInput P,
      Graph.HasCycleWithLength CycleLengthOK (object input) →
        T.Predicate input.object) :
    Core.DichotomyData.{uAmbient, uBranch, 0} P T :=
  Core.DichotomyData.ofAlternative
    (fun input => Nonempty (rootedReturn.RootedReturn (object input)))
    { name := "Exit 1: Mersenne return"
      note := ""
      tags := ["type-a", "node-95", "exit-1"] }
    { name := "Target cycle"
      note := "" }
    { name := "No Mersenne return"
      note := "" }
    (closeLeft := some ⟨fun input witness =>
      closure input
        ((rootedReturn.target_iff_hasRootedReturn (object input)).mpr
          witness.down)⟩)


noncomputable def exitTwoSplit
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    {CycleLengthOK : Nat → Prop}
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject.{uVertex})
    (closure : ∀ input : Core.Strategy.ProblemInput P,
      Graph.HasCycleWithLength CycleLengthOK (object input) →
        T.Predicate input.object) :
    Core.DichotomyData.{uAmbient, uBranch, 0} P T :=
  Core.DichotomyData.ofAlternative
    (fun input => ∃ pair : Graph.CommonEndpointsCycle (object input),
      CycleLengthOK (pair.forward.length + pair.backward.length))
    { name := "Exit 2: power-of-two theta"
      note := ""
      tags := ["type-a", "node-97", "exit-2"] }
    { name := "Target cycle"
      note := "" }
    { name := "No accepted theta"
      note := "" }
    (closeLeft := some ⟨fun input witness =>
      closure input
        ⟨witness.down.choose.target CycleLengthOK witness.down.choose_spec⟩⟩)


noncomputable def exitFiveSplit
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    (presentation : Graph.TypeAB.Presentation.{uVertex})
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject.{uVertex})
    (closure : ∀ input : Core.Strategy.ProblemInput P,
      presentation.Target (object input) → T.Predicate input.object) :
    Core.DichotomyData.{uAmbient, uBranch, 0} P T :=
  Core.DichotomyData.ofAlternative
    (fun input => TargetCompleteCompression presentation (object input))
    { name := "Exit 5: target-complete compression"
      note := ""
      tags := ["type-a", "node-103", "exit-5"] }
    { name := "Uncompressibility contradiction"
      note := "" }
    { name := "No compression"
      note := "" }
    (closeLeft := some ⟨fun input witness => by
      obtain ⟨certificate, smaller, nonempty, proper, baseline, complete⟩ :=
        witness.down
      exact closure input
        (TypeAReceiverClosure.target_of_targetCompleteSubsupport
          certificate nonempty proper baseline complete)⟩)




noncomputable def exitSevenSplit
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    (presentation : Graph.TypeAB.Presentation.{uVertex})
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject.{uVertex}) :
    Core.DichotomyData.{uAmbient, uBranch, 0} P T :=
  Core.DichotomyData.ofAlternative
    (fun input => DecoratedHandoffEnvelope presentation (object input))
    { name := "Exit 7: decorated handoff fan"
      note := ""
      tags := ["type-a", "node-107", "exit-7"] }
    { name := "Type B handoff"
      note := "" }
    { name := "Route-8 residual"
      note := "" }

end Hypostructure.Graph.Strategy.TypeAReceiverExhaustion
