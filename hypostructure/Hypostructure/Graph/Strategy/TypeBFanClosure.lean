import Hypostructure.Core.Strategy.Data
import Hypostructure.Graph.Finite
import Hypostructure.Graph.SupportCharge
import Hypostructure.Graph.TypeBOpenPorts
import Hypostructure.Graph.TypeBMarkedFan
import Hypostructure.Graph.TypeBFanClosedPorts
import Hypostructure.Graph.TypeBDegreeFour
import Hypostructure.Graph.TypeBProfileSchedule
import Hypostructure.Graph.TypeBBridgeResidual
import Hypostructure.Graph.TypeBClosure
import Hypostructure.Graph.TypeBFanMass
import Hypostructure.Graph.Strategy.SurplusAccounting



namespace Hypostructure.Graph.Strategy.TypeBFanClosure

open Hypostructure

universe u uAmbient uBranch

/-- The certificate-marked fan-degree cap of `rem:fan-finite`, read off the
label algebra instead of written as a numeral.

`Graph.TypeBMarkedFan.packingCap` is the block count of the explicit clique
cover of the difference graph `D`, and `Marked.degree_le_packingCap` is the
proof that a certificate-marked fan centre never exceeds it.  The two data the
cover depends on are the window coordinates of a packed `P₁₃` and the target's
dyadic length set (through `isDyadic_wedgeCycle_iff`'s forbidden gaps
`{0, 4, 12}`); at the registered presentation the block count computes to `8`
(`packingCap_eq_eight`).

Unlike `heavyCentreThreshold` below, this cap is **not** a function of the
registered `baselineDegree`: `k` occurs nowhere in `DAdj`, `packingClass` or
`packingCap`, and `rem:fan-finite` derives the bound from the label algebra
alone.  Anything of the form `f baselineDegree` that happens to evaluate to
`8` at `k = 3` would be a coincidence, not this cap. -/
def markedCentreCap : Nat := Graph.TypeBMarkedFan.packingCap


def heavyCentreThreshold (baselineDegree : Nat) : Nat := baselineDegree + 2


theorem degree_eq_succ_baseline_of_low {object : Graph.FiniteObject.{u}}
    {baselineDegree : Nat} {core : Finset object.Vertex}
    (low : Graph.SupportCharge.Low object
      (heavyCentreThreshold baselineDegree) core)
    {centre : object.Vertex} (mem : centre ∈ core)
    (surplus : baselineDegree < object.degree centre) :
    object.degree centre = baselineDegree + 1 := by
  have notHeavy :
      ¬ heavyCentreThreshold baselineDegree ≤ object.degree centre := by
    intro heavy
    have member : centre ∈ Graph.SupportCharge.highCenters object
        (heavyCentreThreshold baselineDegree) core :=
      Finset.mem_filter.mpr ⟨mem, heavy⟩
    rw [low.noHigh] at member
    simp at member
  unfold heavyCentreThreshold at notHeavy
  omega



/-- The object's own vertex set, used as the support core of the heavy-centre
selection.  It is the object's declared vertex order read as a finite set, so
no new carrier is introduced. -/
noncomputable def centreCore (object : Graph.FiniteObject) :
    Finset object.Vertex := by
  letI := object.vertices.decEq
  exact object.orderedVertices.toFinset


noncomputable def degreeSplitDichotomy
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject)
    (baselineDegree : Core.Strategy.ProblemInput P → Nat) :
    Core.DichotomyData.{uAmbient, uBranch, 0} P T where
  LeftPayload := fun input =>
    Graph.SupportCharge.High (object input)
      (heavyCentreThreshold (baselineDegree input))
      (centreCore (object input))
  RightPayload := fun input =>
    PLift (Graph.SupportCharge.Low (object input)
      (heavyCentreThreshold (baselineDegree input))
      (centreCore (object input)))
  classify := fun input => by
    classical
    by_cases heavy :
        (Graph.SupportCharge.highCenters (object input)
          (heavyCentreThreshold (baselineDegree input))
          (centreCore (object input))).Nonempty
    · exact Sum.inl (Graph.SupportCharge.highWitness heavy)
    · exact Sum.inr (PLift.up (Graph.SupportCharge.low_of_not_high heavy))
  metadata :=
    { name := "Type B heavy-centre split"
      note := ""
      tags := ["type-b", "node-68"] }
  leftMetadata :=
    { name := "Heavy centre present"
      note := "" }
  rightMetadata :=
    { name := "No heavy centre"
      note := "" }


noncomputable def certificateLabellingSplit
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject) :
    Core.DichotomyData.{uAmbient, uBranch, 0} P T where
  LeftPayload := fun input =>
    PLift (Nonempty (Graph.TypeBMarkedFan.Marked (object input)))
  RightPayload := fun input =>
    PLift (¬ Nonempty (Graph.TypeBMarkedFan.Marked (object input)))
  classify := fun input => by
    classical
    by_cases marked : Nonempty (Graph.TypeBMarkedFan.Marked (object input))
    · exact Sum.inl (PLift.up marked)
    · exact Sum.inr (PLift.up marked)
  metadata :=
    { name := "Type B certificate labelling"
      note := ""
      tags := ["type-b", "node-71"] }
  leftMetadata :=
    { name := "Certificate labelling present"
      note := "A certificate-marked Type B fan, carrying the fan-degree cap \
        d_G(h) <= 8 of rem:fan-finite." }
  rightMetadata :=
    { name := "No certificate labelling"
      note := "" }


noncomputable def heavyCentreLocalResponse
    (P : Core.Problem.{uAmbient, uBranch})
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject) :
    Core.ResponseData.{uAmbient, uBranch, 0} P where
  Item := fun input => (object input).Vertex
  Response := fun _ => Nat
  Class := fun _ => Nat
  schedule := fun input =>
    { values := (object input).orderedVertices
      nodup := (object input).orderedVertices_nodup
      decEq := (object input).vertices.decEq }
  observe := fun input vertex =>
    (Graph.TypeBOpenPorts.triangularPorts (object input) vertex).length
  classify := fun _ count => count
  metadata :=
    { name := "Heavy-centre local response"
      note := ""
      tags := ["type-b", "node-69"] }


noncomputable def fanSafeCapScan
    (P : Core.Problem.{uAmbient, uBranch})
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject)
    (baselineDegree : Core.Strategy.ProblemInput P → Nat) :
    Core.ScanData.{uAmbient, uBranch, 0} P where
  Item := fun input => (object input).Vertex
  schedule := fun input =>
    { values := (object input).orderedVertices
      nodup := (object input).orderedVertices_nodup
      decEq := (object input).vertices.decEq }
  witness := fun input vertex =>
    heavyCentreThreshold (baselineDegree input) ≤ (object input).degree vertex →
      (object input).degree vertex ≤ markedCentreCap
  witnessDecidable := fun _ _ => inferInstance
  metadata :=
    { name := "Type B fan-safe cap"
      note := ""
      tags := ["type-b", "node-70"] }


noncomputable def directCycleRemovalSplit
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject)
    (LengthOK : Nat → Prop)
    (accepted : Graph.TypeBClosure.AcceptedLengths LengthOK)
    (closure : ∀ input : Core.Strategy.ProblemInput P,
      Graph.HasCycleWithLength LengthOK (object input) →
        T.Predicate input.object) :
    Core.DichotomyData.{uAmbient, uBranch, 0} P T where
  LeftPayload := fun input =>
    PLift (Graph.TypeBClosure.DirectCycleConfiguration (object input))
  RightPayload := fun input =>
    PLift (Graph.TypeBClosure.DirectCycleFree (object input))
  classify := fun input => by
    classical
    by_cases direct :
        Graph.TypeBClosure.DirectCycleConfiguration (object input)
    · exact Sum.inl (PLift.up direct)
    · exact Sum.inr (PLift.up direct)
  closeLeft := some ⟨fun input witness =>
    closure input
      (Graph.TypeBClosure.hasCycleWithLength_of_directCycleConfiguration
        accepted witness.down)⟩
  metadata :=
    { name := "Type B direct-cycle removal"
      note := ""
      tags := ["type-b", "node-72"] }
  leftMetadata :=
    { name := "Direct fan-window or two-window cycle"
      note := "A same-window attachment with gap 2 or 6, a fan wedge across \
        the centre with gap 0, 4 or 12, an interlaced closed pair with \
        L_cross in {8, 16}, or a two-window pair with |i-j| + |a-b| in \
        {0, 4, 12}. Each builds a power-of-two cycle, so this side closes the \
        target." }
  rightMetadata :=
    { name := "Direct-cycle-free closed pair"
      note := "" }


noncomputable def b2LedgerSplit
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject) :
    Core.DichotomyData.{uAmbient, uBranch, 0} P T where
  LeftPayload := fun input =>
    PLift (∃ profile : Graph.TypeBFanClosedPorts.Profile (object input),
      2 ≤ profile.closedCount)
  RightPayload := fun input =>
    PLift (¬ ∃ profile : Graph.TypeBFanClosedPorts.Profile (object input),
      2 ≤ profile.closedCount)
  classify := fun input => by
    classical
    by_cases paid :
        ∃ profile : Graph.TypeBFanClosedPorts.Profile (object input),
          2 ≤ profile.closedCount
    · exact Sum.inl (PLift.up paid)
    · exact Sum.inr (PLift.up paid)
  metadata :=
    { name := "Type B B2 ledger"
      note := ""
      tags := ["type-b", "node-72"] }
  leftMetadata :=
    { name := "B2 disjointness holds"
      note := "" }
  rightMetadata :=
    { name := "B2 disjointness fails"
      note := "" }


noncomputable def fanMassAccounting
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject)
    (baselineDegree : Residual → Nat) :
    Core.Strategy.BaselineDemandAccounting.Registration Residual where
  budget := SurplusAccounting.countingBudget
  Site := fun residual => (object residual).Vertex
  Witness := fun residual _ => (object residual).Vertex
  family := fun residual =>
    { indices :=
        { values := (object residual).orderedVertices
          nodup := (object residual).orderedVertices_nodup
          decEq := (object residual).vertices.decEq }
      fibres := fun site =>
        { values := (object residual).orderedNeighbors site
          nodup := (object residual).orderedNeighbors_nodup site
          decEq := (object residual).vertices.decEq } }
  Active := fun residual vertex =>
    Graph.TypeBFanMass.IsChargedCentre (object residual) vertex
  Supports := fun residual vertex witness =>
    (object residual).graph.Adj vertex witness ∧
      (object residual).degree witness = baselineDegree residual
  contribution := fun residual vertex _ =>
    (object residual).degree vertex - baselineDegree residual
  required := fun residual =>
    (object residual).degreeSurplus (baselineDegree residual)
  capacity := fun residual =>
    (object residual).degreeSurplus (baselineDegree residual)
  activeDecidable := fun residual vertex =>
    decidable_of_iff _
      (Graph.TypeBFanMass.isChargedCentre_iff (object residual) vertex).symm
  supportsDecidable := fun _ _ _ => Classical.propDecidable _
  resourceLEDecidable := Nat.decLe


noncomputable def degreeFourProfileScan
    (P : Core.Problem.{uAmbient, uBranch})
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject) :
    Core.ScanData.{uAmbient, uBranch, 0} P where
  Item := fun input => Graph.TypeBDegreeFour.TriangularCore (object input)
  schedule := fun input =>
    { values := Graph.TypeBDegreeFour.degreeFourCores (object input)
      nodup := Graph.TypeBDegreeFour.degreeFourCores_nodup (object input)
      decEq := Classical.decEq _ }
  witness := fun input core =>
    2 ≤ (Graph.TypeBOpenPorts.triangularPorts (object input) core.center).length
  witnessDecidable := fun _ _ => inferInstance
  metadata :=
    { name := "Degree-four fan profile"
      note := ""
      tags := ["type-b", "node-79"] }


noncomputable def degreeFourBranchSplit
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject)
    (baselineDegree : Core.Strategy.ProblemInput P → Nat) :
    Core.DichotomyData.{uAmbient, uBranch, 0} P T where
  LeftPayload := fun input =>
    PLift (∃ centre : (object input).Vertex,
      (object input).degree centre = baselineDegree input + 1)
  RightPayload := fun input =>
    PLift (¬ ∃ centre : (object input).Vertex,
      (object input).degree centre = baselineDegree input + 1)
  classify := fun input => by
    classical
    by_cases four :
        ∃ centre : (object input).Vertex,
          (object input).degree centre = baselineDegree input + 1
    · exact Sum.inl (PLift.up four)
    · exact Sum.inr (PLift.up four)
  metadata :=
    { name := "Degree-four branch"
      note := ""
      tags := ["type-b", "node-78"] }
  leftMetadata :=
    { name := "Degree-four centre present"
      note := "" }
  rightMetadata :=
    { name := "No degree-four centre"
      note := "" }


noncomputable def hybridEntryScan
    (P : Core.Problem.{uAmbient, uBranch})
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject) :
    Core.ScanData.{uAmbient, uBranch, 0} P where
  Item := fun input =>
    Graph.TypeBFanClosedPorts.Profile (object input)
  schedule := fun input =>
    { values := Graph.TypeBProfileSchedule.profileCandidates (object input)
      nodup := Graph.TypeBProfileSchedule.profileCandidates_nodup (object input)
      decEq := Classical.decEq _ }
  witness := fun input profile =>
    Graph.TypeBProfileSchedule.IsHybridEligible (object := object input) profile
  witnessDecidable := fun _ _ => inferInstance
  metadata :=
    { name := "Type B hybrid B1 entry"
      note := ""
      tags := ["type-b", "node-74"] }


noncomputable def bridgeDeficitScan
    (P : Core.Problem.{uAmbient, uBranch})
    (object : Core.Strategy.ProblemInput P → Graph.FiniteObject)
    (baselineDegree : Core.Strategy.ProblemInput P → Nat) :
    Core.ScanData.{uAmbient, uBranch, 0} P where
  Item := fun input => (object input).Vertex
  schedule := fun input =>
    { values := (object input).orderedVertices
      nodup := (object input).orderedVertices_nodup
      decEq := (object input).vertices.decEq }
  witness := fun input vertex =>
    baselineDegree input ≤ (object input).degree vertex
  witnessDecidable := fun _ _ => inferInstance
  metadata :=
    { name := "Type B bridge deficit"
      note := ""
      tags := ["type-b", "node-76"] }

end Hypostructure.Graph.Strategy.TypeBFanClosure
