import Hypostructure.Core.Strategy.ColdBranchAggregation
import Hypostructure.Graph.InducedPathCold


namespace Hypostructure.Graph.Strategy.ColdBranchGermClosure

open Hypostructure
open Hypostructure.Core.Finite
open Hypostructure.Graph.InducedPathCold

universe u v uPrevious

set_option maxHeartbeats 4000000

/-! ## (F1) The stored first-failure event is an ambient dyadic cycle -/

theorem storedF1Target
    {Previous : Type uPrevious}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (stage : (canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
      Target decideTarget handoffItems handoffSupport).ClassifiedStateStage Previous)
    (owner :
      let family := canonicalFamilyProducer profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
      family.FailureOwner (family.storedClassificationQuery.read stage) .f1) :
    Graph.HasCycleWithLength CycleLengthOK object := by
  let family := canonicalFamilyProducer profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  have event := family.storedFailureEvent stage .f1 (by decide) owner
  exact ⟨f1CycleCertificateOfStoredEvent owner.1.1.1.1 owner.1.1.1.2
    CycleLengthOK cycleLengthDecidable Target decideTarget handoffItems handoffSupport
    event⟩

/-- Disjunctive-target adapter for the same stored F1 event, matching the
`cycle ∨ Rest` target actually registered by the cold recipe. -/
theorem storedF1DisjunctiveTarget
    {Previous : Type uPrevious}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (stage : (canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
      Target decideTarget handoffItems handoffSupport).ClassifiedStateStage Previous)
    (owner :
      let family := canonicalFamilyProducer profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
      family.FailureOwner (family.storedClassificationQuery.read stage) .f1)
    (Rest : FiniteObject.{u} → Prop) :
    Graph.HasCycleWithLength CycleLengthOK object ∨ Rest object :=
  Or.inl (storedF1Target profile CycleLengthOK cycleLengthDecidable Target
    decideTarget handoffItems handoffSupport stage owner)

/-! ## (F3) The stored first-failure event

`def:cold-corridor-first-failure` (F3) is "two prefixes have the same exact
target response against every outside context and one gives a strictly smaller
proper representative".  `F3Valid` is now exactly those clauses, and
`Graph.InducedPathCold.F3Bookkeeping.targetComplete` / `.locallySmaller` /
`.properRepresentative` read them back off the stored event.

`lem:cold-corridor-first-failure` (iii) then closes the stored event against
the inherited interface-replacement ledger.  That step consumes the germ's own
decomposition -- the two-boundary support of `def:cold-bounded-germ` -- and is
supplied by `ColdBranchGermClosure.neutralCompressionFrameImpossible` below
together with a `CompressionFrame` at that site; it is no longer derived from
a compressibility clause smuggled into the scan predicate.
-/

theorem storedF3Impossible
    {Previous : Type uPrevious}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (excluded : ∀ subgraph : Graph.ProperSubgraph object,
      ¬ (object.minDegree ≤ subgraph.value.minDegree))
    (stage : (canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
      Target decideTarget handoffItems handoffSupport).ClassifiedStateStage Previous)
    (owner :
      let family := canonicalFamilyProducer profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
      family.FailureOwner (family.storedClassificationQuery.read stage) .f3) :
    False := by
  let family := canonicalFamilyProducer profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  have event := family.storedFailureEvent stage .f3 (by decide) owner
  obtain ⟨subgraph, minimumDegree⟩ :=
    Graph.Strategy.InterfaceReplacement.properSubgraphOfIntrinsic Target object _
      (f3BookkeepingOfStoredEvent owner.1.1.1.1 owner.1.1.1.2 CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
        event).compressible
  exact excluded subgraph minimumDegree


/-- A distinguishing context at a repeated F5 owner rebuilds `F2Valid` at the
later representative, contradicting the stored F5 classification.  Every input
is read from the active cold ledger: the ordered equal-state pair comes from
`canonicalRepeatedF5Witness_facts` (a projection of `storedRepeatedF5Witness`)
and the exhaustive (F2) failure comes from `storedAllF5`. -/
theorem repeatedResponseEqual
    {Previous : Type uPrevious}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport))
    (owner :
      let family := canonicalFamilyProducer profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
      family.RepeatedF5Owner (family.classifiedStateQuery.read view.previous)) :
    germTargetResponse owner.1.1.1.1.1 owner.1.1.1.1.2 Target decideTarget
        (canonicalRepeatedEarlier profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport view owner) =
      germTargetResponse owner.1.1.1.1.1 owner.1.1.1.1.2 Target decideTarget
        (canonicalRepeatedLater profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport view owner) := by
  classical
  let family := canonicalFamilyProducer profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  letI := family.stateFintype owner.1.1.1
  let repeated := family.storedRepeatedF5Witness view.previous owner
  have earlierEq :
      canonicalRepeatedEarlier profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport view owner =
        repeated.prefixTrace.schedule.get repeated.pair.1 := rfl
  have laterEq :
      canonicalRepeatedLater profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport view owner =
        repeated.prefixTrace.schedule.get repeated.pair.2 := rfl
  have traceSchedule :
      (family.traceAt owner.1.1.1).schedule =
        returnStageSchedule owner.1.1.1.1.1 owner.1.1.1.1.2 :=
    canonicalFamilyProducer_trace_schedule profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport owner.1.1.1
  have contractSchedule :
      (family.contractAt owner.1.1.1).schedule =
        returnStageSchedule owner.1.1.1.1.1 owner.1.1.1.1.2 := by
    exact (family.contractAt_schedule owner.1.1.1).trans traceSchedule
  have prefixMember : ∀ index : Fin repeated.prefixTrace.schedule.card,
      repeated.prefixTrace.schedule.get index ∈
        (returnStageSchedule owner.1.1.1.1.1 owner.1.1.1.1.2).values := by
    intro index
    rw [repeated.prefix_get_eq_original_get index]
    exact Enumeration.get_mem_values_of_eq traceSchedule
      (repeated.originalIndex index)
  by_contra different
  have storedFacts := canonicalRepeatedF5Witness_facts profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport view owner
  rw [earlierEq, laterEq] at different storedFacts
  have valid : F2Valid (object := object) (order := order) (profile := profile)
      owner.1.1.1.1.1 owner.1.1.1.1.2 Target decideTarget
      (repeated.prefixTrace.schedule.get repeated.pair.2)
      (repeated.prefixTrace.schedule.get repeated.pair.1) :=
    ⟨storedFacts.1, storedFacts.2,
      f2TargetDefect_of_response_ne owner.1.1.1.1.1 owner.1.1.1.1.2 Target
        decideTarget (repeated.prefixTrace.schedule.get repeated.pair.1)
        (repeated.prefixTrace.schedule.get repeated.pair.2) different⟩
  have scheduled :
      ULift.up (repeated.prefixTrace.schedule.get repeated.pair.1) ∈
        ((f2EventFamily (object := object) (order := order) (profile := profile)
          owner.1.1.1.1.1 owner.1.1.1.1.2 Target decideTarget).schedule
            (repeated.prefixTrace.schedule.get repeated.pair.2)).values :=
    (Enumeration.mem_map_values _ ULift.up ULift.up_injective
      (Classical.decEq _) _).mpr
      ⟨_, prefixMember _, rfl⟩
  have hit :
      (f2EventFamily (object := object) (order := order) (profile := profile)
        owner.1.1.1.1.1 owner.1.1.1.1.2 Target decideTarget).hit
        (repeated.prefixTrace.schedule.get repeated.pair.2)
        (returnEndpoint owner.1.1.1.1.1 owner.1.1.1.1.2
          (repeated.prefixTrace.schedule.get repeated.pair.2)) :=
    Core.Finite.Search.complete _ _ _
      ⟨ULift.up (repeated.prefixTrace.schedule.get repeated.pair.1),
        scheduled, valid⟩
  have allF5 := family.storedAllF5 view.previous owner.1
  have laterContractMember :
      repeated.prefixTrace.schedule.get repeated.pair.2 ∈
        (family.contractAt owner.1.1.1).schedule.values := by
    rw [contractSchedule]
    exact prefixMember _
  have noF2 := (allF5
    (repeated.prefixTrace.schedule.get repeated.pair.2)
    laterContractMember).2.1
  apply noF2
  exact (canonicalFamilyProducer_contract_f2Hit profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport owner.1.1.1
    (repeated.prefixTrace.schedule.get repeated.pair.2)).mpr hit

theorem repeatedNoTargetDefect
    {Previous : Type uPrevious}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport))
    (owner :
      let family := canonicalFamilyProducer profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
      family.RepeatedF5Owner (family.classifiedStateQuery.read view.previous)) :
    ¬ F2TargetDefect owner.1.1.1.1.1 owner.1.1.1.1.2 Target
        (canonicalRepeatedEarlier profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport view owner)
        (canonicalRepeatedLater profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport view owner) := by
  classical
  let family := canonicalFamilyProducer profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  letI := family.stateFintype owner.1.1.1
  let repeated := family.storedRepeatedF5Witness view.previous owner
  have earlierEq :
      canonicalRepeatedEarlier profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport view owner =
        repeated.prefixTrace.schedule.get repeated.pair.1 := rfl
  have laterEq :
      canonicalRepeatedLater profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport view owner =
        repeated.prefixTrace.schedule.get repeated.pair.2 := rfl
  have traceSchedule :
      (family.traceAt owner.1.1.1).schedule =
        returnStageSchedule owner.1.1.1.1.1 owner.1.1.1.1.2 :=
    canonicalFamilyProducer_trace_schedule profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport owner.1.1.1
  have contractSchedule :
      (family.contractAt owner.1.1.1).schedule =
        returnStageSchedule owner.1.1.1.1.1 owner.1.1.1.1.2 := by
    exact (family.contractAt_schedule owner.1.1.1).trans traceSchedule
  have prefixMember : ∀ index : Fin repeated.prefixTrace.schedule.card,
      repeated.prefixTrace.schedule.get index ∈
        (returnStageSchedule owner.1.1.1.1.1 owner.1.1.1.1.2).values := by
    intro index
    rw [repeated.prefix_get_eq_original_get index]
    exact Enumeration.get_mem_values_of_eq traceSchedule
      (repeated.originalIndex index)
  intro different
  have storedFacts := canonicalRepeatedF5Witness_facts profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport view owner
  rw [earlierEq, laterEq] at different storedFacts
  have valid : F2Valid (object := object) (order := order) (profile := profile)
      owner.1.1.1.1.1 owner.1.1.1.1.2 Target decideTarget
      (repeated.prefixTrace.schedule.get repeated.pair.2)
      (repeated.prefixTrace.schedule.get repeated.pair.1) :=
    ⟨storedFacts.1, storedFacts.2, different⟩
  have scheduled :
      ULift.up (repeated.prefixTrace.schedule.get repeated.pair.1) ∈
        ((f2EventFamily (object := object) (order := order) (profile := profile)
          owner.1.1.1.1.1 owner.1.1.1.1.2 Target decideTarget).schedule
            (repeated.prefixTrace.schedule.get repeated.pair.2)).values :=
    (Enumeration.mem_map_values _ ULift.up ULift.up_injective
      (Classical.decEq _) _).mpr
      ⟨_, prefixMember _, rfl⟩
  have hit :
      (f2EventFamily (object := object) (order := order) (profile := profile)
        owner.1.1.1.1.1 owner.1.1.1.1.2 Target decideTarget).hit
        (repeated.prefixTrace.schedule.get repeated.pair.2)
        (returnEndpoint owner.1.1.1.1.1 owner.1.1.1.1.2
          (repeated.prefixTrace.schedule.get repeated.pair.2)) :=
    Core.Finite.Search.complete _ _ _
      ⟨ULift.up (repeated.prefixTrace.schedule.get repeated.pair.1),
        scheduled, valid⟩
  have allF5 := family.storedAllF5 view.previous owner.1
  have laterContractMember :
      repeated.prefixTrace.schedule.get repeated.pair.2 ∈
        (family.contractAt owner.1.1.1).schedule.values := by
    rw [contractSchedule]
    exact prefixMember _
  have noF2 := (allF5
    (repeated.prefixTrace.schedule.get repeated.pair.2)
    laterContractMember).2.1
  apply noF2
  exact (canonicalFamilyProducer_contract_f2Hit profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport owner.1.1.1
    (repeated.prefixTrace.schedule.get repeated.pair.2)).mpr hit

/-- CT7's distinguishing terminal cannot occur at a repeated F5 owner.  This is
the exact `ResponseMismatch` coordinate CT7 would have to report; the previous
theorem rules it out. -/
theorem repeatedNoResponseMismatch
    {Previous : Type uPrevious}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport))
    (owner :
      let family := canonicalFamilyProducer profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
      family.RepeatedF5Owner (family.classifiedStateQuery.read view.previous))
    (coordinate : DeclaredColdCoordinate) :
    ¬ _root_.Hypostructure.CT7.ResponseMismatch
        (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
          cycleLengthDecidable Target decideTarget handoffItems handoffSupport)
        view ⟨owner.1.1, coordinate⟩ := by
  intro mismatch
  have representativeEq := canonicalF5Representatives_at_repeated profile
    CycleLengthOK cycleLengthDecidable Target decideTarget handoffItems handoffSupport
    view owner
  have equal := repeatedResponseEqual profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport view owner
  apply mismatch
  change
    germTargetResponse owner.1.1.1.1.1 owner.1.1.1.1.2 Target decideTarget
        ((canonicalF5Representatives profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport view).source owner.1.1) =
      germTargetResponse owner.1.1.1.1.1 owner.1.1.1.1.2 Target decideTarget
        ((canonicalF5Representatives profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport view).replacement owner.1.1)
  rw [representativeEq.1, representativeEq.2]
  exact equal.symm


theorem neutralCompressionFrameImpossible
    {threshold : Nat}
    (BranchState : FiniteObject.{u} → Type v)
    (baselineInvariant : FiniteObject.IsomorphismInvariant
      (fun candidate : FiniteObject.{u} => threshold ≤ candidate.minDegree))
    (Presentation : Type) (presentation : Presentation)
    (T : Core.Target (Graph.problemWithPresentation
      (fun candidate : FiniteObject.{u} => threshold ≤ candidate.minDegree)
      BranchState Presentation presentation))
    (targetInvariant : Core.TargetInvariant
      (Graph.isomorphismEquivalenceWithPresentation
        (fun candidate : FiniteObject.{u} => threshold ≤ candidate.minDegree)
        BranchState Presentation presentation baselineInvariant)
      T.Predicate)
    (ctx : Core.MinimalCounterexampleContext
      (Graph.problemWithPresentation
        (fun candidate : FiniteObject.{u} => threshold ≤ candidate.minDegree)
        BranchState Presentation presentation)
      T.Predicate
      (Graph.CanonicalProgress.progress
        (P := Graph.problemWithPresentation
          (fun candidate : FiniteObject.{u} => threshold ≤ candidate.minDegree)
          BranchState Presentation presentation)))
    (closure : Core.Strategy.InterfaceReplacement.ClosurePayload
      (Graph.Strategy.InterfaceReplacement.profileWithPresentation
        (fun candidate : FiniteObject.{u} => threshold ≤ candidate.minDegree)
        BranchState baselineInvariant Presentation presentation
        targetInvariant) ctx)
    (site : Graph.ProperBoundariedAtom ctx.G)
    (frame :
      (Graph.Strategy.InterfaceReplacement.profileWithPresentation
        (fun candidate : FiniteObject.{u} => threshold ≤ candidate.minDegree)
        BranchState baselineInvariant Presentation presentation
        targetInvariant).CompressionFrame ctx.G site)
    (contextUniversal :
      ∀ outside : Graph.OutsideContext site.decomposition.interface,
        T.Predicate (Graph.glue frame.replacement.atom outside) ↔
          T.Predicate (Graph.glue site.decomposition.piece outside)) :
    False :=
  closure.noNeutralCompressionFrame
    (Graph.Strategy.InterfaceReplacement.profileWithPresentation
      (fun candidate : FiniteObject.{u} => threshold ≤ candidate.minDegree)
      BranchState baselineInvariant Presentation presentation targetInvariant)
    site frame (fun outside _ _ => contextUniversal outside)

/-! ## (G3) The germ's boundary data is a projection of the stored corridor state

`def:cold-corridor-first-failure`, verbatim: for an initial segment `J` of the
corridor, `T(J)` is its *two active boundary interfaces*, and

  "Its cold corridor state is the finite two-boundary cut-state obtained from
   rho_{T(J)}^{ex}(J) by retaining exactly the boundary-degree profile, the two
   active boundary half-edges, the cold-window offsets met at the two
   interfaces, and the declared local coordinates of
   def:declared-coordinate-signature whose support is contained in the bounded
   active interface."

So the germ's boundary-degree profile is not a fact to establish: the corridor
state is *defined* to retain it, and `Graph.InducedPathCold.corridorState`
(`Graph/InducedPathCold.lean:1313`) is literally that tuple.  The stored
same-interface equality -- `F2Valid` / `F3Valid` second conjunct, and
`canonicalF5G3RepeatedFacts` for a repeated F5 owner -- therefore already
carries every boundary coordinate the local replacement compares.  These are
those projections and nothing else. -/

theorem corridorBoundaryDegree_eq_of_state_eq
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (earlier later : ReturnStage occurrence member)
    (stateEq : corridorState occurrence member earlier =
      corridorState occurrence member later) :
    corridorBoundaryDegree occurrence member earlier =
      corridorBoundaryDegree occurrence member later :=
  congrArg (fun state => state.2.1) stateEq

theorem corridorLocalAdjacency_eq_of_state_eq
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (earlier later : ReturnStage occurrence member)
    (stateEq : corridorState occurrence member earlier =
      corridorState occurrence member later) :
    corridorLocalAdjacency occurrence member earlier =
      corridorLocalAdjacency occurrence member later :=
  congrArg (fun state => state.2.2) stateEq

/-- Pointwise form at one corridor coordinate, in the shape
`BoundaryPiece.boundaryDegreeProfile` is compared in. -/
theorem corridorBoundaryDegree_apply_eq_of_state_eq
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (earlier later : ReturnStage occurrence member)
    (stateEq : corridorState occurrence member earlier =
      corridorState occurrence member later)
    (coordinate : Fin 4) :
    object.degree (corridorActiveVertex occurrence member earlier coordinate) =
      object.degree (corridorActiveVertex occurrence member later coordinate) :=
  congrArg Fin.val (congrFun
    (corridorBoundaryDegree_eq_of_state_eq occurrence member earlier later
      stateEq) coordinate)



end Hypostructure.Graph.Strategy.ColdBranchGermClosure
