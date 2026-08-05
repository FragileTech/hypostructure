import Hypostructure.Graph.ReceiverExhaustion
import Hypostructure.Graph.Strategy.ColdBranchGermClosure

/-!
# Cold-branch first-failure routing on the classified cold ledger stage

`Hypostructure.Graph.Strategy.ColdBranchGermClosure` closes the three arms of
`lem:cold-corridor-first-failure` that end in a contradiction or in a proved
neutrality: (F1) is an ambient dyadic cycle, (F3) is a forbidden compression,
and the repeat subcase of (F5) is neutral.  The remaining arms are routed into
ledgers that already exist.

* `lem:cold-corridor-first-failure` (ii) -- "case (F2) is a target-defective
  quotient, hence belongs to the sparse exit or to the exit-(4) ledger";
* `lem:cold-corridor-first-failure` (iv) -- "case (F4) is an already named
  Type B or route-8 handoff", i.e. "the charge is transferred to the already
  existing Type B or route-8 ledger";
* `lem:cold-corridor-first-failure` (v), terminal subcase -- "the whole
  corridor has bounded size and two boundary interfaces ... the support
  carries two same-interface representatives ... Thus it is a cold bounded
  germ", which is the residual consumed by `lem:cold-germ-extraction`.

Each arm is expressed as the framework's existing disposition vocabulary:

* the exact `Graph.Response.TargetDefect` already named by
  `Graph.InducedPathCold.F2TargetDefect`, read off the stored classified cold
  entry;
* the exact member of the *incoming* handoff schedule, injected into
  `Graph.ReceiverExhaustion.Exit.handoff` -- the same slot used by
  `Graph.DecoratedFan.toReceiverHandoff`;
* the exact `Q_cold` state bound plus the CT7 neutrality already proved by
  `canonicalF5G3Neutral`.

An (F2) hit is by construction `¬ TargetComplete` -- two prefixes whose target
responses *differ* at one context -- so it can never be discharged through
`Uncompressible.noCompression`, which forbids a *target-complete* compression.
That is why (ii) is a transport and not a closure.

Every hypothesis is a *ledger read*.  An (F2) or (F4) consumer takes only a
`FailureOwner` of the classification **stored** in the active cold stage; a
terminal-(F5) consumer takes only a `TerminalF5Owner` of the **stored**
bounded outcomes.  Those subtypes are inhabitable exactly when the ledger
already recorded the corresponding outcome, so none of the manuscript's
conclusions is accepted as data.  This file declares no `structure` and no
`inductive`.
-/

namespace Hypostructure.Graph.Strategy.ColdBranchFailureRouting

open Hypostructure
open Hypostructure.Core.Finite
open Hypostructure.Graph.InducedPathCold

universe u uAmbient uBranch uData uPrevious

set_option maxHeartbeats 0

/-! ## (F2) The stored first-failure event is a target-defective quotient

`lem:cold-corridor-first-failure` (ii).  The (F2) owner selected by the stored
partition carries two prefixes with the same displayed cold corridor state but
different exact target response against one compatible outside context.  That
is literally a target defect for the two same-boundary pieces, which is the
sparse-exit / exit-(4) ledger entry; `def:surviving-cold-branch` (ii)--(iii) is
what later discards it.  Nothing here manufactures a peel schedule, a routed
load, or a charge update. -/

/-- The stored (F2) event of one owner in the active cold ledger entry.  This
is `storedFailureEvent` at `.f2`; no corridor search is rerun. -/
noncomputable def storedF2Event
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
      family.FailureOwner (family.storedClassificationQuery stage) .f2) :
    Core.Finite.ColdCorridor.Contract.EventWitness
      (canonicalFirstFailurePresentation owner.1.1.1.1 owner.1.1.1.2
        CycleLengthOK cycleLengthDecidable Target decideTarget
        handoffItems handoffSupport).coreContract .f2 :=
  (canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable Target
      decideTarget handoffItems handoffSupport).storedFailureEvent stage .f2 (by decide)
    owner

/-- Complete Graph bookkeeping of that same stored (F2) event: the earlier
prefix, the literal distinguishing context support, the strict prefix order,
the displayed-state equality, and the typed target defect.  Every field is a
projection of the one stored hit. -/
noncomputable def storedF2Bookkeeping
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
      family.FailureOwner (family.storedClassificationQuery stage) .f2) :
    F2Bookkeeping (object := object) (order := order) (profile := profile)
      owner.1.1.1.1 owner.1.1.1.2 Target
      (storedF2Event profile CycleLengthOK cycleLengthDecidable Target
        decideTarget handoffItems handoffSupport stage owner).item :=
  f2BookkeepingOfStoredEvent owner.1.1.1.1 owner.1.1.1.2 CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
    (storedF2Event profile CycleLengthOK cycleLengthDecidable Target
      decideTarget handoffItems handoffSupport stage owner)

/-- Manuscript `lem:cold-corridor-first-failure` (ii).  The stored (F2) owner
yields the exact `Graph.Response.TargetDefect` of the two same-interface
representatives of its own germ. -/
theorem storedF2TargetDefect
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
      family.FailureOwner (family.storedClassificationQuery stage) .f2) :
    let bookkeeping := storedF2Bookkeeping profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport stage owner
    F2TargetDefect owner.1.1.1.1 owner.1.1.1.2 Target
      bookkeeping.earlier
      (storedF2Event profile CycleLengthOK cycleLengthDecidable Target
        decideTarget handoffItems handoffSupport stage owner).item :=
  (storedF2Bookkeeping profile CycleLengthOK cycleLengthDecidable Target
    decideTarget handoffItems handoffSupport stage owner).defect

/-- The two pieces of that defect are genuinely same-interface: the earlier
prefix is strictly earlier in the corridor order and its displayed cold
corridor state is equal.  This is the `def:cold-corridor-first-failure` (F2)
side condition, read off the same stored hit. -/
theorem storedF2SameInterface
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
      family.FailureOwner (family.storedClassificationQuery stage) .f2) :
    let bookkeeping := storedF2Bookkeeping profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport stage owner
    let later := (storedF2Event profile CycleLengthOK cycleLengthDecidable
      Target decideTarget handoffItems handoffSupport stage owner).item
    bookkeeping.earlier.1 < later.1 ∧
      corridorState (object := object) (order := order) (profile := profile)
          owner.1.1.1.1 owner.1.1.1.2 bookkeeping.earlier =
        corridorState (object := object) (order := order) (profile := profile)
          owner.1.1.1.1 owner.1.1.1.2 later :=
  ⟨(storedF2Bookkeeping profile CycleLengthOK cycleLengthDecidable Target
      decideTarget handoffItems handoffSupport stage owner).earlier_before,
    (storedF2Bookkeeping profile CycleLengthOK cycleLengthDecidable Target
      decideTarget handoffItems handoffSupport stage owner).state_eq⟩

/-! ## (F4) The stored first-failure event is an already named handoff

`lem:cold-corridor-first-failure` (iv).  The (F4) event family scans exactly
the *incoming* handoff **item** schedule `handoffItems`, which is a
residual-owned query on the predecessor stage, and reads each item's carrier
through the producer's own `handoffSupport` decoding.  A stored (F4) hit is
therefore literally the statement that the corridor entered the carrier of one
already recorded Type B or route-8 producer item, and the item itself -- not a
deduplicated vertex set that has forgotten which item it came from -- is what
the leaf carries out. -/

/-- The stored (F4) event of one owner in the active cold ledger entry. -/
noncomputable def storedF4Event
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
      family.FailureOwner (family.storedClassificationQuery stage) .f4) :
    Core.Finite.ColdCorridor.Contract.EventWitness
      (canonicalFirstFailurePresentation owner.1.1.1.1 owner.1.1.1.2
        CycleLengthOK cycleLengthDecidable Target decideTarget
        handoffItems handoffSupport).coreContract .f4 :=
  (canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable Target
      decideTarget handoffItems handoffSupport).storedFailureEvent stage .f4 (by decide)
    owner

/-- Manuscript `lem:cold-corridor-first-failure` (iv).  The stored (F4) owner
returns the exact member of the incoming handoff schedule that the corridor
entered, together with the endpoint incidence witnessing the entry.  Both
components are projections of the one stored hit, so this cannot name a
support that was not already on the predecessor ledger. -/
noncomputable def storedF4HandoffEntry
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
      family.FailureOwner (family.storedClassificationQuery stage) .f4) :
    {item : Handoff //
      item ∈ handoffItems.values ∧
        returnEndpoint owner.1.1.1.1 owner.1.1.1.2
          (storedF4Event profile CycleLengthOK cycleLengthDecidable Target
            decideTarget handoffItems handoffSupport stage owner).item ∈
          handoffSupport item} :=
  f4EntryOfStoredEvent owner.1.1.1.1 owner.1.1.1.2 CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
    (storedF4Event profile CycleLengthOK cycleLengthDecidable Target
      decideTarget handoffItems handoffSupport stage owner)

/-- The entered support is a member of the incoming handoff schedule.  This is
the "already named" half of `lem:cold-corridor-first-failure` (iv). -/
theorem storedF4EntryMemberOfIncomingLedger
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
      family.FailureOwner (family.storedClassificationQuery stage) .f4) :
    (storedF4HandoffEntry profile CycleLengthOK cycleLengthDecidable Target
      decideTarget handoffItems handoffSupport stage owner).1 ∈
      handoffItems.values :=
  (storedF4HandoffEntry profile CycleLengthOK cycleLengthDecidable Target
    decideTarget handoffItems handoffSupport stage owner).2.1

/-- The corridor really enters that support: its return endpoint at the stored
event stage lies in it. -/
theorem storedF4EntryEndpointIncidence
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
      family.FailureOwner (family.storedClassificationQuery stage) .f4) :
    returnEndpoint owner.1.1.1.1 owner.1.1.1.2
        (storedF4Event profile CycleLengthOK cycleLengthDecidable Target
          decideTarget handoffItems handoffSupport stage owner).item ∈
      handoffSupport (storedF4HandoffEntry profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
        stage owner).1 :=
  (storedF4HandoffEntry profile CycleLengthOK cycleLengthDecidable Target
    decideTarget handoffItems handoffSupport stage owner).2.2

/-- Manuscript `def:cold-corridor-first-failure` (F4): "the corridor first
enters a declared Type B handoff envelope or the route-8 carrier support
**already recorded in the branch state**".

So an (F4) owner cannot exist unless that branch state records a carrier.  A
branch on which no homogeneous bottleneck ran carries the empty schedule --
`Core/Strategy/Dag.lean:6501` passes `Enumeration.empty` in exactly that case
-- and there the stored (F4) partition is uninhabited.  This is the framework
form of "the corridor would have to be on the structured Type B route to
enter its envelope": the incoming ledger *is* the branch condition, and
`storedF4EntryMemberOfIncomingLedger` is the leaf's own membership in it. -/
theorem storedF4Impossible_of_emptyHandoff
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
    (empty : handoffItems.values = [])
    (stage : (canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
      Target decideTarget handoffItems handoffSupport).ClassifiedStateStage Previous)
    (owner :
      let family := canonicalFamilyProducer profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
      family.FailureOwner (family.storedClassificationQuery stage) .f4) :
    False := by
  have recorded := storedF4EntryMemberOfIncomingLedger profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport stage owner
  exact (List.eq_nil_iff_forall_not_mem.mp empty) _ recorded

/-- Inject the (F4) entry into the established handoff exit -- the same
`Exit.handoff` slot used by `Graph.DecoratedFan.toReceiverHandoff`.  The
carried datum is the already-recorded support and its entry proof, so the
charge is transferred to the existing Type B / route-8 ledger rather than
closed here. -/
def f4ToReceiverHandoff
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    {CycleLengthOK : Nat → Prop}
    {interface : Graph.ReceiverExhaustion.TargetInterface P T CycleLengthOK}
    {Step Residual : Core.Strategy.ProblemInput P → Type u}
    {input : Core.Strategy.ProblemInput P}
    {object : FiniteObject.{u}}
    {Handoff : Type u}
    {handoffItems : Core.Finite.Enumeration Handoff}
    {handoffSupport : Handoff → Finset object.Vertex}
    {endpoint : object.Vertex}
    (entry : {item : Handoff //
      item ∈ handoffItems.values ∧ endpoint ∈ handoffSupport item}) :
    Graph.ReceiverExhaustion.Exit interface Step
      (fun _ => {item : Handoff //
        item ∈ handoffItems.values ∧ endpoint ∈ handoffSupport item})
      Residual input :=
  .handoff entry

/-! ## (F5, terminal subcase) The stored bounded outcome is a cold bounded germ

`lem:cold-corridor-first-failure` (v), terminal subcase: "the whole corridor
has bounded size and two boundary interfaces ... the support carries two
same-interface representatives ... Thus it is a cold bounded germ".  That is a
typed residual feeding `lem:cold-germ-extraction`, not a closure. -/

/-- On a terminal owner selected by the stored terminal-F5 query, CT7's two
representatives are exactly the last and first stages of that same stored
terminal corridor.  This is the terminal counterpart of
`canonicalF5Representatives_at_repeated`; no stage is selected a second time
and no bounded-outcome decision is rerun. -/
theorem canonicalF5Representatives_at_terminal
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
      family.TerminalF5Owner (family.classifiedStateQuery view.previous)) :
    let schedule := returnStageSchedule owner.1.1.1.1.1 owner.1.1.1.1.2
    let nonempty : schedule.values ≠ [] :=
      returnStageSchedule_nonempty owner.1.1.1.1.1 owner.1.1.1.1.2
    let first : Fin schedule.card :=
      ⟨0, Nat.pos_of_ne_zero fun zero =>
        nonempty (List.length_eq_zero_iff.mp (by
          simpa [Core.Finite.Enumeration.card] using zero))⟩
    let last : Fin schedule.card :=
      ⟨schedule.card - 1, Nat.sub_lt
        (Nat.pos_of_ne_zero fun zero =>
          nonempty (List.length_eq_zero_iff.mp (by
            simpa [Core.Finite.Enumeration.card] using zero)))
        Nat.zero_lt_one⟩
    let representatives := canonicalF5Representatives profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport view
    representatives.source owner.1.1 = schedule.get last ∧
      representatives.replacement owner.1.1 = schedule.get first := by
  dsimp only
  let family := canonicalFamilyProducer profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  letI := family.stateFintype owner.1.1.1
  have selected : Core.Finite.ColdCorridor.Contract.Classification.IsFailure
      (family.contractAt owner.1.1.1)
      ((family.storedClassificationQuery view.previous).classify
        owner.1.1) .f5 := owner.1.2
  unfold canonicalF5Representatives
  dsimp only
  unfold canonicalF5RepresentativePair
  rw [dif_pos selected]
  let outcome := family.storedF5BoundedOutcome view.previous owner.1
  have terminalSelected : outcome.IsTerminal := owner.2
  have selected_eq : selected = owner.1.2 := Subsingleton.elim _ _
  cases selected_eq
  let traceNonempty : (family.traceAt owner.1.1.1).schedule.values ≠ [] := by
    rw [canonicalFamilyProducer_trace_schedule profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport owner.1.1.1]
    exact returnStageSchedule_nonempty owner.1.1.1.1.1 owner.1.1.1.1.2
  let schedule := returnStageSchedule owner.1.1.1.1.1 owner.1.1.1.1.2
  let scheduleNonempty : schedule.values ≠ [] :=
    returnStageSchedule_nonempty owner.1.1.1.1.1 owner.1.1.1.1.2
  let first : Fin schedule.card :=
    ⟨0, Nat.pos_of_ne_zero fun zero =>
      scheduleNonempty (List.length_eq_zero_iff.mp (by
        simpa [Core.Finite.Enumeration.card] using zero))⟩
  let last : Fin schedule.card :=
    ⟨schedule.card - 1, Nat.sub_lt
      (Nat.pos_of_ne_zero fun zero =>
        scheduleNonempty (List.length_eq_zero_iff.mp (by
          simpa [Core.Finite.Enumeration.card] using zero)))
      Nat.zero_lt_one⟩
  let traceFirst : Fin (family.traceAt owner.1.1.1).schedule.card :=
    ⟨0, Nat.pos_of_ne_zero fun zero =>
      traceNonempty (List.length_eq_zero_iff.mp (by
        simpa [Core.Finite.Enumeration.card] using zero))⟩
  let traceLast : Fin (family.traceAt owner.1.1.1).schedule.card :=
    ⟨(family.traceAt owner.1.1.1).schedule.card - 1, Nat.sub_lt
      (Nat.pos_of_ne_zero fun zero =>
        traceNonempty (List.length_eq_zero_iff.mp (by
          simpa [Core.Finite.Enumeration.card] using zero)))
      Nat.zero_lt_one⟩
  let scheduleEq : (family.traceAt owner.1.1.1).schedule = schedule :=
    canonicalFamilyProducer_trace_schedule profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport owner.1.1.1
  have firstCast : Enumeration.castIndex scheduleEq traceFirst = first := by
    apply Fin.ext
    rfl
  have lastCast : Enumeration.castIndex scheduleEq traceLast = last := by
    apply Fin.ext
    exact congrArg (fun card => card - 1)
      (congrArg Enumeration.card scheduleEq)
  have firstGet :
      (family.traceAt owner.1.1.1).schedule.get traceFirst =
        schedule.get first := by
    calc
      (family.traceAt owner.1.1.1).schedule.get traceFirst =
          schedule.get (Enumeration.castIndex scheduleEq traceFirst) :=
        (Enumeration.get_castIndex scheduleEq traceFirst).symm
      _ = schedule.get first := congrArg schedule.get firstCast
  have lastGet :
      (family.traceAt owner.1.1.1).schedule.get traceLast =
        schedule.get last := by
    calc
      (family.traceAt owner.1.1.1).schedule.get traceLast =
          schedule.get (Enumeration.castIndex scheduleEq traceLast) :=
        (Enumeration.get_castIndex scheduleEq traceLast).symm
      _ = schedule.get last := congrArg schedule.get lastCast
  have terminalFacts := boundedOutcomeRepresentatives_of_terminal
    owner.1.1.1.1.1 owner.1.1.1.1.2 (family.traceAt owner.1.1.1)
    traceNonempty outcome terminalSelected
  dsimp only at terminalFacts
  change
    (boundedOutcomeRepresentatives owner.1.1.1.1.1 owner.1.1.1.1.2
        (family.traceAt owner.1.1.1) traceNonempty outcome).source =
        schedule.get last ∧
      (boundedOutcomeRepresentatives owner.1.1.1.1.1 owner.1.1.1.1.2
        (family.traceAt owner.1.1.1) traceNonempty outcome).replacement =
        schedule.get first
  exact ⟨terminalFacts.1.trans lastGet, terminalFacts.2.trans firstGet⟩

/-- The `Q_cold` bound of `def:cold-corridor-first-failure`: a terminal cold
corridor reads at most `Fintype.card (CorridorState object order)` stages.
This is `storedTerminalF5Bound` transported along the definitional identity
`traceAt owner |>.schedule = returnStageSchedule ...`. -/
theorem storedTerminalF5ScheduleBound
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
      family.TerminalF5Owner (family.classifiedStateQuery stage)) :
    (returnStageSchedule owner.1.1.1.1.1 owner.1.1.1.1.2).card ≤
      Fintype.card (CorridorState object order) := by
  have bound :=
    (canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable Target
      decideTarget handoffItems handoffSupport).storedTerminalF5Bound stage owner
  rw [canonicalFamilyProducer_trace_schedule profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport owner.1.1.1] at bound
  exact bound

/-- Manuscript `lem:cold-corridor-first-failure` (v), terminal subcase.  The
stored terminal owner supplies exactly the two facts that make its corridor a
cold bounded germ: the `Q_cold` state bound, and the fact that its two stored
representatives -- the last and first stages of that same corridor, as
same-interface representatives of the one germ -- have equal exact target
response.  The second fact is CT7's already-proved neutrality
(`canonicalF5G3Neutral`) evaluated at this owner; no response is recomputed.

This is the honest disposition of the terminal arm: a typed bounded-germ
residual consumed by `lem:cold-germ-extraction`.  It is deliberately not a
closure. -/
theorem storedTerminalF5GermFacts
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
    (certificate : _root_.Hypostructure.CT7.NeutralityCertificate
      (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport) view)
    (owner :
      let family := canonicalFamilyProducer profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
      family.TerminalF5Owner (family.classifiedStateQuery view.previous)) :
    let representatives : Core.Response.Representatives
        (CanonicalColdRepresentative profile) :=
      (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport)
        |>.representativesAt view
    (returnStageSchedule owner.1.1.1.1.1 owner.1.1.1.1.2).card ≤
        Fintype.card (CorridorState object order) ∧
      germTargetResponse owner.1.1.1.1.1 owner.1.1.1.1.2 Target decideTarget
          (representatives.source owner.1.1) =
        germTargetResponse owner.1.1.1.1.1 owner.1.1.1.1.2 Target decideTarget
          (representatives.replacement owner.1.1) := by
  dsimp only
  refine ⟨storedTerminalF5ScheduleBound profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport view.previous
    owner, ?_⟩
  exact canonicalF5G3Neutral profile CycleLengthOK cycleLengthDecidable Target
    decideTarget handoffItems handoffSupport view certificate ⟨owner.1.1, Sum.inl 0⟩

end Hypostructure.Graph.Strategy.ColdBranchFailureRouting
