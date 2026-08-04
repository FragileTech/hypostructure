import Hypostructure.Core.Strategy.Route8CarrierClosureSemantics
import Hypostructure.Core.Finite.EssentialCarrier
import Hypostructure.Graph.TypeARoute8Carriers
import Hypostructure.Graph.Strategy.SurplusAccounting
import Hypostructure.Graph.Strategy.Official.Features.SupportIncidenceLedger
import Hypostructure.Graph.Strategy.InterfaceReplacement
import Hypostructure.Graph.Response


namespace Hypostructure.Graph.Strategy.TypeARoute8Closure

open Hypostructure

universe uResidual uVertex

variable {Residual : Type uResidual}

/-! ## The indexed route-8 entries and their boundary incidences -/

/-- The ledger's own item carrier: an indexed route-8 entry is an item of the
inherited normalized support, which on the graph adapter is a vertex. -/
abbrev Entry (object : Residual → Graph.FiniteObject.{uVertex})
    (residual : Residual) : Type (max uResidual uVertex) :=
  ULift.{uResidual} (object residual).Vertex

/-- Decidable equality of indexed entries, from the object's own finite vertex
enumeration.  Nothing is decided classically.

It is registered as an instance so that every `Finset` operation below -- and
every *statement* mentioning one -- uses the object's own enumeration rather
than a locally introduced copy; two different decidability proofs for the same
carrier is exactly what makes a ledger reading fail to match the fact proved
beside it. -/
instance entryDecEq (object : Residual → Graph.FiniteObject.{uVertex})
    (residual : Residual) : DecidableEq (Entry object residual) := by
  letI : DecidableEq (object residual).Vertex := (object residual).vertices.decEq
  exact inferInstance

/-- The indexed entry schedule.  It is the vertex schedule lifted to the ledger
carrier; nothing is selected here, because `Active` is what
`def:typeA-route8-carriers` uses to pick out the `σ(X) = 0` part. -/
noncomputable def entrySchedule (object : Residual → Graph.FiniteObject.{uVertex})
    (residual : Residual) :
    Core.Finite.Enumeration (Entry object residual) :=
  (SurplusAccounting.vertices (object residual)).map ULift.up
    (fun _ _ equality => congrArg ULift.down equality)
    (entryDecEq object residual)

/-- **`def:typeA-route8-carriers`, collection membership.**  `𝒳` is *"a
collection of Type A supports whose saturated receivers survive only through
route 8"*, and *"since `σ(X) = 0`, every vertex of `X` has ambient degree 3"*.
Surviving only through route 8 is `def:typeA-true-route8-residual`: exits
`(4)`--`(7)` are absent at the saturated receiver. -/
def Active (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat)
    (ExitFour ExitFive ExitSix ExitSeven : Residual → Prop)
    (residual : Residual) (entry : Entry object residual) : Prop :=
  (object residual).degree entry.down = baselineDegree residual ∧
    ¬ ExitFour residual ∧ ¬ ExitFive residual ∧
      ¬ ExitSix residual ∧ ¬ ExitSeven residual

noncomputable def activeDecidable
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat)
    (ExitFour ExitFive ExitSix ExitSeven : Residual → Prop)
    (residual : Residual) (entry : Entry object residual) :
    Decidable
      (Active object baselineDegree ExitFour ExitFive ExitSix ExitSeven residual
        entry) :=
  Classical.propDecidable _

/-- The `σ(X) = 0` part, as a support the framework's incidence ledger reads. -/
noncomputable def activeSupport
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat) (residual : Residual) :
    Finset (object residual).Vertex :=
  letI : DecidableEq (object residual).Vertex :=
    (object residual).vertices.decEq
  letI : DecidablePred fun vertex : (object residual).Vertex =>
      (object residual).degree vertex = baselineDegree residual :=
    fun _ => Nat.decEq _ _
  (SurplusAccounting.vertices (object residual)).toFinset.filter
    fun vertex => (object residual).degree vertex = baselineDegree residual

/-- **`def:typeA-route8-carriers`, the ambient carrier.**  A witness `y` is a
boundary incidence of the entry `x` exactly when `y` is one of `x`'s *outside
neighbours* of the `σ(X) = 0` support, i.e. `xy ∈ E(G)` leaves `X` and
`(x, xy) ∈ ∂_E X`.

That set is not rebuilt here.  It is
`Official.Features.SupportIncidenceLedger.outsideNeighbors`, the same
per-vertex fibre whose total the framework identifies with the ledger's own
boundary-incidence count in `PackedWindowTokenLedger.boundary_count_exact`. -/
noncomputable def BoundaryCarrier
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat) (residual : Residual)
    (entry : Entry object residual) (witness : Entry object residual) : Prop :=
  letI : DecidableEq (object residual).Vertex :=
    (object residual).vertices.decEq
  witness.down ∈
    Official.Features.SupportIncidenceLedger.outsideNeighbors (object residual)
    (activeSupport object baselineDegree residual) entry.down

/-- Membership in the ledger's own outside-neighbour list is a list decision;
nothing is decided classically. -/
noncomputable def boundaryDecidable
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat) (residual : Residual)
    (entry witness : Entry object residual) :
    Decidable (BoundaryCarrier object baselineDegree residual entry witness) := by
  letI : DecidableEq (object residual).Vertex :=
    (object residual).vertices.decEq
  unfold BoundaryCarrier
  infer_instance

/-- `∂_E X` at one indexed entry, as the framework's own restricted schedule.
`Core.Finite.Enumeration.subtype` is what carves it out of the entry schedule;
no second list is built. -/
noncomputable def boundarySchedule
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat) (residual : Residual)
    (entry : Entry object residual) :
    Core.Finite.Enumeration
      { witness : Entry object residual //
          BoundaryCarrier object baselineDegree residual entry witness } :=
  (entrySchedule object residual).subtype
    (BoundaryCarrier object baselineDegree residual entry)
    (boundaryDecidable object baselineDegree residual entry)

noncomputable def boundaryCarriers
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat) (residual : Residual)
    (entry : Entry object residual) : Finset (Entry object residual) :=
  (boundarySchedule object baselineDegree residual entry).toFinset.image
    Subtype.val


/-- `∂B_u`, the single boundary every carrier restriction of one entry is read
at.  It is the framework's own cut boundary of the `σ(X) = 0` support --
`InterfaceReplacement.SupportAtom.boundary` -- and it does not vary with the
carrier set, which is exactly what lets `Response.ContextEquivalent` compare a
restriction with the unrestricted state. -/
noncomputable def carrierBoundary
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat) (residual : Residual)
    (_entry : Entry object residual) : Graph.Boundary.{uVertex} :=
  Graph.Strategy.InterfaceReplacement.SupportAtom.boundary (object residual)
    (activeSupport object baselineDegree residual)

noncomputable def carrierRestriction
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat) (residual : Residual)
    (entry : Entry object residual) (carriers : Finset (Entry object residual)) :
    Graph.BoundaryPiece (carrierBoundary object baselineDegree residual entry) :=
  letI : DecidableEq (object residual).Vertex :=
    (object residual).vertices.decEq
  letI : DecidablePred fun vertex : (object residual).Vertex =>
      ∀ neighbour ∈ Official.Features.SupportIncidenceLedger.outsideNeighbors
          (object residual) (activeSupport object baselineDegree residual)
          vertex,
        (ULift.up neighbour : Entry object residual) ∈ carriers :=
    fun _ => inferInstance
  Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece
    (object residual) (activeSupport object baselineDegree residual)
    ((activeSupport object baselineDegree residual).filter fun vertex =>
      ∀ neighbour ∈ Official.Features.SupportIncidenceLedger.outsideNeighbors
          (object residual) (activeSupport object baselineDegree residual)
          vertex,
        (ULift.up neighbour : Entry object residual) ∈ carriers)

noncomputable def carrierProfile
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat)
    (Target : Graph.FiniteObject.{uVertex} → Prop)
    (restriction : (residual : Residual) → (entry : Entry object residual) →
      Finset (Entry object residual) →
        Graph.BoundaryPiece (carrierBoundary object baselineDegree residual entry))
    (residual : Residual) (entry : Entry object residual) :
    Core.Finite.EssentialCarrier.Profile.{max uResidual uVertex} where
  Carrier := { witness : Entry object residual //
      BoundaryCarrier object baselineDegree residual entry witness }
  schedule := boundarySchedule object baselineDegree residual entry
  Complete := fun carriers =>
    Graph.Response.ContextEquivalent Target
      (restriction residual entry (carriers.image Subtype.val))
      (restriction residual entry
        (boundaryCarriers object baselineDegree residual entry))
  completeDecidable := fun _ => Classical.propDecidable _
  fullComplete := fun _ => Iff.rfl

/-- `𝒞_ess(ξ)`, the canonical carrier core, read back as a subset of the entry
schedule.  It is `EssentialCarrier.Profile.core` and nothing else. -/
noncomputable def essentialCarriers
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat)
    (Target : Graph.FiniteObject.{uVertex} → Prop)
    (restriction : (residual : Residual) → (entry : Entry object residual) →
      Finset (Entry object residual) →
        Graph.BoundaryPiece (carrierBoundary object baselineDegree residual entry))
    (residual : Residual) (entry : Entry object residual) :
    Finset (Entry object residual) :=
  (carrierProfile object baselineDegree Target restriction residual
    entry).core.image Subtype.val

/-- **`lem:typeA-essential-deletion-witness`, transported to the entry
schedule.**  Erasing an essential carrier destroys target-completeness.

The proof is `EssentialCarrier.Profile.erase_not_complete` plus the fact that
`Subtype.val` is injective, so erasing commutes with reading the core back. -/
theorem erase_essential_not_complete
    {object : Residual → Graph.FiniteObject.{uVertex}}
    {baselineDegree : Residual → Nat}
    {Target : Graph.FiniteObject.{uVertex} → Prop}
    {restriction : (residual : Residual) → (entry : Entry object residual) →
      Finset (Entry object residual) →
        Graph.BoundaryPiece (carrierBoundary object baselineDegree residual entry)}
    {residual : Residual} {entry carrier : Entry object residual}
    (member : carrier ∈
      essentialCarriers object baselineDegree Target restriction residual
        entry) :
    ¬ Graph.Response.ContextEquivalent Target
      (restriction residual entry
        ((essentialCarriers object baselineDegree Target restriction residual
          entry).erase carrier))
      (restriction residual entry
        (boundaryCarriers object baselineDegree residual entry)) := by
  haveI : DecidableEq (carrierProfile object baselineDegree Target
      restriction residual entry).Carrier :=
    inferInstanceAs (DecidableEq { witness : Entry object residual //
      BoundaryCarrier object baselineDegree residual entry witness })
  obtain ⟨core, coreMember, rfl⟩ := Finset.mem_image.mp member
  have witness :=
    (carrierProfile object baselineDegree Target restriction residual
      entry).erase_not_complete core coreMember
  simpa [carrierProfile, essentialCarriers,
    Finset.image_erase Subtype.val_injective] using witness

noncomputable def Supports
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat)
    (Target : Graph.FiniteObject.{uVertex} → Prop)
    (restriction : (residual : Residual) → (entry : Entry object residual) →
      Finset (Entry object residual) →
        Graph.BoundaryPiece (carrierBoundary object baselineDegree residual entry))
    (residual : Residual) (entry witness : Entry object residual) : Prop :=
  witness ∈
    essentialCarriers object baselineDegree Target restriction residual entry

/-- Membership in a finite carrier core is a `Finset` decision. -/
noncomputable def supportsDecidable
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat)
    (Target : Graph.FiniteObject.{uVertex} → Prop)
    (restriction : (residual : Residual) → (entry : Entry object residual) →
      Finset (Entry object residual) →
        Graph.BoundaryPiece (carrierBoundary object baselineDegree residual entry))
    (residual : Residual) (entry witness : Entry object residual) :
    Decidable
      (Supports object baselineDegree Target restriction residual entry
        witness) := by
  unfold Supports
  infer_instance

/-- Every indexed entry is scheduled: the entry schedule is the object's own
complete vertex enumeration lifted to the ledger carrier. -/
theorem mem_entrySchedule (object : Residual → Graph.FiniteObject.{uVertex})
    (residual : Residual) (entry : Entry object residual) :
    entry ∈ (entrySchedule object residual).values := by
  refine List.mem_map.mpr ⟨entry.down, ?_, rfl⟩
  exact (object residual).mem_orderedVertices entry.down

/-- **`α_𝒳(ξ) = 0`.**  CT5's deficit output is an active site whose whole
incoming fibre fails `Supports`, and `Supports` is membership in the entry's
canonical carrier core, so the core is empty. -/
theorem essentialCarriers_eq_empty_of_avoids
    {object : Residual → Graph.FiniteObject.{uVertex}}
    {baselineDegree : Residual → Nat}
    {Target : Graph.FiniteObject.{uVertex} → Prop}
    {restriction : (residual : Residual) → (entry : Entry object residual) →
      Finset (Entry object residual) →
        Graph.BoundaryPiece (carrierBoundary object baselineDegree residual entry)}
    {residual : Residual} {entry : Entry object residual}
    (avoids : Core.Finite.Search.Avoids (entrySchedule object residual)
      (Supports object baselineDegree Target restriction residual entry)) :
    essentialCarriers object baselineDegree Target restriction residual entry
      = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun witness member => ?_
  obtain ⟨index, selected⟩ :=
    (Core.Finite.Enumeration.mem_iff_exists_index (entrySchedule object residual)
      witness).mp (mem_entrySchedule object residual witness)
  exact avoids index (selected ▸ member)

/-- The tagged entry family `Ξ(𝒳)` privacy is evaluated in: the active
entries. -/
noncomputable def activeEntries (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat) (residual : Residual) :
    Finset (Entry object residual) :=
  letI : DecidablePred fun vertex : (object residual).Vertex =>
      (object residual).degree vertex = baselineDegree residual :=
    fun _ => Nat.decEq _ _
  (entrySchedule object residual).toFinset.filter
    fun entry => (object residual).degree entry.down = baselineDegree residual

/-- `π_𝒳(ξ)`, the number of private essential carriers: *"an essential carrier
for `ξ` is private for `ξ` inside `𝒳` if it is not essential for any other
indexed route-8 entry in the collection."*  This is that sentence as a
`Finset.filter`, over the framework's own carrier core. -/
noncomputable def privateCount
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat)
    (Target : Graph.FiniteObject.{uVertex} → Prop)
    (restriction : (residual : Residual) → (entry : Entry object residual) →
      Finset (Entry object residual) →
        Graph.BoundaryPiece (carrierBoundary object baselineDegree residual entry))
    (residual : Residual) (entry : Entry object residual) : Nat :=
  ((essentialCarriers object baselineDegree Target restriction residual
      entry).filter
    fun carrier => ∀ other ∈ activeEntries object baselineDegree residual,
      carrier ∈
          essentialCarriers object baselineDegree Target restriction residual
            other →
        other = entry).card

noncomputable def carrierSupply
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat) (residual : Residual) : Nat :=
  ∑ entry ∈ activeEntries object baselineDegree residual,
    (boundaryCarriers object baselineDegree residual entry).card

/-! ## Node `[123]`: the descent state

`DescentState residual load` is a finite active schedule together with the load
it is running under.  The bound is `≤`, not an equation: the measure is
`Finset.card`, and `Finset.card_erase_lt_of_mem` supplies the strict decrease
`CT12.Restoration.continue` asks for. -/

abbrev DescentState (object : Residual → Graph.FiniteObject.{uVertex})
    (residual : Residual) (load : Nat) : Type (max uResidual uVertex) :=
  { active : Finset (Entry object residual) // active.card ≤ load }

theorem no_deficitResidual
    {object : Residual → Graph.FiniteObject.{uVertex}}
    {baselineDegree : Residual → Nat}
    {Target : Graph.FiniteObject.{uVertex} → Prop}
    {restriction : (residual : Residual) → (entry : Entry object residual) →
      Finset (Entry object residual) →
        Graph.BoundaryPiece (carrierBoundary object baselineDegree residual entry)}
    {ExitFour ExitFive ExitSix ExitSeven : Residual → Prop}
    {residual : Residual}
    (collapse : ∀ entry : Entry object residual,
      (essentialCarriers object baselineDegree Target restriction residual
        entry).card ≤ 1 →
        ExitFour residual ∨ ExitFive residual ∨ ExitSix residual ∨
          ExitSeven residual)
    (hit : Core.Finite.Search.IndexedHit (entrySchedule object residual)
      (fun site =>
        Active object baselineDegree ExitFour ExitFive ExitSix ExitSeven residual
            site ∧
          Core.Finite.Search.Avoids (entrySchedule object residual)
            (Supports object baselineDegree Target restriction residual site))) :
    False := by
  obtain ⟨active, avoids⟩ := hit.holds
  have two :=
    TypeARoute8Carriers.two_le_alpha_of_trueRouteEight
      (collapse ((entrySchedule object residual).get hit.index))
      active.2.1 active.2.2.1 active.2.2.2.1 active.2.2.2.2
  rw [essentialCarriers_eq_empty_of_avoids avoids] at two
  simp at two

structure TierResidual (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat)
    (Target : Graph.FiniteObject.{uVertex} → Prop)
    (restriction : (residual : Residual) → (entry : Entry object residual) →
      Finset (Entry object residual) →
        Graph.BoundaryPiece (carrierBoundary object baselineDegree residual entry))
    (requiredPrivateCount : Residual → Nat) (ExitFour : Residual → Prop)
    (residual : Residual) : Type (max uResidual uVertex) where
  /-- The indexed entry the descent stopped at. -/
  entry : Entry object residual
  /-- **(T1)**: the entry belongs to the route-8 collection. -/
  indexed : entry ∈ activeEntries object baselineDegree residual
  /-- **(T2)**, `def:typeA-true-route8-residual`: exit `(4)` is absent. -/
  trueResidual : ¬ ExitFour residual
  /-- **(T3)**: the canonical carrier core is nontrivial. -/
  coreNontrivial : 2 ≤
    (essentialCarriers object baselineDegree Target restriction residual
      entry).card
  /-- **(T4)**: the entry is two-carrier in the private-carrier sense. -/
  twoCarrier :
    privateCount object baselineDegree Target restriction residual entry ≤
      requiredPrivateCount residual
  /-- **(T5)**: *"for every `c ∈ 𝒞_ess(ξ)`, the `c`-deletion witness of
  `lem:typeA-essential-deletion-witness` is part of the obstruction data"* --
  read through the two lemmas that consume it.
  `lem:typeA-two-carrier-deletion-canonical` puts the deletion quotient of a
  two-carrier entry in `𝒬₄(w)`, and `lem:typeA-carrier-deletion-exit` says that
  quotient is target-defective, which *is* exit `(4)`.  So the datum the package
  carries is the exit those two lemmas produce.

  The witness itself is never assumed: it is
  `erase_essential_not_complete` above, i.e. the framework's own
  `EssentialCarrier.Profile.erase_not_complete`, which holds for every element of
  the canonical core by construction. -/
  deletionExit : ∀ carrier ∈
    essentialCarriers object baselineDegree Target restriction residual entry,
    ExitFour residual

structure DemandResidual (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat) (discharge required : Residual → Nat)
    (residual : Residual) : Type where
  /-- **Node `[112]`**, `lem:typeA-route8-burden`: `α⁻¹·D_A ≤ N_basin`, with
  `D_A` the large-budget deficit read off this residual. -/
  burden :
    discharge residual *
        ((SurplusAccounting.vertices (object residual)).card -
          discharge residual * carrierSupply object baselineDegree residual) ≤
      (activeEntries object baselineDegree residual).card
  deficit :
    (SurplusAccounting.vertices (object residual)).card ≤
      discharge residual *
          ((SurplusAccounting.vertices (object residual)).card -
            discharge residual * carrierSupply object baselineDegree residual) +
        discharge residual * carrierSupply object baselineDegree residual
  /-- **Node `[120]`**, the private-carrier budget `req·N_basin ≤ def⁺(R)`. -/
  budget :
    required residual * (activeEntries object baselineDegree residual).card ≤
      carrierSupply object baselineDegree residual
  rate :
    (required residual * discharge residual + 1) *
        carrierSupply object baselineDegree residual <
      required residual * (SurplusAccounting.vertices (object residual)).card

theorem no_demandResidual
    {object : Residual → Graph.FiniteObject.{uVertex}}
    {baselineDegree discharge required : Residual → Nat}
    {residual : Residual}
    (dischargePos : 0 < discharge residual)
    (requiredPos : 0 < required residual)
    (payload : DemandResidual object baselineDegree discharge required residual) :
    False :=
  TypeARoute8Carriers.carrierBudgetContradiction dischargePos requiredPos
    payload.burden payload.deficit payload.budget payload.rate

def Peel (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat)
    (Target : Graph.FiniteObject.{uVertex} → Prop)
    (restriction : (residual : Residual) → (entry : Entry object residual) →
      Finset (Entry object residual) →
        Graph.BoundaryPiece (carrierBoundary object baselineDegree residual entry))
    (discharge requiredPrivateCount : Residual → Nat)
    (ExitFour : Residual → Prop)
    {residual : Residual} {load : Nat}
    (state : DescentState object residual (load + 1)) :
    Type (max uResidual uVertex) :=
  PSum
    (TierResidual object baselineDegree Target restriction
      requiredPrivateCount ExitFour residual)
    (PSum (ULift.{max uResidual uVertex}
        (DemandResidual object baselineDegree discharge requiredPrivateCount
          residual))
      (PSum { entry : Entry object residual // entry ∈ state.val }
        (PLift (state.val = ∅))))

/-! ## The registration -/

noncomputable def registration
    (object : Residual → Graph.FiniteObject.{uVertex})
    (baselineDegree : Residual → Nat)
    (requiredPrivateCount : Residual → Nat)
    (discharge : Residual → Nat)
    (dischargePos : ∀ residual, 0 < discharge residual)
    (requiredPos : ∀ residual, 0 < requiredPrivateCount residual)
    (ExitFour ExitFive ExitSix ExitSeven : Residual → Prop)
    (Target : Graph.FiniteObject.{uVertex} → Prop)
    (restriction : (residual : Residual) → (entry : Entry object residual) →
      Finset (Entry object residual) →
        Graph.BoundaryPiece (carrierBoundary object baselineDegree residual entry))
    (collapse : Option (PLift (∀ (residual : Residual)
      (entry : Entry object residual),
      (essentialCarriers object baselineDegree Target restriction residual
        entry).card ≤ 1 →
        ExitFour residual ∨ ExitFive residual ∨ ExitSix residual ∨
          ExitSeven residual)))
    :
    Core.Strategy.Route8CarrierClosure.Registration.{
      uResidual, max uResidual uVertex, 0}
      Residual (Entry object) where
  budget := SurplusAccounting.countingBudget
  Witness := fun residual _ => Entry object residual
  family := fun residual =>
    { indices := entrySchedule object residual
      fibres := fun _ => entrySchedule object residual }
  Active := Active object baselineDegree ExitFour ExitFive ExitSix ExitSeven
  Supports := Supports object baselineDegree Target restriction
  witnessContribution := fun _ _ _ => SurplusAccounting.countingBudget.ceiling 1
  required := fun _ => SurplusAccounting.countingBudget.zero
  -- Inclusion-minimality of the canonical carrier core: outside `C_ess(ξ)`
  -- every carrier is noncore, so the core itself has no slack.
  capacity := fun _ => SurplusAccounting.countingBudget.zero
  activeDecidable := activeDecidable object baselineDegree ExitFour ExitFive
    ExitSix ExitSeven
  supportsDecidable := supportsDecidable object baselineDegree Target
    restriction
  resourceLEDecidable := Nat.decLe
  Label := fun residual => Entry object residual
  members := entrySchedule object
  memberLowerMass := fun residual _ => requiredPrivateCount residual
  memberCapacity := fun residual entry =>
    some (privateCount object baselineDegree Target restriction residual
      entry)
  memberLabel := fun _ entry => some entry
  labelDecidableEq := entryDecEq object
  State := DescentState object
  Peeled := fun state =>
    Peel object baselineDegree Target restriction discharge
      requiredPrivateCount ExitFour state
  DemandResidual := fun residual =>
    ULift.{max uResidual uVertex}
      (DemandResidual object baselineDegree discharge requiredPrivateCount
        residual)
  TierResidual := TierResidual object baselineDegree Target restriction
    requiredPrivateCount ExitFour
  peel := fun {residual} {_load} state => by
    classical
    by_cases nonempty : state.val.Nonempty
    · by_cases collision :
        Nonempty (DemandResidual object baselineDegree discharge
          requiredPrivateCount residual)
      · exact .inr (.inl ⟨collision.some⟩)
      · by_cases peels : ExitFour residual
        · -- exit (4) occurs: peel that load, `Λ₄` decreases.
          exact .inr (.inr (.inl ⟨nonempty.choose, nonempty.choose_spec⟩))
        · -- the terminal non-peeling case; it enters node `[124]` exactly when
          -- the entry is the two-carrier obstruction of
          -- `def:typeA-terminal-two-carrier`.
          by_cases terminal :
            nonempty.choose ∈ activeEntries object baselineDegree residual ∧
              2 ≤ (essentialCarriers object baselineDegree Target
                    restriction residual nonempty.choose).card ∧
                privateCount object baselineDegree Target restriction
                    residual nonempty.choose ≤
                  requiredPrivateCount residual ∧
                  ∀ carrier ∈ essentialCarriers object baselineDegree Target
                      restriction residual nonempty.choose,
                    ExitFour residual
          · exact .inl ⟨nonempty.choose, terminal.1, peels, terminal.2.1,
              terminal.2.2.1, terminal.2.2.2⟩
          · exact .inr (.inr (.inl ⟨nonempty.choose, nonempty.choose_spec⟩))
    · exact .inr (.inr (.inr
        ⟨Finset.not_nonempty_iff_eq_empty.mp nonempty⟩))
  restorations := fun {residual} {load} {state} peeled =>
    match peeled with
    | .inl terminal => { first := .tier terminal }
    | .inr (.inl collision) => { first := .demand collision }
    | .inr (.inr (.inl step)) =>
        { first := .continue (state.val.erase step.val).card
            ⟨state.val.erase step.val, Nat.le_refl _⟩
            (Nat.lt_of_lt_of_le
              (Finset.card_erase_lt_of_mem step.property) state.property) }
    | .inr (.inr (.inr exhausted)) =>
        { first := .continue load ⟨state.val, by
            rw [exhausted.down]; simp⟩ (Nat.lt_succ_self load) }
  initialLoad := fun residual =>
    (activeEntries object baselineDegree residual).card
  initialState := fun residual =>
    ⟨activeEntries object baselineDegree residual, Nat.le_refl _⟩
  tierImpossible := some ⟨fun _residual payload =>
    TypeARoute8Carriers.no_terminalTwoCarrier
      payload.coreNontrivial payload.deletionExit payload.trueResidual⟩
  capacityImpossible := some ⟨fun residual payload =>
    no_demandResidual (dischargePos residual) (requiredPos residual)
      payload.down⟩
  deficitImpossible := collapse.map fun small =>
    ⟨fun residual => no_deficitResidual (small.down residual)⟩
  requiredAffordable := some ⟨fun _ => SurplusAccounting.countingBudget.leRefl _⟩
  memberCapacityTotal := some ⟨fun _ _ => Option.some_ne_none _⟩
  memberLabelTotal := some ⟨fun _ _ => Option.some_ne_none _⟩

end Hypostructure.Graph.Strategy.TypeARoute8Closure
