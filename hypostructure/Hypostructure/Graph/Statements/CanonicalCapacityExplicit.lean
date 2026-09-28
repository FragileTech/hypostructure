import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.Contracts.SurplusPair.PairSchedule
import Hypostructure.Graph.Contracts.SurplusPair.Activation
import Hypostructure.Graph.Contracts.TypeB.OpenPort

/-!
# Statements: G's canonical capacity presentation, made explicit

The capacity presentation `𝔗_cap` of `def:capacity-token-ledger` built from an
`ActiveSurplusDemands` proof, the node-`[19]` packing and G's avoidance
(`explicitCapacity`); the free side `|Π_free|` of its canonical charge
(`freeCount`); and the canonical object ledger at a presentation, whose entropy
budget is that free side (`canonicalObjectLedgerAt`).  No choice beyond the
presentation's own canonical objects.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- The recorded blocker activation of `def:capacity-token-ledger` at the
active family: `Θ` on G's full pair schedule. -/
noncomputable abbrev explicitActivation
    (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold) :
    object.DemandActivation object.PairCoordinate (object.Vertex × object.Vertex) :=
  Graph.recordSparsePairDEBlockers
    (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
    (LengthOK := data.LengthOK)
    (Graph.pairResponseActivation active)
    (object.portPairSchedule data.threshold)

/-- Every declared canonical blocker of the recorded activation has its
primitive carrier (copied from `capacityTokenLedger_of_pairLedger`, with the
blocker-route input replaced by the connectedness it was used for). -/
theorem explicit_carrierComplete
    (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (graphConnected : object.graph.Connected) :
    ∀ pair ∈ object.portPairSchedule data.threshold,
      ∀ blocker ∈ (explicitActivation active).blockers pair,
        (Graph.FiniteObject.Blocker.carrier object data.threshold
          (by
            letI := object.vertices.decEq
            exact Graph.DeclaredSignature.Coordinate.support)
          (explicitActivation active).chordPort blocker).isSome := by
  classical
  let activation := explicitActivation active
  have connectedOn :
      Graph.SupportComponents.Connected.ConnectedOn
        object object.vertexFinset :=
    Graph.SupportComponents.Connected.connectedOn_vertexFinset
      object graphConnected
  letI : DecidableEq object.Vertex := Classical.decEq _
  have pairCoordinateNonempty
      (pair : Finset
        (object.Vertex × object.Vertex)) :
      (Graph.DeclaredSignature.Coordinate.support
        (Graph.FiniteObject.DemandActivation.pairCoordinate pair
          (((Graph.pairResponseActivation active).pairSupport pair).getD
            ∅))).Nonempty := by
    have pairSupportSome :=
      Graph.FiniteObject.DemandActivation.pairSupport_isSome_of_connected
        (Graph.pairResponseActivation active) pair connectedOn
    obtain ⟨pairSupport, pairSupportEq⟩ :=
      Option.isSome_iff_exists.mp pairSupportSome
    have pairSupportNonempty : pairSupport.Nonempty :=
      (Graph.FiniteObject.DemandActivation.pairSupport_mem_candidates
        pairSupportEq).2.1
    change (((Graph.pairResponseActivation active).pairSupport pair).getD
      ∅).Nonempty
    rw [pairSupportEq]
    exact pairSupportNonempty
  let presentation : object.CarrierPresentation
      object.PairCoordinate
      (object.Vertex ×
        object.Vertex) := {
    coordinateSupport := by
      letI := object.vertices.decEq
      exact Graph.DeclaredSignature.Coordinate.support
    chordEnds := Graph.pairResponseChordEnds active
    chordPort := id }
  have carried : ∀ pair ∈
      object.portPairSchedule data.threshold,
      ∀ blocker ∈ activation.blockers pair,
        (Graph.FiniteObject.Blocker.carrier object
          data.threshold presentation.coordinateSupport
          presentation.chordPort blocker).isSome := by
    classical
    intro pair _pairMem blocker blockerMem
    cases blocker with
    | sharedDeclaredSupport item =>
        cases item <;> rfl
    | sharedReturnSupport item =>
        cases item <;> rfl
    | sharedLocalBuffer _ => rfl
    | boundaryProfile coordinate =>
        have coordinateMem :
            coordinate ∈ activation.profileObstructions pair := by
          simpa [Graph.FiniteObject.DemandActivation.blockers] using
            blockerMem
        have coordinateEq : coordinate =
            Graph.FiniteObject.DemandActivation.pairCoordinate pair
              (((Graph.pairResponseActivation active).pairSupport pair).getD
                ∅) := by
          simp only [activation, explicitActivation,
            Graph.recordSparsePairDEBlockers] at coordinateMem
          split at coordinateMem
          · simpa using coordinateMem
          · simp at coordinateMem
        subst coordinate
        rw [Graph.FiniteObject.Blocker.carrier]
        simp only [Option.isSome_map, List.isSome_head?]
        exact List.ne_nil_of_mem (by
          simpa [presentation] using
            (pairCoordinateNonempty pair).choose_spec)
    | targetResponse coordinate =>
        have coordinateMem :
            coordinate ∈ activation.responseObstructions pair := by
          simpa [Graph.FiniteObject.DemandActivation.blockers] using
            blockerMem
        have coordinateEq : coordinate =
            Graph.FiniteObject.DemandActivation.pairCoordinate pair
              (((Graph.pairResponseActivation active).pairSupport pair).getD
                ∅) := by
          simp only [activation, explicitActivation,
            Graph.recordSparsePairDEBlockers] at coordinateMem
          split at coordinateMem
          · simpa using coordinateMem
          · simp at coordinateMem
        subst coordinate
        rw [Graph.FiniteObject.Blocker.carrier]
        simp only [Option.isSome_map, List.isSome_head?]
        exact List.ne_nil_of_mem (by
          simpa [presentation] using
            (pairCoordinateNonempty pair).choose_spec)
    | arithmeticChordSet chords =>
        have chordMem :
            chords ∈ activation.chordObstructions pair := by
          simpa [Graph.FiniteObject.DemandActivation.blockers] using
            blockerMem
        change chords ∈ (Graph.pairResponseActivation active).chordObstructions pair
          at chordMem
        simp only [Graph.pairResponseActivation] at chordMem
        have chordFacts := List.mem_filter.mp chordMem
        have orderedFacts := List.mem_filter.mp chordFacts.1
        have powersetMember : chords ∈
            (object.excessPorts data.threshold).powerset :=
          of_decide_eq_true orderedFacts.2
        have chordSubset :
            chords ⊆ object.excessPorts data.threshold :=
          Finset.mem_powerset.mp powersetMember
        have obstruction :
            Graph.SparsePairSuppressionChordObstruction active pair
              chords :=
          of_decide_eq_true chordFacts.2
        obtain ⟨_pairSubset, family, suppressionCertificate,
            _familyPorts, _chordEnds, usedChords⟩ := obstruction
        have usedNonempty :=
          family.usedChords_nonempty_of_avoids avoids
            suppressionCertificate
        have chordsNonempty : chords.Nonempty := by
          let portOf := fun index : family.Index =>
            ((family.configuration index).center,
              (family.configuration index).vertex)
          have imageNonempty :
              (family.usedChords suppressionCertificate.walk).image
                portOf |>.Nonempty :=
            usedNonempty.image portOf
          have imageEq :
              (family.usedChords suppressionCertificate.walk).image
                portOf = chords := by
            simpa only [portOf] using usedChords
          rw [← imageEq]
          exact imageNonempty
        have chosenInIntersection : chordsNonempty.choose ∈
            (chords.image presentation.chordPort) ∩
              object.excessPorts data.threshold := by
          refine Finset.mem_inter.mpr ⟨?_,
            chordSubset chordsNonempty.choose_spec⟩
          simpa [presentation] using
            (Finset.mem_image_of_mem presentation.chordPort
              chordsNonempty.choose_spec)
        rw [Graph.FiniteObject.Blocker.carrier]
        simp only [Option.isSome_map, List.isSome_head?]
        exact List.ne_nil_of_mem (by
          simpa using chosenInIntersection)
  exact carried

/-- **The explicit capacity presentation `𝔗_cap` of G**: the recorded blocker
activation of the active family, and `𝒫` = the node-[19] canonical packing. -/
noncomputable def explicitCapacity
    (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (graphConnected : object.graph.Connected) :
    SurplusCapacity data object where
  activation := explicitActivation active
  carrierComplete := explicit_carrierComplete active avoids graphConnected
  packing := canonicalWindowPacking data object
  packingValid := (canonicalWindowPacking_spec data object).1
  packingMaximal := (canonicalWindowPacking_spec data object).2.1

/-- `CapacityLedgerSpec` at the explicit presentation. -/
theorem explicitCapacity_spec
    (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (graphConnected : object.graph.Connected)
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (threeLe : 3 ≤ data.threshold)
    (envelope : object.edgeCount + 2 ≤ (data.threshold - 1) * object.vertexCount)
    (joinSlack : data.threshold * data.windowOrder + 2 ≤ 4 * data.windowOrder) :
    CapacityLedgerSpec data object (explicitCapacity active avoids graphConnected) := by
  classical
  let packing := canonicalWindowPacking data object
  have valid : object.IsWindowPacking data.windowOrder packing :=
    (canonicalWindowPacking_spec data object).1
  let activation := explicitActivation active
  have carried := explicit_carrierComplete active avoids graphConnected
  have connectedOn :
      Graph.SupportComponents.Connected.ConnectedOn
        object object.vertexFinset :=
    Graph.SupportComponents.Connected.connectedOn_vertexFinset
      object graphConnected
  let presentation : object.CarrierPresentation
      object.PairCoordinate (object.Vertex × object.Vertex) :=
    (explicitCapacity active avoids graphConnected).carrier
  have baseline : ∀ vertex : object.Vertex,
      data.threshold ≤ object.degree vertex :=
    fun vertex => le_trans atBaseline
      (object.minDegree_le_degree vertex)
  have handshake : data.threshold * object.vertexCount ≤
      2 * object.edgeCount :=
    Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount
      object data.threshold baseline
  have concrete : Graph.FiniteObject.ConcreteCapacityTokenLedgerStatement
      object data.threshold data.windowOrder activation
      presentation packing := by
    refine ⟨object.card_capacityTokens_add_internalMass
        valid baseline, ?_, ?_, ?_, ?_, ?_⟩
    · exact object.card_capacityTokens_le valid baseline
        threeLe handshake envelope data.windowOrder_pos
        joinSlack
    · intro pair token charged
      exact Graph.FiniteObject.capacityCharge_mem_capacityTokens
        activation presentation data.threshold packing charged
    · rw [← Graph.FiniteObject.capacityTokenOrder_toFinset
          (object := object) (threshold := data.threshold)
          (packing := packing)]
      exact Graph.FiniteObject.card_chargedPairs_eq_sum_load
        activation presentation data.threshold packing
    · exact ⟨carried,
        Graph.FiniteObject.chargedPairs_eq_blockedPairs
          activation presentation data.threshold packing carried⟩
    · have rolePartition : ∀ token :
          Graph.FiniteObject.CapacityToken object,
          (Graph.FiniteObject.tokenFibre activation presentation
            data.threshold packing token).card =
            ∑ role : Graph.SameTokenBlockerRoles.Role,
              (Graph.FiniteObject.tokenRoleFibre activation presentation
                data.threshold packing token role).card :=
          fun token =>
            Graph.FiniteObject.card_tokenFibre_eq_sum_roleFibre
              activation presentation data.threshold packing token
      refine ⟨rolePartition, ?_, ?_⟩
      · rw [← Graph.FiniteObject.chargedPairs_eq_blockedPairs
            activation presentation data.threshold packing carried]
        rw [← Graph.FiniteObject.capacityTokenOrder_toFinset
          (object := object) (threshold := data.threshold)
          (packing := packing)]
        rw [Graph.FiniteObject.card_chargedPairs_eq_sum_load
          activation presentation data.threshold packing]
        apply Finset.sum_congr rfl
        intro token _tokenMem
        exact rolePartition token
      · intro token
        exact ⟨Graph.FiniteObject.tokenFibre_subset activation presentation
            data.threshold packing token,
          fun pair member =>
            Graph.FiniteObject.card_of_mem_tokenFibre activation presentation
              data.threshold packing member,
          Graph.FiniteObject.card_tokenFibre_eq_pairMultiplicity activation
            presentation data.threshold packing token⟩
  exact ⟨⟨active, rfl⟩, object.card_primitiveCarrier baseline,
    object.card_primitiveCarrier_le baseline threeLe handshake envelope,
    concrete, connectedOn, rfl⟩

/-- **Uniqueness**: every presentation meeting `CapacityLedgerSpec` IS the
explicit one (the activation is a function of a proposition, the packing is
pinned to `𝒫`, all other fields are proofs). -/
theorem eq_explicitCapacity_of_spec
    (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (graphConnected : object.graph.Connected)
    {capacity : SurplusCapacity data object}
    (spec : CapacityLedgerSpec data object capacity) :
    capacity = explicitCapacity active avoids graphConnected := by
  obtain ⟨⟨active', activationEq⟩, -, -, -, -, packingEq⟩ := spec
  cases capacity with
  | mk activation carrierComplete packing packingValid packingMaximal =>
    simp only at activationEq packingEq
    subst activationEq packingEq
    rfl

/-- **`canonicalCapacity data G = some (explicitCapacity …)`**. -/
theorem canonicalCapacity_eq_explicit
    (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (graphConnected : object.graph.Connected)
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (threeLe : 3 ≤ data.threshold)
    (envelope : object.edgeCount + 2 ≤ (data.threshold - 1) * object.vertexCount)
    (joinSlack : data.threshold * data.windowOrder + 2 ≤ 4 * data.windowOrder) :
    canonicalCapacity data object = some (explicitCapacity active avoids graphConnected) := by
  obtain ⟨c, hc, spec⟩ := canonicalCapacity_spec data object
    ⟨_, explicitCapacity_spec active avoids graphConnected atBaseline threeLe envelope
      joinSlack⟩
  rw [hc, eq_explicitCapacity_of_spec active avoids graphConnected spec]

end Hypostructure.Graph.Strategy.Spine

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.SameTokenBlockerRoles

universe u

section Ledger

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-- `|Π_free(𝔗)|`: the free side of the canonical charge `Θ_cap` at a
presentation (pairs of `Π(𝒜₀)` no token of the declared order charges). -/
noncomputable def freeCount (capacity : SurplusCapacity data object) : Nat :=
  (Graph.freeSide object.vertexPairDecidableEq (object.portPairSchedule data.threshold)
    capacity.tokenOrder capacity.Eligible capacity.eligibleDecidable).card

/-- The three Prop-inputs of `ObjectCapacityLedger` other than the budget. -/
def ObjectLedgerInputs (capacity : SurplusCapacity data object) : Prop :=
  (object.portPairSchedule data.threshold).card =
      (object.degreeSurplus data.threshold).choose 2 ∧
    capacity.tokens.Nonempty ∧
    capacity.tokens.card ≤
      object.capacityTokenSupply data.threshold + object.degreeSurplus data.threshold

/-- **The canonical object ledger at a presentation**: no choice at all; its
entropy budget is the free side itself (the least budget any ledger at this
presentation can carry). -/
noncomputable def canonicalObjectLedgerAt (capacity : SurplusCapacity data object) :
    Option (Graph.ObjectCapacityLedger object data.threshold data.windowOrder capacity) := by
  classical
  exact if h : ObjectLedgerInputs data object capacity then
    some (Graph.ObjectCapacityLedger.ofCapacityCharge capacity h.1 h.2.1
      (freeCount data object capacity) le_rfl h.2.2)
  else none

theorem canonicalObjectLedgerAt_spec (capacity : SurplusCapacity data object)
    (h : ObjectLedgerInputs data object capacity) :
    ∃ L, canonicalObjectLedgerAt data object capacity = some L ∧
      L.entropyBudget = freeCount data object capacity := by
  classical
  refine ⟨Graph.ObjectCapacityLedger.ofCapacityCharge capacity h.1 h.2.1
      (freeCount data object capacity) le_rfl h.2.2, ?_, rfl⟩
  simp only [canonicalObjectLedgerAt, dif_pos h]

variable {data object}

/-- The free side of EVERY ledger at a presentation is the same set. -/
theorem ledger_free_card {capacity : SurplusCapacity data object}
    (L : Graph.ObjectCapacityLedger object data.threshold data.windowOrder capacity) :
    L.presented.free.card = freeCount data object capacity := rfl

/-- Every ledger's budget dominates the free side. -/
theorem freeCount_le_budget {capacity : SurplusCapacity data object}
    (L : Graph.ObjectCapacityLedger object data.threshold data.windowOrder capacity) :
    freeCount data object capacity ≤ L.entropyBudget := L.sandwich

/-- `CertifiedLedgerSpec` holds at every certified ledger (all its clauses are
identities of the presented ledger). -/
theorem certifiedLedgerSpec_of {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity) :
    CertifiedLedgerSpec data object capacity certified := by
  classical
  let ledger := certified.ledger
  refine ⟨ledger.presented.choose_two_eq_free_add_sum_roleFibre
      ledger.presented.tokenClass,
    fun token => ledger.presented.load_eq_sum_roleFibre token,
    ledger.presented.classwise_split.1.1,
    ledger.presented.classwise_split.1.2,
    ledger.presented.classwise_split.2,
    ledger.presented.subtype_split.1.1,
    ledger.presented.subtype_split.2, ?_⟩
  intro patternBound positive value noMatching noStar
  exact ledger.presented.grainLoad_le_of_no_homogeneous
    ledger.presented.tokenClass value patternBound positive
    noMatching noStar

/-- **Certification criterion at a presentation** (exact, no choice):
a certified ledger exists iff `|Π_free| ≤ S·n + (⌊log₂ n⌋+1)·σ`. -/
theorem certified_nonempty_iff {capacity : SurplusCapacity data object}
    (h : ObjectLedgerInputs data object capacity)
    (sizePos : 0 < object.vertexCount) (S1 : 1 ≤ data.surplusScale) :
    Nonempty (SurplusCertified data object capacity) ↔
      freeCount data object capacity ≤ data.surplusScale * object.vertexCount +
        (Nat.log2 object.vertexCount + 1) * object.degreeSurplus data.threshold := by
  constructor
  · rintro ⟨cert⟩
    have hs := freeCount_le_budget cert.ledger
    rw [cert.entropyBudget_eq] at hs
    have h1 := cert.spineDeficit_le
    have h2 := Nat.mul_le_mul_left (Nat.log2 object.vertexCount + 1) cert.edgeSlack_le
    omega
  · intro hE
    obtain ⟨L, -, hLE⟩ := canonicalObjectLedgerAt_spec data object capacity h
    generalize hkdef : Nat.log2 object.vertexCount + 1 = k at hE
    generalize hσdef : object.degreeSurplus data.threshold = σ at hE
    generalize hSn : data.surplusScale * object.vertexCount = Sn at hE
    have kpos : 0 < k := by omega
    have kle : ∀ x, x % k ≤ Sn := by
      intro x
      subst hSn
      have hn : object.vertexCount ≠ 0 := by omega
      have hlog : Nat.log2 object.vertexCount < object.vertexCount :=
        (Nat.log2_lt hn).2 Nat.lt_two_pow_self
      have : object.vertexCount ≤ data.surplusScale * object.vertexCount :=
        Nat.le_mul_of_pos_left _ S1
      have := Nat.mod_lt x kpos
      omega
    set E := L.entropyBudget with hEdef
    rw [← hLE] at hE
    by_cases big : σ ≤ E / k
    · have hdm : E / k * k ≤ E := Nat.div_mul_le_self E k
      have hkm : k * σ ≤ k * (E / k) := Nat.mul_le_mul_left k big
      rw [Nat.mul_comm k (E / k)] at hkm
      have key : k * σ ≤ E := le_trans hkm hdm
      refine ⟨⟨L, E - k * σ, σ, ?_, ?_, ?_⟩⟩
      · show E = E - k * σ + (Nat.log2 object.vertexCount + 1) * σ
        rw [hkdef]; omega
      · show E - k * σ ≤ data.surplusScale * object.vertexCount
        rw [hSn]; omega
      · show σ ≤ object.degreeSurplus data.threshold
        rw [hσdef]
    · push Not at big
      refine ⟨⟨L, E % k, E / k, ?_, ?_, ?_⟩⟩
      · show E = E % k + (Nat.log2 object.vertexCount + 1) * (E / k)
        rw [hkdef, Nat.mod_add_div]
      · show E % k ≤ data.surplusScale * object.vertexCount
        rw [hSn]
        exact kle E
      · show E / k ≤ object.degreeSurplus data.threshold
        rw [hσdef]; omega

/-- The same criterion, read on the canonical certified ledger at the
presentation: `canonicalCertifiedCapacityDataAt c` is `some` iff the free side
fits the certification budget. -/
theorem canonicalCertified_isSome_iff {capacity : SurplusCapacity data object}
    (h : ObjectLedgerInputs data object capacity)
    (sizePos : 0 < object.vertexCount) (S1 : 1 ≤ data.surplusScale) :
    (canonicalCertifiedCapacityDataAt data object capacity).isSome ↔
      freeCount data object capacity ≤ data.surplusScale * object.vertexCount +
        (Nat.log2 object.vertexCount + 1) * object.degreeSurplus data.threshold := by
  rw [← certified_nonempty_iff h sizePos S1]
  constructor
  · intro hs
    obtain ⟨cert, _⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨cert⟩
  · rintro ⟨cert⟩
    obtain ⟨c', hc', -⟩ := canonicalCertifiedCapacityDataAt_spec data object capacity
      ⟨cert, certifiedLedgerSpec_of cert⟩
    rw [hc']; rfl

end Ledger

end Hypostructure.Graph.Strategy.Spine
