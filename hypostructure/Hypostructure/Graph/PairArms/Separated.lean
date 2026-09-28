import Hypostructure.Graph.PairArms.Classify

/-!
# Pair code, arm A: the clause-(f) fibre of a port is exactly its separated partners

Converse of `fKind_charge`.  At the recorded activation, a pair `{p, q}` of selected
ports with
* disjoint declared supports `T ∪ Γ` and disjoint returns `R`,
* both ports open, each centre outside the other's `T`,
* no clause-(e) determination obstruction,
* `p` before `q` in chord order,

has **only chord-set blockers** (`hno_of_separated`), canonical blocker `{p}`, and is
charged to the port token `p` or a remainder unit at a shoulder of `p`
(`separated_fKind`).  With `fKind_charge`, the clause-(f) pairs are exactly these.
So the clause-(f) role fibre of the port token `p` is
`{{p,q} : q separated from p, no (e), chord-later}` minus the pairs diverted to a high
remainder shoulder of `p`: it consumes no resource of the pair beyond separation.
-/

namespace Hypostructure.Graph.PairArms

open Hypostructure Hypostructure.Graph Hypostructure.Graph.FiniteObject Hypostructure.Graph.CapacityFreeSide

universe u

variable {object : FiniteObject.{u}} {threshold order : Nat}
  {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}

/-- **A separated pair without a clause-(e) obstruction has only chord-set blockers.** -/
theorem hno_of_separated
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (data : CapacityPresentation object threshold order)
    (hact : data.activation = recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) (pairResponseActivation active)
      (object.portPairSchedule threshold))
    {p q : object.Vertex × object.Vertex} {pair : Finset (object.Vertex × object.Vertex)}
    (hpair : ∀ x, x ∈ pair ↔ x = p ∨ x = q)
    (dD : Disjoint (data.activation.declaredSupport p) (data.activation.declaredSupport q))
    (dR : Disjoint (data.activation.returnSupport p) (data.activation.returnSupport q))
    (hnoE : ¬ SparsePairDEResponseObstructionAt (Baseline := Baseline) (LengthOK := LengthOK)
      (pairResponseActivation active) (object.portPairSchedule threshold) pair) :
    ∀ b ∈ data.activation.blockers pair,
      b.kind = SameTokenBlockerRoles.BlockerKind.arithmeticChordSet := by
  classical
  -- a property of both members of the pair, symmetric in the two
  have both : ∀ (X : object.Vertex × object.Vertex → Finset object.Vertex),
      Disjoint (X p) (X q) → ∀ {l r}, l ∈ pair → r ∈ pair → l ≠ r → ∀ v, v ∈ X l → v ∉ X r := by
    intro X dX l r hl hr hlr v hvl hvr
    rw [hpair] at hl hr
    rcases hl with rfl | rfl <;> rcases hr with rfl | rfl
    · exact hlr rfl
    · exact Finset.disjoint_left.1 dX hvl hvr
    · exact Finset.disjoint_left.1 dX hvr hvl
    · exact hlr rfl
  have profEmpty : data.activation.profileObstructions pair = [] := by
    rw [hact]; exact Hypostructure.Graph.WindowChargeKinds.recorded_profile_empty active _ pair
  have respEmpty : data.activation.responseObstructions pair = [] := by
    rw [hact]
    simp only [recordSparsePairDEBlockers]
    rw [if_neg hnoE]
  intro b hb
  cases b with
  | sharedDeclaredSupport item =>
      exfalso
      rw [DemandActivation.sharedDeclaredSupport_mem_blockers_iff] at hb
      obtain ⟨l, hl, r, hr, hlr, hs⟩ := hb
      cases item with
      | vertex w =>
          have hw := DemandActivation.mem_both_of_vertex_mem_sharedItems hs
          exact both _ dD hl hr hlr w hw.1 hw.2
      | incidence e =>
          have he := DemandActivation.endpoints_mem_both_of_incidence_mem_sharedItems hs
          exact both _ dD hl hr hlr e.1 he.1 he.2.2.1
  | sharedReturnSupport item =>
      exfalso
      rw [DemandActivation.sharedReturnSupport_mem_blockers_iff] at hb
      obtain ⟨l, hl, r, hr, hlr, hs⟩ := hb
      cases item with
      | vertex w =>
          have hw := DemandActivation.mem_both_of_vertex_mem_sharedItems hs
          exact both _ dR hl hr hlr w hw.1 hw.2
      | incidence e =>
          have he := DemandActivation.endpoints_mem_both_of_incidence_mem_sharedItems hs
          exact both _ dR hl hr hlr e.1 he.1 he.2.2.1
  | sharedLocalBuffer w =>
      exfalso
      rw [DemandActivation.sharedLocalBuffer_mem_blockers_iff] at hb
      obtain ⟨l, hl, r, hr, hlr, h1, h2⟩ := hb
      exact both _ dD hl hr hlr w
        (DemandActivation.localBuffer_subset_declaredSupport _ l h1)
        (DemandActivation.localBuffer_subset_declaredSupport _ r h2)
  | boundaryProfile c =>
      exfalso
      unfold DemandActivation.blockers at hb
      simp [profEmpty] at hb
  | targetResponse c =>
      exfalso
      unfold DemandActivation.blockers at hb
      simp [respEmpty] at hb
  | arithmeticChordSet S => rfl

/-- **Separated pairs are clause-(f) pairs of their chord-earlier port.** -/
theorem separated_fKind
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (data : CapacityPresentation object threshold order)
    (hact : data.activation = recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) (pairResponseActivation active)
      (object.portPairSchedule threshold))
    (avoids : ¬ HasCycleWithLength LengthOK object)
    {p q : object.Vertex × object.Vertex}
    (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold)
    (hpq : p ≠ q)
    {pair : Finset (object.Vertex × object.Vertex)} (hpair : ∀ x, x ∈ pair ↔ x = p ∨ x = q)
    (dD : Disjoint (data.activation.declaredSupport p) (data.activation.declaredSupport q))
    (dR : Disjoint (data.activation.returnSupport p) (data.activation.returnSupport q))
    (hnoE : ¬ SparsePairDEResponseObstructionAt (Baseline := Baseline) (LengthOK := LengthOK)
      (pairResponseActivation active) (object.portPairSchedule threshold) pair)
    (openP : ¬ object.graph.Adj (pairResponseChordEnds active p).1
      (pairResponseChordEnds active p).2)
    (openQ : ¬ object.graph.Adj (pairResponseChordEnds active q).1
      (pairResponseChordEnds active q).2)
    (hpT : p.1 ∉ portT hq) (hqT : q.1 ∉ portT hp)
    (A B : List (object.Vertex × object.Vertex)) (hL : chordOrder active = A ++ p :: B)
    (hqA : q ∉ A) :
    canonicalBlocker data.activation pair = some (Blocker.arithmeticChordSet {p}) ∧
      (capacityCharge data.activation data.carrier threshold data.packing pair =
          some (.primitive (.inr (.inr p))) ∨
        ∃ v k, (v = (pairResponseChordEnds active p).1 ∨
            v = (pairResponseChordEnds active p).2) ∧
          capacityCharge data.activation data.carrier threshold data.packing pair =
            some (.remainder (v, k))) := by
  classical
  have hno := hno_of_separated active data hact hpair dD dR hnoE
  have declEq : data.activation.declaredSupport =
      (pairResponseActivation active).declaredSupport := by rw [hact]; rfl
  have chordEq : data.activation.chordObstructions =
      (pairResponseActivation active).chordObstructions := by rw [hact]; rfl
  have dD' : Disjoint ((pairResponseActivation active).declaredSupport p)
      ((pairResponseActivation active).declaredSupport q) := by rw [← declEq]; exact dD
  have Tsub : ∀ {d} (hd : d ∈ object.excessPorts threshold),
      portT hd ⊆ (pairResponseActivation active).declaredSupport d := by
    intro d hd
    unfold portT
    rw [← pairResponseActivation_localBuffer_of_mem active hd]
    exact DemandActivation.localBuffer_subset_declaredSupport _ d
  have dT : Disjoint (portT hp) (portT hq) :=
    Finset.disjoint_of_subset_left (Tsub hp) (Finset.disjoint_of_subset_right (Tsub hq) dD')
  obtain ⟨sp, -⟩ := both_singletons_chordObstruction active hp hq openP openQ dD' dT hpT hqT
    pair hpair
  have head := chordObstructions_head active avoids hpair A B hL hqA sp
  have hcan := canonicalBlocker_eq_chord data.activation pair hno (by rw [chordEq]; exact head)
  exact ⟨hcan, separated_charge active data hact avoids hp hq hpq hpair hno openP openQ hpT hqT
    A B hL hqA⟩

end Hypostructure.Graph.PairArms
