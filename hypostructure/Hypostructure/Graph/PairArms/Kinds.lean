import Hypostructure.Graph.WindowChargeKinds
import Hypostructure.Graph.CapacityFreeSide.SeparatedCharge

/-!
# Pair code, arm A: which canonical blockers and which tokens a blocked pair can have

At the recorded blocker activation of an
`ActiveSurplusDemands` certificate:

* `canonicalBlocker_ne_localBuffer`: clause (c) is never canonical (a shared buffer
  vertex is a shared declared vertex, which precedes it);
* `chord_head_of_canonical`: a canonical chord-set blocker is the head of the pair's
  chord-obstruction list;
* `chordObstruction_ports`: a chord obstruction of `{p,q}` makes both ports open, their
  supports `T` disjoint and each centre outside the other's `T`;
* `fKind_charge`: **a clause-(f) canonical pair `{p,q}` (p before q in chord order) has
  canonical blocker `{p}`, is fully separated, and is charged to the port token `p` or to
  a remainder unit at a shoulder of `p` — never to `𝔗_W`, `V` or `I`**;
* `eKind_charge_subtype`: a clause-(e) canonical pair is never charged to `I` or `P`.
-/

namespace Hypostructure.Graph.PairArms

open Hypostructure Hypostructure.Graph Hypostructure.Graph.FiniteObject

universe u v

section generic

variable {object : FiniteObject.{u}} {Coordinate Chord : Type v}

/-- **Clause (c) is never the canonical blocker.** -/
theorem canonicalBlocker_ne_localBuffer
    (activation : DemandActivation object Coordinate Chord)
    (pair : Finset (object.Vertex × object.Vertex)) (w : object.Vertex) :
    canonicalBlocker activation pair ≠ some (Blocker.sharedLocalBuffer w) := by
  classical
  intro h
  have hmem := canonicalBlocker_mem activation h
  rw [DemandActivation.sharedLocalBuffer_mem_blockers_iff] at hmem
  obtain ⟨l, hl, r, hr, hlr, h1, h2⟩ := hmem
  have hv : Blocker.sharedDeclaredSupport (CarrierItem.vertex w) ∈
      activation.blockers pair :=
    (DemandActivation.sharedDeclaredSupport_mem_blockers_iff activation).2
      ⟨l, hl, r, hr, hlr, DemandActivation.vertex_mem_sharedItems
        (DemandActivation.localBuffer_subset_declaredSupport activation l h1)
        (DemandActivation.localBuffer_subset_declaredSupport activation r h2)⟩
  rw [canonicalBlocker] at h
  simp only [List.map_append, List.map_map, List.append_assoc] at h
  have hb := Hypostructure.Graph.WindowChargeKinds.head_filter_mem_of_prefix _ _ _
    (Blocker.sharedDeclaredSupport (CarrierItem.vertex w))
    (by simp [object.mem_orderedVertices]) (by simpa using hv) h
  simp at hb

/-- **A canonical chord-set blocker is the head of the chord-obstruction list.** -/
theorem chord_head_of_canonical
    (activation : DemandActivation object Coordinate Chord)
    (pair : Finset (object.Vertex × object.Vertex)) {S : Finset Chord}
    (h : canonicalBlocker activation pair = some (Blocker.arithmeticChordSet S)) :
    (activation.chordObstructions pair).head? = some S := by
  classical
  rw [canonicalBlocker] at h
  rcases Hypostructure.Graph.WindowChargeKinds.head_filter_append_cases _ _ _ h with hb | h'
  · simp at hb
  · rw [List.filter_eq_self.2] at h'
    · cases hc : activation.chordObstructions pair with
      | nil => rw [hc] at h'; simp at h'
      | cons a l =>
          rw [hc] at h'
          simp only [List.map_cons, List.head?_cons, Option.some.injEq,
            Blocker.arithmeticChordSet.injEq] at h'
          subst h'; rfl
    · intro b hb
      obtain ⟨S', hS', rfl⟩ := List.mem_map.1 hb
      simp only [decide_eq_true_eq]
      unfold DemandActivation.blockers
      exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (by simpa using hS'))))

/-- **A clause-(e) canonical pair is charged to `𝔗_W`, `𝔗_R` or a primitive vertex**,
never to an incidence or a port token (the carrier of a coordinate is a vertex). -/
theorem eKind_charge_subtype
    (activation : DemandActivation object Coordinate Chord)
    (presentation : CarrierPresentation object Coordinate Chord) (threshold : Nat)
    (packing : Finset (Finset object.Vertex))
    {pair : Finset (object.Vertex × object.Vertex)} {c : Coordinate}
    (hb : canonicalBlocker activation pair = some (Blocker.targetResponse c))
    {t : CapacityToken object}
    (ht : capacityCharge activation presentation threshold packing pair = some t) :
    (∃ e, t = .boundaryWindow e) ∨ (∃ e, t = .crossWindow e) ∨ (∃ v, t = .remainder v) ∨
      (∃ v, t = .primitive (.inl v)) := by
  classical
  unfold capacityCharge at ht
  rcases hw : windowJoinChoice activation presentation packing pair with _ | e
  · rw [hw] at ht
    rcases hx : crossWindowChoice activation presentation packing pair with _ | e
    · rw [hx] at ht
      rcases hr : remainderVertexChoice activation presentation threshold packing pair
        with _ | v
      · rw [hr, hb] at ht
        simp only [Blocker.carrier, Option.map_map] at ht
        obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 ht
        exact Or.inr (Or.inr (Or.inr ⟨x, rfl⟩))
      · rw [hr] at ht
        cases ht
        exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
    · rw [hx] at ht
      cases ht
      exact Or.inr (Or.inl ⟨e, rfl⟩)
  · rw [hw] at ht
    cases ht
    exact Or.inl ⟨e, rfl⟩

end generic

/-! ## Clause (f) at the recorded activation -/

section chord

variable {object : FiniteObject.{u}} {threshold order : Nat}
  {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}

open Hypostructure.Graph.CapacityFreeSide

/-- The ports of the chord order are exactly the selected ports. -/
theorem mem_chordOrder_iff
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (x : object.Vertex × object.Vertex) :
    x ∈ chordOrder active ↔ x ∈ object.excessPorts threshold := by
  classical
  unfold chordOrder
  rw [List.mem_insertionSort, List.mem_flatMap, object.mem_excessPorts_iff]
  constructor
  · rintro ⟨c, -, hx⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact he
  · intro h
    exact ⟨x.1, object.mem_orderedVertices x.1, List.mem_map.2 ⟨x.2, h, rfl⟩⟩

/-- Two distinct members of a list: one of them comes first. -/
theorem first_of_two {α : Type*} [DecidableEq α] :
    ∀ (L : List α) {p q : α}, p ∈ L → q ∈ L → p ≠ q →
      (∃ A B, L = A ++ p :: B ∧ q ∉ A) ∨ (∃ A B, L = A ++ q :: B ∧ p ∉ A)
  | [], _, _, hp, _, _ => by cases hp
  | a :: L, p, q, hp, hq, hpq => by
      by_cases hap : a = p
      · subst hap
        exact Or.inl ⟨[], L, rfl, by simp⟩
      by_cases haq : a = q
      · subst haq
        exact Or.inr ⟨[], L, rfl, by simp⟩
      have hp' : p ∈ L := by
        rcases List.mem_cons.1 hp with h | h
        · exact absurd h.symm hap
        · exact h
      have hq' : q ∈ L := by
        rcases List.mem_cons.1 hq with h | h
        · exact absurd h.symm haq
        · exact h
      rcases first_of_two L hp' hq' hpq with ⟨A, B, hL, hA⟩ | ⟨A, B, hL, hA⟩
      · refine Or.inl ⟨a :: A, B, by rw [hL]; rfl, ?_⟩
        simp only [List.mem_cons, not_or]
        exact ⟨fun h => haq h.symm, hA⟩
      · refine Or.inr ⟨a :: A, B, by rw [hL]; rfl, ?_⟩
        simp only [List.mem_cons, not_or]
        exact ⟨fun h => hap h.symm, hA⟩

/-- `T(p) = {x_p, a_p, b_p}` read through the activation's chord ends. -/
theorem mem_portT_iff
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {p : object.Vertex × object.Vertex} (hp : p ∈ object.excessPorts threshold)
    (z : object.Vertex) :
    z ∈ portT hp ↔ z = p.2 ∨ z = (pairResponseChordEnds active p).1 ∨
      z = (pairResponseChordEnds active p).2 := by
  have e : pairResponseChordEnds active p =
      ((active.shoulderPair p hp).choose, (active.shoulderPair p hp).choose_spec.choose) := by
    simp only [pairResponseChordEnds, dif_pos hp]
  rw [e]
  have hs := (active.shoulderPair p hp).choose_spec.choose_spec.1 z
  unfold portT SurplusPort.support
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [Finset.mem_insert, hs]
  rfl

/-- **A chord obstruction of `{p,q}` makes both ports open, their `T` disjoint and each
centre outside the other's `T`** (the compatible-family axioms, read at the pair). -/
theorem chordObstruction_ports
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {pair S : Finset (object.Vertex × object.Vertex)}
    (obs : SparsePairSuppressionChordObstruction active pair S)
    {p q : object.Vertex × object.Vertex} (hpq : p ≠ q)
    (hpair : ∀ x, x ∈ pair ↔ x = p ∨ x = q) :
    ∃ (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold),
      ¬ object.graph.Adj (pairResponseChordEnds active p).1
          (pairResponseChordEnds active p).2 ∧
      ¬ object.graph.Adj (pairResponseChordEnds active q).1
          (pairResponseChordEnds active q).2 ∧
      Disjoint (portT hp) (portT hq) ∧ p.1 ∉ portT hq ∧ q.1 ∉ portT hp := by
  classical
  obtain ⟨sub, F, -, img, ends, -⟩ := obs
  have hp : p ∈ object.excessPorts threshold := sub ((hpair p).2 (Or.inl rfl))
  have hq : q ∈ object.excessPorts threshold := sub ((hpair q).2 (Or.inr rfl))
  have getIdx : ∀ d ∈ pair, ∃ i : F.Index,
      ((F.configuration i).center, (F.configuration i).vertex) = d := by
    intro d hd
    rw [← img] at hd
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hd
    exact ⟨i, hi⟩
  obtain ⟨i, hi⟩ := getIdx p ((hpair p).2 (Or.inl rfl))
  obtain ⟨j, hj⟩ := getIdx q ((hpair q).2 (Or.inr rfl))
  have hij : i ≠ j := by
    rintro rfl
    exact hpq (hi.symm.trans hj)
  -- the three vertices of each port are those of its configuration
  have inT : ∀ {d} (hd : d ∈ object.excessPorts threshold) (k : F.Index),
      ((F.configuration k).center, (F.configuration k).vertex) = d →
      ∀ z ∈ portT hd, z = (F.configuration k).vertex ∨ z = (F.configuration k).left ∨
        z = (F.configuration k).right := by
    intro d hd k hk z hz
    rw [mem_portT_iff active hd] at hz
    have hv : (F.configuration k).vertex = d.2 := congrArg Prod.snd hk
    rcases ends k with he | he <;> rw [hk] at he <;> rw [he] at hz <;>
      rcases hz with h | h | h
    · exact Or.inl (h.trans hv.symm)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl (h.trans hv.symm)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have openOf : ∀ {d} (k : F.Index),
      ((F.configuration k).center, (F.configuration k).vertex) = d →
      ¬ object.graph.Adj (pairResponseChordEnds active d).1
        (pairResponseChordEnds active d).2 := by
    intro d k hk
    have miss := (F.configuration k).shoulder_missing
    rcases ends k with he | he <;> rw [hk] at he <;> rw [he]
    · exact miss
    · exact fun h => miss h.symm
  refine ⟨hp, hq, openOf i hi, openOf j hj, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro z hzp hzq
    have dj := F.support_disjoint hij
    rw [Set.disjoint_left] at dj
    apply dj (a := z)
    · rcases inT hp i hi z hzp with h | h | h <;> simp [h]
    · rcases inT hq j hj z hzq with h | h | h <;> simp [h]
  · intro h
    obtain ⟨c1, c2, c3⟩ := F.center_outside_support i j
    have hc : (F.configuration i).center = p.1 := congrArg Prod.fst hi
    rcases inT hq j hj p.1 h with h' | h' | h'
    · exact c1 (hc.trans h')
    · exact c2 (hc.trans h')
    · exact c3 (hc.trans h')
  · intro h
    obtain ⟨c1, c2, c3⟩ := F.center_outside_support j i
    have hc : (F.configuration j).center = q.1 := congrArg Prod.fst hj
    rcases inT hp i hi q.1 h with h' | h' | h'
    · exact c1 (hc.trans h')
    · exact c2 (hc.trans h')
    · exact c3 (hc.trans h')

/-- The core of `fKind_charge`, with the chord order fixed (`p` before `q`). -/
theorem fKind_charge_ordered
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (data : CapacityPresentation object threshold order)
    (hact : data.activation = recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) (pairResponseActivation active)
      (object.portPairSchedule threshold))
    (avoids : ¬ HasCycleWithLength LengthOK object)
    {pair S : Finset (object.Vertex × object.Vertex)}
    (hcan : canonicalBlocker data.activation pair = some (Blocker.arithmeticChordSet S))
    {p q : object.Vertex × object.Vertex} (hpq : p ≠ q)
    (hpair : ∀ x, x ∈ pair ↔ x = p ∨ x = q)
    (A B : List (object.Vertex × object.Vertex)) (hL : chordOrder active = A ++ p :: B)
    (hqA : q ∉ A) :
    ∃ (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold),
      S = {p} ∧
      ¬ object.graph.Adj (pairResponseChordEnds active p).1
          (pairResponseChordEnds active p).2 ∧
      ¬ object.graph.Adj (pairResponseChordEnds active q).1
          (pairResponseChordEnds active q).2 ∧
      Disjoint ((pairResponseActivation active).declaredSupport p)
        ((pairResponseActivation active).declaredSupport q) ∧
      Disjoint ((pairResponseActivation active).returnSupport p)
        ((pairResponseActivation active).returnSupport q) ∧
      Disjoint (portT hp) (portT hq) ∧ p.1 ∉ portT hq ∧ q.1 ∉ portT hp ∧
      (capacityCharge data.activation data.carrier threshold data.packing pair =
          some (.primitive (.inr (.inr p))) ∨
        ∃ v k, (v = (pairResponseChordEnds active p).1 ∨
            v = (pairResponseChordEnds active p).2) ∧
          capacityCharge data.activation data.carrier threshold data.packing pair =
            some (.remainder (v, k))) := by
  classical
  have chordEq : data.activation.chordObstructions =
      (pairResponseActivation active).chordObstructions := by rw [hact]; rfl
  have head := chord_head_of_canonical data.activation pair hcan
  have Smem : S ∈ (pairResponseActivation active).chordObstructions pair := by
    rw [← chordEq]; exact List.mem_of_mem_head? head
  have obs := suppressionObstruction_of_mem_pairResponseChordObstructions active Smem
  obtain ⟨hp, hq, openP, openQ, dT, hpT, hqT⟩ := chordObstruction_ports active obs hpq hpair
  have pm : p ∈ pair := (hpair p).2 (Or.inl rfl)
  have qm : q ∈ pair := (hpair q).2 (Or.inr rfl)
  have sep := fun v => Hypostructure.Graph.WindowChargeKinds.separated_of_late_canonical data.activation hcan
    (Or.inr (Or.inr ⟨S, rfl⟩)) pm qm hpq v
  have declEq : data.activation.declaredSupport =
      (pairResponseActivation active).declaredSupport := by rw [hact]; rfl
  have retEq : data.activation.returnSupport =
      (pairResponseActivation active).returnSupport := by rw [hact]; rfl
  have dD : Disjoint ((pairResponseActivation active).declaredSupport p)
      ((pairResponseActivation active).declaredSupport q) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rw [← declEq] at h1 h2
    exact (sep v).1 ⟨h1, h2⟩
  have dR : Disjoint ((pairResponseActivation active).returnSupport p)
      ((pairResponseActivation active).returnSupport q) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rw [← retEq] at h1 h2
    exact (sep v).2.1 ⟨h1, h2⟩
  obtain ⟨sp, -⟩ := both_singletons_chordObstruction active hp hq openP openQ dD dT hpT hqT
    pair hpair
  have head' := chordObstructions_head active avoids hpair A B hL hqA sp
  rw [chordEq, head'] at head
  have hS : S = {p} := (Option.some.inj head).symm
  subst hS
  refine ⟨hp, hq, rfl, openP, openQ, dD, dR, dT, hpT, hqT, ?_⟩
  have hport : data.carrier.chordPort p = p := by
    show data.activation.chordPort p = p
    rw [hact]; rfl
  have hends : data.carrier.chordEnds p = pairResponseChordEnds active p := by
    show data.activation.chordEnds p = _
    rw [hact]; rfl
  have := Hypostructure.Graph.CapacityFreeSide.capacityCharge_of_singleton_chord data.activation data.carrier threshold
    data.packing pair hcan hport hp (by rw [hends]; exact openP)
  rw [hends] at this
  exact this

/-- **Clause (f) at the recorded activation.**  A pair whose canonical blocker is a
chord set `S` is `{p, q}` with `p` before `q` in chord order, `S = {p}` (the earlier
port's own single-port suppression cycle), both ports open, fully separated (disjoint
`T ∪ Γ`, disjoint `R`, disjoint `T`, centres outside the other's `T`), and it is charged
to the port token `p` or to a remainder unit at a shoulder of `p`. -/
theorem fKind_charge
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (data : CapacityPresentation object threshold order)
    (hact : data.activation = recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) (pairResponseActivation active)
      (object.portPairSchedule threshold))
    (avoids : ¬ HasCycleWithLength LengthOK object)
    {pair S : Finset (object.Vertex × object.Vertex)}
    (hsched : pair ∈ object.portPairSchedule threshold)
    (hcan : canonicalBlocker data.activation pair = some (Blocker.arithmeticChordSet S)) :
    ∃ p q, ∃ (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold),
      p ≠ q ∧ (∀ x, x ∈ pair ↔ x = p ∨ x = q) ∧
      (∃ A B, chordOrder active = A ++ p :: B ∧ q ∉ A) ∧
      S = {p} ∧
      ¬ object.graph.Adj (pairResponseChordEnds active p).1
          (pairResponseChordEnds active p).2 ∧
      ¬ object.graph.Adj (pairResponseChordEnds active q).1
          (pairResponseChordEnds active q).2 ∧
      Disjoint ((pairResponseActivation active).declaredSupport p)
        ((pairResponseActivation active).declaredSupport q) ∧
      Disjoint ((pairResponseActivation active).returnSupport p)
        ((pairResponseActivation active).returnSupport q) ∧
      Disjoint (portT hp) (portT hq) ∧ p.1 ∉ portT hq ∧ q.1 ∉ portT hp ∧
      (capacityCharge data.activation data.carrier threshold data.packing pair =
          some (.primitive (.inr (.inr p))) ∨
        ∃ v k, (v = (pairResponseChordEnds active p).1 ∨
            v = (pairResponseChordEnds active p).2) ∧
          capacityCharge data.activation data.carrier threshold data.packing pair =
            some (.remainder (v, k))) := by
  classical
  obtain ⟨p, q, hp, hq, hpq, hpair⟩ := pair_of_schedule hsched
  rcases first_of_two (chordOrder active) ((mem_chordOrder_iff active p).2 hp)
      ((mem_chordOrder_iff active q).2 hq) hpq with ⟨A, B, hL, hA⟩ | ⟨A, B, hL, hA⟩
  · obtain ⟨hp', hq', rest⟩ := fKind_charge_ordered active data hact avoids hcan hpq hpair
      A B hL hA
    exact ⟨p, q, hp', hq', hpq, hpair, ⟨A, B, hL, hA⟩, rest⟩
  · have hpair' : ∀ x, x ∈ pair ↔ x = q ∨ x = p := fun x => (hpair x).trans or_comm
    obtain ⟨hq', hp', rest⟩ := fKind_charge_ordered active data hact avoids hcan
      (Ne.symm hpq) hpair' A B hL hA
    exact ⟨q, p, hq', hp', Ne.symm hpq, hpair', ⟨A, B, hL, hA⟩, rest⟩

end chord

end Hypostructure.Graph.PairArms
