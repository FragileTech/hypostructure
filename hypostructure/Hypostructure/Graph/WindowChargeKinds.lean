import Hypostructure.Graph.ObjectCapacityLedger
import Hypostructure.Graph.SparseEntropySandwich

/-!
# Where the windows sit in the capacity charge

Vocabulary-free: stated for any demand activation, carrier presentation and packing.

`𝔗_W = {(e,RW)} ⊔ {(e,v)}` (`boundaryWindow`, `crossWindow`), `|𝔗_W| = e(R,W) + 2e_×`.
A blocked pair `π` is charged to `𝔗_W` exactly by clauses (a)/(b) of `capacityCharge`:
`supp(B_π)` (the declared support of the canonical blocker) contains both ends of an
`R`–`W` (resp. cross-window) edge.  Below:

* `window_charge_support` / `cross_charge_support`: a window charge exhibits that edge;
* `canonicalBlocker_ne_sharedDeclared_incidence` / `…_sharedReturn_incidence`: the
  canonical blocker is never an incidence blocker (vertices are enumerated first);
* `window_charge_kind`: **every pair charged to `𝔗_W` has a canonical blocker of clause
  (d), (e) or (f)** (coordinate or chord set) — vertex/buffer blockers have singleton
  support, incidence blockers are never canonical;
* `window_charge_of_support_edge`: conversely, if `supp(B_π)` contains an `R`–`W` edge
  then `π` is charged to a `boundaryWindow` token;
* `connectedOn_crossing_edge` + `coordinate_spread_window_charge`: a coordinate blocker
  whose (connected) support meets both `R` and `W` is charged to `𝔗_W`.

## The target-response obstruction

`SparsePairDEResponseObstructionAt` has three arms: a residual target defect among
`{r_π} ∪ determiners`, a `ReplacementSupport` at the determination support, and a
whole-graph smaller representative whose target transfers back.  With no replacement
support, target avoidance and lexicographic minimality only the first survives
(`responseObstruction_targetDefect`).
-/

namespace Hypostructure.Graph.WindowChargeKinds

open Hypostructure Hypostructure.Graph Hypostructure.Graph.FiniteObject
open Hypostructure.Graph.Strategy.InterfaceReplacement



universe u v

/-! ## Generic list facts about "first applicable" -/

theorem head_filter_mem_of_prefix {α : Type*} (X Y : List α) (p : α → Bool) (a : α)
    (ha : a ∈ X) (hp : p a = true) {b : α}
    (h : ((X ++ Y).filter p).head? = some b) : b ∈ X := by
  rw [List.filter_append] at h
  cases hX : X.filter p with
  | nil =>
    have hm : a ∈ X.filter p := List.mem_filter.2 ⟨ha, hp⟩
    rw [hX] at hm; cases hm
  | cons c cs =>
    rw [hX, List.cons_append, List.head?_cons] at h
    have hc : c ∈ X.filter p := by rw [hX]; simp
    cases h
    exact (List.mem_filter.1 hc).1

theorem head_filter_append_cases {α : Type*} (X Y : List α) (p : α → Bool) {b : α}
    (h : ((X ++ Y).filter p).head? = some b) : b ∈ X ∨ (Y.filter p).head? = some b := by
  rw [List.filter_append] at h
  cases hX : X.filter p with
  | nil =>
    rw [hX, List.nil_append] at h
    exact Or.inr h
  | cons c cs =>
    rw [hX, List.cons_append, List.head?_cons] at h
    have hc : c ∈ X.filter p := by rw [hX]; simp
    cases h
    exact Or.inl (List.mem_filter.1 hc).1

variable {object : FiniteObject.{u}} {Coordinate Chord : Type v}

/-! ## The canonical blocker is never an incidence blocker -/

theorem canonicalBlocker_ne_sharedDeclared_incidence
    (activation : DemandActivation object Coordinate Chord)
    (pair : Finset (object.Vertex × object.Vertex)) (e : object.Vertex × object.Vertex) :
    canonicalBlocker activation pair ≠
      some (Blocker.sharedDeclaredSupport (CarrierItem.incidence e)) := by
  classical
  intro h
  have hmem := canonicalBlocker_mem activation h
  rw [DemandActivation.sharedDeclaredSupport_mem_blockers_iff] at hmem
  obtain ⟨l, hl, r, hr, hlr, hsh⟩ := hmem
  have ends := DemandActivation.endpoints_mem_both_of_incidence_mem_sharedItems hsh
  have hv : Blocker.sharedDeclaredSupport (CarrierItem.vertex e.1) ∈
      activation.blockers pair :=
    (DemandActivation.sharedDeclaredSupport_mem_blockers_iff activation).2
      ⟨l, hl, r, hr, hlr, DemandActivation.vertex_mem_sharedItems ends.1 ends.2.2.1⟩
  rw [canonicalBlocker] at h
  simp only [List.map_append, List.map_map, List.append_assoc] at h
  have hb := head_filter_mem_of_prefix _ _ _
    (Blocker.sharedDeclaredSupport (CarrierItem.vertex e.1))
    (by simp [object.mem_orderedVertices]) (by simpa using hv) h
  simp at hb

theorem canonicalBlocker_ne_sharedReturn_incidence
    (activation : DemandActivation object Coordinate Chord)
    (pair : Finset (object.Vertex × object.Vertex)) (e : object.Vertex × object.Vertex) :
    canonicalBlocker activation pair ≠
      some (Blocker.sharedReturnSupport (CarrierItem.incidence e)) := by
  classical
  intro h
  have hmem := canonicalBlocker_mem activation h
  rw [DemandActivation.sharedReturnSupport_mem_blockers_iff] at hmem
  obtain ⟨l, hl, r, hr, hlr, hsh⟩ := hmem
  have ends := DemandActivation.endpoints_mem_both_of_incidence_mem_sharedItems hsh
  have hv : Blocker.sharedReturnSupport (CarrierItem.vertex e.1) ∈
      activation.blockers pair :=
    (DemandActivation.sharedReturnSupport_mem_blockers_iff activation).2
      ⟨l, hl, r, hr, hlr, DemandActivation.vertex_mem_sharedItems ends.1 ends.2.2.1⟩
  rw [canonicalBlocker] at h
  simp only [List.map_append, List.map_map, List.append_assoc] at h
  rcases head_filter_append_cases _ _ _ h with hb | h
  · simp at hb
  rcases head_filter_append_cases _ _ _ h with hb | h
  · simp at hb
  have hb := head_filter_mem_of_prefix _ _ _
    (Blocker.sharedReturnSupport (CarrierItem.vertex e.1))
    (by simp [object.mem_orderedVertices]) (by simpa using hv) h
  simp at hb

/-! ## Window charges exhibit a window edge inside `supp(B_π)` -/

variable (activation : DemandActivation object Coordinate Chord)
  (presentation : CarrierPresentation object Coordinate Chord)
  (threshold : Nat) (packing : Finset (Finset object.Vertex))

theorem window_charge_support {pair : Finset (object.Vertex × object.Vertex)}
    {e : object.Vertex × object.Vertex}
    (h : capacityCharge activation presentation threshold packing pair =
      some (.boundaryWindow e)) :
    e ∈ object.windowRemainderIncidences packing ∧
      e.1 ∈ chargeSupport activation presentation pair ∧
      e.2 ∈ chargeSupport activation presentation pair := by
  classical
  rw [capacityCharge] at h
  rcases hw : windowJoinChoice activation presentation packing pair with _ | inc
  · rw [hw] at h
    rcases hc : crossWindowChoice activation presentation packing pair with _ | inc'
    · rw [hc] at h
      rcases hv : remainderVertexChoice activation presentation threshold packing pair
        with _ | w
      · rw [hv] at h
        rcases hb : canonicalBlocker activation pair with _ | b
        · rw [hb] at h; cases h
        · rw [hb, Option.map_eq_some_iff] at h
          obtain ⟨_, _, h⟩ := h
          cases h
      · rw [hv] at h; cases h
    · rw [hc] at h; cases h
  · rw [hw] at h
    have he : inc = e := by simpa using h
    subst he
    have inside : inc ∈ (object.windowRemainderIncidences packing).filter fun c =>
        c.1 ∈ chargeSupport activation presentation pair ∧
          c.2 ∈ chargeSupport activation presentation pair := by
      simpa [windowJoinChoice] using
        List.mem_of_mem_head? (l := ((object.windowRemainderIncidences packing).filter
          fun c => c.1 ∈ chargeSupport activation presentation pair ∧
            c.2 ∈ chargeSupport activation presentation pair).toList) hw
    exact ⟨(Finset.mem_filter.1 inside).1, (Finset.mem_filter.1 inside).2⟩

theorem cross_charge_support {pair : Finset (object.Vertex × object.Vertex)}
    {e : object.Vertex × object.Vertex}
    (h : capacityCharge activation presentation threshold packing pair =
      some (.crossWindow e)) :
    e ∈ object.crossWindowIncidences packing ∧
      e.1 ∈ chargeSupport activation presentation pair ∧
      e.2 ∈ chargeSupport activation presentation pair := by
  classical
  rw [capacityCharge] at h
  rcases hw : windowJoinChoice activation presentation packing pair with _ | inc
  · rw [hw] at h
    rcases hc : crossWindowChoice activation presentation packing pair with _ | inc'
    · rw [hc] at h
      rcases hv : remainderVertexChoice activation presentation threshold packing pair
        with _ | w
      · rw [hv] at h
        rcases hb : canonicalBlocker activation pair with _ | b
        · rw [hb] at h; cases h
        · rw [hb, Option.map_eq_some_iff] at h
          obtain ⟨_, _, h⟩ := h
          cases h
      · rw [hv] at h; cases h
    · rw [hc] at h
      have he : inc' = e := by simpa using h
      subst he
      have inside : inc' ∈ (object.crossWindowIncidences packing).filter fun c =>
          c.1 ∈ chargeSupport activation presentation pair ∧
            c.2 ∈ chargeSupport activation presentation pair := by
        simpa [crossWindowChoice] using
          List.mem_of_mem_head? (l := ((object.crossWindowIncidences packing).filter
            fun c => c.1 ∈ chargeSupport activation presentation pair ∧
              c.2 ∈ chargeSupport activation presentation pair).toList) hc
      exact ⟨(Finset.mem_filter.1 inside).1, (Finset.mem_filter.1 inside).2⟩
  · rw [hw] at h; cases h

/-- **Every pair charged to `𝔗_W` is blocked by a coordinate or a chord set.**  Its
charge support contains two adjacent (hence distinct) vertices; vertex, return-vertex
and buffer blockers have singleton support, and incidence blockers are never
canonical. -/
theorem window_charge_kind {pair : Finset (object.Vertex × object.Vertex)}
    {t : CapacityToken object}
    (h : capacityCharge activation presentation threshold packing pair = some t)
    (ht : (∃ e, t = .boundaryWindow e) ∨ (∃ e, t = .crossWindow e)) :
    ∃ b, canonicalBlocker activation pair = some b ∧
      ((∃ c, b = .boundaryProfile c) ∨ (∃ c, b = .targetResponse c) ∨
        (∃ s, b = .arithmeticChordSet s)) := by
  classical
  obtain ⟨a, c, hadj, ha, hc⟩ : ∃ a c : object.Vertex, object.graph.Adj a c ∧
      a ∈ chargeSupport activation presentation pair ∧
      c ∈ chargeSupport activation presentation pair := by
    rcases ht with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · obtain ⟨hmem, h1, h2⟩ := window_charge_support activation presentation threshold
        packing h
      exact ⟨e.1, e.2, ((object.mem_windowRemainderIncidences_iff packing e).1 hmem).1,
        h1, h2⟩
    · obtain ⟨hmem, h1, h2⟩ := cross_charge_support activation presentation threshold
        packing h
      exact ⟨e.1, e.2, ((object.mem_crossWindowIncidences_iff packing e).1 hmem).1,
        h1, h2⟩
  have hne : a ≠ c := object.graph.ne_of_adj hadj
  rcases hb : canonicalBlocker activation pair with _ | b
  · simp [chargeSupport, hb] at ha
  refine ⟨b, rfl, ?_⟩
  simp only [chargeSupport, hb] at ha hc
  cases b with
  | sharedDeclaredSupport item =>
    cases item with
    | vertex w =>
      simp [Blocker.declaredSupport] at ha hc; exact absurd (ha.trans hc.symm) hne
    | incidence e =>
      exact absurd hb (canonicalBlocker_ne_sharedDeclared_incidence activation pair e)
  | sharedReturnSupport item =>
    cases item with
    | vertex w =>
      simp [Blocker.declaredSupport] at ha hc; exact absurd (ha.trans hc.symm) hne
    | incidence e =>
      exact absurd hb (canonicalBlocker_ne_sharedReturn_incidence activation pair e)
  | sharedLocalBuffer w =>
    simp [Blocker.declaredSupport] at ha hc; exact absurd (ha.trans hc.symm) hne
  | boundaryProfile c => exact Or.inl ⟨c, rfl⟩
  | targetResponse c => exact Or.inr (Or.inl ⟨c, rfl⟩)
  | arithmeticChordSet s => exact Or.inr (Or.inr ⟨s, rfl⟩)

/-- **Converse: an `R`–`W` edge in `supp(B_π)` forces a `boundaryWindow` charge.** -/
theorem window_charge_of_support_edge {pair : Finset (object.Vertex × object.Vertex)}
    {r w : object.Vertex} (hadj : object.graph.Adj r w)
    (hr : r ∈ object.remainderSupport packing) (hw : w ∈ windowSupport packing)
    (hrS : r ∈ chargeSupport activation presentation pair)
    (hwS : w ∈ chargeSupport activation presentation pair) :
    ∃ e, capacityCharge activation presentation threshold packing pair =
      some (.boundaryWindow e) := by
  classical
  have hmem : (r, w) ∈ (object.windowRemainderIncidences packing).filter fun c =>
      c.1 ∈ chargeSupport activation presentation pair ∧
        c.2 ∈ chargeSupport activation presentation pair :=
    Finset.mem_filter.2 ⟨(object.mem_windowRemainderIncidences_iff packing (r, w)).2
      ⟨hadj, hr, hw⟩, hrS, hwS⟩
  rcases hj : windowJoinChoice activation presentation packing pair with _ | e
  · exfalso
    have hnil : ((object.windowRemainderIncidences packing).filter fun c =>
        c.1 ∈ chargeSupport activation presentation pair ∧
          c.2 ∈ chargeSupport activation presentation pair).toList = [] := by
      have := hj
      simp only [windowJoinChoice] at this
      exact List.head?_eq_none_iff.1 (by convert this)
    have : (r, w) ∈ ((object.windowRemainderIncidences packing).filter fun c =>
        c.1 ∈ chargeSupport activation presentation pair ∧
          c.2 ∈ chargeSupport activation presentation pair).toList :=
      Finset.mem_toList.2 hmem
    rw [hnil] at this; cases this
  · exact ⟨e, by rw [capacityCharge, hj]⟩

/-! ## Geometry → charge: a connected support meeting `R` and `W` -/

theorem walk_crossing {V : Type*} {G : SimpleGraph V} (P : V → Prop) (S : V → Prop) :
    ∀ {x y : V} (p : G.Walk x y), P x → ¬ P y → (∀ z ∈ p.support, S z) →
      ∃ a b, G.Adj a b ∧ P a ∧ ¬ P b ∧ S a ∧ S b
  | _, _, .nil, hx, hy, _ => absurd hx hy
  | x, y, .cons (v := m) hxm q, hx, hy, hS => by
    by_cases hm : P m
    · exact walk_crossing P S q hm hy (fun z hz => hS z (by simp [hz]))
    · exact ⟨x, m, hxm, hx, hm, hS x (by simp), hS m (by simp)⟩

/-- A `ConnectedOn` support meeting `R` and `W` contains an `R`–`W` edge. -/
theorem connectedOn_crossing_edge {S : Finset object.Vertex}
    (hS : SupportComponents.Connected.ConnectedOn object S)
    {r w : object.Vertex} (hr : r ∈ S) (hw : w ∈ S)
    (hrR : r ∈ object.remainderSupport packing) (hwW : w ∈ windowSupport packing) :
    ∃ a b, object.graph.Adj a b ∧ a ∈ object.remainderSupport packing ∧
      b ∈ windowSupport packing ∧ a ∈ S ∧ b ∈ S := by
  classical
  obtain ⟨p, _, hp⟩ := hS.2 hr hw
  have hwR : w ∉ object.remainderSupport packing := by
    intro h; exact notMem_windowSupport_of_mem_remainderSupport h hwW
  obtain ⟨a, b, hab, ha, hb, haS, hbS⟩ :=
    walk_crossing (fun z => z ∈ object.remainderSupport packing) (fun z => z ∈ S) p hrR hwR hp
  refine ⟨a, b, hab, ha, ?_, haS, hbS⟩
  by_contra hbW
  apply hb
  simp only [remainderSupport, Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact hbW

/-- **A coordinate-blocked pair whose (connected) coordinate support meets both `R`
and `W` is charged to a `boundaryWindow` token of `𝔗_W`.** -/
theorem coordinate_spread_window_charge {pair : Finset (object.Vertex × object.Vertex)}
    {b : Blocker object Coordinate Chord} {c : Coordinate}
    (hb : canonicalBlocker activation pair = some b)
    (hc : b = .boundaryProfile c ∨ b = .targetResponse c)
    (hconn : SupportComponents.Connected.ConnectedOn object
      (presentation.coordinateSupport c))
    {r w : object.Vertex} (hr : r ∈ presentation.coordinateSupport c)
    (hw : w ∈ presentation.coordinateSupport c)
    (hrR : r ∈ object.remainderSupport packing) (hwW : w ∈ windowSupport packing) :
    ∃ e, capacityCharge activation presentation threshold packing pair =
      some (.boundaryWindow e) := by
  classical
  obtain ⟨a, a', hadj, haR, haW, haS, haS'⟩ :=
    connectedOn_crossing_edge packing hconn hr hw hrR hwW
  have hsupp : chargeSupport activation presentation pair =
      presentation.coordinateSupport c := by
    rcases hc with rfl | rfl <;> simp [chargeSupport, hb, Blocker.declaredSupport]
  exact window_charge_of_support_edge activation presentation threshold packing hadj haR
    haW (hsupp ▸ haS) (hsupp ▸ haS')

/-! ## Coordinate/chord-blocked pairs are fully separated -/

/-- **A pair whose canonical blocker is a coordinate or chord set has pairwise
disjoint declared supports `T ∪ Γ`, disjoint returns `R_p`, and disjoint buffers `T`**
(all clause (a)–(c) blockers precede it in the literal order).  With
`window_charge_kind`: every pair charged to `𝔗_W` is fully separated. -/
theorem separated_of_late_canonical
    (activation : DemandActivation object Coordinate Chord)
    {pair : Finset (object.Vertex × object.Vertex)} {b : Blocker object Coordinate Chord}
    (hb : canonicalBlocker activation pair = some b)
    (hlate : (∃ c, b = .boundaryProfile c) ∨ (∃ c, b = .targetResponse c) ∨
      (∃ s, b = .arithmeticChordSet s))
    {l r : object.Vertex × object.Vertex} (hl : l ∈ pair) (hr : r ∈ pair) (hlr : l ≠ r)
    (v : object.Vertex) :
    ¬ (v ∈ activation.declaredSupport l ∧ v ∈ activation.declaredSupport r) ∧
    ¬ (v ∈ activation.returnSupport l ∧ v ∈ activation.returnSupport r) ∧
    ¬ (v ∈ activation.localBuffer l ∧ v ∈ activation.localBuffer r) := by
  classical
  have hbl : ∀ x, b ≠ .sharedDeclaredSupport x ∧ b ≠ .sharedReturnSupport x ∧
      ∀ w, b ≠ .sharedLocalBuffer w := by
    intro x
    rcases hlate with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩ <;> simp
  rw [canonicalBlocker] at hb
  simp only [List.map_append, List.map_map, List.append_assoc] at hb
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ?_⟩
  · have hv : Blocker.sharedDeclaredSupport (CarrierItem.vertex v) ∈
        activation.blockers pair :=
      (DemandActivation.sharedDeclaredSupport_mem_blockers_iff activation).2
        ⟨l, hl, r, hr, hlr, DemandActivation.vertex_mem_sharedItems h1 h2⟩
    have hm := head_filter_mem_of_prefix _ _ _
      (Blocker.sharedDeclaredSupport (CarrierItem.vertex v))
      (by simp [object.mem_orderedVertices]) (by simpa using hv) hb
    simp only [List.mem_map, Function.comp_apply] at hm
    obtain ⟨w, _, hw⟩ := hm
    exact (hbl (CarrierItem.vertex w)).1 hw.symm
  · have hv : Blocker.sharedReturnSupport (CarrierItem.vertex v) ∈
        activation.blockers pair :=
      (DemandActivation.sharedReturnSupport_mem_blockers_iff activation).2
        ⟨l, hl, r, hr, hlr, DemandActivation.vertex_mem_sharedItems h1 h2⟩
    rcases head_filter_append_cases _ _ _ hb with hm | hb
    · simp only [List.mem_map, Function.comp_apply] at hm
      obtain ⟨w, _, hw⟩ := hm
      exact (hbl (CarrierItem.vertex w)).1 hw.symm
    rcases head_filter_append_cases _ _ _ hb with hm | hb
    · simp only [List.mem_map, Function.comp_apply] at hm
      obtain ⟨w, _, hw⟩ := hm
      exact (hbl _).1 hw.symm
    have hm := head_filter_mem_of_prefix _ _ _
      (Blocker.sharedReturnSupport (CarrierItem.vertex v))
      (by simp [object.mem_orderedVertices]) (by simpa using hv) hb
    simp only [List.mem_map, Function.comp_apply] at hm
    obtain ⟨w, _, hw⟩ := hm
    exact (hbl (CarrierItem.vertex w)).2.1 hw.symm
  · have hv : Blocker.sharedLocalBuffer v ∈ activation.blockers pair :=
      (DemandActivation.sharedLocalBuffer_mem_blockers_iff activation).2
        ⟨l, hl, r, hr, hlr, h1, h2⟩
    rcases head_filter_append_cases _ _ _ hb with hm | hb
    · simp only [List.mem_map, Function.comp_apply] at hm
      obtain ⟨w, _, hw⟩ := hm
      exact (hbl _).1 hw.symm
    rcases head_filter_append_cases _ _ _ hb with hm | hb
    · simp only [List.mem_map, Function.comp_apply] at hm
      obtain ⟨w, _, hw⟩ := hm
      exact (hbl _).1 hw.symm
    rcases head_filter_append_cases _ _ _ hb with hm | hb
    · simp only [List.mem_map, Function.comp_apply] at hm
      obtain ⟨w, _, hw⟩ := hm
      exact (hbl _).2.1 hw.symm
    rcases head_filter_append_cases _ _ _ hb with hm | hb
    · simp only [List.mem_map, Function.comp_apply] at hm
      obtain ⟨w, _, hw⟩ := hm
      exact (hbl _).2.1 hw.symm
    have hm := head_filter_mem_of_prefix _ _ _ (Blocker.sharedLocalBuffer v)
      (by simp [object.mem_orderedVertices]) (by simpa using hv) hb
    simp only [List.mem_map] at hm
    obtain ⟨w, _, hw⟩ := hm
    exact (hbl (CarrierItem.vertex w)).2.2 w hw.symm

/-! ## Where same-hub pairs go -/

/-- **`T(p) = {x(p)} ∪ s(p)` does not contain the hub `c(p)`** (while `R_p` does:
`pairResponseActivation_centre_mem_returnSupport_of_mem`). -/
theorem centre_not_mem_support {threshold : Nat} (port : SurplusPort object threshold) :
    port.centre ∉ port.support := by
  classical
  intro h
  simp only [SurplusPort.support, Finset.mem_insert] at h
  rcases h with h | h
  · exact object.graph.ne_of_adj port.adjacent h
  · exact ((port.mem_shoulders_iff port.centre).1 h).1 rfl

/-- **A shared return vertex forces an early canonical blocker**: a vertex blocker of
clause (a) or (b). -/
theorem early_of_shared_return
    (activation : DemandActivation object Coordinate Chord)
    {pair : Finset (object.Vertex × object.Vertex)}
    {l r : object.Vertex × object.Vertex} (hl : l ∈ pair) (hr : r ∈ pair) (hlr : l ≠ r)
    {c : object.Vertex} (hcl : c ∈ activation.returnSupport l)
    (hcr : c ∈ activation.returnSupport r) :
    ∃ w, canonicalBlocker activation pair =
        some (Blocker.sharedDeclaredSupport (CarrierItem.vertex w)) ∨
      canonicalBlocker activation pair =
        some (Blocker.sharedReturnSupport (CarrierItem.vertex w)) := by
  classical
  have hv : Blocker.sharedReturnSupport (CarrierItem.vertex c) ∈
      activation.blockers pair :=
    (DemandActivation.sharedReturnSupport_mem_blockers_iff activation).2
      ⟨l, hl, r, hr, hlr, DemandActivation.vertex_mem_sharedItems hcl hcr⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1
    (isSome_canonicalBlocker activation ⟨_, hv⟩)
  have hb0 := hb
  rw [canonicalBlocker] at hb
  simp only [List.map_append, List.map_map, List.append_assoc] at hb
  rcases head_filter_append_cases _ _ _ hb with hm | hb'
  · simp only [List.mem_map, Function.comp_apply] at hm
    obtain ⟨w, _, hw⟩ := hm
    exact ⟨w, Or.inl (hb0.trans (by rw [hw]))⟩
  rcases head_filter_append_cases _ _ _ hb' with hm | hb''
  · simp only [List.mem_map, Function.comp_apply] at hm
    obtain ⟨d, _, hd⟩ := hm
    exact absurd (hb0.trans (by rw [hd]))
      (canonicalBlocker_ne_sharedDeclared_incidence activation pair _)
  have hm := head_filter_mem_of_prefix _ _ _
    (Blocker.sharedReturnSupport (CarrierItem.vertex c))
    (by simp [object.mem_orderedVertices]) (by simpa using hv) hb''
  simp only [List.mem_map, Function.comp_apply] at hm
  obtain ⟨w, _, hw⟩ := hm
  exact ⟨w, Or.inr (hb0.trans (by rw [hw]))⟩

/-- **An early (vertex) canonical blocker is charged to a vertex token**: the remainder
unit of `w` (if `w` is a hub of `R`) or the primitive vertex token `w`.  Never `𝔗_W`. -/
theorem early_charge (presentation : CarrierPresentation object Coordinate Chord)
    (activation : DemandActivation object Coordinate Chord) (threshold : Nat)
    (packing : Finset (Finset object.Vertex))
    {pair : Finset (object.Vertex × object.Vertex)} {w : object.Vertex}
    (hb : canonicalBlocker activation pair =
        some (Blocker.sharedDeclaredSupport (CarrierItem.vertex w)) ∨
      canonicalBlocker activation pair =
        some (Blocker.sharedReturnSupport (CarrierItem.vertex w))) :
    (∃ j, capacityCharge activation presentation threshold packing pair =
        some (.remainder (w, j))) ∨
      capacityCharge activation presentation threshold packing pair =
        some (.primitive (.inl w)) := by
  classical
  have hsupp : chargeSupport activation presentation pair = {w} := by
    rcases hb with hb | hb <;> simp [chargeSupport, hb, Blocker.declaredSupport]
  have notLate : ∀ t, capacityCharge activation presentation threshold packing pair =
      some t → ¬ ((∃ e, t = .boundaryWindow e) ∨ (∃ e, t = .crossWindow e)) := by
    intro t ht hW
    obtain ⟨b, hb', hk⟩ := window_charge_kind activation presentation threshold packing ht hW
    rcases hb with hb | hb <;> rw [hb] at hb' <;> cases hb' <;>
      rcases hk with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  rcases hj : windowJoinChoice activation presentation packing pair with _ | e
  · rcases hc : crossWindowChoice activation presentation packing pair with _ | e
    · rcases hv : remainderVertexChoice activation presentation threshold packing pair
        with _ | v
      · right
        rw [capacityCharge, hj, hc, hv]
        rcases hb with hb | hb <;> simp [hb, Blocker.carrier]
      · left
        have inside : v ∈ (object.remainderSupport packing).filter fun c =>
            c ∈ chargeSupport activation presentation pair ∧ threshold < object.degree c := by
          simpa [remainderVertexChoice] using
            List.mem_of_mem_head? (l := ((object.remainderSupport packing).filter fun c =>
              c ∈ chargeSupport activation presentation pair ∧
                threshold < object.degree c).toList) hv
        have hvw : v = w := by
          have := (Finset.mem_filter.1 inside).2.1
          rw [hsupp] at this; simpa using this
        subst hvw
        exact ⟨_, by rw [capacityCharge, hj, hc, hv]⟩
    · exact absurd (Or.inr ⟨e, rfl⟩) (notLate _ (by rw [capacityCharge, hj, hc]))
  · exact absurd (Or.inl ⟨e, rfl⟩) (notLate _ (by rw [capacityCharge, hj]))

/-- **Same-hub port pairs at G's activation are early-blocked**, hence blocked (never
free), and charged to a vertex token (never to `𝔗_W`). -/
theorem sameHub_early {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {pair : Finset (object.Vertex × object.Vertex)}
    {p q : object.Vertex × object.Vertex} (hp : p ∈ pair) (hq : q ∈ pair) (hpq : p ≠ q)
    (hpE : p ∈ object.excessPorts threshold) (hqE : q ∈ object.excessPorts threshold)
    (hub : p.1 = q.1) :
    ∃ w, canonicalBlocker (pairResponseActivation active) pair =
        some (Blocker.sharedDeclaredSupport (CarrierItem.vertex w)) ∨
      canonicalBlocker (pairResponseActivation active) pair =
        some (Blocker.sharedReturnSupport (CarrierItem.vertex w)) :=
  early_of_shared_return (pairResponseActivation active) hp hq hpq
    (pairResponseActivation_centre_mem_returnSupport_of_mem active hpE)
    (hub ▸ pairResponseActivation_centre_mem_returnSupport_of_mem active hqE)

/-- The same at G's recorded activation `explicitActivation = recordSparsePairDEBlockers …`
(it keeps the return supports). -/
theorem sameHub_early_recorded {Baseline Target : FiniteObject.{u} → Prop}
    {LengthOK : Nat → Prop} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    {pair : Finset (object.Vertex × object.Vertex)}
    {p q : object.Vertex × object.Vertex} (hp : p ∈ pair) (hq : q ∈ pair) (hpq : p ≠ q)
    (hpE : p ∈ object.excessPorts threshold) (hqE : q ∈ object.excessPorts threshold)
    (hub : p.1 = q.1) :
    ∃ w, canonicalBlocker (recordSparsePairDEBlockers (Baseline := Baseline)
          (LengthOK := LengthOK) (pairResponseActivation active) pairs) pair =
        some (Blocker.sharedDeclaredSupport (CarrierItem.vertex w)) ∨
      canonicalBlocker (recordSparsePairDEBlockers (Baseline := Baseline)
          (LengthOK := LengthOK) (pairResponseActivation active) pairs) pair =
        some (Blocker.sharedReturnSupport (CarrierItem.vertex w)) :=
  early_of_shared_return _ hp hq hpq
    (show p.1 ∈ (pairResponseActivation active).returnSupport p from
      pairResponseActivation_centre_mem_returnSupport_of_mem active hpE)
    (show p.1 ∈ (pairResponseActivation active).returnSupport q from
      hub ▸ pairResponseActivation_centre_mem_returnSupport_of_mem active hqE)

/-- **A chord-blocked pair is window-charged only if two chord ends are adjacent.** -/
theorem window_chord_charge_close (activation : DemandActivation object Coordinate Chord)
    (presentation : CarrierPresentation object Coordinate Chord) (threshold : Nat)
    (packing : Finset (Finset object.Vertex))
    {pair : Finset (object.Vertex × object.Vertex)} {s : Finset Chord} {t : CapacityToken object}
    (hb : canonicalBlocker activation pair = some (.arithmeticChordSet s))
    (h : capacityCharge activation presentation threshold packing pair = some t)
    (ht : (∃ e, t = .boundaryWindow e) ∨ (∃ e, t = .crossWindow e)) :
    ∃ c ∈ s, ∃ c' ∈ s, ∃ a b, (a = (presentation.chordEnds c).1 ∨ a = (presentation.chordEnds c).2) ∧
      (b = (presentation.chordEnds c').1 ∨ b = (presentation.chordEnds c').2) ∧
      object.graph.Adj a b := by
  classical
  obtain ⟨a, b, hadj, ha, hb'⟩ : ∃ a b : object.Vertex, object.graph.Adj a b ∧
      a ∈ chargeSupport activation presentation pair ∧
      b ∈ chargeSupport activation presentation pair := by
    rcases ht with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · obtain ⟨hmem, h1, h2⟩ := window_charge_support activation presentation threshold packing h
      exact ⟨e.1, e.2, ((object.mem_windowRemainderIncidences_iff packing e).1 hmem).1, h1, h2⟩
    · obtain ⟨hmem, h1, h2⟩ := cross_charge_support activation presentation threshold packing h
      exact ⟨e.1, e.2, ((object.mem_crossWindowIncidences_iff packing e).1 hmem).1, h1, h2⟩
  simp only [chargeSupport, hb, Blocker.declaredSupport, Finset.mem_biUnion,
    Finset.mem_insert, Finset.mem_singleton] at ha hb'
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨c', hc', hb'⟩ := hb'
  exact ⟨c, hc, c', hc', a, b, ha, hb', hadj⟩

/-- **Clause (d) is empty at G's recorded activation** (live
`not_sparsePairDEProfileObstructionAt`): no pair has a profile coordinate blocker, so
the coordinate-blocked pairs are exactly the clause-(e) (target-response) ones. -/
theorem recorded_profile_empty {Baseline Target : FiniteObject.{u} → Prop}
    {LengthOK : Nat → Prop} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (pair : Finset (object.Vertex × object.Vertex)) :
    (recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
      (pairResponseActivation active) pairs).profileObstructions pair = [] := by
  classical
  simp only [recordSparsePairDEBlockers]
  rw [if_neg (not_sparsePairDEProfileObstructionAt _ _ _)]

/-- **Item 5: a pair whose charge support lies in `R` is never window-charged.**  With the
witness carrier `Z ⊇ X_{π₁} ∪ X_{π₂}`: if `Z ⊆ R`, the witness's own pairs are charged to
`𝔗_R ∪ 𝔗_prim` only. -/
theorem no_window_charge_of_support_in_R
    (activation : DemandActivation object Coordinate Chord)
    (presentation : CarrierPresentation object Coordinate Chord) (threshold : Nat)
    (packing : Finset (Finset object.Vertex))
    {pair : Finset (object.Vertex × object.Vertex)}
    (hR : ∀ v ∈ chargeSupport activation presentation pair,
      v ∈ object.remainderSupport packing) (e : object.Vertex × object.Vertex) :
    capacityCharge activation presentation threshold packing pair ≠ some (.boundaryWindow e) ∧
      capacityCharge activation presentation threshold packing pair ≠
        some (.crossWindow e) := by
  classical
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hmem, _, h2⟩ := window_charge_support activation presentation threshold packing h
    have hW := ((object.mem_windowRemainderIncidences_iff packing e).1 hmem).2.2
    exact notMem_windowSupport_of_mem_remainderSupport (hR _ h2) hW
  · obtain ⟨hmem, h1, _⟩ := cross_charge_support activation presentation threshold packing h
    obtain ⟨_, member, present, inside, _⟩ :=
      (object.mem_crossWindowIncidences_iff packing e).1 hmem
    exact notMem_windowSupport_of_mem_remainderSupport (hR _ h1)
      (mem_windowSupport present inside)


/-! ## The target-response obstruction -/

section ClauseE






/-- **Every clause-(e) obstruction at G is a residual target defect.** -/
theorem responseObstruction_targetDefect {LengthOK : Nat → Prop} {threshold : Nat}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (pair : Finset (object.Vertex × object.Vertex))
    (hrepl : ∀ S : Finset object.Vertex, ¬ ReplacementSupport
      (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object S)
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold H → HasCycleWithLength LengthOK H)
    (h : SparsePairDEResponseObstructionAt (Baseline := MinimumDegreeAtLeast threshold)
      (LengthOK := LengthOK) activation pairs pair) :
    ∃ attempt : AttemptedQuotient (MinimumDegreeAtLeast threshold)
        (HasCycleWithLength LengthOK) object (activation.pairFamily pairs)
        sparsePairCoordinateSupport,
    ∃ determiners : Finset object.PairCoordinate,
      SparsePairDetermination (Baseline := MinimumDegreeAtLeast threshold)
          (LengthOK := LengthOK) activation pairs pair attempt determiners ∧
        ResidualTargetDefect (HasCycleWithLength LengthOK) object
          (@insert _ _ (@Finset.instInsert _ (Classical.decEq _))
            (FiniteObject.DemandActivation.pairCoordinate pair
              ((activation.pairSupport pair).getD ∅))
            determiners) sparsePairCoordinateSupport := by
  obtain ⟨attempt, determiners, hdet, hor⟩ := h
  rcases hor with hd | hr | ⟨_, rep, hlt, hb, hback⟩
  · exact ⟨attempt, determiners, hdet, hd⟩
  · exact (hrepl _ hr).elim
  · exact (avoid (hback (minimal rep hlt hb))).elim


end ClauseE


/-! ## The facts as propositions -/

section Bundles

variable {object : FiniteObject.{u}} {Coordinate Chord : Type v}

/-- **The window structure of the capacity charge**: every pair charged to `𝔗_W` has a
coordinate or chord-set canonical blocker; a pair with such a blocker is fully separated
(disjoint declared supports, returns and buffers); a coordinate blocker whose connected
support meets `R` and `W` is charged to a `boundaryWindow` token; a pair whose charge support
lies in `R` is never window-charged; an early (vertex) blocker is charged to a vertex token;
a chord-blocked pair is window-charged only if two chord ends are adjacent. -/
def WindowChargeStructure (activation : DemandActivation object Coordinate Chord)
    (presentation : CarrierPresentation object Coordinate Chord) (threshold : Nat)
    (packing : Finset (Finset object.Vertex)) : Prop :=
  (∀ (pair : Finset (object.Vertex × object.Vertex)) (t : CapacityToken object),
      capacityCharge activation presentation threshold packing pair = some t →
      ((∃ e, t = .boundaryWindow e) ∨ (∃ e, t = .crossWindow e)) →
      ∃ b, canonicalBlocker activation pair = some b ∧
        ((∃ c, b = .boundaryProfile c) ∨ (∃ c, b = .targetResponse c) ∨
          (∃ s, b = .arithmeticChordSet s))) ∧
  (∀ (pair : Finset (object.Vertex × object.Vertex)) (b : Blocker object Coordinate Chord),
      canonicalBlocker activation pair = some b →
      ((∃ c, b = .boundaryProfile c) ∨ (∃ c, b = .targetResponse c) ∨
        (∃ s, b = .arithmeticChordSet s)) →
      ∀ l ∈ pair, ∀ r ∈ pair, l ≠ r → ∀ v : object.Vertex,
        ¬ (v ∈ activation.declaredSupport l ∧ v ∈ activation.declaredSupport r) ∧
        ¬ (v ∈ activation.returnSupport l ∧ v ∈ activation.returnSupport r) ∧
        ¬ (v ∈ activation.localBuffer l ∧ v ∈ activation.localBuffer r)) ∧
  (∀ (pair : Finset (object.Vertex × object.Vertex)) (b : Blocker object Coordinate Chord)
      (c : Coordinate), canonicalBlocker activation pair = some b →
      (b = .boundaryProfile c ∨ b = .targetResponse c) →
      SupportComponents.Connected.ConnectedOn object (presentation.coordinateSupport c) →
      ∀ r w, r ∈ presentation.coordinateSupport c → w ∈ presentation.coordinateSupport c →
        r ∈ object.remainderSupport packing → w ∈ windowSupport packing →
        ∃ e, capacityCharge activation presentation threshold packing pair =
          some (.boundaryWindow e)) ∧
  (∀ pair : Finset (object.Vertex × object.Vertex),
      (∀ v ∈ chargeSupport activation presentation pair, v ∈ object.remainderSupport packing) →
      ∀ e, capacityCharge activation presentation threshold packing pair ≠
          some (.boundaryWindow e) ∧
        capacityCharge activation presentation threshold packing pair ≠ some (.crossWindow e)) ∧
  (∀ (pair : Finset (object.Vertex × object.Vertex)) (w : object.Vertex),
      (canonicalBlocker activation pair =
          some (Blocker.sharedDeclaredSupport (CarrierItem.vertex w)) ∨
        canonicalBlocker activation pair =
          some (Blocker.sharedReturnSupport (CarrierItem.vertex w))) →
      (∃ j, capacityCharge activation presentation threshold packing pair =
          some (.remainder (w, j))) ∨
        capacityCharge activation presentation threshold packing pair =
          some (.primitive (.inl w))) ∧
  (∀ (pair : Finset (object.Vertex × object.Vertex)) (s : Finset Chord)
      (t : CapacityToken object),
      canonicalBlocker activation pair = some (.arithmeticChordSet s) →
      capacityCharge activation presentation threshold packing pair = some t →
      ((∃ e, t = .boundaryWindow e) ∨ (∃ e, t = .crossWindow e)) →
      ∃ c ∈ s, ∃ c' ∈ s, ∃ a b, (a = (presentation.chordEnds c).1 ∨
          a = (presentation.chordEnds c).2) ∧
        (b = (presentation.chordEnds c').1 ∨ b = (presentation.chordEnds c').2) ∧
        object.graph.Adj a b)

theorem windowChargeStructure (activation : DemandActivation object Coordinate Chord)
    (presentation : CarrierPresentation object Coordinate Chord) (threshold : Nat)
    (packing : Finset (Finset object.Vertex)) :
    WindowChargeStructure activation presentation threshold packing :=
  ⟨fun _ _ h ht => window_charge_kind activation presentation threshold packing h ht,
    fun _ _ hb hlate _ hl _ hr hlr v => separated_of_late_canonical activation hb hlate hl hr hlr v,
    fun _ _ _ hb hc hconn _ _ hr hw hrR hwW =>
      coordinate_spread_window_charge activation presentation threshold packing hb hc hconn hr hw
        hrR hwW,
    fun _ hR e => no_window_charge_of_support_in_R activation presentation threshold packing hR e,
    fun _ _ hb => early_charge presentation activation threshold packing hb,
    fun _ _ _ hb h ht => window_chord_charge_close activation presentation threshold packing hb h ht⟩

/-- **The recorded activation of an active family**: two ports of one hub in a pair force
an early (vertex) canonical blocker, and no pair has a profile obstruction. -/
def RecordedActivationFacts {Baseline Target : FiniteObject.{u} → Prop}
    {LengthOK : Nat → Prop} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (pairs : Finset (Finset (object.Vertex × object.Vertex))) : Prop :=
  (∀ (pair : Finset (object.Vertex × object.Vertex)) (p q : object.Vertex × object.Vertex),
      p ∈ pair → q ∈ pair → p ≠ q → p ∈ object.excessPorts threshold →
      q ∈ object.excessPorts threshold → p.1 = q.1 →
      ∃ w, canonicalBlocker (recordSparsePairDEBlockers (Baseline := Baseline)
            (LengthOK := LengthOK) (pairResponseActivation active) pairs) pair =
          some (Blocker.sharedDeclaredSupport (CarrierItem.vertex w)) ∨
        canonicalBlocker (recordSparsePairDEBlockers (Baseline := Baseline)
            (LengthOK := LengthOK) (pairResponseActivation active) pairs) pair =
          some (Blocker.sharedReturnSupport (CarrierItem.vertex w))) ∧
  (∀ pair : Finset (object.Vertex × object.Vertex),
      (recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
        (pairResponseActivation active) pairs).profileObstructions pair = [])

theorem recordedActivationFacts {Baseline Target : FiniteObject.{u} → Prop}
    {LengthOK : Nat → Prop} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (pairs : Finset (Finset (object.Vertex × object.Vertex))) :
    RecordedActivationFacts active pairs :=
  ⟨fun _ _ _ hp hq hpq hpE hqE hub => sameHub_early_recorded active pairs hp hq hpq hpE hqE hub,
    fun pair => recorded_profile_empty active pairs pair⟩

end Bundles

/-- **Every target-response obstruction is a residual target defect** at an activation of
an object with no replacement support, no accepted cycle and lexicographic minimality. -/
def ResponseObstructionsAreTargetDefects {LengthOK : Nat → Prop} {threshold : Nat}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex))) : Prop :=
  ∀ pair : Finset (object.Vertex × object.Vertex),
    SparsePairDEResponseObstructionAt (Baseline := MinimumDegreeAtLeast threshold)
      (LengthOK := LengthOK) activation pairs pair →
    ∃ attempt : AttemptedQuotient (MinimumDegreeAtLeast threshold)
        (HasCycleWithLength LengthOK) object (activation.pairFamily pairs)
        sparsePairCoordinateSupport,
    ∃ determiners : Finset object.PairCoordinate,
      SparsePairDetermination (Baseline := MinimumDegreeAtLeast threshold)
          (LengthOK := LengthOK) activation pairs pair attempt determiners ∧
        ResidualTargetDefect (HasCycleWithLength LengthOK) object
          (@insert _ _ (@Finset.instInsert _ (Classical.decEq _))
            (FiniteObject.DemandActivation.pairCoordinate pair
              ((activation.pairSupport pair).getD ∅))
            determiners) sparsePairCoordinateSupport

theorem responseObstructionsAreTargetDefects {LengthOK : Nat → Prop} {threshold : Nat}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (hrepl : ∀ S : Finset object.Vertex, ¬ ReplacementSupport
      (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object S)
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold H → HasCycleWithLength LengthOK H) :
    ResponseObstructionsAreTargetDefects (LengthOK := LengthOK) (threshold := threshold)
      activation pairs :=
  fun pair h => responseObstruction_targetDefect activation pairs pair hrepl avoid minimal h

end Hypostructure.Graph.WindowChargeKinds
