/- The accepted S1child1.lean follows verbatim as a source dependency.
Its compiled module is not in the read-only import cache. No child-1 proof
is modified or reconstructed; the new child-2 declarations start below. -/
import Hypostructure.Graph.Statements.SparseExitReadings
import HypostructureErdos64EG.Assembly.Residuals

/-! Child 1 only: first boundary contacts on the unchanged original cycle. -/
namespace Hypostructure.Graph.S1child1

open SimpleGraph
universe u

private theorem rotated_eq_of_head {α : Type*} {l m : List α}
    (hn : l.Nodup) (hr : l.IsRotated m) (hh : l.head? = m.head?) : l = m := by
  obtain ⟨n, rfl⟩ := hr
  by_cases he : l = []
  · simp [he]
  have hpos : 0 < l.length := List.length_pos_of_ne_nil he
  have hm : n % l.length < l.length := Nat.mod_lt _ hpos
  have hz : n % l.length = 0 := by
    rw [← List.rotate_mod l n] at hh
    rw [List.head?_rotate hm, List.head?_eq_getElem?] at hh
    simp only [List.getElem?_eq_getElem hpos, List.getElem?_eq_getElem hm] at hh
    exact (hn.getElem_inj_iff.mp (Option.some.inj hh)).symm
  rw [← List.rotate_mod l n, hz, List.rotate_zero]

private theorem rotated_eq_of_last {α : Type*} {l m : List α}
    (hn : l.Nodup) (hr : l.IsRotated m) (hh : l.getLast? = m.getLast?) : l = m := by
  have := rotated_eq_of_head (List.nodup_reverse.mpr hn) hr.reverse (by simpa using hh)
  exact List.reverse_injective this

private theorem last_tail_support {V : Type*} {H : SimpleGraph V} {x y : V}
    (p : H.Walk x y) (hp : ¬ p.Nil) : p.support.tail.getLast? = some y := by
  rw [List.getLast?_tail, p.length_support, if_neg]
  · rw [List.getLast?_eq_some_getLast p.support_ne_nil, p.getLast_support]
  · have := Walk.not_nil_iff_lt_length.mp hp
    omega

/-- A simple cycle's cyclic order and base vertex determine the walk exactly. -/
private theorem eq_of_cyclic_order {V : Type*} {H : SimpleGraph V} {a : V}
    {p q : H.Walk a a} (hp : p.IsCycle)
    (hr : p.support.tail.IsRotated q.support.tail) : p = q := by
  have hq : ¬ q.Nil := by
    intro hz
    have hz' : q.length = 0 := Walk.length_eq_zero_iff.mpr hz
    have hl := hr.perm.length_eq
    simp only [List.length_tail, Walk.length_support, Nat.add_sub_cancel] at hl
    have := hp.three_le_length
    omega
  apply Walk.ext_support
  have he := rotated_eq_of_last hp.support_nodup hr
    ((last_tail_support p hp.not_nil).trans (last_tail_support q hq).symm)
  simpa only [Walk.cons_tail_support] using congrArg (List.cons a) he

/-- Cut a finite walk at its first vertex in a specified set. -/
private theorem first_contact {V : Type*} {H : SimpleGraph V} (B : V → Prop)
    {x y : V} (p : H.Walk x y) (hex : ∃ z ∈ p.support, B z) :
    ∃ (b : V) (front : H.Walk x b) (back : H.Walk b y),
      B b ∧ p = front.append back ∧
      (∀ z ∈ front.support, B z → z = b) := by
  classical
  induction p with
  | @nil x =>
      obtain ⟨z, hz, hb⟩ := hex
      simp only [Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact ⟨x, .nil, .nil, hb, rfl, by simp⟩
  | @cons x t y adj rest ih =>
      by_cases hx : B x
      · exact ⟨x, .nil, .cons adj rest, hx, rfl, by simp⟩
      · have hex' : ∃ z ∈ rest.support, B z := by
          obtain ⟨z, hz, hb⟩ := hex
          rcases List.mem_cons.mp hz with rfl | hz
          · exact (hx hb).elim
          · exact ⟨z, hz, hb⟩
        obtain ⟨b, front, back, hb, he, hf⟩ := ih hex'
        refine ⟨b, .cons adj front, back, hb, ?_, ?_⟩
        · simp [he]
        · intro z hz hB
          rcases List.mem_cons.mp hz with rfl | hz
          · exact (hx hB).elim
          · exact hf z hz hB


/-- First contacts on a finite simple cycle. The two cuts are made in the
original directed cyclic order; the complementary walk is retained. -/
private theorem cycle_first_contacts {V : Type*} {H : SimpleGraph V}
    [DecidableEq V] {v x : V} (c : H.Walk v v) (hc : c.IsCycle)
    (B : V → Prop) (hx : x ∈ c.support) (hxB : ¬ B x)
    (hB : ∃ z₁ z₂, z₁ ≠ z₂ ∧ z₁ ∈ c.support ∧ z₂ ∈ c.support ∧ B z₁ ∧ B z₂) :
    ∃ (a b : V) (ha : a ∈ c.support) (_hb : b ∈ c.support)
      (q : H.Walk a b) (r : H.Walk b a),
      B a ∧ B b ∧ a ≠ b ∧
      c.rotate a ha = q.append r ∧
      q.length + r.length = c.length ∧
      q.length < c.length ∧ 0 < r.length ∧ q.IsPath ∧
      (∃ k, 0 < k ∧ k < q.length ∧ q.getVert k = x) ∧
      (∀ k, 0 < k → k < q.length → ¬ B (q.getVert k)) := by
  classical
  let d := c.rotate x hx
  have hd : d.IsCycle := hc.rotate hx
  have memd (z : V) : z ∈ d.support ↔ z ∈ c.support := c.mem_support_rotate_iff x hx
  obtain ⟨z₁, z₂, hz, hz₁, hz₂, hB₁, hB₂⟩ := hB
  obtain ⟨b, p, back, hbB, ed, hpB⟩ := first_contact B d ⟨z₁, (memd z₁).mpr hz₁, hB₁⟩
  have hxb : x ≠ b := fun h => hxB (h ▸ hbB)
  have hp : ¬ p.Nil := Walk.not_nil_of_ne hxb
  have hback : back.IsPath := Walk.IsCycle.isPath_of_append_right hp (ed ▸ hd)
  obtain ⟨a, l, m, haB, em, hlB⟩ := first_contact B back.reverse
    ⟨b, by simp, hbB⟩
  let s := l.reverse
  let r := m.reverse
  let q := s.append p
  have hxa : x ≠ a := fun h => hxB (h ▸ haB)
  have hl : ¬ l.Nil := Walk.not_nil_of_ne hxa
  have es : back = r.append s := by
    have he := congrArg Walk.reverse em
    simpa only [Walk.reverse_reverse, Walk.reverse_append] using he
  have ed' : d = p.append (r.append s) := ed.trans (congrArg (p.append ·) es)
  have hrpath : r.IsPath := by
    have hm : m.IsPath := Walk.IsPath.of_append_right (em ▸ hback.reverse)
    exact hm.reverse
  have hbound : ∀ z ∈ q.support, B z → z = a ∨ z = b := by
    intro z hz hB
    rcases (Walk.mem_support_append_iff s p).mp hz with hz | hz
    · exact Or.inl (hlB z (by simpa [s] using hz) hB)
    · exact Or.inr (hpB z hz hB)
  have hab : a ≠ b := by
    intro he
    subst b
    have er : r = .nil := (Walk.isPath_iff_nil.mp hrpath).eq_nil
    have only (z : V) (hz : z ∈ d.support) (hBz : B z) : z = a := by
      rw [ed', er, Walk.nil_append, Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · exact hpB z hz hBz
      · exact hlB z (by simpa [s] using hz) hBz
    exact hz ((only z₁ ((memd z₁).mpr hz₁) hB₁).trans
      (only z₂ ((memd z₂).mpr hz₂) hB₂).symm)
  have ha : a ∈ c.support := (memd a).mp (by
    rw [ed', Walk.mem_support_append_iff, Walk.mem_support_append_iff]
    exact Or.inr (Or.inl r.end_mem_support))
  have hb : b ∈ c.support := (memd b).mp (by
    rw [ed', Walk.mem_support_append_iff]
    exact Or.inl p.end_mem_support)
  have cyclic : (q.append r).support.tail.IsRotated d.support.tail := by
    rw [ed']
    simpa only [q, Walk.tail_support_append, List.append_assoc] using
      (List.isRotated_append (l := s.support.tail)
        (l' := p.support.tail ++ r.support.tail))
  have erot : c.rotate a ha = q.append r :=
    eq_of_cyclic_order (hc.rotate ha)
      ((c.support_rotate a ha).trans ((c.support_rotate x hx).symm.trans cyclic.symm))
  have hlen : q.length + r.length = c.length := by
    have he := congrArg Walk.length erot
    simpa only [Walk.length_rotate, Walk.length_append] using he.symm
  have hr : ¬ r.Nil := Walk.not_nil_of_ne hab.symm
  have hrpos : 0 < r.length := Walk.not_nil_iff_lt_length.mp hr
  have hqpath : q.IsPath := Walk.IsCycle.isPath_of_append_left hr (erot ▸ hc.rotate ha)
  refine ⟨a, b, ha, hb, q, r, haB, hbB, hab, erot, hlen, by omega, hrpos, hqpath, ?_, ?_⟩
  · refine ⟨s.length, ?_, ?_, ?_⟩
    · simpa [s] using Walk.not_nil_iff_lt_length.mp hl
    · have hppos := Walk.not_nil_iff_lt_length.mp hp
      simp only [q, Walk.length_append]
      omega
    · simp [q, Walk.getVert_append]
  · intro k hk hkl hBk
    rcases hbound (q.getVert k) (q.getVert_mem_support k) hBk with he | he
    · have := (hqpath.getVert_eq_start_iff hkl.le).mp he
      omega
    · have := (hqpath.getVert_eq_end_iff hkl.le).mp he
      omega


open Classical in
/-- The exact boundary-to-boundary interval of the original certificate.
`private_index` identifies the retained occurrence. The absence of a boundary
at every strictly internal index says that `a` and `b` are the first contacts
in the two directions from that occurrence. `rotation` records the complete
cyclic edge order, including crossing the original basepoint. -/
structure BoundaryInterval {boundary : Boundary.{u}} {P : BoundaryPiece boundary}
    {O : OutsideContext boundary} {LengthOK : Nat → Prop}
    (c : CycleCertificate (glue P O) LengthOK) (x : GluedVertex P O) where
  a : boundary.Vertex
  b : boundary.Vertex
  distinct : a ≠ b
  a_occurs : Sum.inl a ∈ c.walk.support
  b_occurs : Sum.inl b ∈ c.walk.support
  q : (glue P O).graph.Walk (.inl a) (.inl b)
  r : (glue P O).graph.Walk (.inl b) (.inl a)
  rotation : c.walk.rotate (.inl a) a_occurs = q.append r
  length_partition : q.length + r.length = c.walk.length
  proper : q.length < c.walk.length
  complement_positive : 0 < r.length
  simple : q.IsPath
  private_index : Nat
  private_index_pos : 0 < private_index
  private_index_lt : private_index < q.length
  private_occurrence : q.getVert private_index = x
  no_internal_boundary : ∀ k, 0 < k → k < q.length →
    ∀ z : boundary.Vertex, q.getVert k ≠ Sum.inl z

/-- Specialize the finite-cycle construction to the labelled glued carrier. -/
theorem boundaryInterval_of_twoLabels {boundary : Boundary.{u}}
    {P : BoundaryPiece boundary} {O : OutsideContext boundary} {LengthOK : Nat → Prop}
    (c : CycleCertificate (glue P O) LengthOK) (x : GluedVertex P O)
    (hx : x ∈ c.walk.support) (hxB : ∀ a : boundary.Vertex, x ≠ Sum.inl a)
    (labels : DefectGeometry.TwoLabels c) : Nonempty (BoundaryInterval c x) := by
  classical
  obtain ⟨z₁, z₂, hz, hz₁, hz₂⟩ := labels
  obtain ⟨a, b, ha, hb, q, r, ⟨a', ea⟩, ⟨b', eb⟩, hab, erot,
    hlen, hproper, hrpos, hpath, ⟨k, hk, hkl, hkx⟩, hfree⟩ :=
    cycle_first_contacts c.walk c.isCycle
      (fun z => ∃ label : boundary.Vertex, z = Sum.inl label) hx
      (by rintro ⟨a, he⟩; exact hxB a he)
      ⟨Sum.inl z₁, Sum.inl z₂, (fun he => hz (Sum.inl.inj he)),
        hz₁, hz₂, ⟨z₁, rfl⟩, ⟨z₂, rfl⟩⟩
  subst a
  subst b
  exact ⟨{
    a := a'
    b := b'
    distinct := fun he => hab (congrArg Sum.inl he)
    a_occurs := ha
    b_occurs := hb
    q := q
    r := r
    rotation := erot
    length_partition := hlen
    proper := hproper
    complement_positive := hrpos
    simple := hpath
    private_index := k
    private_index_pos := hk
    private_index_lt := hkl
    private_occurrence := hkx
    no_internal_boundary := fun i hi hil z he => hfree i hi hil ⟨z, he⟩
  }⟩

open Strategy.Spine Strategy.InterfaceReplacement

/-- Apply the accepted same-certificate geometry and the cycle-free reading
exclusion, then cut at the actual supplied `pr`. No new private vertex,
certificate, support, or context is selected. -/
theorem retained_firstContacts {data : Parameters} {G : FiniteObject.{u}}
    (w : SparseTargetDefectWitness data G)
    (free : WitnessReadingsCycleFreeAtWitness w)
    {P N : Finset G.Vertex} (orientation : w.Orientation P N)
    (separates : w.Separates P N)
    (c : CycleCertificate (glue (SupportAtom.retainedPiece G w.support P) w.outside)
      data.LengthOK)
    (pl pr : (SupportAtom.boundary G w.support).Vertex ⊕
      SupportAtom.PieceInternal G w.support)
    (edge : s(pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pl,
      pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr) ∈ c.walk.edges)
    (internal : SupportAtom.pieceDecode G w.support pr ∉ SupportAtom.cutBoundary G w.support) :
    Nonempty (BoundaryInterval c
      (pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr)) := by
  classical
  have pieceFree : ¬ HasCycleWithLength data.LengthOK
      (SupportAtom.retainedPiece G w.support P).pack := by
    rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact free.1
    · exact free.2
  have contextFree : ¬ HasCycleWithLength data.LengthOK w.outside.pack := by
    intro yes
    exact separates.2 (hasCycleWithLength_of_hom
      (contextHom (SupportAtom.retainedPiece G w.support N) w.outside)
      (contextEmbedding (SupportAtom.retainedPiece G w.support N) w.outside).injective yes)
  have labels := (DefectGeometry.realized_mixed c
    (DefectGeometry.pieceExclusive c contextFree) pieceFree).2
  apply boundaryInterval_of_twoLabels c _ (c.walk.snd_mem_support_of_mem_edges edge) _ labels
  intro a he
  cases pr with
  | inl b => exact internal b.property
  | inr i => cases he


open HypostructureErdos64EG

/-- Child 1 on the complete residual, for the very tuple and endpoints already
supplied by f118. The only residual projection needed here is f029; its
canonical witness is identified with `w` by the two `some` equalities. -/
theorem firstContacts_on_residual {selected : EGInput.{u}}
    (residual : Node20aOutcome selected)
    (w : SparseTargetDefectWitness spineData.{u}.toParameters selected.object)
    (canonical : sparseTargetDefectWitness spineData.{u}.toParameters selected.object = some w)
    (_spec : w.Spec) {P N : Finset selected.object.Vertex}
    (orientation : w.Orientation P N) (separates : w.Separates P N)
    (_private : w.CyclesUsePrivateEdge P N)
    (c : CycleCertificate
      (glue (SupportAtom.retainedPiece selected.object w.support P) w.outside)
      spineData.{u}.toParameters.LengthOK)
    (pl pr : (SupportAtom.boundary selected.object w.support).Vertex ⊕
      SupportAtom.PieceInternal selected.object w.support)
    (supplied :
      s(pieceEmbedding (SupportAtom.retainedPiece selected.object w.support P) w.outside pl,
        pieceEmbedding (SupportAtom.retainedPiece selected.object w.support P) w.outside pr)
        ∈ c.walk.edges ∧
      selected.object.graph.Adj (SupportAtom.pieceDecode selected.object w.support pl)
        (SupportAtom.pieceDecode selected.object w.support pr) ∧
      SupportAtom.pieceDecode selected.object w.support pl ∈ P ∧
      SupportAtom.pieceDecode selected.object w.support pr ∈ P ∧
      SupportAtom.pieceDecode selected.object w.support pr ∉ N ∧
      SupportAtom.pieceDecode selected.object w.support pr ∉
        SupportAtom.cutBoundary selected.object w.support) :
    Nonempty (BoundaryInterval c
      (pieceEmbedding (SupportAtom.retainedPiece selected.object w.support P) w.outside pr)) := by
  have f029 : WitnessReadingsCycleFreeStatement spineData.{u}.toParameters selected.object :=
    residual.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨w', canonical', free⟩ := f029
  have same : w' = w := Option.some.inj (canonical'.symm.trans canonical)
  subst w'
  exact retained_firstContacts w free orientation separates c pl pr
    supplied.1 supplied.2.2.2.2.2

/-- The f118 private-edge data, augmented only by the exact interval through
its supplied endpoint, for every original positive certificate. -/
def CyclesHaveFirstContacts {data : Parameters} {G : FiniteObject.{u}}
    (w : SparseTargetDefectWitness data G) (P N : Finset G.Vertex) : Prop :=
  ∀ c : CycleCertificate (glue (SupportAtom.retainedPiece G w.support P) w.outside)
      data.LengthOK,
    ∃ pl pr : (SupportAtom.boundary G w.support).Vertex ⊕ SupportAtom.PieceInternal G w.support,
      (s(pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pl,
         pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr) ∈ c.walk.edges ∧
       G.graph.Adj (SupportAtom.pieceDecode G w.support pl)
         (SupportAtom.pieceDecode G w.support pr) ∧
       SupportAtom.pieceDecode G w.support pl ∈ P ∧
       SupportAtom.pieceDecode G w.support pr ∈ P ∧
       SupportAtom.pieceDecode G w.support pr ∉ N ∧
       SupportAtom.pieceDecode G w.support pr ∉ SupportAtom.cutBoundary G w.support) ∧
      Nonempty (BoundaryInterval c
        (pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr))

/-- The conjunction is retained verbatim. f021 binds `w`; f118 is identified
with that same canonical witness. At each original certificate, its supplied
`pl,pr` are passed unchanged to child 1. This is not a ledger publication and
asserts no part of children 2 or 3. -/
theorem node20a_firstContacts {selected : EGInput.{u}} (residual : Node20aOutcome selected) :
    Node20aOutcome selected ∧
    ∃ w : SparseTargetDefectWitness spineData.{u}.toParameters selected.object,
      sparseTargetDefectWitness spineData.{u}.toParameters selected.object = some w ∧ w.Spec ∧
      ∃ P N : Finset selected.object.Vertex,
        w.Orientation P N ∧ w.Separates P N ∧ w.CyclesUsePrivateEdge P N ∧
        ¬ ((SupportAtom.retainedPiece selected.object w.support P).graph ≤
          (SupportAtom.retainedPiece selected.object w.support N).graph) ∧
        CyclesHaveFirstContacts w P N := by
  have f021 : SparseTargetDefectResidualStatement spineData.{u}.toParameters selected.object :=
    residual.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have f118 : PositiveCyclePrivateEdgeStatement spineData.{u}.toParameters selected.object :=
    residual.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨w, canonical, spec⟩ := f021
  obtain ⟨w', canonical', P, N, orientation, separates, privateEdge, notLe⟩ := f118
  have same : w' = w := Option.some.inj (canonical'.symm.trans canonical)
  subst w'
  refine ⟨residual, w, canonical, spec, P, N, orientation, separates, privateEdge, notLe, ?_⟩
  intro c
  obtain ⟨pl, pr, supplied⟩ := privateEdge c
  exact ⟨pl, pr, supplied,
    firstContacts_on_residual residual w canonical spec orientation separates privateEdge
      c pl pr supplied⟩

end Hypostructure.Graph.S1child1

-- The retained-object construction introduces no additional axioms.
#print axioms Hypostructure.Graph.S1child1.retained_firstContacts


/-! End of the verbatim accepted child-1 dependency. Child 2 starts here. -/
namespace Hypostructure.Graph.S1child2

open SimpleGraph S1child1
open Strategy.Spine Strategy.InterfaceReplacement
universe u

/-- The no-label interval containing the supplied piece-internal occurrence
uses the piece throughout. This applies to the input interval itself. -/
theorem interval_piece_owned {boundary : Boundary.{u}}
    {P : BoundaryPiece boundary} {O : OutsideContext boundary} {LengthOK : Nat → Prop}
    {c : CycleCertificate (glue P O) LengthOK} {x : GluedVertex P O}
    (I : BoundaryInterval c x) (internal : ∃ i : P.Internal, x = .inr (.inl i)) :
    ∀ v z, s(v, z) ∈ I.q.edges → PieceOwns P O v z := by
  have labels : ∀ v ∈ I.q.support,
      v = Sum.inl I.a ∨ v = Sum.inl I.b ∨ ∀ a, v ≠ Sum.inl a := by
    intro v hv
    obtain ⟨k, rfl, hk⟩ := Walk.mem_support_iff_exists_getVert.mp hv
    by_cases hzero : k = 0
    · subst k; exact Or.inl (by simp)
    by_cases hend : k = I.q.length
    · subst k; exact Or.inr (Or.inl (by simp))
    exact Or.inr (Or.inr (I.no_internal_boundary k (by omega) (by omega)))
  rcases GluedReadings.arc_owned I.q
      (fun h => I.distinct (Sum.inl.inj h)) I.simple labels with owned | context
  · exact owned
  · obtain ⟨l, _, hs, _⟩ := DefectGeometry.liftWalk (contextEmbedding P O) I.q
      (x := Sum.inl I.a) (y := Sum.inl I.b) rfl rfl context
    have hx := I.q.getVert_mem_support I.private_index
    rw [I.private_occurrence] at hx
    have hx' : x ∈ l.support.map (contextEmbedding P O) := hs ▸ hx
    obtain ⟨v, _, hv⟩ := List.mem_map.mp hx'
    obtain ⟨i, hi⟩ := internal
    rw [hi] at hv
    cases v <;> cases hv

/-- Nontrivial retained-piece walks have every decoded vertex in the
retained set, because every occurrence is incident to an edge of that walk. -/
theorem retained_support_mem {G : FiniteObject.{u}} {Z P : Finset G.Vertex}
    {a b : (SupportAtom.boundary G Z).Vertex ⊕ SupportAtom.PieceInternal G Z}
    (l : (SupportAtom.retainedPiece G Z P).graph.Walk a b) (positive : 0 < l.length) :
    ∀ v ∈ l.support, SupportAtom.pieceDecode G Z v ∈ P := by
  intro v hv
  obtain ⟨k, rfl, hk⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  by_cases hlt : k < l.length
  · exact (GluedReadings.mem_of_retained_adj (l.adj_getVert_succ hlt)).1
  · have heq : k = l.length := by omega
    have hlast : l.length - 1 < l.length := by omega
    have hsucc : l.length - 1 + 1 = k := by omega
    have hm := (GluedReadings.mem_of_retained_adj (l.adj_getVert_succ hlast)).2
    simpa only [hsucc] using hm

/-- Child 2 is dependent on the accepted interval `I`. In particular the
walk is mapped to `I.q` itself, and its private index decodes to the supplied
`pr`. The ambient walk is explicitly the map under the injective reading hom. -/
structure PositiveLift {G : FiniteObject.{u}} {Z P : Finset G.Vertex}
    {O : OutsideContext (SupportAtom.boundary G Z)} {LengthOK : Nat → Prop}
    {c : CycleCertificate (glue (SupportAtom.retainedPiece G Z P) O) LengthOK}
    {pr : (SupportAtom.boundary G Z).Vertex ⊕ SupportAtom.PieceInternal G Z}
    (I : BoundaryInterval c (pieceEmbedding (SupportAtom.retainedPiece G Z P) O pr)) where
  piece_vertices : ∀ v ∈ I.q.support,
    ∃ p, pieceEmbedding (SupportAtom.retainedPiece G Z P) O p = v
  piece_edges : ∀ v z, s(v, z) ∈ I.q.edges →
    PieceOwns (SupportAtom.retainedPiece G Z P) O v z
  walk : (SupportAtom.retainedPiece G Z P).graph.Walk (.inl I.a) (.inl I.b)
  simple : walk.IsPath
  maps_to_q : walk.map (pieceHom (SupportAtom.retainedPiece G Z P) O) = I.q
  vertex_order : I.q.support =
    walk.support.map (pieceEmbedding (SupportAtom.retainedPiece G Z P) O)
  edge_order : I.q.edges =
    walk.edges.map (Sym2.map (pieceEmbedding (SupportAtom.retainedPiece G Z P) O))
  length_eq : walk.length = I.q.length
  length_two : 2 ≤ walk.length
  private_occurrence : walk.getVert I.private_index = pr
  decode_injective : Function.Injective (SupportAtom.pieceDecode G Z)
  decoded_simple : (walk.map (GluedReadings.readingHom Z P)).IsPath
  decoded_in_P : ∀ v ∈ (walk.map (GluedReadings.readingHom Z P)).support, v ∈ P
  decoded_in_Z : ∀ v ∈ (walk.map (GluedReadings.readingHom Z P)).support, v ∈ Z
  decoded_private_occurrence :
    (walk.map (GluedReadings.readingHom Z P)).getVert I.private_index =
      SupportAtom.pieceDecode G Z pr
  reading_subset : P ⊆ Z

/-- Restrict the supplied interval, without changing any of its vertices,
edges, order, certificate, context, or retained private endpoint. -/
theorem restrict_interval {G : FiniteObject.{u}} {Z P : Finset G.Vertex}
    {O : OutsideContext (SupportAtom.boundary G Z)} {LengthOK : Nat → Prop}
    {c : CycleCertificate (glue (SupportAtom.retainedPiece G Z P) O) LengthOK}
    {pr : (SupportAtom.boundary G Z).Vertex ⊕ SupportAtom.PieceInternal G Z}
    (I : BoundaryInterval c (pieceEmbedding (SupportAtom.retainedPiece G Z P) O pr))
    (internal : SupportAtom.pieceDecode G Z pr ∉ SupportAtom.cutBoundary G Z)
    (subset : P ⊆ Z) : Nonempty (PositiveLift I) := by
  have hint : ∃ i : (SupportAtom.retainedPiece G Z P).Internal,
      pieceEmbedding (SupportAtom.retainedPiece G Z P) O pr = .inr (.inl i) := by
    cases pr with
    | inl b => exact (internal b.property).elim
    | inr i => exact ⟨i, rfl⟩
  have owned := interval_piece_owned I hint
  obtain ⟨l, hl, hs, he⟩ :=
    DefectGeometry.liftWalk (pieceEmbedding (SupportAtom.retainedPiece G Z P) O) I.q
      (x := Sum.inl I.a) (y := Sum.inl I.b) rfl rfl owned
  have hmap : l.map (pieceHom (SupportAtom.retainedPiece G Z P) O) = I.q := by
    apply Walk.ext_support
    exact (Walk.support_map _ _).trans hs.symm
  have simple : l.IsPath := by
    apply Walk.IsPath.mk'
    have nd : (l.support.map (pieceEmbedding (SupportAtom.retainedPiece G Z P) O)).Nodup :=
      hs ▸ I.simple.support_nodup
    exact nd.of_map
  have longq : 2 ≤ I.q.length :=
    Nat.succ_le_of_lt (lt_of_le_of_lt I.private_index_pos I.private_index_lt)
  have long : 2 ≤ l.length := hl.symm ▸ longq
  have samepr : l.getVert I.private_index = pr := by
    apply (pieceEmbedding (SupportAtom.retainedPiece G Z P) O).injective
    have hget := congrArg (fun t : (glue (SupportAtom.retainedPiece G Z P) O).graph.Walk
        (.inl I.a) (.inl I.b) => t.getVert I.private_index) hmap
    exact (Walk.getVert_map (pieceHom (SupportAtom.retainedPiece G Z P) O)
      l I.private_index).symm.trans (hget.trans I.private_occurrence)
  have memP := retained_support_mem l (by omega : 0 < l.length)
  have decodedP : ∀ v ∈ (l.map (GluedReadings.readingHom Z P)).support, v ∈ P := by
    intro v hv
    rw [Walk.support_map] at hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    exact memP p hp
  refine ⟨{
    piece_vertices := ?_
    piece_edges := owned
    walk := l
    simple := simple
    maps_to_q := hmap
    vertex_order := hs
    edge_order := he
    length_eq := hl
    length_two := long
    private_occurrence := samepr
    decode_injective := ReadingProfiles.pieceDecode_injective Z
    decoded_simple := Walk.map_isPath_of_injective
      (GluedReadings.readingHom_injective Z P) simple
    decoded_in_P := decodedP
    decoded_in_Z := fun v hv => subset (decodedP v hv)
    decoded_private_occurrence := ?_
    reading_subset := subset
  }⟩
  · intro v hv
    have hm : v ∈ l.support.map (pieceEmbedding (SupportAtom.retainedPiece G Z P) O) := hs ▸ hv
    obtain ⟨p, _, hp⟩ := List.mem_map.mp hm
    exact ⟨p, hp⟩
  · exact (Walk.getVert_map _ _ _).trans
      (congrArg (SupportAtom.pieceDecode G Z) samepr)

/-- The orientation chooses one of the two original declared supports, both
contained in the canonical support retained in `w.Spec`. -/
theorem positive_subset_support {data : Parameters} {G : FiniteObject.{u}}
    (w : SparseTargetDefectWitness data G) (spec : w.Spec)
    {P N : Finset G.Vertex} (orientation : w.Orientation P N) : P ⊆ w.support := by
  classical
  have seed := (CanonicalSupport.mem_candidates_iff.mp
    (CanonicalSupport.select?_mem_candidates spec.2.2.2.1)).1
  rcases orientation with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact fun v hv => seed (Finset.mem_union_left _ hv)
  · exact fun v hv => seed (Finset.mem_union_right _ hv)

open HypostructureErdos64EG

/-- Child 2 on the complete residual and the already supplied tuple. The
input `I` is the exact child-1 interval, not a newly selected path. Every
original conjunct is returned, and the supplied `pl,pr` remain fixed. -/
theorem lift_on_residual {selected : EGInput.{u}}
    (residual : Node20aOutcome selected)
    (w : SparseTargetDefectWitness spineData.{u}.toParameters selected.object)
    (_canonical : sparseTargetDefectWitness spineData.{u}.toParameters selected.object = some w)
    (spec : w.Spec) {P N : Finset selected.object.Vertex}
    (orientation : w.Orientation P N) (_separates : w.Separates P N)
    (_private : w.CyclesUsePrivateEdge P N)
    (c : CycleCertificate
      (glue (SupportAtom.retainedPiece selected.object w.support P) w.outside)
      spineData.{u}.toParameters.LengthOK)
    (pl pr : (SupportAtom.boundary selected.object w.support).Vertex ⊕
      SupportAtom.PieceInternal selected.object w.support)
    (supplied :
      s(pieceEmbedding (SupportAtom.retainedPiece selected.object w.support P) w.outside pl,
        pieceEmbedding (SupportAtom.retainedPiece selected.object w.support P) w.outside pr)
        ∈ c.walk.edges ∧
      selected.object.graph.Adj (SupportAtom.pieceDecode selected.object w.support pl)
        (SupportAtom.pieceDecode selected.object w.support pr) ∧
      SupportAtom.pieceDecode selected.object w.support pl ∈ P ∧
      SupportAtom.pieceDecode selected.object w.support pr ∈ P ∧
      SupportAtom.pieceDecode selected.object w.support pr ∉ N ∧
      SupportAtom.pieceDecode selected.object w.support pr ∉
        SupportAtom.cutBoundary selected.object w.support)
    (I : BoundaryInterval c
      (pieceEmbedding (SupportAtom.retainedPiece selected.object w.support P) w.outside pr)) :
    Node20aOutcome selected ∧ Nonempty (PositiveLift I) := by
  exact ⟨residual, restrict_interval I supplied.2.2.2.2.2
    (positive_subset_support w spec orientation)⟩

/-- Accepted child-1 output augmented by child 2. The dependent interval
binder makes the exact input `q` available to the later child; no endpoint
activity, complementary-arc transfer, or ledger publication is asserted. -/
def CyclesHaveLiftedFirstContacts {data : Parameters} {G : FiniteObject.{u}}
    (w : SparseTargetDefectWitness data G) (P N : Finset G.Vertex) : Prop :=
  ∀ c : CycleCertificate (glue (SupportAtom.retainedPiece G w.support P) w.outside)
      data.LengthOK,
    ∃ pl pr : (SupportAtom.boundary G w.support).Vertex ⊕ SupportAtom.PieceInternal G w.support,
      (s(pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pl,
         pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr) ∈ c.walk.edges ∧
       G.graph.Adj (SupportAtom.pieceDecode G w.support pl)
         (SupportAtom.pieceDecode G w.support pr) ∧
       SupportAtom.pieceDecode G w.support pl ∈ P ∧
       SupportAtom.pieceDecode G w.support pr ∈ P ∧
       SupportAtom.pieceDecode G w.support pr ∉ N ∧
       SupportAtom.pieceDecode G w.support pr ∉ SupportAtom.cutBoundary G w.support) ∧
      ∃ I : BoundaryInterval c
        (pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr),
        Nonempty (PositiveLift I)

/-- Apply child 2 to the accepted child-1 witnesses on the whole original
conjunction, preserving its canonical witness, orientation, exclusions and
all supplied private-edge data for every original positive certificate. -/
theorem node20a_lift_firstContacts {selected : EGInput.{u}}
    (residual : Node20aOutcome selected) :
    Node20aOutcome selected ∧
    ∃ w : SparseTargetDefectWitness spineData.{u}.toParameters selected.object,
      sparseTargetDefectWitness spineData.{u}.toParameters selected.object = some w ∧ w.Spec ∧
      ∃ P N : Finset selected.object.Vertex,
        w.Orientation P N ∧ w.Separates P N ∧ w.CyclesUsePrivateEdge P N ∧
        ¬ ((SupportAtom.retainedPiece selected.object w.support P).graph ≤
          (SupportAtom.retainedPiece selected.object w.support N).graph) ∧
        CyclesHaveLiftedFirstContacts w P N := by
  obtain ⟨kept, w, canonical, spec, P, N, orientation, separates, privateEdge,
    notLe, contacts⟩ := S1child1.node20a_firstContacts residual
  refine ⟨kept, w, canonical, spec, P, N, orientation, separates, privateEdge, notLe, ?_⟩
  intro c
  obtain ⟨pl, pr, supplied, ⟨I⟩⟩ := contacts c
  exact ⟨pl, pr, supplied, I,
    (lift_on_residual kept w canonical spec orientation separates privateEdge
      c pl pr supplied I).2⟩

end Hypostructure.Graph.S1child2

#print axioms Hypostructure.Graph.S1child2.interval_piece_owned
#print axioms Hypostructure.Graph.S1child2.restrict_interval
#print axioms Hypostructure.Graph.S1child2.lift_on_residual
#print axioms Hypostructure.Graph.S1child2.node20a_lift_firstContacts


/-! End of the verbatim accepted child-2 dependency. Child 3 starts here.
The dependency is embedded because no child-2 module is present in the
read-only import cache. All new claims concern the endpoints of its exact lift. -/
namespace Hypostructure.Graph.S1child3

open SimpleGraph S1child1 S1child2
open Strategy.Spine Strategy.InterfaceReplacement

universe u

open Classical in
/-- Activity on the two fixed declared coordinates, without exchanging them. -/
structure ActiveCommonLabel {data : Parameters} {G : FiniteObject.{u}}
    (w : SparseTargetDefectWitness data G)
    (b : (SupportAtom.boundary G w.support).Vertex) : Prop where
  mem_common : b.1 ∈ sparseDeclaredSupport data G w.first ∩
    sparseDeclaredSupport data G w.second
  first_pos : 0 < w.count w.first b
  second_pos : 0 < w.count w.second b
  counts_eq : w.count w.first b = w.count w.second b

/-- Reading-count positivity and f115 apply to a retained edge at the exact
label. Only the retained orientation determines which transfer is used. -/
theorem active_of_retained_neighbour {data : Parameters} {G : FiniteObject.{u}}
    (w : SparseTargetDefectWitness data G)
    (counts : WitnessReadingCountsAtWitness w)
    {P N : Finset G.Vertex} (orientation : w.Orientation P N)
    (b : (SupportAtom.boundary G w.support).Vertex)
    (v : (SupportAtom.boundary G w.support).Vertex ⊕ SupportAtom.PieceInternal G w.support)
    (adj : (SupportAtom.retainedPiece G w.support P).graph.Adj (.inl b) v) :
    ActiveCommonLabel w b := by
  classical
  have mem := GluedReadings.mem_of_retained_adj adj
  have pos : 0 < ReadingProfiles.readingCount w.support P b := by
    apply ReadingCounts.readingCount_pos_of_active
    simp only [ReadingCounts.activePart, Finset.mem_filter]
    exact ⟨mem.1, _, ReadingProfiles.pieceDecode_mem w.support v, mem.2, adj.1⟩
  rcases orientation with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact ⟨Finset.mem_inter.mpr ⟨mem.1, counts.2.1 b mem.1 _ mem.2 adj.1⟩,
      pos, (counts.1 b) ▸ pos, counts.1 b⟩
  · exact ⟨Finset.mem_inter.mpr ⟨counts.2.2 b mem.1 _ mem.2 adj.1, mem.1⟩,
      (counts.1 b).symm ▸ pos, pos, counts.1 b⟩

/-- The neighbours are the decoded vertices at indices `1` and `length - 1`
of the supplied lift, not independently chosen neighbours or a new path. -/
structure ActiveEndpoints {data : Parameters} {G : FiniteObject.{u}}
    (w : SparseTargetDefectWitness data G) {P : Finset G.Vertex}
    {c : CycleCertificate (glue (SupportAtom.retainedPiece G w.support P) w.outside)
      data.LengthOK}
    {pr : (SupportAtom.boundary G w.support).Vertex ⊕ SupportAtom.PieceInternal G w.support}
    (I : BoundaryInterval c
      (pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr))
    (lift : PositiveLift I) : Prop where
  first_neighbour_mem : SupportAtom.pieceDecode G w.support (lift.walk.getVert 1) ∈ P
  first_adj : G.graph.Adj I.a.1
    (SupportAtom.pieceDecode G w.support (lift.walk.getVert 1))
  last_neighbour_mem : SupportAtom.pieceDecode G w.support
    (lift.walk.getVert (lift.walk.length - 1)) ∈ P
  last_adj : G.graph.Adj I.b.1
    (SupportAtom.pieceDecode G w.support (lift.walk.getVert (lift.walk.length - 1)))
  a_active : ActiveCommonLabel w I.a
  b_active : ActiveCommonLabel w I.b

/-- Use the first and last edges of the same lifted `I.q`; length at least
two supplies both edges. No assumption on the complementary arc is used. -/
theorem endpoints_of_lift {data : Parameters} {G : FiniteObject.{u}}
    (w : SparseTargetDefectWitness data G)
    (counts : WitnessReadingCountsAtWitness w)
    {P N : Finset G.Vertex} (orientation : w.Orientation P N)
    {c : CycleCertificate (glue (SupportAtom.retainedPiece G w.support P) w.outside)
      data.LengthOK}
    {pr : (SupportAtom.boundary G w.support).Vertex ⊕ SupportAtom.PieceInternal G w.support}
    (I : BoundaryInterval c
      (pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr))
    (lift : PositiveLift I) : ActiveEndpoints w I lift := by
  have long := lift.length_two
  have first : (SupportAtom.retainedPiece G w.support P).graph.Adj
      (.inl I.a) (lift.walk.getVert 1) := by
    simpa only [Walk.getVert_zero, Nat.zero_add] using
      lift.walk.adj_getVert_succ (by omega : 0 < lift.walk.length)
  have last : (SupportAtom.retainedPiece G w.support P).graph.Adj
      (.inl I.b) (lift.walk.getVert (lift.walk.length - 1)) := by
    have h := lift.walk.adj_getVert_succ
      (by omega : lift.walk.length - 1 < lift.walk.length)
    have hs : lift.walk.length - 1 + 1 = lift.walk.length := by omega
    rw [hs, Walk.getVert_length] at h
    exact h.symm
  exact ⟨(GluedReadings.mem_of_retained_adj first).2, first.1,
    (GluedReadings.mem_of_retained_adj last).2, last.1,
    active_of_retained_neighbour w counts orientation I.a _ first,
    active_of_retained_neighbour w counts orientation I.b _ last⟩

open HypostructureErdos64EG

/-- Read f115 on the complete conjunction and identify its witness with the
already bound `w` by the canonical `some` equality. The input interval and
lift are retained unchanged, along with every original residual conjunct. -/
theorem endpoints_on_residual {selected : EGInput.{u}}
    (residual : Node20aOutcome selected)
    (w : SparseTargetDefectWitness spineData.{u}.toParameters selected.object)
    (canonical : sparseTargetDefectWitness spineData.{u}.toParameters selected.object = some w)
    (_spec : w.Spec) {P N : Finset selected.object.Vertex}
    (orientation : w.Orientation P N) (_separates : w.Separates P N)
    (_private : w.CyclesUsePrivateEdge P N)
    (c : CycleCertificate
      (glue (SupportAtom.retainedPiece selected.object w.support P) w.outside)
      spineData.{u}.toParameters.LengthOK)
    (pl pr : (SupportAtom.boundary selected.object w.support).Vertex ⊕
      SupportAtom.PieceInternal selected.object w.support)
    (_supplied :
      s(pieceEmbedding (SupportAtom.retainedPiece selected.object w.support P) w.outside pl,
        pieceEmbedding (SupportAtom.retainedPiece selected.object w.support P) w.outside pr)
        ∈ c.walk.edges ∧
      selected.object.graph.Adj (SupportAtom.pieceDecode selected.object w.support pl)
        (SupportAtom.pieceDecode selected.object w.support pr) ∧
      SupportAtom.pieceDecode selected.object w.support pl ∈ P ∧
      SupportAtom.pieceDecode selected.object w.support pr ∈ P ∧
      SupportAtom.pieceDecode selected.object w.support pr ∉ N ∧
      SupportAtom.pieceDecode selected.object w.support pr ∉
        SupportAtom.cutBoundary selected.object w.support)
    (I : BoundaryInterval c
      (pieceEmbedding (SupportAtom.retainedPiece selected.object w.support P) w.outside pr))
    (lift : PositiveLift I) :
    Node20aOutcome selected ∧ ActiveEndpoints w I lift := by
  have f115 : WitnessReadingCountsStatement spineData.{u}.toParameters selected.object :=
    residual.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨w', canonical', counts⟩ := f115
  have same : w' = w := Option.some.inj (canonical'.symm.trans canonical)
  subst w'
  exact ⟨residual, endpoints_of_lift w counts orientation I lift⟩

/-- The accepted child-2 witnesses, augmented only by activity of their exact
endpoints; all f118 data and both dependent witnesses remain present. -/
def CyclesHaveActiveFirstContacts {data : Parameters} {G : FiniteObject.{u}}
    (w : SparseTargetDefectWitness data G) (P N : Finset G.Vertex) : Prop :=
  ∀ c : CycleCertificate (glue (SupportAtom.retainedPiece G w.support P) w.outside)
      data.LengthOK,
    ∃ pl pr : (SupportAtom.boundary G w.support).Vertex ⊕ SupportAtom.PieceInternal G w.support,
      (s(pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pl,
         pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr) ∈ c.walk.edges ∧
       G.graph.Adj (SupportAtom.pieceDecode G w.support pl)
         (SupportAtom.pieceDecode G w.support pr) ∧
       SupportAtom.pieceDecode G w.support pl ∈ P ∧
       SupportAtom.pieceDecode G w.support pr ∈ P ∧
       SupportAtom.pieceDecode G w.support pr ∉ N ∧
       SupportAtom.pieceDecode G w.support pr ∉ SupportAtom.cutBoundary G w.support) ∧
      ∃ I : BoundaryInterval c
        (pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr),
        ∃ lift : PositiveLift I, ActiveEndpoints w I lift


/-- S1 endpoint conclusion on the whole original conjunction, for every
original positive certificate. This consumes the accepted child-2 output;
it does not select new contacts, lifts, or private endpoints. -/
theorem node20a_active_firstContacts {selected : EGInput.{u}}
    (residual : Node20aOutcome selected) :
    Node20aOutcome selected ∧
    ∃ w : SparseTargetDefectWitness spineData.{u}.toParameters selected.object,
      sparseTargetDefectWitness spineData.{u}.toParameters selected.object = some w ∧ w.Spec ∧
      ∃ P N : Finset selected.object.Vertex,
        w.Orientation P N ∧ w.Separates P N ∧ w.CyclesUsePrivateEdge P N ∧
        ¬ ((SupportAtom.retainedPiece selected.object w.support P).graph ≤
          (SupportAtom.retainedPiece selected.object w.support N).graph) ∧
        CyclesHaveActiveFirstContacts w P N := by
  obtain ⟨kept, w, canonical, spec, P, N, orientation, separates, privateEdge,
    notLe, contacts⟩ := S1child2.node20a_lift_firstContacts residual
  refine ⟨kept, w, canonical, spec, P, N, orientation, separates, privateEdge, notLe, ?_⟩
  intro c
  obtain ⟨pl, pr, supplied, I, ⟨lift⟩⟩ := contacts c
  exact ⟨pl, pr, supplied, I, lift,
    (endpoints_on_residual kept w canonical spec orientation separates privateEdge
      c pl pr supplied I lift).2⟩

end Hypostructure.Graph.S1child3

#print axioms Hypostructure.Graph.S1child3.active_of_retained_neighbour
#print axioms Hypostructure.Graph.S1child3.endpoints_of_lift
#print axioms Hypostructure.Graph.S1child3.endpoints_on_residual
#print axioms Hypostructure.Graph.S1child3.node20a_active_firstContacts
