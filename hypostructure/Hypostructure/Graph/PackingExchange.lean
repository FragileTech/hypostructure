import Hypostructure.Graph.LocalRigidity
import Hypostructure.Graph.WindowRemainder

/-!
# Exchange at a maximum window packing, and arms glued to window segments

A window packing only asks for vertex-disjoint supports, each inducing the window path; its
members may be adjacent.  At a packing `P₀` of maximum cardinality this gives an exchange
bound: for every subfamily `Q ⊆ P₀`, a window packing `W` whose members avoid every member of
`P₀ \ Q` has `|W| ≤ |Q|`, since `W ∪ (P₀ \ Q)` is again a window packing
(`card_le_of_exchange`).  Two special forms:

* `card_le_of_subset_union_remainder`: the members of `W` lie in `(⋃ Q) ∪ R`, with `R` the
  remainder of `P₀`;
* `false_of_two_windows_off_member` (`k = 1`): two disjoint windows both avoiding every member
  of `P₀` other than one window `P` do not exist.

The second half builds such windows.  An induced path `α` (an *arm*) ending at `x`, and a run
of consecutive positions of a placed window having position `i` as an end (a *segment*), with
`x ~ p i` the only arm–segment edge and disjoint supports, together induce a path
(`exists_inducesWindow_arm_segment`).

Nothing here is specialised to a manuscript: the window order is a parameter.
-/

namespace Hypostructure.Graph.PackingExchange

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.LocalRigidity

universe u

variable {object : FiniteObject.{u}}

/-! ## The exchange bound -/

/-- **`k`-fold exchange.**  Let `packing` be a window packing of maximum cardinality and
`Q ⊆ packing`.  A window packing `W` whose members are disjoint from every member of
`packing \ Q` has at most `|Q|` members: `W ∪ (packing \ Q)` is a window packing (the union is
disjoint because windows are nonempty), so its size `|W| + |packing| − |Q|` is at most the
packing number `|packing|`. -/
theorem card_le_of_exchange {order : Nat} (positive : 0 < order)
    {packing Q W : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing)
    (maximum : packing.card = object.windowPackingNumber order)
    (sub : Q ⊆ packing)
    (packed : object.IsWindowPacking order W)
    (avoid : ∀ S ∈ W, ∀ M ∈ packing, M ∉ Q → Disjoint S M) :
    W.card ≤ Q.card := by
  classical
  have fresh : Disjoint W (packing \ Q) := by
    rw [Finset.disjoint_left]
    intro S hW hP
    obtain ⟨v, hv⟩ := object.nonempty_of_inducesWindow positive (packed.1 S hW)
    have hPQ := Finset.mem_sdiff.1 hP
    exact Finset.disjoint_left.1 (avoid S hW S hPQ.1 hPQ.2) hv hv
  have union : object.IsWindowPacking order (W ∪ (packing \ Q)) := by
    refine ⟨fun S hS => ?_, fun L hL R hR ne => ?_⟩
    · rcases Finset.mem_union.1 hS with h | h
      · exact packed.1 S h
      · exact valid.1 S (Finset.mem_sdiff.1 h).1
    · rcases Finset.mem_union.1 hL with hl | hl <;>
        rcases Finset.mem_union.1 hR with hr | hr
      · exact packed.2 L hl R hr ne
      · exact avoid L hl R (Finset.mem_sdiff.1 hr).1 (Finset.mem_sdiff.1 hr).2
      · exact (avoid R hr L (Finset.mem_sdiff.1 hl).1 (Finset.mem_sdiff.1 hl).2).symm
      · exact valid.2 L (Finset.mem_sdiff.1 hl).1 R (Finset.mem_sdiff.1 hr).1 ne
  have bound := object.card_le_windowPackingNumber union
  rw [Finset.card_union_of_disjoint fresh, Finset.card_sdiff_of_subset sub] at bound
  have := Finset.card_le_card sub
  omega

/-- A support inside `(⋃ Q) ∪ R` (`R` the remainder of a window packing, `Q` a subfamily) is
disjoint from every member of the packing outside `Q`. -/
theorem disjoint_of_subset_union_remainder {order : Nat}
    {packing Q : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing)
    {S : Finset object.Vertex}
    (inside : ∀ v ∈ S, (∃ M ∈ Q, v ∈ M) ∨ v ∈ object.remainderSupport packing)
    {M : Finset object.Vertex} (hM : M ∈ packing) (hMQ : M ∉ Q) (sub : Q ⊆ packing) :
    Disjoint S M := by
  rw [Finset.disjoint_left]
  intro v hS hv
  rcases inside v hS with ⟨M', hM', hv'⟩ | hR
  · have ne : M' ≠ M := fun e => hMQ (e ▸ hM')
    exact Finset.disjoint_left.1 (valid.2 M' (sub hM') M hM ne) hv' hv
  · exact FiniteObject.notMem_windowSupport_of_mem_remainderSupport hR
      (FiniteObject.mem_windowSupport hM hv)

/-- **Exchange into `(⋃ Q) ∪ R`.**  At a maximum window packing with remainder `R`, every
window packing whose members lie in `(⋃ Q) ∪ R` has at most `|Q|` members. -/
theorem card_le_of_subset_union_remainder {order : Nat} (positive : 0 < order)
    {packing Q W : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing)
    (maximum : packing.card = object.windowPackingNumber order)
    (sub : Q ⊆ packing)
    (packed : object.IsWindowPacking order W)
    (inside : ∀ S ∈ W, ∀ v ∈ S, (∃ M ∈ Q, v ∈ M) ∨ v ∈ object.remainderSupport packing) :
    W.card ≤ Q.card :=
  card_le_of_exchange positive valid maximum sub packed fun S hS _M hM hMQ =>
    disjoint_of_subset_union_remainder valid (inside S hS) hM hMQ sub

/-- **Exchange, `k = 1`.**  At a maximum window packing, two disjoint windows that both avoid
every member other than `P` do not exist: with the other members they would form a packing
one larger. -/
theorem false_of_two_windows_off_member {order : Nat} (positive : 0 < order)
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing)
    (maximum : packing.card = object.windowPackingNumber order)
    {P : Finset object.Vertex} (hP : P ∈ packing)
    {S T : Finset object.Vertex}
    (hS : object.InducesWindow order S) (hT : object.InducesWindow order T)
    (ST : Disjoint S T)
    (offS : ∀ M ∈ packing, M ≠ P → Disjoint S M)
    (offT : ∀ M ∈ packing, M ≠ P → Disjoint T M) : False := by
  classical
  have ne : S ≠ T := by
    intro e
    obtain ⟨v, hv⟩ := object.nonempty_of_inducesWindow positive hS
    exact Finset.disjoint_left.1 ST hv (e ▸ hv)
  have packed : object.IsWindowPacking order {S, T} := by
    refine ⟨fun X hX => ?_, fun L hL R hR LR => ?_⟩
    · rcases Finset.mem_insert.1 hX with rfl | hX
      · exact hS
      · rw [Finset.mem_singleton.1 hX]; exact hT
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hL hR
      rcases hL with rfl | rfl <;> rcases hR with rfl | rfl
      · exact absurd rfl LR
      · exact ST
      · exact ST.symm
      · exact absurd rfl LR
  have bound := card_le_of_exchange positive valid maximum
    (Finset.singleton_subset_iff.2 hP) packed (fun X hX M hM hMQ => by
      have hMP : M ≠ P := fun e => hMQ (Finset.mem_singleton.2 e)
      rcases Finset.mem_insert.1 hX with rfl | hX
      · exact offS M hM hMP
      · rw [Finset.mem_singleton.1 hX]; exact offT M hM hMP)
  rw [Finset.card_pair ne, Finset.card_singleton] at bound
  omega

/-! ## Induced paths from maps -/

/-- An injective map from `Fin n` whose adjacency is exactly the path adjacency induces a
window of order `n` on its image. -/
theorem exists_inducesWindow_of_pathMap {n : Nat} {q : Fin n → object.Vertex}
    (inj : Function.Injective q)
    (law : ∀ i j, object.graph.Adj (q i) (q j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) :
    ∃ W : Finset object.Vertex, object.InducesWindow n W ∧
      ∀ v, v ∈ W ↔ ∃ i, q i = v := by
  classical
  refine ⟨Finset.univ.image q, ⟨⟨⟨⟨fun i => ⟨q i, Finset.mem_image_of_mem q
    (Finset.mem_univ i)⟩, ?_⟩, ?_⟩⟩, ?_⟩, ?_⟩
  · intro i j e
    exact inj (congrArg Subtype.val e : _)
  · intro i j
    change object.graph.Adj (q i) (q j) ↔ (SimpleGraph.pathGraph n).Adj i j
    rw [SimpleGraph.pathGraph_adj, law]
  · rw [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin]
  · intro v
    simp

/-- **Concatenation of two induced paths.**  Two induced paths `α` (on `A` vertices) and `σ`
(on `B` vertices), with disjoint images and the single edge `α (A−1) — σ 0` between them,
concatenate to an induced path on `A + B` vertices. -/
theorem append_pathMap {A B : Nat} {α : Fin A → object.Vertex} {σ : Fin B → object.Vertex}
    (αinj : Function.Injective α)
    (αlaw : ∀ i j, object.graph.Adj (α i) (α j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)
    (σinj : Function.Injective σ)
    (σlaw : ∀ i j, object.graph.Adj (σ i) (σ j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)
    (disj : ∀ k t, α k ≠ σ t)
    (cross : ∀ k t, object.graph.Adj (α k) (σ t) ↔ k.1 + 1 = A ∧ t.1 = 0) :
    Function.Injective (Fin.append α σ) ∧
      ∀ i j, object.graph.Adj (Fin.append α σ i) (Fin.append α σ j) ↔
        i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 := by
  constructor
  · intro i j e
    induction i using Fin.addCases with
    | left k =>
      induction j using Fin.addCases with
      | left k' =>
        simp only [Fin.append_left] at e
        rw [αinj e]
      | right t' =>
        simp only [Fin.append_left, Fin.append_right] at e
        exact absurd e (disj k t')
    | right t =>
      induction j using Fin.addCases with
      | left k' =>
        simp only [Fin.append_left, Fin.append_right] at e
        exact absurd e.symm (disj k' t)
      | right t' =>
        simp only [Fin.append_right] at e
        rw [σinj e]
  · intro i j
    induction i using Fin.addCases with
    | left k =>
      induction j using Fin.addCases with
      | left k' =>
        simp only [Fin.append_left, Fin.val_castAdd]
        exact αlaw k k'
      | right t' =>
        simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
        rw [cross k t']
        have := k.2
        omega
    | right t =>
      induction j using Fin.addCases with
      | left k' =>
        simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
        rw [object.graph.adj_comm, cross k' t]
        have := k'.2
        omega
      | right t' =>
        simp only [Fin.append_right, Fin.val_natAdd]
        rw [σlaw t t']
        omega

/-! ## Segments of a placed window -/

/-- **A segment of a placed window with a prescribed end.**  For the run of positions
`l, l+1, …, l+b` of a window of order `n` (`l + b < n`) and `i ∈ {l, l+b}`, there is an
enumeration `pos` of the run starting at `i` (`pos 0 = i`) which preserves consecutiveness;
hence `p ∘ pos` is an induced path whenever `p` is a window placement. -/
theorem exists_segment_enumeration {n : Nat} (l b : Nat) (bound : l + b < n)
    (i : Fin n) (endpoint : i.1 = l ∨ i.1 = l + b) :
    ∃ pos : Fin (b + 1) → Fin n, pos 0 = i ∧ Function.Injective pos ∧
      (∀ t, l ≤ (pos t).1 ∧ (pos t).1 ≤ l + b) ∧
      (∀ s : Fin n, l ≤ s.1 → s.1 ≤ l + b → ∃ t, pos t = s) ∧
      ∀ t t', ((pos t).1 + 1 = (pos t').1 ∨ (pos t').1 + 1 = (pos t).1) ↔
        (t.1 + 1 = t'.1 ∨ t'.1 + 1 = t.1) := by
  rcases endpoint with h | h
  · refine ⟨fun t => ⟨l + t.1, by omega⟩, Fin.ext (by simp [h]), ?_, ?_, ?_, ?_⟩
    · intro t t' e
      exact Fin.ext (by simpa using congrArg Fin.val e)
    · intro t; simp only; omega
    · intro s h1 h2
      exact ⟨⟨s.1 - l, by omega⟩, Fin.ext (by simp only; omega)⟩
    · intro t t'; simp only; omega
  · refine ⟨fun t => ⟨l + b - t.1, by omega⟩, Fin.ext (by simp [h]), ?_, ?_, ?_, ?_⟩
    · intro t t' e
      have := congrArg Fin.val e
      simp only at this
      exact Fin.ext (by omega)
    · intro t; simp only; omega
    · intro s h1 h2
      exact ⟨⟨l + b - s.1, by omega⟩, Fin.ext (by simp only; omega)⟩
    · intro t t'; simp only; omega

/-- **Arm plus segment.**  Let `p` place a window of order `n` and `α` be an induced path on
`a + 1` vertices (an arm) ending at `α (last a)`.  Take a run of positions `l, …, l+b` with
`i` an end, such that the arm meets no vertex of the run, `α (last a) ~ p i`, and this is the
only edge between the arm and the run.  Then the arm and the run together induce a window of
order `(a + 1) + (b + 1)`, whose vertices are exactly those of the arm and of the run. -/
theorem exists_inducesWindow_arm_segment {n : Nat}
    {P : Finset object.Vertex} {p : Fin n → object.Vertex}
    (hp : IsWindowPlacement object P p)
    {S : Finset object.Vertex} {a : Nat} {α : Fin (a + 1) → object.Vertex}
    (hα : IsWindowPlacement object S α)
    (l b : Nat) (bound : l + b < n) (i : Fin n) (endpoint : i.1 = l ∨ i.1 = l + b)
    (edge : object.graph.Adj (α (Fin.last a)) (p i))
    (only : ∀ k (t : Fin n), l ≤ t.1 → t.1 ≤ l + b →
      object.graph.Adj (α k) (p t) → k = Fin.last a ∧ t = i)
    (disj : ∀ k (t : Fin n), l ≤ t.1 → t.1 ≤ l + b → α k ≠ p t) :
    ∃ W : Finset object.Vertex, object.InducesWindow ((a + 1) + (b + 1)) W ∧
      ∀ v, v ∈ W ↔ (∃ k, α k = v) ∨ ∃ t : Fin n, l ≤ t.1 ∧ t.1 ≤ l + b ∧ p t = v := by
  obtain ⟨pos, pos0, posInj, posIn, posOnto, posLaw⟩ :=
    exists_segment_enumeration l b bound i endpoint
  have σinj : Function.Injective (p ∘ pos) := hp.1.comp posInj
  have σlaw : ∀ t t', object.graph.Adj ((p ∘ pos) t) ((p ∘ pos) t') ↔
      t.1 + 1 = t'.1 ∨ t'.1 + 1 = t.1 := by
    intro t t'
    rw [Function.comp_apply, Function.comp_apply, hp.2.2, posLaw]
  have cross : ∀ k t, object.graph.Adj (α k) ((p ∘ pos) t) ↔ k.1 + 1 = a + 1 ∧ t.1 = 0 := by
    intro k t
    constructor
    · intro adj
      obtain ⟨hk, ht⟩ := only k (pos t) (posIn t).1 (posIn t).2 adj
      refine ⟨by rw [hk]; simp, ?_⟩
      have : t = 0 := posInj (ht.trans pos0.symm)
      rw [this]; rfl
    · rintro ⟨hk, ht⟩
      have ek : k = Fin.last a := Fin.ext (by simp; omega)
      have et : t = 0 := Fin.ext ht
      rw [ek, et, Function.comp_apply, pos0]
      exact edge
  obtain ⟨inj, law⟩ := append_pathMap hα.1 hα.2.2 σinj σlaw
    (fun k t => disj k (pos t) (posIn t).1 (posIn t).2) cross
  obtain ⟨W, hW, mem⟩ := exists_inducesWindow_of_pathMap inj law
  refine ⟨W, hW, fun v => ?_⟩
  rw [mem]
  constructor
  · rintro ⟨j, rfl⟩
    induction j using Fin.addCases with
    | left k => exact Or.inl ⟨k, by simp⟩
    | right t =>
      exact Or.inr ⟨pos t, (posIn t).1, (posIn t).2, by simp⟩
  · rintro (⟨k, rfl⟩ | ⟨s, h1, h2, rfl⟩)
    · exact ⟨Fin.castAdd _ k, by simp⟩
    · obtain ⟨t, rfl⟩ := posOnto s h1 h2
      exact ⟨Fin.natAdd _ t, by simp⟩

/-! ## Two windows inside one member and the remainder -/

/-- A window placement stays one when its support is enlarged. -/
theorem placement_mono {n : Nat} {S T : Finset object.Vertex} {q : Fin n → object.Vertex}
    (placement : IsWindowPlacement object S q) (sub : S ⊆ T) :
    IsWindowPlacement object T q :=
  ⟨placement.1, fun i => sub (placement.2.1 i), placement.2.2⟩

/-- **Two windows in `P ∪ R`.**  At a maximum window packing with remainder `R` and a member
`P`, two disjoint windows inside `P ∪ R` do not exist (`false_of_two_windows_off_member`: a
support inside `P ∪ R` avoids every other member). -/
theorem false_of_two_windows_in_member_union_remainder {order : Nat} (positive : 0 < order)
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing)
    (maximum : packing.card = object.windowPackingNumber order)
    {P : Finset object.Vertex} (hP : P ∈ packing)
    {W₁ W₂ : Finset object.Vertex}
    (h₁ : object.InducesWindow order W₁) (h₂ : object.InducesWindow order W₂)
    (disjoint : Disjoint W₁ W₂)
    (in₁ : ∀ v ∈ W₁, v ∈ object.remainderSupport packing ∨ v ∈ P)
    (in₂ : ∀ v ∈ W₂, v ∈ object.remainderSupport packing ∨ v ∈ P) : False := by
  have off : ∀ W : Finset object.Vertex,
      (∀ v ∈ W, v ∈ object.remainderSupport packing ∨ v ∈ P) →
      ∀ M ∈ packing, M ≠ P → Disjoint W M := by
    intro W inside M hM ne
    rw [Finset.disjoint_left]
    intro v hv hvM
    rcases inside v hv with hR | hPv
    · exact FiniteObject.notMem_windowSupport_of_mem_remainderSupport hR
        (FiniteObject.mem_windowSupport hM hvM)
    · exact Finset.disjoint_left.1 (valid.2 P hP M hM ne.symm) hPv hvM
  exact false_of_two_windows_off_member positive valid maximum hP h₁ h₂ disjoint
    (off W₁ in₁) (off W₂ in₂)

/-- **Two arms with disjoint segments.**  At a maximum window packing with remainder `R`, a
member `P` placed by `p`, two vertex-disjoint arms `α`, `β` inside `R` (on `a + 1`, `b + 1`
vertices) ending at `α (last a) ~ p i` and `β (last b) ~ p j`, and two disjoint runs of
positions `[lx, lx+mx] ∋ i`, `[ly, ly+my] ∋ j` (with `i`, `j` an end) of complementary sizes,
whose only arm–run edges are `α (last a) — p i` and `β (last b) — p j`, do not exist: they
give two disjoint windows inside `P ∪ R`. -/
theorem false_of_two_arm_segments {n : Nat} (positive : 0 < n)
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking n packing)
    (maximum : packing.card = object.windowPackingNumber n)
    {P : Finset object.Vertex} (hP : P ∈ packing)
    {p : Fin n → object.Vertex} (hp : IsWindowPlacement object P p)
    {a b : Nat} {α : Fin (a + 1) → object.Vertex} {β : Fin (b + 1) → object.Vertex}
    (hα : IsWindowPlacement object (object.remainderSupport packing) α)
    (hβ : IsWindowPlacement object (object.remainderSupport packing) β)
    (αβ : ∀ k k', α k ≠ β k')
    (i j : Fin n) (lx mx ly my : Nat) (bx : lx + mx < n) (byy : ly + my < n)
    (ei : i.1 = lx ∨ i.1 = lx + mx) (ej : j.1 = ly ∨ j.1 = ly + my)
    (sep : lx + mx < ly ∨ ly + my < lx)
    (sx : (a + 1) + (mx + 1) = n) (sy : (b + 1) + (my + 1) = n)
    (ex : object.graph.Adj (α (Fin.last a)) (p i))
    (ey : object.graph.Adj (β (Fin.last b)) (p j))
    (onlyx : ∀ k (t : Fin n), lx ≤ t.1 → t.1 ≤ lx + mx →
      object.graph.Adj (α k) (p t) → k = Fin.last a ∧ t = i)
    (onlyy : ∀ k (t : Fin n), ly ≤ t.1 → t.1 ≤ ly + my →
      object.graph.Adj (β k) (p t) → k = Fin.last b ∧ t = j) : False := by
  have outR : ∀ v, v ∈ object.remainderSupport packing → v ∈ P → False := fun v hR hv =>
    FiniteObject.notMem_windowSupport_of_mem_remainderSupport hR
      (FiniteObject.mem_windowSupport hP hv)
  have pP : ∀ t, p t ∈ P := hp.2.1
  obtain ⟨W₁, hW₁, mem₁⟩ := exists_inducesWindow_arm_segment hp hα lx mx bx i
    ei ex onlyx (fun k t _ _ e => outR _ (hα.2.1 k) (e ▸ pP t))
  obtain ⟨W₂, hW₂, mem₂⟩ := exists_inducesWindow_arm_segment hp hβ ly my byy j
    ej ey onlyy (fun k t _ _ e => outR _ (hβ.2.1 k) (e ▸ pP t))
  rw [sx] at hW₁
  rw [sy] at hW₂
  have in₁ : ∀ v ∈ W₁, v ∈ object.remainderSupport packing ∨ v ∈ P := by
    intro v hv
    rcases (mem₁ v).1 hv with ⟨k, rfl⟩ | ⟨t, _, _, rfl⟩
    · exact Or.inl (hα.2.1 k)
    · exact Or.inr (pP t)
  have in₂ : ∀ v ∈ W₂, v ∈ object.remainderSupport packing ∨ v ∈ P := by
    intro v hv
    rcases (mem₂ v).1 hv with ⟨k, rfl⟩ | ⟨t, _, _, rfl⟩
    · exact Or.inl (hβ.2.1 k)
    · exact Or.inr (pP t)
  have disjoint : Disjoint W₁ W₂ := by
    rw [Finset.disjoint_left]
    intro v h₁ h₂
    rcases (mem₁ v).1 h₁ with ⟨k, rfl⟩ | ⟨t, t1, t2, rfl⟩ <;>
      rcases (mem₂ _).1 h₂ with ⟨k', e⟩ | ⟨t', t1', t2', e⟩
    · exact αβ k k' e.symm
    · exact outR _ (hα.2.1 k) (e ▸ pP t')
    · exact outR _ (hβ.2.1 k') (e ▸ pP t)
    · have := congrArg Fin.val (hp.1 e)
      omega
  exact false_of_two_windows_in_member_union_remainder positive valid maximum hP hW₁ hW₂
    disjoint in₁ in₂

end Hypostructure.Graph.PackingExchange
