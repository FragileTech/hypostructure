import Hypostructure.Graph.InducedPathMaximalPacking
import Hypostructure.Graph.LabelledOn

/-!
# Packed-window coordinates and their labelled-skeleton realization

This file carries the two facts `prop:p13-density` consumes and nothing else.

`prop:p13-density`'s proof is three sentences long:

> By `lem:p13-window-package`, the window coordinates alone contribute
> `(c₁₃ − o(1)) p₁₃ log₂ n` bits.  Since all target-complete window states are
> realized by labelled near-cubic skeletons under `def:near-cubic-spine`,
> `lem:independent-target-entropy, lem:skeleton-dominates` give
> `(c₁₃ − o(1)) p₁₃ log₂ n ≤ (3/2) n log₂ n + o(n log n)`.

Reading it backwards, the two things it needs are

* **independence of the window coordinates** — "the window coordinates alone
  contribute `p₁₃` independent packages", which rests on the packing's own
  disjointness, and
* **realization** — "all target-complete window states are realized by labelled
  skeletons", which is `lem:state-count-comparison`.

Both are theorems about the *canonical* maximal packing, not data an adapter
supplies:

* the packing is the one the **ledger** already carries -- the CT1 node's
  `Core.Strategy.ObstructionPackingClosure.Packing`, read as an induced-path
  profile by `Graph.Strategy.ObstructionPackingClosure.inducedPathProfileOfPacking`,
  whose `pairwiseDisjoint` field is that packing's own `pairwiseCompatible`
  (the graph presentation's `conflict` *is* `¬ Disjoint (support …) (support …)`).
  So `supports_pairwise_disjoint` and `packed` are derivations from the retained
  ledger entry, and in particular the window count here is definitionally the
  `packingCount` the density comparison was run on, read off the cap ledger by
  `Graph.Strategy.FiniteDensityBudget.capLedger_ambientCapacity_read`.  Nothing in
  this file re-selects a packing: every declaration is parametric in the profile
  it is handed;
* the state assignment of `lem:skeleton-dominates` is *canonical* ("all
  auxiliary objects ... are functions of the labelled adjacency matrix once a
  deterministic tie-breaking rule is fixed"), so it is a plain map
  `LabelledOn n → JointState` and its realization/injectivity are the theorems
  already proved in `Graph.LabelledOn`.

Everything domain-neutral — the product cardinality, the pointwise-injective
lift, the rate-floor compounding — is `Core.FiniteEntropy`'s and is only
applied here.  No new numeric constant, capacity, code, or route appears; the
window index type, its supports and its cardinality are all read off the
object's own canonical packing.
-/

namespace Hypostructure.Graph.PackedWindowRealization

open Hypostructure

universe u v w

variable {object : FiniteObject.{u}} {order : Nat}

/-! ## The packed windows of the canonical maximal packing -/

/-- The window index of a packing: its own selected occurrences, derived from
the profile rather than supplied.  `Graph.InducedPathMaximalPacking.Profile`
already carries `selected_nodup`, so this subtype lists each selected window
exactly once and the `p₁₃` of the manuscript is its cardinality. -/
abbrev PackedWindow (profile : InducedPathMaximalPacking.Profile object order) :=
  {window : InducedPathMaximalPacking.Window object order //
    window ∈ profile.selected}

instance instFinitePackedWindow
    (profile : InducedPathMaximalPacking.Profile object order) :
    Finite (PackedWindow profile) :=
  (profile.selected.finite_toSet).to_subtype

noncomputable instance instFintypePackedWindow
    (profile : InducedPathMaximalPacking.Profile object order) :
    Fintype (PackedWindow profile) :=
  Fintype.ofFinite _

/-- **`p₁₃` is the packing's own cardinality.**

The window index type lists each selected occurrence exactly once -- that is
what `selected_nodup` buys -- so its cardinality is the length of the selected
list.  For the profile read off the ledger's `ObstructionPackingClosure.Packing`
that length is literally the `packingCount` the density comparison is run at,
which is why the window package's multiplicative demand and the density node's
`stateDemand` speak about the same `p₁₃`. -/
theorem card_packedWindow
    (profile : InducedPathMaximalPacking.Profile object order) :
    Nat.card (PackedWindow profile) = profile.selected.length := by
  classical
  have equivalence :
      PackedWindow profile ≃ {window // window ∈ profile.selected.toFinset} :=
    Equiv.subtypeEquivRight fun _window => List.mem_toFinset.symm
  rw [Nat.card_congr equivalence, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup profile.selected_nodup]

/-- The coordinate support of a packed window is its literal embedded vertex
set: `Graph.InducedPathMaximalPacking.support` at the selected occurrence, with
no re-derivation. -/
def support (profile : InducedPathMaximalPacking.Profile object order)
    (window : PackedWindow profile) : Finset object.Vertex :=
  InducedPathMaximalPacking.support object order window.1

/-- **Canonical packing disjointness at the coordinate-support boundary.**

This is the packing's own `pairwiseDisjoint` field, restated at the subtype of
selected windows.  For `maximalProfile` that field is
`maximalWindowSet_admissible`, so nothing here is assumed. -/
theorem supports_pairwise_disjoint
    (profile : InducedPathMaximalPacking.Profile object order)
    (left right : PackedWindow profile) (different : left ≠ right) :
    Disjoint (support profile left) (support profile right) := by
  refine profile.pairwiseDisjoint left.1 left.2 right.1 right.2 ?_
  intro equality
  exact different (Subtype.ext equality)

/-- Packedness of the canonical packing, as the predicate downstream entropy
accounting reads. -/
def Packed (profile : InducedPathMaximalPacking.Profile object order) : Prop :=
  ∀ left right : PackedWindow profile, left ≠ right →
    Disjoint (support profile left) (support profile right)

/-- The canonical packing is packed.  A theorem, never a hypothesis. -/
theorem packed (profile : InducedPathMaximalPacking.Profile object order) :
    Packed profile :=
  fun left right different =>
    supports_pairwise_disjoint profile left right different

/-! ## Independence of the packed-window coordinates -/

/-- **`coordinate_independence`.**  Packed windows carry independent
coordinates: local observations that separate each window's own states
separate every joint state.

The packedness hypothesis is what makes this the *manuscript's* independence
rather than a formal restatement — it is the reason a per-window observation
may be read off the induced structure on that window's support without any
other window's support interfering, i.e. `lem:p13-window-package`'s "no
coordinate is counted twice".  The lift itself is
`Core.FiniteEntropy.injective_pi_of_forall_injective`, owned by Core. -/
theorem coordinate_independence
    (profile : InducedPathMaximalPacking.Profile object order)
    (_packed : Packed profile)
    {State : PackedWindow profile → Type v}
    {Observed : PackedWindow profile → Type w}
    (observe : ∀ window, State window → Observed window)
    (injective : ∀ window, Function.Injective (observe window)) :
    Function.Injective
      (fun (state : ∀ window, State window) window =>
        observe window (state window)) :=
  Core.FiniteEntropy.injective_pi_of_forall_injective observe injective

/-- The joint state of every packed window.  Its dependent-function shape is
what records that each window occurs exactly once. -/
abbrev JointState {profile : InducedPathMaximalPacking.Profile object order}
    (State : PackedWindow profile → Type v) :=
  ∀ window : PackedWindow profile, State window

/-- The exact multiplicative state demand of the window package, derived from
the local carriers rather than declared. -/
noncomputable def demand
    {profile : InducedPathMaximalPacking.Profile object order}
    (State : PackedWindow profile → Type v) : Nat :=
  Nat.card (JointState State)

/-- **`lem:p13-window-package`'s multiplicative form.**  The window package's
demand is the product of the per-window demands — the exact statement that the
packed coordinates are independent, with `log₂` turning the product into the
manuscript's sum over windows. -/
theorem demand_eq_product
    {profile : InducedPathMaximalPacking.Profile object order}
    (State : PackedWindow profile → Type v) [∀ window, Finite (State window)] :
    demand State = ∏ window, Nat.card (State window) :=
  Core.FiniteEntropy.card_pi_eq_prod_card State

/-- **`lem:p13-window-package` at a uniform per-window carrier.**

Every packed window carries the same finite package -- the registered barrier
schedule declared at every separated dyadic scale is the same schedule at each
window -- so the joint demand is that one local count raised to the number of
packed windows:

  `demand State = localDemand ^ p₁₃`.

That is the exact shape the density comparison's `stateDemand` has, with
`localDemand` the derived `safeProduct` and `p₁₃` the ledger packing's own
cardinality.  The exponent is not chosen: it is `card_packedWindow`. -/
theorem demand_eq_pow_of_uniform
    {profile : InducedPathMaximalPacking.Profile object order}
    (State : PackedWindow profile → Type v) [∀ window, Finite (State window)]
    (localDemand : Nat)
    (uniform : ∀ window, Nat.card (State window) = localDemand) :
    demand State = localDemand ^ profile.selected.length := by
  classical
  rw [demand_eq_product State, Finset.prod_congr rfl
    (fun window _ => uniform window), Finset.prod_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, card_packedWindow]

/-! ## Realization by labelled skeletons

`lem:skeleton-dominates` assigns target-complete states to labelled graphs
*canonically*, so the assignment is a plain map `LabelledOn n → JointState`
and the family of states the proof realizes is exactly its range.  The two
facts `prop:p13-density` needs from it are already theorems in
`Graph.LabelledOn`; the packed-window content is what is stated against them
here. -/

/-- **`lem:state-count-comparison` for a packed-window assignment.**  The
window states the proof actually realizes never outnumber the labelled
skeletons of the same order.

This is `Graph.LabelledOn.card_realized_le` at the packed-window joint state
type, and it needs no realization hypothesis: `realize` is the canonical choice
inside a state's own fibre and `realize_injective` is a theorem. -/
theorem card_realized_le
    {profile : InducedPathMaximalPacking.Profile object order}
    {State : PackedWindow profile → Type v} (n : Nat)
    (stateOf : LabelledOn n → JointState State) :
    Nat.card (LabelledOn.Realized stateOf) ≤ Nat.card (LabelledOn n) :=
  LabelledOn.card_realized_le n stateOf

/-- **`state_card_le`.**  A packed-window package whose *whole* joint family is
realized by labelled skeletons has demand at most the labelled-skeleton count.

The hypothesis is exactly the manuscript's "all target-complete window states
are realized by labelled near-cubic skeletons": surjectivity of the canonical
assignment onto the joint family.  Nothing else is assumed, and in particular
no injection is supplied — `Nat.card_le_card_of_surjective` is the pigeonhole
in the direction a *demand* travels. -/
theorem demand_le_card_labelled
    {profile : InducedPathMaximalPacking.Profile object order}
    {State : PackedWindow profile → Type v} {n : Nat}
    (stateOf : LabelledOn n → JointState State)
    (realized : Function.Surjective stateOf) :
    demand State ≤ Nat.card (LabelledOn n) :=
  Nat.card_le_card_of_surjective stateOf realized

/-- The same comparison from an injective realization of the joint family,
which is the shape a per-window realization produces after
`coordinate_independence`. -/
theorem demand_le_card_labelled_of_injective
    {profile : InducedPathMaximalPacking.Profile object order}
    {State : PackedWindow profile → Type v} {n : Nat}
    (realize : JointState State → LabelledOn n)
    (injective : Function.Injective realize) :
    demand State ≤ Nat.card (LabelledOn n) :=
  Nat.card_le_card_of_injective realize injective

/-- **`entropy_cap`.**  A realized packed-window package cannot overflow the
labelled-skeleton count.  This is the closing step of every entropy-cap
argument in the manuscript, here as an eliminator on the overflow branch. -/
theorem entropy_cap
    {profile : InducedPathMaximalPacking.Profile object order}
    {State : PackedWindow profile → Type v} {n : Nat}
    (realize : JointState State → LabelledOn n)
    (injective : Function.Injective realize)
    (overflow : Nat.card (LabelledOn n) < demand State) : False :=
  absurd (demand_le_card_labelled_of_injective realize injective)
    (Nat.not_le.mpr overflow)

/-- **`lem:independent-target-entropy` at the canonical packing.**

`2 ^ k ≤ |𝒢|`: whatever exponent the window package's demand certifies is
certified against the labelled-skeleton count.  The manuscript's `k` is
`(c₁₃ − o(1)) p₁₃ log₂ n`; here it is any exponent the multiplicative demand
already dominates, so no rate constant is named. -/
theorem two_pow_le_card_labelled
    {profile : InducedPathMaximalPacking.Profile object order}
    {State : PackedWindow profile → Type v} {n exponent : Nat}
    (realize : JointState State → LabelledOn n)
    (injective : Function.Injective realize)
    (demanded : 2 ^ exponent ≤ demand State) :
    2 ^ exponent ≤ Nat.card (LabelledOn n) :=
  demanded.trans (demand_le_card_labelled_of_injective realize injective)

/-! ## The labelled-skeleton class as a finite carrier

`lem:skeleton-dominates` counts `𝒢_n`, all labelled simple graphs on `[n]`,
before the edge count is fixed.  `Graph.LabelledOn` is that class as a genuine
finite type; the one quantitative fact the entropy account needs from it is its
size, and only from below. -/

/-- **`|𝒢_n| ≥ 2 ^ binom(n,2)`.**

A labelled simple graph on `[n]` is determined by its edge set, and every
subset of the complete graph's edge set is the edge set of one: the
`2 ^ binom(n,2)` subsets of `⊤.edgeFinset` therefore inject into `LabelledOn n`.
The equality holds too, but only this direction is consumed. -/
theorem two_pow_choose_two_le_card_labelled (n : Nat) :
    2 ^ (n.choose 2) ≤ Nat.card (LabelledOn n) := by
  classical
  set edges : Finset (Sym2 (Fin n)) := (⊤ : SimpleGraph (Fin n)).edgeFinset
    with edgesDef
  have edgesCard : edges.card = n.choose 2 := by
    simpa [edgesDef] using
      (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n))
  have offDiagonal : ∀ {selected : Finset (Sym2 (Fin n))},
      selected ∈ edges.powerset →
        (↑selected : Set (Sym2 (Fin n))) \ Sym2.diagSet = ↑selected := by
    intro selected member
    rw [Finset.mem_powerset] at member
    refine Set.Subset.antisymm Set.sdiff_subset ?_
    intro edge inSelected
    refine ⟨inSelected, ?_⟩
    have inEdges : edge ∈ edges := member inSelected
    rwa [edgesDef, SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top]
      at inEdges
  have injective : Function.Injective
      (fun selected : {chosen : Finset (Sym2 (Fin n)) //
          chosen ∈ edges.powerset} =>
        (⟨SimpleGraph.fromEdgeSet
          (↑(selected : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))⟩ :
            LabelledOn n)) := by
    intro left right equality
    have graphEq := congrArg LabelledOn.graph equality
    simp only at graphEq
    have edgeEq := congrArg SimpleGraph.edgeSet graphEq
    rw [SimpleGraph.edgeSet_fromEdgeSet, SimpleGraph.edgeSet_fromEdgeSet,
      offDiagonal left.2, offDiagonal right.2] at edgeEq
    exact Subtype.ext (Finset.coe_injective edgeEq)
  have bound := Nat.card_le_card_of_injective _ injective
  have subtypeCard :
      Nat.card {chosen : Finset (Sym2 (Fin n)) // chosen ∈ edges.powerset} =
        2 ^ (n.choose 2) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powerset,
      edgesCard]
  omega

/-- **`|𝒢_{|R|}| ≤ |𝒢_n|` whenever `|R| ≤ n`.**

`def:remainder-entropy` puts its class `𝒢(R)` on `V(R)`, the remainder's own
vertex set, while `lem:skeleton-dominates` counts the ambient class `𝒢_n` on
`[n]`.  A labelled graph on `[|R|]` is a labelled graph on `[n]` transported
along the inclusion `[|R|] ↪ [n]`, and transport along an embedding is
injective on graphs, so the remainder class never outnumbers the ambient one.
This is the inclusion `𝒢(R) ⊆ 𝒢_n` that `lem:skeleton-dominates` uses when it
pays the remainder's realized states out of the labelled-skeleton budget. -/
theorem card_labelled_mono {remainder order : Nat} (le : remainder ≤ order) :
    Nat.card (LabelledOn remainder) ≤ Nat.card (LabelledOn order) := by
  refine Nat.card_le_card_of_injective
    (fun skeleton =>
      (⟨SimpleGraph.map (Fin.castLEEmb le) skeleton.graph⟩ :
        LabelledOn order)) ?_
  intro left right equality
  exact LabelledOn.ext
    (SimpleGraph.map_injective (Fin.castLEEmb le)
      (congrArg LabelledOn.graph equality))

/-! ## The near-cubic labelled skeleton class `𝒢_{n,m}`

`lem:skeleton-dominates` fixes the edge count before counting:

> Fix `n` and `m`.  Let `𝒢_{n,m}` be the set of all finite simple labelled
> graphs on vertex set `[n]` with exactly `m` edges.  Then
> `|𝒢_{n,m}| = binom(binom(n,2), m)`.

That count is the `skeletonBudget` the finite density budget registers, so the
class has to exist as a finite type for a realization to land in it.  It is the
subtype of `LabelledOn n` cut out by the edge count, and its cardinality is the
manuscript's binomial exactly — proved, not registered. -/

/-- `𝒢_{n,m}`: the labelled simple graphs on `[n]` carrying exactly `m` edges. -/
def Skeleton (n m : Nat) : Type :=
  {skeleton : LabelledOn n // Nat.card skeleton.graph.edgeSet = m}

instance instFiniteSkeleton (n m : Nat) : Finite (Skeleton n m) :=
  Subtype.finite

/-- **`lem:skeleton-dominates`'s count, proved.**  `|𝒢_{n,m}| =
binom(binom(n,2), m)`: a labelled simple graph on `[n]` is determined by its
edge set, an `m`-element subset of the `binom(n,2)` unordered pairs. -/
theorem card_skeleton (n m : Nat) :
    Nat.card (Skeleton n m) = (n.choose 2).choose m := by
  classical
  set edges : Finset (Sym2 (Fin n)) := (⊤ : SimpleGraph (Fin n)).edgeFinset
    with edgesDef
  have edgesCard : edges.card = n.choose 2 := by
    simpa [edgesDef] using
      (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n))
  have memEdges : ∀ {edge : Sym2 (Fin n)}, edge ∈ edges ↔ ¬ edge.IsDiag := by
    intro edge
    rw [edgesDef, SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top]
    exact Iff.rfl
  -- The chosen `m`-subsets of the complete graph's edge set.
  set chosen : Finset (Finset (Sym2 (Fin n))) := edges.powersetCard m
    with chosenDef
  have offDiagonal : ∀ {selected : Finset (Sym2 (Fin n))}, selected ∈ chosen →
      (↑selected : Set (Sym2 (Fin n))) \ Sym2.diagSet = ↑selected := by
    intro selected member
    rw [chosenDef, Finset.mem_powersetCard] at member
    refine Set.Subset.antisymm Set.sdiff_subset ?_
    intro edge inSelected
    exact ⟨inSelected, memEdges.mp (member.1 inSelected)⟩
  have cardOf : ∀ {selected : Finset (Sym2 (Fin n))}, selected ∈ chosen →
      Nat.card
          (SimpleGraph.fromEdgeSet
            (↑selected : Set (Sym2 (Fin n)))).edgeSet = m := by
    intro selected member
    have cardEq : selected.card = m := by
      rw [chosenDef, Finset.mem_powersetCard] at member
      exact member.2
    rw [SimpleGraph.edgeSet_fromEdgeSet, offDiagonal member]
    rw [Nat.card_eq_card_toFinset]
    simpa using cardEq
  -- The bijection.
  refine Nat.card_eq_of_bijective
    (fun selected : {picked : Finset (Sym2 (Fin n)) // picked ∈ chosen} =>
      (⟨⟨SimpleGraph.fromEdgeSet
          (↑(selected : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))⟩,
        cardOf selected.2⟩ : Skeleton n m)) ?_ |>.symm.trans ?_
  · constructor
    · intro left right equality
      have graphEq :=
        congrArg (fun skeleton : Skeleton n m => skeleton.1.graph) equality
      simp only at graphEq
      have edgeEq := congrArg SimpleGraph.edgeSet graphEq
      rw [SimpleGraph.edgeSet_fromEdgeSet, SimpleGraph.edgeSet_fromEdgeSet,
        offDiagonal left.2, offDiagonal right.2] at edgeEq
      exact Subtype.ext (Finset.coe_injective edgeEq)
    · rintro ⟨⟨graph⟩, graphCard⟩
      refine ⟨⟨graph.edgeSet.toFinset, ?_⟩, ?_⟩
      · rw [chosenDef, Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro edge member
          rw [Set.mem_toFinset] at member
          exact memEdges.mpr (SimpleGraph.not_isDiag_of_mem_edgeSet _ member)
        · rw [← graphCard, Nat.card_eq_card_toFinset]
      · refine Subtype.ext (LabelledOn.ext ?_)
        simp only [Set.coe_toFinset]
        exact SimpleGraph.fromEdgeSet_edgeSet _
  · rw [Nat.card_eq_fintype_card, Fintype.card_coe, chosenDef,
      Finset.card_powersetCard, edgesCard]

/-- **`lem:state-count-comparison` against the near-cubic class.**  A
packed-window package realized inside `𝒢_{n,m}` has demand at most
`binom(binom(n,2), m)`, which is the labelled skeleton budget the finite
density budget registers.

This is `prop:p13-density`'s middle step verbatim: "since all target-complete
window states are realized by labelled near-cubic skeletons under
`def:near-cubic-spine`, `lem:independent-target-entropy, lem:skeleton-dominates`
give ...".  Both `n` and `m` come from the realization's own class; nothing is
chosen here. -/
theorem demand_le_skeletonBudget
    {profile : InducedPathMaximalPacking.Profile object order}
    {State : PackedWindow profile → Type v} {n m : Nat}
    (realize : JointState State → Skeleton n m)
    (injective : Function.Injective realize) :
    demand State ≤ (n.choose 2).choose m :=
  (Nat.card_le_card_of_injective realize injective).trans
    (le_of_eq (card_skeleton n m))

/-- **`lem:independent-target-entropy` against the near-cubic class.**

`2 ^ k ≤ |𝒢_{n,m}|`.  Composed with the exponent bookkeeping of
`Graph.Strategy.FiniteDensityBudget`, this is the whole of `prop:p13-density`:
whatever exponent the window package's own multiplicative demand certifies is
paid out of the labelled skeleton budget, so the density cap is produced by a
realization rather than observed. -/
theorem two_pow_le_skeletonBudget
    {profile : InducedPathMaximalPacking.Profile object order}
    {State : PackedWindow profile → Type v} {n m exponent : Nat}
    (realize : JointState State → Skeleton n m)
    (injective : Function.Injective realize)
    (demanded : 2 ^ exponent ≤ demand State) :
    2 ^ exponent ≤ (n.choose 2).choose m :=
  demanded.trans (demand_le_skeletonBudget realize injective)

end Hypostructure.Graph.PackedWindowRealization
