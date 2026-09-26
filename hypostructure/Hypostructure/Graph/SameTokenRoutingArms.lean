import Hypostructure.Graph.SameTokenRoutingGerms

/-!
# Finite path and incidence facts for two routed arms

Generic list, path, and incidence mathematics used when two simple connector
walks from a common root first separate.  Everything is stated over an
arbitrary simple graph or finite object; no ledger, key, or proof-specific
statement occurs here.

* `mem_pathEdges_endpoint`, `pathEdges_first_incidence`, `pathEdges_singleton`:
  the consecutive-edge set of a list;
* `coreEdges_pair_subset`: the induced edge set of a two-vertex support;
* `eq_singleton_of_head_last_nodup`: a simple list starting and ending at the
  same vertex is that vertex;
* `mem_other_arm_of_saturated`: a degree-at-least-three arm start whose
  incidences all lie in the two-arm skeleton lies on the other arm;
* `exists_firstEntryPrefix`: trim a list at its first entry into a finite set;
* `cubic_third_incidence`, `cubic_incidence_of_separation`: the three
  incidences at a degree-three separator;
* `exists_maximal_commonPrefix`, `commonPrefixLength_shortcut`,
  `RoutingConfiguration.exists_sourcePreserving_shortcut`: common-prefix
  maximization and the shortcut that strictly lengthens it.
-/

namespace Hypostructure.Graph.SameTokenRoutingArms

open Hypostructure.Graph

universe u

section Lists

variable {V : Type*} [DecidableEq V]

/-- Both ends of a consecutive edge of a list lie on the list. -/
theorem mem_pathEdges_endpoint (path : List V) (edge : Sym2 V)
    (edgeMem : edge ∈ ((path.zip path.tail).toFinset).image
      (fun pair => s(pair.1, pair.2)))
    (vertex : V) (vertexMem : vertex ∈ edge) : vertex ∈ path := by
  obtain ⟨pair, pairMem, pairEdge⟩ := Finset.mem_image.mp edgeMem
  have pairListMem : pair ∈ path.zip path.tail :=
    List.mem_toFinset.mp pairMem
  obtain ⟨firstMem, secondTailMem⟩ := List.of_mem_zip pairListMem
  have secondMem : pair.2 ∈ path :=
    List.mem_of_mem_tail secondTailMem
  rw [← pairEdge, Sym2.mem_iff] at vertexMem
  rcases vertexMem with rfl | rfl
  · exact firstMem
  · exact secondMem

/-- In a simple list starting at `start`, the only consecutive edge at
`start` is the first one. -/
theorem pathEdges_first_incidence (path : List V) (start other : V)
    (issued : path.head? = some start) (nodup : path.Nodup)
    (incident : s(start, other) ∈ ((path.zip path.tail).toFinset).image
      (fun pair => s(pair.1, pair.2))) :
    ∃ next rest, path = start :: next :: rest ∧ other = next := by
  cases path with
  | nil => simp at issued
  | cons head tail =>
    have headEq : head = start := by simpa using issued
    subst head
    cases tail with
    | nil => simp at incident
    | cons next rest =>
      have startNotTail : start ∉ next :: rest :=
        (List.nodup_cons.mp nodup).1
      have startNeNext : start ≠ next := by
        intro equal
        exact startNotTail (equal ▸ List.mem_cons_self)
      have firstOrLater :
          s(start, other) = s(start, next) ∨
            s(start, other) ∈ (((next :: rest).zip rest).toFinset).image
              (fun pair => s(pair.1, pair.2)) := by
        simpa [List.zip_cons_cons, Finset.image_insert] using incident
      rcases firstOrLater with first | later
      · rcases (Sym2.mk_eq_mk_iff
          (p := (start, other)) (q := (start, next))).mp first with
          same | swapped
        · exact ⟨next, rest, rfl, (Prod.mk.inj same).2⟩
        · exact False.elim (startNeNext (Prod.mk.inj swapped).1)
      · exact False.elim
          (startNotTail (mem_pathEdges_endpoint (next :: rest)
            (s(start, other)) later start (Sym2.mem_mk_left start other)))

/-- A one-vertex list has no consecutive edge. -/
theorem pathEdges_singleton (start : V) :
    (([start].zip [start].tail).toFinset).image
      (fun pair => s(pair.1, pair.2)) = ∅ := by
  simp

omit [DecidableEq V] in
/-- A simple list whose head and last entry agree is a singleton. -/
theorem eq_singleton_of_head_last_nodup (path : List V) (start : V)
    (issued : path.head? = some start) (last : path.getLast? = some start)
    (nodup : path.Nodup) : path = [start] := by
  cases path with
  | nil => simp at issued
  | cons head tail =>
    have headEq : head = start := by simpa using issued
    subst head
    cases tail with
    | nil => rfl
    | cons next rest =>
      have startNotTail : start ∉ next :: rest :=
        (List.nodup_cons.mp nodup).1
      have tailLast : (next :: rest).getLast? = some start := by
        simpa using last
      have startMemTail : start ∈ next :: rest :=
        List.mem_of_mem_getLast? (by simpa [tailLast])
      exact False.elim (startNotTail startMemTail)

/-- Trim a list at its first entry into a finite set it eventually reaches. -/
theorem exists_firstEntryPrefix (path : List V) (selected : Finset V)
    (lands : ∃ terminal, path.getLast? = some terminal ∧ terminal ∈ selected) :
    ∃ terminal initialSegment,
      initialSegment <+: path ∧
        initialSegment.head? = path.head? ∧
        initialSegment.getLast? = some terminal ∧
        terminal ∈ selected ∧
        ∀ vertex ∈ initialSegment, vertex ∈ selected → vertex = terminal := by
  let meets : V → Bool := fun vertex => decide (vertex ∈ selected)
  obtain ⟨last, lastEq, lastSelected⟩ := lands
  have lastMem : last ∈ path := by
    obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp lastEq
    simp
  have meetsSome : ∃ vertex ∈ path, meets vertex :=
    ⟨last, lastMem, by simp [meets, lastSelected]⟩
  have indexLt : path.findIdx meets < path.length :=
    List.findIdx_lt_length_of_exists meetsSome
  let terminal := path[path.findIdx meets]
  let initialSegment := path.take (path.findIdx meets + 1)
  have terminalSelected : terminal ∈ selected := by
    have found : meets terminal :=
      List.findIdx_getElem (xs := path) (p := meets)
    simpa [meets] using found
  have split :
      initialSegment = path.take (path.findIdx meets) ++ [terminal] := by
    simpa [initialSegment, terminal] using
      List.take_succ_eq_append_getElem indexLt
  refine ⟨terminal, initialSegment, ?_, ?_, ?_, terminalSelected, ?_⟩
  · simpa [initialSegment] using
      (List.take_prefix (path.findIdx meets + 1) path)
  · simp [initialSegment, List.head?_take]
  · rw [split]
    exact List.getLast?_concat
  · intro vertex member selectedMember
    rw [split, List.mem_append] at member
    rcases member with before | final
    · have absent : meets vertex = false :=
        List.false_of_mem_take_findIdx before
      simp [meets, selectedMember] at absent
    · simpa using final

/-- Replacing the entry after a shared vertex by a different one ends the
common prefix there, while keeping it extends the common prefix by one. -/
theorem commonPrefixLength_shortcut :
    ∀ (common : List V) (h a b : V) (tailLeft tailRight after : List V),
      a ≠ b →
      SameTokenRoutingGerms.commonPrefixLength
          (common ++ h :: a :: tailLeft)
          (common ++ h :: b :: tailRight) = common.length + 1 ∧
        common.length + 2 ≤
          SameTokenRoutingGerms.commonPrefixLength
            (common ++ h :: a :: tailLeft)
            (common ++ h :: a :: after) := by
  intro common h a b tailLeft tailRight after different
  induction common with
  | nil =>
    constructor
    · simp [SameTokenRoutingGerms.commonPrefixLength, different]
    · simp [SameTokenRoutingGerms.commonPrefixLength]
  | cons x rest ih =>
    obtain ⟨old, new⟩ := ih
    constructor
    · simpa [SameTokenRoutingGerms.commonPrefixLength, old,
        List.length_cons, Nat.add_assoc] using congrArg Nat.succ old
    · simp only [List.cons_append, List.length_cons,
        SameTokenRoutingGerms.commonPrefixLength, ↓reduceIte]
      omega

/-- Among valid pairs of simple paths in a finite vertex type, one pair has
a maximal common prefix. -/
theorem exists_maximal_commonPrefix [Fintype V] {A B : Type*}
    (pathA : A → List V) (pathB : B → List V)
    (validA : A → Prop) (validB : B → Prop)
    (simpleA : ∀ a, validA a → (pathA a).Nodup)
    (existsA : ∃ a, validA a) (existsB : ∃ b, validB b) :
    ∃ a b, validA a ∧ validB b ∧
      ∀ a' b', validA a' → validB b' →
        SameTokenRoutingGerms.commonPrefixLength (pathA a') (pathB b') ≤
          SameTokenRoutingGerms.commonPrefixLength (pathA a) (pathB b) := by
  classical
  let scores : Finset Nat :=
    (Finset.range (Fintype.card V + 1)).filter fun score =>
      ∃ a b, validA a ∧ validB b ∧
        SameTokenRoutingGerms.commonPrefixLength (pathA a) (pathB b) = score
  have score_mem (a : A) (b : B) (ha : validA a) (hb : validB b) :
      SameTokenRoutingGerms.commonPrefixLength (pathA a) (pathB b) ∈
        scores := by
    have pathBound : (pathA a).length ≤ Fintype.card V := by
      calc
        (pathA a).length = (pathA a).toFinset.card :=
          (List.toFinset_card_of_nodup (simpleA a ha)).symm
        _ ≤ Fintype.card V := Finset.card_le_univ _
    have prefixBound :=
      SameTokenRoutingGerms.commonPrefixLength_le_left (pathA a) (pathB b)
    simp only [scores, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, a, b, ha, hb, rfl⟩
  obtain ⟨a₀, ha₀⟩ := existsA
  obtain ⟨b₀, hb₀⟩ := existsB
  have scoresNonempty : scores.Nonempty := ⟨_, score_mem a₀ b₀ ha₀ hb₀⟩
  obtain ⟨score, scoreIn, scoreMax⟩ :=
    Finset.exists_max_image scores (fun n => n) scoresNonempty
  obtain ⟨a, b, ha, hb, scoreEq⟩ := (Finset.mem_filter.mp scoreIn).2
  refine ⟨a, b, ha, hb, ?_⟩
  intro a' b' ha' hb'
  have comparison := scoreMax _ (score_mem a' b' ha' hb')
  simpa only [id_eq, scoreEq] using comparison

end Lists

section Graphs

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The induced edges of a two-vertex support are at most its one pair. -/
theorem coreEdges_pair_subset (left right : V) :
    (({left, right} : Finset V).biUnion fun vertex =>
      ((({left, right} : Finset V).filter fun other => G.Adj vertex other).image
        fun other => s(vertex, other))) ⊆ {s(left, right)} := by
  intro edge edgeMem
  obtain ⟨first, firstMem, imageMem⟩ := Finset.mem_biUnion.mp edgeMem
  obtain ⟨second, secondMem, pairEdge⟩ := Finset.mem_image.mp imageMem
  have secondCore : second ∈ ({left, right} : Finset V) :=
    (Finset.mem_filter.mp secondMem).1
  have adjacent : G.Adj first second := (Finset.mem_filter.mp secondMem).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at firstMem secondCore
  rcases firstMem with firstEq | firstEq <;>
    rcases secondCore with secondEq | secondEq
  · subst first
    subst second
    exact False.elim (G.irrefl adjacent)
  · subst first
    subst second
    exact Finset.mem_singleton.mpr pairEdge.symm
  · subst first
    subst second
    exact Finset.mem_singleton.mpr
      ((Sym2.eq_swap (a := right) (b := left)).symm.trans pairEdge).symm
  · subst first
    subst second
    exact False.elim (G.irrefl adjacent)

variable [Fintype V]

/-- If every incidence at the start `a` of the arm `left` lies in the skeleton
formed by both arms, the two centre edges, and the induced edges of a
two-vertex core, and `a` has degree at least three, then `a` also lies on the
other arm. -/
theorem mem_other_arm_of_saturated (h a b u v : V) (left right : List V)
    (aneqH : a ≠ h) (aneqB : a ≠ b)
    (head : left.head? = some a) (nodup : left.Nodup)
    (singleOfCore : a ∈ ({u, v} : Finset V) → left = [a])
    (deg : 3 ≤ G.degree a)
    (sat : ∀ edge ∈ G.incidenceFinset a,
      edge ∈ ((((left.zip left.tail).toFinset).image
          (fun pair => s(pair.1, pair.2)) ∪
        ((right.zip right.tail).toFinset).image
          (fun pair => s(pair.1, pair.2)) ∪
        {s(h, a), s(h, b)}) ∪
        (({u, v} : Finset V).biUnion fun vertex =>
          ((({u, v} : Finset V).filter fun other => G.Adj vertex other).image
            fun other => s(vertex, other))))) :
    a ∈ right := by
  by_contra notRight
  let armLeft := ((left.zip left.tail).toFinset).image
    (fun pair => s(pair.1, pair.2))
  let core := ({u, v} : Finset V).biUnion fun vertex =>
    ((({u, v} : Finset V).filter fun other => G.Adj vertex other).image
      fun other => s(vertex, other))
  let I := G.incidenceFinset a
  let P := I ∩ armLeft
  let C := I ∩ core
  have incidentVertex (e : Sym2 V) (he : e ∈ I) : a ∈ e :=
    ((G.mem_incidenceFinset a e).mp he).2
  have pCard : P.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro e he e' he'
    have heI : e ∈ I := (Finset.mem_inter.mp he).1
    have heP : e ∈ armLeft := (Finset.mem_inter.mp he).2
    have heI' : e' ∈ I := (Finset.mem_inter.mp he').1
    have heP' : e' ∈ armLeft := (Finset.mem_inter.mp he').2
    obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.mp (incidentVertex e heI)
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp (incidentVertex e' heI')
    obtain ⟨n, r, hpath, hx⟩ :=
      pathEdges_first_incidence left a x head nodup heP
    obtain ⟨n', r', hpath', hy⟩ :=
      pathEdges_first_incidence left a y head nodup heP'
    have hn : n = n' := by
      rw [hpath] at hpath'
      cases hpath'
      rfl
    simp [hx, hy, hn]
  have cCard : C.card ≤ 1 := by
    have hsub : C ⊆ ({s(u, v)} : Finset (Sym2 V)) := by
      intro e he
      exact coreEdges_pair_subset G u v (Finset.mem_inter.mp he).2
    have := Finset.card_le_card hsub
    simpa using this
  have hsub : I ⊆ ({s(h, a)} ∪ P) ∪ C := by
    intro e he
    have hf := sat e he
    simp only [Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hf
    rcases hf with (((hleft | hright) | hcentre) | hcore)
    · simp [P, armLeft, he, hleft]
    · have atRight :=
        mem_pathEdges_endpoint right e hright a (incidentVertex e he)
      exact False.elim (notRight atRight)
    · rcases hcentre with ha | hb
      · simp [ha]
      · have ahb : a ∈ s(h, b) := hb ▸ incidentVertex e he
        rcases (Sym2.mem_iff.mp ahb) with eq | eq
        · exact False.elim (aneqH eq)
        · exact False.elim (aneqB eq)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨he, hcore⟩)
  have hc : 3 ≤ I.card := by
    rw [show I.card = G.degree a from G.card_incidenceFinset_eq_degree a]
    exact deg
  by_cases inCore : a ∈ ({u, v} : Finset V)
  · have pEmpty : P = ∅ := by
      simp [P, armLeft, singleOfCore inCore]
    have sub2 : I ⊆ ({s(h, a)} : Finset (Sym2 V)) ∪ C := by
      simpa [pEmpty] using hsub
    have hi := Finset.card_le_card sub2
    have hu : (({s(h, a)} : Finset (Sym2 V)) ∪ C).card ≤ 1 + C.card := by
      simpa only [Finset.card_singleton] using
        Finset.card_union_le ({s(h, a)} : Finset (Sym2 V)) C
    omega
  · have cEmpty : C = ∅ := by
      ext e
      simp only [Finset.notMem_empty, iff_false]
      intro he
      have heI : e ∈ I := (Finset.mem_inter.mp he).1
      have heC : e ∈ core := (Finset.mem_inter.mp he).2
      have eq : e = s(u, v) :=
        Finset.mem_singleton.mp (coreEdges_pair_subset G u v heC)
      have amem : a ∈ s(u, v) := eq ▸ incidentVertex e heI
      have aneU : a ≠ u := by
        intro eq; exact inCore (by simp [eq])
      have aneV : a ≠ v := by
        intro eq; exact inCore (by simp [eq])
      rcases (Sym2.mem_iff.mp amem) with eq | eq
      · exact aneU eq
      · exact aneV eq
    have sub2 : I ⊆ ({s(h, a)} : Finset (Sym2 V)) ∪ P := by
      simpa [cEmpty] using hsub
    have hi := Finset.card_le_card sub2
    have hu : (({s(h, a)} : Finset (Sym2 V)) ∪ P).card ≤ 1 + P.card := by
      simpa only [Finset.card_singleton] using
        Finset.card_union_le ({s(h, a)} : Finset (Sym2 V)) P
    omega

/-- At a degree-three vertex with two distinct used neighbours, the unique
remaining neighbour completes its incidence list. -/
theorem cubic_third_incidence (separator nextLeft nextRight : V)
    (nextLeftAdj : G.Adj separator nextLeft)
    (nextRightAdj : G.Adj separator nextRight)
    (nextDifferent : nextLeft ≠ nextRight)
    (neighbourCard : (G.neighborFinset separator).card = 3) :
    ∃ rootIncidence,
      G.Adj rootIncidence separator ∧
        rootIncidence ≠ nextLeft ∧
        rootIncidence ≠ nextRight ∧
        ∀ neighbour, G.Adj separator neighbour →
          neighbour = rootIncidence ∨
            neighbour = nextLeft ∨ neighbour = nextRight := by
  let usedNext : Finset V := {nextLeft, nextRight}
  have usedNextCard : usedNext.card = 2 := by
    simp [usedNext, nextDifferent]
  have remaining : ∃ rootIncidence,
      rootIncidence ∈ G.neighborFinset separator ∧
        rootIncidence ∉ usedNext := by
    by_contra absent
    push Not at absent
    have allUsed : G.neighborFinset separator ⊆ usedNext := by
      intro neighbour member
      exact absent neighbour member
    have counted := Finset.card_le_card allUsed
    rw [neighbourCard, usedNextCard] at counted
    omega
  obtain ⟨rootIncidence, rootMember, rootFresh⟩ := remaining
  have rootAdj : G.Adj rootIncidence separator :=
    ((SimpleGraph.mem_neighborFinset _ _ _).1 rootMember).symm
  have rootNeLeft : rootIncidence ≠ nextLeft := by
    intro equal
    apply rootFresh
    simp [usedNext, equal]
  have rootNeRight : rootIncidence ≠ nextRight := by
    intro equal
    apply rootFresh
    simp [usedNext, equal]
  let usedIncidences : Finset V := {rootIncidence, nextLeft, nextRight}
  have usedIncidencesCard : usedIncidences.card = 3 := by
    simp [usedIncidences, rootNeLeft, rootNeRight, nextDifferent]
  have usedIncidencesSubset :
      usedIncidences ⊆ G.neighborFinset separator := by
    intro neighbour member
    simp only [usedIncidences, Finset.mem_insert,
      Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl
    · exact rootMember
    · exact (SimpleGraph.mem_neighborFinset _ _ _).2 nextLeftAdj
    · exact (SimpleGraph.mem_neighborFinset _ _ _).2 nextRightAdj
  have usedIncidencesEq : usedIncidences = G.neighborFinset separator :=
    Finset.eq_of_subset_of_card_le usedIncidencesSubset (by
      rw [usedIncidencesCard, neighbourCard])
  refine ⟨rootIncidence, rootAdj, rootNeLeft, rootNeRight, ?_⟩
  intro neighbour adjacent
  have member : neighbour ∈ usedIncidences := by
    rw [usedIncidencesEq]
    exact (SimpleGraph.mem_neighborFinset _ _ _).2 adjacent
  simpa [usedIncidences] using member

/-- The three incidences at a degree-three first separator of two simple
walks: the two distinct next vertices and the vertex preceding the separator
(or, when the common prefix is empty, the remaining neighbour). -/
theorem cubic_incidence_of_separation
    (firstPath secondPath common : List V)
    (separator nextLeft nextRight : V) (tailLeft tailRight : List V)
    (firstChain : firstPath.IsChain G.Adj)
    (secondChain : secondPath.IsChain G.Adj)
    (firstNodup : firstPath.Nodup) (secondNodup : secondPath.Nodup)
    (leftDecomposition :
      firstPath = common ++ separator :: nextLeft :: tailLeft)
    (rightDecomposition :
      secondPath = common ++ separator :: nextRight :: tailRight)
    (nextDifferent : nextLeft ≠ nextRight)
    (neighbourCard : (G.neighborFinset separator).card = 3) :
    ∃ rootIncidence,
      G.Adj rootIncidence separator ∧
        rootIncidence ≠ nextLeft ∧
        rootIncidence ≠ nextRight ∧
        ∀ neighbour, G.Adj separator neighbour →
          neighbour = rootIncidence ∨
            neighbour = nextLeft ∨ neighbour = nextRight := by
  have nextLeftAdj : G.Adj separator nextLeft := by
    have chain := firstChain
    rw [leftDecomposition] at chain
    obtain ⟨_, rest, _⟩ := List.isChain_append.mp chain
    exact (List.isChain_cons.mp rest).1 nextLeft (by simp)
  have nextRightAdj : G.Adj separator nextRight := by
    have chain := secondChain
    rw [rightDecomposition] at chain
    obtain ⟨_, rest, _⟩ := List.isChain_append.mp chain
    exact (List.isChain_cons.mp rest).1 nextRight (by simp)
  by_cases commonEmpty : common = []
  · exact cubic_third_incidence G separator nextLeft nextRight nextLeftAdj
      nextRightAdj nextDifferent neighbourCard
  · let rootIncidence := common.getLast commonEmpty
    have rootIncidenceLast : common.getLast? = some rootIncidence :=
      List.getLast?_eq_some_getLast commonEmpty
    have rootIncidenceAdj : G.Adj rootIncidence separator := by
      have chain := firstChain
      rw [leftDecomposition] at chain
      obtain ⟨_, _, joint⟩ := List.isChain_append.mp chain
      exact joint rootIncidence rootIncidenceLast separator (by simp)
    have rootIncidenceNeLeft : rootIncidence ≠ nextLeft := by
      have nodup := firstNodup
      rw [leftDecomposition] at nodup
      exact (List.nodup_append.mp nodup).2.2 rootIncidence
        (List.getLast_mem commonEmpty) nextLeft (by simp)
    have rootIncidenceNeRight : rootIncidence ≠ nextRight := by
      have nodup := secondNodup
      rw [rightDecomposition] at nodup
      exact (List.nodup_append.mp nodup).2.2 rootIncidence
        (List.getLast_mem commonEmpty) nextRight (by simp)
    let usedIncidences : Finset V := {rootIncidence, nextLeft, nextRight}
    have usedIncidencesCard : usedIncidences.card = 3 := by
      simp [usedIncidences, rootIncidenceNeLeft, rootIncidenceNeRight,
        nextDifferent]
    have usedIncidencesSubset :
        usedIncidences ⊆ G.neighborFinset separator := by
      intro neighbour member
      simp only [usedIncidences, Finset.mem_insert,
        Finset.mem_singleton] at member
      rcases member with rfl | rfl | rfl
      · exact (SimpleGraph.mem_neighborFinset _ _ _).2 rootIncidenceAdj.symm
      · exact (SimpleGraph.mem_neighborFinset _ _ _).2 nextLeftAdj
      · exact (SimpleGraph.mem_neighborFinset _ _ _).2 nextRightAdj
    have usedIncidencesEq : usedIncidences = G.neighborFinset separator :=
      Finset.eq_of_subset_of_card_le usedIncidencesSubset (by
        rw [usedIncidencesCard, neighbourCard])
    refine ⟨rootIncidence, rootIncidenceAdj, rootIncidenceNeLeft,
      rootIncidenceNeRight, ?_⟩
    intro neighbour adjacent
    have member : neighbour ∈ usedIncidences := by
      rw [usedIncidencesEq]
      exact (SimpleGraph.mem_neighborFinset _ _ _).2 adjacent
    simpa [usedIncidences] using member

end Graphs

/-- A routing configuration `common ++ h :: b :: tail` whose tail contains a
neighbour `a` of `h` has a shortcut `common ++ h :: a :: after` with the same
source and landing entries. -/
theorem RoutingConfiguration.exists_sourcePreserving_shortcut
    {object : FiniteObject.{u}} {support source selected : Finset object.Vertex}
    (right : SameTokenRoutingGerms.RoutingConfiguration object support source
      selected)
    (common : List object.Vertex) (h a b : object.Vertex)
    (tail : List object.Vertex)
    (decomp : right.path = common ++ h :: b :: tail)
    (edge : object.graph.Adj h a) (inTail : a ∈ tail) :
    ∃ before after : List object.Vertex,
      ∃ shortcut : SameTokenRoutingGerms.RoutingConfiguration object support
          source selected,
        tail = before ++ a :: after ∧
          shortcut.path = common ++ h :: a :: after ∧
          shortcut.path.head? = right.path.head? ∧
          shortcut.path.getLast? = right.path.getLast? := by
  obtain ⟨before, after, tailEq⟩ := List.append_of_mem inTail
  let candidate : List object.Vertex := common ++ h :: a :: after
  have oldEq : right.path = common ++ h :: b :: (before ++ a :: after) := by
    simpa only [tailEq] using decomp
  have subTail : List.Sublist (a :: after) (b :: (before ++ a :: after)) :=
    List.sublist_append_right (b :: before) (a :: after)
  have subRight : List.Sublist (h :: a :: after)
      (h :: b :: (before ++ a :: after)) :=
    List.Sublist.cons_cons h subTail
  have subCandidate : List.Sublist candidate right.path := by
    rw [oldEq]
    simpa only [candidate] using (List.Sublist.refl common).append subRight
  have candidateNodup : candidate.Nodup := subCandidate.nodup right.nodup
  have candidateInside : ∀ item ∈ candidate, item ∈ support := by
    intro item itemMem
    exact right.inside item (subCandidate.subset itemMem)
  have oldChain : (common ++ h :: b :: (before ++ a :: after)).IsChain
      object.graph.Adj := by
    simpa only [oldEq] using right.chain
  have prefixChain : (common ++ [h]).IsChain object.graph.Adj := by
    have chain : ((common ++ [h]) ++ (b :: before ++ a :: after)).IsChain
        object.graph.Adj := by
      simpa [List.append_assoc] using oldChain
    exact chain.left_of_append
  have suffixChain : (a :: after).IsChain object.graph.Adj := by
    have chain : ((common ++ h :: b :: before) ++ (a :: after)).IsChain
        object.graph.Adj := by
      simpa only [List.append_assoc, List.cons_append] using oldChain
    exact chain.right_of_append
  have candidateChain : candidate.IsChain object.graph.Adj := by
    have bridge : ∀ x ∈ (common ++ [h]).getLast?,
        ∀ y ∈ (a :: after).head?, object.graph.Adj x y := by
      intro x hx y hy
      simp at hx hy
      subst x
      subst y
      exact edge
    simpa only [candidate, List.append_assoc, List.singleton_append] using
      prefixChain.append suffixChain bridge
  have candidateHead : candidate.head? = right.path.head? := by
    rw [decomp]
    simp [candidate, List.head?_append]
  have candidateLast : candidate.getLast? = right.path.getLast? := by
    have leftLast : candidate.getLast? = (a :: after).getLast? := by
      simpa [candidate, List.append_assoc] using
        (List.getLast?_append_of_ne_nil (common ++ [h])
          (l₂ := a :: after) (by simp))
    have rightLast : right.path.getLast? = (a :: after).getLast? := by
      rw [oldEq]
      simpa [List.append_assoc] using
        (List.getLast?_append_of_ne_nil (common ++ h :: b :: before)
          (l₂ := a :: after) (by simp))
    exact leftLast.trans rightLast.symm
  let shortcut : SameTokenRoutingGerms.RoutingConfiguration object support
      source selected := {
    path := candidate
    chain := candidateChain
    nodup := candidateNodup
    issued := by
      obtain ⟨initial, head, initialSource⟩ := right.issued
      exact ⟨initial, candidateHead.trans head, initialSource⟩
    inside := candidateInside
    lands := by
      obtain ⟨terminal, last, terminalSelected⟩ := right.lands
      exact ⟨terminal, candidateLast.trans last, terminalSelected⟩
  }
  exact ⟨before, after, shortcut, tailEq, rfl, candidateHead, candidateLast⟩

end Hypostructure.Graph.SameTokenRoutingArms
