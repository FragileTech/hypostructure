import Hypostructure.Graph.CommonPortReturnCycle
import Hypostructure.Graph.Response
import Hypostructure.Graph.InterfaceReplacement
import Hypostructure.Graph.SwitchForcedPaths

/-!
# Connector germs, surviving separators, and the decorated handoff fan envelope

This module owns the objects Type A exit `(7)` is made of, and nothing else:

* `def:typeA-continuation-classes` — outside connector germs through a
  completion port, the vertex two germs *separate at*, the switch support's
  switch constructed from G, and the absorbed/surviving classification of a
  separator;
* `lem:typeA-cubic-switch-absorption` — a surviving first separator has ambient
  degree at least `4`;
* `lem:typeA-continuation-routing` — a family of declared coordinates through
  one port either realizes one of the quotient alternatives or has a surviving
  first separator;
* `def:decorated-fan-envelope` — the envelope `𝔛 = (Y, H)` with its assigned
  first-neighbour sets, handoff arms and fan-safe cliques, and its net charge;
* `lem:typeA-high-degree-handoff` — a surviving first separator *produces* one;
* `lem:decorated-fan-admissibility` — the envelope carries exactly the data the
  Type B fan calculation consumes, and no conclusion of `lem:typeB-exclusion`;
* `def:decorated-typeB-envelope-support` and
  `lem:decorated-envelope-no-double-count` — the grouped envelope family and
  the exact-transfer identity;
* `lem:window-handoff-center-accounting` — a handoff center in a packed window
  is charged once, or the receiver realizes the label-collision exit.

Two things are worth saying about what is *derived* here rather than declared.

The degree bound is derived.  A germ is rooted at the receiver, so the common
prefix of two separating germs is never empty and its last edge is the
manuscript's *root incidence at `z`* in both of its cases at once — the port
edge `wh` when `z = h`, and the last edge of the common prefix otherwise.
Simplicity of the two germs then makes the root incidence and the two next
incidences three distinct neighbours of `z`, which is `d_G(z) ≥ 3`; the
separator being surviving rules out equality, which is `d_G(z) ≥ 4`.

The switch is constructed from G (G repair).  The identification of the two
separated response coordinates is realized on G itself, at the separator `z`:
the two configurations leave `z` through `a` (`nextLeft`) and `b`
(`nextRight`) and continue to `a⁺`, `b⁺`; the switch at `z` exchanges the two
continuations, `G − {a a⁺, b b⁺} + {a b⁺, b a⁺}` (`Separation.switchedGraph`,
all four vertices on the germs, hence in `S_z`; `G` itself when the exchange is
not a proper double-edge switch).  Its switched piece on `S_z` is `Separation.switchedPiece`, and
the switched graph `Separation.switched` has G's vertices.  No reading, state
or coordinate universe is supplied by a caller.  Stated about G, the switch is
target-defective when the switched graph and G differ in target truth, and
target-complete when they agree and `z` has no unused ambient incidence (the
manuscript's *"Assume `d_G(z)=3` ... Consequently `S_z` has no unused ambient
incidence at `z`.  The two separated responses therefore form a finite declared
boundaried response state with the same boundary-degree profile"*).

Nothing here knows a manuscript, a baseline, a scale, a window order, or a
proof.  The accepted-length predicate, the target, the boundary-degree profile,
the high-degree predicate and the coordinate universe are all parameters, and
no registered constant is written.  The one numeral that occurs is the count of
incidences a separation uses at its separator — the root incidence and the two
next incidences — which is intrinsic to the configuration and not a registered
threshold.
-/

namespace Hypostructure.Graph.DecoratedHandoff

open Hypostructure

universe u v w

/-! ## Separation of two lists

`def:typeA-continuation-classes` says two coordinates *separate at `z`* when
they have the same ordered prefix up to `z` and their next incidences after `z`
are distinct.  On the germs' vertex lists that is exactly the decomposition
below, and it forces the shared prefix to be *maximal*: the two lists agree on
`common ++ [z]` and differ immediately after it.  So a separator in this sense
is automatically the first separator of the pair. -/

variable {α : Type u}

/-- **Two lists separate at `z`**: the same ordered prefix up to and including
`z`, and distinct next entries. -/
def SeparatesAt (left right : List α) (separator : α) : Prop :=
  ∃ common nextLeft nextRight tailLeft tailRight,
    left = common ++ separator :: nextLeft :: tailLeft ∧
      right = common ++ separator :: nextRight :: tailRight ∧
        nextLeft ≠ nextRight

/-- **Two distinct lists issued from the same first entry, neither a prefix of
the other, separate somewhere.**  This is the finiteness step of
`lem:typeA-continuation-routing`: *"Since `𝒦` is finite and each configuration is
finite, there is a first such separator in the prefix order"*. -/
theorem exists_separatesAt :
    ∀ {left right : List α} {first : α}, left.head? = some first →
      right.head? = some first → ¬ left <+: right → ¬ right <+: left →
      ∃ separator, SeparatesAt left right separator
  | [], _, _, headLeft, _, _, _ => by simp at headLeft
  | _ :: _, [], _, _, headRight, _, _ => by simp at headRight
  | x :: restLeft, y :: restRight, first, headLeft, headRight,
      notPrefixLeft, notPrefixRight => by
      simp only [List.head?_cons, Option.some.injEq] at headLeft headRight
      subst headLeft
      subst headRight
      match restLeft, restRight with
      | [], _ =>
          exact absurd (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩)
            notPrefixLeft
      | _ :: _, [] =>
          exact absurd (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩)
            notPrefixRight
      | a :: tailLeft, b :: tailRight =>
          by_cases equal : a = b
          · subst equal
            have innerLeft : ¬ (a :: tailLeft) <+: (a :: tailRight) := by
              intro prefixed
              exact notPrefixLeft (List.cons_prefix_cons.mpr ⟨rfl, prefixed⟩)
            have innerRight : ¬ (a :: tailRight) <+: (a :: tailLeft) := by
              intro prefixed
              exact notPrefixRight (List.cons_prefix_cons.mpr ⟨rfl, prefixed⟩)
            obtain ⟨separator, common, nextLeft, nextRight, tailL, tailR,
              leftEq, rightEq, distinct⟩ :=
              exists_separatesAt (first := a) (by simp) (by simp) innerLeft
                innerRight
            exact ⟨separator, y :: common, nextLeft, nextRight, tailL, tailR,
              by simp [leftEq], by simp [rightEq], distinct⟩
          · exact ⟨y, [], a, b, tailLeft, tailRight, by simp, by simp, equal⟩

/-! ## Outside connector germs

`def:typeA-continuation-classes`' germ is `Γ = (x₀,…,x_g)` with `x₀ = h` the
outside end of the completion port `⃗e = (w,h)`, `x_g = ent_X(P)` the first-entry
receiver, and `x₁,…,x_{g-1} ∉ X`.  The germ is recorded here *rooted at `w`*:
the manuscript's root incidence at the separator is the port edge `wh` when the
separator is `h` and the last edge of the common prefix otherwise, and rooting
the germ at `w` makes those one case.  Nothing else changes: the port edge is
the germ's own first edge, which is the completion port. -/

variable {object : FiniteObject.{u}}

/-- **A rooted outside connector germ through the completion port `⃗e = (w,h)`.**
The list is `w, h, x₁, …, x_g`: the receiver, the port's outside end, the
outside connector, and the first-entry receiver in the support. -/
structure RootedGerm (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (receiver outside : object.Vertex) where
  /-- `w, h, x₁, …, x_g`. -/
  path : List object.Vertex
  /-- It is a walk of the object. -/
  chain : path.IsChain object.graph.Adj
  /-- It is simple. -/
  nodup : path.Nodup
  /-- It is rooted at the receiver `w`. -/
  rooted : path.head? = some receiver
  /-- Its first step is the completion port `wh`. -/
  issued : path.tail.head? = some outside
  /-- `ent_X(P)`, the first-entry receiver the germ lands on. -/
  terminal : object.Vertex
  /-- The germ ends there. -/
  terminal_last : path.getLast? = some terminal
  /-- and it is in the support. -/
  terminal_inside : terminal ∈ support
  /-- `x₁,…,x_{g-1} ∉ X`: after the root the germ meets the support only at its
  first entry. -/
  interior : ∀ vertex ∈ path.tail, vertex ∈ support → vertex = terminal

namespace RootedGerm

variable {support : Finset object.Vertex} {receiver outside : object.Vertex}

/-- The germ's list is `w :: h :: …`, so it is never empty. -/
theorem path_ne_nil (germ : RootedGerm object support receiver outside) :
    germ.path ≠ [] := by
  intro empty
  have root := germ.rooted
  rw [empty] at root
  simp at root

/-- The first entry is on the germ's tail: it is the last entry of a list whose
head is the receiver and whose tail is nonempty. -/
theorem terminal_mem_tail (germ : RootedGerm object support receiver outside) :
    germ.terminal ∈ germ.path.tail := by
  match found : germ.path, germ.rooted, germ.issued with
  | [], root, _ => simp at root
  | [_], _, issue => simp at issue
  | first :: second :: rest, _, _ =>
      have last : (second :: rest).getLast? = some germ.terminal := by
        have := germ.terminal_last
        rw [found] at this
        simpa using this
      obtain ⟨front, split⟩ := List.getLast?_eq_some_iff.mp last
      simp [split]

/-- **Neither germ of a separating pair is a prefix of the other.**  A proper
prefix would put its own first entry strictly inside the longer germ, where the
longer germ's interior clause forbids the support -- unless the two first
entries coincide, which simplicity of the longer germ forbids. -/
theorem not_isPrefix_of_ne {left right : RootedGerm object support receiver outside}
    (different : left.path ≠ right.path) : ¬ left.path <+: right.path := by
  rintro ⟨rest, split⟩
  have restNonempty : rest ≠ [] := by
    intro empty
    exact different (by simp [← split, empty])
  -- The shorter germ's first entry sits on the longer germ's tail.
  have member : left.terminal ∈ right.path.tail := by
    have tailSplit : right.path.tail = left.path.tail ++ rest := by
      match found : left.path, left.rooted with
      | [], root => simp at root
      | first :: restLeft, _ => simp [← split, found]
    rw [tailSplit]
    exact List.mem_append_left _ left.terminal_mem_tail
  have identified : left.terminal = right.terminal :=
    right.interior left.terminal member left.terminal_inside
  -- but the longer germ ends strictly later, and it is simple.
  obtain ⟨front, frontSplit⟩ := List.getLast?_eq_some_iff.mp right.terminal_last
  obtain ⟨leftFront, leftSplit⟩ := List.getLast?_eq_some_iff.mp left.terminal_last
  have restLast : rest.getLast? = right.path.getLast? := by
    rw [← split]
    exact (List.getLast?_append_of_ne_nil _ restNonempty).symm
  obtain ⟨restFront, restSplit⟩ :=
    List.getLast?_eq_some_iff.mp (restLast.trans right.terminal_last)
  have nodup : (left.path ++ rest).Nodup := by rw [split]; exact right.nodup
  have disjoint := (List.nodup_append.mp nodup).2.2
  refine disjoint left.terminal ?_ left.terminal ?_ rfl
  · rw [leftSplit]; simp
  · rw [restSplit, identified]; simp

end RootedGerm

/-! ## Separation at a vertex, and the three incidences it uses -/

/-- **Two germs through one completion port, separating at a vertex.**

`def:typeA-continuation-classes`' *"they separate at `z`"*: the two germs have
the same continuation class up to `z`, and their next incidences after `z` are
distinct.  *Same continuation class up to `z`* is three conjuncts and all three
are carried here — `z` occurs in both germs and they have the same ordered
prefix from `h` to `z`, which the two decompositions below exhibit (and exhibit
as maximal, so `z` is the pair's first separator), **and the two coordinates
have the same image in the relevant boundary-degree fibre**, which is the last
carried by G itself.

Stated about G, that third conjunct is decided: the two coordinates' readings
on `S_z` are G's readings of `S_z`, which keep every labelled incidence and so
lie in one boundary-degree fibre.  The former free `leftReading` /
`rightReading` fields (arbitrary pieces that nothing built from G) are removed.
`S_z` is the manuscript's own *"finite connected support consisting of the
common prefix from `h` to `z`, the two connector tails from `z` to their
first-entry receivers, the two receiver-entry channels in `X`, the completion
port boundary datum, and the declared supports of the two response
coordinates"*, presented through the framework's existing support-to-atom
construction. -/
structure Separation (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (receiver outside : object.Vertex) where
  /-- The first of the two declared coordinates' germs. -/
  left : RootedGerm object support receiver outside
  /-- The second. -/
  right : RootedGerm object support receiver outside
  /-- The common ordered prefix, up to but not including the separator. -/
  common : List object.Vertex
  /-- `z`. -/
  separator : object.Vertex
  /-- The next incidence the first germ uses after `z`. -/
  nextLeft : object.Vertex
  /-- The next incidence the second germ uses after `z`. -/
  nextRight : object.Vertex
  /-- What the first germ does afterwards. -/
  tailLeft : List object.Vertex
  /-- What the second germ does afterwards. -/
  tailRight : List object.Vertex
  /-- The first germ's decomposition. -/
  leftEq : left.path = common ++ separator :: nextLeft :: tailLeft
  /-- The second germ's. -/
  rightEq : right.path = common ++ separator :: nextRight :: tailRight
  /-- The two next incidences are distinct: this is what *separating* means. -/
  distinct : nextLeft ≠ nextRight
  /-- `S_z`, the switch support of `def:typeA-continuation-classes`. -/
  switchSupport : Finset object.Vertex
  /-- `S_z` carries the common prefix, the separator and the first connector
  tail: the germ runs inside it. -/
  leftGerm_subset : ∀ vertex ∈ left.path, vertex ∈ switchSupport
  /-- and the second germ. -/
  rightGerm_subset : ∀ vertex ∈ right.path, vertex ∈ switchSupport
  /-- *"the finite **connected** support"*. -/
  switchConnected :
    Graph.SupportComponents.Connected.ConnectedOn object switchSupport
  /-- `S_z` is proper: the manuscript's `Z = G` case is exit `(6)`, never `S_z`
  itself. -/
  switchProper : ∃ vertex, vertex ∉ switchSupport

namespace Separation

variable {support : Finset object.Vertex} {receiver outside : object.Vertex}
variable (separation : Separation object support receiver outside)

/-- `S_z` as a proper boundaried atom of the ambient object.  Nothing is
rebuilt: this is the framework's own support-to-atom construction. -/
noncomputable def atom : Graph.ProperBoundariedAtom object :=
  Graph.Strategy.InterfaceReplacement.SupportAtom.properAtom object
    separation.switchSupport separation.switchConnected separation.switchProper

/-- The profile certificate generated for `S_z`.  The framework computes it
from the atom; its constructor is private, so this is a registration and not a
guess. -/
noncomputable def certificate :
    Graph.BoundariedAtomProfileCertificate separation.atom :=
  Graph.deriveBoundariedAtomProfile separation.atom

/-- The labelled interface `S_z` presents its declared readings on. -/
noncomputable def interface : Graph.Boundary.{u} :=
  separation.atom.decomposition.interface

/-- **The common prefix is never empty.**  Both germs are rooted at `w` and
step first to `h`, so an empty common prefix would make the two next incidences
both equal to `h`. -/
theorem common_ne_nil : separation.common ≠ [] := by
  intro empty
  have leftPath := separation.leftEq
  have rightPath := separation.rightEq
  rw [empty, List.nil_append] at leftPath rightPath
  have leftNext : separation.nextLeft = outside := by
    have := separation.left.issued
    rw [leftPath] at this
    simpa using this
  have rightNext : separation.nextRight = outside := by
    have := separation.right.issued
    rw [rightPath] at this
    simpa using this
  exact separation.distinct (leftNext.trans rightNext.symm)

/-- **The root incidence at `z`.**  The last vertex of the common prefix: the
receiver `w` itself when the separator is the port's outside end `h`, and the
previous vertex of the shared prefix otherwise.  These are the manuscript's two
cases, and rooting the germ at `w` makes them one. -/
noncomputable def root : object.Vertex :=
  separation.common.getLast separation.common_ne_nil

theorem root_mem_common : separation.root ∈ separation.common :=
  List.getLast_mem separation.common_ne_nil

theorem common_getLast? : separation.common.getLast? = some separation.root :=
  List.getLast?_eq_some_getLast separation.common_ne_nil

/-- The root incidence is an edge at `z`. -/
theorem root_adj : object.graph.Adj separation.root separation.separator := by
  have chain := separation.left.chain
  rw [separation.leftEq] at chain
  obtain ⟨_, _, joint⟩ := List.isChain_append.mp chain
  exact joint separation.root separation.common_getLast? separation.separator
    (by simp)

/-- The first germ's next incidence is an edge at `z`. -/
theorem nextLeft_adj :
    object.graph.Adj separation.separator separation.nextLeft := by
  have chain := separation.left.chain
  rw [separation.leftEq] at chain
  obtain ⟨_, rest, _⟩ := List.isChain_append.mp chain
  exact (List.isChain_cons.mp rest).1 separation.nextLeft (by simp)

/-- The second germ's next incidence is an edge at `z`. -/
theorem nextRight_adj :
    object.graph.Adj separation.separator separation.nextRight := by
  have chain := separation.right.chain
  rw [separation.rightEq] at chain
  obtain ⟨_, rest, _⟩ := List.isChain_append.mp chain
  exact (List.isChain_cons.mp rest).1 separation.nextRight (by simp)

/-- The root incidence is not the first germ's next incidence: one lies in the
common prefix, the other after it, and the germ is simple. -/
theorem root_ne_nextLeft : separation.root ≠ separation.nextLeft := by
  have nodup := separation.left.nodup
  rw [separation.leftEq] at nodup
  exact fun equal =>
    (List.nodup_append.mp nodup).2.2 separation.root separation.root_mem_common
      separation.nextLeft (by simp) equal

/-- and not the second germ's. -/
theorem root_ne_nextRight : separation.root ≠ separation.nextRight := by
  have nodup := separation.right.nodup
  rw [separation.rightEq] at nodup
  exact fun equal =>
    (List.nodup_append.mp nodup).2.2 separation.root separation.root_mem_common
      separation.nextRight (by simp) equal

/-- **The three incidences `z` uses.**  `def:typeA-continuation-classes`' switch
support meets `z` in the root incidence and the two separated next incidences,
and they are pairwise distinct. -/
noncomputable def usedIncidences : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact {separation.root, separation.nextLeft, separation.nextRight}

theorem card_usedIncidences : separation.usedIncidences.card = 3 := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [usedIncidences,
    Finset.card_insert_of_notMem (by
      simp [separation.root_ne_nextLeft, separation.root_ne_nextRight]),
    Finset.card_insert_of_notMem (by simp [separation.distinct]),
    Finset.card_singleton]

theorem usedIncidences_subset : ∀ vertex ∈ separation.usedIncidences,
    object.graph.Adj separation.separator vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro vertex member
  rw [usedIncidences] at member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact separation.root_adj.symm
  · exact separation.nextLeft_adj
  · exact separation.nextRight_adj

/-- **`d_G(z) ≥ 3`.**

*"If `z` is the initial outside vertex `h` of the completion port, the port edge
`wh` is the root incidence at `z`; otherwise the last edge of the common prefix
is the root incidence.  Since the two configurations separate at `z`, they use two
distinct next incidences after `z`.  Hence `d_G(z) ≥ 3`."*

The `3` is the count of incidences the configuration itself uses; it is not a
registered baseline. -/
theorem three_le_degree : 3 ≤ object.degree separation.separator := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have contained : separation.usedIncidences ⊆
      object.graph.neighborFinset separation.separator := by
    intro vertex member
    exact (object.graph.mem_neighborFinset separation.separator vertex).mpr
      (separation.usedIncidences_subset vertex member)
  have counted := Finset.card_le_card contained
  rw [separation.card_usedIncidences] at counted
  exact counted

/-- **The separator uses every one of its incidences exactly when its degree is
`3`.**  This is the manuscript's *"the switch support `S_z` has no unused
ambient incidence at `z`"*. -/
theorem usedIncidences_eq_neighbors
    (cubic : object.degree separation.separator = 3) :
    letI : FinEnum object.Vertex := object.vertices
    letI : DecidableRel object.graph.Adj := object.decideAdj
    separation.usedIncidences =
      object.graph.neighborFinset separation.separator := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : DecidableEq object.Vertex := object.vertices.decEq
  refine Finset.eq_of_subset_of_card_le (fun vertex member =>
    (object.graph.mem_neighborFinset separation.separator vertex).mpr
      (separation.usedIncidences_subset vertex member)) ?_
  have degreeEq :
      (object.graph.neighborFinset separation.separator).card =
        object.degree separation.separator := rfl
  rw [degreeEq, cubic, separation.card_usedIncidences]

/-- **The three incidences `z` uses all lie in `S_z`.**  The root incidence is
in the common prefix and the two next incidences are the germs' own next
entries, so all three are germ vertices, and `S_z` carries both germs. -/
theorem usedIncidences_subset_switchSupport :
    ∀ vertex ∈ separation.usedIncidences, vertex ∈ separation.switchSupport := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro vertex member
  rw [usedIncidences] at member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · refine separation.leftGerm_subset separation.root ?_
    rw [separation.leftEq]
    exact List.mem_append_left _ separation.root_mem_common
  · refine separation.leftGerm_subset separation.nextLeft ?_
    rw [separation.leftEq]
    simp
  · refine separation.rightGerm_subset separation.nextRight ?_
    rw [separation.rightEq]
    simp

/-- **`d_G(z) = 3` leaves `z` off the boundary of `S_z`.**

*"Then the root incidence and the two next incidences used by the separated
configurations are all incidences of `z`.  Consequently the switch support `S_z` has no
unused ambient incidence at `z`."*  This is that sentence, computed on the
framework's own `cutBoundary`: at `d_G(z) = 3` the separator's three incidences
are exactly its neighbours, all three lie in `S_z`, so `z` has no neighbour
outside `S_z` and is an internal vertex of the atom rather than an interface
label.  Nothing is assumed -- the manuscript's *"Assume `d_G(z)=3`"* is the
branch `four_le_degree_of_surviving` splits on, and this is what that branch
carries. -/
theorem separator_notMem_cutBoundary
    (cubic : object.degree separation.separator = 3) :
    separation.separator ∉
      Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
        separation.switchSupport := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro onBoundary
  obtain ⟨_inside, neighbour, adjacent, outsideSupport⟩ :=
    (Graph.Strategy.InterfaceReplacement.SupportAtom.mem_cutBoundary_iff object
      separation.switchSupport separation.separator).1 onBoundary
  refine outsideSupport (separation.usedIncidences_subset_switchSupport
    neighbour ?_)
  rw [separation.usedIncidences_eq_neighbors cubic]
  exact (object.graph.mem_neighborFinset separation.separator neighbour).mpr
    adjacent

/-- **`z` on the boundary of `S_z` has ambient degree at least `4`.**

The converse branch of the previous theorem, and the one the manuscript takes
when its *"Assume `d_G(z)=3`"* fails: an interface label of `S_z` has a
neighbour outside `S_z`, that neighbour is none of the three incidences the
separation uses -- those all lie in `S_z` -- so `z` has a fourth neighbour.
Nothing is assumed on either side: the two theorems are the two arms of one
decidable split on the framework's own `cutBoundary`. -/
theorem four_le_degree_of_mem_cutBoundary
    (onBoundary : separation.separator ∈
      Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
        separation.switchSupport) :
    3 < object.degree separation.separator := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨_inside, neighbour, adjacent, outsideSupport⟩ :=
    (Graph.Strategy.InterfaceReplacement.SupportAtom.mem_cutBoundary_iff object
      separation.switchSupport separation.separator).1 onBoundary
  have unused : neighbour ∉ separation.usedIncidences := fun member =>
    outsideSupport
      (separation.usedIncidences_subset_switchSupport neighbour member)
  have contained : insert neighbour separation.usedIncidences ⊆
      object.graph.neighborFinset separation.separator := by
    intro vertex member
    rcases Finset.mem_insert.1 member with rfl | member
    · exact (object.graph.mem_neighborFinset separation.separator vertex).mpr
        adjacent
    · exact (object.graph.mem_neighborFinset separation.separator vertex).mpr
        (separation.usedIncidences_subset vertex member)
  have counted := Finset.card_le_card contained
  rw [Finset.card_insert_of_notMem unused, separation.card_usedIncidences]
    at counted
  exact counted

end Separation

/-! ## The double-edge switch keeps every degree -/

theorem ncard_insert_sdiff {V : Type*} [Finite V] {s : Set V} {p q : V} (hp : p ∈ s) (hq : q ∉ s) :
    (insert q (s \ {p})).ncard = s.ncard := by
  rw [Set.ncard_insert_of_notMem (fun h => hq h.1), Set.ncard_sdiff_singleton_of_mem hp]
  have : 0 < s.ncard := (Set.ncard_pos (Set.toFinite s)).mpr ⟨p, hp⟩
  omega

/-- **A proper double-edge switch keeps every degree**:
`G − {a a', b b'} + {a b', b a'}` with `a a'`, `b b'` edges of G, the four ends
distinct and neither new edge already present. -/
theorem doubleSwitch_ncard_neighborSet {V : Type*} [Finite V] (G : SimpleGraph V) {a a' b b' : V}
    (hA : G.Adj a a') (hB : G.Adj b b') (hab : a ≠ b) (hab' : a ≠ b')
    (ha'b : a' ≠ b) (ha'b' : a' ≠ b') (na : ¬ G.Adj a b') (nb : ¬ G.Adj b a')
    (v : V) :
    ((G.deleteEdges {s(a, a'), s(b, b')} ⊔
        (SimpleGraph.edge a b' ⊔ SimpleGraph.edge b a')).neighborSet v).ncard =
      (G.neighborSet v).ncard := by
  have haa' : a ≠ a' := hA.ne
  have hbb' : b ≠ b' := hB.ne
  set H := G.deleteEdges {s(a, a'), s(b, b')} ⊔
    (SimpleGraph.edge a b' ⊔ SimpleGraph.edge b a') with hH
  have adj : ∀ x y, H.Adj x y ↔ (G.Adj x y ∧ ¬ (s(x, y) = s(a, a') ∨ s(x, y) = s(b, b'))) ∨
      ((x = a ∧ y = b' ∨ x = b' ∧ y = a) ∨ (x = b ∧ y = a' ∨ x = a' ∧ y = b)) := by
    intro x y
    simp only [hH, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.edge_adj,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | (h | h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h.1)
      · exact Or.inr (Or.inr h.1)
    · rintro (h | (h | h))
      · exact Or.inl h
      · refine Or.inr (Or.inl ⟨h, ?_⟩)
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hab'
        · exact hab'.symm
      · refine Or.inr (Or.inr ⟨h, ?_⟩)
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ha'b.symm
        · exact ha'b
  have swap : ∀ {p q : V}, G.Adj v p → ¬ G.Adj v q →
      H.neighborSet v = insert q (G.neighborSet v \ {p}) →
      (H.neighborSet v).ncard = (G.neighborSet v).ncard := by
    intro p q hp hq eq
    rw [eq]
    exact ncard_insert_sdiff hp hq
  by_cases va : v = a
  · subst va
    refine swap hA na ?_
    ext w
    simp only [SimpleGraph.mem_neighborSet, adj, Set.mem_insert_iff, Set.mem_diff,
      Set.mem_singleton_iff, Sym2.eq_iff]
    simp only [ne_eq, haa', haa'.symm, hab, hab.symm, hab', hab'.symm, ha'b, ha'b.symm,
      ha'b', ha'b'.symm, hbb', hbb'.symm, true_and, false_and, and_false, false_or,
      or_false, and_true, not_false_eq_true, not_or]
    tauto
  by_cases va' : v = a'
  · subst va'
    refine swap hA.symm (fun h => nb h.symm) ?_
    ext w
    simp only [SimpleGraph.mem_neighborSet, adj, Set.mem_insert_iff, Set.mem_diff,
      Set.mem_singleton_iff, Sym2.eq_iff]
    simp only [ne_eq, haa', haa'.symm, hab, hab.symm, hab', hab'.symm, ha'b, ha'b.symm,
      ha'b', ha'b'.symm, hbb', hbb'.symm, true_and, false_and, and_false, false_or,
      or_false, and_true, not_false_eq_true, not_or]
    tauto
  by_cases vb : v = b
  · subst vb
    refine swap hB nb ?_
    ext w
    simp only [SimpleGraph.mem_neighborSet, adj, Set.mem_insert_iff, Set.mem_diff,
      Set.mem_singleton_iff, Sym2.eq_iff]
    simp only [ne_eq, haa', haa'.symm, hab, hab.symm, hab', hab'.symm, ha'b, ha'b.symm,
      ha'b', ha'b'.symm, hbb', hbb'.symm, true_and, false_and, and_false, false_or,
      or_false, and_true, not_false_eq_true, not_or]
    tauto
  by_cases vb' : v = b'
  · subst vb'
    refine swap hB.symm (fun h => na h.symm) ?_
    ext w
    simp only [SimpleGraph.mem_neighborSet, adj, Set.mem_insert_iff, Set.mem_diff,
      Set.mem_singleton_iff, Sym2.eq_iff]
    simp only [ne_eq, haa', haa'.symm, hab, hab.symm, hab', hab'.symm, ha'b, ha'b.symm,
      ha'b', ha'b'.symm, hbb', hbb'.symm, true_and, false_and, and_false, false_or,
      or_false, and_true, not_false_eq_true, not_or]
    tauto
  congr 1
  ext w
  simp only [SimpleGraph.mem_neighborSet, adj, Sym2.eq_iff]
  simp only [va, va', vb, vb', false_and, and_false, or_false, false_or, not_false_eq_true,
    and_true, not_or]

/-! ## The forced structure of an accepted cycle of a double-edge switch -/

namespace DoubleSwitch

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A graph with no accepted cycle (the target-avoidance of G, read on its
simple graph). -/
def NoAcceptedCycle (G : SimpleGraph V) (L : ℕ → Prop) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → ¬ L c.length

/-- Split a walk at one of its edges. -/
theorem split_at_edge {K : SimpleGraph V} {u v x y : V} (p : K.Walk u v) (h : K.Adj x y)
    (mem : s(x, y) ∈ p.edges) :
    (∃ (r₁ : K.Walk u x) (r₂ : K.Walk y v), p = r₁.append (Walk.cons h r₂)) ∨
      (∃ (r₁ : K.Walk u y) (r₂ : K.Walk x v), p = r₁.append (Walk.cons h.symm r₂)) := by
  rcases (Walk.isSubwalk_toWalk_iff_mem_edges h).mpr mem with ⟨r₁, r₂, eq⟩ | ⟨r₁, r₂, eq⟩
  · exact Or.inl ⟨r₁, r₂, by rw [eq]; exact (Walk.append_assoc _ _ _).symm⟩
  · exact Or.inr ⟨r₁, r₂, by rw [eq]; exact (Walk.append_assoc _ _ _).symm⟩

/-- **Forced structure of a proper double-edge switch.**  -/
theorem doubleSwitch_forced {L : ℕ → Prop} {a a' b b' : V}
    (S : Set (Sym2 V)) (hS : S = {s(a, a'), s(b, b')})
    (H : SimpleGraph V)
    (hH : H = G.deleteEdges S ⊔ (SimpleGraph.edge a b' ⊔ SimpleGraph.edge b a'))
    (hA : G.Adj a a') (hB : G.Adj b b') (hab : a ≠ b) (hab' : a ≠ b')
    (ha'b : a' ≠ b) (ha'b' : a' ≠ b') (na : ¬ G.Adj a b') (nb : ¬ G.Adj b a')
    (noG : NoAcceptedCycle G L)
    {w : H.Walk a b'}
    (wPath : w.IsPath) (fresh : s(a, b') ∉ w.edges) (accepted : L (w.length + 1)) :
    (∃ P : (G.deleteEdges S).Walk a b', P.IsPath ∧ L (P.length + 1)) ∨
      ∃ (P₁ : (G.deleteEdges S).Walk a a') (P₂ : (G.deleteEdges S).Walk b b'),
        P₁.IsPath ∧ P₂.IsPath ∧ List.Disjoint P₁.support P₂.support ∧
          L (P₁.length + P₂.length + 2) := by
  classical
  have old : ∀ e ∈ H.edgeSet, e ≠ s(a, b') → e ≠ s(b, a') →
      e ∈ (G.deleteEdges S).edgeSet := by
    intro e he n1 n2
    rw [hH, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_sup] at he
    rcases he with he | he | he
    · exact he
    · rw [SimpleGraph.edgeSet_edge_of_ne hab'] at he
      exact absurd (Set.mem_singleton_iff.mp he) n1
    · rw [SimpleGraph.edgeSet_edge_of_ne ha'b.symm] at he
      exact absurd (Set.mem_singleton_iff.mp he) n2
  have gOf : ∀ e ∈ (G.deleteEdges S).edgeSet, e ∈ G.edgeSet :=
    fun e he => SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le S) he
  have notAA : s(a, a') ∉ (G.deleteEdges S).edgeSet := by
    rw [SimpleGraph.edgeSet_deleteEdges]; exact fun h => h.2 (by simp [hS])
  have notBB : s(b, b') ∉ (G.deleteEdges S).edgeSet := by
    rw [SimpleGraph.edgeSet_deleteEdges]; exact fun h => h.2 (by simp [hS])
  by_cases other : s(b, a') ∈ w.edges
  · have hH' : H.Adj b a' := by
      rw [hH]; refine Or.inr (Or.inr ?_)
      simp [SimpleGraph.edge_adj, ha'b.symm]
    have nodup := (Walk.isPath_def _).mp wPath
    have edgesNodup := wPath.isTrail.edges_nodup
    rcases split_at_edge w hH' other with ⟨r₁, r₂, eq⟩ | ⟨r₁, r₂, eq⟩
    · -- crossed: a ⇝ b, b a', a' ⇝ b' closes a cycle of G
      exfalso
      subst eq
      simp only [Walk.edges_append, Walk.edges_cons] at edgesNodup fresh
      have e₁ : ∀ e ∈ r₁.edges, e ∈ (G.deleteEdges S).edgeSet := fun e he =>
        old e (Walk.edges_subset_edgeSet r₁ he) (fun h => fresh (by simp [← h, he]))
          (fun h => by
            rw [h] at he
            exact (List.nodup_append.mp edgesNodup).2.2 _ he _ (by simp) rfl)
      have e₂ : ∀ e ∈ r₂.edges, e ∈ (G.deleteEdges S).edgeSet := fun e he =>
        old e (Walk.edges_subset_edgeSet r₂ he) (fun h => fresh (by simp [← h, he]))
          (fun h => by
            rw [h] at he
            exact (List.nodup_cons.mp (List.nodup_append.mp edgesNodup).2.1).1 he)
      let q₁ := (r₁.transfer (G.deleteEdges S) e₁).transfer G
        (fun e he => gOf e (by rw [Walk.edges_transfer] at he; exact e₁ e he))
      let q₂ := (r₂.transfer (G.deleteEdges S) e₂).transfer G
        (fun e he => gOf e (by rw [Walk.edges_transfer] at he; exact e₂ e he))
      let Q : G.Walk a a' := q₁.append (Walk.cons hB q₂.reverse)
      have supp : Q.support = r₁.support ++ r₂.support.reverse := by
        simp [Q, q₁, q₂, Walk.support_append, Walk.support_transfer, Walk.support_reverse]
      have wsupp : (r₁.append (Walk.cons hH' r₂)).support = r₁.support ++ r₂.support := by
        rw [Walk.support_append, Walk.support_cons, List.tail_cons]
      rw [wsupp] at nodup
      have qPath : Q.IsPath := by
        rw [Walk.isPath_def, supp]
        refine List.nodup_append.mpr ⟨(List.nodup_append.mp nodup).1,
          List.nodup_reverse.mpr (List.nodup_append.mp nodup).2.1, ?_⟩
        intro x hx y hy
        exact (List.nodup_append.mp nodup).2.2 x hx y (List.mem_reverse.mp hy)
      have qEdges : s(a', a) ∉ Q.edges := by
        simp only [Q, Walk.edges_append, Walk.edges_cons, Walk.edges_reverse, q₁, q₂,
          Walk.edges_transfer, List.mem_append, List.mem_cons, List.mem_reverse, not_or]
        refine ⟨fun h => notAA (by rw [Sym2.eq_swap]; exact e₁ _ h), ?_,
          fun h => notAA (by rw [Sym2.eq_swap]; exact e₂ _ h)⟩
        intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          first
            | exact hab h1 | exact hab h1.symm | exact ha'b h1 | exact ha'b h1.symm
            | exact hab h2 | exact hab h2.symm | exact ha'b h2 | exact ha'b h2.symm
      have cyc := (Walk.cons_isCycle_iff Q hA.symm).mpr ⟨qPath, qEdges⟩
      refine noG a' _ cyc ?_
      convert accepted using 1
      simp [Q, q₁, q₂, Walk.length_append, Walk.length_transfer]
      try omega
    · -- parallel: a ⇝ a', a' b, b ⇝ b'
      right
      subst eq
      simp only [Walk.edges_append, Walk.edges_cons] at edgesNodup fresh
      have e₁ : ∀ e ∈ r₁.edges, e ∈ (G.deleteEdges S).edgeSet := fun e he =>
        old e (Walk.edges_subset_edgeSet r₁ he) (fun h => fresh (by simp [← h, he]))
          (fun h => by
            rw [h] at he
            exact (List.nodup_append.mp edgesNodup).2.2 _ he _ (by simp [Sym2.eq_swap]) rfl)
      have e₂ : ∀ e ∈ r₂.edges, e ∈ (G.deleteEdges S).edgeSet := fun e he =>
        old e (Walk.edges_subset_edgeSet r₂ he) (fun h => fresh (by simp [← h, he]))
          (fun h => by
            rw [h] at he
            exact (List.nodup_cons.mp (List.nodup_append.mp edgesNodup).2.1).1
              (by rw [Sym2.eq_swap]; exact he))
      have wsupp : (r₁.append (Walk.cons hH'.symm r₂)).support = r₁.support ++ r₂.support := by
        rw [Walk.support_append, Walk.support_cons, List.tail_cons]
      rw [wsupp] at nodup
      refine ⟨r₁.transfer _ e₁, r₂.transfer _ e₂, ?_, ?_, ?_, ?_⟩
      · rw [Walk.isPath_def, Walk.support_transfer]; exact (List.nodup_append.mp nodup).1
      · rw [Walk.isPath_def, Walk.support_transfer]; exact (List.nodup_append.mp nodup).2.1
      · rw [Walk.support_transfer, Walk.support_transfer]
        intro x hx hy
        exact (List.nodup_append.mp nodup).2.2 x hx x hy rfl
      · convert accepted using 1
        simp [Walk.length_append, Walk.length_transfer]
        try omega
  · left
    have e : ∀ e ∈ w.edges, e ∈ (G.deleteEdges S).edgeSet := fun e he =>
      old e (Walk.edges_subset_edgeSet w he) (fun h => fresh (h ▸ he))
        (fun h => other (h ▸ he))
    exact ⟨w.transfer _ e, wPath.transfer e, by rw [Walk.length_transfer]; exact accepted⟩


/-- A closing edge absent from a path of G closes a cycle of G. -/
theorem closing_edge_rejected {L : ℕ → Prop} (noG : NoAcceptedCycle G L) {u v : V}
    (h : G.Adj u v) (P : G.Walk v u) (pPath : P.IsPath) (fresh : s(u, v) ∉ P.edges) :
    ¬ L (P.length + 1) := by
  have cyc := (Walk.cons_isCycle_iff P h).mpr ⟨pPath, fresh⟩
  simpa using noG u _ cyc

/-- **The apex cycle**: a path `a ⇝ b'` of G avoiding `x` and `b`, with the
edges `x a`, `x b`, `b b'`, closes a cycle of length `|P| + 3`. -/
theorem apex_cycle_rejected {L : ℕ → Prop} (noG : NoAcceptedCycle G L) {x a b b' : V}
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hbb' : G.Adj b b') (hab : a ≠ b)
    (P : G.Walk a b') (pPath : P.IsPath) (xNot : x ∉ P.support) (bNot : b ∉ P.support) :
    ¬ L (P.length + 3) := by
  have hxb' : x ≠ b := hxb.ne
  let Q : G.Walk a x := P.append (Walk.cons hbb'.symm (Walk.cons hxb.symm Walk.nil))
  have qPath : Q.IsPath := by
    rw [Walk.isPath_def]
    simp only [Q, Walk.support_append, Walk.support_cons, Walk.support_nil, List.tail_cons]
    refine List.nodup_append.mpr ⟨(Walk.isPath_def _).mp pPath, ?_, ?_⟩
    · simp [hxb'.symm]
    · intro y hy z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact fun e => bNot (e ▸ hy)
      · exact fun e => xNot (e ▸ hy)
  have qFresh : s(x, a) ∉ Q.edges := by
    simp only [Q, Walk.edges_append, Walk.edges_cons, Walk.edges_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨fun h => xNot (P.fst_mem_support_of_mem_edges h), ?_, ?_⟩
    · intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact xNot (h1 ▸ P.end_mem_support)
      · exact hxb' h1
    · intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hxb' h1
      · exact hab h2
  have cyc := (Walk.cons_isCycle_iff Q hxa).mpr ⟨qPath, qFresh⟩
  have len : (Walk.cons hxa Q).length = P.length + 3 := by
    simp [Q, Walk.length_append]
  exact fun accepted => noG x _ cyc (len ▸ accepted)

/-- The least value of a measure on a nonempty class. -/
theorem exists_min_of_exists {α : Sort*} (f : α → ℕ) {Q : α → Prop} (h : ∃ x, Q x) :
    ∃ x, Q x ∧ ∀ y, Q y → f x ≤ f y := by
  classical
  have ex : ∃ n, ∃ x, Q x ∧ f x = n := by
    obtain ⟨x, hx⟩ := h
    exact ⟨f x, x, hx, rfl⟩
  obtain ⟨x, hx, hxn⟩ := Nat.find_spec ex
  refine ⟨x, hx, fun y hy => ?_⟩
  rw [hxn]
  exact Nat.find_min' ex ⟨y, hy, rfl⟩


/-- **Forced structure of an accepted cycle of a proper double-edge switch**
at a graph with no accepted cycle: one exchanged edge closes a forced path of
`G − S`, or the cycle uses both exchanged edges in parallel orientation and
`G − S` has disjoint paths `a ⇝ a'`, `b ⇝ b'`.  The crossed orientation closes
an accepted cycle of G and is excluded. -/
theorem doubleSwitch_cycle_forced {L : ℕ → Prop} {a a' b b' : V}
    (hA : G.Adj a a') (hB : G.Adj b b') (hab : a ≠ b) (hab' : a ≠ b')
    (ha'b : a' ≠ b) (ha'b' : a' ≠ b') (na : ¬ G.Adj a b') (nb : ¬ G.Adj b a')
    (noG : NoAcceptedCycle G L) {v : V}
    (c : (G.deleteEdges {s(a, a'), s(b, b')} ⊔
      (SimpleGraph.edge a b' ⊔ SimpleGraph.edge b a')).Walk v v)
    (cyc : c.IsCycle) (accepted : L c.length) :
    (∃ P : (G.deleteEdges {s(a, a'), s(b, b')}).Walk a b', P.IsPath ∧ L (P.length + 1)) ∨
    (∃ P : (G.deleteEdges {s(a, a'), s(b, b')}).Walk b a', P.IsPath ∧ L (P.length + 1)) ∨
    ∃ (P₁ : (G.deleteEdges {s(a, a'), s(b, b')}).Walk a a')
      (P₂ : (G.deleteEdges {s(a, a'), s(b, b')}).Walk b b'),
      P₁.IsPath ∧ P₂.IsPath ∧ List.Disjoint P₁.support P₂.support ∧
        L (P₁.length + P₂.length + 2) := by
  classical
  have uses : s(a, b') ∈ c.edges ∨ s(b, a') ∈ c.edges := by
    by_contra none
    push Not at none
    have inG : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
      intro e he
      have h := c.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_sup] at h
      rcases h with h | h | h
      · exact SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le _) h
      · rw [SimpleGraph.edgeSet_edge_of_ne hab'] at h
        exact absurd (Set.mem_singleton_iff.mp h ▸ he) none.1
      · rw [SimpleGraph.edgeSet_edge_of_ne ha'b.symm] at h
        exact absurd (Set.mem_singleton_iff.mp h ▸ he) none.2
    exact noG v (c.transfer G inG) (cyc.transfer inG)
      (by rw [Walk.length_transfer]; exact accepted)
  rcases uses with first | second
  · obtain ⟨w, wPath, fresh, len⟩ :=
      Hypostructure.Graph.ReadingSpectrum.EdgeContext.cycle_through_edge c cyc first
    rcases doubleSwitch_forced _ rfl _ rfl hA hB hab hab' ha'b ha'b' na nb noG wPath fresh
        (len ▸ accepted) with one | ⟨P₁, P₂, p₁, p₂, disj, acc⟩
    · exact Or.inl one
    · exact Or.inr (Or.inr ⟨P₁, P₂, p₁, p₂, disj, acc⟩)
  · obtain ⟨w, wPath, fresh, len⟩ :=
      Hypostructure.Graph.ReadingSpectrum.EdgeContext.cycle_through_edge c cyc second
    have hS : ({s(a, a'), s(b, b')} : Set (Sym2 V)) = {s(b, b'), s(a, a')} :=
      Set.pair_comm _ _
    have hH : G.deleteEdges {s(a, a'), s(b, b')} ⊔
        (SimpleGraph.edge a b' ⊔ SimpleGraph.edge b a') =
      G.deleteEdges {s(a, a'), s(b, b')} ⊔
        (SimpleGraph.edge b a' ⊔ SimpleGraph.edge a b') := by
      rw [sup_comm (SimpleGraph.edge a b')]
    rcases doubleSwitch_forced (a := b) (a' := b') (b := a) (b' := a')
        _ hS _ hH hB hA hab.symm ha'b.symm hab'.symm ha'b'.symm nb na noG wPath fresh
        (len ▸ accepted) with one | ⟨P₂, P₁, p₂, p₁, disj, acc⟩
    · exact Or.inr (Or.inl one)
    · refine Or.inr (Or.inr ⟨P₁, P₂, p₁, p₂, disj.symm, ?_⟩)
      rw [Nat.add_comm P₁.length]
      exact acc

/-- **The canonical least element**: shortest in a measure `f`, and among the
shortest the lexicographically least in a code (the class is finite at each
measure). -/
theorem exists_least {α : Type*} (f : α → ℕ) (code : α → List ℕ)
    (fin : ∀ n, {x | f x ≤ n}.Finite) {Q : α → Prop} (h : ∃ x, Q x) :
    ∃ x, Q x ∧ (∀ y, Q y → f x ≤ f y) ∧
      ∀ y, Q y → f y = f x → code x ≤ code y := by
  classical
  obtain ⟨x₀, hx₀, least⟩ := exists_min_of_exists f h
  have finite : {y | Q y ∧ f y = f x₀}.Finite :=
    (fin (f x₀)).subset fun y hy => le_of_eq hy.2
  obtain ⟨x, hx, hmin⟩ := finite.toFinset.exists_min_image code
    ⟨x₀, by simp [hx₀]⟩
  rw [Set.Finite.mem_toFinset] at hx
  refine ⟨x, hx.1, fun y hy => hx.2 ▸ least y hy, fun y hy hyx => ?_⟩
  exact hmin y (by rw [Set.Finite.mem_toFinset]; exact ⟨hy, hyx.trans hx.2⟩)

/-- Walks of bounded length form a finite set. -/
theorem walk_length_finite {V : Type*} [Fintype V] {K : SimpleGraph V} (u v : V) (n : ℕ) :
    {p : K.Walk u v | p.length ≤ n}.Finite := by
  classical
  exact (Set.toFinite {p : K.Walk u v | p.length < n + 1}).subset
    fun p hp => Nat.lt_succ_of_le hp

/-- Pairs of walks of bounded total length form a finite set. -/
theorem walkPair_length_finite {V : Type*} [Fintype V] {K : SimpleGraph V}
    (u v u' v' : V) (n : ℕ) :
    {pair : K.Walk u v × K.Walk u' v' | pair.1.length + pair.2.length ≤ n}.Finite :=
  ((walk_length_finite u v n).prod (walk_length_finite u' v' n)).subset
    fun pair hp => ⟨le_trans (Nat.le_add_right _ _) hp, le_trans (Nat.le_add_left _ _) hp⟩

end DoubleSwitch

/-- **G's vertex order**: the rank of a vertex in G's fixed enumeration
`object.vertices`.  Walks are compared by the lexicographic order of their
support lists read through it. -/
noncomputable def vertexRank (object : FiniteObject.{u}) (vertex : object.Vertex) : Nat :=
  letI : FinEnum object.Vertex := object.vertices
  ((FinEnum.equiv vertex : Fin (FinEnum.card object.Vertex)) : Nat)

/-! ## The switch at the separator, constructed from G, and absorption

`def:typeA-continuation-classes`: `z` is *absorbed* when the response
identification on the switch support `S_z` is target-defective,
target-complete on a nontrivial response quotient, or target-complete only
after adjoining a larger connected support.

The identification of the two separated response coordinates is realized on G
(G repair), at the separator itself.  The two configurations share the prefix
up to `z` and leave it through distinct next incidences `a = nextLeft`,
`b = nextRight`; each continues along its germ to `a⁺`, `b⁺` (the heads of the
two tails).  **The switch at `z`** exchanges the two continuations:
`G − {a a⁺, b b⁺} + {a b⁺, b a⁺}`.  After it, the configuration through `a`
continues as the one through `b` did and conversely — the two continuation
classes at `z` are identified.  All four vertices lie on the germs, hence in
`S_z`, so the switch changes only `S_z`'s own incidences and keeps every degree
of G.  Every choice is fixed by G's germs.  When the exchange is not a proper
double-edge switch (a next incidence is itself the first entry, coinciding
ends, or an exchanged edge already present) the identification is trivial and
the switched graph is G.  Nothing here is supplied by a caller. -/

namespace Separation

variable {support : Finset object.Vertex} {receiver outside : object.Vertex}
variable (separation : Separation object support receiver outside)

/-- `a⁺`: the vertex after `a = nextLeft` on the first germ (the head of its
tail; `a` itself when `a` is already the first entry). -/
noncomputable def leftAfter : object.Vertex :=
  separation.tailLeft.headD separation.nextLeft

/-- `b⁺`: the vertex after `b = nextRight` on the second germ. -/
noncomputable def rightAfter : object.Vertex :=
  separation.tailRight.headD separation.nextRight

/-- The switch at `z` is a proper double-edge switch: both configurations
continue past their next incidence, `a a⁺` and `b b⁺` are edges of G, the
exchanged ends are distinct, and neither exchanged edge `a b⁺`, `b a⁺` is
already an edge of G. -/
def SwitchValid : Prop :=
  separation.tailLeft ≠ [] ∧ separation.tailRight ≠ [] ∧
    object.graph.Adj separation.nextLeft separation.leftAfter ∧
    object.graph.Adj separation.nextRight separation.rightAfter ∧
    separation.nextLeft ≠ separation.rightAfter ∧
    separation.nextRight ≠ separation.leftAfter ∧
    separation.leftAfter ≠ separation.rightAfter ∧
    ¬ object.graph.Adj separation.nextLeft separation.rightAfter ∧
    ¬ object.graph.Adj separation.nextRight separation.leftAfter

/-- **The switched graph at `z`** on G's vertices: the two configurations
exchange their continuations after `a`, `b`. -/
noncomputable def switchedGraph : SimpleGraph object.Vertex := by
  classical
  exact if separation.SwitchValid then
    object.graph.deleteEdges
        {s(separation.nextLeft, separation.leftAfter),
          s(separation.nextRight, separation.rightAfter)} ⊔
      (SimpleGraph.edge separation.nextLeft separation.rightAfter ⊔
        SimpleGraph.edge separation.nextRight separation.leftAfter)
  else object.graph

/-- The switched graph as an object on G's vertices. -/
noncomputable def switched : FiniteObject.{u} :=
  SwitchForcedPaths.spanning object separation.switchedGraph

/-- **The switched piece on `S_z`'s interface**: G's piece at `S_z` with the
switched incidences.  Glued into `G − S_z` it carries the switched graph (all
four switched vertices lie in `S_z`). -/
noncomputable def switchedPiece : Graph.BoundaryPiece
    (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object
      separation.switchSupport) where
  Internal := Graph.Strategy.InterfaceReplacement.SupportAtom.PieceInternal object
    separation.switchSupport
  internalVertices :=
    (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object
      separation.switchSupport).internalVertices
  graph := SimpleGraph.comap
    (Graph.Strategy.InterfaceReplacement.SupportAtom.pieceDecode object
      separation.switchSupport) separation.switchedGraph
  decideAdj := Classical.decRel _

theorem switched_vertexCount :
    separation.switched.vertexCount = object.vertexCount := rfl

/-- **The switch at `z` keeps every degree of G** (a proper double-edge switch,
or G itself). -/
theorem switched_degree (vertex : object.Vertex) :
    separation.switched.degree vertex = object.degree vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  change (SwitchForcedPaths.spanning object separation.switchedGraph).degree
    vertex = object.degree vertex
  rw [SwitchForcedPaths.spanning_degree, FiniteObject.degree_eq_ncard_neighborSet]
  unfold switchedGraph
  split_ifs with valid
  · obtain ⟨_tailL, _tailR, adjL, adjR, hLR, hRL, hAfter, nL, nR⟩ := valid
    exact doubleSwitch_ncard_neighborSet object.graph adjL adjR
      separation.distinct hLR (Ne.symm hRL) hAfter nL nR vertex
  · rfl

/-- **The switch at `z` keeps G's number of edges** (handshake). -/
theorem switched_edgeCount :
    separation.switched.edgeCount = object.edgeCount := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  rw [SwitchForcedPaths.edgeCount_eq_ncard, SwitchForcedPaths.edgeCount_eq_ncard]
  have switchedSum :=
    SwitchForcedPaths.SwapAccounting.sum_dg separation.switchedGraph
  have ownSum := SwitchForcedPaths.SwapAccounting.sum_dg object.graph
  have same : ∑ vertex, SwitchForcedPaths.SwapAccounting.dg
        separation.switchedGraph vertex =
      ∑ vertex, SwitchForcedPaths.SwapAccounting.dg object.graph vertex := by
    refine Finset.sum_congr rfl fun vertex _ => ?_
    have degree := separation.switched_degree vertex
    change (SwitchForcedPaths.spanning object separation.switchedGraph).degree
      vertex = object.degree vertex at degree
    rw [SwitchForcedPaths.spanning_degree,
      FiniteObject.degree_eq_ncard_neighborSet] at degree
    exact degree
  change separation.switchedGraph.edgeSet.ncard = object.graph.edgeSet.ncard
  omega

/-- **The switch at `z` keeps the degree baseline of G.** -/
theorem switched_baseline {k : Nat} (baseline : MinimumDegreeAtLeast k object) :
    MinimumDegreeAtLeast k separation.switched := by
  haveI : Nonempty separation.switched.Vertex := ⟨separation.separator⟩
  show k ≤ separation.switched.minDegree
  refine FiniteObject.le_minDegree_of_forall_le_degree _ k fun vertex => ?_
  rw [separation.switched_degree vertex]
  exact le_trans baseline (object.minDegree_le_degree vertex)

/-- Every edge of the switched graph is an edge of G or one of the two
exchanged edges `a b⁺`, `b a⁺`. -/
theorem switched_edge {e : Sym2 object.Vertex}
    (member : e ∈ separation.switchedGraph.edgeSet) :
    e ∈ object.graph.edgeSet ∨
      e = s(separation.nextLeft, separation.rightAfter) ∨
      e = s(separation.nextRight, separation.leftAfter) := by
  classical
  unfold switchedGraph at member
  split_ifs at member with valid
  · rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_sup] at member
    rcases member with deleted | fresh | fresh
    · exact Or.inl (SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le _) deleted)
    · right; left
      rw [SimpleGraph.edgeSet_edge_of_ne (fun same => valid.2.2.2.2.1 same)] at fresh
      exact fresh
    · right; right
      rw [SimpleGraph.edgeSet_edge_of_ne (fun same => valid.2.2.2.2.2.1 same)] at fresh
      exact fresh
  · exact Or.inl member

/-- **The target-cycle arm: the cycle is forced through an exchanged edge.**
At a target-avoiding G, an accepted cycle of the switched graph uses one of the
two exchanged edges `a b⁺`, `b a⁺`, and the switch at `z` is a proper
double-edge switch: deleting that edge leaves a path of G minus `{a a⁺, b b⁺}`
whose length plus one is accepted (`SwitchForcedPaths`' forced-path
pattern, the `2^j − 1` path at the dyadic target). -/
theorem switched_forced_cycle {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L object)
    (accepted : HasCycleWithLength L separation.switched) :
    separation.SwitchValid ∧
      ∃ c : CycleCertificate separation.switched L,
        ∃ e ∈ c.walk.edges,
          e = s(separation.nextLeft, separation.rightAfter) ∨
            e = s(separation.nextRight, separation.leftAfter) := by
  classical
  obtain ⟨c⟩ := accepted
  have uses : ∃ e ∈ c.walk.edges,
      e = s(separation.nextLeft, separation.rightAfter) ∨
        e = s(separation.nextRight, separation.leftAfter) := by
    by_contra none
    push Not at none
    have hG : ∀ e ∈ c.walk.edges, e ∈ object.graph.edgeSet := by
      intro e he
      rcases separation.switched_edge (c.walk.edges_subset_edgeSet he) with
        old | fresh | fresh
      · exact old
      · exact absurd fresh (none e he).1
      · exact absurd fresh (none e he).2
    exact avoids ⟨⟨c.vertex, c.walk.transfer object.graph hG,
      c.isCycle.transfer hG, by
        convert c.length_ok using 1
        exact SimpleGraph.Walk.length_transfer _ _⟩⟩
  refine ⟨?_, c, uses⟩
  by_contra invalid
  obtain ⟨e, he, fresh⟩ := uses
  have edge := c.walk.edges_subset_edgeSet he
  change e ∈ separation.switchedGraph.edgeSet at edge
  unfold switchedGraph at edge
  rw [if_neg invalid] at edge
  have hG : ∀ e ∈ c.walk.edges, e ∈ object.graph.edgeSet := by
    intro e he
    have edge := c.walk.edges_subset_edgeSet he
    change e ∈ separation.switchedGraph.edgeSet at edge
    unfold switchedGraph at edge
    rw [if_neg invalid] at edge
    exact edge
  exact avoids ⟨⟨c.vertex, c.walk.transfer object.graph hG,
    c.isCycle.transfer hG, by
      convert c.length_ok using 1
      exact SimpleGraph.Walk.length_transfer _ _⟩⟩

/-- The two exchanged edges `a a⁺`, `b b⁺` of the switch at `z`. -/
noncomputable def exchangedEdges : Set (Sym2 object.Vertex) :=
  {s(separation.nextLeft, separation.leftAfter),
    s(separation.nextRight, separation.rightAfter)}

/-- **The forced paths of the target-cycle arm, with their local length
constraints at `z`** (all in `G − {a a⁺, b b⁺}`, each the shortest of its
kind and, among the shortest, the lexicographically least support in G's
vertex order `vertexRank`, so each is a canonical object of G):

* one exchanged edge `a b⁺`: a path `P : a ⇝ b⁺` with `|P| + 1` accepted; if it
  avoids `z` and `b`, the apex cycle `z a P b⁺ b z` of G has length `|P| + 3`,
  not accepted;
* one exchanged edge `b a⁺`: a path `P : b ⇝ a⁺` with `|P| + 1` accepted; if it
  avoids `z` and `a`, `|P| + 3` is not accepted;
* both exchanged edges (parallel orientation): disjoint paths `P₁ : a ⇝ a⁺`,
  `P₂ : b ⇝ b⁺` with `|P₁| + |P₂| + 2` accepted, and the two cycles
  `P₁ + a⁺a`, `P₂ + b⁺b` of G give `|P₁| + 1`, `|P₂| + 1` not accepted.

The crossed orientation of both exchanged edges is not listed: it closes an
accepted cycle of G itself. -/
def ForcedAtSwitch (L : Nat → Prop) : Prop :=
  (∃ P : (object.graph.deleteEdges separation.exchangedEdges).Walk
        separation.nextLeft separation.rightAfter,
      P.IsPath ∧ L (P.length + 1) ∧
      (∀ P' : (object.graph.deleteEdges separation.exchangedEdges).Walk
          separation.nextLeft separation.rightAfter,
        P'.IsPath → L (P'.length + 1) → P.length ≤ P'.length) ∧
      (∀ P' : (object.graph.deleteEdges separation.exchangedEdges).Walk
          separation.nextLeft separation.rightAfter,
        P'.IsPath → L (P'.length + 1) → P'.length = P.length →
        P.support.map (vertexRank object) ≤ P'.support.map (vertexRank object)) ∧
      (separation.separator ∉ P.support → separation.nextRight ∉ P.support →
        ¬ L (P.length + 3))) ∨
    (∃ P : (object.graph.deleteEdges separation.exchangedEdges).Walk
          separation.nextRight separation.leftAfter,
      P.IsPath ∧ L (P.length + 1) ∧
      (∀ P' : (object.graph.deleteEdges separation.exchangedEdges).Walk
          separation.nextRight separation.leftAfter,
        P'.IsPath → L (P'.length + 1) → P.length ≤ P'.length) ∧
      (∀ P' : (object.graph.deleteEdges separation.exchangedEdges).Walk
          separation.nextRight separation.leftAfter,
        P'.IsPath → L (P'.length + 1) → P'.length = P.length →
        P.support.map (vertexRank object) ≤ P'.support.map (vertexRank object)) ∧
      (separation.separator ∉ P.support → separation.nextLeft ∉ P.support →
        ¬ L (P.length + 3))) ∨
    ∃ (P₁ : (object.graph.deleteEdges separation.exchangedEdges).Walk
          separation.nextLeft separation.leftAfter)
      (P₂ : (object.graph.deleteEdges separation.exchangedEdges).Walk
          separation.nextRight separation.rightAfter),
      P₁.IsPath ∧ P₂.IsPath ∧ List.Disjoint P₁.support P₂.support ∧
        L (P₁.length + P₂.length + 2) ∧
        (∀ (Q₁ : (object.graph.deleteEdges separation.exchangedEdges).Walk
              separation.nextLeft separation.leftAfter)
            (Q₂ : (object.graph.deleteEdges separation.exchangedEdges).Walk
              separation.nextRight separation.rightAfter),
          Q₁.IsPath → Q₂.IsPath → List.Disjoint Q₁.support Q₂.support →
          L (Q₁.length + Q₂.length + 2) →
          P₁.length + P₂.length ≤ Q₁.length + Q₂.length) ∧
        (∀ (Q₁ : (object.graph.deleteEdges separation.exchangedEdges).Walk
              separation.nextLeft separation.leftAfter)
            (Q₂ : (object.graph.deleteEdges separation.exchangedEdges).Walk
              separation.nextRight separation.rightAfter),
          Q₁.IsPath → Q₂.IsPath → List.Disjoint Q₁.support Q₂.support →
          L (Q₁.length + Q₂.length + 2) →
          Q₁.length + Q₂.length = P₁.length + P₂.length →
          (P₁.support ++ P₂.support).map (vertexRank object) ≤
            (Q₁.support ++ Q₂.support).map (vertexRank object)) ∧
        ¬ L (P₁.length + 1) ∧ ¬ L (P₂.length + 1)

/-- **The target-cycle arm at G, accounted**: an accepted cycle of the switched
graph at a target-avoiding G forces the canonical (shortest) forced paths of
`ForcedAtSwitch` with their local length constraints; the crossed use of both
exchanged edges would be an accepted cycle of G. -/
theorem switched_forced_paths {L : Nat → Prop}
    (avoids : ¬ HasCycleWithLength L object)
    (accepted : HasCycleWithLength L separation.switched) :
    separation.SwitchValid ∧ separation.ForcedAtSwitch L := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  have valid := (separation.switched_forced_cycle avoids accepted).1
  obtain ⟨tailL, tailR, adjL, adjR, hLR, hRL, hAfter, nL, nR⟩ := valid
  have noG : DoubleSwitch.NoAcceptedCycle object.graph L :=
    fun v c cyc acc => avoids ⟨⟨v, c, cyc, acc⟩⟩
  have graphEq : separation.switchedGraph =
      object.graph.deleteEdges separation.exchangedEdges ⊔
        (SimpleGraph.edge separation.nextLeft separation.rightAfter ⊔
          SimpleGraph.edge separation.nextRight separation.leftAfter) := by
    unfold switchedGraph
    rw [if_pos ⟨tailL, tailR, adjL, adjR, hLR, hRL, hAfter, nL, nR⟩]
    rfl
  obtain ⟨certificate⟩ := accepted
  have inH : ∀ e ∈ certificate.walk.edges, e ∈
      (object.graph.deleteEdges separation.exchangedEdges ⊔
        (SimpleGraph.edge separation.nextLeft separation.rightAfter ⊔
          SimpleGraph.edge separation.nextRight separation.leftAfter)).edgeSet := by
    intro e he
    rw [← graphEq]
    exact certificate.walk.edges_subset_edgeSet he
  have toG : ∀ {x y : object.Vertex}
      (P : (object.graph.deleteEdges separation.exchangedEdges).Walk x y),
      ∀ e ∈ P.edges, e ∈ object.graph.edgeSet := fun P e he =>
    SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le _) (P.edges_subset_edgeSet he)
  have deleted : ∀ {x y : object.Vertex}
      (P : (object.graph.deleteEdges separation.exchangedEdges).Walk x y),
      s(separation.nextLeft, separation.leftAfter) ∉ P.edges ∧
        s(separation.nextRight, separation.rightAfter) ∉ P.edges := by
    intro x y P
    constructor
    · intro he
      have h := P.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_deleteEdges] at h
      exact h.2 (Or.inl rfl)
    · intro he
      have h := P.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_deleteEdges] at h
      exact h.2 (Or.inr rfl)
  rcases DoubleSwitch.doubleSwitch_cycle_forced adjL adjR separation.distinct hLR
      (Ne.symm hRL) hAfter nL nR noG (certificate.walk.transfer _ inH)
      (certificate.isCycle.transfer inH)
      (by
        convert certificate.length_ok using 1
        exact SimpleGraph.Walk.length_transfer _ _) with
    one | one | both
  · refine ⟨⟨tailL, tailR, adjL, adjR, hLR, hRL, hAfter, nL, nR⟩, Or.inl ?_⟩
    obtain ⟨P, ⟨pPath, pAcc⟩, least, lex⟩ := DoubleSwitch.exists_least
      (fun P : (object.graph.deleteEdges separation.exchangedEdges).Walk
        separation.nextLeft separation.rightAfter => P.length)
      (fun P => P.support.map (vertexRank object))
      (DoubleSwitch.walk_length_finite _ _) one
    refine ⟨P, pPath, pAcc, fun P' p' a' => least P' ⟨p', a'⟩,
      fun P' p' a' l => lex P' ⟨p', a'⟩ l, fun zNot bNot => ?_⟩
    have apex := DoubleSwitch.apex_cycle_rejected noG separation.nextLeft_adj
      separation.nextRight_adj adjR separation.distinct (P.transfer _ (toG P))
      (pPath.transfer (toG P)) (by rw [SimpleGraph.Walk.support_transfer]; exact zNot)
      (by rw [SimpleGraph.Walk.support_transfer]; exact bNot)
    rwa [SimpleGraph.Walk.length_transfer] at apex
  · refine ⟨⟨tailL, tailR, adjL, adjR, hLR, hRL, hAfter, nL, nR⟩, Or.inr (Or.inl ?_)⟩
    obtain ⟨P, ⟨pPath, pAcc⟩, least, lex⟩ := DoubleSwitch.exists_least
      (fun P : (object.graph.deleteEdges separation.exchangedEdges).Walk
        separation.nextRight separation.leftAfter => P.length)
      (fun P => P.support.map (vertexRank object))
      (DoubleSwitch.walk_length_finite _ _) one
    refine ⟨P, pPath, pAcc, fun P' p' a' => least P' ⟨p', a'⟩,
      fun P' p' a' l => lex P' ⟨p', a'⟩ l, fun zNot aNot => ?_⟩
    have apex := DoubleSwitch.apex_cycle_rejected noG separation.nextRight_adj
      separation.nextLeft_adj adjL (Ne.symm separation.distinct)
      (P.transfer _ (toG P)) (pPath.transfer (toG P))
      (by rw [SimpleGraph.Walk.support_transfer]; exact zNot)
      (by rw [SimpleGraph.Walk.support_transfer]; exact aNot)
    rwa [SimpleGraph.Walk.length_transfer] at apex
  · refine ⟨⟨tailL, tailR, adjL, adjR, hLR, hRL, hAfter, nL, nR⟩, Or.inr (Or.inr ?_)⟩
    obtain ⟨⟨P₁, P₂⟩, ⟨p₁, p₂, disj, acc⟩, least, lex⟩ := DoubleSwitch.exists_least
      (fun pair : (object.graph.deleteEdges separation.exchangedEdges).Walk
          separation.nextLeft separation.leftAfter ×
        (object.graph.deleteEdges separation.exchangedEdges).Walk
          separation.nextRight separation.rightAfter =>
        pair.1.length + pair.2.length)
      (fun pair => (pair.1.support ++ pair.2.support).map (vertexRank object))
      (DoubleSwitch.walkPair_length_finite _ _ _ _)
      (Q := fun pair => pair.1.IsPath ∧ pair.2.IsPath ∧
        List.Disjoint pair.1.support pair.2.support ∧
        L (pair.1.length + pair.2.length + 2))
      (by
        obtain ⟨P₁, P₂, rest⟩ := both
        exact ⟨⟨P₁, P₂⟩, rest⟩)
    refine ⟨P₁, P₂, p₁, p₂, disj, acc,
      fun Q₁ Q₂ q₁ q₂ d a => least ⟨Q₁, Q₂⟩ ⟨q₁, q₂, d, a⟩,
      fun Q₁ Q₂ q₁ q₂ d a l => lex ⟨Q₁, Q₂⟩ ⟨q₁, q₂, d, a⟩ l, ?_, ?_⟩
    · have closed := DoubleSwitch.closing_edge_rejected noG adjL.symm
        (P₁.transfer _ (toG P₁)) (p₁.transfer (toG P₁))
        (by
          rw [SimpleGraph.Walk.edges_transfer, Sym2.eq_swap]
          exact (deleted P₁).1)
      rwa [SimpleGraph.Walk.length_transfer] at closed
    · have closed := DoubleSwitch.closing_edge_rejected noG adjR.symm
        (P₂.transfer _ (toG P₂)) (p₂.transfer (toG P₂))
        (by
          rw [SimpleGraph.Walk.edges_transfer, Sym2.eq_swap]
          exact (deleted P₂).2)
      rwa [SimpleGraph.Walk.length_transfer] at closed

/-- **The target-free arm: the switched graph is a counterexample of G's size.**
At a target-avoiding G of minimum degree at least `k`, a switch at `z` without
an accepted cycle is a graph with G's vertices, G's number of edges, minimum
degree at least `k` and no accepted cycle.  It is not lexicographically
smaller than G, so minimality says nothing more: a valid swap preserves size,
and no smaller counterexample arises. -/
theorem switched_sameSize {L : Nat → Prop} {k : Nat}
    (baseline : MinimumDegreeAtLeast k object)
    (targetFree : ¬ HasCycleWithLength L separation.switched) :
    MinimumDegreeAtLeast k separation.switched ∧
      separation.switched.vertexCount = object.vertexCount ∧
      separation.switched.edgeCount = object.edgeCount ∧
      ¬ HasCycleWithLength L separation.switched ∧
      ¬ separation.switched.LexicographicallySmaller object :=
  ⟨separation.switched_baseline baseline, separation.switched_vertexCount,
    separation.switched_edgeCount, targetFree, fun smaller => by
      rcases FiniteObject.lexicographicallySmaller_iff.mp smaller with
        fewer | ⟨_, fewerEdges⟩
      · rw [separation.switched_vertexCount] at fewer
        exact lt_irrefl _ fewer
      · rw [separation.switched_edgeCount] at fewerEdges
        exact lt_irrefl _ fewerEdges⟩

end Separation

/-- **`def:typeA-continuation-classes`: the separator is absorbed**, stated
about G with the switch constructed from G.

The identification is target-defective when the switched graph and G differ in
target truth — which is exit `(4)` — or target-complete when they agree and the
two separated responses lie in one boundary-degree fibre, which the manuscript
derives exactly from *"`S_z` has no unused ambient incidence at `z`"* (`z` off
the boundary of `S_z`) — exit `(5)` — or target-complete only after adjoining a
larger connected support — exit `(6)`, carried as a declared property because
it is a statement about supports strictly larger than `S_z`. -/
def Absorbed {support : Finset object.Vertex} {receiver outside : object.Vertex}
    (Target : FiniteObject.{u} → Prop)
    (separation : Separation object support receiver outside)
    (Enlarges : Prop) : Prop :=
  ¬ (Target separation.switched ↔ Target object) ∨
    (separation.separator ∉
        Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
          separation.switchSupport ∧
      (Target separation.switched ↔ Target object)) ∨
      Enlarges

/-- **`z` is surviving**: it is not absorbed. -/
def Surviving {support : Finset object.Vertex} {receiver outside : object.Vertex}
    (Target : FiniteObject.{u} → Prop)
    (separation : Separation object support receiver outside)
    (Enlarges : Prop) : Prop :=
  ¬ Absorbed Target separation Enlarges

/-- **A separator with no unused ambient incidence is absorbed.**

*"Consider the quotient that identifies the two separated response coordinates
on this finite state.  If some compatible outside context distinguishes the two
responses, the quotient is target-defective ..., which is exit (4).  Otherwise
the identification is target-complete."*  Stated about G the comparison is the
switched graph against G itself; the split is excluded middle on their target
truth. -/
theorem absorbed_of_internal {support : Finset object.Vertex}
    {receiver outside : object.Vertex}
    (Target : FiniteObject.{u} → Prop)
    (separation : Separation object support receiver outside)
    (Enlarges : Prop)
    (internal : separation.separator ∉
      Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
        separation.switchSupport) :
    Absorbed Target separation Enlarges := by
  classical
  by_cases agree : Target separation.switched ↔ Target object
  · exact Or.inr (Or.inl ⟨internal, agree⟩)
  · exact Or.inl agree

/-- **A surviving separator at a target-avoiding G**: the switched graph has no
accepted cycle, `z` has an unused ambient incidence (it is on the boundary of
`S_z`), and the separator does not enlarge. -/
theorem Surviving.of_avoids {support : Finset object.Vertex}
    {receiver outside : object.Vertex} {L : Nat → Prop}
    {separation : Separation object support receiver outside}
    {Enlarges : Prop}
    (avoids : ¬ HasCycleWithLength L object)
    (surviving : Surviving (HasCycleWithLength L) separation Enlarges) :
    ¬ HasCycleWithLength L separation.switched ∧
      separation.separator ∈
        Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
          separation.switchSupport ∧
      ¬ Enlarges := by
  classical
  have agree : HasCycleWithLength L separation.switched ↔
      HasCycleWithLength L object := by
    by_contra differ
    exact surviving (Or.inl differ)
  refine ⟨fun accepted => avoids (agree.mp accepted), ?_,
    fun enlarges => surviving (Or.inr (Or.inr enlarges))⟩
  by_contra internal
  exact surviving (Or.inr (Or.inl ⟨internal, agree⟩))

/-- **`lem:typeA-cubic-switch-absorption`.**  A surviving first separator for
two declared response coordinates through one completion port has

  `d_G(z) ≥ 4`.

*"Hence `d_G(z) ≥ 3` ... Assume `d_G(z) = 3` ... Each of these alternatives is
exactly the absorbed case ... This contradicts that `z` is surviving.  Thus
`d_G(z) ≠ 3`, and the already-proved inequality `d_G(z) ≥ 3` gives
`d_G(z) ≥ 4`."* -/
theorem four_le_degree_of_surviving {support : Finset object.Vertex}
    {receiver outside : object.Vertex}
    {separation : Separation object support receiver outside}
    {Target : FiniteObject.{u} → Prop}
    {Enlarges : Prop} (surviving : Surviving Target separation Enlarges) :
    3 < object.degree separation.separator := by
  classical
  by_cases internal : separation.separator ∉
      Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
        separation.switchSupport
  · exact absurd (absorbed_of_internal Target separation Enlarges internal)
      surviving
  · exact separation.four_le_degree_of_mem_cutBoundary (not_not.1 internal)

/-- **`lem:typeA-continuation-routing`, at a pair of declared coordinates.**

*"Then either one of exits (4)--(6) of `def:typeA-saturated-exits` occurs, or
`𝒦` has a surviving first separator."*

The two germs are distinct declared coordinates through the same port, so
neither is a prefix of the other and they separate; at that separator the
identification is absorbed — which is exits `(4)`--`(6)` — or it is not, which
is the surviving first separator. -/
theorem absorbed_or_surviving {support : Finset object.Vertex}
    {receiver outside : object.Vertex}
    {separation : Separation object support receiver outside}
    (Target : FiniteObject.{u} → Prop)
    (Enlarges : Prop) :
    Absorbed Target separation Enlarges ∨
      Surviving Target separation Enlarges := by
  classical
  exact em _

/-- **Two distinct germs through one port do separate.**  The finiteness step
of `lem:typeA-continuation-routing`, on the germs' own vertex lists. -/
theorem exists_separatesAt_of_ne {support : Finset object.Vertex}
    {receiver outside : object.Vertex}
    {left right : RootedGerm object support receiver outside}
    (different : left.path ≠ right.path) :
    ∃ separator, SeparatesAt left.path right.path separator :=
  exists_separatesAt left.rooted right.rooted
    (RootedGerm.not_isPrefix_of_ne different)
    (RootedGerm.not_isPrefix_of_ne (Ne.symm different))

/-! ## Fan safety

`def:typeB-fan-safe` makes two neighbours `u, v` of a high-degree vertex `h`
adjacent in `F_safe(h)` when five conditions hold.  The first is geometric and
is discharged here from the selected object's own target avoidance: *"any return
from `a` to `b` in `G − h` of length `2^j − 2` would close with the two edges
`ha, hb` to form a cycle of length `2^j`"*.  The remaining four are exactly
the label, target-defect, target-compression and delocalization exits `(3)`--`(6)`,
which are already denied on the branch that reaches exit `(7)`; they are
therefore carried as a parameter and read, never restated. -/

/-- **A simple `a`--`b` return in `G − h`.** -/
structure FanReturn (object : FiniteObject.{u})
    (centre first second : object.Vertex) where
  /-- The return. -/
  walk : object.graph.Walk first second
  /-- It is simple. -/
  isPath : walk.IsPath
  /-- It avoids the centre, which is what `G − h` means. -/
  avoidsCentre : centre ∉ walk.support

/-- **The return closes with the two fan edges.**  `ha`, the return, and `bh`
are a simple cycle of length `|R| + 2`, so a return whose shifted length is
accepted exhibits the target. -/
theorem hasCycleWithLength_of_fanReturn {LengthOK : Nat → Prop}
    {centre first second : object.Vertex}
    (firstAdj : object.graph.Adj centre first)
    (secondAdj : object.graph.Adj centre second)
    (different : first ≠ second)
    (return' : FanReturn object centre first second)
    (accepted : LengthOK (return'.walk.length + 2)) :
    Graph.HasCycleWithLength LengthOK object := by
  classical
  refine ⟨(?pair : Graph.CommonEndpointsCycle object).target LengthOK ?_⟩
  case pair =>
    exact
      { ends := (first, second)
        forward := return'.walk
        backward := SimpleGraph.Walk.cons firstAdj.symm
          (SimpleGraph.Walk.cons secondAdj SimpleGraph.Walk.nil)
        forward_isPath := return'.isPath
        backward_isPath := by
          refine SimpleGraph.Walk.IsPath.mk' ?_
          simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
          refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, ?_⟩⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
            exact fun member => by
              rcases member with equal | equal
              · exact (object.graph.ne_of_adj firstAdj) equal.symm
              · exact different equal
          · simp only [List.mem_singleton]
            exact fun equal => (object.graph.ne_of_adj secondAdj) equal
          · exact List.nodup_singleton _
        internallyDisjoint := by
          intro vertex memberForward memberBackward
          have inSupport : vertex ∈ return'.walk.support :=
            List.mem_of_mem_tail memberForward
          have backwardSupport :
              (SimpleGraph.Walk.cons firstAdj.symm
                (SimpleGraph.Walk.cons secondAdj
                  SimpleGraph.Walk.nil)).reverse.support.tail =
                [centre, first] := by
            simp
          rw [backwardSupport] at memberBackward
          simp only [List.mem_cons, List.not_mem_nil,
            or_false] at memberBackward
          rcases memberBackward with equal | equal
          · exact return'.avoidsCentre (equal ▸ inSupport)
          · -- `a` is the head of a simple return, so it is not on its own tail.
            have nodup : (first :: return'.walk.support.tail).Nodup := by
              have := return'.isPath.support_nodup
              rwa [return'.walk.support_eq_cons] at this
            exact (List.nodup_cons.mp nodup).1 (equal ▸ memberForward)
        nondegenerate := Or.inr (by simp) }
  · simpa using accepted

/-- **`def:typeB-fan-safe`**, as the exit-`(7)` handoff uses it: the geometric
clause, and the four quotient clauses read from the branch.  `Absorbing` is the
branch's own record that one of exits `(3)`--`(6)` occurs at the pair; the
handoff never restates those exits and never proves them here. -/
def FanSafe (object : FiniteObject.{u}) (LengthOK : Nat → Prop)
    (Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop)
    (centre first second : object.Vertex) : Prop :=
  (∀ return' : FanReturn object centre first second,
      ¬ LengthOK (return'.walk.length + 2)) ∧
    ¬ Absorbing centre first second

/-- **The geometric clause of `def:typeB-fan-safe` holds on the selected
object.**  A return whose shifted length is accepted would be an accepted cycle,
and the selection carries none. -/
theorem fanSafe_geometric {LengthOK : Nat → Prop}
    {centre first second : object.Vertex}
    (firstAdj : object.graph.Adj centre first)
    (secondAdj : object.graph.Adj centre second)
    (different : first ≠ second)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object) :
    ∀ return' : FanReturn object centre first second,
      ¬ LengthOK (return'.walk.length + 2) :=
  fun return' accepted =>
    avoids (hasCycleWithLength_of_fanReturn firstAdj secondAdj different return'
      accepted)

/-! ## The decorated handoff fan envelope -/

/-- **`def:decorated-fan-envelope`.**  The pair `𝔛 = (Y, H)` together with the
handoff-arm data: for each decoration a nonempty assigned first-neighbour set,
a simple handoff arm from each assigned first neighbour to a terminal vertex of
the core whose interior avoids `Y ∪ H ∪ {h}`, distinct first neighbours, and the
fan-safe clique condition on the assigned neighbours themselves.

`HighDegree` is the ambient high-degree predicate the decorations are drawn
from; `lem:typeA-cubic-switch-absorption`'s own conclusion `d_G(z) ≥ 4` is what
the exit-`(7)` handoff instantiates it with. -/
structure Envelope (object : FiniteObject.{u}) (LengthOK : Nat → Prop)
    (HighDegree : object.Vertex → Prop)
    (Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop) where
  /-- `Y`, the counted `P₁₃`-free remainder core. -/
  core : Finset object.Vertex
  /-- `H`, the assigned high-degree decorations. -/
  decorations : Finset object.Vertex
  /-- `H ⊆ V_{≥4}(G)`. -/
  decorations_high : ∀ centre ∈ decorations, HighDegree centre
  /-- `K_h ⊆ N_G(h)`, the assigned first neighbours. -/
  assigned : object.Vertex → Finset object.Vertex
  /-- It is nonempty. -/
  assigned_nonempty : ∀ centre ∈ decorations, (assigned centre).Nonempty
  /-- and consists of actual neighbours. -/
  assigned_adj : ∀ centre ∈ decorations, ∀ first ∈ assigned centre,
    object.graph.Adj centre first
  /-- `A_{h,a}`, the simple handoff arm issued at `a`. -/
  arm : object.Vertex → object.Vertex → List object.Vertex
  /-- It starts at `a`. -/
  arm_issued : ∀ centre ∈ decorations, ∀ first ∈ assigned centre,
    (arm centre first).head? = some first
  /-- It is a walk. -/
  arm_chain : ∀ centre ∈ decorations, ∀ first ∈ assigned centre,
    (arm centre first).IsChain object.graph.Adj
  /-- and a simple one. -/
  arm_nodup : ∀ centre ∈ decorations, ∀ first ∈ assigned centre,
    (arm centre first).Nodup
  /-- It lands in the core at `y_{h,a}`. -/
  arm_lands : ∀ centre ∈ decorations, ∀ first ∈ assigned centre,
    ∃ terminal, (arm centre first).getLast? = some terminal ∧ terminal ∈ core
  /-- Its interior avoids `Y ∪ H ∪ {h}`. -/
  arm_interior : ∀ centre ∈ decorations, ∀ first ∈ assigned centre,
    ∀ vertex ∈ arm centre first, vertex ∈ core ∨ vertex ∈ decorations ∨
      vertex = centre →
      (arm centre first).getLast? = some vertex
  /-- `K_h` is a clique in `F_safe(h)`. -/
  fanSafe : ∀ centre ∈ decorations, ∀ first ∈ assigned centre,
    ∀ second ∈ assigned centre, first ≠ second →
      FanSafe object LengthOK Absorbing centre first second

namespace Envelope

variable {LengthOK : Nat → Prop} {HighDegree : object.Vertex → Prop}
variable {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
variable (envelope : Envelope object LengthOK HighDegree Absorbing)

/-- **`ω(h) = d_G(h) − 3`**, the ambient surplus token of a decoration, and
`ω(H)` its sum over the decorations.  This is the framework's own ambient
surplus at the registered baseline; the manuscript's `d_G(h) − 3` is that
quantity at `δ = 3`. -/
noncomputable def centreTokens (threshold : Nat) : Nat :=
  object.ambientSurplus envelope.decorations threshold

/-- **`No(𝔛) = def⁺(Y) − ω(H) − ¼|V(Y)|`, negative side**, cleared of the
division exactly as `def:net-charge` is: `s·def⁺(Y) < |V(Y)| + s·ω(H)`. -/
def NegativeCharge (threshold dischargeScale : Nat) : Prop :=
  dischargeScale * object.positiveDeficiency envelope.core threshold <
    envelope.core.card + dischargeScale * envelope.centreTokens threshold

end Envelope

/-! ## `lem:typeA-high-degree-handoff` -/

/-- **`lem:typeA-high-degree-handoff`.**

*"Let `X` be a Type A support, and let `z` be a surviving first separator for a
finite family of declared response coordinates through one completion port.
Then `z`, together with the separated connector tails from `z` to their
first-entry data in `X`, produces a decorated handoff fan envelope."*

`Y = X` is the counted remainder core and `H = {z}`; the assigned first
neighbours are the two separated next incidences, which are distinct because the
germs separate, and the arms are the two connector tails.  The fan-safe clique
condition on that pair is the geometric clause — discharged from the selected
object's target avoidance — together with the four quotient clauses, which are
the exits already denied on this branch. -/
noncomputable def envelopeOfSeparation {support : Finset object.Vertex}
    {receiver outside : object.Vertex} {LengthOK : Nat → Prop}
    {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    (separation : Separation object support receiver outside)
    (armLeft armRight : List object.Vertex)
    (armLeftIssued : armLeft.head? = some separation.nextLeft)
    (armRightIssued : armRight.head? = some separation.nextRight)
    (armLeftChain : armLeft.IsChain object.graph.Adj)
    (armRightChain : armRight.IsChain object.graph.Adj)
    (armLeftNodup : armLeft.Nodup) (armRightNodup : armRight.Nodup)
    (armLeftLands : ∃ terminal, armLeft.getLast? = some terminal ∧
      terminal ∈ support)
    (armRightLands : ∃ terminal, armRight.getLast? = some terminal ∧
      terminal ∈ support)
    (armLeftInterior : ∀ vertex ∈ armLeft,
      vertex ∈ support ∨ vertex = separation.separator →
      armLeft.getLast? = some vertex)
    (armRightInterior : ∀ vertex ∈ armRight,
      vertex ∈ support ∨ vertex = separation.separator →
      armRight.getLast? = some vertex)
    (high : HighDegree separation.separator)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
    (denied : ¬ Absorbing separation.separator separation.nextLeft
      separation.nextRight)
    (deniedSwap : ¬ Absorbing separation.separator separation.nextRight
      separation.nextLeft) :
    Envelope object LengthOK HighDegree Absorbing := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  refine
    { core := support
      decorations := {separation.separator}
      decorations_high := ?_
      assigned := fun _ => {separation.nextLeft, separation.nextRight}
      assigned_nonempty := ?_
      assigned_adj := ?_
      arm := fun _ first =>
        if first = separation.nextLeft then armLeft else armRight
      arm_issued := ?_
      arm_chain := ?_
      arm_nodup := ?_
      arm_lands := ?_
      arm_interior := ?_
      fanSafe := ?_ }
  · intro centre member
    rw [Finset.mem_singleton] at member
    exact member ▸ high
  · intro _ _
    exact ⟨separation.nextLeft, by simp⟩
  · intro centre member first assignedMember
    rw [Finset.mem_singleton] at member
    subst member
    simp only [Finset.mem_insert, Finset.mem_singleton] at assignedMember
    rcases assignedMember with rfl | rfl
    · exact separation.nextLeft_adj
    · exact separation.nextRight_adj
  · intro _ _ first assignedMember
    simp only [Finset.mem_insert, Finset.mem_singleton] at assignedMember
    rcases assignedMember with rfl | rfl
    · simpa using armLeftIssued
    · by_cases equal : separation.nextRight = separation.nextLeft
      · exact absurd equal.symm separation.distinct
      · simpa [equal] using armRightIssued
  · intro _ _ first assignedMember
    simp only [Finset.mem_insert, Finset.mem_singleton] at assignedMember
    rcases assignedMember with rfl | rfl
    · simpa using armLeftChain
    · by_cases equal : separation.nextRight = separation.nextLeft
      · exact absurd equal.symm separation.distinct
      · simpa [equal] using armRightChain
  · intro _ _ first assignedMember
    simp only [Finset.mem_insert, Finset.mem_singleton] at assignedMember
    rcases assignedMember with rfl | rfl
    · simpa using armLeftNodup
    · by_cases equal : separation.nextRight = separation.nextLeft
      · exact absurd equal.symm separation.distinct
      · simpa [equal] using armRightNodup
  · intro _ _ first assignedMember
    simp only [Finset.mem_insert, Finset.mem_singleton] at assignedMember
    rcases assignedMember with rfl | rfl
    · simpa using armLeftLands
    · by_cases equal : separation.nextRight = separation.nextLeft
      · exact absurd equal.symm separation.distinct
      · simpa [equal] using armRightLands
  · intro centre member first assignedMember
    rw [Finset.mem_singleton] at member
    subst member
    simp only [Finset.mem_insert, Finset.mem_singleton] at assignedMember
    rcases assignedMember with rfl | rfl
    · intro vertex vertexMember alternatives
      simp only at vertexMember ⊢
      refine armLeftInterior vertex vertexMember ?_
      rcases alternatives with inside | rest
      · exact Or.inl inside
      · rcases rest with decoration | equal
        · exact Or.inr (Finset.mem_singleton.mp decoration)
        · exact Or.inr equal
    · by_cases equal : separation.nextRight = separation.nextLeft
      · exact absurd equal.symm separation.distinct
      · intro vertex vertexMember alternatives
        simp only [if_neg equal] at vertexMember ⊢
        refine armRightInterior vertex vertexMember ?_
        rcases alternatives with inside | rest
        · exact Or.inl inside
        · rcases rest with decoration | centreEq
          · exact Or.inr (Finset.mem_singleton.mp decoration)
          · exact Or.inr centreEq
  · intro centre member first firstMember second secondMember different
    rw [Finset.mem_singleton] at member
    subst member
    simp only [Finset.mem_insert, Finset.mem_singleton] at firstMember secondMember
    rcases firstMember with rfl | rfl <;> rcases secondMember with rfl | rfl
    · exact absurd rfl different
    · exact ⟨fanSafe_geometric separation.nextLeft_adj separation.nextRight_adj
        separation.distinct avoids, denied⟩
    · exact ⟨fanSafe_geometric separation.nextRight_adj separation.nextLeft_adj
        (Ne.symm separation.distinct) avoids, deniedSwap⟩
    · exact absurd rfl different

/-! ## The same-token first-separator handoff

`lem:same-token-bottleneck-routing` starts with two declared configurations at
the primitive blocker support.  Unlike a Type-A continuation germ, those
configurations are not presented through one completion-port edge.  What the
paper uses after their first separator is exactly the data below: the two
distinct next incidences, their separated tails, and the common remainder core
on which those tails land.  This constructor therefore builds the same
`Envelope` directly from `SeparatesAt`; it does not manufacture a Type-A
`RootedGerm` or a completion-port carrier. -/

/-- **The handoff constructor used by `lem:same-token-bottleneck-routing`.**

This is `def:decorated-fan-envelope` at one first separator.  All arguments are
clauses of that definition or projections of the two declared configurations;
the result is the framework's existing `Envelope`, not a proof-specific data
carrier. -/
noncomputable def envelopeOfFirstSeparator
    {LengthOK : Nat → Prop}
    {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    (support : Finset object.Vertex)
    (separator nextLeft nextRight : object.Vertex)
    (nextDifferent : nextLeft ≠ nextRight)
    (nextLeftAdj : object.graph.Adj separator nextLeft)
    (nextRightAdj : object.graph.Adj separator nextRight)
    (armLeft armRight : List object.Vertex)
    (armLeftIssued : armLeft.head? = some nextLeft)
    (armRightIssued : armRight.head? = some nextRight)
    (armLeftChain : armLeft.IsChain object.graph.Adj)
    (armRightChain : armRight.IsChain object.graph.Adj)
    (armLeftNodup : armLeft.Nodup) (armRightNodup : armRight.Nodup)
    (armLeftLands : ∃ terminal, armLeft.getLast? = some terminal ∧
      terminal ∈ support)
    (armRightLands : ∃ terminal, armRight.getLast? = some terminal ∧
      terminal ∈ support)
    (armLeftInterior : ∀ vertex ∈ armLeft,
      vertex ∈ support ∨ vertex = separator →
      armLeft.getLast? = some vertex)
    (armRightInterior : ∀ vertex ∈ armRight,
      vertex ∈ support ∨ vertex = separator →
      armRight.getLast? = some vertex)
    (high : HighDegree separator)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
    (denied : ¬ Absorbing separator nextLeft nextRight)
    (deniedSwap : ¬ Absorbing separator nextRight nextLeft) :
    Envelope object LengthOK HighDegree Absorbing := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  refine
    { core := support
      decorations := {separator}
      decorations_high := ?_
      assigned := fun _ => {nextLeft, nextRight}
      assigned_nonempty := ?_
      assigned_adj := ?_
      arm := fun _ first => if first = nextLeft then armLeft else armRight
      arm_issued := ?_
      arm_chain := ?_
      arm_nodup := ?_
      arm_lands := ?_
      arm_interior := ?_
      fanSafe := ?_ }
  · intro centre member
    rw [Finset.mem_singleton] at member
    exact member ▸ high
  · intro _ _
    exact ⟨nextLeft, by simp⟩
  · intro centre member first assignedMember
    rw [Finset.mem_singleton] at member
    subst member
    simp only [Finset.mem_insert, Finset.mem_singleton] at assignedMember
    rcases assignedMember with rfl | rfl
    · exact nextLeftAdj
    · exact nextRightAdj
  · intro _ _ first assignedMember
    simp only [Finset.mem_insert, Finset.mem_singleton] at assignedMember
    rcases assignedMember with firstEq | firstEq
    · subst first
      simpa using armLeftIssued
    · have notLeft : first ≠ nextLeft := by
        intro equal
        exact nextDifferent (equal.symm.trans firstEq)
      have rightNeLeft : nextRight ≠ nextLeft := Ne.symm nextDifferent
      simpa [firstEq, rightNeLeft] using armRightIssued
  · intro _ _ first assignedMember
    simp only [Finset.mem_insert, Finset.mem_singleton] at assignedMember
    rcases assignedMember with firstEq | firstEq
    · subst first
      simpa using armLeftChain
    · have notLeft : first ≠ nextLeft := by
        intro equal
        exact nextDifferent (equal.symm.trans firstEq)
      have rightNeLeft : nextRight ≠ nextLeft := Ne.symm nextDifferent
      simpa [firstEq, rightNeLeft] using armRightChain
  · intro _ _ first assignedMember
    simp only [Finset.mem_insert, Finset.mem_singleton] at assignedMember
    rcases assignedMember with firstEq | firstEq
    · subst first
      simpa using armLeftNodup
    · have notLeft : first ≠ nextLeft := by
        intro equal
        exact nextDifferent (equal.symm.trans firstEq)
      have rightNeLeft : nextRight ≠ nextLeft := Ne.symm nextDifferent
      simpa [firstEq, rightNeLeft] using armRightNodup
  · intro _ _ first assignedMember
    simp only [Finset.mem_insert, Finset.mem_singleton] at assignedMember
    rcases assignedMember with firstEq | firstEq
    · subst first
      simpa using armLeftLands
    · have notLeft : first ≠ nextLeft := by
        intro equal
        exact nextDifferent (equal.symm.trans firstEq)
      have rightNeLeft : nextRight ≠ nextLeft := Ne.symm nextDifferent
      simpa [firstEq, rightNeLeft] using armRightLands
  · intro centre member first assignedMember
    rw [Finset.mem_singleton] at member
    subst member
    simp only [Finset.mem_insert, Finset.mem_singleton] at assignedMember
    rcases assignedMember with firstEq | firstEq
    · subst first
      intro vertex vertexMember alternatives
      simp only at vertexMember ⊢
      refine armLeftInterior vertex vertexMember ?_
      rcases alternatives with inside | rest
      · exact Or.inl inside
      · rcases rest with decoration | equal
        · exact Or.inr (Finset.mem_singleton.mp decoration)
        · exact Or.inr equal
    · have notLeft : first ≠ nextLeft := by
        intro equal
        exact nextDifferent (equal.symm.trans firstEq)
      intro vertex vertexMember alternatives
      simp only [if_neg notLeft] at vertexMember ⊢
      refine armRightInterior vertex vertexMember ?_
      rcases alternatives with inside | rest
      · exact Or.inl inside
      · rcases rest with decoration | centreEq
        · exact Or.inr (Finset.mem_singleton.mp decoration)
        · exact Or.inr centreEq
  · intro centre member first firstMember second secondMember different
    rw [Finset.mem_singleton] at member
    subst member
    simp only [Finset.mem_insert, Finset.mem_singleton] at firstMember secondMember
    rcases firstMember with rfl | rfl <;> rcases secondMember with rfl | rfl
    · exact absurd rfl different
    · exact ⟨fanSafe_geometric nextLeftAdj nextRightAdj nextDifferent avoids,
        denied⟩
    · exact ⟨fanSafe_geometric nextRightAdj nextLeftAdj
        (Ne.symm nextDifferent) avoids, deniedSwap⟩
    · exact absurd rfl different

/-! ## `lem:decorated-fan-admissibility` -/

/-- **The Type B fan-envelope data a decorated handoff carries.**

`lem:decorated-fan-admissibility`: *"contextual target-safety, a `P₁₃`-free
empty-`3`-core remainder core, hereditary target-uncompressibility of the
decorated boundaried profile, and fan-return-safety at every decoration `h ∈ H`."*

This is the *handoff interface* of `rem:typeA-typeB-stratification`: every field
is a hypothesis the Type B calculation consumes, and none is a conclusion of
`lem:typeB-exclusion`. -/
structure Admissible (object : FiniteObject.{u}) (LengthOK : Nat → Prop)
    (Uncompressible : Finset object.Vertex → Prop)
    (WindowFree : Finset object.Vertex → Prop)
    {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    (envelope : Envelope object LengthOK HighDegree Absorbing) : Prop where
  /-- Contextual dyadic-safety: the ambient object carries no accepted cycle. -/
  dyadicSafe : ¬ Graph.HasCycleWithLength LengthOK object
  /-- The counted core is `P₁₃`-free with empty internal `3`-core. -/
  coreWindowFree : WindowFree envelope.core
  /-- Hereditary target-uncompressibility of the decorated profile. -/
  uncompressible : ∀ piece : Finset object.Vertex, Uncompressible piece
  /-- Fan-return safety at every decoration: no assigned pair closes an accepted
  cycle through the centre. -/
  fanReturnSafe : ∀ centre ∈ envelope.decorations,
    ∀ first ∈ envelope.assigned centre, ∀ second ∈ envelope.assigned centre,
      first ≠ second →
      ∀ return' : FanReturn object centre first second,
        ¬ LengthOK (return'.walk.length + 2)

/-- **`lem:decorated-fan-admissibility`.**

*"If exit (7) of `def:typeA-saturated-exits` occurs in a saturated Type A
branch, the resulting decorated handoff fan envelope carries exactly the data
required by the Type B fan calculation."*

The counted core is the Type A support `X` used in
`lem:typeA-high-degree-handoff`, so the first three clauses are inherited from
`def:admissible` — here read as the branch's own committed facts — and the
fourth is the geometric clause of the envelope's fan-safe cliques.  Nothing in
the derivation mentions `lem:typeB-exclusion`. -/
theorem admissible_of_envelope {LengthOK : Nat → Prop}
    {Uncompressible WindowFree : Finset object.Vertex → Prop}
    {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    {envelope : Envelope object LengthOK HighDegree Absorbing}
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
    (windowFree : WindowFree envelope.core)
    (uncompressible : ∀ piece : Finset object.Vertex, Uncompressible piece) :
    Admissible object LengthOK Uncompressible WindowFree envelope where
  dyadicSafe := avoids
  coreWindowFree := windowFree
  uncompressible := uncompressible
  fanReturnSafe := fun centre member first firstMember second secondMember
      different => (envelope.fanSafe centre member first firstMember second
    secondMember different).1

/-! ## `def:decorated-typeB-envelope-support` and the exact transfer -/

/-- **`def:decorated-typeB-envelope-support`.**  A finite family of actual
exit-`(7)` envelopes.  Its Type A cores are pairwise vertex-disjoint, every
envelope is admissible, and every core has a handoff decoration.

No component assignment is stored here.  The core--centre incidence relation
and its connected components are derived below from `Envelope.decorations`.
Thus a caller cannot group unrelated cores or split two cores sharing a centre. -/
structure GroupedEnvelopes (object : FiniteObject.{u}) (LengthOK : Nat → Prop)
    (Uncompressible WindowFree : Finset object.Vertex → Prop)
    (HighDegree : object.Vertex → Prop)
    (Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop)
    (Core : Type v) where
  /-- `𝒴`, the finite family of Type A cores producing exit-`(7)` handoffs. -/
  cores : Finset Core
  /-- The actual decorated envelope carried by a core. -/
  envelope : Core → Envelope object LengthOK HighDegree Absorbing
  /-- Every listed envelope is the admissible Type B handoff supplied by the
  Type A exit. -/
  admissible : ∀ core ∈ cores,
    Admissible object LengthOK Uncompressible WindowFree (envelope core)
  /-- Exit `(7)` supplies at least one high-degree decoration. -/
  decorated : ∀ core ∈ cores, (envelope core).decorations.Nonempty
  /-- The canonical Type A cores are pairwise vertex-disjoint. -/
  pairwiseCoreDisjoint : ∀ ⦃left right : Core⦄,
    left ∈ cores → right ∈ cores → left ≠ right →
      Disjoint (envelope left).core (envelope right).core

namespace GroupedEnvelopes

variable {LengthOK : Nat → Prop}
variable {Uncompressible WindowFree : Finset object.Vertex → Prop}
variable {HighDegree : object.Vertex → Prop}
variable {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
variable {Core : Type v} [DecidableEq Core]
variable (grouped : GroupedEnvelopes object LengthOK Uncompressible WindowFree
  HighDegree Absorbing Core)

/-- The centre type is the ambient vertex type, not a second carrier. -/
abbrev Centre := object.Vertex

/-- All and only decorations appearing in the listed envelopes. -/
noncomputable def centres : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact grouped.cores.biUnion fun core => (grouped.envelope core).decorations

/-- The core--centre incidence relation, derived from the actual envelope. -/
def Incident (core : Core) (centre : object.Vertex) : Prop :=
  core ∈ grouped.cores ∧ centre ∈ (grouped.envelope core).decorations

/-- The finite bipartite incidence graph of the envelope family. -/
noncomputable def incidenceGraph : SimpleGraph (Core ⊕ object.Vertex) :=
  SimpleGraph.fromRel fun left right =>
    match left, right with
    | .inl core, .inr centre => grouped.Incident core centre
    | _, _ => False

/-- The component type is the connected-component quotient of the actual
incidence graph. -/
abbrev Component := grouped.incidenceGraph.ConnectedComponent

/-- The incidence component containing a core. -/
noncomputable def coreComponent (core : Core) : grouped.Component :=
  grouped.incidenceGraph.connectedComponentMk (.inl core)

/-- The incidence component containing an ambient handoff centre. -/
noncomputable def centreComponent (centre : object.Vertex) : grouped.Component :=
  grouped.incidenceGraph.connectedComponentMk (.inr centre)

/-- The components met by the declared finite core and centre families. -/
noncomputable def components : Finset grouped.Component := by
  classical
  exact grouped.cores.image grouped.coreComponent ∪
    grouped.centres.image grouped.centreComponent

/-- `𝒴_𝔆`, the cores in one actual incidence component. -/
noncomputable def componentCores (component : grouped.Component) : Finset Core := by
  classical
  exact grouped.cores.filter fun core => grouped.coreComponent core = component

/-- `H_𝔆`, the ambient centres in one actual incidence component. -/
noncomputable def componentCentres (component : grouped.Component) :
    Finset object.Vertex := by
  classical
  exact grouped.centres.filter fun centre =>
    grouped.centreComponent centre = component

@[simp] theorem mem_centres_iff (centre : object.Vertex) :
    centre ∈ grouped.centres ↔
      ∃ core ∈ grouped.cores,
        centre ∈ (grouped.envelope core).decorations := by
  classical
  simp [centres]

@[simp] theorem mem_componentCores_iff (component : grouped.Component)
    (core : Core) :
    core ∈ grouped.componentCores component ↔
      core ∈ grouped.cores ∧ grouped.coreComponent core = component := by
  classical
  simp [componentCores]

@[simp] theorem mem_componentCentres_iff (component : grouped.Component)
    (centre : object.Vertex) :
    centre ∈ grouped.componentCentres component ↔
      centre ∈ grouped.centres ∧ grouped.centreComponent centre = component := by
  classical
  simp [componentCentres]

theorem coreComponent_mem_components {core : Core} (member : core ∈ grouped.cores) :
    grouped.coreComponent core ∈ grouped.components := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨core, member, rfl⟩)

theorem centreComponent_mem_components {centre : object.Vertex}
    (member : centre ∈ grouped.centres) :
    grouped.centreComponent centre ∈ grouped.components := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨centre, member, rfl⟩)

/-- An envelope and one of its decorations lie in the same graph-derived
incidence component. -/
theorem coreComponent_eq_centreComponent {core : Core} {centre : object.Vertex}
    (incident : grouped.Incident core centre) :
    grouped.coreComponent core = grouped.centreComponent centre := by
  apply SimpleGraph.ConnectedComponent.sound
  refine ⟨SimpleGraph.Walk.cons ?_ SimpleGraph.Walk.nil⟩
  simpa [incidenceGraph, Incident] using incident

/-- Distinct incidence components contain disjoint core families. -/
theorem disjoint_componentCores {left right : grouped.Component}
    (different : left ≠ right) :
    Disjoint (grouped.componentCores left) (grouped.componentCores right) := by
  classical
  rw [Finset.disjoint_left]
  intro core leftMember rightMember
  have leftEq := (grouped.mem_componentCores_iff left core).1 leftMember |>.2
  have rightEq := (grouped.mem_componentCores_iff right core).1 rightMember |>.2
  exact different (leftEq.symm.trans rightEq)

/-- Distinct incidence components contain disjoint centre families.  This is
the manuscript's at-most-once grouped-role property. -/
theorem disjoint_componentCentres {left right : grouped.Component}
    (different : left ≠ right) :
    Disjoint (grouped.componentCentres left) (grouped.componentCentres right) := by
  classical
  rw [Finset.disjoint_left]
  intro centre leftMember rightMember
  have leftEq := (grouped.mem_componentCentres_iff left centre).1 leftMember |>.2
  have rightEq := (grouped.mem_componentCentres_iff right centre).1 rightMember |>.2
  exact different (leftEq.symm.trans rightEq)

/-- Every listed core occurs in exactly one actual incidence component. -/
theorem existsUnique_component_of_core {core : Core} (member : core ∈ grouped.cores) :
    ∃! component : grouped.Component,
      component ∈ grouped.components ∧ core ∈ grouped.componentCores component := by
  refine ⟨grouped.coreComponent core,
    ⟨grouped.coreComponent_mem_components member, ?_⟩, ?_⟩
  · exact (grouped.mem_componentCores_iff _ _).2 ⟨member, rfl⟩
  · intro component property
    exact ((grouped.mem_componentCores_iff component core).1 property.2).2.symm

/-- Every ambient handoff centre occurs in exactly one actual incidence
component. -/
theorem existsUnique_component_of_centre {centre : object.Vertex}
    (member : centre ∈ grouped.centres) :
    ∃! component : grouped.Component,
      component ∈ grouped.components ∧
        centre ∈ grouped.componentCentres component := by
  refine ⟨grouped.centreComponent centre,
    ⟨grouped.centreComponent_mem_components member, ?_⟩, ?_⟩
  · exact (grouped.mem_componentCentres_iff _ _).2 ⟨member, rfl⟩
  · intro component property
    exact ((grouped.mem_componentCentres_iff component centre).1 property.2).2.symm

/-- The union of the pairwise-disjoint counted Type A cores. -/
noncomputable def coreSupport : Finset object.Vertex := by
  classical
  exact grouped.cores.biUnion fun core => (grouped.envelope core).core

/-- Pairwise core coverage is exact: the cardinality of the grouped counted
core is the sum of the cardinalities of its Type A cores. -/
theorem card_coreSupport :
    grouped.coreSupport.card =
      ∑ core ∈ grouped.cores, (grouped.envelope core).core.card := by
  classical
  rw [coreSupport, Finset.card_biUnion]
  exact fun left leftMember right rightMember different =>
    grouped.pairwiseCoreDisjoint leftMember rightMember different

/-- A vertex covered by the grouped counted core belongs to a unique Type A
core of the family. -/
theorem mem_coreSupport_existsUnique (vertex : object.Vertex) :
    vertex ∈ grouped.coreSupport ↔
      ∃! core : Core,
        core ∈ grouped.cores ∧ vertex ∈ (grouped.envelope core).core := by
  classical
  constructor
  · intro member
    obtain ⟨core, coreMember, vertexMember⟩ :=
      Finset.mem_biUnion.1 (show vertex ∈ grouped.cores.biUnion
        (fun core => (grouped.envelope core).core) from member)
    refine ⟨core, ⟨coreMember, vertexMember⟩, ?_⟩
    intro other property
    by_contra different
    exact Finset.disjoint_left.1
      (grouped.pairwiseCoreDisjoint property.1 coreMember different)
      property.2 vertexMember
  · rintro ⟨core, ⟨coreMember, vertexMember⟩, _⟩
    exact Finset.mem_biUnion.2 ⟨core, coreMember, vertexMember⟩

/-- Every listed core is counted exactly once across incidence components. -/
theorem sum_componentCores (weight : Core → Nat) :
    ∑ component ∈ grouped.components,
        ∑ core ∈ grouped.componentCores component, weight core =
      ∑ core ∈ grouped.cores, weight core := by
  classical
  exact Finset.sum_fiberwise_of_maps_to
    (fun core member => grouped.coreComponent_mem_components member) weight

/-- Every ambient handoff centre is counted exactly once across incidence
components. -/
theorem sum_componentCentres (weight : object.Vertex → Nat) :
    ∑ component ∈ grouped.components,
        ∑ centre ∈ grouped.componentCentres component, weight centre =
      ∑ centre ∈ grouped.centres, weight centre := by
  classical
  exact Finset.sum_fiberwise_of_maps_to
    (fun centre member => grouped.centreComponent_mem_components member) weight

/-- `ω(𝔆) = Σ_{h ∈ H_𝔆}(d_G(h)-δ)`, using the ambient centre itself. -/
noncomputable def componentTokens (threshold : Nat)
    (component : grouped.Component) : Nat :=
  ∑ centre ∈ grouped.componentCentres component,
    (object.degree centre - threshold)

/-- Each ambient handoff-centre token is counted exactly once in the grouped
role. -/
theorem sum_componentTokens (threshold : Nat) :
    ∑ component ∈ grouped.components,
        grouped.componentTokens threshold component =
      ∑ centre ∈ grouped.centres, (object.degree centre - threshold) := by
  simpa [componentTokens] using
    grouped.sum_componentCentres fun centre => object.degree centre - threshold

/-- `No(𝔛*_𝔆)` at the discharge scale, computed from the actual cores and
ambient centres in the incidence component. -/
noncomputable def componentCharge (threshold dischargeScale : Nat)
    (component : grouped.Component) : Int :=
  (dischargeScale : Int) *
      (∑ core ∈ grouped.componentCores component,
        object.positiveDeficiency (grouped.envelope core).core threshold : Nat) -
    (dischargeScale : Int) * (grouped.componentTokens threshold component : Nat) -
      (∑ core ∈ grouped.componentCores component,
        (grouped.envelope core).core.card : Nat)

/-- **`lem:decorated-envelope-no-double-count`.**  The graph-derived incidence
components partition both the pairwise-disjoint Type A cores and the ambient
handoff centres.  Hence neither a core deficiency nor a grouped-role centre
token is counted twice. -/
theorem sum_componentCharge (threshold dischargeScale : Nat) :
    ∑ component ∈ grouped.components,
        grouped.componentCharge threshold dischargeScale component =
      ((dischargeScale : Int) *
            (∑ core ∈ grouped.cores,
              object.positiveDeficiency (grouped.envelope core).core threshold : Nat) -
          (∑ core ∈ grouped.cores, (grouped.envelope core).core.card : Nat)) -
        (dischargeScale : Int) *
          (∑ centre ∈ grouped.centres,
            (object.degree centre - threshold) : Nat) := by
  classical
  simp only [componentCharge, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Nat.cast_sum]
  rw [grouped.sum_componentCores (fun core =>
      object.positiveDeficiency (grouped.envelope core).core threshold),
    grouped.sum_componentCores (fun core => (grouped.envelope core).core.card),
    grouped.sum_componentTokens threshold]
  push_cast
  ring

/-- A handoff centre's surplus token belongs to the token sum of its unique
incidence component. -/
theorem token_le_componentTokens (threshold : Nat) {centre : object.Vertex}
    (member : centre ∈ grouped.centres) :
    object.degree centre - threshold ≤
      grouped.componentTokens threshold (grouped.centreComponent centre) := by
  classical
  simpa [componentTokens] using
    (Finset.single_le_sum (s := grouped.componentCentres
        (grouped.centreComponent centre))
      (f := fun h => object.degree h - threshold)
      (fun _ _ => Nat.zero_le _)
      ((grouped.mem_componentCentres_iff _ _).2 ⟨member, rfl⟩))

/-- The grouped-role decoration surplus, read as the ambient surplus of the
deduplicated centre family: `σ(H) = Σ_𝔆 ω(𝔆)`.  This is the bridge between the
component accounting above and the region-surplus comparisons of
`def:window-remainder-surplus-split` — in particular it feeds
`ambientSurplus_le_degreeSurplus`, the `S_B ≤ σ(G)` half of the grouped role of
`def:typeB-residual-mass`. -/
theorem ambientSurplus_centres (threshold : Nat) :
    object.ambientSurplus grouped.centres threshold =
      ∑ component ∈ grouped.components,
        grouped.componentTokens threshold component := by
  rw [grouped.sum_componentTokens threshold]
  rfl

end GroupedEnvelopes

/-- `ω(H)` spelled as the decoration sum `Σ_{h ∈ H}(d_G(h) − δ)`, which is the
form `lem:decorated-envelope-deficit-bound` charges against. -/
theorem Envelope.centreTokens_eq_sum {LengthOK : Nat → Prop}
    {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    (envelope : Envelope object LengthOK HighDegree Absorbing)
    (threshold : Nat) :
    envelope.centreTokens threshold =
      ∑ centre ∈ envelope.decorations, (object.degree centre - threshold) :=
  rfl

end Hypostructure.Graph.DecoratedHandoff
