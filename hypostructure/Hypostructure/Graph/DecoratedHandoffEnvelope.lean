import Hypostructure.Graph.CommonPortReturnCycle
import Hypostructure.Graph.Response
import Hypostructure.Graph.Strategy.InterfaceReplacement

/-!
# Connector germs, surviving separators, and the decorated handoff fan envelope

This module owns the objects Type A exit `(7)` is made of, and nothing else:

* `def:typeA-continuation-classes` — outside connector germs through a
  completion port, the vertex two germs *separate at*, the switch support's
  declared reading, and the absorbed/surviving classification of a separator;
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

The absorbed classification is derived from `lem:context-universality`, and so
is the fibre.  `def:typeA-continuation-classes` puts *"the two coordinates have
the same image in the relevant boundary-degree fibre"* into what *separating at
`z`* means, so `Separation` carries `S_z` — through the framework's own
support-to-atom construction — and registers the two coordinates' declared
readings in the certificate the framework *computes* for that atom.  Both
`Separation.sameFibre` and `SwitchReading.fibre` are then read off that
registration: they are node `[11]`'s `lem:degree-profile-fibres`, and this
module restates neither.  What the switch support supplies is the manuscript's
own registration step — *"the two separated responses therefore form a finite
declared boundaried response state"* at an exhausted separator — which is the
`registered` field of `SwitchReading`.

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
`lem:typeA-continuation-routing`: *"since `𝒦` is finite and each germ is
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
group of fields.

That third conjunct is not a copied boundary profile.  `S_z` is the
manuscript's own *"finite connected support consisting of the common prefix
from `h` to `z`, the two connector tails from `z` to their first-entry
receivers, the two receiver-entry channels in `X`, the completion port boundary
datum, and the declared supports of the two response coordinates"*, presented
through the framework's existing support-to-atom construction; the two
coordinates' declared readings are then registered in that atom's *generated*
profile certificate, whose constructor is private to the framework so that no
caller registers a guessed profile.  `sameFibre` below reads the manuscript's
conjunct off that registration. -/
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
  /-- The first coordinate's declared reading on `S_z`'s interface. -/
  leftReading : Graph.BoundaryPiece
    (Graph.Strategy.InterfaceReplacement.SupportAtom.properAtom object
      switchSupport switchConnected switchProper).decomposition.interface
  /-- and the second's. -/
  rightReading : Graph.BoundaryPiece
    (Graph.Strategy.InterfaceReplacement.SupportAtom.properAtom object
      switchSupport switchConnected switchProper).decomposition.interface
  /-- The first coordinate lies in `S_z`'s registered boundary-degree fibre. -/
  leftRegistered : leftReading.boundaryDegreeProfile =
    (Graph.deriveBoundariedAtomProfile
      (Graph.Strategy.InterfaceReplacement.SupportAtom.properAtom object
        switchSupport switchConnected switchProper)).boundaryDegreeProfile
  /-- and so does the second. -/
  rightRegistered : rightReading.boundaryDegreeProfile =
    (Graph.deriveBoundariedAtomProfile
      (Graph.Strategy.InterfaceReplacement.SupportAtom.properAtom object
        switchSupport switchConnected switchProper)).boundaryDegreeProfile

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

/-- **`def:typeA-continuation-classes`' third conjunct, read off the
registration.**

*"...and the two coordinates have the same image in the relevant boundary-degree
fibre."*  Both readings were registered in `S_z`'s one generated certificate,
so this is `lem:degree-profile-fibres` at node `[11]`; it is not restated
here. -/
theorem sameFibre :
    separation.leftReading.boundaryDegreeProfile =
      separation.rightReading.boundaryDegreeProfile :=
  separation.leftRegistered.trans separation.rightRegistered.symm

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
is the root incidence.  Since the two germs separate at `z`, they use two
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
germs are all incidences of `z`.  Consequently the switch support `S_z` has no
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

/-! ## The switch support's declared reading, and absorption

`def:typeA-continuation-classes`: the switch support `S_z` is the finite
connected support consisting of the common prefix, the two connector tails, the
two receiver-entry channels, the completion-port boundary datum and the declared
supports of the two response coordinates; and `z` is *absorbed* when the
response identification on it is target-defective, target-complete on a
nontrivial response quotient, or target-complete only after adjoining a larger
connected support.

The reading is presented the way every declared reading in this framework is:
one labelled boundary, and the retained coordinate sets read on it, so the two
realizations of the identification are `state (base \ identified)` and
`state base`.  The `fibre` clause is `def:boundaried-gluing`'s bookkeeping for
that presentation: with no unused ambient incidence at `z` the boundary records
exactly the root incidence, the two connector tails and the two receiver-entry
channels, so the two realizations lie in one boundary-degree fibre. -/

/-- **The declared reading the switch support carries.**

The reading is presented on `S_z`'s own interface, and its realizations are
registered in `S_z`'s own generated profile certificate exactly where the
manuscript registers them: *"Assume `d_G(z)=3`. ... Consequently the switch
support `S_z` has no unused ambient incidence at `z`.  The two separated
responses **therefore** form a finite declared boundaried response state with
the same boundary-degree profile: the boundary records the root incidence, the
two connector tails to their first entries in `X`, and the two receiver-entry
channels."*  That sentence is the `registered` field, in the framework's own
registration vocabulary and against the framework's own computed certificate;
the *"same boundary-degree profile"* half is then derived below rather than
declared. -/
structure SwitchReading {support : Finset object.Vertex}
    {receiver outside : object.Vertex}
    (separation : Separation object support receiver outside) where
  /-- The declared coordinate universe of `S_z`. -/
  Coordinate : Type u
  /-- The reading: a retained coordinate set presented on `S_z`'s interface. -/
  state : Finset Coordinate → Graph.BoundaryPiece separation.interface
  /-- The coordinate set before the identification. -/
  base : Finset Coordinate
  /-- The coordinate set the identification leaves: the two separated response
  coordinates have been identified, so at least one is forgotten. -/
  reduced : Finset Coordinate
  /-- The identification forgets coordinates of the base, and it forgets
  something -- the two separated response coordinates are distinct, which is
  what makes the quotient nontrivial. -/
  reduced_ssubset : reduced ⊂ base
  /-- **The manuscript's step where `z` is internal to `S_z`.**  Off the
  interface of `S_z` the identification of two declared coordinates cannot move
  an interface label, so every realization of the reading is a finite declared
  boundaried state in `S_z`'s own registered fibre.  The premise is a decidable
  property of the residual's own `cutBoundary`, discharged on the branch by
  `Separation.separator_notMem_cutBoundary`; it is not an assumption a caller
  chooses. -/
  registered :
    separation.separator ∉
      Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
        separation.switchSupport →
    ∀ retained : Finset Coordinate, retained ⊆ base →
      (state retained).boundaryDegreeProfile =
        separation.certificate.boundaryDegreeProfile
  /-- **The realization before the identification is `S_z` itself.**  A reading
  *of* the switch support reads that support: with no coordinate yet forgotten,
  the declared boundaried state is the atom's own piece.  This is what makes the
  identification a compression *of `S_z`* rather than of an unrelated piece. -/
  baseIsPiece : state base = separation.atom.decomposition.piece
  /-- **The identification descends.**  Forgetting a coordinate strictly shrinks
  the glued realization, exactly as `Graph/ColdCorridor.lean`'s bounded germ
  descends on the sign of its own increment; `lem:replacement`'s compression is
  nontrivial for this reason and not by declaration. -/
  descends :
    (Graph.glue (state reduced)
      separation.atom.decomposition.outside).vertexCount < object.vertexCount

namespace SwitchReading

variable {support : Finset object.Vertex} {receiver outside : object.Vertex}
variable {separation : Separation object support receiver outside}
variable (reading : SwitchReading separation)

/-- The realization after the identification. -/
def quotient : Graph.BoundaryPiece separation.interface :=
  reading.state reading.reduced

/-- The realization before it. -/
def full : Graph.BoundaryPiece separation.interface :=
  reading.state reading.base

/-- **The two realizations lie in one boundary-degree fibre, derived.**

*"The two separated responses therefore form a finite declared boundaried
response state **with the same boundary-degree profile**."*  Both realizations
are registered in `S_z`'s one generated certificate, so the equality is read
off the registration; it is `lem:degree-profile-fibres` at node `[11]`, the same
fact `Separation.sameFibre` reads for the two coordinates, and it is not
restated. -/
theorem fibre
    (internal : separation.separator ∉
      Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
        separation.switchSupport) :
    reading.quotient.boundaryDegreeProfile =
      reading.full.boundaryDegreeProfile :=
  (reading.registered internal reading.reduced
      reading.reduced_ssubset.subset).trans
    (reading.registered internal reading.base (subset_refl _)).symm

end SwitchReading

/-- **The compressed realization is lexicographically smaller**, derived from
the reading's own descent by the framework's vertex-count comparison -- the same
step `ColdCorridor.BoundedGerm.lexicographicallySmaller_of_increment_neg`
makes. -/
theorem SwitchReading.lexicographicallySmaller
    {support : Finset object.Vertex} {receiver outside : object.Vertex}
    {separation : Separation object support receiver outside}
    (reading : SwitchReading separation) :
    (Graph.glue reading.quotient
        separation.atom.decomposition.outside).LexicographicallySmaller object :=
  FiniteObject.lexicographicallySmaller_of_vertexCount_lt reading.descends

/-- **`def:typeA-continuation-classes`: the separator is absorbed.**

The response identification on the switch support is target-defective — which
is exit `(4)` — or target-complete on a nontrivial response quotient — exit
`(5)` — or target-complete only after adjoining a larger connected support —
exit `(6)`.  The third alternative is carried as a declared property of the
switch, because it is a statement about supports strictly larger than `S_z`. -/
def Absorbed {support : Finset object.Vertex} {receiver outside : object.Vertex}
    {separation : Separation object support receiver outside}
    (Target : FiniteObject.{u} → Prop)
    (reading : SwitchReading separation)
    (Enlarges : Prop) : Prop :=
  Graph.Response.TargetDefect Target reading.quotient reading.full ∨
    Graph.Response.TargetComplete Graph.BoundaryPiece.boundaryDegreeProfile
        Target reading.quotient reading.full ∨
      Enlarges

/-- **`z` is surviving**: it is not absorbed. -/
def Surviving {support : Finset object.Vertex} {receiver outside : object.Vertex}
    {separation : Separation object support receiver outside}
    (Target : FiniteObject.{u} → Prop)
    (reading : SwitchReading separation)
    (Enlarges : Prop) : Prop :=
  ¬ Absorbed Target reading Enlarges

/-- **A separator with no unused ambient incidence is absorbed.**

*"Consider the quotient that identifies the two separated response coordinates
on this finite state.  If some compatible outside context distinguishes the two
responses, the quotient is target-defective ..., which is exit (4).  Otherwise
the identification is target-complete."*

`lem:context-universality`'s exhaustiveness is
`Response.contextEquivalent_or_targetDefect`; the boundary-degree half of
target-completeness is the reading's `fibre` clause at the exhausted
separator. -/
theorem absorbed_of_internal {support : Finset object.Vertex}
    {receiver outside : object.Vertex}
    {separation : Separation object support receiver outside}
    (Target : FiniteObject.{u} → Prop)
    (reading : SwitchReading separation)
    (Enlarges : Prop)
    (internal : separation.separator ∉
      Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
        separation.switchSupport) :
    Absorbed Target reading Enlarges := by
  rcases Graph.Response.contextEquivalent_or_targetDefect Target
      reading.quotient reading.full with equivalent | defect
  · exact Or.inr (Or.inl ⟨reading.fibre internal, equivalent⟩)
  · exact Or.inl defect

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
    {reading : SwitchReading separation}
    {Enlarges : Prop} (surviving : Surviving Target reading Enlarges) :
    3 < object.degree separation.separator := by
  classical
  by_cases internal : separation.separator ∉
      Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
        separation.switchSupport
  · exact absurd (absorbed_of_internal Target reading Enlarges internal)
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
    (reading : SwitchReading separation)
    (Enlarges : Prop) :
    Absorbed Target reading Enlarges ∨ Surviving Target reading Enlarges := by
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

/-! ## `lem:decorated-fan-admissibility` -/

/-- **The Type B fan-envelope data a decorated handoff carries.**

`lem:decorated-fan-admissibility`: *"contextual dyadic-safety, a `P₁₃`-free
empty-`3`-core remainder core, hereditary target-uncompressibility of the
decorated boundaried profile, and fan-return-safety at every decoration."*

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
