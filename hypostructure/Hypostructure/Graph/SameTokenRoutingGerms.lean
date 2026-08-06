import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.DeclaredCoordinateSignature
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic

/-!
# Same-token routing germs

`def:same-token-routing-germs`.

The definition has two halves.  The first builds the routing support `Z(π;t,r)`
by `def:declared-coordinate-signature` from the capacity token `t`, the
canonical blocker `Φ_can(π)`, the selected port supports `T(p), T(q)` and the
canonical response supports `Γ(p), Γ(q)`; defines a *routing germ* as a declared
connector germ inside `Z(π;t,r)` running from the primitive carrier of `t` to
`T(p)` or `T(q)`; defines the *first separator* of two germs with a maximal
common initial segment that then leave through two distinct next incidences as
the last vertex of that segment; and calls two germs *parallel* when no such
vertex exists before both enter the same declared selected-port support with the
same endpoint label.  All of that is below: `routingSupport` is the (D8) product
of the six declared entries, and `Coordinate.support_product` is why its support
is their union.

The second half is the routing-label alphabet:

> The *routing label* of a pair in `Π_{t,r}` records the same-token role `r`,
> the subtype of `t`, the ordered endpoint of the pair under discussion, the
> local open/triangular status of the corresponding selected ports, the
> boundary-degree profile of the bounded port supports `T(p),T(q)`, the
> `P₁₃`-label entries appearing in the bounded part of the support, and the
> suppressed-chord flag when the blocker has type (f).  These labels form a
> finite set; denote its cardinality by `Q_geom`.

That is a declared tuple of finite coordinates, and it is stated exactly below:
`RoutingLabel` is the tuple, `geometricLabelBound` is `Fintype.card` of it, and
`geometricPatternBound` is `L_geom = Q_geom + 1`.  The two coordinates whose
alphabets are declared elsewhere -- the boundary-degree profile and the `P₁₃`
label -- are parameters, exactly as `Role` leaves the blocker clause list to
`def:surplus-blockers`.

One consequence of the alphabet is also stated: the pigeonhole step that opens
the proof of `lem:same-token-bottleneck-routing`, "since there are only
`Q_geom` routing labels, two distinct edges of the pattern have the same routing
label".  It holds of any label map, and the manuscript's `ρ`-style label is one.
The rest of that lemma is *not* stated: its remaining steps are the germ
dichotomy, which needs the germs, and the reading of each configuration as an
exit or as decorated fan data, which needs `def:named-surplus-exits` and
`def:decorated-fan-envelope` as live alternatives.
-/

namespace Hypostructure.Graph.SameTokenRoutingGerms

open Hypostructure.Graph.SameTokenBlockerRoles

universe u v

/-- The local status of a selected surplus port: its two shoulders are
nonadjacent (*open*) or adjacent (*triangular*).  This is the dichotomy
`lem:sparse-port-activation` splits on. -/
inductive PortStatus
  | openPort
  | triangular
deriving DecidableEq, Fintype, Repr

/-- **The routing-label alphabet of `def:same-token-routing-germs`.**

The seven coordinates the manuscript records, in its order: the same-token role
`r`; the subtype of `t`; the ordered endpoint of the pair under discussion; the
open/triangular status of the two selected ports; the boundary-degree profile of
the two bounded port supports `T(p), T(q)`; the `P₁₃`-label entries appearing in
the bounded part of the support; and the suppressed-chord flag, which is
meaningful when the blocker has type (f).

The profile and window-label alphabets are parameters: they are declared by
`def:declared-coordinate-signature` and by the `P₁₃` labelling, not here.  What
the manuscript needs of them is that they are finite, and that is what is
required of them here. -/
abbrev RoutingLabel (BoundaryProfile WindowLabel : Type) : Type :=
  Role × TokenSubtype × Fin 2 × (PortStatus × PortStatus) ×
    (BoundaryProfile × BoundaryProfile) × WindowLabel × Bool

/-- **`Q_geom`**: the cardinality of a declared routing-label alphabet.

The manuscript's *"These labels form a finite set; denote its cardinality by
`Q_geom`"* is a statement about the *registered* declared-coordinate signature,
not about any one object, so the alphabet enters as one finite type and this is
its count.  `RoutingLabel` above is what a presentation builds that type with;
`labelBound` at it is the seven-coordinate count. -/
def labelBound (Label : Type) [Fintype Label] : Nat := Fintype.card Label

/-- **`L_geom := Q_geom + 1`** at a declared routing-label alphabet. -/
def patternBound (Label : Type) [Fintype Label] : Nat := labelBound Label + 1

theorem one_le_patternBound (Label : Type) [Fintype Label] :
    1 ≤ patternBound Label := Nat.le_add_left 1 _

/-- **`Q_geom`** at the seven-coordinate tuple built from the two alphabets the
manuscript leaves to `def:declared-coordinate-signature` and to the `P₁₃`
labelling. -/
def geometricLabelBound (BoundaryProfile WindowLabel : Type)
    [Fintype BoundaryProfile] [Fintype WindowLabel] : Nat :=
  labelBound (RoutingLabel BoundaryProfile WindowLabel)

/-- **`L_geom := Q_geom + 1`** of `thm:homogeneous-overload-geometric-closure`,
at the counted routing-label alphabet.  This is
`SameTokenBlockerRoles.geometricPatternBound` with its argument actually
supplied, which is the only reading under which it is `L_geom`. -/
def geometricPatternBound (BoundaryProfile WindowLabel : Type)
    [Fintype BoundaryProfile] [Fintype WindowLabel] : Nat :=
  SameTokenBlockerRoles.geometricPatternBound
    (geometricLabelBound BoundaryProfile WindowLabel)

theorem geometricPatternBound_eq (BoundaryProfile WindowLabel : Type)
    [Fintype BoundaryProfile] [Fintype WindowLabel] :
    geometricPatternBound BoundaryProfile WindowLabel =
      geometricLabelBound BoundaryProfile WindowLabel + 1 := rfl

theorem one_le_geometricPatternBound (BoundaryProfile WindowLabel : Type)
    [Fintype BoundaryProfile] [Fintype WindowLabel] :
    1 ≤ geometricPatternBound BoundaryProfile WindowLabel := by
  simp [geometricPatternBound, SameTokenBlockerRoles.geometricPatternBound]

/-- **The pigeonhole step of `lem:same-token-bottleneck-routing`.**

"Since there are only `Q_geom` routing labels, two distinct edges
`π₁, π₂ ∈ 𝓜` have the same routing label."  The step holds of any label map,
and the manuscript's is one.

This is the only step of that lemma stated in this tree.  What follows it there
-- taking the two routing germs, splitting on parallel versus a first separator,
and reading each configuration as a sparse surplus exit or as decorated Type B
handoff data -- needs the germs of `Z(π;t,r)` and needs
`def:named-surplus-exits` and `def:decorated-fan-envelope` to be live
alternatives.  None of those exists here. -/
theorem exists_same_routingLabel {Pattern : Type v} [DecidableEq Pattern]
    {Label : Type} [Fintype Label] [DecidableEq Label]
    (pattern : Finset Pattern) (label : Pattern → Label)
    (large : labelBound Label < pattern.card) :
    ∃ first ∈ pattern, ∃ second ∈ pattern,
      first ≠ second ∧ label first = label second := by
  classical
  refine Finset.exists_ne_map_eq_of_card_lt_of_maps_to ?_
    (fun member _ => Finset.mem_univ (label member))
  rwa [Finset.card_univ, ← labelBound]

end Hypostructure.Graph.SameTokenRoutingGerms

/-! ## `Z(π;t,r)`, the routing support

"the finite support generated by the declared signature
`def:declared-coordinate-signature` from the following data: the capacity token
`t`, the canonical blocker `Φ_can(π)`, the selected port supports `T(p), T(q)`,
and the canonical response supports `Γ(p), Γ(q)`."

The six entries are declared coordinates of the kinds their clauses name -- the
token, the blocker and the two selected ports are (D7) sparse surplus data, and
the two canonical response supports are (D5) trace data -- and `Z(π;t,r)` is the
support of their (D8) product, which clause (D8) makes the union of theirs. -/

open Hypostructure.Graph.DeclaredSignature

variable {Item : Type u} {Label : Type v} [DecidableEq Item]

/-- The declared coordinate `Z(π;t,r)` is generated from. -/
def routingCoordinate (label : Label)
    (tokenCarrier blocker selectedP selectedQ responseP responseQ : Finset Item) :
    Coordinate Item Label :=
  .product (.base .sparseSurplus label tokenCarrier)
    (.product (.base .sparseSurplus label blocker)
      (.product (.base .sparseSurplus label selectedP)
        (.product (.base .sparseSurplus label selectedQ)
          (.product (.base .typeATrace label responseP)
            (.base .typeATrace label responseQ)))))

/-- **`Z(π;t,r)`**: the finite support the declared signature generates. -/
def routingSupport (label : Label)
    (tokenCarrier blocker selectedP selectedQ responseP responseQ : Finset Item) :
    Finset Item :=
  (routingCoordinate label tokenCarrier blocker selectedP selectedQ responseP
    responseQ).support

/-- Clause (D8): the support is the union of the supports of the entries used. -/
theorem routingSupport_eq (label : Label)
    (tokenCarrier blocker selectedP selectedQ responseP responseQ : Finset Item) :
    routingSupport label tokenCarrier blocker selectedP selectedQ responseP
        responseQ =
      tokenCarrier ∪ (blocker ∪ (selectedP ∪ (selectedQ ∪
        (responseP ∪ responseQ)))) := rfl

/-! ## Routing germs, first separators, and parallelism -/

/-- **A routing germ of `π` at `t`**: a declared connector germ inside
`Z(π;t,r)` which starts at the primitive carrier of `t` and ends at one of the
two selected port supports. -/
structure RoutingGerm (Item : Type u) [DecidableEq Item] (support : Finset Item)
    (carrier : Item) (selected : Finset Item) where
  /-- The declared connector germ, as the items it visits in order. -/
  path : List Item
  /-- It starts at the primitive carrier of `t`. -/
  issued : path.head? = some carrier
  /-- It runs inside the routing support. -/
  inside : ∀ item ∈ path, item ∈ support
  /-- It ends at one of the two selected port supports. -/
  lands : ∃ terminal, path.getLast? = some terminal ∧ terminal ∈ selected

/-- The length of the maximal common initial segment of two germs. -/
def commonPrefixLength : List Item → List Item → Nat
  | [], _ => 0
  | _, [] => 0
  | first :: restLeft, second :: restRight =>
      if first = second then commonPrefixLength restLeft restRight + 1 else 0

/-- The maximal common initial segment itself. -/
def commonPrefix (left right : List Item) : List Item :=
  left.take (commonPrefixLength left right)

/-- **The germs leave through two distinct next incidences**: the common segment
exhausts neither of them, so each continues, and their next entries differ. -/
def Diverges (left right : List Item) : Prop :=
  commonPrefixLength left right < left.length ∧
    commonPrefixLength left right < right.length

instance (left right : List Item) : Decidable (Diverges left right) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **The first separator**: the last vertex of the maximal common initial
segment, when the germs leave through two distinct next incidences. -/
def firstSeparator (left right : List Item) : Option Item :=
  if Diverges left right then (commonPrefix left right).getLast? else none

/-- **Both germs have entered the same declared selected-port support** at or
before the end of their common segment. -/
def EnteredTogether (left right : List Item) (selected : Finset Item) : Prop :=
  ∃ item ∈ commonPrefix left right, item ∈ selected

/-- **Parallel germs**: no first separator exists before both germs enter the
same declared selected-port support. -/
def Parallel (left right : List Item) (selected : Finset Item) : Prop :=
  ¬ Diverges left right ∨ EnteredTogether left right selected

theorem commonPrefixLength_le_left : ∀ left right : List Item,
    commonPrefixLength left right ≤ left.length
  | [], _ => by simp [commonPrefixLength]
  | _ :: _, [] => by simp [commonPrefixLength]
  | first :: restLeft, second :: restRight => by
      by_cases equal : first = second
      · have := commonPrefixLength_le_left restLeft restRight
        simp only [commonPrefixLength, equal, if_pos, List.length_cons]
        omega
      · simp [commonPrefixLength, equal]

theorem length_commonPrefix (left right : List Item) :
    (commonPrefix left right).length = commonPrefixLength left right := by
  simp [commonPrefix, commonPrefixLength_le_left]

/-- Two germs issued from the same primitive carrier agree at their first item,
so their common segment is nonempty. -/
theorem commonPrefixLength_pos {left right : List Item} {carrier : Item}
    (leftIssued : left.head? = some carrier)
    (rightIssued : right.head? = some carrier) :
    0 < commonPrefixLength left right := by
  match left, right with
  | [], _ => simp at leftIssued
  | _ :: _, [] => simp at rightIssued
  | first :: restLeft, second :: restRight =>
      simp only [List.head?_cons, Option.some.injEq] at leftIssued rightIssued
      subst leftIssued
      subst rightIssued
      simp [commonPrefixLength]

/-- **The germ dichotomy of `lem:same-token-bottleneck-routing`.**  Two germs
issued from the same primitive carrier are parallel, or they have a first
separator and have not already entered the same selected-port support. -/
theorem parallel_or_firstSeparator {left right : List Item} {carrier : Item}
    (selected : Finset Item)
    (leftIssued : left.head? = some carrier)
    (rightIssued : right.head? = some carrier) :
    Parallel left right selected ∨
      ∃ separator, firstSeparator left right = some separator ∧
        ¬ EnteredTogether left right selected := by
  by_cases entered : EnteredTogether left right selected
  · exact .inl (.inr entered)
  · by_cases diverges : Diverges left right
    · refine .inr ?_
      have positive := commonPrefixLength_pos leftIssued rightIssued
      have nonempty : commonPrefix left right ≠ [] := by
        intro empty
        have := length_commonPrefix left right
        rw [empty] at this
        simp at this
        omega
      obtain ⟨separator, last⟩ := Option.ne_none_iff_exists'.mp
        (fun none => nonempty (List.getLast?_eq_none_iff.mp none))
      refine ⟨separator, ?_, entered⟩
      simp only [firstSeparator, if_pos diverges]
      exact last
    · exact .inl (.inl diverges)
