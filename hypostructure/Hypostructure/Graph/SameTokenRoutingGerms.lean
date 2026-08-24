import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.DeclaredCoordinateSignature
import Hypostructure.Graph.Object
import Hypostructure.Graph.SupportComponents
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic

/-!
# Same-token routing germs

`def:same-token-routing-germs`.

The definition has two halves.  The first builds the routing support `Z(π;t,r)`
by `def:declared-coordinate-signature` from the capacity token `t`, the
canonical blocker `Φ_can(π)`, the selected port supports `T(p), T(q)` and the
canonical returns `R_p,R_q` and response supports `Γ(p), Γ(q)`; defines a
*routing configuration* as a declared connector configuration inside
`Z(π;t,r)` running from the primitive blocker support of `t` to `T(p)` or
`T(q)`; defines the *first separator* of two configurations with a maximal
common initial segment that then leave through two
distinct next incidences as the last vertex of that segment; and calls two configurations
*parallel* when no such vertex exists before both enter the same declared
selected-port support with the same endpoint label.  The return entries are the
canonical `R_p,R_q` already carried by `def:active-surplus-demands`.  They are
essential when the canonical blocker has type (b): at an open port
`Γ(p)=Q_p` does not contain `R_p`.  Thus `routingSupport` is the (D8) product
of the eight available declared entries, and `Coordinate.support_product` is
why its support is their union.

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
This module also states the finite common-prefix dichotomy.  The selected EG
row owns the complete paper proof and must obtain the graph-derived label and
connector configurations through the declared-signature API; neither is a
parameter of this module.
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

/-- The routed seven-coordinate alphabet is counted factor by factor.  This is
the structural form of `Q_geom`; it avoids enumerating the product alphabet. -/
theorem card_routingLabel (BoundaryProfile WindowLabel : Type)
    [Fintype BoundaryProfile] [Fintype WindowLabel] :
    Fintype.card (RoutingLabel BoundaryProfile WindowLabel) =
      Fintype.card Role * Fintype.card TokenSubtype * 2 *
        (Fintype.card PortStatus * Fintype.card PortStatus) *
        (Fintype.card BoundaryProfile * Fintype.card BoundaryProfile) *
        Fintype.card WindowLabel * 2 := by
  simp only [RoutingLabel, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  ac_rfl

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

The active-family support, routing-configuration schema, and exact
parallel/first-separator dichotomy are stated below.  The sparse-exit and
decorated-Type-B readings are proved only inside the selected ExactLedger row. -/
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

namespace Hypostructure.Graph.SameTokenRoutingGerms

/-! ## `Z(π;t,r)`, the routing support

"the finite support generated by the declared signature
`def:declared-coordinate-signature` from the following data: the capacity token
`t`, the canonical blocker `Φ_can(π)`, the selected port supports `T(p), T(q)`,
the canonical returns `R_p,R_q`, and the canonical response supports
`Γ(p), Γ(q)`."

The return paths are not newly selected here.  They are clause (b) of
`lem:sparse-port-activation`, retained by `def:active-surplus-demands`, and are
also explicit (D7) canonical-return data of the declared signature.  Keeping
them in `Z` is necessary for the type-(b) blocker: for an open port the response
support is the suppression path `Q_p`, so `R_p` cannot be recovered from
`Γ(p)`.  The token, blocker, selected ports, and canonical returns are (D7)
sparse-surplus entries; the two response supports are (D5) trace entries.
`Z(π;t,r)` is the support of their (D8) product, hence their union. -/

open Hypostructure.Graph.DeclaredSignature

variable {Item : Type u} {Label : Type v} [DecidableEq Item]

/-- The declared coordinate `Z(π;t,r)` is generated from. -/
def routingCoordinate (label : Label)
    (tokenCarrier blocker selectedP selectedQ returnP returnQ responseP responseQ :
      Finset Item) :
    Coordinate Item Label :=
  .product (.base .sparseSurplus label tokenCarrier)
    (.product (.base .sparseSurplus label blocker)
      (.product (.base .sparseSurplus label selectedP)
        (.product (.base .sparseSurplus label selectedQ)
          (.product (.base .sparseSurplus label returnP)
            (.product (.base .sparseSurplus label returnQ)
              (.product (.base .typeATrace label responseP)
                (.base .typeATrace label responseQ)))))))

/-- **`Z(π;t,r)`**: the finite support the declared signature generates. -/
def routingSupport (label : Label)
    (tokenCarrier blocker selectedP selectedQ returnP returnQ responseP responseQ :
      Finset Item) :
    Finset Item :=
  (routingCoordinate label tokenCarrier blocker selectedP selectedQ returnP
    returnQ responseP responseQ).support

/-- Clause (D8): the support is the union of the supports of the entries used. -/
theorem routingSupport_eq (label : Label)
    (tokenCarrier blocker selectedP selectedQ returnP returnQ responseP responseQ :
      Finset Item) :
    routingSupport label tokenCarrier blocker selectedP selectedQ returnP returnQ
        responseP responseQ =
      tokenCarrier ∪ (blocker ∪ (selectedP ∪ (selectedQ ∪
        (returnP ∪ (returnQ ∪ (responseP ∪ responseQ)))))) := rfl

/-! ## Routing configurations, first separators, and parallelism -/

/-- **A routing configuration of `π` at `t`**, at the exact interface stated
in `def:same-token-routing-germs`: a declared connector configuration inside
`Z(π;t,r)` which starts in the primitive blocker support and ends in one of
the two selected port supports.

The source is a finite support, not a caller-selected carrier vertex.  In
particular this definition does not manufacture the common root that the proof
of `lem:same-token-bottleneck-routing` later needs; that root must be read from
the declared connector configuration supplied by the signature. -/
structure RoutingConfiguration (object : FiniteObject.{u})
    (support source selected : Finset object.Vertex) where
  /-- The declared connector configuration, as the vertices it visits in
  order. -/
  path : List object.Vertex
  /-- The connector is an actual walk in the current object. -/
  chain : path.IsChain object.graph.Adj
  /-- The declared connector is simple. -/
  nodup : path.Nodup
  /-- It starts in the primitive blocker support of `t`. -/
  issued : ∃ initial, path.head? = some initial ∧ initial ∈ source
  /-- It runs inside the routing support. -/
  inside : ∀ item ∈ path, item ∈ support
  /-- It ends at one of the two selected port supports. -/
  lands : ∃ terminal, path.getLast? = some terminal ∧ terminal ∈ selected

/-- Read an already declared simple connector walk as a routing configuration.
This constructor does not select a walk; its `walk` argument is the connector
proved from the declared support data by the owning ledger row. -/
def RoutingConfiguration.ofWalk {object : FiniteObject.{u}}
    {support source selected : Finset object.Vertex}
    {root terminal : object.Vertex}
    (walk : object.graph.Walk root terminal)
    (isPath : walk.IsPath)
    (rootSource : root ∈ source)
    (inside : ∀ item ∈ walk.support, item ∈ support)
    (terminalSelected : terminal ∈ selected) :
    RoutingConfiguration object support source selected where
  path := walk.support
  chain := walk.isChain_adj_support
  nodup := isPath.support_nodup
  issued := ⟨root, by
    rw [List.head?_eq_some_head walk.support_ne_nil, walk.head_support],
    rootSource⟩
  inside := inside
  lands := ⟨terminal, by
    rw [List.getLast?_eq_getLast_of_ne_nil walk.support_ne_nil,
      walk.getLast_support], terminalSelected⟩

/-- A connected declared sub-support containing the root and a selected-port
vertex supplies a connector configuration in every larger declared support.
The witness walk is the one carried by `ConnectedOn`; this theorem introduces
no path selector or additional support. -/
theorem exists_routingConfiguration_of_connectedOn
    {object : FiniteObject.{u}}
    {support connector source selected : Finset object.Vertex}
    {root : object.Vertex}
    (connected : SupportComponents.Connected.ConnectedOn object connector)
    (rootMem : root ∈ connector)
    (rootSource : root ∈ source)
    (selectedNonempty : selected.Nonempty)
    (selectedSubset : selected ⊆ connector)
    (connectorSubset : connector ⊆ support) :
    ∃ configuration : RoutingConfiguration object support source selected,
      configuration.path.head? = some root := by
  obtain ⟨terminal, terminalSelected⟩ := selectedNonempty
  obtain ⟨walk, isPath, inside⟩ :=
    connected.2 rootMem (selectedSubset terminalSelected)
  let configuration := RoutingConfiguration.ofWalk walk isPath rootSource
    (fun item member => connectorSubset (inside item member)) terminalSelected
  exact ⟨configuration, by
    change walk.support.head? = some root
    rw [List.head?_eq_some_head walk.support_ne_nil, walk.head_support]⟩

/-- The finite vertex support of an existing walk is connected in the ambient
object. -/
theorem connectedOn_walkSupport {object : FiniteObject.{u}}
    [DecidableEq object.Vertex]
    {start finish : object.Vertex}
    (walk : object.graph.Walk start finish) :
    SupportComponents.Connected.ConnectedOn object walk.support.toFinset := by
  classical
  constructor
  · exact ⟨start, by simp⟩
  · intro left right leftMem rightMem
    have leftOnWalk : left ∈ walk.support := by simpa using leftMem
    have rightOnWalk : right ∈ walk.support := by simpa using rightMem
    let leftPart := (walk.takeUntil left leftOnWalk).reverse
    let rightPart := walk.takeUntil right rightOnWalk
    let joined := leftPart.append rightPart
    let path := joined.toPath
    refine ⟨path, path.isPath, ?_⟩
    intro vertex vertexMem
    have inJoined : vertex ∈ joined.support :=
      SimpleGraph.Walk.support_toPath_subset_support joined vertexMem
    rw [SimpleGraph.Walk.mem_support_append_iff] at inJoined
    rcases inJoined with inLeft | inRight
    · have inTaken : vertex ∈ (walk.takeUntil left leftOnWalk).support := by
        simpa [leftPart, SimpleGraph.Walk.support_reverse] using inLeft
      exact List.mem_toFinset.mpr
        (walk.support_takeUntil_subset_support leftOnWalk inTaken)
    · exact List.mem_toFinset.mpr
        (walk.support_takeUntil_subset_support rightOnWalk inRight)

/-- Two connected declared supports with a common vertex have connected union.
This is the support-level gluing used for `X_π` and the already canonical
return supports `R_p`. -/
theorem connectedOn_union_of_common
    {object : FiniteObject.{u}} [DecidableEq object.Vertex]
    {left right : Finset object.Vertex}
    (leftConnected : SupportComponents.Connected.ConnectedOn object left)
    (rightConnected : SupportComponents.Connected.ConnectedOn object right)
    {common : object.Vertex} (commonLeft : common ∈ left)
    (commonRight : common ∈ right) :
    SupportComponents.Connected.ConnectedOn object (left ∪ right) := by
  classical
  constructor
  · obtain ⟨vertex, member⟩ := leftConnected.1
    exact ⟨vertex, Finset.mem_union_left _ member⟩
  · intro first second firstMem secondMem
    rcases Finset.mem_union.mp firstMem with firstLeft | firstRight <;>
      rcases Finset.mem_union.mp secondMem with secondLeft | secondRight
    · obtain ⟨walk, path, inside⟩ := leftConnected.2 firstLeft secondLeft
      exact ⟨walk, path, fun vertex member =>
        Finset.mem_union_left _ (inside vertex member)⟩
    · obtain ⟨toCommon, _, insideLeft⟩ :=
        leftConnected.2 firstLeft commonLeft
      obtain ⟨fromCommon, _, insideRight⟩ :=
        rightConnected.2 commonRight secondRight
      let joined := toCommon.append fromCommon
      let path := joined.toPath
      refine ⟨path, path.isPath, ?_⟩
      intro vertex member
      have inJoined : vertex ∈ joined.support :=
        SimpleGraph.Walk.support_toPath_subset_support joined member
      rw [SimpleGraph.Walk.mem_support_append_iff] at inJoined
      exact inJoined.elim
        (fun inside => Finset.mem_union_left _ (insideLeft vertex inside))
        (fun inside => Finset.mem_union_right _ (insideRight vertex inside))
    · obtain ⟨toCommon, _, insideRight⟩ :=
        rightConnected.2 firstRight commonRight
      obtain ⟨fromCommon, _, insideLeft⟩ :=
        leftConnected.2 commonLeft secondLeft
      let joined := toCommon.append fromCommon
      let path := joined.toPath
      refine ⟨path, path.isPath, ?_⟩
      intro vertex member
      have inJoined : vertex ∈ joined.support :=
        SimpleGraph.Walk.support_toPath_subset_support joined member
      rw [SimpleGraph.Walk.mem_support_append_iff] at inJoined
      exact inJoined.elim
        (fun inside => Finset.mem_union_right _ (insideRight vertex inside))
        (fun inside => Finset.mem_union_left _ (insideLeft vertex inside))
    · obtain ⟨walk, path, inside⟩ := rightConnected.2 firstRight secondRight
      exact ⟨walk, path, fun vertex member =>
        Finset.mem_union_right _ (inside vertex member)⟩

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

/-- **Parallel germs**: both configurations enter the same declared
selected-port support along their common initial segment.  In the routing
lemma the two configurations already have the same endpoint label, so this is
exactly the manuscript's parallel alternative. -/
def Parallel (left right : List Item) (selected : Finset Item) : Prop :=
  EnteredTogether left right selected

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

theorem commonPrefixLength_le_right : ∀ left right : List Item,
    commonPrefixLength left right ≤ right.length
  | [], _ => by simp [commonPrefixLength]
  | _ :: _, [] => by simp [commonPrefixLength]
  | first :: restLeft, second :: restRight => by
      by_cases equal : first = second
      · have := commonPrefixLength_le_right restLeft restRight
        simp only [commonPrefixLength, equal, if_pos, List.length_cons]
        omega
      · simp [commonPrefixLength, equal]

/-- The maximal common prefix is equally the corresponding prefix of the right
configuration; `commonPrefix` chooses the left presentation only to avoid
quotienting lists by this equality. -/
theorem take_commonPrefixLength_eq : ∀ left right : List Item,
    left.take (commonPrefixLength left right) =
      right.take (commonPrefixLength left right)
  | [], right => by simp [commonPrefixLength]
  | left, [] => by cases left <;> simp [commonPrefixLength]
  | first :: restLeft, second :: restRight => by
      by_cases equal : first = second
      · subst second
        simp only [commonPrefixLength, if_pos, List.take_succ_cons,
          List.cons.injEq, true_and]
        exact take_commonPrefixLength_eq restLeft restRight
      · simp [commonPrefixLength, equal]

theorem commonPrefix_eq_right_take (left right : List Item) :
    commonPrefix left right = right.take (commonPrefixLength left right) := by
  exact take_commonPrefixLength_eq left right

theorem length_commonPrefix (left right : List Item) :
    (commonPrefix left right).length = commonPrefixLength left right := by
  simp [commonPrefix, commonPrefixLength_le_left]

/-- A list is its whole common prefix with any extension of itself. -/
theorem commonPrefixLength_append_left (left suffix : List Item) :
    commonPrefixLength left (left ++ suffix) = left.length := by
  induction left with
  | nil => simp [commonPrefixLength]
  | cons head tail ih =>
      simp [commonPrefixLength, ih]

/-- Prefix-comparable configurations do not diverge at a first separator. -/
theorem not_diverges_of_isPrefix {left right : List Item}
    (prefixed : left <+: right) : ¬ Diverges left right := by
  obtain ⟨suffix, rfl⟩ := prefixed
  rw [Diverges, commonPrefixLength_append_left]
  simp

/-- The symmetric prefix-comparable case also cannot diverge. -/
theorem not_diverges_of_isPrefix_right {left right : List Item}
    (prefixed : right <+: left) : ¬ Diverges left right := by
  obtain ⟨suffix, rfl⟩ := prefixed
  have common : commonPrefixLength (right ++ suffix) right = right.length := by
    induction right with
    | nil => cases suffix <;> rfl
    | cons head tail ih =>
        simp [commonPrefixLength, ih]
  rw [Diverges, common]
  simp

/-- Two configurations issued from the same root agree at their first item,
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

/-- Two finite connector configurations with the same declared root are
parallel, or have a first separator before entering their common selected-port
support.  The same-root hypotheses are deliberately explicit: selecting that
root is data of the paper's declared connector configurations, not a
consequence of two arbitrary lists. -/
theorem parallel_or_firstSeparator_of_same_root
    {left right : List Item} {root : Item}
    (selected : Finset Item)
    (leftIssued : left.head? = some root)
    (rightIssued : right.head? = some root)
    (leftLands : ∃ terminal, left.getLast? = some terminal ∧ terminal ∈ selected)
    (rightLands : ∃ terminal, right.getLast? = some terminal ∧ terminal ∈ selected) :
    Parallel left right selected ∨
      ∃ separator, firstSeparator left right = some separator ∧
        ¬ EnteredTogether left right selected := by
  by_cases entered : EnteredTogether left right selected
  · exact .inl entered
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
    · have exhausted : commonPrefixLength left right = left.length ∨
          commonPrefixLength left right = right.length := by
        have leftBound := commonPrefixLength_le_left left right
        have rightBound := commonPrefixLength_le_right left right
        simp only [Diverges] at diverges
        omega
      apply False.elim
      apply entered
      rcases exhausted with leftExhausted | rightExhausted
      · obtain ⟨terminal, terminalLast, terminalSelected⟩ := leftLands
        have terminalMem : terminal ∈ left := by
          obtain ⟨initial, rfl⟩ := List.getLast?_eq_some_iff.mp terminalLast
          simp
        refine ⟨terminal, ?_, terminalSelected⟩
        simpa [commonPrefix, leftExhausted] using terminalMem
      · obtain ⟨terminal, terminalLast, terminalSelected⟩ := rightLands
        have terminalMem : terminal ∈ right := by
          obtain ⟨initial, rfl⟩ := List.getLast?_eq_some_iff.mp terminalLast
          simp
        refine ⟨terminal, ?_, terminalSelected⟩
        rw [commonPrefix_eq_right_take, rightExhausted, List.take_length]
        exact terminalMem

end Hypostructure.Graph.SameTokenRoutingGerms
