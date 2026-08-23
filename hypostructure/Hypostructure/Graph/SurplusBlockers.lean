import Hypostructure.Graph.PortResponseSupport
import Hypostructure.Graph.PrimitiveCarrier
import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.SparsePairLedger

/-!
# The six concrete clauses of `def:surplus-blockers`

> A *sparse surplus blocker* for an unordered pair `{p,q} ⊆ 𝒜₀` is one of the
> following concrete objects.
> (a) a vertex or edge-incidence contained in both declared demand supports
> `(T(p) ∪ Γ(p)) ∩ (T(q) ∪ Γ(q))`;
> (b) a common vertex or common edge-incidence of the two canonical return paths
> `R_p` and `R_q`;
> (c) a common shoulder endpoint or shared cubic buffer vertex among
> `{a_p, b_p, x(p), a_q, b_q, x(q)}`;
> (d) a boundary-degree-profile coordinate which prevents a quotient or
> replacement from staying in a single fibre;
> (e) a target-response coordinate witnessing a target-defective quotient,
> target-complete compression, or delocalization event;
> (f) an arithmetic chord-set obstruction from a suppressed open-port family,
> namely the concrete set `𝒮` of added shoulder chords.
>
> The blocker must be an object explicitly listed above.  A pair is not declared
> blocked merely because the proof has not found a closure; its failed
> compatibility must be represented by a finite-capacity object of one of these
> six types.

The closing paragraph is the reason this module exists.  `Graph/SparsePairLedger`
already carries `def:canonical-blocker-ledger` at an *arbitrary* applicability
relation, which is the generality
`lem:canonical-blocker-ledger-no-overcount` is proved in; what was missing is
the manuscript's own relation, so that `Π_blk` is the set of pairs carrying a
*finite-capacity object* rather than the set of pairs standing in some quantified
relation.

`Blocker` below is that object: one constructor per clause, each carrying the
witness the clause names.  `DemandActivation` is the canonical data
`def:active-surplus-demands` equips a selected port with, in the concrete finite
form the clauses intersect: `T(p) ∪ Γ(p)` for (a), `R_p` for (b), and
`{a_p, b_p, x(p)}` for (c).  Clauses (d), (e) and (f) are not port data — they
are the coordinates and chord sets a *failed* quotient produces — so the
activation carries them as the pair-indexed finite families the dependence
lemmas hand back.

`blockers π` is `𝖡𝗅𝗄(π)`, a genuine `Finset` of these objects, and `Blocks` is
its per-clause reading.  Feeding `Blocks` to `FiniteObject.chargedPairs` at
`canonicalBlockerOrder` instantiates `def:canonical-blocker-ledger`: `Π_blk` is
the pairs with a blocker, `Φ_can` is the first clause of the declared order that
supplies one, and the no-overcount identity is the one already proved.

An item of clauses (a) and (b) is a vertex or an edge-incidence, which are the
first two summands of `def:primitive-sparse-blocker-carrier`'s `𝔘_sp(G)`; that
is why the primitive carrier is the token class those clauses charge to.
-/

namespace Hypostructure.Graph

universe u v

namespace FiniteObject

variable {object : FiniteObject.{u}}

/-! ## The blocker objects -/

/-- **A vertex or an edge-incidence**: the item type clauses (a) and (b) name.
These are the first two summands of `def:primitive-sparse-blocker-carrier`'s
`𝔘_sp(G) = V(G) ⊔ I_E(G) ⊔ 𝒫_exc`, which is what makes them finite-capacity. -/
inductive CarrierItem (object : FiniteObject.{u}) where
  /-- A vertex of `G`. -/
  | vertex (v : object.Vertex)
  /-- An edge-incidence `(e, v)`, recorded as the ordered adjacent pair. -/
  | incidence (pair : object.Vertex × object.Vertex)

/-- **A sparse surplus blocker**, one constructor per clause of
`def:surplus-blockers`.  The type has no other constructor: that is the
manuscript's "the blocker must be an object explicitly listed above".

`Coordinate` is the declared-coordinate alphabet of
`def:declared-coordinate-signature` that clauses (d) and (e) draw from, and
`Chord` is the shoulder-chord alphabet clause (f)'s set `𝒮` is a set of. -/
inductive Blocker (object : FiniteObject.{u}) (Coordinate Chord : Type v) where
  /-- (a) a vertex or edge-incidence in both declared demand supports. -/
  | sharedDeclaredSupport (item : CarrierItem object)
  /-- (b) a common vertex or edge-incidence of the two canonical returns. -/
  | sharedReturnSupport (item : CarrierItem object)
  /-- (c) a common shoulder endpoint or shared cubic buffer vertex. -/
  | sharedLocalBuffer (vertex : object.Vertex)
  /-- (d) a boundary-degree-profile coordinate. -/
  | boundaryProfile (coordinate : Coordinate)
  /-- (e) a target-response coordinate. -/
  | targetResponse (coordinate : Coordinate)
  /-- (f) an arithmetic chord-set obstruction: the concrete set `𝒮`. -/
  | arithmeticChordSet (chords : Finset Chord)

namespace Blocker

variable {Coordinate Chord : Type v}

/-- **`type(B)`**: the clause a blocker comes from, in
`SameTokenBlockerRoles.BlockerKind`'s own alphabet.  The two alphabets are the
same closed clause list (a)--(f), so the ledger's declared order
`canonicalBlockerOrder` orders these objects by their clause without a second
enumeration being written. -/
def kind : Blocker object Coordinate Chord → SameTokenBlockerRoles.BlockerKind
  | .sharedDeclaredSupport _ => .sharedDeclaredSupport
  | .sharedReturnSupport _ => .sharedReturnSupport
  | .sharedLocalBuffer _ => .sharedLocalBuffer
  | .boundaryProfile _ => .boundaryProfile
  | .targetResponse _ => .targetResponse
  | .arithmeticChordSet _ => .arithmeticChordSet

end Blocker

/-! ## The canonical data a clause intersects -/

/-- **The canonical data of `def:active-surplus-demands`, in the concrete form
the six clauses read.**

Clauses (a), (b) and (c) intersect finite vertex sets of the two demands, which
`Graph/PortResponseSupport` builds canonically: `T(p) ∪ Γ(p)` is
`SurplusPort.declaredSupport`, `R_p` is `SurplusPort.returnSupport`, and
`{a_p, b_p, x(p)}` is `SurplusPort.support`.  Nothing here re-derives them; the
fields are the assignment `p ↦ (that data)` over the selected family, which is
what makes a blocker of those clauses an object of `𝔘_sp(G)`.

Clauses (d), (e) and (f) are not data of a port.  They are the coordinates and
chord sets that a *failed* quotient, replacement or suppression produces, so
they enter as the pair-indexed finite families the dependence lemmas hand back.
An empty family is the honest reading of "this pair has no obstruction of that
clause". -/
structure DemandActivation (object : FiniteObject.{u}) (Coordinate Chord : Type v)
    where
  /-- `T(p) ∪ Γ(p)`, the declared demand support of clause (a). -/
  declaredSupport : object.Vertex × object.Vertex → Finset object.Vertex
  /-- `R_p`, the canonical return path's vertices, for clause (b). -/
  returnSupport : object.Vertex × object.Vertex → Finset object.Vertex
  /-- `{a_p, b_p, x(p)}`, the shoulder endpoints and cubic buffer of clause (c). -/
  localBuffer : object.Vertex × object.Vertex → Finset object.Vertex
  /-- The boundary-degree-profile coordinates obstructing the pair, clause (d). -/
  profileObstructions : Finset (object.Vertex × object.Vertex) → Finset Coordinate
  /-- The target-response coordinates obstructing the pair, clause (e). -/
  responseObstructions : Finset (object.Vertex × object.Vertex) →
    Finset Coordinate
  /-- The arithmetic chord-set obstructions of the pair, clause (f). -/
  chordObstructions : Finset (object.Vertex × object.Vertex) →
    Finset (Finset Chord)

namespace DemandActivation

variable {Coordinate Chord : Type v}

/-- The vertices and edge-incidences contained in both of two vertex sets: the
intersection clauses (a) and (b) take, read at both summands of the carrier.  An
edge-incidence is contained in a support exactly when both of its endpoints
are. -/
noncomputable def sharedItems (object : FiniteObject.{u})
    (left right : Finset object.Vertex) : Finset (CarrierItem object) := by
  classical
  exact (left ∩ right).image CarrierItem.vertex ∪
    (object.incidences.filter fun pair =>
      pair.1 ∈ left ∧ pair.2 ∈ left ∧ pair.1 ∈ right ∧ pair.2 ∈ right).image
      CarrierItem.incidence

/-- A vertex of the intersection is a shared item: the vertex half of clauses
(a) and (b). -/
theorem vertex_mem_sharedItems {object : FiniteObject.{u}}
    {left right : Finset object.Vertex} {vertex : object.Vertex}
    (inLeft : vertex ∈ left) (inRight : vertex ∈ right) :
    CarrierItem.vertex vertex ∈ sharedItems object left right := by
  classical
  refine Finset.mem_union_left _ ?_
  exact Finset.mem_image_of_mem _ (Finset.mem_inter.2 ⟨inLeft, inRight⟩)

/-- An edge-incidence item of clauses (a) and (b) is a genuine edge-incidence of
the object: `sharedItems` filters the object's own `I_E(G)`.  This is what makes
such an item a member of `def:primitive-sparse-blocker-carrier`'s second
summand. -/
theorem incidence_mem_incidences_of_mem_sharedItems {object : FiniteObject.{u}}
    {left right : Finset object.Vertex} {pair : object.Vertex × object.Vertex}
    (member : CarrierItem.incidence pair ∈ sharedItems object left right) :
    pair ∈ object.incidences := by
  classical
  rcases Finset.mem_union.1 member with vertexSide | incidenceSide
  · obtain ⟨_, _, equality⟩ := Finset.mem_image.1 vertexSide
    cases equality
  · obtain ⟨other, filtered, equality⟩ := Finset.mem_image.1 incidenceSide
    cases equality
    exact (Finset.mem_filter.1 filtered).1

/-- The two ordered readings of an unordered demand pair.  The diagonal is
excluded: clauses (a)--(c) compare the two *distinct* active demands in
`\{p,q\}`, exactly as `def:surplus-blockers` prescribes. -/
noncomputable def distinctDemandPairs
    (pair : Finset (object.Vertex × object.Vertex)) :
    Finset ((object.Vertex × object.Vertex) ×
      (object.Vertex × object.Vertex)) := by
  classical
  exact (pair ×ˢ pair).filter fun demands => demands.1 ≠ demands.2

/-- **`𝖡𝗅𝗄(π)`**: the finite set of sparse surplus blockers of a pair.

The union of the six clauses, each read at the pair's own two demands.  Clauses
(a), (b) and (c) range over the ordered pairs of distinct members of `π`, which
is how an unordered pair supplies "the two declared supports"; the remaining
three are the obstruction families the activation carries. -/
noncomputable def blockers (activation : DemandActivation object Coordinate Chord)
    (pair : Finset (object.Vertex × object.Vertex)) :
    Finset (Blocker object Coordinate Chord) := by
  classical
  exact
    (distinctDemandPairs pair).biUnion (fun demands =>
        (sharedItems object (activation.declaredSupport demands.1)
            (activation.declaredSupport demands.2)).image
          Blocker.sharedDeclaredSupport ∪
        ((sharedItems object (activation.returnSupport demands.1)
              (activation.returnSupport demands.2)).image
            Blocker.sharedReturnSupport ∪
          ((activation.localBuffer demands.1 ∩
              activation.localBuffer demands.2).image
            Blocker.sharedLocalBuffer))) ∪
      ((activation.profileObstructions pair).image Blocker.boundaryProfile ∪
        ((activation.responseObstructions pair).image Blocker.targetResponse ∪
          (activation.chordObstructions pair).image Blocker.arithmeticChordSet))

/-- An edge-incidence blocker of clause (a) or (b) carries a genuine
edge-incidence of the object.  `def:primitive-sparse-blocker-carrier`'s
`κ(B) = B` for those clauses therefore lands in `𝔘_sp(G)`. -/
theorem incidence_mem_incidences_of_mem_blockers
    (activation : DemandActivation object Coordinate Chord)
    {pair : Finset (object.Vertex × object.Vertex)}
    {incidence : object.Vertex × object.Vertex}
    (member : Blocker.sharedDeclaredSupport (CarrierItem.incidence incidence) ∈
        activation.blockers pair ∨
      Blocker.sharedReturnSupport (CarrierItem.incidence incidence) ∈
        activation.blockers pair) :
    incidence ∈ object.incidences := by
  classical
  rcases member with declared | returned
  · rw [blockers] at declared
    rcases Finset.mem_union.1 declared with local' | remote
    · obtain ⟨_, _, inside⟩ := Finset.mem_biUnion.1 local'
      rcases Finset.mem_union.1 inside with shared | other
      · obtain ⟨item, itemMem, equality⟩ := Finset.mem_image.1 shared
        cases equality
        exact incidence_mem_incidences_of_mem_sharedItems itemMem
      · rcases Finset.mem_union.1 other with second | third
        · obtain ⟨_, _, equality⟩ := Finset.mem_image.1 second
          cases equality
        · obtain ⟨_, _, equality⟩ := Finset.mem_image.1 third
          cases equality
    · rcases Finset.mem_union.1 remote with first | rest
      · obtain ⟨_, _, equality⟩ := Finset.mem_image.1 first
        cases equality
      · rcases Finset.mem_union.1 rest with second | third
        · obtain ⟨_, _, equality⟩ := Finset.mem_image.1 second
          cases equality
        · obtain ⟨_, _, equality⟩ := Finset.mem_image.1 third
          cases equality
  · rw [blockers] at returned
    rcases Finset.mem_union.1 returned with local' | remote
    · obtain ⟨_, _, inside⟩ := Finset.mem_biUnion.1 local'
      rcases Finset.mem_union.1 inside with shared | other
      · obtain ⟨_, _, equality⟩ := Finset.mem_image.1 shared
        cases equality
      · rcases Finset.mem_union.1 other with second | third
        · obtain ⟨item, itemMem, equality⟩ := Finset.mem_image.1 second
          cases equality
          exact incidence_mem_incidences_of_mem_sharedItems itemMem
        · obtain ⟨_, _, equality⟩ := Finset.mem_image.1 third
          cases equality
    · rcases Finset.mem_union.1 remote with first | rest
      · obtain ⟨_, _, equality⟩ := Finset.mem_image.1 first
        cases equality
      · rcases Finset.mem_union.1 rest with second | third
        · obtain ⟨_, _, equality⟩ := Finset.mem_image.1 second
          cases equality
        · obtain ⟨_, _, equality⟩ := Finset.mem_image.1 third
          cases equality

/-- **`def:surplus-blockers` as the ledger's applicability relation.**

A declared clause applies to a pair exactly when the pair carries a blocker
object of that clause.  Handing this to `FiniteObject.chargedPairs` at
`canonicalBlockerOrder` is `def:canonical-blocker-ledger` at the manuscript's own
`𝖡𝗅𝗄`: `Π_blk` becomes the pairs with a blocker rather than the pairs standing
in a quantified relation. -/
def Blocks (activation : DemandActivation object Coordinate Chord)
    (kind : SameTokenBlockerRoles.BlockerKind)
    (pair : Finset (object.Vertex × object.Vertex)) : Prop :=
  ∃ blocker ∈ activation.blockers pair, blocker.kind = kind

/-- The blocker relation is decidable: `𝖡𝗅𝗄(π)` is a finite set and `kind` is a
function into a finite alphabet with decidable equality. -/
noncomputable instance decidableBlocks
    (activation : DemandActivation object Coordinate Chord)
    (kind : SameTokenBlockerRoles.BlockerKind)
    (pair : Finset (object.Vertex × object.Vertex)) :
    Decidable (activation.Blocks kind pair) := by
  classical
  unfold Blocks
  infer_instance

/-- **A pair is blocked exactly when it carries a blocker object.**

This is the manuscript's closing paragraph made into a theorem: the ledger's
`Π_blk` is `{π : 𝖡𝗅𝗄(π) ≠ ∅}`, so no pair is charged for want of a closure, and
every charged pair exhibits a finite-capacity object of one of the six types. -/
theorem exists_blocks_iff_blockers_nonempty
    (activation : DemandActivation object Coordinate Chord)
    (pair : Finset (object.Vertex × object.Vertex)) :
    (∃ kind, activation.Blocks kind pair) ↔ (activation.blockers pair).Nonempty := by
  constructor
  · rintro ⟨_kind, blocker, member, _⟩
    exact ⟨blocker, member⟩
  · rintro ⟨blocker, member⟩
    exact ⟨blocker.kind, blocker, member, rfl⟩

/-- Every clause of the declared order is one of the closed clause list, so a
blocked pair always has a canonical blocker: `Φ_can(π)` is defined on all of
`Π_blk`. -/
theorem blocks_mem_canonicalBlockerOrder
    (activation : DemandActivation object Coordinate Chord)
    {kind : SameTokenBlockerRoles.BlockerKind}
    {pair : Finset (object.Vertex × object.Vertex)}
    (_blocked : activation.Blocks kind pair) :
    kind ∈ SameTokenBlockerRoles.canonicalBlockerOrder :=
  SameTokenBlockerRoles.mem_canonicalBlockerOrder kind

/-! ## The clause introductions

Each of the six clauses is stated as the manuscript states it, so a node that
finds the concrete obstruction records the blocker without knowing how
`blockers` is assembled. -/

/-- **Clause (a).**  A vertex in both declared demand supports blocks the pair. -/
theorem blocks_sharedDeclaredSupport
    (activation : DemandActivation object Coordinate Chord)
    {pair : Finset (object.Vertex × object.Vertex)}
    {left right : object.Vertex × object.Vertex}
    (leftMem : left ∈ pair) (rightMem : right ∈ pair)
    (distinct : left ≠ right)
    {vertex : object.Vertex}
    (inLeft : vertex ∈ activation.declaredSupport left)
    (inRight : vertex ∈ activation.declaredSupport right) :
    activation.Blocks .sharedDeclaredSupport pair := by
  classical
  refine ⟨Blocker.sharedDeclaredSupport (CarrierItem.vertex vertex), ?_, rfl⟩
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_biUnion.2 ⟨(left, right), ?_, ?_⟩
  · simp [distinctDemandPairs, leftMem, rightMem, distinct]
  exact Finset.mem_union_left _
    (Finset.mem_image_of_mem _ (vertex_mem_sharedItems inLeft inRight))

/-- **Clause (b).**  A vertex on both canonical return paths blocks the pair. -/
theorem blocks_sharedReturnSupport
    (activation : DemandActivation object Coordinate Chord)
    {pair : Finset (object.Vertex × object.Vertex)}
    {left right : object.Vertex × object.Vertex}
    (leftMem : left ∈ pair) (rightMem : right ∈ pair)
    (distinct : left ≠ right)
    {vertex : object.Vertex}
    (inLeft : vertex ∈ activation.returnSupport left)
    (inRight : vertex ∈ activation.returnSupport right) :
    activation.Blocks .sharedReturnSupport pair := by
  classical
  refine ⟨Blocker.sharedReturnSupport (CarrierItem.vertex vertex), ?_, rfl⟩
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_biUnion.2 ⟨(left, right), ?_, ?_⟩
  · simp [distinctDemandPairs, leftMem, rightMem, distinct]
  refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
  exact Finset.mem_image_of_mem _ (vertex_mem_sharedItems inLeft inRight)

/-- **Clause (c).**  A shoulder endpoint or cubic buffer vertex shared by the
two demands blocks the pair. -/
theorem blocks_sharedLocalBuffer
    (activation : DemandActivation object Coordinate Chord)
    {pair : Finset (object.Vertex × object.Vertex)}
    {left right : object.Vertex × object.Vertex}
    (leftMem : left ∈ pair) (rightMem : right ∈ pair)
    (distinct : left ≠ right)
    {vertex : object.Vertex}
    (inLeft : vertex ∈ activation.localBuffer left)
    (inRight : vertex ∈ activation.localBuffer right) :
    activation.Blocks .sharedLocalBuffer pair := by
  classical
  refine ⟨Blocker.sharedLocalBuffer vertex, ?_, rfl⟩
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_biUnion.2 ⟨(left, right), ?_, ?_⟩
  · simp [distinctDemandPairs, leftMem, rightMem, distinct]
  refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
  exact Finset.mem_image_of_mem _ (Finset.mem_inter.2 ⟨inLeft, inRight⟩)

/-- **Clause (d).**  A boundary-degree-profile coordinate obstructing the pair
blocks it. -/
theorem blocks_boundaryProfile
    (activation : DemandActivation object Coordinate Chord)
    {pair : Finset (object.Vertex × object.Vertex)} {coordinate : Coordinate}
    (obstructs : coordinate ∈ activation.profileObstructions pair) :
    activation.Blocks .boundaryProfile pair := by
  classical
  refine ⟨Blocker.boundaryProfile coordinate, ?_, rfl⟩
  exact Finset.mem_union_right _
    (Finset.mem_union_left _ (Finset.mem_image_of_mem _ obstructs))

/-- **Clause (e).**  A target-response coordinate obstructing the pair blocks
it. -/
theorem blocks_targetResponse
    (activation : DemandActivation object Coordinate Chord)
    {pair : Finset (object.Vertex × object.Vertex)} {coordinate : Coordinate}
    (obstructs : coordinate ∈ activation.responseObstructions pair) :
    activation.Blocks .targetResponse pair := by
  classical
  refine ⟨Blocker.targetResponse coordinate, ?_, rfl⟩
  refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ obstructs)

/-- **Clause (f).**  An arithmetic chord-set obstruction blocks the pair. -/
theorem blocks_arithmeticChordSet
    (activation : DemandActivation object Coordinate Chord)
    {pair : Finset (object.Vertex × object.Vertex)} {chords : Finset Chord}
    (obstructs : chords ∈ activation.chordObstructions pair) :
    activation.Blocks .arithmeticChordSet pair := by
  classical
  refine ⟨Blocker.arithmeticChordSet chords, ?_, rfl⟩
  refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ obstructs)

/-! ## The canonical blocker, `Π_blk`, and `Π_free` -/

end DemandActivation

noncomputable def canonicalBlocker
    (activation : DemandActivation object Coordinate Chord)
    (pair : Finset (object.Vertex × object.Vertex)) :
    Option (Blocker object Coordinate Chord) :=
  (activation.blockers pair).toList.head?

theorem canonicalBlocker_mem
    (activation : DemandActivation object Coordinate Chord)
    {pair : Finset (object.Vertex × object.Vertex)}
    {blocker : Blocker object Coordinate Chord}
    (selected : canonicalBlocker activation pair = some blocker) :
    blocker ∈ activation.blockers pair := by
  simpa using List.mem_of_mem_head? selected

theorem isSome_canonicalBlocker
    (activation : DemandActivation object Coordinate Chord)
    {pair : Finset (object.Vertex × object.Vertex)}
    (blocked : (activation.blockers pair).Nonempty) :
    (canonicalBlocker activation pair).isSome := by
  obtain ⟨blocker, member⟩ := blocked
  have inside : blocker ∈ (activation.blockers pair).toList :=
    Finset.mem_toList.2 member
  rw [canonicalBlocker]
  cases enumeration : (activation.blockers pair).toList with
  | nil => rw [enumeration] at inside; cases inside
  | cons head tail => simp

namespace DemandActivation

/-- **`Π_blk`** at `def:surplus-blockers`: the pairs of the schedule carrying a
blocker object. -/
noncomputable def chargedPairs (activation : DemandActivation object Coordinate Chord)
    (threshold : Nat) : Finset (Finset (object.Vertex × object.Vertex)) :=
  object.chargedPairs threshold SameTokenBlockerRoles.canonicalBlockerOrder
    activation.Blocks activation.decidableBlocks

/-- **`Π_free`**: the pairs of the schedule with no blocker object at all. -/
noncomputable def freePairs (activation : DemandActivation object Coordinate Chord)
    (threshold : Nat) : Finset (Finset (object.Vertex × object.Vertex)) :=
  object.freePairs threshold SameTokenBlockerRoles.canonicalBlockerOrder
    activation.Blocks activation.decidableBlocks

/-- `Π_blk`, defined directly by nonempty concrete blocker sets. -/
noncomputable def blockedPairs (activation : DemandActivation object Coordinate Chord)
    (threshold : Nat) : Finset (Finset (object.Vertex × object.Vertex)) :=
  (object.portPairSchedule threshold).filter fun pair =>
    (activation.blockers pair).Nonempty

/-- `Π_free`, the complement of the concrete blocked pairs. -/
noncomputable def unblockedPairs (activation : DemandActivation object Coordinate Chord)
    (threshold : Nat) : Finset (Finset (object.Vertex × object.Vertex)) :=
  (object.portPairSchedule threshold).filter fun pair =>
    ¬(activation.blockers pair).Nonempty

/-- The concrete image `B_can = Φ_can(Π_blk)`. -/
noncomputable def canonicalBlockerSet
    (activation : DemandActivation object Coordinate Chord) (threshold : Nat) :
    Finset (Blocker object Coordinate Chord) := by
  classical
  exact (activation.blockedPairs threshold).biUnion fun pair =>
    (canonicalBlocker activation pair).toFinset

/-- The graph `I_can = {(π, Φ_can π) | π ∈ Π_blk}`. -/
noncomputable def canonicalIncidenceLedger
    (activation : DemandActivation object Coordinate Chord) (threshold : Nat) :
    Finset (Sigma fun _ : Finset (object.Vertex × object.Vertex) =>
      Blocker object Coordinate Chord) := by
  classical
  exact (activation.blockedPairs threshold).sigma fun pair =>
    (canonicalBlocker activation pair).toFinset

/-- **`μ(B)`**: the fibre of the concrete canonical blocker `B`. -/
noncomputable def multiplicity (activation : DemandActivation object Coordinate Chord)
    (threshold : Nat) (kind : SameTokenBlockerRoles.BlockerKind) : Nat :=
  object.pairMultiplicity threshold inferInstance
    SameTokenBlockerRoles.canonicalBlockerOrder activation.Blocks
    activation.decidableBlocks kind

/-- `μ(B)`, indexed by the concrete canonical blocker. -/
noncomputable def blockerMultiplicity
    (activation : DemandActivation object Coordinate Chord)
    (threshold : Nat) (blocker : Blocker object Coordinate Chord) : Nat := by
  classical
  exact ((activation.blockedPairs threshold).filter fun pair =>
    canonicalBlocker activation pair = some blocker).card

/-- **The split is exhaustive**: `|Π_blk| + |Π_free| = |Π(𝒜₀)|`, now at
`def:surplus-blockers`' own relation. -/
theorem card_chargedPairs_add_card_freePairs
    (activation : DemandActivation object Coordinate Chord) (threshold : Nat) :
    (activation.chargedPairs threshold).card +
        (activation.freePairs threshold).card =
      (object.portPairSchedule threshold).card :=
  object.card_chargedPairs_add_card_freePairs _ _ _

theorem card_blockedPairs_add_card_unblockedPairs
    (activation : DemandActivation object Coordinate Chord) (threshold : Nat) :
    (activation.blockedPairs threshold).card +
        (activation.unblockedPairs threshold).card =
      (object.portPairSchedule threshold).card := by
  classical
  rw [blockedPairs, unblockedPairs]
  exact Finset.card_filter_add_card_filter_not _

/-- The canonical incidence graph has exactly one entry for each blocked pair. -/
theorem card_canonicalIncidenceLedger
    (activation : DemandActivation object Coordinate Chord) (threshold : Nat) :
    (activation.canonicalIncidenceLedger threshold).card =
      (activation.blockedPairs threshold).card := by
  classical
  rw [canonicalIncidenceLedger, Finset.card_sigma]
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro pair member
  have full : pair ∈ object.portPairSchedule threshold ∧
      (activation.blockers pair).Nonempty := by
    simpa [blockedPairs] using member
  obtain ⟨blocker, selected⟩ := Option.isSome_iff_exists.1
    (isSome_canonicalBlocker activation full.2)
  simp [selected]

/-- **`lem:canonical-blocker-ledger-no-overcount` at the instantiated ledger**:
`|Π_blk| = Σ_{B ∈ ℬ_can} μ(B)`.

The identity is the one `Graph/SparsePairLedger` proves; what is new is that it
is read at `def:surplus-blockers`' own six clauses rather than at a quantified
relation. -/
theorem card_chargedPairs_eq_sum_multiplicity
    (activation : DemandActivation object Coordinate Chord) (threshold : Nat) :
    (activation.chargedPairs threshold).card =
      SameTokenBlockerRoles.canonicalBlockerOrder.toFinset.sum
        (activation.multiplicity threshold) :=
  object.card_chargedPairs_eq_sum_multiplicity inferInstance _ _ _

theorem card_blockedPairs_eq_sum_blockerMultiplicity
    (activation : DemandActivation object Coordinate Chord) (threshold : Nat) :
    (activation.blockedPairs threshold).card =
      (activation.canonicalBlockerSet threshold).sum
        (activation.blockerMultiplicity threshold) := by
    classical
    let assigned := activation.blockedPairs threshold
    let blockers := activation.canonicalBlockerSet threshold
    have maps : Set.MapsTo (canonicalBlocker activation) (↑assigned)
        (↑(blockers.image some)) := by
      intro pair member
      have blocked : (activation.blockers pair).Nonempty := by
        have full : pair ∈ object.portPairSchedule threshold ∧
            (activation.blockers pair).Nonempty := by
          simpa [assigned, blockedPairs] using member
        exact full.2
      obtain ⟨blocker, selected⟩ := Option.isSome_iff_exists.1
        (isSome_canonicalBlocker activation blocked)
      rw [selected]
      refine Finset.mem_image.2 ⟨blocker, ?_, rfl⟩
      change blocker ∈ activation.canonicalBlockerSet threshold
      rw [canonicalBlockerSet]
      exact Finset.mem_biUnion.2 ⟨pair, member, by simp [selected]⟩
    rw [Finset.card_eq_sum_card_fiberwise maps]
    rw [Finset.sum_image (fun _ _ _ _ equality => Option.some_injective _ equality)]
    apply Finset.sum_congr rfl
    intro blocker _
    rfl

end DemandActivation

end FiniteObject

end Hypostructure.Graph
