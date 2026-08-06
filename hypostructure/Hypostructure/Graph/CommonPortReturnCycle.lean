import Hypostructure.Graph.VisibleReceiverEntry
import Hypostructure.Graph.RootedReturn

/-!
# `lem:typeA-common-port-return-cycle`: two returns through one port

An anchored return through the completion port `⃗e = (w,h)` is a simple path
`h ⤳ w` that does not use the port edge `wh`.  Two of them therefore have the
*same ordered pair of endpoints*, so the two-path criterion applies to them
directly: if they are internally vertex-disjoint their union is a simple cycle,
and its length is the sum of the two path lengths.

The manuscript's statement is the specialization of `lem:two-path-criterion` to
this common endpoint pair, and the "in particular" clause is the composite with
the registered cycle-length predicate: two internally disjoint anchored returns
through one port whose lengths sum to an accepted length exhibit an accepted
cycle of the whole object.

Nothing here reads a support, a baseline, a scale, or a numeral.  The port is
only used through the adjacency `w ~ h` that makes it a port, and that
adjacency is exactly what forces an anchored return to have length at least
two -- the length-one path from `h` to `w` is the deleted edge itself.  The
accepted-length predicate is a parameter, so the file states the lemma for
every target algebra rather than for one.
-/

namespace Hypostructure.Graph.VisibleEntry

open Hypostructure

universe u

variable {object : FiniteObject.{u}}

/-! ## Anchored returns through a port are long

The port edge is deleted, so a return cannot be that edge; and the two ends of
a port are adjacent, so they are distinct.  Together these say an anchored
return has length at least two, which is the nondegeneracy the two-path
criterion asks for. -/

/-- **A simple `h ⤳ w` walk avoiding the edge `wh` has length at least two**,
whenever `h ≠ w`.  Length zero would identify the two ends; length one would be
the avoided edge itself. -/
theorem two_le_length_of_avoidsPort {outside receiver : object.Vertex}
    (notEqual : outside ≠ receiver)
    (path : object.graph.Walk outside receiver)
    (avoidsPort : s(receiver, outside) ∉ path.edges) :
    2 ≤ path.length := by
  cases path with
  | nil => exact absurd rfl notEqual
  | cons step rest =>
      cases rest with
      | nil =>
          refine absurd ?_ avoidsPort
          rw [Sym2.eq_swap]
          simp
      | cons nextStep tail =>
          simp only [SimpleGraph.Walk.length_cons]
          omega

namespace AnchoredReturn

variable {receiver outside : object.Vertex}

/-- **An anchored return through a port has length at least two.**  Length zero
would make the two endpoints of the port equal, and adjacency is irreflexive;
length one would make the return the deleted port edge itself, which
`avoidsPort` forbids. -/
theorem two_le_length (adjacent : object.graph.Adj receiver outside)
    (return' : AnchoredReturn object receiver outside) :
    2 ≤ return'.path.length :=
  two_le_length_of_avoidsPort (object.graph.ne_of_adj adjacent).symm
    return'.path return'.avoidsPort

end AnchoredReturn

/-! ## Internal disjointness

`def:typeA-visible-load`'s returns run between the two ends of the port, so
"internally vertex-disjoint as anchored paths" is: the only vertices the two
returns share are the two shared endpoints. -/

/-- **Two anchored returns through one port are internally vertex-disjoint**
when the only vertices they share are the port's own two ends. -/
def InternallyDisjoint {receiver outside : object.Vertex}
    (first second : AnchoredReturn object receiver outside) : Prop :=
  ∀ vertex ∈ first.path.support, vertex ∈ second.path.support →
    vertex = outside ∨ vertex = receiver

/-- **The pair of returns is a common-endpoint path pair.**  Both returns run
from `h` to `w`, so the two-path criterion's data is available verbatim; the
disjointness field is the criterion's own orientation of internal disjointness,
discharged from `InternallyDisjoint` together with the two returns being simple
paths. -/
noncomputable def commonEndpointsCycle {receiver outside : object.Vertex}
    (adjacent : object.graph.Adj receiver outside)
    (first second : AnchoredReturn object receiver outside)
    (disjoint : InternallyDisjoint first second) :
    CommonEndpointsCycle object where
  ends := (outside, receiver)
  forward := first.path
  backward := second.path
  forward_isPath := first.isPath
  backward_isPath := second.isPath
  internallyDisjoint := by
    classical
    -- `forward.support.tail` drops `h`; `backward.reverse.support.tail` drops
    -- `w`.  A common member of the two lists is a common vertex of the two
    -- returns that is neither `h` nor `w`, and `InternallyDisjoint` excludes
    -- exactly that.
    intro vertex firstMember secondMember
    have firstSupport : vertex ∈ first.path.support :=
      List.mem_of_mem_tail firstMember
    have secondSupport : vertex ∈ second.path.support := by
      have := List.mem_of_mem_tail secondMember
      simpa [SimpleGraph.Walk.support_reverse] using this
    have notOutside : vertex ≠ outside := by
      intro equality
      -- `first.path` starts at `h` and is simple, so `h` is not in its tail.
      have nodup : (outside :: first.path.support.tail).Nodup := by
        have := first.isPath.support_nodup
        rwa [first.path.support_eq_cons] at this
      exact (List.nodup_cons.mp nodup).1 (equality ▸ firstMember)
    have notReceiver : vertex ≠ receiver := by
      intro equality
      -- `second.path.reverse` starts at `w` and is simple.
      have nodup : (receiver :: second.path.reverse.support.tail).Nodup := by
        have := second.isPath.reverse.support_nodup
        rwa [second.path.reverse.support_eq_cons] at this
      exact (List.nodup_cons.mp nodup).1 (equality ▸ secondMember)
    rcases disjoint vertex firstSupport secondSupport with equality | equality
    · exact absurd equality notOutside
    · exact absurd equality notReceiver
  nondegenerate := Or.inl (by
    have := AnchoredReturn.two_le_length adjacent first
    omega)

/-- **`lem:typeA-common-port-return-cycle`.**  Two internally vertex-disjoint
anchored returns through one completion port glue to a simple cycle whose
length is `|P₁| + |P₂|`; if that sum is an accepted cycle length, the object
carries an accepted cycle.

This is exit `(2)` of `def:typeA-saturated-exits` discharged: the exit's own
side condition is the acceptance of the sum, so taking the exit exhibits the
target on an object that was selected to avoid it. -/
theorem hasCycleWithLength_of_commonPortReturns
    {receiver outside : object.Vertex} {LengthOK : Nat → Prop}
    (adjacent : object.graph.Adj receiver outside)
    (first second : AnchoredReturn object receiver outside)
    (disjoint : InternallyDisjoint first second)
    (accepted : LengthOK (first.path.length + second.path.length)) :
    HasCycleWithLength LengthOK object :=
  ⟨(commonEndpointsCycle adjacent first second disjoint).target LengthOK
    accepted⟩

/-! ## Exit `(2)` of `def:typeA-saturated-exits`

The exit is stated of *receiver-entry* returns -- the returns
`def:typeA-visible-load` counts -- through one completion port of the saturated
receiver.  Its discharge goes through the anchored returns underneath them, so
the lemma above is what the exit spends. -/

/-- **Exit `(2)` through one completion port**: two receiver-entry returns
through `⃗e = (w,h)` are internally vertex-disjoint as anchored paths, and their
lengths sum to an accepted cycle length.

The port is a parameter rather than an existential because the manuscript fixes
`⃗e` at node `[93]` -- it is the port carrying the visible receiver-entry
returns -- and then walks the exit list of *that* port. -/
def ExitTwoThrough (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (LengthOK : Nat → Prop) (receiver outside : object.Vertex) : Prop :=
  ∃ first second : ReceiverEntryReturn object support receiver outside,
    InternallyDisjoint first.toAnchoredReturn second.toAnchoredReturn ∧
      LengthOK (first.toAnchoredReturn.path.length +
        second.toAnchoredReturn.path.length)

/-- **Exit `(2)` exhibits the target.**  A completion port is an ambient edge
of the receiver, so the adjacency the gluing needs is the port's own membership
condition. -/
theorem hasCycleWithLength_of_exitTwoThrough
    {support : Finset object.Vertex} {LengthOK : Nat → Prop}
    {receiver outside : object.Vertex}
    (port : outside ∈ completionPorts object support receiver)
    (exit : ExitTwoThrough object support LengthOK receiver outside) :
    HasCycleWithLength LengthOK object := by
  obtain ⟨first, second, disjoint, accepted⟩ := exit
  exact hasCycleWithLength_of_commonPortReturns
    (mem_completionPorts.mp port).1 first.toAnchoredReturn
    second.toAnchoredReturn disjoint accepted

end Hypostructure.Graph.VisibleEntry
