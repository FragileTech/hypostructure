import Hypostructure.Graph.ReceiverRouting
import Hypostructure.Graph.TypeADischarge

/-!
# Receiver-entry returns, visible loads, and the visible-first excess basin

`def:typeA-visible-load` reads a receiver `w` of a support `X` through the
ambient edges it still has leaving `X`:

* a **completion port** `⃗e = (w,h)` is one of those edges;
* an **anchored return** through `⃗e` is a simple path `P : h ⤳ w` in `G − wh`;
* `ent_X(P)` is the first vertex of `X` that `P` meets, traversed from `h`;
* a **receiver-entry channel** from `r` to `w` is a simple path `Q : r ⤳ w`
  inside `X`, and an anchored return is a **receiver-entry return** when it
  decomposes as `P = Γ ∘ Q` with `Γ` from `h` to `r` having every internal
  vertex outside `X`;
* such a return is **visible for** a routed load `u` with `r(u) = w` when the
  canonical trace `T_u` is a subpath of `Q`, or `Q` is the lexicographically
  first channel assigned to the terminal receiver edge of `T_u`.

`lem:typeA-first-entry` -- the first entry of an anchored return is a receiver
-- is *proved* here, from the definition alone: the vertex of `X` a return first
meets is entered from outside, so it spends less than the baseline inside `X`.
Nothing assumes it.

The manuscript's second visibility clause fixes a channel by a lexicographic
order without naming it.  The order used here is the framework's own
`Graph.FinitePathSelection.pathSchedule` -- shortest first, then Mathlib's
enumeration -- which is the same order `FiniteObject.tracePath?` selects `T_u`
with, so `T_u` and the canonical channel are read off one schedule rather than
two.  `canonicalChannel?` is that reading: the first scheduled path from `r` to
`w` inside `X` whose last edge is the terminal edge of `T_u`.

On top of the definition this module proves the counting the silent branch
spends, `lem:typeA-silent-excess-count`:

* a receiver has exactly `q(w)` completion ports on a support of no ambient
  surplus (`card_completionPorts`);
* if no port carries `s` visible returns, then `L_vis(w) ≤ (s−1)·q(w)`, which is
  below the payable set's size `c(w) = s·q(w) − 1`, so the visible-first order
  of `def:typeA-excess-basin` pays every visible load and the whole excess basin
  is silent (`one_add_routedLoad_le_silentExcess`);
* summed over the receivers, `|V(X)| ≤ S_sil^exc(X) + s·def⁺(X)`, which is
  `S_sil^exc(X) ≥ s·D_A(X)` with `D_A(X) = |V(X)|/s − def⁺(X)` written without
  division or subtraction
  (`card_le_sum_silentExcess_add_positiveDeficiency`).

Every threshold, scale and order is a parameter or the object's own schedule.
Nothing here knows a degree, an overload factor, a manuscript node, or a graph
family.
-/

namespace Hypostructure.Graph.VisibleEntry

open Hypostructure
open Hypostructure.Core.Finite

universe u

attribute [local instance] vertexDecEq

variable {object : FiniteObject.{u}}

/-! ## Completion ports

`q(w)` counts the ambient edges a receiver still has leaving the support.  The
ports themselves are those edges, named by their outside endpoint. -/

/-- **The completion ports of a receiver**: its neighbours outside the support.
`⃗e = (w,h)` is `w` together with a member `h` of this set. -/
noncomputable def completionPorts (object : FiniteObject.{u})
    (support : Finset object.Vertex) (receiver : object.Vertex) :
    Finset object.Vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact (object.graph.neighborFinset receiver) \ support

theorem mem_completionPorts {support : Finset object.Vertex}
    {receiver outside : object.Vertex} :
    outside ∈ completionPorts object support receiver ↔
      object.graph.Adj receiver outside ∧ outside ∉ support := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  unfold completionPorts
  simp [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]

/-- **A receiver has exactly `q(w)` completion ports.**  On a support of no
ambient surplus every vertex sits exactly at the baseline, so the edges leaving
the support at `w` are the baseline less the edges it spends inside. -/
theorem card_completionPorts (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    {receiver : object.Vertex}
    (exact : object.degree receiver = threshold) :
    (completionPorts object support receiver).card =
      object.missingPorts support threshold receiver := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  have split :
      ((object.graph.neighborFinset receiver) \ support).card +
          ((object.graph.neighborFinset receiver) ∩ support).card =
        (object.graph.neighborFinset receiver).card :=
    Finset.card_sdiff_add_card_inter _ _
  have degreeEq : (object.graph.neighborFinset receiver).card =
      object.degree receiver := rfl
  have internal : ((object.graph.neighborFinset receiver) ∩ support).card =
      object.internalDegree support receiver := rfl
  unfold completionPorts FiniteObject.missingPorts
  omega

/-! ## Anchored returns and the first entry

An anchored return through `⃗e = (w,h)` is a simple `h ⤳ w` path in `G − wh`,
which is the shape `Graph.EdgeRootedReturn` already has at the dart `(w,h)`.
It is repeated here without a length predicate because this node reads the
return's *entry*, not its length; `Graph.EdgeRootedReturn` remains the reading
the length-based exits use. -/

/-- **An anchored return through a completion port.**  A simple path from the
outside endpoint back to the receiver that does not use the port edge. -/
structure AnchoredReturn (object : FiniteObject.{u})
    (receiver outside : object.Vertex) where
  /-- The return path, from `h` back to `w`. -/
  path : object.graph.Walk outside receiver
  /-- It is simple. -/
  isPath : path.IsPath
  /-- It does not use the deleted port edge `wh`. -/
  avoidsPort : s(receiver, outside) ∉ path.edges

/-- **`ent_X(P)`.**  The first vertex of the support the return meets, scanned
from the outside endpoint. -/
noncomputable def firstEntry? (support : Finset object.Vertex)
    {receiver outside : object.Vertex}
    (return' : AnchoredReturn object receiver outside) :
    Option object.Vertex :=
  return'.path.support.find? fun vertex =>
    @decide (vertex ∈ support) (Classical.propDecidable _)

/-- A list whose only member satisfying the predicate is `chosen` finds
`chosen`. -/
private theorem find?_eq_some_of_unique {α : Type u} {predicate : α → Bool}
    {list : List α} {chosen : α} (member : chosen ∈ list)
    (holds : predicate chosen = true)
    (unique : ∀ other ∈ list, predicate other = true → other = chosen) :
    list.find? predicate = some chosen := by
  rcases found : list.find? predicate with _ | other
  · exact absurd holds (List.find?_eq_none.mp found chosen member)
  · exact congrArg some
      (unique other (List.mem_of_find?_eq_some found) (List.find?_some found))

/-- **The first entry exists and is entered from outside the support.**

Scanning a walk that starts outside the support and ends inside it, the first
vertex of the support it meets has a predecessor on the walk that is outside,
and the two are adjacent.  This is the whole content of `lem:typeA-first-entry`
below; it is stated for a bare walk because that is all the argument uses. -/
theorem exists_entry_with_outside_neighbour {support : Finset object.Vertex}
    {source target : object.Vertex} (walk : object.graph.Walk source target)
    (outside : source ∉ support) (inside : target ∈ support) :
    ∃ entry : object.Vertex,
      walk.support.find?
          (fun vertex => @decide (vertex ∈ support)
            (Classical.propDecidable _)) = some entry ∧
        entry ∈ support ∧
          ∃ before : object.Vertex,
            before ∉ support ∧ object.graph.Adj before entry ∧
              s(before, entry) ∈ walk.edges := by
  classical
  induction walk with
  | nil => exact absurd inside outside
  | cons adjacency rest inductionHypothesis =>
      rename_i first second _
      have head :
          (SimpleGraph.Walk.cons adjacency rest).support = first :: rest.support :=
        rfl
      have skipHead :
          (@decide (first ∈ support) (Classical.propDecidable _)) = false := by
        simpa using outside
      by_cases secondInside : second ∈ support
      · refine ⟨second, ?_, secondInside, first, outside, adjacency, ?_⟩
        · rw [head, List.find?_cons_of_neg (by simpa using skipHead),
            rest.support_eq_cons]
          exact List.find?_cons_of_pos (by simpa using secondInside)
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_self
      · obtain ⟨entry, found, memberEntry, before, beforeOutside, adjacent,
          edgeMember⟩ := inductionHypothesis secondInside inside
        refine ⟨entry, ?_, memberEntry, before, beforeOutside, adjacent, ?_⟩
        · rw [head, List.find?_cons_of_neg (by simpa using skipHead)]
          exact found
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ edgeMember

/-- **`lem:typeA-first-entry`: the first entry of an anchored return is a
receiver.**

*"Let `r = ent_X(P)`.  The predecessor of `r` on `P` lies outside `X`, so `r`
has an ambient incidence not counted in `d_X(r)`.  Since `σ(X)=0`, every vertex
of `X` has ambient degree `δ`.  Hence `d_X(r) ≤ δ−1`, and `r` is a receiver."*

The hypothesis is exactly the manuscript's: on a support of no ambient surplus
the vertices of the support sit at the baseline.  Nothing is assumed about the
return beyond its being one. -/
theorem isReceiver_firstEntry {support : Finset object.Vertex} {threshold : Nat}
    {receiver outsideVertex : object.Vertex}
    (return' : AnchoredReturn object receiver outsideVertex)
    (portOutside : outsideVertex ∉ support) (receiverInside : receiver ∈ support)
    (baseline : ∀ vertex ∈ support, object.degree vertex = threshold) :
    ∃ entry : object.Vertex,
      firstEntry? support return' = some entry ∧
        object.IsReceiver support threshold entry := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  obtain ⟨entry, found, memberEntry, before, beforeOutside, adjacency, _edge⟩ :=
    exists_entry_with_outside_neighbour return'.path portOutside receiverInside
  refine ⟨entry, found, memberEntry, ?_⟩
  -- The outside predecessor is a neighbour of `entry` that the internal degree
  -- does not count, so the internal degree is strictly below the ambient one.
  have strict :
      (object.graph.neighborFinset entry) ∩ support ⊂
        object.graph.neighborFinset entry := by
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro contained
    exact beforeOutside
      (Finset.mem_inter.mp
        (contained ((SimpleGraph.mem_neighborFinset _ _ _).mpr
          adjacency.symm))).2
  have degreeEq : object.degree entry = threshold := baseline entry memberEntry
  have lt : object.internalDegree support entry < object.degree entry :=
    Finset.card_lt_card strict
  omega

/-! ## The entry budget

`lem:typeA-entry-budget` reads the first entries of the returns through *one*
port from the other receivers' side: at a receiver with a single completion
port, no return re-enters at that receiver, and the edges through which returns
first enter the support are port edges of the other receivers. -/

/-- **The port edges of the other receivers.**  Every edge through which an
anchored return first enters the support is one of these: its outside end is
outside the support and its inside end is a receiver. -/
noncomputable def entryPortEdges (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) : Finset (Sym2 object.Vertex) := by
  classical
  exact ((object.receivers support threshold).erase receiver).biUnion
    fun other =>
      (completionPorts object support other).image fun outside =>
        s(outside, other)

/-- **`lem:typeA-entry-budget`, first half: the degree-two entry exclusion.**

*"If `r = w`, then the return enters `w` from outside `X` through an ambient
edge different from the deleted edge `wh`.  This is impossible because
`d_X(w) = δ−1` and `σ(X)=0` give exactly one ambient edge from `w` to `G − X`,
namely `wh`."*  The hypothesis is `q(w) = 1`, which is the manuscript's
`d_X(w) = 2` at its own baseline. -/
theorem firstEntry_ne_of_missingPorts_eq_one {support : Finset object.Vertex}
    {threshold : Nat} {receiver outsideVertex entry : object.Vertex}
    (return' : AnchoredReturn object receiver outsideVertex)
    (port : outsideVertex ∈ completionPorts object support receiver)
    (receiverInside : receiver ∈ support)
    (unique : object.missingPorts support threshold receiver = 1)
    (exact : object.degree receiver = threshold)
    (found : firstEntry? support return' = some entry) :
    entry ≠ receiver := by
  classical
  have portOutside : outsideVertex ∉ support := (mem_completionPorts).mp port |>.2
  obtain ⟨other, scanned, _memberEntry, before, beforeOutside, adjacency,
    edgeMember⟩ :=
    exists_entry_with_outside_neighbour return'.path portOutside receiverInside
  have same : other = entry := by
    have := found
    unfold firstEntry? at this
    exact Option.some.inj (scanned.symm.trans this)
  subst same
  intro collides
  subst collides
  -- The outside predecessor is a completion port of the receiver, and the
  -- receiver has exactly one.
  have beforePort : before ∈ completionPorts object support other :=
    (mem_completionPorts).mpr ⟨adjacency.symm, beforeOutside⟩
  have single : (completionPorts object support other).card = 1 := by
    rw [card_completionPorts object support threshold exact, unique]
  obtain ⟨only, singleton⟩ := Finset.card_eq_one.mp single
  have beforeEq : before = only := Finset.mem_singleton.mp (singleton ▸ beforePort)
  have outsideEq : outsideVertex = only :=
    Finset.mem_singleton.mp (singleton ▸ port)
  refine return'.avoidsPort ?_
  have : s(before, other) = s(other, outsideVertex) := by
    rw [beforeEq, outsideEq, Sym2.eq_swap]
  exact this ▸ edgeMember

/-- **`lem:typeA-entry-budget`, second half: the entry budget.**

*"For each first-entry receiver `r`, the entering edge is one of the `q(r)`
completion ports of `r`."*  The first-entry edge of a return therefore lies in
`entryPortEdges`, whose size is at most `Σ_{r ≠ w} q(r)`. -/
theorem mem_entryPortEdges {support : Finset object.Vertex} {threshold : Nat}
    {receiver entry before : object.Vertex}
    (isReceiver : object.IsReceiver support threshold entry)
    (different : entry ≠ receiver) (beforeOutside : before ∉ support)
    (adjacency : object.graph.Adj before entry) :
    s(before, entry) ∈ entryPortEdges object support threshold receiver := by
  classical
  refine Finset.mem_biUnion.mpr ⟨entry, ?_, ?_⟩
  · exact Finset.mem_erase.mpr ⟨different, FiniteObject.mem_receivers.mpr isReceiver⟩
  · exact Finset.mem_image.mpr ⟨before,
      (mem_completionPorts).mpr ⟨adjacency.symm, beforeOutside⟩, rfl⟩

/-- **The entry budget `Σ_{r ≠ w} q(r)`.** -/
theorem card_entryPortEdges_le (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex)
    (baseline : ∀ vertex ∈ support, object.degree vertex = threshold) :
    (entryPortEdges object support threshold receiver).card ≤
      ∑ other ∈ (object.receivers support threshold).erase receiver,
        object.missingPorts support threshold other := by
  classical
  refine le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum ?_)
  intro other member
  have isReceiver : object.IsReceiver support threshold other :=
    FiniteObject.mem_receivers.mp (Finset.mem_of_mem_erase member)
  refine le_trans (Finset.card_image_le) ?_
  exact le_of_eq
    (card_completionPorts object support threshold (baseline other isReceiver.1))

/-! ## Receiver-entry channels and returns

`Q` is a simple path from one receiver to another inside the support, and a
receiver-entry return is an anchored return that decomposes as `Γ ∘ Q` with the
connector `Γ` outside the support until it reaches `Q`'s source. -/

/-- **A receiver-entry channel `Q : r ⤳ w`**: a simple path inside the support.
Being a *receiver*-entry channel is a property of its endpoints, not of the
path; `isReceiver_firstEntry` is what supplies it at a return's entry. -/
def IsChannel (object : FiniteObject.{u}) (support : Finset object.Vertex)
    {entry receiver : object.Vertex}
    (channel : object.graph.Walk entry receiver) : Prop :=
  channel.IsPath ∧ ∀ vertex ∈ channel.support, vertex ∈ support

/-- **A receiver-entry return through `⃗e = (w,h)`**: `P = Γ ∘ Q`, with `Γ`
running from `h` to the entry receiver with every vertex before the entry
outside the support, and `Q` a receiver-entry channel from the entry to `w`.
The anchored-return conditions are stated of the composite, which is exactly
`def:typeA-visible-load`'s `P`. -/
structure ReceiverEntryReturn (object : FiniteObject.{u})
    (support : Finset object.Vertex) (receiver outside : object.Vertex) where
  /-- The first-entry receiver `r = ent_X(P)`. -/
  entry : object.Vertex
  /-- The outside connector `Γ : h ⤳ r`. -/
  connector : object.graph.Walk outside entry
  /-- The internal channel `Q : r ⤳ w`. -/
  channel : object.graph.Walk entry receiver
  /-- `Γ` meets the support only at its own endpoint. -/
  connectorOutside : ∀ vertex ∈ connector.support, vertex ≠ entry →
    vertex ∉ support
  /-- `Q` is a receiver-entry channel. -/
  isChannel : IsChannel object support channel
  /-- `P = Γ ∘ Q` is simple. -/
  isPath : (connector.append channel).IsPath
  /-- `P` does not use the port edge. -/
  avoidsPort : s(receiver, outside) ∉ (connector.append channel).edges

namespace ReceiverEntryReturn

variable {support : Finset object.Vertex} {receiver outside : object.Vertex}

/-- **A receiver-entry return is an anchored return.**  This is the inclusion
`def:typeA-visible-load` states, and it is definitional. -/
def toAnchoredReturn (return' : ReceiverEntryReturn object support receiver outside) :
    AnchoredReturn object receiver outside where
  path := return'.connector.append return'.channel
  isPath := return'.isPath
  avoidsPort := return'.avoidsPort

/-- **The decomposition names the first entry.**  `ent_X(Γ ∘ Q) = r`: every
vertex of `Γ` before `r` is outside the support, and `r` is inside it because it
is the channel's source.  So the two readings of the entry -- the one the
decomposition declares and the one `firstEntry?` scans for -- agree. -/
theorem firstEntry?_toAnchoredReturn
    (return' : ReceiverEntryReturn object support receiver outside) :
    firstEntry? support return'.toAnchoredReturn = some return'.entry := by
  classical
  have entryInside : return'.entry ∈ support :=
    return'.isChannel.2 return'.entry return'.channel.start_mem_support
  have connectorFinds :
      return'.connector.support.find?
          (fun vertex => @decide (vertex ∈ support)
            (Classical.propDecidable _)) = some return'.entry :=
    find?_eq_some_of_unique return'.connector.end_mem_support
      (by simpa using entryInside)
      (fun other member holds => by
        by_contra different
        exact return'.connectorOutside other member different (by simpa using holds))
  unfold firstEntry? toAnchoredReturn
  simp only [SimpleGraph.Walk.support_append, List.find?_append, connectorFinds,
    Option.some_or]

/-! ## The exact finite receiver-entry-return schedule

The manuscript quantifies over the receiver-entry returns through one fixed
completion port.  Both halves of such a return are simple paths in the finite
ambient object, so this is an exact finite family.  The schedule below is
obtained only from the object's vertex order and the complete path schedules;
the filter is precisely the fields of `ReceiverEntryReturn`.
-/

/-- The finite candidate list before duplicate proof representations are
removed.  Every member is already an actual receiver-entry return. -/
private noncomputable def candidateSchedule
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (receiver outside : object.Vertex) :
    List (ReceiverEntryReturn object support receiver outside) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := FinEnum.instFintype
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  exact object.orderedVertices.flatMap fun entry =>
    (FinitePathSelection.pathSchedule object.graph outside entry).flatMap fun connector =>
      (FinitePathSelection.pathSchedule object.graph entry receiver).filterMap fun channel =>
        if valid :
            (forall vertex, vertex ∈ connector.1.support -> vertex ≠ entry ->
              vertex ∉ support) /\
            (forall vertex, vertex ∈ channel.1.support -> vertex ∈ support) /\
            (connector.1.append channel.1).IsPath /\
            s(receiver, outside) ∉ (connector.1.append channel.1).edges then
          some {
            entry := entry
            connector := connector.1
            channel := channel.1
            connectorOutside := valid.1
            isChannel := ⟨channel.2, valid.2.1⟩
            isPath := valid.2.2.1
            avoidsPort := valid.2.2.2 }
        else
          none

/-- **The exact finite schedule of receiver-entry returns through a fixed
completion port.**  Its only data are finite vertex and simple-path schedules;
`eraseDups` removes duplicate proof representations without changing the
mathematical family. -/
noncomputable def schedule (object : FiniteObject.{u})
    (support : Finset object.Vertex) (receiver outside : object.Vertex) :
    Enumeration (ReceiverEntryReturn object support receiver outside) := by
  classical
  let candidates := candidateSchedule object support receiver outside
  exact Enumeration.ofNodupList candidates.toFinset.toList
    (Finset.nodup_toList candidates.toFinset)

/-- The finite schedule is complete: every receiver-entry return through the
fixed port occurs in it. -/
theorem mem_schedule
    (return' : ReceiverEntryReturn object support receiver outside) :
    return' ∈ (schedule object support receiver outside).values := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := FinEnum.instFintype
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  rw [schedule, Enumeration.ofNodupList_values, Finset.mem_toList,
    List.mem_toFinset]
  let connector : object.graph.Path outside return'.entry :=
    ⟨return'.connector, return'.isPath.of_append_left⟩
  let channel : object.graph.Path return'.entry receiver :=
    ⟨return'.channel, return'.isChannel.1⟩
  have connectorMember : connector ∈
      FinitePathSelection.pathSchedule object.graph outside return'.entry :=
    FinitePathSelection.mem_pathSchedule object.graph connector
  have channelMember : channel ∈
      FinitePathSelection.pathSchedule object.graph return'.entry receiver :=
    FinitePathSelection.mem_pathSchedule object.graph channel
  have valid :
      (forall vertex, vertex ∈ connector.1.support -> vertex ≠ return'.entry ->
        vertex ∉ support) /\
      (forall vertex, vertex ∈ channel.1.support -> vertex ∈ support) /\
      (connector.1.append channel.1).IsPath /\
      s(receiver, outside) ∉ (connector.1.append channel.1).edges := by
    exact ⟨return'.connectorOutside, return'.isChannel.2,
      return'.isPath, return'.avoidsPort⟩
  unfold candidateSchedule
  rw [List.mem_flatMap]
  refine ⟨return'.entry, object.mem_orderedVertices return'.entry, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨connector, connectorMember, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨channel, channelMember, ?_⟩
  rw [dif_pos valid]

/-- Every scheduled return carries its canonical first-entry/channel
decomposition: the stored entry is exactly `ent_X(Γ ∘ Q)`. -/
theorem firstEntry?_of_mem_schedule
    (return' : ReceiverEntryReturn object support receiver outside)
    (_member : return' ∈ (schedule object support receiver outside).values) :
    firstEntry? support return'.toAnchoredReturn = some return'.entry :=
  return'.firstEntry?_toAnchoredReturn

end ReceiverEntryReturn

/-! ## Visibility

`def:typeA-visible-load`'s visibility test compares the canonical trace `T_u`
against the channel `Q` of a receiver-entry return: either `T_u` is a subpath of
`Q`, or `Q` is the lexicographically first channel assigned to the terminal
receiver edge of `T_u`.  Both traces and channels end at `w`, so "subpath" is
"the trace's vertex list is a final segment of the channel's", and the terminal
receiver edge of `T_u` is the last edge of `T_u`. -/

/-- **The lexicographically first channel assigned to an edge.**  The first path
of the object's own schedule from `r` to `w` that stays inside the support and
ends with the given edge.  This is the same schedule `tracePath?` selects `T_u`
from, so the manuscript's "lexicographically first" is the framework's one
order rather than a second one. -/
noncomputable def canonicalChannel? (object : FiniteObject.{u})
    (support : Finset object.Vertex) (entry receiver : object.Vertex)
    (terminalEdge : Sym2 object.Vertex) :
    Option (object.graph.Path entry receiver) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := FinEnum.instFintype
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact (FinitePathSelection.pathSchedule object.graph entry receiver).find?
    fun path =>
      @decide (IsChannel object support path.1 ∧
          path.1.edges.getLast? = some terminalEdge)
        (Classical.propDecidable _)

/-- **`P` is visible for the routed load `u`.**  `u` is routed to `w`, and its
canonical trace either sits inside the return's channel as a final segment, or
the channel is the canonical one assigned to the trace's terminal receiver
edge. -/
def VisibleFor (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) {receiver outside : object.Vertex}
    (return' : ReceiverEntryReturn object support receiver outside)
    (load : object.Vertex) : Prop :=
  ∃ trace : object.graph.Path load receiver,
    object.tracePath? support threshold load receiver = some trace ∧
      (trace.1.support.IsSuffix return'.channel.support ∨
        ∃ terminalEdge : Sym2 object.Vertex,
          trace.1.edges.getLast? = some terminalEdge ∧
            canonicalChannel? object support return'.entry receiver
                terminalEdge =
              some ⟨return'.channel, return'.isChannel.1⟩)

namespace ReceiverEntryReturn

variable {support : Finset object.Vertex} {threshold : Nat}
variable {receiver outside load : object.Vertex}

/-- A finite declared support belongs to a receiver-entry return when every
declared vertex lies on that return and its internal channel is visible for the
canonical trace of the routed load. -/
def OwnsDeclaredSupport
    (return' : ReceiverEntryReturn object support receiver outside)
    (declaredSupport : Finset object.Vertex) (load : object.Vertex) : Prop :=
  declaredSupport ⊆ return'.toAnchoredReturn.path.support.toFinset /\
    VisibleFor object support threshold return' load

/-- A boundary-degree coordinate belongs to a receiver-entry return when its
singleton declared support lies on that return and the return's internal
channel is visible for the canonical trace of the routed load.  The second
conjunct is exactly the manuscript's two-way condition: containment of the
trace, or canonical ownership of its terminal receiver edge. -/
def OwnsBoundaryEntry
    (return' : ReceiverEntryReturn object support receiver outside)
    (boundary : object.Vertex)
    (load : object.Vertex) : Prop :=
  OwnsDeclaredSupport (threshold := threshold) return' {boundary} load

/-- The manuscript's two visibility alternatives produce ownership of a D1
boundary-degree entry directly. -/
theorem ownsBoundaryEntry_of_trace
    (return' : ReceiverEntryReturn object support receiver outside)
    (boundary : object.Vertex)
    (trace : object.graph.Path load receiver)
    (boundaryMember : boundary ∈ return'.toAnchoredReturn.path.support)
    (selected : object.tracePath? support threshold load receiver = some trace)
    (channelOwns :
      trace.1.support.IsSuffix return'.channel.support \/
        exists terminalEdge : Sym2 object.Vertex,
          trace.1.edges.getLast? = some terminalEdge /\
            canonicalChannel? object support return'.entry receiver terminalEdge =
              some ⟨return'.channel, return'.isChannel.1⟩) :
    OwnsBoundaryEntry (threshold := threshold) return' boundary load :=
  ⟨by
      intro vertex member
      simp only [Finset.mem_singleton] at member
      subst vertex
      simpa using boundaryMember,
    trace, selected, channelOwns⟩

end ReceiverEntryReturn

/-- A finite declared support is owned at a receiver when one of its actual
completion ports has a scheduled visible receiver-entry return containing the
support. -/
def ownsDeclaredSupport (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex) (declaredSupport : Finset object.Vertex) :
    Prop :=
  exists outside, outside ∈ completionPorts object support receiver /\
    exists return' : ReceiverEntryReturn object support receiver outside,
      return' ∈ (ReceiverEntryReturn.schedule object support receiver outside).values /\
        return'.OwnsDeclaredSupport (threshold := threshold) declaredSupport load

/-- **The finite D1 ownership predicate.**  A boundary-degree coordinate is
owned at a receiver exactly when one of its actual completion ports has a
scheduled receiver-entry return satisfying the manuscript's ownership rule. -/
def ownsBoundaryEntry (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex)
    (boundary : object.Vertex) :
    Prop :=
  ownsDeclaredSupport object support threshold receiver load {boundary}

/-- An actual owned receiver-entry return is never lost by the finite D1
schedule. -/
theorem ownsBoundaryEntry_of_return
    {support : Finset object.Vertex} {threshold : Nat}
    {receiver outside load : object.Vertex}
    (boundary : object.Vertex)
    (port : outside ∈ completionPorts object support receiver)
    (return' : ReceiverEntryReturn object support receiver outside)
    (owns : return'.OwnsBoundaryEntry (threshold := threshold) boundary load) :
    ownsBoundaryEntry object support threshold receiver load boundary :=
  ⟨outside, port, return', return'.mem_schedule, owns⟩

/-- **`L_vis(w, ⃗e)`'s set.**  The routed loads of `w` for which some
receiver-entry return through the port `⃗e = (w,h)` is visible.  The manuscript
counts *distinct routed cubic vertices*, which is the cardinality of this
set. -/
noncomputable def visibleLoadsAt (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver outside : object.Vertex) : Finset object.Vertex := by
  classical
  exact (object.routedLoads support threshold receiver).filter fun load =>
    ∃ return' : ReceiverEntryReturn object support receiver outside,
      VisibleFor object support threshold return' load

/-- **`L_vis(w)`'s set.**  A routed load is visible when it is visible at some
completion port of `w`.  The manuscript assigns a load seen by several ports to
the first of them in the canonical order; that assignment refines this set into
the per-port sets and does not change which loads are visible, which is all the
count below reads. -/
noncomputable def visibleLoads (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) : Finset object.Vertex := by
  classical
  exact (object.routedLoads support threshold receiver).filter fun load =>
    ∃ outside ∈ completionPorts object support receiver,
      load ∈ visibleLoadsAt object support threshold receiver outside

theorem mem_visibleLoads (object : FiniteObject.{u})
    {support : Finset object.Vertex} {threshold : Nat}
    {receiver load : object.Vertex} :
    load ∈ visibleLoads object support threshold receiver ↔
      load ∈ object.routedLoads support threshold receiver ∧
        ∃ outside ∈ completionPorts object support receiver,
          load ∈ visibleLoadsAt object support threshold receiver outside := by
  classical
  unfold visibleLoads
  simp only [Finset.mem_filter]

theorem visibleLoads_subset (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) :
    visibleLoads object support threshold receiver ⊆
      object.routedLoads support threshold receiver := by
  classical
  unfold visibleLoads
  exact Finset.filter_subset _ _

theorem visibleLoadsAt_subset (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver outside : object.Vertex) :
    visibleLoadsAt object support threshold receiver outside ⊆
      object.routedLoads support threshold receiver := by
  classical
  unfold visibleLoadsAt
  exact Finset.filter_subset _ _

/-- **`L_vis(w) ≤ Σ_{⃗e} L_vis(w, ⃗e)`.**  Every visible load is visible at one
of the receiver's own completion ports. -/
theorem card_visibleLoads_le_sum (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) :
    (visibleLoads object support threshold receiver).card ≤
      ∑ outside ∈ completionPorts object support receiver,
        (visibleLoadsAt object support threshold receiver outside).card := by
  classical
  refine le_trans (Finset.card_le_card ?_)
    (Finset.card_biUnion_le
      (s := completionPorts object support receiver)
      (t := fun outside => visibleLoadsAt object support threshold receiver outside))
  intro load member
  obtain ⟨_routed, outside, port, visible⟩ := (mem_visibleLoads object).mp member
  exact Finset.mem_biUnion.mpr ⟨outside, port, visible⟩

/-- **`L_vis(w) ≤ (s−1)·q(w)`.**

*"Since `w` has exactly `q(w)` completion ports, each port carries at most three
visible loads, so `L_vis(w) ≤ 3q(w)`."*  The manuscript's three is `s − 1` at
the registered overload factor: the branch hypothesis is that no port carries
`s` visible receiver-entry returns. -/
theorem card_visibleLoads_le (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    {receiver : object.Vertex}
    (exact : object.degree receiver = threshold)
    (unsaturatedPorts : ∀ outside ∈ completionPorts object support receiver,
      (visibleLoadsAt object support threshold receiver outside).card + 1 ≤
        scale) :
    (visibleLoads object support threshold receiver).card +
        object.missingPorts support threshold receiver ≤
      scale * object.missingPorts support threshold receiver := by
  classical
  have ports := card_completionPorts object support threshold exact
  have bound :
      ∑ outside ∈ completionPorts object support receiver,
          ((visibleLoadsAt object support threshold receiver outside).card + 1) ≤
        ∑ _outside ∈ completionPorts object support receiver, scale :=
    Finset.sum_le_sum unsaturatedPorts
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, smul_eq_mul,
    smul_eq_mul, Nat.mul_one, ports] at bound
  calc (visibleLoads object support threshold receiver).card +
          object.missingPorts support threshold receiver
      ≤ (∑ outside ∈ completionPorts object support receiver,
            (visibleLoadsAt object support threshold receiver outside).card) +
          object.missingPorts support threshold receiver :=
        Nat.add_le_add_right
          (card_visibleLoads_le_sum object support threshold receiver) _
    _ ≤ object.missingPorts support threshold receiver * scale := bound
    _ = scale * object.missingPorts support threshold receiver := Nat.mul_comm _ _

/-! ## The visible-first excess basin

`def:typeA-excess-basin` pays the routed loads of a receiver in the
*visible-first* order -- the visible ones first, then the rest, each block in the
canonical order -- and calls the first `c(w) = s·q(w) − 1` of them the payable
set `A(w)`.  What is left is the excess basin `E(w)`, and `𝒰(w)` is its silent
part.

The canonical order used inside each block is the object's own vertex schedule.
The manuscript breaks ties by port order and then by trace order; the count
below reads only the block structure -- that every visible load is paid before
the payable set runs out -- so the two orders give the same basin size. -/

/-- **The visible-first order** of `def:typeA-excess-basin`: the visible routed
loads in the object's own vertex order, then the remaining routed loads in the
same order. -/
noncomputable def visibleFirstOrder (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) : List object.Vertex := by
  classical
  exact (object.orderedVertices.filter fun vertex =>
      decide (vertex ∈ visibleLoads object support threshold receiver)) ++
    object.orderedVertices.filter fun vertex =>
      decide (vertex ∈ object.routedLoads support threshold receiver ∧
        vertex ∉ visibleLoads object support threshold receiver)

/-- **`A(w)`**, the canonical payable set: the first `c(w) = s·q(w) − 1` routed
loads in the visible-first order. -/
noncomputable def payableSet (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) : Finset object.Vertex := by
  classical
  exact ((visibleFirstOrder object support threshold receiver).take
    (scale * object.missingPorts support threshold receiver - 1)).toFinset

/-- **`E(w) = ℒ(w) ∖ A(w)`**, the excess basin. -/
noncomputable def excessBasin (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) : Finset object.Vertex :=
  (object.routedLoads support threshold receiver) \
    payableSet object support threshold scale receiver

/-- **`𝒰(w) = {u ∈ E(w) : u is silent}`**, the silent excess. -/
noncomputable def silentExcess (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) : Finset object.Vertex :=
  (excessBasin object support threshold scale receiver) \
    visibleLoads object support threshold receiver

/-- The receivers which contribute indexed unpaid-silent route-8 entries. -/
noncomputable def saturatedReceivers (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat) :
    Finset object.Vertex := by
  classical
  exact (object.receivers support threshold).filter
    (object.Saturated support threshold scale)

/-- The payable set has at most `c(w)` members. -/
theorem card_payableSet_le (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) :
    (payableSet object support threshold scale receiver).card ≤
      scale * object.missingPorts support threshold receiver - 1 := by
  classical
  refine le_trans (List.toFinset_card_le _) ?_
  simpa using
    (List.length_take_le
      (scale * object.missingPorts support threshold receiver - 1)
      (visibleFirstOrder object support threshold receiver))

/-- **The visible-first order pays every visible load first.**  The visible
block of the order lists exactly `L_vis(w)` loads, so when `L_vis(w) ≤ c(w)` the
payable set contains all of them. -/
theorem visibleLoads_subset_payableSet (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex)
    (paid : (visibleLoads object support threshold receiver).card ≤
      scale * object.missingPorts support threshold receiver - 1) :
    visibleLoads object support threshold receiver ⊆
      payableSet object support threshold scale receiver := by
  classical
  set visibleBlock := object.orderedVertices.filter fun vertex =>
    decide (vertex ∈ visibleLoads object support threshold receiver)
    with visibleBlockDef
  have blockFinset : visibleBlock.toFinset =
      visibleLoads object support threshold receiver := by
    ext vertex
    simp [visibleBlockDef, List.mem_toFinset, object.mem_orderedVertices vertex]
  have blockLength : visibleBlock.length =
      (visibleLoads object support threshold receiver).card := by
    rw [← blockFinset, List.toFinset_card_of_nodup
      (visibleBlockDef ▸ object.orderedVertices_nodup.filter _)]
  have takeAll : visibleBlock.take
      (scale * object.missingPorts support threshold receiver - 1) =
      visibleBlock :=
    List.take_of_length_le (by omega)
  intro vertex member
  have inBlock : vertex ∈ visibleBlock := by
    rw [← List.mem_toFinset, blockFinset]; exact member
  refine List.mem_toFinset.mpr ?_
  unfold visibleFirstOrder
  rw [List.take_append, takeAll]
  exact List.mem_append_left _ inBlock

/-- **`lem:typeA-silent-excess-count` at one receiver.**

*"If `L(w) ≤ c(w)`, then `w` contributes no unpaid routed vertex.  If
`L(w) > c(w)`, then `w` is saturated; since `w` has exactly `q(w)` completion
ports and no port carries `s` visible receiver-entry returns, `L_vis(w) ≤
(s−1)q(w) ≤ c(w)`, so the visible-first order pays every visible routed load
before the payable set is exhausted, and every unpaid routed vertex at `w` is
silent."*

Written without subtraction, that is `1 + L(w) ≤ |𝒰(w)| + s·q(w)`.  The port
hypothesis is needed only at a saturated receiver, exactly as the manuscript
uses it. -/
theorem one_add_routedLoad_le_silentExcess (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    {receiver : object.Vertex}
    (exact : object.degree receiver = threshold)
    (isReceiver : object.IsReceiver support threshold receiver)
    (scalePos : 1 ≤ scale)
    (unsaturatedPorts : object.Saturated support threshold scale receiver →
      ∀ outside ∈ completionPorts object support receiver,
        (visibleLoadsAt object support threshold receiver outside).card + 1 ≤
          scale) :
    1 + object.routedLoad support threshold receiver ≤
      (silentExcess object support threshold scale receiver).card +
        scale * object.missingPorts support threshold receiver := by
  classical
  have portsPos : 1 ≤ object.missingPorts support threshold receiver := by
    unfold FiniteObject.missingPorts
    have := isReceiver.2
    omega
  have capacityPos :
      1 ≤ scale * object.missingPorts support threshold receiver :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
  by_cases saturated : object.Saturated support threshold scale receiver
  · -- The saturated case: the port bound pays every visible load.
    have paid : (visibleLoads object support threshold receiver).card ≤
        scale * object.missingPorts support threshold receiver - 1 := by
      have := card_visibleLoads_le object support threshold scale exact
        (unsaturatedPorts saturated)
      omega
    have contained := visibleLoads_subset_payableSet object support threshold
      scale receiver paid
    -- The whole excess basin is therefore silent.
    have basin : silentExcess object support threshold scale receiver =
        excessBasin object support threshold scale receiver := by
      unfold silentExcess excessBasin
      ext load
      simp only [Finset.mem_sdiff]
      exact ⟨fun ⟨⟨routed, unpaid⟩, _⟩ => ⟨routed, unpaid⟩,
        fun ⟨routed, unpaid⟩ => ⟨⟨routed, unpaid⟩, fun visible =>
          unpaid (contained visible)⟩⟩
    have split :
        (object.routedLoads support threshold receiver).card ≤
          (excessBasin object support threshold scale receiver).card +
            (payableSet object support threshold scale receiver).card := by
      unfold excessBasin
      exact Finset.card_le_card_sdiff_add_card
    have payable := card_payableSet_le object support threshold scale receiver
    rw [object.routedLoad_eq_card, basin]
    omega
  · -- The unsaturated case: the charge is nonnegative outright.
    have := (object.not_saturated_iff support threshold scale receiver).mp
      saturated
    omega

/-! ## The support-level count

Summed over the receivers of the support, the per-receiver inequality is
`lem:typeA-silent-excess-count` itself.  Its right-hand side
`4D_A(X) = ¼|V(X)| − def⁺(X)` scaled by `s` is `|V(X)| − s·def⁺(X)`, so the
statement written without division or subtraction is

  `|V(X)| ≤ S_sil^exc(X) + s·def⁺(X)`.

The manuscript's `n₃ − 3n₂ − 7n₁ − 11n₀` is that same difference read off the
degree profile: a vertex of internal degree `i` contributes `1 − s(δ−i)` to
`|V(X)| − s·def⁺(X)`, which at `δ = 3`, `s = 4` is `1, −3, −7, −11` for
`i = 3, 2, 1, 0`. -/

/-- **`Σ_{w receiver} q(w) = def⁺(X)`.**  A vertex at or above the baseline has
no positive deficiency, so the sum over the receivers is the sum over the whole
support. -/
theorem sum_missingPorts_eq_positiveDeficiency (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) :
    ∑ receiver ∈ object.receivers support threshold,
        object.missingPorts support threshold receiver =
      object.positiveDeficiency support threshold := by
  classical
  unfold FiniteObject.positiveDeficiency FiniteObject.receivers
    FiniteObject.missingPorts
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm.symm
  intro vertex member absent
  have : ¬ object.internalDegree support vertex < threshold := by
    intro lt
    exact absent (Finset.mem_filter.mpr ⟨member, lt⟩)
  omega

/-- **`lem:typeA-silent-excess-count`.**

*"Suppose that no saturated receiver of `X` has a completion port carrying `s`
visible receiver-entry returns, and form the visible-first excess basins.  Then
`S_sil^exc(X) ≥ n_δ − Σ_w c(w) = s·D_A(X)`."*

Cleared of the division and the subtraction, `s·D_A(X) = |V(X)| − s·def⁺(X)`,
so the statement is `|V(X)| ≤ S_sil^exc(X) + s·def⁺(X)`.  The three hypotheses
are the manuscript's own: the support is capped at the baseline and its vertices
sit exactly there (no ambient surplus), the routing is total (`node [88]`), and
no saturated receiver has a port carrying `s` visible returns (the branch this
count lives on). -/
theorem card_le_sum_silentExcess_add_positiveDeficiency
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold scale : Nat) (scalePos : 1 ≤ scale)
    (baseline : ∀ vertex ∈ support, object.degree vertex = threshold)
    (capped : ∀ vertex ∈ support,
      object.internalDegree support vertex ≤ threshold)
    (routed : ∀ vertex ∈ support,
      object.internalDegree support vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? support threshold vertex = some receiver ∧
          object.IsReceiver support threshold receiver)
    (unsaturatedPorts : ∀ receiver : object.Vertex,
      object.IsReceiver support threshold receiver →
      object.Saturated support threshold scale receiver →
      ∀ outside ∈ completionPorts object support receiver,
        (visibleLoadsAt object support threshold receiver outside).card + 1 ≤
          scale) :
    support.card ≤
      (∑ receiver ∈ object.receivers support threshold,
          (silentExcess object support threshold scale receiver).card) +
        scale * object.positiveDeficiency support threshold := by
  classical
  have perReceiver :
      ∑ receiver ∈ object.receivers support threshold,
          (1 + object.routedLoad support threshold receiver) ≤
        ∑ receiver ∈ object.receivers support threshold,
          ((silentExcess object support threshold scale receiver).card +
            scale * object.missingPorts support threshold receiver) := by
    refine Finset.sum_le_sum ?_
    intro receiver member
    have isReceiver := FiniteObject.mem_receivers.mp member
    exact one_add_routedLoad_le_silentExcess object support threshold scale
      (baseline receiver isReceiver.1) isReceiver scalePos
      (unsaturatedPorts receiver isReceiver)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    smul_eq_mul, Nat.mul_one, ← Finset.mul_sum,
    sum_missingPorts_eq_positiveDeficiency object support threshold,
    FiniteObject.sum_routedLoad object support threshold routed]
    at perReceiver
  -- `|R| + |F| = |V(X)|`: the capped support is its receivers and its full
  -- vertices, which is `Graph/TypeADischarge.lean`'s split, not a second one.
  have split := FiniteObject.card_receivers_add_card_fullVertices object support
    threshold capped
  omega

/-- The visible-first order lists exactly the routed loads. -/
theorem mem_visibleFirstOrder (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver vertex : object.Vertex) :
    vertex ∈ visibleFirstOrder object support threshold receiver ↔
      vertex ∈ object.routedLoads support threshold receiver := by
  classical
  unfold visibleFirstOrder
  rw [List.mem_append, List.mem_filter, List.mem_filter]
  simp only [decide_eq_true_eq, FiniteObject.mem_orderedVertices, true_and]
  constructor
  · rintro (vis | ⟨mem, _⟩)
    · exact visibleLoads_subset object support threshold receiver vis
    · exact mem
  · intro mem
    by_cases vis : vertex ∈ visibleLoads object support threshold receiver
    · exact Or.inl vis
    · exact Or.inr ⟨mem, vis⟩

/-- The visible-first order lists each routed load once. -/
theorem visibleFirstOrder_nodup (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) :
    (visibleFirstOrder object support threshold receiver).Nodup := by
  classical
  unfold visibleFirstOrder
  refine List.Nodup.append (object.orderedVertices_nodup.filter _)
    (object.orderedVertices_nodup.filter _) ?_
  intro vertex memLeft memRight
  rw [List.mem_filter] at memLeft memRight
  simp only [decide_eq_true_eq] at memLeft memRight
  exact memRight.2.2 memLeft.2

/-- The visible-first order has length `L(w)`. -/
theorem length_visibleFirstOrder (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) :
    (visibleFirstOrder object support threshold receiver).length =
      (object.routedLoads support threshold receiver).card := by
  classical
  have finset : (visibleFirstOrder object support threshold receiver).toFinset =
      object.routedLoads support threshold receiver := by
    ext vertex
    rw [List.mem_toFinset]
    exact mem_visibleFirstOrder object support threshold receiver vertex
  rw [← finset,
    List.toFinset_card_of_nodup
      (visibleFirstOrder_nodup object support threshold receiver)]

/-- **An unsaturated receiver has no excess**: `L(w) ≤ c(w)` pays every routed
load, so `E(w) = ∅` (`lem:typeA-silent-excess-count`: *"If `L(w) ≤ c(w)`, then
`w` contributes no unpaid routed vertex"*). -/
theorem excessBasin_eq_empty_of_not_saturated (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    {receiver : object.Vertex}
    (unsaturated : ¬ object.Saturated support threshold scale receiver) :
    excessBasin object support threshold scale receiver = ∅ := by
  classical
  have small :=
    (object.not_saturated_iff support threshold scale receiver).mp unsaturated
  have lengthLe : (visibleFirstOrder object support threshold receiver).length ≤
      scale * object.missingPorts support threshold receiver - 1 := by
    rw [length_visibleFirstOrder, ← object.routedLoad_eq_card]
    omega
  have takeAll : (visibleFirstOrder object support threshold receiver).take
      (scale * object.missingPorts support threshold receiver - 1) =
      visibleFirstOrder object support threshold receiver :=
    List.take_of_length_le lengthLe
  unfold excessBasin payableSet
  rw [takeAll]
  refine Finset.sdiff_eq_empty_iff_subset.mpr ?_
  intro vertex member
  rw [List.mem_toFinset]
  exact (mem_visibleFirstOrder object support threshold receiver vertex).mpr member

/-- An unsaturated receiver contributes no silent excess. -/
theorem silentExcess_eq_empty_of_not_saturated (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    {receiver : object.Vertex}
    (unsaturated : ¬ object.Saturated support threshold scale receiver) :
    silentExcess object support threshold scale receiver = ∅ := by
  unfold silentExcess
  rw [excessBasin_eq_empty_of_not_saturated object support threshold scale
    unsaturated]
  exact Finset.empty_sdiff _

/-! ## The reduced ledger: the visible-first machinery at a peeling stage

`def:typeA-peeling-reduced-ledger` deletes the peeled loads from the receiver
ledger.  The reduced order, payable set, excess basin, and silent excess below
are the visible-first machinery of `def:typeA-excess-basin` on
`ℒ(w) ∖ P₄(w)`.  The staged count below is silence-free: the manuscript's
displayed inequality `Σ_w (L(w) − c(w)) ≥ s·D_A(X)` never uses silence, so no
port hypothesis occurs (`rem:unified-covers-exit4`). -/

/-- Membership in a `take` prefix is monotone in the prefix length. -/
theorem mem_take_succ_of_mem_take {α : Type u} :
    ∀ (l : List α) (n : Nat) (a : α), a ∈ l.take n → a ∈ l.take (n + 1) := by
  intro l
  induction l with
  | nil => intro n a mem; simp at mem
  | cons x xs ih =>
      intro n a mem
      cases n with
      | zero => simp at mem
      | succ m =>
          rw [List.take_succ_cons, List.mem_cons] at mem
          rw [List.take_succ_cons, List.mem_cons]
          rcases mem with rfl | tail
          · exact Or.inl rfl
          · exact Or.inr (ih m a tail)

/-- A surviving member of a paid prefix stays in the paid prefix of the
reduced order: `take`/`filter` monotonicity. -/
theorem mem_take_filter {α : Type u} (p : α → Bool) :
    ∀ (l : List α) (c : Nat) (a : α), a ∈ l.take c → p a = true →
      a ∈ (l.filter p).take c := by
  intro l
  induction l with
  | nil => intro c a mem _; simp at mem
  | cons x xs ih =>
      intro c a mem pa
      cases c with
      | zero => simp at mem
      | succ n =>
          rw [List.take_succ_cons, List.mem_cons] at mem
          rcases mem with rfl | tail
          · rw [List.filter_cons_of_pos pa, List.take_succ_cons]
            exact List.mem_cons_self
          · by_cases px : p x = true
            · rw [List.filter_cons_of_pos px, List.take_succ_cons]
              exact List.mem_cons_of_mem _ (ih n a tail pa)
            · rw [List.filter_cons_of_neg (by simpa using px)]
              exact ih (n + 1) a (mem_take_succ_of_mem_take xs n a tail) pa

/-- The reduced visible-first order: the peeled loads removed. -/
noncomputable def visibleFirstOrderReduced (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) (excluded : Finset object.Vertex) :
    List object.Vertex := by
  classical
  exact (visibleFirstOrder object support threshold receiver).filter
    fun vertex => decide (vertex ∉ excluded)

/-- `A^{P₄}(w)`: the payable set of the reduced ledger. -/
noncomputable def payableSetReduced (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (excluded : Finset object.Vertex) :
    Finset object.Vertex := by
  classical
  exact ((visibleFirstOrderReduced object support threshold receiver
      excluded).take
    (scale * object.missingPorts support threshold receiver - 1)).toFinset

/-- `E^{P₄}(w)`: the excess basin of the reduced ledger. -/
noncomputable def excessBasinReduced (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (excluded : Finset object.Vertex) :
    Finset object.Vertex := by
  classical
  exact ((object.routedLoads support threshold receiver) \ excluded) \
    payableSetReduced object support threshold scale receiver excluded

/-- **Under the manuscript's port bound the whole excess basin is silent**:
`E(w) = 𝒰(w)` — "every unpaid routed vertex at `w` is silent"
(`lem:typeA-silent-excess-count`).  On a silent-first receiver the excess-based
census therefore coincides with the paper's `𝒰(w)`-indexed one. -/
theorem silentExcess_eq_excessBasin (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    {receiver : object.Vertex}
    (exact : object.degree receiver = threshold)
    (isReceiver : object.IsReceiver support threshold receiver)
    (scalePos : 1 ≤ scale)
    (ports : object.Saturated support threshold scale receiver →
      ∀ outside ∈ completionPorts object support receiver,
        (visibleLoadsAt object support threshold receiver outside).card + 1 ≤
          scale) :
    silentExcess object support threshold scale receiver =
      excessBasin object support threshold scale receiver := by
  classical
  by_cases saturated : object.Saturated support threshold scale receiver
  · have portsPos : 1 ≤ object.missingPorts support threshold receiver := by
      unfold FiniteObject.missingPorts
      have := isReceiver.2
      omega
    have capacityPos :
        1 ≤ scale * object.missingPorts support threshold receiver :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have paid : (visibleLoads object support threshold receiver).card ≤
        scale * object.missingPorts support threshold receiver - 1 := by
      have := card_visibleLoads_le object support threshold scale exact
        (ports saturated)
      omega
    have contained := visibleLoads_subset_payableSet object support threshold
      scale receiver paid
    unfold silentExcess excessBasin
    ext load
    simp only [Finset.mem_sdiff]
    exact ⟨fun ⟨⟨routed, unpaid⟩, _⟩ => ⟨routed, unpaid⟩,
      fun ⟨routed, unpaid⟩ => ⟨⟨routed, unpaid⟩, fun visible =>
        unpaid (contained visible)⟩⟩
  · rw [silentExcess_eq_empty_of_not_saturated object support threshold scale
      saturated,
      excessBasin_eq_empty_of_not_saturated object support threshold scale
      saturated]

/-- **A surviving reduced excess load is an original excess load**:
`E^{P₄}(w) ⊆ E(w) ∖ P₄(w)` — peeling only promotes loads into the payable
prefix. -/
theorem excessBasinReduced_subset (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (excluded : Finset object.Vertex) :
    excessBasinReduced object support threshold scale receiver excluded ⊆
      (excessBasin object support threshold scale receiver) \ excluded := by
  classical
  intro load member
  have routedNotEx := (Finset.mem_sdiff.1 member).1
  have unpaidRed := (Finset.mem_sdiff.1 member).2
  have routed := (Finset.mem_sdiff.1 routedNotEx).1
  have notEx := (Finset.mem_sdiff.1 routedNotEx).2
  refine Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨routed, ?_⟩, notEx⟩
  intro paidOrig
  apply unpaidRed
  rw [payableSetReduced, List.mem_toFinset]
  refine mem_take_filter _ _ _ _ ?_ (by simpa using notEx)
  unfold payableSet at paidOrig
  exact List.mem_toFinset.1 paidOrig

/-- **The excess count at one receiver of the reduced ledger** —
`lem:typeA-silent-excess-count`'s displayed count `|E^{P₄}(w)| ≥ L₄(w) − c(w)`,
written without subtraction and with the recorded peels restored:
`1 + L(w) ≤ |E^{P₄}(w)| + |P₄(w) ∩ ℒ(w)| + s·q(w)`.  No port hypothesis
occurs: silence is never used in the count (`rem:unified-covers-exit4`). -/
theorem one_add_routedLoad_le_excessBasinReduced (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    {receiver : object.Vertex}
    (isReceiver : object.IsReceiver support threshold receiver)
    (scalePos : 1 ≤ scale)
    (excluded : Finset object.Vertex) :
    1 + object.routedLoad support threshold receiver ≤
      (excessBasinReduced object support threshold scale receiver
          excluded).card +
        (excluded ∩ object.routedLoads support threshold receiver).card +
        scale * object.missingPorts support threshold receiver := by
  classical
  set L := object.routedLoads support threshold receiver with Ldef
  have portsPos : 1 ≤ object.missingPorts support threshold receiver := by
    unfold FiniteObject.missingPorts
    have := isReceiver.2
    omega
  have capacityPos :
      1 ≤ scale * object.missingPorts support threshold receiver :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have interSplit : (L \ excluded).card + (L ∩ excluded).card = L.card :=
    Finset.card_sdiff_add_card_inter L excluded
  have splitRed : (L \ excluded).card ≤
      (excessBasinReduced object support threshold scale receiver
          excluded).card +
        (payableSetReduced object support threshold scale receiver
          excluded).card := by
    unfold excessBasinReduced
    exact Finset.card_le_card_sdiff_add_card
  have payableLe :
      (payableSetReduced object support threshold scale receiver
          excluded).card ≤
        scale * object.missingPorts support threshold receiver - 1 := by
    unfold payableSetReduced
    refine le_trans (List.toFinset_card_le _) ?_
    simpa using
      (List.length_take_le
        (scale * object.missingPorts support threshold receiver - 1)
        (visibleFirstOrderReduced object support threshold receiver excluded))
  rw [object.routedLoad_eq_card, ← Ldef, Finset.inter_comm excluded L]
  omega

/-- **The silence-free reduced count, summed**
(`lem:typeA-silent-excess-count`'s arithmetic core):
`|V(X)| ≤ Σ_w |E^{P₄}(w)| + s·def⁺(X) + Σ_w |P₄(w) ∩ ℒ(w)|`. -/
theorem card_le_sum_excessBasinReduced_add_positiveDeficiency
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold scale : Nat) (scalePos : 1 ≤ scale)
    (capped : ∀ vertex ∈ support,
      object.internalDegree support vertex ≤ threshold)
    (routed : ∀ vertex ∈ support,
      object.internalDegree support vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? support threshold vertex = some receiver ∧
          object.IsReceiver support threshold receiver)
    (excludedAt : object.Vertex → Finset object.Vertex) :
    support.card ≤
      (∑ receiver ∈ object.receivers support threshold,
          (excessBasinReduced object support threshold scale receiver
            (excludedAt receiver)).card) +
        scale * object.positiveDeficiency support threshold +
        ∑ receiver ∈ object.receivers support threshold,
          (excludedAt receiver ∩
            object.routedLoads support threshold receiver).card := by
  classical
  have perReceiver :
      ∑ receiver ∈ object.receivers support threshold,
          (1 + object.routedLoad support threshold receiver) ≤
        ∑ receiver ∈ object.receivers support threshold,
          ((excessBasinReduced object support threshold scale receiver
              (excludedAt receiver)).card +
            (excludedAt receiver ∩
              object.routedLoads support threshold receiver).card +
            scale * object.missingPorts support threshold receiver) := by
    refine Finset.sum_le_sum ?_
    intro receiver member
    have isReceiver := FiniteObject.mem_receivers.mp member
    exact one_add_routedLoad_le_excessBasinReduced object support threshold
      scale isReceiver scalePos (excludedAt receiver)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, smul_eq_mul, Nat.mul_one, ← Finset.mul_sum,
    sum_missingPorts_eq_positiveDeficiency object support threshold,
    FiniteObject.sum_routedLoad object support threshold routed]
    at perReceiver
  have split := FiniteObject.card_receivers_add_card_fullVertices object support
    threshold capped
  omega

end Hypostructure.Graph.VisibleEntry
