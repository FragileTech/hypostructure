import Hypostructure.Graph.DecoratedHandoffEnvelope

/-!
# Connector tails cut at their first entry into a core

`lem:typeA-high-degree-handoff` (tex 11110-11131): for each continuation class
leaving the decoration `z` through a next neighbour `a`, the handoff arm
`A_{z,a}` is "the remaining connector tail from `a` to its first-entry receiver
in `X`; if `a ∈ X`, this tail has length `0`".  Here a tail is any list of
vertices beginning at `a`, and `firstEntryArm core tail` is its prefix through
its first vertex in the core.

`envelopeOfTails` is `def:decorated-fan-envelope` at one decoration `z` whose
assigned first neighbours carry such tails: when every tail is a simple walk of
the object that avoids `z` and meets the core, and the assigned neighbours are
fan-safe, the cut tails are handoff arms.  The full handoff path `z a A_{z,a}`
is then simple.  This module is proof-agnostic.
-/

namespace Hypostructure.Graph.DecoratedHandoff

universe u

variable {α : Type u} [DecidableEq α]

/-- The prefix of a tail through its first vertex in the core. -/
def firstEntryArm (core : Finset α) (tail : List α) : List α :=
  tail.take (tail.findIdx (fun vertex => decide (vertex ∈ core)) + 1)

theorem firstEntryArm_head? (core : Finset α) (tail : List α) :
    (firstEntryArm core tail).head? = tail.head? := by
  cases tail with
  | nil => rfl
  | cons first rest => simp [firstEntryArm]

theorem firstEntryArm_sublist (core : Finset α) (tail : List α) :
    (firstEntryArm core tail).Sublist tail :=
  List.take_sublist _ _

theorem firstEntryArm_isChain {R : α → α → Prop} (core : Finset α) {tail : List α}
    (chain : tail.IsChain R) : (firstEntryArm core tail).IsChain R :=
  chain.take _

theorem firstEntryArm_nodup (core : Finset α) {tail : List α} (nodup : tail.Nodup) :
    (firstEntryArm core tail).Nodup :=
  nodup.sublist (firstEntryArm_sublist core tail)

/-- A tail that meets the core lands in it: the arm ends at the tail's first
core vertex. -/
theorem firstEntryArm_lands (core : Finset α) {tail : List α}
    (meets : ∃ vertex ∈ tail, vertex ∈ core) :
    ∃ terminal, (firstEntryArm core tail).getLast? = some terminal ∧
      terminal ∈ core := by
  have exists' : ∃ vertex ∈ tail, decide (vertex ∈ core) = true := by
    obtain ⟨vertex, member, inCore⟩ := meets
    exact ⟨vertex, member, by simpa using inCore⟩
  have bound := List.findIdx_lt_length_of_exists exists'
  refine ⟨tail[tail.findIdx (fun vertex => decide (vertex ∈ core))], ?_, ?_⟩
  · rw [firstEntryArm, List.getLast?_eq_getElem?, List.length_take,
      Nat.min_eq_left (by omega)]
    simp
  · simpa using List.findIdx_getElem (w := bound)

/-- Every core vertex of the arm is its terminal. -/
theorem firstEntryArm_interior (core : Finset α) {tail : List α}
    {vertex : α} (member : vertex ∈ firstEntryArm core tail) (inCore : vertex ∈ core) :
    (firstEntryArm core tail).getLast? = some vertex := by
  obtain ⟨position, positionLt, positionEq⟩ := List.getElem_of_mem member
  have takeLength := positionLt
  unfold firstEntryArm at takeLength positionEq ⊢
  rw [List.length_take] at takeLength
  have positionTail : position < tail.length := by omega
  have atPosition : tail[position] = vertex := by
    rw [← positionEq, List.getElem_take]
  have positionEqIndex :
      position = tail.findIdx (fun vertex => decide (vertex ∈ core)) := by
    by_contra different
    have before : position < tail.findIdx (fun vertex => decide (vertex ∈ core)) := by
      omega
    have notCore := List.not_of_lt_findIdx before
    have key : tail[position]'positionTail ∈ core := atPosition ▸ inCore
    exact (decide_eq_false_iff_not.mp notCore) key
  have armLength : (tail.take
      (tail.findIdx (fun vertex => decide (vertex ∈ core)) + 1)).length =
        position + 1 := by
    rw [List.length_take]
    omega
  rw [List.getLast?_eq_getElem?, armLength, Nat.add_sub_cancel, ← positionEq,
    List.getElem?_eq_getElem (by rw [armLength]; omega)]
  rfl

theorem not_mem_firstEntryArm (core : Finset α) {tail : List α} {vertex : α}
    (absent : vertex ∉ tail) : vertex ∉ firstEntryArm core tail :=
  fun member => absent ((firstEntryArm_sublist core tail).subset member)

variable {object : FiniteObject.{u}}

/-- **`def:decorated-fan-envelope` at one decoration from connector tails**
(`lem:typeA-high-degree-handoff`): the decoration `centre`, the assigned first
neighbours `assigned`, and for each assigned neighbour `a` its tail, cut at its
first entry into the core. -/
def envelopeOfTails (LengthOK : Nat → Prop)
    (HighDegree : object.Vertex → Prop)
    (Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop)
    [DecidableEq object.Vertex]
    (core : Finset object.Vertex) (centre : object.Vertex) (high : HighDegree centre)
    (assigned : Finset object.Vertex) (nonempty : assigned.Nonempty)
    (adjacent : ∀ first ∈ assigned, object.graph.Adj centre first)
    (tail : object.Vertex → List object.Vertex)
    (issued : ∀ first ∈ assigned, (tail first).head? = some first)
    (chain : ∀ first ∈ assigned, (tail first).IsChain object.graph.Adj)
    (nodup : ∀ first ∈ assigned, (tail first).Nodup)
    (avoidsCentre : ∀ first ∈ assigned, centre ∉ tail first)
    (meets : ∀ first ∈ assigned, ∃ vertex ∈ tail first, vertex ∈ core)
    (fanSafe : ∀ first ∈ assigned, ∀ second ∈ assigned, first ≠ second →
      FanSafe object LengthOK Absorbing centre first second) :
    Envelope object LengthOK HighDegree Absorbing where
  core := core
  decorations := {centre}
  decorations_high := by
    intro current member
    rw [Finset.mem_singleton] at member
    exact member ▸ high
  assigned := fun _ => assigned
  assigned_nonempty := fun _ _ => nonempty
  assigned_adj := by
    intro current member first firstMember
    rw [Finset.mem_singleton] at member
    exact member ▸ adjacent first firstMember
  arm := fun _ first => firstEntryArm core (tail first)
  arm_issued := by
    intro _ _ first firstMember
    rw [firstEntryArm_head?]
    exact issued first firstMember
  arm_chain := fun _ _ first firstMember =>
    firstEntryArm_isChain core (chain first firstMember)
  arm_nodup := fun _ _ first firstMember =>
    firstEntryArm_nodup core (nodup first firstMember)
  arm_lands := fun _ _ first firstMember =>
    firstEntryArm_lands core (meets first firstMember)
  arm_interior := by
    intro current member first firstMember vertex vertexMember alternative
    rw [Finset.mem_singleton] at member
    subst member
    have absent := not_mem_firstEntryArm core (avoidsCentre first firstMember)
    rcases alternative with inCore | inDecorations | isCentre
    · exact firstEntryArm_interior core vertexMember inCore
    · rw [Finset.mem_singleton] at inDecorations
      exact (absent (inDecorations ▸ vertexMember)).elim
    · exact (absent (isCentre ▸ vertexMember)).elim
  fanSafe := by
    intro current member first firstMember second secondMember different
    rw [Finset.mem_singleton] at member
    subst member
    exact fanSafe first firstMember second secondMember different

@[simp] theorem envelopeOfTails_core (LengthOK : Nat → Prop)
    (HighDegree : object.Vertex → Prop)
    (Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop)
    [DecidableEq object.Vertex] (core : Finset object.Vertex) (centre : object.Vertex)
    (high : HighDegree centre) (assigned : Finset object.Vertex) (nonempty)
    (adjacent) (tail : object.Vertex → List object.Vertex) (issued chain nodup avoidsCentre
      meets fanSafe) :
    (envelopeOfTails LengthOK HighDegree Absorbing core centre high assigned nonempty
      adjacent tail issued chain nodup avoidsCentre meets fanSafe).core = core := rfl

/-- The full handoff path `centre, a, A_{centre,a}` of such an envelope is
simple: no arm returns to the decoration. -/
theorem centre_not_mem_arm_envelopeOfTails (LengthOK : Nat → Prop)
    (HighDegree : object.Vertex → Prop)
    (Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop)
    [DecidableEq object.Vertex] (core : Finset object.Vertex) (centre : object.Vertex)
    (high : HighDegree centre) (assigned : Finset object.Vertex) (nonempty)
    (adjacent) (tail : object.Vertex → List object.Vertex) (issued chain nodup avoidsCentre
      meets fanSafe) :
    ∀ first ∈ assigned, centre ∉
      (envelopeOfTails LengthOK HighDegree Absorbing core centre high assigned nonempty
        adjacent tail issued chain nodup avoidsCentre meets fanSafe).arm centre first :=
  fun first firstMember =>
    not_mem_firstEntryArm core (avoidsCentre first firstMember)

end Hypostructure.Graph.DecoratedHandoff
