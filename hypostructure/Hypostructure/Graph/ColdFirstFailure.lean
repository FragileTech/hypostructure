import Hypostructure.Graph.ColdCorridor
import Hypostructure.Graph.WindowPacking
import Hypostructure.Graph.BoundaryDemand

/-!
# The first failure of a cold return corridor

`def:cold-corridor-first-failure` closes with the five alternatives

> The *first failure* of `ε` is the first initial segment, in the lexicographic
> order along the corridor, at which one of the following happens:
>
> (F1) a compatible completion through a cold-window offset realizes a
>      power-of-two cycle;
> (F2) two prefixes with the same displayed boundary data have different target
>      response against some compatible outside context;
> (F3) two prefixes have the same exact target response against every outside
>      context and one gives a strictly smaller proper representative;
> (F4) the corridor first enters a declared Type B handoff support or the
>      route-8 support already recorded in the incoming ledger;
> (F5) no earlier alternative occurs and either the corridor reaches its
>      successor boundary stub before `Q_cold + 1` states have been read, or a
>      cold corridor state repeats.

and `lem:cold-corridor-first-failure` proves that one of them always happens and
routes each:

> (i) case (F1) is a dyadic cycle in `G`;
> (ii) case (F2) is a target-defective quotient, hence belongs to the sparse
>      exit or to the exit-(4) ledger;
> (iii) case (F3) is a target-complete compression of a proper support;
> (iv) case (F4) is an already named Type B or route-8 handoff;
> (v) case (F5) is a cold bounded germ.

This module is those five clauses and that lemma.  The existence half is the
manuscript's own dichotomy -- reach the successor stub inside `Q_cold` states,
or read `Q_cold + 1` of them and repeat -- and *not* a definition of (F5) as the
complement of the other four, which would make the lemma a tautology.
-/

namespace Hypostructure.Graph.ColdCorridor

open Hypostructure

universe u

/-! ## The cold window a corridor returns through

A completion of clause (F1) runs "through a cold-window offset", so the window
has to be present as a placed path and not only as a support.  A `Window` is
that placement: the manuscript's induced `P₁₃` with its positions in order. -/

/-- **A placed cold window**: the `order` positions of an induced window, in
order, with consecutive positions adjacent in the object. -/
structure Window (object : FiniteObject.{u}) (order : Nat) where
  /-- The window's positions, placed in the object. -/
  place : Fin order → object.Vertex
  /-- Distinct positions are distinct vertices. -/
  injective : Function.Injective place
  /-- Consecutive positions are adjacent: the window is a path. -/
  adjacent : ∀ (index : Nat) (bound : index + 1 < order),
    object.graph.Adj (place ⟨index, by omega⟩) (place ⟨index + 1, bound⟩)

namespace Window

variable {object : FiniteObject.{u}} {order : Nat}

/-- **The walk along the window** from one position forward by a number of
steps.  This is the "cold-window offset" segment a compatible completion closes
through. -/
def segment (window : Window object order) :
    ∀ (start steps : Nat) (bound : start + steps < order),
      object.graph.Walk (window.place ⟨start, by omega⟩)
        (window.place ⟨start + steps, bound⟩)
  | start, 0, _bound =>
      SimpleGraph.Walk.nil (G := object.graph)
        (u := window.place ⟨start, by omega⟩)
  | start, steps + 1, bound =>
      (SimpleGraph.Walk.cons (window.adjacent start (by omega))
        (segment window (start + 1) steps (by omega))).copy rfl
        (congrArg window.place
          (Fin.ext (show start + 1 + steps = start + (steps + 1) by omega)))

/-- The walk along the window has exactly the number of steps it took. -/
theorem segment_length (window : Window object order) :
    ∀ (start steps : Nat) (bound : start + steps < order),
      (window.segment start steps bound).length = steps
  | _start, 0, _bound => by simp [segment]
  | start, steps + 1, bound => by
      simp [segment, segment_length window (start + 1) steps (by omega)]

end Window

/-! ## (F1): a completion through a cold-window offset realizes the target

The completion the manuscript displays is a closed walk of the object:

  the window position the entry stub lands on, along the stub to its outside
  foot, along the corridor prefix to its head, back into the window by a return
  adjacency, and along the window between the two offsets.

Nothing is supplied: the walk is built, and (F1)'s validity is that it is a
cycle of accepted length. -/

namespace Corridor

variable {object : FiniteObject.{u}} {windows component : Finset object.Vertex}
variable {order : Nat}

/-- The corridor prefix at a segment, as a walk of the ambient object. -/
noncomputable def prefixWalk (corridor : Corridor object windows component)
    (segment : corridor.Segment) :
    object.graph.Walk corridor.entryStub.1 (corridor.head segment) :=
  ((corridor.inside.1.take segment.1).map
      (object.induceEmbedding component).toHom).copy rfl rfl

/-- **The displayed completion of clause (F1).**

`entryOffset` is the window position the entry stub lands on and `returnOffset`
is the position the prefix's head returns to; `entryAdj` is the stub itself and
`returnAdj` the return adjacency.  The result is a closed walk at the entry
position, and clause (F1) asks it to be a cycle of accepted length. -/
noncomputable def displayedCompletion
    (corridor : Corridor object windows component) (window : Window object order)
    (entryOffset returnOffset : Nat)
    (ordered : entryOffset + returnOffset < order)
    (segment : corridor.Segment)
    (entryAdj : object.graph.Adj (window.place ⟨entryOffset, by omega⟩)
      corridor.entryStub.1)
    (returnAdj : object.graph.Adj (corridor.head segment)
      (window.place ⟨entryOffset + returnOffset, ordered⟩)) :
    object.graph.Walk (window.place ⟨entryOffset, by omega⟩)
      (window.place ⟨entryOffset, by omega⟩) :=
  (SimpleGraph.Walk.cons entryAdj
      ((corridor.prefixWalk segment).append
        (SimpleGraph.Walk.cons returnAdj
          (window.segment entryOffset returnOffset ordered).reverse)))

/-- **Clause (F1)** at an initial segment: some compatible completion through a
cold-window offset is a cycle of accepted length. -/
def FirstFailureCycle (corridor : Corridor object windows component)
    (window : Window object order) (LengthOK : Nat → Prop)
    (segment : corridor.Segment) : Prop :=
  ∃ (entryOffset returnOffset : Nat) (ordered : entryOffset + returnOffset < order)
    (entryAdj : object.graph.Adj (window.place ⟨entryOffset, by omega⟩)
      corridor.entryStub.1)
    (returnAdj : object.graph.Adj (corridor.head segment)
      (window.place ⟨entryOffset + returnOffset, ordered⟩)),
    (corridor.displayedCompletion window entryOffset returnOffset ordered segment
        entryAdj returnAdj).IsCycle ∧
      LengthOK (corridor.displayedCompletion window entryOffset returnOffset
        ordered segment entryAdj returnAdj).length

/-- **`lem:cold-corridor-first-failure` (i): "case (F1) is a dyadic cycle in
`G`".**

*"The displayed completion is literally a cycle of power-of-two length in `G`,
impossible in a counterexample."*  Nothing is transported: the walk is already a
walk of the object, so the cycle certificate is the completion itself. -/
theorem hasCycleWithLength_of_firstFailureCycle
    {corridor : Corridor object windows component} {window : Window object order}
    {LengthOK : Nat → Prop} {segment : corridor.Segment}
    (failure : corridor.FirstFailureCycle window LengthOK segment) :
    Graph.HasCycleWithLength LengthOK object := by
  obtain ⟨entryOffset, returnOffset, ordered, entryAdj, returnAdj, isCycle, accepted⟩ :=
    failure
  exact ⟨{ vertex := window.place ⟨entryOffset, by omega⟩
           walk := corridor.displayedCompletion window entryOffset returnOffset
             ordered segment entryAdj returnAdj
           isCycle := isCycle
           length_ok := accepted }⟩

/-! ## (F2): different target response against some compatible outside context

Clause (F2) is *"two prefixes with the same displayed boundary data have
different target response against some compatible outside context"*, and
`lem:cold-corridor-first-failure` (ii) routes it: *"the actual quotient is valid
only for the current outside context and fails for another compatible context.
By `lem:context-universality`, this is not target-complete, so it is a
target-defective quotient."*

The distinguishing context is quantified, not collapsed to one ambient
evaluation: `Response.TargetDefect` is `∃ outside, ¬(Target (glue left outside)
↔ Target (glue right outside))` over *all* outside contexts of the shared
interface.  The carrier is a parameter, so the clause holds at every reading of
the corridor's responses. -/

/-- **Clause (F2)** at two initial segments, against a reading of their
responses.

It is not a new object: it is `def:cold-corridor-first-failure`'s own recorded
discrepancy, `Presentation.FirstFailureResponse`, read at the two segments.  The
definition names the same thing once. -/
def FirstFailureDefect {boundary : Graph.Boundary.{u}} {S : DeclaredSignature}
    (corridor : Corridor object windows component)
    (presentation : Presentation.{u} S object)
    (index : corridor.Segment → presentation.Segment)
    (Target : Graph.FiniteObject.{u} → Prop)
    (carrier : presentation.Segment → Graph.BoundaryPiece boundary)
    (left right : corridor.Segment) : Prop :=
  presentation.FirstFailureResponse Target carrier (index left) (index right)

/-- **`lem:cold-corridor-first-failure` (ii), through `lem:context-universality`:
"case (F2) is a target-defective quotient".**

*"If some context `Y₀` distinguished `r₁` and `r₂`, then one of the two gluings
would contain a power-of-two cycle and the other would not.  The quotient would
fail to preserve the target predicate for `Y₀` and therefore would not be
target-complete."*  So an identification of the two prefixes is not
target-complete in *any* immutable profile fibre. -/
theorem not_targetComplete_of_firstFailureDefect {boundary : Graph.Boundary.{u}}
    {S : DeclaredSignature}
    {corridor : Corridor object windows component}
    {presentation : Presentation.{u} S object}
    {index : corridor.Segment → presentation.Segment}
    {Target : Graph.FiniteObject.{u} → Prop}
    {carrier : presentation.Segment → Graph.BoundaryPiece boundary}
    {left right : corridor.Segment} {Profile : Type}
    {profile : Graph.BoundaryPiece boundary → Profile}
    (failure : FirstFailureDefect corridor presentation index Target carrier
      left right) :
    ¬ Graph.Response.TargetComplete profile Target
      (carrier (index left)) (carrier (index right)) :=
  Graph.Response.notTargetComplete_of_targetDefect failure.2

/-- **The (F2)-free reading is context-equivalent.**  This is the other half of
`lem:context-universality` and the step `lem:cold-same-interface-table`'s neutral
row consumes: with the discrepancy excluded, two prefixes carrying the same cold
corridor state have the same target response against every compatible
context. -/
theorem contextEquivalent_of_not_firstFailureDefect {boundary : Graph.Boundary.{u}}
    {S : DeclaredSignature}
    {corridor : Corridor object windows component}
    {presentation : Presentation.{u} S object}
    {index : corridor.Segment → presentation.Segment}
    {Target : Graph.FiniteObject.{u} → Prop}
    {carrier : presentation.Segment → Graph.BoundaryPiece boundary}
    {left right : corridor.Segment}
    (excluded : ¬ FirstFailureDefect corridor presentation index Target carrier
      left right)
    (same : presentation.state (index left) = presentation.state (index right)) :
    Graph.Response.ContextEquivalent Target
      (carrier (index left)) (carrier (index right)) :=
  presentation.contextEquivalent_of_state_eq excluded same

/-! ## (F3): a strictly smaller proper representative

Clause (F3) is *"two prefixes have the same exact target response against every
outside context and one gives a strictly smaller proper representative"*, and
`lem:cold-corridor-first-failure` (iii) routes it: *"context-universality holds
and the displayed representative is strictly smaller while preserving the
boundary-degree profile and the exact target response.  Thus it satisfies
`def:proper-quotient-representative` and is forbidden by `lem:replacement`,
`cor:uncompressible`."*

The structure below carries the *pair*.  The earlier prefix is not an unrelated
existential: it is named, it is earlier along the corridor, it carries the same
cold corridor state -- which is what makes the two same-interface -- and its own
boundary piece is the replacement.  Every remaining field is a clause of
`def:proper-quotient-representative`. -/

/-- **Clause (F3)** at a corridor: a named earlier prefix whose own piece is a
strictly smaller proper representative of a later one. -/
structure FirstFailureCompression {S : DeclaredSignature}
    (corridor : Corridor object windows component)
    (presentation : Presentation.{u} S object)
    (index : corridor.Segment → presentation.Segment)
    (Baseline Target : Graph.FiniteObject.{u} → Prop)
    (support : corridor.Segment → Finset object.Vertex) where
  /-- The later prefix, the one being compressed. -/
  stage : corridor.Segment
  /-- The earlier prefix, whose piece is the smaller representative. -/
  candidate : corridor.Segment
  /-- "One gives a strictly smaller proper representative": the candidate comes
  first in the lexicographic order along the corridor. -/
  earlier : candidate.1 < stage.1
  /-- The two prefixes carry the same cold corridor state, so they are
  same-interface. -/
  sameState : presentation.state (index candidate) = presentation.state (index stage)
  /-- The later prefix's support is a proper connected support of the object. -/
  connected : Graph.SupportComponents.Connected.ConnectedOn object (support stage)
  proper : ∃ vertex, vertex ∉ support stage
  /-- The candidate's own boundary piece, at the later prefix's interface. -/
  replacement :
    Graph.BoundaryPiece (rowAtom object (support stage) connected proper).interface
  /-- `def:proper-quotient-representative` (b): the boundary-degree profile is
  preserved. -/
  sameProfile :
    replacement.boundaryDegreeProfile =
      (rowAtom object (support stage) connected proper).piece.boundaryDegreeProfile
  /-- The replacement meets the standing baseline. -/
  baseline :
    Baseline (glue replacement (rowAtom object (support stage) connected proper).outside)
  /-- "Strictly smaller in the lexicographic order used for the minimal
  counterexample." -/
  smaller :
    (glue replacement
      (rowAtom object (support stage) connected proper).outside).LexicographicallySmaller
      object
  /-- "The same exact target response against every outside context." -/
  contextUniversal :
    ∀ outside, Target (glue replacement outside) ↔
      Target (glue (rowAtom object (support stage) connected proper).piece outside)

/-- **Clause (F3) occurs** at a corridor: some such pair exists.  The structure
carries data, so the proposition the branch denies is its inhabitation. -/
def FirstFailureCompression.Occurs {S : DeclaredSignature}
    (corridor : Corridor object windows component)
    (presentation : Presentation.{u} S object)
    (index : corridor.Segment → presentation.Segment)
    (Baseline Target : Graph.FiniteObject.{u} → Prop)
    (support : corridor.Segment → Finset object.Vertex) : Prop :=
  Nonempty (FirstFailureCompression corridor presentation index Baseline Target
    support)

namespace FirstFailureCompression

variable {S : DeclaredSignature}
variable {corridor : Corridor object windows component}
variable {presentation : Presentation.{u} S object}
variable {index : corridor.Segment → presentation.Segment}
variable {Baseline Target : Graph.FiniteObject.{u} → Prop}
variable {support : corridor.Segment → Finset object.Vertex}

/-- **`lem:cold-corridor-first-failure` (iii): "case (F3) is a target-complete
compression of a proper support".**

Every clause of `CompressibleSupport` is a field of the pair, and the conversion
projects those fields directly. -/
theorem compressibleSupport
    (failure : FirstFailureCompression corridor presentation index Baseline Target
      support) :
    Graph.Strategy.InterfaceReplacement.CompressibleSupport Baseline Target object
      (support failure.stage) :=
  ⟨failure.connected, failure.proper, failure.replacement, failure.sameProfile,
    failure.baseline, failure.smaller, failure.contextUniversal⟩

/-- **And `cor:uncompressible` forbids it.**  On a selected minimal
counterexample no proper support admits a target-complete compression, so (F3)
cannot occur -- which is what makes the corridor continue past it. -/
theorem elim
    (uncompressible : ∀ region : Finset object.Vertex,
      ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport Baseline Target
        object region)
    (failure : FirstFailureCompression corridor presentation index Baseline Target
      support) : False :=
  uncompressible (support failure.stage) failure.compressibleSupport

/-- **(F3) does not occur** when no proper support of the object is
compressible. -/
theorem not_occurs
    (uncompressible : ∀ region : Finset object.Vertex,
      ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport Baseline Target
        object region) :
    ¬ Occurs corridor presentation index Baseline Target support :=
  fun ⟨failure⟩ => failure.elim uncompressible

end FirstFailureCompression

/-! ## (F4): the corridor enters a declared handoff support

Clause (F4) is *"the corridor first enters a declared Type B handoff support or
the route-8 support already recorded in the incoming ledger"*, and
`lem:cold-corridor-first-failure` (iv) routes it: *"the corridor has reached
precisely one of the declared interfaces of `def:decorated-fan-envelope` or the
route-8 support, so the charge is transferred to the already existing
Type B or route-8 ledger."*

The ledger interface is a predicate -- it is *"already recorded"* upstream, so
it is supplied by the ledger and never manufactured here.  "First enters" is
encoded: no earlier prefix has met any declared interface. -/

/-- **Clause (F4)**: the corridor *first* enters a declared handoff support at
this initial segment. -/
def FirstFailureHandoff (corridor : Corridor object windows component)
    (Handoff : Finset object.Vertex → Prop) (segment : corridor.Segment) : Prop :=
  (∃ support, Handoff support ∧ corridor.head segment ∈ support) ∧
    ∀ earlier : corridor.Segment, earlier.1 < segment.1 →
      ∀ support, Handoff support → corridor.head earlier ∉ support

/-- **`lem:cold-corridor-first-failure` (iv)**, in ledger form.
The corridor has reached a support already marked by the incoming branch
ledger.  The cold theorem does not construct a handoff object. -/
theorem handoff_mem {corridor : Corridor object windows component}
    {Handoff : Finset object.Vertex → Prop} {segment : corridor.Segment}
    (failure : FirstFailureHandoff corridor Handoff segment) :
    ∃ support, Handoff support ∧ corridor.head segment ∈ support :=
  failure.1

/-! ## (F5) and the existence of a first failure

Clause (F5) is *"no earlier alternative occurs and either the corridor reaches
its successor boundary stub before `Q_cold + 1` states have been read, or a cold
corridor state repeats"*, and its two subcases fix the bounded support:
*"In case (F5), the bounded support is the whole terminal corridor in the first
subcase, and the support between the two equal states in the second subcase.
With its two boundary interfaces, this bounded support is the first-failure cold
exchange of `ε`."*

`lem:cold-corridor-first-failure`'s existence half is the manuscript's own
dichotomy:

> Follow its initial segments until one of the alternatives occurs.  If the
> successor boundary stub is reached before `Q_cold + 1` states have been read,
> then the whole corridor, together with the two boundary stubs and the two
> `P₁₃`-window interfaces, has at most `M_cold = Q_cold + 30` vertices and gives
> the terminal subcase of (F5).  Otherwise, before the successor is reached,
> `Q_cold + 1` states are read; two states are equal by the definition of
> `Q_cold`, and the first such equality gives the repeat subcase of (F5).  Hence
> a first failure always exists.

That is a genuine case split on the number of states read against `Q_cold`, and
it is proved below as one.  (F5) is **not** defined as the negation of the other
four clauses; if it were, "a first failure always exists" would be a tautology
and the manuscript's argument would not be formalised. -/

/-- The number of cold corridor states a corridor reads: one per initial
segment. -/
noncomputable def statesRead (corridor : Corridor object windows component) : Nat :=
  corridor.inside.1.length + 1

/-- **(F5), first subcase**: the corridor reaches its successor boundary stub
before `Q_cold + 1` states have been read. -/
def TerminalCorridor (corridor : Corridor object windows component)
    (S : DeclaredSignature) : Prop :=
  corridor.statesRead ≤ stateBound S

/-- **(F5), second subcase**: the first cold corridor state repeat.

The later endpoint is minimal: before `right` no two earlier corridor
positions have the same retained state.  This is the manuscript's "the first
such equality", rather than an arbitrary repeated pair. -/
def RepeatedState {S : DeclaredSignature}
    (corridor : Corridor object windows component)
    (presentation : Presentation.{u} S object)
    (index : corridor.Segment → presentation.Segment) : Prop :=
  ∃ left right : corridor.Segment,
    left.1 < right.1 ∧
      presentation.state (index left) = presentation.state (index right) ∧
      ∀ earlierLeft earlierRight : corridor.Segment,
        earlierLeft.1 < earlierRight.1 → earlierRight.1 < right.1 →
          presentation.state (index earlierLeft) ≠
            presentation.state (index earlierRight)

/-- **`lem:cold-corridor-first-failure`, the existence half: "for every
`ε ∈ 𝓔_br`, the cold return corridor of `ε` has a first failure".**

Either the corridor is terminal -- the successor stub is reached inside
`Q_cold` states -- or `Q_cold + 1` states are read and two of them are equal by
the pigeonhole on `Q_cold`.  The split is on the corridor's own length, so no
alternative is defined as the complement of the others and the conclusion is
not vacuous.

`index` is required injective, which is what "reading" `Q_cold + 1` *distinct*
states means: the segments the corridor passes through are distinct positions
along it. -/
theorem exists_firstFailure {S : DeclaredSignature}
    (corridor : Corridor object windows component)
    (presentation : Presentation.{u} S object)
    (index : corridor.Segment → presentation.Segment)
    (injective : Function.Injective index) :
    TerminalCorridor corridor S ∨ RepeatedState corridor presentation index := by
  classical
  by_cases terminal : corridor.statesRead ≤ stateBound S
  · exact Or.inl terminal
  · refine Or.inr ?_
    -- `Q_cold + 1` states are read: the segments carry that many distinct
    -- positions, so the pigeonhole on `Fintype.card (CutState S)` applies.
    have wide : stateBound S + 1 ≤ corridor.statesRead := by omega
    let sample : Fin (stateBound S + 1) → corridor.Segment := fun position =>
      ⟨position.1, by
        have := position.2
        have : corridor.statesRead = corridor.inside.1.length + 1 := rfl
        omega⟩
    have sampleInjective : Function.Injective sample := by
      intro left right same
      apply Fin.ext
      simpa [sample] using congrArg Fin.val same
    obtain ⟨left, right, distinct, same⟩ :=
      presentation.exists_state_eq_of_stateBound_lt (fun position => index (sample position))
    have repeated : ∃ later : corridor.Segment,
        ∃ earlier : corridor.Segment, earlier.1 < later.1 ∧
          presentation.state (index earlier) = presentation.state (index later) := by
      rcases lt_or_gt_of_ne (fun equal => distinct (sampleInjective (Fin.ext equal))) with
        before | after
      · exact ⟨sample right, sample left, before, same⟩
      · exact ⟨sample left, sample right, after, same.symm⟩
    let repeatedRights : Finset corridor.Segment :=
      Finset.univ.filter fun later =>
        ∃ earlier : corridor.Segment, earlier.1 < later.1 ∧
          presentation.state (index earlier) = presentation.state (index later)
    have repeatedRights_nonempty : repeatedRights.Nonempty := by
      obtain ⟨later, earlier, before, same⟩ := repeated
      exact ⟨later, Finset.mem_filter.2
        ⟨Finset.mem_univ _, ⟨earlier, before, same⟩⟩⟩
    let firstRight : corridor.Segment :=
      repeatedRights.min' repeatedRights_nonempty
    have firstRight_mem : firstRight ∈ repeatedRights := by
      exact Finset.min'_mem repeatedRights repeatedRights_nonempty
    obtain ⟨firstLeft, firstBefore, firstSame⟩ :=
      (Finset.mem_filter.1 firstRight_mem).2
    refine ⟨firstLeft, firstRight, firstBefore, firstSame, ?_⟩
    intro earlierLeft earlierRight earlierBefore rightBefore sameEarlier
    have earlierRight_mem : earlierRight ∈ repeatedRights := by
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
        ⟨earlierLeft, earlierBefore, sameEarlier⟩⟩
    have minimal := Finset.min'_le repeatedRights earlierRight earlierRight_mem
    exact (Nat.not_lt_of_ge (show firstRight.1 ≤ earlierRight.1 from minimal)) rightBefore

/-- **The first-failure cold exchange is bounded by `M_cold`.**

*"Thus `M_cold` is a uniform upper bound for the number of vertices in a
first-failure cold exchange."*  In the terminal subcase the whole corridor has
at most `Q_cold` vertices, and the two boundary stubs and the two window
interfaces add the manuscript's `30 = 2·order + 2·2`. -/
theorem exchange_card_le {S : DeclaredSignature}
    (corridor : Corridor object windows component)
    (terminal : TerminalCorridor corridor S) :
    corridor.statesRead + interfaceBudget S ≤ exchangeBound S := by
  have inside : corridor.statesRead ≤ stateBound S := terminal
  unfold exchangeBound
  omega

end Corridor

section Ledgers

variable {object : Graph.FiniteObject.{u}}

/-! ## `def:cold-window-ledger`: the hot/cold split and its thresholds

> Set `c_hot := 118.108581…`, `θ_win := 3/(2c_hot)`.  For a packing density
> `θ = p₁₃/n`, set `τ(θ) := 15θ/(1−13θ)`.  Then `τ(θ) < 1/4 ⟺ θ < 1/73`, and
> `τ(θ) < 3/13 ⟺ θ < 1/78`.  The value `1/78` is the route-8 private-carrier
> threshold, and `1/73` is the negative-net-charge threshold.

The two equivalences are exact and need no rational: at `θ = p/n` the comparison
`τ(θ) < a/b` is `b·s·p < a·(n − e·p)` with `s` the external-stub count and
`e = s − 2` the branch excess, and clearing it gives `(b·s + a·e)·p < a·n`.  The
manuscript's `73` and `78` are the resulting coefficients -- `4·15 + 13 = 73`
and `(13·15 + 3·13)/3 = 78` -- and neither is written anywhere below.

A packed window is *hot* when the current comparison retains, for it, the
injective list of declared window coordinates of `lem:p13-window-package`, and
*cold* otherwise. -/

/-- **`τ(θ) < a/b` at `θ = p/n`, cleared of denominators.**

`stubs` is the window's external-stub count `s(P)` and `stubs − 2` its branch
excess, so this is the manuscript's `15θ/(1−13θ)` with both constants read off
the window rather than written. -/
def TauBelow (stubs numerator denominator packing order : Nat) : Prop :=
  denominator * (stubs * packing) < numerator * (order - (stubs - 2) * packing)

/-- **The threshold form of `def:cold-window-ledger`.**  Below the packing
saturation `(s−2)·p ≤ n`, comparing `τ(θ)` against `a/b` is comparing the
density against the single coefficient `b·s + a·(s−2)` over `a`. -/
theorem tauBelow_iff (stubs numerator denominator packing order : Nat)
    (saturated : (stubs - 2) * packing ≤ order) :
    TauBelow stubs numerator denominator packing order ↔
      (denominator * stubs + numerator * (stubs - 2)) * packing <
        numerator * order := by
  unfold TauBelow
  have expand : (denominator * stubs + numerator * (stubs - 2)) * packing =
      denominator * (stubs * packing) + numerator * ((stubs - 2) * packing) := by
    ring
  have bound : numerator * ((stubs - 2) * packing) ≤ numerator * order :=
    Nat.mul_le_mul_left _ saturated
  rw [expand, Nat.mul_sub]
  omega

/-- **`def:cold-window-ledger`'s `1/4` comparison.**

`τ(θ) < 1/4` at `θ = p/n` is `(5s − 2)·p < n`, with `s` the window's external
stub count.  At the manuscript's own `s = 15` the coefficient is `73`, which is
where `1/73` comes from; the numeral is computed by
`Fixtures.ColdCorridorLedger`, never written. -/
theorem tauBelow_quarter (stubs packing order : Nat) (two : 2 ≤ stubs)
    (saturated : (stubs - 2) * packing ≤ order) :
    TauBelow stubs 1 4 packing order ↔ (5 * stubs - 2) * packing < order := by
  rw [tauBelow_iff stubs 1 4 packing order saturated]
  refine ⟨fun below => ?_, fun below => ?_⟩ <;>
    · rw [show 4 * stubs + 1 * (stubs - 2) = 5 * stubs - 2 by omega] at *
      omega

/-- **`def:cold-window-ledger`'s `3/13` comparison.**

`τ(θ) < 3/13` at `θ = p/n` is `(16s − 6)·p < 3n`.  At `s = 15` that is
`234·p < 3n`, i.e. `78·p < n` -- the route-8 private-carrier threshold, again
computed rather than written. -/
theorem tauBelow_routeEight (stubs packing order : Nat) (two : 2 ≤ stubs)
    (saturated : (stubs - 2) * packing ≤ order) :
    TauBelow stubs 3 13 packing order ↔ (16 * stubs - 6) * packing < 3 * order := by
  rw [tauBelow_iff stubs 3 13 packing order saturated]
  refine ⟨fun below => ?_, fun below => ?_⟩ <;>
    · rw [show 13 * stubs + 3 * (stubs - 2) = 16 * stubs - 6 by omega] at *
      omega

/-- **A packed window is hot** when the current comparison retains for it the
injective list of declared window coordinates of `lem:p13-window-package`:
`packageLength` many, all distinct.  A window not carrying such a live package
is *cold*.

Hotness is decided, not assumed: the two clauses are a length check and a
distinctness check on the retained list, so the hot/cold split of a packing is a
computation on the current comparison. -/
def isHot {Window Coordinate : Type} [DecidableEq Coordinate]
    (retained : Window → List Coordinate) (packageLength : Nat)
    (window : Window) : Bool :=
  decide ((retained window).length = packageLength) &&
    decide (retained window).Nodup

/-- The two clauses of hotness, as the manuscript states them: the full
canonical package is present, and its coordinates are independently
target-testable. -/
theorem isHot_iff {Window Coordinate : Type} [DecidableEq Coordinate]
    (retained : Window → List Coordinate) (packageLength : Nat)
    (window : Window) :
    isHot retained packageLength window = true ↔
      ((retained window).length = packageLength ∧ (retained window).Nodup) := by
  simp [isHot]

/-- The cold windows of a packing: those not carrying a live package. -/
def coldWindows {Window Coordinate : Type} [DecidableEq Window]
    [DecidableEq Coordinate] (retained : Window → List Coordinate)
    (packageLength : Nat) (packing : Finset Window) : Finset Window :=
  packing.filter fun window => isHot retained packageLength window = false

/-- The hot windows of a packing. -/
def hotWindows {Window Coordinate : Type} [DecidableEq Window]
    [DecidableEq Coordinate] (retained : Window → List Coordinate)
    (packageLength : Nat) (packing : Finset Window) : Finset Window :=
  packing.filter fun window => isHot retained packageLength window = true

/-- **`C := |𝒫_cold|`.** -/
def coldCount {Window Coordinate : Type} [DecidableEq Window]
    [DecidableEq Coordinate] (retained : Window → List Coordinate)
    (packageLength : Nat) (packing : Finset Window) : Nat :=
  (coldWindows retained packageLength packing).card

/-- **`𝒫 = 𝒫_hot ⊔ 𝒫_cold`.**  The split is a partition: every packed window is
hot or cold and none is both. -/
theorem coldCount_add_hotCount {Window Coordinate : Type} [DecidableEq Window]
    [DecidableEq Coordinate] (retained : Window → List Coordinate)
    (packageLength : Nat) (packing : Finset Window) :
    coldCount retained packageLength packing +
        (hotWindows retained packageLength packing).card = packing.card := by
  classical
  unfold coldCount coldWindows hotWindows
  rw [Finset.filter_congr (q := fun window =>
      ¬ (isHot retained packageLength window = true))
    (fun window _ => by simp)]
  rw [Nat.add_comm]
  exact Finset.card_filter_add_card_filter_not _

/-- A window is cold exactly when it is not hot. -/
theorem mem_coldWindows_iff {Window Coordinate : Type} [DecidableEq Window]
    [DecidableEq Coordinate] (retained : Window → List Coordinate)
    (packageLength : Nat) (packing : Finset Window) (window : Window) :
    window ∈ coldWindows retained packageLength packing ↔
      (window ∈ packing ∧
        ¬ ((retained window).length = packageLength ∧ (retained window).Nodup)) := by
  simp [coldWindows, ← isHot_iff retained packageLength window]

/-- The length-changing part of `lem:cold-bounded-germ-trichotomy` after the
two ledger-closed arms have been read back by key. -/
theorem boundedGerm_not_survives
    {S : DeclaredSignature} {Baseline Target : Graph.FiniteObject.{u} → Prop}
    {object : Graph.FiniteObject.{u}}
    (notRealizing : ∀ germ : BoundedGerm S Baseline Target object,
      ¬ germ.Realizing)
    (notSilent : ∀ germ : BoundedGerm S Baseline Target object,
      germ.increment < 0 → ¬ germ.Neutral)
    (germ : BoundedGerm S Baseline Target object)
    (shorter : germ.increment < 0) :
    germ.Distinguishing := by
  rcases germ.trichotomy with realizing | distinguishing | neutral
  · exact absurd realizing (notRealizing germ)
  · exact distinguishing
  · exact absurd neutral (notSilent germ shorter)

/-! ## Greedy independence and cold mass -/

section Greedy

variable {α : Type u} [DecidableEq α]

/-- A subfamily is independent for an overlap relation when no two distinct
members overlap. -/
def IndependentFor (Overlaps : α → α → Prop) (independent : Finset α) : Prop :=
  ∀ left ∈ independent, ∀ right ∈ independent, left ≠ right →
    ¬ Overlaps left right

/-- Greedy independence with the division cleared. -/
theorem exists_independent_card_le_mul (Overlaps : α → α → Prop)
    [DecidableRel Overlaps] (symmetric : ∀ left right, Overlaps left right →
      Overlaps right left) (degree : Nat) :
    ∀ family : Finset α,
      (∀ member ∈ family,
        (family.filter fun other => Overlaps member other).card ≤ degree) →
      ∃ independent ⊆ family, IndependentFor Overlaps independent ∧
        family.card ≤ independent.card * (degree + 1) := by
  classical
  intro family
  induction family using Finset.strongInduction with
  | _ family recurse =>
    intro bounded
    rcases Finset.eq_empty_or_nonempty family with rfl | ⟨chosen, member⟩
    · exact ⟨∅, Finset.Subset.refl _, by simp [IndependentFor], by simp⟩
    · set blocked : Finset α :=
        family.filter fun other => other = chosen ∨ Overlaps chosen other
        with blockedDef
      have chosenBlocked : chosen ∈ blocked := by
        simp [blockedDef, member]
      have blockedSubset : blocked ⊆ family := Finset.filter_subset _ _
      have blockedCard : blocked.card ≤ degree + 1 := by
        have split : blocked ⊆
            insert chosen (family.filter fun other => Overlaps chosen other) := by
          intro other otherMember
          simp only [blockedDef, Finset.mem_filter] at otherMember
          rcases otherMember.2 with rfl | overlap
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem
              (Finset.mem_filter.2 ⟨otherMember.1, overlap⟩)
        refine le_trans (Finset.card_le_card split) ?_
        refine le_trans (Finset.card_insert_le _ _) ?_
        exact Nat.succ_le_succ (bounded chosen member)
      set rest : Finset α := family \ blocked with restDef
      have restSubset : rest ⊆ family := Finset.sdiff_subset
      have restSmaller : rest ⊂ family := by
        refine Finset.ssubset_iff_of_subset restSubset |>.2 ⟨chosen, member, ?_⟩
        simp [restDef, chosenBlocked]
      obtain ⟨independent, independentSubset, independentFor, cover⟩ :=
        recurse rest restSmaller (fun other otherMember =>
          le_trans (Finset.card_le_card (Finset.filter_subset_filter _ restSubset))
            (bounded other (restSubset otherMember)))
      have chosenFree : ∀ other ∈ rest, ¬ Overlaps chosen other := by
        intro other otherMember overlap
        have : other ∈ blocked := by
          simp only [blockedDef, Finset.mem_filter]
          exact ⟨restSubset otherMember, Or.inr overlap⟩
        simp only [restDef, Finset.mem_sdiff] at otherMember
        exact otherMember.2 this
      have chosenNotMem : chosen ∉ independent := by
        intro chosenMember
        have : chosen ∈ rest := independentSubset chosenMember
        simp only [restDef, Finset.mem_sdiff] at this
        exact this.2 chosenBlocked
      refine ⟨insert chosen independent, ?_, ?_, ?_⟩
      · exact Finset.insert_subset member
          (Finset.Subset.trans independentSubset restSubset)
      · intro left leftMember right rightMember different
        simp only [Finset.mem_insert] at leftMember rightMember
        rcases leftMember with leftEq | leftMember
        · rcases rightMember with rightEq | rightMember
          · exact absurd (leftEq.trans rightEq.symm) different
          · subst leftEq
            exact chosenFree right (independentSubset rightMember)
        · rcases rightMember with rightEq | rightMember
          · subst rightEq
            exact fun overlap =>
              chosenFree left (independentSubset leftMember) (symmetric _ _ overlap)
          · exact independentFor left leftMember right rightMember different
      · have decompose : family.card = blocked.card + rest.card := by
          have total := Finset.card_sdiff_add_card_eq_card blockedSubset
          rw [restDef]
          omega
        rw [Finset.card_insert_of_notMem chosenNotMem]
        calc family.card = blocked.card + rest.card := decompose
          _ ≤ (degree + 1) + independent.card * (degree + 1) := by
              exact Nat.add_le_add blockedCard cover
          _ = (independent.card + 1) * (degree + 1) := by ring

end Greedy

/-- `lem:hot-failure-cold-mass`, cleared of logarithms and division. -/
theorem hotFailure_coldMass (hotRate skeletonRate order slack : Nat)
    (hotCount coldCount packing : Nat)
    (partition : packing = hotCount + coldCount)
    (hotBound : hotRate * hotCount ≤ skeletonRate * order + slack) :
    hotRate * packing ≤ hotRate * coldCount + (skeletonRate * order + slack) := by
  subst partition
  calc hotRate * (hotCount + coldCount)
      = hotRate * hotCount + hotRate * coldCount := by ring
    _ ≤ (skeletonRate * order + slack) + hotRate * coldCount :=
        Nat.add_le_add_right hotBound _
    _ = hotRate * coldCount + (skeletonRate * order + slack) := by ring

/-- `lem:cold-germ-extraction`, as greedy finite-family extraction. -/
theorem coldGermExtraction {Germ : Type u} [DecidableEq Germ]
    (Overlaps : Germ → Germ → Prop) [DecidableRel Overlaps]
    (symmetric : ∀ left right, Overlaps left right → Overlaps right left)
    (exchangeBound overlapBound : Nat) (candidates : Finset Germ)
    (boundedOverlap : ∀ candidate ∈ candidates,
      (candidates.filter fun other => Overlaps candidate other).card ≤
        exchangeBound * overlapBound) :
    ∃ disjointFamily ⊆ candidates,
      IndependentFor Overlaps disjointFamily ∧
        candidates.card ≤
          disjointFamily.card * (exchangeBound * overlapBound + 1) :=
  exists_independent_card_le_mul Overlaps symmetric (exchangeBound * overlapBound)
    candidates boundedOverlap

/-- A positive candidate family gives a nonempty extracted independent family. -/
theorem coldGerm_nonempty {Germ : Type u} [DecidableEq Germ]
    {candidates disjointFamily : Finset Germ}
    {denominator : Nat}
    (cover : candidates.card ≤ disjointFamily.card * denominator)
    (positive : 0 < candidates.card) : 0 < disjointFamily.card := by
  by_contra empty
  have : disjointFamily.card = 0 := by omega
  rw [this] at cover
  omega

/-- `lem:cold-germ-extraction`, published as a local current-residual fact.

The reusable greedy lemma above is still quantified over a finite family, but
this theorem specializes it to bounded cold germs of the current object and
packages the disjoint family as the existential conclusion of
`ColdGermExtractionLocal`. -/
theorem coldGermExtractionLocal {S : DeclaredSignature} {threshold : Nat}
    {Baseline Target : FiniteObject.{u} → Prop} {object : FiniteObject.{u}} :
    ColdGermExtractionLocal S threshold Baseline Target object := by
  classical
  intro candidates candidateFamily
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let Germ := BoundedGerm S Baseline Target object
  letI : DecidableEq Germ := Classical.decEq Germ
  rcases candidateFamily with ⟨positive, boundedOverlap⟩
  obtain ⟨disjointFamily, subset, independent, cover⟩ :=
    coldGermExtraction
      (Germ := Germ)
      (Overlaps := fun left right : Germ =>
        ¬ Disjoint left.support right.support)
      (symmetric := by
        intro left right overlaps rightLeft
        exact overlaps rightLeft.symm)
      (exchangeBound := exchangeBound S)
      (overlapBound := overlapBound threshold S)
      (candidates := candidates)
      boundedOverlap
  have cover' :
      candidates.card ≤ disjointFamily.card *
        extractionDenominator threshold S := by
    simpa [extractionDenominator] using cover
  have disjointSupports :
      ∀ left ∈ disjointFamily, ∀ right ∈ disjointFamily, left ≠ right →
        Disjoint left.support right.support := by
    intro left leftMember right rightMember different
    by_contra overlaps
    exact independent left leftMember right rightMember different overlaps
  exact ⟨disjointFamily, subset, disjointSupports, cover',
    coldGerm_nonempty cover' positive⟩

/-- The quantitative chain proving a remaining cold candidate is nonempty. -/
theorem coldGerm_positive {Germ : Type u} [DecidableEq Germ]
    {candidates disjointFamily : Finset Germ}
    (perWindow coldCount branchExcess denominator slack : Nat)
    (stubExcess : perWindow * coldCount ≤ branchExcess + slack)
    (candidateLoss : branchExcess ≤ candidates.card + slack)
    (cover : candidates.card ≤ disjointFamily.card * denominator)
    (linear : 2 * slack < perWindow * coldCount) :
    0 < disjointFamily.card := by
  refine coldGerm_nonempty cover ?_
  omega

/-! ## `def:cold-skeleton-excess` and `lem:cold-window-stub-excess`

> The global lexicographic order on vertices and edges induces an order on the
> external stubs of every ambient-cubic cold window.  The first two stubs of `P`
> are called the *transit stubs*; the remaining `s(P) − 2` stubs, when
> `s(P) > 2`, are the *selected branch-excess half-edges* of `P`.  …  Thus
> `|𝓔_br| = b(𝔖_cold)`.

and `b(P) := max{0, s(P) − 2}`. -/

/-- **`b(P) := max{0, s(P) − 2}`**, the branch-excess contribution of one
window. -/
def branchExcessOf (externalStubs : Nat) : Nat := externalStubs - 2

/-- **The selected branch-excess half-edges of one window**: its external stubs
with the two transit stubs dropped. -/
def selectedBranchExcess {Stub : Type} (stubs : List Stub) : List Stub :=
  stubs.drop 2

/-- **`|𝓔_br(P)| = b(P)`.**  Dropping the two transit stubs leaves exactly the
branch-excess contribution, so the count is the definition and not a second
number. -/
theorem selectedBranchExcess_length {Stub : Type} (stubs : List Stub) :
    (selectedBranchExcess stubs).length = branchExcessOf stubs.length := by
  simp [selectedBranchExcess, branchExcessOf]

/-! **`lem:cold-window-stub-excess`, the per-window count.**

*"`P` has exactly `39 − 24 = 15` external stubs.  In the skeleton, a
degree-two corridor through `p` can absorb at most two of these stubs without
branching.  Hence `b(P) = 15 − 2 = 13` for every ambient-cubic cold window."*

Both numbers are read rather than written: `s(P) = δ·order − 2(order − 1)` is
the window's own stub count at the registered baseline and order -- the same
expression node `[28]` compares -- and `b(P)` is `branchExcessOf` of it.  There
is no lemma here, because at that stub count `branchExcessOf` *is* the count by
definition; `Fixtures.ColdCorridorLedger` evaluates both to the manuscript's
`15` and `13`. -/

/-- **`b(𝔖_cold) ≥ 13C − o(n)`.**

*"By `def:surviving-cold-branch`, `|𝒫_cold \ 𝒫_cold^cub| = o(n)`. … Summing
over the remaining windows gives the claim."*  Stated subtraction-free: the
branch excess of the ambient-cubic cold windows, plus the per-window excess
spent on the `o(n)` windows that are not ambient-cubic, is at least the
per-window excess times `C`. -/
theorem branchExcess_ge_of_cubic (perWindow cubicCount coldCount nonCubicBound : Nat)
    (split : coldCount ≤ cubicCount + nonCubicBound) :
    perWindow * coldCount ≤
      perWindow * cubicCount + perWindow * nonCubicBound := by
  calc perWindow * coldCount
      ≤ perWindow * (cubicCount + nonCubicBound) := Nat.mul_le_mul_left _ split
    _ = perWindow * cubicCount + perWindow * nonCubicBound := by ring

/-! ## `lem:cold-corridor-first-failure`, assembled

The existence half is `Corridor.exists_firstFailure` above.  The exclusions
used by the paper's cold residual are ledger facts in the Strategy layer; this
graph file only supplies the local corridor and germ statements. -/

section Routing

variable {S : DeclaredSignature} {order : Nat}
variable {Baseline Target : Graph.FiniteObject.{u} → Prop}

end Routing

end Ledgers

end Hypostructure.Graph.ColdCorridor
