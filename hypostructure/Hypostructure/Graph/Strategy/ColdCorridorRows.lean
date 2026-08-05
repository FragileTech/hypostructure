import Hypostructure.Graph.Strategy.SpineRows
import Hypostructure.Graph.ColdIncrementArithmetic

/-!
# The cold return corridor: rows `[145]`--`[157]`

Two atomic Strategies, one per manuscript object.

`coldCorridorStateRow` commits `def:cold-corridor-first-failure`'s cut-state
clauses: the cold corridor state is *complete* for the local replacement and
*bounded* by `Q_cold`.  It reads nothing from the ledger, because neither
clause depends on anything the earlier nodes proved: both are theorems about
the registered declared signature.

`sameInterfaceTableRow` commits `lem:cold-same-interface-table` together with
`lem:cold-short-self-return-filter`.  It reads exactly the two facts the
manuscript's proof spends -- node `[1]`'s target avoidance and node `[14]`'s
uncompressibility -- and nothing else.  A realizing row would hand the selected
object the target it avoids; a row that is neither handed off nor
distinguishing is a target-complete compression of its own proper support,
which node `[14]` has excluded.  So no row of the table is terminal.

Both rows are quantified over the residual domain's fact system and over the
keys they consume and produce, so the same executor runs after any canonical
branch cursor whose index carries their requirements.  A caller supplies the
schema bridges; the mathematics is `Graph.ColdCorridor`'s.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}
variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Nodes `[145]`--`[157]`: the corridor cut-state `T(J)`

`def:cold-corridor-first-failure` fixes, for an initial segment `J` of a cold
return corridor, its two active boundary interfaces `T(J)` and the cold
corridor state of `J`: the finite two-boundary cut-state obtained from
`ρ^ex_{T(J)}(J)` by retaining exactly the boundary-degree profile, the two
active boundary half-edges, the cold-window offsets met at the two interfaces,
and the declared local coordinates whose support is contained in the bounded
active interface.  "It is not the full labelled prefix."

The row commits the two things that retention has to earn.

*Completeness.*  The manuscript's "after excluding (F2), equality of cold
corridor states is equality for every target-response coordinate used by the
local replacement".  The state retains no (D8) coordinate at all -- no product,
labelled copy, restriction, or quotient image -- and it does not need to: an
(D8) coordinate reads exactly the entries it was generated from, so once the
generating readings agree the derived reading agrees.  That is
`Presentation.reading_eq_of_state_eq`, by induction on the generation.

*Boundedness.*  "Since the boundary has size two and the retained window and
local-coordinate labels are finite, the set of possible cold corridor states is
bounded by a constant `Q_cold` depending only on the fixed declared signature."
`Q_cold` is `Fintype.card` of the retained cut-state of the *registered*
signature, so it mentions no graph, and `Q_cold + 1` segments cannot have
pairwise distinct states.  That pigeonhole is how
`lem:cold-corridor-first-failure` reaches the repeat subcase of (F5).

The row quantifies over every presentation of the object's corridor segments
rather than naming one.  A corridor is data, and no fact can carry data; what
the statement says is that the retention works at every corridor, which is what
the manuscript claims and what a later node needs. -/
@[reducible] noncomputable def coldCorridorStateRow
    (coldCorridorState :
      FactKey (Input BranchState Presentation presentation data))
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ presentation' :
          Graph.ColdCorridor.Presentation data.coldSignature input.object,
        (∀ left right : presentation'.Segment,
          presentation'.state left = presentation'.state right →
          ∀ coordinate : Graph.ColdCorridor.Generated data.coldSignature,
            presentation'.support coordinate ⊆
                ↑(presentation'.activeInterface left) →
              presentation'.reading left coordinate =
                presentation'.reading right coordinate) ∧
        (∀ segments :
            Fin (Graph.ColdCorridor.stateBound data.coldSignature + 1) →
              presentation'.Segment,
          ∃ left right, left ≠ right ∧
            presentation'.state (segments left) =
              presentation'.state (segments right)) ∧
        ∀ (boundary : Graph.Boundary)
          (carrier : presentation'.Segment → Graph.BoundaryPiece boundary)
          (left right : presentation'.Segment),
          (¬ presentation'.FirstFailureResponse
              (Graph.HasCycleWithLength data.LengthOK) carrier left right →
            presentation'.state left = presentation'.state right →
              Graph.Response.ContextEquivalent
                (Graph.HasCycleWithLength data.LengthOK)
                (carrier left) (carrier right)) ∧
          (presentation'.state left = presentation'.state right →
            ¬ Graph.Response.ContextEquivalent
                (Graph.HasCycleWithLength data.LengthOK)
                (carrier left) (carrier right) →
              presentation'.FirstFailureResponse
                (Graph.HasCycleWithLength data.LengthOK) carrier left right)) →
      coldCorridorState.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldCorridorState
    { Requires := []
      Produces := [coldCorridorState]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := coldCorridorState)
        (encode inputs.current fun presentation' =>
          ⟨fun _left _right same coordinate inside =>
              presentation'.reading_eq_of_state_eq same coordinate inside,
            presentation'.exists_state_eq_of_stateBound_lt,
            fun _boundary _carrier _left _right =>
              ⟨fun excluded same =>
                  presentation'.contextEquivalent_of_state_eq excluded same,
                fun same separated =>
                  presentation'.firstFailureResponse_of_not_contextEquivalent same
                    separated⟩⟩)
        .nil)

/-! ## Nodes `[145]`--`[157]`: the same-interface table

`def:cold-same-interface-table` is the finite table whose rows are equal-length
cold bounded germs and the short self-return exceptions of
`lem:cold-short-self-return-filter`, each row recording (T1) the two boundary
vertices and their boundary-degree profile, (T2) the two terminal cold-window
stubs and their offsets, (T3) the exact response profile generated by
`def:declared-coordinate-signature`, and (T4) the target truth value of every
compatible completion represented by that exact profile.

`lem:cold-same-interface-table` closes every row of it, and the manuscript's
proof spends exactly two things this branch already carries.

If a row is *realizing*, "the corresponding completion is a power-of-two cycle
in `G`, which contradicts the counterexample condition": the corridor
representative glued to its own outside context *is* the selected object, up to
the decomposition's reconstruction isomorphism, so the selection's own
avoidance excludes it.

If a row "first meets a declared Type B or route-8 interface, then by the
definition of the surviving cold branch the charge is transferred to that
already closed ledger" -- the handoff alternative, which the statement carries
as an arbitrary ledger predicate so that no row can escape by naming its own.

Otherwise the row is *distinguishing* or *neutral*.  Neutrality "means that the
two representatives have the same boundary-degree profile and the same target
response against every compatible context", and then
`def:admissible-rank-quotient` supplies the strictly smaller proper
representative of `def:proper-quotient-representative`.  Every clause of a
target-complete proper-support compression is then present, and node `[14]`'s
`cor:uncompressible` forbids it.  So a row is handed off or distinguishing, and
no equal-length cold bounded germ is a terminal cold residual.

The second output clause is the filter itself: a cold-window outside
self-return of outside length `ℓ` is smeared over the window offsets, testing
`[ℓ, ℓ+order−1]`, and a length that does not survive that test realizes an
accepted cycle.  The surviving lengths are the exceptional rows of the table,
which the first clause closes with the germs. -/
@[reducible] noncomputable def sameInterfaceTableRow
    (selection uncompressible coldSameInterfaceTable :
      FactKey (Input BranchState Presentation presentation data))
    (distinctRequired : selection ≠ uncompressible)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (excludes : (input : Input BranchState Presentation presentation data) →
      uncompressible.At input →
      ∀ support : Finset input.object.Vertex,
        ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) input.object support)
    (encode : (input : Input BranchState Presentation presentation data) →
      ((∀ Handoff : Finset input.object.Vertex → Prop,
        ∀ row : Graph.ColdCorridor.TableRow data.coldSignature
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) input.object Handoff,
          ¬ row.Realizing ∧ (Handoff row.support ∨ row.Distinguishing)) ∧
        (∀ Handoff : Finset input.object.Vertex → Prop,
          ∀ self : Graph.ColdCorridor.SelfReturn data.coldSignature data.LengthOK
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) input.object Handoff,
            Graph.ColdCorridor.SurvivesSmear data.LengthOK
                (data.coldSignature.windowOrder - 1) self.outsideLength ∧
              ¬ self.row.Realizing ∧
                (Handoff self.row.support ∨ self.row.Distinguishing)) ∧
        (∀ length : Nat,
          ¬ Graph.ColdCorridor.SurvivesSmear data.LengthOK
              (data.windowOrder - 1) length →
            ∃ tested, length ≤ tested ∧
              tested ≤ length + (data.windowOrder - 1) ∧ data.LengthOK tested) ∧
        (Graph.ColdCorridor.tableBound data.coldSignature =
          Fintype.card (Graph.ColdCorridor.Record data.coldSignature)) ∧
        ∀ Handoff : Finset input.object.Vertex → Prop,
          ∀ row : Graph.ColdCorridor.TableRow data.coldSignature
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) input.object Handoff,
            row.increment = 0) →
      coldSameInterfaceTable.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldSameInterfaceTable
    { Requires := [selection, uncompressible]
      Produces := [coldSameInterfaceTable]
      requiresUnique := by simp [distinctRequired]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := coldSameInterfaceTable)
        (encode inputs.current
          ⟨fun _Handoff row =>
              -- `lem:cold-same-interface-table`, at the two facts its proof
              -- spends: the selection's avoidance and node `[14]`'s exclusion.
              Graph.ColdCorridor.row_closed
                (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
                (avoidsOf inputs.current (inputs.get selection))
                (excludes inputs.current (inputs.get uncompressible)) row,
            -- The short self-return exceptions, the table's second row family.
            -- Their lengths are proved to be the filter's surviving ones rather
            -- than assumed to be.
            fun _Handoff self =>
              Graph.ColdCorridor.selfReturn_closed
                (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
                (avoidsOf inputs.current (inputs.get selection))
                (excludes inputs.current (inputs.get uncompressible)) self,
            fun _length failed =>
              Graph.ColdCorridor.exists_accepted_of_not_survivesSmear failed,
            rfl,
            fun _Handoff row => row.increment_eq_zero⟩)
        .nil)


/-! ## Nodes `[155]`--`[157]`: `lem:cold-bounded-germ-trichotomy`

*"No length-changing cold bounded germ survives on the surviving cold branch.
More explicitly, every such germ falls into one of the following three cases."*

One row per arm, because the manuscript routes the three arms to three
different places: G1 to the counterexample condition, G2 to the sparse exit or
exit-(4) ledger, and G3 to `cor:uncompressible`.  Each row commits the arm its
own node owns and reads exactly the facts that arm's proof spends -- node `[1]`'s
target avoidance for G1, node `[14]`'s uncompressibility for G3, and nothing at
all for G2, which is `lem:context-universality` at the germ.

`Graph.ColdCorridor.BoundedGerm` is `def:cold-bounded-germ` itself, and the
equal-length rows of `def:cold-same-interface-table` are the same structure with
`δ = 0` added; the two halves of the definition therefore share one carrier and
no germ can be a row of one family and not of the other. -/

/-- **Node `[155]`: the G1 arm, and the exhaustiveness of the trichotomy.**

*"Hit-realized.  Some compatible live completion and window offset close a
dyadic cycle.  This contradicts the counterexample condition."*  A germ's own
compatible completion is the selected object up to the decomposition's
reconstruction isomorphism, so a realizing germ hands it the target node `[1]`
denies.  Beside it the row commits the split's exhaustiveness, which is what
makes the routing of G2 and G3 a routing of everything that is left. -/
@[reducible] noncomputable def coldGermRealizedRow
    (selection coldGermRealized :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : selection ≠ coldGermRealized)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (encode : (input : Input BranchState Presentation presentation data) →
      Holds BranchState Presentation presentation data .coldGermRealized
        input.object →
      coldGermRealized.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldGermRealized
    (rowManifest selection coldGermRealized distinct)
    (fun inputs =>
      .cons (key := coldGermRealized)
        (encode inputs.current
          ⟨fun germ realizing =>
              avoidsOf inputs.current (inputs.get selection)
                (germ.target_of_realizing
                  (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
                  realizing),
            fun germ => germ.trichotomy⟩)
        .nil)

/-- **Node `[156]`: the G2 arm.**

*"Hit-distinguished.  Some compatible outside context distinguishes the two
representatives by dyadic truth value without already realizing the cycle in the
current graph.  The induced quotient is target-defective, so it is routed to the
sparse exit or exit-(4) ledger."*  Its proof is `lem:context-universality`: the
distinguishing context already denies the all-context clause of
`def:target-complete-quotient`, so the identification fails to be target-complete
in every immutable profile fibre.

The row reads nothing.  Target-defectiveness of a distinguished germ is a
theorem about the germ's own two representatives; the branch facts are spent by
the other two arms. -/
@[reducible] noncomputable def coldGermDistinguishedRow
    (coldGermDistinguished :
      FactKey (Input BranchState Presentation presentation data))
    (encode : (input : Input BranchState Presentation presentation data) →
      Holds BranchState Presentation presentation data .coldGermDistinguished
        input.object →
      coldGermDistinguished.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldGermDistinguished
    (sourceFreeManifest coldGermDistinguished)
    (fun inputs =>
      .cons (key := coldGermDistinguished)
        (encode inputs.current
          (fun germ _Profile profile distinguishing =>
            germ.not_targetComplete_of_distinguishing profile distinguishing))
        .nil)

/-- **Node `[157]`: the G3 arm, with `lem:cold-increment-arithmetic`.**

*"Silent.  No compatible outside context and no relevant scale distinguishes the
two representatives.  Then replacing the longer representative by the shorter one
… strictly decreases the support.  This is a nontrivial target-complete
compression of a proper support"*, forbidden by `cor:uncompressible`, which is
node `[14]`'s fact and the only thing this row reads.

Unlike the equal-length rows of `def:cold-same-interface-table`, the descent is
the increment's own: the shorter representative has strictly fewer internal
vertices, so its completion has strictly fewer vertices than the object, and no
appeal to `def:admissible-rank-quotient` is made.

The remaining outputs are `lem:cold-increment-arithmetic`, which decides which
arm a length-changing germ falls into: the overlapping blocks of case (a), the
attainable power of two of case (b), the order criterion `ord_δ(2) > δ − 13`
that forces (b), the transient reduction of an even modulus to its odd part, and
case (d)'s equal-length switch back to the same-interface table.  Case (c) is the
trichotomy's own exhaustiveness, committed at node `[155]`. -/
@[reducible] noncomputable def coldGermSilentRow
    (uncompressible coldGermSilent :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : uncompressible ≠ coldGermSilent)
    (excludes : (input : Input BranchState Presentation presentation data) →
      uncompressible.At input →
      ∀ support : Finset input.object.Vertex,
        ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) input.object support)
    (encode : (input : Input BranchState Presentation presentation data) →
      Holds BranchState Presentation presentation data .coldGermSilent
        input.object →
      coldGermSilent.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldGermSilent
    (rowManifest uncompressible coldGermSilent distinct)
    (fun inputs =>
      .cons (key := coldGermSilent)
        (encode inputs.current
          ⟨fun germ shorter neutral =>
              excludes inputs.current (inputs.get uncompressible) germ.support
                (germ.compressibleSupport_of_not_distinguishing shorter neutral.2),
            fun germ => germ.increment_eq_zero_iff,
            fun _increment _base _copies _length positive overlapping lower upper
                accepted =>
              Graph.ColdCorridor.exists_not_survivesSmear_of_mem_interval
                positive overlapping lower upper accepted,
            fun _increment _base _exponent _residue positive small reached
                congruent accepted =>
              Graph.ColdCorridor.exists_not_survivesSmear_of_pow_congruent
                positive small reached congruent accepted,
            fun _increment _base _nonzero wide criterion =>
              Graph.ColdCorridor.exists_hit_of_orderOf_lt wide criterion,
            fun _transient _exponent _odd past =>
              Graph.ColdCorridor.pow_mod_of_le past⟩)
        .nil)

/-! ## Nodes `[154]`--`[157]`: the four first-failure producers and the routing

`def:cold-corridor-first-failure`'s five alternatives and
`lem:cold-corridor-first-failure`'s five routings.  Each row commits the clause
its own node owns, and each reads exactly the ledger facts the manuscript's
proof spends -- node `[1]`'s target avoidance for (F1), node `[14]`'s
uncompressibility for (F3), and nothing at all for (F2), (F4) and the existence
half, which are theorems about the corridor and the registered signature. -/

/-- **Node `[154]`, `[155]`: the (F1) producer.**

An (F1) completion is a closed walk of the object built from the entry stub, the
corridor prefix, the return adjacency and the window segment; if it is a cycle
of accepted length then the selected object has an accepted cycle, which node
`[1]` denies.  So (F1) never occurs. -/
@[reducible] noncomputable def coldFailureCycleRow
    (selection coldFailureCycle :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : selection ≠ coldFailureCycle)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (encode : (input : Input BranchState Presentation presentation data) →
      Holds BranchState Presentation presentation data .coldFailureCycle
        input.object →
      coldFailureCycle.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureCycle
    (rowManifest selection coldFailureCycle distinct)
    (fun inputs =>
      .cons (key := coldFailureCycle)
        (encode inputs.current
          (fun _windows _component corridor _order window segment failure =>
            avoidsOf inputs.current (inputs.get selection)
              (Graph.ColdCorridor.Corridor.hasCycleWithLength_of_firstFailureCycle
                failure)))
        .nil)

/-- **Node `[154]`, `[156]`: the (F2) producer.**

Both directions of `lem:context-universality` at the corridor.  An (F2)
discrepancy -- same cold corridor state, different target response against some
compatible outside context -- denies target-completeness of the identification
in every immutable profile fibre; and with the discrepancy excluded, two
prefixes carrying the same state are context-equivalent, which is what the local
replacement of `lem:cold-same-interface-table` consumes.

The row reads nothing: both are theorems about the corridor's own presentation,
already proved when the cut-state was retained. -/
@[reducible] noncomputable def coldFailureDefectRow
    (coldCorridorState coldFailureDefect :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : coldCorridorState ≠ coldFailureDefect)
    (encode : (input : Input BranchState Presentation presentation data) →
      Holds BranchState Presentation presentation data .coldFailureDefect
        input.object →
      coldFailureDefect.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureDefect
    (rowManifest coldCorridorState coldFailureDefect distinct)
    (fun inputs =>
      .cons (key := coldFailureDefect)
        (encode inputs.current
          (fun _windows _component _corridor _presentation _index _boundary
              _carrier _left _right =>
            ⟨fun _Profile _profile failure =>
                Graph.ColdCorridor.Corridor.not_targetComplete_of_firstFailureDefect
                  failure,
              fun excluded same =>
                Graph.ColdCorridor.Corridor.contextEquivalent_of_not_firstFailureDefect
                  excluded same,
              fun branch failure =>
                Graph.ColdCorridor.not_identified_of_firstFailureDefect branch _ _ _
                  _ failure⟩))
        .nil)

/-- **Node `[154]`, `[157]`: the (F3) producer.**

An (F3) pair names an earlier prefix whose own boundary piece is a strictly
smaller proper representative of a later one, with the boundary-degree profile
preserved and the target response equal against every outside context.  That is
a target-complete compression of the later prefix's proper support, and node
`[14]`'s `cor:uncompressible` forbids it.  So (F3) never occurs. -/
@[reducible] noncomputable def coldFailureCompressionRow
    (uncompressible coldFailureCompression :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : uncompressible ≠ coldFailureCompression)
    (excludes : (input : Input BranchState Presentation presentation data) →
      uncompressible.At input →
      ∀ support : Finset input.object.Vertex,
        ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) input.object support)
    (encode : (input : Input BranchState Presentation presentation data) →
      Holds BranchState Presentation presentation data .coldFailureCompression
        input.object →
      coldFailureCompression.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureCompression
    (rowManifest uncompressible coldFailureCompression distinct)
    (fun inputs =>
      .cons (key := coldFailureCompression)
        (encode inputs.current
          (fun _windows _component _corridor _presentation _index _support =>
            Graph.ColdCorridor.Corridor.FirstFailureCompression.not_occurs
              (excludes inputs.current (inputs.get uncompressible))))
        .nil)

/-- **Node `[154]`, `[156]`: the (F4) producer and its handoff exit.**

A corridor that first enters the declared handoff interfaces already recorded in
the branch state reaches *precisely one* of them -- the declared supports are
disjoint -- and the charge transfers to that envelope.  Nothing is closed at the
corridor.  The ledger is quantified, so no row manufactures one and none is
empty by construction. -/
@[reducible] noncomputable def coldFailureHandoffRow
    (coldCorridorState coldFailureHandoff :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : coldCorridorState ≠ coldFailureHandoff)
    (encode : (input : Input BranchState Presentation presentation data) →
      Holds BranchState Presentation presentation data .coldFailureHandoff
        input.object →
      coldFailureHandoff.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureHandoff
    (rowManifest coldCorridorState coldFailureHandoff distinct)
    (fun inputs =>
      .cons (key := coldFailureHandoff)
        (encode inputs.current
          (fun _windows _component _corridor _ledger _segment failure =>
            Graph.ColdCorridor.Corridor.exists_unique_handoff failure))
        .nil)

/-- **Node `[154]`: the classified state.**

`lem:cold-corridor-first-failure`'s existence half, with the two ledgers it is
counted against.

The existence proof is the manuscript's dichotomy, not a definition: either the
corridor reaches its successor stub inside `Q_cold` states, or `Q_cold + 1`
states are read and two are equal by the pigeonhole on `Q_cold`.  (F5) is
therefore not the complement of the other four clauses, and "a first failure
always exists" is not a tautology.

Beside it the row commits `M_cold`'s bound on the first-failure cold exchange,
`def:cold-window-ledger`'s partition `𝒫 = 𝒫_hot ⊔ 𝒫_cold`, and
`lem:cold-window-stub-excess` in subtraction-free form, with `b(P)` read off the
registered baseline and window order. -/
@[reducible] noncomputable def coldFailureRoutingRow
    (coldCorridorState coldFailureRouting :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : coldCorridorState ≠ coldFailureRouting)
    (encode : (input : Input BranchState Presentation presentation data) →
      Holds BranchState Presentation presentation data .coldFailureRouting
        input.object →
      coldFailureRouting.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureRouting
    (rowManifest coldCorridorState coldFailureRouting distinct)
    (fun inputs =>
      .cons (key := coldFailureRouting)
        (encode inputs.current
          ⟨fun _windows _component corridor presentation index injective =>
              Graph.ColdCorridor.Corridor.exists_firstFailure corridor
                presentation index injective,
            fun _windows _component corridor terminal =>
              Graph.ColdCorridor.Corridor.exchange_card_le corridor terminal,
            fun _Window _Coordinate _decWindow _decCoordinate retained
                packageLength packing =>
              Graph.ColdCorridor.coldCount_add_hotCount retained packageLength
                packing,
            fun _Stub stubs =>
              Graph.ColdCorridor.selectedBranchExcess_length stubs,
            fun _cubicCount _coldCount _nonCubicBound split =>
              Graph.ColdCorridor.branchExcess_ge_of_cubic _ _ _ _ split⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
