import Hypostructure.Graph.Strategy.SpineRows

/-!
# The route-8 carrier closure: rows

Figure 9 of the manuscript, nodes `[109]`--`[124]`.  The arm is entered at
`[109]` with the reduced silent core residual of
`def:typeA-silent-core-residual`; nodes `[111]`--`[113]` read its burden and
large-budget deficit; `[114]`--`[116]` establish that every indexed entry has at
least two essential carriers; `[117]`--`[122]` spend the private-carrier census
against the boundary supply and force a two-carrier entry; `[123]` is the
pressure descent; and `[124]` is the terminal two-carrier no-go, which leaves
the arm with no residual at all.

Each row is one atomic Strategy, quantified over the keys it consumes and
produces, and every mathematical step is `Graph.Route8`'s.  No row names a
producer, a predecessor depth, or an execution position, and the residual is
unchanged throughout: the block proves theorems about the object it was handed.
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

/-- The route-8 carrier data of an object, at the spine's registered target. -/
abbrev Route8Data (data : Data.{u}) (object : Graph.FiniteObject.{u}) :=
  Graph.Route8.Data (Graph.HasCycleWithLength data.LengthOK) object

/-! ## Node `[101]`: exit `(4)`, the ladder's peel

`def:typeA-saturated-exits` exit `(4)` is the *target-defect peeling* exit: "it
removes exactly the routed load whose declared coordinate is used by the
canonical target-defective quotient".  `def:typeA-exit4-peeling` gives the
receiver its routed loads `ℒ(w)`, a peeling set `P₄(w) ⊆ ℒ(w)` and the residual
load `L₄(w) = L(w) − |P₄(w)|`; `lem:typeA-exit4-residual-routing` says that while
`L₄(w) ≥ 4q(w)` the unpeeled loads realize an exit, and in the exit-`(4)` case
the peeling set can be enlarged by one; `lem:typeA-exit4-discharge` says that
enlargement is valid and drops the deficit by exactly `¼`; and
`lem:typeA-exit4-peeling-charge` says the remaining charge `q(w) − ¼ − ¼·L₄(w)`
is nonnegative once `L₄(w) ≤ 4q(w) − 1`.

The yes arm is therefore not a terminal: it peels and returns to node `[89]`
with the receiver retested.  This row decides whether the peel step is
available. -/
noncomputable def typeAExitFourPeelDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeAExitFourPeel typeAExitFourNoPeel :
      FactKey (Input BranchState Presentation presentation data))
    (encodePeel :
      (∀ piece : Finset current.object.Vertex,
        ∀ receiver : current.object.Vertex,
          ∀ peeled : Finset current.object.Vertex,
            peeled ⊆ Graph.ExitFour.routedLoads piece data.threshold receiver →
            Graph.ExitFour.SaturatedAfter piece data.threshold
                data.dischargeScale receiver peeled →
              ∃ load ∈ Graph.ExitFour.routedLoads piece data.threshold receiver,
                load ∉ peeled) → typeAExitFourPeel.At current)
    (encodeNoPeel :
      (¬ ∀ piece : Finset current.object.Vertex,
        ∀ receiver : current.object.Vertex,
          ∀ peeled : Finset current.object.Vertex,
            peeled ⊆ Graph.ExitFour.routedLoads piece data.threshold receiver →
            Graph.ExitFour.SaturatedAfter piece data.threshold
                data.dischargeScale receiver peeled →
              ∃ load ∈ Graph.ExitFour.routedLoads piece data.threshold receiver,
                load ∉ peeled) → typeAExitFourNoPeel.At current)
    (peelFresh : typeAExitFourPeel ∉ known)
    (noPeelFresh : typeAExitFourNoPeel ∉ known) :
    Decision typeAExitFourPeel typeAExitFourNoPeel previous :=
  Decision.run previous typeAExitFourPeel typeAExitFourNoPeel
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourPeel
    (by
      classical
      by_cases available :
          ∀ piece : Finset current.object.Vertex,
            ∀ receiver : current.object.Vertex,
              ∀ peeled : Finset current.object.Vertex,
                peeled ⊆
                    Graph.ExitFour.routedLoads piece data.threshold receiver →
                Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled →
                  ∃ load ∈
                      Graph.ExitFour.routedLoads piece data.threshold receiver,
                    load ∉ peeled
      · exact .inl (encodePeel available)
      · exact .inr (encodeNoPeel available))
    peelFresh noPeelFresh

/-! ## Node `[102]`: the peeled receiver, returned to node `[89]`

`lem:typeA-exit4-peeling-charge` and `lem:typeA-exit4-discharge`, run as the
finite descent `lem:typeA-exit4-residual-routing` opens: each peel drops `L₄(w)`
by exactly one, so peeling terminates, and it terminates at a peeling set whose
residual is unsaturated -- the receiver's remaining charge `q(w) − ¼ − ¼·L₄(w)`
is nonnegative and the receiver is retested at node `[89]`.

The row reads node `[101]`'s peel step by exact key; the descent is
`Graph.ExitFour.exists_unsaturated_peeling`. -/
@[reducible] noncomputable def typeAPeeledChargeRow
    (typeAExitFourPeel typeAPeeledCharge :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : typeAExitFourPeel ≠ typeAPeeledCharge)
    (peelOf : (input : Input BranchState Presentation presentation data) →
      typeAExitFourPeel.At input →
      ∀ piece : Finset input.object.Vertex, ∀ receiver : input.object.Vertex,
        ∀ peeled : Finset input.object.Vertex,
          peeled ⊆ Graph.ExitFour.routedLoads piece data.threshold receiver →
          Graph.ExitFour.SaturatedAfter piece data.threshold
              data.dischargeScale receiver peeled →
            ∃ load ∈ Graph.ExitFour.routedLoads piece data.threshold receiver,
              load ∉ peeled)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ piece : Finset input.object.Vertex, ∀ receiver : input.object.Vertex,
        ∃ peeled : Finset input.object.Vertex,
          peeled ⊆ Graph.ExitFour.routedLoads piece data.threshold receiver ∧
            ¬ Graph.ExitFour.SaturatedAfter piece data.threshold
              data.dischargeScale receiver peeled) →
      typeAPeeledCharge.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAPeeledCharge
    (rowManifest typeAExitFourPeel typeAPeeledCharge distinct)
    (fun inputs =>
      let step := peelOf inputs.current (inputs.get typeAExitFourPeel)
      .cons (key := typeAPeeledCharge)
        (encode inputs.current
          (fun piece receiver => by
            obtain ⟨peeled, inside, unsaturated⟩ :=
              Graph.ExitFour.exists_unsaturated_peeling piece data.threshold
                data.dischargeScale receiver (step piece receiver)
            exact ⟨peeled, inside, unsaturated⟩))
        .nil)

/-! ## Node `[101]`: exit `(4)`, the route-8 (Q5) reading

`def:typeA-saturated-exits` exit `(4)` is the target-defective canonical
quotient.  Clause (Q5) of `def:typeA-exit4-family` is the one this branch can
generate: a two-carrier entry whose declared deletion witness makes a
carrier-deletion quotient target-defective.  The yes arm is the manuscript's
target-defect peel; the no arm is (R2) for exit `(4)`, and it is the fact the
route-8 arm reads at nodes `[116]` and `[124]`.

The split is taken on a `Prop`, so no entry is extracted to build the branch,
and the arm not taken is absent from the taken branch's key index. -/
noncomputable def typeAExitFourDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeAExitFour typeAExitFourFree :
      FactKey (Input BranchState Presentation presentation data))
    (encodeExit :
      (∃ residual : Route8Data data current.object,
        ∃ index ∈ residual.entries, residual.ExitFour index) →
        typeAExitFour.At current)
    (encodeFree :
      Graph.Route8.ExitFourFree (Graph.HasCycleWithLength data.LengthOK)
        current.object → typeAExitFourFree.At current)
    (exitFresh : typeAExitFour ∉ known)
    (freeFresh : typeAExitFourFree ∉ known) :
    Decision typeAExitFour typeAExitFourFree previous :=
  Decision.run previous typeAExitFour typeAExitFourFree
    `Hypostructure.Graph.Strategy.Spine.typeAExitFour
    (by
      classical
      by_cases occurs :
          ∃ residual : Route8Data data current.object,
            ∃ index ∈ residual.entries, residual.ExitFour index
      · exact .inl (encodeExit occurs)
      · refine .inr (encodeFree ?_)
        intro residual index member exitFour
        exact occurs ⟨residual, index, member, exitFour⟩)
    exitFresh freeFresh

/-! ## Node `[103]`: exit `(5)`

`def:typeA-saturated-exits` exit `(5)` is the target-complete compression, which
`def:typeA-trace-basin` records as alternative (b): a *nontrivial*
target-complete quotient of the trace-basin reading.  At an indexed entry that
quotient is the internal-forgetting reading `ρ°_𝒞`, so the yes arm is an entry
whose `ρ°_𝒞` agrees with its core reading, and the no arm is the surviving trace
`lem:typeA-one-terminal-collapse` collapses against. -/
noncomputable def typeAExitFiveDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeAExitFive typeAExitFiveFree :
      FactKey (Input BranchState Presentation presentation data))
    (encodeExit :
      (∃ residual : Route8Data data current.object,
        ∃ index ∈ residual.entries, ¬ residual.SurvivingTrace index) →
        typeAExitFive.At current)
    (encodeFree :
      Graph.Route8.TraceSurviving (Graph.HasCycleWithLength data.LengthOK)
        current.object → typeAExitFiveFree.At current)
    (exitFresh : typeAExitFive ∉ known)
    (freeFresh : typeAExitFiveFree ∉ known) :
    Decision typeAExitFive typeAExitFiveFree previous :=
  Decision.run previous typeAExitFive typeAExitFiveFree
    `Hypostructure.Graph.Strategy.Spine.typeAExitFive
    (by
      classical
      by_cases occurs :
          ∃ residual : Route8Data data current.object,
            ∃ index ∈ residual.entries, ¬ residual.SurvivingTrace index
      · exact .inl (encodeExit occurs)
      · refine .inr (encodeFree ?_)
        intro residual index member
        by_contra failing
        exact occurs ⟨residual, index, member, failing⟩)
    exitFresh freeFresh

/-! ## Node `[109]`: the route-8 arm placement

`def:typeA-saturated-exits` exit `(8)` is the one saturated alternative that
does not close, and `def:typeA-silent-core-residual` names the residual it
produces.  The arm is entered behind nodes `[101]` and `[103]`, whose no arms
are (R2), and the question it is placed on is `def:typeA-large-budget-deficit`'s:
does the object carry a *large-budget* route-8 collection --
`Graph.Route8.Data.LargeBudget`, the burden of `lem:typeA-route8-burden`, the
large-budget deficit, and the registered rate condition?

The split is taken on a `Prop`, so no residual is extracted to build the branch,
and the arm not taken is absent from the taken branch's key index: a row of this
block cannot be read by a branch that carries no route-8 residual. -/
noncomputable def route8Placement
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (route8Residual route8Free :
      FactKey (Input BranchState Presentation presentation data))
    (encodeResidual :
      (∃ residual : Route8Data data current.object, residual.LargeBudget) →
        route8Residual.At current)
    (encodeFree :
      (¬ ∃ residual : Route8Data data current.object, residual.LargeBudget) →
        route8Free.At current)
    (residualFresh : route8Residual ∉ known)
    (freeFresh : route8Free ∉ known) :
    Decision route8Residual route8Free previous :=
  Decision.run previous route8Residual route8Free
    `Hypostructure.Graph.Strategy.Spine.route8Residual
    (by
      classical
      by_cases carried :
          ∃ residual : Route8Data data current.object, residual.LargeBudget
      · exact .inl (encodeResidual carried)
      · exact .inr (encodeFree carried))
    residualFresh freeFresh

/-! ## Nodes `[111]`--`[113]`: the collection, its burden, and the deficit bound

`def:typeA-large-budget-deficit` sums `¼|V(X)| − def⁺(X)` over the collection,
and `lem:typeA-route8-burden` is `N_basin(𝒳) ≥ 4·D_A(𝒳)`.  Node `[113]` spends
the second against the first: substituting the burden into the large-budget
bound gives `|R| ≤ N_basin + 4·def⁺(R)`, which is the single reading the census
of node `[122]` collides with the rate condition.

The row **reads the node-`[109]` residual by exact key** and publishes the
reduced form; the substitution is `Graph.Route8.deficit_le_basins`. -/
@[reducible] noncomputable def route8BurdenRow
    (route8Residual route8Burden :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : route8Residual ≠ route8Burden)
    (residualOf : (input : Input BranchState Presentation presentation data) →
      route8Residual.At input →
      ∃ residual : Route8Data data input.object, residual.LargeBudget)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ residual : Route8Data data input.object, residual.Reduced) →
      route8Burden.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8Burden
    (rowManifest route8Residual route8Burden distinct)
    (fun inputs =>
      .cons (key := route8Burden)
        (encode inputs.current
          (Exists.imp
            (fun _residual large =>
              Graph.Route8.Data.Reduced.of_largeBudget large)
            (residualOf inputs.current (inputs.get route8Residual))))
        .nil)

/-! ## Nodes `[114]`--`[116]`: the essential carrier core

`lem:typeA-one-terminal-collapse`: an indexed entry with at most one essential
carrier makes the internal-forgetting reading `ρ°_𝒞` agree with the core
reading, which its surviving trace denies.  So every indexed entry of a true
route-8 residual has `α ≥ 2`.

The proof is `Graph.Route8.Data.two_le_alpha`, and its ingredient is the
object's own: `lem:typeA-carrier-cut-parity` is `Graph.CutParity` at the
support's cut.  The row reads no prerequisite, because the collapse is a
theorem about every route-8 residual of the object. -/
@[reducible] noncomputable def route8CarrierCoreRow
    (route8CarrierCore :
      FactKey (Input BranchState Presentation presentation data))
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ residual : Route8Data data input.object,
        ∀ index ∈ residual.entries,
          residual.SurvivingTrace index → 2 ≤ residual.alpha index) →
      route8CarrierCore.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8CarrierCore
    (sourceFreeManifest route8CarrierCore)
    (fun inputs =>
      .cons (key := route8CarrierCore)
        (encode inputs.current
          (fun residual _index _member surviving =>
            residual.two_le_alpha surviving))
        .nil)

/-! ## Nodes `[117]`--`[122]`: the private-carrier census

`prop:typeA-route8-carrier-reduction`.  If no indexed entry were two-carrier,
every entry would have at least `threshold + 1` private essential carriers;
private carriers of distinct entries are disjoint boundary incidences, so the
collection's indexed count times that floor fits inside the boundary supply,
while node `[113]`'s bound pushes it the other way.  The registered rate
condition -- the manuscript's `τ_win < 3/13` -- makes the two impossible
together, so a two-carrier entry exists, and the residual's own clauses ride
with it into node `[124]` as `def:typeA-terminal-two-carrier`'s package. -/
@[reducible] noncomputable def route8CensusRow
    (route8Census : FactKey (Input BranchState Presentation presentation data))
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ residual : Route8Data data input.object,
        residual.Reduced → residual.TwoCarrierEntry) →
      route8Census.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8Census
    (sourceFreeManifest route8Census)
    (fun inputs =>
      .cons (key := route8Census)
        (encode inputs.current
          (fun _residual reduced => reduced.twoCarrierEntry))
        .nil)

/-! ## Node `[123]`: the pressure descent

The manuscript's node-`[123]` row places the remaining linear Type A deficit in
the unified target-defect/route-8 ledger: *"either peels a target-defect load by
exit (4) or forces a two-carrier route-8 entry; target-defect two-carrier
entries decrease `Λ₄`; the terminal non-peeling case enters node `[124]`."*

Both halves are committed.  The routing is node `[122]`'s census, **read by
exact key**: a reduced residual forces the terminal two-carrier package.  The
descent's own measure is the second clause: peeling an entry off the active set
strictly decreases it, which is why the manuscript's loop back to `[89]` is a
terminating recursion and not a cycle in the DAG. -/
@[reducible] noncomputable def route8DescentRow
    (route8Census route8Descent :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : route8Census ≠ route8Descent)
    (censusOf : (input : Input BranchState Presentation presentation data) →
      route8Census.At input →
      ∀ residual : Route8Data data input.object,
        residual.Reduced → residual.TwoCarrierEntry)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ residual : Route8Data data input.object,
        (residual.Reduced → residual.TwoCarrierEntry) ∧
          ∀ active : Finset residual.Index, ∀ index ∈ active,
            (active.erase index).card < active.card) →
      route8Descent.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8Descent
    (rowManifest route8Census route8Descent distinct)
    (fun inputs =>
      let census := censusOf inputs.current (inputs.get route8Census)
      .cons (key := route8Descent)
        (encode inputs.current
          (fun residual =>
            ⟨census residual,
              fun _active _index member => Finset.card_erase_lt_of_mem member⟩))
        .nil)

/-! ## Node `[103]`: is the exit-`(5)` compression realized by a smaller atom?

`lem:typeA-exits-discharged`: *"Exit (5) is a nontrivial target-complete response
compression.  If the compression is realized by a smaller proper atom, it
contradicts hereditary target-uncompressibility (`cor:uncompressible`); if it
occurs only at the trace-basin response level, it is exactly failure alternative
(b) in `def:typeA-trace-basin` and therefore is not an admissible route-8
residual."*

That sentence is a dichotomy, and this is it.  The yes arm carries the
`lem:replacement` compression, which node `[14]`'s fact denies -- so the arm
closes.  The no arm records that the compression stayed at the response level,
which is where `def:typeA-trace-basin`'s alternative (b) lives; that branch has
no `typeAExitFiveFree` in its index and therefore cannot enter the route-8
arm. -/
noncomputable def typeAExitFiveRealizationDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeAExitFiveCompression typeAExitFiveTraceLevel :
      FactKey (Input BranchState Presentation presentation data))
    (encodeCompression :
      (∃ support : Finset current.object.Vertex,
        Graph.Strategy.InterfaceReplacement.CompressibleSupport
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) current.object support) →
        typeAExitFiveCompression.At current)
    (encodeTraceLevel :
      (¬ ∃ support : Finset current.object.Vertex,
        Graph.Strategy.InterfaceReplacement.CompressibleSupport
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) current.object support) →
        typeAExitFiveTraceLevel.At current)
    (compressionFresh : typeAExitFiveCompression ∉ known)
    (traceLevelFresh : typeAExitFiveTraceLevel ∉ known) :
    Decision typeAExitFiveCompression typeAExitFiveTraceLevel previous :=
  Decision.run previous typeAExitFiveCompression typeAExitFiveTraceLevel
    `Hypostructure.Graph.Strategy.Spine.typeAExitFiveCompression
    (by
      classical
      by_cases realized :
          ∃ support : Finset current.object.Vertex,
            Graph.Strategy.InterfaceReplacement.CompressibleSupport
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) current.object support
      · exact .inl (encodeCompression realized)
      · exact .inr (encodeTraceLevel realized))
    compressionFresh traceLevelFresh

/-! ## Node `[124]`: the terminal two-carrier no-go

`thm:typeA-two-carrier-nogo` with `prop:typeA-route8-closure-from-nogo`.  A
terminal two-carrier route-8 obstruction is a pair `(𝒳, ξ)` whose clauses (T1)
to (T5) the block has now assembled, **each of them as a fact read from the
ledger by exact key**:

* (T1) is node `[113]`'s reduced large-budget collection;
* (T2) is nodes `[101]` and `[103]`'s exit absences;
* (T3) is node `[116]`'s carrier core;
* (T4) is the two-carrier entry node `[123]` routed from node `[122]`'s census;
* (T5) is `lem:typeA-essential-deletion-witness`, which node `[116]`'s core
  *proves*: inclusion-minimality separates the core reading from every
  one-carrier deletion of it, and the forgotten coordinate's carrier support
  contains the deleted carrier.

`lem:typeA-two-carrier-deletion-canonical` and `lem:typeA-carrier-deletion-exit`
assemble those into `Route8.Data.ExitFour` -- clause (Q5) of
`def:typeA-exit4-family` -- and node `[101]` denies it.  So no large-budget
route-8 collection exists, which is the negation of the fact node `[109]`
committed. -/
@[reducible] noncomputable def route8ClosedRow
    (route8Burden route8CarrierCore route8Descent typeAExitFourFree
      typeAExitFiveFree route8Closed :
      FactKey (Input BranchState Presentation presentation data))
    (requiredDistinct :
      [route8Burden, route8CarrierCore, route8Descent, typeAExitFourFree,
        typeAExitFiveFree].Nodup)
    (burdenOf : (input : Input BranchState Presentation presentation data) →
      route8Burden.At input →
      ∃ residual : Route8Data data input.object, residual.Reduced)
    (coreOf : (input : Input BranchState Presentation presentation data) →
      route8CarrierCore.At input →
      ∀ residual : Route8Data data input.object,
        ∀ index ∈ residual.entries,
          residual.SurvivingTrace index → 2 ≤ residual.alpha index)
    (descentOf : (input : Input BranchState Presentation presentation data) →
      route8Descent.At input →
      ∀ residual : Route8Data data input.object,
        (residual.Reduced → residual.TwoCarrierEntry) ∧
          ∀ active : Finset residual.Index, ∀ index ∈ active,
            (active.erase index).card < active.card)
    (exitFourFreeOf :
      (input : Input BranchState Presentation presentation data) →
      typeAExitFourFree.At input →
      Graph.Route8.ExitFourFree (Graph.HasCycleWithLength data.LengthOK)
        input.object)
    (exitFiveFreeOf :
      (input : Input BranchState Presentation presentation data) →
      typeAExitFiveFree.At input →
      Graph.Route8.TraceSurviving (Graph.HasCycleWithLength data.LengthOK)
        input.object)
    (encode : (input : Input BranchState Presentation presentation data) →
      (¬ ∃ residual : Route8Data data input.object, residual.LargeBudget) →
      route8Closed.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8Closed
    { Requires := [route8Burden, route8CarrierCore, route8Descent,
        typeAExitFourFree, typeAExitFiveFree]
      Produces := [route8Closed]
      requiresUnique := requiredDistinct
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let reduced := burdenOf inputs.current (inputs.get route8Burden)
      let core := coreOf inputs.current (inputs.get route8CarrierCore)
      let descent := descentOf inputs.current (inputs.get route8Descent)
      let exitFree :=
        exitFourFreeOf inputs.current (inputs.get typeAExitFourFree)
      let surviving :=
        exitFiveFreeOf inputs.current (inputs.get typeAExitFiveFree)
      .cons (key := route8Closed)
        (encode inputs.current
          (fun _large =>
            Graph.Route8.Data.no_twoCarrierEntry (core reduced.choose)
              (surviving reduced.choose) (exitFree reduced.choose)
              ((descent reduced.choose).1 reduced.choose_spec)))
        .nil)

end Hypostructure.Graph.Strategy.Spine
