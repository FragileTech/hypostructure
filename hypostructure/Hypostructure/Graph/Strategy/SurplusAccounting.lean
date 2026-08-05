import Hypostructure.Core.Strategy.OrderedSurplusActivation
import Hypostructure.Core.Strategy.BaselineDemandAccounting
import Hypostructure.Core.Strategy.CanonicalPairResponseAccounting
import Hypostructure.Core.Strategy.CanonicalPairResponseAccountingSemantics
import Hypostructure.Core.Strategy.CanonicalCapacityTokenAccountingSemantics
import Hypostructure.Core.Strategy.CoupledHomogeneousFibrePressure
import Hypostructure.Core.Strategy.CoupledHomogeneousFibrePressureSemantics
import Hypostructure.Core.Strategy.FiniteBottleneckClassificationSemantics
import Hypostructure.Core.Strategy.HomogeneousBottleneck
import Hypostructure.Core.Strategy.HomogeneousBottleneckSemantics
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Hypostructure.Graph.Finite
import Hypostructure.Graph.Target
import Hypostructure.Graph.Strategy.MinimumDegreeBaseline
import Hypostructure.Graph.Strategy.Official.Features.DegreeSurplusLedger
import Hypostructure.Graph.NearCubicSpine
import Hypostructure.Graph.SameTokenBlockerRoles

/-!
# Graph presentations for surplus accounting

These adapters derive the complete CT presentations from the current finite
graph and a caller-supplied baseline degree.  They select no outcome and own
no execution or routing.
-/

namespace Hypostructure.Graph.Strategy.SurplusAccounting

open Hypostructure

universe u uStage uPrevious

/-- Canonical counting resource used by finite graph accounting. -/
def countingBudget : Core.ResourceBudget where
  Resource := Nat
  le := (· ≤ ·)
  leRefl := Nat.le_refl
  leTrans := Nat.le_trans
  zero := Nat.zero
  add := Nat.add
  ceiling := id
  zeroLe := Nat.zero_le
  addMono := Nat.add_le_add
  addAssoc := Nat.add_assoc
  zeroAdd := Nat.zero_add
  addZero := Nat.add_zero

/-- The canonical vertex scan of a finite graph, at the layer the strategy
members live on.  `Graph.Strategy.vertexScan` is the same schedule above the
member modules; this is the one they can import. -/
noncomputable def vertices (object : Graph.FiniteObject.{u}) :
    Core.Finite.Enumeration object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Core.Finite.Enumeration.ofNodupList object.orderedVertices
    object.orderedVertices_nodup

private noncomputable def neighbours (object : Graph.FiniteObject.{u})
    (vertex : object.Vertex) :
    Core.Finite.Enumeration object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Core.Finite.Enumeration.ofNodupList (object.orderedNeighbors vertex)
    (object.orderedNeighbors_nodup vertex)

/-- Exact degree mass of the complete graph-owned vertex schedule. -/
private noncomputable def degreeMass (object : Graph.FiniteObject.{u}) : Nat :=
  (object.orderedVertices.map object.degree).sum

/-! ## `thm:homogeneous-overload-geometric-closure`: the fixed homogeneous caps

`def:same-token-blocker-roles` bounds the same-token role alphabet over one
capacity token by `Q_st = 6·(2+1+3) = 36`: the six canonical blocker types of
`def:surplus-blockers` times the six token subtypes `RW, WW` (window
incidence), `R` (remainder surplus) and `V, I, P` (primitive carrier).  That
alphabet is the declared type `Graph.SameTokenBlockerRoles.Role`, and
`sameTokenRoleBound` below is its `Fintype.card`; no numeral is written.

`def:homogeneous-token-charge` converts a role-fibre pattern bound `L` into the
uniform per-token load allowance

`Cap_hom(L) = Q_st (L-1)(2L-3)`,

which is `lem:same-token-matching-star`'s matching--star bound `(L-1)(2L-3)`
charged separately to each of the at most `Q_st` role fibres over that token.

`thm:homogeneous-overload-geometric-closure` closes the geometric bottleneck
with the *same* fixed bound in all three token classes,
`L_W = L_R = L_P = L_geom`, so a single uniform cap `M_0 = Cap_hom(L_geom)`
holds at every capacity token.  The proof of
`cor:homogeneous-same-token-caps-close` then only uses the aggregate form of
those caps, `|Π_blk| ≤ M_0 |𝔗_cap|` (`lem:token-ledger-no-overcount`), and
feeds it to `thm:tokenized-surplus-accounting-closure` to obtain
`σ(G) = O(√n)`.  That aggregate comparison is exactly what the final CT14 of
the homogeneous-bottleneck composition performs on the `bounded` route. -/

def sameTokenRoleBound : Nat :=
  Fintype.card Graph.SameTokenBlockerRoles.Role

/-- `Cap_hom(L) = Q_st (L-1)(2L-3)` of `def:homogeneous-token-charge`: the
uniform token load allowed when no role-homogeneous same-token `L`-matching and
no role-homogeneous same-token `L`-star occurs at that token.

`(L-1)(2L-3)` is transcribed verbatim from `lem:same-token-matching-star`; its
coefficients are that lemma's statement, not a threshold chosen here, and `L`
itself is supplied by the caller. -/
def homogeneousCapCharge (patternBound : Nat) : Nat :=
  sameTokenRoleBound * ((patternBound - 1) * (2 * patternBound - 3))

def geometricPatternBound (baselineDegree : Nat) : Nat := baselineDegree + 1

/-- `M_0 = Cap_hom(L_geom)` of `cor:homogeneous-same-token-caps-close`, in the
ordered-incidence units used by the registration below: the bounded CT14 reads
each blocked active-demand pair once from each of its two endpoints, so both
sides of `|Π_blk| ≤ M_0|𝔗_cap|` are doubled and the comparison is unchanged.

The factor is the arity of an unordered pair `π = {p,q}`, i.e. the same `2` as
in `σ(G)(σ(G)-1) = 2|Π_blk|` (`lem:token-ledger-no-overcount`) which the
registered `boundedLowerMass` produces; it is a unit conversion, not a
threshold.  The baseline it is applied at is the caller's, and every call site
below reads it from the registered presentation. -/
def homogeneousTokenCap (baselineDegree : Nat) : Nat :=
  2 * homogeneousCapCharge (geometricPatternBound baselineDegree)

private def singletonUnit : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.singleton ()

private def completeUnit : Core.Finite.CompleteEnumeration Unit :=
  Core.Finite.CompleteEnumeration.ofFinEnum inferInstance

private abbrev BoundedClosedWalk (object : Graph.FiniteObject.{u}) :=
  Σ vertex : object.Vertex,
    { walk : object.graph.Walk vertex vertex //
      walk.length < object.vertexCount + 1 }

/-- Complete finite schedule of closed walks long enough to contain every
simple cycle of a finite graph. -/
private noncomputable def boundedClosedWalks
    (object : Graph.FiniteObject.{u}) :
    Core.Finite.Enumeration (BoundedClosedWalk object) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : SimpleGraph.LocallyFinite object.graph :=
    fun _ => Fintype.ofFinite _
  letI : Fintype (BoundedClosedWalk object) := inferInstance
  letI : DecidableEq (BoundedClosedWalk object) := Classical.decEq _
  let enumeration : FinEnum (BoundedClosedWalk object) :=
    FinEnum.ofList Finset.univ.toList (by simp)
  exact Core.Finite.Enumeration.ofFinEnum enumeration

private def AcceptsBoundedClosedWalk
    (object : Graph.FiniteObject.{u}) (LengthOK : Nat → Prop)
    (candidate : BoundedClosedWalk object) : Prop :=
  candidate.2.1.IsCycle ∧ LengthOK candidate.2.1.length

private noncomputable def acceptedBoundedClosedWalks
    (object : Graph.FiniteObject.{u}) (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length)) :
    Core.Finite.Enumeration
      { candidate : BoundedClosedWalk object //
        AcceptsBoundedClosedWalk object LengthOK candidate } :=
  (boundedClosedWalks object).subtype
    (AcceptsBoundedClosedWalk object LengthOK)
    (fun candidate => by
      letI : DecidableEq object.Vertex := object.vertices.decEq
      exact @instDecidableAnd candidate.2.1.IsCycle
        (LengthOK candidate.2.1.length)
        (Graph.isCycleDecidable candidate.2.1)
        (lengthDecidable candidate.2.1.length))

private def certificateOfAcceptedBoundedClosedWalk
    (object : Graph.FiniteObject.{u}) (LengthOK : Nat → Prop)
    (candidate : { candidate : BoundedClosedWalk object //
      AcceptsBoundedClosedWalk object LengthOK candidate }) :
    Graph.CycleCertificate object LengthOK where
  vertex := candidate.1.1
  walk := candidate.1.2.1
  isCycle := candidate.2.1
  length_ok := candidate.2.2

/-- Exact duplicate-free schedule of every accepted simple-cycle
certificate.  It is derived solely from the finite graph and the public
length predicate. -/
private noncomputable def cycleCertificates
    (object : Graph.FiniteObject.{u}) (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length)) :
    Core.Finite.Enumeration (Graph.CycleCertificate object LengthOK) := by
  letI : DecidableEq (Graph.CycleCertificate object LengthOK) :=
    Classical.decEq _
  let accepted :=
    acceptedBoundedClosedWalks object LengthOK lengthDecidable
  let values := (accepted.values.map
    (certificateOfAcceptedBoundedClosedWalk object LengthOK)).dedup
  exact {
    values := values
    nodup := by exact List.nodup_dedup _
    decEq := inferInstance }

private theorem cycleCertificate_mem
    (object : Graph.FiniteObject.{u}) (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length))
    (certificate : Graph.CycleCertificate object LengthOK) :
    certificate ∈ (cycleCertificates object LengthOK lengthDecidable).values := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  have tail_lt : certificate.walk.tail.length < object.vertexCount := by
    have vertexCard :
        Fintype.card object.Vertex = object.vertexCount := by
      exact (@FinEnum.card_eq_fintypeCard object.Vertex object.vertices).symm
    exact (certificate.isCycle.isPath_tail.length_lt).trans_eq vertexCard
  have walk_lt : certificate.walk.length < object.vertexCount + 1 := by
    have notNil := certificate.isCycle.not_nil
    rw [← certificate.walk.length_tail_add_one notNil]
    omega
  let candidate : BoundedClosedWalk object :=
    ⟨certificate.vertex, ⟨certificate.walk, walk_lt⟩⟩
  let acceptedCandidate :
      { candidate : BoundedClosedWalk object //
        AcceptsBoundedClosedWalk object LengthOK candidate } :=
    ⟨candidate, certificate.isCycle, certificate.length_ok⟩
  have bounded_mem :
      candidate ∈ (boundedClosedWalks object).values := by
    simp [boundedClosedWalks]
  have accepted_mem :
      acceptedCandidate ∈
        (acceptedBoundedClosedWalks object LengthOK
          lengthDecidable).values := by
    exact (Core.Finite.Enumeration.mem_subtype_values
      (boundedClosedWalks object)
      (AcceptsBoundedClosedWalk object LengthOK) _ acceptedCandidate).2
        bounded_mem
  simp only [cycleCertificates, List.mem_dedup]
  exact List.mem_map.mpr ⟨acceptedCandidate, accepted_mem, rfl⟩

private abbrev unitResponseSystem : Core.Response.System Unit :=
  Core.Response.System.ofDecodedContexts Unit Unit Unit (fun _ _ => ()) id

private def unitTargetSemantics :
    Core.Response.TargetSemantics unitResponseSystem where
  TargetResponse := fun _ _ => True
  Accepts := fun _ => True
  target_iff_accepts := by simp

/-- Residual-owned homogeneous-bottleneck presentation over the actual graph
vertex schedule.  All numeric observations are graph degrees or the queried
baseline; the finite response system is the exact one-coordinate unit
system, and CT1 scans the complete graph-derived accepted-cycle schedule. -/
noncomputable def homogeneousBottleneckOfLowerBound
    {Residual : Type u} {Target : Residual → Prop}
    (object : Residual → Graph.FiniteObject)
    (baselineDegree : Residual → Nat)
    (minimumDegree : ∀ residual,
      baselineDegree residual ≤ (object residual).minDegree)
    (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length))
    (cycleToTarget : ∀ residual,
      Graph.HasCycleWithLength LengthOK (object residual) → Target residual) :
    Core.Strategy.HomogeneousBottleneck.Registration.{u, 0}
      Residual Target where
  Item := fun residual => (object residual).Vertex
  HomogeneityCode := fun residual => (object residual).Vertex
  items := fun residual => vertices (object residual)
  completeHomogeneityCodes := fun residual =>
    Core.Finite.CompleteEnumeration.ofFinEnum (object residual).vertices
  homogeneityCodeOf := fun _ vertex => vertex
  homogeneityCapacity := fun residual vertex =>
    (object residual).degree vertex

  CapacityLabel := fun residual => (object residual).Vertex
  codeCapacity := fun residual vertex =>
    some ((object residual).degree vertex)
  codeLabel := fun _ vertex => some vertex
  codeLabelDecidableEq := fun residual => (object residual).vertices.decEq

  Datum := fun residual => (object residual).Vertex
  LocalClass := fun residual => (object residual).Vertex
  Promotion := fun residual => (object residual).Vertex
  data := fun residual => vertices (object residual)
  completeLocalClasses := fun residual =>
    Core.Finite.CompleteEnumeration.ofFinEnum (object residual).vertices
  classOf := fun _ vertex => vertex
  Direct := fun residual vertex =>
    baselineDegree residual < (object residual).degree vertex
  promote := fun _ vertex => vertex
  directDecidable := fun _ _ => inferInstance

  LocalIndex := fun residual => (object residual).Vertex
  LocalFailureData := fun residual vertex =>
    PLift ((object residual).degree vertex < baselineDegree residual)
  localOrder := fun residual => vertices (object residual)
  LocalFailure := fun residual vertex =>
    (object residual).degree vertex < baselineDegree residual
  localFailureData := fun _ _ failure => PLift.up failure
  localFailureDecidable := fun _ _ => inferInstance
  localContribution := fun residual vertex =>
    (object residual).degree vertex

  Representative := Unit
  responseSystem := unitResponseSystem
  targetSemantics := unitTargetSemantics
  ResponseCandidate := Unit
  ResponseRow := Unit
  candidatePiece := fun _ => ()
  rowPiece := fun _ => ()
  rowResponse := fun _ _ => ()
  responseSource := fun _ => ()
  responseCoordinates := fun _ => singletonUnit
  responseCandidates := fun _ => singletonUnit
  responseRows := fun _ => singletonUnit
  ResponseAdmissible := fun _ _ _ => True
  ResponseStrictlySmaller := fun _ _ _ => True
  responseValueDecEq := by
    change DecidableEq Unit
    infer_instance
  responseAdmissibleDecidable := fun _ _ _ => isTrue trivial
  responseSmallerDecidable := fun _ _ _ => isTrue trivial
  responseCandidateCoverage := by
    intro _ candidate _member
    letI : Subsingleton unitResponseSystem.Context := by
      change Subsingleton Unit
      infer_instance
    exact
      Core.Response.FiniteTable.SymbolicCoverage.ofSubsingletonSingleton
        unitResponseSystem
        { source := ()
          replacement := candidate }
        ()
  responseRowCoverage := by
    intro _ row _member
    letI : Subsingleton unitResponseSystem.Context := by
      change Subsingleton Unit
      infer_instance
    exact
      Core.Response.FiniteTable.SymbolicCoverage.ofSubsingletonSingleton
        unitResponseSystem
        { source := ()
          replacement := row }
        ()

  AdmissibilityField := fun residual => (object residual).Vertex
  AdmissibilityFailureData := fun residual vertex =>
    PLift ((object residual).degree vertex < baselineDegree residual)
  admissibilityOrder := fun residual => vertices (object residual)
  AdmissibilityFailure := fun residual vertex =>
    (object residual).degree vertex < baselineDegree residual
  admissibilityFailureData := fun _ _ failure => PLift.up failure
  admissibilityFailureDecidable := fun _ _ => inferInstance
  admissibilityContribution := fun residual vertex =>
    (object residual).degree vertex

  TargetCandidate := fun residual =>
    Graph.CycleCertificate (object residual) LengthOK
  ExceptionalCandidate := fun _ => Empty
  outcomeCandidates := fun residual =>
    (cycleCertificates (object residual) LengthOK lengthDecidable).map
      Sum.inl Sum.inl_injective (Classical.decEq _)
  RealizesTarget := fun _ _ => True
  RealizesException := fun _ impossible => nomatch impossible
  targetRealizationDecidable := fun _ _ => isTrue trivial
  exceptionRealizationDecidable := fun _ impossible => nomatch impossible
  targetOfRealization := fun residual certificate _ =>
    cycleToTarget residual ⟨certificate⟩

  supportBudget := countingBudget
  SupportSite := fun residual => (object residual).Vertex
  SupportWitness := fun _ _ => Unit
  supportFamily := fun residual =>
    { indices := vertices (object residual)
      fibres := fun _ => singletonUnit }
  SupportActive := fun _ _ => True
  SupportRelation := fun residual site _ =>
    baselineDegree residual ≤ (object residual).degree site
  supportContribution := fun residual site _ =>
    (object residual).degree site
  supportRequired := fun _ => countingBudget.zero
  supportCapacity := fun residual => degreeMass (object residual)
  supportActiveDecidable := fun _ _ => isTrue trivial
  supportRelationDecidable := fun _ _ _ => inferInstance
  supportResourceLEDecidable := Nat.decLe

  /- `thm:homogeneous-overload-geometric-closure`, bounded arm.  The bounded
  member schedule is the residual's own capacity-token schedule: every vertex
  carries the window-incidence, remainder-surplus and primitive-carrier tokens
  supported there (`V(G) ⊆ 𝔘_sp(G) ⊆ 𝔗_cap`, `lem:capacity-token-supply`).

  Its lower mass is the token's blocked active-demand load `ℓ_cap`: the token
  at `v` carries `d_G(v) - baseline` active surplus demands
  (`def:active-surplus-demands`), each of which pairs with each of the other
  `σ(G) - 1` active demands, and each blocked pair is read once from each of
  its two endpoint tokens.  Summed over the schedule this is
  `σ(G)(σ(G)-1) = 2|Π_blk|` (`lem:token-ledger-no-overcount`).

  Its capacity is the *fixed* homogeneous cap `M_0 = Cap_hom(L_geom)` of
  `thm:homogeneous-overload-geometric-closure`, the same value in all three
  token classes because `L_W = L_R = L_P = L_geom`; it does not depend on the
  token.  CT14's aggregate comparison is therefore literally
  `|Π_blk| ≤ M_0 |𝔗_cap|`, the hypothesis
  `cor:homogeneous-same-token-caps-close` feeds to
  `thm:tokenized-surplus-accounting-closure`, and the `.capacity` terminal
  records exactly `σ(G) = O(√n)`
  (`homogeneousBottleneck_degreeSurplus_le_of_bounded` below).  It is *not*
  `Σ_v d_G(v) ≤ baseline · n`, which would be the exactly-cubic case
  `σ(G) = 0`. -/
  BoundedMember := fun residual => (object residual).Vertex
  BoundedLabel := fun residual => (object residual).Vertex
  boundedMembers := fun residual => vertices (object residual)
  boundedLowerMass := fun residual vertex =>
    ((object residual).degree vertex - baselineDegree residual) *
      ((object residual).degreeSurplus (baselineDegree residual) - 1)
  boundedCapacity := fun residual _vertex =>
    some (homogeneousTokenCap (baselineDegree residual))
  boundedLabel := fun _ vertex => some vertex
  boundedLabelDecidableEq := fun residual => (object residual).vertices.decEq

  localFailureScheduled := by
    intro residual vertex _member failure
    have lower := (minimumDegree residual).trans
      ((object residual).minDegree_le_degree vertex)
    omega
  responseDefectScheduled := by
    intro _ _ _ _ _ defect
    exact (defect rfl).elim
  admissibilityFailureScheduled := by
    intro residual vertex _member failure
    have lower := (minimumDegree residual).trans
      ((object residual).minDegree_le_degree vertex)
    omega
  supportDeficitScheduled := by
    intro residual vertex member _active unsupported
    have notLower :
        ¬ baselineDegree residual ≤ (object residual).degree vertex := by
      simpa using unsupported ⟨0, by
        change 0 < 1
        omega⟩
    exact (notLower ((minimumDegree residual).trans
      ((object residual).minDegree_le_degree vertex))).elim
  supportCapacityFailureScheduled := by
    intro residual impossible
    exact (impossible (Nat.zero_le (degreeMass (object residual)))).elim
  boundedCapacityTotal := by
    intro residual member _
    exact ⟨homogeneousTokenCap (baselineDegree residual), rfl⟩
  boundedLabelTotal := by
    intro _ member _
    exact ⟨member, rfl⟩

  /- Every one of the five exceptional-schedule obligations above is
  discharged from `minimumDegree`, not by exhibiting a candidate: no local
  failure, response defect, admissibility failure, support deficit, or support
  capacity failure can occur once the queried baseline is below the graph's
  minimum degree.  `ExceptionalCandidate` is correspondingly `Empty`, and CT1
  scans a schedule of accepted cycle certificates only.  Registering that fact
  lets Core discharge the exceptional output as vacuous. -/
  exceptionalImpossible := some ⟨fun _ impossible => nomatch impossible⟩

/-- Canonical homogeneous-bottleneck registration for a graph problem whose
baseline is `minimumDegreeAtLeast k`.  Graph reconstructs both the numeric
threshold and its lower-bound theorem from the literal `ProblemInput`; the
only target bridge consumes a stored cycle certificate. -/
noncomputable def homogeneousBottleneck
    {k : Nat}
    {BranchState : Graph.FiniteObject → Type}
    {Presentation : Type} {presentation : Presentation}
    (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length)) :
    Core.Strategy.HomogeneousBottleneck.Registration
      (Core.Strategy.ProblemInput
        (Graph.problemWithPresentation
          (Graph.MinimumDegreeAtLeast k) BranchState
          Presentation presentation))
      (fun input => Graph.HasCycleWithLength LengthOK input.object) :=
  homogeneousBottleneckOfLowerBound
    (fun input => input.object)
    (fun input =>
      (Graph.Strategy.minimumDegreeThresholdQuery
        (k := k) (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)) input)
    (fun input =>
      Graph.Strategy.minimumDegreeThresholdQuery_le_minDegree input)
    LengthOK lengthDecidable (fun _ cycle => cycle)

/-- The same graph-owned strategy for a target of the canonical form
`cycle ∨ Rest`.  The cycle injection is fixed by Graph; applications provide
no target-closing callback. -/
noncomputable def homogeneousBottleneckOr
    {k : Nat}
    {BranchState : Graph.FiniteObject → Type}
    {Presentation : Type} {presentation : Presentation}
    (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length))
    (Rest : Core.Strategy.ProblemInput
      (Graph.problemWithPresentation
        (Graph.MinimumDegreeAtLeast k) BranchState
        Presentation presentation) → Prop) :
    Core.Strategy.HomogeneousBottleneck.Registration
      (Core.Strategy.ProblemInput
        (Graph.problemWithPresentation
          (Graph.MinimumDegreeAtLeast k) BranchState
          Presentation presentation))
      (fun input =>
        Graph.HasCycleWithLength LengthOK input.object ∨ Rest input) :=
  homogeneousBottleneckOfLowerBound
    (fun input => input.object)
    (fun input =>
      (Graph.Strategy.minimumDegreeThresholdQuery
        (k := k) (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)) input)
    (fun input =>
      Graph.Strategy.minimumDegreeThresholdQuery_le_minDegree input)
    LengthOK lengthDecidable (fun _ cycle => Or.inl cycle)


section BoundedCaps

variable {Residual : Type u} {Target : Residual → Prop}
variable (object : Residual → Graph.FiniteObject)
variable (baselineDegree : Residual → Nat)

private theorem sum_map_mul_right (values : List α) (weight : α → Nat)
    (factor : Nat) :
    (values.map fun value => weight value * factor).sum =
      (values.map weight).sum * factor := by
  induction values with
  | nil => simp
  | cons _ _ ih => simp [ih, Nat.add_mul]

/-- The graph's own surplus ledger read on the declared vertex order: the
registered `σ(G) = 2m - baseline·n` is the sum of the per-vertex surpluses.
This is `DegreeSurplusLedger.exact_edge_count_identity`, not a new count. -/
private theorem sum_vertexSurplus (residual : Residual)
    (minimumDegree : baselineDegree residual ≤ (object residual).minDegree) :
    ((object residual).orderedVertices.map fun vertex =>
        (object residual).degree vertex - baselineDegree residual).sum =
      (object residual).degreeSurplus (baselineDegree residual) := by
  classical
  let baseline :
      Strategy.Official.Features.DegreeSurplusLedger.MinimumDegreeBaseline
        (object residual) :=
    { degree := baselineDegree residual
      lower := fun vertex =>
        minimumDegree.trans ((object residual).minDegree_le_degree vertex) }
  have rows :=
    Strategy.Official.Features.DegreeSurplusLedger.total_derive
      (object residual) baseline
  have handshake :=
    Strategy.Official.Features.DegreeSurplusLedger.total_eq_edge_mass_sub_baseline
      (object residual) baseline
  rw [← rows, handshake]
  rfl

/-- **Registered load on the bounded route.**  The bounded CT14 lower mass,
summed over the residual's capacity-token schedule, is `σ(G)(σ(G)-1)`: each of
the `σ(G)` active surplus demands is read against each of the other `σ(G)-1`,
i.e. `2|Π_blk|` in ordered-incidence units. -/
theorem homogeneousBottleneckOfLowerBound_boundedLoad
    (minimumDegree : ∀ residual,
      baselineDegree residual ≤ (object residual).minDegree)
    (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length))
    (cycleToTarget : ∀ residual,
      Graph.HasCycleWithLength LengthOK (object residual) → Target residual)
    (residual : Residual) :
    (homogeneousBottleneckOfLowerBound object baselineDegree minimumDegree
        LengthOK lengthDecidable cycleToTarget).boundedLoad residual =
      (object residual).degreeSurplus (baselineDegree residual) *
        ((object residual).degreeSurplus (baselineDegree residual) - 1) := by
  change ((object residual).orderedVertices.map fun vertex =>
      ((object residual).degree vertex - baselineDegree residual) *
        ((object residual).degreeSurplus (baselineDegree residual) - 1)).sum = _
  rw [sum_map_mul_right, sum_vertexSurplus object baselineDegree residual
    (minimumDegree residual)]

/-- **Registered capacity on the bounded route.**  Every capacity token gets
the *same* fixed homogeneous cap, so the aggregate is `M_0 |𝔗_cap|` (doubled
by the ordered-incidence convention shared with the load). -/
theorem homogeneousBottleneckOfLowerBound_boundedCap
    (minimumDegree : ∀ residual,
      baselineDegree residual ≤ (object residual).minDegree)
    (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length))
    (cycleToTarget : ∀ residual,
      Graph.HasCycleWithLength LengthOK (object residual) → Target residual)
    (residual : Residual) :
    (homogeneousBottleneckOfLowerBound object baselineDegree minimumDegree
        LengthOK lengthDecidable cycleToTarget).boundedCap residual =
      (object residual).vertexCount *
        homogeneousTokenCap (baselineDegree residual) := by
  change ((object residual).orderedVertices.map fun _ =>
      homogeneousTokenCap (baselineDegree residual)).sum = _
  rw [(object residual).vertexCount_eq_orderedVertices_length]
  induction (object residual).orderedVertices with
  | nil => simp
  | cons _ _ _ => simp [Nat.succ_mul, Nat.add_comm]

theorem degreeSurplus_le_of_homogeneousCaps (target : Graph.FiniteObject.{u})
    (baseline cap : Nat)
    (capped : target.degreeSurplus baseline * (target.degreeSurplus baseline - 1)
      ≤ target.vertexCount * cap) :
    target.degreeSurplus baseline ≤ 1 + Nat.sqrt (cap * target.vertexCount) := by
  rcases Nat.eq_zero_or_pos (target.degreeSurplus baseline) with zero | positive
  · omega
  · have square :
        (target.degreeSurplus baseline - 1) * (target.degreeSurplus baseline - 1)
          ≤ cap * target.vertexCount := by
      refine le_trans (le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ 1)) capped) ?_
      exact le_of_eq (Nat.mul_comm _ _)
    have root := (Nat.le_sqrt
      (m := target.degreeSurplus baseline - 1)
      (n := cap * target.vertexCount)).2 square
    omega

theorem homogeneousBottleneckOfLowerBound_degreeSurplus_le_of_bounded
    (minimumDegree : ∀ residual,
      baselineDegree residual ≤ (object residual).minDegree)
    (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length))
    (cycleToTarget : ∀ residual,
      Graph.HasCycleWithLength LengthOK (object residual) → Target residual)
    (residual : Residual)
    (certificate :
      (homogeneousBottleneckOfLowerBound object baselineDegree minimumDegree
          LengthOK lengthDecidable cycleToTarget).boundedLoad residual ≤
        (homogeneousBottleneckOfLowerBound object baselineDegree minimumDegree
          LengthOK lengthDecidable cycleToTarget).boundedCap residual) :
    (object residual).degreeSurplus (baselineDegree residual) ≤
      1 + Nat.sqrt (homogeneousTokenCap (baselineDegree residual) *
        (object residual).vertexCount) := by
  rw [homogeneousBottleneckOfLowerBound_boundedLoad object baselineDegree
      minimumDegree LengthOK lengthDecidable cycleToTarget residual,
    homogeneousBottleneckOfLowerBound_boundedCap object baselineDegree
      minimumDegree LengthOK lengthDecidable cycleToTarget residual]
    at certificate
  exact degreeSurplus_le_of_homogeneousCaps (object residual)
    (baselineDegree residual) _ certificate

theorem boundedRoute_degreeSurplus_le
    {Previous : Type uPrevious}
    [Core.Residual.HasResidual Previous Residual]
    (profile :
      Core.Strategy.HomogeneousBottleneck.Profile.{uPrevious, u, 0}
        Previous Residual Target)
    (minimumDegree : ∀ residual,
      baselineDegree residual ≤ (object residual).minDegree)
    (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length))
    (cycleToTarget : ∀ residual,
      Graph.HasCycleWithLength LengthOK (object residual) → Target residual)
    (registered : profile.registration =
      homogeneousBottleneckOfLowerBound object baselineDegree minimumDegree
        LengthOK lengthDecidable cycleToTarget)
    {semantics : profile.Semantics} {previous : Previous}
    (witness : profile.RoutedResidual semantics previous .bounded) :
    (object (profile.current previous)).degreeSurplus
        (baselineDegree (profile.current previous)) ≤
      1 + Nat.sqrt
        (homogeneousTokenCap (baselineDegree (profile.current previous)) *
          (object (profile.current previous)).vertexCount) := by
  have certificate :=
    Core.Strategy.HomogeneousBottleneck.Profile.bounded_load_le_cap
      profile witness
  rw [registered] at certificate
  exact homogeneousBottleneckOfLowerBound_degreeSurplus_le_of_bounded object
    baselineDegree minimumDegree LengthOK lengthDecidable cycleToTarget
    (profile.current previous) certificate

end BoundedCaps

/-! ### The same estimate in the Type B ledger's spelling of `σ(G)` -/

theorem globalSurplus_le_of_homogeneousCaps (target : Graph.FiniteObject.{0})
    (minDegree : ∀ vertex : target.Vertex, 3 ≤ target.degree vertex)
    (cap : Nat)
    (capped : target.degreeSurplus 3 * (target.degreeSurplus 3 - 1)
      ≤ target.vertexCount * cap) :
    Graph.TypeBBridgeResidual.globalSurplus target
      ≤ ((1 + Nat.sqrt (cap * target.vertexCount) : Nat) : ℚ) := by
  rw [Graph.NearCubicSpine.globalSurplus_eq_degreeSurplus target minDegree]
  exact_mod_cast degreeSurplus_le_of_homogeneousCaps target 3 cap capped

/-- The positive-part spelling of the same estimate, on the standing branch
`δ(G) ≥ 3`. -/
theorem globalSurplusPos_le_of_homogeneousCaps (target : Graph.FiniteObject.{0})
    (minDegree : ∀ vertex : target.Vertex, 3 ≤ target.degree vertex)
    (cap : Nat)
    (capped : target.degreeSurplus 3 * (target.degreeSurplus 3 - 1)
      ≤ target.vertexCount * cap) :
    Graph.TypeBBridgeResidual.globalSurplusPos target
      ≤ ((1 + Nat.sqrt (cap * target.vertexCount) : Nat) : ℚ) := by
  rw [Graph.NearCubicSpine.globalSurplusPos_eq_degreeSurplus target minDegree]
  exact_mod_cast degreeSurplus_le_of_homogeneousCaps target 3 cap capped

/-- **The same estimate at an arbitrary registered baseline.**  No numeral
appears: the baseline is the presentation's own
`Graph.ReceiverLoad.LoadCapacityProfile.baselineDegree`, the surplus is
`Graph.TypeBBridgeResidual.globalSurplusOf` at that profile, and the bridge to
the natural `degreeSurplus` observable is the registered-baseline handshake
`Graph.NearCubicSpine.globalSurplusOf_eq_degreeSurplus`. -/
theorem globalSurplusOf_le_of_homogeneousCaps (target : Graph.FiniteObject.{0})
    (profile : Graph.ReceiverLoad.LoadCapacityProfile)
    (minDegree :
      ∀ vertex : target.Vertex, profile.baselineDegree ≤ target.degree vertex)
    (cap : Nat)
    (capped : target.degreeSurplus profile.baselineDegree *
        (target.degreeSurplus profile.baselineDegree - 1)
      ≤ target.vertexCount * cap) :
    Graph.TypeBBridgeResidual.globalSurplusOf profile target
      ≤ ((1 + Nat.sqrt (cap * target.vertexCount) : Nat) : ℚ) := by
  rw [Graph.NearCubicSpine.globalSurplusOf_eq_degreeSurplus target profile
    minDegree]
  exact_mod_cast degreeSurplus_le_of_homogeneousCaps target
    profile.baselineDegree cap capped

/-- The positive-part spelling at an arbitrary registered baseline. -/
theorem globalSurplusPosOf_le_of_homogeneousCaps
    (target : Graph.FiniteObject.{0})
    (profile : Graph.ReceiverLoad.LoadCapacityProfile)
    (minDegree :
      ∀ vertex : target.Vertex, profile.baselineDegree ≤ target.degree vertex)
    (cap : Nat)
    (capped : target.degreeSurplus profile.baselineDegree *
        (target.degreeSurplus profile.baselineDegree - 1)
      ≤ target.vertexCount * cap) :
    Graph.TypeBBridgeResidual.globalSurplusPosOf profile target
      ≤ ((1 + Nat.sqrt (cap * target.vertexCount) : Nat) : ℚ) := by
  rw [Graph.NearCubicSpine.globalSurplusPosOf_eq_degreeSurplus target profile
    minDegree]
  exact_mod_cast degreeSurplus_le_of_homogeneousCaps target
    profile.baselineDegree cap capped

/-! ### The two registered node-`[144]` wrappers -/

/-- The registered wrapper is literally the general registration at the
problem-input baseline query.  Stated with explicit residual and target so the
delta step is a projection, not a unification of the whole presentation. -/
private theorem homogeneousBottleneck_eq
    {k : Nat}
    {BranchState : Graph.FiniteObject → Type}
    {Presentation : Type} {presentation : Presentation}
    (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length)) :
    homogeneousBottleneck (k := k) (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        LengthOK lengthDecidable =
      homogeneousBottleneckOfLowerBound
        (Residual := Core.Strategy.ProblemInput
          (Graph.problemWithPresentation
            (Graph.MinimumDegreeAtLeast k) BranchState
            Presentation presentation))
        (Target := fun input => Graph.HasCycleWithLength LengthOK input.object)
        (fun input => input.object)
        (fun input =>
          (Graph.Strategy.minimumDegreeThresholdQuery
            (k := k) (BranchState := BranchState)
            (Presentation := Presentation)
            (presentation := presentation)) input)
        (fun input =>
          Graph.Strategy.minimumDegreeThresholdQuery_le_minDegree input)
        LengthOK lengthDecidable (fun _ cycle => cycle) :=
  rfl

/-- The same delta step for the disjunctive wrapper. -/
private theorem homogeneousBottleneckOr_eq
    {k : Nat}
    {BranchState : Graph.FiniteObject → Type}
    {Presentation : Type} {presentation : Presentation}
    (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length))
    (Rest : Core.Strategy.ProblemInput
      (Graph.problemWithPresentation
        (Graph.MinimumDegreeAtLeast k) BranchState
        Presentation presentation) → Prop) :
    homogeneousBottleneckOr (k := k) (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        LengthOK lengthDecidable Rest =
      homogeneousBottleneckOfLowerBound
        (Residual := Core.Strategy.ProblemInput
          (Graph.problemWithPresentation
            (Graph.MinimumDegreeAtLeast k) BranchState
            Presentation presentation))
        (Target := fun input =>
          Graph.HasCycleWithLength LengthOK input.object ∨ Rest input)
        (fun input => input.object)
        (fun input =>
          (Graph.Strategy.minimumDegreeThresholdQuery
            (k := k) (BranchState := BranchState)
            (Presentation := Presentation)
            (presentation := presentation)) input)
        (fun input =>
          Graph.Strategy.minimumDegreeThresholdQuery_le_minDegree input)
        LengthOK lengthDecidable (fun _ cycle => Or.inl cycle) :=
  rfl

/-- **`cor:homogeneous-same-token-caps-close` for the registered node-`[144]`
strategy.**  Reading the bounded certificate of `homogeneousBottleneck` gives
the near-cubic spine estimate for the object carried by the residual:
`σ(G) ≤ 1 + √(M_0 n)`. -/
theorem homogeneousBottleneck_degreeSurplus_le_of_bounded
    {k : Nat}
    {BranchState : Graph.FiniteObject → Type}
    {Presentation : Type} {presentation : Presentation}
    (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length))
    (input : Core.Strategy.ProblemInput
      (Graph.problemWithPresentation
        (Graph.MinimumDegreeAtLeast k) BranchState
        Presentation presentation))
    (certificate :
      (homogeneousBottleneck (k := k) (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          LengthOK lengthDecidable).boundedLoad input ≤
        (homogeneousBottleneck (k := k) (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          LengthOK lengthDecidable).boundedCap input) :
    input.object.degreeSurplus k ≤
      1 + Nat.sqrt (homogeneousTokenCap k * input.object.vertexCount) := by
  rw [homogeneousBottleneck_eq] at certificate
  exact homogeneousBottleneckOfLowerBound_degreeSurplus_le_of_bounded
    (Residual := Core.Strategy.ProblemInput
          (Graph.problemWithPresentation
            (Graph.MinimumDegreeAtLeast k) BranchState
            Presentation presentation))
    (Target := fun input => Graph.HasCycleWithLength LengthOK input.object)
    (fun input => input.object)
    (fun input =>
      (Graph.Strategy.minimumDegreeThresholdQuery
        (k := k) (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)) input)
    (fun input =>
      Graph.Strategy.minimumDegreeThresholdQuery_le_minDegree input)
    LengthOK lengthDecidable (fun _ cycle => cycle) input certificate

/-- The same reading for the disjunctive wrapper registered by the A/B
frontier. -/
theorem homogeneousBottleneckOr_degreeSurplus_le_of_bounded
    {k : Nat}
    {BranchState : Graph.FiniteObject → Type}
    {Presentation : Type} {presentation : Presentation}
    (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length))
    (Rest : Core.Strategy.ProblemInput
      (Graph.problemWithPresentation
        (Graph.MinimumDegreeAtLeast k) BranchState
        Presentation presentation) → Prop)
    (input : Core.Strategy.ProblemInput
      (Graph.problemWithPresentation
        (Graph.MinimumDegreeAtLeast k) BranchState
        Presentation presentation))
    (certificate :
      (homogeneousBottleneckOr (k := k) (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          LengthOK lengthDecidable Rest).boundedLoad input ≤
        (homogeneousBottleneckOr (k := k) (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          LengthOK lengthDecidable Rest).boundedCap input) :
    input.object.degreeSurplus k ≤
      1 + Nat.sqrt (homogeneousTokenCap k * input.object.vertexCount) := by
  rw [homogeneousBottleneckOr_eq] at certificate
  exact homogeneousBottleneckOfLowerBound_degreeSurplus_le_of_bounded
    (Residual := Core.Strategy.ProblemInput
          (Graph.problemWithPresentation
            (Graph.MinimumDegreeAtLeast k) BranchState
            Presentation presentation))
    (Target := fun input =>
      Graph.HasCycleWithLength LengthOK input.object ∨ Rest input)
    (fun input => input.object)
    (fun input =>
      (Graph.Strategy.minimumDegreeThresholdQuery
        (k := k) (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)) input)
    (fun input =>
      Graph.Strategy.minimumDegreeThresholdQuery_le_minDegree input)
    LengthOK lengthDecidable (fun _ cycle => Or.inl cycle) input certificate

theorem homogeneousBottleneck_registeredSurplus_le_of_bounded
    {BranchState : Graph.FiniteObject → Type}
    {presentation : Graph.ReceiverLoad.LoadCapacityProfile}
    (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length))
    (input : Core.Strategy.ProblemInput
      (Graph.problemWithPresentation
        (Graph.MinimumDegreeAtLeast presentation.baselineDegree) BranchState
        Graph.ReceiverLoad.LoadCapacityProfile presentation))
    (certificate :
      (homogeneousBottleneck (k := presentation.baselineDegree)
          (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := presentation)
          LengthOK lengthDecidable).boundedLoad input ≤
        (homogeneousBottleneck (k := presentation.baselineDegree)
          (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := presentation)
          LengthOK lengthDecidable).boundedCap input) :
    Graph.TypeBBridgeResidual.globalSurplusOf presentation input.object
      ≤ ((1 + Nat.sqrt (homogeneousTokenCap presentation.baselineDegree *
          input.object.vertexCount) : Nat) : ℚ) := by
  have minDegree : ∀ vertex : input.object.Vertex,
      presentation.baselineDegree ≤ input.object.degree vertex := by
    intro vertex
    exact le_trans input.baseline (input.object.minDegree_le_degree vertex)
  rw [Graph.NearCubicSpine.globalSurplusOf_eq_degreeSurplus input.object
    presentation minDegree]
  exact_mod_cast homogeneousBottleneck_degreeSurplus_le_of_bounded
    LengthOK lengthDecidable input certificate

/-- Local active-surplus account derived from the current graph. -/
noncomputable def activeSurplusAccounting
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject)
    (baselineDegree : Residual → Nat) :
    Core.Strategy.BaselineDemandAccounting.Registration Residual where
  budget := countingBudget
  Site := fun residual => (object residual).Vertex
  Witness := fun residual _ => (object residual).Vertex
  family := fun residual =>
    { indices := vertices (object residual)
      fibres := neighbours (object residual) }
  Active := fun residual vertex =>
    baselineDegree residual < (object residual).degree vertex
  Supports := fun residual vertex witness =>
    (object residual).graph.Adj vertex witness ∧
      (object residual).degree witness = baselineDegree residual
  contribution := fun residual vertex _ =>
    (object residual).degree vertex - baselineDegree residual
  required := fun residual =>
    (object residual).degreeSurplus (baselineDegree residual)
  capacity := fun residual =>
    (object residual).degreeSurplus (baselineDegree residual)
  activeDecidable := fun _ _ => inferInstance
  supportsDecidable := fun _ _ _ => Classical.propDecidable _
  resourceLEDecidable := Nat.decLe

/-- CT6 high-centre audit followed by its exact CT5 surplus account. -/
noncomputable def orderedSurplusActivation
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject)
    (baselineDegree : Residual → Nat) :
    Core.Strategy.OrderedSurplusActivation.Registration Residual where
  Index := fun residual => (object residual).Vertex
  FailureData := fun _ _ => Unit
  order := fun residual => vertices (object residual)
  Failure := fun residual centre =>
    baselineDegree residual < (object residual).degree centre ∧
      ∃ endpoint, (object residual).graph.Adj centre endpoint ∧
        (object residual).degree endpoint ≠ baselineDegree residual
  failureData := fun _ _ _ => ()
  failureDecidable := fun _ _ => Classical.propDecidable _
  contribution := fun residual centre =>
    (object residual).degree centre - baselineDegree residual
  accounting := activeSurplusAccounting object baselineDegree

/-- Baseline demand derived only from the registered degree baseline and the
current residual-owned vertex schedule. -/
noncomputable def baselineDemand
    {Residual : Type u}
    (object : Residual → Graph.FiniteObject)
    (baselineDegree : Residual → Nat) :
    Core.Strategy.BaselineDemandAccounting.Registration Residual where
  budget := countingBudget
  Site := fun residual => (object residual).Vertex
  Witness := fun _ _ => Unit
  family := fun residual =>
    { indices := vertices (object residual)
      fibres := fun _ => Core.Finite.Enumeration.singleton () }
  Active := fun _ _ => True
  Supports := fun _ _ _ => True
  contribution := fun residual _ _ => baselineDegree residual
  required := fun residual =>
    baselineDegree residual * (object residual).vertexCount
  capacity := fun residual =>
    baselineDegree residual * (object residual).vertexCount
  activeDecidable := fun _ _ => isTrue trivial
  supportsDecidable := fun _ _ _ => isTrue trivial
  resourceLEDecidable := Nat.decLe

/-! ## Canonical surplus-pair accounting presentations -/

namespace CanonicalAccounting

universe v

variable {Residual : Type u}
variable (object : Residual → Graph.FiniteObject)
variable (baselineDegree : Residual → Nat)

/-- One literal unit of surplus at its residual-owned supporting vertex. -/
private abbrev ActivePort (residual : Residual) :=
  Σ vertex : (object residual).Vertex,
    Fin ((object residual).degree vertex - baselineDegree residual)

private noncomputable def activePorts (residual : Residual) :
    Core.Finite.Enumeration (ActivePort object baselineDegree residual) :=
  Core.Finite.DependentEnumeration.flatten {
    indices := vertices (object residual)
    fibres := fun _ => Core.Finite.Enumeration.ofFinEnum inferInstance
  }

/-- Stable indices into the exact active-port schedule. -/
private abbrev PortIndex (residual : Residual) :=
  Fin (activePorts object baselineDegree residual).card

private noncomputable def completePortIndices (residual : Residual) :
    Core.Finite.CompleteEnumeration
      (PortIndex object baselineDegree residual) :=
  Core.Finite.CompleteEnumeration.ofFinEnum inferInstance

/-- The unordered active-port pairs, represented by increasing indices in the
residual's exact active-port schedule. -/
private abbrev Pair (residual : Residual) :=
  { pair :
      PortIndex object baselineDegree residual ×
        PortIndex object baselineDegree residual //
      pair.1 < pair.2 }

private noncomputable def completePairs (residual : Residual) :
    Core.Finite.CompleteEnumeration (Pair object baselineDegree residual) :=
  Core.Finite.CompleteEnumeration.subtype
    ((completePortIndices object baselineDegree residual).product
      (completePortIndices object baselineDegree residual))
    (fun pair => pair.1 < pair.2)
    (fun _ => inferInstance)

private noncomputable def pairSchedule (residual : Residual) :
    Core.Finite.Enumeration (Pair object baselineDegree residual) :=
  (completePairs object baselineDegree residual).toEnumeration

private noncomputable def portAt (residual : Residual)
    (index : PortIndex object baselineDegree residual) :
    ActivePort object baselineDegree residual :=
  (activePorts object baselineDegree residual).get index

private noncomputable def portVertex (residual : Residual)
    (index : PortIndex object baselineDegree residual) :
    (object residual).Vertex :=
  (portAt object baselineDegree residual index).1

private noncomputable def leftVertex (residual : Residual)
    (pair : Pair object baselineDegree residual) :
    (object residual).Vertex :=
  portVertex object baselineDegree residual pair.1.1

private noncomputable def rightVertex (residual : Residual)
    (pair : Pair object baselineDegree residual) :
    (object residual).Vertex :=
  portVertex object baselineDegree residual pair.1.2

private noncomputable def dependent (residual : Residual)
    (pair : Pair object baselineDegree residual) : Prop :=
  (object residual).graph.Adj
    (leftVertex object baselineDegree residual pair)
    (rightVertex object baselineDegree residual pair)

private noncomputable def completeVertices (residual : Residual) :
    Core.Finite.CompleteEnumeration (object residual).Vertex :=
  Core.Finite.CompleteEnumeration.ofFinEnum (object residual).vertices

private noncomputable def completeBlockerKinds (residual : Residual) :
    Core.Finite.CompleteEnumeration
      ((object residual).Vertex × (object residual).Vertex) :=
  (completeVertices object residual).product
    (completeVertices object residual)

private noncomputable def pairRole (residual : Residual)
    (pair : Pair object baselineDegree residual) :
    Core.Strategy.CanonicalPairResponseAccounting.Role
      ((object residual).Vertex × (object residual).Vertex) := by
  letI : DecidableRel (object residual).graph.Adj :=
    (object residual).decideAdj
  exact
    if _adjacent :
        (object residual).graph.Adj
          (leftVertex object baselineDegree residual pair)
          (rightVertex object baselineDegree residual pair)
    then
      Core.Strategy.CanonicalPairResponseAccounting.Role.blocked
        (leftVertex object baselineDegree residual pair,
          rightVertex object baselineDegree residual pair)
    else
      Core.Strategy.CanonicalPairResponseAccounting.Role.freeAnchor

private theorem pairRole_freeAnchor_exact (residual : Residual)
    (pair : Pair object baselineDegree residual) :
    pairRole object baselineDegree residual pair =
        Core.Strategy.CanonicalPairResponseAccounting.Role.freeAnchor ↔
      ¬ dependent object baselineDegree residual pair := by
  unfold pairRole dependent
  letI : DecidableRel (object residual).graph.Adj :=
    (object residual).decideAdj
  by_cases adjacent :
      (object residual).graph.Adj
        (leftVertex object baselineDegree residual pair)
        (rightVertex object baselineDegree residual pair)
  · rw [dif_pos adjacent]
    change Sum.inl _ = Sum.inr () ↔ ¬ _
    constructor
    · intro impossible
      cases impossible
    · intro notAdjacent
      exact (notAdjacent adjacent).elim
  · rw [dif_neg adjacent]
    change Sum.inr () = Sum.inr () ↔ ¬ _
    constructor
    · intro _
      exact adjacent
    · intro _
      rfl

private noncomputable def canonicalBlocker (residual : Residual)
    (pair : Pair object baselineDegree residual)
    (kind : (object residual).Vertex × (object residual).Vertex) : Prop :=
  pairRole object baselineDegree residual pair =
    Core.Strategy.CanonicalPairResponseAccounting.Role.blocked kind

private theorem dependent_iff_canonicalBlocker (residual : Residual)
    (pair : Pair object baselineDegree residual) :
    dependent object baselineDegree residual pair ↔
      ∃ kind, canonicalBlocker object baselineDegree residual pair kind := by
  constructor
  · intro adjacent
    change (object residual).graph.Adj
      (leftVertex object baselineDegree residual pair)
      (rightVertex object baselineDegree residual pair) at adjacent
    refine
      ⟨(leftVertex object baselineDegree residual pair,
        rightVertex object baselineDegree residual pair), ?_⟩
    unfold canonicalBlocker pairRole
    letI : DecidableRel (object residual).graph.Adj :=
      (object residual).decideAdj
    simp [adjacent,
      Core.Strategy.CanonicalPairResponseAccounting.Role.blocked]
  · rintro ⟨kind, blocked⟩
    by_contra notDependent
    have free :=
      (pairRole_freeAnchor_exact object baselineDegree residual pair).2
        notDependent
    unfold canonicalBlocker at blocked
    rw [free] at blocked
    simp [
      Core.Strategy.CanonicalPairResponseAccounting.Role.freeAnchor,
      Core.Strategy.CanonicalPairResponseAccounting.Role.blocked] at blocked

private def unitCharge : Nat :=
  Fintype.card Unit

/-- CT15 followed by CT9 on the complete residual-owned active-port pair
schedule. -/
noncomputable def pairResponse :
    Core.Strategy.CanonicalPairResponseAccounting.Registration Residual where
  Pair := Pair object baselineDegree
  pairSchedule := pairSchedule object baselineDegree
  IntendedPair := fun _ _ => True
  pairSchedule_exact := by
    intro residual pair
    constructor
    · intro _
      trivial
    · intro _
      exact (completePairs object baselineDegree residual).complete pair
  Dependent := dependent object baselineDegree
  AdmittedDependent := dependent object baselineDegree
  dependent_exact := by
    intro _ _
    rfl
  dependentDecidable := fun residual pair =>
    (object residual).decideAdj
      (leftVertex object baselineDegree residual pair)
      (rightVertex object baselineDegree residual pair)
  pairCharge := fun _ _ => unitCharge
  pairCapacity := fun residual =>
    (pairSchedule object baselineDegree residual).card
  BlockerKind := fun residual =>
    (object residual).Vertex × (object residual).Vertex
  completeBlockerKinds := completeBlockerKinds object
  CanonicalBlocker := canonicalBlocker object baselineDegree
  blocker_exact := dependent_iff_canonicalBlocker object baselineDegree
  roleOf := pairRole object baselineDegree
  role_freeAnchor_exact :=
    pairRole_freeAnchor_exact object baselineDegree
  role_blocked_exact := by
    intro _ _ _
    rfl
  roleCapacity := fun residual _ =>
    (pairSchedule object baselineDegree residual).card

private abbrev Role (residual : Residual) :=
  Core.Strategy.CanonicalPairResponseAccounting.Role
    ((object residual).Vertex × (object residual).Vertex)

private abbrev Label (residual : Residual) :=
  Option (PortIndex object baselineDegree residual) × Role object residual

private noncomputable def completeOptionalTokens (residual : Residual) :
    Core.Finite.CompleteEnumeration
      (Option (PortIndex object baselineDegree residual)) :=
  Core.Finite.CompleteEnumeration.ofFinEnum inferInstance

private noncomputable def completeRoles (residual : Residual) :
    Core.Finite.CompleteEnumeration (Role object residual) :=
  (pairResponse object baselineDegree).completeRoles residual

private noncomputable def completeLabels (residual : Residual) :
    Core.Finite.CompleteEnumeration (Label object baselineDegree residual) :=
  (completeOptionalTokens object baselineDegree residual).product
    (completeRoles object baselineDegree residual)

private noncomputable def selectedToken (residual : Residual)
    (pair : Pair object baselineDegree residual) :
    PortIndex object baselineDegree residual :=
  pair.1.1

private noncomputable def tokenCapacity (residual : Residual)
    (token : PortIndex object baselineDegree residual) : Nat :=
  (object residual).degree
    (portVertex object baselineDegree residual token)

private noncomputable def labelCapacity (residual : Residual)
    (label : Label object baselineDegree residual) : Nat :=
  match label.1 with
  | some token => tokenCapacity object baselineDegree residual token
  | none => (pairSchedule object baselineDegree residual).card

/-- CT4, CT9, and CT14 over the same residual-owned active-port universe. -/
noncomputable def capacityToken :
    Core.Strategy.CanonicalCapacityTokenAccounting.Registration Residual where
  Demand := Pair object baselineDegree
  Token := PortIndex object baselineDegree
  Role := Role object
  Label := Label object baselineDegree
  demands := pairSchedule object baselineDegree
  tokens := fun residual =>
    (completePortIndices object baselineDegree residual).toEnumeration
  completeLabels := completeLabels object baselineDegree
  Eligible := fun residual demand token =>
    token = selectedToken object baselineDegree residual demand
  eligibleDecidable := fun _ _ _ => inferInstance
  demandWeight := fun _ _ => unitCharge
  tokenCapacity := tokenCapacity object baselineDegree
  required := fun residual =>
    (pairSchedule object baselineDegree residual).card
  roleOf := pairRole object baselineDegree
  labelOf := fun _ token role => (token, role)
  labelCapacity := labelCapacity object baselineDegree
  aggregateLabel := Role object
  aggregateLabelDecidableEq := fun residual =>
    (completeRoles object baselineDegree residual).decEq
  memberAggregateLabel := fun _ label => label.2

private noncomputable def itemLabel (residual : Residual)
    (pair : Pair object baselineDegree residual) :
    Label object baselineDegree residual :=
  (some (selectedToken object baselineDegree residual pair),
    pairRole object baselineDegree residual pair)

private noncomputable def obstructionSchedule (residual : Residual) :
    CT13.ObstructionSchedule (Role object residual) := by
  let blockers := completeBlockerKinds object residual
  letI : DecidableEq
      ((object residual).Vertex × (object residual).Vertex) :=
    blockers.decEq
  exact
    { fallbackDefault :=
        Core.Strategy.CanonicalPairResponseAccounting.Role.freeAnchor
      remaining :=
        blockers.values.map
          Core.Strategy.CanonicalPairResponseAccounting.Role.blocked
      nodup := by
        apply List.nodup_cons.mpr
        constructor
        · simp [
            Core.Strategy.CanonicalPairResponseAccounting.Role.freeAnchor,
            Core.Strategy.CanonicalPairResponseAccounting.Role.blocked]
        · exact blockers.nodup.map Sum.inl_injective
      decEq := (completeRoles object baselineDegree residual).decEq }

/-- CT9, CT13, and CT14 over exact residual-owned fibres and payer orders. -/
noncomputable def fibrePressure :
    Core.Strategy.CoupledHomogeneousFibrePressure.Registration Residual where
  Item := Pair object baselineDegree
  Token := PortIndex object baselineDegree
  Role := Role object
  Label := Label object baselineDegree
  items := pairSchedule object baselineDegree
  completeLabels := completeLabels object baselineDegree
  labelOf := itemLabel object baselineDegree
  fibreCapacity := labelCapacity object baselineDegree
  Payer := PortIndex object baselineDegree
  Obstruction := Role object
  Resource := PortIndex object baselineDegree
  payers := fun residual =>
    (completePortIndices object baselineDegree residual).toEnumeration
  obstructions := obstructionSchedule object baselineDegree
  tierTwo := fun residual _ =>
    (completePortIndices object baselineDegree residual).toEnumeration
  Eligible := fun residual payer =>
    baselineDegree residual <
      (object residual).degree
        (portVertex object baselineDegree residual payer)
  obstructionCost := fun residual _ =>
    (pairSchedule object baselineDegree residual).card
  payerResource := fun _ payer => payer
  charge := tokenCapacity object baselineDegree
  demand := fun residual =>
    (pairSchedule object baselineDegree residual).card
  eligibleDecidable := fun _ _ => inferInstance
  resourceDecidableEq := fun residual =>
    (completePortIndices object baselineDegree residual).decEq
  Member := Label object baselineDegree
  AggregateLabel := Role object
  members := fun residual =>
    (completeLabels object baselineDegree residual).toEnumeration
  memberLowerMass := labelCapacity object baselineDegree
  memberCapacity := fun residual label =>
    some (labelCapacity object baselineDegree residual label)
  memberLabel := fun _ label => some label.2
  aggregateLabelDecidableEq := fun residual =>
    (completeRoles object baselineDegree residual).decEq

/-- CT9, CT14, CT10, and CT6 over the same residual-owned finite schedules. -/
noncomputable def bottleneck :
    Core.Strategy.FiniteBottleneckClassification.Registration Residual where
  PatternItem := Pair object baselineDegree
  CoarseCode := Role object
  patternItems := pairSchedule object baselineDegree
  completeCoarseCodes := completeRoles object baselineDegree
  coarseCodeOf := pairRole object baselineDegree
  PressureLabel := Role object
  pressureCapacity := fun residual _ =>
    some (pairSchedule object baselineDegree residual).card
  pressureLabel := fun _ role => some role
  pressureLabelDecidableEq := fun residual =>
    (completeRoles object baselineDegree residual).decEq
  Datum := Pair object baselineDegree
  SemanticTag := Role object
  Promotion := Role object
  data := pairSchedule object baselineDegree
  completeSemanticTags := completeRoles object baselineDegree
  classOf := pairRole object baselineDegree
  Direct := fun _ role =>
    role =
      Core.Strategy.CanonicalPairResponseAccounting.Role.freeAnchor
  promote := fun _ role => role
  directDecidable := fun residual _ =>
    (completeRoles object baselineDegree residual).decEq _ _
  SeparatorIndex := PortIndex object baselineDegree
  SeparatorData := fun _ _ => Unit
  separatorOrder := fun residual =>
    (completePortIndices object baselineDegree residual).toEnumeration
  SeparatorFailure := fun residual token =>
    baselineDegree residual <
      (object residual).degree
        (portVertex object baselineDegree residual token)
  separatorFailureData := fun _ _ _ => ()
  separatorFailureDecidable := fun _ _ => inferInstance
  separatorContribution := fun residual token =>
    (object residual).degree
        (portVertex object baselineDegree residual token) -
      baselineDegree residual

/-! ## Graph support of a canonical pressure item -/

/-- The two-endpoint graph support carried by one canonical pressure item. -/
noncomputable def pairSupport (residual : Residual)
    (pair : Pair object baselineDegree residual) :
    Finset (object residual).Vertex := by
  letI : DecidableEq (object residual).Vertex :=
    (object residual).vertices.decEq
  exact {leftVertex object baselineDegree residual pair,
    rightVertex object baselineDegree residual pair}

/-- **Every named endpoint of a pressure item carries assigned surplus.**

An active port is `Σ vertex, Fin (d(vertex) - baseline)`, so the port schedule
can only index a vertex whose degree is strictly above the residual's own
baseline.  A pressure item names two such ports, so both vertices of its
support are surplus carriers. -/
theorem baselineDegree_lt_degree_of_mem_pairSupport (residual : Residual)
    (pair : Pair object baselineDegree residual)
    (vertex : (object residual).Vertex)
    (member : vertex ∈ pairSupport object baselineDegree residual pair) :
    baselineDegree residual < (object residual).degree vertex := by
  letI : DecidableEq (object residual).Vertex :=
    (object residual).vertices.decEq
  have port : ∀ index : PortIndex object baselineDegree residual,
      baselineDegree residual <
        (object residual).degree
          (portVertex object baselineDegree residual index) := by
    intro index
    have positive :
        0 < (object residual).degree
              (portAt object baselineDegree residual index).1 -
            baselineDegree residual :=
      Nat.lt_of_le_of_lt (Nat.zero_le _)
        (portAt object baselineDegree residual index).2.isLt
    change baselineDegree residual <
      (object residual).degree (portAt object baselineDegree residual index).1
    omega
  have decode : vertex = leftVertex object baselineDegree residual pair ∨
      vertex = rightVertex object baselineDegree residual pair := by
    have expanded : vertex ∈
        ({leftVertex object baselineDegree residual pair,
          rightVertex object baselineDegree residual pair} :
            Finset (object residual).Vertex) := member
    simpa using expanded
  rcases decode with left | right
  · subst left; exact port pair.1.1
  · subst right; exact port pair.1.2

end CanonicalAccounting

end Hypostructure.Graph.Strategy.SurplusAccounting
