import Hypostructure.Graph.Statements.Parameters

/-!
# Canonical objects of the sparse-surplus capacity/pair ledger

Proof-agnostic canonical objects of the selected counterexample `G` on the
strict-surplus survivor (nodes `[134]`--`[144]`).  Fact values are data-free
(`FactSystem.value_subsingleton`), so a witness that an upstream key asserts
with `∃` cannot travel along the ledger.  Each object below is therefore a
*function of `G`*: the `Classical.choose` of exactly that upstream key's
`∃`-body at `G`.  Downstream keys that name the object speak about the same
witness the upstream fact asserted.

## Design

Every guarded object is `Option`-valued:

    if h : ∃ x, Spec data G x then some (Classical.choose h) else none

with the four lemmas `_spec` (existence gives `some x` with `Spec x`),
`_spec_of_eq_some`, and `_eq_none_iff`.  A downstream key pins the object as
`∃ x, obj = some x ∧ Q x`.  That proposition is *false*, never vacuously true,
when the upstream existence fails, and on a ledger that carries the upstream
key it is exactly `Q` at the chosen witness.  No statement is made vacuous by
the `none` default.

Dependent objects are chained: the certified ledger is chosen *at* a capacity
presentation (`canonicalCertifiedCapacityDataAt`), the overloading token and role
*at* a certified ledger, and the homogeneous pattern *at* that token and role.
The whole-object versions compose these with `canonicalCapacity`.

Every `Spec` is the literal `∃`-body of the named upstream key.  The key
statements in `Statements/SurplusPair.lean` and the library predicates of
`ObjectCapacityLedger.lean` currently spell the same bodies anonymously; the
`*_iff_exists` lemmas record the equality, and those definitions should be
refolded onto these `Spec`s when the keys are restated at the canonical
objects.

This module imports only `Statements/Parameters`; it may be imported by any
statement module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

section

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-- The capacity-presentation type at the registered data. -/
abbrev SurplusCapacity := Graph.CapacityPresentation object data.threshold data.windowOrder

/-- The certified-ledger type over a capacity presentation. -/
abbrev SurplusCertified (capacity : SurplusCapacity data object) :=
  Graph.CertifiedObjectCapacityLedger object data.threshold data.windowOrder
    data.surplusScale capacity

/-- The `L_geom` routing-label alphabet of `def:same-token-routing-germs`. -/
abbrev SurplusRoutingLabel :=
  Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
    (Graph.WindowCurvature.Label data.windowOrder)

/-! ## The capacity presentation, node `[134]`--`[136]` -/

/-- **Spec of the canonical capacity presentation** (node `[134]`--`[136]`,
`def:capacity-token-ledger`, tex ~3046): the `∃ capacity`-body of
`CapacityTokenLedgerStatement` (key `.capacityTokenLedger`, idx 114).  The
activation is the recorded blocker activation of some active family (a
proposition, so this conjunct does not re-choose data), together with every
accounting identity proved at `[136]`. -/
def CapacityLedgerSpec (capacity : SurplusCapacity data object) : Prop :=
  (∃ active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
      data.threshold,
    capacity.activation =
      Graph.recordSparsePairDEBlockers
        (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
        (LengthOK := data.LengthOK)
        (Graph.pairResponseActivation active)
        (object.portPairSchedule data.threshold)) ∧
    (object.primitiveCarrier data.threshold).card =
      object.vertexCount + 2 * object.edgeCount +
        object.degreeSurplus data.threshold ∧
    (object.primitiveCarrier data.threshold).card ≤
      object.primitiveCarrierSupply data.threshold ∧
    Graph.FiniteObject.ConcreteCapacityTokenLedgerStatement object
      data.threshold data.windowOrder capacity.activation capacity.carrier
      capacity.packing ∧
    Graph.SupportComponents.Connected.ConnectedOn object object.vertexFinset

/-- **The canonical capacity presentation `𝔗_cap` of `G`**: the witness of
node `[136]`'s `.capacityTokenLedger` (`CapacityTokenLedgerStatement`), chosen
once.  At `d2ded0e` this is the `capacity` destructured by the
`[136]`/`[137]` rows from `K .capacityTokenLedger` (through
`K .blockedPairEntropySandwich` into `roleFibrePartitionRow`). -/
noncomputable def canonicalCapacity : Option (SurplusCapacity data object) := by
  classical
  exact if h : ∃ capacity, CapacityLedgerSpec data object capacity then
    some (Classical.choose h) else none

theorem canonicalCapacity_spec
    (h : ∃ capacity, CapacityLedgerSpec data object capacity) :
    ∃ capacity, canonicalCapacity data object = some capacity ∧
      CapacityLedgerSpec data object capacity := by
  classical
  refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
  simp [canonicalCapacity, h]

theorem canonicalCapacity_spec_of_eq_some {capacity : SurplusCapacity data object}
    (selected : canonicalCapacity data object = some capacity) :
    CapacityLedgerSpec data object capacity := by
  classical
  unfold canonicalCapacity at selected
  split at selected
  · next h =>
      cases selected
      exact Classical.choose_spec h
  · cases selected

theorem canonicalCapacity_eq_none_iff :
    canonicalCapacity data object = none ↔
      ¬ ∃ capacity, CapacityLedgerSpec data object capacity := by
  classical
  unfold canonicalCapacity
  split <;> simp_all

/-! ## The certified capacity ledger, node `[137]` first production -/

/-- **Spec of the canonical certified ledger** at a capacity presentation
(node `[137]`, `lem:exact-surplus-pair-charge-partition` with
`thm:sharp-classwise-homogeneous-token-budget` (a)--(c) and
`thm:sharp-surplus-overload-audit` (b)--(c), tex ~3708): the
`∃ certified`-body of `Graph.RoleFibrePartitionStatement` (key
`.roleFibrePartition`, idx 115). -/
def CertifiedLedgerSpec (capacity : SurplusCapacity data object)
    (certified : SurplusCertified data object capacity) : Prop :=
  let ledger := certified.ledger
  ((object.degreeSurplus data.threshold).choose 2 =
      ledger.presented.free.card +
        ∑ value : Graph.SameTokenBlockerRoles.TokenClass,
          ∑ token ∈ ledger.presented.classTokens value,
            ∑ role : Graph.SameTokenBlockerRoles.Role,
              (ledger.presented.roleFibre token role).card) ∧
    (∀ token : ledger.presented.Token,
      ledger.presented.load token =
        ∑ role : Graph.SameTokenBlockerRoles.Role,
          (ledger.presented.roleFibre token role).card) ∧
    (∑ value : Graph.SameTokenBlockerRoles.TokenClass,
        ledger.presented.classLoad value =
      ledger.presented.blocked.card) ∧
    (ledger.presented.forcedDemand ≤ ledger.presented.blocked.card) ∧
    (∑ value : Graph.SameTokenBlockerRoles.TokenClass,
      (ledger.presented.classTokens value).card =
        ledger.presented.tokens.card) ∧
    (∑ value : Graph.SameTokenBlockerRoles.TokenSubtype,
        ledger.presented.subtypeLoad value =
      ledger.presented.blocked.card) ∧
    (∑ value : Graph.SameTokenBlockerRoles.TokenSubtype,
      (ledger.presented.subtypeTokens value).card =
        ledger.presented.tokens.card) ∧
    (∀ patternBound : Nat, 1 ≤ patternBound →
      ∀ value : Graph.SameTokenBlockerRoles.TokenClass,
      (∀ token ∈ ledger.presented.classTokens value,
        ∀ role : Graph.SameTokenBlockerRoles.Role,
        ¬ ∃ pattern ⊆ ledger.presented.roleFibre token role,
          Graph.PatternFamily.IsMatching pattern ∧ patternBound ≤ pattern.card) →
      (∀ token ∈ ledger.presented.classTokens value,
        ∀ role : Graph.SameTokenBlockerRoles.Role,
        ¬ ∃ centre, ∃ pattern ⊆ ledger.presented.roleFibre token role,
          Graph.PatternFamily.IsStar pattern centre ∧ patternBound ≤ pattern.card) →
      ledger.presented.classLoad value ≤
        Graph.SameTokenBlockerRoles.homogeneousCapCharge patternBound *
          (ledger.presented.classTokens value).card)

/-- The library predicate is exactly the existential over this `Spec`. -/
theorem roleFibrePartitionStatement_iff_exists
    (capacity : SurplusCapacity data object) :
    Graph.RoleFibrePartitionStatement object data.threshold data.windowOrder
        data.surplusScale capacity ↔
      ∃ certified, CertifiedLedgerSpec data object capacity certified :=
  Iff.rfl

/-- **The canonical certified capacity ledger at a presentation**: the witness
of node `[137]`'s `.roleFibrePartition` at that presentation.  At `d2ded0e`
this is the `certified` built by `roleFibrePartitionRow` and destructured by
`fibrePressureRow` and `coupledExcessDichotomy`, which therefore all spoke of
one ledger. -/
noncomputable def canonicalCertifiedCapacityDataAt (capacity : SurplusCapacity data object) :
    Option (SurplusCertified data object capacity) := by
  classical
  exact if h : ∃ certified, CertifiedLedgerSpec data object capacity certified then
    some (Classical.choose h) else none

theorem canonicalCertifiedCapacityDataAt_spec (capacity : SurplusCapacity data object)
    (h : ∃ certified, CertifiedLedgerSpec data object capacity certified) :
    ∃ certified, canonicalCertifiedCapacityDataAt data object capacity = some certified ∧
      CertifiedLedgerSpec data object capacity certified := by
  classical
  refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
  simp [canonicalCertifiedCapacityDataAt, h]

theorem canonicalCertifiedCapacityDataAt_spec_of_eq_some
    {capacity : SurplusCapacity data object}
    {certified : SurplusCertified data object capacity}
    (selected : canonicalCertifiedCapacityDataAt data object capacity = some certified) :
    CertifiedLedgerSpec data object capacity certified := by
  classical
  unfold canonicalCertifiedCapacityDataAt at selected
  split at selected
  · next h =>
      cases selected
      exact Classical.choose_spec h
  · cases selected

theorem canonicalCertifiedCapacityDataAt_eq_none_iff (capacity : SurplusCapacity data object) :
    canonicalCertifiedCapacityDataAt data object capacity = none ↔
      ¬ ∃ certified, CertifiedLedgerSpec data object capacity certified := by
  classical
  unfold canonicalCertifiedCapacityDataAt
  split <;> simp_all

/-- **The canonical certified capacity ledger of `G`**, at the canonical
capacity presentation: the pair `(𝔗_cap, certified)` both later keys read. -/
noncomputable def canonicalCertifiedCapacityData :
    Option ((capacity : SurplusCapacity data object) ×
      SurplusCertified data object capacity) :=
  (canonicalCapacity data object).bind fun capacity =>
    (canonicalCertifiedCapacityDataAt data object capacity).map fun certified =>
      ⟨capacity, certified⟩

theorem canonicalCertifiedCapacityData_eq_some_iff
    (capacity : SurplusCapacity data object)
    (certified : SurplusCertified data object capacity) :
    canonicalCertifiedCapacityData data object = some ⟨capacity, certified⟩ ↔
      canonicalCapacity data object = some capacity ∧
        canonicalCertifiedCapacityDataAt data object capacity = some certified := by
  unfold canonicalCertifiedCapacityData
  constructor
  · intro selected
    cases hc : canonicalCapacity data object with
    | none => simp [hc] at selected
    | some chosen =>
        simp only [hc, Option.bind_some] at selected
        cases hl : canonicalCertifiedCapacityDataAt data object chosen with
        | none => simp [hl] at selected
        | some ledger =>
            simp only [hl, Option.map_some, Option.some.injEq] at selected
            cases selected
            exact ⟨rfl, hl⟩
  · rintro ⟨hc, hl⟩
    simp [hc, hl]

theorem canonicalCertifiedCapacityData_spec_of_eq_some
    {capacity : SurplusCapacity data object}
    {certified : SurplusCertified data object capacity}
    (selected : canonicalCertifiedCapacityData data object = some ⟨capacity, certified⟩) :
    CapacityLedgerSpec data object capacity ∧
      CertifiedLedgerSpec data object capacity certified := by
  obtain ⟨hc, hl⟩ :=
    (canonicalCertifiedCapacityData_eq_some_iff data object capacity certified).1 selected
  exact ⟨canonicalCapacity_spec_of_eq_some data object hc,
    canonicalCertifiedCapacityDataAt_spec_of_eq_some data object hl⟩

theorem canonicalCertifiedCapacityData_spec
    (hc : ∃ capacity, CapacityLedgerSpec data object capacity)
    (hl : ∀ capacity, canonicalCapacity data object = some capacity →
      ∃ certified, CertifiedLedgerSpec data object capacity certified) :
    ∃ capacity certified,
      canonicalCertifiedCapacityData data object = some ⟨capacity, certified⟩ ∧
        CapacityLedgerSpec data object capacity ∧
        CertifiedLedgerSpec data object capacity certified := by
  obtain ⟨capacity, selected, spec⟩ := canonicalCapacity_spec data object hc
  obtain ⟨certified, chosen, certifiedSpec⟩ :=
    canonicalCertifiedCapacityDataAt_spec data object capacity (hl capacity selected)
  exact ⟨capacity, certified,
    (canonicalCertifiedCapacityData_eq_some_iff data object capacity certified).2
      ⟨selected, chosen⟩, spec, certifiedSpec⟩

theorem canonicalCertifiedCapacityData_eq_none_iff :
    canonicalCertifiedCapacityData data object = none ↔
      ∀ capacity, canonicalCapacity data object = some capacity →
        canonicalCertifiedCapacityDataAt data object capacity = none := by
  unfold canonicalCertifiedCapacityData
  cases hc : canonicalCapacity data object with
  | none => simp
  | some chosen => simp

/-! ## The overloading token and role, node `[137]` overload arm -/

/-- **Spec of the canonical overloading token and role** at a certified ledger
(node `[137]` overload arm, `prop:single-graph-sparse-pressure-routing` (b)
with `cor:coupled-single-graph-overload-budget` and
`cor:quantified-homogeneous-class-overload`, tex ~4361--4545): the
`∃ token role`-body of `Graph.OverloadAtClass` with no class selected, i.e. of
`Graph.SparsePressureOverloadStatement` (key `.sparsePressureOverload`,
idx 128). -/
def OverloadTokenSpec {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity)
    (token : certified.ledger.presented.Token)
    (role : Graph.SameTokenBlockerRoles.Role) : Prop :=
  let ledger := certified.ledger
  token ∈ ledger.presented.tokens ∧
    (0 < ledger.presented.coupledExcess ledger.presented.tokenClass
      fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
        data.routingLabelBound) ∧
    (ledger.presented.coupledExcess ledger.presented.tokenClass
        (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
          data.routingLabelBound) ≤
      Graph.SameTokenBlockerRoles.sameTokenRoleBound * ledger.presented.tokens.card *
        ledger.presented.roleFibreExcess ledger.presented.tokenClass
          (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
            data.routingLabelBound) token role) ∧
    ((∃ pattern ⊆ ledger.presented.roleFibre token role,
        Graph.PatternFamily.IsMatching pattern ∧
          Graph.PatternFamily.patternThreshold
              (ledger.presented.roleFibre token role).card ≤ pattern.card) ∨
      (∃ centre, ∃ pattern ⊆ ledger.presented.roleFibre token role,
        Graph.PatternFamily.IsStar pattern centre ∧
          Graph.PatternFamily.patternThreshold
              (ledger.presented.roleFibre token role).card ≤ pattern.card))

/-- The node-`[137]` overload predicate at a certified ledger is exactly the
existential over this `Spec` (with the class selector `fun _ => True`). -/
theorem overloadAtClass_true_iff_exists (capacity : SurplusCapacity data object) :
    Graph.SparsePressureOverloadStatement object data.threshold data.windowOrder
        data.surplusScale data.routingLabelBound capacity ↔
      ∃ certified : SurplusCertified data object capacity,
        ∃ token role, OverloadTokenSpec data object certified token role := by
  unfold Graph.SparsePressureOverloadStatement Graph.OverloadAtClass
  constructor
  · rintro ⟨certified, token, role, mem, -, rest⟩
    exact ⟨certified, token, role, mem, rest⟩
  · rintro ⟨certified, token, role, mem, rest⟩
    exact ⟨certified, token, role, mem, trivial, rest⟩

/-- **The canonical overloading token and role at a certified ledger**: the
token `t` and role `r` of node `[137]`'s overload witness.  At `d2ded0e` this
is the `(token, role)` produced by `coupledExcessDichotomy` from
`exists_overloaded_roleFibre` on the `fibrePressure` ledger, and read (with
the same ledger) by `windowOverloadClassDichotomy` ([139]),
`remainderOverloadClassDichotomy` ([141]) and
`homogeneousBottleneckAuditRow` ([140]/[142]/[143]). -/
noncomputable def canonicalOverloadTokenAt {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity) :
    Option (certified.ledger.presented.Token × Graph.SameTokenBlockerRoles.Role) := by
  classical
  exact if h : ∃ choice : certified.ledger.presented.Token ×
        Graph.SameTokenBlockerRoles.Role,
      OverloadTokenSpec data object certified choice.1 choice.2 then
    some (Classical.choose h) else none

theorem canonicalOverloadTokenAt_spec {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity)
    (h : ∃ token role, OverloadTokenSpec data object certified token role) :
    ∃ token role, canonicalOverloadTokenAt data object certified = some (token, role) ∧
      OverloadTokenSpec data object certified token role := by
  classical
  have h' : ∃ choice : certified.ledger.presented.Token ×
      Graph.SameTokenBlockerRoles.Role,
      OverloadTokenSpec data object certified choice.1 choice.2 := by
    obtain ⟨token, role, spec⟩ := h
    exact ⟨(token, role), spec⟩
  refine ⟨(Classical.choose h').1, (Classical.choose h').2, ?_,
    Classical.choose_spec h'⟩
  simp [canonicalOverloadTokenAt, h']

theorem canonicalOverloadTokenAt_spec_of_eq_some
    {capacity : SurplusCapacity data object}
    {certified : SurplusCertified data object capacity}
    {token : certified.ledger.presented.Token}
    {role : Graph.SameTokenBlockerRoles.Role}
    (selected : canonicalOverloadTokenAt data object certified = some (token, role)) :
    OverloadTokenSpec data object certified token role := by
  classical
  unfold canonicalOverloadTokenAt at selected
  split at selected
  · next h =>
      have spec := Classical.choose_spec h
      rw [Option.some.injEq] at selected
      rw [selected] at spec
      exact spec
  · cases selected

theorem canonicalOverloadTokenAt_eq_none_iff {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity) :
    canonicalOverloadTokenAt data object certified = none ↔
      ¬ ∃ token role, OverloadTokenSpec data object certified token role := by
  classical
  unfold canonicalOverloadTokenAt
  split
  · next h =>
      simp only [reduceCtorEq, false_iff, not_not]
      obtain ⟨choice, spec⟩ := h
      exact ⟨choice.1, choice.2, spec⟩
  · next h =>
      simp only [true_iff]
      rintro ⟨token, role, spec⟩
      exact h ⟨(token, role), spec⟩

/-- **The canonical class witness** of nodes `[139]`/`[141]`: `class(t)` of
the canonical overloading token, read off the token (fig. Part X; the class
tests route to `[140]`, `[142]`, `[143]`).  At `d2ded0e` the two class
decisions case-split `ledger.presented.tokenClass token` of the `[137]`
witness; this is that value. -/
noncomputable def canonicalOverloadClassAt {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity) :
    Option Graph.SameTokenBlockerRoles.TokenClass :=
  (canonicalOverloadTokenAt data object certified).map fun choice =>
    certified.ledger.presented.tokenClass choice.1

theorem canonicalOverloadClassAt_eq_some_iff {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity)
    (value : Graph.SameTokenBlockerRoles.TokenClass) :
    canonicalOverloadClassAt data object certified = some value ↔
      ∃ token role, canonicalOverloadTokenAt data object certified = some (token, role) ∧
        certified.ledger.presented.tokenClass token = value := by
  unfold canonicalOverloadClassAt
  cases h : canonicalOverloadTokenAt data object certified with
  | none => simp
  | some choice =>
      obtain ⟨token, role⟩ := choice
      simp

/-! ## The homogeneous bottleneck pattern, nodes `[140]`/`[142]`/`[143]` -/

/-- The declared same-root connector clause of the geometric audit at one
pattern edge set: every edge has its selected response support and every
endpoint demand a routing configuration from the token's canonical root
(`def:same-token-routing-germs`). -/
def PatternConfigured {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity)
    (token : certified.ledger.presented.Token)
    (pattern : Finset (Finset (object.Vertex × object.Vertex))) : Prop :=
  ∀ pair ∈ pattern,
    ∃ responseSupport : Finset object.Vertex,
      capacity.activation.pairSupport pair = some responseSupport ∧
        ∀ demand ∈ pair,
          ∃ configuration :
              Graph.SameTokenRoutingGerms.RoutingConfiguration
                object (capacity.sameTokenRoutingSupport token pair)
                  (Graph.CapacityPresentation.tokenSupport token)
                  (capacity.activation.localBuffer demand),
            configuration.path.head? = some (Graph.CapacityPresentation.tokenRoot token) ∧
              configuration.path.getLast? = some demand.2

/-- **Spec of the canonical homogeneous pattern** at the overloading token and
role (nodes `[140]`/`[142]`/`[143]`, `lem:same-token-bottleneck-routing`
input, tex ~5565): the pattern `∃`-body of
`Graph.HomogeneousBottleneckPatternStatement` (key
`.homogeneousBottleneckPattern`, idx 141) — a role-homogeneous same-token
matching or star of `L_geom` edges inside the role fibre `H_{t,r}`, with its
declared same-root connector configurations.  The paper's
"matching ∨ star" disjunction is kept inside the `Spec` so the pattern itself
is the single chosen object. -/
def HomogeneousPatternSpec {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity)
    (token : certified.ledger.presented.Token)
    (role : Graph.SameTokenBlockerRoles.Role)
    (pattern : Finset (Finset (object.Vertex × object.Vertex))) : Prop :=
  pattern ⊆ certified.ledger.presented.roleFibre token role ∧
    (Graph.PatternFamily.IsMatching pattern ∨
      ∃ centre, Graph.PatternFamily.IsStar pattern centre) ∧
    Graph.SameTokenRoutingGerms.patternBound (SurplusRoutingLabel data) ≤
      pattern.card ∧
    PatternConfigured data object certified token pattern

/-- **The canonical homogeneous bottleneck pattern** at a token and role: the
matching or star the geometric audit publishes and node `[144]` routes.  At
`d2ded0e` this is the pattern `homogeneousBottleneckAuditRow` builds at the
`[137]` overload witness's `(token, role)` and seals in
`.homogeneousBottleneckPattern`, which `lem:same-token-bottleneck-routing`
destructures. -/
noncomputable def canonicalHomogeneousPatternAt {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity)
    (token : certified.ledger.presented.Token)
    (role : Graph.SameTokenBlockerRoles.Role) :
    Option (Finset (Finset (object.Vertex × object.Vertex))) := by
  classical
  exact if h : ∃ pattern, HomogeneousPatternSpec data object certified token role pattern then
    some (Classical.choose h) else none

theorem canonicalHomogeneousPatternAt_spec {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity)
    (token : certified.ledger.presented.Token)
    (role : Graph.SameTokenBlockerRoles.Role)
    (h : ∃ pattern, HomogeneousPatternSpec data object certified token role pattern) :
    ∃ pattern, canonicalHomogeneousPatternAt data object certified token role = some pattern ∧
      HomogeneousPatternSpec data object certified token role pattern := by
  classical
  refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
  simp [canonicalHomogeneousPatternAt, h]

theorem canonicalHomogeneousPatternAt_spec_of_eq_some
    {capacity : SurplusCapacity data object}
    {certified : SurplusCertified data object capacity}
    {token : certified.ledger.presented.Token}
    {role : Graph.SameTokenBlockerRoles.Role}
    {pattern : Finset (Finset (object.Vertex × object.Vertex))}
    (selected : canonicalHomogeneousPatternAt data object certified token role =
      some pattern) :
    HomogeneousPatternSpec data object certified token role pattern := by
  classical
  unfold canonicalHomogeneousPatternAt at selected
  split at selected
  · next h =>
      cases selected
      exact Classical.choose_spec h
  · cases selected

theorem canonicalHomogeneousPatternAt_eq_none_iff {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity)
    (token : certified.ledger.presented.Token)
    (role : Graph.SameTokenBlockerRoles.Role) :
    canonicalHomogeneousPatternAt data object certified token role = none ↔
      ¬ ∃ pattern, HomogeneousPatternSpec data object certified token role pattern := by
  classical
  unfold canonicalHomogeneousPatternAt
  split <;> simp_all

/-- The configured pattern disjunction of `HomogeneousBottleneckPatternStatement`
is exactly the existential over `HomogeneousPatternSpec`. -/
theorem homogeneousPatternDisjunction_iff_exists
    {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity)
    (token : certified.ledger.presented.Token)
    (role : Graph.SameTokenBlockerRoles.Role) :
    ((∃ pattern ⊆ certified.ledger.presented.roleFibre token role,
        Graph.PatternFamily.IsMatching pattern ∧
          Graph.SameTokenRoutingGerms.patternBound (SurplusRoutingLabel data) ≤
            pattern.card ∧
          PatternConfigured data object certified token pattern) ∨
      (∃ centre, ∃ pattern ⊆ certified.ledger.presented.roleFibre token role,
        Graph.PatternFamily.IsStar pattern centre ∧
          Graph.SameTokenRoutingGerms.patternBound (SurplusRoutingLabel data) ≤
            pattern.card ∧
          PatternConfigured data object certified token pattern)) ↔
      ∃ pattern, HomogeneousPatternSpec data object certified token role pattern := by
  constructor
  · rintro (⟨pattern, sub, matching, bound, configured⟩ |
      ⟨centre, pattern, sub, star, bound, configured⟩)
    · exact ⟨pattern, sub, Or.inl matching, bound, configured⟩
    · exact ⟨pattern, sub, Or.inr ⟨centre, star⟩, bound, configured⟩
  · rintro ⟨pattern, sub, matching | ⟨centre, star⟩, bound, configured⟩
    · exact Or.inl ⟨pattern, sub, matching, bound, configured⟩
    · exact Or.inr ⟨centre, pattern, sub, star, bound, configured⟩

/-! ## Whole-object compositions -/

/-- The canonical overloading token and role of `G`, at the canonical
certified ledger. -/
noncomputable def canonicalOverload :
    Option ((ledger : (capacity : SurplusCapacity data object) ×
        SurplusCertified data object capacity) ×
      (ledger.2.ledger.presented.Token × Graph.SameTokenBlockerRoles.Role)) :=
  (canonicalCertifiedCapacityData data object).bind fun ledger =>
    (canonicalOverloadTokenAt data object ledger.2).map fun choice => ⟨ledger, choice⟩

/-- The canonical class witness of `G` (`class(t)` of the canonical overload). -/
noncomputable def canonicalOverloadClass :
    Option Graph.SameTokenBlockerRoles.TokenClass :=
  (canonicalOverload data object).map fun overload =>
    overload.1.2.ledger.presented.tokenClass overload.2.1

/-- The canonical homogeneous bottleneck pattern of `G`, at the canonical
overload. -/
noncomputable def canonicalHomogeneousPattern :
    Option (Finset (Finset (object.Vertex × object.Vertex))) :=
  (canonicalOverload data object).bind fun overload =>
    canonicalHomogeneousPatternAt data object overload.1.2 overload.2.1 overload.2.2

end

end Hypostructure.Graph.Strategy.Spine
