import Hypostructure.Graph.GrainedTokenBudget
import Hypostructure.Graph.CapacityTokenAssignment
import Hypostructure.Graph.SameTokenRoutingGerms
import Hypostructure.Graph.SparsePairResponse
import Hypostructure.Graph.WindowTargetPackage
import Hypostructure.Graph.NetCharge

/-!
# The capacity-token ledger of an object, and the statements read off it

`Graph/CapacityTokenLedger.lean` presents a capacity-token ledger over an
abstract demand family.  This module fixes the presentation node `[136]` builds
for one object: the token universe `𝔗_cap`, the assignment `Θ_cap`,
`lem:capacity-token-supply`'s `|𝔗_cap| ≤ (3(δ−1)+2)n + σ(G)`, and the free-side
entropy sandwich.  Bundling them is what lets nodes `[137]`--`[144]` speak about
the canonical capacity ledger of the object.

Nothing here is a free parameter of a ledger.  `def:capacity-token-ledger` builds
its token universe and its charge from three declared data -- a valid packing of
induced windows, `def:active-surplus-demands`' activation, and
`def:declared-coordinate-signature`'s coordinate and shoulder-chord presentation.
Those are the `CapacityPresentation` a ledger is indexed by; the token universe,
the declared token order, `sub(t)`, the eligibility and
`def:same-token-blocker-roles`' role reading are *derived* from them.  A
ledger therefore cannot present a token universe that is not the object's own
`𝔗_cap`, and node `[136]` commits the one presentation it actually constructs.

`ObjectCapacityLedger` carries no hypothesis that is not one of
`def:capacity-token-ledger`, `lem:capacity-token-supply` and
`prop:sparse-entropy-sandwich-with-blockers`.  The pair schedule and its count
are not fields either: the schedule is the object's own `portPairSchedule`, and
its count is node `[130]`'s committed `|Π(𝒜₀)| = C(σ(G),2)`.

`L_geom` enters as `def:same-token-routing-germs`' routing-label count `Q_geom`,
which is what `SameTokenBlockerRoles.geometricPatternBound` takes: no numeral is
written, and a caller passing anything other than a routing-label count is not
computing `L_geom`.
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.SameTokenBlockerRoles

universe u v

/-- **`def:capacity-token-ledger`'s declared data at one object.**

A valid packing of induced windows of the registered order and the concrete
demand activation of `def:active-surplus-demands`.  The coordinate support and
shoulder-chord projections read by `def:capacity-token-ledger` are derived from
that activation; there is no second presentation which could disagree with the
ledger fact.  These are exactly the data from which
`def:capacity-token-ledger` constructs `𝔗_cap`, `Θ_cap`, and `ρ_t`. -/
structure CapacityPresentation (object : FiniteObject.{u}) (threshold order : Nat) where
  /-- `def:active-surplus-demands`' concrete activation, whose blockers
  `Θ_cap` charges.  Its coordinate and chord alphabets are the paper's declared
  pair coordinates and selected shoulder chords. -/
  activation : FiniteObject.DemandActivation object object.PairCoordinate
    (object.Vertex × object.Vertex)
  /-- Every declared canonical blocker has the primitive carrier prescribed by
  `def:primitive-sparse-blocker-carrier`.  This is well-formedness of the
  presentation, not a graph hypothesis; it makes the fourth charge clause
  total on the blocked side. -/
  carrierComplete : ∀ pair ∈ object.portPairSchedule threshold,
      ∀ blocker ∈ activation.blockers pair,
        (FiniteObject.Blocker.carrier object threshold
          (by
            letI := object.vertices.decEq
            exact DeclaredSignature.Coordinate.support)
          activation.chordPort blocker).isSome
  /-- The packing of induced windows the two halves of `𝔗_W` are built from. -/
  packing : Finset (Finset object.Vertex)
  /-- The packing is one: its members are induced windows and they are pairwise
  vertex-disjoint. -/
  packingValid : object.IsWindowPacking order packing
  /-- **It is `𝒫`, the maximal packing.**  `def:window-remainder-surplus-split`
  fixes `W = ⋃_{P ∈ 𝒫} V(P)` at a packing attaining `p₁₃`, so the packing the
  token ledger is built on is not any valid one -- and node `[19]`'s prefix
  already carries exactly this in its `maximalPacking` entry, which is why it is
  a clause here rather than a quantifier. -/
  packingMaximal : packing.card = object.windowPackingNumber order

namespace CapacityPresentation

variable {object : FiniteObject.{u}} {threshold order : Nat}

/-- The primitive support carried by a capacity token.  This is a derived view
of `𝔗_cap`, not an additional presentation field. -/
noncomputable def tokenSupport
    (token : FiniteObject.CapacityToken object) : Finset object.Vertex := by
  letI := object.vertices.decEq
  exact match token with
    | .boundaryWindow incidence => {incidence.1, incidence.2}
    | .crossWindow incidence => {incidence.1, incidence.2}
    | .remainder unit => {unit.1}
    | .primitive (.inl vertex) => {vertex}
    | .primitive (.inr (.inl incidence)) => {incidence.1, incidence.2}
    | .primitive (.inr (.inr port)) => {port.1, port.2}

/-- The canonical initial vertex of the primitive token support.  In the
shoulder-chord case the port endpoint is used, exactly the endpoint contained
in that port's selected support. -/
def tokenRoot (token : FiniteObject.CapacityToken object) : object.Vertex :=
  match token with
  | .boundaryWindow incidence => incidence.1
  | .crossWindow incidence => incidence.1
  | .remainder unit => unit.1
  | .primitive (.inl vertex) => vertex
  | .primitive (.inr (.inl incidence)) => incidence.1
  | .primitive (.inr (.inr port)) => port.2

theorem tokenRoot_mem_tokenSupport
    (token : FiniteObject.CapacityToken object) :
    tokenRoot token ∈ tokenSupport token := by
  rcases token with incidence | incidence | unit | item
  · simp [tokenRoot, tokenSupport]
  · simp [tokenRoot, tokenSupport]
  · simp [tokenRoot, tokenSupport]
  · rcases item with vertex | item
    · simp [tokenRoot, tokenSupport]
    · rcases item with incidence | port <;> simp [tokenRoot, tokenSupport]

/-- The carrier presentation is a derived view of the activation already
recorded in the ledger.  In particular, its chord endpoints and port projection
cannot be supplied through a parallel data channel. -/
noncomputable def carrier (data : CapacityPresentation object threshold order) :
    FiniteObject.CarrierPresentation object object.PairCoordinate
      (object.Vertex × object.Vertex) where
  coordinateSupport := by
    letI := object.vertices.decEq
    exact DeclaredSignature.Coordinate.support
  chordEnds := data.activation.chordEnds
  chordPort := data.activation.chordPort

/-- The already-declared connector core `X_π ∪ ⋃_{p∈π} R_p`.  Both
parts are derived from the activation, so this definition carries no new data. -/
noncomputable def pairConnectorSupport
    (data : CapacityPresentation object threshold order)
    (pair : Finset (object.Vertex × object.Vertex)) : Finset object.Vertex := by
  letI := object.vertices.decEq
  exact (data.activation.pairSupport pair).getD ∅ ∪
    pair.biUnion data.activation.returnSupport

/-- The declared support of a same-token connector at one unordered pair.

The first five terms are precisely the token carrier, canonical blocker,
selected supports `T`, canonical returns `R`, and response supports `Γ` of
`def:same-token-routing-germs`.  The final term is `X_π`, the support of the
already declared sparse pair-response coordinate generated by those same
`T`/`Γ` entries.  It records the connector closure already present in the
declared signature; no path or support is selected here. -/
noncomputable def sameTokenRoutingSupport
    (data : CapacityPresentation object threshold order)
    (token : FiniteObject.CapacityToken object)
    (pair : Finset (object.Vertex × object.Vertex)) : Finset object.Vertex := by
  letI := object.vertices.decEq
  exact tokenSupport token ∪
    (FiniteObject.chargeSupport data.activation data.carrier pair ∪
      (pair.biUnion data.activation.localBuffer ∪
        (pair.biUnion data.activation.responseSupport ∪
          data.pairConnectorSupport pair)))

/-- Every unchosen induced window overlaps the actual maximal packing.  This is
derived from the two packing fields; it is not extra presentation data. -/
theorem packingMeets (data : CapacityPresentation object threshold order)
    (orderPos : 0 < order) (support : Finset object.Vertex)
    (window : object.InducesWindow order support) :
    ∃ member ∈ data.packing, ¬ Disjoint support member :=
  object.exists_mem_not_disjoint_of_card_eq orderPos data.packingValid
    data.packingMaximal window

/-- `ρ_t(π)=(type(B_π),sub(Θ_cap(π)))`, derived from the actual charge. -/
noncomputable def role (data : CapacityPresentation object threshold order) :
    Finset (object.Vertex × object.Vertex) → Role :=
  FiniteObject.capacityRole data.activation data.carrier threshold data.packing

/-- **The remainder of `𝒫` is window-free.**

*"Every unchosen induced window meets the packing."* read on a region the
packing misses: any sub-support of it inducing a window would have to meet a
packed window, and it cannot.  This is `def:window-remainder-surplus-split`'s
own maximality spent, and it is where the `P₁₃`-free core the decorated Type B
handoff asks for comes from. -/
theorem inducedPathFree_of_disjoint {object : FiniteObject.{u}} {order : Nat}
    {threshold : Nat} (data : CapacityPresentation object threshold order)
    (orderPos : 0 < order)
    {region : Finset object.Vertex}
    (misses : ∀ member ∈ data.packing, Disjoint region member) :
    Graph.InducedPathFree (object.induce region) order := by
  refine object.inducedPathFree_induce_of_forall ?_
  intro inner inside window
  obtain ⟨member, memberMem, meets⟩ := data.packingMeets orderPos inner window
  exact meets ((misses member memberMem).mono_left inside)

/-- **`𝔗_cap`**, the object's own capacity-token universe at this packing. -/
noncomputable def tokens (data : CapacityPresentation object threshold order) :
    Finset (FiniteObject.CapacityToken object) :=
  object.capacityTokens threshold data.packing

/-- The declared token order whose first applicable label is `Θ_cap`. -/
noncomputable def tokenOrder (data : CapacityPresentation object threshold order) :
    List (FiniteObject.CapacityToken object) :=
  FiniteObject.capacityTokenOrder object threshold data.packing

/-- **`Θ_cap`** read as the ledger's eligibility relation. -/
noncomputable def Eligible (data : CapacityPresentation object threshold order) :
    FiniteObject.CapacityToken object →
      Finset (object.Vertex × object.Vertex) → Prop :=
  FiniteObject.Charges data.activation data.carrier threshold data.packing

noncomputable instance eligibleDecidable
    (data : CapacityPresentation object threshold order)
    (token : FiniteObject.CapacityToken object)
    (pair : Finset (object.Vertex × object.Vertex)) :
    Decidable (data.Eligible token pair) :=
  FiniteObject.decidableCharges data.activation data.carrier threshold
    data.packing token pair

theorem tokenOrder_toFinset (data : CapacityPresentation object threshold order) :
    data.tokenOrder.toFinset = data.tokens :=
  FiniteObject.capacityTokenOrder_toFinset threshold data.packing

/-- The capacity ledger's uncharged side is contained in the canonical
blocker-free side.  Totality of the primitive carrier is exactly what rules out
a blocked pair falling through the fourth charge clause. -/
theorem freeSide_subset_activationFree
    (data : CapacityPresentation object threshold order) :
    freeSide object.vertexPairDecidableEq (object.portPairSchedule threshold)
        data.tokenOrder data.Eligible data.eligibleDecidable ⊆
      data.activation.freePairs threshold := by
  classical
  letI := object.vertexPairDecidableEq
  intro pair free
  have freeParts := Finset.mem_filter.mp free
  have chargeNone :
      ¬ (FiniteObject.capacityCharge data.activation data.carrier threshold
        data.packing pair).isSome := by
    have labelNone := Option.not_isSome_iff_eq_none.mp freeParts.2
    change CanonicalFibreLedger.canonicalLabel
        (FiniteObject.capacityTokenOrder object threshold data.packing)
        (FiniteObject.Charges data.activation data.carrier threshold data.packing)
        pair = none at labelNone
    rw [FiniteObject.canonicalLabel_eq_capacityCharge data.activation
      data.carrier threshold data.packing] at labelNone
    simpa [labelNone]
  rw [FiniteObject.DemandActivation.freePairs, FiniteObject.freePairs,
    CanonicalFibreLedger.unassigned, Finset.mem_filter]
  refine ⟨freeParts.1, ?_⟩
  intro blockerLabel
  obtain ⟨kind, selected⟩ := Option.isSome_iff_exists.mp blockerLabel
  obtain ⟨kind, blocks⟩ : ∃ kind, data.activation.Blocks kind pair :=
    ⟨kind, CanonicalFibreLedger.applies_canonicalLabel selected⟩
  have blocked : (data.activation.blockers pair).Nonempty :=
    (data.activation.exists_blocks_iff_blockers_nonempty pair).mp ⟨kind, blocks⟩
  exact chargeNone (FiniteObject.isSome_capacityCharge data.activation data.carrier
        threshold data.packing blocked (data.carrierComplete pair freeParts.1))

end CapacityPresentation

/-- **`def:capacity-token-ledger` at one object and one declared presentation,
with its supply and its sandwich.**

`orderNonempty` is `𝔗_cap ≠ ∅`, which is what makes the declared token order an
order at all; `sandwich` is `prop:sparse-entropy-sandwich-with-blockers` on the
free side of this very charge; `supply` is `lem:capacity-token-supply`.  The
token universe, the charge and `sub(t)` are the presentation's own, so none of
them is a field. -/
structure ObjectCapacityLedger (object : FiniteObject.{u}) (threshold order : Nat)
    (data : CapacityPresentation object threshold order) where
  /-- Node `[130]`'s committed `|Π(𝒜₀)| = C(σ(G),2)`: the charge is levied on
  the object's own pair schedule, so its count is part of the commitment. -/
  scheduleCard : (object.portPairSchedule threshold).card =
    (object.degreeSurplus threshold).choose 2
  /-- `𝔗_cap ≠ ∅`. -/
  orderNonempty : data.tokens.Nonempty
  /-- `E_spine(n) + ((1/2)σ(G)+1)log₂ n`, or any budget the free side fits in. -/
  entropyBudget : Nat
  /-- `prop:sparse-entropy-sandwich-with-blockers` at this charge. -/
  sandwich :
    (freeSide object.vertexPairDecidableEq (object.portPairSchedule threshold)
      data.tokenOrder data.Eligible data.eligibleDecidable).card ≤ entropyBudget
  /-- **`lem:capacity-token-supply`**: `|𝔗_cap| ≤ (3(δ−1)+2)n + σ(G)`, the
  manuscript's `≤ 8n + σ(G)` at its own `δ = 3`. -/
  supply :
    data.tokens.card ≤
      object.capacityTokenSupply threshold + object.degreeSurplus threshold

namespace ObjectCapacityLedger

variable {object : FiniteObject.{u}} {threshold order : Nat}
  {data : CapacityPresentation object threshold order}

/-- The abstract ledger this presentation is, charged at the object's own pair
schedule with node `[130]`'s committed count. -/
noncomputable def presented (ledger : ObjectCapacityLedger object threshold order data) :
    CapacityTokenLedger.{u} (object.degreeSurplus threshold) :=
  CapacityTokenLedger.ofPortSchedule object threshold (object.degreeSurplus threshold)
    ledger.scheduleCard (FiniteObject.CapacityToken.decidableEq object)
    data.tokenOrder
    (by rw [data.tokenOrder_toFinset]; exact ledger.orderNonempty)
    FiniteObject.CapacityToken.subtype
    data.Eligible data.eligibleDecidable data.role ledger.entropyBudget ledger.sandwich

theorem tokens_eq (ledger : ObjectCapacityLedger object threshold order data) :
    ledger.presented.tokens = data.tokens :=
  data.tokenOrder_toFinset

/-- `lem:capacity-token-supply` in the form the closure step spends: the token
supply is linear in `n` above the active family. -/
theorem tokens_card_le (ledger : ObjectCapacityLedger object threshold order data) :
    ledger.presented.tokens.card ≤
      object.capacityTokenSupply threshold + object.degreeSurplus threshold := by
  rw [ledger.tokens_eq]
  exact ledger.supply

/-- **The object's capacity-token ledger at a declared presentation, built.**

Nothing is selected: the token universe, the declared token order, `sub(t)` and
the eligibility are the presentation's own.  The entropy budget and its bound
are the concrete linear sandwich produced by the mixed spine/free-pair package;
the constructor therefore cannot manufacture a reflexive free-side budget. -/
noncomputable def ofCapacityCharge
    (data : CapacityPresentation object threshold order)
    (scheduleCard : (object.portPairSchedule threshold).card =
      (object.degreeSurplus threshold).choose 2)
    (orderNonempty : data.tokens.Nonempty)
    (entropyBudget : Nat)
    (sandwich :
      (freeSide object.vertexPairDecidableEq (object.portPairSchedule threshold)
        data.tokenOrder data.Eligible data.eligibleDecidable).card ≤ entropyBudget)
    (supply : data.tokens.card ≤
      object.capacityTokenSupply threshold + object.degreeSurplus threshold) :
    ObjectCapacityLedger object threshold order data where
  scheduleCard := scheduleCard
  orderNonempty := orderNonempty
  entropyBudget := entropyBudget
  sandwich := sandwich
  supply := supply

end ObjectCapacityLedger

/-- Node `[136]`'s concrete ledger together with the node-`[129]` deficit and
node-`[131]` mixed-sandwich data from which its entropy budget was built. -/
structure CertifiedObjectCapacityLedger (object : FiniteObject.{u})
    (threshold order deficitScale : Nat)
    (data : CapacityPresentation object threshold order) where
  ledger : ObjectCapacityLedger object threshold order data
  spineDeficit : Nat
  edgeSlack : Nat
  entropyBudget_eq : ledger.entropyBudget =
    spineDeficit + (Nat.log2 object.vertexCount + 1) * edgeSlack
  spineDeficit_le : spineDeficit ≤ deficitScale * object.vertexCount
  edgeSlack_le : edgeSlack ≤ object.degreeSurplus threshold

namespace CertifiedObjectCapacityLedger

variable {object : FiniteObject.{u}} {threshold order deficitScale : Nat}
  {data : CapacityPresentation object threshold order}

/-- The certified node-`[129]`/`[131]` ledger turns the fixed-cap pressure
estimate into the paper's exact square-root bound. -/
theorem degreeSurplus_le_mul_ceilSqrt
    (certified : CertifiedObjectCapacityLedger object threshold order
      deficitScale data)
    (sizePos : 0 < object.vertexCount) (cap : Nat)
    (safety : TokenLoad.quadraticSafetyScale ≤
      2 * (1 + 2 * cap) +
        (2 * deficitScale + 2 * cap * (3 * (threshold - 1) + 2)))
    (pressure : object.degreeSurplus threshold ≤
      1 + 2 * cap + Nat.sqrt (2 * certified.ledger.entropyBudget +
        2 * (cap * object.capacityTokenSupply threshold))) :
    object.degreeSurplus threshold ≤
      (2 * (1 + 2 * cap) +
        (2 * deficitScale +
          2 * cap * (3 * (threshold - 1) + 2))) *
        Core.ceilSqrt object.vertexCount := by
  apply TokenLoad.demand_le_mul_ceilSqrt object.vertexCount
    (object.degreeSurplus threshold) certified.spineDeficit certified.edgeSlack
    cap deficitScale (3 * (threshold - 1) + 2)
  · exact sizePos
  · exact certified.spineDeficit_le
  · exact certified.edgeSlack_le
  · rw [certified.entropyBudget_eq] at pressure
    have supply_eq : object.capacityTokenSupply threshold =
        (3 * (threshold - 1) + 2) * object.vertexCount := by
      simp only [FiniteObject.capacityTokenSupply,
        FiniteObject.primitiveCarrierSupply]
      ring
    rw [supply_eq] at pressure
    convert pressure using 1 <;> ring
  · exact le_rfl
  · exact safety

end CertifiedObjectCapacityLedger

/-! ## The statements nodes `[137]`--`[143]` commit -/

/-- **Node `[137]`, first production**: the exact surplus-pair partition and
the classwise/subtype accounting identities, at the single certified capacity
ledger constructed from the incoming `[136]` presentation and the accepted
free-side entropy count. -/
def RoleFibrePartitionStatement (object : FiniteObject.{u})
    (threshold order deficitScale : Nat)
    (data : CapacityPresentation.{u} object threshold order) : Prop :=
  ∃ (certified : CertifiedObjectCapacityLedger object threshold order
        deficitScale data),
    let ledger := certified.ledger
    -- `lem:exact-surplus-pair-charge-partition`.
    ((object.degreeSurplus threshold).choose 2 =
        ledger.presented.free.card +
          ∑ value : TokenClass,
            ∑ token ∈ ledger.presented.classTokens value,
              ∑ role : Role,
                (ledger.presented.roleFibre token role).card) ∧
      -- The role fibres partition each token fibre.
      (∀ token : ledger.presented.Token,
        ledger.presented.load token =
          ∑ role : Role,
            (ledger.presented.roleFibre token role).card) ∧
      -- `thm:sharp-classwise-homogeneous-token-budget` (a)--(b).
      (∑ value : TokenClass, ledger.presented.classLoad value =
        ledger.presented.blocked.card) ∧
      (ledger.presented.forcedDemand ≤ ledger.presented.blocked.card) ∧
      (∑ value : TokenClass,
        (ledger.presented.classTokens value).card =
          ledger.presented.tokens.card) ∧
      -- `thm:sharp-surplus-overload-audit` (b)--(c).
      (∑ value : TokenSubtype, ledger.presented.subtypeLoad value =
        ledger.presented.blocked.card) ∧
      (∑ value : TokenSubtype,
        (ledger.presented.subtypeTokens value).card =
          ledger.presented.tokens.card) ∧
      -- `thm:sharp-classwise-homogeneous-token-budget` (c).
      (∀ patternBound : Nat, 1 ≤ patternBound → ∀ value : TokenClass,
        (∀ token ∈ ledger.presented.classTokens value, ∀ role : Role,
          ¬ ∃ pattern ⊆ ledger.presented.roleFibre token role,
            PatternFamily.IsMatching pattern ∧ patternBound ≤ pattern.card) →
        (∀ token ∈ ledger.presented.classTokens value, ∀ role : Role,
          ¬ ∃ centre, ∃ pattern ⊆ ledger.presented.roleFibre token role,
            PatternFamily.IsStar pattern centre ∧ patternBound ≤ pattern.card) →
        ledger.presented.classLoad value ≤
          homogeneousCapCharge patternBound *
            (ledger.presented.classTokens value).card)

/-- **Node `[137]`, second production, at one certified ledger**:
`lem:capacity-token-high-load` with `cor:forced-homogeneous-same-token-scale`,
`thm:sharp-classwise-homogeneous-token-budget` (e) and
`thm:sharp-surplus-overload-audit` (d).  Some token and role of the ledger
realize the coupled high-load display, carry at least a `Q_st`-th of the load
and the forced demand up to the token supply, and contain a matching or a star
of `ψ` of the fibre count. -/
def FibrePressureAt {object : FiniteObject.{u}} {threshold order deficitScale : Nat}
    {data : CapacityPresentation.{u} object threshold order}
    (certified : CertifiedObjectCapacityLedger object threshold order
      deficitScale data) : Prop :=
  let ledger := certified.ledger
  ∃ (token : ledger.presented.Token) (role : Role),
    token ∈ ledger.presented.tokens ∧
    -- `lem:capacity-token-high-load`
    ((object.degreeSurplus threshold).choose 2 ≤
      ledger.entropyBudget +
        ledger.presented.tokens.card *
          ledger.presented.load token) ∧
    -- `cor:forced-homogeneous-same-token-scale`
    (ledger.presented.load token ≤
      sameTokenRoleBound *
        (ledger.presented.roleFibre token role).card) ∧
    -- `thm:sharp-classwise-homogeneous-token-budget` (e) and
    -- `thm:sharp-surplus-overload-audit` (d)
    (ledger.presented.forcedDemand ≤
      sameTokenRoleBound * ledger.presented.tokens.card *
        (ledger.presented.roleFibre token role).card) ∧
    ((∃ pattern ⊆ ledger.presented.roleFibre token role,
        PatternFamily.IsMatching pattern ∧
          PatternFamily.patternThreshold
              (ledger.presented.roleFibre token role).card ≤
            pattern.card) ∨
      (∃ centre, ∃ pattern ⊆ ledger.presented.roleFibre token role,
        PatternFamily.IsStar pattern centre ∧
          PatternFamily.patternThreshold
              (ledger.presented.roleFibre token role).card ≤
            pattern.card))

/-- `lem:capacity-token-high-load` at a certified ledger, proved. -/
theorem fibrePressureAt {object : FiniteObject.{u}}
    {threshold order deficitScale : Nat}
    {data : CapacityPresentation.{u} object threshold order}
    (certified : CertifiedObjectCapacityLedger object threshold order
      deficitScale data) :
    FibrePressureAt certified := by
  obtain ⟨token, tokenMem, role, display, roleBound, forced, pattern⟩ :=
    certified.ledger.presented.exists_forced_pattern
  exact ⟨token, role, tokenMem, display, roleBound, forced, pattern⟩

/-- **`prop:single-graph-sparse-pressure-routing` (a), at the exact ledger.** -/
def SparsePressureCappedAt {object : FiniteObject.{u}} {threshold order deficitScale : Nat}
    {data : CapacityPresentation object threshold order}
    (certified : CertifiedObjectCapacityLedger object threshold order deficitScale data)
    (routingLabelBound : Nat) : Prop :=
  object.degreeSurplus threshold ≤
    CapacityTokenLedger.sparsePressureBound certified.ledger.entropyBudget
      (homogeneousTokenCap routingLabelBound) (object.capacityTokenSupply threshold)

/-- **The fixed homogeneous caps `L_W = L_R = L_P = L_geom` at one ledger**
(the subbranch hypothesis of `thm:homogeneous-overload-geometric-closure`): no
token of the ledger supports a role-homogeneous same-token `L_geom`-matching or
`L_geom`-star.  `L_geom = Q_geom + 1` is the counted routing-label alphabet of
`def:same-token-routing-germs`. -/
def HomogeneousCapsHoldAt {object : FiniteObject.{u}} {threshold order : Nat}
    {data : CapacityPresentation.{u} object threshold order}
    (ledger : ObjectCapacityLedger.{u} object threshold order data)
    (Label : Type) [Fintype Label] : Prop :=
  (∀ token ∈ ledger.presented.tokens, ∀ role : Role,
    ¬ ∃ pattern ⊆ ledger.presented.roleFibre token role,
      PatternFamily.IsMatching pattern ∧
        SameTokenRoutingGerms.patternBound Label ≤ pattern.card) ∧
  (∀ token ∈ ledger.presented.tokens, ∀ role : Role,
    ¬ ∃ centre, ∃ pattern ⊆ ledger.presented.roleFibre token role,
      PatternFamily.IsStar pattern centre ∧
        SameTokenRoutingGerms.patternBound Label ≤ pattern.card)

/-- **`cor:homogeneous-same-token-caps-close` at one ledger**, at the counted
`L_geom`, with `thm:homogeneous-overload-geometric-closure`'s edge-count half.
`M₀ = Cap_hom(L_geom)` and the token supply are both derived, so neither is a
parameter.  The fourth conjunct is `m = (3/2)n + O(√n)`. -/
def HomogeneousCapsCloseAt {object : FiniteObject.{u}} {threshold order : Nat}
    {data : CapacityPresentation.{u} object threshold order}
    (ledger : ObjectCapacityLedger.{u} object threshold order data)
    (Label : Type) [Fintype Label] : Prop :=
  (∀ token ∈ ledger.presented.tokens,
    ledger.presented.load token ≤
      homogeneousCapCharge (SameTokenRoutingGerms.patternBound Label)) ∧
  (ledger.presented.blocked.card ≤
    homogeneousCapCharge (SameTokenRoutingGerms.patternBound Label) * ledger.presented.tokens.card) ∧
  (object.degreeSurplus threshold ≤
    1 + 2 * homogeneousCapCharge (SameTokenRoutingGerms.patternBound Label) +
      Nat.sqrt (2 * ledger.entropyBudget +
        2 * (homogeneousCapCharge (SameTokenRoutingGerms.patternBound Label) *
          object.capacityTokenSupply threshold))) ∧
  (2 * object.edgeCount ≤
    threshold * object.vertexCount +
      (1 + 2 * homogeneousCapCharge (SameTokenRoutingGerms.patternBound Label) +
        Nat.sqrt (2 * ledger.entropyBudget +
          2 * (homogeneousCapCharge (SameTokenRoutingGerms.patternBound Label) *
            object.capacityTokenSupply threshold))))

/-! ## The statements, proved -/

/-- **`cor:homogeneous-same-token-caps-close` at one ledger, proved.**

It is `caps_close_at_geometricBound` at that ledger, with the token supply
supplied by the ledger's own `lem:capacity-token-supply` and the caps
discharged by the subbranch hypothesis at the same ledger.  The edge-count half
is that bound spent against `lem:sparse-slack-surplus`. -/
theorem homogeneousCapsCloseAt {object : FiniteObject.{u}}
    {threshold order : Nat} {Label : Type} [Fintype Label]
    {data : CapacityPresentation.{u} object threshold order}
    (ledger : ObjectCapacityLedger.{u} object threshold order data)
    (caps : HomogeneousCapsHoldAt ledger Label)
    (slack : 2 * object.edgeCount =
      threshold * object.vertexCount + object.degreeSurplus threshold) :
    HomogeneousCapsCloseAt ledger Label := by
  obtain ⟨noMatching, noStar⟩ := caps
  obtain ⟨loads, blocked, surplus⟩ :=
    ledger.presented.caps_close_at_geometricBound Label
      (object.capacityTokenSupply threshold) ledger.tokens_card_le noMatching
      noStar
  refine ⟨loads, blocked, surplus, ?_⟩
  rw [slack]
  exact Nat.add_le_add_left surplus _

/-- **`cor:spine-lower-bound-surplus-estimates` at the object**: each lower-bound
package that bounds the pair count of the active family bounds the surplus. -/
theorem surplus_le_of_package (object : FiniteObject.{u}) (threshold : Nat) :
    ∀ package : Nat,
      (object.degreeSurplus threshold).choose 2 ≤ package →
      object.degreeSurplus threshold ≤ 1 + Nat.sqrt (2 * package) :=
  fun package budget =>
    TokenLoad.demand_le_of_package (object.degreeSurplus threshold) package budget

end Hypostructure.Graph
