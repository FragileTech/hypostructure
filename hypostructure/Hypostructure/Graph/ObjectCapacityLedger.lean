import Hypostructure.Graph.GrainedTokenBudget
import Hypostructure.Graph.CapacityTokenAssignment
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

*"every unchosen induced window overlaps a chosen one"* read on a region the
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

/-- **Node `[137]`, second production**: `lem:capacity-token-high-load` with
`cor:forced-homogeneous-same-token-scale`,
`thm:sharp-classwise-homogeneous-token-budget` (e) and
`thm:sharp-surplus-overload-audit` (d).

The statement is existential in the ledger: it says the object's *own*
capacity-token ledger realizes the high-load display, so it is not provable
without node `[136]`'s commitment that such a ledger exists.  That commitment is
read by exact key and supplied by the executor, not assumed here. -/
def FibrePressureStatement (object : FiniteObject.{u})
    (threshold order deficitScale : Nat)
    (data : CapacityPresentation.{u} object threshold order) : Prop :=
  ∃ (certified : CertifiedObjectCapacityLedger object threshold order
        deficitScale data),
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

/-- **`prop:single-graph-sparse-pressure-routing` (a), at the exact ledger.** -/
def SparsePressureCappedAt {object : FiniteObject.{u}} {threshold order deficitScale : Nat}
    {data : CapacityPresentation object threshold order}
    (certified : CertifiedObjectCapacityLedger object threshold order deficitScale data)
    (routingLabelBound : Nat) : Prop :=
  object.degreeSurplus threshold ≤
    CapacityTokenLedger.sparsePressureBound certified.ledger.entropyBudget
      (homogeneousTokenCap routingLabelBound) (object.capacityTokenSupply threshold)

/-- **Node `[137]`, overload arm**: `prop:single-graph-sparse-pressure-routing`
(b) with `cor:coupled-single-graph-overload-budget` (a)--(c) and
`cor:quantified-homogeneous-class-overload`.

Some capacity-token ledger of the object has positive coupled excess `D_all` at
the geometric caps, and some role fibre absorbs its average share over the
`Q_st|𝔗_cap|` slots, hence carries a role-homogeneous same-token matching or
star.  `class(t)` of that token is the one datum nodes `[140]`, `[142]`, `[143]`
dispatch on, and it is read off the token rather than carried beside it. -/
def OverloadAtClass (object : FiniteObject.{u}) (threshold order : Nat)
    (routingLabelBound : Nat)
    (data : CapacityPresentation.{u} object threshold order)
    (Selects : TokenClass → Prop) : Prop :=
  ∃ (ledger : ObjectCapacityLedger.{u} object threshold order data)
      (token : ledger.presented.Token) (role : Role),
      token ∈ ledger.presented.tokens ∧
        Selects (ledger.presented.tokenClass token) ∧
        (0 < ledger.presented.coupledExcess
          ledger.presented.tokenClass
          fun _ => geometricPatternBound routingLabelBound) ∧
        (ledger.presented.coupledExcess
            ledger.presented.tokenClass
            (fun _ => geometricPatternBound routingLabelBound) ≤
          sameTokenRoleBound * ledger.presented.tokens.card *
            ledger.presented.roleFibreExcess
              ledger.presented.tokenClass
              (fun _ => geometricPatternBound routingLabelBound) token role) ∧
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

/-- **Node `[137]`, overload arm**, with no class selected: the overload occurs
somewhere. -/
def SparsePressureOverloadStatement (object : FiniteObject.{u})
    (threshold order routingLabelBound : Nat)
    (data : CapacityPresentation.{u} object threshold order) : Prop :=
  OverloadAtClass object threshold order routingLabelBound data fun _ => True

/-- **Nodes `[139]` and `[141]`, the two class tests.**

`[139]` asks whether the overloading token lies in `𝔗_W` and `[141]` whether it
lies in `𝔗_R`; `class(t)` is read off the token by `tokenClass`, not carried
beside it, so a token cannot be routed to an audit of a class it is not in. -/
def SparsePressureOverloadInClass (object : FiniteObject.{u})
    (threshold order routingLabelBound : Nat)
    (data : CapacityPresentation.{u} object threshold order)
    (value : TokenClass) : Prop :=
  OverloadAtClass object threshold order routingLabelBound data fun class' =>
    class' = value

/-- The concrete overload witness selected upstream has a token outside the
given class.  This is the negative residual of the paper's class test; it is
not the stronger assertion that no overload witness exists in that class. -/
def SparsePressureOverloadOutsideClass (object : FiniteObject.{u})
    (threshold order routingLabelBound : Nat)
    (data : CapacityPresentation.{u} object threshold order)
    (value : TokenClass) : Prop :=
  OverloadAtClass object threshold order routingLabelBound data fun class' =>
    class' ≠ value

/-- **`cor:quantitative-homogeneous-overload` at the object.**

  `K_hom(G) ≥ ψ( N_*(G) / (Q_st(8n + σ(G))) )`,

cleared of division: a share the `Q_st|𝔗_cap|` slots must absorb is realized by
some role fibre, and the pattern it carries has at least `ψ` of that share many
edges.  The denominator is the manuscript's because
`lem:capacity-token-supply` bounds `|𝔗_cap|` by
`capacityTokenSupply + σ(G)`, which the ledger carries. -/
def QuantitativeOverloadStatement (object : FiniteObject.{u})
    (threshold order : Nat) : Prop :=
  ∀ (data : CapacityPresentation.{u} object threshold order)
    (ledger : ObjectCapacityLedger.{u} object threshold order data) (share : Nat),
    0 < sameTokenRoleBound * ledger.presented.tokens.card →
    share * (sameTokenRoleBound *
        (object.capacityTokenSupply threshold + object.degreeSurplus threshold)) ≤
      ledger.presented.forcedDemand →
    ∃ token ∈ ledger.presented.tokens, ∃ role : Role,
      (∃ pattern ⊆ ledger.presented.roleFibre token role,
          PatternFamily.IsMatching pattern ∧
            PatternFamily.patternThreshold share ≤ pattern.card) ∨
        (∃ centre, ∃ pattern ⊆ ledger.presented.roleFibre token role,
          PatternFamily.IsStar pattern centre ∧
            PatternFamily.patternThreshold share ≤ pattern.card)

/-- **The subbranch hypothesis of
`thm:homogeneous-overload-geometric-closure`.**

*"On the subbranch in which sparse surplus exits are absent and all decorated
Type B handoff data have been routed into the Type B fan ledger, the three fixed
homogeneous caps `L_W = L_R = L_P = L_geom` hold."*  Read at the object: no
capacity token, at any declared presentation, supports a role-homogeneous
same-token `L_geom`-matching or `L_geom`-star.  `L_geom = Q_geom + 1` is the
counted routing-label alphabet of `def:same-token-routing-germs`, so the three
caps are one number and it is derived. -/
def HomogeneousCapsHold (object : FiniteObject.{u}) (threshold order : Nat)
    (Label : Type) [Fintype Label] : Prop :=
  ∀ (data : CapacityPresentation.{u} object threshold order)
    (ledger : ObjectCapacityLedger.{u} object threshold order data),
    (∀ token ∈ ledger.presented.tokens, ∀ role : Role,
      ¬ ∃ pattern ⊆ ledger.presented.roleFibre token role,
        PatternFamily.IsMatching pattern ∧
          SameTokenRoutingGerms.patternBound Label ≤ pattern.card) ∧
    (∀ token ∈ ledger.presented.tokens, ∀ role : Role,
      ¬ ∃ centre, ∃ pattern ⊆ ledger.presented.roleFibre token role,
        PatternFamily.IsStar pattern centre ∧
          SameTokenRoutingGerms.patternBound Label ≤ pattern.card)

/-- **Node `[144]`, the bottleneck-pattern arm.**

The literal complement of the fixed homogeneous caps, normalized to the
positive pattern statement the paper routes: some certified capacity-token
ledger has a token and role supporting a role-homogeneous same-token
`L_geom`-matching or `L_geom`-star. -/
def HomogeneousBottleneckPatternStatement (object : FiniteObject.{u})
    (threshold order : Nat)
    (data : CapacityPresentation.{u} object threshold order)
    (Label : Type) [Fintype Label] : Prop :=
  ∃ (ledger : ObjectCapacityLedger.{u} object threshold order data)
      (token : ledger.presented.Token),
      token ∈ ledger.presented.tokens ∧
        ∃ role : Role,
          (∃ pattern ⊆ ledger.presented.roleFibre token role,
              PatternFamily.IsMatching pattern ∧
                SameTokenRoutingGerms.patternBound Label ≤ pattern.card) ∨
            (∃ centre, ∃ pattern ⊆ ledger.presented.roleFibre token role,
              PatternFamily.IsStar pattern centre ∧
                SameTokenRoutingGerms.patternBound Label ≤ pattern.card)

/-- **Node `[144]`, the near-cubic outcome**:
`cor:homogeneous-same-token-caps-close` at the counted `L_geom`, together with
`thm:homogeneous-overload-geometric-closure`'s edge-count half.

`M₀ = Cap_hom(L_geom)` and the token supply are both derived -- the first from
the counted routing-label alphabet, the second from
`lem:capacity-token-supply`, which the ledger carries -- so neither is a
parameter.  The fourth conjunct is `m = (3/2)n + O(√n)`, which is the surplus
bound spent against `lem:sparse-slack-surplus`'s `2m = δn + σ(G)`. -/
def HomogeneousCapsCloseStatement (object : FiniteObject.{u})
    (threshold order : Nat) (Label : Type) [Fintype Label] : Prop :=
  ∀ (data : CapacityPresentation.{u} object threshold order)
    (ledger : ObjectCapacityLedger.{u} object threshold order data),
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

/-- **`cor:quantitative-homogeneous-overload` at the object, proved.** -/
theorem quantitativeOverloadStatement (object : FiniteObject.{u})
    (threshold order : Nat) :
    QuantitativeOverloadStatement object threshold order := by
  intro data ledger share slots absorbs
  refine ledger.presented.exists_homogeneous_pattern_of_share share slots ?_
  refine le_trans (Nat.mul_le_mul_left share ?_) absorbs
  exact Nat.mul_le_mul_left _ ledger.tokens_card_le

/-- After node `[139]` records that its concrete overload token is not a window
token, that same witness lies either in the remainder or primitive class. -/
theorem overloadClassExhaustive (object : FiniteObject.{u})
    (threshold order routingLabelBound : Nat)
    (data : CapacityPresentation.{u} object threshold order)
    (notWindow : SparsePressureOverloadOutsideClass object threshold order
      routingLabelBound data .windowIncidence) :
    SparsePressureOverloadInClass object threshold order routingLabelBound data
        .remainderSurplus ∨
      SparsePressureOverloadInClass object threshold order routingLabelBound data
        .primitiveCarrier := by
  obtain ⟨ledger, token, role, tokenMem,
    outsideWindow, rest⟩ := notWindow
  cases classified : ledger.presented.tokenClass token with
  | windowIncidence =>
      exact absurd classified outsideWindow
  | remainderSurplus =>
      exact Or.inl ⟨ledger, token, role, tokenMem,
        classified, rest⟩
  | primitiveCarrier =>
      exact Or.inr ⟨ledger, token, role, tokenMem,
        classified, rest⟩

/-- **Node `[144]`, proved.**

`cor:homogeneous-same-token-caps-close` is `caps_close_at_geometricBound` at the
object's own ledger, with the token supply supplied by the ledger's own
`lem:capacity-token-supply` rather than by a parameter, and the caps discharged
by the subbranch hypothesis rather than assumed clause by clause.  The
edge-count half is that bound spent against `lem:sparse-slack-surplus`. -/
theorem homogeneousCapsCloseStatement (object : FiniteObject.{u})
    {threshold order : Nat} {Label : Type} [Fintype Label]
    (caps : HomogeneousCapsHold object threshold order Label)
    (slack : 2 * object.edgeCount =
      threshold * object.vertexCount + object.degreeSurplus threshold) :
    HomogeneousCapsCloseStatement object threshold order Label := by
  intro data ledger
  obtain ⟨noMatching, noStar⟩ := caps data ledger
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
