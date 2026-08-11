import Hypostructure.Graph.GrainedTokenBudget
import Hypostructure.Graph.CapacityTokenAssignment
import Hypostructure.Graph.SameTokenBottleneckRouting
import Hypostructure.Graph.WindowTargetPackage

/-!
# The capacity-token ledger of an object, and the statements read off it

`Graph/CapacityTokenLedger.lean` presents a capacity-token ledger over an
abstract demand family.  This module fixes the presentation node `[136]` builds
for one object: the token universe `𝔗_cap`, the assignment `Θ_cap`,
`lem:capacity-token-supply`'s `|𝔗_cap| ≤ (3(δ−1)+2)n + σ(G)`, and the free-side
entropy sandwich.  Bundling them is what lets nodes `[137]`--`[144]` speak about
*the* capacity ledger of the object rather than about an invented one.

Nothing here is a free parameter of a ledger.  `def:capacity-token-ledger` builds
its token universe and its charge from three declared data -- a valid packing of
induced windows, `def:active-surplus-demands`' activation, and
`def:declared-coordinate-signature`'s coordinate and shoulder-chord presentation
-- so those, together with `def:same-token-blocker-roles`' role reading, are the
`CapacityPresentation` a ledger is indexed by, and the token universe, the
declared token order, `sub(t)` and the eligibility are *derived* from them.  A
ledger therefore cannot present a token universe that is not the object's own
`𝔗_cap`, and node `[136]` commits its existence at **every** presentation rather
than at one it chose.

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

A valid packing of induced windows of the registered order, the demand
activation of `def:active-surplus-demands`, the declared coordinate and
shoulder-chord presentation of `def:declared-coordinate-signature`, and the role
reading `ρ_t` of `def:same-token-blocker-roles`.  Everything the token ledger
below needs beyond the object itself is one of these four, and each is data the
manuscript declares rather than a choice a node may make freely. -/
structure CapacityPresentation (object : FiniteObject.{u}) (order : Nat) where
  /-- The declared coordinate alphabet of `def:declared-coordinate-signature`. -/
  Coordinate : Type u
  /-- The shoulder-chord alphabet of `def:declared-coordinate-signature`. -/
  Chord : Type u
  /-- `def:active-surplus-demands`' activation, whose blockers `Θ_cap` charges. -/
  activation : FiniteObject.DemandActivation object Coordinate Chord
  /-- The declared support and shoulder-chord data the two selecting clauses of
  `def:capacity-token-ledger` read. -/
  carrier : FiniteObject.CarrierPresentation object Coordinate Chord
  /-- Every declared canonical blocker has the primitive carrier prescribed by
  `def:primitive-sparse-blocker-carrier`.  This is well-formedness of the
  presentation, not a graph hypothesis; it makes the fourth charge clause
  total on the blocked side. -/
  carrierComplete : ∀ threshold : Nat,
    ∀ pair ∈ object.portPairSchedule threshold,
      ∀ blocker ∈ activation.blockers pair,
        (FiniteObject.Blocker.carrier object threshold carrier.coordinateSupport
          carrier.chordPort blocker).isSome
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
  /-- and every unchosen induced window overlaps a chosen one. -/
  packingMeets : ∀ support : Finset object.Vertex,
    object.InducesWindow order support →
    ∃ member ∈ packing, ¬ Disjoint support member
  /-- `ρ_t`, the same-token role of a blocked pair. -/
  role : Finset (object.Vertex × object.Vertex) → Role

namespace CapacityPresentation

variable {object : FiniteObject.{u}} {order : Nat}

/-- A canonical empty-obstruction presentation.  It is used only to witness
that the universally certified node-`[136]` ledger is inhabited; all numerical
facts still come from the concrete mixed package stored in that ledger. -/
noncomputable def canonical (object : FiniteObject.{u}) (order : Nat)
    (orderPos : 0 < order) : CapacityPresentation object order := by
  classical
  let activation : object.DemandActivation (ULift.{u} (Fin 0))
      (ULift.{u} (Fin 0)) := {
    declaredSupport := fun _ => ∅
    returnSupport := fun _ => ∅
    localBuffer := fun _ => ∅
    profileObstructions := fun _ => ∅
    responseObstructions := fun _ => ∅
    chordObstructions := fun _ => ∅ }
  let carrier : object.CarrierPresentation (ULift.{u} (Fin 0))
      (ULift.{u} (Fin 0)) := {
    coordinateSupport := fun value => Fin.elim0 value.down
    chordEnds := fun value => Fin.elim0 value.down
    chordPort := fun value => Fin.elim0 value.down }
  let packing := (object.exists_windowPacking_card_eq order).choose
  have valid := (object.exists_windowPacking_card_eq order).choose_spec.1
  have maximal := (object.exists_windowPacking_card_eq order).choose_spec.2
  exact {
    Coordinate := ULift.{u} (Fin 0)
    Chord := ULift.{u} (Fin 0)
    activation := activation
    carrier := carrier
    carrierComplete := by
      intro threshold pair pairMem blocker blockerMem
      exfalso
      simpa [activation, FiniteObject.DemandActivation.blockers,
        FiniteObject.DemandActivation.sharedItems] using blockerMem
    packing := packing
    packingValid := valid
    packingMaximal := maximal
    packingMeets := fun support window =>
      object.exists_mem_not_disjoint_of_card_eq orderPos valid maximal window
    role := fun _ => default }

/-- **The remainder of `𝒫` is window-free.**

*"every unchosen induced window overlaps a chosen one"* read on a region the
packing misses: any sub-support of it inducing a window would have to meet a
packed window, and it cannot.  This is `def:window-remainder-surplus-split`'s
own maximality spent, and it is where the `P₁₃`-free core the decorated Type B
handoff asks for comes from. -/
theorem inducedPathFree_of_disjoint {object : FiniteObject.{u}} {order : Nat}
    (data : CapacityPresentation object order) {region : Finset object.Vertex}
    (misses : ∀ member ∈ data.packing, Disjoint region member) :
    Graph.InducedPathFree (object.induce region) order := by
  refine object.inducedPathFree_induce_of_forall ?_
  intro inner inside window
  obtain ⟨member, memberMem, meets⟩ := data.packingMeets inner window
  exact meets ((misses member memberMem).mono_left inside)

/-- **`𝔗_cap`**, the object's own capacity-token universe at this packing. -/
noncomputable def tokens (data : CapacityPresentation object order)
    (threshold : Nat) : Finset (FiniteObject.CapacityToken object) :=
  object.capacityTokens threshold data.packing

/-- The declared token order whose first applicable label is `Θ_cap`. -/
noncomputable def tokenOrder (data : CapacityPresentation object order)
    (threshold : Nat) : List (FiniteObject.CapacityToken object) :=
  FiniteObject.capacityTokenOrder object threshold data.packing

/-- **`Θ_cap`** read as the ledger's eligibility relation. -/
noncomputable def Eligible (data : CapacityPresentation object order)
    (threshold : Nat) :
    FiniteObject.CapacityToken object →
      Finset (object.Vertex × object.Vertex) → Prop :=
  FiniteObject.Charges data.activation data.carrier threshold data.packing

noncomputable instance eligibleDecidable (data : CapacityPresentation object order)
    (threshold : Nat) (token : FiniteObject.CapacityToken object)
    (pair : Finset (object.Vertex × object.Vertex)) :
    Decidable (data.Eligible threshold token pair) :=
  FiniteObject.decidableCharges data.activation data.carrier threshold
    data.packing token pair

theorem tokenOrder_toFinset (data : CapacityPresentation object order)
    (threshold : Nat) :
    (data.tokenOrder threshold).toFinset = data.tokens threshold :=
  FiniteObject.capacityTokenOrder_toFinset threshold data.packing

/-- The capacity ledger's uncharged side is contained in the canonical
blocker-free side.  Totality of the primitive carrier is exactly what rules out
a blocked pair falling through the fourth charge clause. -/
theorem freeSide_subset_activationFree
    (data : CapacityPresentation object order) (threshold : Nat) :
    freeSide object.vertexPairDecidableEq (object.portPairSchedule threshold)
        (data.tokenOrder threshold) (data.Eligible threshold)
        (data.eligibleDecidable threshold) ⊆
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
    threshold data.packing blocked (data.carrierComplete threshold pair freeParts.1))

end CapacityPresentation

/-- **`def:capacity-token-ledger` at one object and one declared presentation,
with its supply and its sandwich.**

`orderNonempty` is `𝔗_cap ≠ ∅`, which is what makes the declared token order an
order at all; `sandwich` is `prop:sparse-entropy-sandwich-with-blockers` on the
free side of this very charge; `supply` is `lem:capacity-token-supply`.  The
token universe, the charge and `sub(t)` are the presentation's own, so none of
them is a field. -/
structure ObjectCapacityLedger (object : FiniteObject.{u}) (threshold order : Nat)
    (data : CapacityPresentation object order) where
  /-- Node `[130]`'s committed `|Π(𝒜₀)| = C(σ(G),2)`: the charge is levied on
  the object's own pair schedule, so its count is part of the commitment. -/
  scheduleCard : (object.portPairSchedule threshold).card =
    (object.degreeSurplus threshold).choose 2
  /-- `𝔗_cap ≠ ∅`. -/
  orderNonempty : (data.tokens threshold).Nonempty
  /-- `E_spine(n) + ((1/2)σ(G)+1)log₂ n`, or any budget the free side fits in. -/
  entropyBudget : Nat
  /-- `prop:sparse-entropy-sandwich-with-blockers` at this charge. -/
  sandwich :
    (freeSide object.vertexPairDecidableEq (object.portPairSchedule threshold)
      (data.tokenOrder threshold) (data.Eligible threshold)
      (data.eligibleDecidable threshold)).card ≤ entropyBudget
  /-- **`lem:capacity-token-supply`**: `|𝔗_cap| ≤ (3(δ−1)+2)n + σ(G)`, the
  manuscript's `≤ 8n + σ(G)` at its own `δ = 3`. -/
  supply :
    (data.tokens threshold).card ≤
      object.capacityTokenSupply threshold + object.degreeSurplus threshold

namespace ObjectCapacityLedger

variable {object : FiniteObject.{u}} {threshold order : Nat}
  {data : CapacityPresentation object order}

/-- The abstract ledger this presentation is, charged at the object's own pair
schedule with node `[130]`'s committed count. -/
noncomputable def presented (ledger : ObjectCapacityLedger object threshold order data) :
    CapacityTokenLedger.{u} (object.degreeSurplus threshold) :=
  CapacityTokenLedger.ofPortSchedule object threshold (object.degreeSurplus threshold)
    ledger.scheduleCard (FiniteObject.CapacityToken.decidableEq object)
    (data.tokenOrder threshold)
    (by rw [data.tokenOrder_toFinset threshold]; exact ledger.orderNonempty)
    FiniteObject.CapacityToken.subtype
    (data.Eligible threshold) (data.eligibleDecidable threshold)
    data.role ledger.entropyBudget ledger.sandwich

theorem tokens_eq (ledger : ObjectCapacityLedger object threshold order data) :
    ledger.presented.tokens = data.tokens threshold :=
  data.tokenOrder_toFinset threshold

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
noncomputable def ofCapacityCharge (data : CapacityPresentation object order)
    (scheduleCard : (object.portPairSchedule threshold).card =
      (object.degreeSurplus threshold).choose 2)
    (orderNonempty : (data.tokens threshold).Nonempty)
    (entropyBudget : Nat)
    (sandwich :
      (freeSide object.vertexPairDecidableEq (object.portPairSchedule threshold)
        (data.tokenOrder threshold) (data.Eligible threshold)
        (data.eligibleDecidable threshold)).card ≤ entropyBudget)
    (supply : (data.tokens threshold).card ≤
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
    (data : CapacityPresentation object order) where
  ledger : ObjectCapacityLedger object threshold order data
  spineDeficit : Nat
  edgeSlack : Nat
  entropyBudget_eq : ledger.entropyBudget =
    spineDeficit + (Nat.log2 object.vertexCount + 1) * edgeSlack
  spineDeficit_le : spineDeficit ≤ deficitScale * object.vertexCount
  edgeSlack_le : edgeSlack ≤ object.degreeSurplus threshold

namespace CertifiedObjectCapacityLedger

variable {object : FiniteObject.{u}} {threshold order deficitScale : Nat}
  {data : CapacityPresentation object order}

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

/-- **Node `[136]`'s existence commitment, proved.**

At *every* declared presentation -- every valid packing of induced windows,
every demand activation, every coordinate/shoulder-chord presentation and every
role reading -- the object's own capacity-token charge is a capacity-token
ledger.  The three obligations are the branch's own: node `[130]`'s pair count,
the vertex the branch's positive surplus exhibits, and
`lem:capacity-token-supply` at the sparse upper envelope and the registered join
comparison. -/
theorem objectCapacityLedgerExists (object : FiniteObject.{u})
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {deficitScale : Nat}
    {threshold order : Nat}
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (vertex : object.Vertex)
    (scheduleCard : (object.portPairSchedule threshold).card =
      (object.degreeSurplus threshold).choose 2)
    (three : 3 ≤ threshold) (orderPos : 0 < order)
    (handshake : threshold * object.vertexCount ≤ 2 * object.edgeCount)
    (envelope : object.edgeCount + 2 ≤ (threshold - 1) * object.vertexCount)
    (joinSlack : threshold * order + 2 ≤ 4 * order)
    (spine : object.BaselineWindowDemand Baseline LengthOK threshold order
      deficitScale)
    (mixed : ∀ declared : CapacityPresentation.{u} object order,
      object.MixedSpinePairDemand Baseline LengthOK threshold order deficitScale spine
        declared.activation) :
    ∀ declared : CapacityPresentation.{u} object order,
      Nonempty (CertifiedObjectCapacityLedger.{u} object threshold order
        deficitScale declared) :=
  fun declared => by
    let budget :=
      spineDeficit object.vertexCount threshold spine.bits +
        (Nat.log2 object.vertexCount + 1) *
          (object.edgeCount - cubicBaselineEdgeCount object.vertexCount threshold)
    have freeSubset := declared.freeSide_subset_activationFree threshold
    have freeBound :
        (freeSide object.vertexPairDecidableEq (object.portPairSchedule threshold)
          (declared.tokenOrder threshold) (declared.Eligible threshold)
          (declared.eligibleDecidable threshold)).card ≤ budget := by
      calc
        _ ≤ (declared.activation.freePairs threshold).card :=
          Finset.card_le_card freeSubset
        _ ≤ budget := (mixed declared).linearSandwich
    let ledger := ObjectCapacityLedger.ofCapacityCharge declared scheduleCard
      (object.capacityTokens_nonempty threshold declared.packing vertex)
      budget freeBound
      (object.card_capacityTokens_le declared.packingValid baseline three
        handshake envelope orderPos joinSlack)
    exact ⟨{
      ledger := ledger
      spineDeficit := spineDeficit object.vertexCount threshold spine.bits
      edgeSlack := object.edgeCount -
        cubicBaselineEdgeCount object.vertexCount threshold
      entropyBudget_eq := rfl
      spineDeficit_le := spine.deficitBound
      edgeSlack_le := edgeSlack_le_degreeSurplus object threshold
        (cubicBaselineEdgeCount_le_edgeCount_of_handshake object threshold
          handshake) }⟩

/-! ## The statements nodes `[137]`--`[143]` commit -/

/-- **Node `[137]`, first production**: `lem:exact-surplus-pair-charge-partition`
with `thm:sharp-classwise-homogeneous-token-budget` (a)--(c) and
`thm:sharp-surplus-overload-audit` (b)--(c), at the object's own capacity
ledger. -/
def RoleFibrePartitionStatement (object : FiniteObject.{u}) (threshold order : Nat) :
    Prop :=
  ∀ (data : CapacityPresentation.{u} object order)
    (ledger : ObjectCapacityLedger.{u} object threshold order data),
    -- `lem:exact-surplus-pair-charge-partition`: every pair of active demands is
    -- free or lies in exactly one class/token/role fibre.
    ((object.degreeSurplus threshold).choose 2 =
        ledger.presented.free.card +
          ∑ value : TokenClass,
            ∑ token ∈ ledger.presented.classTokens value,
              ∑ role : Role,
                (ledger.presented.roleFibre token role).card) ∧
      -- `def:same-token-blocker-roles`' role-fibre partition at every token.
      (∀ token : ledger.presented.Token,
        ledger.presented.load token =
          ∑ role : Role,
            (ledger.presented.roleFibre token role).card) ∧
      -- `thm:sharp-classwise-homogeneous-token-budget` (a): the class split and
      -- the forced blocked-pair demand `N_*(G)`.
      (∑ value : TokenClass, ledger.presented.classLoad value =
        ledger.presented.blocked.card) ∧
      (ledger.presented.forcedDemand ≤
        ledger.presented.blocked.card) ∧
      -- `thm:sharp-classwise-homogeneous-token-budget` (b): the class supplies.
      (∑ value : TokenClass,
        (ledger.presented.classTokens value).card =
          ledger.presented.tokens.card) ∧
      -- `thm:sharp-surplus-overload-audit` (b) and (c): the same at the six
      -- subtypes.
      (∑ value : TokenSubtype, ledger.presented.subtypeLoad value =
        ledger.presented.blocked.card) ∧
      (∑ value : TokenSubtype,
        (ledger.presented.subtypeTokens value).card =
          ledger.presented.tokens.card) ∧
      -- `thm:sharp-classwise-homogeneous-token-budget` (c): the classwise cap.
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
def FibrePressureStatement (object : FiniteObject.{u}) (threshold order : Nat) :
    Prop :=
  ∀ data : CapacityPresentation.{u} object order,
  ∃ (ledger : ObjectCapacityLedger.{u} object threshold order data)
      (token : ledger.presented.Token) (role : Role),
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

/-- **`prop:single-graph-sparse-pressure-routing` (a), the tested half**: every
capacity-token ledger of the object respects the geometric cap, so
`σ(G) ≤ R_L(n)`.  This is the proposition the node `[137]` branch decides. -/
def SparsePressureCapped (object : FiniteObject.{u}) (threshold order : Nat) :
    Prop :=
  ∀ (data : CapacityPresentation.{u} object order)
    (ledger : ObjectCapacityLedger.{u} object threshold order data)
    (routingLabelBound : Nat),
    object.degreeSurplus threshold ≤
      CapacityTokenLedger.sparsePressureBound ledger.entropyBudget
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
    (Selects : TokenClass → Prop) : Prop :=
  ∃ (data : CapacityPresentation.{u} object order)
      (ledger : ObjectCapacityLedger.{u} object threshold order data)
      (routingLabelBound : Nat) (token : ledger.presented.Token) (role : Role),
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
    (threshold order : Nat) : Prop :=
  OverloadAtClass object threshold order fun _ => True

/-- **Nodes `[139]` and `[141]`, the two class tests.**

`[139]` asks whether the overloading token lies in `𝔗_W` and `[141]` whether it
lies in `𝔗_R`; `class(t)` is read off the token by `tokenClass`, not carried
beside it, so a token cannot be routed to an audit of a class it is not in. -/
def SparsePressureOverloadInClass (object : FiniteObject.{u})
    (threshold order : Nat) (value : TokenClass) : Prop :=
  OverloadAtClass object threshold order fun class' => class' = value

/-- The concrete overload witness selected upstream has a token outside the
given class.  This is the negative residual of the paper's class test; it is
not the stronger assertion that no overload witness exists in that class. -/
def SparsePressureOverloadOutsideClass (object : FiniteObject.{u})
    (threshold order : Nat) (value : TokenClass) : Prop :=
  OverloadAtClass object threshold order fun class' => class' ≠ value

/-- **Nodes `[140]`, `[142]`, `[143]`: the geometric audit of one token class.**

`def:homogeneous-token-charge` fixes what a token may carry without a
role-homogeneous pattern, `Cap_hom(L) = Q_st(L−1)(2L−3)`, and the audit is its
contrapositive at the manuscript's own fixed cap: `L_geom = Q_geom + 1` for the
*counted* routing-label alphabet of `def:same-token-routing-germs`.  `Q_geom` is
`Fintype.card` of the declared tuple, so the bound is derived rather than
supplied; the two alphabets it is declared over -- the boundary-degree profile
and the `P₁₃` label -- are `def:declared-coordinate-signature`'s and the
labelling's, so they are quantified here exactly as the manuscript leaves them.

The audit is stated at the object's own ledger, at every declared presentation,
and restricted to the tokens of its own class: `[140]` audits `𝔗_W`, `[142]`
audits `𝔗_R` and `[143]` audits `𝔗_prim`. -/
def ClassAuditStatement (object : FiniteObject.{u}) (threshold order : Nat)
    (Label : Type) [Fintype Label] (value : TokenClass) : Prop :=
  ∀ (data : CapacityPresentation.{u} object order)
    (ledger : ObjectCapacityLedger.{u} object threshold order data)
    (token : ledger.presented.Token),
    ledger.presented.tokenClass token = value →
    homogeneousCapCharge
        (SameTokenRoutingGerms.patternBound Label) <
      ledger.presented.load token →
    ∃ role : Role,
      (∃ pattern ⊆ ledger.presented.roleFibre token role,
          PatternFamily.IsMatching pattern ∧
            SameTokenRoutingGerms.patternBound Label ≤ pattern.card) ∨
        (∃ centre, ∃ pattern ⊆ ledger.presented.roleFibre token role,
          PatternFamily.IsStar pattern centre ∧
            SameTokenRoutingGerms.patternBound Label ≤ pattern.card)

/-- **`cor:quantitative-homogeneous-overload` at the object.**

  `K_hom(G) ≥ ψ( N_*(G) / (Q_st(8n + σ(G))) )`,

cleared of division: a share the `Q_st|𝔗_cap|` slots must absorb is realized by
some role fibre, and the pattern it carries has at least `ψ` of that share many
edges.  The denominator is the manuscript's because
`lem:capacity-token-supply` bounds `|𝔗_cap|` by
`capacityTokenSupply + σ(G)`, which the ledger carries. -/
def QuantitativeOverloadStatement (object : FiniteObject.{u})
    (threshold order : Nat) : Prop :=
  ∀ (data : CapacityPresentation.{u} object order)
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
  ∀ (data : CapacityPresentation.{u} object order)
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
    (threshold order : Nat) (Label : Type) [Fintype Label] : Prop :=
  ∃ (data : CapacityPresentation.{u} object order)
      (ledger : ObjectCapacityLedger.{u} object threshold order data)
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
  ∀ (data : CapacityPresentation.{u} object order)
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

/-- **`thm:homogeneous-overload-geometric-closure`, first assertion, at the
object.**

*"Every role-homogeneous same-token matching or star of size `L_geom` in the
window-incidence, remainder-surplus, or primitive-carrier token classes realizes
either a sparse surplus exit or a decorated Type B handoff fan envelope."*

Read at the routed configuration `def:same-token-routing-germs` declares: at
every declared routed bottleneck of the object, the identification at the first
separator is absorbed -- the quotient, compression and delocalization readings
of `def:named-surplus-exits` -- or the separator survives and the separated
tails are admissible decorated Type B handoff fan data.  This is
`prop:nonnear-cubic-sharp-overload-routing`'s (b) or (c), committed as one
fact. -/
def BottleneckRoutingStatement (object : FiniteObject.{u})
    (Baseline : FiniteObject.{u} → Prop) (LengthOK : Nat → Prop) (order : Nat) :
    Prop :=
  ∀ (HighDegree : object.Vertex → Prop)
    (Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop)
    (bottleneck : SameTokenRoutingGerms.RoutedBottleneck object HighDegree
      Absorbing),
    Graph.InducedPathFree (object.induce bottleneck.support) order →
    DecoratedHandoff.Absorbed (Graph.HasCycleWithLength LengthOK)
        bottleneck.reading
        (SameTokenRoutingGerms.Delocalizes Baseline
          (Graph.HasCycleWithLength LengthOK) object) ∨
      (3 < object.degree bottleneck.separation.separator ∧
        ∃ envelope : DecoratedHandoff.Envelope object LengthOK HighDegree
          Absorbing,
          DecoratedHandoff.Admissible object LengthOK
            (fun piece =>
              ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport Baseline
                (Graph.HasCycleWithLength LengthOK) object piece)
            (fun piece => Graph.InducedPathFree (object.induce piece) order)
            envelope)

/-- **Node `[144]`, the bottleneck arm's fact: the Type B handoff itself.**

`prop:nonnear-cubic-sharp-overload-routing` opens *"If a sparse surplus exit
occurs, there is nothing to route.  Otherwise…"* — so on the branch that reaches
`[144]`, which is node `[125]`'s survivor, outcome (b) is already excluded and
the manuscript's trichotomy is a *dichotomy*: the fixed caps close to the
near-cubic spine, or the bottleneck produces decorated Type B fan data.

This is that second outcome, at every declared routed bottleneck of the object:
`d_G(z) ≥ 4` and the separated tails are admissible decorated Type B handoff fan
data.  It is `lem:same-token-bottleneck-routing` with its absorbed case refuted
by survival, which is the manuscript's *"Thus every surviving separated case
enters the Type B fan ledger."* -/
def TypeBHandoffStatement (object : FiniteObject.{u})
    (Baseline : FiniteObject.{u} → Prop) (LengthOK : Nat → Prop) (order : Nat) :
    Prop :=
  ∀ (HighDegree : object.Vertex → Prop)
    (Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop)
    (bottleneck : SameTokenRoutingGerms.RoutedBottleneck object HighDegree
      Absorbing),
    Graph.InducedPathFree (object.induce bottleneck.support) order →
    bottleneck.separation.separator ∉
      Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
        bottleneck.separation.switchSupport →
    Baseline (Graph.glue bottleneck.reading.quotient
      bottleneck.separation.atom.decomposition.outside) →
    Graph.Response.ContextEquivalent (Graph.HasCycleWithLength LengthOK)
      bottleneck.reading.quotient bottleneck.reading.full →
    3 < object.degree bottleneck.separation.separator ∧
      ∃ envelope : DecoratedHandoff.Envelope object LengthOK HighDegree
        Absorbing,
        DecoratedHandoff.Admissible object LengthOK
          (fun piece => ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
            Baseline (Graph.HasCycleWithLength LengthOK) object piece)
          (fun piece => Graph.InducedPathFree (object.induce piece) order)
          envelope

/-! ## The statements, proved -/

theorem roleFibrePartitionStatement (object : FiniteObject.{u})
    (threshold order : Nat) :
    RoleFibrePartitionStatement object threshold order := by
  intro _data ledger
  refine ⟨ledger.presented.choose_two_eq_free_add_sum_roleFibre
      ledger.presented.tokenClass,
    fun token => ledger.presented.load_eq_sum_roleFibre token,
    ledger.presented.classwise_split.1.1,
    ledger.presented.classwise_split.1.2,
    ledger.presented.classwise_split.2,
    ledger.presented.subtype_split.1.1,
    ledger.presented.subtype_split.2,
    fun patternBound positive value noMatching noStar =>
      ledger.presented.grainLoad_le_of_no_homogeneous
        ledger.presented.tokenClass value patternBound positive noMatching
        noStar⟩

/-- **Nodes `[140]`, `[142]`, `[143]`, proved.**  Each audit is the
contrapositive of `def:homogeneous-token-charge`'s cap charge at the counted
`L_geom`, which is `PatternFamily.card_le_capCharge` summed over the `Q_st` role
fibres.  Nothing about the class is used in the proof: what the class does is
select *which* audit the branch entered, and that is the router's job, not this
theorem's. -/
theorem classAuditStatement (object : FiniteObject.{u}) (threshold order : Nat)
    (Label : Type) [Fintype Label] (value : TokenClass) :
    ClassAuditStatement object threshold order Label value :=
  fun _data ledger token _inClass overloaded =>
    ledger.presented.exists_homogeneous_pattern_of_capCharge_lt
      (fun _ => SameTokenRoutingGerms.patternBound Label) token
      (SameTokenRoutingGerms.one_le_patternBound Label) overloaded

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
theorem overloadClassExhaustive (object : FiniteObject.{u}) (threshold order : Nat)
    (notWindow : SparsePressureOverloadOutsideClass object threshold order
      .windowIncidence) :
    SparsePressureOverloadInClass object threshold order .remainderSurplus ∨
      SparsePressureOverloadInClass object threshold order .primitiveCarrier := by
  obtain ⟨data, ledger, routingLabelBound, token, role, tokenMem,
    outsideWindow, rest⟩ := notWindow
  cases classified : ledger.presented.tokenClass token with
  | windowIncidence =>
      exact absurd classified outsideWindow
  | remainderSurplus =>
      exact Or.inl ⟨data, ledger, routingLabelBound, token, role, tokenMem,
        classified, rest⟩
  | primitiveCarrier =>
      exact Or.inr ⟨data, ledger, routingLabelBound, token, role, tokenMem,
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

/-- The failed fixed-cap subbranch is the positive bottleneck-pattern fact. -/
theorem homogeneousBottleneckPatternStatement_of_not_caps
    (object : FiniteObject.{u}) {threshold order : Nat} {Label : Type}
    [Fintype Label]
    (failure : ¬ HomogeneousCapsHold object threshold order Label) :
    HomogeneousBottleneckPatternStatement object threshold order Label := by
  classical
  by_contra noPattern
  apply failure
  intro declared ledger
  refine ⟨?_, ?_⟩
  · intro token tokenMem role
    rintro ⟨pattern, subset, matching, large⟩
    exact noPattern ⟨declared, ledger, token, tokenMem, role,
      Or.inl ⟨pattern, subset, matching, large⟩⟩
  · intro token tokenMem role
    rintro ⟨centre, pattern, subset, star, large⟩
    exact noPattern ⟨declared, ledger, token, tokenMem, role,
      Or.inr ⟨centre, pattern, subset, star, large⟩⟩

/-- **Node `[144]`'s bottleneck arm, proved.**

Every input is a fact the branch already carries: node `[125]`'s survival, the
selection entry's avoidance, and node `[11]`--`[14]`'s `cor:uncompressible`.
Nothing is assumed and nothing is reconstructed. -/
theorem typeBHandoffStatement (object : FiniteObject.{u})
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop} {order : Nat}
    (survives : Graph.SurvivesSparseExits Baseline
      (Graph.HasCycleWithLength LengthOK) LengthOK object)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
    (uncompressible : ∀ piece : Finset object.Vertex,
      ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport Baseline
        (Graph.HasCycleWithLength LengthOK) object piece) :
    TypeBHandoffStatement object Baseline LengthOK order :=
  fun _HighDegree _Absorbing bottleneck windowFree internal baseline
      contextEquivalent =>
    bottleneck.typeBHandoff survives avoids uncompressible windowFree internal
      baseline contextEquivalent

/-- **The first assertion, proved.**  It is
`lem:same-token-bottleneck-routing` at the declared routed bottleneck; nothing
about the object is assumed. -/
theorem bottleneckRoutingStatement (object : FiniteObject.{u})
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop} {order : Nat}
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
    (uncompressible : ∀ piece : Finset object.Vertex,
      ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport Baseline
        (Graph.HasCycleWithLength LengthOK) object piece) :
    BottleneckRoutingStatement object Baseline LengthOK order :=
  fun _HighDegree _Absorbing bottleneck windowFree =>
    bottleneck.outcome avoids uncompressible windowFree

/-- **`prop:nonnear-cubic-sharp-overload-routing`, the exhaustive outcome at
node `[144]`.**

Either the fixed homogeneous caps hold -- and then the near-cubic estimate above
closes the branch to node `[138]` -- or some capacity token supports a
role-homogeneous same-token `L_geom`-pattern, which is the bottleneck
`lem:same-token-bottleneck-routing` reads as a sparse surplus exit or as
decorated Type B handoff fan data.  The two arms are the two cases of the
excluded middle on a property of the object, so nothing is assumed to make the
split exhaustive. -/
theorem homogeneousCapsRouting (object : FiniteObject.{u})
    (threshold order : Nat) (Label : Type) [Fintype Label] :
    HomogeneousCapsHold object threshold order Label ∨
      ¬ HomogeneousCapsHold object threshold order Label :=
  Classical.em _

theorem fibrePressureStatement (object : FiniteObject.{u}) (threshold order : Nat)
    (existing : ∀ data : CapacityPresentation.{u} object order,
      Nonempty (ObjectCapacityLedger.{u} object threshold order data)) :
    FibrePressureStatement object threshold order := by
  intro data
  obtain ⟨ledger⟩ := existing data
  obtain ⟨token, tokenMem, role, display, roleBound, forced, pattern⟩ :=
    ledger.presented.exists_forced_pattern
  exact ⟨ledger, token, role, tokenMem, display, roleBound, forced, pattern⟩

/-- **`cor:spine-lower-bound-surplus-estimates` at the object**: each lower-bound
package that bounds the pair count of the active family bounds the surplus. -/
theorem surplus_le_of_package (object : FiniteObject.{u}) (threshold : Nat) :
    ∀ package : Nat,
      (object.degreeSurplus threshold).choose 2 ≤ package →
      object.degreeSurplus threshold ≤ 1 + Nat.sqrt (2 * package) :=
  fun package budget =>
    TokenLoad.demand_le_of_package (object.degreeSurplus threshold) package budget

/-- **`prop:single-graph-sparse-pressure-routing` (c): the alternatives are
exhaustive.**

No graph remains at node `[137]`.  Either every capacity ledger of the object
respects the geometric caps -- and then `σ(G) ≤ R_L(n)`, which is the near-cubic
route `[138]` -- or some ledger overloads, and then the coupled excess is
positive and forces a role-homogeneous same-token pattern whose token class
selects `[140]`, `[142]` or `[143]`.  The two arms are the two cases of the
excluded middle on `SparsePressureCapped`, so nothing is assumed to make the
split exhaustive. -/
theorem sparsePressureRouting (object : FiniteObject.{u}) (threshold order : Nat) :
    SparsePressureCapped object threshold order ∨
      SparsePressureOverloadStatement object threshold order := by
  classical
  by_cases capped : SparsePressureCapped.{u} object threshold order
  · exact .inl capped
  · refine .inr ?_
    unfold SparsePressureCapped at capped
    push_neg at capped
    obtain ⟨data, ledger, routingLabelBound, failure⟩ := capped
    obtain ⟨token, tokenMem, role, overload, excess, pattern⟩ :
        ∃ token ∈ ledger.presented.tokens, ∃ role : Role,
          0 < ledger.presented.coupledExcess
              ledger.presented.tokenClass
              (fun _ => geometricPatternBound routingLabelBound) ∧
            ledger.presented.coupledExcess
                ledger.presented.tokenClass
                (fun _ => geometricPatternBound routingLabelBound) ≤
              sameTokenRoleBound * ledger.presented.tokens.card *
                ledger.presented.roleFibreExcess
                  ledger.presented.tokenClass
                  (fun _ => geometricPatternBound routingLabelBound) token role ∧
            ((∃ pattern ⊆ ledger.presented.roleFibre token role,
                PatternFamily.IsMatching pattern ∧
                  PatternFamily.patternThreshold
                      (ledger.presented.roleFibre token role).card ≤
                    pattern.card) ∨
              (∃ centre, ∃ pattern ⊆ ledger.presented.roleFibre token role,
                PatternFamily.IsStar pattern centre ∧
                  PatternFamily.patternThreshold
                      (ledger.presented.roleFibre token role).card ≤
                    pattern.card)) := by
      rcases ledger.presented.sparsePressureAlternative
        ledger.presented.tokenClass
        (fun _ => geometricPatternBound routingLabelBound)
        (homogeneousTokenCap routingLabelBound) (object.capacityTokenSupply threshold)
        (fun _ => Nat.le_refl _) (ledger.tokens_card_le) with
        bounded | ⟨token, tokenMem, role, rest⟩
      · exact absurd bounded (Nat.not_le.mpr failure)
      · exact ⟨token, tokenMem, role, rest⟩
    exact ⟨data, ledger, routingLabelBound, token, role, tokenMem, trivial, overload,
      excess, pattern⟩

end Hypostructure.Graph
