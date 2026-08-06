import Hypostructure.Graph.GrainedTokenBudget
import Hypostructure.Graph.CapacityTokenAssignment

/-!
# The capacity-token ledger of an object, and the statements read off it

`Graph/CapacityTokenLedger.lean` presents a capacity-token ledger over an
abstract demand family.  This module fixes the presentation node `[136]` builds
for one object: the token universe `𝔗_cap`, the assignment `Θ_cap`,
`lem:capacity-token-supply`'s `|𝔗_cap| ≤ 8n + σ(G)`, and the free-side entropy
sandwich.  Bundling them is what lets nodes `[137]`--`[144]` speak about *the*
capacity ledger of the object rather than about an invented one: the bundle is
what node `[136]` commits, and the nodes below read that commitment by exact key
instead of quantifying over a presentation nobody built.

`ObjectCapacityLedger` carries no hypothesis that is not one of
`def:capacity-token-ledger`, `lem:capacity-token-supply` and
`prop:sparse-entropy-sandwich-with-blockers`.  The pair schedule and its count
are not fields: the schedule is the object's own `portPairSchedule`, and its
count is node `[130]`'s committed `|Π(𝒜₀)| = C(σ(G),2)`, supplied wherever the
ledger is spent so that the caller must have read it.

`L_geom` enters as `def:same-token-routing-germs`' routing-label count `Q_geom`,
which is what `SameTokenBlockerRoles.geometricPatternBound` takes: no numeral is
written, and a caller passing anything other than a routing-label count is not
computing `L_geom`.
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.SameTokenBlockerRoles

universe u v

/-- **`def:capacity-token-ledger` at one object, with its supply and its
sandwich.**

`order` is the declared token order whose first applicable label is `Θ_cap`;
`subtype` is `sub(t)`, so `class(t)` is determined; `Eligible` is the four-case
eligibility of that assignment; `role` is `ρ_t`; `supply` is
`lem:capacity-token-supply`; and `sandwich` is
`prop:sparse-entropy-sandwich-with-blockers` on the free side of this very
charge. -/
structure ObjectCapacityLedger (object : FiniteObject.{u}) (threshold : Nat) where
  /-- Node `[130]`'s committed `|Π(𝒜₀)| = C(σ(G),2)`: the charge is levied on
  the object's own pair schedule, so its count is part of the commitment. -/
  scheduleCard : (object.portPairSchedule threshold).card =
    (object.degreeSurplus threshold).choose 2
  /-- The capacity-token universe `𝔗_cap = 𝔗_W ⊔ 𝔗_R ⊔ 𝔗_prim`. -/
  Token : Type u
  tokenDecidable : DecidableEq Token
  /-- The declared token order: "first applicable label" makes `Θ_cap`
  single-valued. -/
  order : List Token
  orderNonempty : order.toFinset.Nonempty
  /-- `sub(t)`, which determines `class(t)`. -/
  subtype : Token → TokenSubtype
  /-- The four-case eligibility whose first applicable label is `Θ_cap`. -/
  Eligible : Token → Finset (object.Vertex × object.Vertex) → Prop
  eligibleDecidable : ∀ token pair, Decidable (Eligible token pair)
  /-- `ρ_t`, the same-token role of a blocked pair. -/
  role : Finset (object.Vertex × object.Vertex) → Role
  /-- `E_spine(n) + ((1/2)σ(G)+1)log₂ n`. -/
  entropyBudget : Nat
  /-- `prop:sparse-entropy-sandwich-with-blockers` at this charge. -/
  sandwich :
    (freeSide object.vertexPairDecidableEq (object.portPairSchedule threshold)
      order Eligible eligibleDecidable).card ≤ entropyBudget
  /-- **`lem:capacity-token-supply`**: `|𝔗_cap| ≤ 8n + σ(G)`. -/
  supply :
    order.toFinset.card ≤ 8 * object.vertexCount + object.degreeSurplus threshold

namespace ObjectCapacityLedger

variable {object : FiniteObject.{u}} {threshold : Nat}

/-- The abstract ledger this presentation is, charged at the object's own pair
schedule with node `[130]`'s committed count. -/
noncomputable def presented (ledger : ObjectCapacityLedger object threshold) :
    CapacityTokenLedger.{u} (object.degreeSurplus threshold) :=
  CapacityTokenLedger.ofPortSchedule object threshold (object.degreeSurplus threshold)
    ledger.scheduleCard ledger.tokenDecidable ledger.order ledger.orderNonempty
    ledger.subtype ledger.Eligible ledger.eligibleDecidable ledger.role
    ledger.entropyBudget ledger.sandwich

/-- `lem:capacity-token-supply` in the form the closure step spends: the token
supply is linear in `n` above the active family. -/
theorem tokens_card_le (ledger : ObjectCapacityLedger object threshold) :
    ledger.presented.tokens.card ≤
      8 * object.vertexCount + object.degreeSurplus threshold :=
  ledger.supply

/-- **The object's capacity-token ledger, built from node `[136]`'s own
`𝔗_cap` and `Θ_cap`.**

Nothing here is a fresh presentation: `Token` is `def:capacity-token-ledger`'s
`CapacityToken`, `order` is the object's own enumeration of `𝔗_cap`, `Eligible`
is `Θ_cap` read as the ledger's eligibility -- so its first applicable label is
the charge itself, by `canonicalLabel_eq_capacityCharge` -- and `subtype` is the
`sub(t)` the constructor already names.  What the caller supplies is only what
lives on other ledger entries: node `[130]`'s pair count, `ρ_t`, and the
free-side entropy budget with its sandwich and node `[136]`'s supply bound. -/
noncomputable def ofCapacityCharge {Coordinate Chord : Type v}
    (activation : FiniteObject.DemandActivation object Coordinate Chord)
    (presentation : FiniteObject.CarrierPresentation object Coordinate Chord)
    (packing : Finset (Finset object.Vertex))
    (role : Finset (object.Vertex × object.Vertex) → Role)
    (entropyBudget : Nat)
    (scheduleCard : (object.portPairSchedule threshold).card =
      (object.degreeSurplus threshold).choose 2)
    (orderNonempty : (object.capacityTokens threshold packing).Nonempty)
    (sandwich :
      (freeSide object.vertexPairDecidableEq (object.portPairSchedule threshold)
        (FiniteObject.capacityTokenOrder object threshold packing)
        (FiniteObject.Charges activation presentation threshold packing)
        (FiniteObject.decidableCharges activation presentation threshold
          packing)).card ≤ entropyBudget)
    (supply : (object.capacityTokens threshold packing).card ≤
      8 * object.vertexCount + object.degreeSurplus threshold) :
    ObjectCapacityLedger object threshold where
  scheduleCard := scheduleCard
  Token := FiniteObject.CapacityToken object
  tokenDecidable := FiniteObject.CapacityToken.decidableEq object
  order := FiniteObject.capacityTokenOrder object threshold packing
  orderNonempty := by
    rw [FiniteObject.capacityTokenOrder, Finset.toList_toFinset]
    exact orderNonempty
  subtype := FiniteObject.CapacityToken.subtype
  Eligible := FiniteObject.Charges activation presentation threshold packing
  eligibleDecidable :=
    FiniteObject.decidableCharges activation presentation threshold packing
  role := role
  entropyBudget := entropyBudget
  sandwich := sandwich
  supply := by
    rw [FiniteObject.capacityTokenOrder, Finset.toList_toFinset]
    exact supply

end ObjectCapacityLedger

/-! ## The statements nodes `[137]`--`[143]` commit -/

/-- **Node `[137]`, first production**: `lem:exact-surplus-pair-charge-partition`
with `thm:sharp-classwise-homogeneous-token-budget` (a)--(c) and
`thm:sharp-surplus-overload-audit` (b)--(c), at the object's own capacity
ledger. -/
def RoleFibrePartitionStatement (object : FiniteObject.{u}) (threshold : Nat) : Prop :=
  ∀ ledger : ObjectCapacityLedger.{u} object threshold,
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
def FibrePressureStatement (object : FiniteObject.{u}) (threshold : Nat) : Prop :=
  ∃ (ledger : ObjectCapacityLedger.{u} object threshold)
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
def SparsePressureCapped (object : FiniteObject.{u}) (threshold : Nat) : Prop :=
  ∀ (ledger : ObjectCapacityLedger.{u} object threshold) (routingLabelBound : Nat),
    object.degreeSurplus threshold ≤
      CapacityTokenLedger.sparsePressureBound ledger.entropyBudget
        (homogeneousTokenCap routingLabelBound) (8 * object.vertexCount)

/-- **Node `[137]`, overload arm**: `prop:single-graph-sparse-pressure-routing`
(b) with `cor:coupled-single-graph-overload-budget` (a)--(c) and
`cor:quantified-homogeneous-class-overload`.

Some capacity-token ledger of the object has positive coupled excess `D_all` at
the geometric caps, and some role fibre absorbs its average share over the
`Q_st|𝔗_cap|` slots, hence carries a role-homogeneous same-token matching or
star.  `class(t)` of that token is the one datum nodes `[140]`, `[142]`, `[143]`
dispatch on, and it is read off the token rather than carried beside it. -/
def SparsePressureOverloadStatement (object : FiniteObject.{u}) (threshold : Nat) :
    Prop :=
  ∃ (ledger : ObjectCapacityLedger.{u} object threshold) (routingLabelBound : Nat)
      (token : ledger.presented.Token) (role : Role),
      token ∈ ledger.presented.tokens ∧
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

/-! ## The statements, proved -/

theorem roleFibrePartitionStatement (object : FiniteObject.{u}) (threshold : Nat) :
    RoleFibrePartitionStatement object threshold := by
  intro ledger
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

theorem fibrePressureStatement (object : FiniteObject.{u}) (threshold : Nat)
    (existing : Nonempty (ObjectCapacityLedger.{u} object threshold)) :
    FibrePressureStatement object threshold := by
  obtain ⟨ledger⟩ := existing
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
theorem sparsePressureRouting (object : FiniteObject.{u}) (threshold : Nat) :
    SparsePressureCapped object threshold ∨
      SparsePressureOverloadStatement object threshold := by
  classical
  by_cases capped : SparsePressureCapped.{u} object threshold
  · exact .inl capped
  · refine .inr ?_
    unfold SparsePressureCapped at capped
    push_neg at capped
    obtain ⟨ledger, routingLabelBound, failure⟩ := capped
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
        (homogeneousTokenCap routingLabelBound) (8 * object.vertexCount)
        (fun _ => Nat.le_refl _) (ledger.tokens_card_le) with
        bounded | ⟨token, tokenMem, role, rest⟩
      · exact absurd bounded (Nat.not_le.mpr failure)
      · exact ⟨token, tokenMem, role, rest⟩
    exact ⟨ledger, routingLabelBound, token, role, tokenMem, overload, excess, pattern⟩

end Hypostructure.Graph
