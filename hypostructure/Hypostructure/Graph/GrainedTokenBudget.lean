import Hypostructure.Graph.CapacityTokenLedger

/-!
# The grained token budget: classwise and subtype accounting on a presented ledger

`thm:sharp-classwise-homogeneous-token-budget` groups the capacity tokens into
the three classes `W, R, P` of `𝔗_cap = 𝔗_W ⊔ 𝔗_R ⊔ 𝔗_prim`;
`thm:sharp-surplus-overload-audit` groups the same tokens into the six subtypes
`RW, WW, R, V, I, P`.  The two are the same accounting at two granularities, so
this module proves it once over an arbitrary finite grouping `grain` of the
token universe and reads both off it.

What is grouped is always the canonical ledger's own data: `𝔗_C` is a `filter`
of `CapacityTokenLedger.tokens`, `B_C` is the sum of `CapacityTokenLedger.load`
over it, and `ℓ(t,r)` is `CapacityTokenLedger.roleFibre`.  Nothing is
re-charged and no second pair representation appears.

The results proved here, in manuscript order:

* `lem:exact-surplus-pair-charge-partition` -- the exact disjoint decomposition
  `C(𝒜₀,2) = Π_free ⊔ ⨆_C ⨆_{t ∈ 𝔗_C} ⨆_r Π_{t,r}`, in its cardinality form;
* `thm:sharp-classwise-homogeneous-token-budget` (a)--(e);
* `cor:quantified-homogeneous-class-overload` (a)--(e);
* `cor:coupled-single-graph-overload-budget` (a)--(c);
* `cor:numerical-single-graph-budget`, as the exact supply identities;
* `prop:single-graph-sparse-pressure-routing`, as the exhaustive alternative
  the node `[137]` branch tests;
* `thm:sharp-surplus-overload-audit`, the same at subtype granularity.

Every manuscript display with a division is written multiplicatively:
`ℓ(t,r) ≥ B_C/(Q_st S_C)` is `B_C ≤ Q_st · S_C · ℓ(t,r)`, which is the same
statement without a rounding convention, and `(x)_+` is `Nat` subtraction.
-/

namespace Hypostructure.Graph

open scoped BigOperators
open Hypostructure.Graph.SameTokenBlockerRoles

universe u

/-- Truncated subtraction is superadditive over a sum: this is the elementary
inequality `Σ_i (x_i − y_i)_+ ≥ (Σ_i x_i − Σ_i y_i)_+` that
`cor:quantified-homogeneous-class-overload` (a) and
`cor:coupled-single-graph-overload-budget` (a) both spend. -/
theorem sub_sum_le_sum_sub {ι : Type*} (support : Finset ι) (upper lower : ι → Nat) :
    (∑ index ∈ support, upper index) - (∑ index ∈ support, lower index) ≤
      ∑ index ∈ support, (upper index - lower index) := by
  classical
  induction support using Finset.induction_on with
  | empty => simp
  | @insert head tail notMem ih =>
      rw [Finset.sum_insert notMem, Finset.sum_insert notMem, Finset.sum_insert notMem]
      omega

namespace CapacityTokenLedger

variable {demandCount : Nat} (ledger : CapacityTokenLedger.{u} demandCount)
variable {Grain : Type} [DecidableEq Grain] [Fintype Grain]

/-! ## The grouping, and the two exact partitions it induces -/

/-- `𝔗_C`, the tokens of one grain: a class `W, R, P` or a subtype
`RW, WW, R, V, I, P`, according to the grouping supplied. -/
def grainTokens (grain : ledger.Token → Grain) (value : Grain) : Finset ledger.Token :=
  ledger.tokens.filter fun token => grain token = value

omit [Fintype Grain] in
theorem grainTokens_subset (grain : ledger.Token → Grain) (value : Grain) :
    ledger.grainTokens grain value ⊆ ledger.tokens :=
  Finset.filter_subset _ _

/-- `B_C = Σ_{t ∈ 𝔗_C} ℓ_cap(t)`, the blocked-pair demand carried by a grain. -/
def grainLoad (grain : ledger.Token → Grain) (value : Grain) : Nat :=
  ∑ token ∈ ledger.grainTokens grain value, ledger.load token

/-- **`thm:sharp-classwise-homogeneous-token-budget` (b), supply half**:
the grains partition the token universe, so `S_W + S_R + S_P = |𝔗_cap|`. -/
theorem sum_grainTokens_card (grain : ledger.Token → Grain) :
    ∑ value : Grain, (ledger.grainTokens grain value).card = ledger.tokens.card :=
  (Finset.card_eq_sum_card_fiberwise fun token _ => Finset.mem_univ (grain token)).symm

/-- **`thm:sharp-classwise-homogeneous-token-budget` (a), split half**:
`B_W + B_R + B_P = |Π_blk|`, because `Θ_cap` assigns every blocked pair exactly
one token and the grains partition the tokens. -/
theorem sum_grainLoad (grain : ledger.Token → Grain) :
    ∑ value : Grain, ledger.grainLoad grain value = ledger.blocked.card := by
  classical
  rw [ledger.blocked_card_eq_sum_load]
  exact Finset.sum_fiberwise_of_maps_to (fun token _ => Finset.mem_univ (grain token))
    (fun token => ledger.load token)

/-- A weight that depends on a token only through its grain is summed grain by
grain: the arithmetic behind every "class supply times class cap" display. -/
theorem sum_grain_weight (grain : ledger.Token → Grain) (weight : Grain → Nat) :
    ∑ token ∈ ledger.tokens, weight (grain token) =
      ∑ value : Grain, weight value * (ledger.grainTokens grain value).card := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset Grain))
    (fun token (_ : token ∈ ledger.tokens) => Finset.mem_univ (grain token))
    (fun token => weight (grain token))]
  refine Finset.sum_congr rfl fun value _ => ?_
  have constant : ∀ token ∈ ledger.grainTokens grain value,
      weight (grain token) = weight value :=
    fun token tokenMem => by rw [(Finset.mem_filter.mp tokenMem).2]
  rw [show ledger.tokens.filter (fun token => grain token = value) =
      ledger.grainTokens grain value from rfl, Finset.sum_const_nat constant]
  exact Nat.mul_comm _ _

/-- `N_*(G) = max{0, C(σ(G),2) − E_spine(n) − ((1/2)σ(G)+1)log₂ n}`, with the
entropy sandwich budget of the presentation in the subtracted position. -/
def forcedDemand : Nat := demandCount.choose 2 - ledger.entropyBudget

/-- **`thm:sharp-classwise-homogeneous-token-budget` (a), lower bound**:
`|Π_blk| ≥ N_*(G)`.  The free side is spent against the entropy sandwich and the
split `|Π_free| + |Π_blk| = C(σ(G),2)` is the ledger's own. -/
theorem forcedDemand_le_blocked : ledger.forcedDemand ≤ ledger.blocked.card := by
  have split := ledger.blocked_card_add_free_card
  have sandwichLe := ledger.free_card_le_entropyBudget
  unfold forcedDemand
  omega

/-- **`lem:exact-surplus-pair-charge-partition`, cardinality form.**

  `C(|𝒜₀|,2) = |Π_free| + Σ_C Σ_{t ∈ 𝔗_C} Σ_{r ∈ 𝔕_st} ℓ(t,r)`.

Every unordered pair of active demands appears in exactly one summand: the
free/blocked split is the canonical ledger's own, `Θ_cap` puts each blocked pair
in exactly one token fibre, the grains partition the tokens, and `ρ_t`
partitions each token fibre by role. -/
theorem choose_two_eq_free_add_sum_roleFibre (grain : ledger.Token → Grain) :
    demandCount.choose 2 =
      ledger.free.card +
        ∑ value : Grain, ∑ token ∈ ledger.grainTokens grain value,
          ∑ role : Role, (ledger.roleFibre token role).card := by
  have inner : ∀ value : Grain,
      ∑ token ∈ ledger.grainTokens grain value,
          ∑ role : Role, (ledger.roleFibre token role).card =
        ledger.grainLoad grain value := by
    intro value
    refine Finset.sum_congr rfl fun token _ => ?_
    exact (ledger.load_eq_sum_roleFibre token).symm
  rw [Finset.sum_congr rfl fun value _ => inner value, ledger.sum_grainLoad grain]
  have split := ledger.blocked_card_add_free_card
  omega

/-! ## The per-token cap, and the classwise budget it sums to -/

/-- **The cap step at one token**: a token none of whose role fibres carries a
role-homogeneous `L`-matching or `L`-star has load at most `Cap_hom(L)`.

This is `lem:same-token-matching-star` charged to each of the `Q_st` role fibres
and summed by the role-fibre partition. -/
theorem load_le_homogeneousCapCharge (token : ledger.Token) (patternBound : Nat)
    (positive : 1 ≤ patternBound)
    (noHomogeneousMatching : ∀ role : Role,
      ¬ ∃ pattern ⊆ ledger.roleFibre token role,
        PatternFamily.IsMatching pattern ∧ patternBound ≤ pattern.card)
    (noHomogeneousStar : ∀ role : Role,
      ¬ ∃ centre : ledger.Demand, ∃ pattern ⊆ ledger.roleFibre token role,
        PatternFamily.IsStar pattern centre ∧ patternBound ≤ pattern.card) :
    ledger.load token ≤ homogeneousCapCharge patternBound := by
  have bounded :=
    PatternFamily.card_le_capCharge (ledger.fibre token) ledger.role Finset.univ
      patternBound positive (ledger.pairs_fibre token) (fun _ _ => Finset.mem_univ _)
      (fun role _ => noHomogeneousMatching role) (fun role _ => noHomogeneousStar role)
  rw [card_univ_eq_sameTokenRoleBound, ← homogeneousCapCharge_eq_capCharge] at bounded
  rw [ledger.load_eq_card_fibre]
  exact bounded

omit [Fintype Grain] in
/-- **`thm:sharp-classwise-homogeneous-token-budget` (c).**

  `B_C ≤ Cap_hom(L_C) S_C`

when no token of the class supports a role-homogeneous same-token
`L_C`-matching or `L_C`-star. -/
theorem grainLoad_le_of_no_homogeneous (grain : ledger.Token → Grain) (value : Grain)
    (patternBound : Nat) (positive : 1 ≤ patternBound)
    (noHomogeneousMatching : ∀ token ∈ ledger.grainTokens grain value, ∀ role : Role,
      ¬ ∃ pattern ⊆ ledger.roleFibre token role,
        PatternFamily.IsMatching pattern ∧ patternBound ≤ pattern.card)
    (noHomogeneousStar : ∀ token ∈ ledger.grainTokens grain value, ∀ role : Role,
      ¬ ∃ centre : ledger.Demand, ∃ pattern ⊆ ledger.roleFibre token role,
        PatternFamily.IsStar pattern centre ∧ patternBound ≤ pattern.card) :
    ledger.grainLoad grain value ≤
      homogeneousCapCharge patternBound * (ledger.grainTokens grain value).card := by
  calc ledger.grainLoad grain value
      ≤ ∑ _token ∈ ledger.grainTokens grain value, homogeneousCapCharge patternBound :=
        Finset.sum_le_sum fun token tokenMem =>
          ledger.load_le_homogeneousCapCharge token patternBound positive
            (noHomogeneousMatching token tokenMem) (noHomogeneousStar token tokenMem)
    _ = homogeneousCapCharge patternBound * (ledger.grainTokens grain value).card := by
        rw [Finset.sum_const_nat fun _ _ => rfl, Nat.mul_comm]

/-- `A_C = Cap_hom(L_C) S_C`, the capacity of one grain at its proposed cap. -/
def grainCapacity (grain : ledger.Token → Grain) (patternBound : Grain → Nat)
    (value : Grain) : Nat :=
  homogeneousCapCharge (patternBound value) * (ledger.grainTokens grain value).card

/-- `A_all = Σ_C Cap_hom(L_C) S_C` of `cor:coupled-single-graph-overload-budget`:
the exact coupled capacity of the grains in the single graph.  All grains are
evaluated against the one presented ledger, which is what makes it coupled. -/
def coupledCapacity (grain : ledger.Token → Grain) (patternBound : Grain → Nat) : Nat :=
  ∑ value : Grain, ledger.grainCapacity grain patternBound value

/-- `D_all = (N_*(G) − A_all)_+`, the coupled excess. -/
def coupledExcess (grain : ledger.Token → Grain) (patternBound : Grain → Nat) : Nat :=
  ledger.forcedDemand - ledger.coupledCapacity grain patternBound

/-- `Ω_C = (B_C − A_C)_+`, the overload of one grain. -/
def grainOverload (grain : ledger.Token → Grain) (patternBound : Grain → Nat)
    (value : Grain) : Nat :=
  ledger.grainLoad grain value - ledger.grainCapacity grain patternBound value

/-- **`thm:sharp-classwise-homogeneous-token-budget` (d).**

  `N_*(G) ≤ Cap_hom(L_W)S_W + Cap_hom(L_R)S_R + Cap_hom(L_P)S_P`

whenever the three proposed caps all hold: equivalently, `D_all = 0`. -/
theorem forcedDemand_le_coupledCapacity (grain : ledger.Token → Grain)
    (patternBound : Grain → Nat) (positive : ∀ value : Grain, 1 ≤ patternBound value)
    (noHomogeneousMatching : ∀ token ∈ ledger.tokens, ∀ role : Role,
      ¬ ∃ pattern ⊆ ledger.roleFibre token role,
        PatternFamily.IsMatching pattern ∧ patternBound (grain token) ≤ pattern.card)
    (noHomogeneousStar : ∀ token ∈ ledger.tokens, ∀ role : Role,
      ¬ ∃ centre : ledger.Demand, ∃ pattern ⊆ ledger.roleFibre token role,
        PatternFamily.IsStar pattern centre ∧ patternBound (grain token) ≤ pattern.card) :
    ledger.forcedDemand ≤ ledger.coupledCapacity grain patternBound := by
  classical
  have classwise : ∀ value : Grain,
      ledger.grainLoad grain value ≤ ledger.grainCapacity grain patternBound value := by
    intro value
    refine ledger.grainLoad_le_of_no_homogeneous grain value (patternBound value)
      (positive value) ?_ ?_
    · intro token tokenMem role
      have inClass : grain token = value := (Finset.mem_filter.mp tokenMem).2
      have := noHomogeneousMatching token (ledger.grainTokens_subset grain value tokenMem) role
      rw [inClass] at this
      exact this
    · intro token tokenMem role
      have inClass : grain token = value := (Finset.mem_filter.mp tokenMem).2
      have := noHomogeneousStar token (ledger.grainTokens_subset grain value tokenMem) role
      rw [inClass] at this
      exact this
  calc ledger.forcedDemand ≤ ledger.blocked.card := ledger.forcedDemand_le_blocked
    _ = ∑ value : Grain, ledger.grainLoad grain value := (ledger.sum_grainLoad grain).symm
    _ ≤ ∑ value : Grain, ledger.grainCapacity grain patternBound value :=
        Finset.sum_le_sum fun value _ => classwise value
    _ = ledger.coupledCapacity grain patternBound := rfl

/-- **`cor:quantified-homogeneous-class-overload` (a).**

  `Ω_W + Ω_R + Ω_P ≥ D_exc`,

by the superadditivity of truncated subtraction applied to the exact class
split. -/
theorem coupledExcess_le_sum_grainOverload (grain : ledger.Token → Grain)
    (patternBound : Grain → Nat) :
    ledger.coupledExcess grain patternBound ≤
      ∑ value : Grain, ledger.grainOverload grain patternBound value := by
  have split : ∑ value : Grain, ledger.grainLoad grain value = ledger.blocked.card :=
    ledger.sum_grainLoad grain
  have lower := ledger.forcedDemand_le_blocked
  calc ledger.coupledExcess grain patternBound
      ≤ (∑ value : Grain, ledger.grainLoad grain value) -
          ∑ value : Grain, ledger.grainCapacity grain patternBound value := by
        unfold coupledExcess coupledCapacity
        omega
    _ ≤ ∑ value : Grain, ledger.grainOverload grain patternBound value :=
        sub_sum_le_sum_sub _ _ _

/-- **`cor:quantified-homogeneous-class-overload` (b).**

Some grain carries at least a `|Grain|`-th of the coupled excess: the manuscript's
`Ω_C ≥ (1/3)D_exc` at the three classes, written without a division. -/
theorem exists_grainOverload_ge [Nonempty Grain] (grain : ledger.Token → Grain)
    (patternBound : Grain → Nat) :
    ∃ value : Grain,
      ledger.coupledExcess grain patternBound ≤
        Fintype.card Grain * ledger.grainOverload grain patternBound value := by
  classical
  obtain ⟨best, _, bestMax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset Grain)
      (fun value => ledger.grainOverload grain patternBound value) Finset.univ_nonempty
  refine ⟨best, le_trans (ledger.coupledExcess_le_sum_grainOverload grain patternBound) ?_⟩
  calc ∑ value : Grain, ledger.grainOverload grain patternBound value
      ≤ ∑ _value : Grain, ledger.grainOverload grain patternBound best :=
        Finset.sum_le_sum fun value valueMem => bestMax value valueMem
    _ = Fintype.card Grain * ledger.grainOverload grain patternBound best := by
        rw [Finset.sum_const_nat fun _ _ => rfl, Finset.card_univ, Nat.mul_comm]

/-- **`cor:quantified-homogeneous-class-overload` (d).**

If the other grains do not overload, the whole coupled deficit lands on this
one: `Ω_C ≥ D_exc`. -/
theorem coupledExcess_le_grainOverload (grain : ledger.Token → Grain)
    (patternBound : Grain → Nat) (value : Grain)
    (others : ∀ other : Grain, other ≠ value →
      ledger.grainLoad grain other ≤ ledger.grainCapacity grain patternBound other) :
    ledger.coupledExcess grain patternBound ≤
      ledger.grainOverload grain patternBound value := by
  classical
  have bound := ledger.coupledExcess_le_sum_grainOverload grain patternBound
  have vanish : ∀ other ∈ (Finset.univ : Finset Grain).erase value,
      ledger.grainOverload grain patternBound other = 0 := by
    intro other otherMem
    have distinct : other ≠ value := (Finset.mem_erase.mp otherMem).1
    have := others other distinct
    unfold grainOverload
    omega
  have decompose :
      ∑ other : Grain, ledger.grainOverload grain patternBound other =
        ledger.grainOverload grain patternBound value +
          ∑ other ∈ (Finset.univ : Finset Grain).erase value,
            ledger.grainOverload grain patternBound other :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ value)).symm
  rw [decompose, Finset.sum_eq_zero vanish] at bound
  omega

/-! ## The forced pattern: where the excess load has to go -/

/-- **`cor:forced-homogeneous-same-token-scale` at one token**: a role fibre of
the token carries at least a `Q_st`-th of its load, and contains a matching or
star of size `ψ` of its own count.  Every member of a role fibre has the same
role, so the pattern is role-homogeneous. -/
theorem exists_roleFibre_pattern (token : ledger.Token) :
    ∃ role : Role,
      ledger.load token ≤ sameTokenRoleBound * (ledger.roleFibre token role).card ∧
        ((∃ pattern ⊆ ledger.roleFibre token role,
            PatternFamily.IsMatching pattern ∧
              PatternFamily.patternThreshold (ledger.roleFibre token role).card ≤
                pattern.card) ∨
          (∃ centre : ledger.Demand, ∃ pattern ⊆ ledger.roleFibre token role,
            PatternFamily.IsStar pattern centre ∧
              PatternFamily.patternThreshold (ledger.roleFibre token role).card ≤
                pattern.card)) := by
  obtain ⟨role, _, large⟩ :=
    PatternFamily.exists_large_roleFibre (ledger.fibre token) ledger.role Finset.univ
      Finset.univ_nonempty fun _ _ => Finset.mem_univ _
  refine ⟨role, ?_, PatternFamily.exists_matching_or_star_of_patternThreshold
    (ledger.roleFibre token role) (ledger.pairs_roleFibre token role)⟩
  rw [ledger.load_eq_card_fibre, ← card_univ_eq_sameTokenRoleBound]
  exact large

/-- **`thm:sharp-surplus-overload-audit` (d), and
`cor:coupled-single-graph-overload-budget` (c) in its unrefined form.**

Whenever the forced blocked-pair demand is positive, some capacity token and
some role at that token carry it up to the two exact factors the manuscript
divides by -- the token supply `|𝔗_cap|` and the role bound `Q_st` -- and that
role fibre contains a role-homogeneous same-token matching or star of size `ψ`
of its own load.  The grain of the token is the class the branch routes on. -/
theorem exists_forced_pattern :
    ∃ token ∈ ledger.tokens, ∃ role : Role,
      demandCount.choose 2 ≤
          ledger.entropyBudget + ledger.tokens.card * ledger.load token ∧
        ledger.load token ≤ sameTokenRoleBound * (ledger.roleFibre token role).card ∧
        ledger.forcedDemand ≤
          sameTokenRoleBound * ledger.tokens.card * (ledger.roleFibre token role).card ∧
        ((∃ pattern ⊆ ledger.roleFibre token role,
            PatternFamily.IsMatching pattern ∧
              PatternFamily.patternThreshold (ledger.roleFibre token role).card ≤
                pattern.card) ∨
          (∃ centre : ledger.Demand, ∃ pattern ⊆ ledger.roleFibre token role,
            PatternFamily.IsStar pattern centre ∧
              PatternFamily.patternThreshold (ledger.roleFibre token role).card ≤
                pattern.card)) := by
  classical
  obtain ⟨token, tokenMem, heavy⟩ :=
    TokenLoad.exists_multiplicity_ge ledger.schedule ledger.order ledger.Eligible
      ledger.orderNonempty
  have loadBound : ledger.blocked.card ≤ ledger.tokens.card * ledger.load token := heavy
  obtain ⟨role, roleBound, pattern⟩ := ledger.exists_roleFibre_pattern token
  refine ⟨token, tokenMem, role, ?_, roleBound, ?_, pattern⟩
  · -- `lem:capacity-token-high-load`: the free side against the sandwich, the
    -- charged side against the fibre identity at the realized maximum.
    have split := ledger.blocked_card_add_free_card
    have sandwichLe := ledger.free_card_le_entropyBudget
    omega
  · have chain : ledger.tokens.card * ledger.load token ≤
        ledger.tokens.card * (sameTokenRoleBound * (ledger.roleFibre token role).card) :=
      Nat.mul_le_mul_left _ roleBound
    have reassociate :
        ledger.tokens.card * (sameTokenRoleBound * (ledger.roleFibre token role).card) =
          sameTokenRoleBound * ledger.tokens.card *
            (ledger.roleFibre token role).card := by
      ring
    have lower := ledger.forcedDemand_le_blocked
    omega

/-- **`cor:quantitative-homogeneous-overload`, the displayed lower bound.**

  `K_hom(G) ≥ ψ( N_*(G) / (Q_st |𝔗_cap|) )`,

where `K_hom(G)` is the largest scale at which some capacity token supports a
role-homogeneous same-token matching or star.  The display is stated
multiplicatively, so no division and no rounding convention is introduced: a
share `q` of the forced demand that the `Q_st|𝔗_cap|` slots must absorb is
realized by some role fibre, and `ψ` is monotone, so the pattern
`cor:forced-homogeneous-same-token-scale` produces has at least `ψ(q)` edges.

Substituting `lem:capacity-token-supply`'s `|𝔗_cap| ≤ 8n + σ(G)` into the
denominator and `E_spine(n) ≤ C_E n` into `N_*(G)` is the manuscript's own
display; both substitutions are made by the caller, since both are facts about
the object rather than about the ledger. -/
theorem exists_homogeneous_pattern_of_share (share : Nat)
    (slots : 0 < sameTokenRoleBound * ledger.tokens.card)
    (absorbs : share * (sameTokenRoleBound * ledger.tokens.card) ≤
      ledger.forcedDemand) :
    ∃ token ∈ ledger.tokens, ∃ role : Role,
      ((∃ pattern ⊆ ledger.roleFibre token role,
          PatternFamily.IsMatching pattern ∧
            PatternFamily.patternThreshold share ≤ pattern.card) ∨
        (∃ centre : ledger.Demand, ∃ pattern ⊆ ledger.roleFibre token role,
          PatternFamily.IsStar pattern centre ∧
            PatternFamily.patternThreshold share ≤ pattern.card)) := by
  obtain ⟨token, tokenMem, role, _display, _roleBound, forced, pattern⟩ :=
    ledger.exists_forced_pattern
  refine ⟨token, tokenMem, role, ?_⟩
  -- The share is at most the realized fibre, so `ψ` of it is at most `ψ` of the
  -- fibre, which the produced pattern already meets.
  have quotient : share ≤ (ledger.roleFibre token role).card := by
    refine Nat.le_of_mul_le_mul_left ?_ slots
    calc sameTokenRoleBound * ledger.tokens.card * share
        = share * (sameTokenRoleBound * ledger.tokens.card) := by ring
      _ ≤ ledger.forcedDemand := absorbs
      _ ≤ sameTokenRoleBound * ledger.tokens.card *
            (ledger.roleFibre token role).card := forced
  have monotone := PatternFamily.patternThreshold_mono quotient
  rcases pattern with ⟨sub, inside, matching, large⟩ | ⟨centre, sub, inside, star, large⟩
  · exact .inl ⟨sub, inside, matching, monotone.trans large⟩
  · exact .inr ⟨centre, sub, inside, star, monotone.trans large⟩

/-- The role-fibre excess `E_{t,r} = (ℓ(t,r) − b_C)_+` of
`cor:coupled-single-graph-overload-budget`, at the cap proposed for the token's
own grain. -/
def roleFibreExcess (grain : ledger.Token → Grain) (patternBound : Grain → Nat)
    (token : ledger.Token) (role : Role) : Nat :=
  (ledger.roleFibre token role).card -
    (patternBound (grain token) - 1) * (2 * patternBound (grain token) - 3)

/-- **`cor:coupled-single-graph-overload-budget` (a).**

  `Σ_{C,t,r} E_{t,r} ≥ D_all`.

The role fibres partition each token fibre, the tokens partition `Π_blk`, and
each of the `Q_st S_C` slots of class `C` is charged `b_C` before it overloads,
so the total charged capacity is exactly `A_all`. -/
theorem coupledExcess_le_sum_roleFibreExcess (grain : ledger.Token → Grain)
    (patternBound : Grain → Nat) :
    ledger.coupledExcess grain patternBound ≤
      ∑ token ∈ ledger.tokens, ∑ role : Role,
        ledger.roleFibreExcess grain patternBound token role := by
  classical
  -- The charged capacity, summed slot by slot, is the coupled capacity.
  have slotCapacity : ∀ token : ledger.Token,
      ∑ _role : Role,
          (patternBound (grain token) - 1) * (2 * patternBound (grain token) - 3) =
        homogeneousCapCharge (patternBound (grain token)) := by
    intro token
    rw [Finset.sum_const_nat fun _ _ => rfl, Finset.card_univ]
    rfl
  have capacityEq :
      ∑ token ∈ ledger.tokens, ∑ _role : Role,
          (patternBound (grain token) - 1) * (2 * patternBound (grain token) - 3) =
        ledger.coupledCapacity grain patternBound := by
    rw [Finset.sum_congr rfl fun token _ => slotCapacity token]
    exact ledger.sum_grain_weight grain fun value => homogeneousCapCharge (patternBound value)
  -- The realized load, summed slot by slot, is the blocked-pair count.
  have loadEq :
      ∑ token ∈ ledger.tokens, ∑ role : Role, (ledger.roleFibre token role).card =
        ledger.blocked.card := by
    rw [ledger.blocked_card_eq_sum_load]
    exact Finset.sum_congr rfl fun token _ => (ledger.load_eq_sum_roleFibre token).symm
  have superadditive : ∀ token : ledger.Token,
      (∑ role : Role, (ledger.roleFibre token role).card) -
          (∑ _role : Role,
            (patternBound (grain token) - 1) * (2 * patternBound (grain token) - 3)) ≤
        ∑ role : Role, ledger.roleFibreExcess grain patternBound token role :=
    fun token => sub_sum_le_sum_sub _ _ _
  have outer :
      (∑ token ∈ ledger.tokens, ∑ role : Role, (ledger.roleFibre token role).card) -
          (∑ token ∈ ledger.tokens, ∑ _role : Role,
            (patternBound (grain token) - 1) * (2 * patternBound (grain token) - 3)) ≤
        ∑ token ∈ ledger.tokens, ∑ role : Role,
          ledger.roleFibreExcess grain patternBound token role :=
    le_trans (sub_sum_le_sum_sub _ _ _) (Finset.sum_le_sum fun token _ => superadditive token)
  rw [loadEq, capacityEq] at outer
  have lower := ledger.forcedDemand_le_blocked
  unfold coupledExcess
  omega

/-- **`cor:coupled-single-graph-overload-budget` (b) and (c).**

The role-fibre slots number `Q_st |𝔗_cap|`, and if the coupled excess is
positive some slot absorbs its average share: a role fibre whose load exceeds
its own class threshold `b_C` by at least `D_all/(Q_st |𝔗_cap|)`.  That fibre
contains a role-homogeneous same-token matching or star of size `ψ` of its
load. -/
theorem exists_overloaded_roleFibre (grain : ledger.Token → Grain)
    (patternBound : Grain → Nat) :
    ∃ token ∈ ledger.tokens, ∃ role : Role,
      ledger.coupledExcess grain patternBound ≤
          sameTokenRoleBound * ledger.tokens.card *
            ledger.roleFibreExcess grain patternBound token role ∧
        ((∃ pattern ⊆ ledger.roleFibre token role,
            PatternFamily.IsMatching pattern ∧
              PatternFamily.patternThreshold (ledger.roleFibre token role).card ≤
                pattern.card) ∨
          (∃ centre : ledger.Demand, ∃ pattern ⊆ ledger.roleFibre token role,
            PatternFamily.IsStar pattern centre ∧
              PatternFamily.patternThreshold (ledger.roleFibre token role).card ≤
                pattern.card)) := by
  classical
  have tokensNonempty : ledger.tokens.Nonempty := ledger.orderNonempty
  obtain ⟨best, bestMem, bestMax⟩ :=
    Finset.exists_max_image (ledger.tokens ×ˢ (Finset.univ : Finset Role))
      (fun slot => ledger.roleFibreExcess grain patternBound slot.1 slot.2)
      (tokensNonempty.product Finset.univ_nonempty)
  have bestToken : best.1 ∈ ledger.tokens := (Finset.mem_product.mp bestMem).1
  have averaged :
      ∑ token ∈ ledger.tokens, ∑ role : Role,
          ledger.roleFibreExcess grain patternBound token role ≤
        (ledger.tokens ×ˢ (Finset.univ : Finset Role)).card *
          ledger.roleFibreExcess grain patternBound best.1 best.2 := by
    rw [← Finset.sum_product']
    calc ∑ slot ∈ ledger.tokens ×ˢ (Finset.univ : Finset Role),
            ledger.roleFibreExcess grain patternBound slot.1 slot.2
        ≤ ∑ _slot ∈ ledger.tokens ×ˢ (Finset.univ : Finset Role),
            ledger.roleFibreExcess grain patternBound best.1 best.2 :=
          Finset.sum_le_sum fun slot slotMem => bestMax slot slotMem
      _ = (ledger.tokens ×ˢ (Finset.univ : Finset Role)).card *
            ledger.roleFibreExcess grain patternBound best.1 best.2 := by
          rw [Finset.sum_const_nat fun _ _ => rfl, Nat.mul_comm]
  have slotCount : (ledger.tokens ×ˢ (Finset.univ : Finset Role)).card =
      sameTokenRoleBound * ledger.tokens.card := by
    rw [Finset.card_product, Finset.card_univ]
    exact Nat.mul_comm _ _
  rw [slotCount] at averaged
  refine ⟨best.1, bestToken, best.2, ?_, ?_⟩
  · exact le_trans (ledger.coupledExcess_le_sum_roleFibreExcess grain patternBound) averaged
  · exact PatternFamily.exists_matching_or_star_of_patternThreshold
      (ledger.roleFibre best.1 best.2) (ledger.pairs_roleFibre best.1 best.2)

/-! ## `prop:single-graph-sparse-pressure-routing`: the node-`[137]` branch test -/

/-- `R_L(n)`, the positive root of
`σ² − (1+log₂ n)σ − 2(C_E + Γ_max)n − 2log₂ n ≤ 0`, in the exact `Nat` form the
absorption step of `thm:tokenized-surplus-accounting-closure` produces: the
entropy budget is the demand-independent part and the uniform cap is the part
that scales with the demand family. -/
def sparsePressureBound (entropyBudget cap scale : Nat) : Nat :=
  1 + 2 * cap + Nat.sqrt (2 * entropyBudget + 2 * (cap * scale))

/-- **`prop:single-graph-sparse-pressure-routing` (a).**

If the coupled excess vanishes -- equivalently, the three proposed caps hold --
then `σ(G) ≤ R_L(n)`, which is the near-cubic route `[138]`. -/
theorem demand_le_sparsePressureBound (grain : ledger.Token → Grain)
    (patternBound : Grain → Nat) (cap scale : Nat)
    (uniform : ∀ value : Grain, homogeneousCapCharge (patternBound value) ≤ cap)
    (supply : ledger.tokens.card ≤ scale + demandCount)
    (balanced : ledger.coupledExcess grain patternBound = 0) :
    demandCount ≤ sparsePressureBound ledger.entropyBudget cap scale := by
  classical
  have capacityBound : ledger.coupledCapacity grain patternBound ≤
      cap * ledger.tokens.card := by
    calc ledger.coupledCapacity grain patternBound
        ≤ ∑ value : Grain, cap * (ledger.grainTokens grain value).card :=
          Finset.sum_le_sum fun value _ =>
            Nat.mul_le_mul_right _ (uniform value)
      _ = cap * ∑ value : Grain, (ledger.grainTokens grain value).card := by
          rw [Finset.mul_sum]
      _ = cap * ledger.tokens.card := by rw [ledger.sum_grainTokens_card grain]
  have forced : ledger.forcedDemand ≤ ledger.coupledCapacity grain patternBound := by
    unfold coupledExcess at balanced
    omega
  refine TokenLoad.demand_le_of_bounded_load demandCount ledger.entropyBudget cap
    ledger.tokens.card scale ?_ supply
  unfold forcedDemand at forced
  omega

/-- **`prop:single-graph-sparse-pressure-routing`, the exhaustive alternative.**

Either the survivor is bounded by `R_L(n)` and routes to node `[138]`, or the
coupled excess is positive and some role fibre overloads its own class
threshold, producing the role-homogeneous same-token pattern that nodes
`[140]`, `[142]`, `[143]` audit according to the grain of its token.  No graph
remains at `[137]`: the two alternatives are the two cases of `Nat`
trichotomy on `D_all`. -/
theorem sparsePressureAlternative (grain : ledger.Token → Grain)
    (patternBound : Grain → Nat) (cap scale : Nat)
    (uniform : ∀ value : Grain, homogeneousCapCharge (patternBound value) ≤ cap)
    (supply : ledger.tokens.card ≤ scale + demandCount) :
    demandCount ≤ sparsePressureBound ledger.entropyBudget cap scale ∨
      ∃ token ∈ ledger.tokens, ∃ role : Role,
        0 < ledger.coupledExcess grain patternBound ∧
          ledger.coupledExcess grain patternBound ≤
            sameTokenRoleBound * ledger.tokens.card *
              ledger.roleFibreExcess grain patternBound token role ∧
          ((∃ pattern ⊆ ledger.roleFibre token role,
              PatternFamily.IsMatching pattern ∧
                PatternFamily.patternThreshold (ledger.roleFibre token role).card ≤
                  pattern.card) ∨
            (∃ centre : ledger.Demand, ∃ pattern ⊆ ledger.roleFibre token role,
              PatternFamily.IsStar pattern centre ∧
                PatternFamily.patternThreshold (ledger.roleFibre token role).card ≤
                  pattern.card)) := by
  rcases Nat.eq_zero_or_pos (ledger.coupledExcess grain patternBound) with balanced | overload
  · exact .inl (ledger.demand_le_sparsePressureBound grain patternBound cap scale uniform
      supply balanced)
  · obtain ⟨token, tokenMem, role, excess, pattern⟩ :=
      ledger.exists_overloaded_roleFibre grain patternBound
    exact .inr ⟨token, tokenMem, role, overload, excess, pattern⟩

/-! ## `cor:numerical-single-graph-budget`: the coupled capacity at exact supplies

The corollary normalizes the classwise supplies by `n`.  In exact arithmetic it
is the identity below: the coupled capacity is `Q_st` times the cap-weighted sum
of the supplies, and the slot count is `Q_st` times their total.  Substituting
`lem:capacity-token-supply`'s `S_W = 15p₁₃ + σ_W`, `S_R = σ_R` and
`S_P = 4n + 2σ(G)` gives the manuscript's `Γ_L` and `Δ` verbatim, with no
constant written here. -/

/-- The coupled capacity is `Q_st` times the cap-weighted supply sum. -/
theorem coupledCapacity_eq (grain : ledger.Token → Grain) (patternBound : Grain → Nat) :
    ledger.coupledCapacity grain patternBound =
      sameTokenRoleBound *
        ∑ value : Grain,
          (patternBound value - 1) * (2 * patternBound value - 3) *
            (ledger.grainTokens grain value).card := by
  unfold coupledCapacity grainCapacity homogeneousCapCharge
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun value _ => by ring

/-- The role-fibre slot count is `Q_st` times the total token supply. -/
theorem slotCount_eq (grain : ledger.Token → Grain) :
    sameTokenRoleBound * ∑ value : Grain, (ledger.grainTokens grain value).card =
      sameTokenRoleBound * ledger.tokens.card := by
  rw [ledger.sum_grainTokens_card grain]

/-! ## The two granularities the manuscript uses -/

/-- **`thm:sharp-classwise-homogeneous-token-budget`**: the grouping is
`class(t) ∈ {W, R, P}`. -/
abbrev classTokens (value : TokenClass) : Finset ledger.Token :=
  ledger.grainTokens ledger.tokenClass value

/-- `B_C` at class granularity. -/
abbrev classLoad (value : TokenClass) : Nat :=
  ledger.grainLoad ledger.tokenClass value

/-- **`thm:sharp-surplus-overload-audit`**: the grouping is
`sub(t) ∈ {RW, WW, R, V, I, P}`. -/
abbrev subtypeTokens (value : TokenSubtype) : Finset ledger.Token :=
  ledger.grainTokens ledger.subtype value

/-- `B_u` at subtype granularity. -/
abbrev subtypeLoad (value : TokenSubtype) : Nat :=
  ledger.grainLoad ledger.subtype value

/-- **`thm:sharp-classwise-homogeneous-token-budget` (a) and (b) at the three
classes**: the class loads sum to `|Π_blk| ≥ N_*(G)` and the class supplies sum
to `|𝔗_cap|`. -/
theorem classwise_split :
    (∑ value : TokenClass, ledger.classLoad value = ledger.blocked.card ∧
        ledger.forcedDemand ≤ ledger.blocked.card) ∧
      ∑ value : TokenClass, (ledger.classTokens value).card = ledger.tokens.card :=
  ⟨⟨ledger.sum_grainLoad ledger.tokenClass, ledger.forcedDemand_le_blocked⟩,
    ledger.sum_grainTokens_card ledger.tokenClass⟩

/-- **`thm:sharp-surplus-overload-audit` (b) and (c) at the six subtypes**: the
subtype loads sum to `|Π_blk| ≥ N_*(G)`, and the subtype supplies sum to the
total token supply, whose `Q_st`-fold is the role-fibre slot count. -/
theorem subtype_split :
    (∑ value : TokenSubtype, ledger.subtypeLoad value = ledger.blocked.card ∧
        ledger.forcedDemand ≤ ledger.blocked.card) ∧
      ∑ value : TokenSubtype, (ledger.subtypeTokens value).card = ledger.tokens.card :=
  ⟨⟨ledger.sum_grainLoad ledger.subtype, ledger.forcedDemand_le_blocked⟩,
    ledger.sum_grainTokens_card ledger.subtype⟩

end CapacityTokenLedger

namespace TokenLoad

/-- **`cor:spine-lower-bound-surplus-estimates`, exact finite form.**

Each lower-bound package of `def:spine-lower-bound-deficits` bounds the pair
count of the active family, and the same absorption step that closes the
tokenized accounting converts that bound into a surplus estimate:

  `C(s,2) ≤ D`  gives  `s ≤ 1 + ⌊√(2D)⌋`.

At `D = D_win + ((1/2)σ+1)log₂ n` this is the manuscript's
`σ(G) = O(√(...) + log n)` with the implicit constant written out; the
near-cubic route `[138]` reads it off whichever package it carries. -/
theorem demand_le_of_package (demand package : Nat)
    (budget : demand.choose 2 ≤ package) :
    demand ≤ 1 + Nat.sqrt (2 * package) := by
  have quadratic : demand * (demand - 1) ≤ 2 * package + 0 * demand := by
    have pairs : 2 * demand.choose 2 = demand * (demand - 1) := by
      rw [Nat.choose_two_right, Nat.mul_comm]
      exact Nat.div_mul_cancel demand.even_mul_pred_self.two_dvd
    have doubled := Nat.mul_le_mul_left 2 budget
    omega
  have absorbed := le_one_add_of_quadratic_le demand (2 * package) 0 quadratic
  simpa using absorbed

end TokenLoad

end Hypostructure.Graph
