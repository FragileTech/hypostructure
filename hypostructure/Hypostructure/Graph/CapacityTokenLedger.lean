import Hypostructure.Graph.HomogeneousTokenCap
import Hypostructure.Graph.TokenLoadClosure
import Hypostructure.Graph.SparsePairLedger
import Hypostructure.Graph.SameTokenRoutingGerms

/-!
# A presented capacity-token ledger, and the three statements read off it

`def:capacity-token-ledger` charges every blocked active-demand pair to one
capacity token; `def:same-token-patterns` reads the charge fibre at a token as
the edge set of a graph `H_t` on the active family; `def:same-token-blocker-roles`
colours those edges by the finite alphabet `𝔕_st`.

The charge itself is **not** rebuilt here.  `Graph/CanonicalFibreLedger.lean` is
the single implementation of both of the manuscript's canonical ledgers, and this
structure is a presentation of *that* ledger: a declared token order, an
eligibility relation, and the pair schedule it charges.  `Π_blk`, `Π_free` and
`ℓ_cap(t)` are its `assigned`, `unassigned` and `multiplicity`, so
`lem:token-ledger-no-overcount` is read from it rather than proved again, and the
representation is the one rows 30--33 already use: a pair is a two-element
`Finset` of demands, exactly `CanonicalFibreLedger.pairs`.

What this module adds is what the manuscript deduces *from* the ledger:
`lem:capacity-token-high-load` with the role split and
`cor:forced-homogeneous-same-token-scale`; the three geometric class audits; and
`cor:homogeneous-same-token-caps-close` with
`thm:tokenized-surplus-accounting-closure`.

Nothing about graphs enters: `Demand` and `Token` are arbitrary types.
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.SameTokenBlockerRoles
open Hypostructure.Graph.CanonicalFibreLedger

universe u

/-- The free side of a presented ledger, spelled with the decidability the
presentation itself supplies.  A structure field cannot open a `letI`, so the
instances are threaded explicitly here and the field below reads this. -/
def freeSide {Demand Token : Type u} (demandDecidable : DecidableEq Demand)
    (schedule : Finset (Finset Demand)) (order : List Token)
    (Eligible : Token → Finset Demand → Prop)
    (eligibleDecidable : ∀ token pair, Decidable (Eligible token pair)) :
    Finset (Finset Demand) :=
  letI := demandDecidable
  letI := eligibleDecidable
  unassigned schedule order Eligible

/-- **A presented capacity-token ledger** over an active family of
`demandCount` surplus demands.

The fields are the canonical ledger's own data at a token alphabet -- the
declared order `𝔗_cap`, the eligibility relation whose first applicable label is
`Θ_cap`, and the pair schedule `Π(𝒜₀)` it charges -- together with
`def:same-token-blocker-roles`' role map and the entropy sandwich bound on the
free side. -/
structure CapacityTokenLedger (demandCount : Nat) where
  /-- The active surplus demands `𝒜₀`, the vertices of every `H_t`. -/
  Demand : Type u
  demandDecidable : DecidableEq Demand
  /-- The capacity-token universe `𝔗_cap`. -/
  Token : Type u
  tokenDecidable : DecidableEq Token
  /-- The declared token order.  "First applicable label" is what makes the
  charge canonical and single-valued. -/
  order : List Token
  orderNonempty : order.toFinset.Nonempty
  /-- `sub(t)`: which summand of `𝔗_cap = 𝔗_W ⊔ 𝔗_R ⊔ 𝔗_prim` a token lies in. -/
  subtype : Token → TokenSubtype
  /-- `Π(𝒜₀) = C(𝒜₀,2)`, the pairs the ledger charges. -/
  schedule : Finset (Finset Demand)
  /-- `|Π(𝒜₀)| = C(s,2)`. -/
  scheduleCard : schedule.card = demandCount.choose 2
  /-- A pair is a pair of *distinct* demands. -/
  schedulePairs : ∀ pair ∈ schedule, pair.card = 2
  /-- Eligibility; its first applicable label is `Θ_cap`. -/
  Eligible : Token → Finset Demand → Prop
  eligibleDecidable : ∀ token pair, Decidable (Eligible token pair)
  /-- `ρ_t`, the same-token role of a blocked pair. -/
  role : Finset Demand → Role
  /-- `E_spine(n) + ((1/2)σ+1)log₂ n`, the entropy sandwich budget. -/
  entropyBudget : Nat
  /-- `prop:sparse-entropy-sandwich-with-blockers` at this presentation. -/
  sandwich :
    (freeSide demandDecidable schedule order Eligible eligibleDecidable).card ≤
      entropyBudget

namespace CapacityTokenLedger

variable {demandCount : Nat} (ledger : CapacityTokenLedger.{u} demandCount)

instance : DecidableEq ledger.Demand := ledger.demandDecidable
instance : DecidableEq ledger.Token := ledger.tokenDecidable
instance (token : ledger.Token) (pair : Finset ledger.Demand) :
    Decidable (ledger.Eligible token pair) := ledger.eligibleDecidable token pair

/-- `𝔗_cap` as a finite set. -/
def tokens : Finset ledger.Token := ledger.order.toFinset

/-- `Π_blk`, the charged pairs: the canonical ledger's `assigned`. -/
def blocked : Finset (Finset ledger.Demand) :=
  assigned ledger.schedule ledger.order ledger.Eligible

/-- `Π_free`, the complementary pairs. -/
def free : Finset (Finset ledger.Demand) :=
  unassigned ledger.schedule ledger.order ledger.Eligible

/-- `ℓ_cap(t) = |Θ_cap^{-1}(t)|`: the canonical ledger's own `multiplicity`. -/
def load (token : ledger.Token) : Nat :=
  multiplicity ledger.schedule ledger.order ledger.Eligible token

/-- `H_t` of `def:same-token-patterns`: the pairs charged to one token. -/
def fibre (token : ledger.Token) : Finset (Finset ledger.Demand) :=
  ledger.schedule.filter fun pair =>
    canonicalLabel ledger.order ledger.Eligible pair = some token

theorem load_eq_card_fibre (token : ledger.Token) :
    ledger.load token = (ledger.fibre token).card := rfl

/-- `H_{t,r}` of `def:same-token-blocker-roles`: the role fibre at a token. -/
def roleFibre (token : ledger.Token) (value : Role) : Finset (Finset ledger.Demand) :=
  PatternFamily.roleFibre (ledger.fibre token) ledger.role value

/-- `class(t)`, read off the token's own subtype. -/
def tokenClass (token : ledger.Token) : TokenClass :=
  SameTokenBlockerRoles.tokenClass (ledger.subtype token)

theorem fibre_subset (token : ledger.Token) :
    ledger.fibre token ⊆ ledger.schedule :=
  Finset.filter_subset _ _

theorem pairs_fibre (token : ledger.Token) :
    ∀ pair ∈ ledger.fibre token, pair.card = 2 :=
  fun pair member => ledger.schedulePairs pair (ledger.fibre_subset token member)

theorem pairs_roleFibre (token : ledger.Token) (value : Role) :
    ∀ pair ∈ ledger.roleFibre token value, pair.card = 2 :=
  fun pair member =>
    ledger.pairs_fibre token pair (PatternFamily.roleFibre_subset _ _ _ member)

/-- **`lem:token-ledger-no-overcount`, read from the canonical ledger**:
`|Π_blk| = Σ_t ℓ_cap(t)`.  Nothing is re-proved; this is
`CanonicalFibreLedger.card_assigned_eq_sum_multiplicity` at a token alphabet. -/
theorem blocked_card_eq_sum_load :
    ledger.blocked.card = ∑ token ∈ ledger.tokens, ledger.load token :=
  card_assigned_eq_sum_multiplicity ledger.schedule ledger.order ledger.Eligible

/-- The entropy sandwich at the ledger's own free side.  The structure field is
spelled through `freeSide`, which is `unassigned` with the presentation's own
instances; this is that field with the spelling normalized. -/
theorem free_card_le_entropyBudget : ledger.free.card ≤ ledger.entropyBudget :=
  ledger.sandwich

/-- **The split is exhaustive**: `|Π_blk| + |Π_free| = |Π(𝒜₀)| = C(s,2)`. -/
theorem blocked_card_add_free_card :
    ledger.blocked.card + ledger.free.card = demandCount.choose 2 := by
  rw [← ledger.scheduleCard]
  exact card_assigned_add_card_unassigned ledger.schedule ledger.order ledger.Eligible

/-- **The role-fibre partition of `def:same-token-blocker-roles`**:
`ℓ_cap(t) = Σ_{r ∈ 𝔕_st} ℓ(t,r)`, over the whole declared alphabet. -/
theorem load_eq_sum_roleFibre (token : ledger.Token) :
    ledger.load token = ∑ value : Role, (ledger.roleFibre token value).card :=
  PatternFamily.card_eq_sum_roleFibre (ledger.fibre token) ledger.role Finset.univ
    fun _ _ => Finset.mem_univ _

/-- **`lem:capacity-token-high-load`, at the token that realizes `L_max`.**

  `C(s,2) ≤ E_spine(n) + ((1/2)σ+1)log₂ n + L_max|𝔗_cap|`.

The free part is spent against the entropy budget and the charged part against
the canonical ledger's own fibre identity, exactly as the manuscript's proof
does. -/
theorem exists_high_load :
    ∃ token ∈ ledger.tokens,
      demandCount.choose 2 ≤
        ledger.entropyBudget + ledger.tokens.card * ledger.load token := by
  obtain ⟨token, tokenMem, bound⟩ :=
    TokenLoad.exists_multiplicity_ge ledger.schedule ledger.order ledger.Eligible
      ledger.orderNonempty
  refine ⟨token, tokenMem, ?_⟩
  have split := ledger.blocked_card_add_free_card
  have sandwichLe := ledger.free_card_le_entropyBudget
  have blockedEq : ledger.blocked.card =
      (assigned ledger.schedule ledger.order ledger.Eligible).card := rfl
  have loadEq : ledger.tokens.card * ledger.load token =
      ledger.order.toFinset.card *
        multiplicity ledger.schedule ledger.order ledger.Eligible token := rfl
  omega

/-- **`cor:forced-homogeneous-same-token-scale`.**

Some capacity token carries the whole high-load display, one of its role fibres
carries at least a `Q_st`-th of its load, and that role fibre contains a matching
or a star of size `ψ(ℓ(t,r))`.  Because every member of a role fibre has the same
role, the pattern produced is role-homogeneous. -/
theorem exists_forced_homogeneous_pattern :
    ∃ token ∈ ledger.tokens,
      demandCount.choose 2 ≤
          ledger.entropyBudget + ledger.tokens.card * ledger.load token ∧
        ∃ value : Role,
          ledger.load token ≤ sameTokenRoleBound * (ledger.roleFibre token value).card ∧
            ((∃ pattern ⊆ ledger.roleFibre token value,
                PatternFamily.IsMatching pattern ∧
                  PatternFamily.patternThreshold (ledger.roleFibre token value).card ≤
                    pattern.card) ∨
              (∃ centre : ledger.Demand, ∃ pattern ⊆ ledger.roleFibre token value,
                PatternFamily.IsStar pattern centre ∧
                  PatternFamily.patternThreshold (ledger.roleFibre token value).card ≤
                    pattern.card)) := by
  obtain ⟨token, tokenMem, display⟩ := ledger.exists_high_load
  obtain ⟨value, _, large⟩ :=
    PatternFamily.exists_large_roleFibre (ledger.fibre token) ledger.role Finset.univ
      Finset.univ_nonempty fun _ _ => Finset.mem_univ _
  refine ⟨token, tokenMem, display, value, ?_, ?_⟩
  · rw [ledger.load_eq_card_fibre, ← card_univ_eq_sameTokenRoleBound]
    exact large
  · exact PatternFamily.exists_matching_or_star_of_patternThreshold
      (ledger.roleFibre token value) (ledger.pairs_roleFibre token value)

/-- **The three geometric audits `[140]`, `[142]`, `[143]`.**

A token whose load exceeds `Cap_hom(L)` for the pattern bound registered at its
own token class carries a role-homogeneous `L`-matching or `L`-star.  This is the
contrapositive of the cap step: if no role fibre carried one, summing
`lem:same-token-matching-star` over the `Q_st` role fibres would bound the load by
`Cap_hom(L)`.

The three classes are audited by one statement at shared parameters -- the bound
is a function of the token's class and the ledger is one presentation -- which is
what makes the test coupled. -/
theorem exists_homogeneous_pattern_of_capCharge_lt
    (patternBound : TokenClass → Nat) (token : ledger.Token)
    (positive : 1 ≤ patternBound (ledger.tokenClass token))
    (overloaded : homogeneousCapCharge (patternBound (ledger.tokenClass token)) <
      ledger.load token) :
    ∃ value : Role,
      (∃ pattern ⊆ ledger.roleFibre token value,
          PatternFamily.IsMatching pattern ∧
            patternBound (ledger.tokenClass token) ≤ pattern.card) ∨
        (∃ centre : ledger.Demand, ∃ pattern ⊆ ledger.roleFibre token value,
          PatternFamily.IsStar pattern centre ∧
            patternBound (ledger.tokenClass token) ≤ pattern.card) := by
  by_contra none
  have bounded :=
    PatternFamily.card_le_capCharge (ledger.fibre token) ledger.role Finset.univ
      (patternBound (ledger.tokenClass token)) positive
      (ledger.pairs_fibre token) (fun _ _ => Finset.mem_univ _)
      (fun value _ => by
        rintro ⟨pattern, inside, matching, large⟩
        exact none ⟨value, .inl ⟨pattern, inside, matching, large⟩⟩)
      (fun value _ => by
        rintro ⟨centre, pattern, inside, star, large⟩
        exact none ⟨value, .inr ⟨centre, pattern, inside, star, large⟩⟩)
  rw [card_univ_eq_sameTokenRoleBound, ← homogeneousCapCharge_eq_capCharge] at bounded
  rw [ledger.load_eq_card_fibre] at overloaded
  exact absurd bounded (Nat.not_le.mpr overloaded)

/-- **`cor:homogeneous-same-token-caps-close`.**

Fixed pattern bounds `L_W, L_R, L_P` for the three token classes, none of which
is realized by a role-homogeneous same-token matching or star, force every token
load below `M₀ = max_C Cap_hom(L_C)`; the canonical ledger's identity then bounds
`|Π_blk|` by `M₀|𝔗_cap|`, and `thm:tokenized-surplus-accounting-closure` turns
that into the square-root bound on the active family.

The manuscript's `σ(G) = O(√n)` appears with its implicit constant written out:
at `|𝔗_cap| ≤ 8n + σ(G)` the parameter `scale` is `8n`, so the conclusion reads
`σ(G) ≤ 1 + 2M₀ + √(2E + 16M₀n)`. -/
theorem caps_close
    (patternBound : TokenClass → Nat) (cap scale : Nat)
    (positive : ∀ class' : TokenClass, 1 ≤ patternBound class')
    (uniform : ∀ class' : TokenClass, homogeneousCapCharge (patternBound class') ≤ cap)
    (supply : ledger.tokens.card ≤ scale + demandCount)
    (noHomogeneousMatching : ∀ token ∈ ledger.tokens, ∀ value : Role,
      ¬ ∃ pattern ⊆ ledger.roleFibre token value,
        PatternFamily.IsMatching pattern ∧
          patternBound (ledger.tokenClass token) ≤ pattern.card)
    (noHomogeneousStar : ∀ token ∈ ledger.tokens, ∀ value : Role,
      ¬ ∃ centre : ledger.Demand, ∃ pattern ⊆ ledger.roleFibre token value,
        PatternFamily.IsStar pattern centre ∧
          patternBound (ledger.tokenClass token) ≤ pattern.card) :
    (∀ token ∈ ledger.tokens, ledger.load token ≤ cap) ∧
      ledger.blocked.card ≤ cap * ledger.tokens.card ∧
      demandCount ≤ 1 + 2 * cap +
        Nat.sqrt (2 * ledger.entropyBudget + 2 * (cap * scale)) := by
  have loads : ∀ token ∈ ledger.tokens, ledger.load token ≤ cap := by
    intro token tokenMem
    have bounded :=
      PatternFamily.card_le_capCharge (ledger.fibre token) ledger.role Finset.univ
        (patternBound (ledger.tokenClass token)) (positive _)
        (ledger.pairs_fibre token) (fun _ _ => Finset.mem_univ _)
        (fun value _ => noHomogeneousMatching token tokenMem value)
        (fun value _ => noHomogeneousStar token tokenMem value)
    rw [card_univ_eq_sameTokenRoleBound, ← homogeneousCapCharge_eq_capCharge] at bounded
    rw [ledger.load_eq_card_fibre]
    exact le_trans bounded (uniform _)
  have ledgerBound : ledger.blocked.card ≤ cap * ledger.tokens.card :=
    TokenLoad.card_assigned_le_mul_of_multiplicity_le ledger.schedule ledger.order
      ledger.Eligible cap loads
  refine ⟨loads, ledgerBound, ?_⟩
  refine TokenLoad.demand_le_of_bounded_load demandCount ledger.entropyBudget cap
    ledger.tokens.card scale ?_ supply
  have split := ledger.blocked_card_add_free_card
  have sandwichLe := ledger.free_card_le_entropyBudget
  omega

end CapacityTokenLedger

/-! ## The ledger presented at an object's own pair schedule

`[136]`'s token ledger charges the pair schedule `[130]` built, so a consumer
does not choose a demand family: it is `FiniteObject.portPairSchedule`, and its
cardinality is the fact node `[130]` commits.  The constructor below is the only
way the spine presents a capacity-token ledger, and it takes that cardinality as
an argument precisely so that the caller must have read it. -/

/-- Every member of a canonical pair family is a pair. -/
theorem card_of_mem_pairs {Demand : Type u} [DecidableEq Demand]
    {family : Finset Demand} {pair : Finset Demand}
    (member : pair ∈ CanonicalFibreLedger.pairs family) : pair.card = 2 :=
  (Finset.mem_powersetCard.mp member).2

/-- Every member of an object's own port-pair schedule is a pair. -/
theorem card_of_mem_portPairSchedule (object : FiniteObject.{u}) (threshold : Nat)
    {pair : Finset (object.Vertex × object.Vertex)}
    (member : pair ∈ object.portPairSchedule threshold) : pair.card = 2 := by
  letI := object.vertexPairDecidableEq
  exact card_of_mem_pairs member

namespace CapacityTokenLedger

/-- **The capacity-token ledger of an object, at its own pair schedule.**

`schedule` is `FiniteObject.portPairSchedule`, and `scheduleCard` is node
`[130]`'s committed `|Π(𝒜₀)| = C(σ(G),2)`: the caller supplies it, which is what
makes this a ledger *read* off the branch rather than one invented at the node.
Everything else -- the declared token order, the eligibility whose first
applicable label is `Θ_cap`, the role map, and the entropy budget with its
sandwich -- is the presentation the node is quantified over. -/
noncomputable def ofPortSchedule (object : FiniteObject.{u}) (threshold demandCount : Nat)
    (scheduleCard :
      (object.portPairSchedule threshold).card = demandCount.choose 2)
    {Token : Type u} (tokenDecidable : DecidableEq Token) (order : List Token)
    (orderNonempty : order.toFinset.Nonempty)
    (subtype : Token → TokenSubtype)
    (Eligible : Token → Finset (object.Vertex × object.Vertex) → Prop)
    (eligibleDecidable : ∀ token pair, Decidable (Eligible token pair))
    (role : Finset (object.Vertex × object.Vertex) → Role)
    (entropyBudget : Nat)
    (sandwich :
      (freeSide (object.vertexPairDecidableEq) (object.portPairSchedule threshold)
        order Eligible eligibleDecidable).card ≤ entropyBudget) :
    CapacityTokenLedger.{u} demandCount where
  Demand := object.Vertex × object.Vertex
  demandDecidable := object.vertexPairDecidableEq
  Token := Token
  tokenDecidable := tokenDecidable
  order := order
  orderNonempty := orderNonempty
  subtype := subtype
  schedule := object.portPairSchedule threshold
  scheduleCard := scheduleCard
  schedulePairs := fun _pair member => card_of_mem_portPairSchedule object threshold member
  Eligible := Eligible
  eligibleDecidable := eligibleDecidable
  role := role
  entropyBudget := entropyBudget
  sandwich := sandwich

end CapacityTokenLedger

/-- **`thm:homogeneous-overload-geometric-closure`, second assertion.**

"On the subbranch in which sparse surplus exits are absent and all decorated
Type B handoff data have been routed into the Type B fan ledger, the three fixed
homogeneous caps `L_W = L_R = L_P = L_geom` hold.  On that subbranch,
`σ(G) = O(√n)`."

This is `cor:homogeneous-same-token-caps-close` at the manuscript's own fixed
cap: `L_geom = Q_geom + 1` for the counted routing-label alphabet of
`def:same-token-routing-germs`, and `M₀ = Cap_hom(L_geom)`.  Nothing is assumed
beyond the corollary's own clauses (a), (b), (c), which are the subbranch
hypothesis stated at that cap.

The theorem's *first* assertion -- that every role-homogeneous
`L_geom`-pattern realizes a sparse surplus exit or produces decorated Type B
handoff fan data -- is `lem:same-token-bottleneck-routing`, and it is not stated
anywhere in this tree.  The edge-count half `m = (3/2)n + O(√n)` is not stated
either; it would follow from this bound and `lem:sparse-slack-surplus`, which
node `[126]` carries. -/
theorem CapacityTokenLedger.caps_close_at_geometricBound
    {demandCount : Nat} (ledger : CapacityTokenLedger.{u} demandCount)
    (Label : Type) [Fintype Label]
    (scale : Nat) (supply : ledger.tokens.card ≤ scale + demandCount)
    (noHomogeneousMatching : ∀ token ∈ ledger.tokens, ∀ value : Role,
      ¬ ∃ pattern ⊆ ledger.roleFibre token value,
        PatternFamily.IsMatching pattern ∧
          SameTokenRoutingGerms.patternBound Label ≤ pattern.card)
    (noHomogeneousStar : ∀ token ∈ ledger.tokens, ∀ value : Role,
      ¬ ∃ centre : ledger.Demand, ∃ pattern ⊆ ledger.roleFibre token value,
        PatternFamily.IsStar pattern centre ∧
          SameTokenRoutingGerms.patternBound Label ≤ pattern.card) :
    (∀ token ∈ ledger.tokens, ledger.load token ≤
        homogeneousCapCharge
          (SameTokenRoutingGerms.patternBound Label)) ∧
      ledger.blocked.card ≤
        homogeneousCapCharge
            (SameTokenRoutingGerms.patternBound Label) *
          ledger.tokens.card ∧
      demandCount ≤ 1 + 2 * homogeneousCapCharge
          (SameTokenRoutingGerms.patternBound Label) +
        Nat.sqrt (2 * ledger.entropyBudget +
          2 * (homogeneousCapCharge
            (SameTokenRoutingGerms.patternBound Label) *
              scale)) :=
  ledger.caps_close
    (fun _ => SameTokenRoutingGerms.patternBound Label)
    (homogeneousCapCharge
      (SameTokenRoutingGerms.patternBound Label))
    scale
    (fun _ => SameTokenRoutingGerms.one_le_patternBound Label)
    (fun _ => Nat.le_refl _) supply noHomogeneousMatching noHomogeneousStar

end Hypostructure.Graph
