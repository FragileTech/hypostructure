import Hypostructure.Graph.HomogeneousTokenCap
import Hypostructure.Graph.TokenLoadClosure

/-!
# A presented capacity-token ledger, and the three statements read off it

`def:capacity-token-ledger` charges every blocked active-demand pair to one
capacity token; `def:same-token-patterns` reads the charge fibre at a token as
the edge set of a graph `H_t` on the active family; `def:same-token-blocker-roles`
colours those edges by the finite alphabet `𝔕_st`.  This module bundles exactly
that data -- a finite token universe with its subtypes, a finite family of
blocked pairs, the charge map, the role map, and the free/blocked split of the
pair set against an entropy budget -- and proves the three statements the
manuscript reads off it:

* `lem:capacity-token-high-load`, the coupled high-load display

    `C(s,2) ≤ E_spine(n) + ((1/2)σ+1)log₂ n + L_max|𝔗_cap|`,

  together with `def:same-token-blocker-roles`' role-fibre partition and
  `cor:forced-homogeneous-same-token-scale`'s forced role-homogeneous pattern
  of size `ψ(ℓ(t,r))`;

* the three geometric audits `[140]`, `[142]`, `[143]`: a token whose load
  exceeds `Cap_hom(L)` for its own class's pattern bound carries a
  role-homogeneous `L`-matching or `L`-star;

* `cor:homogeneous-same-token-caps-close`: fixed caps `L_W, L_R, L_P` for the
  three token classes bound every token load by `M₀ = max_C Cap_hom(L_C)`, and
  `thm:tokenized-surplus-accounting-closure` turns that into `σ(G) = O(√n)`.

The ledger is *presented*, not constructed: this module does not build `𝔗_cap`,
does not define `Θ_cap`, and does not know how the free pairs were charged.
Those are the content of `def:capacity-token-ledger` and
`prop:sparse-entropy-sandwich-with-blockers`, and a consumer supplies them.
What is proved here is everything the manuscript deduces *from* the
presentation, and nothing about graphs enters: `Demand` and `Token` are
arbitrary types.
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.SameTokenBlockerRoles

universe u

/-- **A presented capacity-token ledger** over an active family of
`demandCount` surplus demands.

The fields are `def:capacity-token-ledger`'s data (`𝔗_cap` with its subtypes,
`Θ_cap`, `Π_blk`), `def:same-token-blocker-roles`' role map `ρ`, and the
canonical ledger's own free/blocked split of `C(𝒜₀,2)` together with the
entropy sandwich bound on the free part. -/
structure CapacityTokenLedger (demandCount : Nat) where
  /-- The active surplus demands `𝒜₀`, the vertices of every `H_t`. -/
  Demand : Type u
  demandDecidable : DecidableEq Demand
  /-- The capacity-token universe `𝔗_cap`. -/
  Token : Type u
  tokenDecidable : DecidableEq Token
  /-- The enumerated token universe. -/
  tokens : Finset Token
  tokensNonempty : tokens.Nonempty
  /-- `sub(t)`: which summand of `𝔗_cap = 𝔗_W ⊔ 𝔗_R ⊔ 𝔗_prim` a token lies in. -/
  subtype : Token → TokenSubtype
  /-- `Π_blk`, the blocked pairs of `C(𝒜₀,2)`. -/
  blocked : Finset (Sym2 Demand)
  /-- A pair of demands is a pair of *distinct* demands. -/
  nondiagonal : ∀ pattern ∈ blocked, ¬ pattern.IsDiag
  /-- `Θ_cap`, the canonical charge map. -/
  charge : Sym2 Demand → Token
  chargeDeclared : ∀ pattern ∈ blocked, charge pattern ∈ tokens
  /-- `ρ_t`, the same-token role of a blocked pair. -/
  role : Sym2 Demand → Role
  /-- `|Π_free|`. -/
  free : Nat
  /-- The canonical ledger's partition `C(𝒜₀,2) = Π_free ⊔ Π_blk`. -/
  split : demandCount.choose 2 = free + blocked.card
  /-- `E_spine(n) + ((1/2)σ+1)log₂ n`, the entropy sandwich budget. -/
  entropyBudget : Nat
  /-- `prop:sparse-entropy-sandwich-with-blockers` at this presentation. -/
  sandwich : free ≤ entropyBudget

namespace CapacityTokenLedger

variable {demandCount : Nat} (ledger : CapacityTokenLedger.{u} demandCount)

instance : DecidableEq ledger.Demand := ledger.demandDecidable
instance : DecidableEq ledger.Token := ledger.tokenDecidable

/-- `H_t` of `def:same-token-patterns`: the pairs charged to one token. -/
def fibre (token : ledger.Token) : Finset (Sym2 ledger.Demand) :=
  TokenLoad.fibre ledger.blocked ledger.charge token

/-- `ℓ_cap(t) = e(H_t)`. -/
def load (token : ledger.Token) : Nat := (ledger.fibre token).card

/-- `H_{t,r}` of `def:same-token-blocker-roles`: the role fibre at a token. -/
def roleFibre (token : ledger.Token) (value : Role) : Finset (Sym2 ledger.Demand) :=
  PatternFamily.roleFibre (ledger.fibre token) ledger.role value

/-- `class(t)`, read off the token's own subtype. -/
def tokenClass (token : ledger.Token) : TokenClass :=
  SameTokenBlockerRoles.tokenClass (ledger.subtype token)

theorem fibre_subset (token : ledger.Token) : ledger.fibre token ⊆ ledger.blocked :=
  TokenLoad.fibre_subset _ _ _

theorem nondiagonal_fibre (token : ledger.Token) :
    ∀ pattern ∈ ledger.fibre token, ¬ pattern.IsDiag :=
  fun pattern patternMem => ledger.nondiagonal pattern (ledger.fibre_subset token patternMem)

theorem nondiagonal_roleFibre (token : ledger.Token) (value : Role) :
    ∀ pattern ∈ ledger.roleFibre token value, ¬ pattern.IsDiag :=
  fun pattern patternMem =>
    ledger.nondiagonal_fibre token pattern
      (PatternFamily.roleFibre_subset _ _ _ patternMem)

/-- **`lem:token-ledger-no-overcount`** at this presentation:
`|Π_blk| = Σ_t ℓ_cap(t)`. -/
theorem blocked_card_eq_sum_load :
    ledger.blocked.card = ∑ token ∈ ledger.tokens, ledger.load token :=
  TokenLoad.card_eq_sum_load ledger.blocked ledger.tokens ledger.charge ledger.chargeDeclared

/-- **The role-fibre partition of `def:same-token-blocker-roles`**:
`ℓ_cap(t) = Σ_{r ∈ 𝔕_st} ℓ(t,r)`, over the whole declared alphabet. -/
theorem load_eq_sum_roleFibre (token : ledger.Token) :
    ledger.load token =
      ∑ value : Role, (ledger.roleFibre token value).card :=
  PatternFamily.card_eq_sum_roleFibre (ledger.fibre token) ledger.role Finset.univ
    fun _ _ => Finset.mem_univ _

/-- **`lem:capacity-token-high-load`, at the token that realizes `L_max`.**

  `C(s,2) ≤ E_spine(n) + ((1/2)σ+1)log₂ n + L_max|𝔗_cap|`.

The free part is spent against the entropy budget and the blocked part against
the fibre partition, exactly as the manuscript's proof does. -/
theorem exists_high_load :
    ∃ token ∈ ledger.tokens,
      demandCount.choose 2 ≤
        ledger.entropyBudget + ledger.tokens.card * ledger.load token := by
  obtain ⟨token, tokenMem, bound⟩ :=
    TokenLoad.exists_load_ge ledger.blocked ledger.tokens ledger.charge
      ledger.tokensNonempty ledger.chargeDeclared
  refine ⟨token, tokenMem, ?_⟩
  have splitEq := ledger.split
  have sandwichLe := ledger.sandwich
  omega

/-- **`cor:forced-homogeneous-same-token-scale`.**

Some capacity token carries the whole high-load display, its role fibres
partition its load, one of those role fibres carries at least a `Q_st`-th of
it, and that role fibre contains a matching or a star of size
`ψ(ℓ(t,r))`.  Because every member of a role fibre has the same role, the
pattern produced is role-homogeneous. -/
theorem exists_forced_homogeneous_pattern :
    ∃ token ∈ ledger.tokens,
      demandCount.choose 2 ≤
          ledger.entropyBudget + ledger.tokens.card * ledger.load token ∧
        ledger.load token = ∑ value : Role, (ledger.roleFibre token value).card ∧
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
  refine ⟨token, tokenMem, display, ledger.load_eq_sum_roleFibre token, value, ?_, ?_⟩
  · rwa [← card_univ_eq_sameTokenRoleBound]
  · exact PatternFamily.exists_matching_or_star_of_patternThreshold
      (ledger.roleFibre token value) (ledger.nondiagonal_roleFibre token value)

/-- **The three geometric audits `[140]`, `[142]`, `[143]`.**

A token whose load exceeds `Cap_hom(L)` for the pattern bound registered at its
own token class carries a role-homogeneous `L`-matching or `L`-star.  This is
the contrapositive of the cap step: if no role fibre carried one, summing
`lem:same-token-matching-star` over the `Q_st` role fibres would bound the load
by `Cap_hom(L)`.

The three classes are audited by one statement at shared parameters -- the
bound is a function of the token's class and the ledger is one presentation --
which is what makes the test coupled. -/
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
      (ledger.nondiagonal_fibre token) (fun _ _ => Finset.mem_univ _)
      (fun value _ => by
        rintro ⟨pattern, inside, matching, large⟩
        exact none ⟨value, .inl ⟨pattern, inside, matching, large⟩⟩)
      (fun value _ => by
        rintro ⟨centre, pattern, inside, star, large⟩
        exact none ⟨value, .inr ⟨centre, pattern, inside, star, large⟩⟩)
  rw [card_univ_eq_sameTokenRoleBound,
    ← homogeneousCapCharge_eq_capCharge] at bounded
  exact absurd bounded (Nat.not_le.mpr overloaded)

/-- **`cor:homogeneous-same-token-caps-close`.**

Fixed pattern bounds `L_W, L_R, L_P` for the three token classes, none of which
is realized by a role-homogeneous same-token matching or star, force every
token load below `M₀ = max_C Cap_hom(L_C)`; the ledger identity then bounds
`|Π_blk|` by `M₀|𝔗_cap|`, and
`thm:tokenized-surplus-accounting-closure` turns that into the square-root
bound on the active family.

The manuscript's `σ(G) = O(√n)` appears with its implicit constant written
out: at the manuscript's `|𝔗_cap| ≤ 8n + σ(G)` the parameter `scale` is `8n`,
so the conclusion reads `σ(G) ≤ 1 + 2M₀ + √(2E + 16M₀n)`. -/
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
        (ledger.nondiagonal_fibre token) (fun _ _ => Finset.mem_univ _)
        (fun value _ => noHomogeneousMatching token tokenMem value)
        (fun value _ => noHomogeneousStar token tokenMem value)
    rw [card_univ_eq_sameTokenRoleBound, ← homogeneousCapCharge_eq_capCharge] at bounded
    exact le_trans bounded (uniform _)
  have ledgerBound : ledger.blocked.card ≤ cap * ledger.tokens.card :=
    TokenLoad.card_le_mul_of_load_le ledger.blocked ledger.tokens ledger.charge cap
      ledger.chargeDeclared loads
  refine ⟨loads, ledgerBound, ?_⟩
  refine TokenLoad.demand_le_of_bounded_load demandCount ledger.entropyBudget cap
    ledger.tokens.card scale ?_ supply
  have splitEq := ledger.split
  have sandwichLe := ledger.sandwich
  omega

end CapacityTokenLedger

end Hypostructure.Graph
