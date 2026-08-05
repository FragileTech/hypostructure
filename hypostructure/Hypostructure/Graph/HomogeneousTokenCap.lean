import Hypostructure.Graph.MatchingStar
import Hypostructure.Graph.SameTokenBlockerRoles

/-!
# Role fibres, homogeneous extraction, and the homogeneous cap charge

`def:same-token-blocker-roles` colours the pairs charged to one token by a
finite role alphabet and observes that the role fibres partition the token's
fibre, so

  `ℓ_cap(t) = Σ_{r ∈ 𝔕_st} ℓ(t,r)`.

`lem:same-token-homogeneous-extraction` is the pigeonhole that follows: a
same-token `K`-matching or `K`-star contains a role-homogeneous one of size at
least `⌈K/Q_st⌉`, because a colour class of a matching is a matching and a
colour class of a star is a star with the same centre.

`def:homogeneous-token-charge` records the cap the two facts license:

  `Cap_hom(L) := Q_st(L−1)(2L−3)`,

"the uniform token load allowed by charging each of the at most `Q_st` role
fibres separately when no role-homogeneous same-token `L`-matching or `L`-star
occurs at that token".  The theorem below is that sentence: it charges each
role fibre by `lem:same-token-matching-star` and sums the partition.  This is
the cap step of `cor:homogeneous-same-token-caps-close`'s proof, and the
`Q_st` of the manuscript enters only as the size of the caller's own role
alphabet.

Every statement is about an arbitrary finite family of unordered pairs under an
arbitrary finite colouring.  The ceiling `⌈K/Q⌉` is written multiplicatively as
`K ≤ Q · |class|`, which is the same statement without a division.
-/

namespace Hypostructure.Graph.PatternFamily

open scoped BigOperators

universe u w

variable {V : Type u} [DecidableEq V] {Role : Type w} [DecidableEq Role]

/-- **The role fibre at a colour**: the members of the family carrying it. -/
def roleFibre (family : Finset (Sym2 V)) (role : Sym2 V → Role) (value : Role) :
    Finset (Sym2 V) :=
  family.filter fun edge => role edge = value

omit [DecidableEq V] in
theorem roleFibre_subset (family : Finset (Sym2 V)) (role : Sym2 V → Role)
    (value : Role) : roleFibre family role value ⊆ family :=
  Finset.filter_subset _ _

omit [DecidableEq V] in
theorem roleFibre_mono {family sub : Finset (Sym2 V)} (role : Sym2 V → Role)
    (value : Role) (inside : sub ⊆ family) :
    roleFibre sub role value ⊆ roleFibre family role value := by
  intro edge edgeMem
  have := Finset.mem_filter.mp edgeMem
  exact Finset.mem_filter.mpr ⟨inside this.1, this.2⟩

omit [DecidableEq V] in
/-- **The role-fibre partition of `def:same-token-blocker-roles`.**

  `ℓ_cap(t) = Σ_{r ∈ 𝔕_st} ℓ(t,r)`

at any family whose colours all lie in the declared alphabet. -/
theorem card_eq_sum_roleFibre (family : Finset (Sym2 V)) (role : Sym2 V → Role)
    (roles : Finset Role) (declared : ∀ edge ∈ family, role edge ∈ roles) :
    family.card = ∑ value ∈ roles, (roleFibre family role value).card :=
  Finset.card_eq_sum_card_fiberwise declared

/-- **`Cap_hom(L)`** of `def:homogeneous-token-charge`, with the role bound a
parameter rather than a numeral: the caller's own alphabet supplies `Q_st`. -/
def capCharge (roleBound patternBound : Nat) : Nat :=
  roleBound * ((patternBound - 1) * (2 * patternBound - 3))

/-- **The cap step of `cor:homogeneous-same-token-caps-close`.**

If no role fibre carries a matching of size `L` or a star of size `L`, then the
whole family has at most `Cap_hom(L)` members.  The manuscript's proof exactly:
`lem:same-token-matching-star` charges each fibre by `(L−1)(2L−3)`, and the
role-fibre partition sums those charges over the at most `Q_st` roles. -/
theorem card_le_capCharge (family : Finset (Sym2 V)) (role : Sym2 V → Role)
    (roles : Finset Role) (size : Nat) (positive : 1 ≤ size)
    (nondiagonal : ∀ edge ∈ family, ¬ edge.IsDiag)
    (declared : ∀ edge ∈ family, role edge ∈ roles)
    (noHomogeneousMatching : ∀ value ∈ roles,
      ¬ ∃ sub ⊆ roleFibre family role value, IsMatching sub ∧ size ≤ sub.card)
    (noHomogeneousStar : ∀ value ∈ roles,
      ¬ ∃ centre : V, ∃ sub ⊆ roleFibre family role value,
        IsStar sub centre ∧ size ≤ sub.card) :
    family.card ≤ capCharge roles.card size := by
  classical
  calc family.card
      = ∑ value ∈ roles, (roleFibre family role value).card :=
        card_eq_sum_roleFibre family role roles declared
    _ ≤ ∑ _value ∈ roles, (size - 1) * (2 * size - 3) := by
        refine Finset.sum_le_sum fun value valueMem => ?_
        exact card_le_of_no_matching_no_star _ size positive
          (fun edge edgeMem =>
            nondiagonal edge (roleFibre_subset family role value edgeMem))
          (noHomogeneousMatching value valueMem)
          (noHomogeneousStar value valueMem)
    _ = capCharge roles.card size := by
        rw [Finset.sum_const, smul_eq_mul, capCharge]

/-- The colour class of a family, chosen to be as large as the pigeonhole
allows.  Both halves of `lem:same-token-homogeneous-extraction` are this one
selection: a colour class of a matching is a matching, and a colour class of a
star is a star with the same centre, because both are subfamilies. -/
theorem exists_large_roleFibre (family : Finset (Sym2 V)) (role : Sym2 V → Role)
    (roles : Finset Role) (nonempty : roles.Nonempty)
    (declared : ∀ edge ∈ family, role edge ∈ roles) :
    ∃ value ∈ roles, family.card ≤ roles.card * (roleFibre family role value).card := by
  classical
  obtain ⟨best, bestMem, bestMax⟩ :=
    Finset.exists_max_image roles
      (fun value => (roleFibre family role value).card) nonempty
  refine ⟨best, bestMem, ?_⟩
  calc family.card
      = ∑ value ∈ roles, (roleFibre family role value).card :=
        card_eq_sum_roleFibre family role roles declared
    _ ≤ ∑ _value ∈ roles, (roleFibre family role best).card :=
        Finset.sum_le_sum fun value valueMem => bestMax value valueMem
    _ = roles.card * (roleFibre family role best).card := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **`lem:same-token-homogeneous-extraction`, matching half.**  A same-token
`K`-matching contains a role-homogeneous matching of size at least `⌈K/Q⌉`,
written without a division. -/
theorem exists_homogeneous_matching (family : Finset (Sym2 V)) (role : Sym2 V → Role)
    (roles : Finset Role) (nonempty : roles.Nonempty)
    (pattern : Finset (Sym2 V)) (inside : pattern ⊆ family)
    (matching : IsMatching pattern)
    (declared : ∀ edge ∈ family, role edge ∈ roles) :
    ∃ value ∈ roles, roleFibre pattern role value ⊆ roleFibre family role value ∧
      IsMatching (roleFibre pattern role value) ∧
      pattern.card ≤ roles.card * (roleFibre pattern role value).card := by
  obtain ⟨value, valueMem, large⟩ :=
    exists_large_roleFibre pattern role roles nonempty
      fun edge edgeMem => declared edge (inside edgeMem)
  exact ⟨value, valueMem, roleFibre_mono role value inside,
    matching.subset (roleFibre_subset pattern role value), large⟩

/-- **`lem:same-token-homogeneous-extraction`, star half.**  The colour classes
of a star are stars with the same centre, so the same selection applies. -/
theorem exists_homogeneous_star (family : Finset (Sym2 V)) (role : Sym2 V → Role)
    (roles : Finset Role) (nonempty : roles.Nonempty)
    (pattern : Finset (Sym2 V)) (inside : pattern ⊆ family)
    (centre : V) (star : IsStar pattern centre)
    (declared : ∀ edge ∈ family, role edge ∈ roles) :
    ∃ value ∈ roles, roleFibre pattern role value ⊆ roleFibre family role value ∧
      IsStar (roleFibre pattern role value) centre ∧
      pattern.card ≤ roles.card * (roleFibre pattern role value).card := by
  obtain ⟨value, valueMem, large⟩ :=
    exists_large_roleFibre pattern role roles nonempty
      fun edge edgeMem => declared edge (inside edgeMem)
  exact ⟨value, valueMem, roleFibre_mono role value inside,
    fun edge edgeMem => star edge (roleFibre_subset pattern role value edgeMem), large⟩

/-! ## `ψ`, the token-load threshold

`def:homogeneous-token-charge` fixes `ψ(x)` as "the least integer `k ≥ 0` such
that `x ≤ k(2k−1)`", and the two forced-scale corollaries
`cor:forced-same-token-scale` and `cor:forced-homogeneous-same-token-scale`
read it off the matching--star bound: if `s = max{ν(H), Δ(H)}` then
`e(H) ≤ s(2s−1)`, so `s ≥ ψ(e(H))`.

The definition below is the manuscript's characterizing property rather than
its closed form `⌈(1+√(1+8x))/4⌉`; the closed form is a computation of the same
least element, and the proofs use only minimality. -/

private theorem patternThreshold_exists (load : Nat) :
    ∃ scale : Nat, load ≤ scale * (2 * scale - 1) := by
  refine ⟨load, ?_⟩
  match load with
  | 0 => omega
  | (k + 1) =>
    have : 1 ≤ 2 * (k + 1) - 1 := by omega
    calc k + 1 = (k + 1) * 1 := by ring
      _ ≤ (k + 1) * (2 * (k + 1) - 1) := Nat.mul_le_mul_left _ this

/-- **`ψ(x)`** of `def:homogeneous-token-charge`: the least scale whose
matching--star capacity `k(2k−1)` covers the load. -/
noncomputable def patternThreshold (load : Nat) : Nat :=
  Nat.find (patternThreshold_exists load)

/-- `ψ` covers its own load. -/
theorem le_patternThreshold_mul (load : Nat) :
    load ≤ patternThreshold load * (2 * patternThreshold load - 1) :=
  Nat.find_spec (patternThreshold_exists load)

/-- `ψ` is least: any scale whose capacity covers the load is at least `ψ`. -/
theorem patternThreshold_le (load scale : Nat) (covers : load ≤ scale * (2 * scale - 1)) :
    patternThreshold load ≤ scale :=
  Nat.find_le covers

/-- **`cor:forced-same-token-scale`, combinatorial core.**

A family of unordered pairs contains a matching or a star of size `ψ(e(H))`.
The manuscript's proof: with `s = max{ν(H), Δ(H)}` the matching--star bound
gives `e(H) ≤ s(2s−1)`, so `ψ(e(H)) ≤ s` by minimality, and `s` is realized by
a matching or by a star.

Read at a token fibre this is `cor:forced-same-token-scale`; read at a role
fibre, where every member carries one colour, the pattern it produces is
role-homogeneous, which is `cor:forced-homogeneous-same-token-scale`. -/
theorem exists_matching_or_star_of_patternThreshold (family : Finset (Sym2 V))
    (nondiagonal : ∀ edge ∈ family, ¬ edge.IsDiag) :
    (∃ sub ⊆ family, IsMatching sub ∧ patternThreshold family.card ≤ sub.card) ∨
      (∃ centre : V, ∃ sub ⊆ family, IsStar sub centre ∧
        patternThreshold family.card ≤ sub.card) := by
  classical
  by_contra none
  push_neg at none
  obtain ⟨noMatching, noStar⟩ := none
  set scale := patternThreshold family.card with scaleDef
  have matchings : ∀ sub ⊆ family, IsMatching sub → sub.card ≤ scale - 1 := by
    intro sub inside matching
    have := noMatching sub inside matching
    omega
  have degrees : ∀ vertex : V, degree family vertex ≤ scale - 1 := by
    intro vertex
    by_contra big
    exact absurd ((exists_star_iff family vertex scale).mpr (by omega))
      (by
        rintro ⟨sub, inside, star, large⟩
        have := noStar vertex sub inside star
        omega)
  have bound := card_le_matching_mul_two_mul_degree_sub_one family (scale - 1) (scale - 1)
    nondiagonal matchings degrees
  have minimal : scale ≤ scale - 1 := patternThreshold_le _ _ bound
  -- `ψ = 0` is impossible here: the empty matching already realizes it.
  have positive : 1 ≤ scale := by
    by_contra zero
    have empty := noMatching ∅ (Finset.empty_subset _) (by simp [IsMatching])
    simp only [Finset.card_empty] at empty
    omega
  omega

end Hypostructure.Graph.PatternFamily

namespace Hypostructure.Graph.SameTokenBlockerRoles

/-- The manuscript's `Cap_hom(L) = Q_st(L−1)(2L−3)` is the generic cap charge
of `PatternFamily.capCharge` at the size of this alphabet.  The identity is
definitional; it is stated so that a consumer of the alphabet can spend the
generic theorem without unfolding either definition. -/
theorem homogeneousCapCharge_eq_capCharge (patternBound : Nat) :
    homogeneousCapCharge patternBound =
      PatternFamily.capCharge sameTokenRoleBound patternBound :=
  rfl

/-- `Q_st` is the cardinality of the full role alphabet, so a role schedule
that enumerates it has exactly that many entries. -/
theorem card_univ_eq_sameTokenRoleBound :
    (Finset.univ : Finset Role).card = sameTokenRoleBound :=
  Finset.card_univ

end Hypostructure.Graph.SameTokenBlockerRoles
