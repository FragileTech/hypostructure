import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The same-token role alphabet `𝔕_st` of `def:same-token-blocker-roles`

`def:same-token-blocker-roles` labels a blocked active-demand pair `π` sitting
over a capacity token `t` by the finite triple

`ρ_t(π) = (type(B_π), class(t), sub(t))`.

Each coordinate is a *constructor tag*, not a measurement:

* `type(B_π) ∈ {a,…,f}` is the blocker type of `def:surplus-blockers`, whose
  clause list is closed ("The blocker must be an object explicitly listed
  above… its failed compatibility must be represented by a finite-capacity
  object of one of these six types");
* `sub(t)` is the capacity-token subtype of `def:capacity-token-ledger`, and
  `class(t) ∈ {W, R, P}` is the summand of
  `𝔗_cap = 𝔗_W ⊔ 𝔗_R ⊔ 𝔗_prim` that contains it, so the class is *determined*
  by the subtype and contributes no independent coordinate.

The manuscript's role bound `|𝔕_st| ≤ 6(2+1+3) = 36 =: Q_st` is therefore the
cardinality of `Role` below, and its factorisation `6 · (2+1+3)` is
`card_role` together with `card_tokenSubtype_eq_sum_classFibres`: the second
factor is the sum of the three class fibres of `tokenClass`, of sizes `2`
(`RW, WW`), `1` (`R`) and `3` (`V, I, P`).  No number is written down; every
one is `Fintype.card` of a declared type.

The module is a dependency-free leaf: it declares the alphabet and nothing
else, so any registration that needs `Q_st` reads it off `Fintype.card Role`
instead of writing a numeral.
-/

namespace Hypostructure.Graph.SameTokenBlockerRoles

/-- `type(B)` of `def:same-token-blocker-roles`: the closed clause list
(a)--(f) of `def:surplus-blockers`.

* `sharedDeclaredSupport` -- (a), a vertex or edge-incidence in both declared
  demand supports;
* `sharedReturnSupport` -- (b), a common vertex or incidence of the two
  canonical return paths;
* `sharedLocalBuffer` -- (c), a common shoulder endpoint or shared cubic
  buffer vertex;
* `boundaryProfile` -- (d), a boundary-degree-profile coordinate;
* `targetResponse` -- (e), a target-response coordinate;
* `arithmeticChordSet` -- (f), an arithmetic chord-set obstruction from a
  suppressed open-port family. -/
inductive BlockerKind
  | sharedDeclaredSupport
  | sharedReturnSupport
  | sharedLocalBuffer
  | boundaryProfile
  | targetResponse
  | arithmeticChordSet
deriving DecidableEq, Fintype, Repr

/-- `class(t)` of `def:same-token-blocker-roles`: the summand of the capacity
token universe `𝔗_cap = 𝔗_W ⊔ 𝔗_R ⊔ 𝔗_prim` that contains `t`. -/
inductive TokenClass
  | windowIncidence
  | remainderSurplus
  | primitiveCarrier
deriving DecidableEq, Fintype, Repr

/-- `sub(t)` of `def:same-token-blocker-roles`: the capacity-token subtype.

* `boundaryWindow` -- `RW`, a remainder/window incidence token of `𝔗_W`;
* `crossWindow` -- `WW`, a cross-window endpoint token of `𝔗_W`;
* `remainderSurplus` -- `R`, a remainder surplus unit of `𝔗_R`;
* `primitiveVertex` -- `V`, a vertex of `V(G) ⊆ 𝔗_prim`;
* `primitiveIncidence` -- `I`, an edge-incidence of `I_E(G) ⊆ 𝔗_prim`;
* `primitivePort` -- `P`, an excess port of `𝒫_exc ⊆ 𝔗_prim`. -/
inductive TokenSubtype
  | boundaryWindow
  | crossWindow
  | remainderSurplus
  | primitiveVertex
  | primitiveIncidence
  | primitivePort
deriving DecidableEq, Fintype, Repr

/-- `class(t)` read off `sub(t)`: the subtype already names its summand of
`𝔗_cap`, so the class coordinate of the role triple is redundant. -/
def tokenClass : TokenSubtype → TokenClass
  | .boundaryWindow | .crossWindow => .windowIncidence
  | .remainderSurplus => .remainderSurplus
  | .primitiveVertex | .primitiveIncidence | .primitivePort => .primitiveCarrier

/-- `𝔕_st` of `def:same-token-blocker-roles`: the same-token role of a blocked
pair at a capacity token.  The class coordinate of the manuscript's triple is
`tokenClass` of the subtype, so the label is the pair of the two independent
coordinates. -/
structure Role where
  blocker : BlockerKind
  token : TokenSubtype
deriving DecidableEq, Fintype, Repr

/-- The role alphabet factors as blocker type times token subtype: the `6 · _`
of `|𝔕_st| ≤ 6(2+1+3)`. -/
theorem card_role :
    Fintype.card Role = Fintype.card BlockerKind * Fintype.card TokenSubtype := by
  classical
  exact Fintype.card_congr (⟨fun role => (role.blocker, role.token),
      fun pair => ⟨pair.1, pair.2⟩, fun _ => rfl, fun _ => rfl⟩ :
    Role ≃ BlockerKind × TokenSubtype) |>.trans (Fintype.card_prod _ _)

/-- The token subtypes are partitioned by their class: the `(2+1+3)` of
`|𝔕_st| ≤ 6(2+1+3)` is the sum of the three class fibres of `𝔗_cap`. -/
theorem card_tokenSubtype_eq_sum_classFibres :
    Fintype.card TokenSubtype =
      ∑ class' : TokenClass,
        (Finset.univ.filter fun subtype => tokenClass subtype = class').card := by
  classical
  rw [← Finset.card_eq_sum_card_fiberwise
    (f := tokenClass) (s := (Finset.univ : Finset TokenSubtype))
    (t := (Finset.univ : Finset TokenClass)) (fun _ _ => Finset.mem_univ _)]
  rfl

end Hypostructure.Graph.SameTokenBlockerRoles
