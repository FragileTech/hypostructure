import Hypostructure.Graph.SurplusBlockers
import Hypostructure.Graph.WindowJoinIdentity

/-!
# `def:capacity-token-ledger`: the token universe `𝔗_cap` and its supply

`def:capacity-token-ledger` builds

  `𝔗_cap = 𝔗_prim ⊔ 𝔗_R ⊔ 𝔗_W`,
  `𝔗_prim = 𝔘_sp(G)`,
  `𝔗_R = {(v,j) : v ∈ R, 1 ≤ j ≤ d_G(v) − δ}`,
  `𝔗_W = {(e,RW) : e ∈ E(R,W)} ⊔ {(e,a),(e,b) : e = ab across two windows}`,

and `lem:capacity-token-supply` counts it:

  `|𝔗_cap| = |𝔘_sp(G)| + σ_R + e(R,W) + 2e_×(W) = |𝔘_sp(G)| + 15p₁₃ + σ(G)`,
  `|𝔗_cap| ≤ 8n + σ(G)`.

Each summand is built from data the branch already owns: `𝔗_prim` is
`Graph/PrimitiveCarrier`'s `𝔘_sp(G)`, `𝔗_R` is the excess selector's own
per-vertex surplus units read on the remainder of a packing, and the two halves
of `𝔗_W` are `Graph/WindowJoinIdentity`'s two incidence families -- the same
families the exact window-join identity counts.  Nothing is assumed: the second
display is that identity together with `σ(G) = σ_W + σ_R`, and the third is the
second spent against `lem:primitive-carrier-supply` and against `order·p ≤ n`,
which the packing itself supplies.

The window order and the baseline are parameters throughout.  The manuscript's
`15` is `δ·order − 2(order − 1)` and its `8n` is `6n + 2n`; neither numeral is
written, and the two envelope steps that produce them stay antecedents rather
than becoming hypotheses about the object.
-/

namespace Hypostructure.Graph

open Hypostructure
open scoped BigOperators

universe u

namespace FiniteObject

variable {object : FiniteObject.{u}}

/-! ## `𝔗_R`, the remainder-surplus tokens -/

/-- **`𝔗_R = {(v,j) : v ∈ R, 1 ≤ j ≤ d_G(v) − δ}`**: one token per surplus unit
carried by a remainder vertex.  A remainder vertex at the baseline contributes
none, which is why the count is the remainder's own surplus. -/
noncomputable def remainderSurplusTokens (object : FiniteObject.{u})
    (threshold : Nat) (packing : Finset (Finset object.Vertex)) :
    Finset (object.Vertex × Nat) := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  exact (object.remainderSupport packing).biUnion fun vertex =>
    (Finset.Icc 1 (object.degree vertex - threshold)).image fun index =>
      (vertex, index)

theorem mem_remainderSurplusTokens_iff (object : FiniteObject.{u})
    (threshold : Nat) (packing : Finset (Finset object.Vertex))
    (token : object.Vertex × Nat) :
    token ∈ object.remainderSurplusTokens threshold packing ↔
      token.1 ∈ object.remainderSupport packing ∧
        1 ≤ token.2 ∧ token.2 ≤ object.degree token.1 - threshold := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  obtain ⟨vertex, index⟩ := token
  simp only [remainderSurplusTokens, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_Icc, Prod.mk.injEq]
  constructor
  · rintro ⟨other, inside, value, ⟨lower, upper⟩, rfl, rfl⟩
    exact ⟨inside, lower, upper⟩
  · rintro ⟨inside, lower, upper⟩
    exact ⟨vertex, inside, index, ⟨lower, upper⟩, rfl, rfl⟩

/-- **`|𝔗_R| = σ_R`.**  Distinct remainder vertices contribute disjoint blocks,
and a vertex's block has one member per surplus unit it carries. -/
theorem card_remainderSurplusTokens (object : FiniteObject.{u})
    (threshold : Nat) (packing : Finset (Finset object.Vertex)) :
    (object.remainderSurplusTokens threshold packing).card =
      object.ambientSurplus (object.remainderSupport packing) threshold := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  rw [remainderSurplusTokens, Finset.card_biUnion, ambientSurplus]
  · refine Finset.sum_congr rfl fun vertex _ => ?_
    rw [Finset.card_image_of_injective _ fun _ _ equality => congrArg Prod.snd equality,
      Nat.card_Icc]
    omega
  · intro left _ right _ distinct
    refine Finset.disjoint_left.2 fun token leftMember rightMember => ?_
    obtain ⟨_, _, leftEq⟩ := Finset.mem_image.1 leftMember
    obtain ⟨_, _, rightEq⟩ := Finset.mem_image.1 rightMember
    exact distinct ((congrArg Prod.fst leftEq).trans (congrArg Prod.fst rightEq).symm)

/-! ## `𝔗_cap`, the capacity-token universe -/

/-- **A capacity token.**  The four constructors are the manuscript's three
summands with `𝔗_W` split into its two declared halves:

* `boundaryWindow e` -- `(e, RW)` for a window--remainder edge `e ∈ E(R,W)`;
* `crossWindow (v, w)` -- the token of a cross-window edge `vw` at its end `v`,
  so a cross-window edge contributes one token at each of its two window ends;
* `remainder (v, j)` -- the `j`-th surplus unit of a remainder vertex `v`;
* `primitive u` -- a member of `𝔘_sp(G) = V(G) ⊔ I_E(G) ⊔ 𝒫_exc`.

The four constructors are exactly the `TokenSubtype` alphabet
`def:same-token-blocker-roles` declares, which is what `subtype` below reads. -/
inductive CapacityToken (object : FiniteObject.{u}) where
  /-- `(e, RW)`, a window--remainder edge token of `𝔗_W`. -/
  | boundaryWindow (incidence : object.Vertex × object.Vertex)
  /-- `(e, v)`, a cross-window edge token of `𝔗_W` at one of its two ends. -/
  | crossWindow (incidence : object.Vertex × object.Vertex)
  /-- `(v, j)`, a remainder surplus unit of `𝔗_R`. -/
  | remainder (unit : object.Vertex × Nat)
  /-- A member of `𝔗_prim = 𝔘_sp(G)`. -/
  | primitive (item : object.Vertex ⊕ (object.Vertex × object.Vertex) ⊕
      (object.Vertex × object.Vertex))

namespace CapacityToken

noncomputable instance decidableEq (object : FiniteObject.{u}) :
    DecidableEq (CapacityToken object) := Classical.decEq _

/-- **`sub(t)`** of `def:same-token-blocker-roles`, read off the constructor: a
token names its own summand of `𝔗_cap`, and the three primitive subtypes `V`,
`I`, `P` are the three summands of `𝔘_sp(G)`. -/
def subtype : CapacityToken object → SameTokenBlockerRoles.TokenSubtype
  | .boundaryWindow _ => .boundaryWindow
  | .crossWindow _ => .crossWindow
  | .remainder _ => .remainderSurplus
  | .primitive (.inl _) => .primitiveVertex
  | .primitive (.inr (.inl _)) => .primitiveIncidence
  | .primitive (.inr (.inr _)) => .primitivePort

end CapacityToken

/-- **`𝔗_cap = 𝔗_prim ⊔ 𝔗_R ⊔ 𝔗_W`**, as a finite set of capacity tokens.  The
four constructors are injective with disjoint ranges, so the union is the
manuscript's disjoint union and the count below is the sum of the four. -/
noncomputable def capacityTokens (object : FiniteObject.{u}) (threshold : Nat)
    (packing : Finset (Finset object.Vertex)) :
    Finset (CapacityToken object) := by
  classical
  exact (object.windowRemainderIncidences packing).image CapacityToken.boundaryWindow ∪
    ((object.crossWindowIncidences packing).image CapacityToken.crossWindow ∪
      ((object.remainderSurplusTokens threshold packing).image
          CapacityToken.remainder ∪
        (object.primitiveCarrier threshold).image CapacityToken.primitive))

/-- **`|𝔗_cap| = |𝔘_sp(G)| + σ_R + e(R,W) + 2e_×(W)`**, the first display of
`lem:capacity-token-supply`: the four families are disjoint by their
constructors. -/
theorem card_capacityTokens (object : FiniteObject.{u}) (threshold : Nat)
    (packing : Finset (Finset object.Vertex)) :
    (object.capacityTokens threshold packing).card =
      (object.windowRemainderIncidences packing).card +
        ((object.crossWindowIncidences packing).card +
          (object.ambientSurplus (object.remainderSupport packing) threshold +
            (object.primitiveCarrier threshold).card)) := by
  classical
  rw [capacityTokens, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_union_of_disjoint,
    Finset.card_image_of_injective _ (fun _ _ equality =>
      CapacityToken.boundaryWindow.injEq .. ▸ equality),
    Finset.card_image_of_injective _ (fun _ _ equality =>
      CapacityToken.crossWindow.injEq .. ▸ equality),
    Finset.card_image_of_injective _ (fun _ _ equality =>
      CapacityToken.remainder.injEq .. ▸ equality),
    Finset.card_image_of_injective _ (fun _ _ equality =>
      CapacityToken.primitive.injEq .. ▸ equality),
    object.card_remainderSurplusTokens threshold packing]
  all_goals (
    refine Finset.disjoint_left.2 fun token leftMember rightMember => ?_
    simp only [Finset.mem_image, Finset.mem_union] at leftMember rightMember
    obtain ⟨_, _, rfl⟩ := leftMember
    simp at rightMember)

/-! ## `lem:capacity-token-supply` -/

/-- **`lem:capacity-token-supply`, the exact display**, in subtraction-free form:

  `|𝔗_cap| + 2(order − 1)p = |𝔘_sp(G)| + δ·order·p + σ(G)`,

which at the registered presentation `δ = 3`, `order = 13` is the manuscript's

  `|𝔗_cap| = |𝔘_sp(G)| + 15p₁₃ + σ(G)`.

The proof is the manuscript's: the four summands are disjoint, the window pair
`e(R,W) + 2e_×(W)` is `lem:exact-window-join-identity`, and
`σ_W + σ_R = σ(G)` is `def:window-remainder-surplus-split`.  Nothing is assumed
about the object beyond the standing baseline and the packing being one. -/
theorem card_capacityTokens_add_internalMass (object : FiniteObject.{u})
    {order threshold : Nat} {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    (object.capacityTokens threshold packing).card +
        2 * (order - 1) * packing.card =
      (object.primitiveCarrier threshold).card +
        threshold * (order * packing.card) + object.degreeSurplus threshold := by
  have supply := object.card_capacityTokens threshold packing
  have join := object.exact_window_join_identity valid baseline
  have surplus := object.ambientSurplus_windowSupport_add_remainderSupport packing
    threshold baseline
  omega

/-- `order·p ≤ n`: the manuscript's `13p₁₃ ≤ n`, "because the packed windows are
vertex-disjoint".  The remainder accounts for the rest of the vertex set. -/
theorem order_mul_card_le_vertexCount (object : FiniteObject.{u})
    {order : Nat} {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing) :
    order * packing.card ≤ object.vertexCount := by
  have split := object.remainderSupport_card_add_eq valid
  omega

/-- **`lem:capacity-token-supply`, the displayed bound**: `|𝔗_cap| ≤ 8n + σ(G)`.

The manuscript's own two steps, both kept as antecedents rather than becoming
hypotheses about the object:

* `|𝔘_sp(G)| ≤ 6n` on the sparse upper envelope `m ≤ 2n − 2`, which is
  `lem:primitive-carrier-supply`;
* `15p₁₃ < 2n`, which is `13p₁₃ ≤ n` -- derived here from the packing -- together
  with the comparison `δ·order + 2 ≤ 4·order` between the two registered numbers,
  the manuscript's `15 ≤ 2·13`.

The `8n` is `6n + 2n`, and the `6` and the `2` are those two steps; no numeral is
written except as the coefficients of the envelopes that produce it. -/
theorem card_capacityTokens_le (object : FiniteObject.{u})
    {order threshold : Nat} {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (three : 3 ≤ threshold)
    (handshake : threshold * object.vertexCount ≤ 2 * object.edgeCount)
    (envelope : object.edgeCount + 2 ≤ 2 * object.vertexCount)
    (orderPos : 0 < order)
    (joinSlack : threshold * order + 2 ≤ 4 * order) :
    (object.capacityTokens threshold packing).card ≤
      8 * object.vertexCount + object.degreeSurplus threshold := by
  have identity := object.card_capacityTokens_add_internalMass valid baseline
  have primitive := card_primitiveCarrier_le baseline three handshake envelope
  have covered := object.order_mul_card_le_vertexCount valid
  set count := packing.card with countDef
  set covering := order * count with coveringDef
  set inner := (order - 1) * count with innerDef
  have massEq : 2 * (order - 1) * count = 2 * inner := by rw [innerDef]; ring
  have innerAdd : inner + count = covering := by
    rw [innerDef, coveringDef]
    calc (order - 1) * count + count = ((order - 1) + 1) * count := by ring
      _ = order * count := by
        have restore : order - 1 + 1 = order := by omega
        rw [restore]
  have spread : threshold * covering + 2 * count ≤ 4 * covering := by
    have scaled := Nat.mul_le_mul_right count joinSlack
    have left : (threshold * order + 2) * count = threshold * covering + 2 * count := by
      rw [coveringDef]; ring
    have right : (4 * order) * count = 4 * covering := by rw [coveringDef]; ring
    rw [left, right] at scaled
    exact scaled
  omega

end FiniteObject

end Hypostructure.Graph
