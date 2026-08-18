import Hypostructure.Graph.Route8Census
import Hypostructure.Graph.TypeBEnvelopeCharge

/-!
# The route-8 deficit reading, summed over every canonical piece

`def:typeA-large-budget-deficit` with `lem:typeA-route8-burden` substituted,
node `[113]`, is the inequality `|R| ≤ N_basin + s·|∂R| + o(|R|)`
(`Graph.Route8Census.Deficit`).  Its proof is the manuscript's global squeeze
(node `[111]`, `thm:branch-kill`, `lem:typeA-unified-deficit`): sum the
canonical decomposition of the remainder piece by piece,

* a piece with nonnegative net charge contributes `|X| ≤ s·def⁺(X)`
  (`def:net-charge`);
* a negative zero-surplus piece contributes `|X| ≤ S_sil^exc(X) + s·def⁺(X)`
  (`lem:typeA-silent-excess-count`), provided no saturated receiver has a
  completion port carrying `s` visible receiver-entry returns;
* a negative positive-surplus piece is a Type B bridge component and contributes
  `|X| ≤ s·def⁺(X) + F·s·σ(X)` (`lem:typeB-bridge-deficit-bound`).

Summing, `|R| ≤ N_basin + s·def⁺(R) + F·s·σ(R)`; `def⁺(R) ≤ |∂R|`
(`lem:surplus-aware-window-stub`) and `σ(R) ≤ σ(G) ≤ T(n)` (the near-cubic
spine) give the reading.  The classification hypothesis — every negative piece
is silent-first when it has no surplus and a bridge component when it has —
is the exact content of `thm:branch-kill`'s two clauses at every piece; the
route-8 branch decides it on its residual, and the complementary arm is the
piece that fails it.
-/

namespace Hypostructure.Graph.Route8Deficit

open Hypostructure
open Hypostructure.Graph

universe u

variable (object : FiniteObject.{u})

attribute [local instance] Route8.vertexDecEq

/-- **Silent-first**: no saturated receiver of the piece has a completion port
carrying `s` visible receiver-entry returns — the hypothesis of
`lem:typeA-silent-excess-count`, i.e. node `[93]`'s no arm at that piece. -/
def SilentFirst (piece : Finset object.Vertex) (threshold scale : Nat) : Prop :=
  ∀ receiver : object.Vertex,
    object.IsReceiver piece threshold receiver →
    object.Saturated piece threshold scale receiver →
    ∀ outside ∈ VisibleEntry.completionPorts object piece receiver,
      (VisibleEntry.visibleLoadsAt object piece threshold receiver outside).card + 1 ≤
        scale

/-- **The all-pieces classification of `thm:branch-kill`**: every negative piece
of the canonical decomposition of the remainder is silent-first when it carries
no ambient surplus (Type A: route-8 or target-defect entries only) and is a
Type B bridge component when it carries surplus. -/
def PieceClassification (packing : Finset (Finset object.Vertex))
    (threshold scale : Nat) : Prop :=
  ∀ piece ∈ object.canonicalPieces (object.remainderSupport packing),
    object.NegativeNetCharge
        (object.pieceSupport (object.remainderSupport packing) piece) threshold scale →
      (object.ambientSurplus
          (object.pieceSupport (object.remainderSupport packing) piece) threshold = 0 →
        SilentFirst object (object.pieceSupport (object.remainderSupport packing) piece)
          threshold scale) ∧
      (0 < object.ambientSurplus
          (object.pieceSupport (object.remainderSupport packing) piece) threshold →
        TypeBEnvelopeCharge.BridgeResidualComponentAt object
          (object.pieceSupport (object.remainderSupport packing) piece) threshold scale)

/-- The silent-excess mass a piece contributes to the census: its indexed
entries when it is a Type A piece of `𝒳_A`, nothing otherwise. -/
noncomputable def silentMass (packing : Finset (Finset object.Vertex))
    (threshold scale : Nat) (piece : Finset object.Vertex) : Nat := by
  classical
  exact if piece ∈ Route8Census.typeAPieces object packing threshold scale then
    ∑ receiver ∈ object.receivers piece threshold,
      (VisibleEntry.silentExcess object piece threshold scale receiver).card
  else 0

/-- `N_basin = Σ_{X ∈ 𝒳_A} Σ_w |𝒰_X(w)|`: the census entries are the indexed
`(piece, receiver, load)` triples, counted once each. -/
theorem card_entries (packing : Finset (Finset object.Vertex))
    (threshold scale : Nat) :
    (Route8Census.entries object packing threshold scale).card =
      ∑ piece ∈ Route8Census.typeAPieces object packing threshold scale,
        ∑ receiver ∈ object.receivers piece threshold,
          (VisibleEntry.silentExcess object piece threshold scale receiver).card := by
  classical
  unfold Route8Census.entries
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun piece _ => ?_
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun receiver _ => ?_
      rw [Finset.card_image_of_injective]
      intro left right equal
      simpa using equal
    · intro left _ right _ different
      rw [Function.onFun, Finset.disjoint_left]
      intro index leftMem rightMem
      rw [Finset.mem_image] at leftMem rightMem
      obtain ⟨_, _, rfl⟩ := leftMem
      obtain ⟨_, _, equal⟩ := rightMem
      exact different (Eq.symm (by simpa using (congrArg (fun index => index.2.1) equal)))
  · intro left _ right _ different
    rw [Function.onFun, Finset.disjoint_left]
    intro index leftMem rightMem
    rw [Finset.mem_biUnion] at leftMem rightMem
    obtain ⟨_, _, leftMem⟩ := leftMem
    obtain ⟨_, _, rightMem⟩ := rightMem
    rw [Finset.mem_image] at leftMem rightMem
    obtain ⟨_, _, rfl⟩ := leftMem
    obtain ⟨_, _, equal⟩ := rightMem
    exact different (Eq.symm (by simpa using (congrArg (fun index => index.1) equal)))

/-- The piece supports are injective on the canonical pieces: distinct
components have disjoint, nonempty vertex sets. -/
theorem pieceSupport_injOn (support : Finset object.Vertex) :
    Set.InjOn (object.pieceSupport support) ↑(object.canonicalPieces support) := by
  intro left leftMem right rightMem equal
  by_contra different
  have disjoint := SupportComponents.Connected.disjoint_members object support different
  have nonempty := SupportComponents.Connected.member_nonempty object support
    ((object.mem_canonicalPieces support).mp leftMem)
  obtain ⟨vertex, member⟩ := nonempty
  have member' : vertex ∈ object.pieceSupport support right := equal ▸ member
  exact Finset.disjoint_left.mp disjoint member member'

/-- The silent masses of the pieces sum to the census count. -/
theorem sum_silentMass (packing : Finset (Finset object.Vertex))
    (threshold scale : Nat) :
    ∑ piece ∈ object.canonicalPieces (object.remainderSupport packing),
        silentMass object packing threshold scale
          (object.pieceSupport (object.remainderSupport packing) piece) =
      (Route8Census.entries object packing threshold scale).card := by
  classical
  set R := object.remainderSupport packing with Rdef
  have memTypeA : ∀ piece ∈ object.canonicalPieces R,
      object.pieceSupport R piece ∈ Route8Census.typeAPieces object packing threshold scale ↔
        (object.NegativeNetCharge (object.pieceSupport R piece) threshold scale ∧
          object.ambientSurplus (object.pieceSupport R piece) threshold = 0) := by
    intro piece member
    simp only [Route8Census.typeAPieces, Finset.mem_filter, Finset.mem_image]
    exact ⟨fun h => h.2, fun h => ⟨⟨piece, member, rfl⟩, h⟩⟩
  have image_eq : Route8Census.typeAPieces object packing threshold scale =
      ((object.canonicalPieces R).filter fun piece =>
        object.NegativeNetCharge (object.pieceSupport R piece) threshold scale ∧
          object.ambientSurplus (object.pieceSupport R piece) threshold = 0).image
        (object.pieceSupport R) := by
    ext X
    simp only [Route8Census.typeAPieces, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨piece, member, rfl⟩, property⟩
      exact ⟨piece, ⟨member, property⟩, rfl⟩
    · rintro ⟨piece, ⟨member, property⟩, rfl⟩
      exact ⟨⟨piece, member, rfl⟩, property⟩
  rw [card_entries, image_eq,
    Finset.sum_image (fun left leftMem right rightMem equal =>
      pieceSupport_injOn object R (Finset.mem_filter.mp leftMem).1
        (Finset.mem_filter.mp rightMem).1 equal),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun piece member => ?_
  by_cases typeA : object.NegativeNetCharge (object.pieceSupport R piece) threshold scale ∧
      object.ambientSurplus (object.pieceSupport R piece) threshold = 0
  · rw [if_pos typeA]
    simp only [silentMass, if_pos ((memTypeA piece member).mpr typeA)]
  · rw [if_neg typeA]
    simp only [silentMass, if_neg (fun h => typeA ((memTypeA piece member).mp h))]

/-- **One piece of the squeeze.**  Under the classification, every canonical piece
satisfies `|X| ≤ silentMass(X) + s·def⁺(X) + F·s·σ(X)`. -/
theorem card_piece_le (packing : Finset (Finset object.Vertex))
    (threshold scale massFactor : Nat) (scalePos : 1 ≤ scale)
    (slack : threshold + 2 + scale ≤ massFactor * scale)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (routed : ∀ piece : Finset object.Vertex,
      piece ⊆ object.remainderSupport packing →
      object.ambientSurplus piece threshold = 0 →
      ∀ vertex ∈ piece, object.internalDegree piece vertex = threshold →
        ∃ receiver : object.Vertex,
          object.traceReceiver? piece threshold vertex = some receiver ∧
            object.IsReceiver piece threshold receiver)
    (classified : PieceClassification object packing threshold scale)
    (piece : SupportComponents.Connected.Component object (object.remainderSupport packing))
    (member : piece ∈ object.canonicalPieces (object.remainderSupport packing)) :
    (object.pieceSupport (object.remainderSupport packing) piece).card ≤
      silentMass object packing threshold scale
          (object.pieceSupport (object.remainderSupport packing) piece) +
        scale * object.positiveDeficiency
          (object.pieceSupport (object.remainderSupport packing) piece) threshold +
        massFactor * scale * object.ambientSurplus
          (object.pieceSupport (object.remainderSupport packing) piece) threshold := by
  classical
  set X := object.pieceSupport (object.remainderSupport packing) piece with Xdef
  by_cases negative : object.NegativeNetCharge X threshold scale
  · obtain ⟨silent, bridge⟩ := classified piece member negative
    by_cases surplusZero : object.ambientSurplus X threshold = 0
    · -- Type A: `lem:typeA-silent-excess-count`.
      have exactDegree : ∀ vertex ∈ X, object.degree vertex = threshold := by
        intro vertex vertexMem
        have nonneg := baseline vertex
        have summand : object.degree vertex - threshold = 0 :=
          Nat.eq_zero_of_le_zero
            (surplusZero ▸ Finset.single_le_sum
              (f := fun other => object.degree other - threshold)
              (fun _ _ => Nat.zero_le _) vertexMem)
        omega
      have capped : ∀ vertex ∈ X, object.internalDegree X vertex ≤ threshold :=
        fun vertex vertexMem =>
          exactDegree vertex vertexMem ▸ object.internalDegree_le_degree X vertex
      have count := VisibleEntry.card_le_sum_silentExcess_add_positiveDeficiency
        object X threshold scale scalePos exactDegree capped
        (routed X (object.pieceSupport_subset _ piece) surplusZero)
        (silent surplusZero)
      have typeA : X ∈ Route8Census.typeAPieces object packing threshold scale := by
        simp only [Route8Census.typeAPieces, Finset.mem_filter, Finset.mem_image]
        exact ⟨⟨piece, member, rfl⟩, negative, surplusZero⟩
      simp only [silentMass, if_pos typeA]
      omega
    · -- Type B bridge component: `lem:typeB-bridge-deficit-bound`.
      have positive : 0 < object.ambientSurplus X threshold := Nat.pos_of_ne_zero surplusZero
      obtain ⟨routes, unsaturated⟩ := bridge positive
      have bound := TypeBEnvelopeCharge.bridgeDeficitBound object X slack baseline
        routes unsaturated
      omega
  · -- Nonnegative net charge: `|X| + s·σ(X) ≤ s·def⁺(X)`.
    have nonneg := (object.not_negativeNetCharge_iff X threshold scale).mp negative
    unfold FiniteObject.NonNegativeNetCharge at nonneg
    omega

/-- **`def:typeA-large-budget-deficit` with `lem:typeA-route8-burden` and
`thm:branch-kill` substituted (node `[113]`)**: under the all-pieces
classification, `|R| ≤ N_basin + s·|∂R| + F·s·T(n)`. -/
theorem deficit_of_classification (packing : Finset (Finset object.Vertex))
    (threshold scale massFactor surplusBound : Nat) (scalePos : 1 ≤ scale)
    (slack : threshold + 2 + scale ≤ massFactor * scale)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (routed : ∀ piece : Finset object.Vertex,
      piece ⊆ object.remainderSupport packing →
      object.ambientSurplus piece threshold = 0 →
      ∀ vertex ∈ piece, object.internalDegree piece vertex = threshold →
        ∃ receiver : object.Vertex,
          object.traceReceiver? piece threshold vertex = some receiver ∧
            object.IsReceiver piece threshold receiver)
    (surplus : object.degreeSurplus threshold ≤ surplusBound)
    (classified : PieceClassification object packing threshold scale) :
    Route8Census.Deficit object packing threshold scale
      (massFactor * scale * surplusBound) := by
  classical
  unfold Route8Census.Deficit
  set R := object.remainderSupport packing with Rdef
  have perPiece := fun piece member =>
    card_piece_le object packing threshold scale massFactor scalePos slack baseline
      routed classified piece member
  have summed :
      ∑ piece ∈ object.canonicalPieces R, (object.pieceSupport R piece).card ≤
        ∑ piece ∈ object.canonicalPieces R,
          (silentMass object packing threshold scale (object.pieceSupport R piece) +
            scale * object.positiveDeficiency (object.pieceSupport R piece) threshold +
            massFactor * scale * object.ambientSurplus (object.pieceSupport R piece)
              threshold) :=
    Finset.sum_le_sum perPiece
  rw [object.sum_pieceSupport_card R, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, object.sum_positiveDeficiency_canonicalPieces,
    object.sum_ambientSurplus_canonicalPieces, sum_silentMass] at summed
  have deficiency := object.positiveDeficiency_le_boundaryIncidence R threshold baseline
  rw [← Route8Census.card_supply] at deficiency
  have surplusR := (object.ambientSurplus_le_degreeSurplus R threshold baseline).trans surplus
  have scaledDeficiency := Nat.mul_le_mul_left scale deficiency
  have scaledSurplus := Nat.mul_le_mul_left (massFactor * scale) surplusR
  omega

end Hypostructure.Graph.Route8Deficit
