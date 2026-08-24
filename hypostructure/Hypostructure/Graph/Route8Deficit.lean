import Hypostructure.Graph.Route8Census
import Hypostructure.Graph.ExitFourFamily
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
consumer supplies it as a proved hypothesis on the active residual.
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

/-- **The visible arm's entry state**: a piece that is not silent-first has a
saturated receiver with a completion port carrying the registered overload of
visible returns — `VisibleFourUnpeeledAt` at the empty peeling, the hypothesis
of `lem:typeA-unpeeled-visible-routing`'s canonical package. -/
theorem visibleFourUnpeeledAt_of_not_silentFirst
    {piece : Finset object.Vertex} {threshold scale : Nat}
    (notSilent : ¬ SilentFirst object piece threshold scale) :
    ∃ receiver : object.Vertex,
      object.IsReceiver piece threshold receiver ∧
        object.Saturated piece threshold scale receiver ∧
        ExitFour.VisibleFourUnpeeledAt piece threshold scale receiver ∅ := by
  classical
  unfold SilentFirst at notSilent
  push_neg at notSilent
  obtain ⟨receiver, isReceiver, saturated, outside, portMember, overload⟩ :=
    notSilent
  have portEq : ExitFour.unpeeledVisibleLoadsAt piece threshold receiver
      outside ∅ =
      VisibleEntry.visibleLoadsAt object piece threshold receiver outside := by
    unfold ExitFour.unpeeledVisibleLoadsAt ExitFour.unpeeledLoads
    rw [Finset.sdiff_empty]
    refine Finset.inter_eq_left.mpr ?_
    intro load member
    unfold VisibleEntry.visibleLoadsAt at member
    exact (Finset.mem_filter.mp member).1
  exact ⟨receiver, isReceiver, saturated, outside, portMember, by
    rw [portEq]; omega⟩

/-- **The silent-first specialization**: every negative zero-surplus piece is
silent-first, and every negative positive-surplus piece is a Type B bridge
component.

This is *not* `thm:branch-kill`'s classification.  `thm:branch-kill` (a) lists
"no exit-(4) witness for a routed load" among its hypotheses, and
`rem:unified-covers-exit4` records that the unified collection `\tilde{𝒳}`
"contains, simultaneously, the Type A supports carrying an admissible route-8
residual profile *and* the Type A supports that leave through the target-defect
exit".  A target-defect (exit-(4)) support may realize its exit through four
visible receiver-entry returns, so silent-first does not hold for it.  This
predicate is only the hypothesis under which `lem:typeA-silent-excess-count`
applies to every negative zero-surplus piece; `card_piece_le` and
`deficit_of_classification` below consume exactly it. -/
def SilentClassification (packing : Finset (Finset object.Vertex))
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

/-- **The all-pieces classification of `thm:branch-kill`**, as the manuscript
states it: the contrapositive of clauses (a) and (b) at every negative piece of
the canonical decomposition of the remainder.

A negative zero-surplus piece carries an exit-(4) witness for one of its routed
loads, or an admissible route-8 residual profile, or a decorated Type B
handoff; a negative positive-surplus piece is a Type B bridge residual
(`def:typeB-bridge-statements`: the B2 disjoint ledger with strictly negative
remaining core, or a minimal overlap obstruction — the contrapositive of
`prop:typeB-bridge-reduction`).  `Route8Profile`, `Handoff`, and `Bridge` are
the branch's registered notions of an admissible silent-core residual profile
(`def:typeA-silent-core-residual`), a produced decorated handoff envelope
(`def:decorated-fan-envelope`), and the Type B bridge-residual datum; this
module quantifies over them.

Unlike `SilentClassification`, this statement does **not** make a negative
zero-surplus piece silent-first: per `rem:unified-covers-exit4`, an exit-(4)
support may realize its exit through four visible receiver-entry returns and
still belongs to the unified collection. -/
def PieceClassification (Target : FiniteObject.{u} → Prop)
    (Route8Profile Handoff Bridge : Finset object.Vertex → Prop)
    (packing : Finset (Finset object.Vertex))
    (threshold scale : Nat) : Prop :=
  ∀ piece ∈ object.canonicalPieces (object.remainderSupport packing),
    object.NegativeNetCharge
        (object.pieceSupport (object.remainderSupport packing) piece) threshold scale →
      (object.ambientSurplus
          (object.pieceSupport (object.remainderSupport packing) piece) threshold = 0 →
        (∃ receiver : object.Vertex,
          object.IsReceiver
              (object.pieceSupport (object.remainderSupport packing) piece) threshold
              receiver ∧
            Nonempty (ExitFour.Witness Target
              (object.pieceSupport (object.remainderSupport packing) piece)
              threshold scale receiver ∅)) ∨
          Route8Profile (object.pieceSupport (object.remainderSupport packing) piece) ∨
          Handoff (object.pieceSupport (object.remainderSupport packing) piece)) ∧
      (0 < object.ambientSurplus
          (object.pieceSupport (object.remainderSupport packing) piece) threshold →
        Bridge (object.pieceSupport (object.remainderSupport packing) piece))

/-- The excess mass a piece contributes to the census (`E(w)`-indexed; the
paper's `𝒰(w)` on silent-first pieces): its indexed entries when it is a
Type A piece of `𝒳_A`, nothing otherwise. -/
noncomputable def excessMass (packing : Finset (Finset object.Vertex))
    (threshold scale : Nat) (piece : Finset object.Vertex) : Nat := by
  classical
  exact if piece ∈ Route8Census.typeAPieces object packing threshold scale then
    ∑ receiver ∈ object.receivers piece threshold,
      (VisibleEntry.excessBasin object piece threshold scale receiver).card
  else 0

/-- `N_basin = Σ_{X ∈ 𝒳_A} Σ_w |E_X(w)|`: the census entries are the indexed
`(piece, receiver, load)` triples, counted once each
(`lem:typeA-route8-burden`'s count, silence-free). -/
theorem card_entries (packing : Finset (Finset object.Vertex))
    (threshold scale : Nat) :
    (Route8Census.entries object packing threshold scale).card =
      ∑ piece ∈ Route8Census.typeAPieces object packing threshold scale,
        ∑ receiver ∈ object.receivers piece threshold,
          (VisibleEntry.excessBasin object piece threshold scale receiver).card := by
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
theorem sum_excessMass (packing : Finset (Finset object.Vertex))
    (threshold scale : Nat) :
    ∑ piece ∈ object.canonicalPieces (object.remainderSupport packing),
        excessMass object packing threshold scale
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
    simp only [excessMass, if_pos ((memTypeA piece member).mpr typeA)]
  · rw [if_neg typeA]
    simp only [excessMass, if_neg (fun h => typeA ((memTypeA piece member).mp h))]

/-- **One piece of the squeeze.**  Under the classification, every canonical piece
satisfies `|X| ≤ excessMass(X) + s·def⁺(X) + F·s·σ(X)`. -/
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
    (classified : SilentClassification object packing threshold scale)
    (piece : SupportComponents.Connected.Component object (object.remainderSupport packing))
    (member : piece ∈ object.canonicalPieces (object.remainderSupport packing)) :
    (object.pieceSupport (object.remainderSupport packing) piece).card ≤
      excessMass object packing threshold scale
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
      have basinEq : ∀ receiver ∈ object.receivers X threshold,
          (VisibleEntry.silentExcess object X threshold scale receiver).card =
            (VisibleEntry.excessBasin object X threshold scale receiver).card := by
        intro receiver receiverMem
        have isReceiver := FiniteObject.mem_receivers.mp receiverMem
        rw [VisibleEntry.silentExcess_eq_excessBasin object X threshold scale
          (exactDegree receiver isReceiver.1) isReceiver scalePos
          (fun saturated => (silent surplusZero) receiver isReceiver saturated)]
      have sums : (∑ receiver ∈ object.receivers X threshold,
            (VisibleEntry.silentExcess object X threshold scale
              receiver).card) =
          ∑ receiver ∈ object.receivers X threshold,
            (VisibleEntry.excessBasin object X threshold scale receiver).card :=
        Finset.sum_congr rfl basinEq
      have typeA : X ∈ Route8Census.typeAPieces object packing threshold scale := by
        simp only [Route8Census.typeAPieces, Finset.mem_filter, Finset.mem_image]
        exact ⟨⟨piece, member, rfl⟩, negative, surplusZero⟩
      simp only [excessMass, if_pos typeA]
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

/-- **`def:typeA-large-budget-deficit` with `lem:typeA-route8-burden`
substituted**: under the *silent-first* classification — not `thm:branch-kill`'s
— `|R| ≤ N_basin + s·|∂R| + F·s·T(n)`.  For the unified collection of
`def:typeA-unified-negative` this hypothesis fails on visible exit-(4) supports
(`rem:unified-covers-exit4`), which is exactly why `lem:typeA-unified-burden`
is not derivable from it. -/
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
    (classified : SilentClassification object packing threshold scale) :
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
          (excessMass object packing threshold scale (object.pieceSupport R piece) +
            scale * object.positiveDeficiency (object.pieceSupport R piece) threshold +
            massFactor * scale * object.ambientSurplus (object.pieceSupport R piece)
              threshold) :=
    Finset.sum_le_sum perPiece
  rw [object.sum_pieceSupport_card R, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, object.sum_positiveDeficiency_canonicalPieces,
    object.sum_ambientSurplus_canonicalPieces, sum_excessMass] at summed
  have deficiency := object.positiveDeficiency_le_boundaryIncidence R threshold baseline
  rw [← Route8Census.card_supply] at deficiency
  have surplusR := (object.ambientSurplus_le_degreeSurplus R threshold baseline).trans surplus
  have scaledDeficiency := Nat.mul_le_mul_left scale deficiency
  have scaledSurplus := Nat.mul_le_mul_left (massFactor * scale) surplusR
  omega

end Hypostructure.Graph.Route8Deficit
