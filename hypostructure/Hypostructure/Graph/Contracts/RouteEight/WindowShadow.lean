import Hypostructure.Graph.Contracts.RouteEight.Basic
import Hypostructure.Graph.WindowShadowHit

/-!
# Contracts: window attachment signatures

`def:typeA-window-attachment-shadow`, `lem:typeA-singleton-shadow-table`,
`def:typeA-recorded-window-shadow-hit` and `lem:typeA-window-shadow-hit-routes`
on the selected object.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **`def:typeA-window-attachment-shadow`**: the signature test is exactly the
failure of the singleton window-label safety relation, for a dyadic target. -/
theorem windowShadowSignature (data : Parameters) (object : FiniteObject.{u})
    (lengthOK_iff : ∀ length,
      data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    WindowShadowSignatureStatement data object := by
  classical
  intro support window s a b
  have distance : Nat.dist a.1 b.1 < data.windowOrder := by
    rcases Nat.le_total a.1 b.1 with hab | hba
    · rw [Nat.dist_eq_sub_of_le hab]
      omega
    · rw [Nat.dist_eq_sub_of_le_right hba]
      omega
  rw [Graph.WindowAttachmentShadow.mem_shadow]
  simp [b.isLt, distance, Graph.WindowCurvature.Safe,
    Graph.WindowCurvature.ForbiddenGap,
    Graph.WindowCurvature.closingLength,
    lengthOK_iff]

/-- **The tail of `lem:typeA-singleton-shadow-table`**: beyond window order
plus five, two distinct dyadic lengths cannot both fall in one attachment
interval, so at most one forbidden distance remains. -/
theorem windowShadowSingletonTail (data : Parameters) (object : FiniteObject.{u})
    (lengthOK_iff : ∀ length,
      data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    WindowShadowSingletonTailStatement data object := by
  intro support window s tail
  apply Graph.WindowAttachmentShadow.card_forbiddenDistances_le_one
  intro d₁ bound₁ d₂ bound₂ accepted₁ accepted₂
  obtain ⟨q₁, _lower₁, length₁⟩ :=
    (Core.DyadicLength.powerOfTwoLength_iff _).mp
      ((lengthOK_iff _).mp accepted₁)
  obtain ⟨q₂, _lower₂, length₂⟩ :=
    (Core.DyadicLength.powerOfTwoLength_iff _).mp
      ((lengthOK_iff _).mp accepted₂)
  rcases lt_trichotomy q₁ q₂ with before | same | after
  · have gap : 2 ^ q₁ * 2 ≤ 2 ^ q₂ := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by decide) before
    omega
  · rw [same] at length₁
    omega
  · have gap : 2 ^ q₂ * 2 ≤ 2 ^ q₁ := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by decide) after
    omega

/-- **`def:typeA-recorded-window-shadow-hit`, certificate (O1)**: a recorded
hit closes an actual simple cycle of accepted length through the corridor and
the window arc. -/
theorem windowShadowHitCycle (data : Parameters) (object : FiniteObject.{u}) :
    WindowShadowHitCycleStatement data object := by
  classical
  intro window x y a b corridor corridorPath corridorAvoids
    attachA attachB edgesDistinct hit
  obtain ⟨arc, arcPath, arcLength, arcWindow⟩ :=
    Graph.WindowShadowHit.exists_window_arc window a b
  let tail := corridor.append (SimpleGraph.Walk.cons attachB arc)
  have tailPath : tail.IsPath := by
    have supportEq : tail.support = corridor.support ++
        (SimpleGraph.Walk.cons attachB arc).support.tail :=
      SimpleGraph.Walk.support_append _ _
    rw [SimpleGraph.Walk.isPath_def, supportEq,
      SimpleGraph.Walk.support_cons, List.tail_cons, List.nodup_append]
    refine ⟨corridorPath.support_nodup, arcPath.support_nodup, ?_⟩
    intro v vCorridor v' vArc
    obtain ⟨i, rfl⟩ := arcWindow v' vArc
    intro same
    exact corridorAvoids i (same ▸ vCorridor)
  have edgeFresh : s(window a, x) ∉ tail.edges := by
    intro member
    rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
      List.mem_append, List.mem_cons] at member
    rcases member with corridorEdge | attachEdge | arcEdge
    · exact corridorAvoids a
        (corridor.fst_mem_support_of_mem_edges corridorEdge)
    · exact edgesDistinct (by
        rw [Sym2.eq_swap] at attachEdge
        exact attachEdge)
    · obtain ⟨i, eq⟩ :=
        arcWindow x (arc.snd_mem_support_of_mem_edges arcEdge)
      exact corridorAvoids i (eq ▸ corridor.start_mem_support)
  let cycle := SimpleGraph.Walk.cons attachA tail
  have isCycle : cycle.IsCycle :=
    (SimpleGraph.Walk.cons_isCycle_iff tail attachA).mpr
      ⟨tailPath, edgeFresh⟩
  have length : cycle.length =
      corridor.length + 2 + Nat.dist a.1 b.1 := by
    simp only [cycle, tail, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_append, arcLength]
    omega
  refine ⟨cycle, isCycle, length, ?_⟩
  rw [length]
  exact Graph.WindowAttachmentShadow.accepted_of_mem_shadow hit

/-- **`lem:typeA-window-shadow-hit-routes`**: the selected object has no
target cycle, so it has no recorded shadow hit. -/
theorem windowShadowHitExcluded (data : Parameters) (object : FiniteObject.{u})
    (noTarget : ¬ HasCycleWithLength data.LengthOK object)
    (hitCycle : WindowShadowHitCycleStatement data object) :
    WindowShadowHitExcludedStatement data object := by
  intro window x y a b corridor path avoids attachA attachB distinct hit
  obtain ⟨cycle, isCycle, _length, accepted⟩ :=
    hitCycle
      window x y a b corridor path avoids attachA attachB distinct hit
  exact noTarget
    ⟨⟨window a, cycle, isCycle, accepted⟩⟩

end Hypostructure.Graph.Contracts.RouteEight
