import Hypostructure.Graph.Statements.TypeB

/-!
# Contracts: the Type B support family

Proof-agnostic facts about the assigned Type B supports `X = (Y_X, H_X)` of
`def:typeB-assigned-ledger`.  Every Type B argument reads only these common
consequences of the three entry forms, so each argument is proved once.
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- The assigned centres of either canonical form are high centres
(`def:typeB-assigned-ledger`, `def:decorated-fan-envelope`). -/
theorem TypeBAssignedCentres.high
    {packing : Finset (Finset object.Vertex)} {piece centres : Finset object.Vertex}
    (assigned : TypeBAssignedCentres data object packing piece centres) :
    ∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre := by
  intro centre member
  rcases assigned with ⟨_, _, rfl⟩ | ⟨_, _, envelope, _, rfl, _, _⟩
  · exact (Graph.TypeBRefinedSupport.mem_centres.mp member).2
  · exact envelope.decorations_high centre member

/-- The assigned centres include every high centre of the counted core: for the
ordinary support they are exactly its high centres, and a decorated core has
zero surplus, hence no high centre. -/
theorem TypeBAssignedCentres.centres_subset
    {packing : Finset (Finset object.Vertex)} {piece centres : Finset object.Vertex}
    (assigned : TypeBAssignedCentres data object packing piece centres) :
    Graph.TypeBRefinedSupport.centres object data.threshold piece ⊆ centres := by
  rcases assigned with ⟨_, _, rfl⟩ | ⟨_, zero, _⟩
  · exact Finset.Subset.refl _
  · intro centre member
    exfalso
    obtain ⟨inPiece, high⟩ := Graph.TypeBRefinedSupport.mem_centres.mp member
    have : object.degree centre - data.threshold = 0 := by
      unfold Graph.FiniteObject.ambientSurplus at zero
      exact Finset.sum_eq_zero_iff.mp zero centre inPiece
    exact absurd high (by
      show ¬ data.threshold < object.degree centre
      omega)

/-- Both canonical forms carry the negative net charge of their counted core. -/
theorem TypeBAssignedCentres.negative
    {packing : Finset (Finset object.Vertex)} {piece centres : Finset object.Vertex}
    (assigned : TypeBAssignedCentres data object packing piece centres) :
    object.NegativeNetCharge piece data.threshold data.dischargeScale := by
  rcases assigned with ⟨negative, _, _⟩ | ⟨negative, _, _⟩ <;> exact negative

namespace TypeBSupport

variable {packing : Finset (Finset object.Vertex)} {core centres : Finset object.Vertex}

theorem valid (support : TypeBSupport data object packing core centres) :
    object.IsWindowPacking data.windowOrder packing := support.1

theorem maximal (support : TypeBSupport data object packing core centres) :
    ∀ window : Finset object.Vertex,
      object.InducesWindow data.windowOrder window →
      ∃ member ∈ packing, ¬ Disjoint window member := support.2.1

theorem nonempty (support : TypeBSupport data object packing core centres) :
    centres.Nonempty := support.2.2.1

theorem high (support : TypeBSupport data object packing core centres) :
    ∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre :=
  support.2.2.2.1

/-- A heavy test on a Type B support: an assigned centre that is not heavy has
the unique high-but-not-heavy degree `δ + 1`. -/
theorem degree_eq_of_not_heavy
    (support : TypeBSupport data object packing core centres)
    {centre : object.Vertex} (member : centre ∈ centres)
    (notHeavy : ¬ data.threshold + 1 < object.degree centre) :
    object.degree centre = data.threshold + 1 := by
  have high := TypeBSupport.high support centre member
  simp only [Graph.IsHighCentre] at high
  omega

end TypeBSupport

/-- A canonical Type B support is a Type B support with a canonical core. -/
theorem TypeBCanonicalSupport.support
    {packing : Finset (Finset object.Vertex)}
    {piece : Graph.TypeBRefinedSupport.CanonicalPiece object packing}
    {centres : Finset object.Vertex}
    (canonical : TypeBCanonicalSupport data object packing piece centres) :
    TypeBSupport data object packing piece.vertices centres := canonical.1

theorem TypeBCanonicalSupport.assigned
    {packing : Finset (Finset object.Vertex)}
    {piece : Graph.TypeBRefinedSupport.CanonicalPiece object packing}
    {centres : Finset object.Vertex}
    (canonical : TypeBCanonicalSupport data object packing piece centres) :
    TypeBAssignedCentres data object packing piece.vertices centres := canonical.2

/-- A disjoint choice at the assigned centres restricts to every demand
subfamily. -/
theorem hasDisjointChoice_mono
    {threshold dischargeScale : Nat}
    {packing : Finset (Finset object.Vertex)}
    {piece assigned demands : Finset object.Vertex}
    (subset : demands ⊆ assigned)
    (choice : Graph.TypeBRefinedSupport.HasDisjointChoice object threshold
      dischargeScale packing piece assigned assigned) :
    Graph.TypeBRefinedSupport.HasDisjointChoice object threshold dischargeScale
      packing piece assigned demands := by
  obtain ⟨choice⟩ := choice
  exact ⟨{
    entry := fun hub member => choice.entry hub (subset member)
    eligible := fun hub member => choice.eligible hub (subset member)
    carrierDisjoint := fun left leftMem right rightMem different =>
      choice.carrierDisjoint left (subset leftMem) right (subset rightMem) different
    reserveDisjoint := fun left leftMem right rightMem different =>
      choice.reserveDisjoint left (subset leftMem) right (subset rightMem)
        different }⟩

/-- `lem:typeB-bridge-to-overlap`, both directions: at high assigned centres, a
disjoint choice fails exactly when a minimal overlap obstruction exists. -/
theorem not_hasDisjointChoice_iff_overlapObstruction
    {threshold dischargeScale : Nat}
    {packing : Finset (Finset object.Vertex)}
    {piece assigned : Finset object.Vertex}
    (high : ∀ hub ∈ assigned, Graph.IsHighCentre object threshold hub) :
    ¬ Graph.TypeBRefinedSupport.HasDisjointChoice object threshold dischargeScale
        packing piece assigned assigned ↔
      Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object threshold
        dischargeScale packing piece assigned) := by
  constructor
  · exact Graph.TypeBRefinedSupport.exists_overlapObstruction_of_not_hasDisjointChoice
      object threshold dischargeScale packing piece assigned high
  · rintro ⟨obstruction⟩ choice
    exact obstruction.noDisjointChoice
      (hasDisjointChoice_mono obstruction.demands_subset choice)

end Hypostructure.Graph.Contracts.TypeB
