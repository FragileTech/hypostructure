import Hypostructure.Graph.TypeBOverlapResponseCoordinate

namespace Hypostructure.Graph.TypeBRefinedSupport

universe u

example {object : FiniteObject.{u}} {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing}
    (obstruction : OverlapObstruction object threshold dischargeScale piece) :
    overlapCoordinateSchedule object threshold dischargeScale piece obstruction ≠ [] :=
  obstruction.overlapCoordinateSchedule_nonempty

example {object : FiniteObject.{u}} {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing}
    {obstruction : OverlapObstruction object threshold dischargeScale piece}
    {coordinate : RawOverlapCoordinate object} :
    coordinate ∈ overlapCoordinateSchedule object threshold dischargeScale piece obstruction ↔
      coordinate.IsFor obstruction :=
  mem_overlapCoordinateSchedule_iff

end Hypostructure.Graph.TypeBRefinedSupport
