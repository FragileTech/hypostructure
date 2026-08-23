import Hypostructure.Graph.TypeBOverlapResponseCoordinate

namespace Hypostructure.Graph.TypeBRefinedSupport

universe u

example {object : FiniteObject.{u}} {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing}
    {assigned : Finset object.Vertex}
    (obstruction : OverlapObstruction object threshold dischargeScale packing
      piece.vertices assigned) :
    overlapCoordinateSchedule object threshold dischargeScale packing
      piece.vertices assigned obstruction ≠ [] :=
  obstruction.overlapCoordinateSchedule_nonempty

example {object : FiniteObject.{u}} {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing}
    {assigned : Finset object.Vertex}
    {obstruction : OverlapObstruction object threshold dischargeScale packing
      piece.vertices assigned}
    {coordinate : RawOverlapCoordinate object} :
    coordinate ∈ overlapCoordinateSchedule object threshold dischargeScale
      packing piece.vertices assigned obstruction ↔
      coordinate.IsFor obstruction :=
  mem_overlapCoordinateSchedule_iff

end Hypostructure.Graph.TypeBRefinedSupport
