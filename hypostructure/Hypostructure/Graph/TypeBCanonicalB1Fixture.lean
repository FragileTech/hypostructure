import Hypostructure.Graph.TypeBRefinedSupport

namespace Hypostructure.Graph.TypeBRefinedSupport

universe u

open Classical

example {object : FiniteObject.{u}} {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing} {hub : object.Vertex}
    (profile : TypeBFanClosedPorts.Profile object)
    (localReserve : LocalReserveBlock object)
    (chosenNonWindow : Finset (object.Vertex × object.Vertex))
    (eligible : (CandidateData.positive profile localReserve chosenNonWindow).IsCandidate
      threshold dischargeScale piece hub) :
    0 ≤ (CandidateData.positive profile localReserve chosenNonWindow).entryPayment₂
        threshold dischargeScale piece hub ∧
      2 * TypeBFanIncidence.scaledDeficit object threshold dischargeScale
          profile.envelope hub ≤
        (dischargeScale : Int) *
          ((TypeBHybridIncidence.windowIncidences object threshold
              profile.envelope (object.windowSupport packing) hub : Int) +
            (chosenNonWindow.card : Int)) ∧
      TypeBHybridIncidence.nonWindowDemand object threshold dischargeScale
          profile.envelope (object.windowSupport packing) hub ≤
        (dischargeScale : Int) * (chosenNonWindow.card : Int) :=
  CandidateData.positiveCandidate_localB1 profile localReserve chosenNonWindow
    eligible

example {object : FiniteObject.{u}} {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) :
    HasDisjointChoice object threshold dischargeScale piece
          (centres object threshold piece.vertices) ∨
        Nonempty (OverlapObstruction object threshold dischargeScale piece) :=
  b2_or_overlap object threshold dischargeScale piece

end Hypostructure.Graph.TypeBRefinedSupport
