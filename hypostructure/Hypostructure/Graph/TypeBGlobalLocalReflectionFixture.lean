import Hypostructure.Graph.TypeBGlobalLocalReflection

namespace Hypostructure.Graph.TypeBRefinedSupport

universe u

example
    {presentation : TypeAB.Presentation.{u}}
    {object : FiniteObject.{u}} {order : ℕ} {LengthOK : ℕ → Prop}
    {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing}
    {assigned : Finset object.Vertex}
    (obstruction : OverlapObstruction object threshold dischargeScale packing
      piece.vertices assigned)
    (targetSafe : TypeAB.ContextuallyDyadicSafe presentation object)
    (normalForms : ∀ hub ∈ obstruction.demands,
      NormalForm object threshold hub)
    (cycleFree : ∀ hub ∈ obstruction.demands,
      TypeBDirectCycle.DirectCycleFree object order LengthOK packing hub) :
    GlobalLocalReflectionACE presentation object order LengthOK threshold
      dischargeScale piece assigned obstruction :=
  globalLocalReflectionACE obstruction targetSafe normalForms cycleFree

end Hypostructure.Graph.TypeBRefinedSupport
