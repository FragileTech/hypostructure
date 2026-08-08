import Hypostructure.Graph.TypeAExitSevenGermSchedule

/-!
# Fixture: finite exit-`(7)` connector-germ prefix
-/

namespace Hypostructure.Fixtures.TypeAExitSevenGermSchedule

open Hypostructure.Graph
open Hypostructure.Graph.DecoratedHandoff

universe u

variable {object : FiniteObject.{u}}
variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver : object.Vertex} {peeled : Finset object.Vertex}

noncomputable section

variable (package : ExitFour.VisibleFourUnpeeledPackage support threshold scale
  receiver peeled)

example (selected : package.SelectedGerm) :
    selected ∈ package.germSchedule.values :=
  package.mem_germSchedule selected

example (pair : package.GermPair) :
    pair ∈ package.germPairSchedule.values :=
  package.mem_germPairSchedule pair

example (pair : package.GermPair) :
    SeparatesAt pair.left.germ.path pair.right.germ.path
      pair.firstSeparator.separator :=
  pair.firstSeparator_separatesAt

example (pair : package.GermPair) :
    pair.separatorOrder =
      pair.firstSeparator.separator :: pair.firstSeparator.remaining :=
  pair.separatorOrder_eq_cons

end

end Hypostructure.Fixtures.TypeAExitSevenGermSchedule
