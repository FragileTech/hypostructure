import Hypostructure.Graph.TypeAVisibleQ1Pair

namespace Hypostructure.Graph.ExitFour

open Hypostructure

universe u

variable {object : FiniteObject.{u}}
variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver : object.Vertex} {peeled : Finset object.Vertex}

attribute [local instance] vertexDecEq

namespace VisibleFourUnpeeledPackage

example
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (collision : package.HasSelectedD1Collision) :
    ∃ pair : package.Q1OriginPair, pair.leftD1 = pair.rightD1 :=
  exists_q1OriginPair_of_collision package collision

example
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (two_le_scale : 2 ≤ scale)
    (injective : Function.Injective package.selectedD1Map) :
    ∃ pair : package.Q1OriginPair, pair.leftD1 ≠ pair.rightD1 :=
  exists_first_q1OriginPair_of_injective package two_le_scale injective

example
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (pair : package.Q1OriginPair) :
    pair.leftSupport = {(pair.leftReturn).entry} ∧
      pair.rightSupport = {(pair.rightReturn).entry} :=
  ⟨pair.leftSupport_eq, pair.rightSupport_eq⟩

end VisibleFourUnpeeledPackage
end Hypostructure.Graph.ExitFour
