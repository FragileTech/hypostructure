import Hypostructure.Graph.TypeAVisibleD1Coordinates

/-!
# The selected visible Q1 origin pair

This file retains only the finite data that exist before any semantic response
quotient is constructed: two distinct loads from the canonical visible-four
package, their actual scheduled receiver-entry returns, and the exact D1
entry/value/support data derived from those returns.

No response system, quotient, reading state, replacement, or routing result is
defined here. Those belong to the semantic Q1 construction downstream.
-/

namespace Hypostructure.Graph.ExitFour

open Hypostructure

universe u

variable {object : FiniteObject.{u}}

attribute [local instance] vertexDecEq

namespace VisibleFourUnpeeledPackage

variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver : object.Vertex} {peeled : Finset object.Vertex}

/-- Two distinct originating loads from the canonical selected package. All
return, response, and support data below are derived from these origins. -/
structure Q1OriginPair
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled) where
  left : package.SelectedLoad
  right : package.SelectedLoad
  distinct : left ≠ right

namespace Q1OriginPair

variable
    {package : VisibleFourUnpeeledPackage support threshold scale receiver peeled}
    (pair : package.Q1OriginPair)

/-- The actual scheduled returns retained by the two originating loads. -/
noncomputable def leftReturn := package.selectedReturn pair.left.1 pair.left.2
noncomputable def rightReturn := package.selectedReturn pair.right.1 pair.right.2

/-- Their exact D1 response coordinates. -/
noncomputable def leftD1 : TraceCoordinateSystem.D1.Coordinate object support :=
  package.selectedD1Map pair.left

noncomputable def rightD1 : TraceCoordinateSystem.D1.Coordinate object support :=
  package.selectedD1Map pair.right

/-- Their exact uncapped boundary-degree response values. -/
noncomputable def leftValue : Nat :=
  TraceCoordinateSystem.D1.value object support pair.leftD1

noncomputable def rightValue : Nat :=
  TraceCoordinateSystem.D1.value object support pair.rightD1

/-- Their exact singleton declared supports. -/
noncomputable def leftSupport : Finset object.Vertex :=
  TraceCoordinateSystem.D1.declaredSupport object support pair.leftD1

noncomputable def rightSupport : Finset object.Vertex :=
  TraceCoordinateSystem.D1.declaredSupport object support pair.rightD1

@[simp] theorem leftSupport_eq :
    pair.leftSupport = {(pair.leftReturn).entry} := by
  rfl

@[simp] theorem rightSupport_eq :
    pair.rightSupport = {(pair.rightReturn).entry} := by
  rfl

end Q1OriginPair

/-- The collision branch supplies its actual originating pair. -/
theorem exists_q1OriginPair_of_collision
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (collision : package.HasSelectedD1Collision) :
    ∃ pair : package.Q1OriginPair, pair.leftD1 = pair.rightD1 := by
  rcases collision with ⟨left, right, distinct, equality⟩
  exact ⟨⟨left, right, distinct⟩, equality⟩

/-- In the injective branch, the first two loads in the canonical selected list
form the origin pair. The cardinal premise is discharged from the paper's
presentation (`scale = 4`) upstream; no duplicate numeral is introduced. -/
theorem exists_first_q1OriginPair_of_injective
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (two_le_scale : 2 ≤ scale)
    (injective : Function.Injective package.selectedD1Map) :
    ∃ pair : package.Q1OriginPair, pair.leftD1 ≠ pair.rightD1 := by
  classical
  let loads := selectedVisibleUnpeeledLoads support threshold scale receiver
    package.outside peeled
  have lengthEq : loads.length = scale := package.loadCount
  cases loadsEq : loads with
  | nil =>
      simp [loads, loadsEq] at lengthEq
      omega
  | cons left tail =>
      cases tailEq : tail with
      | nil =>
          simp [loads, loadsEq, tailEq] at lengthEq
          omega
      | cons right rest =>
          have leftMem : left ∈ selectedVisibleUnpeeledLoads support threshold scale
              receiver package.outside peeled := by
            simpa [loads, loadsEq, tailEq]
          have rightMem : right ∈ selectedVisibleUnpeeledLoads support threshold scale
              receiver package.outside peeled := by
            simpa [loads, loadsEq, tailEq]
          let leftLoad : package.SelectedLoad := ⟨left, leftMem⟩
          let rightLoad : package.SelectedLoad := ⟨right, rightMem⟩
          have leftNeRight : leftLoad ≠ rightLoad := by
            intro equality
            have vertexEquality : left = right := congrArg Subtype.val equality
            have nodup : loads.Nodup := by
              simpa [loads] using package.loadNodup
            rw [loadsEq, tailEq] at nodup
            have rightNotMem := (List.nodup_cons.mp nodup).1
            exact rightNotMem (vertexEquality ▸ List.mem_cons_self)
          let pair : package.Q1OriginPair := ⟨leftLoad, rightLoad, leftNeRight⟩
          refine ⟨pair, ?_⟩
          exact fun equality => pair.distinct (injective equality)

end VisibleFourUnpeeledPackage

end Hypostructure.Graph.ExitFour
