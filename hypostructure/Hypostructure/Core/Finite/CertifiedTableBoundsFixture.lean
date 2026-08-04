import Hypostructure.Core.Finite.CertifiedTableBounds

namespace Hypostructure.Core.Finite.CertifiedTableBoundsFixture

open Hypostructure.Core.FiniteBitRelationBarrier
open Hypostructure.Core.Finite.CertifiedTableAggregation
open Hypostructure.Core.Finite.CertifiedTableBounds

private def profile : Profile 1 where
  row := fun _ _ => BitVec.ofFnLE (fun _ => true)

private inductive Length
  | unit

private def lengthValue : Length -> Nat
  | .unit => 0

private def relation : Length -> Fin 1 -> Fin 1 -> Bool :=
  fun _ _ _ => true

private inductive Index
  | unit

private instance : Fintype Index :=
  ⟨{ .unit }, by intro index; cases index; simp⟩

private def table :
    CertifiedTable profile Length lengthValue relation Index where
  semantic := by
    refine ⟨?_⟩
    intro length source target
    cases length
    simp [profile, lengthValue, relation]
  counts := {
    leftLength := fun _ => 0
    rightLength := fun _ => 0
    storedSafe := fun _ => 1
    storedFlat := fun _ => 1
    safeExact := by
      intro index
      cases index
      decide
    flatExact := by
      intro index
      cases index
      decide
  }

example : labelCount table = 1 := by rfl
example : countRowCount table = 1 := by decide
example : flatProduct table = 1 := by decide
example : safeProduct table = 1 := by decide

example (h : 2 ^ 0 * flatProduct table < safeProduct table) :
    Core.FiniteEntropy.RateFloorCertificate :=
  binaryRateFloor table (by decide) h

end Hypostructure.Core.Finite.CertifiedTableBoundsFixture
