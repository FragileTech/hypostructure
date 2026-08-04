import Hypostructure.FiniteChecks.ColdResponse.Semantic

/-!
# Generated complete cold-response encoding table
-/

namespace Hypostructure.FiniteChecks.ColdResponse

/-- Canonical enumeration of a finite index type. -/
def allFin (n : Nat) : List (Fin n) :=
  List.ofFn id

theorem mem_allFin (index : Fin n) : index ∈ allFin n := by
  simp [allFin]

/-- Cartesian enumeration of all inert same-interface encodings.  Every
dimension is the length of a carrier in `Signature`. -/
def generate (signature : Signature) : List (Encoding signature) :=
  (allFin signature.interfaceLabels.length).flatMap fun interfaceIndex =>
    (allFin signature.germStates.length).flatMap fun sourceIndex =>
      (allFin signature.germStates.length).flatMap fun replacementIndex =>
        (allFin signature.contextStates.length).map fun contextIndex =>
          ⟨interfaceIndex, sourceIndex, replacementIndex, contextIndex⟩

theorem mem_generate (row : Encoding signature) :
    row ∈ generate signature := by
  rcases row with ⟨interfaceIndex, sourceIndex, replacementIndex, contextIndex⟩
  simp [generate, mem_allFin]

theorem generate_complete :
    ∀ row : Encoding signature, row ∈ generate signature :=
  mem_generate

theorem generate_length (signature : Signature) :
    (generate signature).length =
      signature.interfaceLabels.length *
        signature.germStates.length *
        signature.germStates.length *
        signature.contextStates.length := by
  simp [generate, allFin, List.length_ofFn]
  simp [Nat.mul_assoc]

end Hypostructure.FiniteChecks.ColdResponse
