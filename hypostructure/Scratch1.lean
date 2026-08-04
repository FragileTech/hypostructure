import Hypostructure.Graph.PackedWindowRealization

open Hypostructure Hypostructure.Graph

example (m n : Nat) (h : m ≤ n) :
    Nat.card (LabelledOn m) ≤ Nat.card (LabelledOn n) := by
  refine Nat.card_le_card_of_injective
    (fun g => (⟨SimpleGraph.map (Fin.castLEEmb h) g.graph⟩ : LabelledOn n)) ?_
  intro a b equal
  have graphEq := congrArg LabelledOn.graph equal
  exact LabelledOn.ext (SimpleGraph.map_injective (Fin.castLEEmb h) graphEq)
