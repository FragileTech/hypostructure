import Hypostructure.Graph.LabelledRelabeling
import Hypostructure.Graph.RemainderEntropy

namespace Hypostructure.Fixtures.RemainderRelabelingProof

open Hypostructure Graph
open Hypostructure.Graph.LabelledRelabeling

example (n : Nat) : (n / 2) ^ (n - n / 2) ≤ Nat.factorial n := by
  exact Core.FiniteRelabelingOrbit.half_pow_le_factorial n

example (component : FiniteObject) (root : component.Vertex)
    (connected : component.graph.Preconnected)
    (subcubic : ∀ vertex, component.degree vertex ≤ 3) :
    Nat.card (component.Iso component) ≤
      Nat.card component.Vertex * 6 ^ Nat.card component.Vertex := by
  exact component.card_automorphisms_le_card_mul_six_pow root connected subcubic

example {n : Nat} (window : Finset (Fin n)) {State : Type*}
    (state : LabelledOn n → State) (skeleton : LabelledOn n)
    (invariant : ∀ permutation : FixedSupportPermutations window,
      state (permutation • skeleton) = state skeleton) :
    Nat.card (FixedSupportPermutations window) ≤
      Nat.card {candidate | state candidate = state skeleton} *
        Nat.card (MulAction.stabilizer
          (FixedSupportPermutations window) skeleton) := by
  exact fixedSupport_card_le_state_fibre_card_mul_stabilizer
    window state skeleton invariant

end Hypostructure.Fixtures.RemainderRelabelingProof
