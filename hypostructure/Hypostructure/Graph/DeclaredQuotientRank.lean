import Hypostructure.Graph.DeclaredRankQuotient
import Hypostructure.Graph.InterfaceReplacement

/-!
# Declared quotients: rank of an admissible quotient

An admissible declared quotient of G is label-injective on any object without
a replacement support whose lexicographically smaller baseline objects all hit
the target, and therefore loses no rank on its family.

Nothing here knows a presentation, a ledger, or a manuscript.
-/

namespace Hypostructure.Graph.DeclaredQuotientRank

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

variable {object : FiniteObject.{u}}

/-- Generic (no EG vocabulary): on any object with no replacement support and
whose every lexicographically smaller baseline object hits the target while it
does not, every admissible declared quotient is label-injective. -/
theorem declared_labelInjective_generic {Baseline Target : Graph.FiniteObject.{u} → Prop}
    {obj : Graph.FiniteObject.{u}}
    (noReplacement : ∀ S : Finset obj.Vertex, ¬ ReplacementSupport Baseline Target obj S)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller obj →
      Baseline H → Target H)
    (_avoid : ¬ Target obj)
    {Coordinate : Type u} {family : Finset Coordinate}
    {cs : Coordinate → Finset obj.Vertex}
    (quotient : DeclaredQuotient Baseline Target obj family cs) :
    Set.InjOn quotient.label ↑family := by
  by_contra reducing
  rcases quotient.localize reducing with replacement | ⟨H, smaller, baseline, noTarget⟩
  · exact noReplacement _ replacement
  · exact noTarget (minimal H smaller baseline)

end Hypostructure.Graph.DeclaredQuotientRank
