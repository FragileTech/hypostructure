import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle

/-!
# Contract lemmas: the named sparse exits of node `[125]`

`def:named-surplus-exits` on the selected minimal counterexample: the named
exits are the two cycle conclusions in G, an accepted cycle (a) and a
suppression-chord certificate whose lifted length is accepted (e), and G's
selection refutes both.  Hence G has none of the named sparse exits
(`not_declaredSparseSurplusExit`), which is `[125]`'s survivor fact.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- **G has none of the named sparse exits** (node `[125]`,
`def:named-surplus-exits`; Lean improvement: the survivor fact is a theorem
about G).  Exit (a) is an accepted cycle of G and exit (e) expands to one, and
`[4]`'s selection says G has no accepted cycle. -/
theorem not_declaredSparseSurplusExit
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (selected : SelectionStatement BranchState Presentation presentation data
      object) :
    ¬ DeclaredSparseSurplusExit data object := by
  intro exit
  cases exit with
  | dyadic cycle =>
      exact selected.1 cycle
  | suppressionChord family certificate violates =>
      let expanded := family.expandCycle certificate
      have accepted : data.LengthOK expanded.walk.length := by
        rw [expanded.length_eq]
        exact violates
      exact selected.1
        ⟨⟨family.sourceVertex certificate.vertex, expanded.walk,
          expanded.isCycle, accepted⟩⟩

end Hypostructure.Graph.Contracts.SurplusPair
