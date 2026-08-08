import Hypostructure.Graph.DeclaredRankQuotient
import Hypostructure.Graph.Route8Residual

/-!
# Response delocalization at a presented route-8 entry

`def:typeA-trace-basin` clause (c): *"an equality among coordinates of
`ρ_u(B_u)` becomes target-complete only after adjoining a larger connected
support `Z ⊋ B_u`, either with `Z ⊊ G` or with `Z = G`"*.  That clause is exit
`(6)` of `def:typeA-saturated-exits`, and `lem:typeA-exits-discharged` disposes
of it in one sentence: *"Exit (6) is excluded by `lem:proper-smearing` in the
proper-support case and by `lem:no-silent-global-smearing` in the whole-graph
case."*

The two exclusions are not restated here.  `lem:proper-smearing` regards `Z` as a
boundaried graph and concludes that a target-complete dependence on a proper
`Z ⊊ G` is a replacement of that support; `lem:no-silent-global-smearing`
concludes that a target-complete whole-graph dependence has a strictly smaller
admissible closed representative.  Both conclusions are already the two clauses
of `def:admissible-rank-quotient` that `DeclaredQuotient` carries, and
`DeclaredQuotient.localize` is already the scope split between them.  So the
only thing this module has to supply is the manuscript's *datum*: the enlarging
support, the equality it makes target-complete, and the fact that no smaller
support does.

`PresentedEntry.declaredSupport` is the total declared-support field of the
coordinate presentation; it is not reconstructed from an event, because the
boundary-degree and other non-event coordinates also have declared supports.
`Delocalization` is the enlargement datum at one presented route-8 entry.  Its
`quotient` is the admissible rank quotient carried by `Z`; `enlarges` is
`Z ⊋ B_u`; `left`, `right`, `distinct` and `identified` are the *equality among
coordinates* the clause names; and `minimal` is *"only after adjoining"* —
no strictly smaller support identifies the same two coordinates admissibly, so
in particular the basin `B_u ⊊ Z` does not, which is what separates exit `(6)`
from exit `(5)`.

Nothing below knows what a route-8 entry means: the coordinate family, its
declared supports and the ambient target are all parameters, and the two
conclusions are the ones `def:admissible-rank-quotient` supplies.
-/

namespace Hypostructure.Graph.Route8

open Hypostructure

universe u

variable {object : FiniteObject.{u}}

/-- **`def:typeA-trace-basin` clause (c), at one presented entry.**

The equality of two declared coordinates of `ρ_u(B_u)` that becomes
target-complete only after adjoining the larger connected support `Z ⊋ B_u`.

The admissibility of the identification at `Z` is `DeclaredQuotient`: its
`connected` field is the clause's *connected* support, its `carries` field is
that `Z` carries the declared coordinate family, its `fibrewise` and
`contextUniversal` fields are target-completeness at `Z`, and its two
representative fields are `def:admissible-rank-quotient`'s proper and closed
clauses.  Nothing here re-derives them. -/
structure Delocalization (Baseline Target : FiniteObject.{u} → Prop)
    (presented : PresentedEntry object) : Type (u + 2) where
  /-- The larger connected support `Z` and the admissible identification it
  carries. -/
  quotient : DeclaredQuotient Baseline Target object presented.coordinates
    presented.declaredSupport
  /-- `Z ⊋ B_u`: the support strictly enlarges the trace basin. -/
  enlarges : presented.support ⊂ quotient.support
  /-- The first coordinate of the equality. -/
  left : presented.Coordinate
  /-- The second coordinate of the equality. -/
  right : presented.Coordinate
  /-- The first coordinate is declared by the entry's reading. -/
  leftMem : left ∈ presented.coordinates
  /-- The second coordinate is declared by the entry's reading. -/
  rightMem : right ∈ presented.coordinates
  /-- The equality is between *two* coordinates, so the identification is a
  genuine rank reduction of the declared family. -/
  distinct : left ≠ right
  /-- The equality itself: the quotient at `Z` identifies them. -/
  identified : quotient.label left = quotient.label right
  /-- *"Only after adjoining"*: no strictly smaller admissible support
  identifies the two coordinates.  Since `B_u ⊊ Z`, the basin is one such
  support, so the equality is not already target-complete at `ρ_u(B_u)` — which
  is what distinguishes clause (c) from clause (b). -/
  minimal : ∀ narrower : DeclaredQuotient Baseline Target object
      presented.coordinates presented.declaredSupport,
    narrower.support ⊂ quotient.support →
    narrower.label left ≠ narrower.label right

namespace Delocalization

variable {Baseline Target : FiniteObject.{u} → Prop}
variable {presented : PresentedEntry object}
variable (delocalization : Delocalization Baseline Target presented)

/-- The identification is rank-reducing on the declared family: it is an
equality between two *distinct* declared coordinates. -/
theorem reducing :
    ¬ Set.InjOn delocalization.quotient.label ↑presented.coordinates :=
  fun injective =>
    delocalization.distinct
      (injective (Finset.mem_coe.mpr delocalization.leftMem)
        (Finset.mem_coe.mpr delocalization.rightMem)
        delocalization.identified)

/-- **`lem:proper-smearing` and `lem:no-silent-global-smearing`, applied
respectively.**

The scope of the enlarging support decides which of the manuscript's two
exclusions fires: at `Z ⊊ G` the admissible rank quotient is a replacement of
the proper boundaried support `Z`, and at `Z = G` it is a strictly smaller
admissible closed representative.  The split is
`DeclaredQuotient.localize`, which is `SupportAtom.classifyScope` on `Z` — the
manuscript's own `Z ⊊ G` / `Z = G` case distinction and no other. -/
theorem localize :
    Strategy.InterfaceReplacement.ReplacementSupport Baseline Target object
        delocalization.quotient.support ∨
      ∃ representative : FiniteObject.{u},
        representative.LexicographicallySmaller object ∧
          Baseline representative ∧ (Target representative → Target object) :=
  delocalization.quotient.localize delocalization.reducing

/-- **`lem:proper-smearing`.**  At a proper enlarging support the dependence is
a replacement of that support. -/
theorem properReplacement (proper : ∃ vertex, vertex ∉ delocalization.quotient.support) :
    Strategy.InterfaceReplacement.ReplacementSupport Baseline Target object
      delocalization.quotient.support :=
  delocalization.quotient.properRepresentative proper delocalization.reducing

/-- **`lem:no-silent-global-smearing`.**  At `Z = G` the dependence supplies a
strictly smaller admissible closed representative. -/
theorem closedRepresentative
    (covers : ∀ vertex, vertex ∈ delocalization.quotient.support) :
    ∃ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object ∧
        Baseline representative ∧ (Target representative → Target object) :=
  delocalization.quotient.closedRepresentative covers delocalization.reducing

end Delocalization

/-- **Exit `(6)` at one indexed entry of a route-8 collection.**

The entry's reading has an equality among its declared coordinates that
delocalizes to a larger connected support.  The datum is existential because the
manuscript's clause is: *some* equality, at *some* enlarging support. -/
def Data.Delocalizes {Target : FiniteObject.{u} → Prop}
    (data : Data Target object) (Baseline : FiniteObject.{u} → Prop)
    (index : data.Index) : Prop :=
  Nonempty (Delocalization Baseline Target (data.presented index))

/-- **`lem:typeA-exits-discharged`'s exit-`(6)` sentence at an indexed entry.**

*"Exit (6) is excluded by `lem:proper-smearing` in the proper-support case and by
`lem:no-silent-global-smearing` in the whole-graph case."*  An entry that
delocalizes therefore hands the branch exactly one of the two conclusions the
manuscript names, decided by the scope of the enlarging support and by nothing
else. -/
theorem Data.localize_of_delocalizes {Target : FiniteObject.{u} → Prop}
    {data : Data Target object} {Baseline : FiniteObject.{u} → Prop}
    {index : data.Index} (delocalizes : data.Delocalizes Baseline index) :
    (∃ support : Finset object.Vertex,
        Strategy.InterfaceReplacement.ReplacementSupport Baseline Target object
          support) ∨
      ∃ representative : FiniteObject.{u},
        representative.LexicographicallySmaller object ∧
          Baseline representative ∧ (Target representative → Target object) := by
  obtain ⟨delocalization⟩ := delocalizes
  rcases delocalization.localize with replacement | representative
  · exact Or.inl ⟨_, replacement⟩
  · exact Or.inr representative

/-- **(R2) for exit `(6)`**: no indexed entry of any route-8 collection of the
object delocalizes.  This is the absence clause the route-8 arm is entered on,
in the same shape as `ExitFourFree` and `TraceSurviving`. -/
def DelocalizationFree (Baseline Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) : Prop :=
  ∀ data : Data Target object, ∀ index ∈ data.entries,
    ¬ data.Delocalizes Baseline index

end Hypostructure.Graph.Route8
