import Hypostructure.Graph.TraceBasinAlternatives

/-!
# Exact visible-entry quotient compatibility import

Clause (Q1) of `def:typeA-exit4-family` is
`Graph.ExitFour.Q1TargetDefect`.  It is
formed only from an actual `VisibleFourUnpeeledPackage.Q1OriginPair`; both
response coordinates and both same-interface response pieces are computed from
that selected pair.
-/

namespace Hypostructure.Graph.ExitFour

open Hypostructure
open Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}}
variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver : object.Vertex} {peeled : Finset object.Vertex}

attribute [local instance] vertexDecEq

namespace VisibleFourUnpeeledPackage

/-- A selected load of the package is an unpeeled routed load. -/
theorem selected_mem_unpeeledLoads
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    {load : object.Vertex}
    (member : load ∈ selectedVisibleUnpeeledLoads support threshold scale
      receiver package.outside peeled) :
    load ∈ unpeeledLoads support threshold receiver peeled :=
  (Finset.mem_inter.mp (package.load_mem member)).2

/-- **The Q1 exit-(4) witness of a target-defective origin pair**
(`lem:typeA-unpeeled-visible-routing`, the Q1 sentence): a compatible outside
context distinguishing the two selected response realizations makes the
identifying quotient target-defective in the canonical family `Q_4(w)`, and its
declared routed-load support contains the pair's own selected loads. -/
def witnessOfPairTargetDefect {Target : FiniteObject.{u} → Prop}
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (pair : package.Q1OriginPair)
    (targetDefect : Response.TargetDefect Target
      (visibleResponsePiece pair.leftResponseCoordinate)
      (visibleResponsePiece pair.rightResponseCoordinate)) :
    Witness Target support threshold scale receiver peeled where
  load := pair.left.1
  unpeeled := package.selected_mem_unpeeledLoads pair.left.2
  member := .q1 ⟨peeled, package, pair, Or.inl rfl, targetDefect⟩

@[simp] theorem witnessOfPairTargetDefect_load {Target : FiniteObject.{u} → Prop}
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (pair : package.Q1OriginPair)
    (targetDefect : Response.TargetDefect Target
      (visibleResponsePiece pair.leftResponseCoordinate)
      (visibleResponsePiece pair.rightResponseCoordinate)) :
    (witnessOfPairTargetDefect package pair targetDefect).load = pair.left.1 :=
  rfl

/-- **The Q1 semantic dichotomy** (`lem:typeA-unpeeled-visible-routing`, after
exits (1)–(3) are removed): either some origin pair of the package is
target-defective — and then the package supplies an exit-(4) witness at one of
its own selected visible unpeeled loads — or every origin pair's two selected
response realizations are target-complete, the identification entering exits
(5)–(7).  The common boundary-degree fibre is
`visibleResponsePiece_boundaryDegreeProfile`; the exhaustiveness is
`lem:context-universality` (`Response.contextEquivalent_or_targetDefect`). -/
theorem exists_witness_or_pairwise_targetComplete
    {Target : FiniteObject.{u} → Prop}
    (package : VisibleFourUnpeeledPackage support threshold scale receiver
      peeled) :
    (∃ witness : Witness Target support threshold scale receiver peeled,
        witness.load ∈ selectedVisibleUnpeeledLoads support threshold scale
          receiver package.outside peeled) ∨
      ∀ pair : package.Q1OriginPair,
        Response.TargetComplete BoundaryPiece.boundaryDegreeProfile Target
          (visibleResponsePiece pair.leftResponseCoordinate)
          (visibleResponsePiece pair.rightResponseCoordinate) := by
  classical
  by_cases defect : ∃ pair : package.Q1OriginPair,
      Response.TargetDefect Target
        (visibleResponsePiece pair.leftResponseCoordinate)
        (visibleResponsePiece pair.rightResponseCoordinate)
  · obtain ⟨pair, targetDefect⟩ := defect
    exact Or.inl
      ⟨witnessOfPairTargetDefect package pair targetDefect, pair.left.2⟩
  · refine Or.inr fun pair => ⟨?_, ?_⟩
    · exact (visibleResponsePiece_boundaryDegreeProfile
        pair.leftResponseCoordinate).trans
        (visibleResponsePiece_boundaryDegreeProfile
          pair.rightResponseCoordinate).symm
    · rcases Response.contextEquivalent_or_targetDefect Target
          (visibleResponsePiece pair.leftResponseCoordinate)
          (visibleResponsePiece pair.rightResponseCoordinate) with
        equivalent | bad
      · exact equivalent
      · exact absurd ⟨pair, bad⟩ defect

/-- **`lem:typeA-unpeeled-visible-routing` under the standing invariants**:
either some selected visible unpeeled load of the overloaded port carries an
exit-(4) witness at the current peeling, or every selected visible unpeeled
load is a route-8 entry.  The per-load routing closes exits (5) and (6)
against the read uncompressibility, replacement-exclusion, avoidance and
minimality facts, and a surviving separator is refuted by the read
no-separator hypothesis (`lem:typeA-exits-discharged` at each selected
load's trace basin). -/
theorem exists_witness_or_forall_route8Entry
    {LengthOK : Nat → Prop}
    (package : VisibleFourUnpeeledPackage support threshold scale receiver
      peeled)
    (connected : SupportComponents.Connected.ConnectedOn object support)
    (noQuotient : ∀ load ∈ selectedVisibleUnpeeledLoads support threshold
        scale receiver package.outside peeled,
      ∀ basin : Finset object.Vertex,
      Route8.TraceBasin.select? object support threshold receiver load =
        some basin →
      ¬ ∃ retained,
        Route8.TraceBasin.TraceResponseQuotient object support threshold
          LengthOK receiver load basin retained)
    (exclusion : ∀ enlarged : Finset object.Vertex,
      ¬ Strategy.InterfaceReplacement.ReplacementSupport
          (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object
          enlarged)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold representative →
      HasCycleWithLength LengthOK representative)
    (noSeparator : ∀ load ∈ selectedVisibleUnpeeledLoads support threshold
        scale receiver package.outside peeled,
      ∀ basin : Finset object.Vertex,
      ¬ Route8.TraceBasin.TraceSurvivingSeparator object support threshold
        LengthOK receiver load basin) :
    (∃ witness : Witness (HasCycleWithLength LengthOK) support threshold scale
        receiver peeled,
      witness.load ∈ selectedVisibleUnpeeledLoads support threshold scale
        receiver package.outside peeled) ∨
      ∀ load ∈ selectedVisibleUnpeeledLoads support threshold scale receiver
          package.outside peeled,
        Route8.TraceBasin.Route8Entry object support threshold LengthOK
          receiver load := by
  classical
  by_cases witnessed : ∃ witness : Witness (HasCycleWithLength LengthOK)
      support threshold scale receiver peeled,
    witness.load ∈ selectedVisibleUnpeeledLoads support threshold scale
      receiver package.outside peeled
  · exact Or.inl witnessed
  · refine Or.inr fun load member => ?_
    have routed : load ∈ object.routedLoads support threshold receiver := by
      have unpeeled := package.selected_mem_unpeeledLoads member
      rw [mem_unpeeledLoads] at unpeeled
      exact unpeeled.1
    rcases Route8.TraceBasin.exists_witness_or_route8Entry connected routed
        (noQuotient load member) exclusion avoids minimality
        (noSeparator load member) with ⟨witness, witnessLoad⟩ | entry
    · refine absurd ?_ witnessed
      exact ⟨⟨load, package.selected_mem_unpeeledLoads member,
        witnessLoad ▸ witness.member⟩, member⟩
    · exact entry

end VisibleFourUnpeeledPackage

end Hypostructure.Graph.ExitFour
