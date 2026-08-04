import Hypostructure.Graph.InducedPath
import Hypostructure.Graph.Target

/-!
# Hegde--Sandeep--Shashank external theorem

The external result is represented as an axiom: a finite induced-`P₁₃`-free
graph of minimum degree at least three contains a power-of-two cycle.
-/

namespace Hypostructure.Graph.External.HegdeSandeepShashank

open Hypostructure.Graph

universe u

/-- Induced-path order appearing in the registered external theorem. -/
def inducedPathOrder : Nat := 13

/-- Minimum-degree threshold appearing in the registered external theorem.
An application that wants to consume this theorem registers a baseline at
least this large; it does not repeat the numeral. -/
def minimumDegree : Nat := 3

/-- Every finite induced-`P₁₃`-free graph of minimum degree at least three
contains a cycle whose length is a power of two. -/
axiom p13Free_hasPowerOfTwoCycle
    (object : FiniteObject.{u})
    [Fintype object.Vertex] [DecidableRel object.graph.Adj]
    (minimumDegreeThree : 3 ≤ object.minDegree)
    (p13Free : InducedPathFree object inducedPathOrder) :
    HasCycleWithLength (fun length =>
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent)
      object

/-- Finite-object form of the external theorem, using exactly the object's
packed finite instances. -/
theorem finiteObject_p13Free_hasPowerOfTwoCycle
    (object : FiniteObject.{u})
    (minimumDegreeThree : 3 ≤ object.minDegree)
    (p13Free : InducedPathFree object inducedPathOrder) :
    HasCycleWithLength (fun length =>
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent)
      object := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  apply p13Free_hasPowerOfTwoCycle object
  · simpa only [FiniteObject.minDegree] using minimumDegreeThree
  · exact p13Free

/-- The external theorem read through a caller-selected executable cycle
length predicate and a caller-selected baseline threshold.  This is the only
form strategy code consumes: the exponent presentation of the axiom's
conclusion and its numeric threshold both stay inside the framework. -/
theorem hasCycleWithLength
    {LengthOK : Nat → Prop}
    (lengthBridge : ∀ length,
      (∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent) →
        LengthOK length)
    {threshold : Nat} (thresholdOK : minimumDegree ≤ threshold)
    (object : FiniteObject.{u})
    (baseline : threshold ≤ object.minDegree)
    (p13Free : InducedPathFree object inducedPathOrder) :
    HasCycleWithLength LengthOK object := by
  rcases finiteObject_p13Free_hasPowerOfTwoCycle object
      (Nat.le_trans thresholdOK baseline) p13Free with ⟨certificate⟩
  exact ⟨{
    vertex := certificate.vertex
    walk := certificate.walk
    isCycle := certificate.isCycle
    length_ok := lengthBridge certificate.walk.length certificate.length_ok }⟩

end Hypostructure.Graph.External.HegdeSandeepShashank
