import Hypostructure.Graph.CurvatureTargetRank
import Hypostructure.Graph.DeclaredRankQuotient
import Hypostructure.Graph.SimultaneousTightVertexSuppression
import Hypostructure.Graph.Strategy.InterfaceReplacement
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.ExcessPortFamily

/-!
# The named sparse-surplus exits

`def:named-surplus-exits`, and the alternative node `[125]` tests.

> A *sparse surplus exit* is one of the following conclusions, each of which is
> defined without invoking the near-cubic Type A/Type B branch machinery:
> (a) a direct dyadic contradiction, equivalently a power-of-two cycle or a
> Mersenne return; (b) a target-defective quotient, as defined by
> `lem:context-universality`; (c) a nontrivial target-complete compression of a
> proper atom, forbidden by `lem:replacement`, `cor:uncompressible`; (d) a
> proper or global delocalization coordinate governed by `lem:proper-smearing`,
> `lem:no-silent-global-smearing`; (e) an open-port suppression cycle whose
> chord set violates the arithmetic conclusion of
> `lem:suppressed-family-critical-cycle`.
>
> A graph *survives the sparse surplus exits* when none of these conclusions
> occurs.

This module declares the five alternatives and their joint negation.  Node
`[125]` performs the manuscript's branch test through `ExactLedger`: an exit is
published on one arm, and `SurvivesSparseExits` is published on the other.  In
particular, this declaration does not claim that selection or replacement
alone rules out target defects, delocalizations, or suppression chords.

Clause (b) retains the actual rank-reducing `AttemptedQuotient` on the declared
family, together with the two realizations it identifies and their separating
context.  It is not a `DeclaredQuotient`: a declared admissible quotient is
already target-complete and would assume away the exit being tested.
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

/-- **A sparse surplus exit** of `def:named-surplus-exits`. -/
inductive SparseSurplusExit (Baseline Target : FiniteObject.{u} → Prop)
    (LengthOK : Nat → Prop) (object : FiniteObject.{u}) : Prop
  /-- (a) a direct dyadic contradiction: an accepted cycle. -/
  | dyadic (cycle : Graph.HasCycleWithLength LengthOK object)
  /-- (b) a target-defective quotient, exactly as
  `lem:context-universality` defines it: the proposed reduced and full
  realizations are identified by the incoming rank-reducing attempt, and a
  compatible outside context distinguishes their target responses.  This is
  the residual's attempted local identification, not arbitrary boundary data
  or an already target-complete `DeclaredQuotient`. -/
  | targetDefect {Coordinate : Type u} (family : Finset Coordinate)
      (coordinateSupport : Coordinate → Finset object.Vertex)
      (attempt : AttemptedQuotient Baseline Target object family
        coordinateSupport)
      (reducing : ¬ Set.InjOn attempt.label ↑family)
      (reduced full : BoundaryPiece
        (SupportAtom.boundary object attempt.support))
      (identified : attempt.Identifies reduced full)
      (defect : Response.TargetDefect Target reduced full)
  /-- (c) a nontrivial target-complete compression of a proper atom, recorded
  at the one-way `ReplacementSupport` strength used by `lem:replacement`. -/
  | compression (support : Finset object.Vertex)
      (replacement : ReplacementSupport Baseline Target object support)
  /-- (d) a proper or global delocalization coordinate: a strictly smaller
  representative meeting the baseline whose target transfers back. -/
  | delocalization (representative : FiniteObject.{u})
      (smaller : representative.LexicographicallySmaller object)
      (baseline : Baseline representative)
      (transfer : Target representative → Target object)
  /-- (e) an open-port suppression cycle whose chord set violates the arithmetic
  conclusion of `lem:suppressed-family-critical-cycle`: the lifted length
  `2^j + |𝒮|` is accepted, where that lemma concludes it is not. -/
  | suppressionChord (family : TightVertexSuppression.CompatibleFamily object)
      (certificate : Graph.CycleCertificate family.suppressed LengthOK)
      (violates : LengthOK (certificate.walk.length +
        (family.usedChords certificate.walk).card))

/-- **A graph survives the sparse surplus exits** when none of the five
conclusions occurs. -/
def SurvivesSparseExits (Baseline Target : FiniteObject.{u} → Prop)
    (LengthOK : Nat → Prop) (object : FiniteObject.{u}) : Prop :=
  ¬ SparseSurplusExit Baseline Target LengthOK object

/-- **`def:active-surplus-demands`.**

> An *active surplus demand* is a selected surplus port `p = (h,x) ∈ 𝒫_exc`
> equipped with the canonical data `T(p)`, `R_p`, and `Γ(p)` from
> `lem:sparse-port-activation`, and not already removed by a sparse surplus exit
> of `def:named-surplus-exits`.

Exit-freeness is a property of the graph, not of one port: the manuscript's
"survives" clause quantifies over every selected demand, every selected pair,
and every baseline spine coordinate at once.  So the family is active exactly
when the object survives and every selected port carries its canonical data.
`T(p)` is `SurplusPort.support`, which every port has; `R_p` is clause (b),
whose existence is the field below. -/
structure ActiveSurplusDemands (Baseline Target : FiniteObject.{u} → Prop)
    (LengthOK : Nat → Prop) (object : FiniteObject.{u}) (threshold : Nat) :
    Prop where
  /-- No sparse surplus exit removes any selected demand. -/
  survives : SurvivesSparseExits Baseline Target LengthOK object
  /-- `|𝒜₀| = σ(G)`. -/
  count : (object.excessPorts threshold).card = object.degreeSurplus threshold
  /-- The canonical shoulder pair of every selected port.  At the manuscript's
  cubic baseline this is the literal statement
  `N(x(p)) \ {c(p)} = {a_p,b_p}` with `a_p ≠ b_p`; retaining it here is what
  lets a suppressed-family blocker name its actual added shoulder chord. -/
  shoulderPair : ∀ pair : object.Vertex × object.Vertex,
    ∀ member : pair ∈ object.excessPorts threshold,
      ∃ left right : object.Vertex,
        (∀ vertex : object.Vertex,
          vertex ∈ (object.surplusPortOfMem member).shoulders ↔
            (vertex = left ∨ vertex = right)) ∧
          left ≠ right
  /-- Every selected port carries **all** the canonical data of
  `lem:sparse-port-activation`: the return path `R_p` of clause (b), the
  suppression path `Q_p` of clause (c) at an open port, and the triangle of
  clause (d) at a triangular one.  `T(p)` is `SurplusPort.support`, which every
  port has definitionally, and `Γ(p)` is
  `SurplusPort.responseSupport` at exactly these two witnesses -- so recording
  them is recording that `Γ(p)` exists at every selected port, which is what
  `def:active-surplus-demands` asks for. -/
  activated : ∀ pair : object.Vertex × object.Vertex,
    ∀ member : pair ∈ object.excessPorts threshold,
      ∀ left right : object.Vertex,
        (∀ vertex : object.Vertex,
          vertex ∈ (object.surplusPortOfMem member).shoulders ↔
            (vertex = left ∨ vertex = right)) →
        left ≠ right →
        Nonempty (FiniteObject.SurplusPort.PortReturn object pair.1 pair.2
            left right) ∧
          (¬ object.graph.Adj left right →
            Nonempty (FiniteObject.SurplusPort.OpenPortWitness object LengthOK
              pair.2 left right)) ∧
          (object.graph.Adj left right →
            object.graph.Adj pair.2 left ∧ object.graph.Adj left right ∧
              object.graph.Adj right pair.2)

/-- **`lem:surviving-active-family`.**

> If `G` survives the sparse surplus exits, then `𝒜₀ := 𝒫_exc` is a finite
> family of active surplus demands and `|𝒜₀| = σ(G)`.

The proof is the manuscript's: every selected port has the canonical data by
`lem:sparse-excess-port-extraction` and `lem:sparse-port-activation`, and since
the object survives, no selected demand is removed by an exit.  Each of the
three inputs is a fact the branch already carries, in full -- node `[128]`'s
entry is read whole rather than projected, because all three of its clauses are
canonical data of an active demand. -/
theorem surviving_active_family
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (survives : SurvivesSparseExits Baseline Target LengthOK object)
    (count : (object.excessPorts threshold).card =
      object.degreeSurplus threshold)
    (shoulderPair : ∀ pair : object.Vertex × object.Vertex,
      ∀ member : pair ∈ object.excessPorts threshold,
        ∃ left right : object.Vertex,
          (∀ vertex : object.Vertex,
            vertex ∈ (object.surplusPortOfMem member).shoulders ↔
              (vertex = left ∨ vertex = right)) ∧
            left ≠ right)
    (activated : ∀ pair : object.Vertex × object.Vertex,
      ∀ member : pair ∈ object.excessPorts threshold,
        ∀ left right : object.Vertex,
          (∀ vertex : object.Vertex,
            vertex ∈ (object.surplusPortOfMem member).shoulders ↔
              (vertex = left ∨ vertex = right)) →
          left ≠ right →
          Nonempty (FiniteObject.SurplusPort.PortReturn object pair.1 pair.2
              left right) ∧
            (¬ object.graph.Adj left right →
              Nonempty (FiniteObject.SurplusPort.OpenPortWitness object LengthOK
                pair.2 left right)) ∧
            (object.graph.Adj left right →
              object.graph.Adj pair.2 left ∧ object.graph.Adj left right ∧
                object.graph.Adj right pair.2)) :
    ActiveSurplusDemands Baseline Target LengthOK object threshold :=
  { survives := survives
    count := count
    shoulderPair := shoulderPair
    activated := activated }

end Hypostructure.Graph
