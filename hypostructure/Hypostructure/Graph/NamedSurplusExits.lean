import Hypostructure.Graph.CurvatureTargetRank
import Hypostructure.Graph.SimultaneousTightVertexSuppression
import Hypostructure.Graph.Strategy.InterfaceReplacement
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.ExcessPortFamily

/-!
# The sparse surplus exits, and why a selected minimal counterexample survives

`def:named-surplus-exits`, and the fact node `[125]` carries.

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

The point of this module is `survives`: a *selected minimal counterexample*
survives, and the proof spends only what the selection entry already carries --
its avoidance and its minimality -- together with `lem:replacement` at that
selection.  Nothing is assumed: each of the five clauses is refuted where the
manuscript refutes it.

* (a) is the selection's own avoidance.
* (b) is `DeclaredQuotient.targetComplete_of_identified`: an identified pair of
  boundaried pieces of an admissible quotient shares a boundary-degree profile
  and is context-equivalent, so neither separation can occur.
* (c) is `cor:uncompressible`, which node `[11]`--`[14]` already committed: the
  caller passes that fact rather than re-deriving it.
* (d) is minimality: a strictly smaller representative meeting the baseline has
  an accepted cycle, and the delocalization coordinate transfers it back.
* (e) is `lem:suppressed-family-critical-cycle`: the expansion of an accepted
  cycle of `G/𝒬` is a simple cycle of `G` of length `2^j + |𝒮|`, so accepting
  that length would be an accepted cycle of `G`.
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

/-- **A sparse surplus exit** of `def:named-surplus-exits`. -/
inductive SparseSurplusExit (Baseline Target : FiniteObject.{u} → Prop)
    (LengthOK : Nat → Prop) (object : FiniteObject.{u}) : Prop
  /-- (a) a direct dyadic contradiction: an accepted cycle. -/
  | dyadic (cycle : Graph.HasCycleWithLength LengthOK object)
  /-- (b) a target-defective quotient, as `lem:context-universality` defines
  one: an admissible quotient identifying two boundaried pieces that are
  nonetheless separated, by their boundary-degree profiles or by an outside
  context. -/
  | targetDefect {region : Finset object.Vertex}
      (quotient : CurvatureQuotient Baseline Target object region)
      (left right : BoundaryPiece (SupportAtom.boundary object quotient.support))
      (identified : ∀ test ∈ object.internalWedgeFamily region,
        quotient.value left (quotient.label test) =
          quotient.value right (quotient.label test))
      (separated : left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile ∨
        Response.TargetDefect Target left right)
  /-- (c) a nontrivial target-complete compression of a proper atom.
  *Target-complete* is the two-way clause: the replacement realizes the target
  against an outside context exactly when the original piece does.  That is
  `CompressibleSupport`, which `cor:uncompressible` forbids -- not the one-way
  `ReplacementSupport`, which is the weaker `lem:replacement` obstruction. -/
  | compression (support : Finset object.Vertex)
      (compressible : CompressibleSupport Baseline
        Target object support)
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

/-- **A selected minimal counterexample survives the sparse surplus exits.**

This is node `[125]`'s standing hypothesis, derived rather than assumed.  Only
the selection entry's own two halves are spent -- avoidance and minimality --
together with `lem:replacement` at that selection. -/
theorem survives_of_selection
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}}
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
    (minimal : ∀ smaller : FiniteObject.{u},
      smaller.LexicographicallySmaller object → Baseline smaller →
      Graph.HasCycleWithLength LengthOK smaller)
    (uncompressible : ∀ support : Finset object.Vertex,
      ¬ CompressibleSupport Baseline
        (Graph.HasCycleWithLength LengthOK) object support) :
    SurvivesSparseExits Baseline (Graph.HasCycleWithLength LengthOK) LengthOK
      object := by
  intro exit
  cases exit with
  | dyadic cycle => exact avoids cycle
  | targetDefect quotient left right identified separated =>
      obtain ⟨fibrewise, universal⟩ :=
        Graph.DeclaredQuotient.targetComplete_of_identified quotient left right
          identified
      rcases separated with different | ⟨outside, distinguishes⟩
      · exact different fibrewise
      · exact distinguishes (universal outside)
  | compression support compressible => exact uncompressible support compressible
  | delocalization representative smaller baseline transfer =>
      exact avoids (transfer (minimal representative smaller baseline))
  | suppressionChord family certificate violates =>
      -- `lem:suppressed-family-critical-cycle`: expanding the accepted cycle of
      -- `G/𝒬` gives a simple cycle of `G` of length `2^j + |𝒮|`.
      obtain ⟨_nonempty, expanded, length⟩ :=
        family.suppressedFamilyExpansion avoids certificate
      exact avoids ⟨{ vertex := family.sourceVertex certificate.vertex
                      walk := expanded.walk
                      isCycle := expanded.isCycle
                      length_ok := by rw [length]; exact violates }⟩

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
  { survives := survives, count := count, activated := activated }

end Hypostructure.Graph
