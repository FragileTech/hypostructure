import Hypostructure.Graph.CurvatureTargetRank
import Hypostructure.Graph.DeclaredRankQuotient
import Hypostructure.Graph.SimultaneousTightVertexSuppression
import Hypostructure.Graph.InterfaceReplacement
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.ExcessPortFamily
import Hypostructure.Graph.CanonicalSupportSelection
import Hypostructure.Graph.ActualContext

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

The named exits are the conclusions of this list that are objects of G: (a)
an accepted cycle of G, and (e) a cycle certificate of G's suppressed graph
whose lifted length is accepted, which expands to an accepted cycle of G.
Clauses (b)--(d) conclude about objects built from G (readings of G's pieces
glued into `G − Z`, a replacement piece glued in, another finite object); on the
selected G each is refuted by G's own facts where it arises: (b) by the
selection's avoidance (`not_residualTargetDefect_of_avoids`: two readings of G
agree in G's own surroundings `G − Z`), (c) and (d) by the selection's
minimality (`Strategy.InterfaceReplacement.not_replacementSupport_of_minimal`).
`SparseSurplusExit` has the two constructors (a) and (e), and
`SurvivesSparseExits` is their joint negation.
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u w w'

/-! ## Clause (b): a target-defective identification of G's own coordinates

`lem:context-universality` (tex 6106-6112) speaks about two coordinates
`r₁, r₂ ∈ ℛ(X)` of a piece `X` **of G**: an identification valid for the actual
outside context `G - X` but not for every `T`-boundaried context is
target-defective.  Clause (b) is therefore stated about a declared coordinate
family of the residual: each coordinate is read as G's own piece at the
canonical connected support `Z` of the two coordinates' union, restricted to the
coordinate's declared support (`SupportAtom.retainedPiece`), on the unchanged
boundary `∂Z`.  Nothing is caller-chosen: no attempted label or value map, no
boundary piece that is not a piece of G.  Stated about G, "every `T`-boundaried
context" is every context of G at `∂Z`, and G has exactly one: its own
surroundings `G − Z`.  So the G-form of the defect is that `G − Z` separates the
two readings (`ResidualTargetDefect`), which never happens at a target-avoiding
G (`not_residualTargetDefect_of_avoids`). -/

/-- Gluing G's actual outside context `G - Z` to any edge restriction of G's
own piece at `Z` is a subgraph of G (`ActualContext.actualGlue_hom`). -/
theorem retainedGlue_hom (object : FiniteObject.{u})
    (support retained : Finset object.Vertex) :
    ∃ hom : (glue (SupportAtom.retainedPiece object support retained)
        (SupportAtom.outside object support)).graph →g object.graph,
      Function.Injective hom :=
  ActualContext.actualGlue_hom object support retained

/-- On a target-avoiding object no retained reading glued to its actual outside
context is target-positive (`ActualContext.not_target_actualGlue`). -/
theorem not_target_retainedGlue {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (support retained : Finset object.Vertex) :
    ¬ HasCycleWithLength LengthOK
      (glue (SupportAtom.retainedPiece object support retained)
        (SupportAtom.outside object support)) :=
  ActualContext.not_target_actualGlue avoids support retained

/-- **A retained reading of G's piece is an explicit replacement candidate**
(`lem:replacement` with `def:proper-quotient-representative`, the
representative `Z'` that clause (c) names), stated about G: replacing G's piece at
a connected proper support `Z` by its reading restricted to `retained` is a
`ReplacementSupport` of `Z` as soon as the reading keeps the piece's
boundary-degree profile, the glued graph `glue X' (G − Z)` keeps the baseline,
and it is lexicographically smaller.  Its target clause -- no target cycle in
`glue X' (G − Z)` -- is automatic on a target-avoiding G: the glued graph is a
subgraph of G (`ActualContext.not_target_actualGlue`). -/
theorem replacementSupport_of_retainedReading {Baseline : FiniteObject.{u} → Prop}
    {LengthOK : Nat → Prop} (object : FiniteObject.{u})
    (support retained : Finset object.Vertex)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (connected : SupportComponents.Connected.ConnectedOn object support)
    (proper : ∃ vertex, vertex ∉ support)
    (profile : (SupportAtom.retainedPiece object support retained).boundaryDegreeProfile =
      (SupportAtom.piece object support).boundaryDegreeProfile)
    (baseline : Baseline (glue (SupportAtom.retainedPiece object support retained)
      (SupportAtom.outside object support)))
    (smaller : (glue (SupportAtom.retainedPiece object support retained)
      (SupportAtom.outside object support)).LexicographicallySmaller object) :
    ReplacementSupport Baseline (HasCycleWithLength LengthOK) object support :=
  ⟨connected, proper, SupportAtom.retainedPiece object support retained,
    profile, baseline, smaller, ActualContext.not_target_actualGlue avoids support retained⟩

/-- **Clause (b) at G's declared family, stated about G**
(`lem:context-universality`, tex 6106-6112; `def:target-complete-compression`,
tex 6138): two distinct declared coordinates of the family, read on G's own
piece at the canonical connected support `Z` of their union, lie in one
boundary-degree fibre and are separated by a context of G.  The paper's
defect is an identification valid in G's actual outside context but not in
every context; the only context of G at `∂Z` is G's own surroundings `G − Z`
(`ActualContext.actualGlue`), so stated about G the defect is that `G − Z`
separates the two readings. -/
def ResidualTargetDefect (Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) {Coordinate : Type w}
    (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex) : Prop := by
  classical
  exact ∃ first ∈ family, ∃ second ∈ family, first ≠ second ∧
    ∃ support : Finset object.Vertex,
      CanonicalSupport.select? object
          (coordinateSupport first ∪ coordinateSupport second) = some support ∧
      (SupportAtom.retainedPiece object support
          (coordinateSupport first)).boundaryDegreeProfile =
        (SupportAtom.retainedPiece object support
          (coordinateSupport second)).boundaryDegreeProfile ∧
      ¬ (Target (ActualContext.actualGlue object support (coordinateSupport first)) ↔
          Target (ActualContext.actualGlue object support (coordinateSupport second)))

/-- **Clause (b) is empty at a target-avoiding G** (Lean improvement: the test
of clause (b), stated about G, is decided at G): two readings of G always agree
in G's own surroundings `G − Z` (`ActualContext.actualGlue_agree`). -/
theorem not_residualTargetDefect_of_avoids {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} (avoids : ¬ HasCycleWithLength LengthOK object)
    {Coordinate : Type w} (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex) :
    ¬ ResidualTargetDefect (HasCycleWithLength LengthOK) object family
      coordinateSupport := by
  rintro ⟨first, -, second, -, -, support, -, -, separated⟩
  exact separated (ActualContext.actualGlue_agree avoids support _ _)

/-- The boundary-profile companion of clause (b) (`lem:degree-profile-fibres`,
tex 6088): two distinct declared coordinates of the family whose readings on
G's piece at their canonical support lie in different boundary-degree fibres.
This is the concrete object of blocker (d) in `def:surplus-blockers`. -/
def ResidualProfileSeparation (object : FiniteObject.{u}) {Coordinate : Type w}
    (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex) : Prop := by
  classical
  exact ∃ first ∈ family, ∃ second ∈ family, first ≠ second ∧
    ∃ support : Finset object.Vertex,
      CanonicalSupport.select? object
          (coordinateSupport first ∪ coordinateSupport second) = some support ∧
      (SupportAtom.retainedPiece object support
          (coordinateSupport first)).boundaryDegreeProfile ≠
        (SupportAtom.retainedPiece object support
          (coordinateSupport second)).boundaryDegreeProfile

/-- A family with at most one coordinate identifies nothing, so it has no
clause-(b) defect. -/
theorem not_residualTargetDefect_of_card_le_one (Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) {Coordinate : Type w}
    (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex)
    (small : family.card ≤ 1) :
    ¬ ResidualTargetDefect Target object family coordinateSupport := by
  rintro ⟨first, firstMem, second, secondMem, different, -⟩
  exact different (Finset.card_le_one.mp small first firstMem second secondMem)

/-- A defect among the coordinates of a subfamily is a defect of every family
containing them with the same declared supports. -/
theorem ResidualTargetDefect.map {Target : FiniteObject.{u} → Prop}
    {object : FiniteObject.{u}} {Coordinate : Type w} {Coordinate' : Type w'}
    {family : Finset Coordinate} {family' : Finset Coordinate'}
    {coordinateSupport : Coordinate → Finset object.Vertex}
    {coordinateSupport' : Coordinate' → Finset object.Vertex}
    (embed : Coordinate → Coordinate')
    (injective : ∀ first ∈ family, ∀ second ∈ family,
      embed first = embed second → first = second)
    (maps : ∀ coordinate ∈ family, embed coordinate ∈ family')
    (supports : ∀ coordinate ∈ family,
      coordinateSupport' (embed coordinate) = coordinateSupport coordinate)
    (defect : ResidualTargetDefect Target object family coordinateSupport) :
    ResidualTargetDefect Target object family' coordinateSupport' := by
  obtain ⟨first, firstMem, second, secondMem, different, support, selected,
    profile, separated⟩ := defect
  refine ⟨embed first, maps first firstMem, embed second, maps second secondMem,
    fun equal => different (injective first firstMem second secondMem equal),
    support, ?_⟩
  rw [supports first firstMem, supports second secondMem]
  exact ⟨selected, profile, separated⟩

/-- **A sparse surplus exit** of `def:named-surplus-exits` (tex 2754-2772):
one of the two conclusions of the list that are objects of G.  The declared
family and the baseline and target predicates are the parameters of the
paper's list; the two constructors read G alone. -/
inductive SparseSurplusExit (Baseline Target : FiniteObject.{u} → Prop)
    (LengthOK : Nat → Prop) (object : FiniteObject.{u}) {Coordinate : Type w}
    (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex) : Prop
  /-- (a) a direct dyadic contradiction: an accepted cycle of G. -/
  | dyadic (cycle : Graph.HasCycleWithLength LengthOK object)
  /-- (e) an open-port suppression cycle whose chord set violates the arithmetic
  conclusion of `lem:suppressed-family-critical-cycle`: the lifted length
  `2^j + |𝒮|` is accepted, where that lemma concludes it is not. -/
  | suppressionChord (tvs : TightVertexSuppression.CompatibleFamily object)
      (certificate : Graph.CycleCertificate tvs.suppressed LengthOK)
      (violates : LengthOK (certificate.walk.length +
        (tvs.usedChords certificate.walk).card))

/-- **A graph survives the sparse surplus exits** of its declared family when
neither of the two cycle conclusions occurs. -/
def SurvivesSparseExits (Baseline Target : FiniteObject.{u} → Prop)
    (LengthOK : Nat → Prop) (object : FiniteObject.{u}) {Coordinate : Type w}
    (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex) : Prop :=
  ¬ SparseSurplusExit Baseline Target LengthOK object family coordinateSupport

/-- **`def:active-surplus-demands`.**

> An *active surplus demand* is a selected surplus port `p = (h,x) ∈ 𝒫_exc`
> equipped with the canonical data `T(p)`, `R_p`, and `Γ(p)` from
> `lem:sparse-port-activation`, and not already removed by a sparse surplus exit
> of `def:named-surplus-exits`.

This structure records the canonical port data.  Exit-freeness is a separate
ledger fact about the graph (node `[125]`, `K .sparseSurplusSurvivor`, stated at
G's declared sparse family): the manuscript's "survives" clause quantifies over
every selected demand, every selected pair and every baseline spine coordinate
at once, so it is read from the ledger where it is needed, not bundled here.
`T(p)` is `SurplusPort.support`, which every port has; `R_p` is clause (b),
whose existence is the field below. -/
structure ActiveSurplusDemands (Baseline Target : FiniteObject.{u} → Prop)
    (LengthOK : Nat → Prop) (object : FiniteObject.{u}) (threshold : Nat) :
    Prop where
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
`lem:sparse-excess-port-extraction` and `lem:sparse-port-activation`; the
survival clause is the separate node-`[125]` ledger fact.  Each of the
three inputs is a fact the branch already carries, in full -- node `[128]`'s
entry is read whole rather than projected, because all three of its clauses are
canonical data of an active demand. -/
theorem surviving_active_family
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
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
  { count := count
    shoulderPair := shoulderPair
    activated := activated }

end Hypostructure.Graph
