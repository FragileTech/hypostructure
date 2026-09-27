import Hypostructure.Graph.CurvatureTargetRank
import Hypostructure.Graph.DeclaredRankQuotient
import Hypostructure.Graph.SimultaneousTightVertexSuppression
import Hypostructure.Graph.InterfaceReplacement
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.ExcessPortFamily
import Hypostructure.Graph.CanonicalSupportSelection

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

Clause (b) is stated at the residual's declared coordinate family: two distinct
coordinates, read on G's own piece at the canonical connected support of their
union (`ResidualTargetDefect`), agree in G's actual outside context and are
separated by another boundaried context.  An identification of arbitrary
boundaried pieces, or a quotient with caller-chosen values, is not an exit of G:
such data made the former clause hold on every graph with a vertex.
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
boundary piece that is not a piece of G. -/

/-- Gluing G's actual outside context `G - Z` to any edge restriction of G's
own piece at `Z` is a subgraph of G. -/
theorem retainedGlue_hom (object : FiniteObject.{u})
    (support retained : Finset object.Vertex) :
    ∃ hom : (glue (SupportAtom.retainedPiece object support retained)
        (SupportAtom.outside object support)).graph →g object.graph,
      Function.Injective hom := by
  classical
  have le : glueGraph (SupportAtom.retainedPiece object support retained)
      (SupportAtom.outside object support) ≤
      glueGraph (SupportAtom.piece object support)
        (SupportAtom.outside object support) := by
    apply glueGraph_mono (piece := SupportAtom.piece object support)
      (SupportAtom.outside object support)
    intro left right adjacent
    exact adjacent.1
  let iso := (SupportAtom.decomposition object support).reconstructionIso
  refine ⟨iso.toHom.comp (SimpleGraph.Hom.ofLE le), ?_⟩
  intro left right equal
  exact iso.injective equal

/-- On a target-avoiding object no retained reading glued to its actual outside
context is target-positive. -/
theorem not_target_retainedGlue {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (support retained : Finset object.Vertex) :
    ¬ HasCycleWithLength LengthOK
      (glue (SupportAtom.retainedPiece object support retained)
        (SupportAtom.outside object support)) := by
  intro cycle
  obtain ⟨hom, injective⟩ := retainedGlue_hom object support retained
  exact avoids (hasCycleWithLength_of_hom hom injective cycle)

/-- **A retained reading of G's piece is an explicit replacement candidate**
(`lem:replacement` with `def:proper-quotient-representative`, the
representative `Z'` that exit (c) needs): replacing G's piece at a connected
proper support `Z` by its reading restricted to `retained` is a
`ReplacementSupport` of `Z` as soon as the reading keeps the piece's
boundary-degree profile, the glued graph keeps the baseline, and it is
lexicographically smaller.  The target transfer is automatic: the reading is a
subgraph of the piece, so a cycle after gluing any context survives in the
piece glued to that context. -/
theorem replacementSupport_of_retainedReading {Baseline : FiniteObject.{u} → Prop}
    {LengthOK : Nat → Prop} (object : FiniteObject.{u})
    (support retained : Finset object.Vertex)
    (connected : SupportComponents.Connected.ConnectedOn object support)
    (proper : ∃ vertex, vertex ∉ support)
    (profile : (SupportAtom.retainedPiece object support retained).boundaryDegreeProfile =
      (SupportAtom.piece object support).boundaryDegreeProfile)
    (baseline : Baseline (glue (SupportAtom.retainedPiece object support retained)
      (SupportAtom.outside object support)))
    (smaller : (glue (SupportAtom.retainedPiece object support retained)
      (SupportAtom.outside object support)).LexicographicallySmaller object) :
    ReplacementSupport Baseline (HasCycleWithLength LengthOK) object support := by
  refine ⟨connected, proper, SupportAtom.retainedPiece object support retained,
    profile, baseline, smaller, ?_⟩
  intro outside cycle
  have le : glueGraph (SupportAtom.retainedPiece object support retained) outside ≤
      glueGraph (SupportAtom.piece object support) outside := by
    apply glueGraph_mono (piece := SupportAtom.piece object support) outside
    intro left right adjacent
    exact adjacent.1
  exact hasCycleWithLength_of_hom
    (left := glue (SupportAtom.retainedPiece object support retained) outside)
    (right := glue (SupportAtom.piece object support) outside)
    (SimpleGraph.Hom.ofLE le) (fun _ _ equal => equal) cycle

/-- **The canonical response of a declared coordinate of G at a support `Z`**
(`def:declared-coordinate-signature`, `val_X(r)`): the coordinate read on G's
own piece at `Z` restricted to its declared support (`retainedPiece`), on the
unchanged boundary `∂Z`, tested against every `∂Z`-boundaried context.  It is
the only response a blocker or an exit may read: no caller-chosen label or
value enters. -/
def canonicalCoordinateResponse (Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) (support carried : Finset object.Vertex) :
    OutsideContext (SupportAtom.boundary object support) → Prop :=
  fun outside => Target (glue (SupportAtom.retainedPiece object support carried) outside)

/-- **Clause (b) at G's declared family** (`lem:context-universality`,
tex 6106-6112; `def:target-complete-compression`, tex 6138): two distinct
declared coordinates of the family, read on G's own piece at the canonical
connected support `Z` of their union, lie in one boundary-degree fibre, agree
in G's actual outside context `G - Z`, and are separated by some
`∂Z`-boundaried context. -/
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
      (canonicalCoordinateResponse Target object support (coordinateSupport first)
          (SupportAtom.outside object support) ↔
        canonicalCoordinateResponse Target object support (coordinateSupport second)
          (SupportAtom.outside object support)) ∧
      ∃ outside : OutsideContext (SupportAtom.boundary object support),
        ¬ (canonicalCoordinateResponse Target object support
              (coordinateSupport first) outside ↔
            canonicalCoordinateResponse Target object support
              (coordinateSupport second) outside)

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
    profile, actual, separated⟩ := defect
  refine ⟨embed first, maps first firstMem, embed second, maps second secondMem,
    fun equal => different (injective first firstMem second secondMem equal),
    support, ?_⟩
  rw [supports first firstMem, supports second secondMem]
  exact ⟨selected, profile, actual, separated⟩

/-- **A sparse surplus exit** of `def:named-surplus-exits` (tex 2754-2772), at
the residual's declared coordinate family. -/
inductive SparseSurplusExit (Baseline Target : FiniteObject.{u} → Prop)
    (LengthOK : Nat → Prop) (object : FiniteObject.{u}) {Coordinate : Type w}
    (family : Finset Coordinate)
    (coordinateSupport : Coordinate → Finset object.Vertex) : Prop
  /-- (a) a direct dyadic contradiction: an accepted cycle. -/
  | dyadic (cycle : Graph.HasCycleWithLength LengthOK object)
  /-- (b) a target-defective quotient, as `lem:context-universality` defines
  it, among the family's own coordinates read on G's own pieces. -/
  | targetDefect
      (defect : ResidualTargetDefect Target object family coordinateSupport)
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
  | suppressionChord (tvs : TightVertexSuppression.CompatibleFamily object)
      (certificate : Graph.CycleCertificate tvs.suppressed LengthOK)
      (violates : LengthOK (certificate.walk.length +
        (tvs.usedChords certificate.walk).card))

/-- **A graph survives the sparse surplus exits** of its declared family when
none of the five conclusions occurs. -/
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
