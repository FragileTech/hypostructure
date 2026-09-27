import Hypostructure.Graph.Statements.CanonicalSameToken

/-!
# Canonical objects of G: the first-separator handoff of a pair obstruction

`lem:pair-system-realizability` (iv) (tex 5110-5130, node `[179]`) and the
periodic arm of `lem:pair-system-increment-arithmetic` (tex 5207-5220, node
`[180]`) name one Type B alternative: "the first nonserial intersection is a
same-token routed bottleneck whose first separator is a high-degree vertex: the
decorated Type B fan data of `lem:same-token-bottleneck-routing`"; in the proof,
"a branching intersection at a high-degree first separator is the routed
bottleneck ... whose first-separator reading is decorated Type B fan data".

The objects are those of the *retained obstruction*, not of any other part of
G: two routes inside the obstruction's own overlap support
`⋃_{π ∈ 𝒰} X_π` from a common vertex to the two demands `d_p`, `d_q` of the
failed pair (`PairDemandReturns`), of maximal common prefix; their first
separator `h` with its two first-entry arms into the core `{d_p, d_q}`; and the
decorated envelope `envelopeOfFirstSeparator` at the node-`[19]` packing `P₀`,
under the same handoff conditions as node `[144]`
(`SameTokenHandoffConditions`).  Each is the `canonicalChoice` of its spec at
the objects fixed before it.

Every object is `Option`-valued; a statement pins it with
`∃ x, obj = some x ∧ Q x`.  This module imports no strategy, row or vocabulary
module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

noncomputable section

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-- The two demand endpoints `{d_p, d_q}` of the obstruction's failed pair: the
core of its handoff envelope. -/
def pairObstructionCore (returns : PairDemandReturns data object) :
    Finset object.Vertex := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact {returns.leftDemand.2, returns.rightDemand.2}

/-- Two routes of the obstruction, as the vertex lists they visit. -/
structure PairObstructionRoutes where
  first : List object.Vertex
  second : List object.Vertex

/-- A route of the obstruction to a demand endpoint: a simple walk of G inside
the obstruction's own overlap support ending at that endpoint. -/
def PairObstructionRoute (returns : PairDemandReturns data object)
    (path : List object.Vertex) (endpoint : object.Vertex) : Prop :=
  path.IsChain object.graph.Adj ∧ path.Nodup ∧
    path.getLast? = some endpoint ∧
    ∀ vertex ∈ path, vertex ∈
      returns.overlap.system.overlapSupport returns.overlap.family

/-- **Spec of the obstruction's routes**: two routes from one common vertex to
`d_p` and `d_q` inside the overlap support, of maximal common prefix among all
such pairs of routes. -/
def PairObstructionRoutesSpec (returns : PairDemandReturns data object)
    (routes : PairObstructionRoutes object) : Prop := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact routes.first ≠ [] ∧ routes.first.head? = routes.second.head? ∧
    PairObstructionRoute data object returns routes.first returns.leftDemand.2 ∧
    PairObstructionRoute data object returns routes.second returns.rightDemand.2 ∧
    ∀ first second : List object.Vertex,
      first ≠ [] → first.head? = second.head? →
      PairObstructionRoute data object returns first returns.leftDemand.2 →
      PairObstructionRoute data object returns second returns.rightDemand.2 →
        Graph.SameTokenRoutingGerms.commonPrefixLength first second ≤
          Graph.SameTokenRoutingGerms.commonPrefixLength routes.first routes.second

/-- **The canonical routes of the obstruction.** -/
def canonicalPairObstructionRoutes (returns : PairDemandReturns data object) :
    Option (PairObstructionRoutes object) :=
  canonicalChoice (PairObstructionRoutesSpec data object returns)

/-- **Spec of the first separator** of the obstruction's routes (the reading of
`lem:same-token-bottleneck-routing`, tex 5596-5612, at the obstruction): the
routes split after their common prefix at `h` into `a ≠ b`, and each arm is the
first-entry prefix of its tail into the core `{d_p, d_q}`, with the local
structure `envelopeOfFirstSeparator` consumes. -/
def PairObstructionSeparatorSpec (returns : PairDemandReturns data object)
    (routes : PairObstructionRoutes object)
    (split : SameTokenFirstSeparator object) : Prop :=
  let core := pairObstructionCore data object returns
  routes.first =
      split.common ++ split.separator :: split.nextFirst :: split.tailFirst ∧
    routes.second =
      split.common ++ split.separator :: split.nextSecond :: split.tailSecond ∧
    split.nextFirst ≠ split.nextSecond ∧
    SameTokenFirstEntry object split.armFirst (split.nextFirst :: split.tailFirst) core ∧
    SameTokenFirstEntry object split.armSecond (split.nextSecond :: split.tailSecond)
      core ∧
    object.graph.Adj split.separator split.nextFirst ∧
    object.graph.Adj split.separator split.nextSecond ∧
    split.armFirst.head? = some split.nextFirst ∧
    split.armSecond.head? = some split.nextSecond ∧
    split.armFirst.IsChain object.graph.Adj ∧
    split.armSecond.IsChain object.graph.Adj ∧
    split.armFirst.Nodup ∧ split.armSecond.Nodup ∧
    (∃ terminal, split.armFirst.getLast? = some terminal ∧ terminal ∈ core) ∧
    (∃ terminal, split.armSecond.getLast? = some terminal ∧ terminal ∈ core) ∧
    (∀ vertex ∈ split.armFirst, vertex ∈ core ∨ vertex = split.separator →
      split.armFirst.getLast? = some vertex) ∧
    (∀ vertex ∈ split.armSecond, vertex ∈ core ∨ vertex = split.separator →
      split.armSecond.getLast? = some vertex)

/-- **The canonical first separator** of the obstruction's canonical routes,
together with those routes. -/
def canonicalPairObstructionSeparator (returns : PairDemandReturns data object) :
    Option (PairObstructionRoutes object × SameTokenFirstSeparator object) :=
  (canonicalPairObstructionRoutes data object returns).bind fun routes =>
    (canonicalChoice (PairObstructionSeparatorSpec data object returns routes)).map
      fun split => (routes, split)

/-- The envelope of a first separator of the obstruction satisfying its spec
and the handoff conditions at `P₀`: exactly `envelopeOfFirstSeparator` on the
core `{d_p, d_q}`. -/
def pairObstructionEnvelopeOf (returns : PairDemandReturns data object)
    (routes : PairObstructionRoutes object)
    (split : SameTokenFirstSeparator object)
    (spec : PairObstructionSeparatorSpec data object returns routes split)
    (conditions : SameTokenHandoffConditions data object split) :
    SameTokenEnvelope data object :=
  Graph.DecoratedHandoff.envelopeOfFirstSeparator
    (pairObstructionCore data object returns) split.separator split.nextFirst
    split.nextSecond spec.2.2.1 spec.2.2.2.2.2.1 spec.2.2.2.2.2.2.1
    split.armFirst split.armSecond spec.2.2.2.2.2.2.2.1 spec.2.2.2.2.2.2.2.2.1
    spec.2.2.2.2.2.2.2.2.2.1 spec.2.2.2.2.2.2.2.2.2.2.1
    spec.2.2.2.2.2.2.2.2.2.2.2.1 spec.2.2.2.2.2.2.2.2.2.2.2.2.1
    spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1 spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    conditions.1 conditions.2.1 conditions.2.2.1 conditions.2.2.2

/-- **The canonical handoff envelope of the obstruction**: the envelope of its
canonical first separator when that separator satisfies the handoff conditions
at `P₀`, and `none` otherwise. -/
def canonicalPairObstructionEnvelope (returns : PairDemandReturns data object) :
    Option (SameTokenEnvelope data object) := by
  classical
  exact match canonicalPairObstructionSeparator data object returns with
    | none => none
    | some (routes, split) =>
        if both : PairObstructionSeparatorSpec data object returns routes split ∧
            SameTokenHandoffConditions data object split then
          some (pairObstructionEnvelopeOf data object returns routes split both.1
            both.2)
        else none

/-- **The first-separator handoff of the obstruction at a support `(Y, H)`**:
the canonical envelope of the obstruction's canonical first separator exists,
escapes physically (`SameTokenEscape`), and has core `Y` and decorations
`H`. -/
def PairObstructionHandoffAt (returns : PairDemandReturns data object)
    (core centres : Finset object.Vertex) : Prop :=
  ∃ routes split envelope,
    canonicalPairObstructionSeparator data object returns = some (routes, split) ∧
    canonicalPairObstructionEnvelope data object returns = some envelope ∧
    SameTokenEscape data object split envelope ∧
    envelope.core = core ∧ envelope.decorations = centres

/-- **Alternative (iv) of `lem:pair-system-realizability` at the obstruction**:
the obstruction's own first separator is a high-degree handoff centre whose
decorated envelope escapes. -/
def PairObstructionHandoff (returns : PairDemandReturns data object) : Prop :=
  ∃ core centres, PairObstructionHandoffAt data object returns core centres

/-- **The canonical Type B support `(Y, H)` of the obstruction's handoff.** -/
def canonicalPairObstructionSupport (returns : PairDemandReturns data object) :
    Option (Finset object.Vertex × Finset object.Vertex) :=
  canonicalChoice fun support =>
    PairObstructionHandoffAt data object returns support.1 support.2

end

end Hypostructure.Graph.Strategy.Spine
