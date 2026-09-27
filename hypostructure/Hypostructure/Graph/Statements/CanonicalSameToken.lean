import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.Statements.CanonicalSurplusCapacity
import Hypostructure.Graph.Statements.CanonicalTypeA

/-!
# Canonical objects of G: the same-token routing of node `[144]`

`lem:same-token-bottleneck-routing` (tex 5565-5620) works on *the* homogeneous
bottleneck pattern of *the* overloading token of node `[137]`, in *the*
capacity-token ledger of G.  It fixes two pattern edges `p ≠ q` with endpoint
demands `d_p`, `d_q` of equal routing label (pigeonhole over `L_geom`), two
valid same-root routes to them of maximal common prefix, and their first
separator `h` with its two arms; the decorated envelope of that separator is the
Type B handoff.  Each of these is a witness that an upstream statement only
asserts with `∃`, so each is a canonical object of G here: the
`canonicalChoice` of exactly that statement at G and at the objects already
fixed before it.

* `canonicalSameTokenRouting data G` -- the canonical ledger, overload, pattern,
  equal-label demands and maximal routes, bundled as one `SameTokenRouting`;
* `canonicalSameTokenSeparator data G` -- the first-separator decomposition of
  those routes (`none` when they do not separate);
* `canonicalSameTokenEnvelope data G` -- `envelopeOfFirstSeparator` at that
  separator, at the node-`[19]` packing, when the separator is a high-degree,
  non-absorbing handoff centre on a target-avoiding G;
* `SameTokenHandoffAt data G core centres` / `canonicalSameTokenSupport data G`
  -- the handoff support `(Y, H)` read off that envelope (the object node `[65]`
  receives).

Every object is `Option`-valued; a downstream statement pins it with
`∃ x, obj = some x ∧ Q x`, which is false (never vacuously true) when the
object does not exist.  This module imports no strategy, row or vocabulary
module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

noncomputable section

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-- The declared same-root connector configurations of a pattern edge's
demand, at a capacity presentation and token (`def:same-token-routing-germs`). -/
abbrev SameTokenConfiguration (capacity : SurplusCapacity data object)
    (token : Graph.FiniteObject.CapacityToken object)
    (pair : Finset (object.Vertex × object.Vertex))
    (demand : object.Vertex × object.Vertex) : Type u :=
  Graph.SameTokenRoutingGerms.RoutingConfiguration object
    (capacity.sameTokenRoutingSupport token pair)
    (Graph.CapacityPresentation.tokenSupport token)
    (capacity.activation.localBuffer demand)

/-- A configuration is a valid same-root route: it starts at the token's
canonical root and ends at the demand's endpoint. -/
def SameTokenValidRoute {capacity : SurplusCapacity data object}
    {token : Graph.FiniteObject.CapacityToken object}
    {pair : Finset (object.Vertex × object.Vertex)}
    {demand : object.Vertex × object.Vertex}
    (route : SameTokenConfiguration data object capacity token pair demand) : Prop :=
  route.path.head? = some (Graph.CapacityPresentation.tokenRoot token) ∧
    route.path.getLast? = some demand.2

/-- Two pattern edges with one endpoint demand each. -/
structure SameTokenDemands where
  first : Finset (object.Vertex × object.Vertex)
  second : Finset (object.Vertex × object.Vertex)
  firstDemand : object.Vertex × object.Vertex
  secondDemand : object.Vertex × object.Vertex

/-- **Spec of the equal-label demands** at a certified ledger, token, role and
pattern (`lem:same-token-bottleneck-routing`, pigeonhole over `L_geom`,
tex 5570-5580): two distinct pattern edges `p ≠ q` and endpoint demands
`d_p ∈ p`, `d_q ∈ q` with equal actual routing labels. -/
def SameTokenDemandsSpec {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity)
    (token : certified.ledger.presented.Token)
    (role : Graph.SameTokenBlockerRoles.Role)
    (pattern : Finset (Finset (object.Vertex × object.Vertex)))
    (demands : SameTokenDemands object) : Prop :=
  demands.first ≠ demands.second ∧
    ∃ (active : Graph.ActiveSurplusDemands
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object data.threshold)
      (cubic : data.threshold = 3)
      (subset : pattern ⊆ certified.ledger.presented.roleFibre token role)
      (firstMem : demands.first ∈ pattern) (secondMem : demands.second ∈ pattern)
      (firstDemandMem : demands.firstDemand ∈ demands.first)
      (secondDemandMem : demands.secondDemand ∈ demands.second),
      sameTokenActualRoutingLabel data object active cubic capacity certified token role
          pattern subset demands.first firstMem demands.firstDemand firstDemandMem =
        sameTokenActualRoutingLabel data object active cubic capacity certified token role
          pattern subset demands.second secondMem demands.secondDemand secondDemandMem

/-- The two routes of the equal-label demands. -/
structure SameTokenRoutes (capacity : SurplusCapacity data object)
    (token : Graph.FiniteObject.CapacityToken object)
    (demands : SameTokenDemands object) where
  first : SameTokenConfiguration data object capacity token demands.first
    demands.firstDemand
  second : SameTokenConfiguration data object capacity token demands.second
    demands.secondDemand

/-- **Spec of the maximal routes** (`lem:same-token-bottleneck-routing`,
tex 5580-5584): both routes are valid same-root routes, and no pair of valid
routes to the same two demands has a longer common prefix. -/
def SameTokenRoutesSpec {capacity : SurplusCapacity data object}
    {token : Graph.FiniteObject.CapacityToken object}
    {demands : SameTokenDemands object}
    (routes : SameTokenRoutes data object capacity token demands) : Prop := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact SameTokenValidRoute data object routes.first ∧
    SameTokenValidRoute data object routes.second ∧
    ∀ (first : SameTokenConfiguration data object capacity token demands.first
        demands.firstDemand)
      (second : SameTokenConfiguration data object capacity token demands.second
        demands.secondDemand),
      SameTokenValidRoute data object first → SameTokenValidRoute data object second →
        Graph.SameTokenRoutingGerms.commonPrefixLength first.path second.path ≤
          Graph.SameTokenRoutingGerms.commonPrefixLength routes.first.path
            routes.second.path

/-- The node-`[144]` routing stage of G: the canonical capacity-token ledger,
its overloading token and role, the homogeneous pattern, the equal-label
demands and their maximal routes. -/
structure SameTokenRouting where
  capacity : SurplusCapacity data object
  certified : SurplusCertified data object capacity
  token : certified.ledger.presented.Token
  role : Graph.SameTokenBlockerRoles.Role
  pattern : Finset (Finset (object.Vertex × object.Vertex))
  demands : SameTokenDemands object
  routes : SameTokenRoutes data object capacity token demands

/-- The canonical equal-label demands at a fixed overload and pattern. -/
def canonicalSameTokenDemandsAt {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity)
    (token : certified.ledger.presented.Token)
    (role : Graph.SameTokenBlockerRoles.Role)
    (pattern : Finset (Finset (object.Vertex × object.Vertex))) :
    Option (SameTokenDemands object) :=
  canonicalChoice (SameTokenDemandsSpec data object certified token role pattern)

/-- The canonical maximal routes at fixed demands. -/
def canonicalSameTokenRoutesAt (capacity : SurplusCapacity data object)
    (token : Graph.FiniteObject.CapacityToken object)
    (demands : SameTokenDemands object) :
    Option (SameTokenRoutes data object capacity token demands) :=
  canonicalChoice (SameTokenRoutesSpec data object (capacity := capacity)
    (token := token) (demands := demands))

/-- **The canonical node-`[144]` routing stage of G**: the canonical ledger
and overload of node `[137]`, the canonical pattern of the audits
`[140]`/`[142]`/`[143]`, and at them the canonical equal-label demands and
maximal routes. -/
def canonicalSameTokenRouting : Option (SameTokenRouting data object) :=
  (canonicalOverload data object).bind fun overload =>
    (canonicalHomogeneousPatternAt data object overload.1.2 overload.2.1
        overload.2.2).bind fun pattern =>
      (canonicalSameTokenDemandsAt data object overload.1.2 overload.2.1
          overload.2.2 pattern).bind fun demands =>
        (canonicalSameTokenRoutesAt data object overload.1.1 overload.2.1
            demands).map fun routes =>
          { capacity := overload.1.1
            certified := overload.1.2
            token := overload.2.1
            role := overload.2.2
            pattern := pattern
            demands := demands
            routes := routes }

/-- The canonical overload of G is its canonical certified ledger together with
the canonical overloading token and role at that ledger. -/
theorem canonicalOverload_eq_some_iff
    {capacity : SurplusCapacity data object}
    {certified : SurplusCertified data object capacity}
    {token : certified.ledger.presented.Token}
    {role : Graph.SameTokenBlockerRoles.Role} :
    canonicalOverload data object = some ⟨⟨capacity, certified⟩, (token, role)⟩ ↔
      canonicalCertifiedCapacityData data object = some ⟨capacity, certified⟩ ∧
        canonicalOverloadTokenAt data object certified = some (token, role) := by
  unfold canonicalOverload
  constructor
  · intro selected
    cases hLedger : canonicalCertifiedCapacityData data object with
    | none => simp [hLedger] at selected
    | some ledger =>
      rw [hLedger, Option.bind_some] at selected
      cases hToken : canonicalOverloadTokenAt data object ledger.2 with
      | none => simp [hToken] at selected
      | some choice =>
        rw [hToken, Option.map_some, Option.some.injEq] at selected
        cases selected
        exact ⟨rfl, hToken⟩
  · rintro ⟨hLedger, hToken⟩
    rw [hLedger, Option.bind_some]
    simp only
    rw [hToken, Option.map_some]

/-- Everything the canonical routing stage satisfies. -/
def SameTokenRoutingSpec (routing : SameTokenRouting data object) : Prop :=
  canonicalOverload data object =
      some ⟨⟨routing.capacity, routing.certified⟩, (routing.token, routing.role)⟩ ∧
    canonicalHomogeneousPatternAt data object routing.certified routing.token
      routing.role = some routing.pattern ∧
    canonicalSameTokenDemandsAt data object routing.certified routing.token
      routing.role routing.pattern = some routing.demands ∧
    canonicalSameTokenRoutesAt data object routing.capacity routing.token
      routing.demands = some routing.routes

theorem canonicalSameTokenRouting_spec_of_eq_some
    {routing : SameTokenRouting data object}
    (selected : canonicalSameTokenRouting data object = some routing) :
    SameTokenRoutingSpec data object routing := by
  unfold canonicalSameTokenRouting at selected
  cases hOverload : canonicalOverload data object with
  | none => simp [hOverload] at selected
  | some overload =>
    rw [hOverload, Option.bind_some] at selected
    cases hPattern : canonicalHomogeneousPatternAt data object overload.1.2
        overload.2.1 overload.2.2 with
    | none => simp [hPattern] at selected
    | some pattern =>
      rw [hPattern, Option.bind_some] at selected
      cases hDemands : canonicalSameTokenDemandsAt data object overload.1.2
          overload.2.1 overload.2.2 pattern with
      | none => simp [hDemands] at selected
      | some demands =>
        rw [hDemands, Option.bind_some] at selected
        cases hRoutes : canonicalSameTokenRoutesAt data object overload.1.1
            overload.2.1 demands with
        | none => simp [hRoutes] at selected
        | some routes =>
          rw [hRoutes, Option.map_some, Option.some.injEq] at selected
          subst selected
          obtain ⟨⟨capacity, certified⟩, token, role⟩ := overload
          exact ⟨hOverload, hPattern, hDemands, hRoutes⟩

theorem canonicalSameTokenRouting_eq_some_of_spec
    {routing : SameTokenRouting data object}
    (spec : SameTokenRoutingSpec data object routing) :
    canonicalSameTokenRouting data object = some routing := by
  obtain ⟨hOverload, hPattern, hDemands, hRoutes⟩ := spec
  unfold canonicalSameTokenRouting
  rw [hOverload, Option.bind_some]
  simp only
  rw [hPattern, Option.bind_some, hDemands, Option.bind_some, hRoutes,
    Option.map_some]

/-! ## The first separator -/

/-- `arm` is the first-entry prefix of `suffix` into `core`: it is a prefix
starting where `suffix` starts, ending at a vertex of `core`, and meeting
`core` only there. -/
def SameTokenFirstEntry (arm suffix : List object.Vertex)
    (core : Finset object.Vertex) : Prop :=
  arm <+: suffix ∧ arm.head? = suffix.head? ∧
    ∃ terminal ∈ core, arm.getLast? = some terminal ∧
      ∀ vertex ∈ arm, vertex ∈ core → vertex = terminal

/-- The two demand endpoints `{d_p, d_q}`: the core of the handoff envelope. -/
def sameTokenCore (demands : SameTokenDemands object) : Finset object.Vertex := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact {demands.firstDemand.2, demands.secondDemand.2}

/-- A first-separator decomposition of two routes: common prefix, separator
`h`, the two next vertices `a ≠ b`, the two tails, and the two first-entry arms
into the core. -/
structure SameTokenFirstSeparator where
  common : List object.Vertex
  separator : object.Vertex
  nextFirst : object.Vertex
  nextSecond : object.Vertex
  tailFirst : List object.Vertex
  tailSecond : List object.Vertex
  armFirst : List object.Vertex
  armSecond : List object.Vertex

/-- **Spec of the first separator** of the canonical routes
(`lem:same-token-bottleneck-routing`, tex 5596-5612): the routes split after
their common prefix at `h` into `a ≠ b`, and each arm is the first-entry prefix
of its tail into the core `{d_p, d_q}`, with the local structure
`envelopeOfFirstSeparator` consumes. -/
def SameTokenSeparatorSpec (routing : SameTokenRouting data object)
    (split : SameTokenFirstSeparator object) : Prop :=
  let core := sameTokenCore object routing.demands
  routing.routes.first.path =
      split.common ++ split.separator :: split.nextFirst :: split.tailFirst ∧
    routing.routes.second.path =
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

/-- **The canonical first separator** of the canonical routes of G, together
with the routing stage it splits. -/
def canonicalSameTokenSeparator :
    Option (SameTokenRouting data object × SameTokenFirstSeparator object) :=
  (canonicalSameTokenRouting data object).bind fun routing =>
    (canonicalChoice (SameTokenSeparatorSpec data object routing)).map
      fun split => (routing, split)

theorem canonicalSameTokenSeparator_spec_of_eq_some
    {routing : SameTokenRouting data object}
    {split : SameTokenFirstSeparator object}
    (selected : canonicalSameTokenSeparator data object = some (routing, split)) :
    canonicalSameTokenRouting data object = some routing ∧
      SameTokenSeparatorSpec data object routing split := by
  unfold canonicalSameTokenSeparator at selected
  cases hRouting : canonicalSameTokenRouting data object with
  | none => simp [hRouting] at selected
  | some chosen =>
    rw [hRouting, Option.bind_some] at selected
    cases hSplit : canonicalChoice (SameTokenSeparatorSpec data object chosen) with
    | none => simp [hSplit] at selected
    | some chosenSplit =>
      rw [hSplit, Option.map_some, Option.some.injEq, Prod.mk.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      exact ⟨rfl, canonicalChoice_spec_of_eq_some hSplit⟩

theorem canonicalSameTokenSeparator_eq_some
    {routing : SameTokenRouting data object}
    {split : SameTokenFirstSeparator object}
    (routingEq : canonicalSameTokenRouting data object = some routing)
    (splitEq : canonicalChoice (SameTokenSeparatorSpec data object routing) =
      some split) :
    canonicalSameTokenSeparator data object = some (routing, split) := by
  unfold canonicalSameTokenSeparator
  rw [routingEq, Option.bind_some, splitEq, Option.map_some]

/-! ## The handoff envelope and support -/

/-- The handoff conditions at a first separator
(`lem:typeA-high-degree-handoff` as `lem:same-token-bottleneck-routing`
applies it, tex 5612-5620): `h` has degree above `δ`, G avoids the target, and
neither ordered next pair is absorbed at the node-`[19]` packing. -/
def SameTokenHandoffConditions (split : SameTokenFirstSeparator object) : Prop :=
  handoffHighDegree data object split.separator ∧
    ¬ Graph.HasCycleWithLength data.LengthOK object ∧
    ¬ handoffAbsorbing data object (canonicalWindowPacking data object)
      split.separator split.nextFirst split.nextSecond ∧
    ¬ handoffAbsorbing data object (canonicalWindowPacking data object)
      split.separator split.nextSecond split.nextFirst

/-- The decorated handoff envelope type at the node-`[19]` packing. -/
abbrev SameTokenEnvelope : Type u :=
  Graph.DecoratedHandoff.Envelope object data.LengthOK
    (handoffHighDegree data object)
    (handoffAbsorbing data object (canonicalWindowPacking data object))

/-- The envelope of a first separator satisfying its spec and the handoff
conditions: exactly `envelopeOfFirstSeparator` on the core `{d_p, d_q}`. -/
def sameTokenEnvelopeOf (routing : SameTokenRouting data object)
    (split : SameTokenFirstSeparator object)
    (spec : SameTokenSeparatorSpec data object routing split)
    (conditions : SameTokenHandoffConditions data object split) :
    SameTokenEnvelope data object :=
  Graph.DecoratedHandoff.envelopeOfFirstSeparator
    (sameTokenCore object routing.demands) split.separator split.nextFirst
    split.nextSecond spec.2.2.1 spec.2.2.2.2.2.1 spec.2.2.2.2.2.2.1
    split.armFirst split.armSecond spec.2.2.2.2.2.2.2.1 spec.2.2.2.2.2.2.2.2.1
    spec.2.2.2.2.2.2.2.2.2.1 spec.2.2.2.2.2.2.2.2.2.2.1
    spec.2.2.2.2.2.2.2.2.2.2.2.1 spec.2.2.2.2.2.2.2.2.2.2.2.2.1
    spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1 spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    conditions.1 conditions.2.1 conditions.2.2.1 conditions.2.2.2

/-- **The canonical same-token handoff envelope of G**: the envelope of the
canonical first separator when it satisfies the handoff conditions, and
`none` otherwise. -/
def canonicalSameTokenEnvelope : Option (SameTokenEnvelope data object) := by
  classical
  exact match canonicalSameTokenSeparator data object with
    | none => none
    | some (routing, split) =>
        if both : SameTokenSeparatorSpec data object routing split ∧
            SameTokenHandoffConditions data object split then
          some (sameTokenEnvelopeOf data object routing split both.1 both.2)
        else none

/-- The physical escape of the handoff (tex 5618-5620): some vertex among the
two next vertices has an edge leaving the envelope's arms, spokes and core
edges, other than towards `h`. -/
def SameTokenEscape (split : SameTokenFirstSeparator object)
    (envelope : SameTokenEnvelope data object) : Prop := by
  classical
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let armEdges (path : List object.Vertex) : Finset (Sym2 object.Vertex) :=
    (path.zip path.tail).toFinset.image (fun pair => s(pair.1, pair.2))
  let coreEdges (support : Finset object.Vertex) : Finset (Sym2 object.Vertex) :=
    support.biUnion fun vertex =>
      (support.filter fun other => object.graph.Adj vertex other).image
        (fun other => s(vertex, other))
  exact ∃ z ∈ ({split.nextFirst, split.nextSecond} : Finset object.Vertex),
    ∃ x : object.Vertex, object.graph.Adj z x ∧ x ≠ split.separator ∧
      s(z, x) ∉
        ((armEdges (envelope.arm split.separator split.nextFirst) ∪
            armEdges (envelope.arm split.separator split.nextSecond) ∪
            {s(split.separator, split.nextFirst), s(split.separator, split.nextSecond)}) ∪
          coreEdges envelope.core)

/-- **The same-token handoff of G at a support `(Y, H)`**: the canonical
envelope exists, escapes physically, and has core `Y` and decorations `H`. -/
def SameTokenHandoffAt (core centres : Finset object.Vertex) : Prop :=
  ∃ routing split envelope,
    canonicalSameTokenSeparator data object = some (routing, split) ∧
    canonicalSameTokenEnvelope data object = some envelope ∧
    SameTokenEscape data object split envelope ∧
    envelope.core = core ∧ envelope.decorations = centres

/-- **The canonical same-token support `(Y, H)` of G** that node `[144]`
hands to the common Type B entry `[65]`. -/
def canonicalSameTokenSupport : Option (Finset object.Vertex × Finset object.Vertex) :=
  canonicalChoice fun support => SameTokenHandoffAt data object support.1 support.2

theorem canonicalSameTokenEnvelope_eq_some_iff
    {envelope : SameTokenEnvelope data object} :
    canonicalSameTokenEnvelope data object = some envelope ↔
      ∃ routing split, canonicalSameTokenSeparator data object = some (routing, split) ∧
        ∃ (spec : SameTokenSeparatorSpec data object routing split)
          (conditions : SameTokenHandoffConditions data object split),
          sameTokenEnvelopeOf data object routing split spec conditions = envelope := by
  classical
  unfold canonicalSameTokenEnvelope
  cases hSep : canonicalSameTokenSeparator data object with
  | none => simp
  | some chosen =>
    obtain ⟨routing, split⟩ := chosen
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · intro selected
      split at selected
      · next both =>
          exact ⟨routing, split, ⟨rfl, rfl⟩, both.1, both.2,
            Option.some.inj selected⟩
      · cases selected
    · rintro ⟨routing', split', ⟨rfl, rfl⟩, spec, conditions, built⟩
      rw [dif_pos ⟨spec, conditions⟩]
      exact congrArg some built

theorem sameTokenEnvelopeOf_core (routing : SameTokenRouting data object)
    (split : SameTokenFirstSeparator object)
    (spec : SameTokenSeparatorSpec data object routing split)
    (conditions : SameTokenHandoffConditions data object split) :
    (sameTokenEnvelopeOf data object routing split spec conditions).core =
      sameTokenCore object routing.demands := rfl

theorem sameTokenEnvelopeOf_decorations (routing : SameTokenRouting data object)
    (split : SameTokenFirstSeparator object)
    (spec : SameTokenSeparatorSpec data object routing split)
    (conditions : SameTokenHandoffConditions data object split) :
    (sameTokenEnvelopeOf data object routing split spec conditions).decorations =
      {split.separator} := by
  simp [sameTokenEnvelopeOf, Graph.DecoratedHandoff.envelopeOfFirstSeparator]

end

end Hypostructure.Graph.Strategy.Spine
