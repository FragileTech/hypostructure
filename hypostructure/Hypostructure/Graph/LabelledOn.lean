import Mathlib.Data.FinEnum
import Hypostructure.Graph.Object
import Hypostructure.Core.FiniteEntropy

/-!
# Labelled graphs on a fixed vertex count

`Graph.FiniteObject.Vertex : Type u` ranges over every type at that universe,
so `Graph.FiniteObject` itself is not finite, and "graphs on `n` vertices" is
not finite either unless `Vertex` is fixed to one canonical representative
type -- otherwise the same labelled graph recurs once per isomorphic copy of
`Fin n` at that universe, which is not a small count.

`LabelledOn n` is that canonical restriction: `Vertex := Fin n` outright, so
it is literally (a wrapper around) `SimpleGraph (Fin n)`, which Mathlib
already knows is finite (`SimpleGraph.instFinite`). This is exactly `lem:
skeleton-dominates`'s `\mathcal G_{n,m}`'s ambient superset `\mathcal G_n`
(all labelled graphs on `[n]`, before fixing the edge count `m`), realized as
a genuine `Core.Problem`-`Ambient`-shaped finite type instead of an informal
counting argument. -/

namespace Hypostructure.Graph

/-- A labelled simple graph on the canonical vertex set `Fin n`. -/
structure LabelledOn (n : Nat) where
  graph : SimpleGraph (Fin n)

namespace LabelledOn

@[ext] theorem ext {n : Nat} {g h : LabelledOn n} (h' : g.graph = h.graph) : g = h := by
  cases g; cases h; simp_all

/-- `LabelledOn n` is finite: it is literally `SimpleGraph (Fin n)` up to the
trivial wrapper, and Mathlib already knows there are finitely many simple
graphs on any finite vertex type. -/
instance instFinite (n : Nat) : Finite (LabelledOn n) :=
  Finite.of_injective (fun g : LabelledOn n => g.graph) fun _ _ h => ext h

noncomputable instance instFintype (n : Nat) : Fintype (LabelledOn n) :=
  Fintype.ofFinite (LabelledOn n)

/-- Embed a canonical labelled graph into the ambient `Graph.FiniteObject`
type used throughout the framework. The embedding is only used to state
cardinality/pigeonhole facts about the finite class `LabelledOn n`, not to
change how the strategy DAG executes on a given input object -- it is
noncomputable exactly because `DecidableRel` is classical here, not because
anything about the graph itself is unclear. -/
noncomputable def toFiniteObject {n : Nat} (g : LabelledOn n) : FiniteObject.{0} :=
  FiniteObject.of g.graph FinEnum.fin (Classical.decRel g.graph.Adj)

theorem toFiniteObject_injective (n : Nat) :
    Function.Injective (toFiniteObject (n := n)) := by
  intro g h heq
  apply ext
  unfold toFiniteObject at heq
  injection heq

/-- The canonical-state pigeonhole (`Core.FiniteEntropy.card_range_le_card_ambient`),
specialized once and for all to the finite class of labelled graphs on `n`
vertices: any canonical state map on graphs with `n` vertices realizes no
more states than `Nat.card (LabelledOn n)`. This is the one instantiation
`S07`'s entropy cap needs from `Ambient` -- everything past this point
(the pigeonhole inequality itself, its `2 ^ k` form, the rate-floor
compounding) is the already-built, fully generic `Core.FiniteEntropy`
machinery; `LabelledOn n` only supplies the finite carrier that machinery
was missing. -/
theorem card_range_le_card {State : Type*} (n : Nat) (stateOf : LabelledOn n -> State) :
    Nat.card (Set.range stateOf) ≤ Nat.card (LabelledOn n) :=
  Core.FiniteEntropy.card_range_le_card_ambient stateOf

/-! ## Realization of states by labelled graphs

`lem:skeleton-dominates` assigns target-complete states to labelled graphs
*canonically*: "all auxiliary objects used in the proof ... are functions of
the labelled adjacency matrix once a deterministic tie-breaking rule is
fixed". A canonical assignment is therefore a plain map
`stateOf : LabelledOn n -> State`, and the family of states the proof
*realizes* is exactly its range.

Consequently the two things a downstream entropy comparison needs -- a
labelled graph realizing each realized state, and the injectivity of that
realization -- are **theorems about the range of the canonical map**, not
extra data an adapter has to assume. Distinct realized states must come from
distinct labelled graphs precisely because `stateOf` is a function: the
graph chosen in a state's fibre already determines the state again. -/

/-- The realized-state family of a canonical assignment: exactly the states
the assignment actually takes, no more. -/
abbrev Realized {State : Type*} {n : Nat} (stateOf : LabelledOn n -> State) :=
  Set.range stateOf

/-- Realization: every realized state is realized by a labelled graph on `n`
vertices. This is the canonical choice inside the state's own fibre, so it
needs no hypothesis beyond `stateOf` being a function. -/
noncomputable def realize {State : Type*} {n : Nat}
    (stateOf : LabelledOn n -> State) (state : Realized stateOf) :
    LabelledOn n :=
  Set.rangeSplitting stateOf state

/-- The realizing graph does realize the state it was chosen for. -/
theorem stateOf_realize {State : Type*} {n : Nat}
    (stateOf : LabelledOn n -> State) (state : Realized stateOf) :
    stateOf (realize stateOf state) = (state : State) :=
  Set.apply_rangeSplitting stateOf state

/-- Realization injectivity, as a theorem: two distinct realized states are
realized by two distinct labelled graphs. -/
theorem realize_injective {State : Type*} {n : Nat}
    (stateOf : LabelledOn n -> State) :
    Function.Injective (realize stateOf) :=
  Set.rangeSplitting_injective stateOf

/-- `lem:state-count-comparison` for the canonical assignment: the realized
states never outnumber the labelled skeletons. Proved from `realize` and
`realize_injective` above, so no adapter supplies it. -/
theorem card_realized_le {State : Type*} (n : Nat)
    (stateOf : LabelledOn n -> State) :
    Nat.card (Realized stateOf) ≤ Nat.card (LabelledOn n) :=
  Nat.card_le_card_of_injective _ (realize_injective stateOf)

/-- The entropy cap in its realized form: a canonical assignment that
realizes at least `2 ^ k` states forces `2 ^ k` labelled skeletons to exist.
`lem:independent-target-entropy` composed with `lem:skeleton-dominates`, with
no realization hypothesis left anywhere. -/
theorem two_pow_le_card_of_realized {State : Type*} {n k : Nat}
    (stateOf : LabelledOn n -> State)
    (realizes : 2 ^ k ≤ Nat.card (Realized stateOf)) :
    2 ^ k ≤ Nat.card (LabelledOn n) :=
  realizes.trans (card_realized_le n stateOf)

/-- The overflow branch of a canonical assignment is empty: no canonical
assignment can realize more states than there are labelled skeletons. This
is the closing step of every entropy-cap argument, and it is now a theorem
rather than a consequence of an assumed injection. -/
theorem not_card_lt_card_realized {State : Type*} (n : Nat)
    (stateOf : LabelledOn n -> State) :
    ¬ Nat.card (LabelledOn n) < Nat.card (Realized stateOf) :=
  Nat.not_lt_of_ge (card_realized_le n stateOf)

end LabelledOn

end Hypostructure.Graph
