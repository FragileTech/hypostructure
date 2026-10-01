import Hypostructure.Graph.Statements.SurplusPairCode
import Hypostructure.Graph.PairCorrelation
import Hypostructure.Graph.SerialFrobenius

/-!
# Statements: the correlation mass of G's canonical pair overlap system

The exact accounting, in G's labelled `(n,m)` class, of how far the canonical
exposure order of the failed prefix of G's pair schedule is from branching at
every realized signature (`Graph.PairCorrelation`).

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

namespace PairOverlapSystem

/-- **G's canonical exposure order of the failed prefix**: its coordinates in the
rank order of G's canonical encoding of the pair schedule (`rank`). -/
noncomputable def failedOrder {data : Parameters} {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object) :
    Fin system.failedFamily.card ≃ {pair // pair ∈ system.failedFamily} := by
  classical
  let ranks : Finset Nat := system.failedFamily.image system.rank
  have ranksCard : ranks.card = system.failedFamily.card :=
    Finset.card_image_of_injective _ system.rank_injective
  let toRanks : {pair // pair ∈ system.failedFamily} ≃ {rank // rank ∈ ranks} :=
    Equiv.ofBijective
      (fun pair => ⟨system.rank pair.1, Finset.mem_image_of_mem _ pair.2⟩)
      ⟨fun left right same =>
          Subtype.ext (system.rank_injective (congrArg Subtype.val same)),
        fun target => by
          obtain ⟨pair, pairMem, pairRank⟩ := Finset.mem_image.mp target.2
          exact ⟨⟨pair, pairMem⟩, Subtype.ext pairRank⟩⟩
  exact (ranks.orderIsoOfFin ranksCard).toEquiv.trans toRanks.symm

/-- **The correlation profile of G's canonical overlap system** (exact, in G's
labelled `(n,m)` class).  With `P_k` the number of distinct `(baseline word,
first k responses)` signatures realized along `failedOrder`, `t` the size of
the failed prefix and `b` the size of the baseline code:

* `t = index + 1`, and `P_0 = 2^b`;
* `P_k ≤ P_{k+1} ≤ 2 P_k` for `k < t`, and `P_t ≤ |class|`;
* the correlation mass `Σ_{k<t} 2^{t-1-k} (2 P_k − P_{k+1})` satisfies
  `2^{b+t} ≤ |class| + mass`;
* the count failure puts a first non-branching index `k* < t`: the first `k*`
  responses are jointly free with the baseline word
  (`P_j+1 = 2 P_j` for `j < k*`) and the next is correlated with them
  (`P_{k*+1} < 2 P_{k*}`), and the repetition is explicit: some realized
  `k*`-signature (baseline word and first `k*` responses, a point of the code space)
  has a forbidden extension, so the `(k*+1)`-th response is forced by that prefix
  over the whole class;
* the failure gap is at most one maximal step: `2^{b+t-1} ≤ |class|` (the last
  successful level) and every single weighted deficiency
  `2^{t-1-k} (2 P_k − P_{k+1}) ≤ 2^{b+t-1}`, so no coordinate is forced to be
  correlated besides one carrying the whole gap `2^{b+t} − |class| ≤ 2^{b+t-1}`. -/
def CorrelationProfile {data : Parameters} {object : Graph.FiniteObject.{u}}
    (system : PairOverlapSystem data object) : Prop :=
  let P := Graph.SparsePairSkeletonModel.signatureCount (LengthOK := data.LengthOK)
    system.toSkeletonModel system.failedFamily system.failedOrder
  (system.failedFamily.card = system.first.firstFailure.index + 1 ∧
  P 0 = 2 ^ system.first.baselineFamily.card ∧
  (∀ k < system.failedFamily.card, P k ≤ P (k + 1) ∧ P (k + 1) ≤ 2 * P k) ∧
  P system.failedFamily.card ≤ Graph.skeletonBudget object ∧
  2 ^ (system.first.baselineFamily.card + system.failedFamily.card) ≤
    Graph.skeletonBudget object +
      Graph.SparsePairSkeletonModel.mass P system.failedFamily.card ∧
  ∃ k < system.failedFamily.card, (∀ j < k, P (j + 1) = 2 * P j) ∧
    P (k + 1) < 2 * P k ∧
    ∃ p ∈ Set.range (Graph.SparsePairSkeletonModel.signature (LengthOK := data.LengthOK)
        system.toSkeletonModel system.failedFamily system.failedOrder k),
      ∃ v : Prop, Graph.SparsePairSkeletonModel.extendSignature k p v ∉
        Set.range (Graph.SparsePairSkeletonModel.signature (LengthOK := data.LengthOK)
          system.toSkeletonModel system.failedFamily system.failedOrder (k + 1))) ∧
  2 ^ (system.first.baselineFamily.card + system.failedFamily.card - 1) ≤
    Graph.skeletonBudget object ∧
  ∀ k < system.failedFamily.card,
    2 ^ (system.failedFamily.card - 1 - k) *
        Graph.SparsePairSkeletonModel.deficiency P k ≤
      2 ^ (system.first.baselineFamily.card + system.failedFamily.card - 1)

end PairOverlapSystem

/-- **Node `[178]`, the correlation mass of G's canonical overlap system**:
the canonical overlap system has the correlation profile of
`PairOverlapSystem.CorrelationProfile`. -/
def PairCorrelationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ system, canonicalPairOverlapSystem data object = some system ∧
    system.CorrelationProfile

/-- **Nodes `[179]`--`[180]`, coverage decided at G.**  At G's canonical return
system and canonical serial system: coverage of
`lem:pair-system-realizability` is exactly the Type B handoff of the retained
obstruction or a serial demand system on those returns (the target-cycle
alternative is empty at G); the arithmetic
input of `lem:pair-system-increment-arithmetic` does not exist (it would
produce an accepted cycle of G); and coverage of the increment test is exactly
the Type B handoff of the serial system's returns. -/
def PairCoverageStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    (Nonempty (PairSystemRealizabilityOutcome returns) ↔
      PairObstructionHandoff data object returns ∨
        ∃ serial : PairSerialDemandSystem data object, serial.returns = returns) ∧
    ∀ serial : PairSerialDemandSystem data object,
      canonicalPairSerialSystem data object = some serial →
        ¬ Nonempty (PairSerialArithmetic serial) ∧
        (Nonempty (PairIncrementOutcome serial) ↔
          PairObstructionHandoff data object serial.returns)

/-- **Node `[180]`, the full-modulus arithmetic of G's canonical serial system.**
The canonical full-modulus data of the serial system (its frequent increments in
`[1, D_sp]`, their gcd `g`, the canonical smear of its offsets, the Frobenius-filled
central range `SerialSystem.System.FullModulus.spectrum`) does not satisfy all of
`SerialSystem.System.FullModulusArithmetic`: at G one of these fails -- no increment
is frequent, `0` is not an offset, the smear is not below `g`, the doubling orbit
criterion `g − (s+1) < ord_g(2)` fails (in particular for even `g`), or no doubling
orbit lies in the central range. -/
def PairFullModulusStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ serial, canonicalPairSerialSystem data object = some serial ∧
    ¬ serial.toSystem.FullModulusArithmetic serial.lengths_nonempty
      (PairDemandReturns.systemBound serial.returns)

/-- **Node `[179]`, the uncrossing of G's canonical connector routes.**  For G's
canonical return system and its canonical routes `forward : left.2 → right.1`,
`backward : right.2 → left.1`: if the routes are disjoint, the closed walk through
the two demand edges has length one or a non-accepted `|forward| + |backward| + 2`;
if they share a vertex, their uncrossing at the first and last common vertex
(`PathUncrossing.exists_uncrossing`) gives two paths of G, `left.2 → left.1` and
`right.2 → right.1`, of lengths `l₁, l₂ ≤ |forward| + |backward|`, each of which
has length one or a non-accepted `l + 1` (it closes with its demand edge). -/
def PairUncrossingStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    ((∀ v ∈ returns.connectorRoutes.forward.support,
        v ∉ returns.connectorRoutes.backward.support) →
      returns.connectorRoutes.forward.length + returns.connectorRoutes.backward.length + 1 = 1 ∨
        ¬ data.LengthOK (returns.connectorRoutes.forward.length +
          returns.connectorRoutes.backward.length + 2)) ∧
    ((∃ v ∈ returns.connectorRoutes.forward.support,
        v ∈ returns.connectorRoutes.backward.support) →
      ∃ l₁ l₂ : ℕ,
        l₁ ≤ returns.connectorRoutes.forward.length + returns.connectorRoutes.backward.length ∧
        l₂ ≤ returns.connectorRoutes.forward.length + returns.connectorRoutes.backward.length ∧
        (l₁ = 1 ∨ ¬ data.LengthOK (l₁ + 1)) ∧ (l₂ = 1 ∨ ¬ data.LengthOK (l₂ + 1)))

end Hypostructure.Graph.Strategy.Spine
