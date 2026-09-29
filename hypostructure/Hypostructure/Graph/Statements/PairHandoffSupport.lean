import Hypostructure.Graph.Statements.PairArms
import Hypostructure.Graph.Statements.SurplusPairOutcome

/-!
# Statements: the Type B support of G's pair-obstruction handoff (residual `[187]`)

Node `[187]`'s Type B entry is produced by the `[179]`/`[180]` early outcome, whose only
surviving alternative is `PairObstructionHandoff` (sparse exits (b), (c) and the target cycle
are excluded at G).  The entry key `K .typeBFanEntry` pins the support `(Y, H)` as an
existential; the two facts below are the quantitative shape of that one canonical support,
stated about G's retained obstruction only:

* `PairHandoffSupportStatement`: the support is `(Y, H) = ({d_p.2, d_q.2}, {h})` with `h` the
  obstruction's canonical first separator, `H` is nonempty and consists of high centres (the
  "nonempty and all high" reading of the Type B entry), and the whole support lies in the
  obstruction's overlap support `U`;
* `PairHandoffChargeStatement`: the ambient surplus of that support: the core ends are cubic
  port ends, so `σ(Y) = 0`, the core and the centre are disjoint, and `ω(H) = d(h) - δ ≥ 1`.

* `PairHandoffNetChargeStatement`: the net charge of that support (`def:net-charge`): the core has
  one or two vertices, `(δ-1)|Y| ≤ def⁺(Y) ≤ δ|Y|`, and the envelope's charge is negative, or
  `ω(H) < def⁺(Y)`, i.e. the centre has degree `< 3δ` (the cap of the Type B certificate).

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- **The canonical Type B support of G's pair-obstruction handoff, exactly.**  -/
def PairHandoffSupportStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    ∃ (routes : PairObstructionRoutes object) (split : SameTokenFirstSeparator object)
      (core centres : Finset object.Vertex),
      canonicalPairObstructionSeparator data object returns = some (routes, split) ∧
      canonicalPairObstructionSupport data object returns = some (core, centres) ∧
      core = pairObstructionCore data object returns ∧
      centres = {split.separator} ∧
      centres.Nonempty ∧
      (∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre) ∧
      (∀ vertex ∈ core, vertex ∈
        returns.overlap.system.overlapSupport returns.overlap.family) ∧
      (∀ vertex ∈ centres, vertex ∈
        returns.overlap.system.overlapSupport returns.overlap.family)

/-- **The ambient surplus of that support**: `σ(Y) = 0` (the core ends are cubic port
ends), `Y ∩ H = ∅`, and `ω(H) = d_G(h) - δ ≥ 1` for the one centre `h`. -/
def PairHandoffChargeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    ∃ (core centres : Finset object.Vertex),
      canonicalPairObstructionSupport data object returns = some (core, centres) ∧
      (∀ vertex ∈ core, object.degree vertex = data.threshold) ∧
      object.ambientSurplus core data.threshold = 0 ∧
      Disjoint core centres ∧
      (∃ centre, centres = {centre} ∧
        object.ambientSurplus centres data.threshold =
          object.degree centre - data.threshold) ∧
      1 ≤ object.ambientSurplus centres data.threshold

/-- **The net charge of that support, exactly**: `1 ≤ |Y| ≤ 2` (the core is `{d_p.2, d_q.2}`),
`(δ-1)|Y| ≤ def⁺(Y) ≤ δ|Y|` (a core end has at most `|Y|-1 ≤ 1` neighbours in `Y`), and at
the canonical envelope either the net charge `No(𝔛) = def⁺(Y) - ω(H) - |Y|/s` is negative, or
`ω(H) < def⁺(Y)`, so the one centre has degree `< 3δ`. -/
def PairHandoffNetChargeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    ∃ (core centres : Finset object.Vertex),
      canonicalPairObstructionSupport data object returns = some (core, centres) ∧
      1 ≤ core.card ∧ core.card ≤ 2 ∧
      (data.threshold - 1) * core.card ≤
        object.positiveDeficiency core data.threshold ∧
      object.positiveDeficiency core data.threshold ≤ data.threshold * core.card ∧
      ∀ envelope : SameTokenEnvelope data object,
        canonicalPairObstructionEnvelope data object returns = some envelope →
        envelope.NegativeCharge data.threshold data.dischargeScale ∨
          (object.ambientSurplus centres data.threshold <
              object.positiveDeficiency core data.threshold ∧
            ∃ centre, centres = {centre} ∧ object.degree centre < 3 * data.threshold)

end Hypostructure.Graph.Strategy.Spine
