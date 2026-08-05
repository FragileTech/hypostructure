import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Strategy.BoundaryDemandAccountingSemantics

/-!
# Residual-indexed local-supply semantics

Inert presentation data for the single CT14 execution implemented in
`LocalSupplyLowerBound.lean`.  The record supplies the local member family,
its labels, the three pointwise numeric observations, and the single
pointwise inequality that Core sums over CT14's exact schedule.
-/

namespace Hypostructure.Core.Strategy.LocalSupplyLowerBound

universe uResidual uAmbient uMember uLabel

open Hypostructure.Core.Strategy

/-- Finite net-deficiency accounting derived from CT14's exact lower and
upper aggregate ledgers.  The fields are published by the producing
Strategy, never supplied to a later consumer. -/
structure NetDeficiencyAccounting where
  scale : Nat
  coefficient : Nat
  deficiency : Nat
  remainder : Nat
  surplus : Nat
  scale_pos : 0 < scale
  finiteCap :
    scale * deficiency ≤ coefficient * remainder + scale * surplus

/-- The net-cap contradiction, stated once on the accounting that owns it.

`finiteCap` caps the normalized deficiency by the accounting's own rate
`coefficient / scale`.  No rate strictly above that one can be reached on a
nonempty remainder: the two bounds on `deficiency - surplus` cross.

The threshold rate is a parameter rather than a written constant, and it is the
*only* place a threshold enters this file.  The manuscript's node-[60] instance
is obtained by instantiating `rate` at the Erdős–Gyárfás discharging rate of
`def:net-charge`; a presentation with a different discharging rate obtains its
own instance from the same statement, with no change here.

This is deliberate.  The discharging rate is not a framework constant and is
not determined by the accounting either: in the manuscript it is a *chosen*
per-vertex charge `α`, entering as `ch(v) = (b - d_X(v)) - α` on a baseline
degree `b` (`lem:typeA-unsaturated-discharge`) and constrained only from the
supply side by `α > τ_win` (`prop:negative-net-charge`, node [56]).  Every
other numeral in that development is a consequence of the choice, not an
independent input: the saturation threshold is `q(w)/α`, the surviving receiver
capacities are `q(w)/α - 1`, the route-8 burden factor is `1/α`, and the Type B
fan deficit is `c - (b - α(d_G(h) + 1))`.  The Graph adapter already carries the
choice explicitly, as `ReceiverLoad.LoadCapacityProfile.loadMultiplier = 1/α`
alongside its `baselineDegree = b`.

A Core carrier that stored `α` would therefore be storing an *input of the
domain*, not anything derivable from the residual, so it is taken as a
parameter of the one statement that consumes it.

The producer publishes the complementary quantity: `coefficient / scale` is the
*cap it proved*, `observedSupply / remainder`
(`Profile.summaryOfResidual`), both numbers being aggregates of the same member
schedule.  The two meet at the applicability hypothesis `above`, which is the
manuscript's node-`[56]` comparison `Δ_net(R) ≤ τ_win < α`.  Storing `α` in
`coefficient / scale` instead would be strictly wrong rather than redundant:
`above` is strict, so a producer that published `α` would make this theorem
inapplicable at `α` -- the one rate `def:net-charge` needs. -/
theorem NetDeficiencyAccounting.not_rate_reached
    (accounting : NetDeficiencyAccounting) {rate : ℝ}
    (above : (accounting.coefficient : ℝ) / accounting.scale < rate)
    (remainderPos : 0 < accounting.remainder) :
    ¬ (rate * accounting.remainder + accounting.surplus ≤
        accounting.deficiency) := by
  intro reached
  have scalePos : (0 : ℝ) < accounting.scale := by
    exact_mod_cast accounting.scale_pos
  have remainderPosReal : (0 : ℝ) < accounting.remainder := by
    exact_mod_cast remainderPos
  have capReal : (accounting.scale : ℝ) * accounting.deficiency ≤
      (accounting.coefficient : ℝ) * accounting.remainder +
        (accounting.scale : ℝ) * accounting.surplus := by
    exact_mod_cast accounting.finiteCap
  have aboveMul : (accounting.coefficient : ℝ) < rate * accounting.scale :=
    (div_lt_iff₀ scalePos).1 above
  nlinarith [mul_le_mul_of_nonneg_left reached scalePos.le,
    mul_lt_mul_of_pos_right aboveMul remainderPosReal]

/-- Exact numeric ledger published by one completed local-supply bound.

`assignedSurplus` is the aggregate of the registered per-member surplus
observation over CT14's own exact member schedule.  It is the quantity the
node-[62] split consumes: on the graph adapter it is
`∑_{h ∈ R} (d_G(h) - baseline)`, the surplus assigned to the normalized
support by its own high-degree members. -/
structure Summary where
  requiredMass : Nat
  /-- Raw observed term before CT14 adds the registered correction.  At paper
  row 39 this is the literal aggregate `W₂(R)`. -/
  observedTerm : Nat
  /-- Registered correction added to the raw term.  At paper row 39 this is
  `2 def⁺(R)`. -/
  defectCorrection : Nat
  observedSupply : Nat
  /-- CT14's capacity column is exactly the raw term plus its correction. -/
  observedSupply_decomposition :
    observedSupply = observedTerm + defectCorrection
  /-- The aggregated pointwise theorem before any asymptotic specialization. -/
  rawLowerBound : requiredMass ≤ observedTerm + defectCorrection
  assignedSurplus : Nat
  /-- Size of the *atom part* of CT14's own exact member schedule: the members
  on which the registered `surplus` observation vanishes.

  This is the subcubicity coordinate of `def:remainder-entropy`'s constrained
  remainder family `𝒢(R)`.  The registered surplus observation is the excess
  of an item's ambient degree over the presentation's own baseline degree, so
  it vanishes exactly on the members whose degree does not exceed that
  baseline — the manuscript's "subcubicity on the atom part", with the
  manuscript's `3` being the registered baseline and never a numeral.  A
  presentation with a different baseline publishes the same field with the
  statement its own baseline gives. -/
  subcubicAtomCard : Nat
  netDeficiency : NetDeficiencyAccounting
  /-- Subcubicity of the remainder, in the published coordinates: every member
  of the schedule either lies in the atom part or contributes at least one unit
  to `assignedSurplus`, so all but `assignedSurplus` members of the remainder
  are subcubic against the registered baseline.  A consumer reads this off the
  ledger instead of re-deriving it from the residual. -/
  subcubicAtomPart :
    netDeficiency.remainder ≤ subcubicAtomCard + assignedSurplus
  /-- **The assigned surplus is carried by an individual member.**

  A positive aggregate surplus is not merely a number: it is a sum of the
  registered per-member surplus observation over CT14's own exact member
  schedule, so some single member of that schedule carries a positive surplus
  and therefore lies outside the atom part.  In the published coordinates that
  says the atom part is a *proper* part of the remainder.

  This is the one fact of `def:canonical-decomp`'s assigned support that the
  numeric aggregate alone does not carry.  It is *not* derivable from the other
  published fields: `subcubicAtomPart` permits `subcubicAtomCard =
  netDeficiency.remainder` whenever `0 < assignedSurplus`, so only the producer,
  which still holds the member schedule, can establish it.

  On the graph adapter (`Graph.Strategy.NormalizationRank.localSupply`) the
  registered surplus is `d_G(v) - baselineDegree`, so the atom part is the
  subcubic part of the normalized support `R` and this field says that some
  member `h ∈ R` has `baselineDegree < d_G(h)` — the individual high-degree fan
  centre the Type B continuation needs.  No numeral appears: the baseline enters
  only through the registration that defines `surplus`. -/
  assignedSurplusNonAtom :
    0 < assignedSurplus → subcubicAtomCard < netDeficiency.remainder
  /-- The net-deficiency cap, computed by the producing Strategy from its own
  aggregates over CT14's exact member schedule.

  Read against the published member count `netDeficiency.remainder` this is the
  *density* statement
  `(requiredMass - assignedSurplus) / remainder ≤ observedSupply / remainder`
  (`Summary.netDeficiencyDensity_le_cap`): the positive net deficiency of the
  remainder, per member, is at most the external supply available to it, per
  member.  It is the fourth coordinate of `def:remainder-entropy`'s constrained
  remainder family `𝒢(R)`, "positive net-deficiency density at most the current
  cap".

  The cap is not a constant.  It is the ratio of two numbers this same ledger
  entry publishes, `observedSupply / netDeficiency.remainder`.  On the graph
  adapter that is `(e(R, W) + ∑_v max(0, k - d_G(v))) / |R|` with `k` the
  registered baseline; on a residual whose ambient minimum degree meets the
  baseline the correction term vanishes and the cap is exactly `e(R, W) / |R|`,
  the remainder-deficiency density cap of `lem:stub-positive`.  A presentation
  with a different baseline, or a residual with a different external supply,
  publishes the same field at its own cap. -/
  netDeficiencyCap : requiredMass ≤ observedSupply + assignedSurplus
  /-- `n`: the ambient item count CT9 partitioned, routed here verbatim
  through the boundary-accounting ledger this Strategy consumes
  (`BoundaryDemandAccounting.Summary.ambientCount`).  Nothing is recomputed;
  the number is CT9's own. -/
  ambientCount : Nat
  /-- `|W|`: CT9's selected fibre count, routed here the same way.  For the
  Erdős–Gyárfás presentation the selected part is the vertex set covered by the
  packed windows, so this is `13 p₁₃` and not the window count `p₁₃`. -/
  selectedCount : Nat
  /-- `|R|`: CT9's complementary fibre count, routed here the same way.  It is
  the normalization's own count of the remainder; `netDeficiency.remainder` is
  this Strategy's own count of the member schedule it aggregated over. -/
  complementCount : Nat

/-- Exact finite form of an asymptotic substitution.  If the required mass is
`baseline · |R|` and the correction has scaled density at most
`correctionCoefficient / scale` up to `error`, then the raw observed term has
the complementary lower density, with the same explicit error. -/
theorem Summary.scaledObservedLowerBound (summary : Summary)
    {mass baseline scale correctionCoefficient error : Nat}
    (requiredExact :
      summary.requiredMass = baseline * mass)
    (correctionCap :
      scale * summary.defectCorrection ≤
        correctionCoefficient * mass + error) :
    (scale * baseline - correctionCoefficient) *
        mass ≤
      scale * summary.observedTerm + error := by
  have scaledRaw := Nat.mul_le_mul_left scale summary.rawLowerBound
  rw [requiredExact] at scaledRaw
  have combined :
      scale * (baseline * mass) ≤
        scale * summary.observedTerm +
          correctionCoefficient * mass + error :=
    calc
      scale * (baseline * mass)
          ≤ scale * (summary.observedTerm + summary.defectCorrection) :=
        scaledRaw
      _ = scale * summary.observedTerm +
            scale * summary.defectCorrection := by ring
      _ ≤ scale * summary.observedTerm +
            (correctionCoefficient * mass + error) :=
        Nat.add_le_add_left correctionCap _
      _ = scale * summary.observedTerm +
            correctionCoefficient * mass + error := by
        omega
  rw [Nat.sub_mul]
  apply Nat.sub_le_iff_le_add.mpr
  simpa [Nat.mul_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    combined

/-- Paper `lem:wedge-lower`'s asymptotic substitution in exact finite form.

At row 39, `requiredMass = 3 |R|`, `defectCorrection = 2 def⁺(R)`, and the
incoming row-38 fact has the division-free form

`scale * def⁺(R) ≤ capNumerator * |R| + error`.

The conclusion is exactly

`(3 * scale - 2 * capNumerator) |R| ≤ scale * W₂(R) + 2 * error`.

Thus the row computes both paper consequences from whichever certified cap is
present in the canonical ledger.  For the window-only cap the coefficient is
`2.54365026308…`; for the sharper high-entropy cap it is
`2.57407357888…`.  The theorem does not hardcode either branch constant: its
output coefficient is forced arithmetically by the incoming exact numerator. -/
theorem Summary.wedgeLowerBoundOfDeficiencyCap (summary : Summary)
    {mass deficiency scale capNumerator error : Nat}
    (requiredExact : summary.requiredMass = 3 * mass)
    (correctionExact : summary.defectCorrection = 2 * deficiency)
    (deficiencyCap :
      scale * deficiency ≤ capNumerator * mass + error) :
    (scale * 3 - 2 * capNumerator) * mass ≤
      scale * summary.observedTerm + 2 * error := by
  apply summary.scaledObservedLowerBound
    (mass := mass) (baseline := 3) (scale := scale)
    (correctionCoefficient := 2 * capNumerator) (error := 2 * error)
    requiredExact
  rw [correctionExact]
  calc
    scale * (2 * deficiency) = 2 * (scale * deficiency) := by ring
    _ ≤ 2 * (capNumerator * mass + error) :=
      Nat.mul_le_mul_left 2 deficiencyCap
    _ = (2 * capNumerator) * mass + 2 * error := by ring

/-- Density form of the published net-deficiency cap: the positive net
deficiency per member is at most the supply per member.

Both sides are divided by the same published member count, so no positivity
hypothesis is needed; on an empty schedule the statement degenerates to
`0 ≤ 0`.  The cap on the right is read off the ledger entry, never written. -/
theorem Summary.netDeficiencyDensity_le_cap (summary : Summary) :
    ((summary.requiredMass : ℝ) - (summary.assignedSurplus : ℝ)) /
        (summary.netDeficiency.remainder : ℝ) ≤
      (summary.observedSupply : ℝ) / (summary.netDeficiency.remainder : ℝ) := by
  have cap : (summary.requiredMass : ℝ) ≤
      (summary.observedSupply : ℝ) + (summary.assignedSurplus : ℝ) := by
    exact_mod_cast summary.netDeficiencyCap
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

/-- Scaled, division-free form of the same cap, in the exact shape the
downstream scaled-deficiency consumers already read
(`scale * deficiency ≤ coefficient * remainder + scale * surplus` at
`scale := remainder`, `coefficient := observedSupply`).  Nothing is recomputed:
it is the published cap multiplied by the published member count. -/
theorem Summary.remainder_mul_requiredMass_le_cap (summary : Summary) :
    summary.netDeficiency.remainder * summary.requiredMass ≤
      summary.observedSupply * summary.netDeficiency.remainder +
        summary.netDeficiency.remainder * summary.assignedSurplus := by
  have cap := summary.netDeficiencyCap
  calc
    summary.netDeficiency.remainder * summary.requiredMass
        ≤ summary.netDeficiency.remainder *
            (summary.observedSupply + summary.assignedSurplus) :=
          Nat.mul_le_mul (Nat.le_refl _) cap
    _ = summary.observedSupply * summary.netDeficiency.remainder +
          summary.netDeficiency.remainder * summary.assignedSurplus := by
        ring

/-- The ledger-only form of the subcubicity fact: at least
`remainder - assignedSurplus` members of the remainder lie in the atom part.
Every consumer that holds the published `Summary` obtains it without touching
the residual, the graph, or the member schedule again. -/
theorem Summary.remainder_sub_assignedSurplus_le_subcubicAtomCard
    (summary : Summary) :
    summary.netDeficiency.remainder - summary.assignedSurplus ≤
      summary.subcubicAtomCard := by
  have law := summary.subcubicAtomPart
  omega

/-- A positive published surplus forces a nonempty remainder.

The atom part is a count over the same member schedule the remainder counts, so
the strict inequality published by `assignedSurplusNonAtom` already bounds the
remainder below.  A consumer that has to supply `0 < netDeficiency.remainder` —
for instance the net-cap contradiction of node `[60]`, whose statement takes
exactly that hypothesis — reads it off the ledger instead of asserting it. -/
theorem Summary.remainder_pos_of_assignedSurplus_pos (summary : Summary)
    (positive : 0 < summary.assignedSurplus) :
    0 < summary.netDeficiency.remainder :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (summary.assignedSurplusNonAtom positive)

/-- Vanishing published surplus means the whole remainder is subcubic against
the registered baseline: the atom part is all of it. -/
theorem Summary.remainder_le_subcubicAtomCard_of_assignedSurplus_eq_zero
    (summary : Summary) (surplusFree : summary.assignedSurplus = 0) :
    summary.netDeficiency.remainder ≤ summary.subcubicAtomCard := by
  have law := summary.subcubicAtomPart
  omega

/-! ### The node-`[29]`/`[56]` window-join arithmetic on the published counts

The two theorems below are the exact, asymptotics-free arithmetic of
`cor:global-window-join-pressure`, stated on the numbers this ledger entry
publishes and nothing else.  No numeral occurs in either statement: the
manuscript's `73` is `4 · stubRate + windowOrder`, the manuscript's `13` is
`windowOrder`, and the manuscript's `15` is `stubRate`.  Both are universally
quantified in exactly the style of `NetDeficiencyAccounting.not_rate_reached`
and of the continuation's `DensityCap56`, so a presentation instantiates them
at whatever window order and per-window stub rate its own registered packing
carries.  For the Erdős–Gyárfás presentation the instantiation is
`windowOrder = 13`, `stubRate = baseline · windowOrder - 2 · (windowOrder - 1)
= 3 · 13 - 24 = 15`, and then `4 · 15 + 13 = 73`, the manuscript's own
`\theta = 1/73` threshold. -/

/-- **The node-`[59]` net-charge alternative, forced by the packing-density
cap.**

Let `p` be the window count, `windowOrder` the vertex order of one packed
window and `stubRate` the per-window external stub rate.  The three premises
are the three structural facts the manuscript uses at this point:

* `windowCover`: the selected part of the ambient support is the vertex set of
  the `p` vertex-disjoint packed windows, `|W| = windowOrder · p` (for
  Erdős–Gyárfás, `|W| = 13 p₁₃`);
* `partition`: CT9's own partition `|R| + |W| = n`, which with the previous
  premise is the manuscript's `|R| = n - 13 p₁₃`;
* `densityCap`: the packing-density cap `(4 · stubRate + windowOrder) · p < n`,
  i.e. the manuscript's `73 p₁₃ < n` of `prop:p13-density`.

The conclusion is the manuscript's dichotomy at node `[59]`: either the
remainder already has negative net charge at the discharging rate `1/4` --
which is `prop:negative-net-charge`'s hypothesis in the ledger's coordinates,
`4 (def⁺(R) - σ_R) < |R|` -- or the positive net deficiency exceeds the whole
window-stub supply, `def⁺(R) - σ_R > stubRate · p`.

The second alternative is not a dead end: read against
`lem:surplus-aware-window-stub`'s `def⁺(R) ≤ stubRate · p + σ_W` it forces
`σ_W > σ_R`, quantified by
`windowJoinPressure_of_not_negativeNetCharge` below.  That is exactly the
window-join pressure the manuscript routes to nodes `[135]`--`[136]`.

Integer subtraction is used on the net deficiency for the same reason
`NegativeNetCharge` does: truncated natural subtraction cannot represent an
overpaid support. -/
theorem Summary.negativeNetCharge_or_windowStubExcess (summary : Summary)
    {windowOrder stubRate windowCount : Nat}
    (windowCover : summary.selectedCount = windowOrder * windowCount)
    (partition :
      summary.netDeficiency.remainder + summary.selectedCount =
        summary.ambientCount)
    (densityCap :
      (4 * stubRate + windowOrder) * windowCount < summary.ambientCount) :
    4 * ((summary.requiredMass : Int) - (summary.assignedSurplus : Int)) <
        (summary.netDeficiency.remainder : Int) ∨
      ((stubRate * windowCount : Nat) : Int) <
        (summary.requiredMass : Int) - (summary.assignedSurplus : Int) := by
  obtain ⟨stubSupply, stubEq⟩ : ∃ value, stubRate * windowCount = value :=
    ⟨_, rfl⟩
  obtain ⟨coverSize, coverEq⟩ : ∃ value, windowOrder * windowCount = value :=
    ⟨_, rfl⟩
  have capSplit : (4 * stubRate + windowOrder) * windowCount =
      4 * stubSupply + coverSize := by
    rw [← stubEq, ← coverEq]; ring
  rw [capSplit] at densityCap
  rw [windowCover, coverEq] at partition
  rw [stubEq]
  omega

/-- **`lem:typeA-unsaturated-discharge` against `def:net-charge`, exactly.**

Manuscript node `[92]`, "unsaturated Type A charge closes".  On the Type A
branch the assigned surplus vanishes and node `[61]` selected the support for
its *negative* net charge, `4(def⁺(X) - σ_R) < |R|`.  If in addition every
receiver is unsaturated, `lem:typeA-unsaturated-discharge` gives
`|V(X)| ≤ 4 def⁺(X)`, and the two are exact opposites.

Every quantity is read off this one published ledger entry; the caller supplies
only the two branch facts, both of which its own stage already carries.  The
`4` is `def:net-charge`'s discharging scale, the same constant
`negativeNetCharge_or_windowStubExcess` above is stated at. -/
theorem Summary.unsaturatedChargeContradiction (summary : Summary)
    (noSurplus : summary.assignedSurplus = 0)
    (negative :
      4 * ((summary.requiredMass : Int) - (summary.assignedSurplus : Int)) <
        (summary.netDeficiency.remainder : Int))
    (discharge :
      summary.netDeficiency.remainder ≤ 4 * summary.requiredMass) :
    False := by
  rw [noSurplus] at negative
  have cast : (summary.netDeficiency.remainder : Int) ≤
      4 * (summary.requiredMass : Int) := by exact_mod_cast discharge
  simp only [Nat.cast_zero, sub_zero] at negative
  linarith

/-- **`cor:global-window-join-pressure`, exactly.**

The manuscript's own conclusion on the alternative branch of the previous
theorem.  `windowStub` is `lem:surplus-aware-window-stub`'s supply bound
`def⁺(R) ≤ stubRate · p + σ_W` in the published coordinates, with `σ_W` the
window surplus; `windowCover` and `partition` are as above.  If the remainder
does *not* have negative net charge, then

  `n ≤ (4 · stubRate + windowOrder) · p + 4 (σ_W - σ_R)`,

which is the manuscript's

  `σ_W - σ_R ≥ (n - 73 p₁₃) / 4`

with the division cleared.  Again no numeral is written: `73` is
`4 · stubRate + windowOrder`.

This is the statement the manuscript routes to nodes `[135]`--`[136]` and
records as the other half of invariant row 24.  It is *not* a consequence of
the stub inequality; it is the price of avoiding a negative support. -/
theorem Summary.windowJoinPressure_of_not_negativeNetCharge (summary : Summary)
    {windowOrder stubRate windowCount windowSurplus : Nat}
    (windowStub :
      summary.requiredMass ≤ stubRate * windowCount + windowSurplus)
    (windowCover : summary.selectedCount = windowOrder * windowCount)
    (partition :
      summary.netDeficiency.remainder + summary.selectedCount =
        summary.ambientCount)
    (notNegative :
      ¬ (4 * ((summary.requiredMass : Int) - (summary.assignedSurplus : Int)) <
        (summary.netDeficiency.remainder : Int))) :
    (summary.ambientCount : Int) ≤
      (((4 * stubRate + windowOrder) * windowCount : Nat) : Int) +
        4 * ((windowSurplus : Int) - (summary.assignedSurplus : Int)) := by
  obtain ⟨stubSupply, stubEq⟩ : ∃ value, stubRate * windowCount = value :=
    ⟨_, rfl⟩
  obtain ⟨coverSize, coverEq⟩ : ∃ value, windowOrder * windowCount = value :=
    ⟨_, rfl⟩
  have capSplit : (4 * stubRate + windowOrder) * windowCount =
      4 * stubSupply + coverSize := by
    rw [← stubEq, ← coverEq]; ring
  rw [capSplit]
  rw [stubEq] at windowStub
  rw [windowCover, coverEq] at partition
  omega

/-- Residual-owned local presentation.  Every field is indexed by the residual
alone, so `pointwise` is a law the domain adapter proves from the incoming
residual and nothing else.

The exact support-complement ledger is not a registration field: Core supplies
it as a typed ledger query.  The producer therefore enumerates and accounts for
members from the inherited complement itself. -/
structure Registration (Residual : Type uResidual)
    (AmbientItem : Residual → Type uAmbient) where
  Member : Residual → Type uMember
  Label : Residual → Type uLabel
  members : (residual : Residual) →
    Core.Finite.Enumeration (AmbientItem residual) →
      Core.Finite.Enumeration (Member residual)
  requiredMass : (residual : Residual) →
    Core.Finite.Enumeration (AmbientItem residual) → Member residual → Nat
  observedSupply : (residual : Residual) →
    Core.Finite.Enumeration (AmbientItem residual) → Member residual → Nat
  defectCorrection : (residual : Residual) →
    Core.Finite.Enumeration (AmbientItem residual) → Member residual → Nat
  /-- Per-member surplus above the presentation's own baseline.  This is a
  primitive observation of exactly the same kind as `requiredMass` and
  `defectCorrection`; Core aggregates it over CT14's exact member schedule and
  publishes the total as `Summary.assignedSurplus`.  It carries no law. -/
  surplus : (residual : Residual) →
    Core.Finite.Enumeration (AmbientItem residual) → Member residual → Nat
  label : (residual : Residual) →
    Core.Finite.Enumeration (AmbientItem residual) → Member residual → Label residual
  labelDecidableEq : (residual : Residual) → DecidableEq (Label residual)
  pointwise : ∀ residual complement member,
    requiredMass residual complement member ≤
      observedSupply residual complement member +
        defectCorrection residual complement member

end Hypostructure.Core.Strategy.LocalSupplyLowerBound
