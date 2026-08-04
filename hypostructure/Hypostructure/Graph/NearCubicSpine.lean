import Hypostructure.Graph.TypeBFanMass
import Hypostructure.Graph.Strategy.ScaleThresholdDichotomy
import Hypostructure.Core.Strategy.ScaleThresholdDichotomy
import Hypostructure.Graph.Strategy.Official.Features.DegreeSurplusLedger
import Hypostructure.Graph.InducedPathMaximalPacking

/-!
# Reading `def:near-cubic-spine` off the node-`[19]` branch

`def:near-cubic-spine` is not an extra global assumption.  The manuscript says
so itself:

> When a later local lemma states `def:near-cubic-spine` among its hypotheses,
> that line records the branch state needed for the normalized estimate, not an
> additional global assumption.

and `prop:nonnear-cubic-sharp-overload-routing` is the proved trichotomy that
supplies it: arm (a) is the near-cubic estimate `σ(G) = O(√n)`, arm (b) is a
sparse surplus exit, arm (c) is the routing of decorated Type B fan data into
the Type B fan ledger.

In the executable proof that trichotomy is the authored node-`[19]`
`scaleThresholdDichotomy`:

* the **at-or-below** arm is arm (a).  Its residual is Core's
  `ScaleThresholdDichotomy.Profile.AtOrBelowResidual`, whose CT14 capacity
  outcome literally records `load ≤ threshold`.  For the graph registration
  `Graph.Strategy.ScaleThresholdDichotomy.degreeSurplusRegistration` the load
  is `object.degreeSurplus baselineDegree` and the threshold is the audited
  square-root table evaluated at `object.vertexCount`, so the recorded fact is
  `σ(G) ≤ c·⌈√n⌉`.
* the **strict-above** arm is the non-near-cubic case, handed to the
  surplus-pair accounting of nodes `[125]`--`[144]`, where arms (b) and (c) are
  the exceptional and structured outputs of the homogeneous bottleneck.

The whole Type B continuation of the authored DAG is nested inside the
at-or-below arm, so arm (a) is in scope at every Type B vertex.  This file
contains the two things needed to *use* it there and nothing else:

* `globalSurplus_eq_degreeSurplus` -- the cast bridge between the Type B
  ledger's `σ(G) = Σ_v (d_G(v) - 3) : ℚ` and the branch fact's
  `object.degreeSurplus 3 : ℕ`.  This is the object's own handshake identity,
  already proved as
  `Graph.Strategy.Official.Features.DegreeSurplusLedger.exact_edge_count_identity`.
* the consumption theorems, which take the branch residual (or the numeric
  fact it records) and close `prop:typeB-bridge-sublinear`'s asymptotic tail
  `M_B ≤ 16 σ(G) = O(√n)`.

No new surplus, token, blocker, bottleneck, branch-state carrier, or near-cubic
predicate is introduced: every hypothesis below is either an existing observable
of the object or the existing residual produced by the existing node-`[19]`
split.
-/

namespace Hypostructure.Graph.NearCubicSpine

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.TypeBOpenPorts
open Hypostructure.Graph.TypeBBridgeResidual
open Hypostructure.Graph.TypeBFanMass
open Hypostructure.Core.Strategy.Official.Features
open Hypostructure.Graph.ReceiverLoad (LoadCapacityProfile)

universe u

/-! ## The cast bridge between the two surplus spellings -/

/-- The object's handshake identity in the form the Type B ledger uses:
`Σ_v (d_G(v) - 3) = 2m - 3n`, with the left side rational and the right side
the natural `degreeSurplus` observable that the node-`[19]` split compares
against its table.

This is not a second surplus notion.  `globalSurplus` and `degreeSurplus` are
the two existing spellings of `σ(G)`; the equality is
`DegreeSurplusLedger.exact_edge_count_identity` cast into `ℚ`. -/
theorem sum_degree_sub_baseline_eq_degreeSurplus (object : FiniteObject.{u})
    (baselineDegree : Nat)
    (minDegree : ∀ v : object.Vertex, baselineDegree ≤ object.degree v) :
    ∑ v ∈ object.vertexFinset,
        ((object.degree v : ℚ) - (baselineDegree : ℚ))
      = ((object.degreeSurplus baselineDegree : Nat) : ℚ) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  let baseline :
      Strategy.Official.Features.DegreeSurplusLedger.MinimumDegreeBaseline
        object :=
    { degree := baselineDegree, lower := minDegree }
  have handshake :
      (Strategy.Official.Features.DegreeSurplusLedger.derive object
          baseline).total + baselineDegree * object.vertexCount =
        2 * object.edgeCount :=
    Strategy.Official.Features.DegreeSurplusLedger.exact_edge_count_identity
      object baseline
  have surplusEq :
      object.degreeSurplus baselineDegree =
        (Strategy.Official.Features.DegreeSurplusLedger.derive object
          baseline).total := by
    unfold FiniteObject.degreeSurplus
    omega
  have totalEq :
      (Strategy.Official.Features.DegreeSurplusLedger.derive object
          baseline).total =
        ∑ v ∈ object.vertexFinset, (object.degree v - baselineDegree) := by
    rw [Strategy.Official.Features.DegreeSurplusLedger.Ledger.total]
    rfl
  have pointwise : ∀ v ∈ object.vertexFinset,
      ((object.degree v - baselineDegree : Nat) : ℚ)
        = (object.degree v : ℚ) - (baselineDegree : ℚ) := by
    intro v _
    have : baselineDegree ≤ object.degree v := minDegree v
    push_cast [Nat.cast_sub this]
    ring
  calc
    (∑ v ∈ object.vertexFinset,
          ((object.degree v : ℚ) - (baselineDegree : ℚ)))
        = ∑ v ∈ object.vertexFinset,
            ((object.degree v - baselineDegree : Nat) : ℚ) :=
        (Finset.sum_congr rfl pointwise).symm
    _ = ((∑ v ∈ object.vertexFinset,
            (object.degree v - baselineDegree) : Nat) : ℚ) := by
        push_cast
        rfl
    _ = ((object.degreeSurplus baselineDegree : Nat) : ℚ) := by
        rw [surplusEq, totalEq]

/-- **The registered-baseline handshake.**  The same identity with the baseline
read off the presentation the problem registered instead of written out.  This
is the form the node-`[144]` accounting uses, where no cubic instance is in
scope. -/
theorem globalSurplusOf_eq_degreeSurplus (object : FiniteObject.{u})
    (profile : LoadCapacityProfile)
    (minDegree :
      ∀ v : object.Vertex, profile.baselineDegree ≤ object.degree v) :
    globalSurplusOf profile object
      = ((object.degreeSurplus profile.baselineDegree : Nat) : ℚ) :=
  sum_degree_sub_baseline_eq_degreeSurplus object profile.baselineDegree
    minDegree

/-- The positive-part registered-baseline handshake. -/
theorem globalSurplusPosOf_eq_degreeSurplus (object : FiniteObject.{u})
    (profile : LoadCapacityProfile)
    (minDegree :
      ∀ v : object.Vertex, profile.baselineDegree ≤ object.degree v) :
    globalSurplusPosOf profile object
      = ((object.degreeSurplus profile.baselineDegree : Nat) : ℚ) := by
  rw [globalSurplusPosOf_eq_globalSurplusOf profile minDegree,
    globalSurplusOf_eq_degreeSurplus object profile minDegree]

theorem globalSurplus_eq_degreeSurplus (object : FiniteObject.{u})
    (minDegree : ∀ v : object.Vertex, 3 ≤ object.degree v) :
    globalSurplus object = ((object.degreeSurplus 3 : Nat) : ℚ) := by
  have step := sum_degree_sub_baseline_eq_degreeSurplus object 3 minDegree
  simpa [globalSurplus] using step

/-- The positive-part spelling, on the standing branch `δ(G) ≥ 3`. -/
theorem globalSurplusPos_eq_degreeSurplus (object : FiniteObject.{u})
    (minDegree : ∀ v : object.Vertex, 3 ≤ object.degree v) :
    globalSurplusPos object = ((object.degreeSurplus 3 : Nat) : ℚ) := by
  rw [globalSurplusPos_eq_globalSurplus minDegree,
    globalSurplus_eq_degreeSurplus object minDegree]

/-! ## Consuming the branch fact: the asymptotic tail of
`prop:typeB-bridge-sublinear` -/

/-- **`prop:typeB-bridge-sublinear`, complete.**  `M_B ≤ 16 σ(G) ≤ 16 c⌈√n⌉`.

The first inequality is `TypeBBridgeResidual.typeBBridgeSublinear_globalSurplus`,
already proved as an observable of the object.  The second is the node-`[19]`
at-or-below branch fact `σ(G) ≤ table.threshold n` -- the manuscript's
`def:near-cubic-spine` -- consumed rather than assumed. -/
theorem residualMass_le_sixteen_threshold (object : FiniteObject.{u})
    (profile : LoadCapacityProfile)
    (table : ScaleDependentThreshold.Table)
    (minDegree : ∀ v : object.Vertex, 3 ≤ object.degree v)
    (nearCubic :
      object.degreeSurplus 3 ≤ table.threshold object.vertexCount)
    (normal : ∀ member ∈ bridgeResiduals object, ∀ h ∈ member.centers,
      NormalForm object h) :
    residualMass object profile
      ≤ 16 * ((table.threshold object.vertexCount : Nat) : ℚ)
        + undischargedMass object profile := by
  obtain ⟨_, _, total⟩ :=
    typeBBridgeSublinear_globalSurplus object profile minDegree normal
  have cast :
      globalSurplus object ≤ ((table.threshold object.vertexCount : Nat) : ℚ) := by
    rw [globalSurplus_eq_degreeSurplus object minDegree]
    exact_mod_cast nearCubic
  linarith

/-- **`prop:typeB-bridge-sublinear` on the charge set of node `[75]`.**
`M_B(𝒳_B) ≤ 16 σ(G) ≤ 16 c⌈√n⌉`, with the asymptotic tail supplied by the
node-`[19]` at-or-below branch instead of carried as a hypothesis. -/
theorem fanResidualMass_le_sixteen_threshold (object : FiniteObject.{u})
    (profile : LoadCapacityProfile)
    (table : ScaleDependentThreshold.Table)
    (minDegree : ∀ v : object.Vertex, 3 ≤ object.degree v)
    (nearCubic :
      object.degreeSurplus 3 ≤ table.threshold object.vertexCount)
    (normal : ∀ member ∈ fanMassResiduals object, ∀ h ∈ member.centers,
      NormalForm object h) :
    fanResidualMass object profile
      ≤ 16 * ((table.threshold object.vertexCount : Nat) : ℚ)
        + fanUndischargedMass object profile := by
  obtain ⟨_, _, total⟩ :=
    typeBFanMassSublinear_globalSurplus object profile minDegree normal
  have cast :
      globalSurplus object ≤ ((table.threshold object.vertexCount : Nat) : ℚ) := by
    rw [globalSurplus_eq_degreeSurplus object minDegree]
    exact_mod_cast nearCubic
  linarith

/-- The same bound with the fan-envelope-free cores already discharged, i.e.
the manuscript's verbatim `M_B(𝒳_B) ≤ 16 σ(G) = O(√n)`. -/
theorem fanResidualMass_le_sixteen_threshold_discharged
    (object : FiniteObject.{u})
    (profile : LoadCapacityProfile)
    (table : ScaleDependentThreshold.Table)
    (minDegree : ∀ v : object.Vertex, 3 ≤ object.degree v)
    (nearCubic :
      object.degreeSurplus 3 ≤ table.threshold object.vertexCount)
    (normal : ∀ member ∈ fanMassResiduals object, ∀ h ∈ member.centers,
      NormalForm object h)
    (discharged : ∀ member ∈ fanMassResiduals object,
      0 ≤ member.residualCoreCharge profile) :
    fanResidualMass object profile
      ≤ 16 * ((table.threshold object.vertexCount : Nat) : ℚ) := by
  have bound :=
    fanResidualMass_le_sixteen_globalSurplus object profile minDegree normal
      discharged
  have cast :
      globalSurplus object ≤ ((table.threshold object.vertexCount : Nat) : ℚ) := by
    rw [globalSurplus_eq_degreeSurplus object minDegree]
    exact_mod_cast nearCubic
  linarith

/-! ## `def:surviving-cold-branch` (vi): all but `o(n)` packed windows are
ambient-cubic

The manuscript states clause (vi) as a *branch precondition* --

> the sparse surplus branch has already supplied the spine estimate in the
> form `m = (3/2)n + o(n)` and `σ(G) = 2m − 3n = o(n)`.  On this branch,
> `|V≥4(G)| ≤ σ(G) = o(n)`.  Hence all but `o(n)` packed `P₁₃`-windows are
> ambient-cubic.

and both sentences after the estimate are derivations from it, not new
hypotheses.  They are the two theorems below.  The `o(n)` on the right is the
audited square-root table of the node-`[19]` split, never a literal constant:
the branch form at the end of this file puts `table.threshold n` there. -/

/-- The `ℕ` spelling of the handshake identity already proved above.  The
rational form is the one the Type B ledger consumes; the counting argument for
clause (vi) never leaves `ℕ`, so it consumes this one. -/
theorem sum_degree_sub_baseline_eq_degreeSurplus_nat (object : FiniteObject.{u})
    (baselineDegree : Nat)
    (minDegree : ∀ v : object.Vertex, baselineDegree ≤ object.degree v) :
    ∑ v ∈ object.vertexFinset, (object.degree v - baselineDegree)
      = object.degreeSurplus baselineDegree := by
  have rational :=
    sum_degree_sub_baseline_eq_degreeSurplus object baselineDegree minDegree
  have cast :
      ((∑ v ∈ object.vertexFinset, (object.degree v - baselineDegree) : Nat) : ℚ)
        = ∑ v ∈ object.vertexFinset,
            ((object.degree v : ℚ) - (baselineDegree : ℚ)) := by
    push_cast
    refine Finset.sum_congr rfl ?_
    intro v _
    have : baselineDegree ≤ object.degree v := minDegree v
    push_cast [Nat.cast_sub this]
    ring
  exact_mod_cast cast.trans rational

/-- **`|V≥4(G)| ≤ σ(G)`.**  The manuscript's first consequence of clause (vi),
with `4` read as `baselineDegree + 1`: every vertex strictly above the baseline
contributes at least `1` to `Σ_v (d(v) − baseline)`, and that sum *is*
`degreeSurplus baseline` on the standing branch `baseline ≤ δ(G)`. -/
theorem card_aboveBaseline_le_degreeSurplus (object : FiniteObject.{u})
    (baselineDegree : Nat)
    (minDegree : ∀ v : object.Vertex, baselineDegree ≤ object.degree v) :
    (object.vertexFinset.filter
        (fun v => baselineDegree < object.degree v)).card
      ≤ object.degreeSurplus baselineDegree := by
  classical
  calc
    (object.vertexFinset.filter
        (fun v => baselineDegree < object.degree v)).card
        = ∑ _v ∈ object.vertexFinset.filter
            (fun v => baselineDegree < object.degree v), 1 := by
          simp
    _ ≤ ∑ v ∈ object.vertexFinset.filter
            (fun v => baselineDegree < object.degree v),
          (object.degree v - baselineDegree) := by
          refine Finset.sum_le_sum ?_
          intro v member
          have := (Finset.mem_filter.mp member).2
          omega
    _ ≤ ∑ v ∈ object.vertexFinset, (object.degree v - baselineDegree) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = object.degreeSurplus baselineDegree :=
          sum_degree_sub_baseline_eq_degreeSurplus_nat object baselineDegree
            minDegree

open Classical in
/-- **The packed windows that are not ambient-cubic are at most `σ(G)` many.**

A selected window fails the ambient-cubic condition of
`InducedPathCold.AmbientCubicScheduledExteriorBranch` exactly when one of its
`order` vertices has degree different from the baseline, hence -- on the
standing branch `baseline ≤ δ(G)` -- strictly above it.  The selected windows
of a maximal packing have pairwise disjoint supports
(`InducedPathMaximalPacking.Profile.pairwiseDisjoint`), so distinct failing
windows contribute disjoint nonempty sets of strictly-above-baseline vertices,
and the count is bounded by `|V≥4(G)|`, hence by `σ(G)`. -/
theorem card_irregularSelected_le_degreeSurplus
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (baselineDegree : Nat)
    (minDegree : ∀ v : object.Vertex, baselineDegree ≤ object.degree v) :
    (profile.selected.toFinset.filter
        (fun window => ¬ ∀ position : Fin order,
          object.degree (window position) = baselineDegree)).card
      ≤ object.degreeSurplus baselineDegree := by
  classical
  set V : Finset object.Vertex :=
    object.vertexFinset.filter (fun v => baselineDegree < object.degree v)
    with hV
  set T : Finset (InducedPathMaximalPacking.Window object order) :=
    profile.selected.toFinset.filter
      (fun window => ¬ ∀ position : Fin order,
        object.degree (window position) = baselineDegree) with hT
  set g : InducedPathMaximalPacking.Window object order →
      Finset object.Vertex :=
    fun window => InducedPathMaximalPacking.support object order window ∩ V
    with hg
  have disjoint : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (g x) (g y) := by
    intro x memberX y memberY different
    have selectedX : x ∈ profile.selected :=
      List.mem_toFinset.mp (Finset.mem_filter.mp memberX).1
    have selectedY : y ∈ profile.selected :=
      List.mem_toFinset.mp (Finset.mem_filter.mp memberY).1
    have base := profile.pairwiseDisjoint x selectedX y selectedY different
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left base)
  have nonempty : ∀ w ∈ T, 1 ≤ (g w).card := by
    intro w member
    have irregular := (Finset.mem_filter.mp member).2
    obtain ⟨position, mismatch⟩ := not_forall.mp irregular
    have strict : baselineDegree < object.degree (w position) :=
      lt_of_le_of_ne (minDegree _) (Ne.symm mismatch)
    have inSupport :
        w position ∈ InducedPathMaximalPacking.support object order w := by
      simp [InducedPathMaximalPacking.support]
    have member : w position ∈ g w :=
      Finset.mem_inter.mpr ⟨inSupport,
        Finset.mem_filter.mpr ⟨object.mem_vertexFinset _, strict⟩⟩
    exact Finset.card_pos.mpr ⟨_, member⟩
  calc
    T.card = ∑ _w ∈ T, 1 := by simp
    _ ≤ ∑ w ∈ T, (g w).card := Finset.sum_le_sum nonempty
    _ = (T.biUnion g).card := (Finset.card_biUnion disjoint).symm
    _ ≤ V.card := by
        refine Finset.card_le_card ?_
        intro v member
        obtain ⟨w, _, memberW⟩ := Finset.mem_biUnion.mp member
        exact (Finset.mem_inter.mp memberW).2
    _ ≤ object.degreeSurplus baselineDegree :=
        card_aboveBaseline_le_degreeSurplus object baselineDegree minDegree

open Classical in
/-- **"All but `σ(G)` packed windows are ambient-cubic", verbatim.**  The
complementary reading of the previous theorem inside the selected packing:
the packing number is at most the number of ambient-cubic selected windows plus
`σ(G)`. -/
theorem selected_le_ambientCubic_add_degreeSurplus
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (baselineDegree : Nat)
    (minDegree : ∀ v : object.Vertex, baselineDegree ≤ object.degree v) :
    profile.selected.length
      ≤ (profile.selected.toFinset.filter
            (fun window => ∀ position : Fin order,
              object.degree (window position) = baselineDegree)).card
        + object.degreeSurplus baselineDegree := by
  classical
  have split :
      (profile.selected.toFinset.filter
          (fun window => ∀ position : Fin order,
            object.degree (window position) = baselineDegree)).card
        + (profile.selected.toFinset.filter
            (fun window => ¬ ∀ position : Fin order,
              object.degree (window position) = baselineDegree)).card
        = profile.selected.toFinset.card :=
    Finset.card_filter_add_card_filter_not _
  have card : profile.selected.toFinset.card = profile.selected.length :=
    List.toFinset_card_of_nodup profile.selected_nodup
  have bound :=
    card_irregularSelected_le_degreeSurplus profile baselineDegree minDegree
  omega

/-! ## The branch fact itself, read off the node-`[19]` residual -/

section Branch

open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy.ScaleThresholdDichotomy (Profile)

universe uPrevious uBranchState

variable {Previous : Type uPrevious}

/-- **Arm (a) of `prop:nonnear-cubic-sharp-overload-routing`, derived.**

Reading the at-or-below residual of the node-`[19]` `scaleThresholdDichotomy`
against the graph registration gives the near-cubic spine estimate for the
object carried by that residual:

`σ(G) ≤ (audited table)(n)`.

Nothing is assumed: `AtOrBelowResidual` is produced by Core's CT14 comparison,
and `AtOrBelowResidual.registeredComparisonAt` is its public projection.

The comparison is read at `current`, the query the compiler lowers the split
at (`Core/Strategy/Dag.lean`, `resolveBinary`): before a minimal-counterexample
selection that is the problem input, after one it is the selected minimal
object.  Taking `current := Query.residual` recovers the residual reading. -/
theorem nearCubicSpine_of_atOrBelow
    {Baseline : FiniteObject.{0} → Prop}
    {BranchState : FiniteObject.{0} → Type uBranchState}
    {Presentation : Type} {presentation : Presentation}
    {baselineDegree : Nat} {table : ScaleDependentThreshold.Table}
    (current : Query Previous fun _ =>
      Core.Strategy.ProblemInput
        (Graph.problemWithPresentation Baseline BranchState
          Presentation presentation))
    {previous : Previous}
    (residual :
      (Profile.ofRegistrationAt (Previous := Previous)
        (Graph.Strategy.ScaleThresholdDichotomy.degreeSurplusRegistration
          Baseline BranchState Presentation presentation baselineDegree
          table) current).AtOrBelowResidual previous) :
    (current.read previous).object.degreeSurplus baselineDegree
      ≤ table.threshold (current.read previous).object.vertexCount :=
  residual.registeredComparisonAt _ _

open Classical in
/-- **`def:surviving-cold-branch` (vi), on the incoming residual.**

Clause (vi) is not derived at the cold node: it is the node-`[19]` at-or-below
branch precondition, already supplied by the sparse surplus branch.  Read off
that residual it says `σ(G) ≤ table(n)`, and combined with the packing count
above it gives the manuscript's own conclusion --

> all but `o(n)` packed `P₁₃`-windows are ambient-cubic

-- with the audited table on the right, which is what `o(n)` abbreviates here.
No constant is written down: `table` is the registered
`ScaleDependentThreshold.Table` of the split that produced `residual`. -/
theorem selected_le_ambientCubic_add_threshold_of_atOrBelow
    {Baseline : FiniteObject.{0} → Prop}
    {BranchState : FiniteObject.{0} → Type uBranchState}
    {Presentation : Type} {presentation : Presentation}
    {baselineDegree : Nat} {table : ScaleDependentThreshold.Table}
    (current : Query Previous fun _ =>
      Core.Strategy.ProblemInput
        (Graph.problemWithPresentation Baseline BranchState
          Presentation presentation))
    {previous : Previous}
    (residual :
      (Profile.ofRegistrationAt (Previous := Previous)
        (Graph.Strategy.ScaleThresholdDichotomy.degreeSurplusRegistration
          Baseline BranchState Presentation presentation baselineDegree
          table) current).AtOrBelowResidual previous)
    {order : Nat}
    (packing : InducedPathMaximalPacking.Profile
      (current.read previous).object order)
    (minDegree : ∀ v, baselineDegree ≤
      (current.read previous).object.degree v) :
    packing.selected.length
      ≤ (packing.selected.toFinset.filter
            (fun window => ∀ position : Fin order,
              (current.read previous).object.degree
                (window position) = baselineDegree)).card
        + table.threshold (current.read previous).object.vertexCount := by
  classical
  have spine := nearCubicSpine_of_atOrBelow current residual
  have bound :=
    selected_le_ambientCubic_add_degreeSurplus packing baselineDegree minDegree
  omega

end Branch

end Hypostructure.Graph.NearCubicSpine
