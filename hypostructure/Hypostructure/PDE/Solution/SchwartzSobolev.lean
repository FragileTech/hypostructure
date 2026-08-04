import Hypostructure.PDE.Solution.ParabolicRegularity

/-!
# A Schwartz function sits at every Sobolev grade

The one fact still missing between "the problem's data is smooth" and "the
framework's bootstrap can consume it".

`SmoothOn` asks for *every* real grade.  Mathlib's `MemSobolev` API produces
only grade zero (`memSobolev_zero_iff`, from an `L²` representative) and moves
*downwards* (`MemSobolev.mono`); it has no lemma putting anything at a positive
grade.  The framework does: `ParabolicRegularity.memSobolev_add_one_of_heat`
raises a grade by one whenever the state *and its heat image* sit at the current
one.  For a Schwartz function both are again Schwartz, so the induction closes
on itself.

The two inputs are mathlib's:

* `lineDerivOp_toTemperedDistributionCLM_eq` — differentiating the tempered
  distribution of a Schwartz function is the tempered distribution of its
  derivative, so the heat operator passes through the embedding;
* `memSobolev_zero_iff` — grade zero from an `L²` representative, and a Schwartz
  function has one.

Nothing here is local or global: it is a statement about one function on the
whole space, used only to certify the *data* of a problem.  No equation,
residual, window or ledger appears.
-/

namespace Hypostructure.PDE.Solution.SchwartzSobolev

open MeasureTheory TemperedDistribution
open Hypostructure.PDE.Solution.InteriorRegularity
open Hypostructure.PDE.Solution.ParabolicRegularity
open scoped SchwartzMap ENNReal Real LineDeriv ContDiff

universe uPoint uValue uIndex

variable {Point : Type uPoint} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [FiniteDimensional ℝ Point] [MeasurableSpace Point] [BorelSpace Point]
  [SecondCountableTopology Point]
  {Value : Type uValue} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  [CompleteSpace Value]
  {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- The tempered distribution of a Schwartz function. -/
noncomputable abbrev place (test : 𝓢(Point, Value)) : 𝓢'(Point, Value) :=
  SchwartzMap.toTemperedDistributionCLM Point Value (volume : Measure Point) test

/-- The heat operator on Schwartz functions: the same formula the tempered heat
operator uses, one level down. -/
noncomputable def schwartzHeat (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (test : 𝓢(Point, Value)) : 𝓢(Point, Value) :=
  ∂_{basis timeIndex} test -
    ∑ index ∈ Finset.univ.erase timeIndex,
      ∂_{basis index} (∂_{basis index} test)

/-- **The heat operator passes through the embedding.**  Both sides are the same
formula; the only content is mathlib's
`lineDerivOp_toTemperedDistributionCLM_eq`, applied once per derivative. -/
theorem place_schwartzHeat (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (test : 𝓢(Point, Value)) :
    place (schwartzHeat basis timeIndex test) =
      heatOperator basis timeIndex (place test) := by
  simp only [schwartzHeat, heatOperator, spatialLaplacian, place, map_sub, map_sum,
    TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq]

/-- A Schwartz function is square integrable, so its state sits at grade zero. -/
theorem memSobolev_zero_place (test : 𝓢(Point, Value)) :
    MemSobolev 0 2 (place test) :=
  memSobolev_zero_iff.mpr
    ⟨test.toLp 2 (volume : Measure Point), (MeasureTheory.Lp.toTemperedDistribution_toLp_eq test).symm⟩

/-- **Every natural grade**, by the framework's own heat gain.

The induction is on the grade, not on the function: at each step the state and
its heat image are both Schwartz, `place_schwartzHeat` identifies the heat image
of the state with the state of the heat image, and
`memSobolev_add_one_of_heat` raises the grade by one.  This is the only route to
a positive grade in the whole development --- mathlib's `MemSobolev` API moves
only downwards. -/
theorem memSobolev_natCast_place (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) :
    ∀ (order : ℕ) (test : 𝓢(Point, Value)), MemSobolev (order : ℝ) 2 (place test) := by
  intro order
  induction order with
  | zero => intro test; simpa using memSobolev_zero_place test
  | succ previous inductive_hypothesis =>
    intro test
    have gained :=
      memSobolev_add_one_of_heat basis timeIndex (inductive_hypothesis test)
        (by
          rw [← place_schwartzHeat basis timeIndex test]
          exact inductive_hypothesis (schwartzHeat basis timeIndex test))
    simpa [Nat.cast_succ] using gained

/-- **A Schwartz function sits at every real grade.**  Any real grade is below
some natural one, and `MemSobolev.mono` walks down. -/
theorem memSobolev_place (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (grade : ℝ) (test : 𝓢(Point, Value)) :
    MemSobolev grade 2 (place test) := by
  obtain ⟨order, bound⟩ := exists_nat_ge grade
  exact MemSobolev.mono bound (memSobolev_natCast_place basis timeIndex order test)

/-- **A state whose every localization is Schwartz is smooth on the region.**

`SmoothOn` reads the state only through bumps supported in the region, so this
hypothesis is exactly as local as the conclusion: nothing is assumed about the
state anywhere else.  This is the form in which smooth *data* enters the
bootstrap --- cutting a smooth function off with a bump leaves a smooth
compactly supported function, which is Schwartz. -/
theorem smoothOn_of_localize_schwartz (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) {region : Set Point} {state : 𝓢'(Point, Value)}
    (localized : ∀ bump : Bump Point, tsupport bump.weight ⊆ region →
      ∃ test : 𝓢(Point, Value), localize bump state = place test) :
    SmoothOn region state := by
  intro grade bump supported
  obtain ⟨test, represents⟩ := localized bump supported
  rw [represents]
  exact memSobolev_place basis timeIndex grade test

/-- Cutting the state of a Schwartz function off with a bump leaves the state of
a Schwartz function: the bump has temperate growth, and the Schwartz space is
closed under multiplication by such a factor. -/
theorem localize_place (bump : Bump Point) (test : 𝓢(Point, Value)) :
    localize bump (place test) =
      place (SchwartzMap.smulLeftCLM Value bump.weight test) := by
  ext probe
  simp only [localize_eq, TemperedDistribution.smulLeftCLM_apply_apply,
    SchwartzMap.toTemperedDistributionCLM_apply_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [SchwartzMap.smulLeftCLM_apply_apply bump.hasTemperateGrowth,
    smul_smul, mul_comm, smul_eq_mul]

/-- **The state of a Schwartz function is smooth on every region.** -/
theorem smoothOn_place (basis : OrthonormalBasis Index ℝ Point) (timeIndex : Index)
    (region : Set Point) (test : 𝓢(Point, Value)) :
    SmoothOn region (place test) :=
  smoothOn_of_localize_schwartz basis timeIndex
    fun bump _ => ⟨_, localize_place bump test⟩

/-- **Smooth compactly supported data is smooth on every region.**  This is the
form the baseline's `sourceSmooth` reaches the bootstrap in: a smooth function
cut off by the window's bump is compactly supported, hence Schwartz. -/
theorem smoothOn_place_of_hasCompactSupport (basis : OrthonormalBasis Index ℝ Point)
    (timeIndex : Index) (region : Set Point) {weight : Point → Value}
    (compact : HasCompactSupport weight) (smooth : ContDiff ℝ ∞ weight) :
    SmoothOn region (place (compact.toSchwartzMap smooth)) :=
  smoothOn_place basis timeIndex region _

end Hypostructure.PDE.Solution.SchwartzSobolev
