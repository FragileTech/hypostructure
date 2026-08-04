import Hypostructure.Core.Strategy.Data
import Hypostructure.Core.FiniteEntropy

/-!
# Reusable entropy-cap closure

`lem:p13-window-package` / `lem:independent-target-entropy`'s combined
punch line -- "assuming this many independently-testable states are
realized is impossible, because there are not enough ambient objects to
hold them" -- is the same closing pattern regardless of whether the ambient
objects are Graph problem's labelled skeletons on `n` vertices or a PDE
problem's finite discretizations. This packages that pattern once: a
problem supplies its own finite ambient class, canonical state map, and
imported numeric rate-floor certificate (its own `c_{13}`-style constant,
computed however the domain computes it), and this module derives the
"high entropy is impossible" contradiction automatically via
`Core.FiniteEntropy.two_pow_mul_le_card_ambient_of_rateFloor` -- no
per-problem re-derivation of the pigeonhole/rate-floor chain. -/

namespace Hypostructure.Core.Strategy

universe uAmbient uBranch uData uAmb uState

open Hypostructure.Core

/-- One registered entropy-cap closure family, generic in the problem `P`
and target `T`: everything past the finite ambient carrier and the
domain's own imported numeric certificate is handled automatically. -/
structure EntropyCapData
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P) where
  /-- The finite ambient class at this input (e.g. `Graph.LabelledOn n` for
  the graph carrying `n = input.object.vertexCount`, or a PDE's finite
  discretization class). -/
  Ambient' : ProblemInput P -> Type uAmb
  ambientFinite : forall input, Finite (Ambient' input)
  /-- The canonical state map whose realized-state count is being bounded. -/
  State : ProblemInput P -> Type uState
  stateOf : forall input, Ambient' input -> State input
  /-- The imported numeric rate-floor certificate: `2 ^ k * flat < safe`,
  e.g. EG's `2 ^ 118 * flatProduct < safeProduct` from its own finite
  curvature enumeration. One bundled import, not five scattered fields --
  domain-supplied data, not derived here. -/
  rateFloor : Core.FiniteEntropy.RateFloorCertificate
  /-- How many disjoint independent windows are combined at this input
  (e.g. the maximal induced-`P_13`-packing cardinality for EG). -/
  windowCount : ProblemInput P -> Nat
  /-- The "too much entropy" branch condition this closure discharges. -/
  HighEntropy : ProblemInput P -> Prop
  /-- Domain content: under `HighEntropy`, the combined per-window family
  really does realize the claimed state count. This is the one piece no
  generic machinery can supply -- it is the domain's own construction of
  `windowCount input` independent testers (via
  `Core.FiniteEntropy.injective_pi_of_forall_injective` composing the
  domain's own per-window classifications), not something derivable from
  `Ambient` alone. -/
  realizes : forall input, HighEntropy input ->
    rateFloor.safe ^ (windowCount input) ≤
      rateFloor.flat ^ (windowCount input) *
        Nat.card (Set.range (stateOf input))
  /-- Domain content: under `HighEntropy`, the claimed state count exceeds
  what the finite ambient class can actually hold -- the concrete
  cardinality fact (e.g. `Nat.card (Graph.LabelledOn n) = 2 ^ (n.choose 2)`
  compared against `windowCount input`) that makes the branch genuinely
  impossible. -/
  impossible : forall input, HighEntropy input ->
    Nat.card (Ambient' input) < 2 ^ (rateFloor.k * windowCount input)
  metadata : Documentation := {}

/-- The automatic contradiction: `HighEntropy` can never hold, fully derived
from the registered data via the generic pigeonhole/rate-floor chain. Zero
new mathematics beyond `realizes`/`impossible`, which are the only fields a
problem must supply. -/
theorem EntropyCapData.false_of_highEntropy
    (data : EntropyCapData.{uAmbient, uBranch, uAmb, uState} P T)
    (input : ProblemInput P) (high : data.HighEntropy input) : False := by
  haveI := data.ambientFinite input
  have hbound := Core.FiniteEntropy.two_pow_mul_le_card_ambient_of_rateFloor
    (data.stateOf input) data.rateFloor.k data.rateFloor.flat data.rateFloor.safe
    (data.windowCount input) data.rateFloor.flatPos data.rateFloor.rate
    (data.realizes input high)
  exact absurd hbound (Nat.not_le.mpr (data.impossible input high))

/-- The `HighEntropy` branch closes to any target vacuously: it can never
occur. This is exactly the `closeLeft` proof an `S07`-style dichotomy needs,
supplied automatically once `realizes`/`impossible` are proved. -/
theorem EntropyCapData.closeHighEntropy
    (data : EntropyCapData.{uAmbient, uBranch, uAmb, uState} P T)
    (input : ProblemInput P) (high : data.HighEntropy input) :
    T.Predicate input.object :=
  (data.false_of_highEntropy input high).elim

end Hypostructure.Core.Strategy
