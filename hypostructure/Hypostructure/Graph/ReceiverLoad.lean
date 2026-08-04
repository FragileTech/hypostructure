import Mathlib.Algebra.Order.Field.Rat
import Hypostructure.Graph.Object
import Hypostructure.Graph.RootedReturn

/-!
# Exhaustive receiver-load ledger

This is a graph semantic boundary for finite receiver-load arguments.  It
records only finite graph data: internal support degree, receiver ports, a
proof-carrying canonical routing of high-load vertices, and the resulting
load/saturation predicates.  It does not choose routes, prove application
lemmas, or perform strategy execution.

The same shape can be used by any graph proof that routes finite full-load
components to boundary receivers.  The degree baseline and overload factor
are explicit profile data; the corresponding exhaustion and well-founded
peeling machinery lives in Core.  The profile is also the presentation record
a graph problem registers with Core, so the numeric thresholds its proof
design fixes -- degree baseline, overload factor, remainder-entropy threshold
-- are declared there once and read from there wherever they are needed.
-/

namespace Hypostructure.Graph.ReceiverLoad

universe u

open Hypostructure

/-- Parameters of a finite load/capacity ledger.  No particular degree,
overload, or entropy-threshold convention is built into the Graph adapter:
every numeric proof-design choice a graph problem makes is declared here, on
the record the problem registers as its `Core.Problem.presentation`, and is
read from there at each use site instead of being written as a literal inside
a strategy registration.

The discharge rate `α = 1/loadMultiplier` is constrained on **both** sides by
the Type B fan ledger, and the two bounds are the same expression
`3 - (k+1)α` -- the credit a fan of degree `k` receives against its
closed-neighbour count -- evaluated at the two ends of the degree range the
certificate-marked fan carries:

* at the **minimum activated fan**, `k = 4` and `c = 2`, the deficit is
  `D_B = 2 - (3 - 5α) = 5α - 1`, and the Type B branch needs it positive:
  `5α > 1`, i.e. `α > 1/5` (`dischargeRate_gt`);
* at the **maximum certificate-marked degree**, `k = 8`, the credit itself
  must be nonnegative or a fan would demand more than its own `2c` incidences
  carry: `9α ≤ 3`, i.e. `α ≤ 1/3` (`dischargeRate_le`).

So the recorded window is `3 ≤ loadMultiplier ≤ 4`.  The registered
`loadMultiplier = 4` sits **exactly on the lower boundary** (`5α = 5/4 > 1`,
with `D_B = 1/4` at the minimum activated fan) and **strictly inside the
upper** one (`9α = 9/4 ≤ 3`, with credit `3/4` at `k = 8`).  Neither bound is
derivable from any residual: choosing `α` is a proof-design decision, exactly
as the manuscript's own two-sided `α > τ_win` and `τ_win < 3α/(α+3)`. -/
structure LoadCapacityProfile where
  baselineDegree : Nat
  loadMultiplier : Nat
  /-- Denominator of the per-vertex remainder-entropy threshold: the problem
  splits its remainders at `η(R) ≥ (1/remainderEntropyThresholdDenominator) ·
  log₂ n`, where `η(R) = log₂|𝒢(R)|/|R|` is the per-vertex skeleton entropy
  of `def:remainder-entropy` and `n` is the ambient order.  Clearing
  denominators turns the low-entropy side into the purely arithmetic
  `|𝒢(R)|^d < n^|R|`, which is what Core's finite-state capacity Strategy
  compares as `statePowerExponent` at manuscript node [50].

  This is a proof-design threshold, not a measurement.  Nothing about the
  object, the barrier table, or the supply ledger determines it, and it is
  not derivable from any residual: choosing it *is* choosing which remainders
  the proof calls low-entropy, so it is declared once here rather than
  restated at a decision node.

  It also carries no live law today, and that is not an omission to be fixed
  by relocating it.  The inequality that would constrain it is
  `eq:feasibility`, whose demand side is the *joint* count
  `|𝒢(R)| · safeProduct ^ packingCount ≤ flatProduct ^ packingCount ·
  ambientCapacity`.  No ledger entry states that: the finite density budget
  executes at node [24], strictly above node [50] in the compiled DAG, so its
  cap omits the `|𝒢(R)|` factor because the realized-state count does not
  exist yet; and node [50]'s own arms compare only `|𝒢(R)|^d` against
  `n^|R|`.  Neither says the product fits.  Moreover `rem:closure-robust`
  records that the window-only bound `θ ≤ θ_win` already yields
  `τ_win = 0.22817486846… < 1/4` without this sharpening at all, so the
  threshold is never load-bearing for the closure.  A documented public field
  on the presentation is therefore its honest resting place. -/
  remainderEntropyThresholdDenominator : Nat
  /-- **The Type B positive-deficit constraint on the chosen discharge rate.**
  The rate `α = 1/loadMultiplier` is not free: the Type B fan ledger needs the
  closed-neighbour deficit of an activated fan to be *positive*, and that is a
  two-sided condition on `α`, of the same species as the manuscript's
  `α > τ_win` and `τ_win < 3α/(α+3)`.

  It is recorded here at its sharp instance rather than assumed anywhere.  The
  deficit of `def:typeB-multiclosed-residual` is
  `D_B = c - (3 - (k+1)α)`, and `prop:fan-closed-port-typeB-routing`
  activates a fan with the minimum closed count `c = 2`
  (`TypeBFanClosedPorts.fanClosedPortTypeBRouting`) at the minimum high degree
  `k = 4` (`TypeBMarkedFan.Marked.highDegree`), against the cubic baseline `3`
  (`TypeBOpenPorts.NormalForm.neighbourCubic`).  There
  `D_B = 2 - 3 + 5α = 5α - 1`, so positivity is exactly `5α > 1`, i.e.
  `α > 1/5`.  The `5` is `k + 1` at that minimum degree, the same geometry
  constant as the `3` and the `4` beside it: the Type B fan geometry is written
  for the cubic case, so a constraint *about* that geometry names it.

  At the registered `loadMultiplier = 4` the constraint is exactly attained,
  `D_B = 1/4 > 0`.  It fails at `loadMultiplier = 5` (`D_B = 0`) and at
  `loadMultiplier = 0` (`5/0 = 0`, `D_B = -1`), so this single inequality also
  rules out the degenerate profile with no discharge at all. -/
  dischargeRate_gt : (1 : ℚ) < 5 / (loadMultiplier : ℚ)
  /-- **The Type B fan-credit constraint on the chosen discharge rate.**
  The credit a fan receives against its closed-neighbour count,
  `3 - (k+1)α`, must be nonnegative, or a fan would demand more than the
  half-credit its own `2c` incidences carry and
  `lem:typeB-hybrid-incidence-budget`'s clause `D_N ≤ ½ I_N` would fail.
  Read off at the largest certificate-marked degree `k = 8`
  (`TypeBMarkedFan.Marked.degree_le_eight`), against the cubic baseline `3`
  (`TypeBOpenPorts.NormalForm.neighbourCubic`): the credit there is `3 - 9α`,
  so the constraint is `9α ≤ 3`, i.e. `α ≤ 1/3`.  The `9` is `k + 1` at that
  maximum degree, the companion of the `5 = k + 1` at the minimum degree in
  `dischargeRate_gt`.

  `9` is the constant the *statement* requires, not a narrower reading:
  `typeBHybridIncidenceBudget` is stated for every certificate-marked profile,
  so the cap it must survive is `Marked.degree_le_eight`.  Relaxing to
  `5α ≤ 3` would be legitimate only if the hybrid budget were applied at
  `k = 4` alone, which it is not.

  At the registered `loadMultiplier = 4` the credit is `3/4 > 0`.  It is
  exactly attained at `loadMultiplier = 3` (credit `0`) and fails at `2`
  (credit `-3/2`).  With `dischargeRate_gt` the recorded window is
  `3 ≤ loadMultiplier ≤ 4`. -/
  dischargeRate_le : (9 : ℚ) / (loadMultiplier : ℚ) ≤ 3

namespace LoadCapacityProfile

/-- The per-vertex discharge rate `α` of the ledger.  The profile records the
overload factor `1/α` as `loadMultiplier`, so the rate itself is
`1 / loadMultiplier`; at the registered profile `loadMultiplier = 4` this is the
manuscript's `α = 1/4` of `lem:typeA-unsaturated-discharge`.

`α` is a *chosen* proof-design parameter, not a quantity measured from a graph,
which is exactly why it belongs to the public presentation record rather than to
a literal buried inside a charge computation. -/
def dischargeRate (profile : LoadCapacityProfile) : ℚ :=
  1 / (profile.loadMultiplier : ℚ)

theorem dischargeRate_nonneg (profile : LoadCapacityProfile) :
    0 ≤ profile.dischargeRate := by
  unfold dischargeRate
  exact div_nonneg zero_le_one (Nat.cast_nonneg _)

/-- The only structural fact the charge algebra needs about the chosen rate: a
vertex is discharged by at most one whole unit.  It holds for every profile,
including the degenerate `loadMultiplier = 0`, where `1 / 0 = 0`. -/
theorem dischargeRate_le_one (profile : LoadCapacityProfile) :
    profile.dischargeRate ≤ 1 := by
  unfold dischargeRate
  rcases Nat.eq_zero_or_pos profile.loadMultiplier with zero | pos
  · simp [zero]
  · have cast : (1 : ℚ) ≤ (profile.loadMultiplier : ℚ) := by exact_mod_cast pos
    rw [div_le_one (by linarith)]
    exact cast

/-- The recorded Type B constraint in the multiplied form the charge algebra
uses: `1 < 5α`.  This is `dischargeRate_gt` with the division cleared, nothing
more. -/
theorem one_lt_five_mul_dischargeRate (profile : LoadCapacityProfile) :
    1 < 5 * profile.dischargeRate := by
  have step := profile.dischargeRate_gt
  unfold dischargeRate
  rw [mul_one_div]
  exact step

/-- The rate is strictly positive: a profile satisfying the Type B constraint
discharges by a nonzero amount.  Immediate from `1 < 5α`. -/
theorem dischargeRate_pos (profile : LoadCapacityProfile) :
    0 < profile.dischargeRate := by
  have step := profile.one_lt_five_mul_dischargeRate
  linarith

/-- The recorded fan-credit constraint in the multiplied form the charge algebra
uses: `9α ≤ 3`.  This is `dischargeRate_le` with the division cleared, nothing
more. -/
theorem nine_mul_dischargeRate_le_three (profile : LoadCapacityProfile) :
    9 * profile.dischargeRate ≤ 3 := by
  have step := profile.dischargeRate_le
  unfold dischargeRate
  rw [mul_one_div]
  exact step

end LoadCapacityProfile

structure Support (object : FiniteObject.{u}) where
  core : Finset object.Vertex

namespace Support

variable {object : FiniteObject.{u}}

noncomputable def internalDegree
    (support : Support object) (vertex : object.Vertex) : Nat := by
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact (support.core.filter (fun neighbor => object.graph.Adj vertex neighbor)).card

abbrev FullVertex (support : Support object) (profile : LoadCapacityProfile) :=
  { vertex : object.Vertex // vertex ∈ support.core ∧
      support.internalDegree vertex = profile.baselineDegree }

abbrev ReceiverVertex (support : Support object) (profile : LoadCapacityProfile) :=
  { vertex : object.Vertex // vertex ∈ support.core ∧
      support.internalDegree vertex < profile.baselineDegree }

noncomputable def fullVertices (support : Support object)
    (profile : LoadCapacityProfile) :
    Finset (support.FullVertex profile) := by
  classical
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  let fullCore := support.core.filter
    (fun vertex => support.internalDegree vertex = profile.baselineDegree)
  letI : Fintype (support.FullVertex profile) :=
    Fintype.subtype fullCore (by
      intro vertex
      simp [fullCore])
  exact Finset.univ

noncomputable def receiverVertices (support : Support object)
    (profile : LoadCapacityProfile) :
    Finset (support.ReceiverVertex profile) := by
  classical
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  let receiverCore := support.core.filter
    (fun vertex => support.internalDegree vertex < profile.baselineDegree)
  letI : Fintype (support.ReceiverVertex profile) :=
    Fintype.subtype receiverCore (by
      intro vertex
      simp [receiverCore])
  exact Finset.univ

noncomputable def missingPorts (support : Support object)
    (profile : LoadCapacityProfile)
    (receiver : support.ReceiverVertex profile) : Nat :=
  profile.baselineDegree - support.internalDegree receiver.1

theorem missingPorts_eq_of_degree
    (support : Support object) (profile : LoadCapacityProfile)
    (receiver : support.ReceiverVertex profile)
    (q : Nat)
    (q_le : q ≤ profile.baselineDegree)
    (degree : support.internalDegree receiver.1 = profile.baselineDegree - q) :
    support.missingPorts profile receiver = q := by
  unfold missingPorts
  omega

end Support

/-! ## Proof-carrying receiver geometry

The following records are the graph-side data used by an exhaustive
receiver-load argument.  They deliberately do not decide which alternative
closes a proof: that interpretation belongs to the application contract and
is consumed by Core's well-founded exhaustion executor.
-/

structure CompletionPort {object : FiniteObject.{u}}
    (support : Support object) (profile : LoadCapacityProfile) where
  receiver : support.ReceiverVertex profile
  outside : object.Vertex
  adjacent : object.graph.Adj receiver.1 outside
  outside_mem : outside ∉ support.core

namespace CompletionPort

variable {object : FiniteObject.{u}} {support : Support object}
variable {profile : LoadCapacityProfile}

def edge (port : CompletionPort support profile) : object.graph.Dart :=
  ⟨(port.receiver.1, port.outside), port.adjacent⟩

end CompletionPort

structure AnchoredReturn {object : FiniteObject.{u}}
    {support : Support object} {profile : LoadCapacityProfile}
    (port : CompletionPort support profile) where
  path : object.graph.Walk port.outside port.receiver.1
  isPath : path.IsPath
  avoidsPort : port.edge.edge ∉ path.edges
  firstEntry : object.Vertex
  firstEntry_mem : firstEntry ∈ support.core
  firstEntry_receiver : support.internalDegree firstEntry < profile.baselineDegree

namespace AnchoredReturn

variable {object : FiniteObject.{u}} {support : Support object}
variable {profile : LoadCapacityProfile}

/-- Convert an anchored return avoiding its completion port into the generic
edge-rooted return certificate used by Graph's target algebra. -/
def toEdgeRootedReturn
    {port : CompletionPort support profile}
    (anchoredReturn : AnchoredReturn port) (ReturnLengthOK : Nat → Prop)
    (accepted : ReturnLengthOK anchoredReturn.path.length) :
    EdgeRootedReturn object ReturnLengthOK := by
  let dart : object.graph.Dart :=
    ⟨(port.receiver.1, port.outside), port.adjacent⟩
  have avoids : dart.edge ∉ anchoredReturn.path.edges := by
    simpa [dart, CompletionPort.edge] using anchoredReturn.avoidsPort
  let path := anchoredReturn.path.toDeleteEdge dart.edge avoids
  refine { dart := dart, path := path, isPath := ?_, length_ok := ?_ }
  · dsimp [path]
    apply anchoredReturn.isPath.toDeleteEdges
  · dsimp [path]
    rw [SimpleGraph.Walk.length_transfer]
    exact accepted

end AnchoredReturn

structure ReceiverEntryChannel {object : FiniteObject.{u}}
    {support : Support object}
    {profile : LoadCapacityProfile}
    (entry receiver : support.ReceiverVertex profile) where
  path : object.graph.Walk entry.1 receiver.1
  isPath : path.IsPath
  supported : ∀ vertex ∈ path.support, vertex ∈ support.core

structure ReceiverEntryReturn {object : FiniteObject.{u}}
    {support : Support object} {profile : LoadCapacityProfile}
    (port : CompletionPort support profile) where
  anchored : AnchoredReturn port
  entry : support.ReceiverVertex profile
  connector : object.graph.Walk port.outside entry.1
  connector_isPath : connector.IsPath
  connector_supported_only_at_end :
    ∀ vertex ∈ connector.support, vertex ∈ support.core → vertex = entry.1
  channel : ReceiverEntryChannel entry port.receiver

/-! A canonical route is supplied as data together with its semantic proof.
The finite lexicographic construction is application-owned because the
ordering of traces is part of the problem's residual ledger. -/

structure CanonicalRouting {object : FiniteObject.{u}}
    (support : Support object) (profile : LoadCapacityProfile) where
  route : support.FullVertex profile → support.ReceiverVertex profile
  /-- The route is the fixed canonical trace assignment selected by the
  application-owned finite trace order. -/
  canonical : Prop

structure VisibleLoadLedger {object : FiniteObject.{u}}
    {support : Support object} {profile : LoadCapacityProfile}
    (routing : CanonicalRouting support profile) where
  port : support.ReceiverVertex profile →
    Finset (CompletionPort support profile)
  visible : support.FullVertex profile → Prop
  visible_decidable : ∀ vertex, Decidable (visible vertex)
  visible_correct : Prop
  silent_correct : Prop

namespace VisibleLoadLedger

variable {object : FiniteObject.{u}}
variable {support : Support object}
variable {profile : LoadCapacityProfile}
variable {routing : CanonicalRouting support profile}

noncomputable def visibleLoad
    (ledger : VisibleLoadLedger routing)
  (receiver : support.ReceiverVertex profile) : Nat := by
  classical
  exact (support.fullVertices profile |>.filter (fun full =>
    routing.route full = receiver ∧ ledger.visible full)).card

noncomputable def silentLoad
    (ledger : VisibleLoadLedger routing)
  (receiver : support.ReceiverVertex profile) : Nat := by
  classical
  exact (support.fullVertices profile |>.filter (fun full =>
    routing.route full = receiver ∧ ¬ ledger.visible full)).card

end VisibleLoadLedger

structure RoutedLoad {object : FiniteObject.{u}}
    (profile : LoadCapacityProfile) (support : Support object) where
  /-- The canonical trace endpoint assigned to every full-load vertex. -/
  route : support.FullVertex profile -> support.ReceiverVertex profile

def CanonicalRouting.toRoutedLoad
    {object : FiniteObject.{u}} {support : Support object}
    {profile : LoadCapacityProfile}
    (routing : CanonicalRouting support profile) : RoutedLoad profile support where
  route := routing.route

namespace RoutedLoad

variable {object : FiniteObject.{u}}

noncomputable def load (routing : RoutedLoad (object := object) profile support)
    (receiver : support.ReceiverVertex profile) : Nat := by
  classical
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  let fullCore := support.core.filter
    (fun vertex => support.internalDegree vertex = profile.baselineDegree)
  letI : Fintype (support.FullVertex profile) :=
    Fintype.subtype fullCore (by
      intro vertex
      simp [fullCore])
  exact (support.fullVertices profile |>.filter
    (fun full => routing.route full = receiver)).card

noncomputable def saturated
    (routing : RoutedLoad (object := object) profile support)
    (receiver : support.ReceiverVertex profile) : Prop :=
  profile.loadMultiplier * support.missingPorts profile receiver ≤
    routing.load receiver

noncomputable def unsaturated
    (routing : RoutedLoad (object := object) profile support)
    (receiver : support.ReceiverVertex profile) : Prop :=
  routing.load receiver ≤
    profile.loadMultiplier * support.missingPorts profile receiver - 1

noncomputable instance saturatedDecidable
    (routing : RoutedLoad (object := object) profile support)
    (receiver : support.ReceiverVertex profile) :
    Decidable (routing.saturated receiver) := by
  classical
  unfold saturated
  infer_instance

noncomputable instance unsaturatedDecidable
    (routing : RoutedLoad (object := object) profile support)
    (receiver : support.ReceiverVertex profile) :
    Decidable (routing.unsaturated receiver) := by
  classical
  unfold unsaturated
  infer_instance

theorem saturated_or_unsaturated
    (routing : RoutedLoad (object := object) profile support)
    (receiver : support.ReceiverVertex profile) :
    routing.saturated receiver ∨ routing.unsaturated receiver := by
  by_cases hSat : routing.saturated receiver
  · exact Or.inl hSat
  · right
    unfold unsaturated
    change ¬ profile.loadMultiplier * support.missingPorts profile receiver ≤
      routing.load receiver at hSat
    omega

theorem total_load_eq_full_card
    (routing : RoutedLoad (object := object) profile support) :
    ∑ receiver ∈ support.receiverVertices profile, routing.load receiver =
      (support.fullVertices profile).card := by
  classical
  letI : DecidableEq (support.FullVertex profile) := inferInstance
  letI : DecidableEq (support.ReceiverVertex profile) := inferInstance
  have mapsTo :
      (support.fullVertices profile : Set (support.FullVertex profile)).MapsTo
        routing.route (support.receiverVertices profile :
          Set (support.ReceiverVertex profile)) := by
    intro full _member
    change routing.route full ∈ support.receiverVertices profile
    simp [Support.receiverVertices]
  have partition := Finset.card_eq_sum_card_fiberwise mapsTo
  calc
    (∑ receiver ∈ support.receiverVertices profile, routing.load receiver) =
        ∑ receiver ∈ support.receiverVertices profile,
          ((support.fullVertices profile).filter
            (fun full => routing.route full = receiver)).card := by
      apply Finset.sum_congr rfl
      intro receiver receiverMem
      rfl
    _ = (support.fullVertices profile).card := partition.symm

theorem unsaturated_threshold
    (routing : RoutedLoad (object := object) profile support)
    (receiver : support.ReceiverVertex profile) (q : Nat)
    (missing : support.missingPorts profile receiver = q)
  (notSaturated : ¬ routing.saturated receiver) :
    routing.load receiver ≤ profile.loadMultiplier * q - 1 := by
  classical
  rw [← missing]
  unfold saturated at notSaturated
  omega

/-! The first global discharge is a finite ledger inequality.  An application
can expand the profile-specific capacity expression into named degree classes;
the generic theorem keeps that arithmetic outside the adapter. -/

theorem unsaturated_capacity_bound
    (routing : RoutedLoad (object := object) profile support)
    (unsaturated : ∀ receiver : support.ReceiverVertex profile,
      routing.unsaturated receiver) :
    (support.fullVertices profile).card ≤
      ∑ receiver ∈ support.receiverVertices profile,
        (profile.loadMultiplier * support.missingPorts profile receiver - 1) := by
  have pointwise : ∀ receiver ∈ support.receiverVertices profile,
      routing.load receiver ≤
        profile.loadMultiplier * support.missingPorts profile receiver - 1 := by
    intro receiver _member
    exact unsaturated receiver
  calc
    (support.fullVertices profile).card =
        ∑ receiver ∈ support.receiverVertices profile, routing.load receiver :=
      (total_load_eq_full_card routing).symm
    _ ≤ ∑ receiver ∈ support.receiverVertices profile,
        (profile.loadMultiplier * support.missingPorts profile receiver - 1) := by
      exact Finset.sum_le_sum pointwise

end RoutedLoad

end Hypostructure.Graph.ReceiverLoad
