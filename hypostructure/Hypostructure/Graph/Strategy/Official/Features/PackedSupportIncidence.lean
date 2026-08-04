/-!
DEPRECATED: migrated to canonical CT composition strategy
(Producer/view: CT14).
This detached feature executor is retained only as a parity oracle until
its CT-ledger equivalence theorem is kernel-checked.  It must not be
registered or executed by the framework.
-/
import Hypostructure.Graph.Strategy.Official.Features.DegreeSurplusLedger
import Hypostructure.Graph.Strategy.Official.Features.PackedSupport
import Hypostructure.Graph.Strategy.Official.Features.SupportIncidenceLedger

/-!
# Packed-support incidence accounting

This is the Graph specialization of the generic support/complement incidence
ledger to a framework-selected induced-path packing.  The path order and
minimum-degree baseline remain parameters.
-/

namespace Hypostructure.Graph.Strategy.Official.Features.PackedSupportIncidence

open Hypostructure.Graph

universe u

structure Ledger (object : FiniteObject.{u}) [DecidableEq object.Vertex]
    (order : Nat)
    (profile : InducedPathMaximalPacking.Profile object order)
    (baseline : DegreeSurplusLedger.MinimumDegreeBaseline object) where
  support : Finset object.Vertex
  support_eq : support = PackedSupport.selected object order profile
  incidence : SupportIncidenceLedger.Ledger object support
  selectedSurplus : Nat
  selectedSurplus_eq :
    selectedSurplus =
      (incidence.selected.map fun vertex =>
        object.degree vertex - baseline.degree).sum

def derive (object : FiniteObject.{u}) [DecidableEq object.Vertex]
    (order : Nat)
    (profile : InducedPathMaximalPacking.Profile object order)
    (baseline : DegreeSurplusLedger.MinimumDegreeBaseline object) :
    Ledger object order profile baseline := by
  let support := PackedSupport.selected object order profile
  let incidence := SupportIncidenceLedger.derive object support
  exact
    { support := support
      support_eq := rfl
      incidence := incidence
      selectedSurplus :=
        (incidence.selected.map fun vertex =>
          object.degree vertex - baseline.degree).sum
      selectedSurplus_eq := rfl }

/-- The selected and remainder schedules are an exact partition of the
ambient vertex schedule. -/
theorem exact_vertex_split (object : FiniteObject.{u})
    [DecidableEq object.Vertex] (order : Nat)
    (profile : InducedPathMaximalPacking.Profile object order)
    (baseline : DegreeSurplusLedger.MinimumDegreeBaseline object) :
    (derive object order profile baseline).incidence.selected.length +
        (derive object order profile baseline).incidence.remainder.length =
      object.vertexCount :=
  SupportIncidenceLedger.selected_remainder_partition object
    (derive object order profile baseline).support

private theorem selected_degree_mass
    (object : FiniteObject.{u}) [DecidableEq object.Vertex]
    (order : Nat)
    (profile : InducedPathMaximalPacking.Profile object order)
    (baseline : DegreeSurplusLedger.MinimumDegreeBaseline object) :
    baseline.degree *
        (derive object order profile baseline).incidence.selected.length +
      (derive object order profile baseline).selectedSurplus =
      ((derive object order profile baseline).incidence.selected.map
        object.degree).sum := by
  let selected :=
    (derive object order profile baseline).incidence.selected
  change baseline.degree * selected.length +
      (selected.map fun vertex =>
        object.degree vertex - baseline.degree).sum =
      (selected.map object.degree).sum
  induction selected with
  | nil => simp
  | cons vertex tail ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have lower := baseline.lower vertex
      rw [Nat.mul_succ]
      omega

/-- Exact packed-support degree identity.  It is the domain-generic form of
window/remainder pressure before identifying the internal baseline edges of a
particular packed shape. -/
theorem exact_support_incidence_identity
    (object : FiniteObject.{u}) [DecidableEq object.Vertex]
    (order : Nat)
    (profile : InducedPathMaximalPacking.Profile object order)
    (baseline : DegreeSurplusLedger.MinimumDegreeBaseline object) :
    (derive object order profile baseline).incidence.boundaryIncidences +
        (derive object order profile baseline).incidence.internalIncidences =
      baseline.degree *
          (derive object order profile baseline).incidence.selected.length +
        (derive object order profile baseline).selectedSurplus := by
  have partition :
      (derive object order profile baseline).incidence.internalIncidences +
          (derive object order profile baseline).incidence.boundaryIncidences =
        ((derive object order profile baseline).incidence.selected.map
          object.degree).sum := by
    simpa [derive] using
      (SupportIncidenceLedger.degree_sum_partition object
        (PackedSupport.selected object order profile))
  have mass := selected_degree_mass object order profile baseline
  omega

/-- Signed internal-incidence excess over the path incidences forced by the
selected packing.  It is computed from the graph and packing, so no aggregate
or numerical witness is supplied by a caller. -/
def internalIncidenceExcess
    {object : FiniteObject.{u}} [DecidableEq object.Vertex]
    {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    {baseline : DegreeSurplusLedger.MinimumDegreeBaseline object}
    (ledger : Ledger object order profile baseline) : Int :=
  (ledger.incidence.internalIncidences : Int) -
    ((2 * (order - 1) * profile.selected.length : Nat) : Int)

/-- Exact packed-window pressure identity.  Every term is derived from the
literal graph, selected packing, and degree baseline.  A later semantic lemma
may identify `internalIncidenceExcess` with twice a cross-piece edge count;
that identification is not assumed here. -/
theorem exact_window_pressure_identity
    (object : FiniteObject.{u}) [DecidableEq object.Vertex]
    (order : Nat)
    (profile : InducedPathMaximalPacking.Profile object order)
    (baseline : DegreeSurplusLedger.MinimumDegreeBaseline object) :
    ((derive object order profile baseline).incidence.boundaryIncidences : Int) +
        internalIncidenceExcess (derive object order profile baseline) =
      ((baseline.degree *
          (derive object order profile baseline).incidence.selected.length :
        Nat) : Int) +
        ((derive object order profile baseline).selectedSurplus : Int) -
        ((2 * (order - 1) * profile.selected.length : Nat) : Int) := by
  unfold internalIncidenceExcess
  have identity :=
    exact_support_incidence_identity object order profile baseline
  have identityInt :
      ((derive object order profile baseline).incidence.boundaryIncidences : Int) +
          ((derive object order profile baseline).incidence.internalIncidences : Int) =
        ((baseline.degree *
            (derive object order profile baseline).incidence.selected.length :
          Nat) : Int) +
          ((derive object order profile baseline).selectedSurplus : Int) := by
    exact_mod_cast identity
  omega

end Hypostructure.Graph.Strategy.Official.Features.PackedSupportIncidence
