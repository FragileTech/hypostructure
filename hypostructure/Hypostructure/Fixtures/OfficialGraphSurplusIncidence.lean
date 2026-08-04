import Hypostructure.Graph.Strategy.Official.Features.DegreeSurplusLedger
import Hypostructure.Graph.Strategy.Official.Features.SupportIncidenceLedger
import Hypostructure.Graph.Strategy.Official.Features.PackedSupportIncidence

namespace Hypostructure.Fixtures.OfficialGraphSurplusIncidence

open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Official.Features

abbrev completeFour : FiniteObject where
  Vertex := Fin 4
  graph := ⊤
  vertices := inferInstance
  decideAdj := inferInstance

def minimumThree :
    DegreeSurplusLedger.MinimumDegreeBaseline completeFour where
  degree := 3
  lower := by
    intro vertex
    native_decide +revert

def minimumTwo :
    DegreeSurplusLedger.MinimumDegreeBaseline completeFour where
  degree := 2
  lower := by
    intro vertex
    native_decide +revert

example :
    (DegreeSurplusLedger.derive completeFour minimumThree).total = 0 := by
  native_decide

example :
    (DegreeSurplusLedger.derive completeFour minimumTwo).total = 4 := by
  native_decide

example :
    (DegreeSurplusLedger.derive completeFour minimumTwo).total +
        minimumTwo.degree * completeFour.vertexCount =
      2 * completeFour.edgeCount :=
  DegreeSurplusLedger.exact_edge_count_identity completeFour minimumTwo

def pairSupport : Finset completeFour.Vertex := {0, 1}

example :
    (SupportIncidenceLedger.derive completeFour pairSupport).selected.length = 2 := by
  native_decide

example :
    (SupportIncidenceLedger.derive completeFour pairSupport).remainder.length = 2 := by
  native_decide

example :
    (SupportIncidenceLedger.derive completeFour pairSupport).internalIncidences = 2 := by
  native_decide

example :
    (SupportIncidenceLedger.derive completeFour pairSupport).boundaryIncidences = 4 := by
  native_decide

example :
    (SupportIncidenceLedger.derive completeFour pairSupport).internalIncidences +
        (SupportIncidenceLedger.derive completeFour pairSupport).boundaryIncidences =
      ((SupportIncidenceLedger.derive completeFour pairSupport).selected.map
        completeFour.degree).sum :=
  SupportIncidenceLedger.degree_sum_partition completeFour pairSupport

#print axioms DegreeSurplusLedger.exact_edge_count_identity
#print axioms DegreeSurplusLedger.total_eq_edge_mass_sub_baseline
#print axioms SupportIncidenceLedger.degree_sum_partition
#print axioms PackedSupportIncidence.exact_support_incidence_identity
#print axioms PackedSupportIncidence.exact_window_pressure_identity

end Hypostructure.Fixtures.OfficialGraphSurplusIncidence
