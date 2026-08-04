import Hypostructure.Graph.Strategy.Official.Features.PackedWindowTokenLedger

/-!
Focused polymorphic fixture for exact packed-window incidence and token
supplies.  It contains no application constants or authored outcomes.
-/

namespace Hypostructure.Fixtures.OfficialPackedWindowTokenLedger

open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Official.Features

universe u

variable (object : FiniteObject.{u}) [DecidableEq object.Vertex]
    (order : Nat)
    (baseline : DegreeSurplusLedger.MinimumDegreeBaseline object)

local instance : FinEnum object.Vertex := object.vertices

noncomputable def profile :=
  InducedPathMaximalPacking.maximalProfile object order

example :
    (PackedSupportIncidence.derive object order
        (profile object order) baseline).incidence.internalIncidences =
      (PackedWindowTokenLedger.pathIncidences object order
        (profile object order)).card +
      (PackedWindowTokenLedger.crossWindowIncidences object order
        (profile object order)).card :=
  PackedWindowTokenLedger.internal_card_eq_path_add_cross
    object order (profile object order) baseline

example :
    baseline.degree *
          (PackedSupportIncidence.derive object order
            (profile object order) baseline).incidence.selected.length +
        (PackedSupportIncidence.derive object order
          (profile object order) baseline).selectedSurplus =
      (PackedWindowTokenLedger.pathIncidences object order
        (profile object order)).card +
      (PackedWindowTokenLedger.crossWindowIncidences object order
        (profile object order)).card +
      (PackedWindowTokenLedger.boundaryIncidences object order
        (profile object order)).card :=
  PackedWindowTokenLedger.exact_degree_surplus_split
    object order (profile object order) baseline

example :
    Fintype.card (PackedWindowTokenLedger.Token object order
      (profile object order) baseline) =
      (PackedWindowTokenLedger.pathIncidences object order
        (profile object order)).card +
      (PackedWindowTokenLedger.crossWindowIncidences object order
        (profile object order)).card +
      (PackedWindowTokenLedger.boundaryIncidences object order
        (profile object order)).card +
      (PackedSupport.selected object order (profile object order)).card +
      (object.vertexCount -
        (PackedSupport.selected object order (profile object order)).card) +
      (DegreeSurplusLedger.derive object baseline).total :=
  PackedWindowTokenLedger.total_token_supply
    object order (profile object order) baseline

#print axioms PackedWindowTokenLedger.internal_card_eq_path_add_cross
#print axioms PackedWindowTokenLedger.boundary_count_exact
#print axioms PackedWindowTokenLedger.exact_degree_surplus_split
#print axioms PackedWindowTokenLedger.total_token_supply

end Hypostructure.Fixtures.OfficialPackedWindowTokenLedger
