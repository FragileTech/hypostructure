import Hypostructure.Fixtures.RegisteredCanonicalAccountingCompositions

/-!
# Canonical accounting-composition reordering fixture

This independent blueprint places the same four registered scalar strategies
in a different order.  Its single root and successful elaboration witness
that Core's DAG registry imposes no hidden strategy order.
-/

namespace Hypostructure.Fixtures.RegisteredCanonicalAccountingReordering

open Hypostructure.Core.Strategy.Dag
open Hypostructure.Fixtures.RegisteredCanonicalAccountingCompositions

noncomputable def reorderedProgram : Program definition.data :=
  Program.ofBlueprint (
    Blueprint.root
      |>.finiteBottleneckClassification
      |>.canonicalCapacityTokenAccounting
      |>.canonicalPairResponseAccounting
      |>.coupledHomogeneousFibrePressure)

end Hypostructure.Fixtures.RegisteredCanonicalAccountingReordering
