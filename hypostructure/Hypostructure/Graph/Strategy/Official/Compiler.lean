import Hypostructure.Graph.Strategy.Official.SealedDag

/-!
# Graph sealed-DAG compiler boundary

Graph no longer constructs an execution kernel.  Compilation is performed
privately by Core's `ofDag%` frontend; this module provides read-only
projections from the resulting sealed declaration.
-/

namespace Hypostructure.Graph.Strategy.Official.Compiler

open Hypostructure

universe uAmbient uBranch uData

abbrev GraphDeclaration :=
  SealedDag.Declaration.{uAmbient, uBranch, uData}

noncomputable def statement
    (declaration : GraphDeclaration.{uAmbient, uBranch, uData}) :=
  SealedDag.statement declaration

noncomputable def path
    (declaration : GraphDeclaration.{uAmbient, uBranch, uData}) :=
  SealedDag.path declaration

noncomputable def traceJson
    (declaration : GraphDeclaration.{uAmbient, uBranch, uData}) :=
  SealedDag.traceJson declaration

end Hypostructure.Graph.Strategy.Official.Compiler
