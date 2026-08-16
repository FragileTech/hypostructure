import Hypostructure.Core.Prelude
import Hypostructure.Core.Problem
import Hypostructure.Core.Progress
import Hypostructure.Core.Context
import Hypostructure.Core.SemanticEquivalence
import Hypostructure.Core.Provision
import Hypostructure.Core.Coordinate.System
import Hypostructure.Core.Coordinate.Path
import Hypostructure.Core.Coordinate.Transport
import Hypostructure.Core.Assembly.Locality
import Hypostructure.Core.Assembly.AtomContext
import Hypostructure.Core.Response.System
import Hypostructure.Core.Response.FiniteTable
import Hypostructure.Core.Budget.Resource
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Finite.Partition
import Hypostructure.Core.Finite.ConnectedPartition
import Hypostructure.Core.Finite.MaximalSelection
import Hypostructure.Core.Finite.EssentialCarrier
import Hypostructure.Core.Finite.CertifiedTableAggregation
import Hypostructure.Core.Finite.CertifiedTableBounds
import Hypostructure.Core.FiniteTriangle
import Hypostructure.Core.FiniteBitRelationBarrier
import Hypostructure.Core.CeilSqrt
import Hypostructure.Core.DyadicLength
import Hypostructure.Core.ArithmeticTransport
import Hypostructure.Core.FiniteEntropy
import Hypostructure.Core.OneThreeRepair
import Hypostructure.Core.AffineBalance
import Hypostructure.Core.Residual.ExactLedger
import Hypostructure.Core.Execution
import Hypostructure.Core.Routing
import Hypostructure.Core.Closure
import Hypostructure.Core.Strategy.ExactExecution
import Hypostructure.Core.Strategy.ProblemResidual
import Hypostructure.Core.Strategy.FactOnlyStrategy
import Hypostructure.Core.Strategy.AtomicDecision
import Hypostructure.Core.Strategy.MinimalCounterexampleScope
import Hypostructure.Core.Strategy.ClosingProgram
import Hypostructure.Core.Strategy.StrategyProgram
import Hypostructure.Core.Strategy.Dag
import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Strategy.SpineRows
import Hypostructure.Graph.Strategy.TypeAExitRun
import Hypostructure.Graph.Strategy.SurplusRun
import Hypostructure.Graph.Strategy.SpineContinuationRun
import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.ColdCorridor
import Hypostructure.Graph.ColdFirstFailure
import Hypostructure.Fixtures.ColdCorridorSignature
import Hypostructure.Fixtures.ColdCorridorLedger
import Hypostructure.Fixtures.ColdCorridorConstruction
import Hypostructure.Fixtures.ColdCorridorShortSelfReturn
import Hypostructure.Fixtures.TypeAReceiverNode
import Hypostructure.Fixtures.TypeAExitOne
import Hypostructure.Fixtures.TypeAExitTwo
import Hypostructure.Fixtures.TypeAExitThree
import Hypostructure.Fixtures.TypeBFanWindowNode
import Hypostructure.Fixtures.SurplusRun
import Hypostructure.Fixtures.ExitFourFamily
import Hypostructure.Core.Strategy.FactManifest
import Hypostructure.Fixtures.ExactLedger
import Hypostructure.Fixtures.ExactExecution
import Hypostructure.Fixtures.MinimalCounterexampleScope
import Hypostructure.Fixtures.DerivedFactPublication
import Hypostructure.Fixtures.AutomaticLedgerClosure
import Hypostructure.Fixtures.ExactLedgerEmptinessClosure
import Hypostructure.Fixtures.LedgerAutorouting
import Hypostructure.Fixtures.BranchScopedExactLedger
import Hypostructure.Fixtures.ClosingProgram
import Hypostructure.Fixtures.StrategyProgram
import Hypostructure.Fixtures.Dag
import Hypostructure.Fixtures.ExactLedgerOpacity
import Hypostructure.Fixtures.ExactLedgerDuplicateFact
import Hypostructure.Fixtures.ExactLedgerMissingFact
import Hypostructure.Fixtures.ExactExecutionMissingRequirement
import Hypostructure.Fixtures.ExactExecutionDroppedFact
import Hypostructure.Routes.Registry
import Hypostructure.Graph.Object
import Hypostructure.Graph.Problem
import Hypostructure.Graph.Finite
import Hypostructure.Graph.Contraction
import Hypostructure.Graph.SurplusPort
import Hypostructure.Graph.ExcessPortFamily
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.BaselineSpineDemand
import Hypostructure.Graph.CanonicalFibreLedger
import Hypostructure.Graph.SparsePairLedger
import Hypostructure.Graph.PrimitiveCarrier
import Hypostructure.Graph.FiniteEdgeBudget
import Hypostructure.Graph.SupportComponents
import Hypostructure.Graph.OneThreeRepair
import Hypostructure.Graph.Isomorphism
import Hypostructure.Graph.Induced
import Hypostructure.Graph.InducedPath
import Hypostructure.Graph.InducedPathMaximalPacking
import Hypostructure.Graph.PackedWindowRealization
import Hypostructure.Graph.Deletion
import Hypostructure.Graph.Progress
import Hypostructure.Graph.Minimality
import Hypostructure.Graph.DeletionCriticality
import Hypostructure.Graph.Target
import Hypostructure.Graph.MinimumDegreeCycleTarget
import Hypostructure.Graph.Coordinate
import Hypostructure.Graph.Boundary
import Hypostructure.Graph.Gluing
import Hypostructure.Graph.BoundariedAtom
import Hypostructure.Graph.BoundaryOverlap
import Hypostructure.Graph.Response
import Hypostructure.Graph.TargetClosure
import Hypostructure.Graph.RootedReturn
import Hypostructure.Graph.SkeletonBudget
import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.MatchingStar
import Hypostructure.Graph.HomogeneousTokenCap
import Hypostructure.Graph.TokenLoadClosure
import Hypostructure.Graph.CapacityTokenLedger
import Hypostructure.Graph.DeclaredCoordinateSignature
import Hypostructure.Graph.SameTokenRoutingGerms
import Hypostructure.Graph.SparseUpperEnvelope
import Hypostructure.Graph.PortResponseSupport
import Hypostructure.Graph.SparseEntropySandwich
import Hypostructure.Graph.SparsePairResponse
import Hypostructure.Graph.SurplusBlockers
import Hypostructure.Graph.DeclaredRankQuotient
import Hypostructure.Graph.CanonicalSupportSelection
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows
import Hypostructure.Fixtures.HomogeneousTokenBottleneck
import Hypostructure.Graph.ReceiverLoad
import Hypostructure.Graph.ReceiverRouting
import Hypostructure.Graph.VisibleReceiverEntry
import Hypostructure.Graph.CommonPortReturnCycle
import Hypostructure.Graph.DecoratedHandoffEnvelope
import Hypostructure.Graph.SameTokenBottleneckRouting
import Hypostructure.Graph.AnchoredReturnCompletion
import Hypostructure.Graph.WindowCurvatureAlgebra
import Hypostructure.Graph.WindowCurvatureEnumeration
import Hypostructure.Graph.WindowCurvatureCode
import Hypostructure.Graph.WindowLabelCollision
import Hypostructure.Graph.SurplusClasswiseOverload

-- Manuscript Part VIII--IX, Figures 8 and 9: the Type A receiver chain and the
-- route-8 carrier closure.  These are reached transitively by the Erdos-Gyarfas
-- application, but naming them here is what keeps a bare `lake build` covering
-- them -- `TypeARoute8Stages` in particular is imported by nothing else.
import Hypostructure.Graph.CutParity
import Hypostructure.Graph.ExitFourPeeling
import Hypostructure.Graph.ExitFourFamily
import Hypostructure.Graph.Route8Carrier
import Hypostructure.Graph.Route8Closure
import Hypostructure.Graph.Route8Residual
import Hypostructure.Graph.ResponseDelocalization

-- Modules rescued from the quarantine boundary: legal modules that happened to
-- be reachable only through a quarantined one.  They are imported explicitly so
-- the quarantine removes the illegal carriers and nothing else -- without these
-- lines they would drop out of the build closure and silently stop being
-- checked.  See `quarantine.txt`.

import Hypostructure.Core.Contract
-- `Graph.WedgeLowerBound` was rescued here until node `[30]` was ported; the
-- spine's own vocabulary imports it now, so it is no longer a rescue.

-- Rescued from the SequentialExtensionLedger quarantine boundary.
import Hypostructure.Graph.FinitePathSelection
import Hypostructure.Graph.Strategy.InterfaceReplacement

-- Rescued from the Core.Routing stage-deletion boundary: legal modules that
-- were reachable only through a quarantined one.
import Hypostructure.Core.DependentOwnerGlueCapacity
