# Statement, contract and key families

The Erdős–Gyárfás proof is split into five families.  Each family owns its
statement module, its contract directory, its row and decision modules, and its
assembly directory; shared files are edited only in the family's own lines.

| Family | Statements (`Graph/Statements/`) | Contracts (`Graph/Contracts/`) | Assembly (`Assembly/`) |
|---|---|---|---|
| F1 Type A | `TypeA.lean`, `CanonicalTypeA.lean` | `TypeA/` | `TypeA/` |
| F2 Type B | `TypeB.lean`, `TypeBLanes.lean`, `CanonicalTypeB.lean`, `TypeBSublinear*.lean` | `TypeB/` | `TypeB/` |
| F3 Route 8 | `RouteEight.lean`, `RouteEightPinned.lean`, `CanonicalRouteEight.lean`, `Route8*.lean` | `RouteEight/` | `RouteEight/` |
| F4 Surplus / Homogeneous / Pair | `SurplusPair*.lean`, `CanonicalSurplus*.lean`, `CanonicalPairHandoff.lean`, `Pair*.lean`, `SameToken*.lean` | `SurplusPair/` | `Surplus/` |
| F5 Spine / Cold / NearCubic | `Parameters.lean`, `Spine.lean`, `ColdResiduals.lean`, `ColdGerm.lean`, `ColdMarkedGerm.lean`, `CanonicalCold.lean`, `BranchD.lean`, `DensityOrder.lean`, and the entry-prefix modules (`CycleCounting`, `LocalRigidity`, `JointHubs`, `HubLinks`, `StubDeficit`, …) | `Spine/` | `Entry.lean`, `NearCubic/`, `NetCharge/` |

## Statement modules

All statement definitions live in
`hypostructure/Hypostructure/Graph/Statements/` (64 modules).  No statement
module imports `SpineVocabulary` or any `Graph/Strategy` module.  They use the
namespace `Hypostructure.Graph.Strategy.Spine`.  Each statement takes the
registered constants as an explicit `Parameters` argument
(`Statements/Parameters.lean`); the vocabulary record is
`structure Data extends Parameters` (`Strategy/SpineVocabulary.lean`), and each
`Holds` branch instantiates its statement at `data.toParameters` and the object.

The base chain is `Parameters ← Spine ← (CanonicalTypeA) ← TypeA ← {TypeB, RouteEight}`, with
`SurplusPair` above `TypeB` and `ColdResiduals` above `Spine` and `SurplusPair`.
A statement needed by several families goes in the lowest module that every
consumer imports.

## Keys

`Graph.Strategy.Spine.Key` has 539 keys, each with an index
(`SpineVocabulary.lean`, `idx`; largest index 9991).  A key is added with its
constructor, its `Holds` branch, `label`, `idx`, `ofIdx`, `name`, and its
`LabelPins` line.  Indices are never renumbered.  A key belongs to the family of
its producing row; where rows of several families produce the same key
(`typeBFanEntry`: F2 and F4 rows), the owner is the family of the majority of
its producing rows.  Keys with no producing row module (produced by the scope
initialization or by a decision in an assembly file, e.g. `selection`,
`surplusAbove`, `surplusAtOrBelow`, `windowPackageRealized`,
`windowPackageUnrealized`, `denseDeficiencyBelow`, `denseDeficiencyAtOrAbove`,
`coldGermSomeDistinguishing`, `coldGermNoneDistinguishing`) belong to F5.

## Shared files

| File | Owner | Rule |
|---|---|---|
| `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean` | F5 (structure, `Data`, key-freshness tactic) | Each family appends only its own key lines, in disjoint regions. |
| `hypostructure/Hypostructure/Graph/Statements/Parameters.lean` | F5 | Registered constants are added only by F5. |
| `Assembly/Final.lean` | F5 | Other families change only the arm of their own returned outcome. |
| `Assembly/Residuals.lean`, `Assembly/Residuals/*.lean` | F5 | The generic residuals of `SelectedLedgerBoundaryResult` and their subtypes and products; a family edits only its own residual. |
| `Assembly/Basic.lean` | F5 | Problem, input and selection key; no family-specific content. |
| `Assembly/{RouteEight,NetCharge,NearCubic,Surplus}/Boundary.lean` | F3, F5, F5, F4 | Boundary chain `RouteEight ← NetCharge ← NearCubic` and `Residuals ← Surplus`; a family edits only its own disjunct. |
| `Graph/Strategy/SpineContinuationRun.lean`, `SpineRows.lean`, `SpineRows/Basic.lean`, `ColdCorridorRows.lean` | F5 | Aggregators; append-only imports. |
| `Graph/Strategy/HomogeneousBottleneckRows.lean` | F4 | Aggregator; append-only imports. |
| `hypostructure/Hypostructure.lean` | F5 | Root import list; append-only. |
| `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Problem.lean` | F5 | Application boundary. |
