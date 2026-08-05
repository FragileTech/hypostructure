import Hypostructure.Core.Residual.Stage

/-!
# Temporary direct-reader migration surface

This module no longer defines a data wrapper.  `Query` is definitionally the
dependent function it used to contain.  The remaining namespace operations
exist only while call sites are migrated to `ExactLedger.get` and
`FactInputs.get`; this module is deleted at the end of that migration.
-/

namespace Hypostructure.Core.Residual

universe uSource uResult uOutput uPrevious uAdded uResidual

/-- Temporary source-compatible spelling for a direct dependent function.
It has no constructor, field, storage, or runtime representation of its own. -/
abbrev Query (Source : Sort uSource) (Result : Source -> Sort uResult) :=
  (source : Source) -> Result source

namespace Query

/-- Read the stable residual, independently of the depth of the ledger. -/
def residual {Source : Sort uSource} {Residual : Type uResidual}
    [HasResidual Source Residual] :
    Query Source (fun _source => Residual) :=
  residualOf

/-- Read the value introduced by the newest extension. -/
def latest {Previous : Sort uPrevious} {Added : Previous -> Sort uAdded} :
    Query (Ledger.Extension Previous Added)
      (fun stage => Added stage.previous) :=
  Ledger.Extension.added

/-- Lift an existing query through one no-copy extension.  This is the
canonical operation for retrieving an inherited fact or stage. -/
def preserve {Previous : Sort uPrevious} {Result : Previous -> Sort uResult}
    (query : Query Previous Result) {Added : Previous -> Sort uAdded} :
    Query (Ledger.Extension Previous Added)
      (fun stage => Result stage.previous) :=
  fun stage => query stage.previous

/-- Pull a query back along a framework-owned projection such as a typed join
projection. -/
def comap {Source : Sort uSource} {Result : Source -> Sort uResult}
    (query : Query Source Result) {NewSource : Sort uPrevious}
    (project : NewSource -> Source) :
    Query NewSource (fun source => Result (project source)) :=
  fun source => query (project source)

/-- Transform one queried value without another ledger read. -/
def map {Source : Sort uSource} {Input : Source -> Sort uResult}
    (query : Query Source Input) {Output : Source -> Sort uOutput}
    (transform : (source : Source) -> Input source -> Output source) :
    Query Source Output :=
  fun source => transform source (query source)

/-- Transform one queried value into a result whose type depends on that exact
queried value. -/
def dependentMap {Source : Sort uSource} {Input : Source -> Sort uResult}
    (query : Query Source Input)
    {Output : (source : Source) -> Input source -> Sort uOutput}
    (transform : (source : Source) -> (input : Input source) ->
      Output source input) :
    Query Source (fun source => Output source (query source)) :=
  fun source => transform source (query source)

/-- Read two inherited values from the identical source stage. -/
def and {Source : Sort uSource}
    {Left : Source -> Sort uResult} {Right : Source -> Sort uOutput}
    (left : Query Source Left) (right : Query Source Right) :
    Query Source (fun source => PProd (Left source) (Right source)) :=
  fun source => ⟨left source, right source⟩

@[simp] theorem read_residual
    {Source : Sort uSource} {Residual : Type uResidual}
    [HasResidual Source Residual] (source : Source) :
    (residual (Source := Source) (Residual := Residual)) source =
      residualOf source :=
  rfl

@[simp] theorem read_latest
    {Previous : Sort uPrevious} {Added : Previous -> Sort uAdded}
    (previous : Previous) (added : Added previous) :
    (latest (Previous := Previous) (Added := Added))
        (Ledger.extend previous added) = added :=
  rfl

/-- Extending a ledger preserves every prior typed query. -/
@[simp] theorem read_preserve
    {Previous : Sort uPrevious} {Result : Previous -> Sort uResult}
    (query : Query Previous Result) {Added : Previous -> Sort uAdded}
    (previous : Previous) (added : Added previous) :
    (query.preserve (Added := Added)) (Ledger.extend previous added) =
      query previous :=
  rfl

@[simp] theorem read_comap
    {Source : Sort uSource} {Result : Source -> Sort uResult}
    (query : Query Source Result) {NewSource : Sort uPrevious}
    (project : NewSource -> Source) (source : NewSource) :
    (query.comap project) source = query (project source) :=
  rfl

@[simp] theorem read_map
    {Source : Sort uSource} {Input : Source -> Sort uResult}
    (query : Query Source Input) {Output : Source -> Sort uOutput}
    (transform : (source : Source) -> Input source -> Output source)
    (source : Source) :
    (query.map transform) source = transform source (query source) :=
  rfl

@[simp] theorem read_dependentMap
    {Source : Sort uSource} {Input : Source -> Sort uResult}
    (query : Query Source Input)
    {Output : (source : Source) -> Input source -> Sort uOutput}
    (transform : (source : Source) -> (input : Input source) ->
      Output source input)
    (source : Source) :
    (query.dependentMap transform) source =
      transform source (query source) :=
  rfl

@[simp] theorem read_and
    {Source : Sort uSource}
    {Left : Source -> Sort uResult} {Right : Source -> Sort uOutput}
    (left : Query Source Left) (right : Query Source Right) (source : Source) :
    (left.and right) source = ⟨left source, right source⟩ :=
  rfl

end Query

namespace Node

/-- Define a proposition node from one typed ledger query and one local
mathematical implication. -/
def derive {Previous : Sort uPrevious} {Input : Previous -> Sort uResult}
    (query : Query Previous Input) {Property : Previous -> Prop}
    (prove : (previous : Previous) -> Input previous -> Property previous) :
    Node Previous Property :=
  Node.create fun previous => prove previous (query previous)

end Node

namespace StageNode

/-- Define a data-bearing node from one typed ledger query. -/
def derive {Previous : Sort uPrevious} {Input : Previous -> Sort uResult}
    (query : Query Previous Input) {Output : Previous -> Sort uOutput}
    (produce : (previous : Previous) -> Input previous -> Output previous) :
    StageNode Previous Output :=
  StageNode.create fun previous => produce previous (query previous)

/-- Produce an output whose type depends on the exact value returned by a
typed predecessor query. -/
def dependent {Previous : Sort uPrevious}
    {Input : Previous -> Sort uResult} (query : Query Previous Input)
    {Output : (previous : Previous) -> Input previous -> Sort uOutput}
    (produce : (previous : Previous) -> (input : Input previous) ->
      Output previous input) :
    StageNode Previous (fun previous => Output previous (query previous)) :=
  StageNode.create fun previous => produce previous (query previous)

end StageNode

end Hypostructure.Core.Residual
