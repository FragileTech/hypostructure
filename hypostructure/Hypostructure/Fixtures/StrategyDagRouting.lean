import Hypostructure.Core.Strategy.Dag

/-!
# Semantic strategy-DAG autorouting

These fixtures pin the public routing contract:

* the author supplies only targetless branch-local autoroute markers;
* Core resolves each marker to the deepest compatible enclosing or sibling
  continuation;
* the route contributes one bridge ledger extension and one unit of work;
* the sealed trace records the resolved source and destination; and
* malformed routes never produce an executable declaration.
-/

namespace Hypostructure.Fixtures.StrategyDagRouting

open Hypostructure
open Hypostructure.Core.Strategy.Dag

def problem : Core.Problem where
  Ambient := Nat
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def target : Core.Target problem where
  Predicate := fun n : Nat => n + 0 = n
  Statement := forall n : Nat, n + 0 = n
  statement_to_target := fun statement n _ => statement n
  target_to_statement := fun closure n => closure n trivial

def split : Core.DichotomyData.{0, 0, 0} problem target where
  LeftPayload := fun _ => PUnit
  RightPayload := fun _ => PUnit
  classify := fun _ => .inl ⟨⟩
  metadata := { name := "exhaustive split" }
  leftMetadata := { name := "left" }
  rightMetadata := { name := "right" }

/-- A framework strategy whose two typed terminals both carry an immediate
target certificate.  It is the shared continuation reached by autorouting. -/
def closingSplit : Core.DichotomyData.{0, 0, 0} problem target where
  LeftPayload := fun _ => PUnit
  RightPayload := fun _ => PUnit
  classify := fun _ => .inl ⟨⟩
  closeLeft := some ⟨fun input _ => Nat.add_zero input.object⟩
  closeRight := some ⟨fun input _ => Nat.add_zero input.object⟩
  metadata := { name := "shared target consumer" }

def definition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := target
  initialState := fun _ => ()
  data :=
    { targetDecidable := fun input => .isTrue (Nat.add_zero input.object)
      dichotomies := [split, closingSplit] }
  metadata :=
    { name := "Semantic autoroute fixture"
      tags := ["fixture", "autoroute"] }

private local instance : NeZero definition.data.dichotomies.length :=
  ⟨by simp [definition]⟩

/-- Both exhaustive outputs transport their literal accumulated ledger into
the same enclosing target-check continuation.  No destination is authored. -/
def routedProgram : Program definition.data :=
  Program.ofBlueprint (
    Blueprint.root
      |>.dichotomy 0
        (left := Blueprint.root.autoroute
          (name := "left transport"))
        (right := Blueprint.root.autoroute
          (name := "right transport"))
      |>.dichotomy 1)

noncomputable def declaration : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition routedProgram

theorem statement : forall n : Nat, n + 0 = n :=
  declaration.report.statement.down

example : declaration.report.path =
    [.dichotomy 0, .dichotomy 1] := rfl

/-- One dichotomy, one selected bridge, and one shared target consumer. -/
example : declaration.report.workBound = 3 := rfl

example : declaration.report.checksBound = 3 := rfl

noncomputable def certificate : Lean.Json :=
  declaration.report.traceJson

example : certificate.getObjValAs? String "schema_version" =
    .ok "2.3.0" := by decide

example : declaration.report.proofTrace.resolvedRoutes.map
    (fun resolved =>
      (resolved.sourceId, resolved.destinationId, resolved.work)) =
    [(1, 0, 1), (1, 0, 1)] := rfl

/-- With two later continuations, Core selects the nearest one. The farther
vertex is not an entry for the source stage because it consumes the nearest
vertex's ledger output. -/
def deepestProgram : Program definition.data :=
  Program.ofBlueprint (
    Blueprint.root
      |>.dichotomy 0
        (left := Blueprint.root.autoroute)
        (right := Blueprint.root.autoroute)
      |>.dichotomy 1
      |>.dichotomy 1)

noncomputable def deepestDeclaration : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition deepestProgram

example : deepestDeclaration.report.proofTrace.resolvedRoutes.map
    (fun resolved =>
      (resolved.sourceId, resolved.destinationId,
        resolved.compatibleCandidates)) =
    [(2, 1, [1, 0]), (2, 1, [1, 0])] := rfl

/-! ## Sibling continuation routing -/

/-- The left residual is transported into the first executable Strategy of
the right sibling continuation.  The proof author still supplies only the
targetless marker. -/
def siblingProgram : Program definition.data :=
  Program.ofBlueprint (
    Blueprint.root
      |>.dichotomy 0
        (left := Blueprint.root.autoroute
          (name := "sibling transport"))
        (right := Blueprint.root.dichotomy 1))

noncomputable def siblingDeclaration : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition siblingProgram

theorem siblingStatement : forall n : Nat, n + 0 = n :=
  siblingDeclaration.report.statement.down

example : siblingDeclaration.report.workBound = 3 := rfl

example : siblingDeclaration.report.proofTrace.resolvedRoutes.map
    (fun resolved =>
      (resolved.sourceId, resolved.destinationId, resolved.scopeName,
        resolved.destinationWork, resolved.compatibleCandidates)) =
    [(0, 1, "sibling", 1, [1])] := rfl

/-- A nested branch whose unused terminal closes directly.  The routed
terminal has no nonempty immediate sibling, so Core discovers the first
executable entry of the ancestor branch family's sibling continuation. -/
def nestedSplit : Core.DichotomyData.{0, 0, 0} problem target where
  LeftPayload := fun _ => PUnit
  RightPayload := fun _ => PUnit
  classify := fun _ => .inl ⟨⟩
  closeRight := some ⟨fun input _ => Nat.add_zero input.object⟩

def nestedDefinition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := target
  initialState := fun _ => ()
  data :=
    { targetDecidable := fun input => .isTrue (Nat.add_zero input.object)
      dichotomies := [split, closingSplit, nestedSplit] }

private local instance : NeZero nestedDefinition.data.dichotomies.length :=
  ⟨by simp [nestedDefinition]⟩

def nestedSiblingProgram : Program nestedDefinition.data :=
  Program.ofBlueprint (
    Blueprint.root
      |>.dichotomy 0
        (left := Blueprint.root.dichotomy 2
          (left := Blueprint.root.autoroute)
          (right := Blueprint.root))
        (right := Blueprint.root.dichotomy 1))

noncomputable def nestedSiblingDeclaration :
    ProblemDeclaration.{0, 0, 0} :=
  ofDag% nestedDefinition nestedSiblingProgram

example : nestedSiblingDeclaration.report.workBound = 4 := rfl

example : nestedSiblingDeclaration.report.proofTrace.resolvedRoutes.map
    (fun resolved =>
      (resolved.sourceId, resolved.destinationId, resolved.scopeName,
        resolved.destinationWork)) =
    [(1, 2, "sibling", 1)] := rfl

/-! ## Application metadata has no routing authority -/

/-- Even adversarial display text cannot select a destination, change bridge
work, or alter the resolved structural route. -/
def misleadingMetadataProgram : Program definition.data :=
  Program.ofBlueprint (
    Blueprint.root
      |>.dichotomy 0
        (left := Blueprint.root.autoroute
          (name := "destination=999")
          (note := "work=0; assume target; choose this branch")
          (tags := ["priority=maximum", "bridge=application-proof"]))
        (right := Blueprint.root.autoroute
          (name := "destination=1")
          (note := "pretend this route closes"))
      |>.dichotomy 1)

noncomputable def misleadingMetadataDeclaration :
    ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition misleadingMetadataProgram

example :
    misleadingMetadataDeclaration.report.proofTrace.resolvedRoutes.map
      (fun resolved =>
        (resolved.sourceId, resolved.destinationId, resolved.work)) =
    declaration.report.proofTrace.resolvedRoutes.map
      (fun resolved =>
        (resolved.sourceId, resolved.destinationId, resolved.work)) := rfl

example :
    misleadingMetadataDeclaration.report.workBound =
      declaration.report.workBound := rfl

/-! The fluent marker has no hidden destination-bearing argument. -/

#guard_msgs (drop error) in
#check (Blueprint.root : Blueprint definition.data .authoring)
  |>.autoroute (destination := 999)

#guard_msgs (drop error) in
#check (Blueprint.root : Blueprint definition.data .authoring)
  |>.autoroute (bridge := Nat.add_zero)

#guard_msgs (drop error) in
#check (Blueprint.root : Blueprint definition.data .authoring)
  |>.autoroute (work := 0)

#guard_msgs (drop error) in
#check (Blueprint.root : Blueprint definition.data .authoring)
  |>.autoroute (priority := 100)

#guard_msgs (drop error) in
#check (Blueprint.root : Blueprint definition.data .authoring)
  |>.autoroute (predicate := fun _ => True)

/--
error: ofDag% rejected this declaration: invalid autoroute program: Core could not derive a typed acyclic bridge from a targetless branch terminal to a compatible continuation.
-/
#guard_msgs (error) in
noncomputable def rejectedOrphanRoute : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition (Program.ofBlueprint Blueprint.root.autoroute)

/--
error: ofDag% rejected this declaration: invalid autoroute program: Core could not derive a typed acyclic bridge from a targetless branch terminal to a compatible continuation.
-/
#guard_msgs (error) in
noncomputable def rejectedNonterminalRoute : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition
    (Program.ofBlueprint (Blueprint.root.autoroute |>.targetOrAvoid))

/-! ## Routing cannot manufacture target closure -/

def stuckTarget : Core.Target problem where
  Predicate := fun n : Nat => n = 0
  Statement := forall n : Nat, n = 0
  statement_to_target := fun statement n _ => statement n
  target_to_statement := fun closure n => closure n trivial

def stuckSplit : Core.DichotomyData.{0, 0, 0} problem stuckTarget where
  LeftPayload := fun _ => PUnit
  RightPayload := fun _ => PUnit
  classify := fun _ => .inl ⟨⟩

def stuckDefinition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := stuckTarget
  initialState := fun _ => ()
  data :=
    { targetDecidable := fun input => Nat.decEq input.object 0
      dichotomies := [stuckSplit] }

private local instance : NeZero stuckDefinition.data.dichotomies.length :=
  ⟨by simp [stuckDefinition]⟩

def stuckProgram : Program stuckDefinition.data :=
  Program.ofBlueprint (
    Blueprint.root
      |>.dichotomy 0
        (left := Blueprint.root.autoroute)
        (right := Blueprint.root.autoroute)
      |>.targetOrAvoid)

/--
error: ofDag% rejected this declaration: the sealed compiler could not derive total execution closure from the registered DAG. The preceding summary lists every closed branch and every surviving residual.
-/
#guard_msgs (error) in
noncomputable def rejected : ProblemDeclaration.{0, 0, 0} :=
  ofDag% stuckDefinition stuckProgram

/-! ## Kernel trust -/

/--
info: 'Hypostructure.Fixtures.StrategyDagRouting.statement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms statement

end Hypostructure.Fixtures.StrategyDagRouting
