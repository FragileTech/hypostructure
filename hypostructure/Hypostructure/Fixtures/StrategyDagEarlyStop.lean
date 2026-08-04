import Hypostructure.Core.Strategy.Dag

/-!
# Runner-owned early stopping

This fixture pins early stopping as a runner-owned law.  The registered
target decision procedure closes the run at the root, so every later vertex
— including a *real*, resolvable `orderedWitnessScan` over a registered
singleton schedule — is skipped structurally by `HaltingProgram.snoc`: the
appended contract is never evaluated and the target certificate is carried
forward unchanged.

Pinned here:
- trace projections of the extended DAG (`rfl`);
- the total certified statement of both sealed reports (the strict `ofDag%`
  frontend only accepts certifying declarations, so `Report.statement`
  needs no residual alternative);
- a backend-level `rfl` pin on the public `HaltingProgram` API: appending a
  contract after closure changes neither the output nor evaluates the
  vertex, the extension records the vertex as skipped (`added = none`), and
  the appended vertex extends the literal predecessor stage;
- an axiom pin on the named statement theorem.
-/

namespace Hypostructure.Fixtures.StrategyDagEarlyStop

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

/-- One registered singleton scan family.  `scans[0]` exists, so the
appended `orderedWitnessScan 0` vertex is real strategy content that the
frontend resolves — early stopping, not refusal, is what skips it. -/
def scanFamily : Core.ScanData.{0, 0, 0} problem where
  Item := fun _ => PUnit
  schedule := fun _ => Core.Finite.Enumeration.singleton PUnit.unit
  witness := fun _ _ => True
  witnessDecidable := fun _ _ => .isTrue trivial

def strategyData : Core.StrategyData.{0, 0, 0} problem target where
  targetDecidable := fun input => .isTrue (Nat.add_zero input.object)
  scans := [scanFamily]

def definition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := target
  initialState := fun _ => ()
  data := strategyData

/-- One-vertex DAG: the early-closure key alone. -/
def dagOne : Blueprint :=
  Blueprint.root.targetOrAvoid

/-- `dagOne` with the real, resolvable scan vertex appended after closure. -/
def dagTwo : Blueprint :=
  dagOne.orderedWitnessScan 0

noncomputable def declarationOne : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition dagOne

noncomputable def declarationTwo : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition dagTwo

/-! ## Trace pins (pure syntactic recursion, `rfl`) -/

example : declarationTwo.report.path =
    [.targetOrAvoid, .orderedWitnessScan 0] := rfl

example : declarationTwo.report.workBound = 2 := rfl

example : declarationTwo.report.checksBound = 2 := rfl

/-! ## Certified statements through the sealed reports

The frontend only accepts certifying declarations, so the statement is a
total projection — for the extended DAG exactly as for the one-vertex DAG,
because the appended vertex is skipped after closure rather than consulted. -/

theorem dagOne_statement : forall n : Nat, n + 0 = n :=
  declarationOne.report.statement.down

theorem dagTwo_statement : forall n : Nat, n + 0 = n :=
  declarationTwo.report.statement.down

/-! ## Backend-level early-stop pin (public `HaltingProgram` API)

The root program already closes the run (the runner consults the registered
decision procedure before vertex 0).  Appending a contract with `snoc` after
closure (i) leaves the output on the target side by `rfl` — the vertex is
never evaluated — (ii) records the skipped vertex as `added = none` in the
new ledger extension, and (iii) extends the literal predecessor stage. -/

def rootProgram : Core.Strategy.HaltingProgram problem target :=
  Core.Strategy.HaltingProgram.root strategyData

/-- A small honest contract appended after the root has closed the run; its
`certify` never fires because the vertex is skipped. -/
def appendedContract : Core.Strategy.Contract.{0, 0, 0} rootProgram.Stage where
  Terminal := PUnit
  Payload := fun _ _ => PUnit
  produce := fun _ => ⟨PUnit.unit, PUnit.unit⟩
  exhaustive := fun _ => ⟨⟨PUnit.unit, PUnit.unit⟩⟩

def extendedProgram : Core.Strategy.HaltingProgram problem target :=
  rootProgram.snoc appendedContract (fun _ _ => none)

-- (i) The extended program's output at an arbitrary input is still the
-- target certificate, by `rfl`: `snoc` never applies the appended contract
-- once the predecessor output is on the target side.
example (input : Core.Strategy.ProblemInput problem) :
    extendedProgram.output input = Sum.inl ⟨Nat.add_zero input.object⟩ := rfl

-- (ii) The extension records the appended vertex as skipped: the added
-- ledger value is `none`, by `rfl`.
example (input : Core.Strategy.ProblemInput problem) :
    (extendedProgram.run input).added = none := rfl

-- (iii) Literal predecessor preservation: the appended vertex extends the
-- exact stage produced by the previous program, by `rfl`.
example (input : Core.Strategy.ProblemInput problem) :
    (extendedProgram.run input).previous = rootProgram.run input := rfl

/-! ## Kernel trust -/

/--
info: 'Hypostructure.Fixtures.StrategyDagEarlyStop.dagTwo_statement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dagTwo_statement

end Hypostructure.Fixtures.StrategyDagEarlyStop
