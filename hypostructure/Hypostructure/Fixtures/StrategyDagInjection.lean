import Hypostructure.Core.Strategy.Dag

/-!
# Strategy DAG injection resistance

Negative compile pins showing that an application cannot smuggle execution
values through the two declared inputs (requirements §19.16–§19.19):

- **§19.16 (no execution callbacks through `ProblemDefinition`).**  A
  hand-built backend `Contract` — public backend API — cannot be registered
  as strategy data: every `StrategyData` field is plain mathematical data,
  so `scans := [contract]` is a type error.
- **§19.17 (no resolution override through local instances).**  A rogue
  high-priority `Decidable` instance declared between two identical
  declarations changes nothing: key resolution reads the stored
  `targetDecidable` field, never instance search, so the two sealed
  declarations are definitionally equal (positive `rfl` pin).
- **§19.18 (output constructors inaccessible).**  Anonymous-constructor
  attempts at `ProblemDeclaration` and at a `Report`-typed value fail:
  both constructors are private, so no forged declarations or reports.
- **§19.16/§19.18 (blueprint carries no payloads).**  Attaching the same
  hand-built `Contract` to a `Blueprint` vertex is a type error: `step`
  accepts only an official `StrategyKey`, pure syntax with no payload slot.
- **Forged closure proofs are type errors.**  The `ofDag%` escape hatch
  `(certifies := …)` elaborates the supplied term against the sealed
  certification obligation; junk proofs are rejected by the type checker.
-/

namespace Hypostructure.Fixtures.StrategyDagInjection

open Hypostructure
open Hypostructure.Core.Strategy.Dag

/-! ## An honest registered problem -/

def problem : Core.Problem where
  Ambient := Nat
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def target : Core.Target problem where
  Predicate := fun n : Nat => n + 0 = n
  Statement := forall n : Nat, n + 0 = n
  statement_to_target := fun statement n _ => statement n
  target_to_statement := fun closure n => closure n trivial

def definition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := target
  initialState := fun _ => ()
  data :=
    { targetDecidable := fun input => .isTrue (Nat.add_zero input.object) }

/-- An honest, well-typed backend contract built from public backend API.
The pins below show that no blueprint vertex and no registered-data field
can absorb it. -/
def contract : Core.Strategy.Contract Bool where
  Terminal := Unit
  Payload := fun _ _ => Bool
  produce := fun previous => ⟨(), previous⟩
  exhaustive := fun previous => ⟨⟨(), previous⟩⟩

/-! ## Pin 1 — blueprint vertices carry no payloads (§19.16, §19.18)

`Blueprint.step` accepts only an official `StrategyKey`; a backend contract
cannot be attached to a vertex. -/

/--
error: Application type mismatch: The argument
  contract
has type
  Core.Strategy.Contract Bool
of sort `Type 1` but is expected to have type
  StrategyKey
of sort `Type` in the application
  Blueprint.root.step contract
-/
#guard_msgs (error) in
example : Blueprint :=
  Blueprint.step Blueprint.root contract

/-! ## Pin 2 — `StrategyData` fields are data only (§19.16)

The same contract cannot be registered as strategy data: `scans` accepts
only residual-indexed `ScanData` (schedules plus decidable witnesses). -/

/--
error: Application type mismatch: The argument
  contract
has type
  Core.Strategy.Contract Bool
but is expected to have type
  Core.ScanData problem
in the application
  List.cons contract
-/
#guard_msgs (error) in
example : Core.StrategyData.{0, 0, 0} problem target :=
  { targetDecidable := fun input => .isTrue (Nat.add_zero input.object)
    scans := [contract] }

/-! ## Pin 3 — no forged declarations (§19.18)

`ProblemDeclaration.mk` is private; the anonymous constructor cannot build
a declaration from application code. -/

/--
error: Invalid `⟨...⟩` notation: Constructor for `Hypostructure.Core.Strategy.Dag.ProblemDeclaration` is marked as private
-/
#guard_msgs (error) in
example : ProblemDeclaration := ⟨definition⟩

/-! ## Pin 4 — no forged reports (§19.18) -/

def strategyDag : Blueprint :=
  Blueprint.root.targetOrAvoid

noncomputable def declA : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition strategyDag

/--
error: Invalid `⟨...⟩` notation: Constructor for `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.Report` is marked as private
-/
#guard_msgs (error) in
example : declA.Report := ⟨⟩

/-! ## Pin 5 — forged closure proofs are type errors

The `(certifies := …)` escape hatch is elaborated against the sealed
certification obligation; junk terms do not typecheck. -/

/--
error: Type mismatch
  trivial
has type
  True
but is expected to have type
  definition.data.Certifies
-/
#guard_msgs (error) in
noncomputable def forgedCertifies : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition strategyDag (certifies := trivial)

/-! ## Pin 6 — instance non-interference (§19.17, §19.19)

A rogue high-priority `Decidable True` instance declared between two
identical declarations does not alter resolution: the compiler reads the
stored `targetDecidable` field, never instance search.  The two sealed
declarations are definitionally equal. -/

local instance (priority := high) rogueDecidableTrue : Decidable True :=
  .isTrue trivial

noncomputable def declB : ProblemDeclaration.{0, 0, 0} :=
  ofDag% definition strategyDag

theorem instance_noninterference : declA = declB := rfl

/--
info: 'Hypostructure.Fixtures.StrategyDagInjection.instance_noninterference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms instance_noninterference

end Hypostructure.Fixtures.StrategyDagInjection
