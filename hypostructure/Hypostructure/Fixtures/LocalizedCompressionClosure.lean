import Hypostructure.Core.Strategy.LocalizedCompressionClosure
import Hypostructure.Fixtures.CT3

/-!
# `localizedCompressionClosure` is genuinely instantiable

A minimal instantiation over a toy problem, reusing the already-verified
`Fixtures.CT3.Neutral` response system and Boolean coordinate schedule: one
region, one scheduled candidate that is unconditionally admissible and
strictly smaller (so CT3 reaches the `.compression` terminal), and a
`bridge` from the resulting compression certificate to the (trivial)
registered target. This pins that the new Core strategy builds a real
`Core.DichotomyData` with no axioms beyond the standard three — no
`sorryAx`, no invented facts.
-/

namespace Hypostructure.Fixtures.LocalizedCompressionClosure

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Fixtures.CT3.Neutral (Row responseSystem targetMeaning
  rowResponse boolCoordinates boolCoordinates_complete)

def problem : Core.Problem where
  Ambient := Bool
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def target : Core.Target problem where
  Predicate := fun _ => True
  Statement := True
  statement_to_target := fun statement _ _ => statement
  target_to_statement := fun closure => closure true trivial

abbrev Input := Core.Strategy.ProblemInput problem

@[reducible] def spec (_input : Input) (_c : Unit) :
    Hypostructure.CT3.Spec Input where
  Representative := Bool
  Candidate := Bool
  Row := Row
  system := responseSystem
  semantics := targetMeaning
  candidatePiece := id
  rowPiece := Row.piece
  rowResponse := rowResponse
  Admissible := fun _ _ _ => True
  StrictlySmaller := fun _ _ _ => True

def coverage (input : Input) (c : Unit) (replacement : Bool) :
    Core.Response.FiniteTable.SymbolicCoverage responseSystem
      ((spec input c).representatives input.object replacement)
      (Core.Response.FiniteTable.ExactSchedule.ofList boolCoordinates.values) where
  locate := by
    intro context
    obtain ⟨index, rfl⟩ :=
      (boolCoordinates.mem_iff_exists_index context).mp
        (boolCoordinates_complete context)
    exact ⟨index, rfl, rfl⟩

def capability (input : Input) (c : Unit) :
    Hypostructure.CT3.Capability (spec input c) where
  source := Query.ofFunction fun (i : Input) => i.object
  coordinates := Query.ofFunction fun _ => boolCoordinates
  candidates := Query.ofFunction fun _ => Core.Finite.Enumeration.singleton false
  rows := Query.ofFunction fun _ => Core.Finite.Enumeration.empty Row
  valueDecEq := by change DecidableEq Bool; infer_instance
  admissibleDecidable := fun _ _ _ => .isTrue trivial
  smallerDecidable := fun _ _ _ => .isTrue trivial
  candidateCoverage := fun previous candidate _member => coverage previous c candidate
  rowCoverage := fun _previous row member =>
    absurd member (by
      simp [Core.Finite.Enumeration.empty, Core.Finite.Enumeration.ofNodupList])
  inputSize := fun _ => 0
  workCoefficient := 8
  workDegree := 0
  workBound := fun _ => by
    simp only [Query.read_ofFunction]
    decide

noncomputable def testDichotomy : Core.DichotomyData problem target :=
  Core.Strategy.localizedCompressionClosure
    (P := problem) (T := target)
    (Component := fun _ => Unit)
    (schedule := fun _ => Core.Finite.Enumeration.singleton ())
    (spec := spec)
    (capability := capability)
    (bridge := some ⟨fun _ _ _ => trivial⟩)

/-! ## Kernel trust -/

#print axioms testDichotomy

/-! ## `wellFoundedCompressionClosure` genuinely recurses

A second toy problem exercising the actual induction step (not just the
immediate base case): `object = true` always compresses to `object = false`
(measure `1 -> 0`), and `object = false` schedules no compressing candidate
at all, so the recursion bottoms out in the real base case exactly once.
This is the same shape a real minimal-counterexample argument has —
"compress until you can't, then close directly" — just with a trivial
target so the pattern's plumbing, not new domain mathematics, is what's
being pinned. -/

namespace Recursive

@[reducible] def problem : Core.Problem where
  Ambient := Bool
  Baseline := fun _ => True
  BranchState := fun _ => Unit

@[reducible] def target : Core.Target problem where
  Predicate := fun _ => True
  Statement := True
  statement_to_target := fun statement _ _ => statement
  target_to_statement := fun closure => closure true trivial

abbrev Input := Core.Strategy.ProblemInput problem

/-- A trivially-neutral response system (one constant coordinate): every
representative responds identically everywhere, so whether a candidate
`Compresses` depends only on `Admissible`/`StrictlySmaller` below — never on
borrowed response semantics that could conflict with them. -/
@[reducible] def recSystem : Core.Response.System.{0, 0, 0, 0} Bool :=
  Core.Response.System.ofDecodedContexts Unit Unit Bool (fun _ _ => true) id

@[reducible] def recSemantics : Core.Response.TargetSemantics recSystem where
  TargetResponse := fun _ _ => True
  Accepts := fun value => value = true
  target_iff_accepts := fun _ _ => ⟨fun _ => rfl, fun _ => trivial⟩

@[reducible] def spec (_input : Input) (_c : Unit) :
    Hypostructure.CT3.Spec.{0, 0, 0, 0, 0, 0, 0} Input where
  Representative := Bool
  Candidate := Bool
  Row := PEmpty
  system := recSystem
  semantics := recSemantics
  candidatePiece := id
  rowPiece := PEmpty.elim
  rowResponse := PEmpty.elim
  Admissible := fun input _ candidate => input.object = true ∧ candidate = false
  StrictlySmaller := fun input _ _ => input.object = true

def capability (input : Input) (c : Unit) :
    Hypostructure.CT3.Capability (spec input c) where
  source := Query.ofFunction fun (i : Input) => i.object
  coordinates := Query.ofFunction fun _ =>
    ({ values := [()], nodup := by simp, decEq := fun _ _ => .isTrue rfl } :
      Core.Finite.Enumeration (spec input c).system.Coordinate)
  -- Constant, input-independent schedule: `false` is always scheduled, but
  -- `Admissible` (below) only accepts it when `input.object = true` — so the
  -- search still correctly finds no compression when `input.object = false`,
  -- just via admissibility rather than an empty schedule, which keeps the
  -- coverage/work-bound obligations input-independent too.
  candidates := Query.ofFunction fun _ => Core.Finite.Enumeration.singleton false
  rows := Query.ofFunction fun _ => Core.Finite.Enumeration.empty PEmpty
  valueDecEq := by change DecidableEq Bool; infer_instance
  admissibleDecidable := fun input _ candidate => inferInstance
  smallerDecidable := fun input _ _ => inferInstance
  candidateCoverage := fun previous candidate _member =>
    letI : Subsingleton (spec input c).system.Context := inferInstanceAs (Subsingleton Unit)
    Core.Response.FiniteTable.SymbolicCoverage.ofSubsingletonSingleton
      (spec input c).system
      ((spec input c).representatives ((Query.ofFunction fun i : Input => i.object).read previous)
        ((spec input c).candidatePiece candidate))
      ()
  rowCoverage := fun _ row _ => row.elim
  inputSize := fun _ => 0
  workCoefficient := 8
  workDegree := 0
  workBound := fun _ => by
    simp only [Query.read_ofFunction, Core.Finite.Enumeration.card,
      Core.Finite.Enumeration.singleton, Core.Finite.Enumeration.ofNodupList,
      Core.Finite.Enumeration.empty, Hypostructure.CT3.localCheckBound]
    decide

/-- The compressed candidate `false` re-packaged as a fresh `ProblemInput`,
with `object := false` — the actual "recurse on the smaller instance". -/
def replacement (_input : Input) (_c : Unit)
    (_cert : Hypostructure.CT3.CompressionCertificate (capability _input _c) _input) :
    Input :=
  { object := false, baseline := trivial, branchState := () }

def measure (input : Input) : Nat := cond input.object 1 0

theorem measureDecreases (input : Input) (c : Unit)
    (cert : Hypostructure.CT3.CompressionCertificate (capability input c) input) :
    measure (replacement input c cert) < measure input := by
  have admissible : input.object = true ∧ cert.candidate = false := cert.valid.1
  simp only [measure, replacement, admissible.1, cond]
  decide

noncomputable def closure : (input : Input) -> target.Predicate input.object :=
  Core.Strategy.wellFoundedCompressionClosure
    (P := problem) (T := target)
    (Component := fun _ => Unit)
    (schedule := fun _ => Core.Finite.Enumeration.singleton ())
    (spec := spec)
    (capability := capability)
    (measure := measure)
    (replacement := replacement)
    (measureDecreases := measureDecreases)
    (transport := fun _ _ _ _ => trivial)
    -- No candidate is ever admissible from `false` (`Admissible` requires
    -- `object = true`), so this base case — the genuine bottom of the
    -- induction — is trivial here since the toy target itself is trivial.
    (baseCase := fun _ _ => trivial)

#print axioms closure

end Recursive

end Hypostructure.Fixtures.LocalizedCompressionClosure
