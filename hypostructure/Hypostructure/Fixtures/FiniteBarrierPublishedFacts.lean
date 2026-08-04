import Hypostructure.Core.Strategy.FiniteBarrierEnumeration

/-!
# Sealed finite-barrier fact publication

This fixture exercises the public result of the sealed Strategy.  The fact
payload constructor and its derivation remain private to
`FiniteBarrierEnumeration.Profile`; consumers can only read the theorem from
the Strategy output retained by the normal ledger extension.
-/

namespace Hypostructure.Fixtures.FiniteBarrierPublishedFacts

open Hypostructure
open Hypostructure.Core.Residual

abbrev Residual := Unit
abbrev Previous := Ledger Residual

def completeUnit : Core.Finite.CompleteEnumeration Unit :=
  Core.Finite.CompleteEnumeration.ofFinEnum inferInstance

noncomputable def registration :
    Core.Strategy.FiniteBarrierEnumeration.Registration Residual where
  Candidate := fun _ => Unit
  candidates := fun _ => completeUnit
  accepted := fun _ _ => True
  acceptedDecidable := fun _ _ => isTrue trivial
  labelCount := fun _ => 1
  relationPosition := fun _ relation => relation
  leftLength := fun _ _ => 0
  rightLength := fun _ _ => 0

noncomputable def profile :
    Core.Strategy.FiniteBarrierEnumeration.Profile Previous Residual where
  registration := registration
  sourceCode := Query.ofFunction fun _ => [true]
  current := Query.residual

noncomputable def zeroProfile :
    Core.Strategy.FiniteBarrierEnumeration.Profile Previous Residual where
  registration := registration
  sourceCode := Query.ofFunction fun _ => [false]
  current := Query.residual

theorem incoming_code_controls_flat_count :
    (profile.decodedProfile (Ledger.initial ())).flatCount 0 0 = 1 ∧
      (zeroProfile.decodedProfile (Ledger.initial ())).flatCount 0 0 = 0 := by
  decide

def previous : Previous := Ledger.initial ()

noncomputable def output := profile.execution.run previous

theorem output_summary_is_derived :
    Core.Strategy.FiniteBarrierEnumeration.Summary.Derived
      (profile.summaryOfOutput previous output) :=
  profile.output_derived previous output

theorem output_summary_is_exactly_incoming_table_rows :
    profile.summaryOfOutput previous output =
      Core.Strategy.FiniteBarrierEnumeration.Summary.ofRows
        (profile.rows previous) :=
  profile.run_exact previous

theorem output_flat_product_is_positive :
    0 < (profile.summaryOfOutput previous output).flatProduct :=
  profile.output_flatProduct_pos previous output

abbrev Stage := Ledger.Extension Previous profile.execution.Output

noncomputable def stage : Stage := Ledger.extend previous output

theorem stage_previous_is_literal : stage.previous = previous := rfl

theorem stage_preserves_residual : residualOf stage = residualOf previous := rfl

#print axioms output_summary_is_derived
#print axioms output_summary_is_exactly_incoming_table_rows
#print axioms output_flat_product_is_positive
#print axioms incoming_code_controls_flat_count
#print axioms stage_previous_is_literal
#print axioms stage_preserves_residual

end Hypostructure.Fixtures.FiniteBarrierPublishedFacts
