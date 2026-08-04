import Hypostructure.FiniteChecks.ColdResponse.Table

/-!
# Kernel audit for generated cold-response rows
-/

namespace Hypostructure.FiniteChecks.ColdResponse

/-- Audited rows pair each inert encoding with the value recomputed by the
semantic evaluator. -/
structure AuditedRow (signature : Signature)
    (evaluator : Evaluator signature) where
  encoding : Encoding signature
  sourceValue : evaluator.Value
  replacementValue : evaluator.Value
  sourceExact : sourceValue = evaluator.evaluateSource encoding
  replacementExact : replacementValue = evaluator.evaluateReplacement encoding

/-- Lean constructs every audit row from the evaluator. -/
def audit (evaluator : Evaluator signature) :
    List (AuditedRow signature evaluator) :=
  (generate signature).map fun encoding =>
    { encoding := encoding
      sourceValue := evaluator.evaluateSource encoding
      replacementValue := evaluator.evaluateReplacement encoding
      sourceExact := rfl
      replacementExact := rfl }

theorem audit_length (evaluator : Evaluator signature) :
    (audit evaluator).length = (generate signature).length := by
  simp [audit]

theorem audit_covers (evaluator : Evaluator signature)
    (encoding : Encoding signature) :
    ∃ row ∈ audit evaluator, row.encoding = encoding := by
  refine ⟨{
    encoding := encoding
    sourceValue := evaluator.evaluateSource encoding
    replacementValue := evaluator.evaluateReplacement encoding
    sourceExact := rfl
    replacementExact := rfl
  }, ?_, rfl⟩
  simp [audit, mem_generate]

end Hypostructure.FiniteChecks.ColdResponse
