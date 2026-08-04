import Mathlib

/-!
# Semantic encodings for finite same-interface response checks

Rows carry only indices into presentation-owned finite carriers.  They contain
no hit/defect/neutral tag and no claimed response value.
-/

namespace Hypostructure.FiniteChecks.ColdResponse

universe u v w

/-- Finite carriers from which every table dimension is derived. -/
structure Signature where
  InterfaceLabel : Type u
  ContextState : Type v
  GermState : Type w
  interfaceLabels : List InterfaceLabel
  contextStates : List ContextState
  germStates : List GermState

/-- One inert pair of same-interface germ encodings and one context encoding. -/
structure Encoding (signature : Signature) where
  interfaceIndex : Fin signature.interfaceLabels.length
  sourceIndex : Fin signature.germStates.length
  replacementIndex : Fin signature.germStates.length
  contextIndex : Fin signature.contextStates.length
deriving DecidableEq

/-- A semantic evaluator is separate from generated rows.  The audit invokes
this function on each encoding; the table cannot author the answer. -/
structure Evaluator (signature : Signature) where
  Value : Type
  instDecidableEq : DecidableEq Value
  evaluateSource : Encoding signature → Value
  evaluateReplacement : Encoding signature → Value

attribute [instance] Evaluator.instDecidableEq

def responsesEqual (evaluator : Evaluator signature)
    (row : Encoding signature) : Prop :=
  evaluator.evaluateSource row = evaluator.evaluateReplacement row

instance (evaluator : Evaluator signature) (row : Encoding signature) :
    Decidable (responsesEqual evaluator row) := by
  unfold responsesEqual
  exact evaluator.instDecidableEq _ _

end Hypostructure.FiniteChecks.ColdResponse
