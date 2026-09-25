import Hypostructure.Graph.Strategy.SpineVocabulary

/-!
Audit check only. This anonymous example shows that the positive pattern
retained on node [144a] is incompatible with fixed homogeneous caps on the
same object. It does not establish closure of the handoff branch.
-/

namespace Hypostructure.Graph

universe u

example (object : FiniteObject.{u}) (threshold order deficitScale routingLabelBound : Nat)
    (Label : Type) [Fintype Label]
    (capacity : CapacityPresentation object threshold order)
    (h : HomogeneousBottleneckPatternStatement object threshold order
      deficitScale routingLabelBound capacity Label) :
    ¬ HomogeneousCapsHold object threshold order Label := by
  intro caps
  rcases h with ⟨certified, token, role, tokenMem, _positive, _multiplicity,
    _coarsePattern, sourceClass, _classEq, root, _rootEq, detailedPattern⟩
  rcases detailedPattern with matching | star
  · rcases matching with ⟨pattern, subset, isMatching, large, _configurations⟩
    exact (caps capacity certified.ledger).1 token tokenMem role
      ⟨pattern, subset, isMatching, large⟩
  · rcases star with ⟨centre, pattern, subset, isStar, large, _configurations⟩
    exact (caps capacity certified.ledger).2 token tokenMem role
      ⟨centre, pattern, subset, isStar, large⟩

end Hypostructure.Graph

namespace Hypostructure.Graph.Strategy.Spine

universe u

/-! The actual [144a] handoff retains the positive source pattern, so a
fixed cap on that graph would itself finish this arm. This is an implication
check, not a derivation of the cap from the handoff. -/
example (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (handoff : SameTokenTypeBHandoffStatement data object) :
    ¬ Graph.HomogeneousCapsHold object data.threshold data.windowOrder
      (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
        (Graph.WindowCurvature.Label data.windowOrder)) := by
  intro caps
  rcases handoff with ⟨_active, capacity, _activationEq, pattern, _envelope⟩
  rcases pattern with ⟨certified, token, role, tokenMem, _positive,
    _multiplicity, _coarsePattern, _sourceClass, _sourceClassEq, _root,
    _rootEq, detailedPattern⟩
  rcases detailedPattern with matching | star
  · rcases matching with ⟨selected, subset, isMatching, large, _routes⟩
    exact (caps capacity certified.ledger).1 token tokenMem role
      ⟨selected, subset, isMatching, large⟩
  · rcases star with ⟨centre, selected, subset, isStar, large, _routes⟩
    exact (caps capacity certified.ledger).2 token tokenMem role
      ⟨centre, selected, subset, isStar, large⟩

end Hypostructure.Graph.Strategy.Spine
