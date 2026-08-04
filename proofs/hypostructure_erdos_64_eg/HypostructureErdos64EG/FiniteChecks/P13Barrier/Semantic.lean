import Hypostructure.Graph.WindowCurvatureCode

/-!
# The source model the P13 barrier table is audited against

The model is the framework's, at the registered window order.  Nothing in this
module defines a label, a legality test, a forbidden-difference schedule or a
relation: every name below is the corresponding declaration of
`Hypostructure.Graph.WindowCurvature`, whose meaning is already a theorem
there.

* `labelCode` is `windowLabelCode`.  It is total without a default value, and
  the label it names, `windowLabel`, is a bijection onto the manuscript's
  `Labels` (`windowLabel_injective`, `windowLabel_surjective`,
  `windowLabel_image`).  So the `Fin 399` the generated certificate is indexed
  by is the legal-label carrier of `lem:labels`, counted by
  `WindowCurvature.labels_card`, and not a stipulated size;
* `semanticRelation` is `windowRelation`, and `windowRelation_eq_safe` says it
  is the manuscript's `C_s` on the labels its indices name;
* the forbidden differences are never listed here: `windowGapSchedule` asks the
  registered dyadic target through `WindowCurvature.ForbiddenGap`.

The generated rows are audited against these names in `Audit00`--`Audit14`;
`Table.lean` carries that audit and the denotation into the registration.
-/

namespace HypostructureErdos64EG.FiniteChecks.P13Barrier

open Hypostructure.Graph.WindowCurvature

/-- The packed attachment label of the registered window order. -/
abbrev LabelCode := BitVec windowOrder

/-- The legal codes, in the ascending order the generated rows are indexed by.
-/
abbrev legalCodes : Array LabelCode := windowLegalCodes

/-- The code a certificate row index names. -/
abbrev labelCode : Fin 399 → LabelCode := windowLabelCode

/-- The relation the generated rows are audited against. -/
abbrev semanticRelation : Nat → Fin 399 → Fin 399 → Bool := windowRelation

end HypostructureErdos64EG.FiniteChecks.P13Barrier
