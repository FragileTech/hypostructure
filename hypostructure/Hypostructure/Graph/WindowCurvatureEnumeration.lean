import Hypostructure.Graph.WindowCurvatureAlgebra

/-!
# The legal-label census, by size

The two definitions below are the census a problem runs to obtain its own
legal-label count and size distribution.  Both take the window order as an
argument, so nothing here is fixed to one manuscript: a problem registers an
order, applies these, and discharges the resulting equation by kernel `decide`
over the powerset of *its* order.

That is where a count like `lem:labels`' `|Labels| = 399` is proved -- at the
problem, against the problem's registered order and the forbidden differences
its own target derives.  No count, order, or difference appears in this file.

## What is retrieved

* `WindowCurvature.Labels` from `Graph/WindowCurvatureAlgebra.lean`.
-/

namespace Hypostructure.Graph.WindowCurvature

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The legal labels of a given size.

*Provenance.* Follows `Graph.TypeBMarkedFan.compatibleParts` at
`Graph/TypeBMarkedFan.lean:338`.
-/
def labelsOfSize (order size : Nat) : Finset (Label order) :=
  (Labels order).filter fun label => label.card = size

/-- The size distribution of the legal labels, indexed by size `1, 2, …`.  The
list is as long as the order, which is a complete range of possible sizes: a
label is a set of coordinates, so it has at most `order` of them.

*Provenance.* Follows the `(List.range _).map` enumeration at
`Graph/Strategy/Official/Features/PackedResponseOverload.lean:230`.
-/
def sizeDistribution (order : Nat) : List Nat :=
  (List.range order).map fun index => (labelsOfSize order (index + 1)).card

end Hypostructure.Graph.WindowCurvature
