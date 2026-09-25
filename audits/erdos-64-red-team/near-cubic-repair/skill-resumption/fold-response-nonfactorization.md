# Folded target response is not a function of the original target response

This rejects one proposed reading construction. It is not a counterexample to
Node [144], whose full residual is much narrower.

Let T be the empty boundary and let R(X) be the function on outside contexts
which says whether X glued to the context has a power-of-two cycle. Let F
identify two fixed marked nonadjacent vertices and simplify the resulting graph.
There is no function f on the unrestricted R-value domain satisfying

    f(R(X)) = R(F(X))

for every such marked boundaried graph X.

Proof. Let X be the cycle h-a-c-b-h, marking a,b for identification. Let Y
be a disjoint union of two copies of that cycle, marking a,b in its first copy.
Both already contain a four-cycle, so R(X)=R(Y) is the constantly true function
on every empty-boundary outside context. F(X) is the path h-w-c, hence has no
power-of-two cycle. F(Y) contains the untouched second four-cycle. Evaluating
at the empty outside context therefore gives R(F(X))=false and R(F(Y))=true
at that context. A function f would take the same input to unequal outputs,
which is impossible. Both original boundary-degree profiles are empty. QED.

The source type checked here is PairResponseValue = OutsideContext -> Prop in
SparsePairResponse.lean, and its actual value is the glued target predicate
in pairResponseReading. It is not a graph-valued tuple. Reading.quotientImage
requires an actual function on that source value type. Thus the proposed
shortcut 'use the graph fold as the projection of that response value' is not
a well-defined construction on its unrestricted realization domain.

This does not rule out a different quotient, a richer declared product with
proved reading semantics, or a construction on a separately justified restricted
domain. Such a repair must construct that exact domain/product and prove its
connection to the retained selected-pair family; it cannot silently replace
PairResponseValue by a graph or treat its support index as a realized graph.
No restriction has been added as a premise to the live residual.

The example's graphs are not minimum-degree-three minimal counterexamples.
They are relevant only to the asserted universal map on the unrestricted
response-value domain. They prove neither the impossibility of the requested
local closure nor the existence of an EG counterexample.
