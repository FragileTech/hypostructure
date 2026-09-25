# Exact routing-label substitution in the source-bound schema

Result: **SUBMITTED_RESULT** for P7-window-98-integrate-actual-routing-label, on revision `node144-window-32d32f9d19e7`. This is a mathematical schema integration using the accepted P1-window-97 transport proof, not a new implementation or kernel check.

## Scope and exact substitution

Keep the complete pinned 50-key window residual on `G = selected.object`, with `data = spineData` and `cubic : data.threshold = 3` from its registered baseline. Fix the identical handoff witnesses `active_h, capacity_h, certified_h, token_h, role_h`. Inside the routed matching or star arm of the accepted P6-window-27 schema, let `P = pattern_h` and retain

```text
H : P ⊆ certified_h.ledger.presented.roleFibre token_h role_h.
```

This is the routed pattern, not the earlier coarse threshold pattern. All activation equalities, token membership, source-class and root equalities, quantitative inequalities, pattern shape, cardinality bounds and routed-response clauses stay exactly as in that schema. In particular the routed cardinality clause is `SameTokenRoutingGerms.patternBound L ≤ P.card`, with the same existing label type

```text
L = SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
      (WindowCurvature.Label data.windowOrder).
```

`data.BoundaryProfile` is `Fin data.threshold → Fin data.threshold`; the named label has this identical codomain. No alphabet, bound, coarse pattern, or routed pattern is replaced.

For `e ∈ P` and `d ∈ e`, abbreviate the following expression, with its displayed membership proofs supplied from those same binders:

```text
A(e, he, d, hd) :=
  sameTokenActualRoutingLabel data G active_h cubic capacity_h certified_h
    token_h role_h P H e he d hd.
```

Let `O(e, hc, d)` be the owner-local `routingLabel` instantiated with `G`, `active_h`, `capacity_h`, `token_h`, and `capacity_h.activation`, as in the accepted transport audit. That audit supplies, without a new proof here,

```text
A(e, he, d, hd) = O(e, hc, d)       (hc : e.card = 2).
```

The cardinality proofs are available on precisely this retained pattern domain. No equality outside that domain is used.

The sole substitution in `SourceEnvelope(P)` is therefore

```text
O(p, hc_p, d_p) = O(q, hc_q, d_q)
                       ↕
A(p, hp, d_p, hdp) = A(q, hq, d_q, hdq),
```

under the unchanged binders `p ∈ P`, `q ∈ P`, `p ≠ q`, `d_p ∈ p`, and `d_q ∈ q`. To prove the displayed equivalence, write the two accepted identities as `T_p : A_p = O_p` and `T_q : A_q = O_q`. An old equality `E` gives `T_p.trans (E.trans T_q.symm)`; a new equality `E'` gives `T_p.symm.trans (E'.trans T_q)`. This uses the transport result, without reproving its profile analysis.

Consequently, for every fixed admissible witness tuple, the old and new source-envelope clauses are equivalent. Conjoining their identical remaining clauses and retaining their identical nested existential binders gives equivalence of the two proposed source-bound schemas, under the full residual. The witness transformation is the identity on all data: only the proof of the equal-label clause changes. No pigeonhole selection or other choice is rerun. Thus the existing selected pair is preserved, even if other equal-label pairs also exist.

## Supports, profiles and extremality

For each `e = p,q` with its selected demand `d_e`, both schemas retain exactly

```text
R_e = RoutingConfiguration G
        (capacity_h.sameTokenRoutingSupport token_h e)
        (CapacityPresentation.tokenSupport token_h)
        (capacity_h.activation.localBuffer d_e),
Valid_e(r) := r.path.head? = some ρ ∧ r.path.getLast? = some d_e.2,
ρ = CapacityPresentation.tokenRoot token_h.
```

The transport supplies coordinate-for-coordinate equality, including the true induced-degree profiles on the same ordered surplus-port supports. No profile values, support orders, or selected endpoint coordinates are replaced by bounds or caller-supplied data. In particular the two pair-specific routing supports, common source support, and respective terminal buffers above are unchanged.

The maximality clause still quantifies over every `r'_p : R_p` and `r'_q : R_q` satisfying these same endpoint conditions, and compares their common-prefix length to that of the retained `r_p,r_q`. Neither its domain nor its objective mentions which spelling of the equal-label predicate was used. Every former extremal configuration pair remains the same extremal configuration pair, with the same maximality proof; this does not assert uniqueness or construct a maximum.

Keep the same separator `h`, distinct next neighbours `a,b`, common prefix and suffixes, first-entry arms, `Y = {d_p.2,d_q.2}`, and constructor equality for the same `E = envelopeOfFirstSeparator(...)`. Its packing remains `capacity_h.packing`. The physical support `S`, skeleton `E(F)` and escape clause

```text
∃ z ∈ {a,b}, ∃ x : G.Vertex, Adj_G(z,x) ∧ x ≠ h ∧ {z,x} ∉ E(F)
```

are identical. The accepted same-witness forgetful projection to the old handoff and direct [65] third alternative therefore remains valid, using this same packing, `Y`, and `E`.

This projection is conditional on an inhabitant of the proposed stronger schema. The current weak handoff's independently existential `packing_h, core_h, envelope_h` are not newly equated with source-route data. Nor are the class-audit witnesses `active_a, capacity_a` or capacity-token witnesses `active_t, capacity_t` identified with the handoff witnesses. Naming the label cannot invert the weak handoff projection or build the stronger witness.

## Retained payoff and accounts

The required outcome implications in `window-reduction-acceptance.json` retain their identical inputs: parallel routes are excluded by the retained sparse-exit exclusion; all-in-skeleton occupancy contradicts the fixed-support maximum-common-prefix condition using the cubic assigned neighbours; the surviving escape must be published with that identical source pair, extremal routes and constructed envelope. This substitution neither reconstructs those arguments nor declares an arm or branch closed. It preserves the reviewed conditional reduction and leaves its construction pending.

Constraint: the equivalence imposes no new graph restriction, including no new physical escape fact on the current weak handoff. Compression: there is no quotient, replacement, smaller graph, or new use of minimality. Quantity: the alphabet and all pattern bounds are unchanged; no demand multiplicity bound, cycle-rank payment, cap, or surplus estimate follows from renaming the descriptor. No account is spent or credited. The strict surplus inequality, `2m = 3n + s`, exact ledgers, positive coupled excess, exclusions, no-target-cycle assertion, and both registered minimality conditions remain retained. There is no move credit.

## Exact input for the pending definition

The definition input is the accepted P6 nested formula, in both routed matching and star arms, with the single equal-label clause replaced by the displayed fully instantiated equality of `sameTokenActualRoutingLabel`. Its membership arguments are supplied by `H`, `hp`, `hq`, `hdp`, `hdq` inside those same binders, and its cubic argument by the retained baseline. It accepts no independent label function, profile assignment, alternate capacity, or alternate source tuple. All other fields and binder dependencies, including fixed-support `Valid`, universal `Max`, constructor equality and physical escape on that same envelope, are unchanged.

The single next construction obligation is to express this substituted nested source-bound predicate in the vocabulary, with those exact dependent binders and same-envelope projection interface. It is identified here, not executed. Proving that the owner inhabits that predicate, including extremal-route selection and escape, remains outside this substitution audit. The schema equivalence has no missing inference; the pending construction is not asserted as a consequence of the current weak handoff.

All nine declared source-manifest hashes were verified against `/input/assignment.json`. Evidence: accepted transport audit (displayed identity and preservation); accepted P6 schema (`Routed`, `Max`, `SourceEnvelope` and projection); accepted P7 integration (one-way projection and three tests); reduction acceptance (required structure and outcomes); Phase 0 (common object, window ancestry and accounts); `SpineVocabulary.lean` (`Data.BoundaryProfile`, `sameTokenActualRoutingLabel`, and current handoff definitions); `ObjectCapacityLedger.lean` (`HomogeneousBottleneckPatternStatement`). No source file was modified.
