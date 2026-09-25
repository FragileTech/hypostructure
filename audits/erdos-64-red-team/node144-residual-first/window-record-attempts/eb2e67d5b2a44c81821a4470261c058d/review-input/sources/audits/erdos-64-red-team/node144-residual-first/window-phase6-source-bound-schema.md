# [144a] window history: exact source-bound escape schema

## Scoped proposition

The notation below is a mathematical expansion of the proposed `Holds`
value. Every quantifier is on the **same** selected graph `G`; `L` is the
existing routing-label type, `Q` is its existing geometric pattern bound, and
`P` is a finite set of demand pairs. Define `R(t,e,d)` to be the **existing**
`RoutingConfiguration G (capacity.sameTokenRoutingSupport t e)
(CapacityPresentation.tokenSupport t) (capacity.activation.localBuffer d)`.
For fixed `t,e,d,ρ`, write

```
Valid(t,e,d,ρ,r) := r : R(t,e,d)
  ∧ r.path.head? = some ρ ∧ r.path.getLast? = some d.2.

Routed(P) := P ⊆ ledger.presented.roleFibre t role
  ∧ Q ≤ |P|
  ∧ ∀ e∈P, ∃ responseSupport,
      capacity.activation.pairSupport e = some responseSupport
      ∧ ∀ d∈e, ∃ r, Valid(t,e,d,ρ,r).

Max(r_p,r_q;p,q,d_p,d_q,t,ρ) :=
  ∀ r'_p : R(t,p,d_p), ∀ r'_q : R(t,q,d_q),
    Valid(t,p,d_p,ρ,r'_p) → Valid(t,q,d_q,ρ,r'_q) →
    commonPrefixLength(r'_p.path,r'_q.path)
      ≤ commonPrefixLength(r_p.path,r_q.path).
```

The complete source-bound statement is the following **one** nested
existential. `ThresholdShape` is written out to prevent confusing the first,
coarse pattern disjunction with the later routed pattern `P`:

```
∃ active : ActiveSurplusDemands(G),
∃ capacity : CapacityPresentation(G),
  capacity.activation = recordSparsePairDEBlockers(pairResponseActivation active,
                                                    G.portPairSchedule)
  ∧ ∃ certified : CertifiedObjectCapacityLedger(G,capacity),
    let ledger := certified.ledger;
    ∃ t : ledger.presented.Token, ∃ role : Role,
      t ∈ ledger.presented.tokens
      ∧ 0 < ledger.presented.coupledExcess(tokenClass,Q)
      ∧ ledger.presented.coupledExcess(tokenClass,Q)
          ≤ sameTokenRoleBound * |ledger.presented.tokens|
              * ledger.presented.roleFibreExcess(tokenClass,Q,t,role)
      ∧ ( (∃ P₀ ⊆ ledger.presented.roleFibre t role,
                  IsMatching(P₀) ∧ patternThreshold(|roleFibre(t,role)|) ≤ |P₀|)
          ∨ (∃ c₀, ∃ P₀ ⊆ ledger.presented.roleFibre t role,
                  IsStar(P₀,c₀) ∧ patternThreshold(|roleFibre(t,role)|) ≤ |P₀|) )
      ∧ ∃ sourceClass : TokenClass,
          ledger.presented.tokenClass t = sourceClass
          ∧ ∃ ρ : G.Vertex,
            ρ = CapacityPresentation.tokenRoot t
            ∧ ( (∃ P, IsMatching(P) ∧ Routed(P) ∧ SourceEnvelope(P))
                ∨ (∃ c, ∃ P, IsStar(P,c) ∧ Routed(P)
                                    ∧ SourceEnvelope(P)) ).
```

Here `SourceEnvelope(P)` expands, under **this** routed `P`, as follows:

```
∃ p∈P, ∃ q∈P, p≠q
  ∧ ∃ d_p∈p, ∃ d_q∈q,
      routingLabel(p,d_p) = routingLabel(q,d_q)
      ∧ ∃ r_p : R(t,p,d_p), ∃ r_q : R(t,q,d_q),
          Valid(t,p,d_p,ρ,r_p) ∧ Valid(t,q,d_q,ρ,r_q)
          ∧ Max(r_p,r_q;p,q,d_p,d_q,t,ρ)
          ∧ ∃ h a b common tail_p tail_q,
              r_p.path = common ++ h :: a :: tail_p
              ∧ r_q.path = common ++ h :: b :: tail_q ∧ a≠b
              ∧ ∃ A_p A_q,
                  FirstEntryPrefix(A_p, a::tail_p, {d_p.2,d_q.2})
                  ∧ FirstEntryPrefix(A_q, b::tail_q, {d_p.2,d_q.2})
                  ∧ ∃ E : Envelope(G, capacity.packing),
                      E = envelopeOfFirstSeparator({d_p.2,d_q.2},h,a,b,
                                                    A_p,A_q; constructor proofs)
                      ∧ ∃ z∈{a,b}, ∃ x : G.Vertex,
                          Adj_G(z,x) ∧ x≠h ∧ {z,x}∉E(F).
```

`FirstEntryPrefix(A,r,Y)` means `A<+:r`, `A.head?=r.head?`,
`A.getLast?=some y` for some `y∈Y`, and any `v∈A∩Y` equals `y`.
`constructor proofs` are exactly the adjacency, chain, nodup, landing,
interior, high-centre, target-avoidance, and denied-absorption arguments of
the existing `envelopeOfFirstSeparator`; they are not new assumptions.
`E(F)` is expanded below. The equality identifies the **same** `E` produced
from the maximal routes with the `E` returned by the handoff. All later
projections must eliminate these very binders, without a second `∃ E`.

The strengthened value of the **existing** `K.typeBHandoff` key must be one nested mathematical witness on `G=selected.object`. It begins with the current `active`, `capacity`, `capacity.activation=recordSparsePairDEBlockers(...)`, and certified same-token overload pattern facts. Inside **that same pattern witness**, choose its certified token `t`, role `r`, matching or star `P`, two distinct `p,q∈P` with equal routing label, and the designated selected demands `d_p∈p`, `d_q∈q`. Keep `|P|≥Q_geom+1`, membership in the actual role fibre, the root `ρ=tokenRoot(t)`, and the original activation/presentation equalities. The separate `windowClassOverload` existential stays a separate earlier key.

Next quantify actual configurations `r_p,r_q` with the existing `RoutingConfiguration` type. Require their source to be `tokenSupport(t)`, visited vertices to lie in `sameTokenRoutingSupport(t,p)` and `sameTokenRoutingSupport(t,q)` respectively, common head `ρ`, final vertices `d_p.2,d_q.2`, and final membership in the corresponding `localBuffer`. Require `commonPrefixLength(r_p.path,r_q.path)` to be maximal among **all pairs of configurations with exactly these fixed p,q,d_p,d_q,t,ρ and terminal conditions**. This quantifier may be expressed as a `∀` inequality or a bounded maximality predicate; it must not optimize over a different source pair or change the routing label.

The retained sparse-exit survival eliminates `Parallel(r_p.path,r_q.path)` and supplies their first separator `h`, distinct next neighbours `a,b`, and suffixes. Set **this** `Y={d_p.2,d_q.2}` and trim **these** suffixes at first entry into `Y`, yielding arms `P_a,P_b`. Require the same envelope `E` to equal `envelopeOfFirstSeparator(Y,h,a,b,P_a,P_b,...)`; equivalently retain all of the constructor's defining equalities together with its arm proofs. In particular `E.core=Y`, `E.decorations={h}`, `E.assigned(h)={a,b}`, and its two arms are `P_a,P_b`. The packing in this witness is `capacity.packing`, with the existing maximality and validity proofs. Equality of the actual envelope is essential: an unrelated `Envelope` existence beside the source route tuple would not record the move.

Define the physical support and skeleton *on this same `E`*:

```
S = Y ∪ {h} ∪ vertices(P_a) ∪ vertices(P_b),
E(F) = E(G[Y]) ∪ {ha,hb} ∪ edges(P_a) ∪ edges(P_b).
```

The new escape field is

```
∃ z∈{a,b}, ∃ x∈V(G), Adj_G(z,x) ∧ x≠h ∧ zx∉E(F).
```

Because `z∈S`, the edge is either in `I=E(G[S])∖E(F)` when `x∈S`, or in `δ_G(S)` when `x∉S`. No distinctness among all four indexed incidences, cycle-rank charge, or original-pair payment is part of this predicate. The source-bound existential retains the same full graph and every inherited key; it strengthens only the value of `typeBHandoff` at [144].

The direct `[65]` projection must return the **same** `capacity.packing`, `Y`, and `E` as an inhabitant of the old `SameTokenTypeBHandoffEnvelopeStatement`, forgetting source routes, extremality and escape. The existing `typeBFanEntry` key remains the third same-token alternative of its current disjunction. The `bottleneckRouting` output may keep its current sparse-exit-or-generic-envelope form, provided the owner constructs it by projecting the **same** stronger witness; it may not generate a second envelope.

This task specifies a value schema, not an implementation or kernel certificate. The next Phase 6 task must install this schema in the current vocabulary and adapt only the [144] owner and direct [65] projection. A proof that merely appends an escape under a separate existential or tests a new independent handoff is inadmissible.

Sources: reviewed `window-phase5-uncrossing-admission.md`; actual `HomogeneousBottleneckPatternStatement` at `hypostructure/Hypostructure/Graph/ObjectCapacityLedger.lean:623–678`; route configuration at `hypostructure/Hypostructure/Graph/SameTokenRoutingGerms.lean:229–246`; owner at `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean:595–640,1370–1535,1844–1950,2195–2222,3075–3115`; old handoff at `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean:3944–3995`.
