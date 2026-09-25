# Installed source-bound predicate: same-witness integration

Result: **SUBMITTED_RESULT** for P7-window-99-integrate-source-bound-predicate on revision `node144-window-32d32f9d19e7`. The installed predicate implies the former handoff proposition and the existing [65] third alternative on identical witnesses. This is a mathematical audit of the literal binders, not an implemented projection theorem or an owner construction. There is no missing schema substitution. Production of the stronger value remains pending; no move, arm, or branch is declared closed.

All eleven source-manifest hashes in `/input/assignment.json` were checked and matched. The P6 kernel check is accepted evidence for the vocabulary declaration only. No Lean source was changed or compiled in this audit; implementation status is `none`.

## Fixed conjunction and binders

Work on the complete pinned window residual with `data = spineData` and `G = selected.object`. Preserve all 50 keys, their domains, no-target-cycle exclusion, both selection minimalities, strict surplus, and all quantitative accounts. The inference below is conditional on an inhabitant `H` of the installed `SameTokenTypeBHandoffStatement data G` (SpineVocabulary.lean:4067–4198). Merely changing that definition does not prove that the existing owner returns such an inhabitant.

Unfold only its local `armEdges`, `coreEdges`, `firstEntry`, `configuration`, `valid`, `routed`, and `sourceEnvelope` expressions as needed. Its outer elimination is, in binder order,

```text
⟨active, capacity, activationEq, cubic, certified, token, role,
  tokenMem, positive, multiplicity, coarse,
  sourceClass, sourceClassEq, root, rootEq, structured⟩.
```

Here `cubic : data.threshold = 3`, `ledger := certified.ledger`, and

```text
L := Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
       (Graph.WindowCurvature.Label data.windowOrder)
Q := Graph.SameTokenBlockerRoles.geometricPatternBound data.routingLabelBound.
```

`positive` is exactly `0 < ledger.presented.coupledExcess ledger.presented.tokenClass (fun _ => Q)`. `multiplicity` is exactly that coupled excess bounded above by

```text
Graph.SameTokenBlockerRoles.sameTokenRoleBound * ledger.presented.tokens.card *
  ledger.presented.roleFibreExcess ledger.presented.tokenClass
    (fun _ => Q) token role.
```

`coarse` is the independent coarse matching-or-star disjunction with bound `Graph.PatternFamily.patternThreshold (ledger.presented.roleFibre token role).card`. It is not identified with the routed pattern. The routed cardinality bound is separately `Graph.SameTokenRoutingGerms.patternBound L ≤ pattern.card`.

All these witnesses are handoff witnesses. No equality is inferred with `active_a, capacity_a` in the class audit or `active_t, capacity_t` in the capacity-token ledger. The projected envelope packing will be `capacity.packing` because this installed source-envelope binder already has that dependent type, not because two formerly independent existential witnesses can be equated.

## Literal projection in every pattern alternative

These are proof expressions in the displayed context, with the installed local lets unfolded; they are not claims of new kernel-checked declarations. Split `structured` in exactly its two alternatives:

```text
matching: ⟨P, subset, shape, routedP, sourceP⟩
star:     ⟨centre, P, subset, shape, routedP, sourceP⟩.
```

In either case `routedP = ⟨large, configurations⟩`. For every `pair ∈ P`, `configurations` retains its same `responseSupport`, proof `capacity.activation.pairSupport pair = some responseSupport`, and every `demand ∈ pair` retains its same route. The installed `configuration pair demand` unfolds to

```text
Graph.SameTokenRoutingGerms.RoutingConfiguration G
  (capacity.sameTokenRoutingSupport token pair)
  (Graph.CapacityPresentation.tokenSupport token)
  (capacity.activation.localBuffer demand),
```

and `valid pair demand route` unfolds to `route.path.head? = some root ∧ route.path.getLast? = some demand.2`. These are precisely the types and endpoint conjunction in ObjectCapacityLedger.lean:623–677; there is no transport of a routing support or route.

Define the old routed disjunct by the following literal reconstructions:

```text
RM := Or.inl ⟨P, subset, shape, routedP.1, routedP.2⟩
RS := Or.inr ⟨centre, P, subset, shape, routedP.1, routedP.2⟩.
```

If the coarse alternative is matching, write its unchanged value as

```text
CM := Or.inl ⟨P0, subset0, matching0, threshold0⟩;
```

if it is star, write its unchanged value as

```text
CS := Or.inr ⟨centre0, P0, subset0, star0, threshold0⟩.
```

For any applicable `C` and `R`, the old homogeneous statement is the tuple

```text
B(C,R) := ⟨certified, token, role, tokenMem, positive, multiplicity,
             C, sourceClass, sourceClassEq, root, rootEq, R⟩.
```

Thus the exhaustive four cases are:

| Coarse alternative | Routed alternative | Old homogeneous witness | Envelope source |
| --- | --- | --- | --- |
| matching | matching | `B(CM,RM)` | this matching arm's `sourceP` |
| matching | star | `B(CM,RS)` | this star arm's `sourceP` |
| star | matching | `B(CS,RM)` | this matching arm's `sourceP` |
| star | star | `B(CS,RS)` | this star arm's `sourceP` |

This preserves coarse centres and patterns independently of routed centres and patterns, as well as both bounds. In particular neither matching nor star requires inventing a new coarse pattern or selecting another pair.

In each row, eliminate that very `sourceP` in the installed order:

```text
⟨p, hp, q, hq, differentPairs, dp, hdp, dq, hdq, equalLabel,
  rp, rq, validP, validQ, maximum,
  h, a, b, common, tailP, tailQ, splitP, splitQ, different,
  armP, armQ, firstP, firstQ,
  adjP, adjQ, issuedP, issuedQ, chainP, chainQ, nodupP, nodupQ,
  landsP, landsQ, interiorP, interiorQ, high, avoids, denied, deniedSwap,
  envelope, envelopeEq, z, zMem, x, adjacent, xNeH, outside⟩.
```

The actual equality `equalLabel` has all the retained arguments:

```text
sameTokenActualRoutingLabel data G active cubic capacity certified
  token role P subset p hp dp hdp
 = sameTokenActualRoutingLabel data G active cubic capacity certified
  token role P subset q hq dq hdq.
```

Set `Y := ({dp.2, dq.2} : Finset G.Vertex)`. The installed `envelopeEq` identifies `envelope` with `Graph.DecoratedHandoff.envelopeOfFirstSeparator Y h a b different adjP adjQ armP armQ issuedP issuedQ chainP chainQ nodupP nodupQ landsP landsQ interiorP interiorQ high avoids denied deniedSwap`. The constructor's `core := support` and `decorations := {separator}` fields (DecoratedHandoffEnvelope.lean:1115 onward) give, by this equality,

```text
eCore : envelope.core = Y
eDecorations : envelope.decorations = {h}
eNonempty : envelope.decorations.Nonempty.
```

For example the first two are obtained by `congrArg` of the corresponding field on `envelopeEq`, followed by constructor reduction; `h` witnesses the third. This is exactly the accepted schema projection, now at the actual constructor arguments, with no new structural proof.

Use the single envelope witness

```text
E := ⟨capacity.packing, capacity.packingValid, capacity.packingMaximal,
       Y, envelope, eCore, eNonempty⟩
     : SameTokenTypeBHandoffEnvelopeStatement data G.
```

The stored packing fields have precisely the validity and cardinality-equals-windowPackingNumber types needed here (ObjectCapacityLedger.lean:75–81). For each of the four rows above the former handoff proposition, as recorded in the historical vocabulary snapshot, is inhabited by

```text
⟨active, capacity, activationEq, B(C,R), E⟩.
```

This is a projection to the historical formula, not an application of the now-strengthened declaration to its old argument list. The [65] `TypeBFanEntryStatement` is inhabited by `Or.inr (Or.inr E)` (SpineVocabulary.lean:4206–4212). The unchanged `bottleneckRouting` value is inhabited by `⟨active, capacity, activationEq, B(C,R), Or.inr E⟩` (11920–11942). These projections are made together from one elimination of `H`, so their packing, core, and envelope are identical. Forgetting source fields for the old types does not alter them in `H` or spend a residual account.

## Exact publication changes, not executed

The installed definition is present. The owner and consumer in the pinned HomogeneousBottleneckRows.lean still express the old publication interface.

In `sameTokenBottleneckRoutingRow` (593 onward), `routing` currently starts with the old tuple at line 640; `concretePattern` is opened at 873–875 into the certified token, role, positive excess, multiplicity, coarse pattern, source class, root, and `structured`. Retain these facts for the strengthened result, including the fields currently named with leading underscores. Within the existing matching/star split at 1758, retain each `patternSubset`, `patternShape`, `large`, and `configurations`. The needed output of this local work is a proof of the installed nested predicate with outer tuple

```text
⟨active, capacity, activationEq, cubic, certified, token, role,
  tokenMem, positive, multiplicity, coarse, sourceClass, sourceClassEq,
  root, rootEq, Or.inl ⟨pattern, patternSubset, patternShape,
                       ⟨large, configurations⟩, sourceEnvelopeProof⟩⟩
```

or the corresponding `Or.inr ⟨centre, pattern, patternSubset, patternShape, ⟨large, configurations⟩, sourceEnvelopeProof⟩`. Here `sourceEnvelopeProof` must inhabit every binder listed above on that selected source. It cannot merely be the generic envelope returned by `handoff_of_envelope` (1048–1057). It must retain universal maximum-common-prefix comparison over the fixed pair-specific configuration types, first-entry arms, all constructor arguments, and the final `z, x, adjacent, xNeH, outside` on this same envelope. The skeleton in `outside` is literally

```text
((armEdges (envelope.arm h a) ∪ armEdges (envelope.arm h b) ∪
   {s(h,a), s(h,b)}) ∪ coreEdges envelope.core).
```

Publishing an unrelated escape or rechoosing an envelope is insufficient. The existing local `outsideSkeletonReturn` alone is not the installed source-bound tuple.

At 3908–3913 the owner currently destructures `routing.down` as `⟨active, capacity, activationEq, pattern, outcome⟩`, eliminates a sparse exit using `active.survives`, and attempts the obsolete five-field handoff tuple. That final conversion cannot recover erased source/extremality/escape data. The owner must retain the strong witness before forgetting fields, return it as `K.typeBHandoff`, and derive the old `K.bottleneckRouting` right alternative by the same-witness projection above. Retain the accepted sparse-exit exclusion where the owner handles that alternative; do not infer the stronger witness by inverting generic routing.

At 3922–3941, `sameTokenTypeBFanEntryRow` must replace the old five-field destructuring `⟨_active, _capacity, _activationEq, _pattern, envelope⟩` by the installed outer elimination, split the routed matching/star alternative, and open its `sourceEnvelope` to obtain `E` as above, then return `Or.inr (Or.inr E)`. A proved projection helper can encapsulate this exact elimination. Its `Requires` and `Produces` keys need no change. This audit specifies these changes without implementing them or claiming an owner/root build.

The one precise pending producer obligation is: from the current `sameTokenBottleneckRoutingRow` input conjunction on `inputs.current.object`, construct the installed `SameTokenTypeBHandoffStatement data inputs.current.object` using the owner's single certified token/role and its routed matching or star witness, with its selected equal-label pair and demands, maximum routes on the fixed supports, constructor envelope, and physical non-skeleton escape, and publish the old routing payload only by projecting this same witness. This is an identified obligation, not a theorem proved by this integration audit and not a new task executed here.

## Retained transport, payoff, and Phase 7 tests

P7-window-98 and window-routing-label-transport.md supply the exact identity between `sameTokenActualRoutingLabel` and the owner-local label on `subset, hp, hq, hdp, hdq`, with retained cubic equality. Their seven-coordinate identity preserves the actual induced-degree profiles, ordered supports, and selected endpoint. Apply that accepted transport to this exact `equalLabel`; do not rerun pair selection or posit arbitrary profiles. The accepted fixed-support extremal payoff is cited from window-reduction-acceptance.json and the accepted schema integration: parallel is excluded by retained survival, and all-in-skeleton occupancy contradicts maximal common prefix using cubic neighbours. This audit neither reproves those implications nor declares those arms closed. The installed universal maximum has precisely the two fixed configuration domains required by that accepted payoff.

Constraint test: an inhabitant of the installed predicate supplies one source-bound envelope with the displayed escaping edge and thereby excludes all-in-skeleton occupancy for that witness. Definition installation alone supplies no inhabitant or new graph restriction on the prior returned residual; the owner remains pending. No restriction on every source-pattern edge, all envelopes, or all original demands is obtained.

Compression test: the predicate and its projection make no quotient, replacement, injection, target-complete reading, or smaller graph. Neither registered minimality is newly applied. An ordinary physical escape is not a compression certificate.

Quantity test: `positive`, `multiplicity`, token membership, coarse threshold, routed `patternBound L`, and packing maximality survive literally. The existential escape adds no demand-per-envelope multiplicity bound, coverage theorem, cycle-rank payment, homogeneous cap, global surplus estimate, or near-cubic estimate. Strict surplus and `2m = 3n + s` remain unchanged. No account is spent or credited and there is no move credit.

Side observations, not followed: the escaping edge's internal/exterior continuation is outside this audit; demand multiplicity and target-complete compression remain separate missing ingredients for broader payoffs. The historic weak handoff cannot be inverted by this projection. The vocabulary-only kernel check does not certify the unchanged producer and consumer against their new interface. No source or representation change, cross-key witness identification, negative-arm selection, or branch closure is made here.
