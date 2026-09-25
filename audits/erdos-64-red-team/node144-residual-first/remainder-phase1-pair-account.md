# [144] remainder arm: blocked-pair account on one certified ledger

Choose the `capacity_h` and `certified_h` occurring **inside the same**
`typeBHandoff` witness, and put `L = certified_h.ledger.presented`. This choice
also contains the selected role-fibre pattern and the envelope in one
`SameTokenTypeBHandoffStatement`; it makes no identification with existential
capacity witnesses from other `Holds` keys. Let
`s = G.degreeSurplus spineData.threshold`.

The units in this account are original unordered pairs in
`G.portPairSchedule spineData.threshold`. At this one presentation,
`ObjectCapacityLedger.scheduleCard` and
`CapacityTokenLedger.blocked_card_add_free_card` give

```text
|L.blocked| + |L.free| = choose(s, 2).
```

`CapacityTokenLedger.blocked_card_eq_sum_load` and
`load_eq_sum_roleFibre` give an exact partition of blocked pairs by token and
role. `ObjectCapacityLedger.tokens_card_le` gives

```text
|L.tokens| ≤ G.capacityTokenSupply spineData.threshold + s.
```

The same ledger's `sandwich` field bounds `|L.free|` by its
`entropyBudget`. These are existing credits and equalities. They do not bound
the individual overloaded role fibre, and they do not convert a decorated
handoff envelope into a payer for any original pair. No pair has been removed
or paid by the [144] handoff. The remaining envelope multiplicity and the
exact charge assigned to it are **unknown**; the available token count cannot
be spent a second time as a load bound.

This check uses only the certified ledger embedded in the handoff witness.
Its source pattern and envelope are co-present in that one proposition, but
the proposition does not give an incidence map from all blocked pairs to
envelopes or centres. Such a map and a bound on its fibres would be a new
mathematical obligation.

Sources: `ObjectCapacityLedger.lean:267–314,344–365,623–682`;
`CapacityTokenLedger.lean:146–171`;
`SpineVocabulary.lean:3961–3995`.
