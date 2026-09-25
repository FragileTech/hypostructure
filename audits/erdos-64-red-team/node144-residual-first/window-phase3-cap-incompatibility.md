# [144] window arm: positive pattern versus fixed caps (Phase 3)

On the tagged window-incidence post-[144] ExactLedger, `typeBHandoff` is a proposition
on `G = selected.object`. Its existential source carries a matching or star
inside one certified ledger's selected token/role fibre of size at least
`SameTokenRoutingGerms.patternBound Label`.

`HomogeneousCapsHold G ... Label` universally forbids such a matching and
forbids such a star in **every** capacity presentation and ledger on `G`.
The anonymous Lean proof in `CapCheck.lean` checks the exact implication

```text
SameTokenTypeBHandoffStatement data G
  → ¬ HomogeneousCapsHold G data.threshold data.windowOrder Label,
```

where `Label` is the routing label in the actual [144] handoff. The Lean
command in `CapCheck.log` exited 0. This is a kernel-checked incompatibility
of two propositions on the same graph, not a proof of the caps.

Thus a derivation of fixed caps from all retained facts of this window arm
would yield `False` and close the arm. The current returned ledger instead
contains the positive source pattern and decorated envelope; it does not
contain the caps. The remaining mathematical obligation is a contradiction
from these retained facts, whether by establishing caps or by some different
cycle/replacement argument. No fact from the near-cubic sibling is used.

Sources: `SpineVocabulary.lean:3944–3979` and
`ObjectCapacityLedger.lean:601–682`; audit proof `CapCheck.lean` and check
log `CapCheck.log`.
