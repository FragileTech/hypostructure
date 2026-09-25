# [144] window arm: class of the handoff source token

On the pinned selected graph `G`, let `(capacity_h, certified_h, token_h)`
denote witnesses chosen together from the retained `typeBHandoff` fact. The
coordinate inspected here is
`certified_h.ledger.presented.tokenClass token_h`. It is a token class in the
same capacity presentation as the handoff's positive pattern and declared
configurations.

The retained `windowClassOverload` fact has its own existential certified
ledger and token `(capacity_w, certified_w, token_w)` satisfying
`tokenClass token_w = .windowIncidence`. The `[140]` producer uses that
selected window overload to construct a `HomogeneousBottleneckPatternStatement`.
That statement, however, existentially chooses a source class equal to the
class of its own token; it does not require `.windowIncidence`.
`SameTokenTypeBHandoffStatement` retains such a pattern statement and an
envelope in one proposition, but has no equation identifying its witnesses
with those of `windowClassOverload` or fixing `tokenClass token_h` to the
window class.

Thus window membership of the **handoff source token** is unresolved by the
literal conjunction of retained `Holds` propositions. The window branch
has a producer history that selected a window overload; this inspection
does not replace that history with an equation between separately quantified
witnesses. It does not assert that the handoff token is outside the window
class, and it makes no new restriction or move.

Sources: `ObjectCapacityLedger.lean:514–565,623–682`;
`SpineVocabulary.lean:11475–11568,3944–3995`;
`HomogeneousBottleneckRows.lean:156–285,3080–3112`.
