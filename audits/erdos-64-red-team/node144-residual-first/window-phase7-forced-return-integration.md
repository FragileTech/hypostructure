# [144a] integrate the forced edge return with the attachment account

Work on the selected `G` and one actual matching or star producer, with its fixed equal-label source pair, maximal common-prefix routes, first separator, two trimmed arms, core and envelope. Let `S` be the vertex set of that envelope and `F` its literal edge skeleton. The owner proofs in both producer arms now derive one *same* `e={nextLeft,x}` with `Adj_G(nextLeft,x)`, `e∉F`, and `HasReturn` for `EdgeContraction G nextLeft x`. The new `K.bridgeless` read is the inherited key on `G`; `selectedBottleneckDischarge` passes it through the same `ExactLedger`. Those Lean facts and their direct caller kernel-check. They do not yet occur in `K.typeBHandoff`'s `Holds` value.

The reviewed mathematical integration uses the return path in `G−e`: adding `e` yields a cycle with nonzero `e` coordinate, whereas every cycle of `F` has zero `e` coordinate. Hence `β(G)≥β(F)+1`. This statement is not yet a Lean theorem. It remains true when the other core vertex is isolated in `F`; the accepted component classification is `c(F)∈{1,2}`, not a blanket connectedness claim.

With `I=E(G[S])∖E(F)` and each exterior component `C` having physical boundary count `k_C`, the retained account is

```
β(G)−β(F) = |I| + Σ_C(β(G[C])+k_C−1) − (c(F)−1).
```

The one-cycle return therefore requires `|I|+Σ_C(β(G[C])+k_C−1)≥c(F)`. In the two-component skeleton case, one raw unit may join components and a second unit is needed for the return cycle. The strict-surplus identity gives only `β(F)≤(n+s)/2` from `β(G)=(n+s)/2+1`. These are total costs for this one envelope. Neither `e` nor its return cycle is assigned injectively to every original source pair; repeated use of the same edge or exterior component spends no additional unit.

The three workflow tests are separate. **Constraint:** the owner-local all-in-`F` arrangement is excluded for its extremally chosen producer envelope, and that actual `e` must lie in `I` or cross `δ_G(S)`. **Compression/transport:** no quotient, replacement, or source-bound transport follows from the return path. **Quantity/closure:** there is one relative rank unit, but no retained upper capacity or bounded-multiplicity map consuming all the source pattern's demands, so no homogeneous cap, near-cubic estimate, target cycle, or [144a] closure follows.

The next construction is one source-bound export through the existing `K.typeBHandoff` value: put the selected pattern, fixed pair and demands, maximal routes, first separator, actual envelope, *same* escape edge, and its return in one nested witness. The `K.typeBFanEntry` projection must forget fields from that very witness and keep the same packing/core/envelope. The separately proved endpoint-location and return existentials must be combined on one chosen `x` if both are exported. After that export, analyze the marked return path against the retained target avoidance and fan safety, including its route through core, opposite arm or exterior components. Any multiplicity or cycle conclusion requires a further proof on that marked path.
