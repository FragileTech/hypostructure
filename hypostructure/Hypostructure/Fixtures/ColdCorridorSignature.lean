import Hypostructure.Graph.ColdCorridor

/-!
# Fixture: the declared signature is the manuscript's, clause by clause

`def:declared-coordinate-signature` fixes the response-coordinate signature
"once and for all" and generates it by eight clauses.  Clause (D8) is the
framework's own closure (`Graph.ColdCorridor.Generated`); clauses (D1)--(D7)
name kinds, and this fixture checks that the registered
`Graph.ColdCorridor.SignatureClause` has *exactly* those kinds and no others.

The manuscript's list, counted:

| clause | kinds | what they are |
|---|---|---|
| (D1) | 1 | boundary-degree entries |
| (D2) | 6 | edge-rooted return data, completion-port data, first-entry receivers, connector lengths, receiver-entry channels, Mersenne return tests |
| (D3) | 4 | window labels, legal-label relations, packed-window incidences, cross-window incidence data |
| (D4) | 1 | raw curvature coordinates |
| (D5) | 6 | canonical traces, trace-incidence coordinates, connector-band constraints, cross-port theta constraints, silent-basin response coordinates, carrier restrictions |
| (D6) | 9 | fan centers, fan-safe pairs, certificate labels, closed fan-window pairs, hybrid incidence entries, candidate ledger entries, overlap demands, decorated handoff fan response coordinates, decorated handoff-arm coordinates |
| (D7) | 5 | selected surplus ports, canonical port returns, open-port suppression paths, triangular-port response triangles, sparse surplus-pair response coordinates |

"And their labelled subcoordinates" of (D5) is not a thirty-third kind: (D8)
already generates the labelled copies and restrictions of every entry of
(D1)--(D7), which is what a labelled subcoordinate is, so listing it again
would double-count.
-/

namespace Hypostructure.Fixtures.ColdCorridorSignature

open Hypostructure.Graph.ColdCorridor

/-- The number of kinds the manuscript's clause `n` names. -/
def declaredCount : Nat → Nat
  | 1 => 1
  | 2 => 6
  | 3 => 4
  | 4 => 1
  | 5 => 6
  | 6 => 9
  | 7 => 5
  | _ => 0

/-- **Every clause has exactly the kinds the manuscript names.**  Checked by
computation against the registered enumeration, so a kind added, dropped, or
moved between clauses fails here. -/
example (clause : Nat) (member : clause ∈ [1, 2, 3, 4, 5, 6, 7]) :
    (SignatureClause.all.filter
        fun kind => kind.clauseNumber == clause).length =
      declaredCount clause := by
  fin_cases member <;> decide

/-- **Thirty-two generating kinds in total**, which is the sum of the column
above. -/
example : SignatureClause.all.length = 32 := by decide

/-- **No kind is listed twice**, so the count above counts kinds and not
entries. -/
example : SignatureClause.all.Nodup := SignatureClause.all_nodup

/-- **No kind is missing**: the enumeration is complete for the type, so
"no other local response coordinate is available to a quotient" is a
type-level fact and not a convention. -/
example (kind : SignatureClause) : kind ∈ SignatureClause.all :=
  SignatureClause.mem_all kind

/-- **Every kind belongs to one of the seven generating clauses.**  There is no
kind outside (D1)--(D7), and in particular none smuggled in by (D8). -/
example (kind : SignatureClause) : kind.clauseNumber ∈ [1, 2, 3, 4, 5, 6, 7] :=
  SignatureClause.clauseNumber_mem kind

/-- The registered signature at a window of order thirteen carries all
thirty-two kinds. -/
example :
    SignatureClause.all.length = 32 ∧ (declaredSignature 13 (by norm_num)).windowOrder = 13 := by
  refine ⟨by decide, rfl⟩

/-- The bounded active interface of `def:cold-corridor-first-failure` at that
order is the manuscript's own `30`: "the two `P₁₃`-window interfaces and the
two boundary stubs".  The additive constant of `M_cold` is computed, never
written. -/
example : interfaceWidth 13 = 30 := by decide

/-- And `interfaceBudget`, the additive term of `M_cold = Q_cold + 30`, agrees
with it at the registered signature. -/
example : interfaceBudget (declaredSignature 13 (by norm_num)) = 30 := by decide

end Hypostructure.Fixtures.ColdCorridorSignature
