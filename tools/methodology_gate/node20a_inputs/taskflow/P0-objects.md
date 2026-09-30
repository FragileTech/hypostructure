# P0-objects — retained-object register

Pinned obligation: `node20a-stage3b-S1@7d3186b`. Assume the complete conjunction `Node20aOutcome selected`; every one of its 128 conjuncts remains retained. This register only names its supplied objects and specializes the accepted private-edge statement.

## Object bindings and domains

| Object | Exact binding and domain | Supplying fact / declaration |
| --- | --- | --- |
| `G` | `G := selected.object : Graph.FiniteObject.{u}`, for the existing `selected : EGInput.{u}`. | `Node20aOutcome` header and its fixed interpretation in the residual record; f001, `K .selection`, `SelectionStatement`, retains selection minimality at this very object. |
| `data` | `data := spineData.toParameters : Parameters`. Occurrences of `data.toParameters` in the record's `Holds` descriptions use its vocabulary parameter `spineData`; they do not mean applying `toParameters` again to this local `data`. | Residual record's fixed interpretation of `Holds`; context §(3), fixed-input paragraph. |
| `w` | `w : SparseTargetDefectWitness data G`, with `hw : sparseTargetDefectWitness data G = some w` and `hSpec : w.Spec`. | f021, `K .sparseTargetDefectResidual`, `SparseTargetDefectResidualStatement` (`Statements/SurplusPair.lean:1200–1212`), by existential elimination. |
| `Z` | `Z := w.support : Finset G.Vertex`. | The support projection of the same f021 witness; also used verbatim by f022, `SparseTargetDefectStructureStatement` (`Statements/SurplusPair.lean:1214–1228`). |
| `O` | `O := w.outside`, in the dependent outside-context type of this witness: a context with boundary labels exactly the subtype `{v : G.Vertex // v ∈ SupportAtom.cutBoundary G Z}`. Its internal carrier is the one carried by `w.outside`. | f021 witness's `outside` projection; f022's final argument to `Graph.BoundTargetDefectGeometryAt`; context §(1), `bound_witness`, and §(3). No realization or replacement of this context is introduced. |
| `A`, `B` | `A := sparseDeclaredSupport data G w.first : Finset G.Vertex`; `B := sparseDeclaredSupport data G w.second : Finset G.Vertex`. The arguments remain the witness's original declared coordinates. | f021 witness's `first` and `second` projections and `sparseDeclaredSupport`; f022 displays both exact applications. |
| `P`, `N` | `P, N : Finset G.Vertex`, the pair supplied by f118 at this `w`, with `w.Orientation P N`, `w.Separates P N`, and `w.CyclesUsePrivateEdge P N`. Orientation retains the ordered positive/negative choice of the two declared supports: `(P = A ∧ N = B) ∨ (P = B ∧ N = A)`. Both lie in the retained support `Z`; neither orientation is selected afresh. | f118, `K .positiveCyclePrivateEdge`, `PositiveCyclePrivateEdgeStatement := AtSparseTargetDefectWitness data G PositiveCyclePrivateEdgeAtWitness`; the at-witness declaration is identified in context §(3), evidence, as `Statements/SparseExitReadings.lean:273–287`. |
| `c` | An arbitrary original `c : Graph.CycleCertificate (Graph.glue (SupportAtom.retainedPiece G Z P) O) data.LengthOK`. Its underlying walk is `c.walk` on that exact gluing. | Universal certificate binder in `w.CyclesUsePrivateEdge P N`, supplied by f118; context §(3) explicitly records this specialization and cites `Statements/SparseExitReadings.lean:134–149`. |
| `pl`, `pr` | The endpoints supplied by that specialization at `c`. Their domain is the vertex carrier of `SupportAtom.retainedPiece G Z P`: precisely the domain of `pieceEmbedding (SupportAtom.retainedPiece G Z P) O` and of `SupportAtom.pieceDecode G Z`. They are piece vertices, prior to embedding or decoding. | f118's `CyclesUsePrivateEdge`, specialized to the retained original `c`, as recorded in context §(3). |
| `y` | `y := SupportAtom.pieceDecode G Z pr : G.Vertex`. This is the decoded right endpoint supplied for `c`, with `y ∈ P`, `y ∉ N`, and `y ∉ SupportAtom.cutBoundary G Z`. | The same f118 specialization; `pieceDecode` applied to its actual `pr`, not a separately chosen private vertex. |

The context and piece domains above are given by their exact dependent projections/function domains, without replacing their carriers by ambient `G.Vertex`. In particular the glued occurrence corresponding to `pr` is `pieceEmbedding (SupportAtom.retainedPiece G Z P) O pr`, whereas `y` belongs to `G.Vertex`.

## Identification and certificate-specific retained conclusions

For a witness `w118` unpacked from f118, retain its canonical equality `sparseTargetDefectWitness data G = some w118`. Together with `hw` this gives `some w118 = some w`, hence `w118 = w` by injectivity of `Option.some`. Substitute this equality before retaining `P,N` and specializing the certificate universal. The same argument identifies the canonical witnesses in f022, f029 and f115 whenever their retained facts are read. It is equality substitution at the same witness type, not a change of representation or domain.

For these very `pl,pr`, keep all conclusions recorded for `CyclesUsePrivateEdge`: the unordered edge joining their piece embeddings belongs to `c.walk.edges`; `G.graph.Adj (SupportAtom.pieceDecode G Z pl) y`; `SupportAtom.pieceDecode G Z pl ∈ P`; `y ∈ P`; `y ∉ N`; and `y ∉ SupportAtom.cutBoundary G Z`. These are the supplied conclusions of f118, not consequences inferred from an unrelated ambient edge. The quantifier order is fixed: choose the f021 witness, identify f118 at it, retain its orientation, fix arbitrary original `c`, then eliminate the private-edge existential for that `c`.

## Scope and checks

The only deductions used for registration are conjunction projection, existential elimination, equality substitution using injectivity of `Option.some`, and universal specialization. They supply the complete requested tuple; no missing inference occurs in this registration. Definitions of `Z,O,A,B,y` abbreviate retained objects. No new graph, context, certificate, orientation, account, or ledger key is constructed.

Selection minimality and target avoidance at `G` remain f001 unchanged; f029's local-arm exclusion and all other retained exclusions remain in the full conjunction. The supplied accepted Stage 1–3 evidence remains active. The later nearest-boundary passage, its lift, and S1–S3 publication are outside P0 and are not executed or claimed here. No move or branch is marked closed.

Both declared source SHA-256 digests were checked against the assignment and match. This is a mathematical object register; no Lean implementation or kernel check is claimed.
