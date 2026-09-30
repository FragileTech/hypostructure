P7-int-interval — submitted integration audit of accepted P6-S1-interval, on `node20a-stage3b-S1@7d3186b`, move `M-3b-S1`.

The accepted artifact supplies exactly child obligation 1 on the retained tuple. No mismatch or missing inference was found in this integration check. This audit does not supply an adjacent child or assert completion of S1 or the Stage 3b publication.

Citations below use **S** = `tools/methodology_gate/node20a_inputs/taskflow/S1child1.lean`, **C** = `tools/methodology_gate/node20a_inputs/taskflow/stage3b-context.md`, **R** = `tools/methodology_gate/node20a_inputs/residual-record.md`, and **A** = `tools/methodology_gate/node20a_inputs/taskflow/P5-admission.md`. Export names are in namespace `Hypostructure.Graph.S1child1`.

The bound objects are `G = selected.object`, `data = spineData.toParameters`, the f021 witness `w` with its canonical equality and `w.Spec`, `Z = w.support`, `O = w.outside`, and the original coordinates `w.first,w.second` with supports A,B. The retained f118 orientation is `P,N`, with `w.Orientation P N`, `w.Separates P N`, and `w.CyclesUsePrivateEdge P N`. The certificate remains an arbitrary original

```lean
c : CycleCertificate (glue (SupportAtom.retainedPiece G Z P) O) data.LengthOK
```

The supplied `pl,pr` stay in `(SupportAtom.boundary G Z).Vertex ⊕ SupportAtom.PieceInternal G Z`. In particular `y = SupportAtom.pieceDecode G Z pr` is the original decoded endpoint, whereas the occurrence in the glued walk is `x = pieceEmbedding (SupportAtom.retainedPiece G Z P) O pr`. These are the two existing maps on the same `pr`, with their original domains. No decoding or lift of the whole segment is asserted here. [C:61–69; S:279–303; A:17–25.]

For an already bound tuple and supplied endpoints, `firstContacts_on_residual` (S:279–310) takes the complete `residual`, `w`, its canonical equality and Spec, the fixed orientation, separation and private-edge statement, the original `c`, and those `pl,pr`. Its `supplied` premise is exactly the six f118 conjuncts: the embedded edge belongs to `c.walk.edges`; the decoded endpoints are adjacent in G; each is in P; the decoded `pr` is outside N; and it is outside `cutBoundary G Z`. Its conclusion is exactly

```lean
Nonempty (BoundaryInterval c
  (pieceEmbedding (SupportAtom.retainedPiece selected.object w.support P) w.outside pr))
```

There is no existential replacement of an input object in this conclusion. The f118 premise matches `SparseTargetDefectWitness.CyclesUsePrivateEdge` in `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean`:134–148.

The exported interval structure is quoted verbatim from S:176–196:

```lean
structure BoundaryInterval {boundary : Boundary.{u}} {P : BoundaryPiece boundary}
    {O : OutsideContext boundary} {LengthOK : Nat → Prop}
    (c : CycleCertificate (glue P O) LengthOK) (x : GluedVertex P O) where
  a : boundary.Vertex
  b : boundary.Vertex
  distinct : a ≠ b
  a_occurs : Sum.inl a ∈ c.walk.support
  b_occurs : Sum.inl b ∈ c.walk.support
  q : (glue P O).graph.Walk (.inl a) (.inl b)
  r : (glue P O).graph.Walk (.inl b) (.inl a)
  rotation : c.walk.rotate (.inl a) a_occurs = q.append r
  length_partition : q.length + r.length = c.walk.length
  proper : q.length < c.walk.length
  complement_positive : 0 < r.length
  simple : q.IsPath
  private_index : Nat
  private_index_pos : 0 < private_index
  private_index_lt : private_index < q.length
  private_occurrence : q.getVert private_index = x
  no_internal_boundary : ∀ k, 0 < k → k < q.length →
    ∀ z : boundary.Vertex, q.getVert k ≠ Sum.inl z
```

This matches C:69 field by field. `a_occurs`, `b_occurs` and `distinct` give distinct boundary occurrences of the same c. The typed walks and literal `rotation` equality give its contiguous cyclic segment and complementary arc, including wraparound at the original basepoint; `length_partition`, `proper` and `complement_positive` record the requested partition and properness. `private_index_pos`, `private_index_lt` and `private_occurrence` place the supplied embedded pr strictly inside that segment. Together with `no_internal_boundary`, this is precisely the first-contact condition in each direction from that occurrence. `simple` records simplicity of this same q. These are the accepted interval's fields, not a replacement by an arbitrary path or an equal-length certificate. [S:170–196; C:69.]

The supporting exports have compatible domains. `boundaryInterval_of_twoLabels` takes `c`, an occurrence `x`, its nonboundary condition and `DefectGeometry.TwoLabels c`, and returns this same `Nonempty (BoundaryInterval c x)` (S:199–203). `retained_firstContacts` specializes it to the actual embedded pr using the fixed orientation, separation, reading exclusion, original edge membership and internality (S:240–253). The accepted application uses f029 for the positive reading exclusion, the negative side of the same separation for context exclusion, and `DefectGeometry.pieceExclusive` and `realized_mixed` on the same c for two-label existence (S:255–267). The latter theorem requires no realization hypothesis: its type is at `hypostructure/Hypostructure/Graph/TargetDefectStructure.lean`:215–218. f029's canonical witness is identified with the input w by `Option.some.inj`, then the original `c pl pr supplied` is passed through (S:304–310). No new mathematical prerequisite is needed for integration.

The complete residual export, quoted from S:334–342 with its proof omitted, is:

```lean
theorem node20a_firstContacts {selected : EGInput.{u}} (residual : Node20aOutcome selected) :
    Node20aOutcome selected ∧
    ∃ w : SparseTargetDefectWitness spineData.{u}.toParameters selected.object,
      sparseTargetDefectWitness spineData.{u}.toParameters selected.object = some w ∧ w.Spec ∧
      ∃ P N : Finset selected.object.Vertex,
        w.Orientation P N ∧ w.Separates P N ∧ w.CyclesUsePrivateEdge P N ∧
        ¬ ((SupportAtom.retainedPiece selected.object w.support P).graph ≤
          (SupportAtom.retainedPiece selected.object w.support N).graph) ∧
        CyclesHaveFirstContacts w P N
```

Its proof obtains w from f021, identifies the f118 witness with that w by the canonical some-equalities, and keeps the supplied P,N, orientation, separation, private-edge statement and non-inclusion (S:343–351). Its first component is literally the input `residual` in `refine ⟨residual, ...⟩` (S:351). Thus every one of the 128 conjuncts in R:25–281 remains present, including f001 selection minimality, all exclusions and independent witnesses, f022 geometry and f115 counts. The three residual projections select exactly f021, f029 and f118. The theorem does not replace the residual by those dependencies. No account is added or changed; the branch's account list stays empty.

`CyclesHaveFirstContacts w P N` is the precise augmented payload (S:314–328): for every original c in the positive gluing, there exist `pl,pr` with all six original private-edge conclusions, conjoined with `Nonempty (BoundaryInterval c (pieceEmbedding ... pr))` for that same pr. The wrapper introduces c, eliminates `privateEdge c` once and returns `⟨pl, pr, supplied, firstContacts_on_residual ... c pl pr supplied⟩` (S:352–356). The interval and private-edge data are therefore paired witnesses. For a consumer that has already eliminated f118 and bound P,N,pl,pr, the fixed-input export `firstContacts_on_residual` is the interface that preserves those exact bindings; it need not eliminate the wrapper's existentials again.

The next child receives the unchanged residual and tuple, all six supplied edge facts, and an interval `I : BoundaryInterval c (pieceEmbedding ... pr)` obtained by eliminating the returned `Nonempty` in its proof. It can use `I.q`, `I.r`, their exact endpoints, the strict internal index, simplicity, absence of internal boundary occurrences, rotation equality and length partition together. This is a proposition asserting existence, not an exported computational selector. Child 2's input is this very `I.q`. Its positive-piece ownership, lift with preserved vertex and edge order, and injective decoding are the separate obligation stated at C:71. Child 3's active common endpoints remain C:73. Neither has been established by this artifact or this audit. [S:176–196, 279–328; A:25.]

For the Stage 3b owner-local consumer, this is the checked first-contact component needed for `claim_projections[S1].declaration`, to compose dependently with the subsequent children on the same q and its lift. It is not yet that full S1 projection or a FactInputs/ExactLedger publication. Reading and eliminating f021 in the owner-local row, the remaining S1 work, S2–S3 and weakest-case projections, the single structure-fact publication retaining every inherited key, and the locked kernel check remain as specified in C:42–52,75,91–93 and A:31–33. This audit neither executes those tasks nor chooses a next assignment.

The consumer gains no additional domain restriction: the exports assume neither exactly two labels, whole readings, a high private endpoint, a refined spectrum witness, nor realization of O or either reading. The stated weakest-case intersection remains within the original universal certificate domain. The complementary arc remains the original r and may contain further private passages; no transfer to it is asserted. [S:279–342; C:87; A:37.]

All eight files in the assignment's source manifest were checked byte-for-byte by SHA-256 and match their pinned values. The residual definition contains 128 conjuncts, and the displayed projections were checked against their ordered keys. P6-S1-interval's supplied `kernel_checked` evidence, including the successful prescribed Lean command and reported axiom audit, is reused as an accepted prerequisite. This audit introduces no Lean implementation and does not repeat that kernel check; its own `implementation_status` is `none`. No object representation or domain changes, account changes, negative outcome, move closure or branch closure are claimed. There is no first missing inference within this assigned audit, and no immediate subobligations are submitted.
