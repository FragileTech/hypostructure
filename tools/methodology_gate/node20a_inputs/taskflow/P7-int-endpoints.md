P7-int-endpoints — integration audit of accepted P6-S1-endpoints.

Result: SUBMITTED_RESULT. On pinned branch `node20a-stage3b-S1@7d3186b`, the accepted child-3 exports match the assigned endpoint obligation on the retained tuple and preserve the complete residual. No mismatch or missing inference was found in this integration check. This is an audit of the accepted result, with no new mathematical inference, implementation, publication, or branch-closure claim.

For the citations below, C3 denotes `tools/methodology_gate/node20a_inputs/taskflow/S1child3.lean`; C2 denotes `tools/methodology_gate/node20a_inputs/taskflow/S1child2.lean`; context denotes `tools/methodology_gate/node20a_inputs/taskflow/stage3b-context.md`; residual denotes `tools/methodology_gate/node20a_inputs/residual-record.md`; admission denotes `tools/methodology_gate/node20a_inputs/taskflow/P5-admission.md`. Line numbers refer to the supplied pinned files.

The exact assigned child is context §3, line 73:

> 3. **Make its exact endpoints active common labels.** For that same lifted q, use its first and last edges to provide a P-neighbour at a and b. Apply reading-count positivity and f115 on the fixed coordinates, swapping the roles only according to w.Orientation P N. Conclude both labels belong to A intersect B and have positive equal counts in those two readings. This closes S1 on the fixed tuple, without a realization of O or either reading.

The endpoint predicates are in namespace `Hypostructure.Graph.S1child3`. C3:625–632 states exactly:

```lean
structure ActiveCommonLabel {data : Parameters} {G : FiniteObject.{u}}
    (w : SparseTargetDefectWitness data G)
    (b : (SupportAtom.boundary G w.support).Vertex) : Prop where
  mem_common : b.1 ∈ sparseDeclaredSupport data G w.first ∩
    sparseDeclaredSupport data G w.second
  first_pos : 0 < w.count w.first b
  second_pos : 0 < w.count w.second b
  counts_eq : w.count w.first b = w.count w.second b
```

C3:658–674 ties the endpoint claims to the supplied dependent lift exactly:

```lean
structure ActiveEndpoints {data : Parameters} {G : FiniteObject.{u}}
    (w : SparseTargetDefectWitness data G) {P : Finset G.Vertex}
    {c : CycleCertificate (glue (SupportAtom.retainedPiece G w.support P) w.outside)
      data.LengthOK}
    {pr : (SupportAtom.boundary G w.support).Vertex ⊕ SupportAtom.PieceInternal G w.support}
    (I : BoundaryInterval c
      (pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr))
    (lift : PositiveLift I) : Prop where
  first_neighbour_mem : SupportAtom.pieceDecode G w.support (lift.walk.getVert 1) ∈ P
  first_adj : G.graph.Adj I.a.1
    (SupportAtom.pieceDecode G w.support (lift.walk.getVert 1))
  last_neighbour_mem : SupportAtom.pieceDecode G w.support
    (lift.walk.getVert (lift.walk.length - 1)) ∈ P
  last_adj : G.graph.Adj I.b.1
    (SupportAtom.pieceDecode G w.support (lift.walk.getVert (lift.walk.length - 1)))
  a_active : ActiveCommonLabel w I.a
  b_active : ActiveCommonLabel w I.b
```

Thus the neighbours are the decodings of vertices `1` and `lift.walk.length - 1` of the same walk. The accepted `endpoints_of_lift` (C3:678–703) has inputs `w`, `counts : WitnessReadingCountsAtWitness w`, `orientation : w.Orientation P N`, the original-domain `c`, the supplied `pr`, `I`, and `lift : PositiveLift I`, and conclusion `ActiveEndpoints w I lift`. Its first/last retained edges are obtained at C3:688–699 using `lift.length_two`. The accepted `active_of_retained_neighbour` (C3:636–654) uses retained adjacency, decoded-support membership and reading-count positivity, then the two cases of `orientation` to apply the appropriate f115 membership transfer. Both cases return counts on `w.first` and `w.second` in that fixed order. This is precisely the requested endpoint inference. The relevant domains are explicit in `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean`: count and Orientation at 111–122, and the equality and two transfers in `WitnessReadingCountsAtWitness` at 190–208.

The fixed-tuple residual entry point is `Hypostructure.Graph.S1child3.endpoints_on_residual` (C3:710–742). Its explicit inputs retain `selected`, `residual : Node20aOutcome selected`, `w`, its canonical some-equality and Spec, `P,N`, orientation, separation, private-edge universal, original `c`, supplied `pl,pr` with the complete f118 conjunction, and the very `I` and `lift`. Its return type at C3:735–736 is exactly:

```lean
    (lift : PositiveLift I) :
    Node20aOutcome selected ∧ ActiveEndpoints w I lift
```

Here `G = selected.object`, `data = spineData.toParameters`, `Z = w.support` and `O = w.outside` throughout. The certificate binder at C3:717–719 is exactly `CycleCertificate (glue (SupportAtom.retainedPiece selected.object w.support P) w.outside) spineData.toParameters.LengthOK`. The supplied conjunction at C3:722–732 preserves the embedded edge in `c.walk.edges`, decoded adjacency, both decoded vertices in P, and `y = SupportAtom.pieceDecode selected.object w.support pr` outside N and the cut boundary. The interval binder at C3:733–734 is indexed by this same c and embedded pr. No realization hypothesis for O or a reading is added.

C3:737–742 reads f115 from the complete residual and identifies its witness by the exact equality

```lean
  have same : w' = w := Option.some.inj (canonical'.symm.trans canonical)
```

It then returns `⟨residual, endpoints_of_lift w counts orientation I lift⟩`. Canonical identification is equality of the already retained witness, not a new object or domain. The underscored Spec, separation, private and supplied binders remain inputs even though the local endpoint deduction needs only f115, orientation and the accepted lift. The aggregate export below retains those data explicitly for the consumer.

C3:746–761 gives the exact consumer package:

```lean
def CyclesHaveActiveFirstContacts {data : Parameters} {G : FiniteObject.{u}}
    (w : SparseTargetDefectWitness data G) (P N : Finset G.Vertex) : Prop :=
  ∀ c : CycleCertificate (glue (SupportAtom.retainedPiece G w.support P) w.outside)
      data.LengthOK,
    ∃ pl pr : (SupportAtom.boundary G w.support).Vertex ⊕ SupportAtom.PieceInternal G w.support,
      (s(pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pl,
         pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr) ∈ c.walk.edges ∧
       G.graph.Adj (SupportAtom.pieceDecode G w.support pl)
         (SupportAtom.pieceDecode G w.support pr) ∧
       SupportAtom.pieceDecode G w.support pl ∈ P ∧
       SupportAtom.pieceDecode G w.support pr ∈ P ∧
       SupportAtom.pieceDecode G w.support pr ∉ N ∧
       SupportAtom.pieceDecode G w.support pr ∉ SupportAtom.cutBoundary G w.support) ∧
      ∃ I : BoundaryInterval c
        (pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr),
        ∃ lift : PositiveLift I, ActiveEndpoints w I lift
```

The final export, including its witness-preserving composition, is C3:767–784:

```lean
theorem node20a_active_firstContacts {selected : EGInput.{u}}
    (residual : Node20aOutcome selected) :
    Node20aOutcome selected ∧
    ∃ w : SparseTargetDefectWitness spineData.{u}.toParameters selected.object,
      sparseTargetDefectWitness spineData.{u}.toParameters selected.object = some w ∧ w.Spec ∧
      ∃ P N : Finset selected.object.Vertex,
        w.Orientation P N ∧ w.Separates P N ∧ w.CyclesUsePrivateEdge P N ∧
        ¬ ((SupportAtom.retainedPiece selected.object w.support P).graph ≤
          (SupportAtom.retainedPiece selected.object w.support N).graph) ∧
        CyclesHaveActiveFirstContacts w P N := by
  obtain ⟨kept, w, canonical, spec, P, N, orientation, separates, privateEdge,
    notLe, contacts⟩ := S1child2.node20a_lift_firstContacts residual
  refine ⟨kept, w, canonical, spec, P, N, orientation, separates, privateEdge, notLe, ?_⟩
  intro c
  obtain ⟨pl, pr, supplied, I, ⟨lift⟩⟩ := contacts c
  exact ⟨pl, pr, supplied, I, lift,
    (endpoints_on_residual kept w canonical spec orientation separates privateEdge
      c pl pr supplied I lift).2⟩
```

The provenance of the fixed tuple is visible in the accepted dependency: C3:346–359 binds w from f021, identifies the f118 witness by canonical some-equalities, takes `pl,pr,supplied` from `privateEdge c`, and passes them to child 1. C2:596–603 passes the same data and interval to child 2. C3:777–784 takes the resulting `kept,w,P,N,pl,pr,I,lift` and repackages them unchanged with `ActiveEndpoints w I lift`. In particular, the final existential export does not assert uniqueness of P,N or of private-edge witnesses; when these are already bound, `endpoints_on_residual` is the exact entry point that accepts them as inputs. No equality between independently chosen orientations or occurrences is needed or asserted.

The consumer therefore receives the complete residual and the canonical w with Spec, the retained orientation and separation, the f118 private-edge universal and retained-piece non-inclusion, and for every original positive c the full f118 edge data together with one dependent interval/lift/activity package. The interval retains distinct first contacts, the proper simple q and complementary r, the exact rotation equality and length partition, the strictly internal occurrence of embedded pr, and absence of internal boundary labels (C3:179–199). The lift retains piece ownership, equality of its mapped walk with I.q, vertex and edge order, length at least two, the same private index and decoded y, injective decoding, and all decoded vertices in P subset Z (C2 and C3:422–448). The endpoint predicates above add the requested first/last neighbours and active common labels at I.a and I.b. These are dependent witnesses, not three independently chosen passages.

There is no further S1 child listed after child 3 in context §3:67–75. The specified next consumer is the Stage 3b owner-local S1 publication, specifically `claim_projections[S1].declaration` (context §2:42–52; admission:25–33). It receives the accepted extraction, lift and endpoint assertions together on each original certificate. If that owner has already bound its tuple in its f021/f118 eliminations, it can consume the fixed-tuple endpoint theorem above on its retained child-2 lift; the existential corollary provides the packaged S1 data from the complete residual. This audit records that interface and does not implement the owner-local row.

The full conjunction is retained as the first output of both residual exports. `endpoints_on_residual` returns the original `residual` directly (C3:742), and `node20a_active_firstContacts` returns `kept` unchanged from the accepted child-2 export (C3:777–779). The accepted prefix returns the original residual at C3:354 and carries it through C2:596–598. The retained type is exactly the 128-conjunct `Node20aOutcome selected` in residual:25–281, with the full key inventory at 288–415. Hence f001 selection minimality and target exclusion (residual:419–434), f021, f029, f115, f118, all other facts, independent witnesses and exclusions remain available at the same selected G. The unchanged separation includes the negative-gluing cycle exclusion (`SparseExitReadings.lean`:124–130); the final export also retains the f118 non-inclusion at C3:774–775. No account is added or altered; the assignment's account list remains empty. There is no representation or domain change requiring transport.

The consumer's remaining owner-local FactInputs elimination, S2–S3 and weakest-case projections, single ExactLedger publication preserving every inherited key, and locked kernel check remain the Stage 3b requirements stated in context §2 and admission:33. They are not performed or assigned here. The endpoint result adds no exactly-two-label, whole-reading, high-centre, refined-spectrum, or context-realization restriction, so it does not exclude the retained weakest case described in context:87 and admission:37. No assertion about transferring the complementary arc is added. Accepted Stages 1–3, the open outcome, and the branch endpoint remain unchanged.

All 10 files in this assignment's source manifest match their SHA-256 values. C2 is a byte-for-byte prefix of C3 (31,392 bytes, 610 lines), confirming the accepted dependency was retained. P6-S1-endpoints supplies the accepted kernel-check and axiom-audit evidence for C3; its four new audit commands are at C3:788–791. This audit reuses that accepted evidence and performs no new Lean compilation. Its implementation_status is therefore `none`. No missing integration inference or immediate subobligation is recorded.
