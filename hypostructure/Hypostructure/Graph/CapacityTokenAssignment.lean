import Hypostructure.Graph.CapacityTokenUniverse

/-!
# `Θ_cap`: the four-case capacity-token assignment, and `def:same-token-patterns`

`def:capacity-token-ledger` charges a blocked pair `π` to one capacity token by
the canonical rule

> (a) if `supp(B_π)` contains a window--remainder edge, take the least such edge's
>     token `(e, RW) ∈ 𝔗_W`;
> (b) otherwise, if it contains a cross-window edge, take the least such edge and
>     then the least of its two endpoint tokens in `𝔗_W`;
> (c) otherwise, if it contains a vertex `v ∈ R` with `d_G(v) > δ`, take the least
>     such `v`, rank `π` among the pairs that reach this case at `v`, and take the
>     token `(v, 1 + (rk_v(π) mod (d_G(v) − δ))) ∈ 𝔗_R`;
> (d) otherwise, take `κ(B_π) ∈ 𝔗_prim`,

where `B_π = Φ_can(π)` is the canonical blocker of `def:canonical-blocker-ledger`
and `supp(B)` is the declared support of `def:capacity-token-ledger`.

Every ingredient is built here from data the branch already owns.  `Φ_can(π)` is
the canonical first member of `𝖡𝗅𝗄(π)` — the same `Finset` of concrete blocker
objects `def:surplus-blockers` builds — selected by the framework's own
enumeration idiom, the one `Graph/CanonicalSupportSelection` already uses for the
manuscript's "the lexicographically first …".  `supp(B)` and `κ(B)` are the two
clause-by-clause readings the definition gives.  The three geometric candidate
families are the ones `Graph/WindowJoinIdentity` and `Graph/WindowRemainder`
already build, and the fourth case's carrier lands in
`Graph/PrimitiveCarrier`'s `𝔘_sp(G)`.

`Θ_cap` is single-valued because it is a function into `Option`, so
`lem:token-ledger-no-overcount` is `Graph/CanonicalFibreLedger`'s fibre identity
read at the token alphabet — the same identity `def:canonical-blocker-ledger`
already reads, not a second one.  `def:same-token-patterns`' fibre graph `H_t`
is that identity's fibre, and `e(H_t) = ℓ_cap(t)` holds by construction.

Nothing is specialized to one manuscript: the baseline, the window order, the
declared coordinate alphabet and the shoulder-chord alphabet are all parameters.
-/

namespace Hypostructure.Graph

open Hypostructure
open scoped BigOperators

universe u v

/-- The first element of a declared list satisfying a predicate that only one
element satisfies is that element. -/
theorem List.find?_eq_some_of_unique {α : Type*} {list : List α} {predicate : α → Bool}
    {value : α} (member : value ∈ list) (holds : predicate value = true)
    (unique : ∀ other ∈ list, predicate other = true → other = value) :
    list.find? predicate = some value := by
  induction list with
  | nil => cases member
  | cons head tail step =>
    rw [_root_.List.find?_cons]
    by_cases fires : predicate head = true
    · simp only [fires]
      rw [unique head (_root_.List.mem_cons_self ..) fires]
    · simp only [fires]
      refine step ?_ fun other inside => unique other (_root_.List.mem_cons_of_mem _ inside)
      rcases _root_.List.mem_cons.mp member with rfl | inside
      · exact absurd holds fires
      · exact inside

namespace FiniteObject

variable {object : FiniteObject.{u}} {Coordinate Chord : Type v}

/-! ## The fixed vertex order, read off the object's own schedule -/

/-- The position of a vertex in the object's own vertex schedule: the manuscript's
"fixed vertex order". -/
noncomputable def vertexIndex (object : FiniteObject.{u}) (vertex : object.Vertex) :
    Nat :=
  letI : FinEnum object.Vertex := object.vertices
  (FinEnum.equiv vertex).val

/-- The induced order on ports and edge-incidences: the manuscript's
"induced lexicographic order on edge-incidences", cleared into one index by the
schedule's own length. -/
noncomputable def portIndex (object : FiniteObject.{u})
    (port : object.Vertex × object.Vertex) : Nat :=
  letI : FinEnum object.Vertex := object.vertices
  object.vertexIndex port.1 * FinEnum.card object.Vertex + object.vertexIndex port.2

/-- **The canonical pair order** of `def:capacity-token-ledger`: unordered pairs
of active surplus demands ordered lexicographically by their two demands in the
selected-port order. -/
noncomputable def pairIndex (object : FiniteObject.{u})
    (pair : Finset (object.Vertex × object.Vertex)) : Lex (Nat × Nat) := by
  letI := object.vertexPairDecidableEq
  exact toLex ((pair.image object.portIndex).min.getD 0,
    (pair.image object.portIndex).max.getD 0)

/-! ## `supp(B)` and `κ(B)` -/

namespace Blocker

/-- **`supp(B)`** of `def:capacity-token-ledger`: "the singleton vertex for a
vertex blocker, the marked edge for an edge-incidence blocker, the declared
support of a boundary-profile or target-response coordinate, and the union of the
shoulder chords for a chord-set blocker". -/
noncomputable def declaredSupport (object : FiniteObject.{u})
    (coordinateSupport : Coordinate → Finset object.Vertex)
    (chordEnds : Chord → object.Vertex × object.Vertex)
    (blocker : Blocker object Coordinate Chord) : Finset object.Vertex := by
  classical
  exact match blocker with
    | .sharedDeclaredSupport (.vertex vertex) => {vertex}
    | .sharedDeclaredSupport (.incidence incidence) => {incidence.1, incidence.2}
    | .sharedReturnSupport (.vertex vertex) => {vertex}
    | .sharedReturnSupport (.incidence incidence) => {incidence.1, incidence.2}
    | .sharedLocalBuffer vertex => {vertex}
    | .boundaryProfile coordinate => coordinateSupport coordinate
    | .targetResponse coordinate => coordinateSupport coordinate
    | .arithmeticChordSet chords =>
        chords.biUnion fun chord => {(chordEnds chord).1, (chordEnds chord).2}

/-- **`κ(B)`** of `def:primitive-sparse-blocker-carrier`, clause by clause:

* (a), (b) a vertex or edge-incidence blocker is its own carrier;
* (c) a common shoulder endpoint or cubic buffer vertex is its own carrier;
* (d), (e) a coordinate's carrier is the least item contained in its declared
  support, which is its least vertex because `V(G)` is the first summand of
  `𝔘_sp(G)`;
* (f) a chord-set obstruction's carrier is the least selected surplus port whose
  shoulder chord belongs to the set.

The two selecting clauses are partial: the manuscript's reason that the carrier
exists — the declared support of a sparse pair-response coordinate contains
`T(p) ∪ T(q)`, and the chord set of a suppressed family is nonempty — is a
property of the presentation, so it stays an antecedent here rather than becoming
a hypothesis about the object. -/
noncomputable def carrier (object : FiniteObject.{u}) (threshold : Nat)
    (coordinateSupport : Coordinate → Finset object.Vertex)
    (chordPort : Chord → object.Vertex × object.Vertex)
    (blocker : Blocker object Coordinate Chord) :
    Option (object.Vertex ⊕ (object.Vertex × object.Vertex) ⊕
      (object.Vertex × object.Vertex)) := by
  classical
  exact match blocker with
    | .sharedDeclaredSupport (.vertex vertex) => some (.inl vertex)
    | .sharedDeclaredSupport (.incidence incidence) => some (.inr (.inl incidence))
    | .sharedReturnSupport (.vertex vertex) => some (.inl vertex)
    | .sharedReturnSupport (.incidence incidence) => some (.inr (.inl incidence))
    | .sharedLocalBuffer vertex => some (.inl vertex)
    | .boundaryProfile coordinate =>
        ((coordinateSupport coordinate).toList.head?).map .inl
    | .targetResponse coordinate =>
        ((coordinateSupport coordinate).toList.head?).map .inl
    | .arithmeticChordSet chords =>
        (((chords.image chordPort) ∩ object.excessPorts threshold).toList.head?).map
          fun port => .inr (.inr port)

end Blocker

/-- A carrier the four clauses select is a member of `𝔘_sp(G)`: a vertex is one,
an edge-incidence blocker carries a genuine incidence, and the chord clause
selects inside the excess selector by construction. -/
theorem carrier_mem_primitiveCarrier
    {activation : DemandActivation object Coordinate Chord} {threshold : Nat}
    {coordinateSupport : Coordinate → Finset object.Vertex}
    {chordPort : Chord → object.Vertex × object.Vertex}
    {pair : Finset (object.Vertex × object.Vertex)}
    {blocker : Blocker object Coordinate Chord}
    (member : blocker ∈ activation.blockers pair)
    {item : object.Vertex ⊕ (object.Vertex × object.Vertex) ⊕
      (object.Vertex × object.Vertex)}
    (selected :
      Blocker.carrier object threshold coordinateSupport chordPort blocker =
        some item) :
    item ∈ object.primitiveCarrier threshold := by
  classical
  have vertexSide : ∀ vertex : object.Vertex,
      (Sum.inl vertex :
        object.Vertex ⊕ (object.Vertex × object.Vertex) ⊕
          (object.Vertex × object.Vertex)) ∈ object.primitiveCarrier threshold := by
    intro vertex
    rw [primitiveCarrier]
    exact Finset.inl_mem_disjSum.2 (object.mem_vertexFinset vertex)
  have incidenceSide : ∀ incidence : object.Vertex × object.Vertex,
      incidence ∈ object.incidences →
      (Sum.inr (Sum.inl incidence) :
        object.Vertex ⊕ (object.Vertex × object.Vertex) ⊕
          (object.Vertex × object.Vertex)) ∈ object.primitiveCarrier threshold := by
    intro incidence inside
    rw [primitiveCarrier]
    exact Finset.inr_mem_disjSum.2 (Finset.inl_mem_disjSum.2 inside)
  have portSide : ∀ port : object.Vertex × object.Vertex,
      port ∈ object.excessPorts threshold →
      (Sum.inr (Sum.inr port) :
        object.Vertex ⊕ (object.Vertex × object.Vertex) ⊕
          (object.Vertex × object.Vertex)) ∈ object.primitiveCarrier threshold := by
    intro port inside
    rw [primitiveCarrier]
    exact Finset.inr_mem_disjSum.2 (Finset.inr_mem_disjSum.2 inside)
  match blocker, member, selected with
  | .sharedDeclaredSupport (.vertex vertex), _, selected =>
      rw [Blocker.carrier] at selected
      cases selected
      exact vertexSide vertex
  | .sharedDeclaredSupport (.incidence incidence), member, selected =>
      rw [Blocker.carrier] at selected
      cases selected
      exact incidenceSide incidence
        (DemandActivation.incidence_mem_incidences_of_mem_blockers activation
          (Or.inl member))
  | .sharedReturnSupport (.vertex vertex), _, selected =>
      rw [Blocker.carrier] at selected
      cases selected
      exact vertexSide vertex
  | .sharedReturnSupport (.incidence incidence), member, selected =>
      rw [Blocker.carrier] at selected
      cases selected
      exact incidenceSide incidence
        (DemandActivation.incidence_mem_incidences_of_mem_blockers activation
          (Or.inr member))
  | .sharedLocalBuffer vertex, _, selected =>
      rw [Blocker.carrier] at selected
      cases selected
      exact vertexSide vertex
  | .boundaryProfile coordinate, _, selected =>
      rw [Blocker.carrier, Option.map_eq_some_iff] at selected
      obtain ⟨vertex, _, rfl⟩ := selected
      exact vertexSide vertex
  | .targetResponse coordinate, _, selected =>
      rw [Blocker.carrier, Option.map_eq_some_iff] at selected
      obtain ⟨vertex, _, rfl⟩ := selected
      exact vertexSide vertex
  | .arithmeticChordSet chords, _, selected =>
      rw [Blocker.carrier, Option.map_eq_some_iff] at selected
      obtain ⟨port, found, rfl⟩ := selected
      refine portSide port ?_
      have inside : port ∈ (chords.image chordPort) ∩ object.excessPorts threshold := by
        simpa using List.mem_of_mem_head? found
      exact (Finset.mem_inter.1 inside).2

/-! ## The presentation the two selecting clauses read -/

/-- The declared data `def:capacity-token-ledger`'s clauses (d)--(f) read: the
support a declared coordinate is supported on, the two ends of a shoulder chord,
and the selected surplus port a shoulder chord belongs to.  These are
`def:declared-coordinate-signature`'s own maps; no theorem is carried. -/
structure CarrierPresentation (object : FiniteObject.{u}) (Coordinate Chord : Type v)
    where
  /-- `X_π`, the declared support of a response coordinate. -/
  coordinateSupport : Coordinate → Finset object.Vertex
  /-- The two ends of an added shoulder chord. -/
  chordEnds : Chord → object.Vertex × object.Vertex
  /-- The selected surplus port whose shoulder chord this is. -/
  chordPort : Chord → object.Vertex × object.Vertex

/-! ## `supp(B_π)` -/

variable (activation : DemandActivation object Coordinate Chord)
  (presentation : CarrierPresentation object Coordinate Chord)
  (threshold : Nat) (packing : Finset (Finset object.Vertex))

/-- **`supp(B_π)`**, the declared support of the pair's canonical blocker.  A free
pair has no canonical blocker and therefore no support, which is why no case of
`Θ_cap` fires on it. -/
noncomputable def chargeSupport
    (pair : Finset (object.Vertex × object.Vertex)) : Finset object.Vertex :=
  match canonicalBlocker activation pair with
  | none => ∅
  | some blocker =>
      Blocker.declaredSupport object presentation.coordinateSupport
        presentation.chordEnds blocker

/-! ## The three geometric cases -/

/-- **Case (a)**: the least window--remainder edge contained in `supp(B_π)`. -/
noncomputable def windowJoinChoice
    (pair : Finset (object.Vertex × object.Vertex)) :
    Option (object.Vertex × object.Vertex) := by
  classical
  exact ((object.windowRemainderIncidences packing).filter fun incidence =>
    incidence.1 ∈ chargeSupport activation presentation pair ∧
      incidence.2 ∈ chargeSupport activation presentation pair).toList.head?

/-- **Case (b)**: the least cross-window edge contained in `supp(B_π)`, taken at
the least of its two window ends.  The cross-window family carries an entry at
each end, so the least entry of the candidate set is the least endpoint token of
the least such edge. -/
noncomputable def crossWindowChoice
    (pair : Finset (object.Vertex × object.Vertex)) :
    Option (object.Vertex × object.Vertex) := by
  classical
  exact ((object.crossWindowIncidences packing).filter fun incidence =>
    incidence.1 ∈ chargeSupport activation presentation pair ∧
      incidence.2 ∈ chargeSupport activation presentation pair).toList.head?

/-- **Case (c), the vertex**: the least high-degree remainder vertex contained in
`supp(B_π)`. -/
noncomputable def remainderVertexChoice
    (pair : Finset (object.Vertex × object.Vertex)) : Option object.Vertex := by
  classical
  exact ((object.remainderSupport packing).filter fun vertex =>
    vertex ∈ chargeSupport activation presentation pair ∧
      threshold < object.degree vertex).toList.head?

/-- **`𝒫_v`**: the pairs for which the first two cases fail and whose least
high-degree remainder vertex is `v`. -/
noncomputable def remainderCohort (vertex : object.Vertex) :
    Finset (Finset (object.Vertex × object.Vertex)) := by
  classical
  exact (object.portPairSchedule threshold).filter fun pair =>
    (windowJoinChoice activation presentation packing pair).isNone ∧
      (crossWindowChoice activation presentation packing pair).isNone ∧
        remainderVertexChoice activation presentation threshold packing pair =
          some vertex

/-- **`rk_v(π)`**: the rank of `π` in `𝒫_v` under the canonical pair order. -/
noncomputable def remainderRank (vertex : object.Vertex)
    (pair : Finset (object.Vertex × object.Vertex)) : Nat := by
  classical
  exact ((remainderCohort activation presentation threshold packing vertex).filter
    fun other => object.pairIndex other < object.pairIndex pair).card

/-- **`j(π) = 1 + (rk_v(π) mod (d_G(v) − δ))`**, the surplus unit of `𝔗_R` the
third case charges to. -/
noncomputable def remainderUnit (vertex : object.Vertex)
    (pair : Finset (object.Vertex × object.Vertex)) : Nat :=
  1 + remainderRank activation presentation threshold packing vertex pair %
    (object.degree vertex - threshold)

/-! ## `Θ_cap` -/

/-- **`Θ_cap`**, the four-case canonical charge of `def:capacity-token-ledger`.
It is a function into `Option`, so it is single-valued by construction; `none` is
exactly the case in which no clause fires, which on a blocked pair with a defined
carrier does not happen. -/
noncomputable def capacityCharge
    (pair : Finset (object.Vertex × object.Vertex)) :
    Option (CapacityToken object) :=
  match windowJoinChoice activation presentation packing pair with
  | some incidence => some (.boundaryWindow incidence)
  | none =>
    match crossWindowChoice activation presentation packing pair with
    | some incidence => some (.crossWindow incidence)
    | none =>
      match remainderVertexChoice activation presentation threshold packing pair with
      | some vertex =>
          some (.remainder (vertex,
            remainderUnit activation presentation threshold packing vertex pair))
      | none =>
        match canonicalBlocker activation pair with
        | none => none
        | some blocker =>
            (Blocker.carrier object threshold presentation.coordinateSupport
              presentation.chordPort blocker).map CapacityToken.primitive

/-- **`Θ_cap` lands in `𝔗_cap`.**  Each clause selects inside the family that
builds its own summand of the token universe: the two window incidence families,
the remainder surplus units — the modulus keeps the index inside the vertex's own
range — and `𝔘_sp(G)`. -/
theorem capacityCharge_mem_capacityTokens
    {pair : Finset (object.Vertex × object.Vertex)} {token : CapacityToken object}
    (charged : capacityCharge activation presentation threshold packing pair =
      some token) :
    token ∈ object.capacityTokens threshold packing := by
  classical
  rw [capacityCharge] at charged
  rw [capacityTokens]
  rcases windowCase : windowJoinChoice activation presentation packing pair with
    _ | incidence
  · rw [windowCase] at charged
    rcases crossCase : crossWindowChoice activation presentation packing pair with
      _ | incidence
    · rw [crossCase] at charged
      rcases vertexCase :
        remainderVertexChoice activation presentation threshold packing pair with
        _ | vertex
      · rw [vertexCase] at charged
        rcases blockerCase : canonicalBlocker activation pair with _ | blocker
        · rw [blockerCase] at charged; cases charged
        · rw [blockerCase, Option.map_eq_some_iff] at charged
          obtain ⟨item, selected, rfl⟩ := charged
          refine Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ?_)))
          exact carrier_mem_primitiveCarrier
            (canonicalBlocker_mem activation blockerCase) selected
      · rw [vertexCase] at charged
        cases charged
        have inside : vertex ∈ (object.remainderSupport packing).filter
            fun candidate =>
              candidate ∈ chargeSupport activation presentation pair ∧
                threshold < object.degree candidate := by
          simpa [remainderVertexChoice] using
            List.mem_of_mem_head? (l := ((object.remainderSupport packing).filter
              fun candidate =>
                candidate ∈ chargeSupport activation presentation pair ∧
                  threshold < object.degree candidate).toList) vertexCase
        obtain ⟨remainderMem, _, high⟩ := Finset.mem_filter.1 inside
        refine Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ?_)))
        rw [mem_remainderSurplusTokens_iff]
        refine ⟨remainderMem, ?_, ?_⟩
        · exact Nat.le_add_right 1 _
        · have modulus : remainderRank activation presentation threshold packing
              vertex pair % (object.degree vertex - threshold) <
                object.degree vertex - threshold :=
            Nat.mod_lt _ (by omega)
          show 1 + remainderRank activation presentation threshold packing vertex pair %
            (object.degree vertex - threshold) ≤ object.degree vertex - threshold
          omega
    · rw [crossCase] at charged
      cases charged
      have inside : incidence ∈ (object.crossWindowIncidences packing).filter
          fun candidate =>
            candidate.1 ∈ chargeSupport activation presentation pair ∧
              candidate.2 ∈ chargeSupport activation presentation pair := by
        simpa [crossWindowChoice] using
          List.mem_of_mem_head? (l := ((object.crossWindowIncidences packing).filter
            fun candidate =>
              candidate.1 ∈ chargeSupport activation presentation pair ∧
                candidate.2 ∈ chargeSupport activation presentation pair).toList)
            crossCase
      exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_filter.1 inside).1))
  · rw [windowCase] at charged
    cases charged
    have inside : incidence ∈ (object.windowRemainderIncidences packing).filter
        fun candidate =>
          candidate.1 ∈ chargeSupport activation presentation pair ∧
            candidate.2 ∈ chargeSupport activation presentation pair := by
      simpa [windowJoinChoice] using
        List.mem_of_mem_head? (l := ((object.windowRemainderIncidences packing).filter
          fun candidate =>
            candidate.1 ∈ chargeSupport activation presentation pair ∧
              candidate.2 ∈ chargeSupport activation presentation pair).toList)
          windowCase
    exact Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_filter.1 inside).1)

/-- **`Θ_cap` is defined on `Π_blk`.**  A blocked pair has a canonical blocker,
and if none of the three geometric clauses fires the fourth does, provided the
canonical blocker has a primitive carrier — which is the manuscript's own reason
that case (d) always applies, kept as an antecedent. -/
theorem isSome_capacityCharge
    {pair : Finset (object.Vertex × object.Vertex)}
    (blocked : (activation.blockers pair).Nonempty)
    (carried : ∀ blocker ∈ activation.blockers pair,
      (Blocker.carrier object threshold presentation.coordinateSupport
        presentation.chordPort blocker).isSome) :
    (capacityCharge activation presentation threshold packing pair).isSome := by
  rw [capacityCharge]
  rcases windowCase : windowJoinChoice activation presentation packing pair with
    _ | incidence
  · rcases crossCase : crossWindowChoice activation presentation packing pair with
      _ | incidence
    · rcases vertexCase :
        remainderVertexChoice activation presentation threshold packing pair with
        _ | vertex
      · rcases blockerCase : canonicalBlocker activation pair with _ | blocker
        · exact absurd blockerCase
            (Option.ne_none_iff_isSome.2 (isSome_canonicalBlocker activation blocked))
        · obtain ⟨item, selected⟩ := Option.isSome_iff_exists.1
            (carried blocker (canonicalBlocker_mem activation blockerCase))
          simp [selected]
      · simp
    · simp
  · simp

/-! ## The token ledger at `Θ_cap`, and `def:same-token-patterns` -/

/-- The declared token alphabet: `𝔗_cap` in the object's own enumeration. -/
noncomputable def capacityTokenOrder (carrier : FiniteObject.{u}) (threshold : Nat)
    (packing : Finset (Finset carrier.Vertex)) : List (CapacityToken carrier) :=
  (carrier.capacityTokens threshold packing).toList

/-- **`Θ_cap` as the ledger's eligibility relation.**  A token applies to a pair
exactly when it is the pair's charge, so the "first applicable label" of
`Graph/CanonicalFibreLedger` is `Θ_cap` itself. -/
def Charges (token : CapacityToken object)
    (pair : Finset (object.Vertex × object.Vertex)) : Prop :=
  capacityCharge activation presentation threshold packing pair = some token

noncomputable instance decidableCharges (token : CapacityToken object)
    (pair : Finset (object.Vertex × object.Vertex)) :
    Decidable (Charges activation presentation threshold packing token pair) :=
  Classical.dec _

/-- **The declared order recovers `Θ_cap`.**  Only the charge itself applies, and
it lies in the declared alphabet, so the canonical first applicable label is the
charge. -/
theorem canonicalLabel_eq_capacityCharge
    (pair : Finset (object.Vertex × object.Vertex)) :
    CanonicalFibreLedger.canonicalLabel (capacityTokenOrder object threshold packing)
        (Charges activation presentation threshold packing) pair =
      capacityCharge activation presentation threshold packing pair := by
  classical
  rcases charge : capacityCharge activation presentation threshold packing pair with
    _ | token
  · rw [CanonicalFibreLedger.canonicalLabel, List.find?_eq_none]
    intro other _ applies
    have : Charges activation presentation threshold packing other pair :=
      of_decide_eq_true applies
    rw [Charges, charge] at this
    cases this
  · rw [CanonicalFibreLedger.canonicalLabel]
    refine List.find?_eq_some_of_unique ?_ ?_ ?_
    · exact Finset.mem_toList.2
        (capacityCharge_mem_capacityTokens activation presentation threshold packing
          charge)
    · show CanonicalFibreLedger.appliesTo
        (Charges activation presentation threshold packing) pair token = true
      simp only [CanonicalFibreLedger.appliesTo, decide_eq_true_eq]
      exact charge
    · intro other _ applies
      rw [CanonicalFibreLedger.appliesTo, decide_eq_true_eq] at applies
      have equality : capacityCharge activation presentation threshold packing pair =
          some other := applies
      rw [charge] at equality
      exact (Option.some_injective _ equality).symm

/-- **`H_t` of `def:same-token-patterns`**: the pairs charged to one token, read
as the edge set of a graph on the active family `𝒜₀`.  Its vertex set is the
active family and its edges are `Π_t = Θ_cap^{-1}(t)`. -/
noncomputable def tokenFibre (token : CapacityToken object) :
    Finset (Finset (object.Vertex × object.Vertex)) := by
  classical
  exact (object.portPairSchedule threshold).filter fun pair =>
    capacityCharge activation presentation threshold packing pair = some token

theorem tokenFibre_subset (token : CapacityToken object) :
    tokenFibre activation presentation threshold packing token ⊆
      object.portPairSchedule threshold :=
  Finset.filter_subset _ _

/-- Every member of a token fibre is a pair of distinct active demands: `H_t` is
a simple graph on `𝒜₀`. -/
theorem card_of_mem_tokenFibre {token : CapacityToken object}
    {pair : Finset (object.Vertex × object.Vertex)}
    (member : pair ∈ tokenFibre activation presentation threshold packing token) :
    pair.card = 2 := by
  letI := object.vertexPairDecidableEq
  exact (Finset.mem_powersetCard.mp
    (tokenFibre_subset activation presentation threshold packing token member)).2

/-- **`e(H_t) = ℓ_cap(t)`**: the token fibre is the ledger's own multiplicity
fibre, so the fibre graph's edge count *is* the token load. -/
theorem card_tokenFibre_eq_pairMultiplicity (token : CapacityToken object) :
    (tokenFibre activation presentation threshold packing token).card =
      object.pairMultiplicity threshold (CapacityToken.decidableEq object)
        (capacityTokenOrder object threshold packing)
        (Charges activation presentation threshold packing)
        (decidableCharges activation presentation threshold packing) token := by
  letI := object.vertexPairDecidableEq
  rw [pairMultiplicity, CanonicalFibreLedger.multiplicity, tokenFibre]
  refine congrArg Finset.card (Finset.ext fun pair => ?_)
  simp only [Finset.mem_filter, canonicalLabel_eq_capacityCharge]

/-- **`Π_blk` at `Θ_cap`**: the pairs the token ledger charges are exactly the
pairs whose charge is defined. -/
theorem chargedPairs_eq_filter :
    object.chargedPairs threshold (capacityTokenOrder object threshold packing)
        (Charges activation presentation threshold packing)
        (decidableCharges activation presentation threshold packing) =
      (object.portPairSchedule threshold).filter (fun pair =>
        (capacityCharge activation presentation threshold packing pair).isSome) := by
  letI := object.vertexPairDecidableEq
  rw [chargedPairs, CanonicalFibreLedger.assigned]
  refine Finset.ext fun pair => ?_
  simp only [Finset.mem_filter, canonicalLabel_eq_capacityCharge]

/-- **`lem:token-ledger-no-overcount` at `Θ_cap`**: `|Π_blk| = Σ_t ℓ_cap(t)`, now
at the manuscript's own token universe and its own four-case assignment rather
than at a quantified alphabet.  The identity is
`Graph/CanonicalFibreLedger`'s, read here; nothing is proved twice. -/
theorem card_chargedPairs_eq_sum_load :
    (object.chargedPairs threshold (capacityTokenOrder object threshold packing)
        (Charges activation presentation threshold packing)
        (decidableCharges activation presentation threshold packing)).card =
      ∑ token ∈ (capacityTokenOrder object threshold packing).toFinset,
        (tokenFibre activation presentation threshold packing token).card := by
  classical
  rw [object.card_chargedPairs_eq_sum_multiplicity (CapacityToken.decidableEq object)
    (capacityTokenOrder object threshold packing)
    (Charges activation presentation threshold packing)
    (decidableCharges activation presentation threshold packing)]
  exact Finset.sum_congr rfl fun token _ =>
    (card_tokenFibre_eq_pairMultiplicity activation presentation threshold packing
      token).symm

/-- The declared alphabet is `𝔗_cap` itself, so the fibre sum above runs over the
token universe the supply lemma counts. -/
theorem capacityTokenOrder_toFinset :
    (capacityTokenOrder object threshold packing).toFinset =
      object.capacityTokens threshold packing := by
  classical
  ext token
  rw [capacityTokenOrder]
  simp

/-- **The token ledger is total on `Π_blk`.**  Every blocked pair whose canonical
blocker has a primitive carrier is charged, so the fibre identity above is read at
the whole blocked family — which is what makes `|Π_blk| = Σ_t ℓ_cap(t)` the
manuscript's display rather than a statement about a subfamily. -/
theorem chargedPairs_eq_of_blocked
    (blocked : ∀ pair ∈ object.portPairSchedule threshold,
      (activation.blockers pair).Nonempty)
    (carried : ∀ pair ∈ object.portPairSchedule threshold,
      ∀ blocker ∈ activation.blockers pair,
        (Blocker.carrier object threshold presentation.coordinateSupport
          presentation.chordPort blocker).isSome) :
    object.chargedPairs threshold (capacityTokenOrder object threshold packing)
        (Charges activation presentation threshold packing)
        (decidableCharges activation presentation threshold packing) =
      object.portPairSchedule threshold := by
  classical
  rw [chargedPairs_eq_filter]
  refine Finset.filter_true_of_mem fun pair member => ?_
  exact isSome_capacityCharge activation presentation threshold packing
    (blocked pair member) (carried pair member)

/-! ## The statement nodes `[134]`--`[136]` commit

Written out once, here, and referenced by both the residual domain's value schema
and the row that proves it, so that the schema and the row cannot drift apart.
It is quantified over exactly two things the branch does not fix: a maximal
packing of induced windows -- the manuscript's own `𝒫`, and the object carries
one -- and the declared coordinate and shoulder-chord presentation of
`def:declared-coordinate-signature`.  Everything else is the object's own. -/

/-- **Nodes `[134]`--`[136]`**: `def:capacity-token-ledger` with
`lem:capacity-token-supply`, `lem:token-ledger-no-overcount` and
`def:same-token-patterns`, at the object's own token universe and its own
four-case charge. -/
def CapacityTokenLedgerStatement (object : FiniteObject.{u}) (threshold order : Nat) :
    Prop :=
  ∀ (packing : Finset (Finset object.Vertex)),
    object.IsWindowPacking order packing →
    ∀ (Coordinate Chord : Type u)
      (activation : DemandActivation object Coordinate Chord)
      (presentation : CarrierPresentation object Coordinate Chord),
      -- `lem:capacity-token-supply`, exact:
      -- `|𝔗_cap| + 2(order−1)p = |𝔘_sp(G)| + δ·order·p + σ(G)`.
      ((object.capacityTokens threshold packing).card +
            2 * (order - 1) * packing.card =
          (object.primitiveCarrier threshold).card +
            threshold * (order * packing.card) + object.degreeSurplus threshold) ∧
        -- `lem:capacity-token-supply`, displayed:
        -- `|𝔗_cap| ≤ (3(δ−1)+2)n + σ(G)`, the manuscript's `≤ 8n + σ(G)`.  The
        -- sparse upper envelope and the registered join comparison are spent by
        -- the node rather than carried, so the display is unconditional.
        ((object.capacityTokens threshold packing).card ≤
          object.capacityTokenSupply threshold + object.degreeSurplus threshold) ∧
        -- `def:capacity-token-ledger`: `Θ_cap` charges into `𝔗_cap`.
        (∀ (pair : Finset (object.Vertex × object.Vertex))
            (token : CapacityToken object),
          capacityCharge activation presentation threshold packing pair =
              some token →
            token ∈ object.capacityTokens threshold packing) ∧
        -- `lem:token-ledger-no-overcount` at `Θ_cap`: `|Π_blk| = Σ_t ℓ_cap(t)`.
        ((object.chargedPairs threshold (capacityTokenOrder object threshold packing)
              (Charges activation presentation threshold packing)
              (decidableCharges activation presentation threshold packing)).card =
          ∑ token ∈ object.capacityTokens threshold packing,
            (tokenFibre activation presentation threshold packing token).card) ∧
        -- The identity is read at the whole blocked family: `Θ_cap` is total on
        -- `Π_blk` once every canonical blocker has its primitive carrier.
        ((∀ pair ∈ object.portPairSchedule threshold,
            (activation.blockers pair).Nonempty) →
          (∀ pair ∈ object.portPairSchedule threshold,
            ∀ blocker ∈ activation.blockers pair,
              (Blocker.carrier object threshold presentation.coordinateSupport
                presentation.chordPort blocker).isSome) →
          object.chargedPairs threshold (capacityTokenOrder object threshold packing)
              (Charges activation presentation threshold packing)
              (decidableCharges activation presentation threshold packing) =
            object.portPairSchedule threshold) ∧
        -- `def:same-token-patterns`: `H_t` is a simple graph on `𝒜₀` with
        -- `e(H_t) = ℓ_cap(t)`.
        (∀ token : CapacityToken object,
          tokenFibre activation presentation threshold packing token ⊆
              object.portPairSchedule threshold ∧
            (∀ pair ∈ tokenFibre activation presentation threshold packing token,
              pair.card = 2) ∧
            (tokenFibre activation presentation threshold packing token).card =
              object.pairMultiplicity threshold (CapacityToken.decidableEq object)
                (capacityTokenOrder object threshold packing)
                (Charges activation presentation threshold packing)
                (decidableCharges activation presentation threshold packing) token)

/-- **Nodes `[134]`--`[136]`, proved.**  Every clause is one of the theorems
above; nothing is assumed about the object beyond the standing baseline, the
registered `3 ≤ δ` and `0 < order`, and the handshake the baseline gives. -/
theorem capacityTokenLedgerStatement (object : FiniteObject.{u}) {threshold order : Nat}
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (three : 3 ≤ threshold) (orderPos : 0 < order)
    (handshake : threshold * object.vertexCount ≤ 2 * object.edgeCount)
    (envelope : object.edgeCount + 2 ≤ (threshold - 1) * object.vertexCount)
    (joinSlack : threshold * order + 2 ≤ 4 * order) :
    CapacityTokenLedgerStatement object threshold order := by
  intro packing valid _Coordinate _Chord activation presentation
  refine ⟨object.card_capacityTokens_add_internalMass valid baseline, ?_, ?_, ?_, ?_, ?_⟩
  · exact object.card_capacityTokens_le valid baseline three handshake envelope
      orderPos joinSlack
  · intro pair token charged
    exact capacityCharge_mem_capacityTokens activation presentation threshold packing
      charged
  · rw [← capacityTokenOrder_toFinset (object := object) (threshold := threshold)
      (packing := packing)]
    exact card_chargedPairs_eq_sum_load activation presentation threshold packing
  · intro blocked carried
    exact chargedPairs_eq_of_blocked activation presentation threshold packing blocked
      carried
  · intro token
    exact ⟨tokenFibre_subset activation presentation threshold packing token,
      fun pair member =>
        card_of_mem_tokenFibre activation presentation threshold packing member,
      card_tokenFibre_eq_pairMultiplicity activation presentation threshold packing
        token⟩

end FiniteObject

end Hypostructure.Graph
