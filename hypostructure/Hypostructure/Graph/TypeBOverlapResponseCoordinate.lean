import Hypostructure.Graph.TypeBCanonicalB2

/-!
# Canonical Type B overlap-response coordinates

The failure of the finite B2 choice problem has two literal forms.  A demand
may have no eligible entry, or an attempted family may contain two entries
which use the same augmented-ledger carrier.  This file enumerates exactly
those finite coordinates.  It also records the graph support carried by every
candidate in the obstruction, including its decorated fan paths and the
packed windows actually met by its selected incidences.

No response classification is stored here.  The later global--local row must
derive that classification from the inherited replacement and delocalization
theorems.
-/

namespace Hypostructure.Graph

universe u

namespace TypeBRefinedSupport

open Classical

noncomputable section

/-- The vertices literally named by one tagged B2 carrier atom. -/
def supportAtomVertices {object : FiniteObject.{u}}
    (atom : SupportAtom object) : Finset object.Vertex :=
  match atom with
  | .inl vertex => {vertex}
  | .inr incidence => {incidence.1, incidence.2}

/-- The vertex support of a finite family of tagged B2 carrier atoms. -/
def carrierVertexSupport {object : FiniteObject.{u}}
    (atoms : Finset (SupportAtom object)) : Finset object.Vertex :=
  atoms.biUnion supportAtomVertices

/-- All paths in the canonical decorated fan retained by a candidate profile. -/
def profilePathSupport {object : FiniteObject.{u}}
    (profile : TypeBFanClosedPorts.Profile object) : Finset object.Vertex :=
  profile.marked.fan.rim.attach.biUnion fun rim =>
    (profile.marked.fan.decoration rim.1 rim.2).walk.support.toFinset

/-- Packed windows actually touched by the selected incidence carriers. -/
def selectedWindowSupport {object : FiniteObject.{u}}
    (packing : Finset (Finset object.Vertex))
    (incidences : Finset (object.Vertex × object.Vertex)) :
    Finset object.Vertex :=
  (packing.filter fun window =>
    ∃ incidence ∈ incidences, incidence.2 ∈ window).biUnion id

/-- The actual graph support retained by one canonical candidate entry. -/
def CandidateData.witnessSupport {object : FiniteObject.{u}}
    (data : CandidateData object) (threshold : ℕ)
    (packing : Finset (Finset object.Vertex)) (hub : object.Vertex) :
    Finset object.Vertex :=
  insert hub <|
    data.profile.envelope ∪
      profilePathSupport data.profile ∪
        carrierVertexSupport (data.supportAtoms threshold packing hub) ∪
          selectedWindowSupport packing
            (data.selectedIncidences threshold packing hub)

/-- The support of every eligible candidate for one obstruction demand. -/
def candidateFamilyWitnessSupport (object : FiniteObject.{u})
    (threshold dischargeScale : ℕ)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (hub : object.Vertex) :
    Finset object.Vertex :=
  (candidateFamily object threshold dischargeScale piece hub).toFinset.biUnion
    fun data => data.witnessSupport threshold packing hub

/-- The manuscript overlap support `Z(O)`: the obstruction demands together
with every carrier, decorated path, and touched packed-window support occurring
in their finite candidate families. -/
def OverlapObstruction.overlapSupport {object : FiniteObject.{u}}
    {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing}
    (obstruction : OverlapObstruction object threshold dischargeScale piece) :
    Finset object.Vertex :=
  obstruction.demands ∪ obstruction.demands.biUnion fun hub =>
    candidateFamilyWitnessSupport object threshold dischargeScale piece hub

/-- The literal boundary of a finite support inside the ambient graph. -/
def supportBoundary (object : FiniteObject.{u})
    (support : Finset object.Vertex) : Finset object.Vertex :=
  support.filter fun vertex =>
    ∃ outside, outside ∉ support ∧ object.graph.Adj vertex outside

/-- The degree owned by a finite support at one of its vertices. -/
def supportDegree (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) : ℕ :=
  letI : Fintype object.Vertex :=
    @FinEnum.instFintype _ object.vertices
  (object.graph.neighborFinset vertex ∩ support).card

/-- The canonical boundary-degree profile of `Z(O)`.  Its domain is the
actual ambient boundary, rather than a supplied interface. -/
def OverlapObstruction.boundaryDegreeProfile {object : FiniteObject.{u}}
    {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing}
    (obstruction : OverlapObstruction object threshold dischargeScale piece) :
    {vertex // vertex ∈ supportBoundary object obstruction.overlapSupport} → ℕ :=
  fun vertex => supportDegree object obstruction.overlapSupport vertex.1

/-- A proof-free finite coordinate for the two exact failure modes of the B2
candidate selection problem. -/
inductive RawOverlapCoordinate (object : FiniteObject.{u}) where
  | missingCandidate (hub : object.Vertex)
  | supportConflict
      (left right : object.Vertex)
      (leftEntry rightEntry : CandidateData object)
      (atom : SupportAtom object)
  | reserveConflict
      (left right : object.Vertex)
      (leftEntry rightEntry : CandidateData object)
      (unit : OrdinaryDeficiencyReserve.Carrier object)

/-- Exact semantic validity of one enumerated overlap-response coordinate. -/
def RawOverlapCoordinate.IsFor {object : FiniteObject.{u}}
    {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing}
    (obstruction : OverlapObstruction object threshold dischargeScale piece) :
    RawOverlapCoordinate object → Prop
  | .missingCandidate hub =>
      hub ∈ obstruction.demands ∧
        candidateFamily object threshold dischargeScale piece hub = []
  | .supportConflict left right leftEntry rightEntry atom =>
      left ∈ obstruction.demands ∧
        right ∈ obstruction.demands ∧
          left ≠ right ∧
            leftEntry ∈ candidateFamily object threshold dischargeScale piece left ∧
              rightEntry ∈ candidateFamily object threshold dischargeScale piece right ∧
                atom ∈ leftEntry.supportAtoms threshold packing left ∧
                  atom ∈ rightEntry.supportAtoms threshold packing right
  | .reserveConflict left right leftEntry rightEntry unit =>
      left ∈ obstruction.demands ∧
        right ∈ obstruction.demands ∧
          left ≠ right ∧
            leftEntry ∈ candidateFamily object threshold dischargeScale piece left ∧
              rightEntry ∈ candidateFamily object threshold dischargeScale piece right ∧
                unit ∈ leftEntry.consumedReserveUnits threshold piece left ∧
                  unit ∈ rightEntry.consumedReserveUnits threshold piece right

/-- All proof-free coordinates obtainable from the literal finite candidate
families.  The semantic filter below removes equal-demand and nonempty-family
`missingCandidate` records. -/
def rawOverlapCoordinateSchedule (object : FiniteObject.{u})
    (threshold dischargeScale : ℕ)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing)
    (obstruction : OverlapObstruction object threshold dischargeScale piece) :
    List (RawOverlapCoordinate object) :=
  obstruction.demands.toList.map RawOverlapCoordinate.missingCandidate ++
    obstruction.demands.toList.flatMap fun left =>
      obstruction.demands.toList.flatMap fun right =>
        (candidateFamily object threshold dischargeScale piece left).flatMap fun leftEntry =>
          (candidateFamily object threshold dischargeScale piece right).flatMap fun rightEntry =>
            ((leftEntry.supportAtoms threshold packing left ∩
                rightEntry.supportAtoms threshold packing right).toList.map fun atom =>
              RawOverlapCoordinate.supportConflict
                left right leftEntry rightEntry atom) ++
            ((leftEntry.consumedReserveUnits threshold piece left ∩
                rightEntry.consumedReserveUnits threshold piece right).toList.map fun unit =>
              RawOverlapCoordinate.reserveConflict
                left right leftEntry rightEntry unit)

/-- The finite schedule of exactly valid overlap-response coordinates. -/
def overlapCoordinateSchedule (object : FiniteObject.{u})
    (threshold dischargeScale : ℕ)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing)
  (obstruction : OverlapObstruction object threshold dischargeScale piece) :
    List (RawOverlapCoordinate object) :=
  (rawOverlapCoordinateSchedule object threshold dischargeScale piece obstruction).filter
    fun coordinate => coordinate.IsFor obstruction

theorem mem_rawOverlapCoordinateSchedule_of_isFor
    {object : FiniteObject.{u}} {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing}
    {obstruction : OverlapObstruction object threshold dischargeScale piece}
    {coordinate : RawOverlapCoordinate object}
    (valid : coordinate.IsFor obstruction) :
    coordinate ∈ rawOverlapCoordinateSchedule object threshold dischargeScale piece obstruction := by
  cases coordinate with
  | missingCandidate hub =>
      exact List.mem_append_left _ (by simpa [RawOverlapCoordinate.IsFor] using valid.1)
  | supportConflict left right leftEntry rightEntry atom =>
      rcases valid with
        ⟨leftMem, rightMem, _different, leftEligible, rightEligible,
          atomLeft, atomRight⟩
      simp only [rawOverlapCoordinateSchedule, List.mem_append, List.mem_flatMap,
        List.mem_map, Finset.mem_toList, Finset.mem_inter]
      right
      refine ⟨left, leftMem, right, rightMem, leftEntry, leftEligible,
        rightEntry, rightEligible, ?_⟩
      left
      exact ⟨atom, ⟨atomLeft, atomRight⟩, rfl⟩
  | reserveConflict left right leftEntry rightEntry unit =>
      rcases valid with
        ⟨leftMem, rightMem, _different, leftEligible, rightEligible,
          unitLeft, unitRight⟩
      simp only [rawOverlapCoordinateSchedule, List.mem_append, List.mem_flatMap,
        List.mem_map, Finset.mem_toList, Finset.mem_inter]
      right
      refine ⟨left, leftMem, right, rightMem, leftEntry, leftEligible,
        rightEntry, rightEligible, ?_⟩
      right
      exact ⟨unit, ⟨unitLeft, unitRight⟩, rfl⟩

/-- Membership in the finite schedule is definitionally the exact overlap
coordinate predicate. -/
theorem mem_overlapCoordinateSchedule_iff
    {object : FiniteObject.{u}} {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing}
    {obstruction : OverlapObstruction object threshold dischargeScale piece}
    {coordinate : RawOverlapCoordinate object} :
    coordinate ∈ overlapCoordinateSchedule object threshold dischargeScale piece obstruction ↔
      coordinate.IsFor obstruction := by
  constructor
  · intro member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · intro valid
    exact List.mem_filter.mpr
      ⟨mem_rawOverlapCoordinateSchedule_of_isFor valid, decide_eq_true valid⟩

/-- A minimal B2 obstruction always has a concrete finite response coordinate:
either a genuinely empty candidate family, or a literal shared carrier in a
full attempted selection. -/
theorem OverlapObstruction.exists_overlapCoordinate
    {object : FiniteObject.{u}} {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing}
    (obstruction : OverlapObstruction object threshold dischargeScale piece) :
    ∃ coordinate : RawOverlapCoordinate object, coordinate.IsFor obstruction := by
  by_cases missing : ∃ hub ∈ obstruction.demands,
      candidateFamily object threshold dischargeScale piece hub = []
  · rcases missing with ⟨hub, hubMem, empty⟩
    exact ⟨.missingCandidate hub, hubMem, empty⟩
  · have familyNonempty : ∀ hub, hub ∈ obstruction.demands →
        ∃ entry, entry ∈ candidateFamily object threshold dischargeScale piece hub := by
      intro hub hubMem
      have notEmpty : candidateFamily object threshold dischargeScale piece hub ≠ [] := by
        intro empty
        exact missing ⟨hub, hubMem, empty⟩
      exact List.exists_mem_of_ne_nil _ notEmpty
    choose entry eligible using familyNonempty
    by_cases carriers : ∀ left (leftMem : left ∈ obstruction.demands)
        right (rightMem : right ∈ obstruction.demands), left ≠ right →
          Disjoint
            ((entry left leftMem).supportAtoms threshold packing left)
            ((entry right rightMem).supportAtoms threshold packing right)
    · have notReserves : ¬ ∀ left (leftMem : left ∈ obstruction.demands)
          right (rightMem : right ∈ obstruction.demands), left ≠ right →
            Disjoint
              ((entry left leftMem).consumedReserveUnits threshold piece left)
              ((entry right rightMem).consumedReserveUnits threshold piece right) := by
          intro reserves
          exact obstruction.noDisjointChoice
            ⟨{ entry := entry
               eligible := eligible
               carrierDisjoint := carriers
               reserveDisjoint := reserves }⟩
      push Not at notReserves
      rcases notReserves with
        ⟨left, leftMem, right, rightMem, different, notDisjoint⟩
      rcases Finset.not_disjoint_iff.mp notDisjoint with
        ⟨unit, unitLeft, unitRight⟩
      exact ⟨.reserveConflict left right (entry left leftMem)
          (entry right rightMem) unit,
        leftMem, rightMem, different, eligible left leftMem,
        eligible right rightMem, unitLeft, unitRight⟩
    · push Not at carriers
      rcases carriers with
        ⟨left, leftMem, right, rightMem, different, notDisjoint⟩
      rcases Finset.not_disjoint_iff.mp notDisjoint with
        ⟨atom, atomLeft, atomRight⟩
      exact ⟨.supportConflict left right (entry left leftMem)
          (entry right rightMem) atom,
        leftMem, rightMem, different, eligible left leftMem,
        eligible right rightMem, atomLeft, atomRight⟩

theorem OverlapObstruction.overlapCoordinateSchedule_nonempty
    {object : FiniteObject.{u}} {threshold dischargeScale : ℕ}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing}
    (obstruction : OverlapObstruction object threshold dischargeScale piece) :
    overlapCoordinateSchedule object threshold dischargeScale piece obstruction ≠ [] := by
  rcases obstruction.exists_overlapCoordinate with ⟨coordinate, valid⟩
  exact List.ne_nil_of_mem (mem_overlapCoordinateSchedule_iff.mpr valid)

end

end TypeBRefinedSupport

end Hypostructure.Graph
