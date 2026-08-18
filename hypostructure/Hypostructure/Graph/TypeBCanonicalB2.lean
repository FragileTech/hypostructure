import Hypostructure.Graph.TypeBCanonicalCarrier
import Hypostructure.Graph.OrdinaryDeficiencyReserve
import Hypostructure.Graph.TypeBProfileSchedule

/-!
# Canonical refined Type B support ledger

This is the finite B2 carrier on an actual member of the canonical remainder
decomposition.  A positive candidate scans finite blocks of literal core
vertices; eligibility checks their provenance and their actual charge.  Thus a
missing local block is a genuine finite-family failure and not an assumed
existence theorem.
-/

namespace Hypostructure.Graph.TypeBRefinedSupport

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.TypeBFanIncidence
open Hypostructure.Graph.TypeBHybridIncidence
open Hypostructure.Graph.TypeBProfileSchedule
open Hypostructure.Graph.TypeBCanonicalCarrier
open scoped BigOperators

universe u v

variable {object : FiniteObject.{u}}

noncomputable section

local instance (priority := low) {alpha : Type v} : DecidableEq alpha :=
  Classical.decEq alpha

/-- Ambient high centres carried by a vertex support. -/
noncomputable def centres (object : FiniteObject.{u}) (threshold : Nat)
    (piece : Finset object.Vertex) : Finset object.Vertex := by
  classical
  exact piece.filter (Graph.IsHighCentre object threshold)

theorem mem_centres {threshold : Nat} {piece : Finset object.Vertex}
    {vertex : object.Vertex} :
    vertex ∈ centres object threshold piece ↔
      vertex ∈ piece ∧ Graph.IsHighCentre object threshold vertex := by
  classical
  simp [centres]

theorem centres_subset {threshold : Nat} {piece : Finset object.Vertex} :
    centres object threshold piece ⊆ piece := by
  classical
  exact Finset.filter_subset _ _

noncomputable def scaledCoreCharge (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (piece : Finset object.Vertex)
    (vertex : object.Vertex) : Int :=
  ((dischargeScale *
      (threshold - object.internalDegree piece vertex) : Nat) : Int) - 1

noncomputable def scaledCentreCharge (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (centre : object.Vertex) : Int :=
  - ((dischargeScale * (object.degree centre - threshold) : Nat) : Int) - 1

/-- **`def:typeB-assigned-ledger`'s augmented ledger `Ĉh_B(X)` at an assigned
support `X = (Y_X, H_X)`**: the core charges over the counted core `Y_X` and the
centre charges over the assigned centres `H_X` (which need not lie in the core:
in a decorated handoff envelope they are the decorations outside it). -/
noncomputable def augmentedLedgerWith (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (piece demands : Finset object.Vertex) : Int :=
  (∑ vertex ∈ piece,
      scaledCoreCharge object threshold dischargeScale piece vertex) +
    ∑ centre ∈ demands,
      scaledCentreCharge object threshold dischargeScale centre

/-- The ordinary Type B support's ledger: `H_X` is the piece's own set of high
centres (`def:canonical-decomp`). -/
noncomputable def augmentedLedger (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (piece : Finset object.Vertex) : Int :=
  augmentedLedgerWith object threshold dischargeScale piece
    (centres object threshold piece)

theorem augmentedLedger_eq (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (piece : Finset object.Vertex) :
    augmentedLedger object threshold dischargeScale piece =
      (∑ vertex ∈ piece,
          scaledCoreCharge object threshold dischargeScale piece vertex) +
        ∑ centre ∈ centres object threshold piece,
          scaledCentreCharge object threshold dischargeScale centre := rfl

/-- Assigning more high centres lowers the ledger plus its centre count: each
extra centre `h` contributes `−(s·(d(h)−δ)) − 1 + 1 ≤ 0`. -/
theorem augmentedLedgerWith_add_card_le (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (piece demands : Finset object.Vertex)
    (subset : centres object threshold piece ⊆ demands) :
    augmentedLedgerWith object threshold dischargeScale piece demands +
        (demands.card : Int) ≤
      augmentedLedger object threshold dischargeScale piece +
        ((centres object threshold piece).card : Int) := by
  classical
  rw [augmentedLedger, augmentedLedgerWith, augmentedLedgerWith]
  have split : demands = centres object threshold piece ∪
      (demands \ centres object threshold piece) :=
    (Finset.union_sdiff_of_subset subset).symm
  have disjoint : Disjoint (centres object threshold piece)
      (demands \ centres object threshold piece) := Finset.disjoint_sdiff
  have cardEq : (demands.card : Int) =
      ((centres object threshold piece).card : Int) +
        ((demands \ centres object threshold piece).card : Int) := by
    have := Finset.card_sdiff_add_card_eq_card subset
    omega
  have sumEq : (∑ centre ∈ demands,
      scaledCentreCharge object threshold dischargeScale centre) =
      (∑ centre ∈ centres object threshold piece,
        scaledCentreCharge object threshold dischargeScale centre) +
      ∑ centre ∈ demands \ centres object threshold piece,
        scaledCentreCharge object threshold dischargeScale centre := by
    conv_lhs => rw [split]
    exact Finset.sum_union disjoint
  have extra : (∑ centre ∈ demands \ centres object threshold piece,
      scaledCentreCharge object threshold dischargeScale centre) +
      ((demands \ centres object threshold piece).card : Int) ≤ 0 := by
    have : (∑ centre ∈ demands \ centres object threshold piece,
        (scaledCentreCharge object threshold dischargeScale centre + 1)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro centre _
      rw [scaledCentreCharge]
      have := Int.natCast_nonneg
        (dischargeScale * (object.degree centre - threshold))
      linarith
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at this
    exact this
  rw [sumEq, cardEq]
  linarith

/-- A retained canonical component, with `Y_X` recovered definitionally. -/
abbrev CanonicalPiece (object : FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) := PieceIndex object packing

namespace CanonicalPiece

noncomputable abbrev vertices {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) : Finset object.Vertex :=
  TypeBCanonicalCarrier.support object piece

theorem vertices_subset_remainder {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) :
    piece.vertices ⊆ object.remainderSupport packing :=
  TypeBCanonicalCarrier.support_subset_remainder object piece

end CanonicalPiece

/-- Literal carrier atoms: vertex-ledger summands and incidence provenance. -/
abbrev SupportAtom (object : FiniteObject.{u}) :=
  Sum object.Vertex (object.Vertex × object.Vertex)

noncomputable def vertexAtoms (vertices : Finset object.Vertex) :
    Finset (SupportAtom object) :=
  vertices.image Sum.inl

noncomputable def incidenceAtoms
    (incidences : Finset (object.Vertex × object.Vertex)) :
    Finset (SupportAtom object) :=
  incidences.image Sum.inr

/-- Literal support of one indexed ordinary-reserve unit.  This is used only
to compute which reserve units a candidate actually meets. -/
noncomputable def reserveUnitSupport
    (unit : OrdinaryDeficiencyReserve.Carrier object) :
    Finset (SupportAtom object) := by
  classical
  exact match unit with
  | .inl deficiency => {Sum.inl deficiency.1}
  | .inr incidence =>
      {Sum.inl incidence.1, Sum.inl incidence.2, Sum.inr incidence}

/-! ## Exhaustive finite candidate data -/

/-- A literal local internal/mixed reserve block `Q`.  Its capacity is derived
from the charges of these selected ledger vertices.  The chosen non-window
incidences remain separate B1 carriers and are never identified with the core
charge of their far endpoints. -/
structure LocalReserveBlock (object : FiniteObject.{u}) where
  vertices : Finset object.Vertex

inductive CandidateData (object : FiniteObject.{u}) where
  | certificate (profile : TypeBFanClosedPorts.Profile object)
      (assigned : Finset object.Vertex)
  | positive (profile : TypeBFanClosedPorts.Profile object)
      (localReserve : LocalReserveBlock object)
      (chosenNonWindow : Finset (object.Vertex × object.Vertex))

namespace CandidateData

variable {threshold dischargeScale : Nat}
variable {packing : Finset (Finset object.Vertex)}
variable {piece : CanonicalPiece object packing} {hub : object.Vertex}

def profile (data : CandidateData object) : TypeBFanClosedPorts.Profile object :=
  match data with
  | .certificate profile _ => profile
  | .positive profile _ _ => profile

def localReserve (data : CandidateData object) : LocalReserveBlock object :=
  match data with
  | .certificate _ _ => ⟨∅⟩
  | .positive _ localReserve _ => localReserve

def chosenNonWindow (data : CandidateData object) :
    Finset (object.Vertex × object.Vertex) :=
  match data with
  | .certificate _ _ => ∅
  | .positive _ _ chosen => chosen

noncomputable def chargedVertices (data : CandidateData object)
    (threshold : Nat) (hub : object.Vertex) : Finset object.Vertex :=
  match data with
  | .certificate _ assigned => assigned
  | .positive profile localReserve _ =>
      closedNeighbours object threshold profile.envelope hub ∪
        localReserve.vertices

/-- The canonical window incidences and precisely those non-window incidences
whose far endpoint belongs to the selected actual block `Q`. -/
noncomputable def selectedIncidences (data : CandidateData object)
    (threshold : Nat) (packing : Finset (Finset object.Vertex))
    (hub : object.Vertex) : Finset (object.Vertex × object.Vertex) :=
  match data with
  | .certificate _ _ => ∅
  | .positive profile _ chosenNonWindow =>
      windowIncidenceSet object threshold profile.envelope
          (object.windowSupport packing) hub ∪
        chosenNonWindow

noncomputable def localReserveVertexUniverse
    (profile : TypeBFanClosedPorts.Profile object)
    (threshold : Nat) {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (hub : object.Vertex) :
    Finset object.Vertex :=
  (((nonWindowIncidenceSet object threshold profile.envelope
      (object.windowSupport packing) hub).image Prod.snd) ∩ piece.vertices) \
    (centres object threshold piece.vertices ∪
      closedNeighbours object threshold profile.envelope hub)

/-- Vertex atoms at both endpoints of every selected incidence. -/
noncomputable def incidenceEndpointAtoms
    (incidences : Finset (object.Vertex × object.Vertex)) :
    Finset (SupportAtom object) :=
  vertexAtoms (incidences.image Prod.fst ∪ incidences.image Prod.snd)

noncomputable def supportAtoms (data : CandidateData object)
    (threshold : Nat) (packing : Finset (Finset object.Vertex))
    (hub : object.Vertex) : Finset (SupportAtom object) :=
  vertexAtoms (insert hub (data.chargedVertices threshold hub)) ∪
    (incidenceEndpointAtoms (data.selectedIncidences threshold packing hub) ∪
      incidenceAtoms (data.selectedIncidences threshold packing hub))

/-- The ordinary-reserve units literally met by this candidate carrier.  No
unit is authored or assigned: this is the intersection induced by support. -/
noncomputable def consumedReserveUnits (data : CandidateData object)
    (threshold : Nat) {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (hub : object.Vertex) :
    Finset (OrdinaryDeficiencyReserve.Carrier object) := by
  classical
  exact (object.ordinaryDeficiencyReserve threshold packing piece.vertices).filter
    fun unit => ¬ Disjoint (reserveUnitSupport unit)
      (data.supportAtoms threshold packing hub)

theorem consumedReserveUnits_subset (data : CandidateData object)
    (threshold : Nat) {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (hub : object.Vertex) :
    data.consumedReserveUnits threshold piece hub ⊆
      object.ordinaryDeficiencyReserve threshold packing piece.vertices := by
  classical
  exact Finset.filter_subset _ _

/-- Exact common-scale capacity of a selected local reserve block. -/
noncomputable def localReserveCapacity₂
    (block : LocalReserveBlock object)
    (threshold dischargeScale : Nat)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) : Int :=
  2 * ∑ vertex ∈ block.vertices,
    scaledCoreCharge object threshold dischargeScale piece.vertices vertex

/-- The literal B1 half-incidence payment made by the chosen non-window
carriers.  This is independent of the local reserve block's core charge. -/
def PaysHybridB1 (data : CandidateData object)
    (threshold dischargeScale : Nat)
    {packing : Finset (Finset object.Vertex)} (hub : object.Vertex) : Prop :=
  match data with
  | .certificate _ _ => True
  | .positive profile _ chosen =>
      TypeBHybridIncidence.nonWindowDemand object threshold dischargeScale
          profile.envelope (object.windowSupport packing) hub ≤
        (dischargeScale : Int) * (chosen.card : Int)

/-- The candidate's exact common-scale subledger contribution.  Incidences
are provenance for the refinement; no incidence capacity is added to the core
charge a second time. -/
noncomputable def entryPayment₂ (data : CandidateData object)
    (threshold dischargeScale : Nat)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (hub : object.Vertex) : Int :=
  2 * (scaledCentreCharge object threshold dischargeScale hub +
    ∑ vertex ∈ data.chargedVertices threshold hub,
      scaledCoreCharge object threshold dischargeScale piece.vertices vertex)

def EntryRefines (data : CandidateData object)
    (threshold dischargeScale : Nat)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (hub : object.Vertex) : Prop :=
  0 ≤ data.entryPayment₂ threshold dischargeScale piece hub

/-- Eligibility is a finite test of the two manuscript candidate variants.
The positive case scans actual `Y_X` vertex blocks and tests their charge; no
local block is postulated. -/
def IsCandidate (data : CandidateData object)
    (threshold dischargeScale : Nat)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (hub : object.Vertex) : Prop :=
  data.profile ∈ profileCandidatesWith object (object.windowSupport packing) ∧
  data.profile.marked.fan.hub = hub ∧
  hub ∈ centres object threshold piece.vertices ∧
  data.chargedVertices threshold hub ⊆ piece.vertices ∧
  Disjoint (data.chargedVertices threshold hub)
    (centres object threshold piece.vertices) ∧
  data.EntryRefines threshold dischargeScale piece hub ∧
  data.PaysHybridB1 threshold dischargeScale (packing := packing) hub ∧
  match data with
  | .certificate profile assigned =>
      IsCertificateClosed object threshold dischargeScale profile.envelope hub ∧
        assigned ⊆ TypeBMarkedFan.neighbourRim object hub
  | .positive profile localReserve chosenNonWindow =>
      0 < scaledDeficit object threshold dischargeScale profile.envelope hub ∧
        localReserve.vertices ⊆
          localReserveVertexUniverse profile threshold piece hub ∧
        chosenNonWindow ⊆
          nonWindowIncidenceSet object threshold profile.envelope
            (object.windowSupport packing) hub

theorem IsCandidate.chargedVertices_subset
    {data : CandidateData object}
    (eligible : data.IsCandidate threshold dischargeScale piece hub) :
    data.chargedVertices threshold hub ⊆ piece.vertices :=
  eligible.2.2.2.1

theorem IsCandidate.chargedVertices_disjoint_centres
    {data : CandidateData object}
    (eligible : data.IsCandidate threshold dischargeScale piece hub) :
    Disjoint (data.chargedVertices threshold hub)
      (centres object threshold piece.vertices) :=
  eligible.2.2.2.2.1

theorem IsCandidate.entryRefines {data : CandidateData object}
    (eligible : data.IsCandidate threshold dischargeScale piece hub) :
    data.EntryRefines threshold dischargeScale piece hub :=
  eligible.2.2.2.2.2.1

theorem IsCandidate.paysHybridB1 {data : CandidateData object}
    (eligible : data.IsCandidate threshold dischargeScale piece hub) :
    data.PaysHybridB1 threshold dischargeScale (packing := packing) hub :=
  eligible.2.2.2.2.2.2.1

/-- Paying the exact remaining non-window demand implies the complete B1
half-incidence inequality by the definition of that remaining demand. -/
theorem paysHybridB1_total
    (profile : TypeBFanClosedPorts.Profile object)
    (localReserve : LocalReserveBlock object)
    (chosenNonWindow : Finset (object.Vertex × object.Vertex))
    (pays : (CandidateData.positive profile localReserve chosenNonWindow).PaysHybridB1
      threshold dischargeScale (packing := packing) hub) :
    2 * scaledDeficit object threshold dischargeScale profile.envelope hub ≤
      (dischargeScale : Int) *
        ((TypeBHybridIncidence.windowIncidences object threshold
            profile.envelope (object.windowSupport packing) hub : Int) +
          (chosenNonWindow.card : Int)) := by
  have demandLower :
      2 * scaledDeficit object threshold dischargeScale profile.envelope hub -
          (dischargeScale : Int) *
            (TypeBHybridIncidence.windowIncidences object threshold
              profile.envelope (object.windowSupport packing) hub : Int) ≤
        TypeBHybridIncidence.nonWindowDemand object threshold dischargeScale
          profile.envelope (object.windowSupport packing) hub := by
    simp only [TypeBHybridIncidence.nonWindowDemand]
    exact le_max_right _ _
  simp only [PaysHybridB1] at pays
  nlinarith

/-- Exact local B1 output for one positive candidate: its literal augmented
subledger contribution is nonnegative, and the chosen non-window incidence
carriers pay both the total hybrid deficit and its non-window remainder. -/
theorem positiveCandidate_localB1
    (profile : TypeBFanClosedPorts.Profile object)
    (localReserve : LocalReserveBlock object)
    (chosenNonWindow : Finset (object.Vertex × object.Vertex))
    (eligible : (CandidateData.positive profile localReserve chosenNonWindow).IsCandidate
      threshold dischargeScale piece hub) :
    0 ≤ (CandidateData.positive profile localReserve chosenNonWindow).entryPayment₂
        threshold dischargeScale piece hub ∧
      2 * scaledDeficit object threshold dischargeScale profile.envelope hub ≤
          (dischargeScale : Int) *
            ((TypeBHybridIncidence.windowIncidences object threshold
                profile.envelope (object.windowSupport packing) hub : Int) +
              (chosenNonWindow.card : Int)) ∧
        TypeBHybridIncidence.nonWindowDemand object threshold dischargeScale
            profile.envelope (object.windowSupport packing) hub ≤
          (dischargeScale : Int) * (chosenNonWindow.card : Int) := by
  refine ⟨eligible.entryRefines, ?_⟩
  exact ⟨paysHybridB1_total profile localReserve chosenNonWindow
      eligible.paysHybridB1,
    by simpa [PaysHybridB1] using eligible.paysHybridB1⟩

/-- The positive entry's exact subledger split.  `Q` contributes only the
charges of its selected vertices; the chosen incidence set remains the B1
payment certificate and contributes no second copy of core charge. -/
theorem positive_entryPayment₂_eq
    (profile : TypeBFanClosedPorts.Profile object)
    (localReserve : LocalReserveBlock object)
    (chosenNonWindow : Finset (object.Vertex × object.Vertex))
    (disjoint : Disjoint
      (closedNeighbours object threshold profile.envelope hub)
      localReserve.vertices) :
    (CandidateData.positive profile localReserve chosenNonWindow).entryPayment₂
        threshold dischargeScale piece hub =
      2 * (scaledCentreCharge object threshold dischargeScale hub +
        ∑ vertex ∈ closedNeighbours object threshold profile.envelope hub,
          scaledCoreCharge object threshold dischargeScale piece.vertices vertex) +
        localReserveCapacity₂ localReserve threshold dischargeScale piece := by
  rw [entryPayment₂, chargedVertices,
    Finset.sum_union disjoint]
  simp only [localReserveCapacity₂]
  ring

noncomputable def isCandidateDecidable (data : CandidateData object)
    (threshold dischargeScale : Nat)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (hub : object.Vertex) :
    Decidable (data.IsCandidate threshold dischargeScale piece hub) :=
  Classical.dec _

end CandidateData

/-- The exhaustive finite raw schedule.  Both `A_h` and `Q` range over every
finite subset of their literal graph-derived universes. -/
noncomputable def candidateDataSchedule (object : FiniteObject.{u})
    (threshold : Nat) {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (hub : object.Vertex) :
    List (CandidateData object) :=
  (profileCandidatesWith object (object.windowSupport packing)).flatMap
    fun profile =>
      ((((TypeBMarkedFan.neighbourRim object hub ∩ piece.vertices) \
          centres object threshold piece.vertices).powerset.toList.map
        fun assigned => CandidateData.certificate profile assigned) ++
      ((CandidateData.localReserveVertexUniverse profile threshold piece hub).powerset.toList.flatMap
        fun localReserveVertices =>
          (nonWindowIncidenceSet object threshold profile.envelope
            (object.windowSupport packing) hub).powerset.toList.map
              fun chosenNonWindow =>
                CandidateData.positive profile ⟨localReserveVertices⟩
                  chosenNonWindow))

noncomputable def candidateFamily (object : FiniteObject.{u})
    (threshold dischargeScale : Nat)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (hub : object.Vertex) :
    List (CandidateData object) := by
  classical
  exact (candidateDataSchedule object threshold piece hub).filter
    fun data => data.IsCandidate threshold dischargeScale piece hub

theorem mem_candidateFamily_iff
    {threshold dischargeScale : Nat}
    {packing : Finset (Finset object.Vertex)}
    {piece : CanonicalPiece object packing} {hub : object.Vertex}
    {data : CandidateData object} :
    data ∈ candidateFamily object threshold dischargeScale piece hub ↔
      data ∈ candidateDataSchedule object threshold piece hub ∧
        data.IsCandidate threshold dischargeScale piece hub := by
  classical
  simp [candidateFamily]

/-! ## The finite B2 choice and exact global partition -/

structure DisjointChoice (object : FiniteObject.{u})
    (threshold dischargeScale : Nat)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (demands : Finset object.Vertex) where
  entry : ∀ hub ∈ demands, CandidateData object
  eligible : ∀ hub (member : hub ∈ demands),
    entry hub member ∈ candidateFamily object threshold dischargeScale piece hub
  carrierDisjoint : ∀ left (leftMem : left ∈ demands)
      right (rightMem : right ∈ demands), left ≠ right →
    Disjoint ((entry left leftMem).supportAtoms threshold packing left)
      ((entry right rightMem).supportAtoms threshold packing right)
  reserveDisjoint : ∀ left (leftMem : left ∈ demands)
      right (rightMem : right ∈ demands), left ≠ right →
    Disjoint ((entry left leftMem).consumedReserveUnits threshold piece left)
      ((entry right rightMem).consumedReserveUnits threshold piece right)

def HasDisjointChoice (object : FiniteObject.{u})
    (threshold dischargeScale : Nat)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (demands : Finset object.Vertex) : Prop :=
  Nonempty (DisjointChoice object threshold dischargeScale piece demands)

theorem hasDisjointChoice_empty (object : FiniteObject.{u})
    (threshold dischargeScale : Nat)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) :
    HasDisjointChoice object threshold dischargeScale piece ∅ := by
  classical
  exact ⟨{
    entry := fun hub member => False.elim (Finset.notMem_empty hub member)
    eligible := fun hub member => False.elim (Finset.notMem_empty hub member)
    carrierDisjoint := fun left leftMem =>
      False.elim (Finset.notMem_empty left leftMem)
    reserveDisjoint := fun left leftMem =>
      False.elim (Finset.notMem_empty left leftMem) }⟩

/-- **The B2 disjoint ledger of an assigned Type B support `X = (Y_X, H_X)`**
(`def:typeB-assigned-ledger`): a disjoint choice at the assigned centres
`demands = H_X`, which are high centres and include every high centre of the
counted core (`def:canonical-decomp`: for the ordinary support they are exactly
the core's high centres; for a decorated handoff envelope the core has none and
`H_X` is the decoration set). -/
structure DisjointLedger (object : FiniteObject.{u})
    (threshold dischargeScale : Nat)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (demands : Finset object.Vertex) where
  choice : DisjointChoice object threshold dischargeScale piece demands
  demands_high : ∀ hub ∈ demands, Graph.IsHighCentre object threshold hub
  centres_subset : centres object threshold piece.vertices ⊆ demands

namespace DisjointLedger

variable {threshold dischargeScale : Nat}
variable {packing : Finset (Finset object.Vertex)}
variable {piece : CanonicalPiece object packing}
variable {demands : Finset object.Vertex}

theorem demands_inter_subset_centres
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    demands ∩ piece.vertices ⊆ centres object threshold piece.vertices := by
  intro hub member
  rw [Finset.mem_inter] at member
  exact mem_centres.mpr ⟨member.2, ledger.demands_high hub member.1⟩

theorem entry_isCandidate
    (ledger : DisjointLedger object threshold dischargeScale piece demands)
    (hub : object.Vertex) (member : hub ∈ demands) :
    (ledger.choice.entry hub member).IsCandidate threshold dischargeScale piece hub :=
  (mem_candidateFamily_iff.mp (ledger.choice.eligible hub member)).2

theorem entry_refines
    (ledger : DisjointLedger object threshold dischargeScale piece demands)
    (hub : object.Vertex) (member : hub ∈ demands) :
    (ledger.choice.entry hub member).EntryRefines
      threshold dischargeScale piece hub :=
  (ledger.entry_isCandidate hub member).entryRefines

/-- The literal indexed ordinary-reserve units met by the selected carriers. -/
noncomputable def consumedReserveUnits
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    Finset (OrdinaryDeficiencyReserve.Carrier object) :=
  (demands).attach.biUnion fun hub =>
    (ledger.choice.entry hub.1 hub.2).consumedReserveUnits threshold piece hub.1

theorem consumedReserveUnits_subset
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    ledger.consumedReserveUnits ⊆
      object.ordinaryDeficiencyReserve threshold packing piece.vertices := by
  classical
  intro unit member
  obtain ⟨hub, _hubMem, unitMem⟩ := Finset.mem_biUnion.mp member
  exact CandidateData.consumedReserveUnits_subset
    (ledger.choice.entry hub.1 hub.2) threshold piece hub.1 unitMem

noncomputable def remainingReserve
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    Finset (OrdinaryDeficiencyReserve.Carrier object) :=
  object.ordinaryDeficiencyReserve threshold packing piece.vertices \
    ledger.consumedReserveUnits

theorem consumed_union_remainingReserve
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    ledger.consumedReserveUnits ∪ ledger.remainingReserve =
      object.ordinaryDeficiencyReserve threshold packing piece.vertices := by
  classical
  exact Finset.union_sdiff_of_subset ledger.consumedReserveUnits_subset

theorem consumed_disjoint_remainingReserve
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    Disjoint ledger.consumedReserveUnits ledger.remainingReserve := by
  classical
  rw [Finset.disjoint_left]
  intro unit consumed remaining
  exact (Finset.mem_sdiff.mp remaining).2 consumed

noncomputable def consumedReserveCapacity
    (ledger : DisjointLedger object threshold dischargeScale piece demands) : Int :=
  OrdinaryDeficiencyReserve.capacity dischargeScale ledger.consumedReserveUnits

noncomputable def remainingReserveCapacity
    (ledger : DisjointLedger object threshold dischargeScale piece demands) : Int :=
  OrdinaryDeficiencyReserve.capacity dischargeScale ledger.remainingReserve

theorem consumed_add_remainingReserveCapacity
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    ledger.consumedReserveCapacity + ledger.remainingReserveCapacity =
      OrdinaryDeficiencyReserve.capacity dischargeScale
        (object.ordinaryDeficiencyReserve threshold packing piece.vertices) := by
  rw [consumedReserveCapacity, remainingReserveCapacity,
    ← OrdinaryDeficiencyReserve.capacity_union
      ledger.consumed_disjoint_remainingReserve,
    ledger.consumed_union_remainingReserve]

noncomputable def chargedVertexSupport
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    Finset object.Vertex :=
  (demands).attach.biUnion fun hub =>
    (ledger.choice.entry hub.1 hub.2).chargedVertices threshold hub.1

theorem chargedVertices_disjoint
    (ledger : DisjointLedger object threshold dischargeScale piece demands)
    (left : object.Vertex) (leftMem : left ∈ demands)
    (right : object.Vertex) (rightMem : right ∈ demands)
    (distinct : left ≠ right) :
    Disjoint
      ((ledger.choice.entry left leftMem).chargedVertices threshold left)
      ((ledger.choice.entry right rightMem).chargedVertices threshold right) := by
  classical
  rw [Finset.disjoint_left]
  intro vertex leftVertex rightVertex
  have leftAtom : Sum.inl vertex ∈
      (ledger.choice.entry left leftMem).supportAtoms threshold packing left := by
    rw [CandidateData.supportAtoms, Finset.mem_union]
    exact Or.inl (Finset.mem_image.mpr
      ⟨vertex, Finset.mem_insert_of_mem leftVertex, rfl⟩)
  have rightAtom : Sum.inl vertex ∈
      (ledger.choice.entry right rightMem).supportAtoms threshold packing right := by
    rw [CandidateData.supportAtoms, Finset.mem_union]
    exact Or.inl (Finset.mem_image.mpr
      ⟨vertex, Finset.mem_insert_of_mem rightVertex, rfl⟩)
  exact (Finset.disjoint_left.mp
    (ledger.choice.carrierDisjoint left leftMem right rightMem distinct))
      leftAtom rightAtom

theorem chargedVertexSupport_subset
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    ledger.chargedVertexSupport ⊆ piece.vertices := by
  classical
  intro vertex member
  obtain ⟨hub, _, vertexMem⟩ := Finset.mem_biUnion.mp member
  exact (ledger.entry_isCandidate hub.1 hub.2).chargedVertices_subset vertexMem

theorem chargedVertexSupport_disjoint_centres
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    Disjoint ledger.chargedVertexSupport demands := by
  classical
  rw [Finset.disjoint_left]
  intro vertex charged centreMem
  obtain ⟨hub, _, vertexMem⟩ := Finset.mem_biUnion.mp charged
  have inPiece : vertex ∈ piece.vertices :=
    (ledger.entry_isCandidate hub.1 hub.2).chargedVertices_subset vertexMem
  have inCentres : vertex ∈ centres object threshold piece.vertices :=
    ledger.demands_inter_subset_centres (Finset.mem_inter.mpr ⟨centreMem, inPiece⟩)
  exact (Finset.disjoint_left.mp
    (ledger.entry_isCandidate hub.1 hub.2).chargedVertices_disjoint_centres)
      vertexMem inCentres

theorem chargedVertexSupport_disjoint_demandsInPiece
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    Disjoint ledger.chargedVertexSupport (demands ∩ piece.vertices) :=
  Finset.disjoint_of_subset_right Finset.inter_subset_left
    ledger.chargedVertexSupport_disjoint_centres

noncomputable def remainingCore
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    Finset object.Vertex :=
  piece.vertices \
    (demands ∪ ledger.chargedVertexSupport)

noncomputable def removedVertices
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    Finset object.Vertex :=
  demands ∪ ledger.chargedVertexSupport

theorem remainingCore_subset
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    ledger.remainingCore ⊆ piece.vertices :=
  Finset.sdiff_subset

theorem centre_mem_removedVertices
    (ledger : DisjointLedger object threshold dischargeScale piece demands)
    {hub : object.Vertex}
    (member : hub ∈ demands) :
    hub ∈ ledger.removedVertices :=
  Finset.mem_union_left _ member

theorem noHighCentre_remaining
    (ledger : DisjointLedger object threshold dischargeScale piece demands)
    {hub : object.Vertex} (member : hub ∈ ledger.remainingCore) :
    ¬ Graph.IsHighCentre object threshold hub := by
  intro high
  have inPiece := ledger.remainingCore_subset member
  have inCentres := mem_centres.mpr ⟨inPiece, high⟩
  exact (Finset.mem_sdiff.mp member).2
    (ledger.centre_mem_removedVertices (ledger.centres_subset inCentres))

noncomputable def selectedEntryPayment₂
    (ledger : DisjointLedger object threshold dischargeScale piece demands) : Int :=
  ∑ hub ∈ (demands).attach,
    (ledger.choice.entry hub.1 hub.2).entryPayment₂
      threshold dischargeScale piece hub.1

theorem sum_chargedVertexSupport
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    (∑ vertex ∈ ledger.chargedVertexSupport,
        scaledCoreCharge object threshold dischargeScale piece.vertices vertex) =
      ∑ hub ∈ (demands).attach,
        ∑ vertex ∈ (ledger.choice.entry hub.1 hub.2).chargedVertices
            threshold hub.1,
          scaledCoreCharge object threshold dischargeScale piece.vertices vertex := by
  classical
  rw [chargedVertexSupport, Finset.sum_biUnion]
  intro left _ right _ distinct
  exact ledger.chargedVertices_disjoint left.1 left.2 right.1 right.2
    (fun equality => distinct (Subtype.ext equality))

theorem selectedEntryPayment₂_eq
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    ledger.selectedEntryPayment₂ =
      2 * (∑ centre ∈ demands,
        scaledCentreCharge object threshold dischargeScale centre) +
      2 * ∑ vertex ∈ ledger.chargedVertexSupport,
        scaledCoreCharge object threshold dischargeScale piece.vertices vertex := by
  classical
  rw [selectedEntryPayment₂, ledger.sum_chargedVertexSupport]
  simp_rw [CandidateData.entryPayment₂, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have centreAttach := congrArg (fun value : Int => 2 * value)
    (Finset.sum_attach (demands)
      (fun centre => scaledCentreCharge object threshold dischargeScale centre))
  rw [centreAttach]
  rw [← Finset.mul_sum]

/-- B2(c), at the common scale `2s`: the selected actual vertex subledgers and
the remaining actual core form a literal disjoint partition of the counted core;
the assigned centres inside the core are counted once as core vertices, and
every assigned centre contributes its `¼` (`def:typeB-assigned-ledger`,
(B-ledger)). -/
theorem augmentedLedger_partition
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    2 * (augmentedLedgerWith object threshold dischargeScale piece.vertices demands +
      (demands.card : Int)) =
      ledger.selectedEntryPayment₂ +
        2 * (∑ vertex ∈ ledger.remainingCore,
          scaledCoreCharge object threshold dischargeScale piece.vertices vertex) +
        2 * (∑ centre ∈ demands ∩ piece.vertices,
          scaledCoreCharge object threshold dischargeScale piece.vertices centre) +
        2 * (demands.card : Int) := by
  classical
  have selectedSubset :
      demands ∩ piece.vertices ∪ ledger.chargedVertexSupport ⊆ piece.vertices :=
    Finset.union_subset Finset.inter_subset_right ledger.chargedVertexSupport_subset
  have remainingEq : ledger.remainingCore =
      piece.vertices \ (demands ∩ piece.vertices ∪ ledger.chargedVertexSupport) := by
    rw [remainingCore]
    ext vertex
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    tauto
  have selectedDisjoint : Disjoint
      (demands ∩ piece.vertices ∪ ledger.chargedVertexSupport)
      ledger.remainingCore := by
    rw [Finset.disjoint_left]
    intro vertex selected remaining
    rw [remainingEq] at remaining
    exact (Finset.mem_sdiff.mp remaining).2 selected
  have cover :
      (demands ∩ piece.vertices ∪ ledger.chargedVertexSupport) ∪
          ledger.remainingCore = piece.vertices := by
    rw [remainingEq]
    exact Finset.union_sdiff_of_subset selectedSubset
  have coreSplit :
      (∑ vertex ∈ piece.vertices,
          scaledCoreCharge object threshold dischargeScale piece.vertices vertex) =
        (∑ centre ∈ demands ∩ piece.vertices,
          scaledCoreCharge object threshold dischargeScale piece.vertices centre) +
        (∑ vertex ∈ ledger.chargedVertexSupport,
          scaledCoreCharge object threshold dischargeScale piece.vertices vertex) +
        ∑ vertex ∈ ledger.remainingCore,
          scaledCoreCharge object threshold dischargeScale piece.vertices vertex := by
    let charge : object.Vertex → Int := fun vertex =>
      scaledCoreCharge object threshold dischargeScale piece.vertices vertex
    change (∑ vertex ∈ piece.vertices, charge vertex) =
      (∑ centre ∈ demands ∩ piece.vertices, charge centre) +
      (∑ vertex ∈ ledger.chargedVertexSupport, charge vertex) +
      ∑ vertex ∈ ledger.remainingCore, charge vertex
    calc
      (∑ vertex ∈ piece.vertices, charge vertex) =
          ∑ vertex ∈
            ((demands ∩ piece.vertices ∪
                ledger.chargedVertexSupport) ∪ ledger.remainingCore),
              charge vertex :=
        congrArg (fun vertices : Finset object.Vertex =>
          ∑ vertex ∈ vertices, charge vertex) cover.symm
      _ = (∑ vertex ∈ demands ∩ piece.vertices ∪
              ledger.chargedVertexSupport, charge vertex) +
            ∑ vertex ∈ ledger.remainingCore, charge vertex :=
        Finset.sum_union selectedDisjoint
      _ = (∑ centre ∈ demands ∩ piece.vertices,
              charge centre) +
            (∑ vertex ∈ ledger.chargedVertexSupport, charge vertex) +
            ∑ vertex ∈ ledger.remainingCore, charge vertex := by
        rw [Finset.sum_union ledger.chargedVertexSupport_disjoint_demandsInPiece.symm]
  rw [augmentedLedgerWith, coreSplit, ledger.selectedEntryPayment₂_eq]
  ring

theorem selectedEntryPayment₂_nonnegative
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    0 ≤ ledger.selectedEntryPayment₂ := by
  classical
  rw [selectedEntryPayment₂]
  apply Finset.sum_nonneg
  intro hub _
  exact (ledger.entry_isCandidate hub.1 hub.2).entryRefines

/-- The exact successful B2 refinement, with no authored partition proof. -/
structure ExactAugmentedLedgerRefinement
    (ledger : DisjointLedger object threshold dischargeScale piece demands) : Prop where
  partition :
    2 * (augmentedLedgerWith object threshold dischargeScale piece.vertices demands +
      (demands.card : Int)) =
      ledger.selectedEntryPayment₂ +
        2 * (∑ vertex ∈ ledger.remainingCore,
          scaledCoreCharge object threshold dischargeScale piece.vertices vertex) +
        2 * (∑ centre ∈ demands ∩ piece.vertices,
          scaledCoreCharge object threshold dischargeScale piece.vertices centre) +
        2 * (demands.card : Int)
  selectedNonnegative : 0 ≤ ledger.selectedEntryPayment₂
  carrierDisjoint : ∀ left
      (leftMem : left ∈ demands)
      right (rightMem : right ∈ demands),
    left ≠ right →
      Disjoint
        ((ledger.choice.entry left leftMem).supportAtoms threshold packing left)
        ((ledger.choice.entry right rightMem).supportAtoms threshold packing right)
  reserveDisjoint : ∀ left
      (leftMem : left ∈ demands)
      right (rightMem : right ∈ demands),
    left ≠ right →
      Disjoint
        ((ledger.choice.entry left leftMem).consumedReserveUnits threshold piece left)
        ((ledger.choice.entry right rightMem).consumedReserveUnits threshold piece right)
  reservePartition :
    ledger.consumedReserveUnits ∪ ledger.remainingReserve =
      object.ordinaryDeficiencyReserve threshold packing piece.vertices
  reserveCapacityPartition :
    ledger.consumedReserveCapacity + ledger.remainingReserveCapacity =
      OrdinaryDeficiencyReserve.capacity dischargeScale
        (object.ordinaryDeficiencyReserve threshold packing piece.vertices)

theorem exactAugmentedLedgerRefinement
    (ledger : DisjointLedger object threshold dischargeScale piece demands) :
    ledger.ExactAugmentedLedgerRefinement :=
  ⟨ledger.augmentedLedger_partition, ledger.selectedEntryPayment₂_nonnegative,
    ledger.choice.carrierDisjoint, ledger.choice.reserveDisjoint,
    ledger.consumed_union_remainingReserve,
    ledger.consumed_add_remainingReserveCapacity⟩

end DisjointLedger

/-! ## Finite failure and minimal overlap -/

structure OverlapObstruction (object : FiniteObject.{u})
    (threshold dischargeScale : Nat)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) where
  demands : Finset object.Vertex
  demands_high : ∀ hub ∈ demands, Graph.IsHighCentre object threshold hub
  demands_nonempty : demands.Nonempty
  noDisjointChoice :
    ¬ HasDisjointChoice object threshold dischargeScale piece demands
  minimal : ∀ sub ⊂ demands, sub.Nonempty →
    HasDisjointChoice object threshold dischargeScale piece sub

theorem exists_overlapObstruction_of_not_hasDisjointChoice
    (object : FiniteObject.{u}) (threshold dischargeScale : Nat)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (demands : Finset object.Vertex)
    (high : ∀ hub ∈ demands, Graph.IsHighCentre object threshold hub)
    (failure : ¬ HasDisjointChoice object threshold dischargeScale piece demands) :
    Nonempty (OverlapObstruction object threshold dischargeScale piece) := by
  classical
  have nonempty : demands.Nonempty := by
    rcases Finset.eq_empty_or_nonempty demands with rfl | present
    · exact absurd (hasDisjointChoice_empty object threshold dischargeScale piece)
        failure
    · exact present
  let failing : Finset (Finset object.Vertex) :=
    demands.powerset.filter fun family => family.Nonempty ∧
      ¬ HasDisjointChoice object threshold dischargeScale piece family
  have selfMember : demands ∈ failing := by simp [failing, nonempty, failure]
  obtain ⟨minimalFamily, minimalMember, minimalCard⟩ :=
    failing.exists_min_image Finset.card ⟨demands, selfMember⟩
  have data : minimalFamily ⊆ demands ∧ minimalFamily.Nonempty ∧
      ¬ HasDisjointChoice object threshold dischargeScale piece minimalFamily := by
    simpa [failing] using minimalMember
  refine ⟨{
    demands := minimalFamily
    demands_high := fun hub member => high hub (data.1 member)
    demands_nonempty := data.2.1
    noDisjointChoice := data.2.2
    minimal := ?_ }⟩
  intro sub proper subNonempty
  by_contra subFailure
  have subMember : sub ∈ failing := by
    simp [failing, proper.subset.trans data.1, subNonempty, subFailure]
  exact (Nat.not_lt_of_ge (minimalCard sub subMember))
    (Finset.card_lt_card proper)

/-- The B2 alternative at an assigned support `(Y_X, H_X)`: a disjoint choice at
the assigned centres, or a minimal overlap obstruction among them. -/
theorem b2_or_overlap (object : FiniteObject.{u})
    (threshold dischargeScale : Nat)
    {packing : Finset (Finset object.Vertex)}
    (piece : CanonicalPiece object packing) (demands : Finset object.Vertex)
    (high : ∀ hub ∈ demands, Graph.IsHighCentre object threshold hub) :
    HasDisjointChoice object threshold dischargeScale piece demands ∨
      Nonempty (OverlapObstruction object threshold dischargeScale piece) := by
  classical
  by_cases choice : HasDisjointChoice object threshold dischargeScale piece demands
  · exact Or.inl choice
  · exact Or.inr (exists_overlapObstruction_of_not_hasDisjointChoice object
      threshold dischargeScale piece demands high choice)

theorem centres_high (object : FiniteObject.{u}) (threshold : Nat)
    (piece : Finset object.Vertex) :
    ∀ hub ∈ centres object threshold piece, Graph.IsHighCentre object threshold hub :=
  fun _hub member => (mem_centres.mp member).2

end

end Hypostructure.Graph.TypeBRefinedSupport
