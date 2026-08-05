import Hypostructure.Graph.HighCentreNormalForm
import Hypostructure.Graph.BoundaryDemand

/-!
# The refined support ledger and its overlap obstruction

This is the mathematics of the *global* half of manuscript node `[72]` (and of
node `[81]`, the same question on the degree-four branch): clause (B2) of
`def:typeB-bridge-statements`, together with `def:typeB-ledger-carriers`,
`def:typeB-candidate-ledger`, `def:typeB-overlap-obstruction`,
`lem:typeB-maximal-completion` and `lem:typeB-bridge-to-overlap`.

B2 asks a *simultaneous choice* question.  Each assigned high-degree centre of a
connected assigned support carries a finite set of candidate ledger entries, and
the ledger exists when one entry can be chosen at every centre at once with
pairwise disjoint carriers.  That is not a local count: an entry that pays at one
centre may need a carrier another centre has already spent.  Failure of the
choice is therefore not "some centre cannot pay" but "no global selection is
disjoint", and `lem:typeB-bridge-to-overlap` turns exactly that failure into a
*minimal* overlap obstruction -- a smallest failing subfamily.

## Charges are scaled integers

`def:typeB-assigned-ledger` writes `ch_X(v) = δ_X^+(v) − α` for a non-centre
vertex and `ch_X(h) = −(d_G(h) − δ) − α` for an assigned centre, at the
discharge scale `α = 1/s`, and `def:typeB-ledger-carriers` gives a chosen
incidence the capacity `1/2`.  Every comparison below is made after multiplying
through by `2s`, exactly as `Graph.NegativeNetCharge` multiplies through by `s`:
the reciprocals never appear, nothing rounds, and no numeral other than the
scaling itself is written.

Nothing here is specialized to a manuscript: the baseline, the discharge scale,
the support and the centre family are all parameters.
-/

namespace Hypostructure.Graph.TypeBRefinedSupport

open Hypostructure

universe u

variable {object : FiniteObject.{u}}

/-! ## The assigned centre family -/

/-- **`H_X`**, the assigned high-degree centres of a support: the vertices of the
support whose ambient degree is above the baseline. -/
noncomputable def centres (object : FiniteObject.{u}) (threshold : Nat)
    (piece : Finset object.Vertex) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidablePred (Graph.IsHighCentre object threshold) :=
    fun _ => Classical.dec _
  exact piece.filter (Graph.IsHighCentre object threshold)

theorem mem_centres {threshold : Nat} {piece : Finset object.Vertex}
    {vertex : object.Vertex} :
    vertex ∈ centres object threshold piece ↔
      vertex ∈ piece ∧ Graph.IsHighCentre object threshold vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidablePred (Graph.IsHighCentre object threshold) :=
    fun _ => Classical.dec _
  simp [centres, Finset.mem_filter]

theorem centres_subset {threshold : Nat} {piece : Finset object.Vertex} :
    centres object threshold piece ⊆ piece := by
  intro vertex member
  exact (mem_centres.mp member).1

/-! ## `def:typeB-ledger-carriers`

A carrier is either a vertex of the support charge ledger -- a non-centre vertex
or the assigned centre itself -- or one of the half-capacity incidences the
positive-deficit entry spends.  An incidence is named by its ordered pair of
endpoints, which is what makes two entries' incidence sets comparable. -/

/-- **A Type B carrier**: a vertex carrier or an incidence carrier. -/
abbrev Carrier (object : FiniteObject.{u}) : Type u :=
  object.Vertex ⊕ (object.Vertex × object.Vertex)

/-! ## `def:typeB-candidate-ledger`

One structure covers both clauses.  Clause (a), the certificate-closed entry, is
the case `chosen = ∅`: the centre together with a set of incident non-centre
vertices whose augmented charge pays the centre charge.  Clause (b), the
positive-deficit hybrid entry, adds the chosen half-capacity incidences, each
contributing `1/2` -- `s` after the `2s` scaling.  `pays` is the one inequality
both clauses ask for. -/

/-- **A candidate Type B ledger entry at the demand centre `hub`.** -/
structure CandidateEntry (object : FiniteObject.{u}) (threshold dischargeScale : Nat)
    (piece : Finset object.Vertex) (hub : object.Vertex) where
  /-- `A_h`, the assigned non-centre vertices of the entry. -/
  assigned : Finset object.Vertex
  /-- `A_h ⊆ N(h)`. -/
  assigned_adjacent : ∀ vertex ∈ assigned, object.graph.Adj hub vertex
  /-- `A_h ⊆ X`: the charge spent is the support's own. -/
  assigned_subset : assigned ⊆ piece
  /-- `A_h ∩ H_X = ∅`: an assigned centre is never spent as a non-centre
  carrier. -/
  assigned_notCentre :
    ∀ vertex ∈ assigned, vertex ∉ centres object threshold piece
  /-- The chosen half-capacity incidences of the hybrid entry. -/
  chosen : Finset (object.Vertex × object.Vertex)
  /-- Each chosen incidence leaves a vertex the entry itself owns. -/
  chosen_owned :
    ∀ incidence ∈ chosen,
      (incidence.1 = hub ∨ incidence.1 ∈ assigned) ∧
        object.graph.Adj incidence.1 incidence.2
  /-- **The entry pays.**  `ch_X(h) + Σ_{v ∈ A_h} ch_X(v) + ½·|chosen| ≥ 0`,
  cleared of denominators at the scale `2s`. -/
  pays :
    2 * dischargeScale * (object.degree hub - threshold) + 2 + 2 * assigned.card ≤
      2 * dischargeScale *
          (∑ vertex ∈ assigned, (threshold - object.internalDegree piece vertex)) +
        dischargeScale * chosen.card

namespace CandidateEntry

variable {threshold dischargeScale : Nat} {piece : Finset object.Vertex}
variable {hub : object.Vertex}

/-- **The carrier support of an entry**: the centre and its assigned vertices,
together with the incidences the entry spends. -/
noncomputable def carriers
    (entry : CandidateEntry object threshold dischargeScale piece hub) :
    Finset (Carrier object) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (insert hub entry.assigned).disjSum entry.chosen

theorem hub_mem_carriers
    (entry : CandidateEntry object threshold dischargeScale piece hub) :
    Sum.inl hub ∈ entry.carriers := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp [carriers, Finset.inl_mem_disjSum]

/-- **Disjoint carriers force distinct centres**, which is the manuscript's "no
carrier is assigned to two different fan centres" read at the centre itself. -/
theorem hub_ne_of_disjoint_carriers {other : object.Vertex}
    (entry : CandidateEntry object threshold dischargeScale piece hub)
    (otherEntry : CandidateEntry object threshold dischargeScale piece other)
    (disjoint : Disjoint entry.carriers otherEntry.carriers) : hub ≠ other := by
  intro same
  refine Finset.disjoint_left.mp disjoint entry.hub_mem_carriers ?_
  rw [same]
  exact otherEntry.hub_mem_carriers

end CandidateEntry

/-! ## `def:typeB-candidate-ledger`: the disjoint refined ledger -/

/-- **A disjoint refined Type B ledger for a finite family of demands.**

One candidate entry at every demand, with pairwise disjoint carriers.  This is
clauses (a)--(c) of B2 in one statement: (a) and (b) are the entries themselves,
and (c) -- mutual disjointness of the certificate-closed, reserve and
half-incidence entries -- is the disjointness of the carriers. -/
def HasDisjointChoice (object : FiniteObject.{u}) (threshold dischargeScale : Nat)
    (piece demands : Finset object.Vertex) : Prop :=
  ∃ entry : ∀ hub ∈ demands,
      CandidateEntry object threshold dischargeScale piece hub,
    ∀ (left : object.Vertex) (leftMember : left ∈ demands)
      (right : object.Vertex) (rightMember : right ∈ demands), left ≠ right →
      Disjoint (entry left leftMember).carriers (entry right rightMember).carriers

variable {threshold dischargeScale : Nat} {piece : Finset object.Vertex}

/-- The empty demand family has a disjoint refined ledger. -/
theorem hasDisjointChoice_empty :
    HasDisjointChoice object threshold dischargeScale piece ∅ :=
  ⟨fun _hub member => absurd member (Finset.notMem_empty _),
    fun _left leftMember => absurd leftMember (Finset.notMem_empty _)⟩

/-- **A disjoint refined ledger restricts to every subfamily of demands.**  This
is what makes a *minimal* failing subfamily meaningful. -/
theorem hasDisjointChoice_mono {demands sub : Finset object.Vertex}
    (contained : sub ⊆ demands)
    (choice : HasDisjointChoice object threshold dischargeScale piece demands) :
    HasDisjointChoice object threshold dischargeScale piece sub := by
  obtain ⟨entry, disjoint⟩ := choice
  exact ⟨fun hub member => entry hub (contained member),
    fun left leftMember right rightMember different =>
      disjoint left (contained leftMember) right (contained rightMember) different⟩

/-- **`def:typeB-candidate-ledger`, maximality; `def:typeB-bridge-statements`
clause (d).**  After the entries are removed the remaining core carries no
high-degree centre: every assigned centre of the support has been entered as a
demand. -/
def IsMaximal (object : FiniteObject.{u}) (threshold : Nat)
    (piece demands : Finset object.Vertex) : Prop :=
  centres object threshold piece ⊆ demands

/-- **`def:typeB-bridge-statements` (B2), packaged.**  The refined support ledger
of a connected assigned Type B support: a demand family drawn from its assigned
centres, a disjoint choice of candidate entries, and maximality. -/
structure RefinedSupportAssignment (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (piece : Finset object.Vertex) where
  /-- `𝒟`, the Type B demands. -/
  demands : Finset object.Vertex
  /-- Every demand is an assigned high-degree centre of the support. -/
  demands_subset : demands ⊆ centres object threshold piece
  /-- Clauses (a)--(c): the disjoint choice. -/
  disjointChoice :
    HasDisjointChoice object threshold dischargeScale piece demands
  /-- Clause (d): maximality. -/
  maximal : IsMaximal object threshold piece demands

/-- **`def:typeB-overlap-obstruction`.**  A minimal Type B overlap obstruction: a
nonempty family of demands with no disjoint choice, every proper nonempty
subfamily of which does have one. -/
structure OverlapObstruction (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (piece : Finset object.Vertex) where
  /-- `𝒟`, the demand family the obstruction is carried by. -/
  demands : Finset object.Vertex
  /-- Every demand is an assigned high-degree centre of the support. -/
  demands_subset : demands ⊆ centres object threshold piece
  /-- `𝒟` is nonempty. -/
  demands_nonempty : demands.Nonempty
  /-- No choice of one candidate entry per demand has pairwise disjoint
  carriers. -/
  noDisjointChoice :
    ¬ HasDisjointChoice object threshold dischargeScale piece demands
  /-- Minimality: every proper nonempty subfamily does admit a disjoint
  choice. -/
  minimal : ∀ sub ⊂ demands, sub.Nonempty →
    HasDisjointChoice object threshold dischargeScale piece sub

/-! ## `lem:typeB-bridge-to-overlap` -/

/-- **`lem:typeB-bridge-to-overlap`.**

If the disjoint-carrier part of B2 fails for a demand family, the support
carries a minimal Type B overlap obstruction: among the nonempty subfamilies
whose disjoint choice fails, one of least cardinality is minimal by
construction.

The candidate entries are a finite family because the support is finite, which
is why the minimization is available at all -- the manuscript's own reason. -/
theorem exists_overlapObstruction_of_not_hasDisjointChoice
    {demands : Finset object.Vertex}
    (contained : demands ⊆ centres object threshold piece)
    (failure :
      ¬ HasDisjointChoice object threshold dischargeScale piece demands) :
    Nonempty (OverlapObstruction object threshold dischargeScale piece) := by
  classical
  -- The empty family always has a choice, so a failing family is nonempty.
  have nonempty : demands.Nonempty := by
    rcases Finset.eq_empty_or_nonempty demands with empty | witness
    · exact absurd (empty ▸ hasDisjointChoice_empty) failure
    · exact witness
  -- The failing nonempty subfamilies, as a finset.
  set failing :=
    demands.powerset.filter
      (fun family => family.Nonempty ∧
        ¬ HasDisjointChoice object threshold dischargeScale piece family)
    with failingDef
  have selfMember : demands ∈ failing := by
    rw [failingDef, Finset.mem_filter]
    exact ⟨Finset.mem_powerset.2 (subset_refl _), nonempty, failure⟩
  obtain ⟨minimal, minimalMember, least⟩ :=
    failing.exists_min_image Finset.card ⟨demands, selfMember⟩
  rw [failingDef, Finset.mem_filter, Finset.mem_powerset] at minimalMember
  obtain ⟨minimalContained, minimalNonempty, minimalFailure⟩ := minimalMember
  refine ⟨{
    demands := minimal
    demands_subset := minimalContained.trans contained
    demands_nonempty := minimalNonempty
    noDisjointChoice := minimalFailure
    minimal := ?_ }⟩
  intro sub proper subNonempty
  by_contra subFailure
  have subMember : sub ∈ failing := by
    rw [failingDef, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨(proper.subset.trans minimalContained), subNonempty, subFailure⟩
  exact absurd (Finset.card_lt_card proper) (Nat.not_lt.2 (least sub subMember))

/-- **The node-`[72]` alternative, exhaustively.**  Either the assigned centres
of the support admit the disjoint refined ledger of B2, or the support carries a
minimal Type B overlap obstruction.  Nothing else can happen: the split is on
the disjoint-choice proposition itself. -/
theorem hasDisjointChoice_or_overlapObstruction
    (object : FiniteObject.{u}) (threshold dischargeScale : Nat)
    (piece : Finset object.Vertex) :
    HasDisjointChoice object threshold dischargeScale piece
        (centres object threshold piece) ∨
      Nonempty (OverlapObstruction object threshold dischargeScale piece) := by
  classical
  by_cases choice :
      HasDisjointChoice object threshold dischargeScale piece
        (centres object threshold piece)
  · exact Or.inl choice
  · exact Or.inr (exists_overlapObstruction_of_not_hasDisjointChoice
      (subset_refl _) choice)

/-- **`lem:typeB-maximal-completion`.**

A connected assigned Type B support carrying no Type B overlap obstruction
admits a *maximal* disjoint refined Type B ledger.  The completion is immediate
at the full centre family: entering every assigned centre as a demand is
maximality by definition, and the absence of an obstruction is exactly the
statement that this family has a disjoint choice.  The manuscript's step-by-step
completion is what makes the full family available; here the family is the
support's own finite centre set, so no step is needed. -/
theorem typeBMaximalCompletion
    (object : FiniteObject.{u}) (threshold dischargeScale : Nat)
    (piece : Finset object.Vertex)
    (free : ¬ Nonempty (OverlapObstruction object threshold dischargeScale piece)) :
    Nonempty (RefinedSupportAssignment object threshold dischargeScale piece) := by
  rcases hasDisjointChoice_or_overlapObstruction object threshold dischargeScale
      piece with choice | obstruction
  · exact ⟨{
      demands := centres object threshold piece
      demands_subset := subset_refl _
      disjointChoice := choice
      maximal := subset_refl _ }⟩
  · exact absurd obstruction free

end Hypostructure.Graph.TypeBRefinedSupport
