import Hypostructure.Graph.SurplusPort

/-!
# The excess selector `𝒫_exc` and its count

`lem:sparse-excess-port-extraction`.  `def:surplus-ports` selects, at every
vertex `h` strictly above the registered baseline `δ`, exactly `d_G(h) − δ` of
the ports incident with `h`; a vertex at or below the baseline contributes
none.  The selection is canonical: it takes the first `d_G(h) − δ` entries of
the object's own ordered neighbour list at `h`, so it is a function of the
object and the baseline alone.

The count is the manuscript's

  `|𝒫_exc| = Σ_{h ∈ V_{>δ}} (d_G(h) − δ) = Σ_v (d_G(v) − δ) = σ(G)`,

whose middle step is that a vertex at the baseline contributes a zero term.
The second step is `ambientSurplus_univ_eq_degreeSurplus`, which needs the
standing baseline and nothing else.

Nothing here is specialized to one manuscript: the baseline is a parameter and
no numeral occurs.
-/

namespace Hypostructure.Graph

universe u

namespace FiniteObject

variable (object : FiniteObject.{u}) (threshold : Nat)

/-- **The ports selected at one centre.**  The first `d_G(h) − δ` neighbours of
`h` in the object's own ordered neighbour list.  At a centre sitting at or below
the baseline the count is zero and the selection is empty. -/
noncomputable def selectedPortEndpoints (centre : object.Vertex) :
    List object.Vertex :=
  (object.orderedNeighbors centre).take (object.degree centre - threshold)

variable {object threshold}

theorem selectedPortEndpoints_sublist (centre : object.Vertex) :
    List.Sublist (object.selectedPortEndpoints threshold centre)
      (object.orderedNeighbors centre) :=
  List.take_sublist _ _

theorem mem_selectedPortEndpoints_adj {centre endpoint : object.Vertex}
    (member : endpoint ∈ object.selectedPortEndpoints threshold centre) :
    object.graph.Adj centre endpoint :=
  (object.mem_orderedNeighbors_iff centre endpoint).1
    ((selectedPortEndpoints_sublist centre).subset member)

theorem selectedPortEndpoints_nodup (centre : object.Vertex) :
    (object.selectedPortEndpoints threshold centre).Nodup :=
  (object.orderedNeighbors_nodup centre).sublist
    (selectedPortEndpoints_sublist centre)

/-- A centre contributes exactly `d_G(h) − δ` selected endpoints: the ordered
neighbour list has `d_G(h)` entries, so the truncation is not shortened. -/
theorem selectedPortEndpoints_length (centre : object.Vertex) :
    (object.selectedPortEndpoints threshold centre).length =
      object.degree centre - threshold := by
  rw [selectedPortEndpoints, List.length_take, object.orderedNeighbors_length]
  omega

variable (object threshold)

/-- **`𝒫_exc` of `def:surplus-ports`**, as ordered pairs `(c(p), x(p))`.

The family is indexed by its centre, so distinct centres contribute disjoint
blocks; that is what makes the count a sum of the per-centre contributions. -/
noncomputable def excessPorts : Finset (object.Vertex × object.Vertex) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact Finset.univ.biUnion fun centre =>
    (object.selectedPortEndpoints threshold centre).toFinset.image
      fun endpoint => (centre, endpoint)

variable {object threshold}

theorem mem_excessPorts_iff (pair : object.Vertex × object.Vertex) :
    pair ∈ object.excessPorts threshold ↔
      pair.2 ∈ object.selectedPortEndpoints threshold pair.1 := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨centre, endpoint⟩ := pair
  constructor
  · intro member
    simp only [excessPorts, Finset.mem_biUnion, Finset.mem_image,
      List.mem_toFinset] at member
    obtain ⟨other, _, candidate, selected, equality⟩ := member
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ equality
    exact selected
  · intro selected
    simp only [excessPorts, Finset.mem_biUnion, Finset.mem_image,
      List.mem_toFinset]
    exact ⟨centre, Finset.mem_univ _, endpoint, selected, rfl⟩

/-- A selected port is a `def:surplus-ports` port: its centre is strictly above
the baseline and its endpoint is a neighbour of the centre. -/
theorem centre_high_of_mem_excessPorts {pair : object.Vertex × object.Vertex}
    (member : pair ∈ object.excessPorts threshold) :
    threshold < object.degree pair.1 := by
  have selected := (mem_excessPorts_iff pair).1 member
  by_contra low
  have empty : (object.selectedPortEndpoints threshold pair.1).length = 0 := by
    rw [selectedPortEndpoints_length]
    omega
  rw [List.length_eq_zero_iff] at empty
  rw [empty] at selected
  exact absurd selected (by simp)

theorem adj_of_mem_excessPorts {pair : object.Vertex × object.Vertex}
    (member : pair ∈ object.excessPorts threshold) :
    object.graph.Adj pair.1 pair.2 :=
  mem_selectedPortEndpoints_adj ((mem_excessPorts_iff pair).1 member)

/-- **A selected port, as `def:surplus-ports` declares it.**  Reading a member of
the selector back as a `SurplusPort` is what gives a consumer the shoulder set
and the endpoint's baseline degree without re-deriving either. -/
noncomputable def surplusPortOfMem {pair : object.Vertex × object.Vertex}
    (member : pair ∈ object.excessPorts threshold) :
    SurplusPort object threshold where
  centre := pair.1
  endpoint := pair.2
  centre_high := centre_high_of_mem_excessPorts member
  adjacent := adj_of_mem_excessPorts member

/-- **`lem:sparse-excess-port-extraction`, the count.**

`|𝒫_exc| = σ(G)`.  Each centre contributes `d_G(h) − δ` selected ports and
distinct centres contribute disjoint blocks, so the total is `Σ_v (d_G(v) − δ)`
— the object's own ambient surplus at the baseline, which on the standing
baseline is the `degreeSurplus` observable that node `[19]` compared. -/
theorem card_excessPorts
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    (object.excessPorts threshold).card = object.degreeSurplus threshold := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have disjoint : ∀ left ∈ (Finset.univ : Finset object.Vertex),
      ∀ right ∈ (Finset.univ : Finset object.Vertex), left ≠ right →
      Disjoint
        ((object.selectedPortEndpoints threshold left).toFinset.image
          fun endpoint => (left, endpoint))
        ((object.selectedPortEndpoints threshold right).toFinset.image
          fun endpoint => (right, endpoint)) := by
    intro left _ right _ different
    refine Finset.disjoint_left.2 fun pair leftMember rightMember => ?_
    simp only [Finset.mem_image] at leftMember rightMember
    obtain ⟨_, _, leftEq⟩ := leftMember
    obtain ⟨_, _, rightEq⟩ := rightMember
    apply different
    have first : pair.1 = left := by rw [← leftEq]
    have second : pair.1 = right := by rw [← rightEq]
    rw [← first, second]
  have blocks : (object.excessPorts threshold).card =
      ∑ centre : object.Vertex, (object.degree centre - threshold) := by
    rw [excessPorts, Finset.card_biUnion disjoint]
    refine Finset.sum_congr rfl fun centre _ => ?_
    rw [Finset.card_image_of_injective _
        (fun _ _ equality => congrArg Prod.snd equality),
      List.toFinset_card_of_nodup (selectedPortEndpoints_nodup centre),
      selectedPortEndpoints_length]
  rw [blocks, ← object.ambientSurplus_univ_eq_degreeSurplus threshold baseline]
  rfl

end FiniteObject

end Hypostructure.Graph
