## CycleCounting.Object declarations
```lean
/-! ## The properties -/

/-- `G − h` is connected, seen from every neighbour `x` of `h`: the component
of `x` in `G − h` is everything but `h`. -/
noncomputable def DeletionConnected (h : object.Vertex) : Prop :=
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  ∀ x, object.graph.Adj h x → insert h (comp object.graph h x) = Finset.univ

/-- **Vertex-deletion shape.** For every vertex `h`: `G − h` is connected, or
`d_h` is even, `d_h = 2·#blocks(h)`, and the component of every neighbour `x`
of `h` in `G − h` holds exactly two neighbours of `h`. -/
noncomputable def VertexDeletionShape : Prop :=
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  ∀ h : object.Vertex, DeletionConnected object h ∨
    (Even (object.degree h) ∧ object.degree h = 2 * #(blocks object.graph h) ∧
      ∀ x, object.graph.Adj h x →
        #(object.graph.neighborFinset h ∩ comp object.graph h x) = 2)

/-- **Cycles through a vertex.** For every vertex `h`: if `G − h` is connected,
`G` has at least `C(d_h, 2)` cycles through `h`; otherwise exactly `d_h / 2`
pairs of edges at `h` are closed in `G − h` (`2·#pairs = d_h`) and `G` has at
least `d_h / 2` cycles through `h`. -/
noncomputable def CyclesThroughVertex : Prop :=
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  ∀ h : object.Vertex,
    (DeletionConnected object h ∧
      (object.degree h).choose 2 ≤ #(cyclesThrough object.graph (fun _ => True) h)) ∨
    (¬ DeletionConnected object h ∧
      2 * #(pairsThrough object.graph (fun _ => True) h) = object.degree h ∧
      object.degree h / 2 ≤ #(cyclesThrough object.graph (fun _ => True) h))

/-- The vertices off the baseline degree `δ`. -/
noncomputable def offBaseline (δ : ℕ) : Finset object.Vertex :=
  letI : FinEnum object.Vertex := object.vertices
  Finset.univ.filter fun v => object.degree v ≠ δ

/-- **Pair sums over the high vertices** `H = {d ≠ δ}` against the surplus
`σ = 2m − δn`: `σ = Σ_H (d_h − 3)`, `5σ ≤ Σ_H C(d_h, 2)`, the Cauchy–Schwarz
form `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, the cap
`2 Σ_H C(d_h, 2) ≤ 16σ²`, and a heavy centre `σ ≤ |H|(d_h − 3)` (unless
`σ = 0`). -/
noncomputable def HighPairSum (δ : ℕ) : Prop :=
  object.degreeSurplus δ = ∑ h ∈ offBaseline object δ, (object.degree h - 3) ∧
  5 * object.degreeSurplus δ ≤ ∑ h ∈ offBaseline object δ, (object.degree h).choose 2 ∧
  object.degreeSurplus δ ^ 2 + 5 * object.degreeSurplus δ * #(offBaseline object δ) +
      6 * #(offBaseline object δ) ^ 2 ≤
    2 * #(offBaseline object δ) * ∑ h ∈ offBaseline object δ, (object.degree h).choose 2 ∧
  2 * ∑ h ∈ offBaseline object δ, (object.degree h).choose 2 ≤
    16 * object.degreeSurplus δ ^ 2 ∧
  (object.degreeSurplus δ = 0 ∨ ∃ h ∈ offBaseline object δ,
    object.degreeSurplus δ ≤ #(offBaseline object δ) * (object.degree h - 3))

/-- The per-vertex lower bound on the cycles through `h`: `C(d_h, 2)` when
`G − h` is connected, `d_h / 2` otherwise. -/
noncomputable def cycleLowerAt (h : object.Vertex) : ℕ :=
  if DeletionConnected object h then (object.degree h).choose 2 else object.degree h / 2

/-- **Double count of the cycles at the high vertices** `H = {d ≠ δ}`:
`2 Σ_{h∈H} #cycles(h) ≤ n · #cycles(G)`, `2 Σ_{h∈H} L_h ≤ n · #cycles(G)` with
`L_h` the per-vertex lower bound, and `#cycles(G) ≤ 2^m`. -/
noncomputable def CycleDoubleCount (δ : ℕ) : Prop :=
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  2 * ∑ h ∈ offBaseline object δ, #(cyclesThrough object.graph (fun _ => True) h) ≤
      object.vertexCount * #(allCycles (G := object.graph)) ∧
    2 * ∑ h ∈ offBaseline object δ, cycleLowerAt object h ≤
      object.vertexCount * #(allCycles (G := object.graph)) ∧
    #(allCycles (G := object.graph)) ≤ 2 ^ object.edgeCount

/-- **Star constraint.** Two paths `x → y`, `x → z` of `G − h` to distinct
neighbours `y, z` of `h`, meeting only at `x`, have `|P| + |Q| + 2 ≠ 2^k`
(`k ≥ 2`). -/
def StarConstraint : Prop :=
  ∀ ⦃h x y z : object.Vertex⦄, object.graph.Adj h y → object.graph.Adj h z → y ≠ z →
    ∀ (P : object.graph.Walk x y) (Q : object.graph.Walk x z), P.IsPath → Q.IsPath →
      h ∉ P.support → h ∉ Q.support → (∀ v ∈ P.support, v ∈ Q.support → v = x) →
      ∀ k, 2 ≤ k → P.length + Q.length + 2 ≠ 2 ^ k

/-- **Meeting constraint.** Two paths `x → y`, `x → z` of `G − h` to distinct
neighbours of `h` meet at a vertex `t` reached along them by `P₁`, `Q₁`, and
`|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`. -/
def MeetingConstraint : Prop :=
  ∀ ⦃h x y z : object.Vertex⦄, object.graph.Adj h y → object.graph.Adj h z → y ≠ z →
    ∀ (P : object.graph.Walk x y) (Q : object.graph.Walk x z), P.IsPath → Q.IsPath →
      h ∉ P.support → h ∉ Q.support →
      ∃ t, ∃ P₁ Q₁ : object.graph.Walk x t, P₁.length ≤ P.length ∧ Q₁.length ≤ Q.length ∧
        ∀ k, 2 ≤ k → P.length + Q.length + 2 ≠ 2 ^ k + P₁.length + Q₁.length

/-- **Neighbourhood pairs.** For every vertex `h`: `G[N(h)]` is a matching,
`N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every
neighbour `x` has at least `d_h − 2` nonadjacent partners in `N(h)`. -/
noncomputable def NeighbourhoodPairs : Prop :=
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  ∀ h : object.Vertex,
    (∀ x ∈ object.graph.neighborFinset h,
      #((object.graph.neighborFinset h).filter (object.graph.Adj x)) ≤ 1) ∧
    (object.degree h).choose 2 - object.degree h / 2 ≤
      #(nonAdjPairs object.graph (object.graph.neighborFinset h)) ∧
    ∀ x ∈ object.graph.neighborFinset h, object.degree h - 2 ≤
      #(((object.graph.neighborFinset h).erase x).filter (fun y => ¬ object.graph.Adj x y))

/-- **Block paths at a cut vertex.** For every vertex `h` with `G − h`
disconnected and every neighbour `a` of `h`, the block of `a` is `{a, b}` with
`b ≠ a` a neighbour of `h`, and:
* every `a → b` path of `G − h` has `|r| + 2 ≠ 2^k` (`k ≥ 2`);
* every return `q : a → h` of `ha` is `a ⋯ b h` with an `a → b` path of `G − h`
  of length `|q| − 1`;
* every `a → b` path avoiding `ha`, `hb` avoids `h`, and has `|p| ≡ 3 (mod 4)`
  when `|p| + 1 = 2^j` (`j ≥ 2`);
* every path from `a` to a neighbour `a₂` outside the component of `a`, avoiding
  `ha`, `ha₂`, splits at `h` as `a ⋯ b₁ h b₂ ⋯ a₂` with `|r₁| + |r₂| + 2 = |p|`,
  and when `|p| + 1 = 2^j` (`j ≥ 2`), `|r₁| + |r₂| ≡ 1 (mod 4)` with opposite
  parities. -/
noncomputable def BlockPaths : Prop :=
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  ∀ h : object.Vertex, ¬ DeletionConnected object h →
    ∀ a, object.graph.Adj h a → ∃ b, b ≠ a ∧ object.graph.Adj h b ∧
      object.graph.neighborFinset h ∩ comp object.graph h a = {a, b} ∧
      (∀ r : object.graph.Walk a b, r.IsPath → h ∉ r.support →
        ∀ k, 2 ≤ k → r.length + 2 ≠ 2 ^ k) ∧
      (∀ q : object.graph.Walk a h, q.IsPath → s(h, a) ∉ q.edges →
        ∃ r : object.graph.Walk a b, r.IsPath ∧ h ∉ r.support ∧ r.length + 1 = q.length) ∧
      (∀ p : object.graph.Walk a b, p.IsPath → s(h, a) ∉ p.edges → s(h, b) ∉ p.edges →
        h ∉ p.support ∧ ∀ j, 2 ≤ j → p.length + 1 = 2 ^ j → p.length % 4 = 3) ∧
      (∀ a₂, object.graph.Adj h a₂ → a₂ ∉ comp object.graph h a →
        ∀ p : object.graph.Walk a a₂, p.IsPath → s(h, a) ∉ p.edges → s(h, a₂) ∉ p.edges →
          ∃ b₁ b₂, b₁ ≠ a ∧ b₂ ≠ a₂ ∧ object.graph.Adj h b₁ ∧ object.graph.Adj h b₂ ∧
            b₁ ∈ comp object.graph h a ∧ b₂ ∈ comp object.graph h a₂ ∧
            ∃ (r₁ : object.graph.Walk a b₁) (r₂ : object.graph.Walk a₂ b₂),
              r₁.IsPath ∧ r₂.IsPath ∧ h ∉ r₁.support ∧ h ∉ r₂.support ∧
              r₁.length + r₂.length + 2 = p.length ∧
              ∀ j, 2 ≤ j → p.length + 1 = 2 ^ j →
                (r₁.length + r₂.length) % 4 = 1 ∧ r₁.length % 2 ≠ r₂.length % 2)

/-! ## Converters from the generic hypotheses -/

section Converters

```

## LocalRigidity declarations
```lean
def ThreeRouteFan : Prop :=
  ∀ ⦃h a b c p₁ p₂ q₁ q₂ : object.Vertex⦄,
    object.graph.Adj h a → object.graph.Adj h b → object.graph.Adj h c → b ≠ c →
    ThreePath object.graph a p₁ p₂ b → ThreePath object.graph a q₁ q₂ c →
    h ≠ p₁ → h ≠ p₂ → h ≠ q₁ → h ≠ q₂ →
    p₁ = q₁ ∧ p₂ ≠ q₂ ∧ p₂ ≠ c ∧ q₂ ≠ b

/-- **The chain `3, 3, 3`.**  At every vertex `h`, paths of length `3` of
`G − h` joining neighbours `a → b → c → d` of `h` (`a ≠ c`, `b ≠ d`) have their
middle path `b p₂ q₁ c` through the inner vertices of the outer two. -/
def ThreeRouteChain : Prop :=
  ∀ ⦃h a b c d p₁ p₂ r₁ r₂ q₁ q₂ : object.Vertex⦄,
    object.graph.Adj h a → object.graph.Adj h b → object.graph.Adj h c →
    object.graph.Adj h d → a ≠ c → b ≠ d →
    ThreePath object.graph a p₁ p₂ b → ThreePath object.graph b r₁ r₂ c →
    ThreePath object.graph c q₁ q₂ d →
    h ≠ p₁ → h ≠ p₂ → h ≠ r₁ → h ≠ r₂ → h ≠ q₁ → h ≠ q₂ →
    r₁ = p₂ ∧ r₂ = q₁

/-- **The cross-edge gap.**  Two vertex-disjoint placed paths `p`, `q` of `G`
joined by edges `p i – q j` and `p i' – q j'` close no accepted cycle: the
closing length `|i − i'| + 2 + |j − j'|` is not a power of two `≥ 4`. -/
def CrossGap : Prop :=
  ∀ ⦃m n : ℕ⦄ ⦃p : Fin m → object.Vertex⦄ ⦃q : Fin n → object.Vertex⦄,
    IsPlacedPath object.graph p → IsPlacedPath object.graph q → (∀ a b, p a ≠ q b) →
    ∀ ⦃i i' : Fin m⦄ ⦃j j' : Fin n⦄,
      object.graph.Adj (p i) (q j) → object.graph.Adj (p i') (q j') →
      ¬ WindowCurvature.ForbiddenGap (Nat.dist i.1 i'.1) (Nat.dist j.1 j'.1)

/-- A placement of a window support: its `order` positions, injective, inside
the support, with adjacency exactly the path adjacency (the window is an
induced path). -/
def IsWindowPlacement {order : ℕ} (support : Finset object.Vertex)
    (q : Fin order → object.Vertex) : Prop :=
  Function.Injective q ∧ (∀ i, q i ∈ support) ∧
    ∀ i j, object.graph.Adj (q i) (q j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1

/-- The attachment label of a vertex on a placed window: the positions it is
adjacent to. -/
noncomputable def attachLabel {order : ℕ} (q : Fin order → object.Vertex)
    (x : object.Vertex) : WindowCurvature.Label order := by
  classical
  exact Finset.univ.filter fun j => object.graph.Adj x (q j)

/-- **Window positions and stubs at a packing.**  Every window of the packing
has a placement; at every placement, an interior position `i` carries
`d(q i) − 2` external neighbours (exactly one when `d(q i) = 3`), and an end
position `d(q i) − 1` (for `order ≥ 2`). -/
def WindowPositionStubs (order : ℕ) (packing : Finset (Finset object.Vertex)) : Prop :=
  ∀ P ∈ packing, (∃ q : Fin order → object.Vertex, IsWindowPlacement object P q) ∧
    ∀ q : Fin order → object.Vertex, IsWindowPlacement object P q →
      (∀ i : Fin order, 0 < i.1 → i.1 + 1 < order →
        (object.externalNeighbours P (q i)).card + 2 = object.degree (q i)) ∧
      (∀ i : Fin order, 0 < i.1 → i.1 + 1 < order → object.degree (q i) = 3 →
        (object.externalNeighbours P (q i)).card = 1) ∧
      (2 ≤ order → ∀ i : Fin order, (i.1 = 0 ∨ i.1 + 1 = order) →
        (object.externalNeighbours P (q i)).card + 1 = object.degree (q i))

/-- **Attachment rules at a packing.**  At every placed window `q` of the
packing:
* every outside vertex with a nonempty attachment label carries a legal label
  (no attachment gap `d` with `d + 2` accepted);
* two adjacent outside vertices carry `C₁`-safe labels;
* two distinct windows `p`, `q` joined at `(i, j)` and `(i', j')` have
  `|i − i'| + 2 + |j − j'|` not accepted, and in particular form no ladder
  (`|i − i'| = |j − j'| = 1`). -/
def WindowAttachmentRules (order : ℕ) (packing : Finset (Finset object.Vertex)) : Prop :=
  (∀ P ∈ packing, ∀ q : Fin order → object.Vertex, IsWindowPlacement object P q →
    ∀ x ∉ P, (attachLabel object q x).Nonempty →
      attachLabel object q x ∈ WindowCurvature.Labels order) ∧
  (∀ P ∈ packing, ∀ q : Fin order → object.Vertex, IsWindowPlacement object P q →
    ∀ x ∉ P, ∀ y ∉ P, object.graph.Adj x y →
      WindowCurvature.Safe 1 (attachLabel object q x) (attachLabel object q y)) ∧
  (∀ P ∈ packing, ∀ Q ∈ packing, P ≠ Q →
    ∀ p q : Fin order → object.Vertex, IsWindowPlacement object P p →
      IsWindowPlacement object Q q →
      ∀ i i' j j' : Fin order, object.graph.Adj (p i) (q j) → object.graph.Adj (p i') (q j') →
        ¬ WindowCurvature.ForbiddenGap (Nat.dist i.1 i'.1) (Nat.dist j.1 j'.1)) ∧
  (∀ P ∈ packing, ∀ Q ∈ packing, P ≠ Q →
    ∀ p q : Fin order → object.Vertex, IsWindowPlacement object P p →
      IsWindowPlacement object Q q →
      ∀ i i' j j' : Fin order, Nat.dist i.1 i'.1 = 1 → Nat.dist j.1 j'.1 = 1 →
        ¬ (object.graph.Adj (p i) (q j) ∧ object.graph.Adj (p i') (q j')))

```
