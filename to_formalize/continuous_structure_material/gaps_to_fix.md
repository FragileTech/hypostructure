
# Continuum-framework gap audit

Sections A--G preserve the defects found at the start of the audit.  They are
not statements about the current manuscript.  The numbered resolution audit
and verification matrix below give the controlling disposition for every
item.  A stronger theorem is never inferred merely because the corresponding
false claim was removed.

## A. Invalid terminal semantics

  1. Contact-derived records are incorrectly promoted to independently realized singularities.

  The manuscript correctly defines an explicit singular mechanism as requiring independent origin polarity (\mathsf{Ind}) at to_formalize/continuous_hamiltonian_structural_complexity.tex:17007.
  But the terminalization theorem later—or earlier in logical dependency—uses a contact-derived orbit to declare its diagonal limit an explicit singular mechanism at to_formalize/
  continuous_hamiltonian_structural_complexity.tex:15669.

  These statements are incompatible:

  [
  \mathsf{Hyp}\neq\mathsf{Ind}.
  ]

  A contradiction hypothesis cannot be recycled into an independent existence proof.

  2. A nonordinary total-graph value is treated as a realized singularity.

  At to_formalize/continuous_hamiltonian_structural_complexity.tex:15646, a cofinal nonordinary coordinate is called a “singular corona record.” But a nonordinary value only means that an
  operation failed to have its ordinary graph value. It need not be a PDE solution, continuation germ, defect measure arising from approximations, or physical orbit.

  Required repair: a nonordinary value must remain a successor until it is either charged, target-null, or reconstructed from the approximation tower.

  3. A carrier-polar separator is still treated as a terminal mechanism.

  The general evaluator declares a separator part of a “realized singular mechanism” at to_formalize/continuous_hamiltonian_structural_complexity.tex:15781.

  But the earlier, logically correct carrier-polar theorem says a separator is a successor and becomes a singular atom only after independent ordinary realization at to_formalize/
  continuous_hamiltonian_structural_complexity.tex:5230.

  A separating functional is not a trajectory.

  4. The “binary continuum terminal theorem” is therefore unproved.

  The claimed dichotomy

  [
  \text{avoidance}\quad\text{or}\quad\text{realized singular mechanism}
  ]

  at to_formalize/continuous_hamiltonian_structural_complexity.tex:15680 depends on the invalid promotion in holes 1–3.

  The valid output currently is only:

  [
  \text{avoidance}
  \quad\text{or}\quad
  \text{target-aligned prospective structural model}.
  ]

  5. “Independent realization” is named but not constructed.

  Several sections say that a prospective atom becomes singular “when independently generated,” for example to_formalize/continuous_hamiltonian_structural_complexity.tex:16952. The framework does
  not provide a general constructor that takes the structural atom and produces such an independent orbit.

  That phrase is currently an external existence requirement in disguise.

  ## B. Reconstruction and compactification holes

  6. Positive-functional reconstruction does not reconstruct a PDE orbit.

  The moment hierarchy reconstructs a measure on a compact total-graph inverse limit at to_formalize/continuous_hamiltonian_structural_complexity.tex:16910. This supplies a relaxed model, not
  necessarily:

  - a function or distribution;
  - a coherent time-dependent path;
  - a solution of the nonlinear weak equation;
  - a path with the required initial datum;
  - an orbit reaching the continuation target.

  A measure on graph coordinates is not automatically a PDE solution.

  7. Ordinary values of every finite coordinate do not automatically give one coherent ordinary orbit.

  Finite-coordinate consistency can hold along different approximating subsequences. The manuscript needs a same-origin projective realization theorem proving that all coordinates arise
  simultaneously from one approximation path.

  Diagonal compactness alone does not prove this.

  8. The compactification contains artificial boundary points.

  The product/order-unit compactification deliberately makes every coordinate bounded. Its spectrum can therefore contain positive functionals that satisfy all finite readouts but do not
  represent any analytic state.

  Such points are safe for proving target exclusion, because excluding a larger relaxed space is sound. They are not safe for proving singular existence.

  9. Graph completeness preserves information but does not prove physical attainability.

  Recording inputs, outputs, oscillations, concentrations, tails, and graph defects prevents information loss. It does not prove that every compatible collection of those coordinates is
  dynamically attainable.

  The paper repeatedly moves from “nothing was forgotten” to “therefore this is a physical mechanism.” That implication is missing.

  10. The approximation tower is not yet linked surjectively to terminal atoms.

  The public approximation grammar is defined, but there is no theorem establishing:

  [
  \text{independently realized terminal atom}
  \iff
  \text{coherent zero-defect approximation tower reaching }\Sigma.
  ]

  Without this, singular terminals remain relaxed models.

  ## C. Ordered-algebra evaluation holes

  11. Carrier-cone membership is semantic.

  The framework says that an owner is charged when

  [
  Q\in\mathscr D_{\mathfrak b}^{\Phys}.
  ]

  But general membership in the closed infinite-dimensional carrier cone is not reduced to a finite proof-producing test. Defining the cone as closed makes separation available abstractly; it
  does not calculate which side contains (Q).

  12. Closedness of the carrier cone is not derived in the required topology.

  Hahn–Banach separation at to_formalize/continuous_hamiltonian_structural_complexity.tex:5237 requires a specified locally convex topology and a closed cone. The manuscript largely obtains
  closedness by completion, but it does not prove that this completion remains faithful to the PDE and physical-ledger relations.

  13. A continuous separator need not be found by the stated rational enumeration.

  A product-topology continuous functional depends on finitely many coordinates, but its coefficients can be irrational and its separation margin can be zero on the boundary. The manuscript needs
  a rationalization theorem with a positive separation margin or an exact algebraic representation.

  14. Finite semialgebraic elimination does not cover the full graph language.

  The branch-and-bound theorem invokes exact semialgebraic elimination at to_formalize/continuous_hamiltonian_structural_complexity.tex:16888. The actual language contains:

  - exponentials and resolvents;
  - unbounded operators;
  - distributional products;
  - graph boundaries;
  - measures;
  - infinite-dimensional domains;
  - limiting relations.

  These are not automatically finite rational semialgebraic constraints.

  15. The ordered consequence grammar is not relatively complete for PDE identities.

  The grammar enumerates localizations, commutators, squares, adjoints, scale identities, and polarizations. There is no theorem showing that every true target-local carrier domination or nullity
  statement has a derivation in this grammar.

  Thus “the proof search did not find an identity” cannot yet imply the existence of a physical countermodel.

  16. Strict positivity and equality are conflated.

  Archimedean Positivstellensatz-style completeness handles strict separation well. PDE regularity frequently sits on a zero-margin equality stratum. The manuscript adds real-radical and
  resaturation language, but it does not prove a complete real-radical calculus for its infinite graph algebra.

  17. Semantic emptiness still enters through compactness.

  Statements of the form

  [
  X_\infty=\varnothing
  \Longrightarrow
  X_N=\varnothing\text{ for some }N
  ]

  are topologically correct for decreasing compact sets. But the framework still needs a finite algebraic derivation verifying (X_N=\varnothing). A finite empty cover is not itself a proof unless
  every deletion edge carries a checked identity.

  18. The primal–polar fixed point is not evaluated.

  After every enumerated successor has been processed, the framework permits a primal–polar fixed atom. Fixedness only means:

  [
  \text{the current grammar generated no new coordinate}.
  ]

  It does not mean:

  [
  \text{charged},\quad\text{target-null},\quad\text{or physically realized}.
  ]

  This is the current continuous analogue of stopping after discovering a target-aligned algorithm without evaluating what it does.

  19. Infinite successor closure prevents loss but not indecision.

  The cumulative joint construction correctly prevents infinitely many small contributions from disappearing. However, after preserving their sum, the manuscript still needs to evaluate the
  resulting joint owner. “The record is fixed under all current constructors” is not a terminal truth theorem.

  20. The consequence algebra has no proved universal truth-evaluation theorem.

  What is missing is precisely:

  [
  \boxed{
  \begin{aligned}
  \text{every target-active zero-price joint model}
  \Longrightarrow
  &\ \text{finite carrier/nullity derivation}\
  &\quad\text{or coherent independently realized orbit}.
  \end{aligned}}
  ]

  Part II currently asserts variants of this theorem but does not prove either exhaustive reconstruction or exhaustive finite elimination.

  ## D. Physical-financing holes

  21. Uniform finiteness in the covariant financing branch is conditional.

  The evaluator says the generated weighted root, physical, and exterior coordinates are “uniformly finite” at to_formalize/continuous_hamiltonian_structural_complexity.tex:15825. The physical
  production is bounded by the physical ledger, but the weighted root and adjoint-weighted exterior terms need not be.

  Their boundedness must be derived, not included inside the successful branch description.

  22. Target-visible unbounded weighted-root financing is still unevaluated.

  The latest correction properly removes target-null horizon growth. But a target-visible unbounded weighted-root coordinate is merely retained as a terminal mechanism. The framework still must
  determine whether it:

  - telescopes after compatible horizon gluing;
  - belongs to another source-owned carrier;
  - creates a new scale successor;
  - is physically singular;
  - or is inconsistent with the public equation.

  23. Exact financing of the shell current is not guaranteed.

  The relation

  [
  \mathsf Q_N
  \le
  \delta\mathscr K_N+\mathsf P_N+\mathsf B_N+\mathsf N_N
  ]

  is an evaluator branch. There is no theorem that every target-active current either admits such an identity or that its separator reconstructs a physical counter-orbit.

  This is the main carrier-polar gap.

  24. Sourcewise signed measures may not exist globally.

  The identity

  [
  \Gamma_\Sigma=\sum_cQ^c
  ]

  is proved on finite occurrence sets. Passing to global signed measures requires control preventing both positive and negative variations of some (Q^c) from being infinite on the same set.

  Without that, the sourcewise Lebesgue decompositions

  [
  Q^c=g_c\mu_{\Phys}+S_c
  ]

  at to_formalize/continuous_hamiltonian_structural_complexity.tex:15490 are not automatically defined.

  25. The physical-singular part is classified but not evaluated.

  A target current singular with respect to (\mu_{\Phys}) is correctly assigned a five-source owner. But singularity with respect to the budget measure does not itself prove either PDE
  singularity or inconsistency. It must enter the same carrier-polar and realization evaluator.

  26. Bounded amplification is an exact criterion, not a computed result.

  The measure-theoretic statement

  [
  \Gamma_\Sigma^\perp=0,\qquad f_\Sigma\in L^\infty
  \Longrightarrow\text{finitely many crossings}
  ]

  is correct. The framework has not computed those two properties from the PDE syntax in every source cell. Calling them “computed by the algebra” is currently too strong.

  ## E. Target and continuation holes

  27. The singular target depends on the declared continuation class.

  A terminal germ is called singular when it fails continuation in the declared regularity class. This is legitimate only after proving that the class matches the intended regularity theorem and
  that no weaker acceptable continuation has been omitted.

  Otherwise target contact can be an artifact of the presentation.

  28. Terminal coverage uses compactified germs.

  The terminal-coverage proposition obtains a germ by compact metrizability at to_formalize/continuous_hamiltonian_structural_complexity.tex:12697. It still needs to prove that the germ
  corresponds to actual noncontinuation rather than only convergence in the relaxed evaluation compactification.

  29. Shell cofinality is presentation-relative.

  The shell cascade is correct once the shell family is genuinely cofinal for the analytic continuation target. The manuscript generates shells from target coordinates, but it needs a separation
  theorem showing that these coordinates detect every failure relevant to the chosen continuation class.

  30. The fundamental shell-current identity is only as faithful as its graph realization.

  Derived Stieltjes shell currents solve the differentiability problem. But if the weak equation, nonlinear product, trace, or chart is nonordinary, the corresponding current is again a graph
  object. The framework still must evaluate or realize that graph current; source classification alone is insufficient.

  ## F. Navier–Stokes unit-test holes

  31. The NS unit test explicitly remains conditional.

  It says regularity holds precisely when its third cell is empty at to_formalize/continuous_hamiltonian_structural_complexity.tex:20227. The example never eliminates that cell.

  32. The NS terminal decomposition is circular.

  The objects (f_{\Sigma_{\rm sing}}) and (\Gamma_{\Sigma_{\rm sing}}^\perp) are constructed on a contact-derived occurrence record. The claimed equivalence at to_formalize/
  continuous_hamiltonian_structural_complexity.tex:20256 does not compute reachability from the initial datum; it characterizes what a hypothetical contact record would have to look like.

  33. The NS “realized singular terminals” have hypothetical origin.

  The critical-tail theorem calls unbounded-amplification and physical-singular tails “realized singular terminals” at to_formalize/continuous_hamiltonian_structural_complexity.tex:20093. Those
  tails were extracted from the contact hypothesis, so their origin polarity is (\mathsf{Hyp}), not (\mathsf{Ind}).

  34. Uniform normalized (L^2), (L^3), and pressure bounds are not derived.

  The canonical microscope theorem asserts common bounds at to_formalize/continuous_hamiltonian_structural_complexity.tex:19954. Basic kinetic energy does not give a scale-uniform normalized
  (L^2) bound because

  [
  |r,u(x_0+r\cdot)|_{L^2(B_2)}^2

  r^{-1}|u|{L^2(B{2r})}^2.
  ]

  The “first-scale choice” does not by itself repair this.

  35. The claimed uniform critical price depends on that unproved bound.

  The positive constant (d_) at to_formalize/continuous_hamiltonian_structural_complexity.tex:19996 depends on a uniform (M_2). Without a derived scale-uniform (M_2), (d_) can degenerate along
  the cascade.

  36. Normalized dissipation is not the physical expenditure.

  Even if (D_j^{\rm act}\ge d_*) in normalized coordinates, its physical cost carries a scale factor. Therefore

  [
  \sum_j D_j^{\rm act}=\infty
  ]

  does not contradict finite physical kinetic-energy dissipation. The scale current must finance the difference through the exact covariant carrier. That financing has not been closed.

  37. The signed scale remainder is retained but not eliminated.

  The corrected decomposition

  [
  F_{\rm sc,\phi}
  =-aK_\phi-aY_\phi
  ]

  is now right. But the target-visible remainder involving (aY_\phi), pressure transport, cutoff gradients, and exterior flux can still inhabit the separator branch. The example does not prove it
  is a coboundary, physically charged, or target-null.

  38. Ordinary zero-production tangents are handled; nonordinary ones are not.

  The proof that an ordinary zero-production tangent has (\nabla V=0) and is Galilean-null is good. But the NS proof reaches its difficulty precisely when the tangent is nonordinary. The
  manuscript then uses the invalid terminalization theorem instead of evaluating that nonordinary branch.

  39. Pressure and harmonic tails remain successor labels.

  The NS sections enumerate local Calderón–Zygmund pressure, harmonic gauges, and exterior tails. They do not provide a completed recursive argument proving every target-aligned tail charged,
  null, or independently realizable.

  40. The scale-saturation equality state is not eliminated.

  The intended Perelman-style endpoint should be:

  [
  \Delta_{\rm car}=0
  \Longrightarrow
  \text{relative scale equilibrium}
  \Longrightarrow
  \text{target-null}.
  ]

  The manuscript has portions of this mechanism, but no single theorem derives the relative-equilibrium equation and eliminates every target-active ordinary and generalized equality state.

  41. The NS example does not finish the carrier-polar recursion.

  Its final separator is exactly the object the framework says must be recursively expanded. The example instead calls it an explicit singular mechanism.

  ## G. Spectral/Hamiltonian scope holes

  42. The Hamiltonian track begins after the operator has been constructed.

  The resolvent and Hamiltonian machinery analyzes a given closed form or generator. It does not generally construct the Hilbert space, operator domain, vacuum, or continuum limit.

  43. Spectral singularities are not automatically PDE reachability singularities.

  Resolvent poles, pseudospectral growth, loss of closed range, and PDE noncontinuation need explicit realization maps. Without them, the Hamiltonian formulation is an analytical backend, not a
  complete equivalent formulation of target reachability.

  44. Regulator-to-continuum spectral reconstruction is incomplete.

  For applications such as quantum Yang–Mills, the current framework does not generate the continuum theory, reflection-positive Hilbert space, vacuum, or strongly continuous Hamiltonian.
  Therefore it cannot yet evaluate the mass-gap target from textbook finite-regulator data.

  ## Bottom line

  The root defect is:

  [
  \boxed{
  \text{Part II exhausts provenance but does not yet exhaust truth evaluation.}
  }
  ]

  The manuscript correctly ensures that no target-aligned structure disappears into (J_{\rm res}). But it still allows three nonterminal objects to masquerade as conclusions:

  [
  \boxed{
  \text{positive functional},\qquad
  \text{polar separator},\qquad
  \text{nonordinary fixed graph record}.
  }
  ]

  All three must be internal successor states. The only permissible final outputs are:

  [
  \boxed{
  \text{finite target-local regularity derivation}
  \quad\text{or}\quad
  \text{independently reconstructed singular orbit}.}
  ]

  Until the framework proves that exhaustive truth-evaluation theorem and the NS specialization discharges its scale-financing branch, Part II is not complete and the NS unit test is not closed.

## Soundness-repair audit

The descriptions above are the failures as found; the dispositions below
record the current manuscript.  A defect
is resolved only by changing the logical type of the relevant theorem or by
adding the missing construction.  Merely renaming a branch does not count.

Three disposition types are used.  **Closure** means that a proved
construction supplies the missing implication stated in the numbered item.
**Typing repair** means that
an object previously promoted past what was proved is now kept as an internal
successor and every reachability theorem has been narrowed accordingly.
**Scope boundary** means that the manuscript explicitly does not claim the
missing universal capability.  A scope boundary repairs an invalid theorem;
it is not evidence that the stronger capability has been obtained.

Accordingly, this section is a soundness audit, not a declaration that every
capability requested in A--G has been constructed.  An item is a closed
framework capability only when its matrix row says **Closure** without a
qualification.  A row saying typing repair, exact gate, recursive transition,
or scope boundary certifies that the manuscript no longer reasons through the
gap; it does not certify termination of that branch.

1. Contact-derived records retain origin polarity `Hyp` through every join,
   limit, and corona transition.  The terminal compiler now requires `Ind`
   and the ordinary approximation--orbit realization criterion.
2. A nonordinary total-graph value is a typed successor.  It cannot be an
   existence terminal.
3. A carrier-polar separator is a dual-graph successor.  It re-enters adjoint,
   polarization, cone, and realization processing.
4. The former binary theorem is now a terminal-*soundness* theorem: every
   verdict actually reached is either checked avoidance or an independently
   realized ordinary singular orbit.  It does not assert termination.
5. Independent realization is no longer inferred from a prospective atom.
   `thm:approximation-orbit-realization-criterion` gives a sufficient test in
   terms of one coherent zero-defect, zero-variance, ordinary-domain tower,
   and an exact test for any realization claimed through that tower;
   `thm:dirac-realization-gate` reconstructs the orbit when the test holds.
   A direct ordinary value of the total solution graph realizes itself.  The
   manuscript does **not** claim that every
   relaxed atom has such a tower or that the hierarchy manufactures one.
6. Positive-functional reconstruction is explicitly typed as relaxation.
   The Dirac gate is required to obtain one PDE path.
7. The approximation--orbit criterion requires convergence of all coordinates
   along one compatible tower path.  Coordinatewise subsequences do not pass.
8. Artificial compactification points are harmless for exclusion and barred
   from existence by the no-compactification-promotion corollary.
9. Graph completeness now means information preservation only.  Attainability
   is a separate ordinary realization row.
10. `thm:approximation-orbit-realization-criterion` proves sufficiency of a
    coherent zero-defect, zero-variance, ordinary-domain tower and necessity
    for every realization asserted through the public approximation grammar.
    It explicitly does not infer that every ordinary solution is approximable
    by that grammar.  Direct ordinary solution-graph evaluations remain the
    other realization route.  Target contact additionally uses ordinary shell
    and continuation rows.
11. The carrier cone is split into the finite algebraic cone and its
    topological closure.  Only algebraic membership is a finite charging
    proof; closure-only membership is a typed cone-boundary successor.
12. The carrier-current topology is now the initial locally convex topology
    of bounded rational cylinder seminorms.  Faithfulness is enforced by the
    approximation--orbit realization gate.
13. Strict separators are proved to depend on finitely many cylinder
    coordinates, but their coefficients are not falsely declared rational.
    Rational enumeration is claimed complete only for rational-polyhedral
    finite projections.
14. Finite semialgebraic elimination is restricted to the polynomial moment
    relaxation.  Exponentials, resolvents, unbounded operations,
    distributional products, and limits remain total-graph coordinates.
15. The ordered grammar makes no relative-completeness claim for all true PDE
    identities.  Failure to derive an identity produces a relaxed positive
    functional, never a physical counterexample.
16. Strict positivity and zero-margin equality are separated.  Equality
    is now tested first by the dyadic ordered-coercivity terminal rule.  A
    generated finite-coefficient row (A^{2^k}\le CM^aP^b) and zero
    production force zero target activity directly for every positive
    functional.  Only an unbounded coefficient, a nonordinary relation, or an
    equality cell lacking such a generated domination row continues.
17. Compact semantic emptiness is usable only with the checked finite deletion
    identities at the finite empty level.
18. A primal--polar fixed point is a prospective source atom, not a verdict.
19. Infinite successor closure now uses the exact Part-I backward-frontier
    mechanism.  Every stopped shell readout factors through a finite joint
    ancestral cut; nested conditional expectations split its target
    projection into orthogonal contextual increments.  Across a cofinal shell
    family these frontiers are joined before projection, so a nonzero limit
    has a nonzero finite-prefix increment, while the separate unnormalized
    cocycle retains every crossing and its physical owner.  Actual contact is
    linked to the projection identity by the canonical two-record law on the
    source-current frontier (the unit crossing record versus the algebraic
    zero-current record), so no observer-law hypothesis is used.  The finite
    occurrence direct sum gives the exact identities
    `(N/4)=sum_{j<N,l} Delta_{j,l}` and
    `N=sum_{j<N,l} widehat Delta_{j,l}`; consequently the argument neither
    identifies distinct shell spaces nor normalizes away their multiplicity.
    Compact terminal
    windows, finite local critical norm, and perturbative critical-space
    bounds are not premises of this extraction.
20. The manuscript no longer asserts universal analytic truth evaluation.
    `prop:sound-scope-ordered-hierarchy` states the exact contract: finite
    identities are proof objects, compatible moment levels reconstruct only
    relaxed positive functionals, and physical existence requires the
    separate approximation--orbit criterion.  This repairs the false theorem
    claim; it does not pretend that a universal PDE decision procedure has
    been proved.
21. Covariant financing now splits verified finite endpoint/exterior rows from
    unbounded weighted-root or exterior coordinates.  Finiteness is derived
    inside the finite-financing cell, not assumed globally.
22. Target-visible unbounded financing is projected before interpretation and
    returned as a source-owned corona successor.
23. Exact shell financing is one cone value.  Its complement is recursively
    processed through cone boundary or polar separation and is not called a
    terminal.
24. Global sourcewise signed-measure decompositions were removed.  Source
    extraction is performed on finite occurrence sets before the directed
    join; only the positive total target measure receives a global Lebesgue
    decomposition.
25. Physical-singular target mass enters source-resolved amplification,
    zero-production, corona, carrier-polar, and realization transitions.
26. Bounded amplification is an exact recordwise criterion.  The manuscript
    no longer calls it a reachability computation from the initial datum.
27. `def:singular-target` defines the physical target as a same-origin finite
    noncontinuation **event** of an ordinary maximal preterminal path in the
    declared public continuation class.  The event therefore does not depend
    on existence of a terminal analytic state.  Its relaxed shell closure is
    distinguished notationally and logically.
28. `prop:terminal-coverage` proves that an actual ordinary maximal path with
    finite noncontinuation reaches that event target.  Compactness yields only
    relaxed terminal analytic coordinates; those coordinates, and arbitrary
    compactification points, require the approximation--orbit gate before
    they are interpreted as PDE states.  Thus neither genuine blow-up nor
    compactification artifacts are lost.
29. `prop:shell-cofinality-realization-fidelity` supplies cofinality for the
    relaxed closed event target, while the same-origin preterminal path and
    discrete noncontinuation flag provide physical fidelity.  An unrelated
    relaxed point cannot inherit that flag.
30. Nonordinary shell currents remain typed graph successors.  The shell
    identity supplies prospective accountability, not analytic realization.
31. The Navier--Stokes audit no longer claims a conditional or unconditional
    regularity conclusion from an unevaluated third cell.
32. The contact-derived measure decomposition is stated only as a necessary
    amplification consequence.  The circular reachability equivalence was
    deleted.
33. Navier--Stokes critical tails retain `Hyp` origin and are prospective
    source-owned successors.
34. Scale-uniform normalized `L2`, `L3`, and pressure bounds were removed from
    the canonical microscope construction; their failures are amplitude,
    pressure, or tail coordinates.  The quotient-activity split is also
    cofinally exhaustive: either a rational positive floor persists or the
    activity tends to zero while its unnormalized shell ledger survives as a
    vanishing-activity successor.
35. The uniform constant price was replaced by the explicit scale-dependent
    schedule involving the actual normalized `L2` coordinate.
36. Normalized dissipation is never equated with physical expenditure.  The
    covariant scale current and original physical denominator are retained.
37. The signed scale, pressure, cutoff, chart, and exterior remainder is glued
    before positive parts and passed owner-by-owner through carrier--polar
    recursion.
38. Ordinary zero-production tangents are Galilean-null; nonordinary tangents
    return to their least typed realization successor.
39. Pressure and harmonic tails are total graphs with recursive successors,
    not terminal labels.
40. Scale-saturation equality is processed by the target-cyclic equality and
    corona queues.  The finite-amplitude equality fiber is now closed directly
    at the positive-functional level: the generated fourth-power weighted
    Poincare--Sobolev row and zero production imply zero quotient activity,
    without Dirac realization.  The complementary unbounded or nonordinary
    amplitude value is the typed amplitude/scale successor.
41. The final Navier--Stokes separator now returns to the general
    carrier--polar queue and ordinary realization gate.
42. The Hamiltonian track is explicitly conditional on construction of its
    closed form/generator; it cannot manufacture the operator domain.
43. Spectral coordinates affect PDE reachability only through an explicit
    same-origin realization map intertwining evolution, target, and carrier.
44. Regulator moment models do not establish a quantum continuum.  A mass-gap
    conclusion additionally requires zero-defect projective consistency,
    reflection positivity, nontriviality, strong continuity, and the
    reconstructed Hamiltonian.

The resulting contract has no hidden third terminal.  There are only checked
finite target exclusion and independently reconstructed ordinary contact.
Positive functionals, separators, compactified germs, cone-boundary values,
and fixed prospective atoms are internal states.  This repair makes the
calculus sound; it deliberately does not relabel a nonterminating internal
evaluation as a proof of regularity or singularity.

### Verification matrix

The following matrix identifies the exact manuscript interface that now
controls every numbered defect.  Labels refer to
`continuous_hamiltonian_structural_complexity.tex`.

| Item | Disposition | Controlling definition/theorem |
|---:|---|---|
| 1 | Closure | `thm:no-recycled-contact-realization`, `thm:three-output-target-aligned-current-compiler` |
| 2 | Typing repair | `thm:approximation-realization-first-failure`, `cor:no-compactification-existence-promotion` |
| 3 | Typing repair | `def:target-local-carrier-polar-successor`, `cor:no-pre-polar-realization` |
| 4 | Typing repair | `cor:binary-terminal-semantics`, `cor:binary-continuum-terminal-theorem` |
| 5 | Scope boundary plus exact gate | `thm:dirac-realization-gate`, `thm:approximation-orbit-realization-criterion` |
| 6 | Typing repair plus exact Dirac gate | `prop:sound-scope-ordered-hierarchy` (S2), `thm:dirac-realization-gate` |
| 7 | Closure | `thm:approximation-orbit-realization-criterion` (D1)--(D2) |
| 8 | Typing repair | `cor:no-compactification-existence-promotion` |
| 9 | Typing repair | `cor:no-compactification-existence-promotion` |
| 10 | Exact gate, not universal surjectivity | `thm:approximation-orbit-realization-criterion` |
| 11 | Closure | `def:target-local-carrier-polar-successor`, `thm:recursive-carrier-polar-exhaustion` |
| 12 | Closure for topology; realization kept separate | `def:target-local-carrier-polar-successor`, `cor:no-compactification-existence-promotion` |
| 13 | Closure | `lem:rational-carrier-separation` |
| 14 | Typing repair | `prop:sound-scope-ordered-hierarchy` (S3) |
| 15 | Scope boundary | `prop:sound-scope-ordered-hierarchy`, final paragraph |
| 16 | Constructive closure for generated dyadic coercivity rows; complementary equality remains typed | `thm:dyadic-ordered-coercivity-terminal-rule`, `prop:sound-scope-ordered-hierarchy` (S4), `thm:saturation-equation-compiler` |
| 17 | Closure | `def:finite-pruning-transcript`, `thm:canonical-finite-pruning-transcript` |
| 18 | Typing repair plus coercivity/equality transition | `thm:dyadic-ordered-coercivity-terminal-rule`, `thm:three-output-target-aligned-current-compiler`, `thm:no-terminal-zero-price-model` |
| 19 | Exact finite-prefix backward-frontier and cumulative-accounting closure | `thm:exact-prospective-continuum-backward-factorization`, `thm:cofinal-prospective-frontier-closure`, `thm:continuum-composition-no-creation`, `cor:no-limit-created-target-alignment` |
| 20 | No-go closure for a universal profile verdict | `thm:quantifier-faithful-continuum-accountability`, `prop:sound-scope-ordered-hierarchy`, `cor:binary-continuum-terminal-theorem` |
| 21 | Closure | `thm:complete-covariant-corona-evaluator` (V1)/(V3) |
| 22 | Typing repair as a source-owned successor | `thm:complete-covariant-corona-evaluator` (V3) |
| 23 | Recursive transition; automatic financing not closed | `thm:target-aligned-carrier-duality`, `thm:complete-covariant-corona-evaluator` |
| 24 | Closure | `def:same-origin-occurrence-measure`, `thm:prospective-source-amplification-extraction` |
| 25 | Typing repair plus evaluated transition and finite-coefficient equality closure | `thm:exact-compositional-physical-accounting`, `thm:amplification-zero-production-tangent`, `thm:dyadic-ordered-coercivity-terminal-rule` |
| 26 | Exact criterion; universal computation not closed | `thm:physical-target-capacity-duality` |
| 27 | Closure | `def:singular-target` |
| 28 | Closure | `prop:terminal-coverage`, `cor:no-compactification-existence-promotion` |
| 29 | Closure | `prop:shell-cofinality-realization-fidelity` |
| 30 | Typing repair as graph transition | `thm:defect-totalization-five-channel`, `thm:projection-first-saturation` |
| 31 | Typing repair; no NS regularity claim | `thm:ns-backend-scope`, conclusion after (A10) |
| 32 | Typing repair | `thm:ns-empty-singular-target-core` |
| 33 | Closure | `thm:ns-critical-tail-nullity`, `thm:no-recycled-contact-realization` |
| 34 | Typing repair | `thm:ns-canonical-target-orbit` (C2)--(C3) |
| 35 | Closure | `lem:ns-computed-critical-price` |
| 36 | Closure of scale accounting | `prop:ns-no-free-shrinkage`, `thm:ns-signed-covariant-carrier` |
| 37 | Recursive transition; terminal elimination not closed | `prop:ns-complete-covariant-corona-execution` |
| 38 | Closure of ordinary/nonordinary split | `prop:ns-ordinary-amplification-tangent-nullity`, `thm:ns-critical-tail-nullity` |
| 39 | Total-graph recursion; terminal elimination not closed | `def:ns-collapsed-successor-cells`, `thm:ns-critical-tail-nullity` |
| 40 | Finite-amplitude positive-functional equality fiber closed; the survivor is localized to the joint amplitude--scale cell | `thm:dyadic-ordered-coercivity-terminal-rule`, `prop:ns-ordinary-amplification-tangent-nullity`, `cor:ns-surviving-amplitude-scale-cell`, `thm:complete-covariant-corona-evaluator` |
| 41 | Routing closure only; termination not closed | `thm:ns-carrier-polar-recursion`, `prop:ns-complete-covariant-corona-execution` |
| 42 | Scope boundary | `thm:continuum-reconstruction-output`, `cor:spectral-realization-boundary` |
| 43 | Closure by an explicit interface requirement | `cor:spectral-realization-boundary` |
| 44 | Scope boundary plus reconstruction gate | `thm:continuum-reconstruction-output`, `thm:uniform-gap-proof-model`, `cor:spectral-realization-boundary` |

This matrix deliberately distinguishes a rigorous repair from a stronger
result that has not been proved.  Every invalid promotion or inference listed
in A--G is now blocked.  The stronger termination or reconstruction
capability requested by items 5, 10, 15--16, 18--19, 22--23, 25--26, 30--31,
37, 39--44 is not closed.  In those rows the manuscript has a sound gate,
successor, or scope restriction, but no theorem forcing that successor to
terminate in finite exclusion or ordinary realization.  The remaining rows
close the stated local defect.

Therefore the present source is logically sound and type-safe, but the claim
that every item in A--G has been converted into a terminating universal
continuum evaluator would be false.  In particular, the manuscript does not
prove unconditional three-dimensional Navier--Stokes regularity or construct
a Yang--Mills continuum theory.  Those conclusions cannot be inserted by
renaming a prospective atom, separator, or reconstruction antecedent as a
closure theorem.

The quantifier obstruction is now a theorem rather than a scope convention:
`thm:quantifier-faithful-continuum-accountability` proves that source
exhaustion yields

[
\operatorname{Reach}_\Sigma^{\rm Phys}>0
\Longrightarrow
\mathsf T_\Sigma^{\rm Phys,Sat}(\mathcal B)\ge 1/5,
]

and also proves that the framework cannot force the opposite profile bound
uniformly over public presentations, because presentations with independently
realized contact are allowed.  Thus a demand that source classification alone
close every target cell would contradict the framework's explicit allowance
of singular equations.  A particular specialization closes by a generated
upper-profile derivation or by an independently realized contacting orbit;
neither value may be inserted into the public presentation.

### Remaining terminal cell after the coercivity implementation

The general dyadic ordered-coercivity rule now performs the equality step
constructively.  Whenever the public equation generates

[
A^{2^k}\le C M^aP^b,
\qquad M\le M_0<\infty,
]

zero production forces zero target activity for every graph-complete positive
functional.  This closes the former generalized-equality loophole without
ordinary realization.  In the Navier--Stokes specialization the weighted
Poincare--Sobolev row closes every finite-amplitude amplification tangent.

The surviving positive-activity cell is therefore the joint value

[
r_j\to0,
\qquad
M_{2,j}\to\infty,
]

with the complete tuple

[
(r_j,M_{2,j},D_j,M_j,r_j(D_j+M_j),
  \mathcal O_{\zeta,j},Q_{\Sigma,j},\operatorname{Anc}_j).
]

`cor:ns-surviving-amplitude-scale-cell` proves this localization.  It also
proves that the current physical carrier cannot close the cell: the public
relation (p_j=r_j(D_j+M_j)) admits (r_j\to0), arbitrary normalized
dissipation, and (p_j\to0).  Thus a scale-independent estimate
(D_j+M_j\le Cp_j) is not an ordered consequence of the existing algebra.

The fast-track notebook does not repair this missing implication.  Its scale
module assumes scale stability and a positive per-log-scale dissipation
quantum, while its conservative-carrier module assumes uniform domination
constants.  Importing any of those rows as data would reintroduce the exact
certificate gap being audited.  The remaining terminal construction must
therefore derive a new scale-critical carrier from the public equation or
prove the joint amplitude--scale cell target-null.  The present equation and
energy-carrier relations do not imply either statement.

## Part-I-aligned repair program

This section turns every numbered defect into an implementation task.  The
translation used throughout is

| Part I | Continuum extension |
|---|---|
| first successful test | first completed target-shell crossing |
| finite computation transcript | finite stopped current history |
| joint observable frontier | joint pre-contact current frontier |
| conditional projection increment | conditional shell-current increment |
| constructor cost | owner-tagged physical valuation |
| saturated success profile | saturated target-reachability profile |
| executed algorithm | ordinary same-origin PDE orbit |

The public presentation supplies textbook data: equation, state and
continuation classes, initial and boundary data, native energy law, covariance
maps, and standard approximation operators.  It supplies neither a regularity
conclusion nor a problem-specific estimate.  Every identity below must be
generated from that presentation by the structural grammar.

### A. Terminal semantics

#### 1. Preserve origin polarity

**Part-I analogue:** a completed success label cannot be an ancestor of the
selector that produced success.  **Construction:** attach `Hyp/Ind` to every
shell, limit, corona, separator, and realization record; make joins, limits,
quotients, and graph completion preserve `Hyp`.  Only a direct ordinary
solution graph or an approximation tower built independently of assumed
contact may create `Ind`.  **Closed when:** structural induction over every
constructor proves `Hyp` can never become `Ind`, and all singular-existence
theorems require `Ind`.

#### 2. Make nonordinary values proper descendants

**Part-I analogue:** a failed evaluator is a transcript state, not acceptance.
**Construction:** totalize each partial analytic operation into disjoint
ordinary, domain-failure, blow-up, oscillation, concentration, and tail
values; retain the source owner and shell cocycle and reapply target
projection.  **Closed when:** every such value is charged, target-null,
strictly refined, or ordinarily realized; none is a singular verdict.

#### 3. Treat separators as dual source records

**Part-I analogue:** a distinguisher exposes useful ancestry but is not an
execution.  **Construction:** join every polar separator to its primal owner,
generate adjoint pullbacks and polarizations, and re-enter the joint word into
the five-source compiler.  **Closed when:** the separator disappears only by
a finite carrier identity, target-nullity, or ordinary realization of its
primal owner.

#### 4. Use a sound terminal contract

**Part-I analogue:** accountability does not declare every task hard.
**Construction:** distinguish internal evaluator states from verdicts.
Profiles, positive functionals, separators, equality cells, and graph
descendants are internal.  Verdicts are checked target exclusion and
independently realized ordinary contact.  **Closed when:** both verdict maps
are sound; uniform termination over all PDE presentations is not asserted.

#### 5. Construct independent realization

**Part-I analogue:** a legal transcript is executable from the public input.
**Construction:** build a same-origin approximation path carrying initial
data, chronology, equation/domain/trace/product defects, physical ledger, and
shell contact.  A Dirac gate returns an orbit exactly when one coherent path
has vanishing defects and converges in the weak-equation topology.  **Closed
when:** this condition is necessary and sufficient for every existence claim
made through the approximation grammar; direct ordinary solution graphs form
the second realization route.

### B. Reconstruction and compactification

#### 6. Separate relaxed laws from paths

**Part-I analogue:** a law on transcripts is not one executed transcript.
**Construction:** disintegrate the positive functional over time and origin;
test zero conditional variance and every equation/domain graph.  **Closed
when:** orbit extraction requires a Dirac conditional law, common origin,
chronological consistency, and vanishing public defects.

#### 7. Enforce one projective branch

**Part-I analogue:** all vertices belong to one transcript.  **Construction:**
organize approximations as a rooted refinement tree and require one infinite
branch whose restrictions agree on every earlier cylinder.  **Closed when:**
the inverse-limit point is proved to arise from one branch; unrelated
coordinatewise subsequences fail realization.

#### 8. Block artificial compactification points from existence

**Part-I analogue:** inaccessible table entries are not executable advice.
**Construction:** compactification points may support separation and
exclusion, but have empty realization fiber until reached by a zero-defect
branch.  **Closed when:** every existence verdict lies in the image of the
ordinary realization map.

#### 9. Restrict graph completeness to information preservation

**Part-I analogue:** a complete record preserves provenance but does not make
an operation executable.  **Construction:** factor terminal evaluation as
`record -> graph-complete value -> realization gate`.  **Closed when:** no
graph-compatible value is promoted directly to physical existence.

#### 10. Prove approximation--orbit equivalence

**Part-I analogue:** operational and transcript semantics agree.
**Construction:** prove stability of the weak equation, initial data, traces,
products, and physical ledger along a zero-defect branch; compile every orbit
claimed through the grammar back into compatible prefixes.  **Closed when:**
the equivalence holds for the declared approximation grammar.  Solutions
outside that grammar are not claimed.

### C. Ordered-algebra evaluation

#### 11. Replace semantic cone membership by finite-cylinder duality

**Part-I analogue:** source cells are evaluated on finite represented
frontiers.  **Construction:** project owner and carrier cone to the first
`n` generated cylinders.  Exact membership returns a finite carrier identity;
strict nonmembership returns a finite separator; boundary membership appends
the next cylinder with its error.  **Closed when:** finite primal/dual values
are monotone and converge, and only finite identities authorize charging.

#### 12. Derive the topology from target tests

**Part-I analogue:** the observable algebra fixes the relevant topology.
**Construction:** use the initial topology of bounded shell, current, ledger,
and realization-defect cylinders; complete exact ancestry cells separately,
then quotient the target-null kernel.  **Closed when:** every limit constructor
is continuous on its declared cell and ordinary zero-defect branches embed
faithfully.

#### 13. Make separator discovery coefficient-complete

**Part-I analogue:** a readout retains its actual coefficients.  **Construction:**
enumerate rational separators only on rational-polyhedral projections;
otherwise retain the exact real coefficient tuple.  Rationalize only after a
positive recorded margin.  **Closed when:** every strict separation appears
on a finite cylinder and approximation error is smaller than its margin.

#### 14. Totalize the non-semialgebraic grammar

**Part-I analogue:** every legal constructor has an operational graph.
**Construction:** give exponentials, resolvents, unbounded domains,
distributional products, traces, measures, and limits explicit total graphs;
use semialgebraic elimination only on polynomial fragments.  **Closed when:**
every proof expression expands into a finite declared DAG or a typed boundary
value.

#### 15. Prove the relative completeness Part I requires

**Part-I analogue:** saturation covers the declared grammar, not every
mathematical truth.  **Construction:** prove that every finite consequence of
the generated target-local cylinder algebra has a finite derivation or a
finite positive functional separating it.  The latter remains a profile
state, not an orbit.  **Closed when:** every generated finite identity is
accounted for without claiming completeness for all analytic PDE identities.

#### 16. Compile equality ideals

**Part-I analogue:** zero advantage is evaluated on its exact fiber.
**Construction:** on zero production, generate the finite real radical using
squares, polarization, adjoints, symmetries, and dyadic coercivity; reproject
the target after every enlargement.  **Closed when:** each finite equality
cell becomes target-null or strictly smaller, while nonordinary coefficients
remain typed descendants.

#### 17. Require checked deletion transcripts

**Part-I analogue:** pruning requires a verifier record.  **Construction:**
attach a finite ordered emptiness or nullity identity to every deleted cell
and a checked covering proof to every finite cover.  **Closed when:** replaying
the transcript verifies all deletions without semantic compactness as an
oracle.

#### 18. Evaluate fixed atoms as source profiles

**Part-I analogue:** a target-aligned algorithm is a success-profile witness,
not a seventh mechanism.  **Construction:** insert a primal--polar fixed atom
into its exact five-source profile with target increment and physical
valuation, then apply profile duality, equality compilation, and realization.
**Closed when:** fixedness is never terminal; the atom remains an explicit
profile lower bound until charged, nulled, or realized.

#### 19. Preserve infinite composition by backward frontiers

**Part-I analogue:** many individually null operations cannot create
uncharged joint information.  **Construction:** use the implemented canonical
two-record source-current law, conditional increments, occurrence direct sum,
and cumulative joint algebra.  **Closed when:**
`N/4=sum Delta`, `N=sum widehat Delta`, and every nonzero limit has a nonzero
finite contextual increment.  This item is closed in the manuscript.

#### 20. Replace universal truth evaluation by profile evaluation

**Part-I analogue:** accountability plus a task-specific profile bound proves
hardness.  **Construction:** derive an exact primal--dual formula for each
physical source profile.  Each PDE specialization must derive a profile
ceiling or an independently realized contacting orbit from the same algebra.
**Closed when:** no third verdict exists.  Uniform termination is not required,
because singular equations are valid presentations.

### D. Physical financing

#### 21. Derive weighted-root and exterior ceilings

**Part-I analogue:** downstream normalization stays in the constructor ledger.
**Construction:** solve adjoint weights on finite horizons, retain both
endpoints, glue horizons before positive parts, and restrict exterior input to
the public boundary/forcing measure.  **Closed when:** every finite-financing
verdict contains derived bounds for root, production, and exterior terms;
unbounded weights enter scale cells.

#### 22. Expand unbounded financing

**Part-I analogue:** an over-budget constructor exposes its responsible
resource coordinate.  **Construction:** factor the term through scale rate,
carrier, horizon, and exterior owner; apply the backward frontier and generate
its adjoint carrier.  **Closed when:** it telescopes, is charged, is null, or
enters a strictly refined scale/equality cell.

#### 23. Prove source-profile/carrier duality

**Part-I analogue:** capability profiles are inverse resource frontiers.
**Construction:** for each exact source cell, equate the supremum of normalized
contextual progress under the physical ceiling with the infimum over generated
covariant carriers dominating that progress.  Include storage and exterior
terms.  **Closed when:** finite-cylinder strong duality, monotone passage,
equality evaluation, and realization typing are proved; separators are dual
profile witnesses only.

#### 24. Keep signed currents finite-prefix local

**Part-I analogue:** conditional increments are combined before undefined
cancellation.  **Construction:** define signed source currents on finite
occurrence algebras, retain total variation, and pass globally only with a
proved local-finiteness bound; globally decompose only the positive contact
measure.  **Closed when:** every global signed-measure claim has a variation
proof.

#### 25. Evaluate physical-singular target mass

**Part-I analogue:** residual-ancestry correlation re-enters a source profile.
**Construction:** project the component singular to the physical measure into
five owners and apply amplification, equality, carrier-polar, and realization
steps owner-by-owner.  **Closed when:** measure singularity is only a typed
zero-denominator cell, never a blow-up verdict by itself.

#### 26. Compute amplification cellwise

**Part-I analogue:** profiles are bounded through exact source cells.
**Construction:** totalize target progress divided by production, storage,
and exterior input in every source/polarity cell; bound finite ratios by
carrier duality and route infinite ratios through equality and realization.
**Closed when:** finitely verified cell bounds cover the saturated profile.

### E. Target and continuation

#### 27. Compile the target from the theorem statement

**Part-I analogue:** the accepting set belongs to the task presentation.
**Construction:** declare the weakest acceptable continuation class, local
uniqueness, and gauge identifications; define contact as its failure on an
ordinary maximal path.  **Closed when:** target avoidance is equivalent to the
stated global-regularity conclusion.

#### 28. Make event contact primary

**Part-I analogue:** first hit is primary and completed quotients are
accounting.  **Construction:** use the finite noncontinuation flag on the
same-origin path; compactified germs are shell-support coordinates requiring
realization.  **Closed when:** every actual noncontinuation triggers the flag
and no unrelated relaxed point inherits it.

#### 29. Prove shell cofinality by separation

**Part-I analogue:** verifier observables separate target and nontarget.
**Construction:** generate rational ramps of continuation-defect coordinates
and prove their joint zero set equals the regular continuation locus.  **Closed
when:** every ordinary noncontinuation crosses cofinal normalized shells and
every regular continuation eventually avoids them.

#### 30. Evaluate nonordinary shell currents

**Part-I analogue:** a failed primitive remains in the expanded transcript.
**Construction:** totalize products, traces, pressure, charts, and Stieltjes
pairings; retain the first failed graph with target covector, owner, physical
denominator, and multiplicity; run the same backward/carrier evaluator.
**Closed when:** every graph current is charged, null, strictly refined, or
ordinarily realized.

### F. Navier--Stokes unit test

#### 31. Execute the general evaluator, not an NS-specific terminal rule

**Part-I analogue:** LPN instantiates the general profile theorem.
**Construction:** map viscosity, convection, pressure, gauges, cutoffs, scale,
exterior flux, and suitable-energy defect into general source cells and run
the common backward, valuation, equality, and realization compilers.  **Closed
when:** the example has no conditional conclusion or NS-only terminal branch.

#### 32. Remove contact-derived reachability equivalences

**Part-I analogue:** a successful transcript lower-bounds the success profile;
it does not prove reachability from unrelated input.  **Construction:** use
contact-derived decompositions only prospectively and determine reachability
through the ordinary initial-data realization map.  **Closed when:** no
post-contact quantity proves its own existence.

#### 33. Preserve `Hyp` in critical tails

**Part-I analogue:** retrospective labels never become selectors.
**Construction:** propagate `Hyp` through amplification, pressure, scale,
tail, and corona records.  **Closed when:** singular existence requires a
separate `Ind` path with the same coordinates.

#### 34. Make failed normalized bounds amplitude cells

**Part-I analogue:** absence of a cheap quotient is retained structure.
**Construction:** totalize normalized `L2`, `L3`, pressure, and tail values;
join finite/unbounded/nonordinary cells with scale and unnormalized energy.
**Closed when:** the microscope assumes no uniform normalized bound and every
failure is a source-owned amplitude/scale cell.

#### 35. Use the actual scale-dependent price

**Part-I analogue:** constructor cost uses its actual parameters.
**Construction:** compute coercive price from retained amplitude, scale,
activity, and carrier coordinates and sum its physical value on disjoint
occurrences.  **Closed when:** every divergent-price claim follows from this
schedule and the kinetic-energy ledger.

#### 36. Put the covariant microscope in the valuation

**Part-I analogue:** representation change cannot erase cost.  **Construction:**
treat scale as `Lift`, differentiate the pulled-back carrier, retain scale
current and adjoint weight, and glue scale interfaces before comparing
normalized and physical production.  **Closed when:** shrinkage with zero
physical price necessarily enters the equality compiler.

#### 37. Aggregate signed transport first

**Part-I analogue:** joint effects are evaluated before coordinatewise norms.
**Construction:** add convection, pressure, cutoff, translation, scale,
exterior, and defect currents with signs on compatible interfaces; compare
only the aggregate inward current with the carrier.  **Closed when:** no proof
sums absolute internal currents and every remainder re-enters carrier duality.

#### 38. Treat ordinary and nonordinary tangents uniformly

**Part-I analogue:** failure values remain in the same saturated grammar.
**Construction:** quotient ordinary tangents by Galilean/gradient kernels;
send nonordinary tangents to their first failed domain, pressure, scale, or
convergence graph.  **Closed when:** both pass through equality and realization
and neither is called singular solely from zero production.

#### 39. Compile pressure and harmonic tails

**Part-I analogue:** boundary/oracle calls retain query and readout ancestry.
**Construction:** split local pressure, harmonic gauge, exterior tail, and
trace; generate adjoint shell pairings and interface cancellation; retain
truncation and exterior owners on failures.  **Closed when:** every visible
tail is charged, null, reduced, or realized.

#### 40. Compile scale equality into relative equilibria

**Part-I analogue:** equality exposes the exact attaining structure.
**Construction:** saturate equality in the signed covariant carrier, derive
the relative scale/translation equation, quotient gauges, and apply generated
coercivity; keep unbounded amplitude joined to scale and price.  **Closed
when:** every equality cell is null, charged, or independently realized.  The
finite-amplitude cell is closed; the unbounded amplitude--scale cell remains
the stress test.

#### 41. Finish the test through the general terminal machinery

**Part-I analogue:** the application substitutes cellwise bounds into general
accountability.  **Construction:** feed all NS separators, equality cells, and
tails into the general profile evaluator.  **Closed when:** the example ends
in checked avoidance or an `Ind` zero-defect contacting orbit, with no
unevaluated NS successor.

### G. Hamiltonian and spectral reconstruction

#### 42. Construct the operator inside the grammar

**Part-I analogue:** the transition operator is derived from the presented
computation.  **Construction:** generate Hilbert space, closed form, domain,
generator, and boundary conditions from the PDE/regulator presentation;
totalize closability, density, and domain failures.  **Closed when:** spectral
machinery is used only after this graph has an ordinary value.

#### 43. Add a same-origin spectral-to-reachability map

**Part-I analogue:** a spectral feature counts through the pre-hit selector
that uses it.  **Construction:** construct an intertwiner preserving time,
shells, source currents, and carrier; pull spectral covectors back through its
adjoint.  **Closed when:** poles, pseudospectra, and range defects affect PDE
reachability only through nonzero same-origin pulled-back pairing.

#### 44. Treat regulator reconstruction as realization

**Part-I analogue:** consistent finite instances do not automatically define
one uniform infinite execution.  **Construction:** join regulator levels and
generate projective consistency, reflection positivity, nontriviality,
cyclic-vacuum, strong-continuity, and Hamiltonian tests.  **Closed when:** a
zero-defect projective branch constructs the continuum Hilbert space and
Hamiltonian before the mass-gap target is evaluated.

## Implementation order

1. Retain items 1--4, 8--9, 17, 19, 24, and 27--29 as the soundness and
   accountability base already implemented.
2. Complete physical valuation and exact profile duality: items 11--16 and
   21--26.
3. Complete equality and covariant-scale evaluation: items 18, 22, 30, and
   34--40.
4. Complete same-origin realization: items 5--10.
5. Re-run the Navier--Stokes backend through items 31--41 without adding
   application-specific terminal rules.
6. Apply the realization architecture to operator and regulator presentations:
   items 42--44.

The accountability layer matches Part I when every target effect is forced
into a finite contextual source increment.  The operational layer matches
Part I when physical valuation computes the corresponding saturated source
profile.  Continuum dynamics additionally needs the realization layer because
finite structural consistency must be converted into one ordinary
time-dependent orbit before singular existence is asserted.
