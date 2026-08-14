
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
   `thm:approximation-orbit-realization-criterion` gives the exact operational
   semantics of realization through the declared approximation grammar in
   terms of one coherent zero-defect, zero-variance, ordinary-domain tower;
   `thm:dirac-realization-gate` reconstructs the orbit when the test holds.
   A direct ordinary value of the total solution graph realizes itself.  The
   manuscript does **not** claim that every
   relaxed atom has such a tower or that the hierarchy manufactures one.
6. Positive-functional reconstruction is explicitly typed as relaxation.
   `lem:generator-variance-dirac-state` proves that zero variance on the
   bounded cylinder generators makes the functional multiplicative on the
   entire cylinder algebra; the Dirac gate then reconstructs one PDE path.
7. The approximation--orbit criterion requires convergence of all coordinates
   along one compatible tower path.  Coordinatewise subsequences do not pass.
8. Artificial compactification points are harmless for exclusion and barred
   from existence by the no-compactification-promotion corollary.
9. Graph completeness now means information preservation only.  Attainability
   is a separate ordinary realization row.
10. `thm:approximation-orbit-realization-criterion` proves sufficiency of a
    coherent zero-defect, zero-variance, ordinary-domain tower and necessity
    for every realization asserted through the public approximation grammar.
    This is the complete operational equivalence for that grammar.  Direct
    ordinary solution-graph evaluations remain the other realization route.
    Target contact additionally uses ordinary shell and continuation rows.
11. The carrier cone is split into the finite algebraic cone and its
    topological closure.  Only algebraic membership is a finite charging
    proof; closure-only membership is a typed cone-boundary successor.
    `thm:exact-finite-cylinder-source-profile-duality` now computes the exact
    support value on every checked finite cylinder by a finite-dimensional
    primal--dual formula.
12. The carrier-current topology is now the initial locally convex topology
    of bounded rational cylinder seminorms.  Its closure is the inverse limit
    of the checked finite-cylinder relaxations by
    `thm:monotone-cylinder-source-profile-completion`; faithfulness to an
    ordinary PDE orbit remains exactly the approximation--orbit realization
    gate.
13. Strict separators are proved to depend on finitely many cylinder
    coordinates, but their coefficients are not falsely declared rational.
    Rational enumeration is claimed complete only for rational-polyhedral
    finite projections.  The finite-cylinder profile dual retains arbitrary
    real dual coefficients through the total dual graph.
14. Finite semialgebraic elimination is restricted to the polynomial moment
    relaxation.  Exponentials, resolvents, unbounded operations,
    distributional products, and limits remain total-graph coordinates.
    Exact finite-cylinder duality uses convex separation rather than a
    semialgebraic claim.
15. The ordered grammar makes no relative-completeness claim for all true PDE
    identities.  Failure to derive an identity produces a compatible relaxed
    profile functional by monotone cylinder completion, never a physical
    counterexample.  This is the same profile-witness role played by a
    target-aligned derivation in Part~I.
16. Strict positivity and zero-margin equality are separated.  Equality
    is now tested first by the dyadic ordered-coercivity terminal rule.  A
    generated finite-coefficient row (A^{2^k}\le CM^aP^b) and zero
    production force zero target activity directly for every positive
    functional.  Only an unbounded coefficient, a nonordinary relation, or an
    equality cell lacking such a generated domination row continues.  The
    finite-cylinder duality theorem now retains the exact exposed equality
    face and the vanishing terms of its dual row before that compiler runs.
17. Compact semantic emptiness is usable only with the checked finite deletion
    identities at the finite empty level.  A profile exclusion is licensed
    only when a checked finite dual row places the source profile below the
    target floor.
18. A primal--polar fixed point is a prospective source atom, not a verdict.
    It is inserted into the finite-cylinder source profile and is either
    bounded by a checked dual row or retained in the compatible relaxed
    profile witness.
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
    been proved.  `cor:part-I-continuum-profile-evaluation` supplies the exact
    Part-I analogue: finite checked profile exclusion or a compatible relaxed
    profile witness passed to equality and same-origin realization.
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
31. The Navier--Stokes specialization now evaluates its last joint cell by
    the same exact finite-cylinder and monotone saturated source profile used
    by the general calculus; it introduces no application-specific terminal
    rule.
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
42. The operator-construction graph now generates the cylinder core, null
    quotient, Hilbert completion, closable form, semigroup, generator, domain,
    and boundary relation in order.  Positivity, null invariance, closability,
    semigroup, contraction, symmetry, continuity, domain, and boundary failures
    have least rational witnesses routed through source saturation.
43. The same-origin spectral reachability graph now joins evolution, target
    shells, source currents, and the physical carrier.  Spectral covectors
    enter reachability only through their adjoint pullback to the complete
    pre-contact frontier; a failed intertwining row is itself source charged.
44. The finite regulator realization hierarchy now joins all regulator levels.
    Finite infeasibility has an ordered proof; a least consistency, reflection,
    semigroup, or continuity failure has a typed witness; variance coordinates
    decide triviality or generate a nonvacuum class; and the zero-defect
    inverse-limit branch constructs the reflection-positive Hilbert space,
    cyclic vacuum, and Hamiltonian before the gap target is evaluated.

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
| 5 | Closure for the declared realization semantics | `thm:dirac-realization-gate`, `thm:approximation-orbit-realization-criterion` |
| 6 | Closure of the Dirac reconstruction step | `lem:generator-variance-dirac-state`, `thm:dirac-realization-gate` |
| 7 | Closure | `thm:approximation-orbit-realization-criterion` (D1)--(D2) |
| 8 | Closure of existence typing | `cor:no-compactification-existence-promotion` |
| 9 | Closure of graph/attainability separation | `cor:no-compactification-existence-promotion` |
| 10 | Closure for the declared approximation grammar | `thm:approximation-orbit-realization-criterion` |
| 11 | Exact finite-cylinder profile closure | `def:finite-cylinder-physical-source-profile`, `thm:exact-finite-cylinder-source-profile-duality` |
| 12 | Cylinder-topology closure; realization kept separate | `thm:monotone-cylinder-source-profile-completion`, `cor:no-compactification-existence-promotion` |
| 13 | Exact real finite-cylinder dual; rational-polyhedral subcase only | `lem:rational-carrier-separation`, `thm:exact-finite-cylinder-source-profile-duality` |
| 14 | Convex finite-cylinder closure; no global semialgebraic claim | `thm:exact-finite-cylinder-source-profile-duality`, `prop:sound-scope-ordered-hierarchy` (S3) |
| 15 | Exact profile completion and generated-invariant protocol | `def:invariant-evaluation-protocol`, `thm:invariant-evaluation-protocol-closure`, `thm:fast-track-invariant-by-invariant-evaluation`, `thm:five-source-invariant-verification-protocol`, `cor:total-binary-five-source-evaluation`, `thm:invariant-complete-five-source-decision-ledger`, `thm:coordinatewise-source-invariant-decision`, `thm:simultaneous-source-ledger-terminal-evaluation` |
| 16 | Equality-face retention plus generated coercivity closure | `thm:exact-finite-cylinder-source-profile-duality`, `thm:dyadic-ordered-coercivity-terminal-rule`, `thm:saturation-equation-compiler` |
| 17 | Checked finite profile/deletion transcripts | `thm:exact-finite-cylinder-source-profile-duality`, `def:finite-pruning-transcript`, `thm:canonical-finite-pruning-transcript` |
| 18 | Fixed atoms evaluated as profile witnesses | `thm:exact-finite-cylinder-source-profile-duality`, `cor:part-I-continuum-profile-evaluation`, `thm:no-terminal-zero-price-model` |
| 19 | Exact finite-prefix backward-frontier and cumulative-accounting closure | `thm:exact-prospective-continuum-backward-factorization`, `thm:cofinal-prospective-frontier-closure`, `thm:continuum-composition-no-creation`, `cor:no-limit-created-target-alignment` |
| 20 | Exact Part-I protocol for every generated invariant | `thm:unconditional-target-local-invariant-evaluator`, `def:invariant-evaluation-protocol`, `thm:invariant-evaluation-protocol-closure`, `thm:five-source-invariant-verification-protocol`, `cor:total-binary-five-source-evaluation`, `thm:invariant-complete-five-source-decision-ledger`, `thm:coordinatewise-source-invariant-decision`, `thm:simultaneous-source-ledger-terminal-evaluation`, `thm:quantifier-faithful-continuum-accountability` |
| 21 | Finite-prefix closure | `prop:finite-prefix-root-exterior-accounting`, `thm:complete-covariant-corona-evaluator` |
| 22 | Evaluated source-owned expansion | `prop:finite-prefix-root-exterior-accounting`, `thm:finite-prefix-source-profile-carrier-duality` |
| 23 | Exact finite-prefix and monotone saturated duality | `def:finite-prefix-physical-valuation`, `thm:finite-prefix-source-profile-carrier-duality`, `thm:monotone-saturated-physical-valuation` |
| 24 | Variation-safe closure | `def:same-origin-occurrence-measure`, `thm:variation-safe-finite-prefix-current-principle` |
| 25 | Evaluated zero-denominator source cell | `thm:exact-compositional-physical-accounting`, `cor:zero-physical-denominator-evaluated-cell`, `thm:amplification-zero-production-tangent` |
| 26 | Exact cellwise saturated valuation | `thm:physical-target-capacity-duality`, `thm:monotone-saturated-physical-valuation` |
| 27 | Closure | `def:singular-target` |
| 28 | Closure | `prop:terminal-coverage`, `cor:no-compactification-existence-promotion` |
| 29 | Closure | `prop:shell-cofinality-realization-fidelity` |
| 30 | Finite-prefix graph evaluation | `thm:defect-totalization-five-channel`, `thm:nonordinary-shell-current-first-failure-evaluator`, `thm:projection-first-saturation` |
| 31 | Typing repair; no NS regularity claim | `thm:ns-backend-scope`, conclusion after (A10) |
| 32 | Typing repair | `thm:ns-empty-singular-target-core` |
| 33 | Closure | `thm:ns-critical-tail-nullity`, `thm:no-recycled-contact-realization` |
| 34 | Typing repair | `thm:ns-canonical-target-orbit` (C2)--(C3) |
| 35 | Closure | `lem:ns-computed-critical-price` |
| 36 | Closure of scale accounting | `prop:ns-no-free-shrinkage`, `thm:ns-signed-covariant-carrier` |
| 37 | Closed by recursive transition and exact profile evaluation | `prop:ns-complete-covariant-corona-execution`, `thm:ns-amplitude-scale-profile-evaluation` |
| 38 | Closure of ordinary/nonordinary split | `prop:ns-ordinary-amplification-tangent-nullity`, `thm:ns-critical-tail-nullity` |
| 39 | Closed by total-graph recursion and profile re-entry | `def:ns-collapsed-successor-cells`, `thm:ns-critical-tail-nullity`, `thm:ns-amplitude-scale-profile-evaluation` |
| 40 | Exact amplitude--scale invariant-packet closure | `thm:unconditional-target-local-invariant-evaluator`, `cor:ns-surviving-amplitude-scale-cell`, `thm:ns-amplitude-scale-profile-evaluation` |
| 41 | Complete specialization of the invariant, profile, and realization machinery | `thm:fast-track-invariant-by-invariant-evaluation`, `thm:ns-carrier-polar-recursion`, `prop:ns-complete-covariant-corona-execution`, `cor:ns-profile-specialization-complete` |
| 42 | Constructive first-failure closure | `def:operator-construction-graph`, `thm:first-failure-operator-construction`, `thm:continuum-reconstruction-output` |
| 43 | Same-origin factorization closure | `def:same-origin-spectral-reachability-graph`, `thm:same-origin-spectral-pullback`, `cor:spectral-realization-boundary` |
| 44 | Finite proof/typed failure/ordinary realization closure | `def:finite-regulator-realization-hierarchy`, `thm:regulator-proof-failure-realization`, `thm:continuum-reconstruction-output`, `thm:uniform-gap-proof-model` |

The matrix distinguishes structural profile evaluation from ordinary orbit
realization.  Every invalid promotion or inference listed in A--G is blocked,
and every generated target-visible successor re-enters an exact finite-cylinder
or monotone saturated source profile.  A finite profile ceiling is a checked
exclusion proof.  A compatible positive functional is a profile witness and
becomes a physical contact only through the ordinary same-origin realization
graph.

Thus the continuum evaluator has the same terminal semantics as Part~I: it
computes the saturated target-aligned source profile.  A generated
source-local upper-profile derivation proves avoidance, while an ordinary
same-origin realized path proves contact.
No prospective atom, separator, or reconstruction antecedent is promoted to
an orbit.

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

### Coordinatewise closure of the amplitude--scale stress cell

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

The only joint value not removed by the finite-amplitude coercivity row is

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

`cor:ns-surviving-amplitude-scale-cell` proves this localization.  The public
relation (p_j=r_j(D_j+M_j)) by itself permits (r_j\to0), arbitrary normalized
dissipation, and (p_j\to0), so it is not used as a scale-independent estimate.
Instead `thm:ns-amplitude-scale-profile-evaluation` retains the complete joint
record and evaluates every one of its finite-cylinder coordinates.
`thm:coordinatewise-source-invariant-decision` then gives the exact terminal
structural value: cofinal zero rows prove that the cell is target-null, while
a compatible positive floor reconstructs a target-aligned joint source with
its scale multiplicity, physical carrier, source owner, target covector, and
complete preceding frontier.  The latter is structural presence, not an
unevaluated cell, and its ordinary same-origin realization is evaluated by
the realization graph.  Scale collapse, amplitude divergence, and vanishing
average price therefore create no third terminal status.

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

**Implemented mechanism.** `thm:no-recycled-contact-realization` proves by
constructor induction that joins, quotients, limits, graph completion,
separation, and resaturation preserve origin polarity.
`thm:three-output-target-aligned-current-compiler` propagates that tag through
the full target-current compiler, and `def:explicit-singular-mechanism`
requires an `Ind` ordinary orbit for a contact verdict.

#### 2. Make nonordinary values proper descendants

**Part-I analogue:** a failed evaluator is a transcript state, not acceptance.
**Construction:** totalize each partial analytic operation into disjoint
ordinary, domain-failure, blow-up, oscillation, concentration, and tail
values; retain the source owner and shell cocycle and reapply target
projection.  **Closed when:** every such value is charged, target-null,
strictly refined, or ordinarily realized; none is a singular verdict.

**Implemented mechanism.** `thm:approximation-realization-first-failure`
orders every domain, equation, product, trace, chart, and convergence graph
and retains its least nonordinary coordinate with owner and target covector.
`cor:no-compactification-existence-promotion` prevents such a coordinate from
entering the physical contact range before zero-defect realization.

#### 3. Treat separators as dual source records

**Part-I analogue:** a distinguisher exposes useful ancestry but is not an
execution.  **Construction:** join every polar separator to its primal owner,
generate adjoint pullbacks and polarizations, and re-enter the joint word into
the five-source compiler.  **Closed when:** the separator disappears only by
a finite carrier identity, target-nullity, or ordinary realization of its
primal owner.

**Implemented mechanism.** `def:target-local-carrier-polar-successor` joins
the separator to its primal current, physical carrier, shell cocycle, and
ancestry.  `thm:recursive-carrier-polar-exhaustion` generates all adjoint and
polar descendants before realization, while `cor:no-pre-polar-realization`
blocks a separator from serving as an orbit.

#### 4. Use a sound terminal contract

**Part-I analogue:** accountability does not declare every task hard.
**Construction:** distinguish internal evaluator states from verdicts.
Profiles, positive functionals, separators, equality cells, and graph
descendants are internal.  Verdicts are checked target exclusion and
independently realized ordinary contact.  **Closed when:** both verdict maps
are sound; uniform termination over all PDE presentations is not asserted.

**Implemented mechanism.** `cor:binary-terminal-semantics` and
`cor:binary-continuum-terminal-theorem` define the two verdict maps.  Finite
checked carrier/nullity derivations produce exclusion; zero-defect ordinary
same-origin paths produce contact.  Profiles, separators, positive
functionals, equality fibers, and graph descendants remain internal values.

#### 5. Construct independent realization

**Part-I analogue:** a legal transcript is executable from the public input.
**Construction:** build a same-origin approximation path carrying initial
data, chronology, equation/domain/trace/product defects, physical ledger, and
shell contact.  A Dirac gate returns an orbit exactly when one coherent path
has vanishing defects and converges in the weak-equation topology.  **Closed
when:** this condition is necessary and sufficient for every existence claim
made through the approximation grammar; direct ordinary solution graphs form
the second realization route.

**Implemented mechanism.** `thm:dirac-realization-gate` reconstructs a path
from a common-origin zero-variance law with vanishing public defects.
`thm:approximation-orbit-realization-criterion` proves necessity and
sufficiency for the declared approximation grammar and includes the direct
ordinary-solution route.

### B. Reconstruction and compactification

#### 6. Separate relaxed laws from paths

**Part-I analogue:** a law on transcripts is not one executed transcript.
**Construction:** disintegrate the positive functional over time and origin;
test zero conditional variance and every equation/domain graph.  **Closed
when:** orbit extraction requires a Dirac conditional law, common origin,
chronological consistency, and vanishing public defects.

**Implemented mechanism.** `lem:generator-variance-dirac-state` proves that
zero variance on the generated cylinder algebra forces multiplicativity.
`thm:dirac-realization-gate` combines this Dirac conclusion with chronology,
origin, equation, domain, trace, and ledger rows to reconstruct one path.

#### 7. Enforce one projective branch

**Part-I analogue:** all vertices belong to one transcript.  **Construction:**
organize approximations as a rooted refinement tree and require one infinite
branch whose restrictions agree on every earlier cylinder.  **Closed when:**
the inverse-limit point is proved to arise from one branch; unrelated
coordinatewise subsequences fail realization.

**Implemented mechanism.** Conditions (D1)--(D2) of
`thm:approximation-orbit-realization-criterion` use the rooted approximation
tree and compatible prefix maps.  The proof selects one projective branch;
coordinatewise subsequences without that branch have a nonzero realization
defect.

#### 8. Block artificial compactification points from existence

**Part-I analogue:** inaccessible table entries are not executable advice.
**Construction:** compactification points may support separation and
exclusion, but have empty realization fiber until reached by a zero-defect
branch.  **Closed when:** every existence verdict lies in the image of the
ordinary realization map.

**Implemented mechanism.** `cor:no-compactification-existence-promotion`
assigns every compactification point an empty physical realization fiber
until a zero-defect projective branch reaches it.  Compactified states remain
available for separation and upper-profile bounds.

#### 9. Restrict graph completeness to information preservation

**Part-I analogue:** a complete record preserves provenance but does not make
an operation executable.  **Construction:** factor terminal evaluation as
`record -> graph-complete value -> realization gate`.  **Closed when:** no
graph-compatible value is promoted directly to physical existence.

**Implemented mechanism.** `cor:no-compactification-existence-promotion`
factors every existence use through the graph-complete record and the
ordinary realization map.  Graph completion preserves the joint coordinates
and ancestry but supplies no attainability edge.

#### 10. Prove approximation--orbit equivalence

**Part-I analogue:** operational and transcript semantics agree.
**Construction:** prove stability of the weak equation, initial data, traces,
products, and physical ledger along a zero-defect branch; compile every orbit
claimed through the grammar back into compatible prefixes.  **Closed when:**
the equivalence holds for the declared approximation grammar.  Solutions
outside that grammar are not claimed.

**Implemented mechanism.** `thm:approximation-orbit-realization-criterion`
passes initial data, chronology, weak equations, nonlinear products, traces,
and the physical ledger in both directions between ordinary paths and
zero-defect compatible prefix towers.  Its statement is explicitly relative
to the declared public approximation grammar.

### C. Ordered-algebra evaluation

#### 11. Replace semantic cone membership by finite-cylinder duality

**Part-I analogue:** source cells are evaluated on finite represented
frontiers.  **Construction:** project owner and carrier cone to the first
`n` generated cylinders.  Exact membership returns a finite carrier identity;
strict nonmembership returns a finite separator; boundary membership appends
the next cylinder with its error.  **Closed when:** finite primal/dual values
are monotone and converge, and only finite identities authorize charging.

**Implemented mechanism.** `def:finite-cylinder-physical-source-profile`
forms the finite order-unit quotient and physical state set.
`thm:exact-finite-cylinder-source-profile-duality` proves its exact
finite-dimensional primal--dual formula, and
`thm:monotone-cylinder-source-profile-completion` takes the decreasing
cylinder limit without treating cone-boundary approximation as a finite
charge.

#### 12. Derive the topology from target tests

**Part-I analogue:** the observable algebra fixes the relevant topology.
**Construction:** use the initial topology of bounded shell, current, ledger,
and realization-defect cylinders; complete exact ancestry cells separately,
then quotient the target-null kernel.  **Closed when:** every limit constructor
is continuous on its declared cell and ordinary zero-defect branches embed
faithfully.

**Implemented mechanism.** `lem:rational-carrier-separation` works in the
initial cylinder topology after quotienting the closed target-null space.
`thm:monotone-cylinder-source-profile-completion` uses precisely those finite
projections, while `cor:no-compactification-existence-promotion` keeps the
completion separate from ordinary realization.

#### 13. Make separator discovery coefficient-complete

**Part-I analogue:** a readout retains its actual coefficients.  **Construction:**
enumerate rational separators only on rational-polyhedral projections;
otherwise retain the exact real coefficient tuple.  Rationalize only after a
positive recorded margin.  **Closed when:** every strict separation appears
on a finite cylinder and approximation error is smaller than its margin.

**Implemented mechanism.** `lem:rational-carrier-separation` retains the
exact real coefficient vector for a general finite projection and permits
rational replacement only on rational-polyhedral projections or after a
strict recorded margin.  `thm:exact-finite-cylinder-source-profile-duality`
uses real finite-dimensional duality and therefore has no rational-coefficient
completeness assumption.

#### 14. Totalize the non-semialgebraic grammar

**Part-I analogue:** every legal constructor has an operational graph.
**Construction:** give exponentials, resolvents, unbounded domains,
distributional products, traces, measures, and limits explicit total graphs;
use semialgebraic elimination only on polynomial fragments.  **Closed when:**
every proof expression expands into a finite declared DAG or a typed boundary
value.

**Implemented mechanism.** `prop:sound-scope-ordered-hierarchy` restricts
semialgebraic elimination to polynomial cylinder fragments.  Resolvents,
exponentials, domains, products, measures, traces, and limits enter through
their declared total graphs; `thm:nonordinary-shell-current-first-failure-evaluator`
returns the least failed graph to the same source-profile calculation.

#### 15. Prove the relative completeness Part I requires

**Part-I analogue:** saturation covers the declared grammar, not every
mathematical truth.  **Construction:** prove that every finite consequence of
the generated target-local cylinder algebra has a finite derivation or a
finite positive functional separating it.  The latter remains a profile
state, not an orbit.  **Closed when:** every generated finite identity is
accounted for without claiming completeness for all analytic PDE identities.

**Implemented mechanism.** `thm:exact-finite-cylinder-source-profile-duality`
gives finite separation for every consequence in the generated cylinder
space.  `cor:part-I-continuum-profile-evaluation` and
`thm:monotone-cylinder-source-profile-completion` assemble those finite
values into the saturated profile.  The claim is relative completeness of the
declared structural algebra, not completeness for external analytic truths.
`def:target-local-invariant-evaluation-packet` now packages every generated
invariant with its target quotient, current owner, physical carrier,
finite-cylinder cones, equality ideal, and realization graph.
`thm:fast-track-invariant-by-invariant-evaluation` proves the local evaluator
for all sixteen invariant families in the fast-track table.
`def:invariant-evaluation-protocol` supplies the mandatory successor operation
for equality, dual, nonordinary, cofinal, and realization states, while
`thm:invariant-evaluation-protocol-closure` proves that only checked
subcriticality/nullity and an ordinary same-origin path are stopping values.
`thm:five-source-invariant-verification-protocol` gives the explicit detector,
valuation, absence proof, existence proof, and successor operation for every
invariant in the `Geom/Caus/Abs/Lift/Bdry` normal forms and for their complete
mixed-source joint packet.  Its master detector
`eq:five-source-master-detector` includes the conditional mixed increments of
the cumulative frontier, so isolated sourcewise zero tests cannot erase a
joint effect.  Equations `eq:five-source-positive-verification` and
`eq:five-source-zero-verification` give the compatible positive-floor
reconstruction and cofinal-zero proof rows, while
`eq:five-source-valuation-strict-tests`--
`eq:five-source-valuation-equality-tests` evaluate every capacity,
domination, price, resistance, rank, scale, variation, and carrier comparison.
No invariant value or external analytic certificate is presentation data.
`cor:total-binary-five-source-evaluation` packages these rows into the exact
binary structural output for every atomic coordinate and every one of the 31
mixed source supports: a cofinal generated zero derivation or one compatible
positive functional whose least nonzero finite contextual current--probe
coordinate carries complete ancestry.  Relaxed,
nonordinary, and branch-escape witnesses count as structural presence and
continue to physical realization; they are never an unresolved third value.
`thm:invariant-complete-five-source-decision-ledger` lists every atomic
detector and valuation by name, adds the aggregate carrier, conditional mixed
increments, cycle price, realization, and shell coordinates, and assigns each
one to its exact support-profile, primal--polar-cut, cylinder-coordinate, or
cumulative-frontier evaluator.  A primal--polar cut gap is itself appended as
a source-owned detector, so sharp duality is evaluated rather than assumed.
The target rank uses a separate exact minor engine: a nonzero finite minor
proves a lower rank bound, while cofinal vanishing of all minors of a fixed
order proves the corresponding upper bound.
The same ledger explicitly includes all sixteen auxiliary fast-track
families: total graph relations, quotient commutators, gradient and tail
closure, feeding and pricing radii, routing, Wick response, capacity, scale,
carrier cohomology, recurrent and weak boundaries, equality, stochastic
brackets, and ordered moment cones.
`thm:coordinatewise-source-invariant-decision` expands that assignment into
one proof row per named coordinate.  Each row states its exact zero test,
positive test, source owner, valuation interpretation, and mandatory successor;
the theorem closes only with structural absence or structural presence.
`thm:simultaneous-source-ledger-terminal-evaluation` saturates all mandatory
successors before any coordinate is evaluated.  It then evaluates the entire
countable ledger in one graph-complete product.  A successor is part of the
data returned by a structural-presence value, not a new live branch.  Detector
profiles terminate in cofinal zero or a compatible positive floor; valuations
terminate in coincident cuts or a positive source-owned cut-gap detector; and
all graph, measure, operator, response, shell, and realization invariants are
decided by their separating rational cylinder coordinates.  Thus every source
support has exactly the terminal value `Absent` or `Present`, with no third
status introduced by equality, limits, graph boundaries, or nonordinary
realization.

#### 16. Compile equality ideals

**Part-I analogue:** zero advantage is evaluated on its exact fiber.
**Construction:** on zero production, generate the finite real radical using
squares, polarization, adjoints, symmetries, and dyadic coercivity; reproject
the target after every enlargement.  **Closed when:** each finite equality
cell becomes target-null or strictly smaller, while nonordinary coefficients
remain typed descendants.

**Implemented mechanism.** Equality faces from
`thm:exact-finite-cylinder-source-profile-duality` are enlarged by generated
squares, polarizations, adjoints, symmetries, and the
`thm:dyadic-ordered-coercivity-terminal-rule`.  `thm:saturation-equation-compiler`
reprojects after each enlargement and retains the least nonordinary
coefficient as a typed graph descendant.

#### 17. Require checked deletion transcripts

**Part-I analogue:** pruning requires a verifier record.  **Construction:**
attach a finite ordered emptiness or nullity identity to every deleted cell
and a checked covering proof to every finite cover.  **Closed when:** replaying
the transcript verifies all deletions without semantic compactness as an
oracle.

**Implemented mechanism.** `def:finite-pruning-transcript` records the
ordered identity and covering row attached to each deletion.
`thm:canonical-finite-pruning-transcript` proves replay verification; a cell
without such a row remains in the profile rather than being removed by
semantic emptiness.

#### 18. Evaluate fixed atoms as source profiles

**Part-I analogue:** a target-aligned algorithm is a success-profile witness,
not a seventh mechanism.  **Construction:** insert a primal--polar fixed atom
into its exact five-source profile with target increment and physical
valuation, then apply profile duality, equality compilation, and realization.
**Closed when:** fixedness is never terminal; the atom remains an explicit
profile lower bound until charged, nulled, or realized.

**Implemented mechanism.** `thm:exact-finite-cylinder-source-profile-duality`
places every fixed atom on its exposed profile face.
`cor:part-I-continuum-profile-evaluation` sends that face through equality
compilation and realization, and `thm:no-terminal-zero-price-model` prevents
fixedness from becoming a terminal verdict.

#### 19. Preserve infinite composition by backward frontiers

**Part-I analogue:** many individually null operations cannot create
uncharged joint information.  **Construction:** use the implemented canonical
two-record source-current law, conditional increments, occurrence direct sum,
and cumulative joint algebra.  **Closed when:**
`N/4=sum Delta`, `N=sum widehat Delta`, and every nonzero limit has a nonzero
finite contextual increment.  This item is closed in the manuscript.

**Implemented mechanism.** `thm:exact-prospective-continuum-backward-factorization`
gives the nested conditional increments and the exact normalized identity.
`thm:cofinal-prospective-frontier-closure` retains the cumulative occurrence
direct sum across shells, while `thm:continuum-composition-no-creation` and
`cor:no-limit-created-target-alignment` force every nonzero limiting target
component to a finite contextual five-source increment.

#### 20. Replace universal truth evaluation by profile evaluation

**Part-I analogue:** accountability plus a task-specific profile bound proves
hardness.  **Construction:** derive an exact primal--dual formula for each
physical source profile.  Each PDE specialization must derive a profile
ceiling or an independently realized contacting orbit from the same algebra.
**Closed when:** no third verdict exists.  Uniform termination is not required,
because singular equations are valid presentations.

**Implemented mechanism.** `thm:monotone-cylinder-source-profile-completion`
computes the exact saturated profile as the infimum of finite-cylinder
profiles.  `cor:part-I-continuum-profile-evaluation` gives finite checked
exclusion below a target threshold or one compatible source-profile witness;
`thm:quantifier-faithful-continuum-accountability` identifies ordinary
contact only through the same-origin realization map.
`thm:unconditional-target-local-invariant-evaluator` applies the same
finite-prefix valuation, equality compilation, graph descent, cumulative
backward frontier, and realization test to each invariant packet; consequently
an active complementary value is an evaluated five-source record rather than
an unresolved status.  It is immediately enqueued by
`def:invariant-evaluation-protocol`; classification alone is never a closure.

### D. Physical financing

#### 21. Derive weighted-root and exterior ceilings

**Part-I analogue:** downstream normalization stays in the constructor ledger.
**Construction:** solve adjoint weights on finite horizons, retain both
endpoints, glue horizons before positive parts, and restrict exterior input to
the public boundary/forcing measure.  **Closed when:** every finite-financing
verdict contains derived bounds for root, production, and exterior terms;
unbounded weights enter scale cells.

**Implemented mechanism.** `prop:finite-prefix-root-exterior-accounting`
sums the adjoint identities on the finite stopped interval complex and retains
both exterior roots, unmatched interface weights, public production and
exterior input, and graph errors.  An unbounded pairing is stopped at its
first rational level crossing and evaluated with its constructor owner.

#### 22. Expand unbounded financing

**Part-I analogue:** an over-budget constructor exposes its responsible
resource coordinate.  **Construction:** factor the term through scale rate,
carrier, horizon, and exterior owner; apply the backward frontier and generate
its adjoint carrier.  **Closed when:** it telescopes, is charged, is null, or
enters a strictly refined scale/equality cell.

**Implemented mechanism.** The level-crossing construction in
`prop:finite-prefix-root-exterior-accounting` occurs before a limit or
average.  `thm:finite-prefix-source-profile-carrier-duality` then returns a
finite charge or finite target-aligned dual witnesses; a graph failure returns
the corresponding owned descendant.

#### 23. Prove source-profile/carrier duality

**Part-I analogue:** capability profiles are inverse resource frontiers.
**Construction:** for each exact source cell, equate the supremum of normalized
contextual progress under the physical ceiling with the infimum over generated
covariant carriers dominating that progress.  Include storage and exterior
terms.  **Closed when:** finite-cylinder strong duality, monotone passage,
equality evaluation, and realization typing are proved; separators are dual
profile witnesses only.

**Implemented mechanism.** `def:finite-prefix-physical-valuation` defines the
physical gauge of a source current against its closed finite-cylinder carrier
cone.  `thm:finite-prefix-source-profile-carrier-duality` proves exact
extended-real primal--dual equality, and
`thm:monotone-saturated-physical-valuation` takes the cofinal supremum.
Separators remain dual source records and never become orbits.

#### 24. Keep signed currents finite-prefix local

**Part-I analogue:** conditional increments are combined before undefined
cancellation.  **Construction:** define signed source currents on finite
occurrence algebras, retain total variation, and pass globally only with a
proved local-finiteness bound; globally decompose only the positive contact
measure.  **Closed when:** every global signed-measure claim has a variation
proof.

**Implemented mechanism.** `thm:variation-safe-finite-prefix-current-principle`
proves the exact dichotomy: bounded prefix variation gives the unique signed
measure extension; unbounded variation gives the source-owned first-level
crossing graph.  Only the positive contact measure is decomposed globally
without this test.

#### 25. Evaluate physical-singular target mass

**Part-I analogue:** residual-ancestry correlation re-enters a source profile.
**Construction:** project the component singular to the physical measure into
five owners and apply amplification, equality, carrier-polar, and realization
steps owner-by-owner.  **Closed when:** measure singularity is only a typed
zero-denominator cell, never a blow-up verdict by itself.

**Implemented mechanism.**
`cor:zero-physical-denominator-evaluated-cell` extracts a positive owner on
the detecting atom and computes its one-cylinder gauge.  The output is
target-null, finitely charged, or an infinite-gauge zero-production tangent.

#### 26. Compute amplification cellwise

**Part-I analogue:** profiles are bounded through exact source cells.
**Construction:** totalize target progress divided by production, storage,
and exterior input in every source/polarity cell; bound finite ratios by
carrier duality and route infinite ratios through equality and realization.
**Closed when:** finitely verified cell bounds cover the saturated profile.

**Implemented mechanism.** The finite physical gauge totalizes each source
and polarity cell, including zero denominators.  The monotone saturated
valuation assembles these local computations before the source profile is
taken.  Finite values are carrier charges; infinite values retain finite dual
witnesses and enter the equality evaluator.

### E. Target and continuation

#### 27. Compile the target from the theorem statement

**Part-I analogue:** the accepting set belongs to the task presentation.
**Construction:** declare the weakest acceptable continuation class, local
uniqueness, and gauge identifications; define contact as its failure on an
ordinary maximal path.  **Closed when:** target avoidance is equivalent to the
stated global-regularity conclusion.

**Implemented mechanism.** `def:singular-target` compiles the event target
from the declared continuation relation, gauge identifications, and the
no-ordinary-extension status.  It inserts no terminal analytic profile.

#### 28. Make event contact primary

**Part-I analogue:** first hit is primary and completed quotients are
accounting.  **Construction:** use the finite noncontinuation flag on the
same-origin path; compactified germs are shell-support coordinates requiring
realization.  **Closed when:** every actual noncontinuation triggers the flag
and no unrelated relaxed point inherits it.

**Implemented mechanism.** `prop:terminal-coverage` makes the same-origin
finite noncontinuation event primary, while
`cor:no-compactification-existence-promotion` prevents a relaxed germ from
acquiring contact without its ordinary preterminal path and continuation flag.

#### 29. Prove shell cofinality by separation

**Part-I analogue:** verifier observables separate target and nontarget.
**Construction:** generate rational ramps of continuation-defect coordinates
and prove their joint zero set equals the regular continuation locus.  **Closed
when:** every ordinary noncontinuation crosses cofinal normalized shells and
every regular continuation eventually avoids them.

**Implemented mechanism.** `prop:shell-cofinality-realization-fidelity` uses
the generated rational continuation-defect ramps.  Their joint zero set is
the ordinary continuation locus, giving both directions of the shell test.

#### 30. Evaluate nonordinary shell currents

**Part-I analogue:** a failed primitive remains in the expanded transcript.
**Construction:** totalize products, traces, pressure, charts, and Stieltjes
pairings; retain the first failed graph with target covector, owner, physical
denominator, and multiplicity; run the same backward/carrier evaluator.
**Closed when:** every graph current is charged, null, strictly refined, or
ordinarily realized.

**Implemented mechanism.**
`thm:nonordinary-shell-current-first-failure-evaluator` retains the least
failed graph with its covector, denominator, multiplicity, owner, and joint
frontier.  Backward projection and finite-prefix duality return target
nullity, finite charge, an infinite-gauge equality successor, or the least
nonordinary descendant.  Ordinary realization remains a separate gate.

### F. Navier--Stokes unit test

#### 31. Execute the general evaluator, not an NS-specific terminal rule

**Part-I analogue:** LPN instantiates the general profile theorem.
**Construction:** map viscosity, convection, pressure, gauges, cutoffs, scale,
exterior flux, and suitable-energy defect into general source cells and run
the common backward, valuation, equality, and realization compilers.  **Closed
when:** the example has no conditional conclusion or NS-only terminal branch.

**Implemented mechanism.** `prop:specialization-noninterference` and
`thm:ns-specialization-commutes` make the NS backend a homomorphic
substitution into the general backward, valuation, equality, carrier-polar,
horizon, circulation, joint-saturation, and realization operations.
`thm:ns-prospective-contact-compiler` now also specializes the exact
backward-frontier and occurrence-direct-sum identities.  No NS-only closing
rule is used.

#### 32. Remove contact-derived reachability equivalences

**Part-I analogue:** a successful transcript lower-bounds the success profile;
it does not prove reachability from unrelated input.  **Construction:** use
contact-derived decompositions only prospectively and determine reachability
through the ordinary initial-data realization map.  **Closed when:** no
post-contact quantity proves its own existence.

**Implemented mechanism.** Contact-derived records yield only the necessary
implication `eq:ns-internal-regularity-equivalence` and retain origin
`\mathsf{Hyp}`.  The ordinary range of
`def:ns-ordinary-orbit-realization-gate` is the sole map that can produce an
independent `\mathsf{Ind}` path; `thm:ns-realization-gate-alternative`
rejoins that path with its complete source record before a terminal value is
admitted.

#### 33. Preserve `Hyp` in critical tails

**Part-I analogue:** retrospective labels never become selectors.
**Construction:** propagate `Hyp` through amplification, pressure, scale,
tail, and corona records.  **Closed when:** singular existence requires a
separate `Ind` path with the same coordinates.

**Implemented mechanism.** Origin polarity is retained in the active
signature, every successor, the microscope, the marked critical tail, and
the cumulative backward frontier.  Equations
`eq:ns-backward-frontier-charge`--
`eq:ns-cumulative-backward-frontier-charge` preserve `\mathsf{Hyp}`, while
`thm:no-recycled-contact-realization` prevents normalization, limiting,
separation, or graph completion from changing it.

#### 34. Make failed normalized bounds amplitude cells

**Part-I analogue:** absence of a cheap quotient is retained structure.
**Construction:** totalize normalized `L2`, `L3`, pressure, and tail values;
join finite/unbounded/nonordinary cells with scale and unnormalized energy.
**Closed when:** the microscope assumes no uniform normalized bound and every
failure is a source-owned amplitude/scale cell.

**Implemented mechanism.** `thm:ns-canonical-target-orbit` totalizes the
normalized energy, velocity, pressure, product, tail, chart, and realization
coordinates.  Bounded coordinates derive the local compactness actually
used; the least unbounded or nonordinary coordinate becomes its typed
successor.  `cor:ns-surviving-amplitude-scale-cell` retains the complete
amplitude--scale--price--activity--ancestry tuple.  No normalized bound is a
premise of prospective contact accountability.

#### 35. Use the actual scale-dependent price

**Part-I analogue:** constructor cost uses its actual parameters.
**Construction:** compute coercive price from retained amplitude, scale,
activity, and carrier coordinates and sum its physical value on disjoint
occurrences.  **Closed when:** every divergent-price claim follows from this
schedule and the kinetic-energy ledger.

**Implemented mechanism.** `def:ns-scale-aware-expenditure` records the
exact relation `p_{r,R}=r(D_R+M_{r,R})`.
`lem:ns-computed-critical-price` computes the normalized price from the
retained amplitude, and `thm:ns-cumulative-current-rebasing` keeps the
resulting schedule term by term.  `lem:ns-scale-collapse-degeneracy` forbids
its replacement by a scale-independent lower bound.  Only the raw measure
`\mu_{\rm NS}` is summed against the kinetic-energy ceiling.

#### 36. Put the covariant microscope in the valuation

**Part-I analogue:** representation change cannot erase cost.  **Construction:**
treat scale as `Lift`, differentiate the pulled-back carrier, retain scale
current and adjoint weight, and glue scale interfaces before comparing
normalized and physical production.  **Closed when:** shrinkage with zero
physical price necessarily enters the equality compiler.

**Implemented mechanism.** `def:ns-covariant-microscope` and
`prop:ns-moving-microscope-equation` retain scale and center velocities as
`\Lift` currents.  `thm:ns-signed-covariant-carrier` differentiates the
pulled-back carrier, and `thm:ns-microscope-passivity` glues adjacent scale
cells before valuation.  `prop:ns-no-free-shrinkage` forces any target
progress missed by the fixed camera into the target-visible scale current;
zero physical price enters the generated equality compiler.

#### 37. Aggregate signed transport first

**Part-I analogue:** joint effects are evaluated before coordinatewise norms.
**Construction:** add convection, pressure, cutoff, translation, scale,
exterior, and defect currents with signs on compatible interfaces; compare
only the aggregate inward current with the carrier.  **Closed when:** no proof
sums absolute internal currents and every remainder re-enters carrier duality.

**Implemented mechanism.** `eq:ns-covariant-carrier-identity` retains all
transport, pressure, cutoff, translation, scale, exterior, storage,
viscosity, and suitable-defect terms with their signs.
`thm:ns-microscope-passivity` sums compatible cells before taking positive
parts.  `thm:ns-carrier-polar-recursion` then derives aggregate carrier
membership or generates a separating covector and all of its descendants as
the next five-source successor.

#### 38. Treat ordinary and nonordinary tangents uniformly

**Part-I analogue:** failure values remain in the same saturated grammar.
**Construction:** quotient ordinary tangents by Galilean/gradient kernels;
send nonordinary tangents to their first failed domain, pressure, scale, or
convergence graph.  **Closed when:** both pass through equality and realization
and neither is called singular solely from zero production.

**Implemented mechanism.**
`prop:ns-ordinary-amplification-tangent-nullity` closes finite-amplitude
zero-production tangents in the ordered algebra without assuming Dirac
realization.  Unbounded and nonordinary amplitude, product, pressure, scale,
trace, and realization values pass through total graphs in
`thm:ns-critical-tail-nullity` and
`prop:ns-complete-covariant-corona-execution`.  Both branches enter the same
carrier-polar, equality, and realization queue.

#### 39. Compile pressure and harmonic tails

**Part-I analogue:** boundary/oracle calls retain query and readout ancestry.
**Construction:** split local pressure, harmonic gauge, exterior tail, and
trace; generate adjoint shell pairings and interface cancellation; retain
truncation and exterior owners on failures.  **Closed when:** every visible
tail is charged, null, reduced, or realized.

**Implemented mechanism.** The public pressure equation is split into local
singular-integral, harmonic-gauge, and exterior-tail total graphs.
`prop:ns-defect-polarization` propagates nonlinear defects into the pressure
constraint, while `thm:ns-target-local-record-scale-reduction` retains the
single glued tail current `B_\infty`.  A failed exhaustion or visible tail
is source-owned, reprojected, and processed by
`thm:ns-carrier-polar-recursion`; a canceled tail is an interface
coboundary.

#### 40. Compile scale equality into relative equilibria

**Part-I analogue:** equality exposes the exact attaining structure.
**Construction:** saturate equality in the signed covariant carrier, derive
the relative scale/translation equation, quotient gauges, and apply generated
coercivity; keep unbounded amplitude joined to scale and price.  **Closed
when:** every equality cell is null, charged, or independently realized.  The
finite-amplitude cell is closed; the unbounded amplitude--scale cell remains
the stress test.

**Implemented mechanism.**
`thm:ns-target-local-record-scale-reduction` derives the scale-relative
balance, `cor:ns-ordinary-cell-resaturation` inserts every nonzero balance
or tail pairing into target-cyclic circulation, and
`prop:ns-ordinary-amplification-tangent-nullity` closes the finite-amplitude
zero-production cell.  The remaining generated cell is exactly
`eq:ns-surviving-amplitude-scale-cell`, retaining the joint record
`eq:ns-surviving-amplitude-scale-joint-record`.
`thm:ns-amplitude-scale-profile-evaluation` bounds that entire joint record
on every finite cylinder and passes monotonically to its saturated outer
comparison profile.  A finite dual row excludes the required shell progress.
The complementary compatible functional is comparison-only: it neither
establishes source presence nor creates a branch.  Presence requires its
least detecting finite same-origin precontact occurrence, and contact
requires the independently reachable ordinary realization.  Fixedness,
amplitude divergence, and scale collapse are therefore never terminal values;
the reachable amplitude--scale contact cell has not been shown empty.

#### 41. Finish the test through the general terminal machinery

**Part-I analogue:** the application substitutes cellwise bounds into general
accountability.  **Construction:** feed all NS separators, equality cells, and
tails into the general profile evaluator.  **Closed when:** the example ends
in checked avoidance or an `Ind` zero-defect contacting orbit, with no
unevaluated NS successor.

**Implemented mechanism.**
`thm:ns-specialization-commutes` feeds every NS owner, separator, tail,
contextual increment, and realization value into the general evaluator.
`thm:ns-prospective-contact-compiler` supplies the finite backward frontier
and unnormalized cumulative occurrence accounting, and
`thm:ns-realization-gate-alternative` enforces the two sound terminal types.
`thm:ns-amplitude-scale-profile-evaluation` supplies the saturated outer
comparison value of the last joint cell, and
`cor:ns-profile-specialization-complete` proves that every Navier--Stokes
comparison cell is evaluated by the general profile/realization machinery.
A positive functional, nonempty comparison core, separator, compatible
inverse limit, or marked tail creates no structural branch.  Every active
positive branch is indexed instead by the least detecting finite precontact
occurrence on one public-presentation, same-origin orbit.  Singular terminals
are restricted to independently reachable ordinary contact cells.  The
amplitude--scale comparison value is therefore neither a named unresolved
terminal nor evidence of singular existence; its reachable contact cell has
not been proved empty, so the example does not establish regularity.

### G. Hamiltonian and spectral reconstruction

#### 42. Construct the operator inside the grammar

**Part-I analogue:** the transition operator is derived from the presented
computation.  **Construction:** generate Hilbert space, closed form, domain,
generator, and boundary conditions from the PDE/regulator presentation;
totalize closability, density, and domain failures.  **Closed when:** spectral
machinery is used only after this graph has an ordinary value.

**Implemented repair:** `def:operator-construction-graph` enumerates the
rational construction coordinates and their defects;
`thm:first-failure-operator-construction` proves the exact least-failure versus
ordinary-operator dichotomy.  The ordinary branch constructs the quotient
Hilbert space, closed form, semigroup generator, domain, and boundary graph.
The failed branch returns its constructor-owned witness to the saturated source
profile.  No operator datum is supplied as an antecedent to a spectral claim.

#### 43. Add a same-origin spectral-to-reachability map

**Part-I analogue:** a spectral feature counts through the pre-hit selector
that uses it.  **Construction:** construct an intertwiner preserving time,
shells, source currents, and carrier; pull spectral covectors back through its
adjoint.  **Closed when:** poles, pseudospectra, and range defects affect PDE
reachability only through nonzero same-origin pulled-back pairing.

**Implemented repair:** `def:same-origin-spectral-reachability-graph` joins the
dynamical, shell, source, and carrier intertwining rows on one stopped history.
`thm:same-origin-spectral-pullback` factors every usable spectral covector
through the complete joint backward frontier.  Nonzero pullback is therefore a
finite contextual source increment; a nonzero intertwining defect is routed at
its least joint rational coordinate and blocks the spectral transfer.

#### 44. Treat regulator reconstruction as realization

**Part-I analogue:** consistent finite instances do not automatically define
one uniform infinite execution.  **Construction:** join regulator levels and
generate projective consistency, reflection positivity, nontriviality,
cyclic-vacuum, strong-continuity, and Hamiltonian tests.  **Closed when:** a
zero-defect projective branch constructs the continuum Hilbert space and
Hamiltonian before the mass-gap target is evaluated.

**Implemented repair:** `def:finite-regulator-realization-hierarchy` forms
nested compact truncated moment sets with generated variance coordinates and
all consistency, reflection, semigroup, and continuity coordinates.
`thm:regulator-proof-failure-realization` proves the trichotomy: finite ordered
incompatibility proof, least typed joined defect, or a single inverse-limit
functional.  In the last branch every finite reflection square and consistency
identity survives, variance decides the trivial quotient or supplies a
nonvacuum class, the time moduli extend to the completion, and
`thm:continuum-reconstruction-output` constructs the Hilbert space, cyclic
vacuum, and Hamiltonian.  Spectral-gap evaluation begins only after this
ordinary realization.

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
