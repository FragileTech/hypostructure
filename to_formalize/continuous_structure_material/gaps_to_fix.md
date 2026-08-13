  - The current framework does not yet prove 3D Navier–Stokes regularity from textbook data alone. It gives a rigorous necessary-mechanism reduction, but the decisive elimination step is
    presently semantic rather than constructive.

  - It cannot presently prove the Yang–Mills mass gap as a PDE-regularity application. The Clay problem is a quantum-field existence and spectral-gap problem, and the manuscript begins after
    several objects that must instead be constructed.

  The five-channel classification is substantially sound. The remaining problem is not classification; it is evaluation.

  ## Target-aligned reduction is the organizing principle

  Every repair below must preserve the principal reduction already supplied by
  the structural framework.  The continuum evaluator does not analyze the
  entire weak current space.  It first constructs the prospective shell
  covectors descending toward the generated target \(\Sigma\):

  \[
  \Gamma_\Sigma
  =\overline{\operatorname{cone}}
  \{D\Phi:\Phi\text{ is a generated pre-contact cylinder shell}\}.
  \]

  For the saturated current space \(\mathscr J^{\rm sat}\), define

  \[
  \mathcal N_\Sigma
  :=\bigcap_{\gamma\in\Gamma_\Sigma}\ker\gamma,
  \qquad
  \mathscr J_\Sigma
  :=\mathscr J^{\rm sat}/\mathcal N_\Sigma.
  \]

  A source occurrence is target-aligned when its positive pairing with some
  \(\gamma\in\Gamma_\Sigma\) is nonzero.  The formation support of an event
  \(R\) is

  \[
  \operatorname{Align}_\Sigma(R)
  :=\left\{c\in\{\Geom,\Caus,\Abs,\Lift,\Bdry\}:
  \sup_{\gamma\in\Gamma_\Sigma}
  \langle\gamma,J^c(R)\rangle_+>0\right\}.
  \]

  The derived shell-current identity must prove

  \[
  \text{contact with }\Sigma
  \Longrightarrow
  \operatorname{Align}_\Sigma(R_j)\ne\varnothing
  \quad\text{on every shell-crossing event }R_j.
  \]

  Graph-complete compactification and source-preserving saturation first fix
  the ancestry of every limit.  All subsequent carrier comparison, scale
  cohomology, moment relaxation, and pruning operations are performed
  sourcewise on \(\mathscr J_\Sigma\).  Currents in \(\mathcal N_\Sigma\) are
  removed before those calculations.  The post-saturation residual
  \(J_{\rm res}\) is precisely such a target-null coordinate and never carries
  a target-bearing alternative.  These currents are the continuum counterpart of computation
  that expends resources without increasing prospective target success.
  Consequently, the evaluator asks the narrow question

  \[
  \boxed{
  \text{which inherited structure supplies positive pre-contact progress
  toward the singular target?}}
  \]

  A regularity proof needs to eliminate only the target-aligned saturation
  cells.  This quotient is the structural source of the reduction in
  difficulty; the ordered proof machinery below evaluates that reduced
  problem rather than replacing it.

  Compactness, moment, and sum-of-squares constructions serve as finite
  evaluator backends after the structural algebra has performed the reductions
  specific to this framework:

  1. prospective target-shell accountability identifies structure available
     before contact;
  2. five-source compilation assigns complete ancestry before any limit or
     estimate is taken;
  3. source-preserving saturation keeps oscillations, concentrations, tails,
     and graph failures inside inherited cells;
  4. the target-null quotient removes every current that cannot advance a
     singular shell;
  5. signed carrier gluing cancels internal transport, gauge, chart, and
     interface currents before physical expenditure is measured;
  6. zero-price first failures generate successor dynamics instead of analytic
     side conditions; and
  7. stationary saturation converts an infinite cascade into a finite family
     of equality, cohomology, and relative-dynamics cells.

  This sequence is the continuum analogue of Part I's reduction of all legal
  computations to target-aligned represented source occurrences.  Its purpose
  is to replace global norm control by evaluation of the much smaller quotient
  of structure that can actually form the target.

  ### Target-alignment implementation checklist

  - [ ] Generate \(\Gamma_\Sigma\) prospectively from finite-cylinder shells
    and their strictly pre-contact differentials.
  - [ ] Normalize the shell covectors so that unit shell progress has a fixed
    scale-independent readout.
  - [ ] Prove that \(\mathcal N_\Sigma\) is closed under sourcewise limits,
    successor maps, gauge descent, and signed carrier gluing.
  - [ ] Form the target-active quotient only after the five-channel ancestry
    of every current and defect has been fixed.
  - [ ] Define positive alignment separately in every inherited source cell.
  - [ ] Prove shell accountability before invoking physical expenditure:
    contact forces nonempty aligned support without a price hypothesis.
  - [ ] Propagate the target-null quotient through every later graph,
    cohomology, moment, and reconstruction operation.
  - [ ] Run physical-price and saturation calculations only on persistent
    aligned supports.
  - [ ] Require every surviving positive functional to carry a normalized
    target pairing and the pre-contact shell witness that generated it.
  - [ ] Conclude regularity when all aligned cells vanish, regardless of the
    size or complexity of target-null dynamics.
  - [ ] Treat moment, SOS, interval, spectral, and compactness routines only as
    interchangeable backends for an already source-reduced cell.
  - [ ] Reject any backend condition that is stated on the full PDE state space
    when the same condition can be descended to \(\mathscr J_\Sigma\).

  ### Structural fast-track invariant

  Every PDE specialization should reduce a putative contact orbit through the
  same target-aligned chain.  For disjoint normalized shell events \(R_j\),

  \[
  1
  =\operatorname{Prog}_\Sigma(R_j)
  =\sum_{c\in\Channels}Q_{c,j},
  \qquad
  A_j:=\{c:Q_{c,j}^{+}>0\}\ne\varnothing.
  \]

  Finite source exhaustion selects a persistent nonempty support \(A\).  Signed
  carrier gluing then assigns the single physical prices
  \(p_j=\mu_{\rm phys}(R_j)\).  Exactly two cases remain:

  \[
  \sum_jp_j=\infty
  \quad\Longrightarrow\quad
  \text{contact contradicts the finite physical budget},
  \]

  or

  \[
  \sum_jp_j<\infty
  \quad\Longrightarrow\quad
  p_{j_k}\to0
  \quad\Longrightarrow\quad
  \nu_A\text{ is a target-aligned stationary saturation law}.
  \]

  Source-preserving limit closure keeps \(\nu_A\) in the same ancestry cell.
  The fixed nonreversible term remains \(\Caus\); it is never replaced by a
  freely selected transition.  Equality reduction is then performed on
  \(\Pi_\Sigma\nu_A\), not on the full orbit.  Hence the final task is the
  finite family of target-aligned kernel problems

  \[
  \Pi_\Sigma
  \bigl(ker Q_{\rm phys}\cap
  \ker I_{\rm PDE}\cap
  \mathfrak F_A\bigr)=0,
  \qquad \varnothing\ne A\subseteq\Channels.
  \]

  This is the continuum fast track.  Classical estimates are used only when
  they compile one of these reduced kernel identities.  A failed estimate is
  itself a typed graph value and is passed through the same target quotient;
  it cannot enlarge the source alphabet or become a target-bearing residual.

  ## Continuum extension principle

  The repair extends Part I; it does not replace its algebra.  The five source
  families, prospective target accountability, saturation, source ancestry,
  first-contact reasoning, and target-null residual semantics remain
  unchanged.  Continuum analysis supplies realizations of the same objects:

  | Part-I object | Continuum realization |
  |---|---|
  | finite state or task record | state, germ, jet law, or normalized profile |
  | finite generator occurrence | distributional current occurrence on a time window |
  | saturated constructor closure | sourcewise closure under dynamically generated weak limits |
  | computational resource ceiling | the equation's single finite physical-expenditure measure |
  | prospective selector advantage | positive pre-contact shell-current pairing |
  | first hit of the target | first contact or terminal noncontinuation germ |
  | target-aligned source occurrence | target-aligned Geom/Caus/Abs/Lift/Bdry current occurrence |
  | exhaustive finite search | exhaustive rational-cylinder ordered consequence search |
  | post-saturation residual | target-null current in \(\mathcal N_\Sigma\) |

  The continuum completion must therefore be a source- and target-preserving
  functor \(\mathfrak C\) on the structural algebra.  For every discrete or
  cylinder-level record \(R\), it must satisfy

  \[
  \operatorname{Anc}\bigl(\mathfrak C(R)\bigr)
  =\operatorname{cl}_{\rm src}\operatorname{Anc}(R),
  \qquad
  \Pi_\Sigma\mathfrak C(R)
  =\mathfrak C\bigl(\Pi_\Sigma R\bigr),
  \]

  and it must preserve composition, signed sums, restriction, first-contact
  stopping, and physical-ledger addition.  Weakness, concentration,
  oscillation, escape, loss of trace, and failure of a chain rule change the
  realization of a record but not the principles governing it.

  ### Extension-preservation checklist

  - [ ] State the continuum extension functor on atomic state, current,
    target, source, and boundary records.
  - [ ] Prove that it preserves the five source tags and appends only the
    already available \(\Abs\), \(\Lift\), and \(\Bdry\) ancestry required by
    quotient, chart, and terminal operations.
  - [ ] Prove compatibility with finite sums, signed gluing, composition,
    restriction, stopping, and successor formation.
  - [ ] Prove that sourcewise limit closure creates no sixth source.
  - [ ] Prove that the target-null kernel commutes with continuum completion.
  - [ ] Derive continuum shell accountability as the limit of finite-cylinder
    prospective accountability.
  - [ ] Derive physical countable additivity as the continuum realization of
    the single additive resource ledger, without introducing a representation
    budget.
  - [ ] Prove that restricting the continuum construction to finite state
    spaces recovers the Part-I definitions and accountability theorem.
  - [ ] Audit every new analytic constructor against this preservation theorem
    before it enters the closed algebra.
  - [ ] Reject any continuum theorem whose statement requires a new primitive
    source, a target-visible residual, or a target-relative input not generated
    from the equation and target shells.

  ## What remains assumed or unevaluated

  ### 1. The public inputs

  These are genuine inputs, though reasonable ones:

  - a standard local solution theorem;
  - a declared regularity and continuation class;
  - the native formal energy/action/entropy identity;
  - the equation’s standard symmetries, gauges, and weak formulation.

  They are stated explicitly in the to_formalize/continuous_hamiltonian_structural_complexity.tex:616. For Navier–Stokes these are textbook facts. They are not enough to define quantum Yang–
  Mills.

  The finite-budget theorem additionally works on branches where

  [
  K_u\ge K_->-\infty,
  \qquad
  W_u^+([0,T_*))<\infty.
  ]

  That restriction is explicit in the to_formalize/continuous_hamiltonian_structural_complexity.tex:850. It is satisfied for unforced Navier–Stokes by the energy inequality, but not automatically
  for every PDE.

  #### Recommended fix: generate the solution and carrier graphs from an approximation tower

  The public presentation should contain the equation, datum, boundary
  conditions, weak test syntax, native transformations, and native formal
  balance law.  A local solution theorem may identify an already understood
  ordinary branch, but the global evaluator must not depend on that theorem.
  Instead, the equation syntax should generate a countable approximation
  tower consisting of all rational Galerkin truncations, mollifications,
  implicit time steps, and domain exhaustions compatible with the displayed
  equation.  The tower is exhaustive rather than scheme-selective: every
  approximation assembled from the public operations occurs in it.

  Each approximation carries its exact finite-dimensional evolution relation
  and its exact tested carrier identity.  Passing through the graph-complete
  limit construction then produces either an ordinary solution, a typed
  equation defect, or a typed carrier defect.  Local existence is consequently
  a value of the generated tower rather than a premise used to suppress an
  empty solution graph.

  The physical budget remains a single object.  It is the positive production
  measure in the native signed carrier law.  Auxiliary multipliers may split,
  localize, or compare this measure, but may not create another budget.  If the
  carrier has no lower bound or receives infinite exterior work, the generated
  branch records that physical mechanism.  The framework then makes no
  finite-expenditure regularity conclusion on that branch.

  #### Implementation checklist

  - [ ] Define a countable grammar of rational spatial truncations, temporal
    discretizations, mollifiers, boundary exhaustions, and gauge fixings using
    only operations in the public equation signature.
  - [ ] Include every grammar word rather than choosing one favorable
    approximation scheme.
  - [ ] Solve each finite approximation by its finite-dimensional total
    evolution graph; retain finite-time escape and nonuniqueness as graph
    values.
  - [ ] Test every approximate equation against the enumerated rational test
    core and generate the approximate signed carrier identity mechanically.
  - [ ] Construct one projective approximation graph whose compatible paths
    include all approximation schemes and all refinement subsequences.
  - [ ] Attach prospective target-shell pairings to approximate events while
    preserving their strictly pre-contact origin indices.
  - [ ] Define ordinary continuum solutions as zero-defect projective-limit
    values and define every failed passage as the first typed graph defect.
  - [ ] Prove that every classical or standard weak solution embeds in the
    zero-defect locus of the approximation graph.
  - [ ] Prove that a zero-defect limit satisfies the public weak equation and
    native carrier law.
  - [ ] Derive the single measure \(\mu_{\rm phys}\) from the positive part of
    that carrier law and prohibit later target-dependent additions.
  - [ ] Restate all regularity conclusions on the generated finite-carrier
    locus; route lower-bound and exterior-work failures as physical branches,
    not as hypotheses or regularity conclusions.

  ### 2. The evaluation compactification is compact but not analytically faithful by itself

  The manuscript embeds bounded evaluation coordinates into ([-1,1]^{\mathbb N}) and takes the closure. Compactness then follows automatically.

  What has not been proved is that this compactification:

  - distinguishes every continuation-critical phenomenon;
  - passes every nonlinear PDE term in a physically meaningful way;
  - contains no target-active boundary records that are artifacts of the weak coordinates;
  - turns every surviving graph-boundary record into an actual generalized orbit.

  Totalizing failed products and chain rules prevents loss of ancestry, but it does not make their limits physical.

  Thus the framework proves

  [
  \text{actual contact}\Longrightarrow\text{compact successor mechanism},
  ]

  but not

  [
  \text{compact successor mechanism}\Longrightarrow\text{actual contact}.
  ]

  That asymmetry is explicitly visible where surviving cells are only physical “on an ordinary contact origin” to_formalize/continuous_hamiltonian_structural_complexity.tex:6640.

  #### Recommended fix: replace the product closure by a graph-complete jet-law compactification

  Compactness should be taken in the state space of the full ordered cylinder
  algebra generated by the PDE, not in a product of readouts that forgets how
  nonlinear terms were formed.  For every typed operation \(F\) occurring in
  the equation or carrier law, add coordinates for its inputs, output, graph
  residual, oscillation law, concentration mass, and exterior tail.  A limit
  point then retains enough information to evaluate every term of the weak
  equation without assigning an artificial value to a nonlinear product.

  The resulting points are normalized positive functionals on this cylinder
  algebra.  Positivity, marginal consistency, locality, source ancestry, and
  the weak equation are closed relations.  Ordinary functions embed as Dirac
  jet laws.  A nonordinary point has a least failed typed relation and hence a
  concrete oscillation, concentration, tail, gauge, or interface coordinate.

  Two conclusions must be distinguished.  Target exclusion may be proved on
  the larger graph-complete state space; this is sound because it excludes a
  superset of the actual orbit limits.  A claim that a surviving state produces
  singular contact requires a coherent approximation path.  Such a path must
  be extracted from the approximation tower, rather than supplied as a
  realization certificate.

  #### Implementation checklist

  - [ ] Enumerate every nonlinear product, constitutive map, trace, inverse
    constraint, chart map, and covariance map appearing in the equation.
  - [ ] For each operation introduce a closed graph bundle containing ordinary
    values and separate oscillation, concentration, tail, and domain-defect
    coordinates.
  - [ ] Build the rational cylinder algebra from weak jet pairings and all
    graph-bundle coordinates.
  - [ ] Impose positivity, normalization, marginal consistency, locality, and
    sourcewise ancestry as algebraic order relations.
  - [ ] Define the compact state space as the normalized positive-functional
    spectrum of this ordered algebra.
  - [ ] Prove compactness from the order unit and prove that its cylinder
    coordinates separate states.
  - [ ] Prove the Dirac embedding theorem for ordinary states and ordinary
    orbit segments.
  - [ ] Prove a zero-defect realization theorem: a projectively compatible
    point with zero operation defects solves the public weak equation.
  - [ ] Prove a first-failure theorem assigning every nonordinary point to the
    least failed typed operation and its inherited five-channel ancestry.
  - [ ] Add continuation-modulus and terminal-germ coordinates so that the
    target is separated by the same cylinder algebra used for dynamics.
  - [ ] Prove that graph completion commutes with the target-null quotient:
    target-visible limits retain inherited source ancestry, while only zero
    shell pairings enter \(\mathcal N_\Sigma\).
  - [ ] Formulate regularity as exclusion of the target in the relaxed state
    space; this direction requires no converse realization theorem.
  - [ ] Permit a singularity conclusion only when the projective approximation
    graph itself supplies a coherent realizing path.

  ### 3. The total shell identity classifies failure but does not control it

  For a failed chain rule, the manuscript defines

  [
  \eta_{r,u}(I)

  \Phi_r(u_b)-\Phi_r(u_a)-\sum_c Q_{c,r}(I).
  ]

  This is correct as exhaustive accounting: contact cannot disappear merely because differentiability fails. But it is tautological at the quantitative level. A positive (\eta) has inherited
  ancestry, yet nothing currently forces it to:

  - spend positive physical budget;
  - descend to a simpler defect;
  - become target-null;
  - or generate an actual singular solution.

  See the to_formalize/continuous_hamiltonian_structural_complexity.tex:1850. “Lack of a property is structure” is implemented as classification, but not yet as a terminating evaluator.

  #### Recommended fix: replace the catch-all shell defect by a derived Radon current

  The target shell algebra should be generated by smooth finite-cylinder
  observables whose evolution is defined by the weak equation.  Along every
  approximation, the shell derivative is an exact signed measure.  Uniform
  bounded variation yields a Radon current in the projective limit.  Its
  Lebesgue, jump, Cantor, oscillation, concentration, and exterior parts are
  retained separately.  The endpoint shell increment is then the mass of this
  derived current, rather than the definition of an undifferentiated remainder
  \(\eta\).

  The cylinder shell family must also be proved cofinal for the continuation
  target.  Contact then forces unit progress in the limit of finite-cylinder
  shells.  Each unit is carried either by an ordinary five-channel current or
  by one of the typed singular parts above.  Every part enters the same carrier
  comparison and ordered consequence calculus.  A part that has no positive
  carrier comparison becomes a zero-price successor state with explicit
  coordinates; it does not remain an unconstrained shell defect.

  #### Implementation checklist

  - [ ] Construct finite-cylinder Urysohn shells from the continuation
    coordinates and rational smooth ramps.
  - [ ] Prove that these shells are cofinal: every target contact crosses a
    sequence whose endpoint progress tends to one.
  - [ ] Derive the time-distributional derivative of each cylinder shell from
    the approximate weak equation.
  - [ ] Decompose that derivative into the five ordinary channel currents
    before taking limits.
  - [ ] Pass to a finite signed Radon current and retain its absolutely
    continuous, jump, Cantor, oscillation, concentration, and exterior parts.
  - [ ] Assign every singular part to the first failed graph operation and
    inherit its source word.
  - [ ] Prove the exact Stieltjes identity equating endpoint progress with the
    total mass of the derived current.
  - [ ] Derive \(1\le\sum_c Q^+_{c,r}\) on every normalized contact shell and
    retain only the source cells with positive summands.
  - [ ] Remove the definition of \(\eta\) as an arbitrary endpoint difference.
  - [ ] Generate a joint carrier relation for each singular current part.
  - [ ] Send carrier-dominated parts to physical-price accounting and send
    zero-price parts to the ordered successor calculus.
  - [ ] Prove the no-spontaneous-contact theorem using the derived current:
    vanishing of every target-active current measure implies constancy of every
    target shell along the orbit.

  ### 4. The generated consequence algebra is not proved complete

  The consequence algebra enumerates integration by parts, localization, adjoints, completion of squares, graph closure, and related operations. But there is no theorem that these rules derive
  every structural identity needed to eliminate a target-active zero-price mechanism.

  The passivity theorem itself says that equality forces a production term to vanish only when the algebra already contains a domination identity

  [
  p=q+r,\qquad q,r\ge0.
  ]

  That is exactly the remaining pressure point to_formalize/continuous_hamiltonian_structural_complexity.tex:3217. The manuscript does not ask the user to supply (p=q+r), but neither does it give
  a general procedure that necessarily derives or refutes it.

  #### Recommended fix: use an Archimedean ordered consequence calculus

  The continuous counterpart of exhaustive finite saturation is an ordered
  algebra with a primal--dual completeness theorem.  Let \(\mathcal A_{\mathbb
  Q}\) be the rational cylinder algebra of the graph-complete state space.  Let
  \(I_{\rm PDE}\) be the ideal generated by the weak equation, covariance,
  consistency, and stationary-successor identities.  Let \(Q_{\rm phys}\) be
  the quadratic module generated by squares, the nonnegative production
  atoms, graph-defect masses, and bounded-coordinate order relations.  Bounded
  coordinates make this order Archimedean.

  Before this algebraic evaluator is formed, every current generator is
  descended to \(\mathscr J_\Sigma\) and split by its nonempty aligned source
  support.  The target module \(Q_{\Sigma,\eta}\) records a positive
  prospective pairing in one such cell.  Consequently, the ordered search
  evaluates only structure capable of contributing to contact; it does not
  seek global estimates for target-null dynamics.

  For a rational target floor \(\eta>0\), the calculus must prove the exact
  alternative

  \[
  -1\in I_{\rm PDE}+Q_{\rm phys}+Q_{\Sigma,\eta}
  \quad\text{or}\quad
  \exists L:\mathcal A_{\mathbb Q}\to\mathbb R
  \text{ positive, normalized, stationary, and target-active}.
  \]

  The first outcome is a finite derivation that the target-active zero-price
  set is empty.  The second is a positive functional; Riesz/GNS reconstruction
  produces the stationary successor law already required by the continuum
  algebra.  Compactness of the state space gives completeness: semantic
  emptiness has a finite algebraic contradiction, while failure of every
  finite contradiction has a consistent positive-functional model.

  Nonpolynomial operations should be handled by graph variables and rational
  upper/lower enclosure relations.  The proof search then uses exact rational
  arithmetic and never asks for a PDE-specific inequality.  Familiar energy,
  commutator, Pohozaev, Noether, and entropy arguments become derivable words
  in this calculus.

  #### Implementation checklist

  - [ ] Define the typed rational cylinder algebra
    \(\mathcal A_{\mathbb Q}\) and its involution, localization, and successor
    pullback operations.
  - [ ] Translate every weak equation and graph-consistency relation into
    generators of an ideal \(I_{\rm PDE}\).
  - [ ] Translate squares, carrier productions, defect masses, and coordinate
    bounds into generators of a quadratic module \(Q_{\rm phys}\).
  - [ ] Add rational graph enclosures for exponential, inverse, determinant,
    and other nonpolynomial operations used by the equation.
  - [ ] Prove the Archimedean order-unit property from the bounded graph
    coordinates.
  - [ ] Encode zero physical price, successor consistency, stationarity, and a
    rational target floor as additional algebraic relations.
  - [ ] Construct those relations separately for every persistent aligned
    source support and delete target-null generators before degree truncation.
  - [ ] Prove soundness: every finite ordered derivation is valid on every
    generated orbit and graph-complete limit.
  - [ ] Prove compact completeness: if the constrained state space is empty,
    \(-1\) has a finite derivation from finitely many generators.
  - [ ] Prove rationalization of strict contradictions: every real-coefficient
    Archimedean separation of \(-1\) has a rational proof after a controlled
    perturbation, so the proof enumerator can find it.
  - [ ] Prove the dual reconstruction theorem: a consistent positive
    functional gives a probability law on the compact path space and satisfies
    all successor identities.
  - [ ] Add real-radical saturation rules so that \(p=0\) automatically forces
    every generated \(q\) with \(p=q+r\), \(q,r\ge0\), to vanish.
  - [ ] Enumerate multiplier, polarization, commutator, scale, Noether, and
    Pohozaev words from the public syntax rather than registering their desired
    conclusions.
  - [ ] State a relative-completeness theorem: every strict target separation
    true in the graph-complete semantics is eventually found by the proof
    enumerator.

  ### 5. “Canonical finite pruning” is existential, not currently constructive

  This is the largest hidden issue.

  A pruning node must establish facts such as

  [
  p\ge q \quad\text{on }\overline B_\ell
  ]

  and

  [
  \mathcal R_\eta(\overline B_\ell\cap Z_0)
  \subseteq\bigcup_i B_{\ell_i}.
  ]

  These are universal analytic assertions over compact sets; see the to_formalize/continuous_hamiltonian_structural_complexity.tex:3664.

  Compactness proves that a finite transcript exists if (Z_N=\varnothing). Choosing the least code among valid transcripts does not supply an algorithm for recognizing validity or proving
  (Z_N=\varnothing). It is a canonical semantic selection, not a derivation from the PDE syntax.

  Therefore the claim that “no externally supplied emptiness proof” is required to_formalize/continuous_hamiltonian_structural_complexity.tex:3692 is too strong. No user-supplied proof is
  requested, but the manuscript itself has not performed that proof either.

  The final PDE theorem consequently remains the dichotomy

  [
  Z_N^\Sigma=\varnothing\text{ for some }N
  \quad\text{or}\quad
  Z_n^\Sigma\ne\varnothing\text{ for every }n,
  ]

  rather than a procedure determining which branch holds; see the to_formalize/continuous_hamiltonian_structural_complexity.tex:6796.

  #### Recommended fix: replace semantic pruning by a proof-producing moment hierarchy

  A pruning node should contain a finite ordered-algebra derivation, not a
  universal inclusion asserted over a compact set.  At truncation level
  \((n,d,N)\), retain the first \(n\) cylinder coordinates, products of degree
  at most \(d\), and successor paths of length at most \(N\).  The primal
  problem is feasibility of the corresponding positive moment functional.
  The dual problem is a rational ordered derivation that the cylinder is
  impossible or has positive physical price.

  The hierarchy is formed on the target-active quotient.  Each primal table
  contains the normalized shell pairing and its source-resolved positive
  contributions.  Each dual derivation may close a cell either by positive
  physical price or by exact target-nullity.  It need not control the full PDE
  state space.

  This gives two checkable outputs.  Dual infeasibility certificates close
  cells by exact arithmetic.  A compatible sequence of primal moment tables
  defines, by projective compactness, a positive functional and hence an
  infinite successor law.  The hierarchy therefore constructs both sides of
  the alternative.  “Least-coded” may select the first derivation found by the
  enumerator, but it may no longer select among semantically valid forests
  whose validity has not been proved.

  #### Implementation checklist

  - [ ] Replace conditions (T1)--(T3) by formal sequents in the ordered
    consequence calculus.
  - [ ] Define finite truncation indices \((n,d,N)\) for coordinates, algebraic
    degree, and successor depth.
  - [ ] Construct the primal moment matrix, localizing matrices, consistency
    constraints, price-zero constraints, and target-floor constraints at each
    truncation.
  - [ ] Block-diagonalize the hierarchy by persistent target-aligned source
    support and remove the common target kernel before forming moment matrices.
  - [ ] Construct the dual cone of rational sums of squares, carrier atoms,
    graph relations, and successor telescoping identities.
  - [ ] Require every pruning edge and every positive-price assertion to carry
    an explicit dual identity checkable by exact rational arithmetic and
    certified interval enclosures.
  - [ ] Allow a dual node to close by an exact target-null identity even when
    the underlying current or recurrent orbit is nonzero.
  - [ ] Dovetail the finite searches over \((n,d,N)\); do not invoke a semantic
    membership or set-inclusion oracle.
  - [ ] Prove weak and strong dual soundness for every finite truncation.
  - [ ] Prove hierarchy completeness from the Archimedean compactness theorem:
    an empty target-active fixed point is detected at a finite truncation.
  - [ ] Prove projective reconstruction: compatible feasible moment tables
    yield a stationary zero-price successor law with the recorded target
    pairing and source ancestry.
  - [ ] Attach the original approximation indices to every moment coordinate
    so that an actual contact branch remains diagonally traceable.
  - [ ] Report certified lower and upper bounds at every finite stage, making
    the evaluator quantitatively useful before termination.
  - [ ] Delete the claim that topological compactness alone constructs a
    pruning proof; compactness supplies completeness only after the formal
    proof calculus has been defined.

  ## Stress test: 3D Navier–Stokes

  For unforced Navier–Stokes,

  [
  \partial_tu+(u\cdot\nabla)u+\nabla p
  =\nu\Delta u,
  \qquad \nabla\cdot u=0,
  ]

  the native physical budget is valid:

  [
  \frac12|u(t)|_2^2
  +
  \nu\int_0^t|\nabla u(s)|_2^2,ds
  \le
  \frac12|u_0|_2^2.
  ]

  The framework can derive:

  1. A finite-time failure of strong continuation crosses infinitely many target shells.
  2. Every crossing contains target-aligned Geom/Caus/Abs/Lift/Bdry ancestry.
  3. Countable additivity supplies a subsequence of windows with physical price tending to zero.
  4. Normalization and compact activity lifting produce a stationary zero-price successor law.

  That part is meaningful.

  The decisive obstruction is scaling. Under

  [
  V_j(y,s)

  r_j u(x_j+r_jy,t_j+r_j^2s),
  ]

  viscous expenditure transforms as

  [
  \int_{Q_{r_j}}|\nabla u|^2,dx,dt

  r_j\int_{Q_1}|\nabla V_j|^2,dy,ds.
  ]

  Even if every normalized window has unit-order dissipation, the physical prices can behave like (r_j), and a geometric sequence satisfies (\sum_jr_j<\infty). The manuscript correctly
  acknowledges this positive-exponent problem to_formalize/continuous_hamiltonian_structural_complexity.tex:6002.

  So finite kinetic energy alone does not exclude a singular cascade.

  The method would actually prove Navier–Stokes regularity only after deriving, internally,

  [
  \boxed{
  \Pi_{\Sigma_{\rm sing}}\operatorname{supp}\nu=0
  \quad
  \text{for every stationary zero-price successor law }\nu.
  }
  ]

  Equivalently, it must derive

  [
  Z_\infty^{\Sigma_{\rm sing}}=\varnothing.
  ]

  Concretely, that requires the algebra to prove all three of the following from the Navier–Stokes identities:

  - a genuinely scale-critical signed carrier/passivity identity;
  - saturation implies a finite relative-equilibrium or recurrent scale equation;
  - every target-active solution of that saturation equation is target-null.

  The current passivity theorem proves only the averaged inequality

  [
  \int F_{\rm sc},d\nu
  \le
  \int(D+M),d\nu,
  ]

  and sends equality back into the successor fixed point. It does not eliminate equality. At that point the classical scale-soliton, ancient-profile, pressure-tail, and defect-measure
  difficulties have been reorganized, but not yet dissolved.

  Therefore: the present continuum paper alone does not prove 3D Navier–Stokes regularity. Its current endpoint is a precise zero-price mechanism that still requires substantive elimination. Clay
  still lists the Navier–Stokes problem as unsolved. Clay Mathematics Institute (https://www.claymath.org/millennium/Navier-Stokes-Equation/)

  ### Recommended Navier--Stokes repair: compute the scale-carrier cohomology inside the ordered calculus

  The Navier--Stokes specialization should not attempt to extract a
  scale-independent price from viscous dissipation.  Its positive scaling
  exponent makes that route unavailable.  Instead, the compiler should form
  the signed local-energy current on a coherent tree of parabolic charts and
  compute the cohomology class of the scale feed after convection, pressure,
  translation, cutoff motion, and gauge terms have been glued with their
  signs.  Both the carrier complex and its cohomology are formed after
  projection to the target-aligned quotient.  Large turbulent currents with
  zero singular-shell pairing play no role in the regularity calculation.

  There are then two algebraic branches.  If the scale feed is a coboundary,
  invariant averaging removes it and zero physical price forces the viscous
  and suitable-energy productions to vanish.  If it is not a coboundary, its
  finite set of harmonic scale coordinates becomes part of the saturation
  equation.  Stationarity turns those coordinates into the Euler--Lagrange
  equation for a scale-relative orbit.  The multiplier enumerator then applies
  the generated scaling, translation, pressure-constraint, and local-energy
  identities to that equation.  A positive target separator eliminates the
  relative orbit; a failure produces a positive functional satisfying the
  complete scale-relative equations, not an unnamed analytic remainder.

  This is the continuous analogue of reducing a large discrete search to its
  quotient invariants before exhaustive evaluation.  The difficult estimates
  are replaced by three finite structural computations: signed-current
  cancellation, scale-cohomology computation, and ordered-kernel elimination.
  The Navier--Stokes application is complete only when the generated proof
  transcript eliminates every target-active kernel; naming the kernel is not
  a regularity proof.

  ### Navier--Stokes implementation checklist

  - [ ] Generate the Galerkin/mollified approximation tower for divergence-free
    data and derive the global energy inequality at the approximate level.
  - [ ] Use the kinetic-energy production
    \(\nu|\nabla u|^2\,dx\,dt\), including the suitable-energy defect, as the
    single physical expenditure measure.
  - [ ] Generate the singular target from failure of strong continuation and
    add scale-critical local velocity, pressure, vorticity, and continuation
    coordinates to the graph-complete compactification.
  - [ ] Generate the prospective singular-shell covectors and compute the
    sourcewise formation support before estimating any velocity or pressure
    norm.
  - [ ] Compile viscosity as \(\Geom\), fixed nonlinear transport as \(\Caus\),
    Galilean/gauge reduction as \(\Abs\), blow-up charts and scale motion as
    \(\Lift\), and true exterior or terminal flux as \(\Bdry\).
  - [ ] Derive pressure from
    \(-\Delta p=\partial_i\partial_j(u_i u_j)\); route the local singular
    integral, harmonic gauge, and exterior tail through separate graph
    coordinates.
  - [ ] Build the coherent parabolic chart tree from the canonical disjoint
    shell cascade.
  - [ ] Restrict the tree to descendants retaining positive target alignment;
    discard target-null descendants before carrier and scale computations.
  - [ ] Sum the local-energy identities with their native signs before taking
    positive parts.
  - [ ] Verify algebraically that convection, pressure transport, chart
    translation, cutoff motion, and compatible interior fluxes are edge
    coboundaries or explicit exterior coordinates.
  - [ ] Compute the remaining scale-current cohomology using the cellular
    boundary operator of the target-retaining chart tree.
  - [ ] On the exact-cohomology branch, use invariant averaging to derive
    vanishing of viscosity and suitable-energy defect on every zero-price
    stationary law.
  - [ ] Propagate \(\nabla V=0\) through incompressibility and the Galilean
    quotient and prove that the resulting constant class is target-null.
  - [ ] On each nonexact scale-cohomology branch, derive the corresponding
    scale-relative Navier--Stokes equation from stationarity rather than
    declaring a soliton ansatz.
  - [ ] Enumerate the rational cutoff limits of the scaling, translation,
    pressure, local-energy, Pohozaev, and Noether multipliers on that equation.
  - [ ] Route every nonvanishing cutoff boundary term through the pressure-tail
    and boundary successor graphs; do not assume decay at infinity.
  - [ ] Encode the resulting equality system and target floor in the ordered
    moment hierarchy.
  - [ ] Produce either a finite positive-separator derivation for every
    source/mode cell or a consistent positive-functional model of the complete
    scale-relative system.
  - [ ] Conclude global regularity only after all target-active models have
    finite elimination transcripts checked by the proof kernel.
  - [ ] If a model survives, reconstruct its coherent approximation tower and
    report the exact ancient, recurrent, concentration, tail, and gauge
    coordinates that remain; this is a mathematically specified candidate
    singular mechanism rather than an inconclusive branch.

  ## Stress test: Yang–Mills mass gap

  This exposes a different problem.

  The Clay problem is not classical Yang–Mills global regularity. It asks for the existence of a nontrivial quantum Yang–Mills theory on four-dimensional space and a positive mass gap. Clay
  Mathematics Institute (https://www.claymath.org/millennium/yang-mills-the-maths-gap/)

  The manuscript’s spectral Hamiltonian begins with:

  [
  \text{“Let }\mathfrak q\text{ be a densely defined closed nonnegative form on a Hilbert space.”}
  ]

  See the to_formalize/continuous_hamiltonian_structural_complexity.tex:4309. For the mass-gap problem, constructing the continuum Hilbert space, vacuum, observable algebra, and Hamiltonian is
  already part of the required theorem. They cannot be textbook presentation inputs without assuming away the existence half of the problem.

  Even after constructing (H), the mass gap is the assertion

  [
  \langle\psi,H\psi\rangle
  \ge
  \Delta|\psi|^2,
  \qquad
  \psi\perp\Omega,
  \qquad
  \Delta>0.
  ]

  A useful structural target would be a sequence

  [
  |\psi_n|=1,\qquad
  \psi_n\perp\Omega,\qquad
  \langle\psi_n,H\psi_n\rangle\to0.
  ]

  The analogue of the zero-price successor program would have to classify all ways such a sequence can survive:

  - escape to infinite volume;
  - ultraviolet concentration;
  - gauge-null motion;
  - topological-sector drift;
  - vacuum degeneracy;
  - loss of norm in a weak limit;
  - regulator-dependent boundary states.

  But a classical action budget does not eliminate those possibilities. One must construct regulated theories and derive, uniformly as volume and lattice cutoffs are removed:

  1. a nontrivial continuum limit;
  2. reflection positivity and reconstruction of the physical Hilbert space;
  3. a vacuum sector;
  4. a regulator-independent positive spectral gap.

  The current Hamiltonian/resolvent machinery can analyze a Hamiltonian once it exists. It does not construct quantum Yang–Mills or derive the uniform gap. Applying the existing PDE regularity
  theorem directly would therefore be a category error.

  ### Recommended Yang--Mills repair: add a regulator-to-continuum spectral track

  Classical Yang--Mills regularity and the quantum mass-gap problem must use
  different targets.  Classical Yang--Mills fits the physical-reachability
  track: finite-action or finite-energy orbits are tested against a
  noncontinuation target.  The quantum mass gap requires a spectral-limit
  track whose public presentation begins with finite lattice gauge systems,
  not with an assumed continuum Hilbert space or Hamiltonian.

  At each finite regulator, Haar measure and the lattice action generate the
  Euclidean measure, reflection operation, gauge-invariant cylinder algebra,
  transfer form, and finite-volume Hamiltonian.  Refinement, volume growth,
  and block-spin maps form a graph-complete regulator tower.  Continuum states
  are compatible positive functionals on the gauge-invariant cylinder
  algebra.  Reflection positivity is a closed order relation, so a positive
  continuum functional generates its Hilbert space, vacuum, semigroup, and
  Hamiltonian by reconstruction rather than assumption.

  Gap failure is the target family

  \[
  \|\psi_n\|=1,\qquad \psi_n\perp\Omega,\qquad
  \langle\psi_n,H\psi_n\rangle\longrightarrow0.
  \]

  The ordered successor calculus must track every way this family can persist
  through ultraviolet refinement and infinite-volume passage.  The target is
  excluded only by a regulator-uniform ordered derivation showing that the
  zero-energy kernel equals the vacuum sector.  The spectral form is a
  physical energy, but it is not a second PDE reachability budget; the mass-gap
  theorem is a separate spectral application of the same source, quotient,
  compactification, and dual-evaluation machinery.

  The spectral calculation must retain the same prospective principle.  At
  finite regulator, low-energy spectral filters and vacuum-orthogonal
  correlation shells generate a family \(\Gamma_{\rm gap}\).  Only regulator
  currents and observable directions with positive pairing against
  \(\Gamma_{\rm gap}\) enter the zero-gap successor problem.  Vacuum motion,
  pure gauge motion, and regulator changes invisible to every such filter are
  removed before the uniform-gap calculation.

  ### Yang--Mills implementation checklist

  - [ ] Define the public quantum presentation from a compact simple gauge
    group, finite lattices, Haar measure, local gauge action, reflection, and
    gauge-invariant cylinder observables.
  - [ ] Construct each finite-regulator probability measure and transfer form
    directly from this presentation.
  - [ ] Generate gauge reduction as an \(\Abs\) quotient and retain gauge-fixing
    and Gribov-type graph defects rather than choosing a global gauge slice.
  - [ ] Prove finite-regulator reflection positivity inside the ordered
    cylinder algebra.
  - [ ] Form the refinement, block-spin, and volume-extension graph with
    ultraviolet, infrared, boundary, topological-sector, and normalization
    coordinates.
  - [ ] Apply the graph-complete positive-functional compactification to this
    regulator tower.
  - [ ] Require projective consistency, locality, reflection positivity, and
    nontrivial observable variance as closed order relations.
  - [ ] Reconstruct the continuum Hilbert space, vacuum vector, transfer
    semigroup, and self-adjoint Hamiltonian from any zero-defect positive
    continuum functional.
  - [ ] Treat failure of tightness, reflection positivity, strong continuity,
    or nontriviality as a typed regulator-limit mechanism with inherited
    source ancestry.
  - [ ] Encode vacuum orthogonality and Rayleigh quotients in the cylinder
    moment algebra without assuming the existence of a gap.
  - [ ] Generate prospective low-energy spectral filters and correlation-shell
    covectors \(\Gamma_{\rm gap}\) at every finite regulator.
  - [ ] Compile Dirichlet/form geometry as \(\Geom\), directed transfer as
    \(\Caus\), gauge quotient as \(\Abs\), refinement and block-spin motion as
    \(\Lift\), and ultraviolet, infrared, and volume faces as \(\Bdry\).
  - [ ] Quotient all regulator directions annihilated by
    \(\Gamma_{\rm gap}\) before applying the moment hierarchy.
  - [ ] Define the target-active zero-gap successor set across simultaneous
    ultraviolet and infinite-volume limits.
  - [ ] Derive regulator-uniform correlation, transfer, and reflection-positive
    inequalities through the ordered consequence enumerator.
  - [ ] Compile renormalization-scale feeding into a signed cocycle and compute
    its invariant cohomology before taking absolute values.
  - [ ] On the zero-price branch, derive the saturation equations for a
    nonvacuum zero-energy state and reduce them by gauge, locality, cluster,
    and topological-sector relations generated by the regulator tower.
  - [ ] Use the proof-producing moment hierarchy to establish either a uniform
    positive separator from the vacuum or a compatible zero-gap positive
    functional at every regulator scale.
  - [ ] Claim a mass gap only after the separator is uniform in volume and
    ultraviolet cutoff and survives continuum reconstruction.
  - [ ] Claim existence only after the reconstructed continuum functional is
    reflection positive, local, nontrivial, and yields a strongly continuous
    time-translation semigroup.

  For classical Yang--Mills regularity, use the PDE checklist instead: generate
  curvature-energy shells, quotient gauge motion, retain bubbling and
  topological charge as explicit target-active mechanisms, and apply the same
  carrier-cohomology and ordered-kernel elimination.  Instantons or bubbles
  with finite action are legitimate saturation states; the algebra must retain
  them whenever the chosen target and topological sector permit them.

  ## Bottom line

  The remaining hidden difficulty is concentrated in one statement:

  [
  \boxed{
  \text{Every target-active zero-price fixed point must be either
  finitely eliminable or physically realizable.}
  }
  ]

  The paper currently proves neither half in general:

  - finite eliminability is defined through semantic inequalities and inclusions;
  - surviving compact mechanisms need not correspond to actual dynamics.

  For Navier–Stokes, this means the difficulty has moved into eliminating the target-active zero-price scale-saturation law. For Yang–Mills mass gap, the required quantum state space and
  Hamiltonian are not generated at all.

  So the manuscript has achieved an exhaustive provenance calculus, but it does not yet possess an exhaustive truth-evaluation calculus. That is the precise remaining defect.

  ## Unified implementation order

  The five repairs above should be implemented as one dependency chain:

  \[
  \text{public equation syntax}
  \longrightarrow
  \text{exhaustive approximation tower}
  \longrightarrow
  \text{graph-complete ordered cylinder algebra}
  \longrightarrow
  \text{five-source compilation and sourcewise saturation}
  \longrightarrow
  \text{prospective target-aligned quotient}
  \longrightarrow
  \text{signed shell/carrier currents}
  \longrightarrow
  \text{zero-price successor/equality reduction}
  \longrightarrow
  \text{primal--dual moment evaluator}.
  \]

  This chain yields the required truth-evaluation theorem:

  \[
  \boxed{
  \begin{aligned}
  &\text{finite ordered derivation excluding every target-active}\\
  &\text{zero-price successor state},
  \end{aligned}}
  \quad\text{or}\quad
  \boxed{
  \begin{aligned}
  &\text{a compatible positive-functional model carrying the}\\
  &\text{complete equation, source ancestry, price, and target pairing}.
  \end{aligned}}
  \]

  The first box proves target avoidance.  The second box is already a complete
  generalized mechanism.  It supports a physical singularity claim only when
  the generated approximation graph supplies a coherent realizing path.  No
  semantic set inclusion, favorable invariant value, compactness theorem,
  Liouville statement, or PDE-specific certificate is accepted as application
  data.

  ### Cross-cutting completion checklist

  - [ ] Implement the approximation grammar before modifying the successor
    algebra.
  - [ ] Replace the evaluation product closure with the positive-functional
    state space of the graph-complete cylinder algebra.
  - [ ] Replace every catch-all defect by a least typed graph failure and its
    derived Radon current.
  - [ ] Compile full five-channel ancestry before taking any target quotient or
    analytic limit.
  - [ ] Generate prospective target alignment and delete target-null currents
    before invoking compactness, cohomology, or moment machinery.
  - [ ] Glue signed carrier currents before taking positive parts or assigning
    physical price.
  - [ ] Implement the Archimedean ordered proof kernel and prove soundness.
  - [ ] Prove compact completeness and positive-functional reconstruction.
  - [ ] Replace semantic pruning forests by dual derivation forests.
  - [ ] Attach exact rational verification data to every finite pruning node.
  - [ ] Preserve approximation-origin indices through every successor and
    stationary-law construction.
  - [ ] Prove relaxed target exclusion without requiring realization of every
    compactified point.
  - [ ] Require coherent approximation realization for every affirmative
    singularity or zero-gap existence claim.
  - [ ] Instantiate the full pipeline for Navier--Stokes and verify every
    target-active scale-cohomology cell.
  - [ ] Keep the quantum Yang--Mills spectral track separate from the PDE
    physical-reachability theorem while reusing the ordered structural
    machinery.
  - [ ] Revise the main continuum manuscript only after these replacement
    theorems have precise statements and dependency order.
