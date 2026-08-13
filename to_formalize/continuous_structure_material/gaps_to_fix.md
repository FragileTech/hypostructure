  - The current framework does not yet prove 3D Navier–Stokes regularity from textbook data alone. It gives a rigorous necessary-mechanism reduction, but the decisive elimination step is
    presently semantic rather than constructive.

  - It cannot presently prove the Yang–Mills mass gap as a PDE-regularity application. The Clay problem is a quantum-field existence and spectral-gap problem, and the manuscript begins after
    several objects that must instead be constructed.

  The five-channel classification is substantially sound. The remaining problem is not classification; it is evaluation.

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

  ### 4. The generated consequence algebra is not proved complete

  The consequence algebra enumerates integration by parts, localization, adjoints, completion of squares, graph closure, and related operations. But there is no theorem that these rules derive
  every structural identity needed to eliminate a target-active zero-price mechanism.

  The passivity theorem itself says that equality forces a production term to vanish only when the algebra already contains a domination identity

  [
  p=q+r,\qquad q,r\ge0.
  ]

  That is exactly the remaining pressure point to_formalize/continuous_hamiltonian_structural_complexity.tex:3217. The manuscript does not ask the user to supply (p=q+r), but neither does it give
  a general procedure that necessarily derives or refutes it.

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