import HypostructureErdos64EG.Assembly.NetCharge.Boundary

/-!
# Assembly: NearCubic / Boundary

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The near-cubic branch after node `[19]`: node `[21]`, the `[22]` split and
live-hot cap, and — on the cap arm, exactly as `[24]` prescribes — the cold
branch `[145]`--`[157]` on the literal cap residual.  Both spine arms — `[146]`'s
yes arm (`θ < 1/78`, node `[147]`: closed by the spine's route-8 closure with
`K .coldRoute8Below` as its private-carrier inequality) and `[153]`'s bounded
arm (`[24]`'s density cap) — run `[25]`--`[31]` on their literal residuals,
decide `[32]` and enter `[33]` (Branch D) or `[34]` (Residual B); `[35]`--`[46]`
and `[47]` onward fail loudly; the routed cold closure `[157]` fails loudly at
its target-defect/handoff discharge. -/
-- EG-NODE [22] hot/cold split $\mathcal P=\mathcal P_{\rm hot}\sqcup\mathcal P_{\rm cold}$: live-hot entropy cap closes?
-- EG-NODE [24] bounded cold-mass return from [153]: $\theta\le\theta_{\rm win}+o(1)$; high entropy: $\theta\le0.01198542083\ldots$
-- EG-NODE [25] Residual A: $R=G-\bigcup V(P)$ is large and componentwise $P_{13}$-free
-- EG-NODE [26] Residual A: $R$ large and componentwise $P_{13}$-free
-- EG-NODE [27] no component of $R$ has an internal $3$-core
-- EG-NODE [28] positive deficiency $\defp(X)=\sum_v\max(0,3-d_X(v))$
-- EG-NODE [29] external-incidence supply: $\defp(R)\le15p_{13}+o(n)$ and $\defp(R)-\sigma_R\le15p_{13}+o(n)$
-- EG-NODE [30] wedge lower bound: $W_2(R)\ge\omega_{\rm win}|R|-o(|R|)$ (sharper high-entropy $\omega=2.57407357888\ldots$)
-- EG-NODE [31] obstruction rank $r_\Omega(R)$
-- EG-NODE [32] rank drop? $r_\Omega(R)<W_2(R)-o(W_2)$
-- EG-NODE [33] Branch D: rank-reducing obstruction dependence
-- EG-NODE [34] Residual B: no rank drop; full obstruction rank $r_\Omega(R)\ge W_2(R)-o(W_2)$
-- EG-NODE [35] Branch D: rank-reducing obstruction dependence
-- EG-NODE [47] Residual B: full obstruction rank $r_\Omega(R)\ge W_2(R)-o(W_2)$
-- EG-NODE [48] forced obstruction cost $c_\Omega W_2(R)\ge K_{\rm win}|R|-o(|R|)$ (high entropy: $K=5.89262883286\ldots$)
-- EG-NODE [49] per-vertex remainder entropy $\eta(R)=\log_2|\mathcal G(R)|/|R|$
-- EG-NODE [50] $\eta(R)\ge\frac1{10}\log_2 n$?
-- EG-NODE [51] high-entropy remainder branch
-- EG-NODE [52] window plus remainder accounting bounds $\theta$
-- EG-NODE [53] remaining non-obstruction budget $<K|R|$?
-- EG-NODE [54] entropy cap closes
-- EG-NODE [55] Residual C: large-budget branch; $\theta\le\theta_{\rm win}+o(1)$
-- EG-NODE [56] $\Delta_{\mathrm{net}}(R)=\dfrac{\defp(R)-\sigma_R}{|R|}\le\tau_{\rm win}+o(1)<1/4$
-- EG-NODE [145] cold-branch continuation from the no-edge of [22], after the spine estimate
-- EG-NODE [146] \(\theta<1/78\)?
-- EG-NODE [147] route-8 private-incidence collision closes
-- EG-NODE [148] live-hot entropy cap closes?
-- EG-NODE [150] hot failure forces cold mass: \(C\ge(\theta-\theta_{\rm win})n-o(n)\)
-- EG-NODE [151] all but \(o(n)\) cold windows ambient-cubic
-- EG-NODE [152] selected interior-stub excess: \(b_{\rm int}(\mathfrak S_{\rm cold})\ge9C-o(n)\)
-- EG-NODE [153] linear first-failure extraction? \(N_{\rm conf}\ge9C/D_{\rm cold}-o(n)\)
-- EG-NODE [154] bounded configuration case?
-- EG-NODE [155] G1: power-of-two cycle
-- EG-NODE [156] G2: target defect, exit (4), or handoff
-- EG-NODE [157] G3 or same-interface table: compression
-- EG-NODE [160] exact rate split: first \(\tau(\theta)<1/4\)?; on yes, private-carrier rate \(\tau(\theta)<3/13\)?
-- EG-NODE [161] both rates hold: negative-net-charge collision; continue at [25] with the deficiency cap in place of [24]
-- EG-NODE [162] dense hot/cold pass: run [22]--[24] and [145]--[157] on the dense residual; [23], [149], [155], [156], [157] close as before; bounded arm of [153] and [146]/[160] arms return to [25]
-- EG-NODE [163] neutral equal-length terminal configuration: second strand graph-realized?
-- EG-NODE [164] all-cold comparison closes: \(|\mathcal G(R)|\le|\mathcal G_{n,m}|\) by the remainder glue
-- EG-NODE [165] canonical replacement \(E\ne Q\): swap \(Q\to E\) gives a same-size counterexample
-- EG-NODE [166] refined lexicographic minimality: \(Q=E\)
-- EG-NODE [167] symmetric strand pair: finite two-strand check on the closing lengths \(2\ell\), \(\ell+d\)
-- EG-NODE [168] surviving pair attaches only at endpoints: not a selected interior half-edge
-- EG-NODE [169] trivial neutral-configuration residual: dense packing, every corridor terminal and neutral, \(Q=E\); every window is blocked at every dyadic scale
abbrev SelectedNearCubicSurvivorBoundary (selected : EGInput.{u}) :=
  SelectedNetChargeBoundary selected ∨
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
        erdosReceiverLoadProfile spineData .route8RateFails selected.object ∨
      Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData .blockedBarrierOverlap selected.object ∨
        Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData .coldBranchClosed selected.object

/-- The literal target-defect exit left by the enclosing `[20]` sparse-exit
classification.  It is an outgoing residual, not a contradiction, not a
survivor fact, and not an output of routing-only node `[125]`. -/
abbrev SelectedSparseTargetDefectBoundary (selected : EGInput.{u}) :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
    erdosReceiverLoadProfile spineData .sparseTargetDefectResidual
      selected.object

/-- The near-cubic branch either leaves through the paper's named
target-defect exit or, after all sparse exits have been excluded, follows the
surviving-cold/net-charge continuation. -/
abbrev SelectedNearCubicBoundary (selected : EGInput.{u}) :=
  (SelectedSparseTargetDefectBoundary selected ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseTargetDefectStructure
        selected.object) ∨
    SelectedNearCubicSurvivorBoundary selected

end HypostructureErdos64EG
