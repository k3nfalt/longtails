# Finite-variance high-probability convergence of persistent Muon

## Result and scope

[The theorem](FiniteVarianceMuonHighProbability.lean) proves a high-probability nuclear-gradient stationarity guarantee for ideal exact-polar Muon with an unchanged, persistent exponential moving average and one oracle sample per training update. A separate, explicitly charged validation stage returns a training iterate. The new contribution is the confidence guarantee under finite variance alone, including unbounded and asymmetric noise and unbounded population gradients. The geometric advantage over scalar SGD is a comparison of certified upper bounds inherited from non-Euclidean optimization; it is not a new lower-bound separation or a claim of best problem-class complexity.

The single [setup](../Setups/FiniteVarianceSpectralSmooth.lean) concerns arbitrary finite rectangular matrices and general nonlinear, lower-bounded differentiable objectives. It requires

\[
\|\nabla f(X)-\nabla f(Y)\|_*\le L\|X-Y\|_{\mathrm{op}},\qquad
f(X_0)-f_{\min}\le\Delta,
\]

where the lower bound need not be attained. The stochastic gradient is jointly measurable and unbiased. There is a fixed, analysis-only orthonormal left basis \((u_i)\) and nonnegative numbers \(\sigma_i\) such that, uniformly in \(X\),

\[
\mathbb E\|[G(X,\xi)-\nabla f(X)]^\top u_i\|_2^2\le\sigma_i^2,
\qquad \sum_i\sigma_i\le s.
\]

The specification includes the necessary row square-integrability and full oracle integrability. The latter is redundant in finite dimension but makes the unbiased integral well defined directly. Rows need not be independent; their correlations may depend on the query. The algorithm knows only the aggregate bound \(s\), not the basis, profile, objective, lower-bound value, or noise distribution. The other public inputs are \(L,\Delta,\varepsilon,\delta,X_0\). Parameters satisfy \(L,\Delta,s\ge0\), \(\varepsilon>0\), and \(0<\delta<1\).

The sampling law is an arbitrary probability measure with IID coordinate samples, using the repository's shared IID structure. It is not prescribed to be a product measure. `MuonProcess.coordinateIID_map` transports any abstract IID sample sequence to this path-space representation. There is no finite-sample-space restriction. The theorem's probability includes both this oracle law and the algorithm's independent random index selections.

Writing

\[
A=1+s^2/\varepsilon^2,\quad R=1+L\Delta/\varepsilon^2,
\quad J=\log(2^{56}AR/\delta),
\]

the proved oracle budget is zero if \(2L\Delta\le\varepsilon^2\), and otherwise

\[
N=\left\lceil 2^{45}A\left(R+\sqrt R\,J^2\right)\right\rceil.
\]

For the returned point \(\widehat X\), the actual `execute` output is measurable and

\[
\Pr\{\|\nabla f(\widehat X)\|_*>\varepsilon\}\le\delta.
\]

Thus the nontrivial-regime polynomial dependence is
\(\widetilde O((1+s^2/\varepsilon^2)L\Delta/\varepsilon^2)\), with the displayed additive square-root-gap confidence term. The explicit constant is conservative. This is stationarity for ordinary unconstrained function minimization, not global optimality of a nonconvex function, a minimax guarantee, or a statement about training loss values. Nuclear norm is the same accuracy criterion in all comparisons below.

## Algorithm and cost

Matrix types and norm definitions live with [MatrixPolar](../Algorithms/MatrixPolar.lean), rather than in a separate setup module. [ValidatedMuon](../Algorithms/ValidatedMuon.lean) defines the algorithm independently of its proofs. In the nontrivial case set

\[
e=\varepsilon/8,\quad\gamma=\delta/4,\quad D=L\Delta/e^2,
\quad a=\max\{1,4096s^2/e^2\},\quad
H=\log(2^{30}aD/\gamma),
\]
\[
T=\lceil2^{20}a(D+\sqrt D H^2)\rceil,
\quad\alpha=1/a,\quad\eta=\Delta/(eT).
\]

Starting with \(M_0=0\), training takes exactly one new sample at each step:

\[
M_{t+1}=(1-\alpha)M_t+\alpha G(X_t,\xi_t),\qquad
X_{t+1}=X_t-\eta\,\operatorname{polar}(M_{t+1}).
\]

The polar is the canonical partial polar, zero on the kernel. [MatrixPolarCharacterization](../Proofs/MatrixPolarCharacterization.lean) proves that the definition used by the algorithm has this singular-basis characterization for rectangular and rank-deficient matrices. No spectral gap or full-rank premise is used. This is plain EMA Muon, without Nesterov modification. Exact polar computation is part of the ideal oracle algorithm; the result does not analyze finite Newton–Schulz iterations or wall-clock complexity.

The pool consists of the \(T\) pre-update points \(X_0,\ldots,X_{T-1}\). Draw

\[
Q=\lceil\log(1/\gamma)/\log2\rceil
\]

independent uniform pool indices. For each selected point use \(k\) fresh disjoint IID sample batches, each of size \(b\), where

\[
b=\max\{1,\lceil144s^2/e^2\rceil\},\qquad
k=\lceil8\log(Q/\gamma)\rceil.
\]

These batches are independent conditional on the selected point and training past; batch means evaluated at a shared random point need not be unconditionally independent. Choose a batch-mean representative having a strict majority of neighbors within nuclear distance \(2e/3\), with a deterministic fallback and tie rule. Return the sampled point whose representative has least nuclear norm. This requires no function values or exact gradients. The training recurrence is neither clipped, batched, restarted, nor reset; the complete output algorithm does batch its validation queries.

Useful calls are exactly \(T+Qbk\). [MuonTuning](../Proofs/MuonTuning.lean) proves this is at most the displayed public budget. The framework executes all \(N\) calls, including harmless fallback queries after validation is complete; those calls are charged and do not change the output. [ValidatedMuonExecution](../Proofs/ValidatedMuonExecution.lean) proves the execution identity and the precise offsets of every training and validation sample. The setup's `MuonFamily` enforces the recurrence and output-selection family through law-preserving state simulation, while leaving all tuning parameters free. This restriction records the popular-method claim; it is not used to exclude stronger competitors from the comparison.

## New proof mechanism

The obstacle in raw momentum is that the current direction retains an unbounded random tracking error from the entire past. A conditional one-step error bound is therefore random even when the unconditional tracking estimate is small. Simply applying a martingale tail inequality to the usual expected-error proof does not establish the claimed confidence dependence.

The proof instead studies the nonnegative alignment deficit

\[
z_t=\|\nabla f(X_t)\|_*-\langle\nabla f(X_t),\operatorname{polar}(M_{t+1})\rangle.
\]

It conditions a logarithmic number of momentum memory lengths into the past. The old tracking error decays exponentially; the intervening centered noise is controlled by conditional, deterministic-weight Hilbert row estimates. A polynomial-tail bound on the remote tracker therefore costs only a logarithmic lag.

The deficit is stopped when the objective exits a sublevel set or the remote tracker exceeds its analysis threshold. On that stopped set, smoothness and the lower bound give a deterministic bound on the population gradient, even though no global gradient bound is assumed. Nonnegativity allows the future-survival indicator to be removed when bounding the delayed conditional mean. This is the step that avoids incorrectly conditioning on a future good event. A bounded-nonnegative exponential estimate, applied to lag-separated residue classes and their prefixes, controls all required partial sums. A descent bootstrap then proves that objective exit never occurs on the resulting event and removes the stopping. Warmup, initialization, and remote-tracker noise are all retained.

[MuonTraining](../Proofs/MuonTraining.lean) proves that the average nuclear gradient over the pool is at most \(2e\), except with probability \(\gamma\). At least half the pool then has nuclear gradient at most \(4e\). The random selections miss this half with probability at most \(\gamma\). Row-profile batch estimates and a strict-majority representative bound make all validation estimates accurate to \(e\), except with probability at most \(\gamma\). On their joint success the returned point has gradient norm at most \(6e<\varepsilon\). [MuonConvergence](../Proofs/MuonConvergence.lean) combines these statements for the actual execution law, without assuming independence between training success and validation errors.

The contribution is this delayed conditional concentration and stopping/bootstrap argument for persistent raw EMA, not the standard row moment estimate, robust selection, a renamed noise parameter, or Lean formalization alone. For one-row matrices the method becomes ordinary Euclidean normalized momentum, so the confidence result also addresses that established special case.

## Closest work and reductions

Literature checks were made through 20 October 2026 UTC, including the latest accessible revisions and official conference records. The following distinctions are essential.

| Primary result | Applicable guarantee or restriction | Relation to this result |
|---|---|---|
| [NSGD under heavy-tailed noise, v3, 9 July 2025](https://arxiv.org/html/2410.13849v3), especially Appendix D.3 and the conclusion; [AISTATS 2025](https://proceedings.mlr.press/v258/hubler25a.html) | Finite-moment normalized methods; D.3 identifies conditional tracking error as the unresolved persistent-momentum high-probability obstacle | The present proof resolves the finite-variance case for persistent plain EMA. It does not claim the full moment range \(1<p<2\) or variance-reduced variants. |
| [Heavy-tailed Muon, 2606.14560v1](https://arxiv.org/html/2606.14560v1), conclusion | Expected convergence under heavy tails; high-probability theory is left open | The new confidence guarantee retains raw persistent updates and a matrix noise profile. The expected geometric benefit is prior work. |
| [Lions and Muons, v4, 25 August 2026](https://arxiv.org/html/2506.04192v4), Theorems 3, 5, 6 and Algorithms 5, 6; [official ICML 2026 proceedings](https://proceedings.mlr.press/v306/sfyraki26a.html) | Expected Frank–Wolfe gap; its high-probability algorithms clip inputs before EMA on a compact constrained domain. The variance-reduced variant also uses paired samples and individual smoothness | Does not give the unchanged unconstrained raw-EMA guarantee under the present assumptions. Its clipping and constrained update cannot simply be dropped. |
| [Unified High-Probability Analysis of Stochastic Variance-Reduced Estimation, 2605.15388v1](https://arxiv.org/html/2605.15388v1) | Conditional exponential-square noise control | Stronger tail assumption than a finite second moment. It does not cover arbitrary finite-variance spikes. |
| [Adaptive Algorithms with Sharp Convergence Rates for Stochastic Hierarchical Optimization, 2509.15399v2](https://arxiv.org/html/2509.15399v2), NeurIPS 2025 | Hierarchical minimax/bilevel setting, almost-sure noise bounds and additional noise conditions | These conditions are absent here; its result is not a finite-variance-only substitute. |
| [Spectral-smooth Muon/SGDM comparison, 2601.19156](https://arxiv.org/html/2601.19156), Section 4.5, Theorem 3; ICLR 2026 | Expected nuclear-gradient SGDM bound with rank factors and Frobenius noise variance | Supplies a directly matched scalar-momentum comparison, discussed below. The geometric comparison itself is not new. |
| [AdaGrad under Anisotropic Smoothness, 2406.15244v2](https://arxiv.org/html/2406.15244v2), Assumption 3.5 and Appendix D | Coordinate variance and geometry-aware scalar-SGD comparisons; coordinate adaptation can improve them | Use actual smoothness/noise geometry when available. No claim that Muon dominates coordinate AdaGrad or Shampoo. |

The row-profile model is a natural block version of the coordinate variance assumption in [signSGD, ICML 2018, Assumption 3](https://proceedings.mlr.press/v80/bernstein18a/bernstein18a.pdf) and the cited anisotropic AdaGrad work. It is not claimed to be an identical previously published Muon assumption. A common PSD envelope \(\mathbb E NN^\top\preceq\Sigma^2\) implies it with \(s=\operatorname{tr}\Sigma\). Requiring only row bounds permits varying cross-row correlations. This routine model weakening is not the central novelty. Merely assuming \(\mathbb E\|N\|_*^2\le s^2\) would not justify the dimension-free averaging argument and is not substituted for the profile.

Two standard reductions limit the claim. First, fresh-batch polar normalized SGD with batch size of order \(1+s^2/\varepsilon^2\) has no persistent tracking term. The same bounded-deficit reasoning gives training cost of order \(A[D+\sqrt D\log(1/\delta)]\), before comparable selection costs, and matches or improves the present problem-class rate. Second, independent constant-success runs followed by the same finite-variance validation give logarithmic confidence amplification for existing methods, including scalar SGD. Thus neither polylogarithmic confidence alone nor the output selector is new. These reductions change the persistent one-sample training dynamics whose robustness is proved here; they do not prove this trajectory's guarantee.

The survey also screened ordinary smoothness versus Hessian-Lipschitz implicit-gradient-transport results, including [Cutkosky–Mehta, ICML 2020](https://proceedings.mlr.press/v119/cutkosky20b.html), [2506.11214v2](https://arxiv.org/html/2506.11214v2), and [2605.05577](https://arxiv.org/abs/2605.05577). Their stronger regularity can yield an \(\varepsilon^{-7/2}\) stochastic dependence. That regularity is not part of this setup, and the present theorem does not dominate those results on instances where they apply.

## What “better than SGD” means here

Let \(r=\min(m,n)\), let \(L_F\) be an available Frobenius smoothness constant, and write \(\sigma_F^2\) for a Frobenius variance bound. Generic scalar SGD/SGDM guarantees converted to the same nuclear-gradient accuracy have polynomial oracle dependence

\[
\frac{rL_F\Delta}{\varepsilon^2}
+\frac{r^2L_F\Delta\sigma_F^2}{\varepsilon^4}.
\]

The spectral-smooth SGDM theorem cited above gives the corresponding rank-dependent comparison directly. Batching counts every sample and does not remove the leading stochastic rank factor in these bounds; restarting and validation add confidence and selection costs to both methods. With the row profile, \(\sigma_F^2\le\sum_i\sigma_i^2\), whereas Muon's leading stochastic term is \(L\Delta s^2/\varepsilon^4\). When the available geometry does not give a smaller scalar-SGD coefficient, the ratios of these certified polynomial terms are

\[
\frac{rL_F}{L},\qquad
\frac{r^2L_F\sigma_F^2}{Ls^2}.
\]

For \(L_F\asymp L\) and a rank-one noise profile, the latter is of order \(r^2\); for an isotropic square-matrix profile it is of order \(r\). If \(L_F\ll L/r\), or a sharper Hessian/noise contraction improves scalar SGD, this conclusion need not hold. A geometry-aware scalar comparison must use that sharper coefficient, not replace it with a loose worst-case norm conversion. Rectangular row profiles also need not give the best possible noise parameter in every orientation.

Minibatch Frobenius-normalized SGD is also a scalar adaptive update and must be included. At Frobenius accuracy \(\varepsilon_F=\varepsilon/\sqrt r\), set \(D_F=rL_F\Delta/\varepsilon^2\) and batch size \(b_F\asymp1+r\sigma_F^2/\varepsilon^2\). The fresh-batch reduction gives training cost \(b_F[D_F+\sqrt{D_F}\log(1/\delta)]\), plus the same charged selection stage. This stronger scalar comparator retains the displayed polynomial geometric factors; it can have better confidence overhead than persistent Muon. The comparison therefore does not exclude scalar normalization, clipping, batching, or confidence amplification by definition.

The meaningful asymptotic regime has \(D=L\Delta/\varepsilon^2\) at least of order \(J^4\): precisely, \(\sqrt D J^2\le D\) when \(D\ge J^4\), and rank/profile advantage larger than the confidence overhead. The explicit \(2^{45}\) constant prevents an assertion of practical numerical speedup from these formulas alone. No all-adaptive-scalar-SGD lower bound is proved; no claim is made that every SGD tuning or output rule is slower. The theorem provides a stronger certified finite-variance, high-probability guarantee for this Muon family in the stated geometric regimes. It does not manufacture a comparison by restricting competitors to `MuonFamily`.

## Nonlinear instances and practical meaning

The assumptions describe structured matrix-gradient noise rather than independent scalar coordinates. A noisy response in a matrix regression term produces rank-one noise with a dimension-independent row budget. For a layer gradient \(dh^\top\), bounded activations or appropriate mixed moments can bound \(\mathbb E[d_i^2\|h\|^2]\) and hence the centered row variances. Separate second moments of \(d_i\) and \(h\) alone are insufficient. The theorem does not assume a neural network automatically satisfies global spectral smoothness.

A concrete interacting nonlinear family exists in every square dimension \(r\ge2\). Let \(A_0=E_{00}\), \(v_i=(e_i+e_{i+1\bmod r})/\sqrt2\), \(B_i=v_iv_i^\top\), \(\phi(z)=(1-e^{-z^2})/2\), and \(\lambda=e^{-1}/32\). Consider robust matrix regression with a ridge:

\[
f(X)=\tfrac12(\langle A_0,X\rangle+1)^2
+\frac1{4r}\sum_i\phi(\langle B_i,X\rangle+1)
+\frac\lambda{2r}\|X\|_F^2.
\]

It is coercive, has overlapping noncommuting measurements, spectral-to-nuclear smoothness at most \(5/4+\lambda\), and Frobenius smoothness at least \(3/4\). At zero, the Hessian in direction \(E_{01}\) is at most \(-e^{-1}/(32r)\), so the objective is genuinely nonconvex. Its gradient at zero is positive definite, giving full-rank gradients on an open neighborhood. A centered noisy response \(-1+\zeta\) in the first squared term yields centered oracle noise \(-\zeta A_0\) and \(s=\sqrt{\mathbb E\zeta^2}\), independent of dimension. Any finite-variance law, including unbounded heavy tails, is allowed. Starting at zero gives a dimension-independent gap upper bound since the objective is nonnegative and its value there is bounded.

This family establishes nonlinear scope and a natural noise mechanism, not an SGD hardness example. It has additional Hessian regularity, so implicit-gradient-transport methods can outperform the present accuracy dependence in suitable regimes. The general theorem does not assume that additional regularity. The example's calculations are explanatory mathematics, not additional formal hypotheses or a separate Lean theorem.

## Formalization and limitations

The main proof uses only the pinned framework and mathlib. Supporting modules establish exact polar geometry and measurability, conditional row moments for adaptive IID queries, delayed concentration, the bootstrap, validation, execution, and explicit budget domination. No core definitions, oracle interfaces, or existing theorems are weakened. The main declaration names `FiniteVarianceSpectralSmooth.spec` directly and constructs `finiteVarianceMuon` with its enforced output family.

This result is not parameter-free: it uses upper bounds on smoothness, initial gap, and noise. It proves stationarity, not minimizer proximity; it covers exact plain EMA polar Muon, not every implementation called Muon. It does not cover Markov sampling, arbitrary bias, infinite-variance noise, or the full \(p<2\) heavy-tail regime. Geometric gains, batching, and robust selection are established ingredients. The new claim is the persistent-EMA confidence analysis under the stated weak tail assumptions, together with its fully charged executable output guarantee.
