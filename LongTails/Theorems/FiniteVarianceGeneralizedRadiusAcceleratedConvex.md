# Radius-based acceleration with finite-variance gradients

The [main theorem](FiniteVarianceGeneralizedRadiusAcceleratedConvex.lean) proves a high-probability oracle bound for convex optimization under gradient-dependent smoothness. Its contribution is a coarse stochastic warm start that removes the initial-gap dependence from the curvature cost while preserving accelerated accuracy dependence and an additive variance cost.

## Specification and guarantee

The theorem reuses the existing [finite-variance generalized-smooth convex specification](../Setups/FiniteVarianceGeneralizedSmoothAndConvex.lean) exactly. On a separable real Hilbert space, the objective is convex, has an everywhere differentiable gradient, and satisfies

$$
\|D\nabla f(x)\|\le L_0+L_1\|\nabla f(x)\|\quad\text{for every }x.
$$

There is a minimizer $x^\star$ with $\|x_0-x^\star\|\le R$. The oracle is jointly measurable, vector-unbiased, and has uniform second centered moment at most $\sigma^2$; the integrability conditions are those of the shared stochastic-gradient definition. Samples are IID under an abstract probability measure, including independence and the prescribed marginal law. Neither a finite sample space nor a prescribed product probability space is required. No samplewise smoothness, bounded realizations, exponential moments, function-value queries, or repeated access to the same random sample is assumed.

The parameter ranges are $L_0,R,\Delta,\varepsilon>0$, $L_1,\sigma\ge0$, and $0<\delta<1$. The reused specification supplies $f(x_0)-f(x^\star)\le\Delta$, but neither the algorithm nor this budget uses $\Delta$. Thus the theorem is uniform in this certificate; the algorithm needs only the radius and the other displayed parameters.

Set

$$
h=L_1R,\quad T=L_0R^2/\varepsilon,\quad
V=\sigma^2R^2/\varepsilon^2,\quad
\ell=\log\!\left(\frac{e(2+T+h+\sigma R/\varepsilon)}{\delta}\right).
$$

After exactly the public budget

$$
K=\left\lceil 2^{70}(1+h+\sqrt T+V)\ell^3\right\rceil
$$

of stochastic-gradient calls, the returned point $\widehat x$ satisfies

$$
P\{f(\widehat x)-f(x^\star)>\varepsilon\}\le\delta.
$$

The theorem invokes the repository's `execute` interface. This is a high-probability statement about the actual output, not a minimum over unobserved objective values or an expected-gap assertion. The bound is dimension-free under the stated norm-variance bound; an application may have dimension-dependent $L_0,L_1,R,\sigma$. Arithmetic complexity is not bounded, and the universal constant is deliberately conservative.

## Algorithm and new mechanism

The [combined algorithm](../Algorithms/CoarseGeneralizedAccelerated.lean) first runs the [coarse warm-start dynamics](../Algorithms/CoarseGeneralizedWarmstart.lean), then restarts the existing [robust generalized acceleration algorithm](../Algorithms/RobustGeneralizedAccelerated.lean). Its output is the latter algorithm's last completed accelerated $x$ iterate after the remaining calls. During an unfinished estimator batch it returns the preceding completed iterate; after termination, padding leaves that iterate unchanged. It does not select an iterate by evaluating objective values. All choices depend on public parameters and observed replies, not on the minimizer, exact gradients, or unavailable objective values.

For $h\ge1$, the warm stage uses error tolerance $\zeta=\sigma+L_0R$, inflated analysis curvature

$$
\lambda=L_0+2^{20}L_1^2R\zeta,
$$

$4096\lceil h\rceil$ rounds, and at most

$$
d+2,\qquad d=\left\lceil\log_2(2^{20}(1+h)^2)\right\rceil+1
$$

coarse queries per round. Each coarse query uses a robust center of $G$ independent means of 576 raw samples, where $C=4096\lceil h\rceil(d+2)$ and $G=\lceil\log_2(4(1+C)/\delta)\rceil+1$. These are counted as $576GC$ oracle calls, including padding after an early exit. For $h<1$, the warm stage is skipped.

With failure probability at most $\delta/4$, its returned point $x_w$ obeys both

$$
\|x_w-x^\star\|\le R,\qquad f(x_w)-f(x^\star)\le B,
\qquad B=2^{35}R^2\bigl[(1+h)L_0+L_1\sigma\bigr].
$$

Crucially, the tolerance is independent of target accuracy, and $B$ is polynomial in the parameters. The final solver uses the original $L_0,L_1,\sigma,R$, the certificate $B$, confidence $\delta/2$, and fresh samples. It does not inherit $\lambda$ as its smoothness parameter.

The difficult step is preserving radius and accelerated weight growth despite coarse, adaptive gradient errors. At a large reply norm $s$, generalized smoothness and the minimizer give a positive support surplus of order $s\log(L_1s/\lambda)/L_1$. A directional bisection certifies a sign only outside its noise margin; inside that margin it returns a point with controlled alignment and objective error. Curvature inflation absorbs the remaining $R\zeta$ terms into the descent quantity $D=s^2/(\lambda+L_1s)$. An energy inequality retains both a radius bound and a sum of squared weighted reply norms. A counting argument then forces exit within $O(h)$ accepted steps, independently of the initial objective gap. This is a stability theorem for coarse errors, not an assumption that the oracle already supplies a convergent trajectory.

The supporting proofs explicitly establish the cached-search invariant, descent, surplus, energy, weight counting, finite-variance batch concentration, and the connection to raw execution. The random restart is handled using the abstract IID prefix-tail law and a measurable conditional argument. Every batch sample and fixed-horizon padding call is included. The [budget proof](../Proofs/CoarseGeneralizedBudget.lean) bounds the complete execution by the displayed single formula; the [convergence proof](../Proofs/CoarseGeneralizedConvergence.lean) transfers the probability statement to that execution.

## Closest results and precise improvement

The two closest recent papers are preprints; no conference acceptance is asserted for them.

* [Rudomanov, Fomin, Gasnikov, and Stonyakin, “Descending Everest,” arXiv:2610.21461v1](https://arxiv.org/html/2610.21461v1), Theorem 3.7, proves the exact-gradient radius-only bound $5\sqrt T+240(1+h)\log_2(64(1+h))+2$. Its Lemmas 3.2, 3.4, and 3.5 and Algorithms 1–2 supply the support-surplus, energy, and counting ideas underlying our warm stage. Linear curvature dependence and this deterministic mechanism are already known. The new part is their coarse stochastic stability with a polynomial restart gap and unchanged final statistical cost.
* [El Bakkali El Kadi and Gorbunov, “Acceleration Survives Heavy Tails,” arXiv:2610.23301v2](https://arxiv.org/html/2610.23301v2), Theorem 2 and Remarks 1–2, already give accelerated heavy-tail convergence with an initial-gap-dependent transient. At moment exponent two, the statistical cost is additive $V$, up to logarithms. Their radius-only substitution $\Delta\le L_0(e^h-1-h)/L_1^2$ can produce a quadratic-in-$h$ transient. Treating the initial-gap logarithm as an innocuous logarithm of $h$ would erase the issue addressed here.
* The stronger [existing repository theorem](FiniteVarianceGeneralizedAcceleratedConvex.lean), explained in its [companion note](FiniteVarianceGeneralizedAcceleratedConvex.md), has cost $\widetilde O(1+\sqrt T+L+(hL)^{2/3}+V)$, where $L=\log(4+4\Delta/\varepsilon)$. This is the final solver reused here and is included as a baseline regardless of publication status. In the worst radius-derived gap regime it gives curvature power $h^{4/3}$, rather than $h^2$. The new uniform radius-based bound reduces that power to $h$, up to the explicitly displayed logarithms.

The meaningful separation is in growing-curvature regimes where the initial gap can be exponential in $h$ and $\sqrt T+V$ does not already dominate the old curvature term. At fixed confidence and polynomially scaling remaining parameters, the ratio between the old worst-radius curvature term and the new one grows as $h^{1/3}$ up to logarithms. This is not a universal improvement: with a small supplied initial gap the existing theorem can have an $h^{2/3}$ term, when noise dominates both bounds have leading $V$, and the new constants and logarithms can be much worse. In the zero-noise limit, the deterministic preprint has the sharper logarithmic guarantee. No new deterministic rate, randomized minimax lower bound, practical speedup, or improvement comparable in breadth to the original discovery of AGD is claimed.

## Reductions, assumptions, and scope

The assumptions are those of the existing generalized-smooth convex finite-variance problem; no new restriction on the objective or oracle is introduced. The Hessian growth condition is the one used in the exact-gradient radius analysis above. Unbiasedness and bounded variance are the moment-two case of the stochastic model in the heavy-tail paper. The smoothness formulations must be compared literally: a global asymmetric all-pairs gradient bound is stronger than the Hessian condition used here.

Several obvious reductions do not give the result. Substituting the exponential radius certificate into the strongest existing solver leaves the $h^{4/3}$ term. Localizing ordinary smooth acceleration to the radius ball gives exponential effective smoothness. Estimating every exact gradient to final accuracy can multiply the warm-stage cost by an accuracy-dependent variance cost; exact-gradient sign tests and radius invariants do not survive arbitrary coarse substitutions. The proved coarse-error invariant is what permits a constant-size mean group, logarithmically many groups per query, and a polynomial restart certificate. Composition with the known final solver is standard once that invariant is available; composition, robust means, and IID conditioning are not themselves novelty claims.

[ARC-SG, “Localize, Restart, Accelerate,” arXiv:2609.06555v1](https://arxiv.org/html/2609.06555v1), Proposition 6 and Corollary 3 in Appendix E, is a direct stochastic warm-start comparison under stronger sub-Gaussian noise. Its Phase-I count contains $h\Lambda_{\mathrm{lg}}$, with $\Lambda_{\mathrm{lg}}$ logarithmic in the initial gap, and its tolerance decreases with that logarithm. The default radius certificate makes the count quadratic in $h$ (also stated in Remark 1). Inflating $L_0$ to a polynomial $\lambda$ only subtracts a logarithm of that polynomial from a worst-case gap logarithm of order $h$; it does not remove the quadratic count. Exponential inflation can suppress that logarithm but supplies an exponential restart certificate, restoring the final solver’s gap-dependent cost. Thus inflation, robust batching, and this existing Phase I do not give the coarse warm-start guarantee proved here.

The [August 24, 2026 author-uploaded preprint by Alkousa, Alashqar, and Stonyakin](https://www.researchgate.net/publication/413568957_First-Order_Methods_for_Optimization_Problems_with_Generalized_Smoothness_and_Generalized_Inexact_Oracle), Definitions 2.2 and 3.1, Lemma 6.3, Theorem 6.4, and Remark 6.5, was also checked. It uses a stronger global asymmetric gradient condition and a value-and-gradient inexact oracle. Its radius bound contains accumulated inexactness, with error decreasing as $N^{-3}$ to keep that radius bounded. It does not supply the coarse-error radius-preserving warm start used here. The source is explicitly under revision; an arXiv submission identifier is not a verified published arXiv version.

A nonlinear family illustrating the objective class in arbitrary finite dimension is

$$
f(x)=\sum_i\bigl(\cosh((Mx)_i)-1\bigr)
$$

for a dense invertible matrix $M$. It has interacting coordinates and unbounded Hessian. Since $\cosh t\le1+|\sinh t|$, it satisfies the growth condition with $L_0=\|M\|^2$ and $L_1=\|M\|^2/\sigma_{\min}(M)$. An additive independent mean-zero vector perturbation with finite second moment gives the required oracle. This example illustrates scope, not a separate formalized theorem or evidence of novelty by itself. The Lean proof applies to the full stated nonlinear class, not merely this family or quadratics.

The literature screening used the current date October 26, 2026: official ICML and ICLR 2025–2026 proceedings/OpenReview, NeurIPS 2025 proceedings and the available 2026 accepted-paper listings, roughly two years of arXiv submissions and revisions, and older cited foundations. Accepted status was distinguished from submission and preprint status. The decisive current comparisons above were checked in their primary theorem and proof statements. One older publisher PDF for Ablaev et al., *Automation and Remote Control* 86(9), remained inaccessible; available primary material concerns additional quasar-convex/PL structure and does not establish a matching theorem for the present generic convex class. This is a record of search coverage and limitations, not a claim that search can certify the absence of every unpublished or inaccessible result.
