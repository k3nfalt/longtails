# Coupled cubic models under strong growth

The [main theorem](CoupledCubicStrongGrowth.lean) concerns finite-sum second-order stationarity under expected strong growth. Its [setup](../Setups/StrongGrowthFiniteSumSecondOrder.lean) and [algorithm](../Algorithms/CoupledCubicTournament.lean) cover arbitrary finite-dimensional real Hilbert spaces and general nonlinear objectives. The proposed contribution is an accuracy-independent batch size for a stochastic cubic method, obtained by controlling coupled gradient/Hessian errors and selecting models without access to population derivatives. The guarantee has an explicit linear dimension cost; it is not an improvement for unrestricted finite sums or Hessian-vector-product oracles.

Let $F(x)=n^{-1}\sum_{i=1}^n f_i(x)$, $d=\dim E$, and $g_i=\nabla f_i$, $H_i=\nabla^2 f_i$. The assumptions are $n\ge1$, each $f_i\in C^2$, $\kappa\ge1$, $\rho,\epsilon>0$, $\Delta\ge0$, and, for every $x,y\in E$,

$$
\frac1n\sum_i\|g_i(x)\|^2\le\kappa\|\nabla F(x)\|^2,
\qquad
\frac1n\sum_i\|H_i(x)-H_i(y)\|_{\rm op}^2\le\rho^2\|x-y\|^2,
\qquad F(x_0)-F(x)\le\Delta.
$$

Strong growth is an established interpolation-like assumption, substantially stronger than interpolation only at global minimizers: all component gradients vanish at every population stationary point. It is not asserted for arbitrary interpolating neural networks. RMS component Hessian Lipschitzness is implied by the usual common component Hessian-Lipschitz bound, and implies population Hessian Lipschitzness with the same constant. No global gradient-Lipschitz constant, uniform additive Hessian-noise bound, relative light-tail condition, nonsingular Hessian, or Hessian interpolation assumption is imposed. The RMS condition is an additional restriction relative to analyses assuming only population Hessian regularity.

A query chooses a component and point and returns the exact pair $(g_i(x),H_i(x))$. A full Hessian matrix is charged as part of that pair. Charging its gradient and Hessian separately changes costs by a factor of two. Sampling is uniform with replacement, independently across batches and rounds. Population derivatives and spectral bases used in the analysis are not algorithm inputs.

Define

$$
 b=\left\lceil10^{20}\kappa(d+1)\right\rceil,\qquad
 T=\left\lceil\frac{16000\sqrt\rho\,\Delta}{\epsilon\sqrt\epsilon}\right\rceil+1,
 \qquad K=\lfloor\log_2(3T)\rfloor+1.
$$

The returned output $X$, run through the repository's `execute`, satisfies

$$
\Pr\!\left(\|\nabla F(X)\|\le\epsilon\ \text{and}\quad
 \nabla^2F(X)\succeq-\sqrt{\rho\epsilon}\,I\right)\ge\frac23
$$

using $bKT$ paired calls. Thus the oracle complexity is

$$
O\!\left(\kappa(d+1)\left(1+\frac{\sqrt\rho\Delta}{\epsilon^{3/2}}\right)
\log\!\left(3+\frac{3\sqrt\rho\Delta}{\epsilon^{3/2}}\right)\right).
$$

The theorem's public `budget` inlines the entire formula. The constants are deliberately conservative and very large; the comparison is asymptotic, not a practical finite-sample speed claim.

At each point, the algorithm builds $K$ paired empirical models from $b$ component queries each and minimizes each cubic model with cubic term $\rho\|s\|^3/6$. For candidate $j$, it computes
$Q_j(v)=\|\widehat H_jv\|+\rho\|s_j\|\|v\|$.
Two candidates are compatible when, in both anchor directions, their Hessian difference is at most $10^{-6}Q_j(v)$ for every $v$, and their coupled gradient/Hessian difference evaluated at $s_j$ is at most $10^{-6}\rho\|s_j\|^2$. It selects the first candidate compatible with a strict majority. A selected step of norm at most $\sqrt{\epsilon/\rho}/5$ freezes the output. All remaining rounds still issue their $bK$ queries, so the formal budget counts every call. Exact cubic minimization and compatibility tests are uncharged local computations; no arithmetic-runtime guarantee is claimed.

For the true cubic step $s_\star$, write $r=\|s_\star\|$, $H=\nabla^2F(x)$, and $A=|H|+\rho rI$. The new sampling argument uses strong growth at displaced points to derive

$$
\mathbb E_i\|g_i(x)+H_i(x)s_\star\|^2\le\tfrac52\kappa\rho^2r^4,
\qquad
\mathbb E_i\|H_i(x)v\|^2\le64\kappa(\|Hv\|^2+\rho^2r^2\|v\|^2).
$$

A single weighted score for the residual and $d$ Hessian columns yields simultaneous coupled residual and right-relative Hessian control. Zero weights are handled by proving exact zero errors from zero raw moments; they are not discarded. At $r=0$, differentiating strong growth gives the required Hessian moment and kernel annihilation directly.

The nonlinear stability proof converts these errors into radius comparability, objective decrease, and second-order accuracy. Its observable tournament compares the empirical $Q_j$ with the unknown $A$, so a selected model inherits sufficient accuracy from one good neighbor. A batch is good with probability at least $15/16$; majority amplification gives round failure at most $2^{-K}$. A finite-history conditioning proof handles adaptively chosen query points. Each nonstopping certified step decreases $F$ by more than $\epsilon\sqrt\epsilon/(16000\sqrt\rho)$, which forces stopping within $T$ rounds. The [moment](../Proofs/CoupledCubicMoments.lean), [selection](../Proofs/CoupledCubicSelection.lean), [batch](../Proofs/CoupledCubicBatch.lean), [descent](../Proofs/CoupledCubicDescent.lean), and [execution](../Proofs/CoupledCubicRun.lean) modules formalize these steps.

The closest interpolation-like result is Roy–Balasubramanian–Ghadimi–Mohapatra, accepted at [NeurIPS 2020](https://proceedings.neurips.cc/paper/2020/hash/92a08bf918f44ccd961477be30023da1-Abstract.html), [arXiv v1](https://arxiv.org/abs/2009.13016v1). Their Theorem 4.1 gives SCRN complexity $\widetilde O(\epsilon^{-5/2})$; the stronger applicable baseline is PSGD, Theorem 3.1(a), with $\widetilde O(\epsilon^{-2})$, relative sub-Gaussian tails, and population gradient smoothness. The present result adds RMS component Hessian smoothness while avoiding those latter conditions. This is an assumption tradeoff, not a blanket generalization. Their SCRN expected signed-eigenvalue criterion is also different from the joint probability event here. With common smoothness, growth, tail, and gap parameters fixed, the present rate improves the PSGD exponent when $d+1=o(\epsilon^{-1/2}/\log(1/\epsilon))$. PSGD uses the weaker gradient-only oracle; comparisons charge our full-Hessian calls explicitly.

For finite sums without strong growth, Shen–Zhou–Fang–Ribeiro's [STR, arXiv:1903.01540v1](https://arxiv.org/abs/1903.01540v1), Estimator 6, Lemma 5.1, and Corollary 5.1, already supplies total first/second-order complexity $\widetilde O(n+n^{3/4}\sqrt\rho\Delta\epsilon^{-3/2})$. Its $\sqrt n$ Hessian-only count must not be mistaken for total paired cost. On the shared component-smooth subclass, the present dependence improves that bound when $\kappa(d+1)\log(3T)\ll n^{3/4}$, apart from universal constants. It requires strong growth and can be worse outside this regime. For example, with other parameters fixed, $n=\epsilon^{-1}$, $d=\epsilon^{-1/4}$ gives exponents $7/4$, $9/4$, and $2$ for this result, STR total cost, and PSGD, respectively, ignoring logarithms. STR is cited as a preprint; no acceptance status is needed for its priority.

Two recent preprints require separate qualification. [Re3MCN, arXiv:2510.08714v2](https://arxiv.org/abs/2510.08714v2), revised 27 April 2026, reports a total $\widetilde O(n+\sqrt n\epsilon^{-3/2})$ bound under additional gradient smoothness and third-moment Hessian smoothness. We could not validate its Appendix B proof of Lemma 5.4: Algorithm 1, line 11, smooths the previous estimate toward the current SARAH estimate, but the displayed error decomposition omits deterministic lag. For identical quadratic components, the centered innovations vanish and SARAH is exact, whereas the smoothed error obeys $e_t=(1-\alpha_t)(e_{t-1}+g(x_{t-1})-g(x_t))$, generally nonzero. Thus we distinguish its reported rate from an established comparison. Even taking that rate as a benchmark on the shared subclass, our dependence improves in the stricter regime $\kappa(d+1)\log(3T)\ll\sqrt n$; the preceding example remains in this regime. [Higher-order finite sums, arXiv:2609.28202v2](https://arxiv.org/abs/2609.28202v2), revised 19 October 2026, Theorem 3.2, gives the $n^{3/4}$ exponent at order two for first-order stationarity with value-inclusive component jets. Its returned-point criterion does not certify the joint second-order event here. Neither preprint is treated as an accepted conference paper.

The guarantee is not obtained by inserting SGC into classical separate-error cubic bounds. [Kohler–Lucchi, ICML 2017](https://proceedings.mlr.press/v70/kohler17a/kohler17a.pdf), Assumptions 4–5, require separate gradient and Hessian-action errors of order $\|s\|^2$. For $f_i(x)=w_i\lambda x^2/2$, mean weight one, a fixed batch near zero can have both separate errors of order $\|s_\star\|$, while their coupled residual is order $\|s_\star\|^2$ by cubic stationarity. Separate-error batching therefore loses the claimed accuracy-independent batch size. The scalar example diagnoses the reduction obstruction; the theorem and stability argument are not restricted to quadratics.

A nonlinear interacting family is $f_i(x)=\sum_j w_{ij}(1-\cos u_j(x))$, $u_j(x)=x_j+a\sin x_{j+1}$ cyclically, $0<a<1$, mean weights one, $|w_{ij}|\le W$, and mean squared weights at most $\nu$. It has strong-growth constant at most $\nu((1+a)/(1-a))^2$, dimension-independent Hessian-Lipschitz bound $W[(1+a)^3+3a(1+a)+a]$, and genuine saddles. A complementary example is $f_i(x)=\sum_jw_{ij}q((Bx)_j)$, $q(t)=|t|^3-at^2$, $a>0$, the same mean and square-moment weight bounds with nonnegative weights, and $B=I+cS$, where $S$ is the cyclic shift and $0<c<1$. It has $\kappa\le\nu((1+c)/(1-c))^2$, $\rho\le6W(1+c)^3$, and $F_{\min}=-4da^3/27$. Nontrivial weight variance gives unbounded global Hessian-noise variance, and the population gradient is not globally Lipschitz. This second illustration is separable after an invertible linear feature transformation; it is a scope example, not the novelty claim. In both families, initializing all but a bounded number of features at minima keeps the gap bounded as dimension grows.

Searches through 6 November 2026 included available 2025/2026 ICML, ICLR, and NeurIPS catalogs, recent arXiv submissions/revisions, and older applicable results. The cited Roy, STR, and 2026 SGC trust-region versions remain their latest listed arXiv versions. The 2026 [SGC trust-region preprint](https://arxiv.org/abs/2604.14017v1), Theorem 4.7, concerns first-order stationarity, not this second-order guarantee. Some catalog searches timed out and some OpenReview/poster pages were inaccessible; those limitations were recorded during research and were not used as evidence of novelty. No exhaustive priority certification or optimality claim is made. The unresolved comparative risk is an earlier joint-error Newton analysis that already implies the full coupled sampling-and-selection guarantee. The original unrestricted near-optimal finite-sum/HVP question remains outside this specialized result.
