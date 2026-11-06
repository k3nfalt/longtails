# Acceleration with sharp covariance-dependent confidence under finite variance

The contribution is a high-probability oracle bound for general smooth convex optimization that combines an accelerated deterministic term with separate total-variance and directional-variance terms. The algorithm is a finite Gaussian-mixture method with rolling medoid hints. This is an oracle-complexity result; no polynomial bound on its internal computation is claimed.

## Setup and guarantee

The [setup](../Setups/CovarianceSmoothConvex.lean) considers a differentiable convex function on an arbitrary finite-dimensional real Hilbert space. Its gradient is globally $L$-Lipschitz, $L>0$, and an unconstrained minimizer $x_\star$ satisfies $\|x_0-x_\star\|\le R$. A fresh, jointly measurable gradient oracle satisfies, at every query $x$,

$$
\mathbb E g(x,\xi)=\nabla f(x),\qquad
\mathbb E\|g(x,\xi)-\nabla f(x)\|^2\le\sigma^2,\qquad
\mathbb E\langle v,g(x,\xi)-\nabla f(x)\rangle^2\le s^2\|v\|^2.
$$

Here $0\le s\le\sigma$. The sampling law is abstract IID; it is not prescribed to be a product measure. The specification includes the integrability conditions required by these integrals. It does not assume exponential noise tails, samplewise smoothness, bounded gradients, strong convexity, access to objective values, or sample reuse. The algorithm knows $L,R,\sigma,s,\varepsilon,\delta,x_0$, but not $x_\star$, the true gradient, or the oracle distribution.

For $\varepsilon>0$ and $0<\delta<1$, define

$$
\ell=\log(3/\delta),\qquad
J=\log\!\left(\frac{2^{56}(1+LR^2/\varepsilon+R^2\sigma^2/\varepsilon^2)}{\delta^2}\right),
$$
$$
N=\left\lceil 2^{40}\left[J^2+\sqrt{\frac{LR^2}{\varepsilon}}J+
\frac{R^2(\sigma^2+s^2\ell)}{\varepsilon^2}\right]\right\rceil.
$$

The [public theorem](CovarianceAcceleratedHighProbability.lean) constructs the [configured algorithm](../Algorithms/CovarianceAcceleratedTuned.lean) and guarantees

$$
P\{\varepsilon<f(\mathrm{output})-f(x_\star)\}\le\delta.
$$

The output is measurable. Execution consumes exactly $N$ gradient calls, including all warmup observations. For $R=0$, it returns $x_0=x_\star$; the framework still executes its assigned budget.

The underlying [rate proof](../Proofs/CovarianceAcceleratedRate.lean) establishes, after $k$ warmup calls and $T$ accelerated calls,

$$
f(y_T)-f(x_\star)\le
65536\left[\frac{LR^2k^2}{T^2}+
\frac{R(\sigma+s\sqrt\ell)}{\sqrt T}\right]
$$

outside an event of probability at most $T e^{-7k/32}+2e^{-\ell}$, under the stated tuning conditions. For the public budget, $j=\log(54N/\delta)$, $k=\lceil16j\rceil$, and $T=N-k$. The [budget proof](../Proofs/CovarianceAcceleratedBudget.lean) proves $k+T=N$, $T\ge k^2$, all tuning conditions, and the final accuracy and confidence bounds. The constants are deliberately conservative.

## Algorithm and technical contribution

A finite net of the radius-$R$ ball has mesh $R/T^2$ and includes zero. Gaussian components have centers given by this net divided by a scale $a$. A simplex vector specifies their mixture; its physical mean is $x_0+a\,\mathrm{mean}$. Initialization is the component centered at zero. Each update minimizes a clipped, hint-centered linear loss plus Gaussian-mixture KL divergence, a quadratic penalty on physical-mean movement, and a strictly positive quadratic penalty on simplex-weight movement. The last penalty ensures a unique continuous choice even when grid centers coincide. Its contribution to the initial potential is retained.

The query is the accelerated combination of the previous output and current mixture mean. The hint is the medoid of the last $k$ oracle replies. Only then is one fresh reply requested. The algorithm updates the mixture and the accelerated output using that reply. The returned point is this accelerated physical mean, not an independently selected best iterate. Gaussian integrals are internal computations, not additional oracle samples.

The new estimate controls both exponential signs of the clipping error. Its leading contribution is proportional to

$$
\alpha_t^2R^2s^2+(\alpha_t a)^2\sigma^2,
$$

while the predictable hint-residual contribution is exponentially small in the inverse Gaussian-shift variance. This separates directional confidence from the total noise scale. Smooth coupling then permits acceleration without reinstating a polynomial residual-variance penalty.

All physical queries stay inside the known ball. Their controlled motion makes old replies useful: simultaneously over the run, the hint error is at most

$$
48\sigma+\frac{96LRk}{t+1}
$$

except on an explicitly bounded event. The concentration proof uses predictable masks and two separate exponential processes, one for the log normalizer and one for the comparator error. It never conditions the oracle law on a future good event or treats these two quantities as independent.

For a single Gaussian comparator, the initial KL cost is bounded by squared center displacement, with no logarithm of the grid cardinality. Unconstrained stationarity gives the net approximation error $LR^2/(2T^4)$. The [calibrated guarantee](../Proofs/CovarianceAcceleratedGuarantee.lean) retains this error, both regularizers, initialization, warmup, noise, and confidence terms.

## Closest results and what changes

The comparison concerns objective-gap accuracy with tunable failure probability and counts every gradient observation. It is not a claim that this method improves every existing guarantee in every regime.

* Zhang, Wu, Zhang, and Li, [arXiv:2610.00260v2](https://arxiv.org/html/2610.00260v2), Theorems 2.1–2.2, obtain sharp statistical confidence for nonsmooth convex optimization. Their all-budget upper bound retains a deterministic term of order $GR/\sqrt T$. This preprint is prior work regardless of its stated publication intentions. The present result exploits smoothness to replace that obstruction by an accelerated term, up to logarithms.
* Das et al., [NeurIPS 2024](https://proceedings.neurips.cc/paper_files/paper/2024/hash/10bf96894abaf4c293b205709a98fc74-Abstract-Conference.html), [Theorem 3 and Appendix D](https://arxiv.org/html/2410.20135v1#S4.SS2), analyze smooth convex clipped SGD under a fixed covariance envelope $\Sigma$. Their leading terms include $LR^2/T$ and $R\sqrt{[\operatorname{tr}\Sigma+\sqrt{\|\Sigma\|_{\rm op}}(\sqrt{\operatorname{tr}\Sigma}+LR)\log(\log T/\delta)]/T}$, with additional finite-budget terms. On the common class with trace at most $\sigma^2$ and operator norm at most $s^2$, our bound removes the mixed $s(\sigma+LR)$ confidence dependence and accelerates the deterministic term. Separate scalar moment bounds do not require a supplied common covariance envelope.
* Marsden et al., [NeurIPS 2025](https://proceedings.neurips.cc/paper_files/paper/2025/hash/a1c0bb652b64f99e26b5bcd60ed2c68f-Abstract-Conference.html), [Definitions 4–5 and Corollaries 3–4](https://arxiv.org/html/2510.20745v1#S1.SS1), give cutting-plane guarantees for Lipschitz convex objectives. Their directional sub-exponential parameter is normalized by $1/\sqrt d$: a directional tail scale $b$ corresponds to $\sigma_E=\sqrt d\,b$, so Corollary 3 costs $\widetilde O(d+d b^2R^2/\varepsilon^2)$, with success probability $2/3$. Finite variance alone gives Corollary 4's $\widetilde O(d+d\sigma^2R^2/\varepsilon^2)$. Neither is the present tunable-confidence finite-covariance guarantee; no free confidence conversion is assumed here.

The new result is not obtained merely by inserting acceleration into the earlier Gaussian-mixture estimate. Substituting the same rolling residual into Lemma A.2 of arXiv:2610.00260v2 leaves, in that bound, a term of order $bL^2R^2k^2/T$, where $b=\eta a^2$. Balancing it with $R^2/(bT^2)$ gives $LR^2k/T^{3/2}$. The exponential residual estimate removes this specific obstruction. This is a limitation of that reduction, not a lower bound on the earlier algorithm or problem class.

A standard composition of robust gradient-mean estimation with deterministic inexact acceleration also does not supply the claimed rate: bounding the norm error of every gradient and summing those errors loses martingale cancellation and introduces an extra iteration factor in the statistical sampling cost. The concentration argument here operates on the whole adaptive run instead.

Three acceleration or confidence wrappers were checked explicitly:

* [Kulunchakov–Mairal, NeurIPS 2019](https://proceedings.neurips.cc/paper_files/paper/2019/file/4a1c2f4dcf2bf76b6b278ae40875d536-Paper.pdf), Equation (13), gives stochastic Catalyst a noise cost proportional to $BV/(q^{3/2}\tau\varepsilon)$, where $q=\mu/(\mu+\kappa)$. With $\kappa\asymp L$, $B\asymp1/L$, and constant $\tau$, regularizing at $\mu\asymp\varepsilon/R^2$ leaves an extra $\sqrt{LR^2/\varepsilon}$ multiplying $R^2V/\varepsilon^2$, even if an ideal sharp inner noise quantity $V=\sigma^2+s^2\ell$ is granted. Proposition 6 removes that loss for methods supplying the strongly convex, closed-form-minimizable surrogates satisfying (H1), (H2), and Equation (14). A high-probability endpoint guarantee alone does not supply those surrogate certificates.
* [Carmon et al., ICML 2022, RECAPP](https://proceedings.mlr.press/v162/carmon22a/carmon22a.pdf), Definitions 3.1–3.2, requires both a relative expected proximal-objective error and an exactly unbiased proximal-point estimator with a specified squared-distance bound. Theorem 3.5 is an expected-accuracy result. Their multilevel construction is effective for their relative-error primitive; an arbitrary accurate endpoint does not certify that primitive or preserve directional covariance after a nonlinear proximal map. For independent inner solves with level-$r$ cost of order $2^r$ and squared error of order $2^{-r}$, naive randomized telescoping is at the critical cost–variance boundary: choosing level probabilities cannot make both sums finite. A stronger coupling or oracle-specific construction is not ruled out.
* [Davis et al., JMLR 2021, proxBoost](https://jmlr.org/papers/volume22/20-821/20-821.pdf), Section 5, Corollary 9, and Equation (28), is a valid gradient-only confidence conversion for norm-variance stochastic acceleration. Regularization at $\mu\asymp\varepsilon/R^2$ gives a bound of the form $\widetilde O((\sqrt{LR^2/\varepsilon}+R^2\sigma^2/\varepsilon^2)\ell)$, with additional condition-number logarithms. Thus it provides an important baseline, but multiplies the total-variance cost by confidence; it does not substitute $s^2\ell$ for $\sigma^2\ell$.

These checks identify the missing conditions or actual costs of specific reductions. They are not impossibility statements about all proximal or acceleration wrappers.

The repository's earlier [covariance soft-cut result](CovarianceSoftCutConvex.md) is another distinct benchmark, not a literature citation or evidence that an extension is open. On the overlapping globally Lipschitz class, its operator-variance normalization gives $\widetilde O(d+d s^2R^2/\varepsilon^2)$ at fixed success $2/3$. To obtain tunable confidence, run $M=\lceil\log(2/\delta)/\log3\rceil$ independent copies at accuracy $\varepsilon/2$. The probability that all fail is at most $\delta/2$. A balanced gradient-only comparison tree of depth $H=\max\{1,\lceil\log_2 M\rceil\}$ can combine their outputs through approximate segment minimization with total additive error $\varepsilon/2$: each merge uses scalar median-of-means estimates at tolerance of order $\varepsilon/(RH)$ and $K=O(1+\log_+(GRH/\varepsilon))$ segment bisections, where $G$ is the Lipschitz bound. All generator outputs lie in the radius-$2R$ ball around the initial point; segment minimization and subsequent merges remain in that convex ball. There are fewer than $MK$ such estimates. Allocating failure $\delta/(2MK)$ to each gives selection cost
$$
O\!\left(MK\log(MK/\delta)\max\{1,s^2R^2H^2/\varepsilon^2\}\right),
$$
in addition to all $M$ generation budgets. Consequently this elementary conversion costs, up to logarithms in $d,GR/\varepsilon,\ell$,
$$
d\ell+\ell^2+(d\ell+\ell^2)s^2R^2/\varepsilon^2.
$$
The displayed $\ell$ factors are not suppressed. In the diagnostic regime below the fixed-confidence generation cost is order $d^6$, while this repetition-and-selection guarantee costs order $d^7$. No conversion of this benchmark to the new bound at no extra cost is assumed.

## Improvement regimes and limitations

Ignoring the displayed initialization and deterministic logarithmic terms only when they are dominated, the statistical cost is

$$
\frac{R^2(\sigma^2+s^2\ell)}{\varepsilon^2}.
$$

Against a norm-variance confidence cost $R^2\sigma^2\ell/\varepsilon^2$, its gain is of order $\ell/(1+s^2\ell/\sigma^2)$. For isotropic covariance with $s^2=\sigma^2/d$, this can reach order $\min\{\ell,d\}$. This ratio is not asserted for arbitrary loose upper bounds as an identity involving dimension.

For example, take $L=R=1$, $\sigma=d^{-1}$, $s=d^{-3/2}$, $\ell\asymp d$, and $\varepsilon=d^{-4}$. The displayed budget is $O(d^6)$; its two initialization/deterministic terms are only $O(d^2)$ and $O(d^3)$. Norm-variance high-probability bounds and the finite-variance cutting-plane benchmark have statistical costs of order $d^7$, before their additional factors. A nonsmooth $GR/\sqrt T$ term with constant $G$ requires order $d^8$. Even optimistically deleting the $LR$ contribution from the mixed-covariance expression above leaves a $d^{6.5}$ statistical scale. That last calculation grants a stronger comparison; it is not a claimed published localization theorem.

A concrete nonlinear family is

$$
f(x)=m^{-1}\sum_i\log\cosh\langle a_i,x-x_\star\rangle,
$$

with dense, interacting feature vectors. Its Hessian is bounded by $m^{-1}\sum_i a_i a_i^\top$, and no global strong-convexity modulus is required. Independent centered Student-$t_3$ noise scaled to covariance $\sigma^2I/d$ gives the two variance scales without exponential tails. This family illustrates the assumptions; the theorem covers arbitrary objectives satisfying the setup, not just these examples.

The method may require exponentially many grid components and exact variational/Gaussian-integral computations. Computational efficiency and unknown-parameter adaptation remain unresolved. The deterministic term has logarithmic overhead relative to noiseless accelerated gradient descent. No general optimality theorem, universal superiority claim, or fixed-method restriction is asserted.

Literature comparisons were checked against primary versions available on 6 November 2026, including the two most recent publicly available conference editions in the initial survey and recent arXiv work. In particular, [Yu and Lin, arXiv:2610.33761v1](https://arxiv.org/html/2610.33761v1), Assumption 3 and Section 5, require exponential norm-square control for their high-probability acceleration argument. [Tang et al., UAI 2022](https://proceedings.mlr.press/v180/tang22a/tang22a.pdf), Theorem 3.8 and Section 3.4, do not provide this general finite-covariance accelerated rate: their stronger complexity statement imposes additional symmetry. These differences are substantive oracle assumptions, not differences in notation.
