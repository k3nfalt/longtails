# Global reverse-Fisher GD without a separation threshold

[Lean theorem](SymmetricReverseFisherGlobalGD.lean) · [Setup](../Setups/SymmetricGaussianReverseFisher.lean) · [Algorithm and output](../Algorithms/SymmetricReverseFisherGD.lean)

This result proves global, last-iterate convergence of ordinary gradient descent on the original-noise population reverse Fisher divergence for balanced symmetric two-component Gaussian mixtures. It covers every signal magnitude, including coincident components, and gives logarithmic accuracy dependence when a positive signal lower bound is supplied. Its contribution concerns the dynamics of this score-training objective. It does not improve the best known complexity of Gaussian-mixture estimation over all algorithms.

## Model, oracle, and guarantee

In arbitrary finite dimension \(d\ge1\), the teacher and student are

\[
 p_\mu=\tfrac12\mathcal N(\mu,I)+\tfrac12\mathcal N(-\mu,I),\qquad
 p_\theta=\tfrac12\mathcal N(\theta,I)+\tfrac12\mathcal N(-\theta,I).
\]

Their score is \(s_\theta(x)=\theta\tanh\langle\theta,x\rangle-x\). The setup defines the actual loss

\[
 F_\mu(\theta)=\mathbb E_{X\sim p_\theta}
       \|s_\theta(X)-s_\mu(X)\|^2
\]

as the average of two integrals against the standard multivariate Gaussian. The oracle returns the **full parameter gradient** \(\nabla F_\mu(\theta)\), including the dependence of the sampling distribution on the student parameter. It is not a gradient with that distribution held fixed. One oracle call means one exact population-gradient evaluation; no finite-sample estimator or point-score implementation is asserted.

The public information is \(d,s,B,\varepsilon,\delta\), with
\(0\le s\le\|\mu\|\le B\), \(0<\varepsilon\le1\), and \(0<\delta\le1\).
The lower bound \(s=0\) is allowed. The algorithm does not know the teacher direction or its exact norm. Draw independent coordinates \(Z_i\sim\operatorname{Uniform}[-1,1]\), initialize \(\theta_0=Z/\|Z\|\), and use the first coordinate unit vector when \(Z=0\). This is normalized cube sampling, not uniform-sphere sampling. Run

\[
 \eta=\frac1{48+20B},\qquad
 \theta_{k+1}=\theta_k-\eta\nabla F_\mu(\theta_k),
\]

for exactly

\[
 K=\left\lceil
 10^{15}\frac{(1+B)(1+s^2)}{\max\{s^2,\varepsilon\}}
 \log\!\left(\frac{10^{15}d(1+B)}{\delta\varepsilon}\right)
 \right\rceil
\]

population-gradient calls. The named `output` executes these updates through the repository's `execute` interface and returns the last state. The theorem proves

\[
 \Pr\!\left[
 \min\{\|\theta_K-\mu\|^2,\|\theta_K+\mu\|^2\}\le\varepsilon
 \right]\ge1-\delta.
\]

The probability is the explicit product of the algorithm's cube-coordinate law and the oracle's seed law. Admissibility requires every oracle answer to equal the exact gradient, so oracle seeds do not change the iterate. Output measurability is proved. Initialization uses no gradient calls; its random-coordinate generation and arithmetic are not claimed to have zero computational cost.

The setup's `allowedAlgorithm` enforces a GD update, positive state-dependent step sizes, gradient queries at the represented state, and last-state output. It does not prescribe the particular constant step, initialization, or budget. Those choices belong to the constructed algorithm and proof.

For \(s=0\), the bound is
\(O((1+B)\varepsilon^{-1}\log(e d(1+B)/(\delta\varepsilon)))\).
For \(s>0\) and \(\varepsilon\le s^2\), it is
\(O((1+B)(1+s^{-2})\log(e d(1+B)/(\delta\varepsilon)))\).
Thus the latter regime has geometric accuracy dependence, while the former remains uniform through zero signal. The large universal constant is a proof constant, not a practical iteration recommendation. No matching lower bound or optimality claim is made.

## What changes relative to the closest results

| Primary result | Relevant guarantee and assumptions | Difference here |
|---|---|---|
| [Tyurin, arXiv:2606.19876v1, Theorems 3.2/E.1](https://arxiv.org/html/2606.19876v1) | Same reverse-Fisher objective; arbitrary numbers of independent means, global large-sphere initialization, a dimension condition, and separation depending on target accuracy. The accuracy is squared distance of every student mean to its initially closest teacher, at all iterations beyond the threshold, with probability at least \(1-4\rho\). The displayed bound has an inverse-accuracy term; under the stated scaling Theorem 3.2 summarizes it as \(\widetilde O(n^2/\varepsilon)\). | Avoids a separation threshold and separation-dependent approximation error in the tied balanced two-component subclass, covers all dimensions and zero signal, and yields logarithmic accuracy dependence at fixed positive signal. Tying and initialization change, so this is not a theorem-level superset or a universal speed comparison. |
| [Shah, Chen, and Klivans, NeurIPS 2023](https://proceedings.neurips.cc/paper_files/paper/2023/hash/3ec077b4af90f2556b517b556e186f64-Abstract-Conference.html), [arXiv:2307.01178v1, supplementary Theorem 13 / §D.1](https://arxiv.org/abs/2307.01178v1) | The small-separation two-component result already permits a single **high** noise level, with noise chosen using dimension and accuracy, projected/radius-normalized dynamics, a norm estimate, a positive signal lower bound, and finite-sample guarantees. | Analyzes unprojected full GD at the original fixed noise and includes zero signal. It is not the first single-noise score result and does not improve that paper's sample complexity. |
| [Wu and Zhou, *Randomly initialized EM algorithm for two-component Gaussian mixture achieves near optimality in \(O(\sqrt n)\) iterations*, Mathematical Statistics and Learning 4](https://doi.org/10.4171/MSL/29), Theorems 1–2 | Global random-initialization EM guarantees in the standard symmetric model, including weak-signal statistical rates. | Establishes that the problem class was already globally learnable. The present theorem is about GD on reverse Fisher, not a new globally learnable mixture family or a better statistical estimator. |

The separation-free question is motivated by the limitation discussed in Tyurin's §3.1. The zero-signal endpoint alone overlaps the single-teacher setting of its Theorem 2.1; the contribution is the quantitative interpolation across nonzero overlapping mixtures and the discrete dynamics that preserve it. The exact-gradient oracle is comparable to that population optimization analysis, but it is not interchangeable with the sample or point-score access in other work.

The symmetric, balanced model with known center and covariance is established in mixture optimization research, notably the EM and DDPM references above. It is a substantial restriction. Tying forces coverage of the two antipodal modes, excludes unequal weights and covariances, and changes the basin problem relative to independent student means. It is essential to the current proof. A representative nonlinear family is \(\mu=a(1,\ldots,1)/\sqrt d\), for any \(a>0\): the score couples coordinates through \(\tanh(a\sum_i x_i/\sqrt d)\), and arbitrary student directions evolve through both angle and radius. The theorem is not restricted to scalar, quadratic, or coordinate-separable losses, although rotational symmetry reduces its analysis to two scalar quantities.

## New mechanism and why standard reductions do not suffice

Write \(a=\|\mu\|\), \(r=\|\theta\|\), and \(c=\langle\theta,\mu\rangle\). The proof derives, from the Gaussian integrals rather than assuming a landscape condition,

\[
 F_\mu(\theta)=f(r)+g_a(c),\qquad
 \nabla F_\mu(\theta)=\alpha(r)\theta-B_a(c)\mu.
\]

For the radial force \(K(a,r)\), the central estimate is

\[
 \partial_a K(a,r)\ge
 \frac{\min\{a,1\}\min\{r,1\}}{60},\qquad a,r>0.
\]

Its derivative is a Gaussian expectation of \(2V(ax)+a^2W(ax)\), where \(W\) changes sign. Pointwise positivity is therefore unavailable. The proof establishes a single crossing for \(W\) and a zero weighted integral; monotone reweighting handles \(r\le a\). Polynomial bounds at bounded amplitude and an explicit Gaussian-tail estimate handle the other regimes. Integrating this inequality gives an aligned radial secant bound with no separation-dependent additive error.

The rest of the analysis connects this estimate to genuine finite-step GD. The exact gradient preserves the sign of the signal projection and contracts the angle ratio. An exact cone invariant, followed by a capped-growth recurrence, gives escape from the small-radius region at a fixed time. The radial map is globally 48-Lipschitz. Gaussian Stein identities through third order give \(a^2|B_a'(c)|\le9a\), justifying the chosen step size. After escape, with
\(m=a^2/[100000(1+a^2)]\) and \(R=1+600a\), the parameter error is bounded by
\(148R\,m^{-1}\exp(-\eta m k/960)\).
A separate capped-decay estimate handles \(a^2\le\varepsilon/10000\), including \(a=0\), without division by the signal norm. The normalized-cube bound gives an initial absolute projection at least \(\delta/d\) with probability at least \(1-\delta\). Every auxiliary phase and ceiling is absorbed into the single public budget, which is proved sufficient for the actual final iterate.

The checked standard reductions do not establish the central mismatch inequality. The reverse-Fisher gradient is not generally a positive scalar multiple of the EM direction. Matched Gaussian-channel identities do not provide the required inequality for independently varying teacher and student amplitudes. The squared score mismatch is not monotone in absolute input, so folded-normal stochastic dominance cannot replace the sign-changing-kernel argument. Heat-flow dissipation changes the distributions/noise and does not prove this fixed-noise parameter path. Batching and clipping address noisy gradients, not the missing exact-population geometry. These distinctions are the technical basis for the novelty claim; an unsuccessful keyword search alone is not.

## Scope and verification

This is a method-specific GD contribution in a standard but narrow model. It does not extend to nonhomogeneous variance, unknown covariance, unequal weights, independent untied component means, general multimodal coverage, SGD, or finite-sample score estimation. No claim of improvement over EM or optimal problem-class oracle complexity is made. A stronger point-score oracle can recover the teacher in this special model, so the population-gradient dynamics guarantee must not be interpreted as an information-theoretic lower bound. Dependence on \(B,s,\delta,d\) and the universal constant has not been optimized.

The literature comparison was checked on 2026-10-19 UTC. Both agents independently surveyed the two most recent publicly available ICML and ICLR editions, NeurIPS 2025 and the public 2026 program/downloads, roughly two years of arXiv submissions and revisions, and older foundational results. This was a targeted survey, not an exhaustive proof audit of every proceedings paper. The Tyurin and Shah arXiv records were rechecked for revisions; each listed only v1. Tyurin's conference acceptance was not verified and it is treated as a preprint. Some OpenReview pages were inaccessible; official proceedings/program pages were used for status where available, with primary arXiv texts for theorem comparisons. No unresolved inaccessible source is used as positive evidence for novelty.

The Lean specification contains the Gaussian loss, exact oracle condition, admissible GD family, parameter ranges, probability criterion, and cost model. Supporting proofs derive the integral identities, differentiation, geometry, dynamics, probability, and budget. The public theorem imports the setup directly and uses `Convergence spec budget`; the budget is one explicit line in public parameters. The verification commands are `./build.sh`, `./lint.sh`, and `python3 run_comparator.py SymmetricReverseFisherGlobalGD.lean`. The comparator checks the convergence result and budget with only `propext`, `Classical.choice`, and `Quot.sound` permitted.
