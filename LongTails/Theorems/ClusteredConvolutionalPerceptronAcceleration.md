# Cyclic convolutional perceptron acceleration on interacting residual clusters

This result proves logarithmic dependence on inverse contrast for a simultaneous, two-tap convolutional perceptron on arbitrarily many examples. The examples have a common background and two small, opposite residual clusters. There is no pure-background reference example, injected noise, reference kick, or offline separator construction. The comparison is a **method-dynamics separation from ordinary perceptron**, including perceptron using the same frozen initial convolution filter. It is not a new optimal oracle complexity for unrestricted linear classification.

The [main theorem](ClusteredConvolutionalPerceptronAcceleration.lean) uses the [setup](../Setups/ClusteredConvolutionalPerceptron.lean), [algorithm and output](../Algorithms/ClusteredConvolutionalPerceptron.lean), and [execution/convergence proof](../Proofs/ClusteredConvolutionalPerceptronConvergence.lean). The [explicit instances](../Proofs/ClusteredConvolutionalPerceptronInstances.lean) and [linear lower bound](../Proofs/ClusteredPerceptronLowerBound.lean) establish the matched comparison.

## Problem and information

Let $P$ be cyclic coordinate shift on $\mathbb R^d$, and let $e=d^{-1/2}(1,\ldots,1)$. There are $N$ signed examples, with the binary labels already absorbed into the vectors:

\[
 D_i=\frac{\alpha_i}{\sqrt2}e+\mu u_i,
 \qquad g\le |\alpha_i|\le R,\qquad \langle e,u_i\rangle=0.
\]

Here $d>0$, $N\ge1$, $0<g\le R$, $\mu>0$, and $0<\kappa\le1/4$. There is an unknown center $u_\star$ satisfying

\[
 \|u_\star\|\le\tfrac12,
 \quad \left\|\frac{u_\star-Pu_\star}{\sqrt2}\right\|\ge2\kappa,
 \quad \|u_i-u_\star\|\le\frac\kappa{64}\quad\text{for every }i.
\]

The center is not supplied to the algorithm. It need not be centered; each actual defect is centered. In the original, unabsorbed data, positive and negative residuals therefore lie near opposite centers, while their backgrounds can be nearly identical. The specification allows either sign of $\alpha_i$ and does not require both signs; the separation instances below have both. Its field `samples` is $N-1$.

Define

\[
 \rho=\frac g{4R},\qquad \delta=\left(\frac\mu{4R}\right)^2.
\]

The guarantee requires $\delta\le\kappa^2\rho^8/4096$, equivalently $\mu/R\le\kappa\rho^4/16$. This is a sufficient small-contrast condition from the proof, not a lower bound on the algorithm's capabilities. The cap radius is proportional to derivative separation and is independent of $N,d,\mu$ at fixed $\kappa$. These are specialized clustered-data assumptions, not arbitrary margin separability.

One oracle call chooses an index and a model point and returns the exact signed margin and its full parameter gradient. No sample distribution, expectation, or stochastic approximation is involved. All examples can have distinct, interacting residual directions. The result is dimension independent in its call count; a call returns a gradient with $d+2$ scalar components, so this is not a dimension-independent arithmetic or bit-complexity claim.

## Algorithm and proved cost

The predictor is

\[
 f_{w,v}(D)=\langle w_1D+w_2PD,v\rangle.
\]

The algorithm scans indices cyclically, advancing after every call. When the signed margin is nonpositive, it performs the simultaneous update

\[
 (w,v)\leftarrow(w,v)+\eta\nabla f_{w,v}(D_i),\qquad \eta=\frac1{4R},
\]

using the old point in every component of the gradient. Otherwise it leaves the point unchanged. Initialization is deterministic:

\[
 w_0=\left(\frac{\kappa/8+1}{\sqrt2},\frac{\kappa/8-1}{\sqrt2}\right),
 \qquad v_0=0.
\]

Thus the mean-filter coordinate is $a_0=\kappa/8$, and the difference-filter coordinate is $t_0=1$. This initialization uses the public $\kappa$, not $u_\star$, the labels of unqueried samples, or a contrast-dependent preconditioner. It is not a generic random-initialization theorem.

The last iterate returned by `execute` strictly separates every signed example after

\[
 \boxed{N\left(\left\lceil128\frac{R^2}{g^2}
       \log\frac{16R^2}{\mu^2}\right\rceil+3\right)}
\]

component oracle calls. This is the literal one-line public Lean budget, with natural-number ceiling. It includes correct inspections, not only mistaken updates. No batching, hidden transition cost, preprocessing calls, or uncounted certification pass is omitted. A separator is absorbing, so a fixed-budget execution may continue to inspect examples safely after separation.

## Technical mechanism

Write $a=(w_1+w_2)/\sqrt2$, $t=(w_1-w_2)/\sqrt2$, and $v=qe+\eta\mu z$. For label-absorbed residual features

\[
 p_i=(u_i+Pu_i)/\sqrt2,\qquad r_i=(u_i-Pu_i)/\sqrt2,
\]

the cap assumptions imply $\|p_i\|,\|r_i\|\le1$, $\langle r_i,r_j\rangle\ge\kappa^2$, and $|\langle p_i,r_j\rangle|\le\kappa/8$. Cross terms need not vanish. A mistaken update, with $b_i=\eta\alpha_i$, obeys exactly

\[
 a'=a+b_iq+\delta\langle p_i,z\rangle,\quad q'=q+b_ia,
 \qquad t'=t+\delta\langle r_i,z\rangle,\quad z'=z+ap_i+tr_i.
\]

The proof derives, rather than assumes, a history cone $|a_k|\le(\kappa/8)t_k$. With $T_k=\sum_{j<k}t_j$, it proves

\[
 t_k\ge1,\qquad
 t_k^2\ge\delta(\kappa^2/2)T_k^2,\qquad
 a_k\langle p_i,z_k\rangle+t_k\langle r_i,z_k\rangle
       \ge(\kappa^2/2)t_kT_k.
\]

The quadratic inequality is global: its equality recurrence multiplies the difference of the two sides by $1-\delta\kappa^2/2$, while additional positive signal growth preserves it. It does not keep $t_k$ artificially close to one.

The last inequality forces **every actual mistake** to satisfy $b_i a_kq_k\le0$. Consequently the two background coordinates switch in the contracting direction. For $W_k=|a_k+q_k|+|a_k-q_k|$, a forced two-step contraction and the global quadratic inequality close the cone induction and give

\[
 W_k\le\frac\kappa4(1-\rho^2/2)^{\lfloor k/2\rfloor}
       +\frac{3\kappa}{\rho^2}\delta T_k.
\]

Since $\delta T_k\le(\rho^4/32)t_k$, the forced term is absorbed by the discriminating margin. After $K=\lceil8\rho^{-2}\log(1/\delta)\rceil+2$ mistakes, every margin is positive. The cyclic execution proof charges each noncertifying pass to at least one mistake and bounds all inspections by $N(K+1)$.

This coupled, global argument is the substantive step beyond the two-example spectral calculation and the repository's earlier finite-prefix reference-sample proof. It handles changing, noncommuting example updates without a common residual eigenvector.

## Explicit growing-rank separation

For every $N=2(n+1)$, take $d=N+2$, standard coordinate vectors $E_j$, and

\[
 \kappa=\tfrac18,\quad
 u_\star=\tfrac14(E_0-E_1),\quad
 h_j=\tfrac12(E_{j+2}-E_1),\quad
 u_j=u_\star+\tfrac1{512}h_j\quad(0\le j<N).
\]

These vectors are centered, $\|u_\star\|\le1/2$, $\|h_j\|\le1$, and $\|u_j-u_\star\|\le\kappa/64$. Coordinate $1$ of $(u_\star-Pu_\star)/\sqrt2$ has magnitude $1/(2\sqrt2)\ge1/4=2\kappa$. Coordinate $j+2$ isolates $1/1024$ times the coefficient of $u_j$ in a linear combination; hence the $N$ defects are linearly independent. They share coordinate $1$, and cyclic shifts couple adjacent coordinates. They are not copies of a scalar or two-example invariant subproblem.

Interleave positive examples $e+\mu u_{2i}$ and negative examples $(1+\mu)e-\mu u_{2i+1}$. Their signed versions instantiate the setup with $g=\sqrt2$, $R=2\sqrt2$. The file proves the setup's validity for every $0<\mu\le2^{-20}$, its geometry, the parity-to-sample correspondence, and the residual linear independence.

For ordinary zero-initialized, unit-step perceptron, after $k$ complete pairs the background coefficient is $-k\mu$, and the residual norm is at most $2k\mu$. Before every positive call its margin is nonpositive; immediately after that update the next negative margin is strictly negative. Both thresholded updates are proved to occur whenever $k\mu\le1/4$. Thus separation needs $\Omega(1/\mu)$ calls. The proof uses actual thresholded updates, including the intervening odd state, not a stipulated alternating-error sequence. Any fixed positive linear-perceptron step size is equivalent to unit step by rescaling its zero-initialized weights, so this lower trace also applies at the nonlinear algorithm’s step size $\eta$.

The same conclusion holds when only the readout is trained on the **same frozen initial convolution filter**. Its background response is $\beta=\sqrt2\kappa/8\ne0$, and transformed residual norms are at most $2$. The lower proof requires $\mu\le\kappa^2/512$, which the displayed family satisfies. Therefore the acceleration is not explained by the initialization alone. An exactly differencing frozen filter, with zero background response, is a different and easier comparator.

For example, $N=2^{m+1}$, $\mu=2^{-2m-20}$, $m\ge0$, gives rank $N$, nonlinear cost $O(2^m(m+1))$, and raw and frozen-filter perceptron lower cost $\Omega(2^{2m})$. All distinct examples are visited and mistaken in the slow phase; none are inert padding. More generally the separation is meaningful when $N\log(1/\mu)=o(1/\mu)$, at fixed $\kappa,R/g$. It is not a uniform advantage for all dataset sizes.

## Closest prior results and restrictions

* **Tyurin, ICML 2026**, [official PMLR article](https://proceedings.mlr.press/v306/tyurin26a.html), [arXiv:2512.11587v2, 21 May 2026](https://arxiv.org/html/2512.11587v2): Theorems 5.1–5.2 establish convolutional acceleration and a linear-perceptron comparison for a special two-example construction; Section 6 gives broader model representations, not this arbitrary-$N$ cyclic rate. The shared-eigenprojection proof does not cover independent residual perturbations in both classes. The present result adds genuine dataset size/rank growth, noiseless cyclic simultaneous updates, and a global coupled proof, while imposing a residual-cap model and a specified initialization. It does not extend every assumption or initialization regime in that paper.
* **Existing repository results:** [TwoSampleQuadraticPerceptronAcceleration](TwoSampleQuadraticPerceptronAcceleration.lean) and [NoisyBatchQuadraticPerceptronGlobal](NoisyBatchQuadraticPerceptronGlobal.lean) address, respectively, a special two-example acceleration mechanism and more general noisy-batch global convergence. [ManySampleConvolutionalPerceptronAcceleration](ManySampleConvolutionalPerceptronAcceleration.lean) already treats arbitrarily many derivative-separable defects, but uses a pure reference, a directed kick, and a finite-prefix small-drift analysis. Our residual-cap class and its class are not nested: the new theorem removes the pure reference and kick but adds the cap condition. This is not a blanket stronger result on its broader defect geometry.
* **Cluster modeling:** Li–Soltanolkotabi–Oymak, [AISTATS 2020, Definition 1.1 and Theorem 2.2](https://proceedings.mlr.press/v108/li20j/li20j.pdf), motivates bounded cluster balls. Its unit-normalized, balanced cluster model trains an overparameterized smooth network with fixed output weights and squared loss; its cluster radius and width depend on the cluster covariance eigenvalue. It is provenance for clustering, not an exact match or a corollary yielding this simultaneous short-filter rate. The common-background and derivative-cap conjunction here is explicitly a specialized new model assumption. Chatterji–Long–Bartlett, [JMLR 2021, Theorem 2 and Section 2.4](https://jmlr.org/papers/volume22/20-1372/20-1372.pdf), requires weak correlation of opposite-label cluster centers, unlike these highly correlated raw inputs.
* **Other nonlinear alignment:** Min–Mallada–Vidal, [arXiv:2307.12851v2, 25 March 2024](https://arxiv.org/html/2307.12851v2), studies gradient-flow alignment under signed-pair correlation conditions excluded by the opposite common-background examples. Telgarsky, [arXiv:2208.02789v1, Assumption 3.1 and Theorem 3.2](https://arxiv.org/pdf/2208.02789), studies wide ReLU gradient flow under cone/polar assumptions. Alignment and growing useful features are not new by themselves; the new step here is their discrete coupling to exact switching contraction and finite cyclic call accounting.
* **Stronger linear algorithms remain relevant:** Wang et al., [ICLR 2023, Theorems 2–3](https://arxiv.org/html/2210.09371v1), give accelerated linear-perceptron guarantees with full-data iteration cost. This work does not beat all accelerated, second-order, preprocessed, or adaptive linear methods. The exact gradient oracle can reveal all $N$ samples in $N$ calls, after which unconstrained offline separation costs no further oracle calls. Explicitly removing the known constant background can also make this family easy. Neither caching nor differencing analyzes the stipulated simultaneous perceptron dynamics, so these reductions do not establish the theorem, but they preclude an unrestricted problem-class oracle-optimality claim.
* **Recent logistic and factorized analyses:** [Zhang–Wu–Bartlett, ICML 2025](https://proceedings.mlr.press/v267/zhang25cf.html) concerns large adaptive logistic steps and averaged risk, with margin-dependent burn-in and a fixed output layer in its nonlinear extension. [Gong–Li, arXiv:2610.06675v1](https://arxiv.org/html/2610.06675v1) gives rank/margin-dependent large-step logistic guarantees, not a uniform logarithmic inverse-contrast mistake bound. [Zhang–Peyré, arXiv:2610.09356v1, Theorem 3.6](https://arxiv.org/html/2610.09356v1) uses smooth PL predictor losses and covariance-support conditions; it does not directly apply to the nonsmooth mistake-selected recurrence. Batching those results or substituting a margin parameter does not produce the theorem above. Standard perceptron analysis after freezing the supplied filter retains contrast-dependent geometry; the matched lower trace demonstrates the obstruction directly.

## Search coverage and limits

The Researcher and independent Reviewer surveyed primary sources separately before candidate selection, using 24 October 2026 UTC. Coverage included the publicly available ICML 2025/2026, ICLR 2025/2026, and NeurIPS 2025/2026 listings, targeted arXiv submissions/revisions from roughly October 2024 onward, and foundational references. Conference status was checked through official proceedings where available; October 2026 arXiv papers cited above are preprints, not asserted accepted conference papers. Latest relevant versions and followups were checked, including the revised Tyurin paper, recent clustered feature-learning work, and smooth factorized-gradient analyses.

Some OpenReview pages returned browser challenges. The NeurIPS 2026 listing titled “Fast and slow gradient descent dynamics of logistic regression through weak alignment” did not yield an accessible full source in the survey, so its theorem-level scope was not verified. This is an explicit coverage limitation, not evidence of novelty. The comparison rests on checked primary results and the exact difference in algorithm, assumptions, accuracy, and component-call cost; absence of a search hit alone is not a novelty argument.

Remaining mathematical limitations are the relative cap condition, specialized contrast-independent initialization, conservative small-contrast restriction, noiseless oracle, and worst-case $N$-fold scanning cost. The theorem does not cover arbitrary derivative-separable residuals, stochastic or adversarial oracle errors, general convolution widths, generic random initialization, or an optimal linear-classification oracle rate. Removing these restrictions is not claimed solved.
