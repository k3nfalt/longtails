# Optimal residual complexity with an inexact Jacobian

[Lean theorem](OptimalInexactJacobianMonotone.lean) · [Setup](../Setups/InexactJacobianMonotone.lean) · [Algorithm and output](../Algorithms/NestedAnchoredInexactJacobian.lean)

## Problem and guarantee

Let $F:E\to E$ be differentiable and monotone on an arbitrary finite-dimensional real inner-product space. Assume

\[
\|DF(x)-DF(y)\|\le M\|x-y\|,\qquad
F(x_\star)=0,\qquad \|x_0-x_\star\|\le R.
\]

The public parameters are the initial point $x_0$, positive scalars $M,R,\varepsilon$, and $\delta\ge0$. A single oracle call at $x$ returns the pair $(F(x),J)$ with
$\|J-DF(x)\|\le\delta$. The value is exact. The Jacobian error may be biased, discontinuous, and depend on the entire query history. There is no bound on $\|DF(x)\|$, strong monotonicity assumption, compact-domain restriction, or restriction to a prescribed algorithm family. An affine map is included by supplying any positive upper bound $M$.

`result` constructs `NestedAnchoredInexactJacobian.algorithm`. Its named `output` is the last accepted outer iterate, run using `execute`. It satisfies $\|F(\mathrm{output})\|\le\varepsilon$ within

\[
\boxed{\left\lceil 4194304\left(1+
       (MR^2/\varepsilon)^{2/5}+\delta R/\varepsilon\right)\right\rceil}
\]

combined oracle calls. Every model query, certificate query, and failed radius-guess phase is counted. Execution with the public budget may make additional dummy calls after the output has been frozen; these also fit within that budget. Exact affine linear-system solves and other algebra are free in this oracle model; the bound is not an arithmetic-runtime guarantee.

The proof holds for every admissible oracle seed sequence. The framework expresses its consequence almost surely under the explicit product of the algorithm law and oracle law. This is a pathwise bounded-error result, not a stochastic variance or expectation bound. The setup does not assume unbiasedness, independence, or a sampling-based mechanism for obtaining $J$.

## Contribution and strongest comparisons

The contribution is a **logarithm-free mixed oracle-complexity bound for the standard inexact-Jacobian monotone root problem**. It is not a new polynomial exponent over all compositions of previous methods, nor a claim that a new inner acceleration principle is needed.

| Primary result | Model and accuracy | Comparison |
| --- | --- | --- |
| [Agafonov et al., NeurIPS 2024](https://papers.neurips.cc/paper_files/paper/2024/file/d1ca7877cdaf3201ecfa95b1240f7942-Paper-Conference.pdf), [arXiv 2405.15990v2](https://arxiv.org/html/2405.15990v2), Assumption 2.1, Theorems 3.2 and 6.2 | Exact values and norm-bounded Jacobian error; weak Minty gap on a bounded domain, and a restarted strongly monotone distance guarantee | The weak-gap rate is $O(MD^3/T^{3/2}+\delta D^2/T)$. This is a different accuracy criterion. Its strongly monotone solver is a stronger building block than directly converting that gap bound. |
| [Jiang–Yoon, arXiv 2609.30212v1](https://arxiv.org/html/2609.30212v1), Theorems 3.2, 4.4, and 6.1, Lemma 4.1 | Anchored extra-proximal residual convergence; exact higher derivatives; full-space root problems included | Supplies the outer potential and weighted displacement energy, and an applicable exact-jet lower bound. Its second-order implementation has logarithmic overhead. |
| [Zhang et al., arXiv 2609.23557v1](https://arxiv.org/html/2609.23557v1), Theorems 3.1 and 5.1, Definition 2.2, Lemmas 5.2–5.4 | Exact Taylor tensors, compact convex feasible set, tangent residual | Already removes logarithms in exact higher-order complexity. Generic exact-oracle log removal is therefore not claimed here. Its local Taylor contraction does not directly tolerate arbitrary $\delta$-errors when $\delta$ exceeds the regularization strength. |

The last two sources are September 2026 arXiv preprints; no conference acceptance is asserted for them. The comparison uses their theorem statements rather than treating absence from conference proceedings as evidence of novelty.

A stronger standard-reduction baseline is obtained by placing the strongly monotone VIJI distance solver inside accelerated Halpern or extra-proximal regularization. A shifted-affine finishing step converts distance to a residual certificate without assuming a global bound on $\|DF\|$. This yields the same mixed dependence **up to logarithmic factors**. For example, for regularization strength $\mu$, radius guess $D\ge\tau$, and target residual $\mu\tau$, solving to distance
$e\le\min\{\tau,\mu\tau/[24(\mu+\delta+MD)]\}$ and applying that finisher suffices. The distance solve and radius search retain precision or conditioning logarithms. This is an inferred composition of published results, not a separately published mixed-complexity theorem.

Composite accelerated splitting is another serious comparison. [arXiv 2501.04585v2](https://arxiv.org/html/2501.04585v2), Theorem 4.1 and Corollary 2, and [arXiv 2609.14953v1](https://arxiv.org/html/2609.14953v1), Theorem 3.1, permit monotonicity of the total operator without separately requiring the explicit remainder to be monotone. Freezing a shifted Jacobian leaves a remainder whose Lipschitz bound is local, of order $\delta+Mr$. Thus the inner solver alone is not the novelty claim. The additional argument is a certified localization with an unknown radius, preserving the *actual* radius in the residual numerator, together with the outer energy accounting below. No checked theorem directly supplies the resulting logarithm-free mixed bound through substitution alone.

## Mechanism and cost accounting

Set $Q=MR^2/\varepsilon$, $K=\lceil Q^{2/5}\rceil+1$,
$\lambda=4R/[\varepsilon K(K+1)]$, $a_k=\lambda(k+1)$, and
$A_k=\lambda k(k+1)/2$. At outer step $k$, let

\[
b_k=\frac{a_kx_0+A_kz_k}{A_k+a_k},\qquad
c_k=b_k-\frac{a_kA_k}{A_k+a_k}F(z_k),\qquad
G_k(x)=F(x)+a_k^{-1}(x-b_k).
\]

The next point $y$ is accepted only after querying its exact value and checking
$\|a_kG_k(y)\|\le\|y-c_k\|/2$. No root, derivative of the true operator, or unknown radius is supplied to the algorithm.

For the inner problem let $\mu=1/a_k$ and let $r$ denote the distance from $c_k$ to the zero of $G_k$, used only in the analysis. Try radii
$\rho_j=2^j(\mu+\delta)/M$. Each phase starts afresh at $c_k$ and uses constant-step anchored extra-proximal iterations with

\[
t_j=(128\delta+512M\rho_j)^{-1},\qquad
N_j=\lceil8/(t_j\mu)\rceil+1.
\]

At each inner extrapolation point, a shifted affine model uses $J+(\mu+\delta)I$. The shift guarantees monotonicity and invertibility even for an invalid radius guess. A valid phase, $\rho_j\ge r$, preserves a bounded trajectory and satisfies the relative error condition for its actual nonlinear operator. Crucially, its residual bound is $2r/(N_jt_j)$, retaining $r$ rather than replacing it by $\rho_j$. It therefore certifies the outer step after at most $N_j$ iterations. Invalid phases are capped; no convergence claim is made for them. Any earlier acceptance is safe because it is checked against the true value.

Summing the geometrically increasing phase costs proves at most
$65536(1+\delta a_k+Ma_kr_k)$ calls for an outer solve. With
$s_k=\|z_{k+1}-c_k\|$, the accepted outer steps satisfy

\[
\sum_{k<K}(A_{k+1}/a_k)^2s_k^2\le\tfrac43R^2,
\qquad r_k\le\tfrac32s_k,
\qquad \sum_{k<K}a_kr_k\le4\lambda R\sqrt K.
\]

Since $\sum a_k=2R/\varepsilon$, the total is at most
$65536(17K+2\delta R/\varepsilon)$, dominated by the displayed public budget. This couples certified local work to outer progress without precision logarithms. The accepted-step potential gives the final residual $2R/A_K=\varepsilon$.

The Lean proof separately establishes the model geometry, finite-phase invariant, successful guess existence, first accepted index, outer energy, budget algebra, and equality between the canonical trajectory and actual history-dependent `execute`. `Nat.find` and the exact resolvent appear only in supporting proofs, not in the algorithm's available information.

## Natural instances, regimes, and limitations

The assumptions combine the established Lipschitz-Jacobian monotone class with the norm-error model in Agafonov et al., Assumption 2.1. No structural restriction was added to repair the proof. Known bounds $M,\delta,R$ and target accuracy are tuning inputs; adaptivity to unknown values is not claimed.

A nonlinear interacting-coordinate family is

\[
F(x)=\mu_0x+Sx+\sum_i w_i\tanh(a_i^\top x)a_i-b,
\qquad \mu_0>0,\quad S^\top=-S,\quad w_i\ge0.
\]

Nonorthogonal feature vectors give nonseparable nonlinear interactions. It is monotone, has a unique root, and satisfies
$\operatorname{Lip}(DF)\le2\sum_iw_i\|a_i\|^3$. Any positive public $M$ at least this upper bound is valid. Omitting selected nonlinear Jacobian summands produces
$\|J-DF(x)\|\le\sum_{i\text{ omitted}}w_i\|a_i\|^2$. The public $\delta$ must bound this sum uniformly over the selected subsets and histories; the subset may change discontinuously with point or history. This is a concrete approximation mechanism, not a cumulative-error hypothesis. The example's positive $\mu_0$ guarantees a root but is not required by the theorem. Choosing skew coupling between two blocks and separate nonlinear potentials within the blocks gives the usual convex-concave saddle operator. Dimension is arbitrary; constants depend on the stated norm bounds, not an additional dimension factor. The formal theorem covers the whole class, rather than formalizing only these examples.

The curvature term dominates when
$\delta\lesssim M^{2/5}\varepsilon^{3/5}/R^{1/5}$.
For fixed positive $\delta$, sufficiently small accuracy has $\varepsilon^{-1}$ complexity. The comparison to the strongest composed baseline is removal of logarithmic overhead, not uniform polynomial improvement. The explicit constant is conservative and supports no practical-efficiency claim.

Deterministic worst-case optimality, up to universal constants and the additive one, follows from two existing lower bounds. Jiang–Yoon Theorem 6.1 with $p=2$ and $H=0$ gives the $Q^{2/5}$ term on the full-space root class; its construction uses [Jang–Ryu, arXiv 2607.05947v1](https://arxiv.org/html/2607.05947v1), Lemmas 2.3 and 3.5–3.8. For the other term, [Park–Ryu, ICML 2022](https://proceedings.mlr.press/v162/park22c/park22c.pdf), Theorem 4.6 and Appendix D.2–D.4, supplies an affine nonexpansive-map residual lower bound. Set $F=(\delta/2)(I-T)$ and return $J=0$: the map is monotone, $\|DF\|\le\delta$, and its Jacobian Lipschitz constant is zero. The resulting lower bound is $\Omega(\delta R/\varepsilon)$. An ignored initial query accommodates arbitrary first queries; arbitrary outputs are permitted. The maximum of these lower terms is within a factor two of their sum. These are **deterministic, growing-dimension** statements. Randomized or fixed-dimension optimality, noisy function values, constraints, and arithmetic complexity are not established here. The lower bounds are literature comparisons, not additional newly formalized Lean theorems.

## Search coverage

The independent Researcher and Reviewer searches used the UTC date 2026-11-04. Both surveyed the publicly available 2025 and 2026 ICML, ICLR, and NeurIPS program/proceedings listings, approximately the preceding two years of arXiv submissions and revisions, and older cited foundations. Relevant checks included the exact high-order residual papers above, the October revision [2609.13462v2](https://arxiv.org/html/2609.13462v2), inexact higher-order VI analyses, composite anchored methods, and standard regularization reductions. Official NeurIPS proceedings verify the Agafonov paper; PMLR verifies Park–Ryu. OpenReview challenge pages and some conference endpoints were intermittently inaccessible; accessible official listings and primary arXiv texts were used instead. Search coverage is evidence for the comparison, not a guarantee that all possible unpublished or unindexed analyses have been excluded. The strongest remaining novelty objection is that the localized certification and energy composition are elementary; the claimed contribution is their sharp mixed-complexity consequence under the established full problem class.
