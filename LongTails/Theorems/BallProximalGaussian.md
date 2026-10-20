# Reproducing the Gaussian ball-proximal objective-gap bound

This is a formal reproduction of the headline quantitative result of Richtárik and Li, [*A Sharper Theory of Ball-Proximal Optimization: Convergence and Radius Selection*, arXiv:2609.35147v1](https://arxiv.org/abs/2609.35147v1), 28 September 2026: the Gaussian relaxation in Theorem 3.4, equation (42), and the accuracy budget in equation (43). It claims no new optimization result or improvement over that paper. The target is a preprint; no conference acceptance is asserted.

The public result is [`result`](BallProximalGaussian.lean). It reuses the existing [`ConvexBallProximal.spec`](../Setups/ConvexBallProximal.lean) and the existing [`BallProximal.algorithm`](../Algorithms/BallProximal.lean) without modifying either. The new supporting proofs are in [`BallProximalGaussian`](../Proofs/BallProximalGaussian.lean).

## Problem, information, and output

The objective is any proper closed convex extended-valued function on an arbitrary finite-dimensional real inner-product space, with a minimizer. Lean represents it by a nonempty convex domain `C`, a real-valued `f` on `C`, convexity on that domain, and a closed epigraph. The domain need not itself be closed. A feasible initial point and a minimizer `xstar` satisfy

\[
\|x_0-x_\star\|\le R,\qquad f(x_0)-f(x_\star)\le\Delta,
\]

with `R ≥ 0`, `Δ > 0`. There are no smoothness, strong-convexity, bounded-subgradient, or separability assumptions. These are the objective and oracle assumptions of the paper's attained-minimum setting (Assumptions 1–3), expressed using supplied upper bounds; the stopping convention is discussed below. Choosing a nearest minimizer and the exact positive initial gap recovers `R = D₀` and `Δ = Δ₀`. An optimal start is also covered by any positive gap upper bound.

For fixed `t > 0`, each oracle call returns an exact minimizer over `C ∩ B(x,t)`. The query and reply are points. No objective values, optimum value, subgradients, or radial multipliers are supplied to the algorithm. Starting at `x₀`, the algorithm queries at its previous reply and returns the last reply `x_K`. The existing setup enforces this update and output through `allowedAlgorithm`; the public theorem proves compliance. Updates do not use `R`, `Δ`, or `ε`; only the stopping budget does.

Examples include nonsmooth coupled objectives `max_j(a_jᵀx+b_j)` on compact convex constraint sets, and coercive convex composite objectives with interacting coordinates. Neither the statement nor proof restricts dimension or imposes a quadratic model. Exact ball minimization is the oracle model, not a claim that ball subproblems are cheap in gradient evaluations.

## Reproduced guarantee and exact call budget

The supporting lemma `execution_gaussian` proves, for every horizon `K` and `R > 0`,

\[
f(x_K)-f(x_\star)\le \Delta\exp\!\left(-\frac{2K^2t^2}{R^2}\right).
\]

The public convergence theorem returns a feasible last iterate with objective gap at most `ε > 0` after exactly

\[
K=\left\lceil\min\left\{(R/t)^2,
 (R/t)\sqrt{\frac{\max\{0,\log(\Delta/\varepsilon)\}}2}\right\}\right\rceil
\]

exact ball-oracle calls. For `0 < ε < Δ`, this is equation (43): ceiling commutes with the minimum. The nonnegative logarithm extends it to `ε ≥ Δ`, where zero calls suffice. If `R = 0`, the initial point is already optimal and the budget is also zero. The complexity is dimension independent; its two alternatives are the quadratic finite-termination cap and the Gaussian accuracy bound. All parameters and constants are explicit in the one-line Lean budget.

The execution uses the repository's `execute`. Every update consumes one call, with no hidden batching or inner-oracle cost. Arbitrary time- and seed-dependent exact-oracle tie breaking is allowed; accuracy is proved for every seed realization and then stated almost surely under the framework's explicit product law. This is not a stochastic-noise assumption.

The paper holds its trajectory fixed upon reaching a minimizer. Our fixed-budget point-oracle execution can continue moving among minimizers, and counts those additional calls. Objective monotonicity and minimality ensure that the objective gap remains zero. Thus the last-iterate objective guarantee and sufficient budget agree; identity of stopped trajectories or implementable detection of optimality is not claimed.

## Proof and scope of reproduction

Existing separation arguments derive a positive radial supporting vector from each nonterminal exact ball minimization. Existing squared-distance and objective-progress lemmas give a scalar profile whose work is bounded by `R²` and whose mass is bounded by the objective decrease. Applying the existing logarithmic profile inequality yields the new execution-level lemma

\[
2(Kt)^2\le R^2\bigl(\log\Delta-\log(f(x_K)-f(x_\star))\bigr)
\]

when the terminal gap is positive. Exponentiation gives the Gaussian bound; a nonpositive gap is immediate. The public budget proof combines this inequality with the strict squared-radius bound for a nonterminal execution. These certificates are proved from convexity and exact optimality, not assumed of the oracle. The proof reuses the library's logarithmic-profile argument instead of copying the paper's Jensen proof line for line.

This reproduces the Gaussian part of Theorem 3.4 and its call budget. It does not reproduce the stronger rational factor in equation (42), variable-radius convergence characterization, dimension-dependent self-contraction bound, stationarity and Bregman estimates, adaptive radii, or relaxed updates elsewhere in the abstract and paper.

The earlier [Gruntkowska–Li–Rane–Richtárik paper, arXiv:2502.02002v2](https://arxiv.org/abs/2502.02002v2), Theorem 8.1 and Corollary 8.2, supplies the original convex BPM theory. The repository's existing [`BallProximalSharpProfile`](BallProximalSharpProfile.md) proves stronger profile bounds. This reproduction neither replaces that result nor claims a gain over it. Accelerated ball methods, including [Carmon et al., NeurIPS 2020](https://proceedings.neurips.cc/paper_files/paper/2020/hash/dba4c1a117472f6aca95211285d0587e-Abstract.html), address a different algorithmic guarantee; no problem-class optimality claim is made.

Source checks on 20 October 2026 identified v1 as the latest available version of the target. Targeted searches covered recent ICML, ICLR, and NeurIPS listings and 2024–2026 arXiv work. This is a source-fidelity review, not a claim of exhaustive literature coverage or mathematical novelty.
