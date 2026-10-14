# Exact worst-case profiles for fixed-radius ball-proximal optimization

This result characterizes the finite-horizon worst case of the unchanged, exact ball-proximal point method over proper closed convex objectives. Its main contribution is an exact scalar feasibility characterization, including a matching family of coupled nonlinear objectives. An explicit last-iterate oracle budget follows from that characterization. The budget improves the leading constant of the strongest applicable dimension-free gap analysis in specified regimes; it does not improve its asymptotic complexity order.

The public theorem is [`result`](BallProximalSharpProfile.lean), for the [`ConvexBallProximal` specification](../Setups/ConvexBallProximal.lean) and [`algorithm`](../Algorithms/BallProximal.lean). The exact characterization and the matching families are proved as supporting lemmas in [`BallProximalExact`](../Proofs/BallProximalExact.lean), [`BallProximalRealization`](../Proofs/BallProximalRealization.lean), and [`BallProximalSharpness`](../Proofs/BallProximalSharpness.lean).

## Problem, oracle, and returned point

Let the ambient space be any finite-dimensional real inner-product space. The objective is a proper closed convex extended-real function, represented in Lean by a feasible domain `C`, a real-valued function `f` on that domain, convexity on `C`, and a closed epigraph. The domain need not be bounded or closed separately. Assume an attained minimizer `xstar`, a feasible starting point, and bounds

\[
\|x_0-x_\star\|\le R,\qquad f(x_0)-f(x_\star)\le\Delta,
\]

where `R ≥ 0`, `Δ > 0`. The radius `t > 0` and requested objective accuracy `ε > 0` are public. There is no smoothness, strong convexity, Lipschitz-gradient, bounded-gradient, error-bound, or separability assumption.

One oracle call at `x` returns an exact minimizer of `f` over `C ∩ B(x,t)`. It returns only a point. The algorithm repeatedly queries at its previous reply and returns `x_K`. It receives neither the optimum value nor subgradients, radial multipliers, or an additional projection oracle. The setup's `allowedAlgorithm` is equality to this algorithm, and the main theorem proves compliance. Thus the theorem formally restricts both the update family and the last-iterate output rule.

This is the ball-proximal point method, not the linearized local oracle of BroxGD. It addresses the ball-proximal operator that underlies that research program. Exact ball subproblems may themselves be expensive: the cost model counts each exact point-oracle call as one, and makes no gradient-evaluation or arithmetic-cost claim for solving it. A run with budget `K` makes `K` calls, including any calls after an optimum has already been reached. Arbitrary admissible time- and seed-dependent tie breaking is allowed. Accuracy holds for every seed realization, hence also almost surely under the framework's oracle law.

## Explicit convergence guarantee

Write `D = R/t` and `r = ε/Δ`. The proved call budget is

\[
K=\left\lceil\min\left\{D^2,
D\sqrt{\min\{1/2,\max\{0,1-r\}\}^2
       +\tfrac12\max\{0,\log(1/(2r))\}}\right\}\right\rceil.
\]

After these calls, `f(x_K) − f(xstar) ≤ ε`. The Lean `budget` expands the complete expression directly in public parameters on one line. It includes the finite-termination cap and uses no unspecified tuning constant. In particular it is zero if `ε ≥ Δ` or `R = 0`.

Before the termination cap, the bound is `ceil(D(1-r))` for `1/2 ≤ r < 1`, and `ceil((D/2) sqrt(1+2 log(1/(2r))))` for `0 < r < 1/2`. The proof splits an objective-gap profile for analysis; the algorithm never restarts or changes its radius.

## Exact finite-horizon characterization

Normalize the radius and initial objective gap to one. Fix `K ≥ 1` and terminal gap `0 < r < 1`. For positive nonincreasing numbers `a_0,…,a_{K−1}`, define

\[
F_K(a,r)=K+2\sum_{0\le i<j<K}\frac{a_j}{a_i}
       +2r\sum_{i=0}^{K-1}\frac1{a_i}
       +\left(\frac r{a_{K-1}}\right)^2.
\]

There exists an admissible ball-oracle execution with initial gap exactly one, terminal gap exactly `r`, and initial squared distance to a minimizer at most `S` **if and only if** there exists such a profile with

\[
\sum_i a_i=1-r,\qquad F_K(a,r)\le S.
\]

The same equivalence holds with `sum a_i ≤ 1-r`. The latter is a convex feasibility problem after substituting `a_i = exp(z_i)`: the order constraints are linear, the mass constraint is a convex exponential sublevel set, and the displayed objective is a positive sum of exponentials of affine functions, plus a constant. The mass equality itself is not convex in these coordinates. Uniformly scaling the slopes up to saturate the mass constraint preserves their ordering and decreases the energy, proving equivalence of the two formulations.

Lean proves both execution/feasibility equivalences and the profile-energy expansion. The elementary log-coordinate interpretation above is an explanation of the scalar formulation, not a claim that a numerical optimizer, optimizer uniqueness, or convex-program solver has been verified. No attainment assumption is needed for either equivalence. If `Φ_K(r)` denotes the infimum of `F_K` over the profiles, it describes the infimum required squared distance; the feasibility theorem is stated with an actual feasible profile, avoiding an unproved equality-boundary attainment assertion.

The upper direction covers all dimensions and all objectives in the specification. The reverse direction realizes every feasible profile in dimension at most `K`. It does not merely match a particular rate on scalar or quadratic examples.

## Proof mechanism and nonlinear matching instances

At every nonterminal exact ball step, convex separation supplies a radial supporting vector `g_i = a_i u_i`, where `u_i = x_i−x_{i+1}` has unit norm. This certificate is derived from ball optimality in [`BallProximalSupport`](../Proofs/BallProximalSupport.lean); it is not an extra oracle assumption. Consecutive support inequalities show that the `a_i` decrease. Objective progress, the squared-distance telescope, and the terminal supporting inequality yield `R² ≥ F_K(a,r)`. Retaining the terminal term is essential.

The reverse construction uses unit vectors with

\[
\langle u_i,u_j\rangle=a_j/a_i\quad(i\le j).
\]

A triangular square-root construction proves that this Gram matrix exists, including repeated slopes. Set

\[
x_i=\sum_{j=i}^{K-1}u_j+(r/a_{K-1})u_{K-1},\qquad
f(x)=\max\{0,\max_j a_j\langle u_j,x\rangle\}.
\]

These are continuous convex finite max-affine objectives with interacting coordinates. Their values satisfy `f(x_i)=r+sum_{j≥i}a_j`, zero is a nearest minimizer, and `||x_0||²=F_K(a,r)`. The active radial support makes `x_{i+1}` the unique radius-one minimizer centered at `x_i`. The Lean proof also constructs a valid oracle at every other query point by compact-ball minimization and connects its actual `execute` output to this finite prefix. No claim is made that the displayed constant extension of the points after `K` is a BPM trajectory.

For the explicit bound, a logarithmic-mean inequality controls the part of a scalar gap profile above `2r`. A separate terminal-energy inequality controls the remainder. Splitting an interval fractionally preserves the energy exactly. This gives a sharper leading envelope than discarding either the terminal-distance relation or the within-profile structure.

## Sharp leading behavior

For `1/2 ≤ r < 1`, constant slopes attain

\[
\Phi_K(r)=K^2/(1-r)^2.
\]

For fixed `0 < r < 1/2`, put `h=log(1/(2r))`. The supporting proofs establish

\[
\frac{4K^2}{1+2h}\le\Phi_K(r)
\le\frac{4K^2}{1+2h}+K+4+\frac2h
\]

whenever `ceil(K/(1+2h)) < K`, which holds in particular when `2hK ≥ 1+2h`. The upper construction uses `m=ceil(K/(1+2h))`, `n=K−m`, `q=exp(−h/n)`, geometric prefix slopes `(1−q)q^i`, and `m` constant tail slopes `r/m`. It has exact energy `n(1+q)/(1−q)+4m²`; `exp(h/n) ≥ 1+h/n` gives the displayed finite remainder.

Consequently the leading coefficient is sharp as `K` grows at a fixed gap ratio. The remainder is not uniform as `r` approaches `1/2`, and this statement must not be transferred to an arbitrary joint limit where `r` depends on `K`. The explicit low-gap envelope is not asserted to equal `Φ_K(r)` at finite `K`.

## Closest results and what changes

The strongest directly comparable baseline is Richtárik and Li, [*A Sharper Theory of Ball-Proximal Optimization: Convergence and Radius Selection*, arXiv:2609.35147v1](https://arxiv.org/abs/2609.35147v1), 28 September 2026. It uses the same proper closed convex class and exact predecessor-centered ball oracle. Theorem 3.4 gives the Jensen gap bound and its Gaussian relaxation. Remark 3.5 retains final distance and gives the stronger implicit restriction

\[
r^2+\frac K S\frac{1+r^{1/K}}{1-r^{1/K}}\le1.
\]

That remark identifies exact sharpness as unresolved. The contribution here is the exact profile characterization and its complete nonlinear realization, rather than another formalization of that restriction. Its fixed-`r`, large-`K` call coefficient is `sqrt((1−r²) log(1/r)/2)`; our sharp leading coefficient is `1-r` above one half and `sqrt((1+2log(1/(2r)))/4)` below it. The gain against this stronger baseline is modest—for example about 4.26% at `r=0.2`—and is a constant improvement, not an order improvement. The exact characterization improves the description of the worst case. The simpler explicit envelope does **not** uniformly dominate the published finite-`K` implicit inequality: at `K=1` that inequality is already exact.

The same paper's Theorem 4.5 gives dimension-dependent `O_d(1+R/t)` termination. It can outperform our dimension-free budget for fixed small dimension and high accuracy. Our lower constructions allow the dimension to grow with `K`; they neither supersede that theorem nor determine its sharp dimension dependence.

Gruntkowska, Li, Rane, and Richtárik, [*The Ball-Proximal (=“Broximal”) Point Method*, arXiv:2502.02002v2](https://arxiv.org/abs/2502.02002v2), Theorem 8.1 and Corollary 8.2, establish the underlying convex contraction and finite-termination theory. These assumptions and the algorithm are inherited, not newly introduced here. [*Broximal Gradient Descent*, arXiv:2605.08850v2](https://arxiv.org/abs/2605.08850v2), studies a different, linearized ball-constrained subproblem; our theorem does not imply a new BroxGD gradient-oracle rate.

Standard proximal-point reductions do not provide the exact characterization. Substituting the BPM radial multiplier into the PPA objective estimate of Taylor, Hendrickx, and Glineur, [*Exact Worst-Case Performance of First-Order Methods for Composite Convex Optimization*, SIAM Journal on Optimization 2017](https://doi.org/10.1137/16M108104X), Theorem 4.1, and using Cauchy–Schwarz yields a rational bound of the form `r ≤ S/(S+4K²)`, which loses the interpolation structure and matching instance construction. Gu and Yang, [*Tight Convergence Rate in Subgradient Norm of the Proximal Point Algorithm*, arXiv:2301.03175v1](https://arxiv.org/abs/2301.03175v1), Theorem 4.1 and Corollary 4.2, also give the sharp PPA terminal-subgradient bound `||g_K|| ≤ R/(sum α_i)`. With BPM multipliers `α_i=1/a_i`, this restricts `a_{K−1} sum_i 1/a_i`; it does not retain the objective-gap profile or give the required sufficiency construction. The new step is proving that the full scalar energy constraints are sufficient for a convex instance, not just necessary inequalities. Batching, clipping, regularization, and composition do not alter this deterministic exact-oracle problem without changing its oracle or algorithm.

Accelerated ball methods must also be distinguished. Carmon et al., [*Acceleration with a Ball Optimization Oracle*, NeurIPS 2020](https://proceedings.neurips.cc/paper_files/paper/2020/hash/dba4c1a117472f6aca95211285d0587e-Abstract.html), Theorem 6, obtains a better radius exponent using a smooth strictly convex full-space problem and additional gradient information. Carmon et al., [*Thinking Inside the Ball: Near-Optimal Minimization of the Maximal Loss*, COLT 2021](https://proceedings.mlr.press/v134/carmon21a.html), Definition 1 and Theorem 2, removes the smoothness/gradient requirement for globally Lipschitz finite convex objectives but uses a richer oracle for arbitrary quadratically regularized ball subproblems. These are important faster algorithms in their respective models. No minimax-optimality claim over all algorithms or richer oracles is made here.

Literature checks used the current UTC date, 11 October 2026, covering ICML and ICLR 2025/2026, NeurIPS 2025/2026 public paper listings with 2024 proceedings also checked, and approximately October 2024–October 2026 arXiv submissions and revisions, followed by older proximal-point and accelerated-ball sources. The NeurIPS 2026 public listing was available while its completed proceedings endpoint was not. The September 2026 sharper-BPM and BroxGD revisions are treated as preprints, not asserted conference acceptances. Search coverage and independent review exchanges are kept outside the repository. The comparisons above describe checked theorem scopes; they do not claim an exhaustive proof that no unlocated prior result exists.
