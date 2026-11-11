# Accelerated empirical proximal steps under convex strong growth

The [main theorem](StrongGrowthConvexFiniteSumAcceleration.lean) proves expected objective accuracy for a finite sum of smooth convex component functions satisfying the strong growth condition, without strong convexity or quadratic growth. The contribution is a total component-gradient bound with a square-root dependence on the strong growth parameter in its accuracy-dependent term. The algorithm uses reusable component indices, not an oracle supplying fresh stochastic gradients only.

## Problem and guarantee

The [setup](../Setups/FiniteSumStrongGrowthConvex.lean) specifies an arbitrary finite-dimensional real inner product space and

\[
f(x)=\frac1n\sum_{i=1}^n f_i(x),\qquad
\frac1n\sum_i\|\nabla f_i(x)\|^2\leq\rho\|\nabla f(x)\|^2\quad\text{for every }x.
\]

Each component is convex, differentiable, and has an L-Lipschitz gradient. Here n is positive, L>0, rho>=1, epsilon>0, and a minimizer xstar satisfies ||x0-xstar||<=R, with R>=0. These are the usual finite-sum strong growth assumptions; individual convexity is essential to this proof. The mean need not be strongly convex. Strong growth implies that every component has zero gradient at any mean minimizer; component convexity then makes that point a common minimizer. Common minimization is derived, not added as an assumption.

The algorithm knows n,L,rho,R,epsilon,x0 and may query any component gradient at any point, including querying the same component repeatedly. It receives no function values, minimizer, population gradient, or optimization/proximal oracle. No algorithm-family restriction is imposed. Internal randomness is an explicit uniform finite tape, independent of any oracle seed; oracle replies are exact. Thus the result permits continuous decision spaces, although the algorithm's random tape is finite. There is no dependence on dimension in the call bound, and arithmetic and storage costs are not included.

Put r=min(n,ceil(1024 rho)). The theorem's explicit budget is

\[
7000\left(r+\left\lceil\sqrt{rLR^2/\varepsilon}\right\rceil\right)
\left\lceil\log_2\left\lceil2^{32}\rho^5\right\rceil\right\rceil.
\]

The inner ceiling rounds to an integer; the outer ceiling logarithm is implemented by `Nat.clog`. Executing the named algorithm within this budget returns its **last primal iterate** X and proves measurability, integrability, and

\[
\int(f(X(\omega))-f(x_\star))\,dP(\omega)\leq\varepsilon.
\]

P is the explicitly constructed private-tape measure times the oracle-seed measure in `execute`; no hidden choice of a probability law is used. The bound is O((r+sqrt(rLR^2/epsilon)) log(2+rho)). This is an expected guarantee, not a high-probability claim or a lower bound. Constants are conservative, and there is no claim of optimality.

## Algorithm and counted execution

[EmpiricalProximalAcceleration](../Algorithms/EmpiricalProximalAcceleration.lean) sets mu=1024 L/r and lambda=1/mu. Starting with A=0 and x=z=x0, each outer step sets

\[
a=(\lambda+\sqrt{\lambda^2+4\lambda A})/2,\qquad
v=(Ax+az)/(A+a).
\]

It draws r independent uniform component indices, with replacement, and forms the empirical objective fB. When r=n it enumerates all components instead, eliminating sampling error. It approximately minimizes fB(w)+mu||w-v||^2/2 with Katyusha, using fresh independent inner indices. Its prescribed relative expected subproblem-gap tolerance is delta=1/[2^20 rho(1+L/mu)^4]. No gap evaluation or stopping test is required. It then explicitly queries all r batch gradients at w to compute h=grad fB(w), and updates (A,x,z) to (A+a,w,z-a h).

The number of outer steps is 1+ceil sqrt(4 mu R^2/epsilon). The extra step also covers R=0 without a separate execution branch. The Katyusha tuning parameter equals one. Each inner solve uses 12 ceil-log2 ceil[14*2^20 rho(1+L/mu)^4] epochs, with 9r charged component calls per epoch. This includes dummy gradient calls used by the query-plan translation for quadratic proximal operations, whose answers are ignored and whose outputs are computed arithmetically. The subsequent empirical gradient costs another r calls. These costs, and any padding in `execute`, fit the displayed budget. [Execution](../Proofs/EmpiricalProximalExecution.lean) identifies the query program's returned point with the mathematical iterate; [Parameters](../Proofs/EmpiricalProximalParameters.lean) proves the simplified public budget dominates its execution cost.

## New proof mechanism

The obstacle is that an empirical proximal point depends on the same batch whose gradient supports the outer step. Treating that gradient as unbiased at the adaptive point is invalid. Moreover, adding a deterministic quadratic around x0 generally destroys strong growth at the shifted minimizer, so the existing strongly convex strong-growth theorem cannot simply be regularized.

The proof controls the adaptive empirical support error and approximate proximal residual together. Let yB be the exact empirical proximal point, y the population proximal point, w the computed point, D=||v-y||^2, and H=E||grad fB(w)||^2. Finite-sample replacement stability, individual convexity, and strong growth give, for the selected batch size,

\[
E\|y_B-y\|^2\leq D/1024,\qquad
E[f(y_B)-f_B(y_B)]\leq\mu D/64.
\]

Both errors are zero in the full-sum branch. The inner solve gives

\[
(L+\mu)^2 E\|w-y_B\|^2\leq\mu^2D/2^{20}.
\]

The [certificate](../Proofs/EmpiricalProximalCertificate.lean) then establishes

\[
G:=E[f(w)-f_B(w)]\leq\lambda H/4,\qquad
E\|\lambda\nabla f_B(w)+w-v\|^2\leq\lambda^2H/16.
\]

The key displacement closure is D<=8 lambda^2 H; it converts stability and solver errors into a charge against the same actual-gradient energy decrease used by acceleration. Fixed pre-batch comparator terms are unbiased, whereas the adaptive-point term is handled by G. A Young inequality charges the residual another lambda H/4. Both charges fit the negative lambda H/2 term in the accelerated potential. Consequently [Convergence](../Proofs/EmpiricalProximalConvergence.lean) proves

\[
E[f(x_K)-f(x_\star)]\leq 2\mu\|x_0-x_\star\|^2/K^2.
\]

The argument derives each error from the oracle and objective assumptions. Stability, accelerated potentials, and Katyusha are established ingredients; the contribution is their adaptive empirical-support closure and the resulting merely convex total-call guarantee, not a claim to invent those ingredients.

## Closest comparisons and scope of novelty

Write T=LR^2/epsilon and suppress logarithmic factors only in the following comparisons. The improvement concerns regimes with rho much smaller than n and T. It is not a uniform improvement over every competing guarantee.

* [Hermant et al., ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/hash/cf5e02e94c2804af895ade10be1be00b-Abstract-Conference.html), [arXiv 2410.07870v3](https://arxiv.org/abs/2410.07870v3), Theorem 3, equation (8), gives the convex accelerated strong-growth dependence rho sqrt(T). Increasing batch size reduces its iteration parameter but leaves the linear rho factor in total component calls. The present algorithm changes the method and uses repeated access to an empirical batch.
* [SHANG++, arXiv 2603.09355v2](https://arxiv.org/abs/2603.09355v2), August 2026, Theorem 2.3 (the convex theorem), also has linear rho dependence at norm-normalized expected objective accuracy. Its initial-potential parameter scales with rho squared. The published article is in [Computers & Mathematics with Applications 220 (2026)](https://doi.org/10.1016/j.camwa.2026.07.033). Its strong convexity theorem is Theorem 2.2 and is not used as a convex baseline.
* Generic accelerated finite-sum optimization yields n+sqrt(nT), up to logarithms, without requiring strong growth. For example, [Katyusha, JMLR 2018](https://jmlr.org/papers/volume18/16-410/16-410.pdf), Corollary 3.5, gives n log(initial-gap/epsilon)+sqrt(nT) via adaptive regularization; its direct Theorem 4.1 has a different initial-gap term and should not be substituted for that corollary. The full-sum branch of this result recovers that parameter dependence with an additional log(2+rho) factor. In the small-rho regime it replaces n by O(rho), at the price of assuming strong growth. Ordinary interpolation-based convex SGD gives O(T) calls; [Woodworth and Srebro, NeurIPS 2021, arXiv 2106.02720v2](https://arxiv.org/abs/2106.02720v2), including its interpolation minibatching analysis, does not turn accelerated parallel rounds into the claimed smaller total-call bound.
* The existing repository [strongly convex finite-sum result](StrongGrowthFiniteSumAcceleration.lean) achieves the analogous r+sqrt(rL/mu) dependence when the mean is strongly convex. The present result removes that assumption, changes the outer potential and gradient update, and proves a last-primal objective bound. Standard regularization changes the minimizer and introduces nonzero component gradients there. Strong growth is then lost; restarting the old distance contraction alone has a radius floor rather than the required objective-accuracy guarantee. No such reduction is being claimed.
* The repository's [ProximalStormStrongGrowth](ProximalStormStrongGrowth.lean) gives, up to logarithms, rho+rho^(3/4) sqrt(Lbar R^2/epsilon), under a broader mean-square-smooth stochastic model with same-sample gradient pairs. On the present subclass Lbar<=L. This theorem improves the rho exponent to 1/2 when the relevant smoothness scales are comparable, but requires individual convexity and reusable selectable component access. It is not an improvement for the broader stochastic class. Smaller Lbar can favor the older guarantee.

For example, let rho=q, n=q^3, T=q^3. Ignoring logarithms and universal constants, the new bound is q^2, compared with q^(9/4) for the last stochastic bound when Lbar=L, q^(5/2) for direct strong-growth acceleration, and q^3 for interpolation SGD or generic finite-sum acceleration. This is a polynomial improvement in a specified common-assumption regime. Large constants, logarithms, small T, smaller Lbar, or rho comparable to n can remove a numerical advantage. The factor rho^(1/4) over the strongest checked stochastic comparison is smaller than the factor sqrt(rho) over direct acceleration and should not be conflated with it.

Existing stochastic proximal analyses are also relevant. [Wang, Wang and Srebro, COLT 2017](https://proceedings.mlr.press/v65/wang17a.html) analyze minibatch proximal methods with different loss assumptions and an unaccelerated outer argument. [Yuan and Li, arXiv 2301.03125](https://arxiv.org/abs/2301.03125), Lemma 3, establish smooth minibatch-proximal stability, but not the displacement-scaled support/residual certificate above. [Chadha, Cheng and Duchi, arXiv 2101.02696v1](https://arxiv.org/abs/2101.02696v1) analyze accelerated approximate proximal models with additive noise and a population-smoothness-limited step; their separate interpolation discussion does not provide this total-call guarantee. [Tovmasyan et al., arXiv 2502.03401v2](https://arxiv.org/abs/2502.03401v2), Theorems 5.3–5.4 and 6.3–6.4, respectively treat unaccelerated convex and strongly convex star-similarity regimes. The strong convexity used in the latter proofs cannot be dropped by reading a shortened statement alone.

A claimed square-root-rho stochastic acceleration in an older version of [Mishkin et al., arXiv 2404.02378](https://arxiv.org/abs/2404.02378v2) was explicitly withdrawn in v2 because of an error in equation (6). Its valid equation (5) uses exact population-gradient information. It therefore is not a valid same-oracle competing theorem. This correction matters to the novelty comparison.

## Nonlinear instances and assumption necessity

A family in arbitrarily large finite dimension illustrates that strong growth does not supply hidden strong convexity. Write x=(t,u), choose nonorthogonal vectors vj spanning the u-space, and put

\[
a(t)=Lt^2/2,\quad b(u)=c\sum_j\phi(\langle v_j,u\rangle),\quad
\phi(s)=s^2/2-\log\cosh s.
\]

For an integer q>=1, let a fraction 1/q of the components equal a+q b and the remaining components equal a. Choose c>0 with q c sum_j ||vj||^2<=L. Since phi''=tanh^2 lies in [0,1], all components are smooth convex. The mean is a+b and has unique minimizer zero. Its Hessian vanishes in the u-directions at zero, so neither positive global strong convexity nor quadratic growth holds. The nonorthogonal directions interact nonlinearly. Strong growth holds with rho=q, tightly on t=0 and u nonzero. The common t-direction makes the component, population, and mean-square smoothness scales equal to L. Taking n=q^3 realizes the comparison regime above. This example establishes coverage and compatible parameter scales, not a lower bound: its duplicate component types may admit specialized algorithms.

Every substantive setup condition has a role. Individual convexity supplies empirical monotonicity, replacement stability, and supporting hyperplanes. Global strong growth turns population proximal gradients into batch variance bounds and implies common minimization. Exact component access permits repeated optimization of a fixed empirical objective. The radius bound supplies the initial accelerated potential; L and rho supply explicit solver and batch tuning. The proof does not establish the result under population convexity alone, local strong growth alone, additive noise, an unknown radius, or fresh-only stochastic access. Removing any of these conditions would require a new argument. There is no additional bounded-domain, bounded-gradient, finite-decision-space, quadratic, or separability assumption.

## Literature coverage and limitations

Researcher and Reviewer independently surveyed the publicly available 2025 and 2026 ICML, ICLR and NeurIPS editions and approximately the preceding two years of arXiv submissions and revisions as of 11 November 2026 UTC, then followed foundational references and relevant corrections. The comparisons above use the latest checked versions, rather than historical proposal verdicts. Conference acceptance and preprint status were distinguished.

One access limitation remains explicit: the accepted NeurIPS 2026 OpenReview record [wx2qpHOXO8](https://openreview.net/forum?id=wx2qpHOXO8), “From Inexact Gradients to Byzantine Robustness: Acceleration and Optimization under Similarity,” returned HTTP 403/ChallengeRequired through both the page and public API. The accessible [arXiv 2602.03329v1](https://arxiv.org/abs/2602.03329v1) uses global aggregation/proxy information and does not supply this total component-call guarantee. The inaccessible accepted manuscript has not been checked; this limits exhaustive novelty assurance. No proof of an optimal lower bound, empirical performance advantage, tunable-confidence conversion, or guarantee outside the stated oracle model is claimed.

The formal theorem and supporting proofs establish the upper bound. Mathematical significance rests on its merely convex regime and polynomial total-call improvement, not on formalization alone.
