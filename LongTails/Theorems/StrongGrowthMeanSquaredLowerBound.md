# Tight complexity of strong-growth convex optimization with a same-sample mean-squared-smooth oracle

The [lower theorem](StrongGrowthMeanSquaredLowerBound.lean) and the companion [upper theorem](StrongGrowthMeanSquaredUpperBound.lean) determine, up to one factor $\log(e(1+\Gamma))$ and universal constants, the expected-accuracy oracle complexity of convex optimization under the strong growth condition when each oracle call returns the stochastic gradients of one fresh sample at two query points and the oracle is mean-squared smooth:

$$
\Theta\!\Big((1+\Gamma)^{3/2}\sqrt{\bar L R^2/\varepsilon}\Big)
\quad\text{up to }\log(e(1+\Gamma)),\qquad
\text{whenever } 2^{26}\sqrt{1+\Gamma^2}\,\varepsilon\le\bar L R^2 .
$$

The new mathematical statement is the all-algorithm lower bound for this oracle class. The upper bound is the repository's earlier [ProximalStormStrongGrowth](ProximalStormStrongGrowth.lean) theorem, transferred through a formal inclusion. The hard oracle is the known Bernoulli masking construction. The contribution is therefore the closed characterization of this class, showing that the proximal-STORM rate is optimal up to $\log(e(1+\Gamma))$; it is not a new hiding technique (see "Prior work").

## Problem class, oracle and criterion

The [setup](../Setups/EuclideanStrongGrowthMeanSquared.lean) is the repository setup [StrongGrowthMeanSquaredSmoothConvex](../Setups/StrongGrowthMeanSquaredSmoothConvex.lean), whose `admissible` and `successful` predicates are reused verbatim, specialized to $E=\mathbb R^d$ (with the Borel σ-algebra). An instance is a convex differentiable $f:\mathbb R^d\to\mathbb R$ with a minimizer $x_\star$, $\|x_0-x_\star\|\le R$. The oracle answers a query $(x,y)$ with $(g(x,\xi_k),g(y,\xi_k))$, using one fresh sample $\xi_k$ for both points; the sample sequence is IID (the repository's `IID` structure), and $g$ is jointly measurable with

- unbiasedness: $\int g(x,\xi)\,d\mu=\nabla f(x)$;
- strong growth (SGC): $\int\|g(x,\xi)-\nabla f(x)\|^2d\mu\le\Gamma^2\|\nabla f(x)\|^2$, i.e. second-moment constant $\rho=1+\Gamma^2$ ([Schmidt–Le Roux 2013](https://arxiv.org/abs/1308.6370); [Vaswani–Bach–Schmidt 2019](https://arxiv.org/abs/1810.07288));
- mean-squared smoothness (MSS): $\int\|g(x,\xi)-g(y,\xi)\|^2d\mu\le\bar L^2\|x-y\|^2$ ([Arjevani et al. 2019](https://arxiv.org/abs/1912.02365); the same-sample pair oracle of SPIDER/STORM);
- the integrability conditions needed for these integrals.

Success is the original criterion: measurable output, integrable objective gap, and $\int (f(\hat x)-f(x_\star))\,dP\le\varepsilon$ under the product of the algorithm's seed law and the sample law. All parameters $(d,\bar L,\Gamma,R,\varepsilon,x_0)$ are public; any randomized adaptive algorithm is allowed.

Relative to the original setup, `valid` adds only parameter restrictions:

- $R>0$ and $2^{26}\sqrt{1+\Gamma^2}\,\varepsilon\le\bar L R^2$ (the accuracy-dominated regime; it guarantees that the lower budget is at least $1+\Gamma^2$, while the proof itself only uses the constant $2^{18}$);
- $d\ge\big(\bar L R^2/(\sqrt{1+\Gamma^2}\,\varepsilon)\big)^3$ (polynomial dimension, an artifact of the randomized hiding argument; the upper bound is dimension-free);
- the noise space contains two distinct points with measurable singletons (otherwise every oracle is deterministic).

The regime is nonempty for every $\Gamma\ge0$ (take $R=\varepsilon=1$, $\bar L=2^{26}\sqrt{1+\Gamma^2}$, $d$ large, $\Omega$ = `Bool`), and includes $\Gamma=0$. The formal [inclusion](../Proofs/StrongGrowthMeanSquaredInclusion.lean) `inclusion : Inclusion StrongGrowthMeanSquaredSmoothConvex.spec EuclideanStrongGrowthMeanSquared.spec` records that the new setup is a subclass of the original one: valid parameters map to valid parameters, and admissibility and success are identical. Hence the lower bound is also a lower bound for the original repository setup `StrongGrowthMeanSquaredSmoothConvex` at the mapped parameters, and every upper bound for the original setup transfers to the new one.

## The two theorems

**Lower bound** (`result : NonConvergence spec budget`). For every valid parameter choice, every allowed algorithm, and every budget $b\le B$, including $b=0$,

$$
B=\Big\lfloor \sqrt{(1+\Gamma^2)\sqrt{1+\Gamma^2}\,\bar L R^2/\varepsilon}\,/\,8192\Big\rfloor
=\Big\lfloor (1+\Gamma^2)^{3/4}\sqrt{\bar L R^2/\varepsilon}\,/\,8192\Big\rfloor ,
$$

there is an admissible instance and oracle on which the execution fails the success criterion: if the output is measurable and its gap integrable, the expected gap exceeds $\varepsilon$. The instance may depend on the algorithm, never on its realized seed.

**Upper bound** (`result : Convergence spec budget`, transferred from ProximalStorm):

$$
U=\Big\lceil\sqrt{2\bar L R^2/((1+\Gamma)\varepsilon)}\Big\rceil\cdot\Big\lceil(1+\Gamma)^2\big(4810+3200\log(1+\Gamma)\big)\Big\rceil .
$$

On the valid regime $\sqrt{\bar LR^2/\varepsilon}\ge 2^{13}(1+\Gamma^2)^{1/4}$, so the lower budget satisfies $B\ge\lfloor 1+\Gamma^2\rfloor\ge1$ and $B$ is at least half of the unrounded value; the square root in the first ceiling of $U$ is at least $2^{13}$, so $U\le(1+2^{-13})\sqrt2\,(1+\Gamma)^{3/2}\sqrt{\bar LR^2/\varepsilon}\,\big(4811+3200\log(1+\Gamma)\big)$; and $(1+\Gamma^2)^{3/4}\ge(1+\Gamma)^{3/2}/2^{3/4}$. Hence on the whole valid regime $U/B\le 4\cdot10^4\,\big(4811+3200\log(1+\Gamma)\big)$ (constants are not optimized). In order notation both are $(1+\Gamma)^{3/2}\sqrt{\bar LR^2/\varepsilon}$, up to the single factor $\log(e(1+\Gamma))$ in the upper bound.

## Hard instance and proof

All constructions are in [StrongGrowthMeanSquaredLowerBound.lean](../Proofs/StrongGrowthMeanSquaredLowerBound.lean) and the generic simulation in [StrongGrowthThinning.lean](../Proofs/StrongGrowthThinning.lean).

1. **Masked oracle.** Put $\rho=1+\Gamma^2$, $p=1/\rho$, and $L'=\bar L/\sqrt\rho$. The sample law is the two-atom law $p\,\delta_a+(1-p)\delta_b$, and the trajectory law is the infinite product (`Measure.infinitePi`), whose IID property is proved. The oracle is $g(x,\xi)=\rho\,\mathbf 1\{\xi=a\}\nabla f(x)$, used with the same $\xi$ at both query points. Then $\int g=\nabla f$, the SGC holds with equality, $\int\|g(x)-g(y)\|^2=\rho\|\nabla f(x)-\nabla f(y)\|^2\le\rho L'^2\|x-y\|^2=\bar L^2\|x-y\|^2$, and joint measurability and all integrability clauses are proved (`hard_admissible`).
2. **Hard objective.** $f(x)=F_\pi(x-x_0)$, where $F_\pi$ is the repository's nonlinear localized smooth convex chain ([SmoothConvexFiniteWall](../Proofs/SmoothConvexFiniteWall.lean)) with smoothness $L'$, chain length $K=2M+1$, $M=\lfloor\sqrt{L'R^2/\varepsilon}/1024\rfloor$, embedded on hidden coordinates $\pi$ of $\mathbb R^d$; its minimizer lies within $R$ of $x_0$.
3. **Coin-fixing simulation** (`pair_eq_real`). Fix the algorithm seed and the sample path. A reply is zero when $\xi_k\ne a$ and carries no information. If at most $M$ of the first $b$ samples equal $a$, the actual execution equals a $2M$-step exact-gradient process whose state skips the zero replies and spends two exact gradient evaluations per informative pair call. This is proved for the actual `execute` trajectory, for every adaptive query rule.
4. **Hiding.** The repository's randomized polynomial-dimension hiding lemma (`execution_average_gap`, used by [SmoothConvexExpectedLowerBound](SmoothConvexExpectedLowerBound.lean)) applies pointwise to that process: summed over all hidden coordinate words, the objective gaps are at least $4\varepsilon$ times the number of words.
5. **Counting informative calls.** The number of informative calls has mean $bp$; Markov's inequality and the budget give probability at least $7/8$ that it is at most $M$. Integrating over the product of seed and sample laws, the average expected gap over words is at least $3.5\varepsilon$, so some word fails. The word is selected after integrating over seeds, so it depends only on the algorithm.

The choice $L'=\bar L/\sqrt{1+\Gamma^2}$ is the only new calibration: the chain needs about $\sqrt{L'R^2/\varepsilon}$ exact gradients and each costs $1+\Gamma^2$ calls, giving $(1+\Gamma^2)^{3/4}\sqrt{\bar LR^2/\varepsilon}$.

## Prior work and what is new

- **Masking oracle.** The oracle "return $0$ w.p. $1-p$ and $\nabla F/p$ otherwise" is the *naive construction* of [Arjevani, Carmon, Duchi, Foster, Srebro, Woodworth (arXiv:1912.02365 v2, §3)](https://arxiv.org/abs/1912.02365). The coin-fixing reduction to an exact-gradient algorithm is Theorem A.10 of [Novoselov, Dorn, Dvinskikh, Gasnikov (arXiv:2610.38354 v1, Oct 2026)](https://arxiv.org/abs/2610.38354) (masked quadratic samples, randomized algorithms), and simulation by batches of exact queries per informative call appears in Appendix G (Lemma G.1) of [arXiv:2610.12641 v1](https://arxiv.org/abs/2610.12641). With one worker, Theorem A.10 already gives the single-sample SGC lower bound $\Omega((1+\Gamma^2)\sqrt{LR^2/\varepsilon})$, which answers the question left open by [Mishkin, Pilanci, Schmidt (arXiv:2404.02378 v2, App. D)](https://arxiv.org/abs/2404.02378). That single-sample statement is **not** claimed here. The present lower bound follows quickly from these ideas with batch size two and the calibration $\bar L=\sqrt{1+\Gamma^2}\,L'$; we state this plainly.
- **Upper bounds.** For single-sample SGC oracles with $L$-smooth $f$, accelerated SGD costs $O((1+\Gamma^2)\sqrt{LR^2/\varepsilon})$ ([Vaswani et al. 2019, Thm. 2](https://arxiv.org/abs/1810.07288); [AGNES, Gupta–Siegel–Wojtowytsch, NeurIPS 2024, Thm. 3](https://arxiv.org/abs/2302.05515)). For the same-sample MSS class, the only upper bound we know is the repository's ProximalStorm theorem, $O((1+\Gamma)^{3/2}\sqrt{\bar LR^2/\varepsilon}\log(e(1+\Gamma)))$.
- **What is new.** (i) A formal, all-randomized-algorithm lower bound for the SGC + MSS same-sample class, in polynomial dimension, with expected accuracy. (ii) Together with ProximalStorm, the class complexity $\tilde\Theta((1+\Gamma)^{3/2}\sqrt{\bar LR^2/\varepsilon})$ on the valid regime. No published statement of this complexity or of a lower bound for this class was found.
- **Comparison with single-sample methods.** On instances where both bounds apply, the upper bounds differ by a factor of about $\sqrt{\Gamma L/\bar L}/\log(e(1+\Gamma))$, a gain only when $\bar L\ll\Gamma L$ (for $\bar L\approx\Gamma L$ the two rates coincide, since $\Gamma^{3/2}\sqrt{\Gamma L}=\Gamma^2\sqrt L$). No class-level separation between the single-sample and the same-sample oracle is proved: with parameters $(L,\bar L,\Gamma)$ masking gives only $\min\{\Gamma^2\sqrt L,\Gamma^{3/2}\sqrt{\bar L}\}R/\sqrt\varepsilon$ for single-sample methods, and whether single-sample methods can match the pair rate remains open.

## Limitations

- Tightness holds only on the regime $2^{26}\sqrt{1+\Gamma^2}\,\varepsilon\le\bar LR^2$ and only up to $\log(e(1+\Gamma))$ and large universal constants. Below that regime the upper bound is dominated by its $(1+\Gamma)^2\log$ term and has no matching lower bound here; that regime is not covered.
- The dimension condition is polynomial and comes from the hiding argument.
- The result concerns IID sampling, the expected-gap criterion, and convex objectives; no high-probability, strongly convex, or dependent-sampling statement is made.
- The hard objectives are the nonlinear localized chains of the repository (coordinates interact through the chain and the smooth wall, so they are neither quadratic nor separable). The upper bound covers every nonlinear instance of the class; see the [ProximalStorm note](ProximalStormStrongGrowth.md) for natural examples.

## Literature search

Searches on 14 November 2026 (UTC) covered ICML/ICLR/NeurIPS 2025–2026 material and roughly two years of arXiv on strong growth, multiplicative/relative noise, interpolation lower bounds, and variance reduction (STORM/SPIDER/MSS) lower bounds, following citations to Arjevani et al. (2019), Woodworth–Srebro (2021), Vaswani et al. (2019), AGNES (2024), Hermant et al. (ICLR 2025), Chen–Na–Kolar (MOR), Mishkin et al. (v2), and the Novoselov et al. preprints (Oct 2026, unrefereed). The search was topical, not an exhaustive proceedings scan.

## Scope requirements

- *Lower bound for a popular repository setup:* the lower bound holds for the repository setup `StrongGrowthMeanSquaredSmoothConvex` (SGC + MSS, both standard assumptions) on the stated parameters.
- *Slightly strengthened parameter assumptions:* only $R>0$, the accuracy regime, polynomial dimension, and a non-degenerate noise space are added, all in `valid`.
- *Tight upper and lower bounds up to logs:* the paired theorems match up to $\log(e(1+\Gamma))$ on the whole valid regime.
- *Inclusion into another setup:* `inclusion` in [StrongGrowthMeanSquaredInclusion.lean](../Proofs/StrongGrowthMeanSquaredInclusion.lean) uses [Includes](../Includes.lean).
- *Not the $(L_0,L_1)$ setting:* the class is globally mean-squared smooth.
