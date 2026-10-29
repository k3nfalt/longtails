# Known-value nondual optimization with gradient-dependent curvature

[The Lean theorem](KnownValueNondualGeneralizedRate.lean) constructs [the algorithm](../Algorithms/KnownValueNondual.lean) for [the setup](../Setups/KnownValueNondualGeneralizedConvex.lean). It gives a deterministic first-order oracle bound for a globally convex, continuously differentiable function on arbitrary finite-dimensional Euclidean space, with a known optimal value and an ℓ₁ prior on a minimizer. The contribution is a curvature-dependent oracle guarantee using one persistent sequence of localization bodies across all accuracy levels.

The public information is $d,L_0,L_1,R,\varepsilon,f^*,x^0$, with $d\ge1$ and all four real parameters positive. There exists a global minimizer $x^*$ with $f(x^*)=f^*$ and $\|x^0-x^*\|_1\le R$. The symmetric generalized-smoothness condition is

$$
\|\nabla f(x)-\nabla f(y)\|_2
\le \left(L_0+L_1\sup_{z\in[x,y]}\|\nabla f(z)\|_2\right)\|x-y\|_2.
$$

One oracle call returns the exact pair $(f(x),\nabla f(x))$. The oracle is available on the whole space, including outside the initial ℓ₁ ball. No initial objective-gap bound, bounded gradient, Hessian regularity, strong convexity, separability, or dimension restriction is assumed. The setup does not restrict the admissible algorithm family. The conclusion is objective error at most $\varepsilon$ for the returned incumbent, for every oracle seed satisfying the exact-answer specification; the framework expresses this as an almost-sure guarantee.

Set

$$
 A=\frac{L_0R^2}{\varepsilon},\qquad B=L_1R,\qquad
 Q=1+A^{1/3}+B^{2/3},\qquad
 L=1+\log(2d)+\log(2+A+B).
$$

The public budget is exactly

$$
 \left\lceil 2^{36}QL^2\right\rceil
$$

paired oracle calls. Thus the rate is $\widetilde O(1+A^{1/3}+B^{2/3})$, with dimension appearing only logarithmically. The universal constant is deliberately loose; the claim concerns parameter exponents and oracle complexity, not practical superiority of this numerical budget.

The algorithm maintains a body in translated coordinates $u=x-x^0$, initially $R B_1^d$, and an incumbent. Its selector is the exact average of Euclidean projections onto the body over a Euclidean ball of radius $R\sqrt{d/(1+\lfloor\log_2d\rfloor)}$. The formal proof establishes total movement at most $12R\sqrt{(1+\lfloor\log_2d\rfloor)(1+\lfloor\log_2T\rfloor)}$ for every positive finite horizon $T$, including bodies with empty interior. Zero-horizon movement is zero. Selector computation is free in this oracle model. No polynomial-time implementation or efficient approximation of these exact integrals is claimed.

A finite line search between the selector and incumbent returns a cached value-gradient pair. Its small-gradient branch immediately certifies accuracy. Otherwise, with $G=\|\nabla f(x)\|_2$ and $H=L_0+L_1G$, it guarantees objective monotonicity and coupling error at most $G^2/(16H)$. The next incumbent is $x-\nabla f(x)/(4H)$, with decrease certificate $D=5G^2/(24H)$. The observable quantity $f(x)-D$ supplies the stopping and phase tests without querying that next incumbent.

Warmup uses $h=1+\lceil B^{1/3}\rceil$. Failed warmup rounds add a strengthened cut

$$
 f(x)+\langle\nabla f(x),x^0+u-x\rangle+
 \frac{hG}{2L_1}\le f^*.
$$

The proof derives the gradient threshold making this cut valid at minimizers from the failed-round condition. This strengthened affine expression is not asserted to be a global minorant of the objective. After warmup, failures add ordinary tangent cuts at level $f^*$. These cuts are never discarded when the target halves. For $B\le1$, warmup is skipped using the proved initial-gap bound $2L_0R^2$; this avoids a spurious dependence on $\log(1/B)$.

The new accounting links local curvature to global selector motion. If $M$ is total movement, $q$ the number of phase changes, and $n_w,n_0,n_1$ the respective warm, low-gradient, and high-gradient failure counts, the formal trajectory satisfies

$$
 7h n_w\le16L_1M,\qquad
 n_0^3\le\frac{30L_0}{\varepsilon}M^2,\qquad
 n_1^2\le20L_1(1+q)M.
$$

The low-phase charge sums telescope across changing targets: the potentials $(f(y)-f^*)/\Gamma^2$ and $(f(y)-f^*)/\Gamma$ give respectively $\sum D/\Gamma^2\le3/\varepsilon$ and $\sum D/\Gamma\le2+2q$. They also handle the last clamped target and both terminal branches. Retaining the localization body makes the movement in these bounds global. Warmup leaves $q=O(h+\log(2+A+B))$; balancing $B/h$ against $\sqrt{Bh}$ produces the exponent $2/3$.

The proof connects these counts to actual `execute` calls. Every line-search block uses exactly $3+\lfloor\log_2\lceil128(1+32A+4B)^2\rceil\rfloor$ paired queries, including padding after an early line-search decision. Termination occurs within $\lceil2^{30}QL\rceil$ blocks. The public budget covers all complete blocks and any remaining calls; a finished incumbent is frozen. These facts are proved in the [execution](../Proofs/KnownValueNondualExecution.lean), [potential](../Proofs/KnownValueNondualPotential.lean), [counting](../Proofs/KnownValueNondualCounting.lean), and [budget](../Proofs/KnownValueNondualBudget.lean) modules.

The closest comparisons are as follows; the cited versions were checked through 29 October 2026.

| Primary result | Relevant guarantee and distinction |
| --- | --- |
| Rudomanov–Fomin–Gasnikov–Stonyakin, [v1, Definition 2.1 and Theorem 3.7](https://arxiv.org/html/2610.21461v1) | The same symmetric generalized smoothness with a Euclidean radius prior admits $O(\sqrt A+(1+B)\log(2+B))$ gradient calls, without values or known $f^*$. Their Appendix B's $B^{2/3}$ term requires a bounded initial gap; that restriction is absent here. Their descent, minimizer inequalities, and line-search ideas are supporting ingredients, not claimed novelties. This is an arXiv preprint. |
| Martínez-Rubio–Bullins–Guzmán–Molina, [v1, Theorems 4 and 6, and their proofs](https://arxiv.org/pdf/2609.21880v1) | The smooth ℓ₁/ℓ₂ specialization has cubic error decay and $\widetilde O(A^{1/3})$ complexity. Its phasewise reduction sums separate movement costs; it does not directly provide the present gradient-dependent-curvature bound. Uniform smoothness on a radius ball can be exponentially large in $B$. This is an arXiv preprint. |
| Martínez-Rubio–Guzmán, [v1, Fact 7 and Section 3](https://arxiv.org/pdf/2609.20701v1) | Small Euclidean movement for nested subsets of an ℓ₁ ball is established machinery. The present exact projection-average selector is supporting formalization, not the optimization novelty. Their computational guarantees for approximate selectors are not inherited here. This is an arXiv preprint. |
| Deng–Lan–Lin, [v3, Theorem 2.1 and “Choice of $X_k$”](https://arxiv.org/html/2412.06319v3) | Known-value full-memory cuts are already explicit in APMM. Its theorem uses a uniform local Hölder constant, which can be exponentially large for this class; it does not supply the global motion/curvature charge bound above. The paper is [accepted in INFORMS Journal on Computing](https://pubsonline.informs.org/doi/10.1287/ijoc.2025.1177). |

A stronger comparison than simply replacing the Euclidean radius by $R$ is necessary. Reconstructing a standard warmup-plus-restarted-nondual composition yields

$$
 \widetilde O\!\left(1+A^{1/3}+B/h+
 \sqrt B\,[h+\log_+(A/B)]\right).
$$

Taking $h\asymp1+B^{1/4}$ gives $\widetilde O(1+A^{1/3}+B^{3/4})$. This is a reconstructed reduction from the cited analyses, not a separately published theorem. Restarting loses the shared-movement bound and pays $\sqrt B\,q$; the present accounting pays $\sqrt{Bq}$. Accordingly, the meaningful exponent improvement is in the regime $B\gg1$, $A\ll B^{9/4}$, up to logarithmic factors. When the $A^{1/3}$ term dominates, no exponent improvement is claimed. Knowledge of $f^*$ is essential to the persistent-cut construction; the theorem does not settle the unknown-optimum-value problem.

There is also evidence that the curvature exponent has intrinsic meaning. Theorem 4.8 of the Everest preprint has dimension $2n$ and minimum zero. Setting its Euclidean radius to $R/\sqrt{2n}$ gives an ℓ₁-valid lower-bound family whenever

$$
 2\sqrt2\,n\log(1+L_1^2\varepsilon/L_0)
 +9\sqrt2\,n^{3/2}\sqrt{\log(4n)}\le B.
$$

The norm inequality remains valid after resisting rotations, and the common known minimum remains zero. This gives a deterministic $\widetilde\Omega(B^{2/3})$ obstruction when the additional logarithm is modest. It is a literature comparison, not an additional formal lower-bound theorem; no randomized lower bound is claimed.

The assumptions have motivation independent of this proof. Known zero loss occurs in interpolation and feasibility models, while ℓ₁ priors capture sparse or small-total-mass displacements without restricting the objective to separable functions. For a concrete nonlinear family, take a dense invertible $m\times m$ matrix $C$ and $f(x)=\sum_i(\cosh((Cx-b)_i)-1)$. Its known minimum is zero at $C^{-1}b$, and it satisfies generalized smoothness with $L_0=m\|C\|_2^2$, $L_1=\sqrt m\|C\|_2^2/\sigma_{\min}(C)$. Coordinates interact through $C$. This example imposes no extra restriction on the theorem.

The substantive claim is the new oracle exponent under this established combination of global generalized smoothness, ℓ₁ prior geometry, and known optimal value. Neither fixed-level cuts, movement selectors, ordinary smooth cubic decay, nor Lean verification alone is the novelty. The tradeoffs are exact values, known $f^*$, potentially expensive selector computation, and conservative constants. The literature search included available 2025–2026 conference records, recent arXiv versions and followups, and foundational citations; it is finite rather than exhaustive.
