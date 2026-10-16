# Second-order residual complexity under standard weak Minty

The [Lean theorem](FullRangeSecondOrderWeakMinty.lean) proves an exact-oracle complexity bound for finding a small residual of a smooth, possibly nonmonotone operator. It uses the [WeakMintySecondOrder setup](../Setups/WeakMintySecondOrder.lean) and constructs the [WeakMintyHybrid algorithm](../Algorithms/WeakMintyHybrid.lean). The contribution is removal of the trajectory-scale smallness restriction in prior higher-order analyses of **standard squared-residual weak Minty**, while retaining inverse-linear dependence on residual accuracy. It is not a new proximal correction framework or a formalization-only novelty claim.

## Problem and guarantee

Let $F:E\to E$ be continuously differentiable on an arbitrary finite-dimensional real inner-product space. Its derivative $J$ need not be symmetric. Assume

$$
\|F(x)-F(y)\|\le L_1\|x-y\|,\qquad
\|J(x)-J(y)\|\le L_2\|x-y\|,
$$

where $L_1,L_2>0$. For some zero $x_\star$, assume $\|x_0-x_\star\|\le R$ and

$$
\langle F(x),x-x_\star\rangle\ge-\frac\rho2\|F(x)\|^2
\quad\text{for every }x,\qquad \rho\ge0,\quad \rho L_1<2.
$$

This is the usual weak-Minty condition, with an explicit factor-of-two convention. The algorithm knows $L_1,L_2,\rho,\varepsilon,x_0$; it does not know $x_\star$ or $R$. It has separate exact value and full-Jacobian queries. Each costs one oracle call. No monotonicity, two-point cohypomonotonicity, bounded operator, compact domain, or error bound is assumed.

Write $\delta=1-\rho L_1/2\in(0,1]$. For every $\varepsilon>0$, the algorithm returns a queried, certified point $x_{\rm out}$ with $\|F(x_{\rm out})\|\le\varepsilon$ within

$$
\left\lceil
\frac{1048576\,(1+L_2R^2/\varepsilon)\log(2/\delta)}{\delta^5}
\right\rceil
$$

calls, counting both query types and all inner iterations. The formal accuracy statement is almost sure under the explicit product of the algorithm and oracle seed laws; exact replies make the claim true for every seed. The output is the first certified anchor or trial point, not an average or an unqueried existence witness.

For fixed positive margin, the bound is $O(1+L_2R^2/\varepsilon)$, without a separate initialization cost. The constants and margin dependence are conservative. The condition $\rho L_1<2$ is the full range of the compared proximal framework, **not** a proved boundary for second-order solvability.

## Algorithm and mathematical mechanism

At an anchor $x$, query $g=F(x)$ and return $x$ if its residual is small enough. Set

$$
 c=16/\delta,\quad \tau=\delta/4,\quad
 G=\delta^2L_1^2/(64L_2),\quad
 K=\left\lceil(4/\delta)\log(1024/\delta^2)\right\rceil.
$$

If $\|g\|\le G$, query $J(x)$, select a root

$$
 g+J(x)s+cL_2\|s\|s=0,
$$

and take $y=x+s$, $\eta=(cL_2\|s\|)^{-1}$. A nonzero anchor residual makes $s\ne0$. Otherwise set $\eta=(1-\delta/4)/L_1$ and use $K$ Picard steps $y_0=x$, $y_j=x-\eta F(y_{j-1})$. The already queried anchor value supplies the first step. Query $v=F(y)$; return $y$ if certified, and otherwise replace $x$ by $x-\tau\eta v$.

Three facts make the scope extension possible.

1. **Every cubic-model root is controlled at a small-residual anchor.** For $\alpha=cL_2\|s\|$, the equation gives $\alpha(\alpha-L_1)\le cL_2\|g\|$. At the threshold this implies $\alpha\le(1+\delta/4)L_1$, hence $\rho/\eta\le2-\delta$. No special root-selection invariant or inverse-Jacobian assumption is needed.
2. **Both branches satisfy the same relative certificate.** The Taylor remainder or the explicitly counted contraction gives $\|y-x+\eta F(y)\|\le(\delta/16)\|y-x\|$. The established relaxed proximal correction then decreases squared distance by at least $\delta^2\|y-x\|^2/16$.
3. **Complementary residual regimes pay for the same accuracy scale.** On a nonterminal cubic attempt, $\|F(y)\|\le17L_2\|y-x\|^2/\delta$. On a fallback attempt, $\|y-x\|\ge\|F(x)\|/(4L_1)$, while $\|F(x)\|>\max\{\varepsilon,G\}$. Consequently $\|F(x)\|^2\ge\varepsilon G$. Every nonterminal attempt therefore decreases squared distance by at least $\delta^4\varepsilon/(16384L_2)$. This argument permits arbitrary switching between branches; an initially small residual need not remain small.

A cubic attempt costs three calls. A fallback costs $K+1$, including its final certificate. The proof uses the common upper bound $K+2$, proves that a certified absorbing state is reached, and connects it to `execute`. Calls after certification, which the framework continues until budget exhaustion, are also included.

The [model-root existence proof](../Proofs/RegularizedLinearRoot.lean) minimizes the shift over compact feasible pairs $(\alpha,s)$ satisfying $(J+\alpha I)s=-g$, $\|s\|\le\alpha/(cL_2)$. An invertible interior minimum contradicts inverse continuity; a singular one can be moved along a kernel direction to the required sphere. Selection depends only on cached $g,J,cL_2$. In coordinates, a nonsingular shift solves a scalar secular equation, which becomes a polynomial of degree at most $2d+2$ after clearing denominators; singular shifts require an affine-sphere check. The Lean algorithm uses classical choice from the proved existence statement. This is an oracle-complexity result, not an arithmetic or bit-complexity bound, and a full Jacobian query is not a single Hessian-vector product.

## Closest prior results and comparison

- **Vyas and Bullins, [arXiv:2304.08389v1](https://arxiv.org/abs/2304.08389v1), April 2023, Assumptions 1–3, Theorem 3.5 and Appendix B.1.** Their main higher-order weak-Minty condition uses residual power $(p+1)/p$. Appendix B.1 does address standard power two, with trajectory-scale smallness. The theorem literally displays $\rho\le[15/(16D^q)]\,[p!D^{(p+1)/p}/L_p]$, which at $p=q=2$ says $\rho L_2\sqrt D\le15/8$. Its proof instead displays the absorption coefficient $\rho D^q(L_p/(p!D))^{(p+1)/p}$, and equation (B.2) loses the $p!/L_p$ weight needed to apply its weak-Minty assumption to (B.1). These normalizations are inconsistent. Independently reconstructing the correctly scaled correction gives the dimensional smallness condition $\rho\sqrt{L_2D}\lesssim1$; this is our reconstruction, not a quoted theorem formula or a verified constant from the paper. We compare against this corrected reconstruction as well as the literal statement. Both retain trajectory dependence. Here $D$ is a Lipschitz constant times a trajectory radius; the statement and proof also differ on anchor versus trial indexing. Thus standard weak Minty with a second-order inverse-linear residual rate was already known under this extra restriction. The present theorem removes that restriction throughout $\rho L_1<2$. We compare best residuals, not the preprint's displayed expectation conversion. Only arXiv v1 was listed when checked; no conference acceptance is asserted.
- **Pethick, Mavrothalassitis and Cevher, [ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf), scheme (8), Theorem 5.5 and Section 6.** The relaxed inexact-proximal potential and constant-in-accuracy Picard solver are established there. Their headline $O(1/\varepsilon)$ counts accuracy in the **squared** tangent residual, hence $O(1/\varepsilon^2)$ for the norm criterion here. We do not claim their correction mechanism as new. Our addition is the cubic certificate and complementary accounting that retain the higher-order rate without trajectory-scale smallness. Their publication status is confirmed by the official proceedings.
- **Vyas and Bullins, [arXiv:2603.13491v1](https://arxiv.org/abs/2603.13491v1), March 2026, Theorem 4.2 and Appendix B.3.** This later structured-VI preprint again distinguishes higher-order Minty from the standard-power condition; its latter extension uses bounded residuals and parameter-dependent smallness. Its broader non-Euclidean scope is not covered by our theorem. The draft contains unresolved constant annotations, so it is not used to support a sharp constant comparison.
- **Lin and Jordan, [Perseus](https://arxiv.org/abs/2205.03202), Mathematical Programming 2024**, and **Agafonov et al., [NeurIPS 2024, Exploring Jacobian Inexactness](https://papers.neurips.cc/paper_files/paper/2024/file/d1ca7877cdaf3201ecfa95b1240f7942-Paper-Conference.pdf), Assumption 1.3**, provide higher-order nonmonotone guarantees under the nonnegative Minty condition. They do not supply this negative-defect weak-Minty extension. Our exact-Jacobian theorem does not inherit their inexact-oracle guarantees.

The assumption-relaxation comparison is on the shared regime $\rho L_1<2$: within that regime the trajectory-smallness condition is removed. No containment is claimed for prior guarantees outside this range. The global residual-power-$3/2$ condition and the squared-residual condition are not interchangeable; their relative strength changes with residual scale.

For fixed $\delta>0$, the rate improves the applicable first-order norm-residual upper bounds as $\varepsilon\to0$. One comparable Picard-corrected first-order bound scales as $O((1+L_1^2R^2/\varepsilon^2)\delta^{-3}\log(2/\delta))$; the second-order leading term is favorable when $\varepsilon\ll\delta^2L_1^2/L_2$, with $\varepsilon\lesssim L_2R^2$ so its nonconstant term is relevant. This is an upper-bound comparison, not a lower bound against all first-order methods, nor universal superiority near the margin boundary. Within the stronger assumptions of the earlier higher-order theorem, no improved accuracy exponent is claimed.

A direct substitution into Appendix B.1 cannot remove its trajectory-dependent restriction. Running a first-order method until one small residual and then using only cubic steps does not establish a small-residual invariant. The per-attempt root bound and charging argument address exactly that missing step. Batching identical exact replies adds no information. For a normalization $G=\psi(\|F\|)F$ with $\psi>0$, weak Minty gives a residual-power-$3/2$ defect coefficient $\rho\sqrt{\|F\|/\psi(\|F\|)}$. Uniform control for unbounded $F$ requires at least linear growth of $\psi$, rather than bounded clipping. The natural choice $G=\|F\|F$ has derivative regularity involving $\|F\|L_2$; localization reintroduces a radius-dependent constant. Thus this standard normalization does not directly transfer the earlier theorem with the claimed cost. This calculation identifies an obstruction to that reduction, not an impossibility theorem for every transformation.

## Nonlinear scope and limitations

A concrete separating VI family exists in every even dimension. Let $K$ be any orthogonal skew-symmetric matrix, including a dense orthogonal conjugate of the standard rotation matrix, and put

$$
F(z)=-z+\left(100+\frac{1000}{1+\|z\|^2}\right)Kz.
$$

This smooth field has negative radial drift and radius-dependent rotation. It satisfies the assumptions with $x_\star=0$, $\rho=2/10001$, $L_1=1601$, and $L_2=4000$, independently of dimension. Indeed, $\langle F(z),z\rangle=-\|z\|^2$, $\|F(z)\|^2\ge10001\|z\|^2$, and differentiating the rational rotation gives the stated derivative bounds. It is unbounded and violates every global residual-power-$3/2$ Minty bound along rays. Large initial radii violate the earlier trajectory-scale smallness restriction.

It is also not globally cohypomonotone for any finite constant. On the plane spanned by $e,Ke$, its Jacobian at $z=re$ is $[[-1,-b],[b+rb_r,-1]]$. Its determinant is positive at $r=0$ and negative at $r^2=3$, hence vanishes somewhere. At such a point a kernel vector $v=(b,-1)$ has $J^Tv\ne0$. Perturbing $v$ toward $-J^Tv$ contradicts any derivative inequality $\langle Jh,h\rangle\ge-C\|Jh\|^2$. This is a VI example, not a claimed scalar zero-sum game gradient field. It demonstrates separation of assumptions, not worst-case hardness: its additional global error bound permits faster instance-specific methods.

The theorem covers descent-ascent fields when they satisfy the stated assumptions, but certifies only a stationary root residual, not a local Nash equilibrium or minimax optimality. It is unconstrained, Euclidean, deterministic, and uses exact full Jacobians. It establishes neither optimal accuracy complexity for the entire weak-Minty class nor optimal dependence on $\delta$. Extension beyond the compared proximal range, noisy Jacobians, constrained problems, and practical approximate algebraic root computation remain open here.

The literature comparison was checked against primary sources through 16 October 2026, including the initial ICML 2025/2026, ICLR 2025/2026, NeurIPS 2024/2025 and recent-arXiv survey and targeted older citations. NeurIPS 2026 acceptance was not assumed from submissions. Search coverage and inaccessible-source records were kept outside the repository; the directly blocked OpenReview PDF for the ICLR baseline was read through its official proceedings copy.
