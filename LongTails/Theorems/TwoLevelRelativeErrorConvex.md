# Two-level acceleration with relative gradient error

A smaller relative error buys a fourth power of the tolerance in the term linear in \(T=LR^2/\varepsilon\). The cost is a factor \(\log(1/\alpha)\) and an initialization term. With the explicit constants, the gain occurs at very high target accuracy. The algorithm compares two integer budgets before its first query. [Theorem and budget](TwoLevelRelativeErrorConvex.lean)

## Guarantee and call count

Let \(f\) be convex and \(L\)-smooth on a real Hilbert space, with a minimizer \(x_\star\) within distance \(R\) of \(x_0\). Every reply \(v\) at \(t\), for every history and seed, satisfies \(\|v-\nabla f(t)\|\le\alpha\|\nabla f(t)\|\). The public input includes \(x_0,L,R,\varepsilon,\alpha\), with \(L,\varepsilon>0,\ R\ge0,\ 0\le\alpha<1\). The output achieves \(f(x_{\rm out})-f(x_\star)\le\varepsilon\) on every realization. The setup asks for almost-sure success. [Setup](../Setups/RelativeErrorSmoothConvex.lean)

Write \(U=T/(1-\alpha)\) and \(N_0=\lceil7\sqrt U+11\alpha^2U\rceil\). On \(0<\alpha\le1/32,\ T\ge1\), put
\[
s=\alpha^{-4},\quad r=(1+s)/(1-2\alpha),\quad H=8\sqrt r+128\alpha^2r,
\qquad m=\left\lceil H\log\frac{1+s}{32\alpha^2}\right\rceil ,
\]
\[
K=\left\lceil\sqrt{12e\alpha^4 T}+1536e\alpha^6 T\right\rceil .
\]
The budget is \(\min(N_0,Km)\) on this range and \(N_0\) elsewhere. The public formula uses the exact count so its comparison remains sharp after rounding. The single-loop method handles ties, exact gradients, and \(R=0\) (zero calls in the last case). The simpler estimate for the two-level branch is
\[
Km\le1711\bigl(\alpha^{-2}+\sqrt{12e}\sqrt T+1536e\alpha^4T\bigr)\log(1/\alpha).
\]
Indeed \(r\le2\alpha^{-4}\), \(H\le272\alpha^{-2}\), and the inner logarithm is at most \(6\log(1/\alpha)\). Applying each ceiling separately gives the estimate. [Call-count proof](../Proofs/TwoLevelRelativeErrorConvexBudget.lean)

## Method and proof

Start with \(z_0=x_0\). Set \(\mu=L\alpha^4,\ \eta=1/\mu,\ \sigma=16\alpha,\ q=1/(6+3\sigma^2 K)\). At step \(k\) take \(y=(kx_k+2z_k)/(k+2)\). Starting both inner states at \(y\), run \(m\) steps of the mixed-error strongly convex solver on \(h(t)=f(t)+(\mu/2)\|t-y\|^2\) with parameters \(L+\mu,\mu,2\alpha\). Each step queries the physical oracle once and adds \(\mu(t-y)\) to the reply. With \(u\) the last inner primal iterate, set \(x_{k+1}=u,\ z_{k+1}=z_k-q(k+1)(y-u)/2\). The plan returns \(x_K\) on call \(Km\). Its pointwise guarantee certifies that output without measuring the objective or testing a residual. [Algorithm](../Algorithms/TwoLevelRelativeErrorConvex.lean)

Let \(p=\arg\min h,\ d=y-p\). Stationarity gives \(\nabla f(p)=\mu d\). Strong monotonicity gives \(\mu\|t-p\|\le\|\nabla h(t)\|\), so the inner error is bounded by \(2\alpha\|\nabla h(t)\|+\alpha\mu\|d\|\). The inner momentum satisfies \(2/\theta=H\), hence \((1-\theta/2)^m(L+\mu)\le32\alpha^2\mu\). The existing inner accuracy lemma now gives \(h(u)-h(p)\le\sigma^2\mu\|d\|^2/2\). Proximal growth and convexity at \(p\) give, for every \(t\),
\[
\|d-(y-u)\|\le\sigma\|d\|,\qquad
(f(u)-f(t))/\mu\le\langle d,y-t\rangle-3\|d\|^2/8 .
\]
These inequalities also cover \(d=0\). The physical reply map carries the absolute call index through every inner solve, so successive solves can depend on the entire preceding history. [Inner proof](../Proofs/TwoLevelRelativeErrorConvexInner.lean)

With \(A=qk(k+1)/4,\ a=q(k+1)/2,\ B=A+a\), use \(\Phi_k=A(f(x_k)-f_\star)/\mu+\|z_k-x_\star\|^2/2\). Weight the second inequality at \(x_k,x_\star\) by \(A,a\). The identity \(By=Ax_k+az_k\) cancels the linear term from the mirror step up to \(a\sigma\|d\|\|z_k-x_\star\|\). Since \(a^2\le qB,\ q\le1/6,\ \|y-u\|\le3\|d\|/2\), the quadratic mirror cost leaves at least \(3B\|d\|^2/16\) of descent. Young's inequality uses \(B\|d\|^2/6\) of this, giving \(\Phi_{k+1}\le(1+3q\sigma^2)\Phi_k\). Thus \(\Phi_K\le eR^2/2\). The ceiling for \(K\) gives \(K(K-1536e\alpha^6 T)\ge12e\alpha^4T\), which yields the claimed gap directly for \(f(x_K)\). [Potential](../Proofs/TwoLevelRelativeErrorConvexPotential.lean) · [Iteration and accuracy](../Proofs/TwoLevelRelativeErrorConvex.lean)

## Where the budget improves

Against the full-range single loop the comparison is exact. Write \(b=7\sqrt U+11\alpha^2U\) throughout. Off the two-level range the budgets agree. On it, write \(j=\sqrt{12e\alpha^4T}+1536e\alpha^6T\). The new budget is strictly smaller exactly when \(m\lceil j\rceil<b\), and equal otherwise. It is never larger. For fixed \(\alpha\), a gain is possible for sufficiently large \(T\) precisely when \(1536em\alpha^6<11\alpha^2/(1-\alpha)\). The square-root coefficient \(m\sqrt{12e}\alpha^2\) already exceeds \(7/\sqrt{1-\alpha}\) throughout this range, so a failure of the linear-coefficient test precludes a gain at *any* \(T\).

Numerically, the linear coefficients cross near \(\alpha=0.0006942\). Indeed \(m\ge136\alpha^{-2}\log(1/(32\alpha^6))\); substituting this lower bound in the ratio of linear coefficients gives an increasing function on \((0,1/32]\) which exceeds 1 at \(0.000695\). At \(\alpha=0.0003\), \(m=68{,}349{,}026{,}370\). The counts below illustrate the crossover with both ceilings included.

| \(T\) | \(Km\) | \(N_0\) |
|---:|---:|---:|
| \(2.00\cdot10^{21}\) | 1,987,316,290,734,120 | 1,980,907,274,738,322 |
| \(2.02\cdot10^{21}\) | 1,999,277,370,348,870 | 2,000,714,778,109,022 |
| \(10^{22}\) | 5,593,684,318,120,800 | 9,903,670,996,291,012 |

For \(\ell=\log(1/\alpha)\), division by \(N_0\ge11\alpha^2T\) bounds the ratio by a constant times \(\ell/(\alpha^4T)+\ell/\sqrt{\alpha^4T}+\alpha^2\ell\). This tends to zero if \(\alpha\to0\) and \(\alpha^4T/\ell^2\to\infty\). For example, at \(\alpha=1/\log(2+T)\), which eventually exceeds both restricted tolerances below, the single-loop budget, the earlier two-level upper bound and the new count have orders \(T/(\log T)^2\), \(T/(\log T)^3\) and \(T\log\log T/(\log T)^4\), respectively. The earlier “Tightness” sketch chooses the outer horizon from \(\alpha\) and the regularization from \(T\). Its hand bound has \(\log(2+T/\alpha^2)\) and covers \(\alpha\le1/27\). Here the fixed ratio \(\mu/L=\alpha^4\) makes the inner logarithm independent of \(T\), with explicit constants on \(\alpha\le1/32\). [Single-loop theorem and sketch](AcceleratedRelativeErrorConvex.md)

For the restricted results put \(w=\log(2+T),\ v=1+w,\ P=33v\). The following are their published integer budgets \(C\).

| Result | Additional condition on \(\alpha\) | \(C\) |
|---|---|---|
| [Recursive](RecursiveRelativeErrorConvex.lean) | \(\alpha\le e^{-8(1+\sqrt w)}/100\) | \(\lceil4\sqrt{2+T}\exp(32(1+\sqrt w)\log(32+w))\rceil\) |
| [Polylog precision](PolylogPrecisionRelativeErrorConvex.lean) | \(\alpha\le1/(100P^{12})\) | \(\lceil8P^{20}(2+T)^{5/8}\rceil\) |
| [Near-accelerated polylog precision](NearAcceleratedPolylogPrecisionRelativeErrorConvex.lean) | \(\alpha\le1/(100P^{12})\) | \(\lceil32768P^{16}(1+\log P)(2+T)^{1/2+\log(16384(1+\log P))/(32\log(32v))}\rceil\) |

An exact finite-parameter test applies to each row on its domain. Define \(D(n)\) to hold if \(b\le n\), or if the two-level range holds and \(j\le\lfloor n/m\rfloor\). The latter test is used only when \(m\) is defined on that range. The new budget is smaller for \(D(C-1)\), equal for \(D(C)\land\neg D(C-1)\), and larger for \(\neg D(C)\). This follows by moving the ceilings across an integer inequality. At each row's maximal tolerance, as \(T\to\infty\), both candidates here cost \(T^{1-o(1)}\), while the rows cost respectively \(T^{1/2+o(1)},T^{5/8+o(1)},T^{1/2+o(1)}\). At \(\alpha=0\), or \(\alpha\le T^{-1/4}\) on their domains for large \(T\), our single-loop option costs \(O(\sqrt T)\) and beats each row. Outside a row's validity range it gives no guarantee.

The exact-gradient subclass already needs order \(\sqrt T\) calls in growing dimension. The repository's expected-gap lower bound uses \(T\ge262144\), budget \(n=\lfloor\sqrt T/512\rfloor\), and dimension \(d\ge65536(n+1)^5\). Exact replies satisfy every relative tolerance. The lower-bound setup uses an integrable expected gap, whereas the present pointwise proof bounds a nonnegative gap for deterministic execution. No lower bound here captures the cost of nonzero \(\alpha\). In particular, at fixed small positive \(\alpha\) these upper bounds still grow linearly in \(T\). [Exact-gradient lower bound](SmoothConvexExpectedLowerBound.lean)

## Prior work and limitations

The comparison uses physical gradient calls for a final objective gap. In the strongly convex comparisons below, \(\kappa=L/\mu_{\rm sc}\) refers to the condition number of the *objective in the cited theorem*. The original objective here can have zero strong-convexity modulus.

| Primary source | Error model, guarantee, and comparison |
|---|---|
| [Kornilov et al., Theorem 3.1, (7)–(10)](https://arxiv.org/pdf/2310.00506) | Assumption 4 uses \(\hat\varepsilon=\alpha\) relative to the true gradient. For \(p=2\), ISTM bounds the gap by \(O(LR^2\max\{N^{-2},\sqrt\alpha N^{-3/2},\alpha/N,\alpha^2\})\). Its certificate has an \(\alpha^2 LR^2\) floor. Theorem 3.2, (17)–(18), uses restarts and strong convexity. |
| [Vasin and Gasnikov, (10), Theorems 7.1, 7.2 and 9.3](https://arxiv.org/pdf/2603.12376) | With the absolute error set to zero their norm condition matches ours. For \(T>1\) in Theorems 7.1–7.2, regularized descent uses \(O(T\log T)\) for \(\alpha<1/2\) with a tolerance-dependent prefactor. Regularized acceleration uses \(O(T^{1-\beta}\log T)\) if \(\alpha\le(12T)^{-\beta}/3,\ 0\le\beta\le1/2\). Theorem 9.3 uses \((2T)^{-\tau}/9\) for \(T\ge1\). Optimizing these exponents gives order \(\max(\sqrt T,\alpha T)\log(2+T)\) in the respective ranges. |
| [Vasin, Tyurin and Gasnikov, (7)–(9), Theorems 3.2–3.3](https://arxiv.org/pdf/2610.24863) | Their composite error becomes the same relative error when the absolute term vanishes. Theorem 3.3 assumes known \(R=\|x_0-x_\star\|\) and, for \(0<\varepsilon\le f(x_0)-f_\star\) and \(\alpha\le1/3\), regularizes at \(\varepsilon/(39R^2)\le L_0\). The LongTails setup supplies an upper bound on that distance. With initial smoothness estimate of order \(L\), substituting their \(\gamma^\star\) gives \(O(\max\{\sqrt T,9\alpha^2 T\}\log(2+T))\) gradient calls. Their adaptive line search also accesses function values. The authors describe fixed-parameter use when the constants are known. Remark 3.1 compares the single-loop LongTails result. |
| [Vasin et al., (4), Theorem 5.1 and Remark 7.7](https://arxiv.org/pdf/2102.02921) · [Vasin et al., Assumption 2, Theorems 4–5](https://arxiv.org/pdf/2503.06628) | Both use error relative to the true gradient. The first strongly convex analysis retains an accelerated linear rate for sufficiently small \(\alpha=O(1/\kappa)\). In the second, \(\alpha=\kappa^{-1/2+\tau}/3,\ 0\le\tau\le1/2\), gives contraction \(1-\kappa^{-1/2-\tau}/(10\sqrt2)\). The iteration factor interpolates from \(\sqrt\kappa\) to \(\kappa\). Applying either directly to a regularized objective would require error relative to its shifted gradient. |
| [Gannot, Proposition 1.8 and (1.16)](https://arxiv.org/pdf/1912.13494) | For strongly convex objectives with true-gradient-relative error \(\delta=\alpha\), the triple momentum state has a geometric distance bound \(c\bar\rho_{\rm TM}(\delta)^k\) in the stated range \(\delta<(\sqrt\kappa+1)/(4\kappa-3\sqrt\kappa+1)\). The analysis requires positive curvature. |
| [Bollapragada and Gupta, Condition 2.1 and Theorem 3.8(ii)](https://link.springer.com/article/10.1007/s10589-026-00788-y) | Adaptive gradient estimation gives \(O(1/k^2)\) expected composite gap. Among its conditions the relative tolerance \(\eta_k\) decreases to zero with \(\sum k\eta_k^2<\infty\). Repeating a query under our fixed positive tolerance can return the same biased vector every time. |
| [Khanh, Mordukhovich and Tran, (3.3), Theorems 3.5–3.6](https://dattran24.github.io/assets/pdf/momentum_inexactGD.pdf) | IGDm measures the error against the reply norm. Our condition implies theirs with \(\nu=\alpha/(1-\alpha)\) when this is below one. They obtain stationarity and, under the additional Polyak–Łojasiewicz–Kurdyka condition, exponent-dependent rates. For example, their local iterate distance decays as \(O(k^{-(1-q)/(2q-1)})\) for exponent \(1/2<q<1\). |
| [Hallak and Levy, Theorem 4.2 and Corollary 4.3](https://proceedings.mlr.press/v235/hallak24a.html) · [Vernimmen and Glineur, Theorem 3.1](https://arxiv.org/pdf/2506.17145) | Hallak and Levy recover exact conditional-gradient iterates under box constraints because the linear minimization separates by coordinate and their oracle preserves coordinate signs. Vernimmen and Glineur use true-gradient-relative errors for constant-step gradient descent. For normalized step \(0<h<3/[2(1+\alpha)]\) they bound the smallest squared gradient norm divided by \(L\) by the initial gap divided by \(Nh(1-\alpha)+1/2\). These criteria and algorithm classes differ from the present comparison. |

The asserted lower bound in Vasin and Gasnikov's Theorem 10.2 would obstruct improvements in part of the range above. The proof of Theorem G.3 applies Lemma G.1 to represent an erroneous gradient by a general inexact-model oracle, then invokes Theorem G.2 for that larger class. This inclusion alone leaves open whether its hard oracle is realizable by the smaller gradient class. We use the exact-gradient lower bound above. [Appendix G, proof of Theorem G.3, used in Theorem G.4](https://arxiv.org/pdf/2603.12376)

The search covered the papers cited by the repository's convex relative-error notes and targeted searches for acceleration under relative gradient errors, including strongly convex, adaptive-error and momentum methods. The comparisons use the linked versions. The result establishes the two-level count and the indicated improvement over the single-loop bound. Sharp constants, the optimal dependence on \(\alpha\), and the complexity at fixed positive tolerance remain open. The cost model counts oracle calls and assumes exact arithmetic with the public parameters.
