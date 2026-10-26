# Polynomial acceleration at polylogarithmic relative precision

The [main theorem](PolylogPrecisionRelativeErrorConvex.lean) proves a dimension-independent oracle-complexity guarantee for ordinary smooth convex minimization with adversarial relative gradient errors. It uses the [specification](../Setups/SharpRelativeErrorSmoothConvex.lean) and constructs [sharpEnvelopeOutput](../Algorithms/SharpEnvelope.lean). The specification permits all oracle algorithms; it imposes no update-family restriction.

Write
\[
T=LR^2/\varepsilon,\qquad s=1+\log(2+T).
\]
If
\[
0\le\alpha\le\frac1{100(33s)^{12}},
\]
the returned point satisfies \(f(x_{\mathrm{out}})-f(x_\star)\le\varepsilon\) within
\[
\boxed{K=\left\lceil8(33s)^{20}(2+T)^{5/8}\right\rceil}
\]
physical gradient-oracle calls. Thus a fixed polynomial improvement over nearly linear complexity is possible when the allowed relative error decreases only as an inverse power of \(\log T\). The contribution is this complexity guarantee and its nearly lossless recursive oracle construction. It is not a new objective class, the use of averaging by itself, or the formalization of an existing theorem.

## Assumptions, information, and examples

The objective is differentiable on a real Hilbert space and satisfies, for every \(x,y\),
\[
0\le f(y)-f(x)-\langle\nabla f(x),y-x\rangle\le L\|y-x\|^2/2.
\]
A global minimizer \(x_\star\) exists with \(\|x_0-x_\star\|\le R\). The theorem includes general nonlinear functions in every finite dimension and also complete infinite-dimensional inner-product spaces. There is no strong convexity, PL condition, bounded level set, separability, quadratic structure, or bound on the iterates.

Every reply obeys
\[
\|g_k(x)-\nabla f(x)\|\le\alpha\|\nabla f(x)\|.
\]
It may be biased, vary with the call index, and depend arbitrarily on its seed. The execution proof holds for every seed sequence, so the specification's almost-sure accuracy follows from a pathwise statement. No unbiasedness, variance, independence, or stochastic expectation hypothesis is used. Adaptive adversarial replies along the deterministic execution are covered. The algorithm knows \(L,R,\varepsilon,x_0\); \(\alpha\) is public but the constructed method uses the displayed design precision instead. It receives no function values, exact gradients, minimizers, or proximal-oracle answers.

The objective and relative-error conditions are standard: see [Hallak–Levy, ICML 2024](https://proceedings.mlr.press/v235/hallak24a.html), and [Vasin–Gasnikov, arXiv:2603.12376v1](https://arxiv.org/abs/2603.12376v1), equations (2), (3), and (10). The new restriction is solely the explicit relationship between allowed error and requested accuracy. It changes the oracle-precision regime, not the objective class. The exponents and constants in that sufficient relationship are proof choices, not asserted necessities.

A concrete nonlinear family is
\[
f(x)=\sum_{j=1}^m\log\cosh(a_j^\top x-b_j)
\]
with a dense full-column-rank matrix \(A\). It is coercive, has a minimizer, and has Hessian \(A^\top\operatorname{diag}(\operatorname{sech}^2(Ax-b))A\), bounded above by \(\|A\|^2I\). Coordinates interact, and curvature varies with the iterate. Its Hessian approaches zero along generic rays, so global strong convexity is unavailable. Bounded gradients and unbounded objective values exclude global PL. The dimension enters only through \(L\) and \(R\), not an additional factor in the budget.

Relative coordinate quantization is one independently motivated oracle mechanism: round each nonzero gradient coordinate's magnitude down to a power of \(1+\alpha\), preserving its sign. Coordinatewise error at most \(\alpha\) times that coordinate's magnitude gives the required Euclidean norm bound. This mechanism is biased and requires no cancellation. It models relative communication precision, not a reduction in the cost of computing an exact gradient before compression. Finite floating-point range, underflow, and cancellation inside a gradient computation are not automatically covered. The sufficient precision corresponds to \(O(\log\log T)\) accuracy bits in an ideal relative-precision model.

## Constructed algorithm and physical cost

Set
\[
b=\lceil32s\rceil,\quad q=4b^{32}-1,\quad
D=\left\lceil\frac{\log(2+T)}{\log q}\right\rceil,\quad
n=b^{20},\quad\theta=\frac1{4b^{16}},
\]
\[
L_i=L/q^i,\qquad
\beta_i=\frac{1+i/(D+1)}{100b^{12}},\qquad
\tau=\frac1{8(D+1)}.
\]
The analysis defines \(f_0=f\) and \(f_{i+1}\) as the Moreau envelope of \(f_i\) with regularization coefficient \(\mu=L_{i+1}\). These exact envelopes and their minimizers are proof objects. The algorithm constructs their approximate gradients recursively from physical replies.

A level-\((i+1)\) gradient request at center \(c\) approximately minimizes
\(h(x)=f_i(x)+\mu\|x-c\|^2/2\). A level-\(i\) reply is augmented by \(\mu(y-c)\). There are two phases, each using exactly \(n\) such requests:

1. Warm start: the repository's robust accelerated inner method, with smoothness \(L_i+\mu\), strong convexity \(\mu\), and relative parameter \(2\beta_i\). Its momentum is explicitly
   \[
   \vartheta_i=\left(4\sqrt{\frac{L_i+\mu}{\mu(1-2\beta_i)}}+
   \frac{64\beta_i^2(L_i+\mu)}{\mu(1-2\beta_i)}\right)^{-1}.
   \]
2. Reset both accelerated states to the warm-start primal point. At each of the next \(n\) steps, use
   \[
   y=(x+\theta z)/(1+\theta),\quad
   x^+=y-\widetilde\nabla h(y)/(L_i+\mu),\quad
   z^+=(1-\theta)z+\theta y-(\theta/\mu)\widetilde\nabla h(y).
   \]
   Return the arithmetic average of the \(n\) **pre-update primal states** \(x\), not the query points \(y\).

If the averaged point is \(\bar x\), the approximate envelope-gradient reply is \(\mu(c-\bar x)\). To obtain an original-objective output, start at \(x_0\) on level \(D\) and apply these approximate proximal solves successively down to level zero. The final recovered point is the named output.

Let \(m=2n\). A level-\(i\) request uses exactly \(m^i\) physical calls. Recovery therefore uses
\(\sum_{i=1}^D m^i\le2m^D\) calls, including all warm starts and averages. Since \(m^8\le q^5\), \(q^D\le q(2+T)\), and \(q^{5/8}\le4b^{20}\), this is at most the unrounded public budget. The framework's execution to budget \(K\) may make extra fallback queries after the plan finishes; those calls are included in \(K\), and they cannot change its stored output. No inner work is treated as a free proximal oracle. Arithmetic, storage, and total running time are not bounded by the oracle theorem.

## New proof mechanism

Let \(p=\operatorname{prox}_{f_i/\mu}(c)\), \(w=\nabla f_i(p)=\mu(c-p)\), and \(H=h-h(p)\). Monotonicity gives the sharper decomposition
\[
\|\nabla f_i(y)-w\|\le\|\nabla h(y)\|,
\]
so for error \(e\),
\[
\|e\|^2\le(1+\tau)\beta_i^2\|w\|^2+
(1+1/\tau)\beta_i^2\|\nabla h(y)\|^2.
\]
For \(V=H(x)+\mu\|z-p\|^2/2\), the second-phase update satisfies
\[
V^+-V+\theta H(x)\le
A\|e\|^2-\frac{\|\nabla h(y)\|^2}{4(L_i+\mu)},
\]
\[
A=\frac\theta{2\mu}+\frac3{4(L_i+\mu)}+
\frac{\theta^3}{2\mu(1-\theta^2)}
\le\frac\theta{2\mu}(1+\tau).
\]
The proof retains both the strong-convexity mixing dissipation and the gradient-descent dissipation. Two separate square completions control the error pairings with \(z-p\) and \(y-z\). The retained gradient term absorbs the second term in the relative-error decomposition when \(\beta_i^2\le\tau\theta/2\).

Warm start gives \(H(x_{\mathrm{warm}})\le128\beta_i^2\mu\|c-p\|^2\); resetting the auxiliary state gives \(V_0\le256\beta_i^2\mu\|c-p\|^2\). The explicit iteration counts ensure \(n\theta\tau\ge512\). Summing the certificate at the actual indexed execution, and using a supporting affine inequality at its returned average, yields
\[
H(\bar x)\le\frac{((1+2\tau)\beta_i)^2\mu}{2}\|c-p\|^2.
\]
Consequently the envelope error amplifies by at most \(1+2\tau\), and
\((1+2\tau)\beta_i\le\beta_{i+1}\). This permits \(D=\Theta(\log T/\log\log T)\) levels without exponentially worsening precision. Recovery multiplies objective gaps by \(1+\beta_i^2\); the proved product is at most \(1+D/(D+1)<2\). The top envelope's initial gap is at most \(L_D R^2/2\), completing the original-objective guarantee.

The [energy proof](../Proofs/SharpEnvelopeEnergy.lean), [finite inner execution](../Proofs/SharpEnvelopeInner.lean), [recursive convergence](../Proofs/SharpEnvelopeConvergence.lean), [parameter inequalities](../Proofs/SharpEnvelopeParameters.lean), [budget](../Proofs/SharpEnvelopeBudget.lean), and [execute bridge](../Proofs/SharpEnvelopeGuarantee.lean) establish these steps separately. No convergence estimate is assumed in the setup. An admissible discontinuous noisy oracle need not have a zero even after regularization; the finite averaging proof never assumes one.

## Closest guarantees and standard-reduction checks

Comparisons below use objective error \(\varepsilon\), radius \(R\), and physical gradient calls. A source's stronger oracle or smaller precision regime is retained.

| Baseline | Guarantee and comparison |
|---|---|
| Vasin–Gasnikov, arXiv:2603.12376v1, Theorems 7.2 and 9.3 | Regularized RE-AGM gives \(O(\max\{\sqrt T,\alpha T\}\log T)\) in its stated small-error range. At inverse-polylogarithmic \(\alpha\), its exponent in \(T\) remains one. This is a preprint, not a verified conference acceptance. |
| [AcceleratedRelativeErrorConvex](AcceleratedRelativeErrorConvex.md), existing repository result | \(O(\sqrt{T/(1-\alpha)}+\alpha^2T/(1-\alpha))\), with the same radius information and arbitrary relative errors. The present result improves the large-\(T\), inverse-polylogarithmic-precision regime, not all parameter values. |
| Two-level proposition in that existing note | \(O((\alpha^{-2}+\sqrt T+\alpha^4T)\log(2+T/\alpha^2))\). It is a checked paper derivation, not its Lean theorem. This is stronger than the single-loop comparator and still has exponent one at inverse-polylogarithmic precision. |
| [RecursiveRelativeErrorConvex](RecursiveRelativeErrorConvex.md), existing repository result | \(T^{1/2+o(1)}\), but requires \(\alpha\le e^{-8(1+\sqrt{\log(2+T)})}/100\). It can outperform this result where that much smaller error is available. Its factor-16 oracle degradation does not justify the present precision regime. |
| [Gürbüzbalaban, arXiv:2309.11481v5](https://arxiv.org/abs/2309.11481v5), Proposition 5.3 and Corollary 5.4; MOR 2025 | Already analyzes averaged accelerated output under adversarial additive disturbances. The displayed nonlinear small-step gain is \(2\sqrt5/\sqrt\mu\), with a constant gap from \(1/\sqrt{2\mu}\). Averaging and robust-control certificates are established ideas. The new step is a near-one transfer factor with retained gradient dissipation, enabling the recursive complexity improvement. |

For \(\alpha\) equal to a fixed positive constant times \(s^{-12}\) within the admissible threshold, the new budget is \(O(T^{5/8}s^{20})\), versus \(O(T/s^{24})\) for the single-loop bound and \(O(T/s^{47})\) for the two-level bound. Their asymptotic ratios therefore tend to zero, respectively like \(s^{44}/T^{3/8}\) and \(s^{67}/T^{3/8}\), up to constants. These comparisons describe diagonal precision/accuracy regimes; they do not say that a fixed positive \(\alpha\) permits arbitrarily small \(\varepsilon\) under this theorem. The exact-gradient benchmark remains \(\Theta(\sqrt T)\); a factor \(T^{1/8}\) times logarithms remains, and optimality at polylogarithmic precision is unresolved.

Repeated batching cannot reduce adversarial bias: identical admissible replies may recur. Clipping cannot manufacture a smaller norm-relative error bound. Ordinary regularization turns relative error in \(\nabla f\) into mixed error for \(\nabla h\), so substituting a strongly convex theorem without controlling that transformation is invalid. Fixed-factor inner transfer over \(D\) levels requires precision smaller by that factor to the power \(D\). At \(\alpha\asymp s^{-12}\), only \(O(\log\log T)\) such levels keep the effective relative error small; the previous mixed-error inner estimates then do not certify a fixed polynomial improvement. This is a limitation of those estimates, not a lower bound for their algorithms.

Other important reductions require information absent here:

- [Catalyst, JMLR 2018](https://jmlr.org/papers/v18/17-748.html), criterion C2 and Theorem 7, uses a decaying inner-error schedule in the convex accelerated guarantee; a persistent inherited relative floor does not directly satisfy it.
- [Barré–Taylor–Bach, arXiv:2106.15536v3](https://arxiv.org/abs/2106.15536v3), Section 2.3, equations (3)–(5), and the accelerated proximal-hybrid-extragradient framework require a primal-dual or enlarged-subgradient certificate. For \(f(x_1,x_2)=\log\cosh x_1\), the valid reply \((\tanh x_1,\alpha\tanh x_1)\) is not any finite-\(\epsilon\) subgradient when \(x_1\ne0\): its nonzero flat-direction component makes the conjugate infinite. Norm-relative proximity alone supplies no such certificate.
- [Burns–Liang, arXiv:2602.17878v1](https://arxiv.org/abs/2602.17878v1), equations (50)–(52) and the FLOrA framework, requires certified global lower models; its restarted accelerated-gradient realization uses exact gradients. A proximal objective-gap consequence does not imply that the required lower model is available from this oracle.
- [Bollapragada–Gupta, COAP 2026](https://link.springer.com/article/10.1007/s10589-026-00788-y), Condition 2.1 and Theorem 3.8(ii), allows bias but requires a progressively vanishing relative-error schedule with weighted square summability for convex acceleration. The fixed per-run precision here does not provide that schedule. The June 16 correction concerns labels and a section reference.
- [Khanh–Mordukhovich–Tran, JOTA 208:40](https://doi.org/10.1007/s10957-025-02864-5), Theorems 3.5–3.6, treats a comparable relative-error model, but gives asymptotic and PLK-dependent guarantees rather than this uniform convex-radius oracle complexity.

The lower-bound claim in Vasin–Gasnikov's Appendix G is not used to establish optimality or impossibility. Its Lemma G.1 embeds bounded gradient errors into a larger inexact-model oracle class; a lower bound for that larger class does not automatically hold for the embedded subclass. This prevents using the claimed bound as a reason to reject a stronger upper bound, but does not establish a replacement lower bound.

## Coverage and limitations

The research and independent review surveys were conducted on October 26, 2026 UTC. They targeted ICML 2025/2026, ICLR 2025/2026, NeurIPS 2025/2026, and roughly the preceding two years of arXiv submissions and revisions, then followed relevant older citations. Official PMLR, OpenReview proceedings, and NeurIPS Downloads records were used to distinguish accepted papers from submissions. This was a topic-focused survey, not a claim to have read every conference paper. Current heavy-tail, generalized-smoothness, monotone-operator, and second-order-smooth nonconvex results informed candidate screening; none is imported under mismatched assumptions.

The key relative-error preprint remains arXiv:2603.12376v1 (March 12, 2026). The latest checked relative-minimax version is arXiv:2503.06628v3 (December 9, 2025). The robust-control comparison used arXiv:2309.11481v5, the institutional 47-page manuscript, and the published MOR supplement; the final journal main text was not accessible. Its follow-up arXiv:2509.13628v3 (January 13, 2026), Corollaries 5.4–5.5, retains the conservative gain coefficients in a stochastic risk-sensitive setting. The latest checked Burns–Liang version is v1. Bollapragada–Gupta's published corrected full text and the author-hosted final JOTA paper were read. Some NeurIPS virtual pages and an unrelated OpenReview CompSGD PDF were inaccessible; official conference lists were available. Novelty is assessed from positive theorem/model comparisons and explicit reduction obstructions, not missing search hits.

Constants and logarithmic powers are conservative. The certified gain over prior bounds is asymptotic and may require extremely large \(T\); no practical speedup is claimed. The result does not improve the best exact-gradient rate, handle arbitrary fixed relative precision asymptotically, remove knowledge of \(L,R,\varepsilon\), or cover an absolute noise floor, constrained objectives, or non-Euclidean geometry. No new oracle-precision lower bound is proved. The algorithm's nested execution can require substantial arithmetic and storage. Zero relative error and \(R=0\) are included without division by the actual error or distance; positive design tolerances and \(2+T\) make initialization and all phase counts well-defined.
