# Heavy-tailed acceleration in generalized-smooth composite mirror geometry

[The main theorem](StochasticGeneralizedMirrorAccelerated.lean) proves a tunable high-probability objective guarantee for convex composite optimization in an arbitrary finite-dimensional norm. The contribution is a scope extension of generalized-smooth acceleration to non-Euclidean Bregman geometry, nonsmooth composite terms, and boundary minimizers. It does not improve the strongest checked Euclidean unconstrained rate or introduce a new acceleration principle.

The [setup](../Setups/StochasticGeneralizedMirror.lean) specifies a problem and its oracle access; it does not restrict the admissible algorithm family. The [constructed algorithm](../Algorithms/StochasticGeneralizedMirror.lean) returns `lastIterate`, the current accelerated candidate `x`. This is the last candidate in the coupled sequence, with no separate output-selection or validation procedure.

Write \(F=f+\psi\), \(B=L_0+L_1G\), \(r=1/(\alpha-1)\), and \(p=\alpha/(\alpha-1)\). Define

\[
S=1+(1+L_1R)\log(8+8\Delta/\varepsilon)
 +\sqrt{BR^2/\varepsilon}
 +256^r(\sigma R/\varepsilon)^p.
\]

The public, deterministic oracle-call budget is

\[
N=\left\lceil 2^{33}S\,[\log(2^{33}S/\delta)]^2\right\rceil.
\]

Under the stated assumptions, the actual `execute` output satisfies

\[
\Pr\{x_{\rm out}\notin Q\ \text{or}\ F(x_{\rm out})-F(x^\star)>\varepsilon\}\le\delta.
\]

Thus, for fixed \(\alpha\in(1,2]\), the bound has an additive generalized-smooth transient, an accelerated \(\varepsilon^{-1/2}\) optimization term, and the finite-moment statistical term \(\varepsilon^{-\alpha/(\alpha-1)}\), with a squared logarithmic overhead. The factor \(256^{1/(\alpha-1)}\) is explicit and is not uniform as \(\alpha\downarrow1\). It multiplies only the statistical term: when \(\sigma=0\), it disappears. The numerical constants are conservative proof constants, not a practical tuning recommendation. No optimality claim is made for the full setup or its confidence dependence.

**Assumptions and information.** The ambient space is any finite-dimensional real normed space, and gradients belong to its continuous dual. The smooth part is globally convex and continuously differentiable. Its precise generalized-smoothness condition is: for every segment from \(x\) to \(y\), if all gradient dual norms on that segment are at most \(M\), then

\[
\|df(x)-df(y)\|_*\le(L_0+L_1M)\|x-y\|.
\]

The assumptions require \(L_0>0\), \(L_1\ge0\). For twice continuously differentiable objectives, the usual norm-to-dual Hessian bound \(\|\nabla^2f(x)\|\le L_0+L_1\|df(x)\|_*\) implies this segment condition. This is the affine-link specialization of the general-norm smoothness model in [Yu et al., §2, v4 dated May 30, 2026](https://arxiv.org/html/2502.00753v4), whose conference status is verified by the [ICML 2026 proceedings](https://proceedings.mlr.press/v306/yu26s.html). The global extension of \(f\), rather than smoothness only on \(Q\), is an actual restriction of this theorem.

The feasible set \(Q\) is convex and measurable; \(\psi\) is measurable and convex on \(Q\). A mirror function \(h\) is differentiable on an open convex set \(U\). For \(z\in Q\cap U\), \(u\in Q\), its divergence satisfies

\[
D_h(u,z)\ge\tfrac12\|u-z\|^2.
\]

The oracle provides a measurable exact minimizer over \(Q\) of

\[
a\{v(u-z)+\psi(u)\}+D_h(u,z),
\]

and returns it in \(Q\cap U\). These are the strongly convex Bregman support and composite three-point conditions, not an assumed convergence property. A separate convexity assumption on all of \(Q\) is unnecessary and has been removed: the displayed support inequality and differentiability are the conditions used in the proof. No upper smoothness bound on \(h\), global Bregman diameter, bounded feasible domain, or symmetry of \(D_h\) is required. The minimizer \(x^\star\) need only lie in \(Q\), and may lie outside \(U\). Exact prox access and its existence for every positive weight and dual direction are genuine oracle assumptions.

The public inputs include bounds

\[
D_h(x^\star,x_0)\le R^2/2,\qquad
F(x_0)-F(x^\star)\le\Delta,\qquad
\|df(x^\star)\|_*\le G,
\]

with \(x_0\in Q\cap U\). The bound \(G\) is supplied to the algorithm; \(df(x^\star)\) itself is not. This is a strengthening relative to methods that adapt without a supplied solution-gradient bound. It is natural, for example, on \(Q=E\) when \(\psi\) is a known \(G\)-Lipschitz convex regularizer: optimality gives \(-df(x^\star)\in\partial\psi(x^\star)\). For constrained problems, an unbounded normal cone prevents this inference. A crude global bound on \(G\) can erase the rate's usefulness. The theorem does not establish that knowledge of \(G\) is necessary.

At each feasible query point, the jointly measurable gradient oracle is integrable and satisfies

\[
\int g(x,\omega)\,d\mu=df(x),\qquad
\int\|g(x,\omega)-df(x)\|_*^\alpha\,d\mu\le\sigma^\alpha,
\]

with the displayed moment integrable and \(1<\alpha\le2\). The sampling law is an abstract probability measure with the repository's IID structure; a product representation is derived internally from independence. There is no finite-sample-space restriction and no Banach type or vector-averaging variance assumption. These are the standard central finite-moment conditions used in robust stochastic acceleration, including [Nguyen et al., NeurIPS 2023, Appendix D](https://proceedings.neurips.cc/paper_files/paper/2023/file/4c454d34f3a4c8d6b4ca85a918e5d7ba-Paper-Conference.pdf). All model parameters, accuracy, and confidence are supplied; the result is not parameter adaptive.

**Algorithm and cost accounting.** Set

\[
\Lambda=96\sigma+\varepsilon/R
 +2(256\sigma^\alpha R/\varepsilon)^{1/(\alpha-1)},
\quad V=4\Lambda^{2-\alpha}\sigma^\alpha,
\]
\[
H=4096(1+L_1R)\log(8+8\Delta/\varepsilon)
 +1024\sqrt{BR^2/\varepsilon}
 +262144(1+\Lambda R/\varepsilon+VR^2/\varepsilon^2),
\]
\[
\ell=\log(64H/\delta),\quad m=\lceil8\ell\rceil,
\quad K=\lceil H\ell\rceil,
\quad A_0=R^2/[8(\Delta+\varepsilon)].
\]

At a phase with \(A<R^2/\varepsilon\), choose

\[
a=\min\left\{\frac{A}{1024(1+L_1R)},
\frac{\sqrt A}{128\sqrt B},
\frac{R}{65536\Lambda\ell},
\frac{\varepsilon}{65536(V+\varepsilon^2/R^2)\ell}\right\}.
\]

Form \(y=(Ax+az)/(A+a)\). Use \(m\) independent pilot gradients to choose a robust center, then clip one fresh gradient around that center at radius \(\Lambda\). Apply the exact composite Bregman prox to obtain \(z^+\), and set \(x^+=(Ax+az^+)/(A+a)\), \(A^+=A+a\). Each phase uses exactly \(m+2\) oracle calls: \(m\) pilots, one fresh gradient, and one prox call. The prox call consumes its own IID tape coordinate, although its reply is deterministic. Once the target weight is reached, the state freezes. The remaining calls in the public budget are counted dummy gradient calls at \(x_0\).

The proofs show target attainment by phase \(K\), \(K(m+2)\le N\), and equality of the frozen output under the larger execution budget. In particular, the budget is not merely a count of useful gradient samples. Its simplification uses

\[
1+\Lambda R/\varepsilon+VR^2/\varepsilon^2
 \le512\{1+256^r(\sigma R/\varepsilon)^p\},\qquad H\le2^{27}S.
\]

**Technical contribution and comparisons.** The central extension is a local-model and radius argument compatible with one-sided Bregman control and a nonstationary smooth component at the constrained/composite minimizer. Composite optimality makes the analytically tilted function \(f-df(x^\star)(\cdot)\) globally minimized at \(x^\star\). The proof derives

\[
\|df(x)-df(x^\star)\|_*^2
 \le32\{B+L_1\|df(x)-df(x^\star)\|_*\}\,[F(x)-F(x^\star)].
\]

The potential \(A[F(x)-F(x^\star)]+D_h(x^\star,z)\) controls \(z\); a separate convex-history invariant controls \(x\). A prox comparison first gives a provisional radius for the new prox point, which validates local descent before the energy bound restores the tighter radius. This avoids assuming the desired locality or an upper bound on Bregman distances. Tilting is used only in the analysis. The algorithm never evaluates the unknown \(df(x^\star)\).

Independent pilot centering, clipping, scalar dual-functional concentration, and the accelerated potential are established tools. Here they are combined with that geometric closure. The stopped error is zeroed for an invalid prior state or bad current pilot; the algorithm itself does not observe this stopping event. Adapted concentration and a first-exit induction prove the invariant. There is no appeal to a \(1/m\) vector variance bound in a general norm.

| Closest primary result | Applicable guarantee and difference |
|---|---|
| [Yu et al., v4, Theorems 3.7 and 4.2](https://arxiv.org/html/2502.00753v4) | General-norm deterministic acceleration has bound \(L D_h(x^\star,x_0)/[\eta T(T+1)]\), with \(L=\ell(4G_{\rm init})\) and the theorem's fixed tuning. Its stochastic result is nonaccelerated. The present accuracy coefficient uses \(L_0+L_1G\), with initial-gap dependence in an additive transient, under the explicit global/composite assumptions above. |
| [arXiv:2610.23301v2, October 19, 2026, Theorem 2 and Remark 1](https://arxiv.org/html/2610.23301v2) | Already gives one-phase heavy-tailed generalized-smooth acceleration in the Euclidean unconstrained case, including a linear \(L_1R\) logarithmic-gap transient. This theorem does not improve that Euclidean rate. It extends the guarantee to the stated arbitrary-mirror composite/boundary class, while requiring a supplied \(G\). |
| [Lobanov, Dvinskikh, and Gasnikov, arXiv:2609.33415v1, September 27, 2026, Theorem 9 and Appendix A](https://arxiv.org/html/2609.33415v1) | Has high-probability single-sample acceleration for Euclidean gap-dependent smoothness and mixed heavy-tailed noise. Its compact \(Q\) is an auxiliary localization set, not a composite feasible-domain theorem. Its projection/second-moment arguments do not provide the arbitrary-norm result here. We do not cover its stronger mixed-noise and interpolation conclusions. |
| [Nguyen et al., NeurIPS 2023, Theorem D.1](https://proceedings.neurips.cc/paper_files/paper/2023/file/4c454d34f3a4c8d6b4ca85a918e5d7ba-Paper-Conference.pdf) | Classical-smooth clipped accelerated mirror descent gives the optimization/statistical orders already used here, with the extra stationary-solution condition in that theorem. Substituting a localized global smoothness bound can introduce exponential dependence on \(L_1R\). It does not directly give the generalized-smooth composite/boundary guarantee. |
| [arXiv:2310.01860v2, July 24, 2024, Theorem 2.7](https://arxiv.org/html/2310.01860v2) | Robust composite acceleration and shifted clipping are prior ingredients. The theorem is Euclidean and classically smooth; its Bregman notation does not itself supply an arbitrary-norm generalized-smooth theorem. |
| [Liu et al., arXiv:2606.00520v1, May 30, 2026, Assumption 3.2 and Theorem 3.3](https://arxiv.org/html/2606.00520v1) | General-norm composite heavy-tail acceleration uses a fixed mixed \((L,M)\) model and a fractional objective-moment criterion. A direct Markov conversion has polynomial confidence costs; a logarithmic-confidence conversion needs a valid selector and its oracle cost. A small global \(L\) is not implied by this setup. |

The strongest rejection argument is incrementality: the coupled schedule and robust mirror ingredients are known. The claimed new result is the simultaneous scope and geometry-sensitive bound, not the ingredients individually. In particular, inability to restart entropy geometry is not a novelty argument against the closest one-phase Euclidean baseline, which already avoids restarts.

**Meaningful instances and improvement regimes.** Dense, interacting exponential risks provide a nonlinear family in every finite dimension:

\[
f(x)=\sum_j w_j e^{a_j^\top x},\qquad \psi(x)=\lambda\|x\|_1,
\quad w_j>0,\quad\lambda>0,\quad\|a_j\|_\infty\le A,\quad a_{j1}\ge b>0.
\]

Rows may be nonparallel and full rank. In the \(\ell_1/\ell_\infty\) geometry, \(\|\nabla^2 f(x)\|_{1\to\infty}\le A^2\sum_jw_je^{a_j^\top x}\) and \(\|df(x)\|_\infty\ge b\sum_jw_je^{a_j^\top x}\), giving \(L_1=A^2/b\) and any positive \(L_0\). The composite objective is coercive and admits a minimizer, with the known bound \(G=\lambda\). For a fully specified mirror instance, take \(Q=U=E\), \(x_0=0\), and \(h(x)=\|x\|_{p_0}^2/[2(p_0-1)]\), with \(1<p_0\le2\). Writing \(W=\sum_jw_j\), valid bounds are \(\Delta=W\), \(R=W/[\lambda\sqrt{p_0-1}]\), \(G=\lambda d^{1-1/p_0}\), and \(L_1=d^{2-2/p_0}A^2/b\). Coercivity gives \(\|x^\star\|_1\le W/\lambda\), which supplies the stated initial divergence bound. For \(d\ge3\), choosing \(p_0=1+1/\log d\) keeps \(d^{1-1/p_0}<e\) and introduces only a \(\sqrt{\log d}\) factor in this radius bound. An additive, independent, mean-zero dual noise with finite \(\alpha\)-moment supplies the stated stochastic oracle; ordinary component sampling need not have a uniform moment bound on this unbounded domain. This avoids a supplied solution or a quadratic/separable restriction. The theorem assumes exact access to the associated prox; no efficient implementation of every such prox is asserted.

For an explicit stochastic comparison on this same family, take additive noise \(\zeta=\tau Zs\), where \(s\) has independent uniform signs and is independent of a centered scalar \(Z\) with \(\mathbb E|Z|^\alpha=1\). Each query uses an independent pair. The exact dual moment scales are \(\sigma_{p_0^*}=\tau d^{1-1/p_0}<e\tau\) and \(\sigma_2=\tau\sqrt d\). With \(p_0=1+1/\log d\), the supplied radius bounds above give
\[
\sigma_{p_0^*}R_{p_0}\le e\tau(W/\lambda)\sqrt{\log d},
\qquad \sigma_2R_2=\tau(W/\lambda)\sqrt d,
\]
where the Euclidean comparison uses its valid supplied bound \(R_2=W/\lambda\). For fixed \(\alpha\), fixed positive \(\tau\), and sufficiently small accuracy so that the statistical term dominates the transient and optimization terms, the generic statistical upper-bound parameters therefore differ by a factor of order \((d/\log d)^{\alpha/[2(\alpha-1)]}\), up to constants and logarithmic overhead. This compares the stated parameter-dependent guarantees using these supplied radius bounds; it is not a lower bound, a claim that the radius bounds are tight, or universal dominance over optimally preconditioned methods. It gives a concrete nonlinear composite regime where the change of geometry matters without assuming that coordinate gradients can be averaged with a dimension-free variance law. Classical localized smooth mirror methods already have this statistical term; this noise-only comparison is not an improvement over that baseline.

A separate, explicit deterministic comparison illustrates the joint curvature/radius effect. On the unit simplex in dimension \(d\ge4\), let
\[
f(x)=e^{Ma^\top x}+e^{Mb^\top x},\qquad \psi=0,
\]
where \(a_1=b_1=0\), \(a_2=b_2=1\), and all other entries lie in \([1/2,1]\), with nonparallel rows. Take \(M\ge1\), the uniform start, and entropy geometry. The unique minimizer is \(e_1\), which is a boundary point. Valid parameters are \(L_0=M^2\), \(L_1=M\), \(G=2M\), \(B=3M^2\), \(R^2=2\log d\), and \(\Delta=2e^M-2\). Indeed the gradient infinity norm is \(M(e^{Ma^\top x}+e^{Mb^\top x})\), and the Hessian norm from \(\ell_1\) to \(\ell_\infty\) is \(M\) times that quantity. In contrast, any classical smoothness constant on the simplex in this geometry is at least \(M^2e^M/2\), by the feasible direction \(e_2-e_1\) at \(e_2\). An ambient Euclidean generalized-smooth pair satisfies \(B_2\ge M^2(d-2)/4\) at the minimizer, while its distance from the start is exactly \(\sqrt{1-1/d}\). Thus the radius does not cancel the curvature comparison.

For the concrete joint regime \(M=\log d\), \(\varepsilon=1/d\), \(\sigma=0\), and fixed confidence, our displayed budget is \(O(\sqrt d(\log d)^{7/2})\). The corresponding curvature-distance terms in the ambient Euclidean and fixed-classical-smoothness mirror bounds are respectively \(\Omega(d\log d)\) and \(\Omega(d(\log d)^{3/2})\), before their other nonnegative terms or confidence overheads. This compares those theorem formulas, not all possible adaptive local-curvature methods. The minimizer is deliberately easy to identify if the coefficients are available; this example is not an oracle lower bound or evidence of intrinsic hardness. It demonstrates a simultaneous parameter regime and the boundary scope of the general theorem, which does not impose this special feature structure.

Compared with a fixed-curvature localization bound \(L_{\rm loc}\), an improvement is possible when the additive transient and statistical cost are smaller than \(R\sqrt{L_{\rm loc}/\varepsilon}\), while \(B\ll L_{\rm loc}\). For small \(L_1R\), large supplied \(G\), or dominant noise, the result need not improve an existing bound. The method is not adaptive to unknown \(G,\sigma,\alpha,R,\Delta\), and no expected-objective or almost-sure guarantee is inferred from its high-probability statement.

Literature screening used the publicly available 2025–2026 ICML, ICLR, and NeurIPS collections, roughly two years of arXiv work and revisions, and older primary references. The comparisons above were rechecked through November 12, 2026. Some OpenReview/ICLR pages and conference-index requests were inaccessible or intermittently failed; coverage is not claimed exhaustive. Papers cited only through arXiv are treated as preprints unless their conference status is separately verified. The Lean proof verifies the stated mathematics; research novelty and significance remain separate review questions.
