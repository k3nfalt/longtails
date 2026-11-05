**Sharp nonlinear bilevel curvature and fewer total first-order calls**

The [main theorem](BilevelFirstOrderCurvature.lean) constructs the [implemented algorithm](../Algorithms/BilevelAccelerated.lean) for the [higher-smoothness bilevel specification](../Setups/HigherSmoothBilevel.lean). It bounds **total joint first-order oracle calls**, including every lower-level solve and both endpoint evaluations in each hypergradient estimate. The contribution concerns the established nonconvex–strongly-convex problem class; the specification does not restrict admissible algorithms to the construction.

Let
\[
S(x)=\arg\min_y g(x,y),\qquad F(x)=f(x,S(x)),\qquad \kappa=L/\mu\ge1.
\]
The upper and lower spaces are arbitrary finite-dimensional real Hilbert spaces, including zero-dimensional spaces. The assumptions are:

- \(f\in C^2\), \(\|Df\|\le L\), and both \(Df,D^2f\) are globally \(L\)-Lipschitz.
- \(g\in C^3\), and \(Dg,D^2g,D^3g\) are globally \(L\)-Lipschitz. For every \(x\), \(g(x,\cdot)\) is \(\mu\)-strongly convex.
- Known parameters satisfy \(0<\mu\le L\), \(\Delta>0\), \(G\ge0\), \(\varepsilon>0\), with \(F(x_0)-F(x)\le\Delta\) for every \(x\), and \(\|\nabla_y g(x_0,y_0)\|\le G\).

A query at \((x,y)\) returns \((f,g,Df,Dg)\) there, exactly. It returns neither Hessians nor Hessian-vector products. Responses must agree with these derivatives at every history and seed. The algorithm knows the displayed parameters and initial points; it does not know \(S\), a minimizer of \(F\), or the hypergradient. The formal success criterion is differentiability at the returned point and \(\|\nabla F(\widehat x)\|\le\varepsilon\). The supporting execution lemma establishes this for every seed; the public setup expresses the corresponding almost-sure statement.

These smoothness requirements are the common-constant specialization of the established \(p=2\) class in Definition 2.1 of [Chen, Ji, and Zhang, *On the Condition Number Dependency in Bilevel Optimization*, arXiv:2511.22331v4, August 11, 2026](https://arxiv.org/html/2511.22331v4). Definition 2.4 supplies the joint first-order model. No additional structural restriction, bounded cumulative error assumption, or algorithm-specific admissibility condition is imposed. Bounded \(Df\) and higher smoothness are substantive restrictions relative to the broader ordinary smooth bilevel class; this theorem does not cover that broader class. The known residual bound \(G\) is initialization information used to choose a finite inner-solve horizon.

Lean uses the maximum norm on the product of the two Hilbert spaces. Standard Euclidean product-norm assumptions imply these conditions after replacing a common derivative bound by at most four times that bound: derivative orders through four contribute at most \((\sqrt2)^4\). This conversion has no dependence on either dimension and does not change the reported parameter exponents.

Write
\[
U=\left(\frac{L\kappa^3}{\varepsilon}\right)^{1/4},\qquad
W=\Delta\sqrt{\frac{L\kappa^4}{\varepsilon^3}},\qquad
P=\kappa(1+L/\varepsilon)(1+\Delta/\varepsilon)(1+G/\varepsilon).
\]
The public budget is the single explicit formula
\[
\boxed{\left\lceil 2^{40}U(1+W)\log(2P)\right\rceil.}
\]
The Lean definition expands \(\kappa=L/\mu\); it contains no local tuning variables or opaque helpers. Its polynomial dependence is
\[
\widetilde O\!\left(
L^{1/4}\kappa^{3/4}\varepsilon^{-1/4}
+\Delta L^{3/4}\kappa^{11/4}\varepsilon^{-7/4}
\right).
\]
The first term is necessary startup/final-epoch work in this construction, not a discarded lower-order term. The logarithm retains the initial residual \(G\). The universal constant is deliberately conservative; the theorem makes no claim of practical superiority from this constant.

For \(\varepsilon<2L\kappa\), set \(q=\sqrt\kappa\), \(\mathcal L=32Lq^5\), \(\rho=512Lq^8\), \(e=\varepsilon/1024\), \(\eta=1/(4\mathcal L)\), \(B=\sqrt{e/\rho}\), and \(\sigma=e/100\). The outer method is restarted accelerated descent with momentum \(1-1/K\), where
\[
K=\left\lfloor\frac1{\sqrt{32\eta\sqrt{\rho e}}}\right\rfloor,
\qquad E=\left\lfloor\frac{\Delta\sqrt\rho}{e\sqrt e}\right\rfloor+1.
\]
It immediately restarts when the current epoch length times accumulated squared movement exceeds \(B^2\). A retained \(K\)-step epoch succeeds. Among its movements with indices \(\lfloor K/2\rfloor,\ldots,K-1\), the algorithm selects a minimum and returns the average of **all extrapolated query points up to that index**. This is not a last-iterate assertion or a selection by unobserved objective values.

Each hypergradient estimate solves the lower objectives \(g(x,\cdot)\) and \(g(x,\cdot)+f(x,\cdot)/\lambda\), then returns
\[
\nabla_x f(x,y)+\lambda\bigl(\nabla_x g(x,y)-\nabla_x g(x,z)\bigr).
\]
Here \(\lambda=1+2\kappa+16L\kappa^3/\sigma\). The inner solver restarts ordinary convex accelerated gradient descent in blocks of \(m=\lceil8\sqrt\kappa\rceil\) calls. Its number of blocks is
\[
J=\left\lceil\frac{\log(1+2LD/\tau)}{\log2}\right\rceil,
\quad \tau=\frac{\sigma\mu}{10\lambda L},\quad
D=\frac{G+LR+L/\lambda}{\mu},
\quad R=E\bigl(2B+\eta[L(1+\kappa)+\sigma]\bigr)+2B.
\]
The two solves and two final evaluations cost exactly \(2mJ+2\) joint calls per estimate. There are \(KE\) scheduled estimates. After success, state and output freeze, but the scheduled padding calls are still counted. The public budget also counts padding by `execute`. For \(\varepsilon\ge2L\kappa\), the algorithm returns \(x_0\); this branch still permits the budgeted ignored calls and is not described as a zero-call execution.

The new mathematical mechanism is the dimension-free mixed implicit-response estimate. Positivity of \(D^2_{yy}g\), together with Lipschitz continuity of \(D^3g\), controls the third-derivative tensor in the lower-Hessian energy norm. Applying this control to mixed upper/lower directions avoids treating every inverse lower Hessian independently. The proof obtains
\[
\|D^2F(x)\|\le32L\kappa^{5/2},\qquad
\|D^2F(x)-D^2F(x')\|\le512L\kappa^4\|x-x'\|.
\]
The second estimate is proved by finite differences and transport of the weighted second response. It needs no fourth derivative of \(g\) and no third derivative of \(f\). In particular, a scalar calculation or a diagonal quadratic analysis would miss the mixed-direction and moving-metric terms that must be controlled for general nonlinear objectives.

The supporting [curvature](../Proofs/BilevelCurvature.lean), [implicit estimates](../Proofs/BilevelImplicitEstimates.lean), [response transport](../Proofs/BilevelResponseTransport.lean), and [hyperobjective bounds](../Proofs/BilevelHyperobjective.lean) contain this argument. PSD derivative interpolation itself is known, including equation (48) and Lemma 4.1 of [Nesterov, *Superfast Second-Order Methods*, JOTA 191 (2021)](https://d-nb.info/1248443187/34); it is not claimed as new. Scalar conjugacy results such as Proposition 6 of [Sun and Tran-Dinh, arXiv:1703.04599v3](https://arxiv.org/html/1703.04599v3) also do not themselves supply the required general mixed response transport.

The rest of the construction uses established acceleration and penalty ideas. The [penalty proof](../Proofs/BilevelPenalty.lean) bounds exact bias by \(4L\kappa^3/\lambda\), and the [inner execution proof](../Proofs/BilevelInner.lean) adds at most \(5\lambda L\tau/\mu\). The [epoch proof](../Proofs/BilevelEpochConvergence.lean) establishes decrease at least \(eB\) on every failed epoch and gradient norm at most \(773e\) at the selected successful output. The [trajectory](../Proofs/BilevelTrajectory.lean) and [restart execution](../Proofs/BilevelRestartExecution.lean) proofs connect these claims to the actual implementation, including ties, first-step exits, and query radii. The radius is established before invoking the inner-estimator guarantee, avoiding circular accuracy assumptions. The [budget proof](../Proofs/BilevelBudget.lean) bounds the full count, not just outer iterations.

The closest comparisons are:

| Prior result | Relevant information and guarantee | Difference here |
| --- | --- | --- |
| Chen–Ji–Zhang v4, Appendix F, Theorem F.2 and estimates F.3/F.5 | Fully first-order total leading cost \(\widetilde O(\Delta L^{3/4}\kappa^{13/4}\varepsilon^{-7/4})\), using curvature orders \(L\kappa^3,L\kappa^5\). Its SOSP conclusion is stronger than the FOSP criterion here. | A factor \(\sqrt\kappa\) improvement in the leading total cost when these guarantees are used to obtain FOSP; no SOSP improvement is claimed. |
| [Yang–Luo–Li–Jordan, arXiv:2307.00126v1, Corollary 3.6 and Table 1](https://arxiv.org/html/2307.00126v1) | Upper-function gradients and Jacobian-vector calls already have exponent \(11/4\); lower gradients and Hessian-vector calls have exponent \(13/4\). | The exponent \(11/4\) is not new by itself. The improvement is in total joint **first-order** calls, with all inner work charged. |
| [Yang–Liu–Chen–Lui, arXiv:2605.06431v1, Theorems 3.4/4.3](https://arxiv.org/html/2605.06431v1) | Second-order FSBA/LFSBA; accepted ICML 2026, also checked against the [official program](https://icml.cc/Downloads/2026). | Full-gradient finite differences give a competing dimension-dependent first-order reduction, described below; the present claim is dimension-free. |

The condition-number comparison fixes the shared bound \(L\); it does not assert improvement over every specialization with heterogeneous derivative constants.

There is an important standard-reduction limitation. Let \(D_{\rm tot}=\dim X+\dim Y\). Reconstructing both Hessians at a snapshot takes at most \(2(D_{\rm tot}+1)\) joint gradient queries, with arbitrarily small deterministic error in this exact-real oracle model. Optimizing lazy refresh length gives the competing first-order bound
\[
\widetilde O\!\left(\sqrt\kappa+D_{\rm tot}
+\Delta\sqrt L\,[\kappa^3+\sqrt{D_{\rm tot}}\,\kappa^{11/4}]\varepsilon^{-3/2}\right).
\]
This is a derived finite-difference reduction, not a first-order theorem quoted verbatim from that paper. Its FOSP analysis uses the implemented lazy stopping certificate directly to repair the implication from nontermination used in Appendix D.2. Hessian reconstruction error is allocated within Lemma 4.2's tolerances; arithmetic and matrix storage are not oracle calls. Relative to the new leading term, its polynomial ratio is \((\varepsilon/L)^{1/4}[\kappa^{1/4}+\sqrt{D_{\rm tot}}]\). It can be better at sufficiently small accuracy in fixed dimension. Thus there is no claim of universal superiority over dimension-dependent simulations. The gain is meaningful for ill-conditioned problems in regimes where this ratio is large, and in a dimension-independent complexity statement. Constants, logarithms, and startup terms matter near a crossover.

A concrete nonlinear family is
\[
g(x,y)=\frac\mu2\|y\|^2+\sum_j a_j\log\cosh(c_j^Ty+d_j^Tx)-x^TBy,\qquad a_j\ge0.
\]
Dense, nonorthogonal \((d_j,c_j)\) and a dense coupling matrix give interacting coordinates. In Euclidean product norm, common derivative bounds follow from
\(\mu+\|B\|+\sum_j a_j\|(d_j,c_j)\|^2\),
\(2\sum_j a_j\|(d_j,c_j)\|^3\), and
\(6\sum_j a_j\|(d_j,c_j)\|^4\).
An upper objective formed from nonnegative weighted log-cosh validation terms plus bounded sine terms has bounded gradient, Lipschitz first and second derivatives, and a known lower bound. For a term \(w\log\cosh(v^Tz-b)\), the respective bounds are \(w\|v\|,w\|v\|^2,2w\|v\|^3\); a term \(c\sin(u^Tz)\) contributes \(|c|\|u\|^r\) at derivative order \(r\le3\). Taking the maximum of these sums and the lower-level bounds supplies \(L\), with the norm conversion above. This family models regularized nonlinear training with validation loss; it is neither quadratic nor separable.

As a sharpness diagnostic, for \(0<\mu\le1\), take \(f(x,y)=\sin y\) and \(g(x,y)=(1+\mu)y^2/2+\cos y-1-xy\). All required smoothness constants are uniformly bounded. At the point with \(S(x)=\sqrt\mu\), \(|F''(x)|\ge(2/27)\mu^{-5/2}\); at zero, \(F'''(0)=-\mu^{-3}-\mu^{-4}\). These calculations explain why the two curvature exponents cannot generally be reduced. They are not oracle-complexity lower bounds and are not a substitute for the general theorem.

No optimality claim is made. In particular, the NC-Q lower-bound class preceding Definition 2.3 of Chen–Ji–Zhang permits an infinite upper-gradient bound; its Theorem 4.2 does not automatically give a matching lower bound for the finite common-\(L\) class here. There is also no stochastic, constrained, composite, or second-order-stationarity guarantee in this theorem.

The literature assessment used independent searches of publicly available 2025/2026 ICML, ICLR, and NeurIPS material, roughly two years of arXiv submissions/revisions, and older foundational and stronger results. The three main arXiv version histories above were rechecked on November 5, 2026 UTC. The merged Chen–Ji–Zhang v4 is cited as that manuscript, rather than assigning its full contents an inferred conference status. Related recent stochastic, finite-sum, and explicit-hyper-Hessian results were checked for oracle-model collisions. One OpenReview source, `XIAta0WOJ6`, was inaccessible behind a challenge; no claim rests on its snippets. Search coverage is evidence for novelty, not a proof that every possible prior result has been found. The claimed contribution is the mixed nonlinear curvature mechanism and its total first-order consequence, not the length of the Lean formalization.
