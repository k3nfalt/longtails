# Stochastic fixed points in smooth Banach geometry

The [Lean theorem](StochasticSmoothBanachFixedPoint.lean) proves an RMS fixed-point residual guarantee for whole-space nonexpansive maps in finite-dimensional real normed spaces with a smooth squared norm. The claimed research contribution is an additive, rather than multiplicative, stochastic oracle cost beyond Hilbert geometry. The proposed gain is in the accuracy exponent under a standard geometric assumption; neither recursive anchoring nor the smooth-norm inequality is new.

## Problem and precise guarantee

The [setup](../Setups/StochasticSmoothBanachFixedPoint.lean) assumes a map \(T:E\to E\) satisfying
\[
\|T(x)-T(y)\|\leq\|x-y\|,
\qquad T(x_\star)=x_\star,
\qquad \|x_0-x_\star\|\leq R.
\]
The squared norm has a continuous duality map \(J:E\to E^*\), with \(\|J(x)\|_*\leq\|x\|\), such that
\[
\|x+y\|^2\leq\|x\|^2+2J(x)[y]+C\|y\|^2,
\qquad C\geq1.
\]
This is classical 2-smooth norm geometry, independent of the algorithm. For finite-dimensional \(\ell_p\), \(2\leq p<\infty\), it holds with \(C=p-1\). The exact primary derivation is Ben-Tal, Margalit, and Nemirovski, [*The Ordered Subsets Mirror Descent Optimization Method with Applications to Tomography*](https://www2.isye.gatech.edu/~nemirovs/SIOPT_MD_2001.pdf), SIAM Journal on Optimization 12(1), 2001, Appendix 1, Section 8, equations (43)–(44). Their notation uses the dual exponent for this smoothness inequality. The abstract smooth-norm theorem is formalized here; the cited \(\ell_p\) geometric certificate is not separately formalized.

The oracle is jointly measurable and satisfies, for every query \(x\),
\[
\int g(x,\omega)\,dp(\omega)=T(x),\qquad
\int\|g(x,\omega)-T(x)\|^2\,dp(\omega)\leq\sigma^2.
\]
Vector integrability and integrability of the squared centered norm are explicit assumptions. Samples are IID under an abstract probability law \(P\); the proof derives the needed product laws internally. There is no finite-sample-space restriction, bounded-noise assumption, or regularity assumption on individual sampled maps. The algorithm knows \(x_0,R,C,\sigma,\epsilon\), with \(R,\sigma\geq0\) and \(\epsilon>0\), and uses only oracle replies. It does not know \(x_\star,T\), or \(J\).

For the returned last point \(Z\), the theorem establishes measurability, integrability, and
\[
\int\|T(Z)-Z\|^2\,dP\leq\epsilon^2
\]
within the explicit total oracle budget
\[
\boxed{\left\lceil2^{20}
\left(1+\frac R\epsilon+\frac{C\sigma^2}{\epsilon^2}\right)
\left(1+\log\left(1+\frac{16R}\epsilon\right)\right)^4\right\rceil.}
\]
The formal successful-output law also includes the algorithm's trivial deterministic seed. All calls, including padding after the final stage, are counted. There is no claim that the large universal constant or logarithmic power is sharp.

## Algorithm and proof

The [algorithm](../Algorithms/SmoothBanachAnchoring.lean) uses recursive anchors and damped stochastic Picard steps. Put
\[
m=\lceil\log_2(\lceil16R/\epsilon\rceil+1)\rceil,\quad S=m+1,\quad
 a_j=2^{j-m},\quad
 \delta=\frac1{1+2^m+1024C\sigma^2S^2/\epsilon^2},\quad
 N=\lceil8S/\delta\rceil.
\]
The implementation uses `Nat.clog` for the displayed integer logarithm. Initially \(b_0=a_0x_0\). Stage \(j=0,\ldots,m\) performs \(N\) fresh single-call updates
\[
x^+=\bigl(1-\eta_j(1+a_j)\bigr)x+\eta_jg(x,\xi)+\eta_jb_j,
\qquad \eta_j=\delta/a_j.
\]
It returns the stage's last point \(z_j\), sets \(b_{j+1}=b_j+a_jz_j\), and starts the next stage at \(z_j\). The overall output is \(z_m\). `execute` runs this state machine; after \(SN\) useful calls it freezes its state while any remaining budgeted calls are still charged.

The technical combination is a stochastic contraction estimate in the original norm and a metric recursive-anchor argument. For
\(H_j(x)=(1+a_j)x-T(x)-b_j\), Banach contraction gives a unique zero \(u_j\) and an inverse-Lipschitz bound with constant \(1/a_j\). The noiseless damped map contracts by \(1-\delta\). Smoothness of the squared norm cancels the centered fresh noise without requiring a Hilbert inner product, giving
\[
 a_j^2\mathbb E[\|z_j-u_j\|^2\mid\mathcal F_j]
 \leq \frac{a_j^2\|x_j-u_j\|^2}{64S^2}+C\delta\sigma^2.
\]
Here \(\mathcal F_j\) is the history before stage \(j\); its initial point, anchor, and exact zero are measurable with respect to this history. Changing the anchor moves its exact zero by at most half the stage error. Thus normalized state energy has drift at most \(V_j/4+3\epsilon^2/256\), starting below \(\epsilon^2/64\). Consequently every stage satisfies
\[
\mathbb E[a_j^2\|z_j-u_j\|^2]\leq\epsilon^2/(256S^2).
\]
A telescoping anchor correction bounds the original residual by the sum of these weighted errors plus the initial regularization bias. Squaring and integrating gives the stronger intermediate bound \(17\epsilon^2/32\). No almost-sure warm-start or bounded-iterate hypothesis is inserted to justify this argument.

[Norm geometry and anchor lemmas](../Proofs/SmoothBanachAnchoring.lean), [noise cancellation](../Proofs/SmoothBanachNoise.lean), [inner iteration](../Proofs/SmoothBanachIteration.lean), [epoch drift](../Proofs/SmoothBanachProcess.lean), [IID sampling](../Proofs/SmoothBanachSampling.lean), [terminal recovery](../Proofs/SmoothBanachTerminal.lean), [accuracy](../Proofs/SmoothBanachAccuracy.lean), [execution equivalence](../Proofs/SmoothBanachExecution.lean), and [budget algebra](../Proofs/SmoothBanachBudget.lean) supply the supporting formal proof. The algorithm's tuning inequalities are proved [separately](../Proofs/SmoothBanachTuning.lean).

## Closest results and improvement regimes

The comparison below uses primary versions checked on 26 October 2026. The three 2026 fixed-point papers are arXiv preprints; no conference acceptance is asserted for them.

| Result | Scope and accuracy | Relevant oracle bound |
|---|---|---|
| Chen and Luo, [RAIN, JMLR 25(387), 2024](https://jmlr.org/papers/volume25/22-1126/22-1126.pdf), Lemmas 3.1–3.2, Theorem 4.2, Appendix A | Hilbert monotone Lipschitz operators; stochastic residual guarantee | Near \(\epsilon^{-2}\) statistical dependence; establishes the anchoring baseline |
| Lee, [arXiv:2610.26484v1](https://arxiv.org/html/2610.26484v1), Theorem 3 | Whole-space nonexpansive maps, finite \(\ell_p\), matching-norm unbiased bounded variance; expected residual norm | \(O(R/\epsilon+(p-1)R\sigma^2/\epsilon^3)\) |
| Diakonikolas, Guzmán, Martínez-Rubio, [arXiv:2609.09524v1](https://arxiv.org/abs/2609.09524v1), Theorem 5 and Corollary 6 | Compact convex domains, type-2 geometry, retractions; high-probability residual | \(\widetilde O(D/\epsilon+D\sigma^2/\epsilon^3)\) for fixed type and retraction constants; broader domain model |
| Shehu, [arXiv:2610.00295v1](https://arxiv.org/html/2610.00295v1), Theorem 4.3 and Remark 4.4 | Whole-space 2-uniformly smooth Banach geometry | An \(\epsilon^{-4}\) bound; acknowledges stronger \(\epsilon^{-3}\) work. Theorem 4.8 and Remarks 4.9–4.10 place the RAIN \(\epsilon^{-2}\) guarantee in Hilbert spaces |
| Present theorem | Whole-space 2-smooth norm, unbiased finite variance, RMS residual | \(\widetilde O(1+R/\epsilon+C\sigma^2/\epsilon^2)\) |

In the compact-domain row, \(D\) is the domain diameter, not the initial-distance bound \(R\) used here. That row records context rather than a comparison on identical instance classes. The directly comparable improvement is for non-Hilbert finite \(p>2\), with \(C=p-1\). RMS accuracy implies expected-norm accuracy. It does not by itself provide the logarithmic-confidence high-probability guarantee of the compact-domain result. The Hilbert case \(p=2\) is already known and is not a novelty claim.

Write \(t=R/\epsilon\), \(v=(p-1)\sigma^2/\epsilon^2\), and \(L=1+\log(1+16t)\). The compared orders are \(t(1+v)\) and \((1+t+v)L^4\). For \(t\geq1\), their ratio is at most
\[
L^4\left(\frac2{1+v}+\frac1t\right)
\]
up to universal constants. Thus the gain is substantive when both \(t\) and \(v\) dominate the logarithmic factor. For fixed positive \(R,\sigma\) and finite \(p\), the accuracy exponent improves from three to two, up to logarithms. In the very small-noise regime the additional logarithms can make this bound worse. Scalar mean estimation already requires \(\sigma^2/\epsilon^2\) calls; we do not assert that every deterministic or logarithmic factor is optimal for each finite \(p\).

This is not a claim of a new outer anchoring lemma: the pertinent RAIN argument uses inverse-Lipschitz control and triangle inequalities. The new guarantee results from supplying it with a stochastic contraction solver in standard non-Hilbert smooth geometry and proving its random warm starts and terminal residual control. For a regularized contraction with strength \(a\) and target RMS distance \(r\), the straightforward per-step accuracy reduction takes \(\widetilde O(1/a)\) iterations and batches to oracle error \(ar\). Its cost is \(\widetilde O(1/a+C\sigma^2/(a^3r^2))\). Centered stochastic damping instead gives \(\widetilde O(1/a+C\sigma^2/(a^2r^2))\). With the anchor recursion targeting \(ar\) of order \(\epsilon/S\), this removes the extra initial \(1/a\) factor, of order \(R/\epsilon\), from the statistical cost. This calculation describes the checked batching reduction, not a lower bound against all batched algorithms. Hilbert norm equivalence does not supply the theorem: an \(\ell_p\)-nonexpansive map need not remain nonexpansive, and \(I-T\) need not remain monotone, in the Euclidean norm. Scaling the map changes its fixed points. Even on the subclass also nonexpansive in Euclidean norm, direct norm conversion introduces dimension factors \(d^{1/2-1/p}\) in the distance term and \(d^{1-2/p}\) in the variance term. The contribution must be judged by this scope and complexity gain, not by the formalization or by novelty of its individual ingredients.

## Nonlinear instances and limitations

Independent motivation comes from computing nonlinear implicit-network equilibria in non-Euclidean geometry. Jafarpour, Davydov, Proskurnikov, and Bullo, [*Robust Implicit Networks via Non-Euclidean Contractions*](https://papers.nips.cc/paper_files/paper/2021/file/51a6ce0252d8fa6e913524bdce8db490-Paper.pdf), NeurIPS 2021, equation (11) and Theorem 4, study this problem using weighted infinity-norm certificates. Their result motivates equilibrium computation; it is not a finite-p stochastic guarantee and is not implied by the present theorem. Nor do we claim that all their models satisfy the present smooth-norm assumptions.

A natural family is a random-feature equilibrium map
\[
T(x)=\mathbb E[v_\xi\tanh(w_\xi^\top x+b_\xi)],\qquad
\|v_\xi\|_p\leq1,\quad\|w_\xi\|_{p/(p-1)}\leq1.
\]
Dense features couple coordinates in arbitrary finite dimension. The sampled map is a bounded unbiased oracle, with centered second moment at most \(4\), independent of dimension. The mean map is nonexpansive and maps into the unit ball, so a fixed point exists by the finite-dimensional fixed-point theorem. This gives a concrete equilibrium-computation mechanism rather than an oracle engineered to satisfy a convergence conclusion. The formal theorem also allows sampled maps without these individual Lipschitz properties.

For an explicit interacting non-Hilbert example, in \(\ell_4^{16}\) let \(v_i=1/2\), \(u=(1,1/4096,\ldots,1/4096)\), \(c=(1+15/65536)^{3/4}\), and \(A=vu^\top/c\). Then \(T(x)=\tanh(Ax)\), componentwise, is \(\ell_4\)-nonexpansive and fixes zero. Its derivative at zero has Euclidean norm greater than one, and the symmetric part of \(A\) has an eigenvalue greater than one, so \(I-T\) is not Euclidean monotone. This example rules out the direct Euclidean reduction; it does not rule out every tailored change of norm for that particular map.

The theorem is whole-space. It does not cover arbitrary compact convex constraints through a generic Lipschitz retraction, and it does not improve the \(\ell_\infty\) lower bound in Diakonikolas–Guzmán–Martínez-Rubio, Theorem 13. Letting \(p\) grow increases \(C=p-1\); no uniform conclusion in \(p\) or in infinite dimension is asserted. The algorithm is tuned to known upper bounds on geometry, distance, and variance, and is not parameter-adaptive. Continuity and the dual-norm bound on \(J\) specify standard norm geometry; the stochastic recurrence itself only uses its displayed quadratic inequality. Finite dimension, completeness, Borel measurability, and second countability are explicit in the formal setup.
