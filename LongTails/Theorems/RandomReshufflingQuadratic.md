# A larger stable step for random reshuffling with indefinite quadratic components

The [main Lean theorem](RandomReshufflingQuadratic.lean), `OracleTemplate.QuadraticFiniteSum.result`, proves expected objective accuracy for the last epoch endpoint of ordinary random reshuffling. Its contribution is an improved upper bound on the number of epochs needed for the quadratic rate as the ratio of the condition number to the number of components grows. It does not improve the accuracy exponent, establish a lower bound, or characterize the Hölder-curvature threshold for nonquadratic objectives.

## Setup and algorithm

The [setup](../Setups/QuadraticFiniteSum.lean) specifies

\[
 F(x)=\frac1n\sum_{i=1}^n\left(\tfrac12\langle x,A_i x\rangle+\langle b_i,x\rangle\right),
 \qquad A_i=A_i^*,\quad \|A_i\|\le L,\quad \bar A\succeq\mu I.
\]

Here \(n\ge1\), \(0<\mu\le L\), and the space is a real Hilbert space. A minimizer \(x_*\) satisfies \(\|x_0-x_*\|\le R\) and \(\max_i\|A_i x_*+b_i\|\le G\), where \(R,G\ge0\). These are bounds supplied to the algorithm, together with the target \(\varepsilon>0\). Neither the minimizer nor the matrices or offsets are supplied. One oracle call at \((i,x)\) returns exactly \(A_i x+b_i\). Component convexity, commutation, interpolation, and bounded trajectories are not assumed.

These assumptions are the quadratic model of [Ahn, Yun, and Sra, NeurIPS 2020, Theorem 2 and Appendix B](https://arxiv.org/pdf/2006.06946), with explicit bounds on initialization and the component gradients at the optimum. Their Appendix B uses this same optimum-gradient bound after translating the minimizer to zero. The Hilbert-space formulation adds no restriction in finite dimension. Positive \(\mu\), bounded component Hessians, and quadratic structure are essential to the argument here; the result does not extend automatically to general smooth finite sums.

Indefinite components arise naturally in covariance-corrected least squares: a component Hessian can be \(z_i z_i^\top-\Sigma_w+\lambda I\). Ridge regularization can make the average positive definite even when some components remain indefinite. The covariance correction is used in [Loh and Wainwright, JMLR 2015, Section 3.2, equations (11)–(13)](https://jmlr.org/papers/volume16/loh15a/loh15a.pdf). Our theorem concerns its strongly convex quadratic regime, not their entire constrained nonconvex statistical problem.

The [algorithm](../Algorithms/QuadraticReshuffling.lean) draws an independent uniform permutation each epoch and performs \(x\leftarrow x-\eta(A_i x+b_i)\) once for every component. It returns the final endpoint, without averaging or restarting. Define

\[
 q=\frac{32L}{\mu}+\frac{64L^{3/2}G}{n\mu^2\sqrt\varepsilon}
       +4\left(\frac{L^3G^2}{n\mu^4\varepsilon}\right)^{1/3},
 \qquad \eta=\frac1{\mu n q},\qquad
 K=\left\lceil2q\log\left(1+\frac{LR^2}{\varepsilon}\right)\right\rceil.
\]

The private random seed is a uniformly distributed tuple of \(K\) permutations, which is exactly independent uniform reshuffling. The framework's additional oracle randomness is immaterial because every admissible oracle returns the exact component gradient. The [execution proof](../Proofs/ReshufflingExecution.lean) connects the query program to these iterates and counts exactly \(nK\) calls, including all calls in every epoch. If \(R=0\), then \(K=0\) and the algorithm returns the supplied initial optimum.

## Guarantee and mechanism

For any constant step with \(0\le\eta\) and \(\eta nL\le1/32\), the supporting proofs establish

\[
 \mathbb E[F(y_K)-F(x_*)]
 \le \frac{LR^2}{2}(1-\eta n\mu/2)^K
       +\frac{512\eta^2L^3G^2}{\mu^2}
       +\frac{4\eta^3 n^2L^3G^2}{\mu}.
\]

The chosen parameters make this at most \(\varepsilon\). The public budget is the single explicit expression

\[
 n\left\lceil\left(\frac{64L}{\mu}
 +\frac{128L^{3/2}G}{n\mu^2\sqrt\varepsilon}
 +8\left(\frac{L^3G^2}{n\mu^4\varepsilon}\right)^{1/3}\right)
 \log\left(1+\frac{LR^2}{\varepsilon}\right)\right\rceil.
\]

Writing \(\kappa=L/\mu\), \(A=L^{3/2}G/(\mu^2\sqrt\varepsilon)\), and \(B=(n^2L^3G^2/(\mu^4\varepsilon))^{1/3}\), the cost is
\(O(n+(n\kappa+A+B)\log(1+LR^2/\varepsilon))\).

The new technical step is a uniform mean-square contraction

\[
 \mathbb E_\pi\|P_\pi v\|^2\le(1-\eta n\mu)\|v\|^2,
 \qquad P_\pi=(I-\eta A_{\pi(n)})\cdots(I-\eta A_{\pi(1)}),
 \qquad \eta nL\le1/32.
\]

The [homogeneous proof](../Proofs/ReshufflingHomogeneousEnergy.lean) expands the palindromic product \(P_\pi^*P_\pi\). The comparison polynomial is \(\sum_{m=0}^{2n}(-2\eta)^m S^m/m!\), where \(S=\sum_i A_i\). After averaging, distinct-label terms agree exactly with those of this polynomial at every degree; both distinct-label parts vanish above degree \(n\). The full identity adds the repeated-label terms from the palindrome and subtracts those from the comparison polynomial. At degree two, the difference is the negative term \(-\eta^2 Q\), where \(Q=\sum_i A_i^2\). Higher-degree repeated-label terms are bounded in the quadratic form of \(Q\), rather than by \(nL^2\|v\|^2\). Permutation symmetry gives uniform endpoint marginals; endpoint Cauchy–Schwarz and collision counts then make the entire remainder absorbable by \(\eta^2Q\) whenever \(\eta nL\) is a small universal constant. The pure powers are controlled using positivity of \(S\).

The palindromic expansion and its negative second-order term are already present in Ahn–Yun–Sra, Appendix B. Endpoint energy bounds and absorption by a negative quadratic term also appear in [Peng, Section 4.2, Lemma 7](https://arxiv.org/html/2607.22620). Those ingredients individually are not claimed as new. The contribution is their collision-specific use for the *Gram product*, yielding a conditioning-independent \(1/(nL)\) mean-square stability radius. Peng controls a mean product in a positive contraction setting at a radius of order \(n^{-2}\); that theorem does not imply this Gram-product estimate for indefinite Hessians. A direct tensor lift need not preserve its assumptions: for scalar Hessians \(L,-L\), the mean of the squared step factors is \(1+\eta^2L^2>1\).

The [affine proof](../Proofs/ReshufflingAffineEpoch.lean) retains nonzero gradients at the optimum. A permutation swap controls the correlation between the epoch product and its accumulated affine error; centered permutation-prefix second moments control the remaining error energy. [Iteration](../Proofs/ReshufflingIteration.lean), [affine convergence](../Proofs/ReshufflingAffineConvergence.lean), [tuning](../Proofs/ReshufflingTuning.lean), and [accuracy](../Proofs/ReshufflingAccuracy.lean) then give the stated bound. These supporting steps are not separate claims of new stochastic-oracle or accelerated complexity.

## Comparison and improvement regime

The strongest directly comparable quadratic last-endpoint baseline identified is Ahn–Yun–Sra, Theorem 2 and Appendix B, Lemma 6. It allows indefinite, noncommuting components and the same gradient oracle. Its admissible step is
\(\eta\le 3(16nL)^{-1}\min\{1,\sqrt{n/\kappa}\}\).
Their Appendix B distance estimate has noise terms
\(640\eta^2L^2G^2/\mu^2+36\eta^3n^2L^2G^2\log n/\mu\).
Converting distance to objective gives the same powers of \(A\) and \(B\) as above, up to logarithms, but with transient cost
\(\widetilde O(n\kappa\max\{1,\sqrt{\kappa/n}\})\).
Our improvement replaces that transient by \(\widetilde O(n\kappa)\). With the displayed constants, our admissible step is literally larger when \(\kappa>36n\). It is a polynomial improvement when \(\kappa/n\) grows and the noise-dependent terms do not dominate. It is not a claim that the old threshold is a lower bound.

Steps of order \(1/(nL)\) are already known under stronger assumptions. [Mishchenko, Khaled, and Richtárik, Theorem 2](https://arxiv.org/html/2006.05988) assumes convex components. The linear Polyak–Łojasiewicz guarantee in their Section 3.3, Theorem 4, requires a globally uniform gradient-variance bound (\(A=0\) in their Assumption 2). Distinct quadratic Hessians have unbounded component-gradient variance along some ray, so that condition does not cover the present class or the example below. Their general nonconvex statement instead bounds the best gradient norm with a horizon-dependent step restriction.

Ahn–Yun–Sra, Appendix C, Theorem 14, additionally analyzes a tail-averaged output. Its better noise dependence corresponds to \(A/\sqrt\kappa\) and \(B/\kappa^{1/3}\), while retaining the older transient threshold. Our last-endpoint theorem does not dominate that guarantee in all regimes. Full-gradient acceleration also gives \(\widetilde O(n\sqrt\kappa)\) component calls for this strongly convex average. Our result concerns ordinary reshuffling, not optimal complexity among unrestricted finite-sum algorithms.

One sufficient improvement regime is
\(\kappa\gg n\) and \(0<G\le n\mu\sqrt{\varepsilon/L}\).
Then \(A,B\le n\kappa\), so the new cost is \(\widetilde O(n\kappa)\), versus the older transient \(\widetilde O(n\kappa\sqrt{\kappa/n})\), including for the tail-averaged comparison.

This regime has noninterpolating, noncommuting examples. Let \(n\) be divisible by eight, \(L=1\), \(\mu=n^{-p}\) for fixed \(p>1\), \(R=1\), \(\varepsilon=\mu/8\), and \(G=n\mu^{3/2}/\sqrt8>0\). In two dimensions take equal numbers of the four Hessians \(\mu I\pm H,\mu I\pm J\), where \(H=\operatorname{diag}(1,-1)/2\) and \(J\) has off-diagonal entries \(1/2\) and zero diagonal. Pair each Hessian with offsets \(+Gv,-Gv\) for a fixed unit vector \(v\). The average Hessian is \(\mu I\), each norm is at most one, and components are indefinite and do not all commute. The offsets sum to zero and prevent a common stationary point. With \(x_*=0,x_0=e_1\), the initial objective gap is \(\mu/2=4\varepsilon\). The uniform class guarantees differ by a factor \(n^{(p-1)/2}\), up to logarithms. This explicit family demonstrates that the parameter regime is nonempty and noninterpolating; it is not a lower-bound family. In particular, its \(Q=\sum_i A_i^2\) is uniformly positive, and exploiting that additional spectral information in an earlier intermediate expansion can permit a stronger instance-specific analysis. The new guarantee holds uniformly from only the stated parameters and requires no lower spectral bound on \(Q\). Covariance-corrected regression supplies independent motivation for the class.

The improvement is in the conditioning transient at moderate relative accuracy and low heterogeneity. For a fixed noninterpolating instance as \(\varepsilon\to0\), the noise terms eventually dominate. No sharp stable-step constant, improved accuracy exponent, general Hölder-curvature upper bound, or necessity claim is proved. The public Lean theorem formalizes the upper guarantee and execution; the literature comparison and illustrative instance calculations are explained here rather than asserted as additional public Lean theorems.
