# Safe stochastic KKT points under uniform MFCQ

[Main theorem](SafeStochasticMfcqKkt.lean) · [Setup](../Setups/StochasticMfcqInequalities.lean) · [Algorithm and output](../Algorithms/StochasticMfcq.lean) · [Joint execution guarantee](../Proofs/StochasticMfcqGuarantee.lean) · [Budget proof](../Proofs/StochasticMfcqBudget.lean)

The result gives a tunable high-probability, exactly feasible KKT guarantee for smooth nonlinear inequality constraints accessed through a stochastic oracle. It allows redundant constraints, arbitrary finite dimension, nonconvex objectives and nonconvex feasible sets, and a supplied feasible point on the boundary. Under paired mean-square-smooth finite-variance observations, every primitive oracle type has an accuracy exponent of three, up to logarithms, in the regime specified below. The contribution concerns the combination of nonlinear constraint qualification, safe queries, and finite-variance oracle complexity; it is not a claim that variance reduction or an exponent of three is new in unconstrained or convex optimization.

## Problem and information

Minimize a differentiable function \(f\) subject to \(c_i(x)\le0\), \(i=1,\ldots,m\), in a finite-dimensional real inner-product space. The setup requires \(m>0\), \(H\ge1\), \(0<\mu\le H\), \(\tau>0\), \(\Delta,\sigma,L\ge0\), \(\varepsilon>0\), and \(0<\rho<1\).

The objective gradient and each constraint gradient are globally \(H\)-Lipschitz. Their norms are at most \(H\) at feasible points. The supplied \(x_0\) is feasible, and \(f(x_0)-f(x)\le\Delta\) for every feasible \(x\). A minimizer need not exist. Uniform near-active MFCQ means that, at every feasible \(x\), some \(z\) with \(\|z\|\le1\) satisfies

\[
\langle\nabla c_i(x),z\rangle\le-\mu
\quad\text{whenever }c_i(x)\ge-\tau.
\]

This is a common inward direction, not a full-row-rank Jacobian assumption. It permits duplicated rows and \(m>\dim E\). The near-active qualification has direct precedent in Assumption 4 of [LB-SGD, JMLR 25(171), 2024](https://www.jmlr.org/papers/volume25/22-0878/22-0878.pdf). Our global smoothness requirement is stronger than smoothness restricted to its feasible region; this distinction is retained in the comparison.

The algorithm knows the setup parameters and \(x_0\), but not the objective, constraints, their means, a minimizer, a feasible-set projection, or an MFCQ direction. A request at \((x,y)\) returns stochastic objective gradients, constraint vectors, and full constraint Jacobians at both endpoints, using the **same fresh sample**. The three observation maps are jointly measurable. At feasible points they are integrable and unbiased, with the sum of their squared centered Hilbert norms having integrable expectation at most \(\sigma^2\). At two feasible points, the sum of squared paired differences is integrable with expectation at most \(L^2\|x-y\|^2\). No sub-Gaussian or almost-sure noise bound is imposed. No oracle moment condition is needed outside the feasible set. The observation maps remain globally defined and measurable so execution is defined on failure events too.

The sampling law is an abstract probability measure with the repository's IID certificate. Product representations are derived internally from independence. The setup imposes no restriction to finite sample spaces and no prescribed algorithm family.

## Output, accuracy, and cost

The named `output` executes the algorithm using the repository's `execute`. It returns the first certified stopping point and its nonnegative multiplier vector, retained through the remaining scheduled slots. It is neither a random iterate nor an average.

With probability at least \(1-\rho\), the same event guarantees that **every recorded query endpoint is feasible**, and the returned \((x,\lambda)\) satisfies

\[
\lambda_i\ge0,\qquad c_i(x)\le0,\qquad
\left\|\nabla f(x)+\sum_i\lambda_i\nabla c_i(x)\right\|\le\varepsilon,
\qquad \sum_i|\lambda_i c_i(x)|\le\varepsilon.
\]

The public `Convergence` theorem uses the output accuracy specification. The additional all-query safety assertion is proved jointly with accuracy by `execution_guarantee`, against the actual `executeWithTrace` history. It is not inferred from output feasibility. The framework's output-only success predicate does not itself encode a trace property.

For readability set \(e=\min\{\varepsilon,1,\tau\}\), \(u=\mu e\), and

\[
A=2+\frac{3200H^3\Delta}{u^2}.
\]

The public Lean budget expands these abbreviations and is exactly

\[
K=\left\lceil3500\left[
\frac{1600H^2\sigma^2}{u^2}
+A\left(1+\frac{40\sigma L}{u}\right)
\right]\right\rceil
\left(1+\left\lceil\frac{\log(A/\rho)}{\log4}\right\rceil\right).
\]

This counts paired joint requests. There are exactly \(K\) recorded requests, including padding after the finite query plan finishes. Each costs at most six vector primitive evaluations: two objective gradients, two constraint vectors, and two full Jacobians. Under scalar-row accounting the bound is \((2+4m)K\). Reset requests still evaluate and pay for the second endpoint even though the estimator discards it. Thus the six-vector-primitive bound is \(6K\), not a gradient-only count. Padding queries are \((x_0,x_0)\), and their safety is proved.

For fixed \(H,\mu,\tau,\Delta,\sigma,L\) and \(\varepsilon\le\min\{1,\tau\}\), the leading noisy term is

\[
\widetilde O\!\left(\frac{H^3\Delta\sigma L}{\mu^3\varepsilon^3}
+\frac{H^2\sigma^2+H^3\Delta}{\mu^2\varepsilon^2}
+\frac{\sigma L}{\mu\varepsilon}+1\right),
\]

where the displayed budget specifies the confidence logarithm. The noise and initialization terms cannot be dropped. When \(\sigma=0\), or when \(L=0\), the bound has accuracy exponent two rather than three. Large \(\varepsilon\) saturates at the band/normalization scale \(e\). This is an upper bound, not an optimality claim for all parameter regimes.

## Algorithm and proof mechanism

Use \(\delta=\mu e/(40H)\), step length \(\eta=\delta/(4H)\), and \(N=1+\lceil2H\Delta/\delta^2\rceil\). Parallel recursive estimators track the joint gradient/value/Jacobian vector along the common adaptive trajectory. They reset periodically, and otherwise average same-sample endpoint differences. A robust center of the replicas supplies an estimate with joint error at most \(\delta\).

A row is included when its estimated constraint value is at least \(-4\delta\). A finite Frank–Wolfe hull solver combines the estimated objective gradient with those rows. A large hull residual supplies a normalized direction that preserves exact feasibility and decreases the objective by at least \(\delta^2/(2H)\). A residual at most \(4\delta\) supplies multipliers: MFCQ forces a positive objective coefficient, allowing normalization while controlling stationarity and **sum** complementarity. This interface needs constraint-value accuracy proportional to \(\varepsilon\), rather than \(\varepsilon^2\). The feasible objective-gap bound rules out \(N\) nonstopping steps.

Ordinary independence of the accumulated replicas would be false: they share an adaptive iterate sequence. The stochastic proof instead bounds a product of shifted squared errors using independence only of the fresh, disjoint batches at a fixed history. Reset error and the entire epoch's paired increments each contribute at most \(\delta^2/1152\). With \(V=\delta^2/576\), the pre-update reward has expectation at most \((2V)^r\); a bad majority forces it to be at least \((8V)^r\). Markov's inequality therefore gives \(4^{-r}\), with \(r=1+\lceil\log(N/\rho)/\log4\rceil\).

A persistent alive indicator kills the potential after loss of query validity. Crucially the bad-event test uses the **pre-update** reward, so it detects a first unsafe step instead of hiding it. Finite-prefix IID integration handles arbitrary measurable entering states without regular conditional distributions. A first-exit induction then establishes live-state accuracy, feasibility, and the final certificate together. Exact flat sample indices connect this argument to the implemented plan, including incomplete epochs. This is the finite-variance adaptive concentration step; a fixed-point median-of-means assertion alone would not justify it.

The hull subproblem uses a finite number of arithmetic operations and no extra oracle access. Its internal iteration limit is \(1+\lceil10(H+1)^2/\delta^2\rceil\), with two phases. Consequently the oracle improvement does not imply an equally good arithmetic complexity or a practical speedup. The numerical constants are conservative.

## Closest results and scope of the contribution

- **LB-SGD:** Theorem 8 of the [published JMLR version](https://www.jmlr.org/papers/v25/22-0878.html) gives a safe first-order sample bound with exponent seven. It requires a known strictly feasible starting margin, bounded feasible diameter, and sub-Gaussian observations. Our result permits a boundary start and only finite variance, but assumes paired mean-square smoothness and global derivative smoothness. This is an oracle-model tradeoff, not unconditional dominance over its one-point model. Its componentwise complementarity criterion also differs from our stronger sum criterion.
- **SafePD:** [arXiv:2505.09349v1, May 2025](https://arxiv.org/abs/2505.09349), Theorem 17, gives an exponent-six safe guarantee for a single smooth constraint; the manuscript discusses a multi-constraint extension. Appendix D, equation (17), needs internal complementarity/value accuracy of order the squared stationarity tolerance. Its separate value-estimation term remains even if its inner optimizer is replaced by SPIDER. Thus that replacement alone does not give the all-primitive bound proved here. Conference acceptance was not verified; it is treated as a preprint. These are limitations of that analysis, not lower bounds on safe optimization.
- **Adaptive directional decomposition:** [Shi and Wang, arXiv:2511.03210v2, November 2025](https://arxiv.org/abs/2511.03210), Theorem 7, separates derivative and constraint-value complexities with exponents three and five. Its equality/nonnegativity formulation, Jacobian rank requirements, bounded noise, and samplewise regularity differ from the present inequality-MFCQ model. Our claim counts values as well as derivatives and allows redundant nonlinear rows; it does not establish superiority on every instance covered by their formulation.
- **Unified high-probability variance-reduced estimation:** [Luo et al., arXiv:2605.15388v1, May 2026](https://arxiv.org/html/2605.15388v1), Theorem 6.3 and Appendix F, already obtain exponent-three bounds for convex expectation constraints. Main Assumption 6.2 requires convex **mean** functions, a bounded known domain, and bounded stochastic subgradients; we compare against that weaker condition rather than Appendix F's sample-convex wording. The output is an approximately feasible selected average with an objective-gap guarantee. Assumptions 3.2 and 5.2 impose sub-Gaussian oracle/difference conditions. A direct proximal reduction using its generic \(\widetilde O(\zeta^{-3})\) bound at inner objective tolerance \(\zeta=O(\varepsilon^2)\) already costs \(\widetilde O(\varepsilon^{-6})\) per solve, before outer iterations. Moreover, its known-domain projection does not provide projection onto our unknown feasible set, and approximate output feasibility does not ensure safe queries. These observations block that direct reduction, not every tailored reduction, and are not lower bounds. Official conference status was not independently verified.
- **Federated stochastic switching:** [Upadhyay et al., arXiv:2601.16897v2, October 2026](https://arxiv.org/html/2601.16897v2), Corollary 1 and Appendix A.4.4, obtains a weakly convex STORM bound of \(\widetilde O(K^{-1/3})\) for average squared proximal distance, hence \(\widetilde O(K^{-1/6})\) for distance. This gives accuracy exponent six at the norm scale, not three. A smooth-problem transfer to KKT residuals requires multiplier/regularity control and output selection; the result is not dismissed merely because its stationarity point is proximal. It does not supply the present exact all-query safety guarantee.


The novelty claim is the safe, all-primitive, tunable-confidence guarantee under finite-variance paired observations and uniform near-active MFCQ for general nonlinear inequalities, together with its value-accuracy and adaptive-estimator argument. Classical feasible directions, Frank–Wolfe, recursive variance reduction, and robust centers are prior ingredients. The repository's full-surjectivity result already attains exponent three at constant success under a different rank condition; this result is not presented as the first exponent-three theorem under any constraint regularity. No conversion from a fixed-success theorem to the present joint guarantee is assumed for free.

## Nonlinear instances and limitations

A concrete family is \(c_i(x)=x^TQ_i x-s_i+\psi_i(x)\), with dense positive-definite matrices \(qI\preceq Q_i\preceq QI\), \(s\le s_i\le S\), bounded smooth oscillations \(|\psi_i|\le a\), \(\|\nabla\psi_i\|\le b\), and globally Lipschitz gradients. If \(\tau<s-a\) and \(2q\sqrt{(s-\tau-a)/Q}>b\), the radial inward direction supplies uniform MFCQ. Small gradient amplitude does not force small curvature: the feasible set may be nonconvex. For example, \(x^2+y^2+\sin(64x)/256\le1\) has nonconvex boundary geometry. Dense matrices and rotated oscillations give interacting coordinates in arbitrary dimension; rows may be duplicated. Smooth trigonometric objectives plus a linear term have bounded gradients on this compact feasible region. Additive joint finite-variance noise supplies an oracle satisfying the paired model. These examples establish meaningful nonlinear scope, not additional theorem assumptions.

Dimension and row count enter through the actual \(H,L,\sigma,\mu\), and through scalar-row cost; they are not asserted to be uniformly bounded as dimension grows. The theorem does not cover equality constraints, unknown tuning constants, biased oracles, dependent sampling, arbitrary one-point finite-variance observations, or constraint qualification failing near the boundary. Global smoothness and a uniform MFCQ band remain substantive restrictions. The current proof does not show that these restrictions, the parameter powers, or the confidence logarithm are necessary.

The contribution comparison is based on primary sources checked through 12 November 2026 UTC, including the recent convex variance-reduction result above. The Lean theorem alone does not establish research novelty.
