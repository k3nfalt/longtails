# Finite-bit local extragradient under Jacobian regularity and strong growth

[Theorem](DistributedJacobianLocalExtragradient.lean) · [Setup](../Setups/DistributedJacobianStrongGrowth.lean) · [Event-driven algorithm](../Algorithms/DistributedLocalExtragradientProtocol.lean) · [Tuning and reference output](../Algorithms/DistributedLocalExtragradientTuning.lean)

## Problem and guarantee

The result concerns finding a root of a nonlinear operator in arbitrary finite dimension. For $F:\mathbb R^d\to\mathbb R^d$, the assumptions are

$$
F(x_*)=0,\quad \langle F(x),x-x_*\rangle\ge\mu\|x-x_*\|^2,
\quad \|F(x)-F(y)\|\le L\|x-y\|,
\quad \|DF(x)-DF(y)\|\le M\|x-y\|.
$$

The root and Jacobian are hidden. The public input supplies positive $\mu,R,\varepsilon$, bounds $L\ge\mu$, $M\ge0$, and $\|x_0-x_*\|\le R$. The root-directed inequality is quasi-strong monotonicity; pairwise strong monotonicity is sufficient but unnecessary. The Jacobian exists everywhere. No convex potential, quadratic structure, separability, or fixed dimension is assumed.

There are $n\ge1$ workers on a public rooted tree of depth at most $h$. Worker $i$ receives unbiased, jointly measurable replies satisfying

$$
\mathbb E[g_i(x,\xi)]=F(x),\qquad
\mathbb E\|g_i(x,\xi)\|^2\le\rho\|F(x)\|^2,\qquad \rho\ge1.
$$

The workers share the mean operator, but their noise distributions may differ. Samples are IID under an abstract probability law; the specification does not prescribe that law as a product sample space. The oracle assumptions require the relevant integrability explicitly. They do not require bounded realizations, fourth moments, samplewise smoothness, paired evaluations of a sample, or a finite sample space. Strong growth implies interpolation at the root.

Each worker has at most one pending oracle query, of duration $\tau>0$. Each directed tree edge has at most one pending message, of duration $\lambda+\beta b$ for its actual bit count $b$. Distinct directed edges can operate concurrently. Computation and communication may overlap. The public theorem proves

$$
\mathbb E\|\operatorname{execute}(B)-x_*\|^2\le\varepsilon^2
$$

under `DistributedTemplate.law`, together with measurable output, integrable squared error, and almost-sure finite-event execution at every deadline up to $B$. In fact, finite-event termination is proved for every seed. This is an elapsed-time upper bound, not a query-count bound or a distributed lower bound. Jensen also gives expected norm error at most $\varepsilon$.

## The time bound

Write $\kappa=L/\mu$, $G=2+\rho/8+\rho^2/128$, and $J=\log(R/\varepsilon)$. If $R\le\varepsilon$, the output is $x_0$ at time zero. If $\varepsilon<R$ and $n<64\kappa G$, the algorithm uses root-only SGD and the budget is

$$
B=\tau\left\lceil\rho\kappa^2\log(R^2/\varepsilon^2)\right\rceil.
$$

Otherwise define the local depth explicitly by

$$
T=\min\left\{\lfloor\kappa\rfloor,\left\lfloor\frac{\log(n/(64\kappa))}{\log G}\right\rfloor\right\}.
$$

This is the largest positive integer satisfying $T\le\kappa$ and $64\kappa G^T\le n$. The branch condition guarantees $T\ge1$. Put

$$
q=1+32\rho MR G^T/\mu,\quad r=R/q,\quad
A=1+\log(dq),\quad
u=\frac{\kappa}{T}[\log(2r/\varepsilon)]_+,
$$
$$
C=\lambda+\beta\{64+d\log(2n)\},\qquad
D=\lambda+\beta\{64+d\log(2+nd r/\varepsilon)\}.
$$

The certified public bound is

$$
\boxed{B=65536\left[(\tau\rho\kappa^2+hC)A+\tau\kappa J+hD\,u\right].}
$$

All logarithms here are natural. Constants are deliberately loose; no logarithmic factors are suppressed. The three terms expose initialization, accuracy-dependent computation, and refinement communication. The formula covers $M=0$, zero communication costs, and zero refinement rounds.

The Lean `budget` now defines $\kappa,G,T,q$ by the explicit formulas above and displays the three cost terms directly. It contains no infimum, existential characterization, or tuning search. The four tuning abbreviations are defined in the public declaration itself; no chain of algorithm or encoding helpers is needed to read the rate. The setup declares these short parameter fields directly: `p.τ` for computation time, `p.l` for latency ($\lambda$ above), `p.β` for time per bit, and `p.h` for tree height. The algorithm, supporting proofs, and public budget use these same fields; no parameter aliases are needed. Renaming these fields preserves their types, the setup assumptions, and the elapsed-time bound.

This is an exact reformulation of the previous implicit budget on every valid parameter choice, not merely an asymptotic relaxation. The [budget proof](../Proofs/DistributedJacobianStrongGrowthBudgetCharacterization.lean) identifies the former singleton infimum with the implemented depth and radius ratio, and `envelopeTime_explicit_eq` identifies the new closed expression with the same value. The zero-time and root-only branches are unchanged. The equality preserves $M=0$, zero communication costs, the worker threshold, and skipped refinement. [Elapsed-time algebra](../Proofs/DistributedJacobianStrongGrowthBudgetTime.lean) continues to connect this value to the actual execution.

The integer floors and positive part are retained because deleting them need not preserve the rate. For example, with $\kappa=2$, $n\asymp128G^{3/2}$ and $32\rho MR/\mu=1/G$, the actual depth gives $T=1,q=2$, whereas continuous depth gives $q\asymp\sqrt G$ and adds an unbounded $\log G$ startup factor. The displayed abbreviations keep these essential dependencies readable without expanding them repeatedly.

The simplification does remove unnecessary notation and rounding. The combined computation count is within universal constants of $\rho\kappa^2A+\kappa J$; the apparent $1/n$ confidence term is absorbed only after combining startup and refinement. Refinement ceiling overhead is absorbed into the already-paid median startup when the continuous count is below one. This preserves skipped refinement instead of imposing an artificial positive round count.

## Algorithm and new mechanism

The algorithm first runs independent SGD trajectories at step $\mu/(\rho L^2)$. It projects their endpoints onto the known initial ball and computes a quantized coordinatewise upper median through tree reductions and broadcasts. Its per-worker warm-up count is

$$
s=\left\lceil\rho\kappa^2\left[\log(64dR^2/r^2)+\frac2n\log(8R^2/\varepsilon^2)\right]\right\rceil.
$$

The median is within $3r/8$ of the root except on an event of probability at most $\varepsilon^2/(8R^2)$. This is a proved initialization procedure, not an assumed local starting point or a fixed-success guarantee. Every final output lies in the initial ball, bounding the failure contribution to expected squared error.

Each refinement block runs $T$ independent-sample extragradient steps per worker with step $1/(4L)$, consuming exactly $2T$ fresh replies. It clips endpoint displacements at $256\kappa(G^T+1)r/T$, quantizes, aggregates integer codes exactly up the tree, broadcasts, and projects onto the local and initial balls. The returned point is the last completed projected block iterate; with no refinement it is the warm median. The exact refinement count is

$$
K=\left\lceil\frac{128\kappa}{T}\log(4r^2/\varepsilon^2)\right\rceil_+.
$$

The central mathematical step separates an endpoint's mean from its second moment. The second moment may grow as $G^T$, while the mean follows a contracting linearized extragradient recursion plus a Taylor remainder controlled by $M\mathbb E\|X-x_*\|^2$. Averaging across $n\ge64\kappa G^T$ workers pays for the growing variance. Localization makes the nonlinear bias small enough to retain a contraction proportional to $T/\kappa$. Clipping controls encoding range and its bias using only second moments. No fourth-moment closure or stability of every local realization is assumed.

The proved rounded recursion contracts by $1-T/(128\kappa)$, with an explicit quantization term. Parallel confidence amplification, bounded failure loss, and fresh-sample composition turn this local mechanism into expected accuracy from the original radius $R$. The implementation proves that the actual asynchronous event history has exactly the sample indices, payloads, and outputs used in that mathematical argument. Finite bits and event accounting support the guarantee; they are not the novelty claim by themselves.

## Comparison and improvement regime

The contribution is a nonlinear, globally initialized counterpart of affine local-averaging gains under second-moment strong growth, with a fully charged finite-bit tree implementation. It adds quantitative Jacobian regularity to the broader Lipschitz strong-growth class; it is not an improvement for that entire broader class. The proof also needs only quasi-strong monotonicity, but the strongest comparative separation below is on the strongly monotone overlap.

- Novoselov, Dorn, Dvinskikh and Gasnikov, [arXiv:2610.12641v1](https://arxiv.org/html/2610.12641v1), §4.2, equation (3), Proposition F.4, give the nonlinear strongly monotone exponent $ND_{\rm sched}/\kappa$, with $D_{\rm sched}=\max\{K_0/\rho,\min\{nK_0/\rho,1\}\}$. Their affine §3 guarantees already exploit longer local depth. Here the nonlinear refinement exponent uses $T/\kappa$ after a charged startup, under the additional Jacobian assumption. This is not a claim to improve their affine result or contradict their broader-class lower bounds.
- Wang and Kale, [arXiv:2602.09164v1](https://arxiv.org/html/2602.09164v1), Assumption 1 and Theorem 4 in §4.2, already use bounded operator curvature and control local bias. Their LIPPAX theorem concerns a bounded operator, additive variance, and expected restricted weak gap. Even granting a localized variance substitution $\sigma\lesssim\sqrt\rho Lr$, its drift term requires local work of order $\rho\kappa^3$ for a constant distance contraction. It does not yield this worker-dependent local exponent by the checked restart substitution. The Taylor-bias principle itself is not claimed as new.
- Sadchikov et al., [arXiv:2409.10478v2](https://arxiv.org/html/2409.10478v2), Assumptions 1–2 and Theorem 5.3, analyze Local SGD for convex quadratic-plus-residual objectives with growing variance. Their exponential term does not gain the present worker-dependent depth. Their centered variance coefficient corresponds to $\rho-1$, not the raw second-moment factor $\rho$. Their objective-gap/output guarantee and decomposition assumptions must not be silently identified with this VI setup.
- Gorbunov et al., [AISTATS 2022](https://proceedings.mlr.press/v151/gorbunov22b.html), Assumptions 1.2 and 4.1, Theorem 4.1/equation (18), provide the standard quasi-strong-monotonicity and distance-growing-variance baseline. Independent-sample minibatching gives an order $\kappa+(\rho-1)\kappa^2/b$ iteration coefficient under the direct variance substitution. The comparison above uses the stronger nonlinear strongly monotone schedule bound where applicable.
- [Federated Affine Variational Inequalities, arXiv:2611.02598v1](https://arxiv.org/abs/2611.02598), studies exact affine averaging. Its pathwise commutation does not hold for general nonlinear $F$. No novelty is claimed for the affine specialization of this theorem.

A concrete asymptotic separation uses $\kappa=T=t\to\infty$, $\rho=t^2$, $MR/L\asymp1$, $n\asymp64tG^t$, a star with $h=1$, $d\asymp n$, and $J=t^4$. Set $\lambda=\tau t^2$ and allow positive bandwidth cost satisfying

$$
\beta\le\frac{\lambda}{100d(J+\log n)}.
$$

The new bound is $O(\tau t^6)$, including $O(\tau t^5\log t)$ warm computation and median startup. The better of the checked serial/common-query guarantees is of order $\tau t^7$, even before charging their bits. This demonstrates a growing factor $t$, not universal superiority. Large worker counts, high accuracy, high concurrent root fanout, and a latency-dominated bandwidth regime are essential to this comparison. A common-query baseline may select fewer workers: on this star every nonroot worker still incurs the same latency. A balanced tree would not justify the stated separation, because a small root subtree can reduce its communication depth.

Finite-difference Newton and related first-order simulations must also be considered. A direct independent-column Jacobian estimate can require order $\rho\kappa^2d^2$ samples before confidence and communication costs; it may be attractive at small dimension and large worker count. The separation above takes large dimension and does not establish a lower bound against all Newton-type or unrestricted algorithms. Hessian-vector or sample-reuse oracles supply information absent here. No problem-class optimality or matching lower bound is claimed.

## Assumptions, examples, and limitations

Quasi-strong monotonicity and strong-growth noise are established assumptions. Lipschitz Jacobian regularity is a standard higher-order smoothness condition, also used in local-method analyses; combining it with interpolation is the substantive restricted class studied here. It is required globally because unbounded oracle realizations can send local iterates outside the initial ball. The algorithm never evaluates the Jacobian.

Nonlinear interacting examples include

$$
F(z)=\mu z+Sz+\delta B^\top\tanh(Bz),\qquad S^\top=-S,\quad\delta\ge0,
$$

with root zero and dense $B$. One may take $L=\mu+\|S\|+\delta\|B\|^2$ and $M=2\delta\|B\|^3$. The nonlinear term is monotone and has globally bounded first and second derivatives. Taking $S=0$ gives gradients of strongly convex log-cosh objectives; skew coupling also permits regularized nonlinear saddle examples. Multiplicative oracles $g_i(z,\xi)=a_i(\xi)F(z)$, with mean-one multipliers and second moments at most $\rho$, satisfy the model and may have infinite fourth moments. These demonstrate substantive nonlinear scope without restricting the theorem to these examples.

The setup excludes distinct worker mean objectives, additive noise at the root, nonsmooth constraints, dependent samples, and noninterpolating stochastic problems. The theorem uses all declared parameter bounds for tuning and does not adapt to unknown $L,\mu,M,\rho$. Startup can dominate at moderate accuracy. Total oracle work is $n(s+2TK)$ in the rich branch and can be very large. With fixed positive per-bit cost, increasing accuracy increases message width; the latency-dominated comparison cannot be extrapolated indefinitely. The result is an upper bound only.

## Fairness and limitations of `TemplateDistributed.lean`

The template is useful here because it distinguishes elapsed time from oracle calls, charges the actual encoded bit lists, models pending operations and concurrency, and requires finite-event execution. A bound on ideal rounds would not establish this theorem. The proof also avoids a free real-valued clock channel: the algorithm uses a constant clock and two timer codes, and the template's 64 framing bits are included in every transmitted packet.

The network and timing assumptions belong to this setup, not to universal properties of the template. This setup gives each directed edge independent capacity, allows full duplex, has uniform deterministic compute times, and imposes no shared worker-port, radio, or switch contention. It uses a rooted aggregation tree with a coordinator; it is decentralized in its communication graph, not coordinator-free. Comparisons must use the same latency, bandwidth, concurrency and information model. Central baselines should not be charged an artificially worse network or deprived of available parallelism.

Local arithmetic, projection, encoding, median comparisons and scheduling are free in the present model. Real implementations also pay memory, serialization, synchronization and contention costs, and may have random compute times, failures, finite-precision arithmetic or time-varying graphs. Adding charged local processing, shared-port/link resources, and explicit stochastic delays would make such comparisons closer to those systems. Those changes would require new setups and execution proofs; they are not consequences of the current theorem. The frozen template was not modified, and formal verification is not evidence that its idealizations dominate more realistic models.

## Literature coverage and status

The research and independent review surveyed recent ICML, ICLR, NeurIPS and arXiv optimization work, then checked stronger older results and standard batching, localization and restart reductions. The latest-version refresh on 18 November 2026 reconfirmed the four arXiv versions cited above and screened the publicly available NeurIPS 2026 program. Wang–Kale's acceptance is verified by its [official NeurIPS 2026 poster](https://nips.cc/virtual/2026/loc/atlanta/poster/152615). Both the [author homepage](https://guanghui-wang-gatech.github.io/) and [Apple publication page](https://pr-mlr-shield-prod.apple.com/research/federated-variational-inequalities) link the checked arXiv version. The OpenReview conference PDF and API returned HTTP 403 to both researchers: the comparison is to that author-linked public version, and identity with the conference text has not been verified. AISTATS 2022 status is verified by its official proceedings. An arXiv identifier alone is not evidence of conference acceptance. The claim concerns the mathematical guarantee and the stated improvement regime, not acceptance of this contribution or absence of every possible future improvement.

The final refresh also checked [Patel et al., arXiv:2607.14731v1](https://arxiv.org/html/2607.14731v1), Theorem 6, and [Quan et al., arXiv:2611.13916v1](https://arxiv.org/html/2611.13916v1), Theorem 3.17. The former treats convex gradient objectives with bounded additive variance and second-order worker heterogeneity; it does not cover the general skew-coupled operators here. Even granting a localized variance bound $\sigma^2\lesssim\rho L^2r^2$, its residual drift term requires order $\rho\kappa^3$ local steps for one round to achieve a constant distance contraction. The latter uses uniform additive variance and common-point minibatches, rather than independent local endpoint trajectories. These results do not supply the claimed nonlinear local-depth guarantee under the present oracle assumptions. This is a scope comparison, not a claim of superiority on their respective problem classes.
