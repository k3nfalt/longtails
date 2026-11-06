This result extends the high-accuracy full-Hessian minimax rate to a known closed convex dual domain, allowing changes in the active constraints. The contribution is a finite-jet constrained saddle model with sharp value and gradient error bounds. It does not improve the best unconstrained complexity, and it does not provide second-order stationarity.

The formal result is [ConstrainedMinimaxCubic.result](ConstrainedMinimaxCubic.lean), for [ConstrainedMinimaxSecondOrder.spec](../Setups/ConstrainedMinimaxSecondOrder.lean). The constructed [method and output](../Algorithms/ConstrainedSaddleCubic.lean) run through `execute` with one exact oracle channel.

**Problem and information.** Let the primal and dual spaces be arbitrary finite-dimensional real inner-product spaces, and let

\[
\Phi(x)=\max_{y\in Y}f(x,y),\qquad \kappa=L/\mu\ge1.
\]

The known set \(Y\) is nonempty, closed and convex. The function has a globally \(L\)-Lipschitz joint gradient, a globally \(\rho\)-Lipschitz joint Hessian, and is globally \(\mu\)-strongly concave in its dual argument. Strong concavity and smoothness are imposed on the ambient space, not merely on \(Y\). We assume \(\rho,\mu,\varepsilon>0\), a supplied feasible \((x_0,y_0)\), and supplied bounds

\[
\Phi(x_0)-\Phi(x)\le\Delta\quad\text{for every }x,
\qquad \|\nabla f(x_0,y_0)\|\le B.
\]

One call at \((x,y)\) returns \((f(x,y),\nabla f(x,y),\nabla^2f(x,y))\). Every call is charged, including duplicate queries, initialization, and tracking to the final center. The algorithm knows the displayed parameters and \(Y\). Exact projection onto \(Y\), affine variational-inequality solves, and global minimization of transcript-defined models are internal computations. There is no polynomial arithmetic-time or projection-complexity claim. The algorithm never receives an exact maximizer of the original objective or a function of all dual points as a free oracle reply.

The dual constraint is a standard minimax feature: for example, [Lin, Jin and Jordan, ICML 2020](https://proceedings.mlr.press/v119/lin20a.html), studies nonconvex–concave optimization over convex bounded dual sets. The joint smoothness and global strong-concavity assumptions match the full-Hessian unconstrained baselines cited below. The new specification permits unbounded closed convex \(Y\), but does not relax those ambient regularity assumptions. The initial-gradient bound supplies a quantitative initialization cost; it is not a global bounded-gradient condition. No constraint qualification, strict complementarity, interior margin, fixed active set, or envelope Hessian is assumed.

**Guarantee and cost.** The deterministic returned primal point \(\widehat x\) satisfies

\[
\|\nabla\Phi(\widehat x)\|\le\varepsilon.
\]

The proof establishes differentiability of \(\Phi\). The specification expresses accuracy almost surely under the explicit product of algorithm and oracle seed laws; the proof actually establishes it for every seed because all admissible replies are exact.

For reading the explicit one-line Lean budget, define

\[
\begin{aligned}
E&=\left\lceil16\kappa\log(1+32\rho B/\mu^2)\right\rceil,\\
J&=1+\left\lceil2\log(33+512L\mu/(\rho\varepsilon))\right\rceil,\\
T&=1+\left\lceil384\Delta\sqrt\rho\,\kappa^{3/4}/(\varepsilon\sqrt\varepsilon)\right\rceil,\\
H&=\left\lceil2048\rho\sqrt\kappa\,\Delta/(\mu\varepsilon)
             +8\sqrt{\rho\varepsilon}/\mu\right\rceil.
\end{aligned}
\]

All ceilings are nonnegative integer ceilings. The public budget is

\[
K=4\bigl[1+E+(1+T+H)(1+J)\bigr].
\]

Its Lean definition substitutes \(L/\mu\) explicitly and contains no opaque tuning helper. The proof pays for \(2E\) initialization calls, \(2J\) initial refinement calls, one model query per outer step, and \(2Jm\) calls for each center move with \(m\) tracking segments. The public cap also pays for any padding after termination. The \(8\sqrt{\rho\varepsilon}/\mu\) term covers tracking the terminal move, including immediate termination. It is not discarded when \(\Delta=0\).

Writing \(A=\Delta\sqrt\rho\,\kappa^{3/4}\varepsilon^{-3/2}\), the principal terms, apart from the displayed logarithms, are

\[
\kappa\log(1+\rho B/\mu^2)
+\bigl(1+A+\rho\sqrt\kappa\,\Delta/(\mu\varepsilon)
+\sqrt{\rho\varepsilon}/\mu\bigr)
 \log(33+L\mu/(\rho\varepsilon)).
\]

In the high-accuracy regime \(\varepsilon\le L^2/(\rho\kappa^{3/2})\), the nonterminal tracking term is at most a constant multiple of \(A\). When \(A\) also dominates initialization, the additive constants, and terminal tracking, the leading rate is \(\widetilde O(A)\). Outside that regime the full formula applies; no universal superiority or matching all-regime optimality is claimed. A quadratic objective satisfies the assumptions with any positive supplied \(\rho\); the formula does not have a uniform zero-modulus guarantee.

**Algorithm and proof mechanism.** Define

\[
\mathcal E(z)=\min_u\max_{y\in Y}\{f(u,y)+L\|u-z\|^2\}.
\]

Projected extragradient initializes a saddle estimate. Repeated affine saddle Newton corrections then produce a point \(w\) and a computable correction \(e\) such that \(w\) is the exact regularized saddle of \(f_e(v)=f(v)-\langle e,v-w\rangle\) at the current center. Each correction asks for the jet at the old point and at the computed affine saddle. The final query supplies its residual certificate.

A single additional joint jet at \(w\) constructs the entire quadratic model \(q\) of \(f_e\). The method minimizes

\[
M(z)+\tfrac{R}{3}\|z-z_0\|^3,
\quad M(z)=\min_u\max_{y\in Y}\{q(u,y)+L\|u-z\|^2\},
\quad R=\rho(4+\kappa)^{3/2}.
\]

The key estimates, proved in [ConstrainedSaddleModel](../Proofs/ConstrainedSaddleModel.lean) and [ConstrainedSaddlePerturbation](../Proofs/ConstrainedSaddlePerturbation.lean), are

\[
\begin{aligned}
|[\mathcal E(z)-\mathcal E(z_0)]-[M(z)-M(z_0)]|
&\le R\|z-z_0\|^3/6+2\sqrt\kappa\|e\|\|z-z_0\|,\\
\|\nabla\mathcal E(z)-\nabla M(z)\|
&\le R\|z-z_0\|^2+2\sqrt\kappa\|e\|.
\end{aligned}
\]

Weighted saddle monotonicity controls primal and dual displacements separately. Taylor remainders at mixed saddle pairs yield the value estimate; weighted residual stability yields the gradient estimate. This bypasses differentiating the constrained solution map. In particular, neither \(\mathcal E\) nor the model error needs to be twice differentiable. Retaining the exact dependence of the original objective on every \(y\), instead of using the single joint jet, would grant a different and stronger oracle.

The residual target is
\(\min\{\mu^2/(32\rho),\varepsilon/[128(\kappa+2\sqrt\kappa+1)]\}\).
The center move is divided into segments of length at most
\(\mu/[16\rho\sqrt{4+\kappa}]\).
The method stops when the cubic step has squared length at most \(\varepsilon/(4R)\), tracks to that **new** center, and returns the tracked saddle's primal coordinate. The proof transfers the envelope gradient to this actual output with loss at most \((\kappa+2\sqrt\kappa+1)\|e\|\).

[ConstrainedSaddleOuter](../Proofs/ConstrainedSaddleOuter.lean) proves model-minimum existence and descent. [ConstrainedSaddleExecution](../Proofs/ConstrainedSaddleExecution.lean) links the finite query plan to `execute` and proves accuracy. [ConstrainedSaddleBudget](../Proofs/ConstrainedSaddleBudget.lean) bounds its actual reply-dependent path length by decreasing the remaining objective-gap allowance; it does not multiply a worst-case inner cost by every outer iteration.

**Closest results and novelty boundary.** [Zhang et al., arXiv:2610.16771v2, 19 October 2026](https://arxiv.org/html/2610.16771v2), §3, Theorem 4.1 and Appendix E, is the strongest checked unconstrained first-order-stationarity baseline. It already obtains the high-accuracy \(\widetilde O(A)\) rate, amortizes inner work, certifies an actual primal output, and permits exact transcript-model computation. It also supplies other accuracy regimes and faster initialization. Those features are not claimed as new here. Our explicit EG startup can be worse by a condition-number factor than accelerated startup. That source is an unreviewed preprint and explicitly states that conference or journal submission is not intended.

[Zhou, Chen, Luo and Liu, arXiv:2610.20345v1, 14 October 2026](https://arxiv.org/html/2610.20345v1), §§3–4, develops envelope cubic regularization for unconstrained dual variables with the same leading conditioning exponent and a stronger second-order-stationarity target. Our first-order guarantee is not an extension of that stronger conclusion. The substantive extension is to arbitrary closed convex dual constraints while retaining the high-accuracy leading full-jet rate and accounting for every inexact saddle solve.

A constrained gradient-only baseline is [Lin, Jin and Jordan, COLT 2020](https://proceedings.mlr.press/v125/lin20a/lin20a.pdf), Theorem 20 and Appendix E.3, on bounded convex dual domains. Its leading cost is \(\widetilde O(\sqrt\kappa\,L\Delta\varepsilon^{-2})\). Although the theorem states success probability \(2/3\), its proof explicitly bounds the expected squared primal gradient by \(8L\Delta/T+72\kappa^2L\delta\), so expected norm accuracy follows with the same leading cost. Approximate proximal solves cost \(\widetilde O(\sqrt\kappa)\) gradients each; their tolerance affects logarithms. This baseline does not need Hessian regularity or Hessian replies. On common instances our oracle can implement it by ignoring the Hessian. The ratio of our leading term \(A\) to its leading term is \(\sqrt{\rho\varepsilon}\,\kappa^{1/4}/L\), which tends to zero at fixed positive parameters as accuracy increases. This comparison uses the additional Hessian regularity and access, and retains the initialization and terminal-cost qualifications above; it is not an improvement for the broader gradient-only model.

Generic Taylor-model convergence is established work. [Nabou and Necoara, arXiv:2203.13367v3](https://arxiv.org/html/2203.13367v3), Definition 2, requires differentiability and Lipschitz higher derivatives of the surrogate error; those conditions need not hold across the active-set changes covered here. [Drusvyatskiy, Ioffe and Lewis, arXiv:1610.03446v1](https://arxiv.org/html/1610.03446v1), Theorem 3.1, relates model steps to slope at a nearby point. It does not supply this finite-jet saddle model's conditioning bound or the computed-output gradient estimate. Cubic descent, extragradient, affine VI Newton corrections, and warm-start accounting are supporting techniques, not separate novelty claims.

The obvious unconstrained reduction also fails to directly preserve the stated assumptions: adding the indicator of \(Y\) is nonsmooth, while squared-distance penalization is generally only continuously differentiable. A smooth penalty or barrier would require a new accuracy transfer and explicit regularity and oracle-cost accounting. This observation excludes a direct substitution, not every possible alternative reduction.

**Instances and limitations.** A concrete interacting nonlinear example is

\[
f(x,y)=\tfrac1{20}\|x\|^2+x_1y+\tfrac15\sin^2(x_2)\tanh(y)-2y^2,
\qquad Y=[0,\infty).
\]

Its joint second and third derivatives are bounded, its dual curvature is uniformly negative, and \(\Phi(x)\ge\|x\|^2/20\). For \(x_2=\pi/2\) and sufficiently positive \(x_1\), the primal value is nonconvex. At an activation boundary the envelope Hessian jumps; the true and quadratic-model activation boundaries differ, so their error need not be twice differentiable. This is a diagnostic, not a restriction of the theorem to scalar dual variables.

More generally, dense bilinear coupling plus finitely many terms \(a_j\sin^2(b_j^Tx)\tanh(c_j^Ty)\), a positive primal quadratic, and a dominating negative dual quadratic gives nonlinear coupled finite-dimensional instances on convex domains containing zero. For a dual term \(-\beta\|y\|^2/2\), the sufficient condition \(\beta>2\sum_j|a_j|\|c_j\|^2\) ensures strong concavity. The theorem has no explicit dimension multiplier, although the supplied regularity constants depend on these data and dimensions through their norms. These example calculations explain the scope; they are not separate formalized example theorems.

The literature assessment used independent searches of the two latest publicly available ICML, ICLR and NeurIPS editions and roughly November 2024–November 2026 arXiv work, followed by older primary sources. The four closest arXiv version records above were rechecked on 6 November 2026 UTC. This is not an exhaustive novelty certificate. The contribution is an assumption/scope extension with a new constrained-model interface, not a claim of a new unconstrained exponent, an arithmetic-time algorithm, or a constrained second-order-stationarity theorem.
