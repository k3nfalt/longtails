# DASHA with deterministic gradients, finite messages, and free broadcast

This contribution formalizes the full-gradient DASHA method under the user's explicit waiver of mathematical novelty. It does not claim a new state-of-the-art optimization rate or an optimality theorem over all encodings. The public [theorem](DashaFreeBroadcastDeterministic.lean) is `DashaFreeBroadcastDeterministic.result`. Its budget is the explicit closed formula below, proved sufficient for the actual selected execution. This revision simplifies the presentation of an existing formal guarantee; it does not claim a new optimization theorem.

The [setup](../Setups/DistributedFreeBroadcastSmoothNonconvex.lean) specifies arbitrary finite-dimensional, possibly nonconvex local functions, their average objective, exact local gradient oracles, and the network. The [algorithm](../Algorithms/DashaDistributed.lean), [parameter choices](../Algorithms/DashaDistributedTrackedParameters.lean), and [selection rule](../Algorithms/DashaDistributedSelection.lean) implement actual bit messages. The [execution and accuracy proof](../Proofs/DashaDistributedTracked.lean) connects the implementation to `DistributedTemplate.execute` and its probability law.

## Problem and guarantee

There are $n\ge1$ workers and $d\ge1$ coordinates. Write $F=n^{-1}\sum_i f_i$. Each local function is differentiable with the stated gradient. The parameters satisfy $L,\widehat L,\varepsilon>0$, $\Delta,G\ge0$, $h_i>0$, and $\ell,b\ge0$. The smoothness assumptions are

\[
\|\nabla F(x)-\nabla F(y)\|\le L\|x-y\|,\qquad
\frac1n\sum_i\|\nabla f_i(x)-\nabla f_i(y)\|^2\le\widehat L^2\|x-y\|^2,
\]

together with a lower bound $F_*\le F(x)$, $F(x_0)-F_*\le\Delta$, and $\|\nabla f_i(x_0)\|\le G$. The algorithm knows these bounds, not the functions or future gradients. The initial local-gradient bound supplies a numerical range for the signed and sparse initialization options; it is not a bound on gradients throughout the trajectory.

When the zero-time certificate below does not apply, the returned point is uniformly selected from the first $K$ iterates. In every case,

\[
\mathbb E\|\nabla F(x_{\rm out})\|^2\le\varepsilon^2.
\]

Expectations include compression and output-selection randomness. Local gradients and network service times are deterministic. This is neither a stochastic-gradient oracle theorem nor a pathwise stationarity guarantee. The proof includes output measurability and integrability, and finite events at every deadline up to the time budget.

The assumptions admit nonlinear objectives with interacting coordinates. For example, a positive quadratic plus bounded sinusoidal terms in nonorthogonal linear combinations of coordinates has a globally Lipschitz gradient and a finite lower bound. Local affine perturbations whose sum is zero can make individual initial gradients arbitrarily large without changing the average objective. This latter family explains why communication should depend on the aggregate range when possible.

## Explicit elapsed-time budget

Write $\lambda=\min(L,\widehat L)$, $h_{\max}=\max_i h_i$, and $\tau=h_{\max}+\ell+64b$. If $\min(2\lambda\Delta,G^2)\le\varepsilon^2$, the algorithm returns $x_0$ at time zero. Otherwise, define the following quantities solely to read the formula; the public Lean `budget` expands them directly in the setup parameters:

\[
N=1+\lambda\Delta/\varepsilon^2,\quad
X=\frac{\widehat L\Delta}{\varepsilon^2\sqrt n},\quad
Z=\frac{G^2}{n\varepsilon^2},\quad
M=1+\frac{\Delta}{\varepsilon^2}\left[\lambda+d\min\!\left(\lambda,\frac{\widehat L}{\sqrt n}\right)\right].
\]
\[
B=2+\ln(N+X)+\ln(1+\ln(nd)),\quad
L_0=1+\ln(1+\ln(dN)),\quad U_0=1+\ln(ndN),
\]
\[
\Phi=\min\{\sqrt{ZBL_0},\ L_0+\ln(1+ZB),\ U_0\}.
\]

All logarithms are natural. Their arguments are positive throughout the stated parameter range, including $n=d=1$. With the explicit universal constant $C=2^{22}$, the proved deadline is

\[
T=C\begin{cases}
N\,[\tau+bd\{2+\ln N+\ln(1+\ln d)\}],&n=1,\\
N\tau+b\,[BM+d\Phi],&n>1.
\end{cases}
\]

This replaces the previous public finite optimization over packet capacities and tuning parameters. There are no opaque tuning helpers in the public budget. The factor $C$ is a conservative proof constant, not a claim about practical runtime. The simplification preserves the parameter and logarithmic dependence; it does not absorb a logarithmic loss into soft-O notation. The $64b$ term retains the mandatory padding on every upload, and $d\Phi$ retains initialization. The one-worker branch uses the valid bounds $\widehat L\leftarrow\lambda$ and $G\leftarrow\min(G,\sqrt{2\lambda\Delta})$, avoiding a spurious dependence on loose local bounds.

The [closed-budget proof](../Proofs/DashaDistributedClosedBudget.lean) bounds the selected implementation's execution time by this formula. The [deadline algorithm](../Algorithms/DashaDistributedDeadline.lean) and [deadline proof](../Proofs/DashaDistributedDeadline.lean) preserve its DASHA trajectory and returned output at the larger published deadline. This is an upper bound on actual execution, not an equality with the old finite minimum.

## Algorithm and cost accounting

The implementation retains the finite selection rule over block sizes, precisions, and initialization types. Its [proved recipe comparisons](../Proofs/DashaDistributedRecipes.lean) supply explicit choices covering all parameter regimes. For $X\le N$, a small-initial-gradient regime uses sparse initialization and sparse updates; otherwise, a more accurate full initializer or modular dense initializer is selected. For $X>N$, full-coordinate updates with increased precision keep the iteration count proportional to $N$. The minimum in $\Phi$ accounts for these initialization alternatives. Clipped coordinate counts cover every $d\ge1$, including saturation at one and at $d$.

For a retained-coordinate count $k$ and precision $r$, put
\[
\omega=(1+2/4^r)d/k-1,\quad
D=\lambda+\widehat L\sqrt{\omega(2\omega+1)/n},\quad
\eta=1/(8D),\quad a=1/(2\omega+1).
\]
Each worker uses a fresh independent random cyclic mask and unbiased scalar rounding. A mask is a uniformly shifted cyclic block of $k$ coordinates, not a uniform draw from all $k$-subsets. Its equal inclusion probabilities give the compressor moments used in the proof. The updates are
\[
x^{t+1}=x^t-\eta\bar g^t,\qquad
g_i^{t+1}=g_i^t+\mathcal C_i^t\bigl(\nabla f_i(x^{t+1})-\nabla f_i(x^t)-a(g_i^t-\nabla f_i(x^t))\bigr).
\]
The lattice spacing is $\rho=\frac{\varepsilon}{16}\sqrt{n/[d(\omega+1)]}$. Dense initialization rounds every local gradient; sparse initialization has its own block size and precision. With initial penalty $A=(4\omega+1)\omega_0G^2/n$ for sparse initialization and $A=0$ for dense initialization,
\[
K=1+\left\lceil(32\Delta D+4A)/\varepsilon^2\right\rceil_+.
\]
In the nonzero branch, exactly $K$ local gradient evaluations occur per worker: initialization and $K-1$ updates. One auxiliary update used in the telescoping proof is not executed. Uniform selection of the returned iterate and its free broadcast require no further gradient query.

For actual initialization and update payloads $B_{\rm init}$ and $B_{\rm round}$, the execution time is
\[
K\tau+b[B_{\rm init}+(K-1)B_{\rm round}].
\]
The proof bounds these actual bit-list lengths, including sign, precision, exponent fields, and initialization, before simplifying the expression. All uploads use dedicated links concurrently. Root broadcasts have zero latency and zero per-bit cost, as requested, while remaining finite bit lists and finite event sequences.

## Why the finite-bit implementation matters

The main proof combines descent with local and aggregate tracking-error energies. Independent worker compression provides the $1/n$ variance reduction. Quantization introduces an additive error floor; the displayed spacing makes that floor compatible with the requested squared-norm accuracy.

For message capacities, a pathwise envelope for the gradient and local tracking errors grows at most geometrically in the iteration index. Exponent fields therefore represent a possibly exponentially large numeric range without using a fixed-point field whose width grows linearly with the iteration count. This bound applies to every seed, including rare unstable compression sequences. The closed-budget proof amortizes the remaining range logarithms over all messages and the initialization charge, instead of charging the worst range independently to every round.

Put $\delta=\rho\sqrt d$ and $J=\min(G,\sqrt{2\lambda\Delta})$. Modular dense initialization sends each integer code modulo a common power of two. The root sums the residues and restores the signed total only after every worker has contributed. The aggregate range is at most $n(J+\delta)/\rho$ per coordinate. Workers retain their full local codes. This removes avoidable dependence on large cancelling local gradient offsets from both dense initialization and subsequent packet ranges; it does not assert a range bound for partial sums or individual local gradients.

## Prior work, scaling, and limitations of the comparison

The closest baseline is Tyurin and Richtárik's [DASHA paper, Theorem 6.1 and Corollary 6.2](https://openreview.net/pdf?id=VA1YpcNr7ul), ICLR 2023. Its deterministic analysis gives the same smoothness/compression dependence, up to constants, with exact real-valued compressed coordinates. Its squared-gradient tolerance must be replaced by $\varepsilon^2$ when comparing with our accuracy convention; the different notation does not give an improved accuracy exponent. The [arXiv version is v2, 22 May 2022](https://arxiv.org/abs/2202.01268v2). Our mean-square component smoothness condition is standard: see [PAGE, Assumption 2, equation (5)](https://proceedings.mlr.press/v139/li21a/li21a.pdf). Individual smoothness constants with the prescribed root-mean-square bound imply it; the converse with the same constants is not assumed. Relative to the ideal real-coordinate analysis, this setup additionally supplies an initial local-gradient bound $G$ and a concrete network model. The modular dense range bounds use $G$ only through $J$, which saturates at the global gap-based bound.

For comparable global and component smoothness, choosing $k\asymp d/\sqrt n\ge1$ and constant precision keeps $D=O(\lambda)$. With dense initialization, or with sparse initialization satisfying $A=O(\lambda\Delta)$, the iteration count retains its usual $O(\lambda\Delta/\varepsilon^2)$ order while the main-round coordinate payload decreases by order $\sqrt n$, before the displayed finite-bit factors. This is a regime statement: initialization, latency, metadata, small dimension, and computation can dominate total time. The theorem retains each of these costs. It does not promise unbounded or universal linear speedup in $n$.

The implementation’s finite-family minimum is not a lower bound on DASHA or on the problem class. The public formula is a sufficient deadline with a conservative universal constant, not the exact value of that minimum. A universal optimal-time claim would require comparisons against adaptive, correlated, variable-length, and other encodings. The proved [precision-cutoff comparison](../Proofs/DashaDistributedBudget.lean) bounds the selected time by four times the cost of every unrestricted precision choice in this same float/static-range coding family. The capping map retains each comparator’s block sizes and initialization type; the finite minimum may select different ones. The proof caps main and initial precisions, bounds the resulting iteration count by twice its original value, and accounts for the changed packet widths, initialization, latency, and metadata. This comparison does not establish optimality against an ordinary fixed-range fine-grid codec or other encoding families. No claim of mathematical novelty or universal coding optimality is made.

## Fairness and realism of `TemplateDistributed.lean`

The [distributed template](../TemplateDistributed.lean) is stronger than a round-count abstraction for this purpose: it checks actual asynchronous event processing, query completion, bit-list communication, deadlines, and finite-event execution. Those features prevent treating an idealized round count as a proved elapsed-time bound. This implementation is nevertheless a synchronous DASHA schedule on that event interface; the original paper's absence of periodic synchronization resets does not mean it tolerates arbitrary stale gradients.

Several favorable assumptions come from the chosen setup and star network, rather than being unavoidable restrictions of the template. These include dedicated parallel uplinks, known fixed worker computation times, linear upload cost, free server broadcast, and shared randomness that makes masks known without coordinate-index messages. Comparisons must use the same assumptions. Charging dense broadcasts could remove the claimed communication advantage even though convergence and some computation speedup remain possible.

The model charges oracle service and communication, but not local real arithmetic, integer coding, aggregation, or offline parameter search. Exact local gradients and exact arithmetic on retained integer codes are idealizations. There is no bandwidth contention, packet loss, variable service-time distribution, or realistic cost for distributing the common random seed. A more realistic study could charge these operations, model a shared uplink bottleneck or multicast, include nonzero downlink costs, and expose randomized service times. Such changes need explicit execution and probability models, rather than an informal multiplier added to this theorem. The frozen template is not modified by this contribution.

## Verification status

The Researcher and independent Reviewer each passed `./build.sh`, `./lint.sh`, and `python3 run_comparator.py DashaFreeBroadcastDeterministic.lean` on the integrated Lean contents. The full build completed 7315 jobs. Fourteen linters reported zero errors in 48508 declarations and 49835 automatically generated declarations. Comparator accepted the one main result and its budget with Lean’s default kernel and only `propext`, `Classical.choice`, and `Quot.sound` as permitted axioms. The templates, core definitions, verification infrastructure, toolchain, and dependency pins are unchanged.

These checks establish the formal guarantee under the stated model. They do not establish mathematical novelty, universal coding optimality, or realistic performance on an unspecified physical network.
