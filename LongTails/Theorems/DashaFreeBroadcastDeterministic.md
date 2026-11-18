# DASHA with deterministic gradients, finite messages, and free broadcast

This contribution formalizes the full-gradient DASHA method under the user's explicit waiver of mathematical novelty. It does not claim a new state-of-the-art optimization rate or an optimality theorem over all encodings. The public [theorem](DashaFreeBroadcastDeterministic.lean) is `DashaFreeBroadcastDeterministic.result`. Its budget is the explicit finite minimum below, and its proof establishes equality with the implemented execution budget.

The [setup](../Setups/DistributedFreeBroadcastSmoothNonconvex.lean) specifies arbitrary finite-dimensional, possibly nonconvex local functions, their average objective, exact local gradient oracles, and the network. The [algorithm](../Algorithms/DashaDistributed.lean), [parameter choices](../Algorithms/DashaDistributedTrackedParameters.lean), and [selection rule](../Algorithms/DashaDistributedSelection.lean) implement actual bit messages. The [execution and accuracy proof](../Proofs/DashaDistributedTracked.lean) connects the implementation to `DistributedTemplate.execute` and its probability law.

## Problem and guarantee

There are $n\ge1$ workers and $d\ge1$ coordinates. Write $F=n^{-1}\sum_i f_i$. Each local function is differentiable with the stated gradient. The parameters satisfy $L,\widehat L,\varepsilon>0$, $\Delta,G\ge0$, $h_i>0$, and $\ell,b\ge0$. The smoothness assumptions are

\[
\|\nabla F(x)-\nabla F(y)\|\le L\|x-y\|,\qquad
\frac1n\sum_i\|\nabla f_i(x)-\nabla f_i(y)\|^2\le\widehat L^2\|x-y\|^2,
\]

together with a lower bound $F_*\le F(x)$, $F(x_0)-F_*\le\Delta$, and $\|\nabla f_i(x_0)\|\le G$. The algorithm knows these bounds, not the functions or future gradients. The initial local-gradient bound supplies a numerical range for the signed and sparse initialization options; it is not a bound on gradients throughout the trajectory.

The returned point is uniformly selected from the first $K$ iterates, with

\[
\mathbb E\|\nabla F(x_{\rm out})\|^2\le\varepsilon^2.
\]

Expectations include compression and output-selection randomness. Local gradients and network service times are deterministic. This is neither a stochastic-gradient oracle theorem nor a pathwise stationarity guarantee. The proof includes output measurability and integrability, and finite events at every deadline up to the time budget.

The assumptions admit nonlinear objectives with interacting coordinates. For example, a positive quadratic plus bounded sinusoidal terms in nonorthogonal linear combinations of coordinates has a globally Lipschitz gradient and a finite lower bound. Local affine perturbations whose sum is zero can make individual initial gradients arbitrarily large without changing the average objective. This latter family explains why communication should depend on the aggregate range when possible.

## Updates, precision, and elapsed time

Set $\lambda=\min(L,\widehat L)$. For one worker, the implementation also replaces the local smoothness bound by $\lambda$ and $G$ by $\min(G,\sqrt{2\lambda\Delta})$; these follow from the original assumptions. The following formulas use the resulting parameters.

For a retained-coordinate count $k\in\{1,\ldots,d\}$ and precision $r\ge0$, define

\[
q=d/k,\quad \omega=(1+2/4^r)q-1,\quad
D=\lambda+\widehat L\sqrt{\omega(2\omega+1)/n},\quad
\eta=1/(8D),\quad a=1/(2\omega+1),
\]
\[
\rho=\frac{\varepsilon}{16}\sqrt{\frac{n}{d(\omega+1)}},\qquad
\delta=\rho\sqrt d,\qquad J=\min(G,\sqrt{2\lambda\Delta}).
\]

Each worker uses a fresh independent random cyclic mask and unbiased scalar rounding. The mask is a uniformly shifted cyclic block of $k$ coordinates, not a uniform draw from all $k$-subsets; its equal inclusion probabilities give the compressor moments used here. Its update is

\[
x^{t+1}=x^t-\eta\bar g^t,\qquad
g_i^{t+1}=g_i^t+\mathcal C_i^t\bigl(\nabla f_i(x^{t+1})-\nabla f_i(x^t)-a(g_i^t-\nabla f_i(x^t))\bigr).
\]

Dense initialization rounds every local gradient to the lattice of spacing $\rho$. Sparse initialization uses separate choices $k_0,r_0$, with $q_0=d/k_0$, $\omega_0=(1+2/4^{r_0})q_0-1$, and penalty $A=(4\omega+1)\omega_0G^2/n$. For dense initialization set $A=0$. The iteration count is

\[
K=1+\left\lceil\frac{32\Delta D+4A}{\varepsilon^2}\right\rceil_+.
\]

Exactly $K$ local gradient evaluations are performed per worker: initialization and $K-1$ subsequent updates. The analytic telescoping argument extends the estimator trajectory by one auxiliary gradient/compressor update. That auxiliary gradient evaluation is not executed. Forming the final point and sending its free broadcasts require no additional gradient query.

Let $s(z)$ denote the binary size of a natural number. The packet capacities use

\[
C=(2+2q)(1+\sqrt n\,\widehat L\eta),\qquad
B_0=\begin{cases}J+3\delta&\text{dense},\\J+(2q_0+1)G+3\delta&\text{sparse},\end{cases}
\]
\[
U=q(1+\sqrt n\,\widehat L\eta)B_0/\rho,\qquad
e=s\bigl(s(\lceil U\rceil_+)+K\,s(\lceil C\rceil_+)\bigr),\qquad
B_{\rm round}=k(r+e+3).
\]

The initial payload, according to the chosen option, is:

\[
B_{\rm init}=\begin{cases}
d\,[s(\lceil G/\rho+1\rceil_+)+1]&\text{signed dense},\\
d\,[s(\lceil n(J+\delta)/\rho\rceil_+)+1]&\text{modular dense},\\
k_0\,[r_0+s(s(\lceil q_0G/\rho\rceil_+))+3]&\text{sparse}.
\end{cases}
\]

With $h_{\max}=\max_i h_i$, upload latency $\ell$, and per-bit time $b$, the concrete execution time is

\[
T=K(h_{\max}+\ell+64b)+b\,[B_{\rm init}+(K-1)B_{\rm round}].
\]

The 64-bit term is the template's mandatory per-message padding. All uploads use dedicated links concurrently. Root broadcasts have zero latency and zero per-bit cost, as requested, but are still finite bit lists and finite event sequences.

In the Lean search space, a coordinate-count index `k : Fin d` represents `k.val + 1` retained coordinates. The optional second index specifies sparse initialization; `none` specifies dense initialization. The Boolean chooses signed (`false`) or modular (`true`) dense initialization and has no effect on sparse initialization. All formulas and finite index ranges are displayed immediately above the public budget.

The selection rule minimizes the proved time over all $k$, precisions $0\le r\le 2+s(\lceil2\widehat L/(\lambda\sqrt n)\rceil_+)$, and the initialization options. Sparse initial precisions range through $2+s(\lceil\sqrt{2(4\omega+1)}G/(\varepsilon\sqrt n)\rceil_+)$. If $\min(2\lambda\Delta,G^2)\le\varepsilon^2$, it instead returns $x_0$ at time zero, without queries or messages. The finitely many initial wake events are included in its termination proof.

## Why the finite-bit implementation matters

The main proof combines descent with local and aggregate tracking-error energies. Independent worker compression provides the $1/n$ variance reduction. Quantization introduces an additive error floor; the displayed spacing makes that floor compatible with the requested squared-norm accuracy.

For message capacities, the pathwise quantity
\[
\|\nabla F(x^t)\|+\max_i\|g_i^t-\nabla f_i(x^t)\|+2\delta
\]
is bounded by $B_0C^t$. Exponent fields therefore represent a possibly exponentially large numeric range without using a fixed-point field whose width grows linearly with the iteration count. This bound applies to every seed, including rare unstable compression sequences.

Modular dense initialization sends each integer code modulo a common power of two. The root sums the residues and restores the signed total only after every worker has contributed. The aggregate range is at most $n(J+\delta)/\rho$ per coordinate. Workers retain their full local codes. This removes avoidable dependence on large cancelling local gradient offsets from both dense initialization and subsequent packet ranges; it does not assert a range bound for partial sums or individual local gradients.

## Prior work, scaling, and limitations of the comparison

The closest baseline is Tyurin and Richtárik's [DASHA paper, Theorem 6.1 and Corollary 6.2](https://openreview.net/pdf?id=VA1YpcNr7ul), ICLR 2023. Its deterministic analysis gives the same smoothness/compression dependence, up to constants, with exact real-valued compressed coordinates. Its squared-gradient tolerance must be replaced by $\varepsilon^2$ when comparing with our accuracy convention; the different notation does not give an improved accuracy exponent. The [arXiv version is v2, 22 May 2022](https://arxiv.org/abs/2202.01268v2). Our mean-square component smoothness condition is standard: see [PAGE, Assumption 2, equation (5)](https://proceedings.mlr.press/v139/li21a/li21a.pdf). Individual smoothness constants with the prescribed root-mean-square bound imply it; the converse with the same constants is not assumed. Relative to the ideal real-coordinate analysis, this setup additionally supplies an initial local-gradient bound $G$ and a concrete network model. The modular dense range bounds use $G$ only through $J$, which saturates at the global gap-based bound.

For comparable global and component smoothness, choosing $k\asymp d/\sqrt n\ge1$ and constant precision keeps $D=O(\lambda)$. With dense initialization, or with sparse initialization satisfying $A=O(\lambda\Delta)$, the iteration count retains its usual $O(\lambda\Delta/\varepsilon^2)$ order while the main-round coordinate payload decreases by order $\sqrt n$, before the displayed finite-bit factors. This is a regime statement: initialization, latency, metadata, small dimension, and computation can dominate total time. The theorem retains each of these costs. It does not promise unbounded or universal linear speedup in $n$.

The exact finite-family minimum is not a lower bound on DASHA or on the problem class. A universal optimal-time claim would require comparisons against adaptive, correlated, variable-length, and other encodings. The proved [precision-cutoff comparison](../Proofs/DashaDistributedBudget.lean) bounds the selected time by four times the cost of every unrestricted precision choice in this same float/static-range coding family. The capping map retains each comparator’s block sizes and initialization type; the finite minimum may select different ones. The proof caps main and initial precisions, bounds the resulting iteration count by twice its original value, and accounts for the changed packet widths, initialization, latency, and metadata. This comparison does not establish optimality against an ordinary fixed-range fine-grid codec or other encoding families. No claim of mathematical novelty or universal coding optimality is made.

## Fairness and realism of `TemplateDistributed.lean`

The [distributed template](../TemplateDistributed.lean) is stronger than a round-count abstraction for this purpose: it checks actual asynchronous event processing, query completion, bit-list communication, deadlines, and finite-event execution. Those features prevent treating an idealized round count as a proved elapsed-time bound. This implementation is nevertheless a synchronous DASHA schedule on that event interface; the original paper's absence of periodic synchronization resets does not mean it tolerates arbitrary stale gradients.

Several favorable assumptions come from the chosen setup and star network, rather than being unavoidable restrictions of the template. These include dedicated parallel uplinks, known fixed worker computation times, linear upload cost, free server broadcast, and shared randomness that makes masks known without coordinate-index messages. Comparisons must use the same assumptions. Charging dense broadcasts could remove the claimed communication advantage even though convergence and some computation speedup remain possible.

The model charges oracle service and communication, but not local real arithmetic, integer coding, aggregation, or offline parameter search. Exact local gradients and exact arithmetic on retained integer codes are idealizations. There is no bandwidth contention, packet loss, variable service-time distribution, or realistic cost for distributing the common random seed. A more realistic study could charge these operations, model a shared uplink bottleneck or multicast, include nonzero downlink costs, and expose randomized service times. Such changes need explicit execution and probability models, rather than an informal multiplier added to this theorem. The frozen template is not modified by this contribution.

## Verification status

The Researcher and independent Reviewer each passed `./build.sh`, `./lint.sh`, and `python3 run_comparator.py DashaFreeBroadcastDeterministic.lean` on the integrated Lean contents. Lint reported zero errors, and Comparator accepted the main result and its budget using Lean’s default kernel with only `propext`, `Classical.choice`, and `Quot.sound` as permitted axioms. The original templates, core definitions, verification infrastructure, toolchain, and dependency pins are unchanged.

These checks establish the formal guarantee under the stated model. They do not establish mathematical novelty, universal coding optimality, or realistic performance on an unspecified physical network.
