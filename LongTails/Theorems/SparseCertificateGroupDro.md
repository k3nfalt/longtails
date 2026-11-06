# Optimum-gap adaptive sampling for convex group DRO

[Main theorem](SparseCertificateGroupDro.lean) · [Setup](../Setups/OptimumGapGroupDro.lean) · [Algorithm](../Algorithms/SparseGroupSampling.lean)

The result gives a dimension-dependent raw-sample complexity bound governed by group risk gaps **at a minimizer**, without requiring a separation condition throughout the domain. It applies to general nonlinear convex losses. It is an information-theoretic sample guarantee: the finite meshes and exhaustive optimization used by the algorithm can be computationally expensive.

## Problem and guarantee

Let $Q\subseteq\mathbb R^d$ be nonempty, compact and convex, with a public point $x_0\in Q$ and $\|x-x_0\|\le R$ for every $x\in Q$. A known jointly measurable loss $\ell(x,z)$ is convex and $G$-Lipschitz in $x$ on $Q$, and takes values in $[0,1]$. There are $K\ge1$ unknown group distributions. A query chooses one group and returns one independent sample from it. Retained samples can be evaluated at other decisions without further sample queries.

Write
\[
f_i(x)=\mathbb E_i[\ell(x,Z)],\qquad F(x)=\max_{i\le K}f_i(x).
\]
Fix any minimizer $x_\star\in Q$, and let
\[
\Delta_i=F(x_\star)-f_i(x_\star).
\]
The setup's private parameters $g_i\in[0,1]$ are lower bounds $g_i\le\Delta_i$. They affect only the theorem's budget; the algorithm receives neither these bounds, the distributions, nor the minimizer. Taking $g_i=\Delta_i$ gives the strongest instance-dependent specialization. Different minimizers may have different group gaps; no unique-minimizer assumption is made.

For $0<\varepsilon\le1$, $0<\delta\le1/4$, set $s=d+1$ and
\[
L=\log\frac{128Ks}{\varepsilon\delta}
  +d\log\left(8+\frac{4096Rs^2(1+G)}{\varepsilon}\right).
\]
The proved budget is
\[
N=\left\lceil512s^2L\sum_{i=1}^K
       \frac{1}{\max\{g_i,\varepsilon\}^2}\right\rceil.
\]
After exactly $N$ calls through the repository's `execute`, the returned feasible point $Y$ is measurable and satisfies
\[
\Pr\{F(Y)-F(x_\star)>\varepsilon\}\le\delta.
\]
Every query, including padding after certification, is counted. There is no extra validation query. The guarantee concerns the actual returned random point, rather than the objective evaluated at its expectation.

The sample space can be an arbitrary measurable space; there is no finite-support restriction. The formal oracle uses an abstract IID reservoir of rows, with independent group coordinates within each row. Each query exposes only the next unused coordinate of its chosen group. The execution seeds are the diagonal replication of that hidden reservoir, so **execution seeds are not asserted to be IID**. This is a canonical encoding of fresh adaptive group sampling; it does not expose the other coordinates or distribution laws to the algorithm. The Lean specification uses this encoding explicitly.

## Algorithm and proof mechanism

The algorithm fixes a finite primal mesh inside $Q$, with covering radius
$\rho=\varepsilon/[512s(1+G)]$, and a finite sup-norm mesh inside the simplex of weights supported on at most $s$ groups, with radius $\eta=\varepsilon/(512sK)$. These meshes depend only on public geometry and parameters. Their existence is proved; the construction uses fixed real constants and classical choice, and does not provide a rational, finite-bit mesh algorithm.

At count $n_i$, let $\widehat f_i$ be the group's empirical risk and
\[
r_i=\begin{cases}1,&n_i=0,\\
\min\{1,\sqrt{8L/n_i}\},&n_i>0.
\end{cases}
\]
The zero-count empirical function is zero. Thus the initial upper risk is identically one, and no uncounted initialization samples are needed. Define $U_i=\widehat f_i+r_i$. The primal choice minimizes $\max_i U_i$ on the primal mesh. The dual choice maximizes the minimum weighted upper risk on that mesh, over the sparse dual mesh. Both use deterministic finite-list tie breaking.

The algorithm samples a group maximizing $w_i r_i$. It freezes its primal choice when
$\max_i w_i r_i\le\varepsilon/(4s)$. Certification is checked immediately after each sample. Subsequent calls query a fixed group but leave the frozen state and output unchanged.

The new acquisition argument combines sparse convex certificates with confidence-weighted sampling. Helly's theorem and separation of an open convex upper image produce normalized nonnegative weights supported on at most $d+1$ groups. No gradients, differentiability, strong convexity, interior optimizer, or strict complementarity are needed. Approximation by the two finite meshes gives the corresponding discrete certificate. Simultaneous Hoeffding confidence is required only at primal mesh points; Lipschitz continuity transfers it to the optimizer.

If $V$ is the empirical upper value at the primal choice, the resulting inequalities are
\[
\sum_i w_i\Delta_i\le2\sum_iw_i r_i+E,
\qquad
F(Y)-F(x_\star)\le2\sum_iw_i r_i-\sum_iw_i\Delta_i+E,
\]
where
\[
E=4G\rho+\frac{\varepsilon}{64s}+2K\eta
 \le\frac{7\varepsilon}{256s}<\frac{\varepsilon}{8s}.
\]
For an uncertified selected group $i$, sparse support gives
$\sum_j w_jr_j\le s w_ir_i$. The additive error is absorbed by the selection threshold. Consequently
\[
\max\{\Delta_i,\varepsilon\}\le4s r_i.
\]
A selected positive pre-count therefore obeys
\[
n_i\le\frac{128s^2L}{\max\{\Delta_i,\varepsilon\}^2}.
\]
The same bound holds with the private lower gap $g_i$. Accounting separately for the first pull and the final increment yields the total budget above. The algorithm need not identify the active set or know any positive gap.

The confidence proof unions over groups, primal mesh points, and counts up to the auxiliary horizon $\lceil e^{4L}\rceil$; the actual budget is proved no larger than this horizon. There is no union over dual weights. The mesh cardinality enters logarithmically. The execution proof tracks oracle history counts separately from frozen algorithm counts, proves equality on the active prefix, and proves preservation of empirical totals and the stored output after freezing.

The principal supporting modules are [sparse convex separation](../Proofs/SparseConvexCertificate.lean), [finite saddle approximation](../Proofs/FiniteSparseSaddle.lean), [state accuracy](../Proofs/SparseGroupAccuracy.lean), [concentration](../Proofs/SparseGroupConcentration.lean), [execution](../Proofs/SparseGroupExecution.lean), and [integration](../Proofs/SparseGroupConvergence.lean). Classical convex geometry, Hoeffding concentration, covering arguments, and finite measurable selection are supporting ingredients, not separate novelty claims.

## What changes relative to prior work

The bounded convex Lipschitz sample-loss assumptions, compact decision set, and reusable raw-sample oracle match the established GDRO model in Nguyen, Mehta and Guzmán, [*Beyond Minimax Rates in Group Distributionally Robust Optimization via a Novel Notion of Sparsity*](https://proceedings.mlr.press/v267/nguyen25e.html), ICML 2025, [arXiv 2410.00690v2](https://arxiv.org/abs/2410.00690v2), Assumption 2.1. Their Theorem 3.4 uses uniform $(\lambda,\beta_\lambda)$-sparsity throughout the domain and gives, suppressing constants,
\[
\frac{Kd\log(GDK/\delta)}{\lambda^2}
 +\frac{(D^2G^2+\beta_\lambda)\log(K/\delta)}{\varepsilon^2},
\]
with their diameter parameter $D$ (here $D\le2R$). Appendix G discusses the difficulty of replacing this all-point structure by locality at the optimum. Our setup removes the uniform-sparsity assumption rather than adding curvature to localize the iterates. The price is an additional dimension dependence and computationally expensive finite optimization. Their fully adaptive covering-based result is itself information-theoretic; our result does not match the computational efficiency of their semi-adaptive method.

For exact gaps, let $\beta=|\{i:\Delta_i=0\}|$. When the positive inactive gaps exceed $\varepsilon$, our guarantee becomes
\[
\widetilde O\left((d+1)^2[d+1]
 \left[\frac{\beta}{\varepsilon^2}
       +\sum_{\Delta_i>0}\frac1{\Delta_i^2}\right]\right),
\]
where the explicit $L$ above specifies the logarithmic and geometric dependence. In fixed dimension, fixed positive inactive gaps contribute no leading $\varepsilon^{-2}$ term. Against the usual $\widetilde O(((GR)^2+K)/\varepsilon^2)$ GDRO bound, this is meaningful when $K$ is large compared with the dimension factor times $\beta$, and the inactive-gap term is smaller than the baseline's $K/\varepsilon^2$ term. Up to logarithms, sufficient comparison conditions are
$K\gg d(d+1)^2\beta$ and
$\varepsilon^2\sum_{\Delta_i>0}\Delta_i^{-2}\ll K/[d(d+1)^2]$ for $d\ge1$. This is not universal superiority: dense active sets, small gaps, high dimension, or a demand for efficient computation can favor existing methods. The theorem does not prove an optimal dimension dependence.

Other close results and reduction checks:

- Ito, Luo, Tsuchiya and Wu, [*Instance-Dependent Regret Bounds for Learning Two-Player Zero-Sum Games with Bandit Feedback*](https://proceedings.mlr.press/v291/ito25a.html), COLT 2025, [arXiv 2502.17625v1](https://arxiv.org/abs/2502.17625v1), Theorem 1 and Appendix D, provide mixed-comparator Tsallis regret and equilibrium-gap self-bounding. Combining that analysis with strongly convex primal OGD gives a standard localization route. It requires additional curvature and does not yield this general-convex, high-probability actual-output guarantee. Such a composition is not claimed as new here.
- Hanashiro and Jaillet, [*Distribution-Dependent Rates for Multi-Distribution Learning*](https://proceedings.mlr.press/v313/hanashiro26a.html), ALT 2026, [arXiv 2312.13130v2](https://arxiv.org/abs/2312.13130v2), Sections 4–5, already use confidence-driven distribution sampling and sample reuse, with finite decisions and a covering extension. Their allocation depends on decision-specific group gaps across the decision set, not only gaps at one optimizer. Confidence sampling and reuse alone are therefore not our novelty claim.
- Zheng, Waggoner, Liu and Chen, [*Active Information Acquisition for Linear Optimization*](https://arxiv.org/abs/1709.10061v3), UAI 2018, Theorem 4.2, analyze confidence-guided constraint sampling in linear optimization. The gap dependence is over visited decisions, with known linear coefficients and noisy right-hand sides. This is an important predecessor, but does not give the nonlinear optimum-only bound.
- Jiang and Zhang, [*An LP-Based Approach for Bilinear Saddle Point Problem with Instance-dependent Guarantee and Noisy Feedback*](https://arxiv.org/abs/2602.12513v1), February 2026 preprint, Theorem 3.4, uniformly estimate matrix entries and identify supports using basis-value gaps and singular-value conditions. Theorem 5.1 controls suboptimality of the mean output. Reducing nonlinear GDRO to a mesh game introduces mesh-size and basis-conditioning costs; it does not imply the groupwise optimum-gap, high-probability bound proved here. Empirical saddle-support selection itself is not new.

Uniform batching or uniform risk estimation still pays fine accuracy for every group. Strongly convex localization introduces a curvature assumption and a localization cost. Replacing the finite mesh by a matrix game and invoking existing entrywise support-identification results introduces different gaps and conditioning parameters. The substantive mechanism beyond these reductions is that **each selected group's uncertainty is bounded below by its gap at an optimizer**, through a sparse upper-risk dual certificate. No restriction to a fixed algorithm family is imposed in the setup to manufacture this comparison.

## Nonlinear scope and limitations

A concrete two-dimensional separation from all-point sparsity is obtained on $Q=[-1,1]^2$. Let
\[
\phi(x,y)=\log\cosh(x+y)+(x^2+y^2)/2,
\quad f_\pm=\phi\pm ax,
\quad f_j=\phi+(a+\Delta)x+b_jy-\Delta,
\]
with $a>0$, small positive $\Delta$, and distinct small $b_j$. The maximum is minimized at the origin: the two active groups give $\phi+a|x|\ge0$, while every inactive group has value $-\Delta$ there. At $(1,0)$, the positive-slope active group and all inactive groups tie for the worst risk, so the all-point sparsity parameter is at least $K-1$, although exactly two groups are worst at the optimum. The $\log\cosh(x+y)$ term couples coordinates. A common positive scaling and shift, and bounded mean-zero affine sample perturbations, give sample losses in $[0,1]$ with bounded Lipschitz constants independent of $K$. This example establishes a meaningful strict extension; strong convexity in this example is not required by the theorem.

A standard testing family explains the fixed-dimensional statistical dependence, with an explicit restricted regime: $\beta\ge2$, $0<\varepsilon\le1/512$, $0<\Delta_i\le1/32$ for inactive groups, and $0<\delta\le1/10$. On $[-1/4,1/4]$, take $\phi(x)=\log\cosh(x)/16$ and sample losses
\[
\ell_i(x,Z)=\tfrac12+\phi(x)+a_i x+Z,\qquad Z\in\{-1/8,1/8\}.
\]
There are $\beta-1$ active groups with slope $a_i=1/8$, one with slope $-1/8$, and inactive groups with slope $1/4$. Active offset means are zero; inactive means are $-\Delta_i$. All sample losses are convex, bounded in $[0,1]$, and uniformly Lipschitz. The baseline optimum is $x_\star=0$, with value $1/2$, and every $\varepsilon$-optimal baseline output satisfies $|x|\le8\varepsilon$.

For each inactive group separately, change only its offset mean to $12\varepsilon$. Every baseline-good point then has alternative risk at least $1/2+10\varepsilon$. At $x=-32\varepsilon$, the alternative maximum is at most $1/2+4\varepsilon+32\varepsilon^2$, using $\phi(x)\le x^2/32$. Hence the two sets of $\varepsilon$-optimal outputs are disjoint. Changing instead one positive-slope active mean from zero to $12\varepsilon$ gives alternative risk at least $1/2+11\varepsilon$ on baseline-good points; $x=-48\varepsilon$ has alternative maximum at most $1/2+6\varepsilon+72\varepsilon^2$, again separating the acceptable outputs. These test points lie in the domain in the stated regime.

The Bernoulli probability corresponding to mean $m$ is $1/2+4m$. Baseline and alternative probabilities stay in a fixed interval inside $(0,1)$, so their per-sample KL divergence is at most a universal constant times $(\Delta_i+12\varepsilon)^2$ for inactive groups and $\varepsilon^2$ for the tested active groups. Replaying a retained sample reveals no additional information about its offset mean.

Consider **any single algorithm uniformly $\delta$-correct across this family** with an observable stopping time $T$, and a baseline high-probability sample bound $\Pr(T\le N)\ge1-\delta$. In the transcript truncated at $T\wedge N$, the event “stop by $N$ and return a baseline-good point” has baseline probability at least $1-2\delta$ and alternative probability at most $\delta$. Binary testing therefore requires order $\log(1/\delta)$ KL divergence. The adaptive transcript chain rule charges this only to samples of the changed group. Summing the separate tests and using $\mathbb E[T\wedge N]\le N$ yields
\[
N=\Omega\!\left(\log(1/\delta)
 \left[\frac{\beta-1}{\varepsilon^2}
 +\sum_{\Delta_i>0}\frac1{\max\{\Delta_i,\varepsilon\}^2}\right]\right).
\]
Thus the upper bound matches this statistical dependence in fixed dimension, up to logarithms, in the stated stopping model and parameter regime. This comparison does not establish the best dimension dependence.

That lower-bound interpretation is qualified: the repository's `Convergence` predicate evaluates an algorithm at a private instance-dependent horizon, and alone does not require correctness at the baseline horizon on another instance. We do **not** assert the stopping lower bound for every algorithm satisfying that predicate. Our concrete certificate-freeze algorithm has an observable stopping rule and can use the public worst-case cap obtained by setting all private gaps to zero. The proved confidence event ensures correct certification and freezing by the instance budget. The lower-family comparison is explanatory mathematics, not an additional formally verified lower-bound theorem or a claim of dimension-optimality.

The result does not cover pointwise-only value/gradient feedback without reusable samples, unbounded losses without further estimation machinery, infinite-dimensional decisions, or computationally efficient implementations. It does not solve the dimension-free or runtime versions of the optimum-local sparsity question.

## Literature coverage

The Researcher and independent Reviewer began separate topic-directed surveys of the publicly available ICML, ICLR and NeurIPS 2025–2026 editions and roughly the preceding two years of arXiv submissions/revisions, then followed older primary references. The focused GDRO comparison was rechecked through 2026-11-06 UTC. The versions linked above were the latest versions located in those checks; official proceedings verify the stated accepted venues. The Jiang–Zhang paper is treated as a preprint, not an accepted conference result. Its SSRN page was inaccessible, but the arXiv primary text was read. These were targeted searches rather than an exhaustive inspection of every proceedings paper. No unresolved inaccessible source is used as evidence that a theorem is absent.
