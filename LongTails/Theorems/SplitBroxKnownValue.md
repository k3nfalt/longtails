# Accelerated local linear minimization with a known optimal value

The theorem [SplitBroxKnownValue.lean](SplitBroxKnownValue.lean) proves an epsilon-accuracy guarantee for a projection-free method that uses exact, point-only linear minimization over the feasible set intersected with a ball. It counts value-gradient queries and every local linear query, including unsuccessful radius trials. The returned point is the last primal iterate.

## Problem and information

The [setup](../Setups/KnownValueSmoothConvexLocalLinear.lean) specifies a closed convex set `C` in a real complete inner-product space, a feasible initial point `x0`, and a minimizer `xstar` with `‖x0-xstar‖ ≤ R`. The objective has a gradient at every feasible point and satisfies the standard first-order convex lower model and quadratic upper model on `C`:

\[
f(x)+\langle\nabla f(x),y-x\rangle\le f(y)
\le f(x)+\langle\nabla f(x),y-x\rangle+\tfrac L2\|y-x\|^2,
\qquad x,y\in C.
\]

These assumptions include ordinary convex objectives with an `L`-Lipschitz gradient, restricted to an arbitrary closed convex feasible set. The formulation does not require control of normal-gradient variation away from the feasible set. It covers general nonlinear objectives in arbitrary finite dimension and, conditional on the exact oracle contract, complete Hilbert spaces. There is no diameter bound, strong convexity, bound on the gradient at a constrained minimizer, or level-set radius assumption.

The algorithm knows `L>0`, `R≥0`, `ε>0`, `x0`, and **the exact optimal value `fstar`**. It does not know a minimizer. Knowing the value is a material information assumption, shared with accelerated Polyak minorant methods; this is not a result for unknown optimal values or arbitrary lower bounds.

One oracle query returns `(f(z),∇f(z))`. Another returns any minimizer of `⟨g,v⟩` over `v∈C`, `‖v-x‖≤r`, for a supplied feasible center `x`, direction `g`, and radius `r≥0`. Only the point is returned. Ties can depend arbitrarily on the query index and oracle seed. Both query types have unit cost in the combined interface. No projection or dual multiplier is provided. The cost of implementing either oracle internally is outside this oracle-complexity model.

A concrete nonlinear family is
\[
C=\{x:x_d\ge0\},\qquad
f(x)=\sum_i\log\cosh(a_i^\top(x-x_\star))+M x_d,
\quad (x_\star)_d=0,\quad M\ge0.
\]
Dense, nonorthogonal rows `a_i` give interacting coordinates. The known value is zero by nonnegativity, `L=‖A‖²` is a smoothness bound, and the normal gradient at the minimizer is `M e_d`, with no bound on `M`. More generally, a known zero fitting loss plus a nonnegative cost supplies the optimal-value certificate in constrained interpolation problems. The theorem does not require this particular structure.

## Method and proved budget

The [algorithm](../Algorithms/SplitBrox.lean) maintains momentum `x` and primal `y`, initially both `x0`. For iteration `k=1,…,K`, let `α=2/(k+1)` and `z=(1-α)y+αx`. Query `f(z),g=∇f(z)` and form
\[
H=f(z)+\langle g,x-z\rangle-f_\star.
\]
If `H≤0`, keep `x` and set `y=z`. Otherwise query the local linear oracle at the same center and direction with radii `b,2b,4b,…`, stopping at the first reply `u` satisfying `⟨g,x-u⟩≥H`. Set the new primal to `(1-α)y+αu`. If the crossing occurred at radius `b`, keep the momentum; otherwise set it to the previous reply, whose cut inequality was strict in the opposite direction. There are no restarts or best-iterate selection.

The setup permits any algorithm using the stated public information and oracle access. The convergence theorem establishes existence by constructing this SplitBrox state machine with explicit tuning; its last-primal output is a property of that construction, rather than a restriction on all admissible algorithms.

For any positive proof radius `D` bounding the initial distance, take `b=D/√K`. The analysis gives
\[
f(y_K)-f_\star\le\frac{10LD^2}{K(K+1)},
\]
using at most `K` value-gradient queries and `2K` local linear queries before completion. The fixed-budget implementation freezes the output after completion and pads with radius-zero local queries, all counted.

The epsilon theorem uses the explicit tuning
\[
K=\left\lceil\sqrt{10LR^2/\varepsilon}\right\rceil+1,
\qquad D=\sqrt{R^2+\varepsilon/(10L)},\qquad b=D/\sqrt K.
\]
This covers `R=0` without a separate algorithm. Since `K(K+1)≥10LR²/ε+1`, the gap is at most `ε`. The public Lean budget is exactly
\[
\boxed{3\left(\left\lceil\sqrt{10LR^2/\varepsilon}\right\rceil+1\right)}.
\]
It is `O(1+√(LR²/ε))` total calls, with no explicit dimension factor; implementing the oracles may still have dimension-dependent cost. If `R>0` and a prescribed horizon is used instead, the analysis with `D=R` gives the displayed `10LR²/[K(K+1)]` rate. Do not confuse that horizon tuning with the slightly inflated radius used by the public epsilon theorem.

## New mechanism and proof

The two adjacent replies serve different purposes. A strict undercut reply `v` has `⟨g,xstar⟩<⟨g,v⟩`. Exact local linear optimality and convexity then imply
\[
\|v-x\|=r_{\rm low},\qquad
\|v-x_\star\|^2\le\|x-x_\star\|^2-r_{\rm low}^2.
\]
This is the momentum distance decrease. The crossing reply supplies the linear model inequality needed for the accelerated primal recurrence. Using one reply for both purposes, or interpolating an overshoot onto the cut, does not generally preserve the distance inequality.

With `A_k=k(k+1)/2`, the weighted primal recurrence charges at most `L r²` for a crossing radius `r`. Except at the initial radius, `r²=4r_low²`, so the curvature errors are paid by the momentum distance decrease. Initial-radius crossings cost at most `K b²`. Consequently the total squared crossing radii are at most `5D²`.

The same distance decrease pays for rejected queries: a crossing after `j≥1` doublings has `j≤4^(j-1)=r_low²/b²`. The total number of extra trials is at most `D²/b²=K`. This is why no logarithmic search factor appears in the total oracle count.

The formal proof uses two state invariants, including pending searches, and a rank that increases with every pre-completion oracle call. An unfinished state has rank strictly below `3K`, proving completion within the actual execution budget. This avoids assuming termination or counting only accepted iterations. Supporting modules are [geometry](../Proofs/SplitBroxGeometry.lean), [one-step bounds](../Proofs/SplitBroxStep.lean), [state invariants](../Proofs/SplitBroxState.lean), [counting](../Proofs/SplitBroxCounting.lean), [execution](../Proofs/SplitBroxExecution.lean), and [tuning](../Proofs/SplitBroxBudget.lean).

## Closest prior results and scope of the contribution

* Richtárik, Gruntkowska, and Li, [Broximal Gradient Descent](https://arxiv.org/abs/2605.08850v2), v2, September 28, 2026, Theorems 3.2 and D.2: the same exact point-only local linear oracle gives `O(LR²/ε)` calls for a best-iterate smooth convex guarantee. Their practical backtracking analysis, Theorem 3.6 and Appendix D, has different level-set and trial-count qualifications. Their strongly convex geometric-radius result, Theorem 3.3, is a stronger applicable baseline for that narrower objective class. Their smoothness hypothesis is an `L`-Lipschitz gradient on an open convex neighborhood of the feasible set; our specification needs the lower and quadratic upper models only on the set itself. The present result assumes the optimal value is known and is not an improvement over all BroxGD guarantees under identical information.
* Richtárik and Mahran, [Local LMO is Secretly a Projection Method!](https://arxiv.org/abs/2609.33383v1), v1, September 27, 2026, Theorems 2–4: undercut local linear queries have a projection interpretation, and suitably deep cuts yield nonaccelerated universal rates. That geometry informs the distance lemma here. The contribution is the accelerated split between adjacent replies and the simultaneous amortization of curvature and query cost, not a new claim that local linear minimization is related to projection.
* Deng, Lan, and Lin, [Uniformly Optimal and Parameter-free First-order Methods for Convex and Function-constrained Optimization](https://arxiv.org/abs/2412.06319v3), v3, April 16, 2026, Algorithm 1, Theorem 2.1, and Proposition A.1: APMM uses the same known-optimal-value idea and achieves accelerated rates through exact projections onto a feasible set intersected with linear level cuts. The smooth primal weighting is established there. APMM does not need `R` or `L` for its updates, whereas our base radius uses a distance bound and a horizon; `L` is used in our epsilon-dependent tuning. Thus the oracle improvement comes with this tuning-information difference. Replacing each exact cut projection by an uncounted subproblem would not establish our oracle guarantee. The split replies preserve the two needed inequalities separately and prove a linear total number of point-only local linear calls.
* Carmon et al., [RECAPP](https://proceedings.mlr.press/v162/carmon22a.html), ICML 2022, and [inexact accelerated proximal methods with relative error rules](https://arxiv.org/abs/2005.03766), provide important acceleration reductions. Their required relative objective or residual certificates are not supplied merely by a constant number of generic local linear queries. Straightforward sufficiently accurate inner solves introduce logarithmic factors; this observation is not a lower bound on all possible reductions. The new proof avoids these inner certificates through its joint primal and momentum analysis.
* [Acceleration with a Ball Optimization Oracle](https://papers.nips.cc/paper_files/paper/2020/hash/dba4c1a117472f6aca95211285d0587e-Abstract.html), NeurIPS 2020, and Richtárik and Li's [A Sharper Theory of Ball-Proximal Optimization](https://arxiv.org/abs/2609.35147v1), v1, September 28, 2026, use nonlinear objective minimization over balls, a different oracle from linear minimization. Their rates should not be transferred to the present oracle by counting an inner solve as free.

The claimed contribution is an accelerated `O(√(LR²/ε))` bound for both oracle types, with a last-primal guarantee, arbitrary convex constraints, and no normal-gradient bound, **under known optimal value**. The improvement is meaningful as `LR²/ε` grows. It is not a constant-factor novelty claim, an unknown-value result, or a universal superiority claim over projection-based methods. We make no oracle lower-bound or minimax-optimality claim in the known-value model. Exact local minimization remains a substantial oracle requirement; inexact replies and unknown optimal values are outside the theorem.

The literature assessment used independent Researcher and Reviewer searches as of October 11, 2026: ICML 2026/2025, ICLR 2026/2025, NeurIPS 2025/2024 proceedings, the public NeurIPS 2026 listing, roughly two years of arXiv submissions and revisions, and foundational references. The September 2026 BroxGD, projection-interpretation, and sharper ball-proximal papers are treated as preprints; no accepted conference status was verified for them. APMM's arXiv record reports acceptance in INFORMS Journal on Computing. A NeurIPS 2026 adaptive conditional-gradient listing was found, but its individual conference page was inaccessible; the primary arXiv paper was checked. The survey is a documented novelty assessment, not a claim of exhaustive literature coverage or actual conference acceptance.
