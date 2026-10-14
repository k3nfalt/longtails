# Scalar stationarity with Hölder gradients and heavy-tailed feedback

The [Lean theorem](ScalarHolderHeavyTailStationarity.lean) proves a constant-success oracle-complexity upper bound for finding a stationary point of a possibly nonconvex function on the real line. The dimension-one restriction is essential. The result does not give an expected-gradient bound, a higher-dimensional guarantee, or a formalized minimax lower bound.

## Problem and guarantee

The [setup](../Setups/ScalarHolderStochastic.lean) assumes a differentiable, lower-bounded function `f : ℝ → ℝ`, an initial point `x₀`, and known positive `H, Δ, ε` such that

\[
 |f'(x)-f'(y)|\le H|x-y|^\nu,\qquad
 f(x_0)-\inf f\le\Delta,
 \quad 0<\nu\le1.
\]

The specification expresses the gap using an existential global lower bound; neither that lower bound nor function values are provided to the algorithm. A call at `x` returns a fresh scalar `g(x,ξ)`. The oracle is jointly measurable, unbiased, and has an integrable uniform central moment

\[
 \mathbb E|g(x,\xi)-f'(x)|^p\le\sigma^p,
 \qquad 1<p\le2,\quad\sigma\ge0.
\]

The common objective and moment assumptions appear in Liu, Assumption 4 with `G=0` (linked below). Our fresh IID oracle is a standard specialization of that paper’s more general adaptive-noise formulation, not a weakening of its assumptions.

Its sample stream has an abstract IID law. Independence at adaptive queries is derived from that law; a product distribution is not imposed as an extra assumption. There is no convexity, PL condition, bounded-gradient assumption, finite-support restriction, samplewise smoothness, or supplied stationary point. The algorithm knows the displayed bounds and exponents.

Write

\[
 A=\frac{H^{1/(1+\nu)}\Delta^{\nu/(1+\nu)}}{\varepsilon},
 \qquad Q=\left(\frac{\sigma}{\varepsilon}\right)^{p/(p-1)}.
\]

The actual returned point `X` satisfies `Pr(|f'(X)| > ε) ≤ 1/3`. The public budget is the single explicit expression

\[
 \left\lceil 2^{200/(p-1)}(1+1/\nu)
       \left[1+A+Q\log(2+A)\right]\right\rceil.
\]

Thus the call order is `O_{ν,p}(1 + A + Q log(2+A))`. Constants are deliberately loose and are not uniform as `p ↓ 1` or `ν ↓ 0`. The statement includes zero noise and initialization terms; it does not claim optimal behavior when the initial gap is already small enough to certify `x₀`.

## Algorithm and proof

The [algorithm](../Algorithms/ScalarHolderSearch.lean) uses only point-gradient replies and independent private randomness. A robust initial estimate either identifies an accurate initial point or selects a descent orientation. Uniform probes in a segment of length `32Δ/ε`, with dyadic accuracy levels, then find either an approximately stationary point or an opposite-sign endpoint. The gap and Hölder regularity imply a quantitative mass of useful probes. Probes run from coarse to fine scales; all their raw samples are charged.

The resulting bracket can contain arbitrarily many sign changes. A noisy search descends through locally valid subintervals and retreats when endpoint checks invalidate its current path. Candidate points receive additional validation steps. A uniformly selected recorded state is validated with fresh samples; the procedure makes 32 attempts and returns its first accepted candidate, with a specified fallback. It is not an ordinary monotone binary search, an average iterate, or a minimum selected using exact derivatives.

The central proof step is an occupation bound for this arbitrary-sign search. A potential subtracts twice the number of invalid nodes on the current path from the current depth. Reliable steps outside the acceptable region increase this potential, while any step decreases it by at most one. A charging argument controls visits below invalid ancestors and prevents an inaccurate candidate from becoming absorbing unless enough oracle tests fail. It yields a constant fraction of acceptable recorded states without assuming a unique root or monotonicity of the derivative. Conditional probability estimates then apply at the random bracket discovered from earlier samples. The selected recording times remain independent of this past.

The estimator combines a sample anchor, clipping of centered fresh replies, and repeated validation. These are established heavy-tail estimation ideas. Its proof retains the anchor cost, central-moment bias, integrability, and low-noise single-sample case. The complete execution also charges failed tests, all discovery stages, all attempts, and calls after an early successful candidate. The framework pads the completed plan to the public budget with ignored replies; these calls are counted. [Accuracy and execution proofs](../Proofs/ScalarHolderSearch.lean) connect the plan to `execute`; the [budget proof](../Proofs/ScalarHolderBudget.lean) proves the displayed ceiling dominates every call.

## Contribution and primary comparisons

The contribution claimed here is the nonconvex scalar upper bound with additive deterministic cost `A` and statistical cost `Q log(2+A)`, supported by the local-validity occupation argument. Neither the heavy-tail mean-estimation exponent, the scalar deterministic search rate, the statistical logarithm, backtracking itself, nor Lean formalization is claimed as a new mathematical idea.

| Primary result | Relation and limitations |
| --- | --- |
| [Chewi–Bubeck–Salim, ALT 2023, Theorems 2–3 and Appendix A](https://proceedings.mlr.press/v201/chewi23a/chewi23a.pdf) | Establishes the importance of scalar randomized search and its exact-gradient complexity. The smooth, noiseless `A` term is already known. Exact sign tests do not supply the noisy arbitrary-sign occupation guarantee. |
| [Liu, ALT 2026 full version, Appendix G.2.3, Theorem 17 and Corollaries 11–12](https://optimization-online.org/wp-content/uploads/2025/08/Online-Convex-Optimization-with-Heavy-Tails.pdf) | Uses Hölder gradients and central heavy-tail moments together. Its general-dimensional bound has dominant accuracy exponent `1+1/ν+p/(p−1)` for expected gradient norm. Markov's inequality converts that criterion to constant success after a constant accuracy adjustment. Our scalar restriction is substantial; this is not a uniformly better general-dimensional method. |
| [Ou–Wang, arXiv:2609.03990v2, Appendix D.4, Lemmas D.11–D.12, and the single-stage proof in D.1(ii), equations (244)–(255)](https://arxiv.org/pdf/2609.03990v2) | Despite the paper's PL objective, this single-stage stationarity argument is PL-free. Applying it to `F(x,y)=f(x)` gives, for `ν=1`, `A≥1`, and fixed `p`, a comparator of order `A^(4/3) log^(5/3)(2+A) + Q log^(p/(p−1)+2)(2+A)`. This comparison has not been established for fractional `ν`. We do not attribute PL to that particular argument. |
| [Foster et al., COLT 2019, Appendix C, Theorem 11](https://proceedings.mlr.press/v99/foster19b/foster19b.pdf) | Already proves the scalar smooth finite-variance statistical lower bound with a logarithmic dependence on `HΔ/ε²`. The logarithm in our upper is therefore not a new lower-bound discovery. Their convex upper results do not cover arbitrary nonconvex derivatives, and stronger sampled-function access must not be equated with raw point-gradient calls. |
| [Karp–Kleinberg, SODA 2007, Sections 4–5](https://www.cs.cornell.edu/~rdk/papers/karpr2.pdf) | Backtracking and occupation reasoning with indifference regions are established. Their promising-descendant properties use ordered search structure; arbitrary-sign brackets need the additional local-validity charging argument. |
| [Chaudhuri–Kalyanakrishnan, AAAI 2017, Theorem 3.1](https://ojs.aaai.org/index.php/AAAI/article/download/10802/10661) | Reservoir selection is an established comparator for discovery. Robust median elimination across scales can already achieve a discovery order `A+Q`; our particular confidence allocation is not asserted to be essential novelty. |

A stronger comparator than the displayed Ou–Wang reduction is a **standard composition under the same scalar setup**, even without a single paper stating its final formula. Robust multiscale discovery costs `O_{ν,p}(1+A+Q)`. Once it has a genuine opposite-sign bracket, ordinary bisection requires `D = O_ν(log(2+A))` tests. Monotonicity is unnecessary for this noiseless bracket invariant: either half selected by a reliable midpoint sign retains opposite-sign endpoints. Estimating each midpoint to a constant multiple of `ε` with failure probability `O(1/D)` costs `O_p((1+Q) log(2+D))` calls. A union bound makes all tests reliable with constant probability. Consequently this composition gives

\[
 O_{\nu,p}\!\left(1+A+Q\log(2+A)\log\log(3+A)\right).
\]

Here the harmless positive logarithm conventions absorb bounded-depth cases, and `D log(2+D)` is absorbed into `O_ν(1+A)`. This is a derived baseline, not a claim that Ou–Wang states it. It supersedes the larger explicit-paper comparator when assessing the size of the contribution.

**The improvement over this strongest routine baseline is removal of one `log log(3+A)` factor from the statistical search term.** There is no improved accuracy power, no deterministic polynomial improvement over that baseline, and no asymptotic improvement when `A` dominates both noisy terms. For growing `A` with `Q log(2+A)` dominating `A`, the new upper removes that factor; in particular this is the fixed-positive-parameter small-accuracy regime. The Ou–Wang comparison remains a valid comparison with a particular primary result at `ν=1`, but it does not establish the strongest available baseline. No claim of universal superiority across dimensions, access models, or success criteria is intended.

The theoretical significance rests on reaching the known lower-bound order in the smooth finite-variance scalar problem while allowing arbitrary sign changes, rather than on the numerical size of a new exponent. Ordinary high-confidence bisection pays for simultaneous correctness of every test. Classical noisy ordered search avoids that payment using a unique target or ordered promising descendants. The local-validity occupation proof establishes the needed robustness without either property, allowing different good branches and inaccurate near-zero tests. Whether closing this iterated-logarithmic gap is sufficiently significant is the strongest potential objection to the contribution; the improvement should not be inflated by omitting the standard composition. The fractional-regularity and heavy-tail extensions broaden the guarantee, but their standard estimation and scaling ingredients are not separately claimed as deep novelty.

For the smooth finite-variance endpoint `ν=1, p=2`, a precise nontrivial comparison regime is `A≥128`. Foster et al., Theorem 11, supplies the statistical lower term when `ε<σ/2`; Chewi–Bubeck–Salim supplies the deterministic term. Their maximum equals their sum up to a constant. In the complementary regime `σ≤2ε`, one has `Q≤4` and therefore `Q log(2+A)=O(A)`, so the deterministic lower bound suffices. This comparison matches the displayed upper order in that regime without asserting a newly formalized lower theorem.

The known deterministic and smooth finite-variance lower bounds explain the two terms. Extending those constructions by Hölder rescaling and rare informative replies suggests matching dependence for general `ν,p` in nontrivial large-`A` regimes. Such extensions are not part of the Lean theorem delivered here and are not presented as a new lower-bound mechanism. The proved result is the upper bound stated above.

## Nontrivial instances and limitations

A concrete scalar family is the stochastic linear-response loss

\[
 \ell(x;Y)=\frac{|x|^{1+\nu}}{1+\nu}-Yx+a\cos x,
 \qquad
 g(x,Y)=\operatorname{sign}(x)|x|^\nu-Y-a\sin x.
\]

If `E|Y−EY|^p ≤ σ^p`, its population objective is finite and coercive, its gradient noise has exactly that central moment, and a global Hölder constant is `2^(1−ν)(1+|a|)`. For `ν<1` and nonzero `a`, it has nonconvex regions; at `ν=1` one may choose `|a|>1`. For `p<2`, labels can have infinite variance. This is a linear-response or noisy-gradient example, not ordinary uncentered power-loss regression. The theorem also permits point-dependent noise and is not restricted to this additive example.

The result is scalar, assumes known regularity and moment parameters, uses ideal real arithmetic and continuous private randomness, and gives constant success only. Practical constants, unknown-parameter adaptation, higher dimensions, and a formalized matching lower bound remain outside its scope.
