# Warm-started radius halving for Broximal Gradient Descent in a general norm under constrained PL

The theorem [WarmHalvingBroxGeneralNorm.lean](WarmHalvingBroxGeneralNorm.lean) formalizes the main oracle-complexity result of P. Richtárik and X. Qian, [*Broximal Gradient Descent in General Norms: Convergence without Fejér Monotonicity*](https://arxiv.org/abs/2611.24645), arXiv:2611.24645v1 (18 Nov 2026). This is an unrefereed preprint, and v1 is its only version.

The formalized result is the warm-started radius-halving method (Algorithm "warm-started radius halving" in Section 4.3). It combines:

- Theorem "total oracle calls of warm-started halving", Section 4.3;
- Corollary "oracle calls to reach a prescribed accuracy", Section 4.3.

**Scope.** The user explicitly waived novelty for this task and asked for a clean formalization of the paper's setup, method and main convergence theorem. This note therefore claims no new optimization result. It records how faithfully the Lean statement matches the paper, and what was proved in addition.

## Why this is the paper's main convergence theorem

The paper does not label a single main theorem; its Table 1 is a catalogue of results. We chose this corollary for four reasons.

- It is the final quantitative claim of the abstract: "warm starting gives logarithmic total oracle complexity in inverse accuracy". It also appears as contribution (iv) and in the conclusion.
- Table 1 lists no earlier counterpart for it.
- It is the only result in the paper stated natively as a total oracle-call count for reaching accuracy `ε`.
- It is the paper's adaptive result: the method needs neither the PL modulus nor an initial gap bound.

The independent Reviewer selected the same result before seeing the Researcher's choice.

## Setup

The [setup](../Setups/BroxGeneralNormConstrainedPL.lean) follows Assumptions "geometry", "Lipschitz gradient in the dual norm" and "constrained PL" of the paper.

**Information visible to the algorithm.** `E` is an arbitrary finite-dimensional real normed space. It is not assumed to be an inner-product space, and its norm need not be smooth or strictly convex. The algorithm also receives:

- a valid smoothness constant `L > 0`;
- an initial cap radius `r = r̂₀ > 0`;
- the initial point `x0`.

**Hidden parameters.** These appear only in `Params`, which the algorithm does not receive:

- the PL modulus `μ > 0`;
- an upper bound `Δ ≥ f(x0) − f⋆`;
- the target accuracy `ε > 0`.

Because the algorithm cannot see them, the Lean statement enforces the paper's claim that the method uses neither `μ` nor a gap bound.

**Instance.** An instance is an objective `f : E → ℝ` and a feasible set `C ⊆ E`. The assumptions are:

- `C` is convex and closed, and `x0 ∈ C`.
- `f` is differentiable at every point of `C`.
- The gradient is `L`-Lipschitz in the dual norm on `C`: `‖f′(y) − f′(x)‖ ≤ L‖y − x‖` for `x, y ∈ C`. Here `f′(x) = fderiv ℝ f x : E →L[ℝ] ℝ`, and its operator norm is the dual norm.
- `f` is bounded below on `C`, with `f⋆ := inf_C f`. Attainment is not assumed.
- The constrained PL inequality holds on all of `C`: `μ (f(x) − f⋆) ≤ s(x)²/2`.
- `f(x0) − f⋆ ≤ Δ`.

The stationarity measure is the paper's normal-cone residual
`s(x) = inf_{n ∈ N_C(x)} ‖f′(x) + n‖_*`, where `N_C(x) = {n ∈ E* : n(z − x) ≤ 0 for all z ∈ C}`.

**Oracles.** There are two oracles, counted separately.

- Oracle 0 is the exact gradient. At `x ∈ C` it returns `f′(x)`.
- Oracle 1 is the exact local linear minimization oracle. At a center `x ∈ C`, radius `ρ ≥ 0` and functional `g`, it returns some minimizer of `g` over `C ∩ {‖v − x‖ ≤ ρ}`.

The LMO's choice among minimizers is adversarial and may depend on the query history and on the oracle seed. No function values, projections, multipliers, `f⋆` or `s` are revealed. Existence of LMO outputs follows from closedness of `C` and finite dimensionality, which is why both stay in the setup even though the proof never uses them.

**Accuracy criterion.** The output must lie in `C` and satisfy `f(output) − f⋆ ≤ ε`. The bound holds deterministically, for every admissible oracle; the template states it almost surely.

### Example instances

- **Strongly convex objectives.** By Section 5 of the paper, every `μ`-strongly convex objective, with respect to the chosen norm, whose gradient is `L`-Lipschitz in the dual norm satisfies the constrained PL inequality with modulus `μ`. This holds on every closed convex `C`. An example is a ridge-regularized logistic loss `Σᵢ log(1 + exp(aᵢᵀx)) + (λ/2)‖x‖₂²` with dense rows `aᵢ`, which couples the coordinates, on a box or a polytope in `ℓ∞` (sign-descent) or `ℓ1` (coordinate) geometry. Because all norms on `ℝᵈ` are equivalent, it is strongly convex with a Lipschitz gradient in every norm, with norm-dependent constants `μ` and `L`.
- **Convex objectives with quadratic growth.** More generally, convexity plus quadratic growth with constant `c` on all of `C` gives constrained PL with modulus `c/2`. The paper (Section 5) notes that this implication holds only on the region where the growth bound holds, while the setup needs PL on all of `C`.
- **An example with `μ > L`.** Take `f(x) = x` on `C = [0, 1]`. Then `s ≡ 1` on `(0, 1]` and `s(0) = 0`, so PL holds with `μ = 1/2` for every `L > 0`. Constrained PL does not force `μ ≤ L`, and the budget keeps the exact denominator `log(1 + μ/(25L))` instead of a bound such as `(1 + 25L/μ)`, which would lose a `log(μ/L)` factor when `μ ≫ L`.
- **Nonconvex objectives.** Nonconvex objectives satisfying ordinary PL (`C = E`, where `s = ‖f′‖_*`) are included.

These are illustrations from the paper. They are not separate Lean theorems.

## Method and output

The [algorithm](../Algorithms/WarmHalvingBrox.lean) is the paper's warm-started halving rule, with `r̂₀ = r`.

1. At each new center `x_k`, query the gradient `g = f′(x_k)` once.
2. Query the local LMO with `g` at radii `r̂_k, r̂_k/2, r̂_k/4, …`, where `r̂_k = r̂₀·2^{e}` for an integer exponent `e`.
3. For a reply `q`, let `d = −g(q − x_k)`.
   - If `d = 0`, stop: the center is stationary, and therefore optimal under PL.
   - Otherwise, if `d ≥ L·radius²`, accept: `x_{k+1} = q` and `r̂_{k+1} = 2·(accepted radius)`.
   - Otherwise, halve the radius and query again.

The returned point is the **current center**: the last accepted iterate, or `x0`. It is never a rejected trial point. After a stop, the state is frozen; any remaining budget is spent on gradient queries that do not change the output. The algorithm uses only `L`, `r̂₀`, `x0` and the oracle replies.

## Proved budget

Let

```text
K = ⌊log₄(1 + 6Δ/(L r²))⌋₊ + ⌈log_{1+μ/(25L)}(Δ/ε)⌉₊.
```

The public budget is:

- **gradient calls:** `K`;
- **local LMO calls:** `2K + ⌈log₄(r²(8L²/μ + 6L)/ε)⌉₊`.

Here `⌈·⌉₊` and `⌊·⌋₊` are `Nat.ceil` and `Nat.floor`, so negative arguments contribute `0`.

**Relation to the paper's constants.**

- The first term of `K` is the paper's bound `k_cap ≤ log₄(1 + 6Δ₀/(L r̂₀²))`. The second term is `⌈log(Δ₀/ε)/log(1 + μ/(25L))⌉`.
- The extra LMO term equals the paper's `log₂⁺(2 r̂₀ √(C_rej/ε))`, because `log₄((2 r̂₀)² C_rej/ε) = log₂(2 r̂₀ √(C_rej/ε))`, with `C_rej = 2L²/μ + 3L/2`.
- The paper's call bound is `2T − 1 + log₂⁺(…)`. The Lean budget uses `2K` in place of `2T − 1`, one extra call, to keep the formula simple.
- The paper does not count gradient evaluations separately; it states that one gradient is evaluated per center. Lean counts them: at most `K`.

**Asymptotic dependence.** The total is `O(log(Δ/ε)/log(1 + μ/L) + log(1 + Δ/(L r̂₀²)) + log(1 + r̂₀²(L²/μ + L)/ε))` oracle calls. This is logarithmic in `1/ε`, and no parameter dependence is lost relative to the paper. When `Δ ≤ ε`, the second term of `K` vanishes, and the guarantee is trivially met by `x0`.

**From hitting time to a fixed budget.** The paper bounds the first index at which the gap falls below `ε`, together with the number of calls used up to that index. The repository template instead runs the algorithm for a fixed per-oracle budget and evaluates the output at that point. The conversion relies on two facts:

- accepted updates never increase `f`, and a stop is optimal;
- the current center is therefore `ε`-accurate as soon as a budget runs out.

This conversion is proved in Lean; it is not stated in the paper.

## Proof outline and Lean modules

[WarmHalvingBroxAnalysis.lean](../Proofs/WarmHalvingBroxAnalysis.lean) contains the one-step analysis.

- **Two-sided quadratic model.** `|f(y) − f(x) − f′(x)(y − x)| ≤ (L/2)‖y − x‖²` on `C`, by a one-dimensional fencing argument. The lower half is needed for the paper's rejected-radius floor.
- **Certificate at the output** (the paper's Lemma "certificate at the output"): `s(q) ≤ Lr + d/r`. The paper derives the multipliers from a convex-analysis sum rule (Rockafellar, Theorem 23.8). The Lean proof uses two steps instead.
  1. An elementary comparison point `x + β(z − x)`, with `β = r/(r + ‖z − q‖)`, gives `−g(z − q) ≤ (d/r)‖z − q‖` for every `z ∈ C`.
  2. A Hahn–Banach extension (`exists_extension_of_le_sublinear`, applied to the sublinear function `v ↦ inf_{k ∈ cone(C − q)} (M‖v + k‖ − φ(k))`) produces `n ∈ N_C(q)` with `‖g + n‖_* ≤ d/r`. This step works in any real normed space.
- **Early stop.** `d = 0` implies `−g ∈ N_C(x)`, hence `s(x) = 0`, and PL then makes `x` optimal.

[WarmHalvingBroxSteps.lean](../Proofs/WarmHalvingBroxSteps.lean) contains the step lemmas.

- descent and ascent;
- the rejected-radius bound `Δ(x) < C_rej·radius²` (from Corollary "oracle calls to reach a prescribed accuracy");
- the uncapped-step bound `Δ(q) < 25L²r²/(2μ)` (from Theorem "total oracle calls of warm-started halving"(b));
- the radius-exponent bound `−e ≤ ⌈log₄(…)⌉₊`;
- a generic lemma: if an invariant on (state, remaining per-oracle budget) is preserved by every affordable query, and every state at which some budget is exhausted satisfies the target predicate, then the output of `OracleTemplate.execute` satisfies it.

[WarmHalvingBroxExecution.lean](../Proofs/WarmHalvingBroxExecution.lean) contains the execution invariant. While the run is not stopped, the invariant records:

- the exact call counts: gradient calls `= m (+1 once the center's gradient is fetched)` and LMO calls `= 2m − e`, the paper's identity `2K − 1 + log₂(r̂₀/r_{K−1})`;
- monotonicity of the gaps;
- the radius floor `Δ(center) ≤ ε ∨ radius ≥ min{r̂₀, ½√(ε/C_rej)}`;
- the information `d(2r) < L(2r)²` left by a rejection at radius `2r`;
- one of two phases.
  - In the all-capped initial phase, `Δ(x_m) + (L r̂₀²/2)(4^m − 1)/3 ≤ Δ`. This yields `k_cap`.
  - In the post phase, the gap contracts by `1 + μ/(25L)` per update, which is the paper's analysis of uncapped steps and of capped steps after an uncapped one.

While `Δ(center) > ε`, these facts give `m < K` and `2m − e < 2K + ⌈log₄(…)⌉₊`, so no budget can run out before an `ε`-accurate center is reached.

The comparator audit of `result` and `budget` accepts only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Differences from the paper's statement

All of the following are weakenings of the hypotheses or slightly looser constants. None strengthens an assumption.

- **Differentiability.** Lean requires differentiability only at the points of `C`. The paper assumes differentiability on an open convex neighborhood of `C`, which is stronger.
- **LMO input.** The LMO accepts an arbitrary functional, which is slightly richer than "the BroxGD oracle at `(x, r)`". The algorithm only ever passes the gradient of the current center.
- **Gap bound.** `Δ` is any upper bound on the initial gap. The paper uses the exact `Δ₀`; the budget is monotone in `Δ`.
- **Accuracy range.** The paper's corollary assumes `0 < ε < Δ₀`. The Lean theorem covers every `ε > 0`.
- **Call count.** `2K` replaces `2T − 1`, as described above.

## Relation to prior work

Novelty is waived. The paper itself says that the local oracle and the residual inequality are established ingredients.

- **Ferris and Zavriev (1996, Wisconsin TR 96-12)** analyze the same subproblem, linear minimization over `C ∩ {‖h‖ ≤ r}` in an arbitrary norm. They use an Armijo-type radius search based on function values and prove linear convergence under the Luo–Tseng error bound. We found no bound on the total number of LP solves in that report; their successive-linear-programming method solves at least two LPs per iteration.
- **Nesterov, "Universal gradient methods for convex optimization problems", Math. Program. 2015.** Restarting each search at twice the last accepted step, with the resulting `2K + log` amortized count of backtracking calls, is the standard device from this paper.
- **D. Kovalev, [arXiv:2503.12645](https://arxiv.org/abs/2503.12645).** The proof of Theorem 1 already contains the inequality `Δ(q) + r·s(q) ≤ Δ(x) + 3Lr²/2`, taking the regularizer to be `ι_C`. The intermediate certificate `s(q) ≤ Lr + d/r` used here is the paper's refinement of it.
- **K. Gruntkowska and P. Richtárik, [arXiv:2510.00823](https://arxiv.org/abs/2510.00823).** The non-Euclidean broximal point method; the paper cites it as the source of the linearized ball-proximal update in a general norm.
- **P. Richtárik, K. Gruntkowska and H. Li, [arXiv:2605.08850](https://arxiv.org/abs/2605.08850) (v2).** This is the Euclidean version of BroxGD.
  - Their linear rate under PL (Theorem D.16) assumes the stronger PL condition on the projected-gradient mapping, and its radius needs a projection.
  - Their backtracking result (Theorem 3.6), under strong convexity, counts accepted steps only.
  - The present result extends to general norms, uses the weaker normal-cone PL condition, and bounds total calls.
- **Karimi, Nutini and Schmidt (ECML-PKDD 2016)** introduced proximal-PL conditions, to which the constrained PL condition is closely related.

## Limitations

- The guarantee concerns oracle calls. Each local LMO call is an exact subproblem solve (an LP when `C` and the norm ball are polyhedral), and its cost is outside the model.
- The method needs a valid smoothness constant `L`.
- The PL inequality must hold on all of `C`, because the analysis applies it at rejected trial points, which may lie above the current level set.
- The bound is an upper bound. No matching lower bound is claimed.
