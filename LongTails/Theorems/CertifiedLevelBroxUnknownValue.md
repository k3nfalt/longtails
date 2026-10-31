# Accelerated local linear minimization without the optimal value or the smoothness constant

The theorem [CertifiedLevelBroxUnknownValue.lean](CertifiedLevelBroxUnknownValue.lean) gives an accelerated oracle-complexity bound for smooth convex minimization over an arbitrary closed convex set. The method accesses the set only through the *local linear minimization oracle* (local LMO): exact linear minimization over the feasible set intersected with a ball. The algorithm is given the initial point, an upper bound R on its distance to a minimizer, and the target accuracy ε. It is **not** given the optimal value f⋆ or the smoothness constant L. Every value-gradient query and every local LMO query is counted, including all rejected radius trials, all smoothness checks, and all aborted runs.

## Problem and information

The [setup](../Setups/UnknownValueSmoothConvexLocalLinear.lean) fixes a closed convex set `C` in a real Hilbert space and a feasible initial point `x0`. The objective `f` has a gradient at every point of `C` and satisfies, for all `x, y ∈ C`, the first-order convexity inequality and the quadratic upper model

\[
f(x)+\langle\nabla f(x),y-x\rangle\le f(y)\le f(x)+\langle\nabla f(x),y-x\rangle+\tfrac L2\|y-x\|^2 .
\]

There is a minimizer `x⋆ ∈ C` with `‖x0 − x⋆‖ ≤ R` and `f(x0) − f(x⋆) ≤ Δ`. The set may be unbounded. The setup assumes no diameter bound, no gradient bound, and no bound on the normal gradient `‖∇f(x⋆)‖` at a constrained minimizer.

The setup has two kinds of data:

- **Public input to the algorithm:** the space, `x0`, `R` and `ε`.
- **Parameters used only in the budget:** `L ≥ 0` and `Δ ≥ 0`.

The quantity `f⋆` appears nowhere in the specification seen by the algorithm.

There are two oracle query types, both counted with unit cost:

- `(f(z), ∇f(z))` for a feasible point `z`.
- The local LMO. Given a feasible centre `x`, a radius `r ≥ 0` and a direction `g`, it returns some minimizer of `⟨g, v⟩` over `v ∈ C` with `‖v − x‖ ≤ r`.
  - It returns only the point, not a multiplier.
  - Ties may be broken adversarially, depending on the query index.

This is the oracle of Ferris and Zavriev (1996), reintroduced by Richtárik, Gruntkowska and Li ([Broximal Gradient Descent, arXiv:2605.08850 v2](https://arxiv.org/abs/2605.08850)) and analysed by Richtárik and Mahran ([Local LMO is Secretly a Projection Method!, arXiv:2609.33383 v1](https://arxiv.org/abs/2609.33383)).

One nonlinear family with interacting coordinates is the following:

- the set is `C = {x : x_d ≥ 0}`;
- the objective is `f(x) = Σ_i log cosh(a_iᵀ(x − x̄)) + M x_d + (λ/2)‖x‖²`;
- the rows `a_i` are dense and non-orthogonal, and `M ≥ 0` is unrestricted.

In general its optimal value is not known in closed form. More broadly, any smooth convex problem over a set with a cheap ball-intersected LMO is covered: ℓ_p or nuclear-norm balls, boxes, simplices, and flow polytopes. BroxGD §B gives closed forms for several of these.

## Guarantee

The public budget is

\[
\Big\lceil 400\sqrt{LR^2/\varepsilon}+40\log_2\!\big(2+(\Delta+LR^2)/\varepsilon\big)\Big\rceil+300
\]

total oracle calls. It is `O(√(LR²/ε) + log((Δ + LR²)/ε))`, and the logarithm is additive. After that many calls, the returned point is feasible and satisfies `f(y) − f(x⋆) ≤ ε`. The output is the feasible point with the best observed value, which is what the method maintains as its upper bound.

## Method

The [algorithm](../Algorithms/CertifiedLevelBrox.lean) maintains:

- a certified lower bound `lb ≤ f⋆`;
- the best observed value `ub = f(best)` and its point;
- a smoothness estimate `L̂`.

**Initialization.** One value-gradient query at `x0` and one local LMO query at radius `R` give
`lb = f(x0) + ⟨∇f(x0), v − x0⟩`. This is valid because `x⋆ ∈ C ∩ B(x0, R)`. The initial gap satisfies
`ub − lb ≤ Δ + LR²/2`. The method sets `L̂ = ε/R²`. If `R = 0`, the gap is zero and the method stops at once.

**Phases.** While `gap = ub − lb > ε`, the method fixes the level `ℓ = (ub + lb)/2`, the horizon `K = ⌈√(40 L̂R²/gap)⌉ + 1` and the base radius `R/√K`. It then runs the split-reply accelerated local-LMO scheme from `x0` with level `ℓ` in place of an optimal value.
- The split-reply scheme is the scheme of the repository's earlier [SplitBroxKnownValue](SplitBroxKnownValue.md) theorem, reused through `SplitBrox.query`/`SplitBrox.update`.
- After each accepted inner step, one extra value-gradient query at the new primal point checks the quadratic upper model with constant `L̂` between the gradient point and the new primal point.
- The inner run is capped at `4K` calls.

Each phase ends in one of three outcomes:

1. **A check fails.** This proves `L̂ < L`. The method doubles `L̂` and restarts the phase.
2. **The run completes with `f(y_K) ≤ ℓ + gap/4`.** The method sets `ub := f(y_K)`, so the gap shrinks by at least a factor `3/4`.
3. **Otherwise** (the cap is reached, or the run completes with a larger value). This proves `ℓ < f⋆`, and the method sets `lb := ℓ`, halving the gap.

## Why the certificates are valid (the new mechanism)

The split-reply analysis uses the optimal value only through the cut inequality `f(z) + ⟨∇f(z), x⋆ − z⟩ ≤ f⋆`. It uses the smoothness constant only through the upper model between the gradient point `z` and the newly accepted primal point.

The [level-model lemmas](../Proofs/LevelBroxState.lean) therefore restate the invariants for an arbitrary level `ℓ`, an anchor `p ∈ C` with `f(p) ≤ ℓ`, and an upper-model hypothesis required only on crossing steps.

If `ℓ ≥ f⋆`, take `p = x⋆`. If every check in the phase passed, the invariants then hold with `L̂`. Two consequences follow:

- The run completes before `rank + completed` reaches `4K`.
- The final energy gives `f(y_K) − ℓ ≤ 10L̂R²/(K(K+1)) ≤ gap/4`.

Outcome 3 is therefore impossible when `ℓ ≥ f⋆`. Contrapositively, it certifies `ℓ < f⋆`. The certificate needs no detection of an empty level set, no projection, and no knowledge of `f⋆`. The call cap and the threshold are the certificate.

The [counting proof](../Proofs/CertifiedLevelBroxBudget.lean) uses the potential `200√(L̂R²/gap) + 9(phases + doublings)`:

- Every phase outcome raises the potential by at least the cost of the run it ends.
- The gap shrinks by `3/4` per non-aborted phase.
- `L̂ ≤ max(ε/R², 2L)` doubles at most `log₂(1 + 2LR²/ε)` times, and phases number at most `2.5 log₂(…)`.
- Phase costs are geometric in `gap^{-1/2}` and in `√L̂`, which gives the additive logarithm.

## Relation to prior work

| Work | Oracle and information | Guarantee | Relation |
| --- | --- | --- | --- |
| Richtárik, Gruntkowska, Li, [BroxGD, arXiv:2605.08850 v2](https://arxiv.org/abs/2605.08850) (28 Sep 2026), Thm 3.2(ii) | Same local LMO plus gradients; knows `R`, not `L` or `f⋆`; requires smoothness on an open neighbourhood of `C` | `f(x_best) − f⋆ ≤ LR²/(2K)`, i.e. `O(LR²/ε)` calls | Same information. The new bound improves `LR²/ε` to `√(LR²/ε)` plus an additive logarithm. |
| BroxGD Thms 3.4–3.5 (Polyak radius) | Needs `f⋆` | Non-accelerated `O(LR²/ε)`; `O(1/ε²)` for bounded subgradients | The new bound is accelerated and does not need `f⋆`. |
| BroxGD Thm 3.3 | Strongly convex; knows `L`, `μ` and a gap bound | `4κ log(C₀/ε)` | A different class. A restarted, accelerated strongly convex version is not formalized here. |
| Richtárik and Mahran, [arXiv:2609.33383 v1](https://arxiv.org/abs/2609.33383) | Local LMO; the Polyak-radius results need `f⋆` | Non-accelerated universal rates `O(K^{-(1+ϑ)/2})` | The new bound is accelerated in the smooth case. The Hölder (universal) case is not treated here. |
| Repository [SplitBroxKnownValue](SplitBroxKnownValue.md) (earlier, unpublished) | Same oracle; knows `f⋆`, `L` and `R` | `3(⌈√(10LR²/ε)⌉ + 1)` calls | The leading-rate mechanism (split replies) is that result's. The present theorem removes both `f⋆` and `L`. |
| Hazan and Kakade, [arXiv:1905.00313](https://arxiv.org/abs/1905.00313) (unknown-`f⋆` reduction for Polyak steps), combined with SplitBrox | Guess `f⋆`, with failure detected by a call cap; needs `L` for the cap | `O(√(LR²/ε)·log(Δ/ε))` | Certified gap reduction turns the multiplicative logarithm into an additive one. Online checks remove `L`. |
| Abdukhakimov, Pham, Horváth, Takáč, Hanzely, [arXiv:2508.17288](https://arxiv.org/abs/2508.17288); Liu, Bragin, Chen, Guan, [arXiv:2311.18255 v3](https://arxiv.org/abs/2311.18255) | Online estimation of `f⋆` for Polyak-type gradient/subgradient steps; unconstrained or projection-based | Non-accelerated | Same goal (no `f⋆`), but a different oracle, with no accelerated rate. |
| Lan's accelerated prox-level/bundle-level methods (Math. Program. 2015); Deng, Lan, Lin, APMM, [arXiv:2412.06319 v3](https://arxiv.org/abs/2412.06319) | Projections onto `C` intersected with level cuts. APL needs a compact domain; APMM needs `f⋆` | Optimal accelerated rates | Not available with a local LMO. The level-phase logic here is Lan's certified gap reduction, transplanted to this oracle. |
| Kiwiel, Larsson, Lindberg, ballstep subgradient level methods (1999) | Trust region plus level cut, nonsmooth | `O(1/ε²)` | Non-accelerated. |

**Projection emulation is not a shortcut.**
- By the KKT conditions, a local LMO reply is `P_C(x − t g)` for an unobserved step `t`.
- Large-step accelerated frameworks (A-HPE, RECAPP, adaptive Monteiro–Svaiter) need the step actually used in their weights.
- With a computable bracket `[t_lo, t]` obtained from a second radius, the HPE residual is exactly `(t − t_lo) g`. This residual is unbounded relative to `‖v − x̃‖` whenever the projection truncates the step, i.e. whenever `∇f` has a large normal component.
- Certifying the step therefore costs per-iteration logarithms of an unbounded truncation ratio, or an added gradient bound. The level-cut route never needs step lengths. This is an obstruction for that route, not a lower bound.

**What is new.** To our knowledge this is the first accelerated complexity bound for local-LMO methods that needs neither `f⋆` nor `L`. Under exactly the information of BroxGD Thm 3.2(ii), it improves the order from `LR²/ε` to `√(LR²/ε)`. The new mathematical ingredients are:

- level-model versions of the split-reply invariants, in which only the checked pairs carry the smoothness hypothesis;
- a certified level-phase controller in which the call cap and a value threshold prove `ℓ < f⋆`;
- a potential-function count that makes both the gap reduction and the `L̂` doubling additive.

The search covered arXiv 2025–2026 (local LMO, broximal methods, ball-oracle and trust-region acceleration), the two Richtárik et al. papers above, and their citations. It found no other accelerated local-LMO result, but a search cannot establish priority.

## Limitations

- **Novelty and origin of the question:** the leading-rate mechanism is the repository's split-reply analysis. The level estimation and the backtracking on `L̂` are textbook ideas; the contribution is making them certifiable for this oracle with additive overhead. The question of acceleration without `f⋆` was raised in the repository's own review of SplitBrox, not in a published paper.
- **Oracle and information:** the local LMO is a recent oracle, used so far by essentially one group. Exactness of its replies is assumed. The algorithm needs `R` and `ε`; `Δ` and `L` enter only the budget.
- **Constants:** they are not optimized (`400` and `40`). The method restarts every phase from `x0` and uses the best observed value as output; it gives no last-iterate guarantee.
- **Not covered:** strongly convex, Hölder-smooth, inexact-oracle and stochastic variants. No lower bound for the local-LMO model is claimed.

## Lean modules

- **Setup:** [UnknownValueSmoothConvexLocalLinear](../Setups/UnknownValueSmoothConvexLocalLinear.lean).
- **Algorithm:** [CertifiedLevelBrox](../Algorithms/CertifiedLevelBrox.lean).
- **Proofs:**
  - [LevelBroxState](../Proofs/LevelBroxState.lean): level-model split-reply invariants;
  - [CertifiedLevelBroxInvariant](../Proofs/CertifiedLevelBroxInvariant.lean): controller invariant;
  - [Start](../Proofs/CertifiedLevelBroxStart.lean), [Transition](../Proofs/CertifiedLevelBroxTransition.lean), [Init](../Proofs/CertifiedLevelBroxInit.lean), [RunStep](../Proofs/CertifiedLevelBroxRunStep.lean) and [CheckStep](../Proofs/CertifiedLevelBroxCheckStep.lean): phase outcomes and stage steps;
  - [Budget](../Proofs/CertifiedLevelBroxBudget.lean): counting;
  - [Execution](../Proofs/CertifiedLevelBroxExecution.lean): from the execution to the accuracy guarantee.
