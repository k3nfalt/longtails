# Novelty assessment: NearAcceleratedPolylogPrecisionRelativeErrorConvex

[`result`](../../LongTails/Theorems/NearAcceleratedPolylogPrecisionRelativeErrorConvex.lean) concerns a convex, globally L-smooth `f` on a real Hilbert space with a minimizer `x*` satisfying `‖x₀−x*‖ ≤ R`. Every gradient reply may be adversarial, provided `‖g−∇f(x)‖ ≤ α‖∇f(x)‖` with `α ≤ 1/(100(33(1+log(2+LR²/ε)))¹²)` ([setup](../../LongTails/Setups/SharpRelativeErrorSmoothConvex.lean), which restricts [this base spec](../../LongTails/Setups/RelativeErrorSmoothConvex.lean)). Under these conditions, the deterministic recursive Moreau-envelope method [`distanceEnvelopeOutput`](../../LongTails/Algorithms/SharpDistanceEnvelope.lean) returns a point with `f(x_out) − f(x*) ≤ ε` for every seed. The method uses `L, R, ε, x₀` but not α.

**Complexity.** L is the smoothness constant, R the initial distance, ε the target gap and α the relative error. Write `s = 1+log(2+LR²/ε)`. The exact public budget then gives, counting physical gradient calls:

  N = O( s¹⁶ · log(33s) · (2+LR²/ε)^{1/2 + log(16384(1+log(33s)))/(32 log(32s))} ),  valid for `0 ≤ α ≤ (100(33s)¹²)⁻¹`.

The suppressed constant is `32768·33¹⁶ ≈ 7·10²⁸`. The exponent excess is below 0.089 for every T ≥ 0, and it tends to 0 like `log log log T / (32 log log T)`. So the bound is `T^{1/2+o(1)}` with T = LR²/ε, but it is not `√T·polylog T`. Below, α* is the admissible threshold (≈8·10⁻²⁵ at T = 1). I computed crossovers numerically at α = α*; smaller α favours the baselines.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Vasin–Gasnikov, [arXiv:2603.12376v1](https://arxiv.org/abs/2603.12376v1) (12 Mar 2026 preprint, prior), Thm 7.2 (Thm 9.3 is similar), with the largest admissible β = log(1/(3α))/log(12T) | `150(12T)^{1−β}ln(4T)`, which is `T^{1−o(1)}` at α* → N | `T^{1−O(log log T/log T)}` → `T^{1/2+o(1)}`. The bound is smaller only for `ln T ≳ 606`. | None (same class restricted to α ≤ α*) | None (same last-output gap). Their method needs α; this one does not use α in its updates. | Far worse for `ln T < 606`. Their theorem allows α up to 1/3 at β = 0; this one needs α ≤ α*. |
| Repository damped acceleration [AcceleratedRelativeErrorConvex](../../LongTails/Theorems/AcceleratedRelativeErrorConvex.lean) (Lean, 2026-10-14, prior; restated in [arXiv:2610.24863v1](https://arxiv.org/abs/2610.24863v1), Remark 3.1) | `⌈7√(T/(1−α)) + 11α²T/(1−α)⌉`, which is `≈T/(10⁴(33s)²⁴)` at α* → N | `T/polylog T` → `T^{1/2+o(1)}`. Better iff `11α²T ≳ N`, i.e. only for `ln T ≳ 935` at α = α*. | None | None (that method needs α; this one does not) | Worse whenever `α ≲ √(N/T)`, and for all practical T. That baseline covers every α < 1. |
| Repository [PolylogPrecisionRelativeErrorConvex](../../LongTails/Theorems/PolylogPrecisionRelativeErrorConvex.lean) (Lean, 2026-10-26, prior; **identical spec**) | `⌈8(33s)²⁰(2+T)^{5/8}⌉` → N | **Uniformly smaller.** The exponent drops from 5/8 to below 0.589, and the prefactor ratio `4096(1+log 33s)/(33s)⁴` is below 1. For example, log₁₀N goes from 98.5 to 85.6 at ln T = 100. | None | Output: averaged inner iterate → last inner iterate (internal only; public output is the same kind of point) | None found |
| Repository [RecursiveRelativeErrorConvex](../../LongTails/Theorems/RecursiveRelativeErrorConvex.lean) (Lean, 2026-10-24, prior) | `4√(2+T)(32+log(2+T))^{32(1+√log(2+T))}`, valid only for `α ≤ e^{−8(1+√log(2+T))}/100` → N | On that overlap, this result is smaller for `ln T ≲ 1.7·10⁹`. Beyond that, the earlier result wins: its excess, `≈32 log log T/√log T`, decays faster. | Tolerance `e^{−O(√log T)}` → `Θ((log T)^{−12})`: covers every α in between | None | Asymptotically worse on the overlap |

**Reduction check.** The general-convex relative-error results I checked, apart from the repository's, either need `α ≲ T^{−1/2}` for an accelerated rate or pay `T^{1−β}` with `α ≍ T^{−β}`: Kornilov et al. [arXiv:2310.00506](https://arxiv.org/abs/2310.00506), Thm 3.1; Vasin–Gasnikov Thm 7.2/9.3; and Vasin–Tyurin–Gasnikov 2610.24863v1, Thm 2.4/3.3 (`O(T log)`, or `T^{1−2γ}` with `3α = (μ/L)^γ`). Batching cannot reduce adversarial bias. A plain Catalyst / inexact-proximal composition ([Lin–Mairal–Harchaoui, JMLR 2018](https://jmlr.org/papers/v18/17-748.html); Burns–Liang [arXiv:2602.17878v1](https://arxiv.org/abs/2602.17878), Thm 2.3, which uses exact gradients) fails because the regularized subproblem receives an absolute error floor `αμ‖c−p‖`.

**Proof ancestry.** The Moreau-envelope recursion and warm solver come from the repository's own two predecessors. The new step is the shifted-storage potential `φ(x)+μ‖z−p‖²/2` for the last iterate. Its nonnegativity comes from convex subtraction, not from a PSD certificate of the kind in Gürbüzbalaban ([arXiv:2309.11481v5](https://arxiv.org/abs/2309.11481v5)). It yields a nearly unit distance contraction whose slack costs only `log(1/τ)` iterations. This removes the polynomial overhead behind the 5/8 exponent. I read the companion description of this lemma and the theorem wiring. I did not check the proofs line by line, build the project, or run the comparator.

**Lower-bound note.** Like its siblings, the result conflicts with the literal Thm 10.2 of 2603.12376v1 only under the reading criticised in earlier reviews (App. G). I did not resolve that dispute independently.

**Search coverage** (2026-11-04 UTC). I searched arXiv and the web for relative or multiplicative gradient error, acceleration, and Catalyst / inexact-proximal schemes. I checked statement-level text of 2603.12376v1 (§7, §9.3; §10 only partly verbatim) and 2610.24863v1 (Thm 2.4, 3.3, Rem 3.1). I also checked 2506.09730v3 (Vernimmen–Glineur: PEP numerics only, no complexity theorem), 2408.00720v3 (absolute error only) and 2602.17878v1. I did not read the JOTA final text of Kornilov et al. or the final MOR text of Gürbüzbalaban. I found no external result with exponent below 1 at inverse-polylog relative precision. The companion note's citations, the 1/46 crossover scale (`log s ≈ 14.7`) and its regime statements match what I checked. Its 12/23 retuning figure is an unverified hand calculation that I did not use.

## Conclusion

**Only asymptotically: against outside methods, the proved budget is smaller only once `ln(LR²/ε)` exceeds roughly 600–935.** The strongest baselines are the repository's damped accelerated method (any α < 1) and Vasin–Gasnikov's regularized method (2026 preprint, Thm 7.2).

At the largest admissible relative error `α ≍ (log T)^{−12}`:

| Method | Calls |
|---|---|
| Vasin–Gasnikov Thm 7.2 | `T^{1−o(1)}` |
| Damped acceleration (repo) | `T/(log T)²⁴` |
| Predecessor, same spec (repo) | `T^{5/8}(log T)²⁰` |
| This result | `T^{1/2+o(1)}(log T)¹⁶` |

Within the repository, the gain is clean: the budget is uniformly smaller than its identical-spec predecessor. It also combines the precision of that predecessor with the near-`√T` exponent of the recursive result, which needs `α ≤ e^{−O(√log T)}`. Against outside methods, the gain begins only near T ≈ e⁶⁰⁶, and the constant is ≈10²⁹. Whenever `α ≲ √(N/T)`, damped acceleration is better.

The comparison proves this asymptotic gain. The search found no prior result of this kind, which supports priority but cannot establish it. The improvement comes from a sharper inner last-iterate certificate inside the repository's own recursive scheme, a week after two closely related results. What can be claimed is that, for smooth convex minimization, adversarial relative gradient error of order `(log(LR²/ε))^{−12}` still permits `(LR²/ε)^{1/2+o(1)}` gradient calls. That is a qualitative precision–complexity statement, not a usable speedup.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
