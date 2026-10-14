# GdNonconvex: novelty assessment

[`result`](../../LongTails/Theorems/GdNonconvex.lean) proves the following. Let `f` be differentiable on a real Hilbert space `E` (any dimension), with an `L`-Lipschitz gradient, and let some lower bound satisfy `f(x0) − inf f ≤ Δ` ([setup](../../LongTails/Setups/SmoothNonconvex.lean)). Run gradient descent with step `1/L` for `K = max(1, ⌈2LΔ/ε²⌉)` gradient calls at `x_0, …, x_{K−1}`, and return the queried point with the smallest observed gradient norm ([algorithm](../../LongTails/Algorithms/GdNonconvex.lean)). That **best iterate** satisfies `‖∇f(x̂)‖² ≤ ε²`. The admissibility condition makes every oracle answer equal to the true gradient, so the expectation in the statement is deterministic.

**Complexity** (exact gradient calls):

  N = max(1, ⌈2 L Δ / ε²⌉) = O(1 + LΔ/ε²).

Here `L` is the gradient-Lipschitz constant, `Δ` bounds the initial objective gap, and `ε` is the target gradient norm. There are no logarithms. The [proof](../../LongTails/Proofs/GdNonconvex.lean) is the textbook telescoping argument: summing the descent lemma `f(x_{k+1}) ≤ f(x_k) − ‖∇f(x_k)‖²/(2L)` gives `min_{k<K} ‖∇f(x_k)‖² ≤ 2LΔ/K`. The initial threshold `2LΔ` for the best iterate is valid because `‖∇f(x0)‖² ≤ 2LΔ`. In the boundary cases `Δ = 0` or `ε² ≥ 2LΔ`, `K = 1` and the method returns `x0`, which is correct.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Classical GD with step `1/L` (Nesterov, *Introductory Lectures*, 2004, §1.2.3, as quoted in Abbaszadehpeivasti et al. p. 2 and in Carmon et al. §1: "at most `2L₁Δε⁻²` iterations") | `⌈2LΔ/ε²⌉` (+1 in AdKZ's indexing) → `max(1, ⌈2LΔ/ε²⌉)` | None: same order and same constant | None | None (same min-gradient best-iterate output; same knowledge of `L`) | The selected algorithm also needs `Δ` to fix the stopping time. Classical GD can instead stop once `‖∇f(x_k)‖ ≤ ε`, which needs no `Δ` and has the same worst-case bound. |
| Abbaszadehpeivasti–de Klerk–Zamani, *Optim. Lett.* 16 (2022) 1649–1661, [arXiv:2104.05468](https://arxiv.org/abs/2104.05468), Prop. 3 (step `1/L`: `min_{k≤N+1}‖∇f‖² ≤ 4LΔ/(3N+2)`) and Cor. 1 (step `√(4/3)/L`: `≤ 6√3 LΔ/(8N+3√3)`) | `≈ 4LΔ/(3ε²) + 1` (step `1/L`), `≈ 1.30 LΔ/ε² + 1` (step `√(4/3)/L`) → `max(1, ⌈2LΔ/ε²⌉)` | Worse: about 1.5× (same step) or 1.54× (better step) more calls when `LΔ/ε² ≫ 1` | None. AdKZ state results on `ℝⁿ` with the minimum value `f*`. I did not check line by line whether their PEP proof extends to Hilbert spaces with an unattained infimum. | None | The selected constant is not tight for this method |
| Lower bound: Carmon–Duchi–Hinder–Sidford, [arXiv:1710.11606](https://arxiv.org/abs/1710.11606) (*Math. Program.* 2020), Thms 1–2 (`p = 1`) | Ω(LΔ/ε²) for any deterministic or randomized algorithm in dimension of order `LΔ/ε²` and above → `O(1 + LΔ/ε²)` | None: the rate is order-optimal in high dimension, but the lower bound already certifies classical GD | None | None | In fixed low dimension, dimension-dependent methods can beat this rate; for example, Hollender–Zampetakis (COLT 2023) treat `d = 2`. I did not check those normalizations in detail. |

**Reduction check.** The result is the standard descent-lemma telescoping bound with best-iterate selection; it contains no new mechanism. Its only nonstandard features are the arbitrary Hilbert space and the unattained lower bound. Both are covered verbatim by the textbook proof, which uses only the descent lemma and `f ≥ lower`. There is no meaningful repository overlap: no other theorem in `LongTails/Theorems` targets gradient-norm stationarity for smooth nonconvex `f`.

**Search coverage.** On 2026-10-07 I read the full texts of AdKZ (Thm 2, Prop. 3, Thm 3, Cor. 1) and Carmon et al. v3 (Thms 1–2 and §1). Nesterov's book was not re-opened, so its bound is cited through those two papers. There is no companion note. The theorem was introduced in commit ea894ff (2026-09-21), and every cited baseline predates it.

**Conclusion**

**No: this is the textbook gradient-descent stationarity bound, and its constant is weaker than the best known analysis of the same method.**

For an `L`-smooth function with initial gap `Δ`, the bounds for `min ‖∇f(x_k)‖ ≤ ε` are:

| Method | Gradient calls |
|---|---|
| This result (GD, step 1/L, best iterate) | `max(1, ⌈2LΔ/ε²⌉)` |
| Nesterov 2004, same GD | `≈ 2LΔ/ε²` |
| AdKZ 2022, GD with step `√(4/3)/L` | `≈ 1.30 LΔ/ε² + 1` |

The bound has been classical for about two decades. AdKZ's tight analysis needs about two-thirds as many calls for the same step size, and slightly fewer with a better step. Carmon et al. show that `Ω(LΔ/ε²)` calls are necessary for every first-order method in high dimension, so no rate improvement is possible there.

The setup is not meaningfully broader: Hilbert spaces and unattained infima are handled by the same two-line argument. The output and the required information are no better either; the algorithm even needs `Δ`, which a gradient-norm stopping test avoids. The only contribution that can be claimed is a machine-checked formalization of a known theorem.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
