# RecursiveGradientNonconvex: what is actually new?

[`result`](../../LongTails/Theorems/RecursiveGradientNonconvex.lean) proves the following for every admissible instance of the [setup](../../LongTails/Setups/FiniteSumSmoothNonconvex.lean). Minibatch SARAH/SpiderBoost-type recursive gradient descent ([updates](../../LongTails/Algorithms/RecursiveGradient.lean), [query plan](../../LongTails/Algorithms/RecursiveGradientQueries.lean)) returns a uniformly random pre-update iterate `X` with `E‖∇F(X)‖² ≤ ε²`.

**Setup.** The objective is `F = n⁻¹Σᵢ fᵢ` on any real Hilbert space. Each `fᵢ` is differentiable, and the components satisfy mean-squared smoothness: `n⁻¹Σᵢ‖∇fᵢ(x)−∇fᵢ(y)‖² ≤ L²‖x−y‖²`. The objective is bounded below by some `ℓ`, with `F(x₀)−ℓ ≤ Δ`. The setup assumes neither convexity nor an attained minimum. The oracle returns the exact `∇fᵢ(x)` for each query `(i,x)`.

**Tuning.** The method uses step `η = 1/(2L)`, minibatch size `b = ⌊√n⌋+1`, and `b−1` inner steps per epoch. Minibatches are sampled with replacement. Each epoch starts with a full refresh, and the number of epochs is `S = max{1, ⌈4LΔ/(bε²)⌉}`.

**Complexity.** The method uses a fixed number of component-gradient calls:

> `5n + ⌈20√n·LΔ/ε²⌉ = O(n + √n·LΔ/ε²)`, valid for `n ≥ 1`, `L > 0`, `Δ ≥ 0`, `ε > 0`.

There is no logarithmic factor. Each epoch costs `n + 2b(b−1) ≤ 5n` calls, because every sampled difference requires two calls. Even when `Δ = 0`, the method still spends `5n` calls.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Nguyen et al., *Finite-sum smooth optimization with SARAH*, [arXiv:1901.07648 v2](https://arxiv.org/abs/1901.07648) (Jan/Apr 2019); Comput. Optim. Appl. 82 (2022); Thm 2 + Cor 3 (minibatch SARAH, Assumption 1 = average smoothness) | `b=⌊√n⌋+1`, `m=b−1`. Then `4m(n−b)/(b(n−1)) ≤ 4`, so `η ≤ 2/(L(√5+1))` admits `1/(2L)`. With `S=⌈2Δ/(ηbε²)⌉`, the cost `(n+2bm)S` is `O(n+√n·LΔ/ε²)` → `O(n+√n·LΔ/ε²)` | None: same order | `ℝᵈ` → Hilbert space only. The proof is dimension-free. Smoothness, lower bound, and criterion are the same: their `ε` is the squared accuracy, and `F*` is any lower bound | None: both use the same uniform random iterate and the same required knowledge of `L, Δ, n` | Sampling without replacement → with replacement. Both give variance factor `≤ 1/b`, and the rate is unchanged |
| Wang et al., *SpiderBoost*, NeurIPS 2019, [arXiv:1810.10690 v3](https://arxiv.org/abs/1810.10690), Thm 1 | `O(n+√n·LΔ/ε²)` → same | None: same order | Each `∇fᵢ` `L`-Lipschitz and attained `inf` → mean-square smoothness and any lower bound. Nguyen et al. already cover this relaxation | None: the algorithm is the same (`η=1/(2L)`, `q=|S|=√n`). The theorem states `E‖∇f‖ ≤ ε`, and its appendix proof goes through the squared bound | None beyond the minibatch-sampling detail |
| Li et al., *PAGE*, [ICML 2021](https://proceedings.mlr.press/v139/li21a/li21a.pdf), Thm 1 / Cor 2 (Assumption 2 = average smoothness) | `n + 8LΔ√n/ε²` expected calls, `E‖∇f‖ ≤ ε`. Rescaling `ε` gives `O(n+√n·LΔ/ε²)` → same order for `E‖∇F‖² ≤ ε²` | None: same order | None | Expected call count → deterministic count. SARAH already gives a deterministic count. The first-moment criterion is implied by the squared one (Jensen); PAGE's proof also bounds the squared gradient | Lean result needs fixed epochs, while PAGE uses random refresh |

**Reduction check.** The theorem is Nguyen et al.'s Theorem 2 with `b ≈ m ≈ √n`, in a Hilbert space and with with-replacement minibatches. The [energy proof](../../LongTails/Proofs/RecursiveGradientEnergy.lean) uses the SARAH/SPIDER recursive-error identity and epoch-wise descent telescoping. I found no new mechanism.

**Lower bound and repository context.** PAGE Theorem 2 gives `Ω(n + LΔ√n/ε²)` for linear-span algorithms under average smoothness and the first-moment criterion. Jensen's inequality transfers it to this criterion, so the rate is order-optimal for that class. That optimality was already known. Within the repository, [`GdNonconvex`](../../LongTails/Theorems/GdNonconvex.lean) gives `O(n·LΔ/ε²)` component calls by simulating full gradients. The `√n` gain over it is classical.

**Search coverage.** The search on 2026-10-07 UTC read the theorem statements of Nguyen et al. Thm 1–2/Cor 3–4, SpiderBoost Thm 1/Assumption 1, and PAGE Thm 1/Cor 2/Thm 2. SPIDER (NeurIPS 2018), ProxSARAH and SNVRG were not rechecked; they are older and cannot strengthen any novelty claim. There is no companion note. The result was introduced locally in commit `09c3bf9` (2026-09-23), so all baselines predate it. No build was run.

**Conclusion**

**No: this is a known result, formalized.** The strongest baseline is minibatch SARAH (Nguyen et al. 2019, Thm 2). It uses the same mean-square smoothness, lower-bound gap, uniform random-iterate output, and squared-gradient criterion. With the same `√n` batch and epoch length, it gives exactly the Lean rate:

| | component-gradient calls for `E‖∇F(X)‖² ≤ ε²` |
|---|---|
| SARAH Thm 2 (2019), SpiderBoost (2019), PAGE (2021) | `O(n + √n·LΔ/ε²)` |
| This result | `5n + ⌈20√n·LΔ/ε²⌉` |

This order matches PAGE's lower bound for linear-span methods, so no better rate is possible for that class. The remaining differences are a Hilbert-space setting instead of `ℝᵈ`, with-replacement batches, and explicit constants. None of them adds instances of independent interest or improves any parameter regime.

What can be claimed is a correct, fully call-accounted machine-checked proof of the classical SARAH/SpiderBoost nonconvex finite-sum bound. That is not a new optimization result.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
