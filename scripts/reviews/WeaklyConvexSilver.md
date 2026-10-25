# Novelty assessment: long-step silver GD on smooth weakly convex functions

[`WeaklyConvexSilver.lean`](../../LongTails/Theorems/WeaklyConvexSilver.lean) proves the following. Let `f` on a real Hilbert space have an `L`-Lipschitz gradient, let `f + (ρ/2)‖·‖²` be convex, and let `f(x₀) − inf f ≤ Δ`. Then gradient descent with a predetermined, periodically repeated silver block of steps ([algorithm](../../LongTails/Algorithms/WeaklyConvexSilver.lean)) returns its best-gradient queried iterate with `‖∇f‖² ≤ ε²`. The setup is [`SmoothWeaklyConvex.lean`](../../LongTails/Setups/SmoothWeaklyConvex.lean). Its `gdFamily` restriction enforces positive predetermined GD steps and best-gradient output, and compliance is proved.

**Complexity** (exact gradient calls; `L` = smoothness, `ρ` = weak-convexity modulus, `Δ` = initial gap, `ε` = gradient-norm target). The proved budget is `⌈32L(ρ/L)^{3/20}Δ/ε²⌉ + ⌈13(LΔ/ε²)^{4/5}⌉ + 3`, that is,

`N = O(1 + L^{17/20} ρ^{3/20} Δ/ε² + (LΔ/ε²)^{4/5})`.

This holds for `L, ε > 0` and `ρ, Δ ≥ 0`. When `ρ > L`, the first term exceeds the plain-GD bound. The theorem does not replace `ρ` by `min(ρ, L)`, even though `L`-smoothness already implies `L`-weak convexity.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Constant-step GD with `h = 1/L`, by the descent lemma (Nesterov, *Introductory Lectures*, Thm 2.1.5). Rotaru–Glineur–Patrinos [2406.17506](https://arxiv.org/abs/2406.17506) (v2, Jan 2026) give exact constant-step rates on this hypoconvex class. | `⌈2LΔ/ε²⌉` → `O(1 + L^{17/20}ρ^{3/20}Δ/ε² + (LΔ/ε²)^{4/5})` | Speedup factor `min((L/ρ)^{3/20}, (LΔ/ε²)^{1/5})`, i.e. polynomial in `L/ρ`. With the proved constants, the budget is below `2LΔ/ε²` only if `ρ/L ≲ 10⁻⁸` and `LΔ/ε² ≳ 4·10⁵` (from `32(ρ/L)^{0.15} < 2` and `13T^{0.8} < T`). | None (same class) | None (both use best-iterate output and know `L`) | Needs `ρ` and the horizon `LΔ/ε²` to choose the schedule. Worse than plain GD when `ρ/L ≳ 10⁻⁸`. |
| Carmon–Duchi–Hinder–Sidford, Almost-convex-AGD, [1611.00756](https://arxiv.org/abs/1611.00756) Lemma 3.1 (SIOPT 2018) | `O((√(Lρ)Δ/ε² + √(LΔ)/ε)·log(2 + LΔ/ε²))` → `O(1 + L^{17/20}ρ^{3/20}Δ/ε² + (LΔ/ε²)^{4/5})` | **Worse** for `LΔ/ε²` large, whenever `ρ ≤ L`. Ratio of first terms: `(L/ρ)^{7/20}/log(…)`. Ratio of second terms: `(LΔ/ε²)^{3/10}/log`. | None | Theirs stops on a computed gradient-norm check and outputs the point that passed it. This result runs a fixed budget and outputs the best queried iterate. | Theirs uses momentum and proximal subproblems, so it lies outside the GD family. The bound is stated in `ℝᵈ`; it is dimension-free, but the Hilbert-space transfer was not checked. |
| Grimmer–Shu–Wang [2403.14045](https://arxiv.org/abs/2403.14045) Thm 1 (v4, Apr 2024; arXiv only). Special case `ρ = 0`, convex with a minimizer. | `O((LΔ/ε²)^{log_{1+√2} 2}) = O((LΔ/ε²)^{0.7864})` → `O(1 + (LΔ/ε²)^{4/5})` | **Worse** by `(LΔ/ε²)^{0.0136}` | Convex with a minimizer → `ρ`-weakly convex and bounded below | Theirs is a **last-iterate** guarantee; this result is best-iterate. | None beyond the output change |

**Standard-reduction check.** I found no reduction that yields long-step GD rates for `ρ > 0`. The obvious route, a uniform defect bound over the block, gives only exponent ≈0.098 according to the companion note; I did not verify this. The new mechanism is the virtual-anchor/scale-decay induction, certified by SOS ([`WeaklyConvexSilverCertificate.lean`](../../LongTails/Proofs/WeaklyConvexSilverCertificate.lean)). Proof ancestry is the recursive silver certificate of Altschuler–Parrilo ([2309.07879](https://arxiv.org/abs/2309.07879)), which covers only the convex case.

**Search coverage.** On 2026-10-25 I searched arXiv and the web for long-step, silver and hypoconvex GD, including the 2026 silver-optimality papers [2609.09152](https://arxiv.org/abs/2609.09152) and [2605.31386](https://arxiv.org/abs/2605.31386). Both concern only the convex case. Altschuler–Parrilo and Grimmer–Shu–Wang ([2309.09961](https://arxiv.org/abs/2309.09961)) explicitly leave nonconvex long steps open. I did not read Rotaru–Glineur–Patrinos's full theorems, and conference or journal versions were not checked. The result was introduced in commit `427a361` (2026-10-25). The companion note agrees with the Lean statement and correctly concedes that acceleration is better for the class.

## Conclusion

**No improvement for the problem class; the possible novelty is the first long-step analysis showing that plain GD can beat its `LΔ/ε²` rate on weakly convex functions.**

The strongest applicable baseline is Carmon et al.'s Almost-convex-AGD, which uses the same gradient oracle and the same `‖∇f‖ ≤ ε` target:

| | Gradient calls |
|---|---|
| Almost-convex-AGD | `(√(Lρ)Δ/ε² + √(LΔ)/ε)·log(LΔ/ε²)` |
| This result | `L^{17/20}ρ^{3/20}Δ/ε² + (LΔ/ε²)^{4/5}` |

For `ρ ≤ L` and large `LΔ/ε²`, acceleration wins both terms by polynomial factors. At `ρ = 0`, Grimmer–Shu–Wang's long-step schedule is slightly faster (exponent 0.786 vs 0.8) and gives a last-iterate guarantee.

Within GD with predetermined steps, the comparison does show a gain over constant steps by the factor `min((L/ρ)^{3/20}, (LΔ/ε²)^{1/5})`. With the proved constants, however, the gain appears only once `ρ/L ≲ 10⁻⁸`. The exponent 3/20 is far from AGD's 1/2, so this is not a case of "GD is almost as fast as AGD".

My search found no prior long-step result for `ρ > 0`, and two papers name the question as open. Absence of a hit does not establish priority. The defensible claim is a new method-specific analysis: a polynomial-in-`L/ρ` speedup of predetermined-step GD on smooth weakly convex functions. It is not an improved optimization guarantee.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
