# BallProximalGaussian: novelty assessment

[`result`](../../LongTails/Theorems/BallProximalGaussian.lean) shows the following. Take any proper closed convex objective on a finite-dimensional inner-product space with an attained minimizer, where `‖x₀−x⋆‖ ≤ R` and `f(x₀)−f⋆ ≤ Δ`. The fixed-radius exact ball-proximal point method ([setup](../../LongTails/Setups/ConvexBallProximal.lean), [algorithm](../../LongTails/Algorithms/BallProximal.lean)) returns a feasible last iterate with `f(x_K)−f⋆ ≤ ε` for every oracle tie-breaking choice, after

$$K=\Big\lceil \min\Big\{\tfrac{R^2}{t^2},\ \tfrac{R}{t}\sqrt{\tfrac12\max\{0,\log(\Delta/\varepsilon)\}}\Big\}\Big\rceil$$

exact ball-oracle calls. Here `t` is the ball radius, `R` bounds the initial distance, `Δ` bounds the initial gap, and `ε` is the target accuracy. Each call returns only a minimizer of `f` over `C ∩ B(x,t)`. The proof rests on [`execution_gaussian`](../../LongTails/Proofs/BallProximalGaussian.lean), which gives `f(x_K)−f⋆ ≤ Δ·exp(−2K²t²/R²)`. `allowedAlgorithm` fixes the update and last-iterate output, and compliance is proved by `rfl`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Richtárik–Li, [arXiv:2609.35147v1](https://arxiv.org/abs/2609.35147v1) (28 Sep 2026, preprint), Thm 3.4, eqs. (42)–(43); same BPM, same Assumptions 1–3 | `min{⌈R²/t²⌉, ⌈(R/t)√(½log(Δ/ε))⌉}` → the same `K` (the ceiling commutes with the minimum) | None: identical budget | None. Lean's supplied bounds `R, Δ` instead of `D₀, Δ₀`, and its `ε ≥ Δ` and `R = 0` edge cases, are trivial extensions | None: both are last-iterate, with updates free of `R, Δ, ε` | Weaker than the same theorem's rational factor `((S−K)/(S+K))^K` in (42), with `S = R²/t²`; Remark 3.5 and Thm 4.5's `O_d(1+R/t)` termination (statement read only via the paper's summary) are stronger still |
| Gruntkowska–Li–Rane–Richtárik, [arXiv:2502.02002v2](https://arxiv.org/abs/2502.02002v2) (preprint), Thm 8.1 (finite termination), Cor. 8.2 (`Δ₀(1+t/D₀)^{−K}`) | `O(min{R²/t², (1+R/t)log(Δ/ε)})` → `O(min{R²/t², (R/t)√log(Δ/ε)})` | Factor `≈√(2 log(Δ/ε))` when `log(Δ/ε) < 2R²/t²` and `R ≥ t`; this gain belongs to Richtárik–Li, not to this result | None | None | None beyond the first row |
| Repository: [`BallProximalSharpProfile`](../../LongTails/Theorems/BallProximalSharpProfile.lean) (committed 14 Oct 2026) | `⌈min{R²/t², (R/t)√(min{½, 1−ε/Δ}²_+ + ½log₊(Δ/2ε))}⌉` → `K` | Worse: the sibling's coefficient is pointwise no larger (`¼+½log(1/2r) < ½log(1/r)` and `(1−r)² ≤ ½log(1/r)` for `r ≥ ½`, where `r = ε/Δ`) | None | None | Same spec; the selected result is strictly dominated |

**Reduction check.** No reduction is needed: the result *is* the published Theorem 3.4 Gaussian relaxation. The Lean proof derives it from the library's existing radial-certificate and logarithmic-profile lemmas rather than from the paper's Jensen step, so it adds no new mathematical mechanism. The proof ancestry is GLRR's separation/contraction argument plus the profile energy used by the sibling result.

**Search coverage (20 Oct 2026).** I checked the arXiv abstract and HTML of 2609.35147v1, which is the only version; its Theorem 3.4, Assumptions 1–3 and Remark 3.5 match the Lean statement. I also read GLRR v2's Section 8 from the PDF text. I did not read Theorem 4.5's full statement, which was beyond the retrieved text. The companion note says this is a reproduction claiming no novelty, and that is accurate. Chronology: the paper (28 Sep 2026) predates the commit introducing this theorem (`9df494c`, 20 Oct 2026).

**Conclusion**

**No, this is a formal reproduction of an already-published bound, not a new result.** The strongest baseline is Richtárik–Li (arXiv:2609.35147v1), Theorem 3.4. It states exactly the same guarantee for the same method, function class, oracle and output:

$$\text{Richtárik–Li (43)}:\ \min\{\lceil R^2/t^2\rceil,\lceil (R/t)\sqrt{\tfrac12\log(\Delta/\varepsilon)}\rceil\}\quad=\quad\text{this result's }K.$$

The improvement over the original BPM analysis (Gruntkowska et al., Corollary 8.2: about `(R/t)·log(Δ/ε)` calls) is a `√log(Δ/ε)` factor. That improvement is due to the earlier paper, not to this theorem.

The result also has no present-day advantage in any regime. The same paper's rational factor is sharper. The repository's own `BallProximalSharpProfile` budget, introduced six days earlier on the same setup, is pointwise no larger for every `ε/Δ`. The only additions are trivial extensions to `ε ≥ Δ` and `R = 0`, plus a Lean formalization with arbitrary tie-breaking. These do not count as mathematical novelty.

What can be claimed is a machine-checked reproduction of Richtárik–Li's Gaussian objective-gap bound and its call budget.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
