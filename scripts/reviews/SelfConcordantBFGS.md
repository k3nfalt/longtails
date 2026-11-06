# BFGS with weak Wolfe steps on standard self-concordant functions

[`result`](../../LongTails/Theorems/SelfConcordantBFGS.lean) shows that the last iterate of unmodified BFGS (`allowedAlgorithm` forces `bfgs x0 B0`, output `x_T`) satisfies `f(x_T) − f⋆ ≤ ε` deterministically. This holds for every standard self-concordant `f` on an open convex domain `D ⊆ ℝ^d`, with positive-definite Hessian, closed sublevel sets and a minimizer in `D`, and for every adversarial weak-Wolfe step oracle with `0 < c1 < c2 < 1`. Setup: [`SelfConcordantBFGS`](../../LongTails/Setups/SelfConcordantBFGS.lean). Algorithm: [`method`](../../LongTails/Algorithms/SelfConcordantBFGS.lean).

**Proved budget.** The parameters are:

- `Δ ≥ f(x0) − f⋆`, the initial objective gap;
- `Φ0 ≥ Σᵢ log((1+λᵢ)²/(4λᵢ))`, where `λᵢ` are the eigenvalues of `∇²f(x0)⁻¹B0`;
- `d`, the dimension;
- `c1, c2`, the Wolfe parameters;
- `ε`, the target accuracy.

The number of Wolfe-oracle calls is `⌈N⌉+2`, so

```
O( (1+d)(1+Δ)[(1+Δ)/(c1³ min(c1,1−c2)²) + (1+d)/(c1 min(c1,1−c2)⁴)] + Φ0/min(c1,1−c2)² + log(2+1/ε)/min(c1,1−c2) ).
```

For fixed `c1, c2` this is `O(Φ0 + log(2+1/ε) + d(1+Δ)² + d²(1+Δ))`. Each call returns a Wolfe step and the gradient there. The cost of finding the step inside the line search is **not** counted.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Jin–Mokhtari, [arXiv 2507.00361v2](https://arxiv.org/abs/2507.00361) (Oct 2025; [NeurIPS 2025](https://neurips.cc/virtual/2025/poster/117030)), Thm 3.3/4.3, App. D eqs. (92)–(94). **Applies only to strongly self-concordant `f` on all of ℝ^d.** On that overlap, rescale `f` by `M²/4` so `Δ = M²(f(x0)−f⋆)/4` and `D0 = 2ω⁻¹(Δ) ≍ Δ+√Δ`. | Minimum of (92)–(94); the burn-in (93) is `O(Ψ(B̃0) + (Ψ(B̄0)+(1+Δ)²)Δ + log 1/ε)`, followed by a superlinear phase (94). Here `Ψ(A)=tr A−d−log det A` is measured at `x⋆`. → `O(Φ0 + log(1/ε) + d(1+Δ)² + d²(1+Δ))` | Regime gains in proved upper bounds. (i) Take `B0 ≈ ∇²f(x⋆)`, `Δ ≥ 1`, `log(1/ε) ≲ dΔ²`: `Θ(Δ³)` → `O(dΔ²)`, a factor `Δ/d` when `d ≪ Δ`. (ii) Take `B0 = a∇²f(x⋆)`, `a ≫ 1`: the `Ψ(B̃0) + Ψ(B̄0)D0 ≈ da` terms become `d log a`. **Worse** when `d ≳ Δ` (extra `d²(1+Δ)`, even at `Δ→0`) and for tiny `ε`, since this result has no superlinear phase. | Strongly self-concordant on ℝ^d → standard self-concordant on an open convex `D` with closed sublevel sets. Newly covered examples: `cᵀx − Σ log(bᵢ−aᵢᵀx)` on bounded full-dimensional polytopes, and `−log det`. | None. Both give a last-iterate gap and both need `Δ` and the mismatch bound only for stopping. | Line search: Jin–Mokhtari bound bisection evaluations per iteration (Prop. 5.1); here they are uncounted. Jin–Mokhtari require `c1 < 1/2`; here any `c1 < c2` is allowed. The constants are huge: `2²¹/c1³`. There is no superlinear phase. |
| Jin–Jiang–Mokhtari, [arXiv 2404.16731](https://arxiv.org/abs/2404.16731), NeurIPS 2024. **Applies only to μ-strongly convex, L-smooth `f`.** | Linear rate `(1−1/κ)^t`, then κ-free phases → κ-free, affine-invariant bound | Not comparable in general: their bounds involve `κ`, ours do not. This row is subsumed by row 1 on its overlap. | Strongly convex, smooth → standard self-concordant (overlap needs a Lipschitz Hessian) | None | Same caveats as row 1 |

**Standard-reduction check.** Jin–Mokhtari's proof cannot simply be reparametrized. Their analysis uses strong self-concordance on ℝ^d, `∇²f(x)−∇²f(y) ⪯ M‖x−y‖_z∇²f(y)` for all `x,y,z`. Log barriers on bounded domains violate this, and the authors list the standard case as open (§7: "extending results to standard self-concordance is a potential future direction").

The proof here uses a new symmetric log-det potential `kΦ(B;Q) + log gᵀ(B+Q)⁻¹g`. Each BFGS step changes it by an exact scalar factor, and it is combined with a self-concordance calculus along Wolfe segments that needs no global constants. My search did not find this potential in prior work.

Proof ancestry: Byrd–Nocedal (1989) self-correction and the trace–log-det potentials used by Rodomanov–Nesterov and Jin–Mokhtari motivate the mechanism, but they do not give this bound.

Problem-class context: damped Newton needs `O(Δ + log log 1/ε)` steps, but it uses Hessians, so it is a different oracle. I did not verify any gradient- or Wolfe-only problem-class method on this class.

**Search coverage (2026-11-06).** I searched arXiv, NeurIPS/OpenReview and the web for BFGS and quasi-Newton methods under (strong or standard) self-concordance. I also checked Gao–Goldfarb ([arXiv 1612.06965](https://arxiv.org/abs/1612.06965)), which proves only asymptotic convergence for BFGS with adaptive steps and assumes a bounded Hessian, and Yu–Gao–Luo ([arXiv 2509.22508](https://arxiv.org/abs/2509.22508)), which assumes strong convexity.

- OpenReview was blocked.
- I did not check Rodomanov's [arXiv 2404.15051](https://arxiv.org/abs/2404.15051) statements.
- I found no later work treating the standard self-concordant case.

The result was added in commit `18fc61a8` (2026-11-06). The companion note's citations and its "Thm 3.3/eq. (93)" reading match the paper, and its NeurIPS 2025 status is confirmed. Its claim that the competing transient is "dimension-free" is loose, because `d` enters through `Ψ`.

## Conclusion

**Yes: this proves the first explicit global bound for standard Wolfe-BFGS beyond strong self-concordance, which covers barrier functions.**

The strongest baseline is Jin–Mokhtari (NeurIPS 2025). Their result requires strong self-concordance on all of ℝ^d, which excludes log barriers of bounded polytopes and similar interior-point objectives. Those objectives satisfy every hypothesis here. Jin–Mokhtari name this extension as open.

On their class, the proved burn-in bounds compare as follows (for `B0 ≈ ∇²f(x⋆)`, fixed `c1, c2`):

| | burn-in iterations |
|---|---|
| Jin–Mokhtari | `O(Δ³ + log 1/ε)`, then superlinear |
| this result | `O(dΔ² + d²Δ + log 1/ε)` |

The new bound is better when `d ≪ Δ` or when `B0` is badly mis-scaled (the mismatch cost drops from linear to logarithmic). It is worse when `d ≳ Δ`, at high accuracy (no superlinear phase), in its constants, and in leaving line-search work uncounted.

This is a method-specific analysis of BFGS, a very popular algorithm, and the setup really enforces that algorithm. It is not a problem-class improvement: damped Newton, using Hessians, is faster. The literature search found no prior or later standard-self-concordance BFGS bound, but that cannot establish priority conclusively.

What can be claimed: an affine-invariant, condition-number-free global last-iterate bound for unmodified Wolfe-BFGS on standard self-concordant functions (including barriers), which settles a stated open direction. There are also regime-specific gains on the strongly self-concordant overlap.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
