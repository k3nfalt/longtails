# Novelty assessment: ConstrainedMinimaxCubic

[`ConstrainedMinimaxCubic.result`](../../LongTails/Theorems/ConstrainedMinimaxCubic.lean) concerns `min_x max_{y∈Y} f(x,y)`, where `Y` is a known closed convex (possibly unbounded) set and the exact oracle returns value, gradient and full Hessian. It proves that the deterministic method in [`ConstrainedSaddleCubic`](../../LongTails/Algorithms/ConstrainedSaddleCubic.lean) returns `x̂` with `‖∇Φ(x̂)‖ ≤ ε` for `Φ(x)=max_{y∈Y} f(x,y)`. The guarantee holds for every seed, under the assumptions of [`ConstrainedMinimaxSecondOrder.spec`](../../LongTails/Setups/ConstrainedMinimaxSecondOrder.lean):
- `∇f` is `L`-Lipschitz and `∇²f` is `ρ`-Lipschitz on all of `E×F`;
- `f(x,·)` is `μ`-strongly concave on all of `F`;
- `Φ(x₀)−inf Φ ≤ Δ` and `‖∇f(x₀,y₀)‖ ≤ B`, with `y₀ ∈ Y`.

**Proved budget, simplified.** Constants are suppressed; the formula was derived from the Lean `budget`. All calls are counted.

`O( (L/μ)·log(1+ρB/μ²) + [1 + Δ√ρ L^{3/4} μ^{−3/4} ε^{−3/2} + ρ√L Δ μ^{−3/2} ε^{−1} + √(ρε)/μ] · log(33+Lμ/(ρε)) )`

The two middle terms are compared through `r := ρ L^{3/2} ε /(μ^{3/2} L²) = ρε/(√L μ^{3/2})`:
- the third term equals the second times `√r`;
- the second term leads iff `r ≤ 1`, i.e. `ε ≤ √L μ^{3/2}/ρ`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Lin–Jin–Jordan, [COLT 2020](https://proceedings.mlr.press/v125/lin20a.html), Thm 20 (Minimax-PPA, NC-SC). Prior. **Restriction:** `Y` bounded with diameter `D_y`; gradient-only. | `O(√(L/μ)·LΔε^{−2}·log²(L²(D̃ₓ²+D_y²)/(με²)))` gradient calls → the formula above. Our oracle can run their method by ignoring Hessians. | When `r<1` (`ε < √L μ^{3/2}/ρ`), the leading term shrinks by the factor `√r = √(ρε) μ^{−3/4} L^{−1/4}`: the accuracy exponent goes from `ε^{−2}` to `ε^{−3/2}`. For `r>1` our tracking term `ρ√LΔμ^{−3/2}ε^{−1}` is worse. | Bounded `Y` → any closed convex `Y`. | Success probability 2/3 → deterministic, every seed. | Needs a `ρ`-Lipschitz joint Hessian on the ambient space, full-Hessian replies, and `B`. Initialization costs `(L/μ)log(1+ρB/μ²)`. |
| Zhang et al., [arXiv:2610.16771v2](https://arxiv.org/abs/2610.16771) (v1 12 Oct 2026, v2 19 Oct 2026), Thm 4.1. Prior; an unreviewed auto-research preprint not intended for publication. **Restriction:** `Y = ℝ^{d_y}`. | `Õ(I₀ + min{A(1+r^{1/7}), A₁(1+r^{2/7}), √(L/μ)A₁})`, with `A = Δ√ρ L^{3/4}μ^{−3/4}ε^{−3/2}`, `A₁ = LΔε^{−2}`, `I₀ = Õ(1+min{√(L/μ), (ρD_{y,0}/μ)^{2/7}})` → ours. | None on the overlap `Y=F` when `r ≤ 1`: same order `A`. Worse for `r>1`, where ours is `A√r` against their `≤ A₁ min{r^{2/7}, √(L/μ)}`. Worse initialization: `L/μ` against `≤ √(L/μ)`. | Unconstrained `y` → closed convex `Y`. The new instances are those whose dual constraints become active or change. | None. | Same oracle. Ours is weaker outside the high-accuracy regime and has no regime-adaptive branches. |
| Zhou–Chen–Luo–Liu, [arXiv:2610.20345v1](https://arxiv.org/abs/2610.20345) (14 Oct 2026), ECRN, Thm 11. Prior. **Restriction:** `Y = ℝ^{d_y}`. | `Õ(Δ√ρ L^{3/4}μ^{−3/4}ε^{−3/2})` second-order calls for an `(ε, √(ρ(4+L/μ)^{3/2}ε))`-SOSP, when `ε ≤ L²/(ρ(4+L/μ)^{3/2})` → ours (first order only). | None: same leading order on `Y=F`. | Unconstrained → closed convex `Y`. | Worse: second-order stationarity → first-order only. | Weaker output criterion. |

The repository's [EnvelopeCubicNonconvexPL](../../LongTails/Theorems/EnvelopeCubicNonconvexPL.lean) has an unconstrained PL inner problem. Its instance class is incomparable to this one.

**Reduction check.** With `Y=F`, the result is the unconstrained envelope-cubic rate; the envelope Hessian constant `R = ρ(4+L/μ)^{3/2}` is ECRN's Lemma 5. For constrained `Y`, the standard routes don't go through directly:
- An indicator penalty is nonsmooth.
- A squared-distance penalty is `C^{1,1}` but has no Lipschitz Hessian.
- ECRN's argument differentiates the saddle map via the implicit function theorem (Lemma 4, Prop. 3). That map is not differentiable when active sets change.

The new mechanism is the value and gradient model-error bounds for the finite-jet constrained saddle model ([ConstrainedSaddleModel](../../LongTails/Proofs/ConstrainedSaddleModel.lean), [ConstrainedSaddlePerturbation](../../LongTails/Proofs/ConstrainedSaddlePerturbation.lean)), which avoid second derivatives of the envelope. Proof ancestry, which supplies techniques but not the complexity:
- Nesterov–Polyak cubic descent;
- inexact-model frameworks (Nabou–Necoara, arXiv:2203.13367);
- projected extragradient;
- Newton corrections for affine variational inequalities.

**Scope caveat.** Regularity is imposed on all of `F`, which excludes plain DRO couplings such as `Σ yᵢℓᵢ(x)`: their `x`-gradient Lipschitz constant grows with `‖y‖`. Such couplings fit only after replacing `yᵢ` by a bounded smooth extension equal to `yᵢ` on `Y`, which requires bounded losses with bounded derivatives. The companion's `tanh` example does satisfy every assumption and has an active constraint for sufficiently negative `x₁`.

**Search coverage.** The search ran on 6 Nov 2026 UTC over arXiv, COLT, ICML, NeurIPS and ICLR on second-order and gradient-only NC-SC methods.
- I read the relevant statements of LJJ Thm 20 (PDF), 2610.16771v2 §3–§5, 2610.20345 (§§1–3 verbatim, Thm 11 and Thm 18 from a partial read) and 2606.07003.
- 2606.07003 (single-loop Newton) is unconstrained and certifies an SOSP of a penalty function, not `‖∇Φ‖`.
- I did not check whether MCN (arXiv:2110.04814), arXiv:2411.15769 or arXiv:2602.14058 handle constrained `Y`; from their abstracts they target unconstrained SOSP.
- I did not verify the lower-bound proofs.
- No gradient-only baseline for *unbounded* constrained `Y` was checked.
- The companion note's citations and claims agree with what I checked, including its statements of what it does not claim.
- The result was committed on 6 Nov 2026, after both October preprints.

**Conclusion**

**The rate is not new; the contribution is extending it to constrained dual variables.** Two October 2026 preprints already prove the high-accuracy full-Hessian bound for unconstrained `y`: Zhang et al. (first-order stationarity) and Zhou–Chen–Luo–Liu (second-order stationarity). This theorem proves the same leading bound when `y` ranges over any closed convex `Y`, a case where their implicit-function-theorem analysis fails once active constraints change.

The decisive comparison is with the only checked end-to-end constrained baseline, Lin–Jin–Jordan's gradient-only method for bounded `Y`. Writing `r = ρε/(√L μ^{3/2})`:

| | leading cost |
|---|---|
| Lin–Jin–Jordan (bounded `Y`, gradients) | `√(L/μ)·LΔ/ε²` |
| this result (closed convex `Y`, Hessians) | `Δ√ρ L^{3/4}μ^{−3/4}/ε^{3/2}` |

This result is cheaper by the factor `√r` when `ε < √L μ^{3/2}/ρ`. It loses when `r > 1`, has worse initialization than accelerated startup, and uses stronger regularity and oracle access.

That comparison proves a gain. Priority is less certain: the search found no constrained second-order result, but several second-order NC-SC papers were checked only through their abstracts, and the lower bound that would make the rate near-optimal is reported, not verified. Ambient-space smoothness also limits which constrained applications fit without modification.

The claimable contribution is the high-accuracy `Δ√ρ(L/μ)^{3/4}ε^{−3/2}` full-Hessian guarantee for nonconvex–strongly-concave problems with closed convex dual constraints, which needs a new model-error argument.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
