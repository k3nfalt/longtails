# HeavyTailedPLLastIterate: plain SGD on smooth PL objectives under finite-moment noise

[`result`](../../LongTails/Theorems/HeavyTailedPLLastIterate.lean) proves the following. Take an L-smooth objective that satisfies the global μ-PL inequality on a Hilbert space, and an i.i.d. unbiased oracle whose variance is at most σ² and whose q-th central moment is at most ν^q for some q > 2, uniformly in x. Then plain SGD with step η_t = 4/(μ(t+t₀)), t₀ = ⌈8L/μ⌉+2, satisfies P{f(x_T) − inf f > ε} ≤ δ at its **last iterate** after the stated number of oracle calls ([setup](../../LongTails/Setups/HeavyTailedPL.lean), [algorithm](../../LongTails/Algorithms/ScheduledSgd.lean)).

`allowedAlgorithm` enforces `ScheduledSgd.method η x0` with positive deterministic steps and last-iterate output, and `Convergence` proves compliance. Because `makeAlgorithm` receives only the public input (E, L, μ, x₀), the Lean statement also enforces that the steps use only L and μ. The run length is exactly `budget` (introduced in commit 869290c, 2026-10-11).

**Complexity** (κ = L/μ; Δ ≥ f(x₀) − inf f; 0 < δ < 1; one oracle call per iteration):

$$T=O\Big(\kappa\sqrt{\Delta/\varepsilon}+\frac{\sigma^2(\kappa+\log(1/\delta))}{\mu\varepsilon}+\Big(\frac{\kappa^2\nu^2\log(1/\delta)}{\sigma^2}\Big)^{\frac{q}{q-2}}\delta^{-\frac{2}{q-2}}\Big).$$

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Sadiev et al., ICML 2023, [arXiv 2302.00999v2](https://arxiv.org/abs/2302.00999), Thm 3.1 Case 2 / Thm E.4: clipped-SGD, PL, α = 2 (**direct competitor**: its assumptions are implied by this setup) | O(κ log(K/δ) log(Δ/ε) + κσ² log(K/δ) log²(B_K)/(με)), where K is the iteration count and B_K grows polynomially in K → the bound above | Polylogarithmic in the noise-dominated regime ε ≲ σ⁴/(μ²Δ), once the burn-in is also below κσ²/(με). Example: with κ, δ, q, ν/σ fixed and ε → 0, the gain factor is ≍ log³(1/ε). **Worse** for ε ≫ σ⁴/(μ²Δ), since √(Δ/ε) replaces log(Δ/ε), and when the δ^{-2/(q-2)} burn-in dominates. | None. Clipping needs only finite variance (and α ∈ (1,2]) on a level-set neighbourhood. | Step and clipping level need Δ, σ, K, δ → step needs only L and μ and does not depend on the horizon. Stopping still needs σ, ν, q, Δ, ε, δ. Same last-iterate output. | Extra uniform q > 2 moment; assumptions are global rather than local; does not cover α < 2. |
| Madden–Dall'Anese–Becker, [JMLR 25 (2024)](https://www.jmlr.org/papers/v25/23-0466.html), Thm 8: plain SGD, PL, step depends on L and μ (**special case**: conditionally norm-sub-Gaussian noise) | O(κσ² log(1/δ)/(με)), initial-gap term suppressed in their O → on that overlap with q = 2+2log(3/δ) and ν ≲ σ√q: O(κ√(Δ/ε) + σ²(κ+log(1/δ))/(με) + κ^{2+2/log(3/δ)} log²(1/δ)) | Noise term: κ·log(1/δ) → κ + log(1/δ), a factor of order min(κ, log(1/δ)). Holds when ε ≲ min{σ²/(μκ^{1+2/log(3/δ)} log(1/δ)), σ⁴log²(1/δ)/(μ²Δ)}. | Norm-sub-Gaussian noise → finite variance plus one finite q-th moment (q > 2), e.g. Student-t noise. | None: same L, μ-only step and same last iterate. | Requires an i.i.d. oracle with moments uniform in x (Madden allows adapted martingale noise); adds a burn-in. |
| Tong–Ikeda–Kawasumi, [arXiv 2609.32195v1](https://arxiv.org/abs/2609.32195) (26 Sep 2026, unreviewed, about two weeks earlier), Thm 3.7: same plain SGD and step | (1/ε)·exp(2 log^{1/β}(T/δ))·√(log T·log(e/δ)), with constants depending on the trajectory cap G and the Orlicz scale (not explicit) → the bound above | Not comparable in full, because the constants are not explicit. In ε and δ with other parameters fixed on the overlap, the super-polylogarithmic factor exp(2 log^{1/β}(1/(εδ))) disappears. | Removes the trajectory cap η_t‖∇f(x_t)‖ ≤ G and the finite-dataset restriction. β-Orlicz noise (all moments finite) → a single q > 2 moment. The classes are **incomparable**, because the moments here are uniform in x rather than conditional along the trajectory. | None | Uniform-in-x moments exclude finite sums with heterogeneous curvature. The burn-in is polynomial in 1/δ. |

**Reductions and mechanism.**
- The standard reductions are weaker. Markov's inequality applied to the in-expectation PL-SGD bound gives O((κ√(Δ/ε) + κσ²/(με))/δ). Truncating at ν(T/δ)^{1/q} and then running a light-tailed analysis leaves a (T/δ)^{2/q} factor on the leading term.
- The new step is a single exponential supermartingale over the truncated noise. A localization stopped at the first time the Bernstein range condition fails, together with a pathwise first-bad-time argument, pushes the entire heavy-tail cost into an ε-independent burn-in. The ingredients are familiar (Fuk–Nagaev truncation, Freedman/Bernstein bounds, the stopping arguments of Sadiev et al.), but I found no derivation of this bound from them.
- Sadiev et al., Thm 2.1, shows that constant-step SGD under finite variance alone cannot achieve log(1/δ) dependence. That motivates the q > 2 assumption, but does not by itself prove it is necessary for the 1/t schedule.

**Search coverage (2026-10-12).** Sources read in full or at the theorem level:
- arXiv, PMLR, JMLR: Sadiev v2, Madden et al., Tong et al. Thm 3.7, and Lou–Zhu–Wu (JMLR 23, 2022, Thm 2; averaged SGD for linear regression with dimension-dependent mini-batches, a special case only).

Sources checked from abstracts only:
- Wu, arXiv 2609.30499v2 (average-gradient stationarity, no PL result).
- Ou–Wang, arXiv 2609.03990v2. Its claimed matching PL lower bound is unverified, so no optimality is claimed here.
- Suvorikova et al., arXiv 2609.32962 (averaged SGD).
- Sarkar et al., arXiv 2606.26316 (Markov chain noise, clipped methods for heavy tails).
- Yamada et al., UAI 2026 (in-expectation bounds only).

Not checked: Li–Liu (ICML 2022, sub-Weibull PL), in full. The repository has no other stochastic PL result. The companion note matches the Lean statement, except that the theorem fixes the run length at exactly `budget` rather than at any K ≥ budget.

## Conclusion

**The result covers more noise for plain SGD, but it does not establish a meaningfully better complexity for the problem class.**

The strongest baseline is clipped-SGD (Sadiev et al., ICML 2023). It already reaches log(1/δ) confidence on the same class using finite variance alone, with a logarithmic initialization cost:

| | total oracle calls |
|---|---|
| clipped-SGD | κ log(K/δ) log(Δ/ε) + κσ² log(K/δ) log²K/(με) |
| this result | κ√(Δ/ε) + σ²(κ+log(1/δ))/(με) + burn-in(κ, ν/σ, q, δ) |

Here burn-in(κ, ν/σ, q, δ) = (κ²ν² log(1/δ)/σ²)^{q/(q−2)} δ^{−2/(q−2)}, the last term of the formula above. The selected result wins only by polylogarithmic factors, and only when the noise term dominates: ε ≲ σ⁴/(μ²Δ) and the burn-in is small. It loses for moderate ε and for small δ when q is close to 2, and it needs an extra q > 2 moment.

What is new is the method-specific guarantee. Previous high-probability last-iterate bounds for unclipped SGD on PL objectives required sub-Gaussian noise (Madden et al.) or Orlicz tails plus a trajectory cap (Tong et al.). This result needs one q > 2 moment, uses a step that depends only on L and μ, and improves Madden's κ·log(1/δ) to κ + log(1/δ). My search found no earlier result of this kind for plain SGD, but that does not prove priority.

The claimable contribution is a high-probability last-iterate guarantee for parameter-light plain SGD under polynomial-tailed noise, not a better rate for smooth PL optimization.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
