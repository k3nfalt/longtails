# Novelty assessment: WarmHalvingBroxGeneralNorm

[`result`](../../LongTails/Theorems/WarmHalvingBroxGeneralNorm.lean) proves a deterministic guarantee for warm-started radius halving ([algorithm](../../LongTails/Algorithms/WarmHalvingBrox.lean)), which is given only `L`, `r`, and `x0`. Setting:

- an arbitrary finite-dimensional normed space;
- a closed convex set `C`;
- `f` with an `L`-Lipschitz gradient in the dual norm on `C`, bounded below;
- the normal-cone PL inequality `μ(f(x)−f⋆) ≤ s(x)²/2` on all of `C` ([setup](../../LongTails/Setups/BroxGeneralNormConstrainedPL.lean)).

The returned current center `x` lies in `C` and satisfies `f(x) − inf_C f ≤ ε` within the stated per-oracle budget. The two oracles are exact gradients and an exact LMO over `C ∩ ball(x, ρ)` with adversarial tie-breaking.

**Complexity (gradient + local-LMO calls).** Valid parameters are `L, μ, ε, r > 0`. Here `Δ ≥ f(x0) − f⋆`, `r` is the initial radius cap, and `log⁺ = max(log, 0)`. The algorithm does not know `μ`, `Δ`, or `ε`.

```text
N = O( log(1 + Δ/(L r²)) + log⁺(Δ/ε) / log(1 + μ/L) + log⁺( r² L (1 + L/μ) / ε ) )
```

When `μ ≤ L`, the middle term is `≍ (L/μ) log(Δ/ε)`. This follows from the budget: `K` gradient calls plus `2K + ⌈log₄(r²(8L²/μ+6L)/ε)⌉₊` LMO calls, using `log(1+μ/(25L)) ≥ log(1+μ/L)/25`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Richtárik–Qian, [arXiv:2611.24645v1](https://arxiv.org/abs/2611.24645) (18 Nov 2026, unrefereed), Thm 30 + Cor 31 — **the source being formalized; identical setup** | `2T−1+log₂⁺(2r√(C_rej/ε))` with `T ≤ k_cap + ⌈log(Δ/ε)/log(1+μ/(25L))⌉`, `k_cap ≤ log₄(1+6Δ/(Lr²))` → same formula with `2K` in place of `2T−1` | None: same order; Lean has one more call | Differentiability on an open neighborhood of `C` → only on `C`; `0<ε<Δ₀` → all `ε>0` (the extra cases are trivial) | Hitting time of the iterate sequence → fixed-budget guarantee for the output center (routine, since `f` decreases monotonically along accepted steps) | None |
| Garber–Hazan, [arXiv:1301.4666](https://arxiv.org/abs/1301.4666) / SIAM J. Optim. 26 (2016), Alg. 2, Lemmas 1–2 with an exact local oracle (`ρ=1`) — **restricted to Euclidean, σ-strongly convex, minimizer attained** | `2⌈1+(4L/μ)log(C/ε)⌉`, with `C ≥ Δ` known → `O((L/μ)log⁺(Δ/ε) + log(1+Δ/(Lr²)) + log⁺(r²L²/(με)))` | None: same leading order. Worse by additive logarithms and a larger constant (25 vs 4) | Euclidean strongly convex → general norm, normal-cone PL (nonconvex PL objectives; no attained minimizer) | Known `μ`, `L`, and `C ≥ Δ` → only `L` (plus an initial cap `r`) | The cap `r` enters through additive logarithmic terms. The lemma proofs use only smoothness and `‖x−x⋆‖² ≤ 2h/σ`, so the strongly convex rate transfers to any norm |
| Richtárik–Gruntkowska–Li, [arXiv:2605.08850v2](https://arxiv.org/abs/2605.08850) (Sep 2026), Thm 3.3 (prescribed geometric radii); Thm 3.6 (backtracking) — **Euclidean** | Thm 3.3: `⌈(4L/μ)log(C₀/ε)⌉` local solves, needs `μ, L, C₀`. Thm 3.6: counts accepted steps only, no total-call bound → `N` above | None in order versus Thm 3.3. Versus Thm 3.6, a total-call bound where none was given | Strongly convex (Thm 3.3/3.6) or projected-gradient PL (App. D) → normal-cone PL in a general norm | `μ, C₀` known → unknown | Same as above |

**Standard reduction and proof ancestry.** I found no reduction giving `μ`- and `Δ`-free total-call bounds under constrained PL in a general norm. The relevant ingredients are all established:

- the warm-start doubling with `2K + log` amortized calls (Nesterov's universal method, 2015);
- Armijo-type radius search for local linear programs (Ferris–Zavriev, 1996);
- the certificate inequality from Kovalev ([arXiv:2503.12645](https://arxiv.org/abs/2503.12645), Thm 1).

In the unconstrained case `C=E`, normalized steepest descent with step `‖g‖_*/L` already gives `O((L/μ)log(Δ/ε))` calls with no knowledge of `μ` (my one-line derivation). In the Euclidean strongly convex case, the repository's accelerated local-LMO method ([CertifiedLevelBroxUnknownValue](../../LongTails/Theorems/CertifiedLevelBroxUnknownValue.lean)) needs `R`. Restarting it with known `μ` should give `O(√(L/μ)log(Δ/ε))`, beating this result there; that restart was not checked. The Lean formalization adds:

- an elementary Hahn–Banach proof of the normal-cone certificate;
- the hitting-time → fixed-budget conversion.

Neither adds new optimization content.

**Search coverage (21 Nov 2026).**

- **Read:** the arXiv HTML of 2611.24645v1, including Section 4.3 and Table 1; Garber–Hazan Alg. 2 and Lemmas 1–2 (PDF); a partly summarized reading of 2605.08850v2.
- **Not read:** Ferris–Zavriev TR 96-12, the exact text of Assumption 26, and Thm D.16 of 2605.08850 verbatim.
- **Commit timing:** the result was introduced in commit `df6339e3` on 21 Nov 2026, three days after the preprint appeared.
- **Companion note:** it waives novelty and correctly attributes the result. Its claimed differences from the paper match what I found.

## Conclusion

**No: this formalizes a published preprint theorem and adds no new optimization result.** The baseline is the paper being formalized: Richtárik–Qian, arXiv:2611.24645, Theorem 30 and Corollary 31. The Lean budget reproduces that bound, apart from one extra call, under identical oracles, information, and accuracy criterion.

The small differences between the Lean statement and the paper are routine:

- it requires differentiability only on `C`;
- it allows every `ε > 0`;
- it converts the paper's hitting-time bound into a fixed-budget output guarantee.

Compared with older literature, the preprint's contribution is real but concerns scope and adaptivity, not rate. With exact local oracles, Garber–Hazan (2016) already achieve `O((L/μ)log(Δ/ε))` calls for Euclidean strongly convex objectives, but they need `μ` and a gap bound. The preprint keeps that order and extends it in three ways:

- to general norms;
- to normal-cone PL, which covers nonconvex PL objectives and minimizers that are not attained;
- to unknown `μ` and `Δ`.

The price is additive logarithmic terms and a constant about 6× larger. On the Euclidean strongly convex overlap, accelerated local-LMO methods with restarts are expected to be faster. That credit belongs to the preprint, posted three days before this result was introduced.

The only claim this result supports is a faithful, slightly generalized machine-checked formalization of Richtárik–Qian's Corollary 31.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
