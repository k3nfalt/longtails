# DriftCorrectedGD: novelty assessment

[`AffineDriftPL.result`](../../LongTails/Theorems/DriftCorrectedGD.lean) concerns a differentiable, possibly nonconvex f on ℝ^d (d ≥ 1) with an L-Lipschitz gradient, a global minimizer, and the μ-PL inequality. It uses a deterministic value oracle whose k-th answer is f(x) + a_t + b_t·j + e_k(x), with t = ⌊k/(d+2)⌋, j = k mod (d+2), arbitrary drift sequences a and b, and |e_k| ≤ ν where 4dLν ≤ με ([setup](../../LongTails/Setups/AffineDriftPL.lean)). Under these assumptions, the last iterate of GD with step 1/L satisfies f(x_K) − f* ≤ ε for every outcome. The gradient is estimated by forward differences, h = √(με/d)/L, with the base point queried at the start and end of each block and linearly interpolated ([algorithm](../../LongTails/Algorithms/DriftCorrectedGD.lean)).

**Complexity.** Here d is the dimension, L the smoothness constant, μ the PL constant, Δ ≥ f(x₀) − f* the initial gap, ν the noise bound, and ε the target accuracy. The total number of value queries is

  N = (d+2)·⌈(L/μ)·log(1 + 2Δ/ε)⌉ = O(d·(1 + (L/μ)·log(1 + Δ/ε))),  valid only when ν ≤ με/(4dL).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Forward-difference GD: [Berahas–Cao–Choromanski–Scheinberg, FoCM 2022](https://arxiv.org/abs/1905.01332), Thm 2.1 (error ≤ √d·Lh/2 + 2√d·ν/h), combined with [Friedlander–Schmidt, SISC 2012](https://arxiv.org/abs/1104.2373), Lemma 2.1 (its proof uses strong convexity only through the PL inequality (2.4)). **Special case: a = b = 0** | (d+1)⌈(L/μ)log(1+2Δ/ε)⌉ → (d+2)⌈(L/μ)log(1+2Δ/ε)⌉, both under 4dLν ≤ με with the same h | None: same order (one extra query per iteration) | Drift-free oracle → oracle with arbitrary within-block linear drift b_t·j. Plain forward differences then incur unbounded bias b_t·(i+1)/h | None: both give a deterministic last-iterate objective gap | The drift blocks must align exactly with the method's (d+2)-query batches; outside the aligned class, arbitrary jumps can fall inside a batch and break the method |
| TOBYQA: [Yao–Xie, arXiv:2608.18124](https://arxiv.org/abs/2608.18124) (v1 16 Jul 2026, v2 7 Sep 2026; prior work, not peer-reviewed). Thm 3.5: exact drift-invariance of the recovered gradient under F = f(x) + βt + noise. Thm 4.10: E[K] = O(L(f(x₀) − f_low)/ε²) iterations to reach ‖∇f‖² ≤ ε | Not comparable: different criteria (expected stationarity versus objective gap) → (d+2)⌈(L/μ)log(1+2Δ/ε)⌉ | Not comparable: TOBYQA's bound relies on its assumed fully-linear model accuracy (Assumption 4.3), and the classes differ | Global single-rate drift βt → per-block drift with arbitrary jumps between blocks (when time = call index, βk is the special case a_t = β(d+2)t, b_t = β) | Expected stationarity → deterministic objective gap, at the cost of assuming PL | Requires PL and ν ≤ με/(4dL); TOBYQA covers nonconvex f and C² nonlinear drift up to a bias term (Thm 3.7) |

**Reduction check.** The selected guarantee follows by composing known results. With t = (i+1)/(d+1), the interpolated baseline (1−t)r₀ + t·r_{d+1} equals f(x) + a + b(i+1) plus a convex combination of noise terms, so the drift cancels exactly. The decoded vector is therefore an ordinary forward-difference gradient with per-coordinate noise at most 2ν. Berahas et al.'s Thm 2.1 then gives the Lean bound d(Lh/2 + 2ν/h)² ≤ d(Lh)² = με, and Friedlander–Schmidt's Lemma 2.1 yields (1−μ/L)^K·Δ + ε/2. The detrending device is classical nuisance-trend removal: TOBYQA's Theorem 3.5 proves exactly this invariance for affine drift and attributes it to the Frisch–Waugh–Lovell principle. I found no new technical mechanism. Within the repository, [GdPL](../../LongTails/Theorems/GdPL.lean) is the exact-gradient analogue, with ⌈(L/μ)log(1+Δ/ε)⌉ gradient calls.

**Search coverage (2026-10-07).** I searched arXiv, FoCM, SISC, and general web sources on noisy finite differences, PL with inexact gradients, and drift-robust derivative-free optimization. I read the cited theorems in Berahas et al., Friedlander–Schmidt, and TOBYQA. I did not check classical trend-free experimental designs directly. No companion note exists. Local references list no prior work, and the setup was introduced in commit f972912 on 2026-09-23, after TOBYQA v1/v2. I found no paper that states this exact PL guarantee under aligned piecewise-affine drift.

**Conclusion**

**No: this is a routine composition of known results, not a complexity gain or a meaningfully broader setup.**

The strongest relevant baseline is forward-difference GD (Berahas et al. Thm 2.1 plus Friedlander–Schmidt Lemma 2.1). On drift-free oracles, it gives the same order of complexity:

| | Value queries |
|---|---|
| Forward-difference GD (no drift) | (d+1)·⌈(L/μ)log(1+2Δ/ε)⌉ |
| This result (aligned affine drift) | (d+2)·⌈(L/μ)log(1+2Δ/ε)⌉ |

Both require noise ν ≤ με/(4dL). The only gain in scope is tolerating drift that is affine within each query block. One extra query at the base point removes that drift exactly, after which the known analysis applies unchanged. The same drift-cancellation idea for affine drift appears in TOBYQA's Theorem 3.5 (July 2026), which predates this result.

The broader drift class is also not independently motivated. Its blocks have length d+2 and must align with this algorithm's batches, so the class is defined around the method; the natural globally affine drift is a special case. The literature search did not find this exact PL statement, but the derivation shows it is a direct corollary.

What can be claimed is a formal, drift-tolerant version of forward-difference GD under PL. It costs one extra query per gradient and makes no improvement in rate or problem class beyond the aligned-drift device.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
