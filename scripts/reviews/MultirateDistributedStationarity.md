# MultirateDistributedStationarity: multirate gradient table for heterogeneous workers

[`result`](../../LongTails/Theorems/MultirateDistributedStationarity.lean) proves the following. Let `F = n⁻¹Σfᵢ`, where each `∇fᵢ` is `Lᵢ`-Lipschitz, `F` is bounded below with initial gap `Δ`, and worker `i` has its own unbiased, IID oracle of variance `σᵢ²`. Run [`MultirateSchedule.algorithm`](../../LongTails/Algorithms/MultirateSchedule.lean) on a complete FIFO multiport network ([setup](../../LongTails/Setups/DistributedComponentSmoothNonconvex.lean)). Its output `X` then satisfies `E‖∇F(X)‖² ≤ ε²` by the deadline `budget p`, and the execution has almost surely finitely many events.

**Elapsed time.** Write `L̄ = n⁻¹ΣLᵢ` and `r = 1 + L̄Δ/ε²`. The parameters are: `hᵢ`, the time per sample on worker `i`; `ℓ`, the latency per message; `b`, the time per bit; and `d`, the dimension. Simplifying the Lean budget, with universal constants dropped:

$$T=O\Big(\max_i h_i+\frac{\sum_i\sigma_i^2h_i}{n^2\varepsilon^2}+r\big[\ell+b\,(1+d\log(2+n(d+1)r))\big]+\frac{\Delta}{\varepsilon^2}\Big[\frac{\sum_iL_ih_i}{n}+\frac{(\sum_i\sigma_i\sqrt{L_ih_i})^2}{n^3\varepsilon^2}\Big]\Big).$$

The parameter ranges are `hᵢ, ε > 0` and `Lᵢ, Δ, σᵢ ≥ 0`. The schedule must know every `hᵢ, Lᵢ, σᵢ` as well as `Δ, ε, ℓ, b`.

The table uses equal `Lᵢ = L` and `σᵢ = σ`, and `h̄ = n⁻¹Σhᵢ`. It also assumes the global smoothness constants are comparable, `L_F ≈ L`, as in a common curved ridge plus local affine offsets. Prior bounds were converted from `E‖∇F‖² ≤ ε` to `ε²`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Malenia SGD, [Tyurin–Richtárik, NeurIPS 2023, arXiv:2305.12387](https://arxiv.org/abs/2305.12387), Thm A.4 (prior); its lower bound is Thm A.2 | `(LΔ/ε²)(max hᵢ + σ²h̄/(nε²))` with free communication → `max hᵢ + σ²h̄/(nε²) + (LΔ/ε²)(h̄ + σ²(n⁻¹Σ√hᵢ)²/(nε²))` + communication | `max hᵢ → h̄` in the recurring term; `h̄ → (mean √hᵢ)² ≤ h̄` in the noise term (Cauchy–Schwarz). Gain factor up to `max hᵢ/h̄` when `max hᵢ ≥ σ²h̄/(nε²)` and compute dominates communication. Never worse up to constants on this overlap with free communication when `LΔ ≥ ε²` | None. Malenia's class needs only `L_F`; this one adds local `Lᵢ`. With `L̄ ≥ L_F` the classes are nested | Worse: Malenia needs neither `hᵢ` nor local constants. Both outputs are random iterates | Local smoothness is required. The result loses when `L_F ≪ L̄`, for example when curvature cancels across workers. It charges bits and latency, sending all `d` coordinates to every peer |
| Ringleader ASGD, [Maranjyan–Richtárik, ICLR 2026, arXiv:2509.22860v3](https://arxiv.org/abs/2509.22860) (prior); smoothness constant satisfying `L_F ≤ L_RL ≤ (n⁻¹ΣLᵢ²)^{1/2}` | `(L_RLΔ/ε²)(max hᵢ + σ²h̄/(nε²))` → same as row 1 | Same as row 1 on the stated overlap | None. Ringleader already exploits local smoothness, yet it keeps `max hᵢ` | Worse: Ringleader handles unknown and time-varying speeds | As in row 1 |
| Rescaled ASGD, [Mahran–Maranjyan–Richtárik, arXiv:2605.13434v1](https://arxiv.org/abs/2605.13434) (13 May 2026; ICML 2026), Cor. 4.2 | `LΔσ²h̄/(nε⁴) + LΔ max hᵢ/ε² +` heterogeneity and staleness terms in `L_max, ζ, ρ` → as above | Same gain. Rescaled ASGD also has an extra term `ΔL_maxρ(max hᵢ)²/(τ_Hε²)`, where `τ_H` is the harmonic mean of the times | Removes the harmonic-period assumption (3.1) and bounded heterogeneity (`ζ, ρ`) | Worse: needs `hᵢ, Lᵢ, σᵢ` | As in row 1 |
| Repository [FiniteBitLeon](../../LongTails/Theorems/FiniteBitLeon.lean) (same model with bits and latency) | `r[max hᵢ + σ²Σhᵢ/(n²ε²) + ℓ + b⌈d/n⌉log(2+nd)]` → `T` | The same compute gain. Bit term worse: `⌈d/n⌉log(nd) → d log(nd·r)` | Global `L_F` and common `σ` → local `Lᵢ` with per-worker `σᵢ`. The classes are incomparable | None | The network gets roughly `n log r` times more bit traffic |

**Scaling check.** I verified the note's example by hand. Group `g = 0..J` has `2^{J−g}` workers with `h = 4^g`, so `n = 2^{J+1}−1`, `h̄ ≈ n/2`, `max hᵢ ≈ n²/4` and `n⁻¹Σ√hᵢ ≈ (J+1)/2`. Set `Lᵢ = σᵢ = Δ = 1`, `ε = n⁻²` and `d ≤ n`. Malenia and Ringleader then give `Θ(n⁸)`, while this result gives `O(n⁷log²n)`. Its initialization costs `n⁴` and its communication costs `O(n⁵log n)`.

**Reduction check and proof ancestry.** I found no composition of published theorems that yields the curvature-weighted term `ΣLᵢhᵢ/n`. The natural reductions fall short:
- Malenia and Ringleader pay `max hᵢ`.
- The note's grouped anchoring scheme loses only a `log n` factor in this example. That argument is the note's own and I did not verify it.

The new mechanism is that worker `i` refreshes every `⌈tᵢ/D⌉` steps, where `tᵢ` is its batch-plus-message time and `D` is the curvature-weighted average of the `tᵢ`. It computes ahead while faster workers advance. Normalized steps then bound the stale-table error by `n⁻¹ΣLᵢ·(age)`, and batches are allocated by a Lagrange-type split.

The ingredients are known:
- Stale gradient tables come from IAG/SAG, and from [DuDe-ASGD, Thm 1](https://arxiv.org/abs/2405.16966) with maximum delay.
- Smoothness-driven lazy refresh comes from [LAG, NeurIPS 2018](https://arxiv.org/abs/1805.09965), which is deterministic and has no time model; I read only its abstract.
- The finite-bit aggregation comes from the repository's FiniteBitLeon.

**Search coverage (2026-11-19 UTC).** I searched arXiv, ICLR, ICML and NeurIPS sources on heterogeneous-data asynchronous and parallel SGD under fixed computation times, local smoothness, and stale tables.
- Read through the arXiv HTML: Rescaled ASGD Sections 2–4, Ringleader's assumptions and Table 1, and Tyurin's [arXiv:2609.17483v1](https://arxiv.org/abs/2609.17483) (Sep 2026, prior) Theorems 2.3, 3.2 and 3.8.
- Tyurin's lower bounds contain only the `h̄σ²` term, consistent with the initialization term here. The nonconvex part of that paper is only sketched, and I did not read it verbatim.
- Not read verbatim: Malenia's Thm A.2 construction (Appendix E.1) and Ringleader's §5 theorem.
- Chronology: the result was introduced in commit `c549e116` on 2026-11-19, after all the cited works.
- The companion note's claims match the Lean statement and the checked sources.
- I did not run the build or the axiom audit.

## Conclusion

**Yes: with local smoothness and slow workers, the proved elapsed time is polynomially better than every published guarantee I checked.**

The strongest baselines are Malenia SGD and Ringleader ASGD. Both pay the slowest worker's time on every step, even though Ringleader already uses local smoothness. With equal `Lᵢ, σᵢ` and `L_F ≈ L`:

| | recurring cost per `LΔ/ε²` steps |
|---|---|
| Malenia / Ringleader | `max hᵢ + σ² h̄/(nε²)` |
| this result | `h̄ + σ²(mean √hᵢ)²/(nε²)`, plus a one-time `max hᵢ + σ²h̄/(nε²)` |

On the multi-scale family above this is `n⁸ → n⁷log²n`. The result agrees with Malenia's lower bound, which puts all the curvature on the slowest worker so that `ΣLᵢhᵢ/n = L·max hᵢ`.

The result loses when curvature cancels across workers (`L_F ≪ L̄`), when bit traffic dominates (it sends `d` rather than `d/n` coordinates per link), and in adaptivity: it needs every `hᵢ, Lᵢ, σᵢ`, while Ringleader tolerates unknown and varying speeds.

The comparison proves this gain against the checked baselines. Priority in this fast-moving line of work is supported only by not finding a counterexample. What can be claimed is a known-parameter, curvature-weighted multirate schedule that replaces `max hᵢ` by `ΣLᵢhᵢ/ΣLᵢ` in the recurring time under local smoothness.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
