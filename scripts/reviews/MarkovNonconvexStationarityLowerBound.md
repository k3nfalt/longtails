# Novelty assessment: MarkovNonconvexStationarityLowerBound

[The theorem](../../LongTails/Theorems/MarkovNonconvexStationarityLowerBound.lean) is stated in [the setup](../../LongTails/Setups/MarkovSmoothNonconvex.lean); the hard instance is built in [MarkovParityLower](../../LongTails/Proofs/MarkovParityLower.lean). It shows that every randomized adaptive algorithm fails at some admissible instance for each budget `b ≤ ⌊τLΔσ²/(2⁵⁶ε⁴)⌋`. The instance may depend on the algorithm and on `b`, but not on the seed. Failure means `E‖∇f(output)‖ > ε`. The oracle returns one vector `g(x,Z_t)` per transition of a chain that starts stationary and satisfies `sup_z TV(Pᵗ(z,·),π) ≤ 2e^{-t/τ}`. Under the stationary law, `g` is unbiased and its variance is at most `σ²`.

**Necessary oracle calls:** Ω(τ·LΔσ²/ε⁴), valid for all `L,ε>0`, `τ≥1`, `σ≥4096ε`, `LΔ≥2²⁶ε²`, `d≥2⁴⁰(1+τLΔσ²/ε⁴)⁴`. Here `L` is the gradient-Lipschitz constant, `Δ` the initial gap, `σ²` the stationary variance, `τ` the uniform mixing scale, `ε` the target accuracy and `d` the dimension. Since `σ²/ε² ≥ 2²⁴`, any additive `τLΔ/ε²` term is already absorbed.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Arjevani et al., *Math. Program.* 2023 ([arXiv:1912.02365](https://arxiv.org/abs/1912.02365)), Thm 3. IID special case: an IID chain mixes at every τ≥1. | Ω(LΔσ²/ε⁴) → Ω(τLΔσ²/ε⁴) | Larger by a factor of τ, for every τ>1 | IID samples → Markov chain with mixing scale τ | None. Both cover randomized algorithms and expected norm. | Dimension polynomial in the budget (quartic); constant 2⁻⁵⁶; requires σ≥4096ε. |
| Sun & Wei, NeurIPS 2025 ([paper](https://proceedings.neurips.cc/paper_files/paper/2025/file/1cdbce34681a3aaa0154b300706743d8-Paper-Conference.pdf)), Thm 3.1, smooth case. Hitting-time class τ_h, zero-respecting algorithms. | Ω(τ_h LΔ/ε² + τ_h σ²·min{σ²,LΔ}/ε⁴). Their hard chain (App. A.1) is a lazy directed cycle of about τ_h states, so its mixing time is about τ_h². In terms of mixing time this gives Ω(√τ·LΔσ²/ε⁴) when σ²≥LΔ, and Ω(√τ·σ⁴/ε⁴) when σ²<LΔ → Ω(τLΔσ²/ε⁴) | In mixing units: √τ → τ when σ²≥LΔ. When σ²<LΔ: √τ·σ⁴/ε⁴ → τLΔσ²/ε⁴, a factor √τ·LΔ/σ² | Hitting-time parameter → mixing-time parameter (incomparable classes) | Zero-respecting → all randomized adaptive algorithms, including outputs that were never queried | Same stationary-moment oracle. Their bound needs no huge-dimension condition. |
| Sun & Wei, ICML 2025 ([PMLR 267](https://proceedings.mlr.press/v267/sun25u.html)), Thm 3.1. Countable chains, hitting time, zero-respecting. | Ω(τ_h σ²/ε² + τ_h σ²·min{σ²,LΔ}/ε⁴). The appended chain is again a lazy directed cycle. | Same comparison as the NeurIPS row | Same | Same | Same |

**Reduction check.** Converting hitting time to mixing time does not recover the τ factor, because the published hard chains mix in about τ_h² steps, not τ_h. I did not check whether some different chain with linear mixing would also satisfy their argument. Holding an IID sample for τ steps also fails, as the companion note says: with Arjevani's oracle, a held revealing sample lets an adaptive algorithm advance one link per query. The genuinely new mechanism has three parts:
- a parity colour mask, so each run of one colour reveals at most one link;
- a refresh chain with colour mass q≍ε²/σ²;
- a prefix simulator plus coordinate hiding, which handle arbitrary randomized queries and the output.

**Proof ancestry.** The probabilistic zero-chain and the direction-hiding technique come from Arjevani et al. and Carmon et al. The alternating-parity idea comes from Sun–Wei. None of them supplies the τ·TV count against unrestricted algorithms.

**Gap to upper bounds.** The repository's companion upper bound is O(τLΔσ²/ε⁴·log(σ²/ε²)) in the identical model, so the remaining gap is log(σ²/ε²). Beznosikov et al. (NeurIPS 2023, [arXiv:2305.15938](https://arxiv.org/abs/2305.15938)) prove Õ(τ(LΔ/ε² + LΔσ²/ε⁴)), but under statewise-bounded noise. The hard oracle here has statewise errors of order σ²/ε ≫ σ. The lower bound therefore says nothing about that uniform-noise class.

**Search coverage (2026-11-18 UTC).** The theorem was introduced in commit c8bf1984 on 2026-11-18, so all sources above predate it. I read the full text of both Sun–Wei papers. I searched arXiv up to 2026-11, including [arXiv:2607.25785](https://arxiv.org/abs/2607.25785) (Ω(τε⁻³), hitting time, mean-squared smooth) and [arXiv:2606.26316](https://arxiv.org/abs/2606.26316) (PL quadratic). The statement of Even (ICML 2023) was taken from secondary descriptions only. Arjevani's Theorem 3 was taken from the companion note and the standard statement, not re-read. The companion note does not mention that the Sun–Wei chains mix in about τ_h² steps, which is the decisive point for the mixing-time comparison. Otherwise its claims agree with the Lean statement.

**Conclusion**

**Yes: for mixing-time-parameterised Markov oracles, this lower bound is larger than any previously proved one.** The strongest earlier result is Sun–Wei's Theorem 3.1. It holds only for zero-respecting algorithms, and its chains mix in about τ_h² steps, so it implies only

  Ω(√τ · LΔσ²/ε⁴) (if σ² ≥ LΔ)  →  Ω(τ · LΔσ²/ε⁴) (all σ ≥ 4096ε, LΔ ≥ 2²⁶ε²).

The new bound also covers all randomized adaptive algorithms and the regime σ² < LΔ. Against the IID bound of Arjevani et al., the gain is a factor of τ.

It matches the companion upper bound up to log(σ²/ε²). Its limits:
- the dimension must be quartic in the budget;
- the constants are very large;
- the hard oracle has statewise errors far above σ, so the uniform-noise model of Beznosikov et al. is not covered.

The comparison establishes a stronger proved lower bound than the published ones. It does not show that Sun–Wei's argument could not be rerun on some chain with linear mixing; I did not check that adaptation. My searches found no earlier Ω(τLΔσ²/ε⁴) bound for general algorithms. The claimable contribution is the first such lower bound, nearly tight with the upper bound, for single-trajectory Markov oracles with stationary moments.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
