# Two-oracle stochastic sliding for nonconvex composite problems: lower bound

Lean: [`SlidingStochasticCompositeLowerBound.lean`](SlidingStochasticCompositeLowerBound.lean),
setup [`HighDimensionalSlidingStochasticComposite.lean`](../Setups/HighDimensionalSlidingStochasticComposite.lean).
The setup reuses the instance class, admissibility and success predicates of
[`SlidingStochasticComposite.lean`](../Setups/SlidingStochasticComposite.lean) verbatim, in `ℝ^d`.
The hard instances are built in `Proofs/SlidingLower*.lean` (chain A) and `Proofs/SlidingWire*.lean` (wire B).
The matching upper bound is [`SlidingStochasticCompositeUpperBound.md`](SlidingStochasticCompositeUpperBound.md).

## Statement

The problem class, oracles (gradient-only: exact `∇f` and stochastic `∇h`, with no function values) and accuracy
criterion are exactly those of the upper bound:

- `F = f + h`, with `f` `ℓ`-smooth and nonconvex, and `h` convex and `L`-smooth;
- an exact `∇f` oracle, and an IID unbiased `∇h` oracle with variance `σ²`;
- success means `E Γ(x̂) ≤ ε²/(8ℓ)`, where `Γ` is the Moreau gap.

Write `X = ℓΔ/ε²` and `H = X (1 + σ²/ε² + √(L/ℓ))`. The parameters carry a corner selector `c : Fin 2`, the
oracle whose calls are restricted, and a free allowance `K` for the other oracle. The theorem
`result : NonConvergence spec budget` states the following.

- **∇f corner** (`c = 0`). Every randomized algorithm fails with at most `⌊X/2⁶⁰⌋` calls to ∇f and at most
  `K` calls to ∇h, for any `K`.
- **∇h corner** (`c = 1`). Every randomized algorithm fails with at most `⌊H/2⁶⁰⌋` calls to ∇h and at most
  `K` calls to ∇f, for any `K`.

"Fails" means that there is an admissible instance and oracle for which the success predicate is false. Success is
"the output is measurable, `Γ ∘ output` is integrable, and `E Γ(x̂) ≤ ε²/(8ℓ)`"; we show that integrability together
with the bound is impossible. The hard instance depends on the algorithm and the budget, never on the seed, as
required.

Validity requires:

- `0 < ℓ ≤ L`, `σ ≥ 0`, `ε > 0`, and `2⁶² ε² ≤ ℓΔ`;
- a polynomial dimension bound `d ≥ 2²⁰⁰ (1 + K + H)(1 + X)³(1 + √(L/ℓ))⁹`.

Since `K` is arbitrary, each corner says that the count for one oracle is necessary however many calls the other
oracle receives. Taking `K` larger than the matching upper-bound counts gives the joint statement. With the upper bound
`(M, M·N)` this gives a **tight characterization up to universal constants**:

    ∇f:  Θ(ℓΔ/ε²)          ∇h:  Θ(ℓΔσ²/ε⁴ + √(ℓL) Δ/ε² + ℓΔ/ε²).

The ∇h upper bound has additive lower-order terms `√(1+L/ℓ) + σ²/ε²`. These are dominated in the regime
`ℓΔ ≥ 2⁶² ε²`.

## Hard instances

The proof picks one of three constructions according to the budget.

**A. Masked frontier coupling (σ-term and the ∇f corner).** We start from the interleaved chain of
[Li–Tian–Zhang–Jadbabaie, NeurIPS 2021](https://arxiv.org/abs/2104.08708), with coordinates `x₀, z₁, x₁, …, z_T, x_T`.

- The nonconvex gates `edge(z_i, x_i)` and `−potential(x₀)` are put in `f`, using the repository's frontier-chain
  profiles.
- The couplings `8·hub(x_i − z_{i+1}/2)` are put in `h`. Here `hub` is a dead-zone Huber function, so `h` is convex.
- Everything is compressed through the soft radial projection `ρ = project R`, and a ridge `(1/40)‖w‖²` is added.
- The compression breaks convexity of `h`. A ridge `κ = 12 G_H/R = 192√T/R` is moved from `f` to `h`, where
  `G_H = 16√T` bounds the coupling field. Convexity of `H∘ρ + (6G_H/R)‖·‖²` follows from a second-order Taylor bound
  for `ρ`. The radius is `R = 5280(1 + √T)`.
- The stochastic ∇h oracle multiplies the gradient of the **frontier coupling only** by an independent coin `c ∈ {0, 1/p}`.
  The frontier is the coupling leaving the last coordinate whose magnitude exceeds `1/8`. The coin is unbiased and has
  variance `≤ 576 (a/s)²(1/p − 1)`.
- The noise therefore lives entirely in the convex component. This placement is what is new compared with the masking
  of [Arjevani et al. 2023](https://arxiv.org/abs/1912.02365), which masks a nonconvex link.

Three facts drive the bound:

- An exact ∇f call never reveals `z_{i+1}`, because the gates are flat while `|z| ≤ 1/2`.
- A ∇h call reveals the next coordinate only when its coin is `1`. That happens with probability `p ≍ ε²/σ²`, and
  independently of the past.
- So the expected number of revealed coordinates after `b_h` calls is at most `p·b_h`. With `p = 1` and exposure
  counted on ∇f instead, the same chain gives the ∇f corner.

**B. Robin wire (the √(ℓL) term).** We use the known function `f = −(ℓ/2)‖x‖²`, so ∇f calls carry no information, and
`h = F_B + (ℓ/2)‖x‖²`. Here `F_B` is an `O(1)`-weakly convex chain.

- Each coupling `x_i → z_{i+1}` is replaced by a wire of `n = r²` dead-zone Huber springs.
- The springs have stiffness `r²` in the interior and soft ends `r y₁ − 7x_i` and `r y_n − (7/2) z_{i+1}`.
- The function is localized by the convex wall `smoothMax(F, 2‖·‖² − 4R²)` instead of compression, which keeps `h`
  convex.
- The wire has the exact invariance `∂_x + 2∂_z + (7/r)Σ_j ∂_{y_j} = 0`. Together with a block force-balance lemma,
  this gives an `n`-independent gradient lower bound (`≥ 1/320`) at every point where the end coordinate is unreached.
- Each ∇h call reveals one wire coordinate. The chain has `T·(n+2) ≍ (ℓΔ/ε²)·√(L/ℓ)` coordinates, and `h` is
  `L`-smooth.

**Failure criterion.** In both instances, if the output's hidden end coordinate is small, the Moreau gap is large:

- Let `y` be the prox point of the output. Then `∇F(y) = 2ℓ(x̂ − y)` and `Γ(x̂) ≥ (ℓ/2)‖x̂ − y‖²`.
- Either `y` is also unreached, and the gradient lower bound applies at `y`, or `y` is far from `x̂`.

**Hiding and averaging.**

- Random coordinate embeddings are used with partial replies that read only links fully inside the revealed prefix.
- Adaptive exposure is handled with `prefix_family_bad_count_bound`, because the prefix length is a stopping time.
- Coin independence is used per step, together with Fubini over the algorithm's seed. Algorithms need not be measurable.

## Relation to prior work

- **∇f corner.** This corner is essentially classical: with `h = 0` it is the exact-oracle lower bound of
  [Carmon et al. 2020](https://arxiv.org/abs/1710.11606) for randomized algorithms, transferred to the Moreau-gap
  criterion. We include it so
  that both counts are lower-bounded for any budget of the other oracle.
- **Single oracle.** Instance B puts all hardness into `h` with a known `f`. So the ∇h corner also implies the
  single-oracle bound for `ℓ`-weakly convex, `L`-smooth `F` with stochastic `∇F`. That bound is not new. Its √(ℓL)
  term is:
  - known for linear-span algorithms ([Zhou–Gu, ICML 2019, Thm. 4.7](https://arxiv.org/abs/1901.11224), `n = 1`);
  - implicit for randomized algorithms in the construction of
    [Zhang et al., arXiv:2610.00245v2](https://arxiv.org/abs/2610.00245) (an unrefereed preprint).

  The `ℓΔσ²/ε⁴` term is the [Arjevani et al.](https://arxiv.org/abs/1912.02365) rate with smoothness replaced by `ℓ`.
  We give a direct randomized construction and do not claim the single-oracle corollary as new.
- **New in this result.**
  - The **two-oracle** statements. The σ-term holds with an exact `∇f` and the noise confined to the convex part, for
    any number of `∇f` calls. The ∇f term holds for any number of `∇h` calls.
  - Together with the upper bound, the resulting Θ characterization. We found no lower bound for sliding-type
    two-oracle models in the nonconvex stochastic setting. Convex sliding lower bounds, such as those of Lan and of
    Kovalev et al., use convex hard instances.
- **Search coverage.**
  - arXiv listings and search, 2024 to November 2026, with the queries "gradient sliding" ∧ nonconvex, "gradient
    sliding" ∧ stochastic, composite ∧ "two oracles", "weakly convex" ∧ "lower bound" ∧ stochastic,
    plug-and-play ∧ stochastic, and "sliding" ∧ "lower bound".
  - Web searches for NeurIPS, ICML and ICLR 2024–2026 papers on these topics. Conference status was taken from
    arXiv comment fields and proceedings pages. Full proceedings listings were not scanned.
  - Papers read: Lan 2016 (GS); Lan–Ouyang (AGS); Kovalev et al. 2022 (OGS); Ghadimi–Lan 2016; Lan–Li–Xu
    2412.14291v3 (which cites the Kong–Melo–Monteiro single-oracle weakly convex rate); Allen-Zhu 1801.02982
    (SGD4); Zhou–Gu 2019; Arjevani et al. 2023; Li–Tian–Zhang–Jadbabaie 2021; Zhang et al. 2610.00245v2;
    2610.00229v2; 2608.03246v3.
  - Also checked: 2609.34099, 2602.04161, 2610.35663 and 2605.18528. None overlaps.
  - Not accessible: OpenReview submissions under review (e.g. ICLR 2027) and paywalled journal versions, beyond their
    arXiv versions.

## Limitations

- The constants are loose (`2⁻⁶⁰`), and the dimension requirement is a large polynomial in `X`, `K` and `√(L/ℓ)`.
- The regime `ℓΔ ≥ 2⁶² ε²` is needed. Outside it, the lower-order terms of the upper bound are not matched.
- The corner encoding has a limit: the two oracles' counts are lower-bounded one at a time (with the other unlimited),
  not as a joint tradeoff curve.
- The oracle model is gradient-only. Function-value queries are not covered.
- The bound is for the Moreau-gap criterion. It implies a gradient-norm lower bound up to constants, because
  `‖∇F‖ ≤ ε/2` implies `Γ ≤ ε²/(8ℓ)`.
