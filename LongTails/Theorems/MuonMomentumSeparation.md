# Muon with momentum versus SGD with momentum and normalized SGD with momentum, at a fixed momentum parameter

The [main theorem](MuonMomentumSeparation.lean) proves two things inside one Lean [setup](../Setups/MomentumSpectralSmooth.lean):

1. An oracle-complexity upper bound for Muon with EMA momentum on the whole class of spectrally smooth matrix objectives with row-profile noise. The bound holds at every public momentum parameter \(\beta\in[0,1)\).
2. Lower bounds at the same \(\beta\), for every step size, batch size and horizon, for two competitors run in exactly the same algorithm family:
   - SGD with EMA momentum (SGD-M);
   - Frobenius-normalized SGD with EMA momentum (NSGD-M, Cutkosky–Mehta).

The two lower bounds are part of the setup's `successful` predicate, in the same way as in [MuonNoiseSeparation](MuonNoiseSeparation.md) and [MuonAdamSgdSeparation](MuonAdamSgdSeparation.md). The theorem `result` therefore proves the upper bound and both lower bounds together.

The comparison follows [AdamHeavyTailedFixedMomentum](AdamHeavyTailedFixedMomentum.md): the momentum parameter is part of the public problem parameters and is shared by all three methods. Only the step size, batch size and horizon are tuned.

**What is new.**
- **The NSGD-M lower bound is new.** We know of no prior algorithm-specific lower bound for Euclidean-normalized SGD with momentum under nuclear-norm stationarity. It holds for every fixed \(\beta\), uniformly in \((\eta,B,T)\). At \(\beta=0\) it has no logarithmic loss, whereas the Gaussian witness of [MuonNoiseSeparation](MuonNoiseSeparation.md) loses a log factor; the trade-off is a width condition on the matrix (see Limitations).
- **The SGD-M lower bound is not claimed as a new phenomenon.** It is known that fixed-\(\beta\) heavy-ball or EMA momentum does not improve SGD's stochastic rate (Kidambi et al., ICLR 2018; Paquette–Paquette 2021). Our bound is a formally verified nuclear-geometry instance of that fact.
- **The Muon-M upper bound is not new.** This repository's [FiniteVarianceMuonHighProbability](FiniteVarianceMuonHighProbability.md) already proves a high-probability bound for persistent-EMA, single-sample Muon under the same row-profile noise model. Closely related momentum-Muon analyses appear in Yu et al. ([arXiv 2602.07425](https://arxiv.org/abs/2602.07425)) and, for the batched momentum-free method, in Tao–Yu–Zhang ([arXiv 2605.06615](https://arxiv.org/abs/2605.06615), Thm 4). Here the bound is restated in expectation, with a batch size that scales with \(1-\beta\), explicit constants and uniform-output accounting matched to the competitors.

## Problem class, oracle and accuracy

Matrices \(X\in\mathbb R^{m\times n}\) are stored as `Space m n`. The setup reuses, without change, the admissibility predicate of [BatchedSpectralSmooth](../Setups/BatchedSpectralSmooth.lean). An instance with public parameters \(L,\Delta,s,\varepsilon,\beta,X_0\) is admissible when:
- \(f\) is differentiable and spectrally smooth: \(\|\nabla f(X)-\nabla f(Y)\|_*\le L\|X-Y\|_{op}\). This is the assumption of Pethick et al. (ICML 2025), Shen et al. ([arXiv 2505.23737](https://arxiv.org/abs/2505.23737)) and Tao–Yu–Zhang (Assumption 2).
- Some \(f_{\min}\le f\) satisfies \(f(X_0)-f_{\min}\le\Delta\).
- The oracle is unbiased, jointly measurable and IID, with a **row noise profile**: there are an orthonormal basis \((b_i)\) of \(\mathbb R^m\) and \(\sigma_i\ge0\) with \(\sum_i\sigma_i\le s\) and \(\mathbb E\|(G-\nabla f)^\top b_i\|^2\le\sigma_i^2\).
  - This is the existing `FiniteVarianceSpectralSmooth.GradientModel`.
  - It is implied by the one-sided covariance condition \(\mathbb E[NN^\top]\preceq\Sigma^2\), \(s=\|\Sigma\|_*\), of ASGO ([arXiv 2503.20762](https://arxiv.org/abs/2503.20762), NeurIPS 2025) and Tao–Yu–Zhang.

Validity requires \(L>0\), \(\Delta\ge0\), \(s\ge0\), \(\varepsilon>0\) and \(0\le\beta<1\).

The accuracy criterion is \(\mathbb E\|\nabla f(\hat X)\|_*\le\varepsilon\), with output measurability and integrability. The expectation is under the product of the algorithm seed and the oracle law.

## The common algorithm family

`FollowsMomentum direction β η B T X₀` specifies the execution exactly:
\[
M_{-1}=0,\qquad M_t=\beta M_{t-1}+(1-\beta)\,\bar G_t,\qquad X_{t+1}=X_t-\eta\,\mathrm{dir}(M_t),
\]
\[
\bar G_t=\tfrac1B\textstyle\sum_{j<B}G(X_t,\omega_{Bt+j}).
\]
- Query \(Bt+j\) is made at \(X_t\).
- The output is \(X_\tau\), with \(\tau\) uniform on \(\{0,\dots,T\}\) and drawn from the algorithm seed.
- The output is pinned for every budget of at least \(B(T+1)\) calls, which is the counted cost.

The three methods ([algorithms](../Algorithms/MomentumDirection.lean)) differ only in the direction map:

| Method | \(\mathrm{dir}\) |
|---|---|
| Muon-M | \(\mathrm{polar}\) (exact polar factor, \(\mathrm{polar}(0)=0\)) |
| SGD-M | \(\mathrm{id}\) |
| NSGD-M (Cutkosky–Mehta, ICML 2020) | \(M\mapsto M/\|M\|_F\) (`frobeniusNormalize`, \(0\mapsto0\)) |

The constraints on each method:
- \(\beta\) is the public `p.β`, the same for all three.
- \(\eta>0\), \(B\ge1\) and \(T\) are free. They may depend on every public parameter.
- `allowedAlgorithm` requires Muon-M to be in this family. The theorem proves compliance through `momentum_follows polar`.

## Main result

**Upper bound (Muon-M, every admissible instance, every \(m,n,X_0,\beta\)).** Take
\[
\eta=\frac{(1-\beta)\varepsilon}{8L},\qquad B=\Big\lceil\frac{128(1-\beta)s^2}{\varepsilon^2}\Big\rceil+1,\qquad T=\Big\lceil\frac{32L\Delta/\varepsilon^2+16}{1-\beta}\Big\rceil.
\]
Then \(\mathbb E\|\nabla f(X_\tau)\|_*\le\varepsilon\) with the public budget
\[
\texttt{budget}=\Big(\Big\lceil\tfrac{128(1-\beta)s^2}{\varepsilon^2}\Big\rceil+1\Big)\Big(\Big\lceil\tfrac{32L\Delta/\varepsilon^2+16}{1-\beta}\Big\rceil+1\Big)
=O\!\Big(\frac{L\Delta s^2}{\varepsilon^4}+\frac{s^2}{\varepsilon^2}+\frac{L\Delta/\varepsilon^2+1}{1-\beta}\Big).
\]
The bound is independent of \(m\) and \(n\). Batch size \(\propto 1-\beta\) is the right scaling because the EMA already averages the noise by a factor \(\sqrt{2(1-\beta)}\).

The proof is in [MomentumMuonRate](../Proofs/MomentumMuonRate.lean). It combines:
- the spectral descent lemma for \(\|P\|_{op}\le1\);
- \(\langle\nabla f,\mathrm{polar}(M)\rangle\ge\|\nabla f\|_*-2\|M/(1-\beta^{t+1})-\nabla f\|_*\), using the scale invariance of polar;
- a lag bound from \(L\)-smoothness and the step length \(\eta\);
- an EMA noise bound \(\mathbb E\|\cdot\|_*\le s\sqrt{\sum_u w_u^2/B}\), from the row profile and martingale orthogonality;
- a time-averaging lemma for the bias-correction weights.

**Lower bounds (`sgd_momentum_lower`, `nsgd_momentum_lower`, setup predicate `MomentumLower p dir 3 (2^21)`).** Let \(r=\min(m,n)\ge2\), \(L\Delta\ge1024\varepsilon^2\) and \(N=B(T+1)\). For every \(\eta>0\), \(B\ge1\), \(T\), and every algorithm following the SGD-M or NSGD-M family at the public \(\beta\), there is an instance satisfying exactly the setup's `admissible` predicate on which success forces
\[
n-r+1\le 4N^2\qquad\text{or}\qquad (r-1)\,L\Delta\,s^2\,(1-\beta)^3\le 2^{21}\,\varepsilon^4\,N.
\]
Equivalently,
\[
N\ \ge\ \min\Big\{\tfrac12\sqrt{n-r+1},\ \frac{(r-1)(1-\beta)^3L\Delta s^2}{2^{21}\varepsilon^4}\Big\}.
\]

**Separation.** Fix \(\beta\) and take the noise-dominated regime \(s^2\ge\varepsilon^2/(1-\beta)\), with matrices wide enough that the width term does not bind.
- Muon-M costs \(O(L\Delta s^2/\varepsilon^4)\) on the whole class.
- SGD-M and NSGD-M need \(\Omega((1-\beta)^3(r-1)L\Delta s^2/\varepsilon^4)\) on members of the same class.
- The ratio grows linearly in \(r=\min(m,n)\) at every fixed \(\beta\).

## Hard instances and mechanism

Index the \(n\) columns so that \(K=\{0\}\cup\{r,\dots,n-1\}\), with \(|K|=k=n-r+1\). The witness ([instance](../Proofs/MomentumSeparationInstance.lean), [model](../Proofs/MomentumSeparationModel.lean)) is
\[
f(X)=\frac{\ell}{2}\sum_{j\in K}(X-X_0)_{0j}^2+c\sum_{i=1}^{r-1}\psi\big((X-X_0)_{ii}\big),\qquad \ell=\tfrac L2,\ c=\tfrac{8\varepsilon}{r-1}.
\]
- The first term is a quadratic "stiff row" on row 0, restricted to the columns in \(K\).
- \(\psi\) is the pseudo-Huber valley of width \(w=16\varepsilon/L\) and depth \(D=\Delta/(8\varepsilon)\) from the existing [SeparationInstance](../Proofs/SeparationInstance.lean).
- The noise is one-hot: \(G=\nabla f+s\,\varsigma\,E_{0J}\), with \(J\) uniform on \(K\) and \(\varsigma\) a uniform sign. It is bounded (\(\|N\|_F=s\)) and has row profile \((s,0,\dots,0)\).

Lean checks that the instance belongs to the class:
- \(\|\nabla f(X)-\nabla f(Y)\|_*\le(\ell+(r-1)c/w)\|X-Y\|_{op}=L\|X-Y\|_{op}\);
- the gap is at most \(\Delta\);
- the oracle is the IID product law.

**Why Muon is unaffected.** The stiff row and the flat diagonal are orthogonal blocks. The polar factor normalizes each block separately, so the stiff-row noise does not shrink the flat steps.

**Why SGD-M and NSGD-M are throttled.**
- **Good event.** Let 𝒢 be the event that all \(BT\) sampled columns are distinct. A birthday bound gives \(P(\neg\mathcal G)\le (BT)^2/k\le1/4\) when \(k>4N^2\) ([probability](../Proofs/MomentumSeparationProbability.lean)). On 𝒢, every sample's noise lives on its own column of the stiff row.
- **Reduction to scalar recursions.** Each column then follows an exact scalar heavy-ball impulse response, which is deterministic up to its sign. The flat block follows a deterministic recursion driven by the common normalizer \(\kappa(M_t)\) (\(\kappa\equiv1\) for SGD-M, \(\kappa=1/\|M_t\|_F\) for NSGD-M) ([bridge](../Proofs/MomentumSeparationBridge.lean)).
- **The quantitative lemmas** ([core](../Proofs/MomentumSeparationCore.lean)):
  - *Fresh injection (Lemma K).* Each batch injects stiff mass \(\gtrsim(1-\beta)\eta\kappa\nu\) with \(\nu=s/\sqrt B\).
  - *Persistence (Lemma P).* While \(\ell\eta\kappa\) is small over a window, injected mass decays by at most a factor 2.
  - *Window floor.* Summing persistent fresh columns lower-bounds \(\sum_t\ell\|\text{stiff}(X_t)\|_F\) over windows of length \(\asymp1/(\ell\eta\kappa)\).
  - *Normalizer band.* For NSGD-M, \(\|M_t\|_F\) is pinned between \((1-\beta)\nu\)-type quantities. Steps outside the band are few, by an EMA-sum bound.
  - *Flat travel.* The flat block moves at most \(\eta\kappa c\) per step and must travel \(D-w\).
- **Combining.** Success forces both a small stiff gradient sum and the full valley crossing on a single good path, and that gives \((D-w)\ell(1-\beta)^3\nu^2\le6912\,c\,\varepsilon^2(T+1)\) ([lower](../Proofs/MomentumSeparationLower.lean)).
- **From expectation to a path.** Expected uniform-output success gives \(\sum_{t\le T}\mathbb E\|\nabla f(X_t)\|_*\le(T+1)\varepsilon\). On 𝒢, which has probability at least \(3/4\), some path has sum at most \(3(T+1)\varepsilon\) ([bounds](../Proofs/MomentumSeparationBounds.lean)). Substituting \(D,w,c\) gives the constant \(2^{21}\).

The hard part relative to the momentum-free case is that the NSGD-M normalizer \(\|M_t\|_F\) is correlated across steps through the EMA. Momentum can also average the stiff noise down before it enters the normalizer. The fresh-orthogonal determinization on 𝒢 turns these correlated random quantities into deterministic impulse responses. The persistence/floor pair then shows that momentum averaging cannot reduce the stiff-row mass by more than a factor \((1-\beta)^{O(1)}\).

## Closest prior work

| Work | What it proves | Relation |
|---|---|---|
| [FiniteVarianceMuonHighProbability](FiniteVarianceMuonHighProbability.md) (this repository) | High-probability bound for persistent-EMA, single-sample Muon under the row-profile noise model | Prior art for our Muon-M upper bound, which is its in-expectation, batched, uniform-output counterpart |
| [MuonNoiseSeparation](MuonNoiseSeparation.md) (this repository) | Momentum-free (\(\beta=0\)) batched Muon vs SGD and NSGD: factors \(r\) and \(r/\log\), Gaussian witness, any \(n\ge m\) | We add EMA momentum at any fixed \(\beta\) and remove the log factor. The cost is the width condition \(k>4N^2\) and the factor \((1-\beta)^3\) |
| Tao, Yu, Zhang ([arXiv 2605.06615](https://arxiv.org/abs/2605.06615), NeurIPS 2026) | Thm 4: batched momentum-free Muon upper bound. Thm 3: SGD lower bound (\(B=1\), constant step, \(\mathbb E\min_t\)) | No momentum lower bounds and no NSGD lower bound |
| Yu, Tao, Wan, Luo, Zhang ([arXiv 2602.07425](https://arxiv.org/abs/2602.07425) v2, NeurIPS 2026) | Dimension-free momentum-Muon upper bounds, including heavy tails | A closely related bound under a different matrix noise condition; we did not compare their noise assumption with the row profile, and we do not claim the two conditions coincide. They prove no competitor lower bounds |
| Hübler, Pethick, Sra ([arXiv 2606.14560](https://arxiv.org/abs/2606.14560) v1), Thms 3.7–3.8 | Class lower bounds that momentum Muon matches under nuclear-norm noise; Euclidean methods compared through upper bounds only | They give no algorithm-specific NSGD-M or SGD-M lower bound |
| Zhang, Lin ([arXiv 2605.18528](https://arxiv.org/abs/2605.18528) v4) | Tight class complexity of Muon under heavy-tailed nuclear-norm noise | Class-level; no NSGD-M lower bound |
| Cutkosky, Mehta, *Momentum improves normalized SGD* (ICML 2020) | NSGD-M upper bounds with \(1-\beta\asymp\varepsilon^2/\sigma^2\)-type tuning | The algorithm we lower-bound. Their tuned \(\beta\to1\) regime is **not** covered by our fixed-\(\beta\) bound |
| Kidambi, Netrapalli, Jain, Kakade (ICLR 2018); Paquette, Paquette (2021) | Fixed-parameter stochastic heavy-ball/momentum does not improve SGD | Prior art for the SGD-M half; we claim no novelty for it |
| Xie, Wang, Wu, Li ([arXiv 2511.20584](https://arxiv.org/abs/2511.20584), ICLR 2026), Thm 4.9 | Fixed-hyperparameter lower bound for signSGD-M in ℓ∞ geometry | Related technique; it does not cover Euclidean normalization or nuclear stationarity |
| Kim, Yun (ICML 2026 workshop, OpenReview only; not read in full) | Lower bounds for SHB, Signum and Muon at optimal constant steps | Lower bounds for the momentum methods themselves; it does not list NSGD-M among the methods studied. This comparison is unverified because the paper was not accessible |

Search coverage:
- Official ICML 2025/2026, ICLR 2025/2026 and NeurIPS 2025/2026 listings.
- Targeted arXiv searches up to 2026-10-28.
- Both agents searched independently.
- OpenReview full-text search and the Kim–Yun workshop paper were not accessible in full.

## Limitations

- **Width condition.** The lower bound is informative only while \(N<\tfrac12\sqrt{n-r+1}\). It therefore needs matrices much wider than tall: \(n\gtrsim m+4N^2\), where \(N\) is the sample budget. Tall matrices (\(m>n\)) are not covered: there \(k=1\) and the left disjunct holds trivially. The row-profile class is not transpose-symmetric, so this is not a relabelling. The width condition comes from the birthday-bound determinization. Reducing it to \(k\gtrsim N\,\mathrm{polylog}N\) is open.
- **Fixed momentum and the \((1-\beta)^3\) factor.** The comparison is at a shared, public \(\beta\).
  - The exponent 3 is a proof artifact. Simulations of the deterministic recursion suggest no \(\beta\)-loss.
  - NSGD-M with its own theoretically tuned momentum (\(1-\beta\to0\) with \(\varepsilon\), as in Cutkosky–Mehta) is **not** covered; the bound is vacuous there.
  - The theorem does not show that optimally momentum-tuned NSGD-M is worse than Muon.
- **Constants and crossover.** In the noise-dominated regime, Muon's budget is about \(4096\,L\Delta s^2/\varepsilon^4\). The lower bound beats it only when \((r-1)(1-\beta)^3\gtrsim2^{33}\). Even at \(\beta=0\) this needs \(r\gtrsim9\cdot10^9\), and more for larger \(\beta\). The result establishes the order of growth in \(r\), not a speedup at practical sizes.
- **Structure of the witness.** The hard instance has a stiff row block and a separable flat diagonal. On the witness, Muon coincides with blockwise (row-normalized) momentum SGD, so the separation does not distinguish Muon from per-block normalized methods. The coupling between the two blocks comes from the competitors' global normalization.
- **Algorithm variants not covered.**
  - Nesterov-style momentum;
  - step-size schedules, warmup and decay;
  - best-iterate and last-iterate outputs;
  - Newton–Schulz polar approximations. The upper bound uses the exact polar factor.
- **Accuracy criterion.** The result is about nuclear-norm stationarity, the standard criterion for Muon. Under Frobenius stationarity, SGD is minimax optimal and no class-wise separation is possible.
- **Novelty scope.** The Muon-M upper bound and the SGD-M phenomenon are known. The new mathematical content is the NSGD-M lower bound and the joint verified separation.

## How the requested scope is met

The research direction asked, in the spirit of `AdamHeavyTailedFixedMomentum.lean`, for a provable advantage of Muon over SGD and NSGD in a practical setup not yet investigated in the literature.
- **Same family.** All three methods run in one Lean-specified family: EMA momentum at the same fixed public \(\beta\) (as in the Adam fixed-momentum result), the same oracle, the same sample accounting and the same uniform output. Each method has free \((\eta,B,T)\).
- **Practical regime.** The momentum (\(\beta>0\)) regime is how Muon and NSGD-M are run in practice. It was not covered by the momentum-free separation [MuonNoiseSeparation](MuonNoiseSeparation.md), and we found no prior NSGD-M lower bound in nuclear geometry.
- **Upper bound.** Muon-M's dimension-free upper bound holds on the whole standard spectral-smooth, row-profile class.
- **Lower bounds.** SGD-M and NSGD-M provably need a factor \((1-\beta)^3(r-1)\) more calls on members of the same class, subject to the width condition.
- **Limitations.** The stylized witness, the width requirement, the fixed-\(\beta\) restriction and the astronomical constants are stated above.

## Lean files

- Setup: [MomentumSpectralSmooth](../Setups/MomentumSpectralSmooth.lean)
- Algorithms: [MomentumDirection](../Algorithms/MomentumDirection.lean)
- Execution: [MomentumDirectionExecution](../Proofs/MomentumDirectionExecution.lean)
- Upper bound: [MomentumMuonRate](../Proofs/MomentumMuonRate.lean)
- Lower bound: [Instance](../Proofs/MomentumSeparationInstance.lean), [Model](../Proofs/MomentumSeparationModel.lean), [Bridge](../Proofs/MomentumSeparationBridge.lean), [Core](../Proofs/MomentumSeparationCore.lean), [Lower](../Proofs/MomentumSeparationLower.lean), [Probability](../Proofs/MomentumSeparationProbability.lean), [Bounds](../Proofs/MomentumSeparationBounds.lean)
