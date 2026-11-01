# Width-free Muon versus scheduled, fixed-momentum SGD-M and NSGD-M

The [main theorem](MuonWidthSeparation.lean) proves a width-independent oracle-complexity upper bound for momentum-free batched Muon. It does so in a [setup](../Setups/ScheduledMomentumComparison.lean) whose success predicate also contains two lower bounds:
- `SgdMomentumLower`, for SGD with momentum;
- `NsgdMomentumLower`, for Frobenius-normalized SGD with momentum.

Both lower bounds are proved in Lean ([SGD-M](../Proofs/ScheduledMomentumSgd.lean), [NSGD-M](../Proofs/ScheduledMomentumNsgd.lean)). They hold for every fixed momentum \(\beta\in[0,1)\), every constant batch size \(B\ge 1\), and **every deterministic step-size schedule** \((\eta_t)_t\). On explicit hard instances inside the same problem class, they force an oracle budget that grows **linearly in the width** \(r=\min(m,n)\). Muon's budget does not depend on \(r\) at all.

**What is new.**
- The Muon upper bound is **not** new. It is Tao, Yu and Zhang's Thm 4 for momentum-free batched msign descent ([arXiv 2605.06615v1](https://arxiv.org/abs/2605.06615)), restated under the row-profile noise condition with explicit constants. It is exactly the repository's [`MuonNoiseSeparation`](MuonNoiseSeparation.lean) bound, with the noise batch tightened from \(64s^2/\varepsilon^2\) to \(16s^2/\varepsilon^2\).
- The new results are the two lower bounds. As far as we know, they are:
  - the first algorithm-specific lower bounds for SGD **with momentum** under nuclear-norm (ℓ1-type) stationarity that allow **arbitrary learning-rate schedules**;
  - the first such lower bounds for Euclidean-normalized SGD with momentum.
- Prior separations of the same kind fix a constant step size and use no momentum. This includes the repository's [`MuonNoiseSeparation`](MuonNoiseSeparation.md) lower-bound module, TYZ Thm 3, and Jiang–Maladkar–Mokhtari (COLT 2025).

## Problem class, oracle, and accuracy

Matrices \(X\in\mathbb R^{m\times n}\) are stored as `Space m n`. Let \(\|\cdot\|_{op}\) be the spectral norm and \(\|\cdot\|_*\) the nuclear norm. The setup reuses `BatchedSpectralSmooth.spec.admissible` unchanged. An instance \(f\) with public parameters \(L,\Delta,s,\varepsilon,X_0\) is admissible when all of the following hold:
- **Smoothness.** \(f\) is differentiable and \(\|\nabla f(X)-\nabla f(Y)\|_*\le L\|X-Y\|_{op}\). This is the spectral smoothness of Shen et al. (arXiv 2505.23737), Pethick et al. (ICML 2025), and TYZ Assumption A3b.
- **Initial gap.** \(f(X_0)-\inf f\le\Delta\), witnessed by some \(f_{\min}\).
- **Noise.** The stochastic gradient oracle is unbiased and jointly measurable. It has a row noise profile with \(\sum_i\sigma_i\le s\). This is implied by the one-sided covariance condition \(\mathbb E[NN^\top]\preceq\Sigma^2\), \(\|\Sigma\|_*=s\), of ASGO and TYZ A2b.
- **Sampling.** Samples are IID under an abstract probability measure.

The parameter condition `valid` requires \(r\ge2\), \(L>0\), \(\Delta\ge0\), \(s\ge0\), \(\varepsilon>0\) and \(L\Delta\ge72\varepsilon^2\). The last condition only excludes trivial instances: when \(L\Delta\) is of order \(\varepsilon^2\), \(O(1)\) steps already suffice.

The accuracy criterion is \(\mathbb E\|\nabla f(\hat X)\|_*\le\varepsilon\), the integral taken over the product of the algorithm seed and the oracle law, together with measurability and integrability of the output gradient norm.

## Algorithms

**Muon (the algorithm of `result`).** `allowedAlgorithm` is the existing `BatchedSpectralSmooth` family:
\[
X_{t+1}=X_t-\eta\,\mathrm{polar}(\bar G_t),\qquad \bar G_t=\tfrac1B\textstyle\sum_{j<B}G(X_t,\omega_{Bt+j}),
\]
with the output \(X_\tau\), where \(\tau\) is uniform on \(\{0,\dots,T\}\).

**Comparators.** `FollowsScheduledMomentum direction β η B T x0 A` is defined in the setup. An algorithm \(A\) is in the family when, for every seed and every reply stream:
- it queries \(X_t\) exactly \(B\) times for \(t=0,\dots,T\);
- its output is \(X_\tau\) for a seed-measurable \(\tau\) that is uniform on \(\{0,\dots,T\}\);
- the iterates follow EMA momentum started at \(M_0=0\):
\[
M_{t+1}=\beta M_t+(1-\beta)\bar G_t,\qquad X_{t+1}=X_t-\eta_t\,\mathrm{dir}(M_{t+1}),
\]

with \(\mathrm{dir}=\mathrm{id}\) for **SGD-M** (`sgdDirection`) and \(\mathrm{dir}(M)=M/\|M\|_F\), \(0\mapsto0\), for **NSGD-M** (`nsgdDirection`).
- The step sequence \(\eta:\mathbb N\to\mathbb R\) is arbitrary and deterministic. It may depend on all public parameters and on \(T\), so constant, warmup, cosine, step-decay and WSD schedules are all covered. It may not depend on observed gradients.
- The momentum \(\beta\in[0,1)\) and the batch \(B\ge1\) are arbitrary constants.
- All \(B(T+1)\) oracle calls are charged.

**Nonvacuity.** [`ScheduledMomentum.method`](../Algorithms/ScheduledMomentum.lean) is a concrete state machine (`sgdMomentum`, `nsgdMomentum`). [`method_follows`](../Proofs/ScheduledMomentumExecution.lean) proves that it satisfies `FollowsScheduledMomentum` for every \(\beta,\eta,B\ge1,T\). It is run through the template's `execute`.

## Results

Write \(N=B(T+1)\), \(Q=L\Delta/\varepsilon^2\) and \(r=\min(m,n)\).

**Muon upper bound (`result`, from TYZ Thm 4).** Take \(\eta=\varepsilon/(2L)\), \(B=\lceil16s^2/\varepsilon^2\rceil+1\) and \(T=\lceil8L\Delta/\varepsilon^2\rceil\). Then every admissible instance of every width satisfies \(\mathbb E\|\nabla f(X_\tau)\|_*\le\varepsilon\) with
\[
N_{\rm Muon}=\Big(\big\lceil\tfrac{16s^2}{\varepsilon^2}\big\rceil+1\Big)\Big(\big\lceil\tfrac{8L\Delta}{\varepsilon^2}\big\rceil+1\Big).
\]

**SGD-M lower bound (`SgdMomentumLower`, new).** Fix any \(\beta\in[0,1)\), any deterministic \((\eta_t)\), any \(B\ge1\), any \(T\), and any algorithm \(A\) in the SGD-M family. Then there is an admissible instance on which success at budget \(N\) implies
\[
(1-\beta)\,(r-1)\,L\,\Delta\,s\;\le\;81\,\varepsilon^3\,N,
\qquad\text{i.e.}\qquad N\ \ge\ \frac{(1-\beta)(r-1)\,Q\,(s/\varepsilon)}{81}.
\]

**NSGD-M lower bound (`NsgdMomentumLower`, new).** Under the same quantifiers, with \(\Lambda=2+\log(1+s\sqrt r/\varepsilon)\), success forces
\[
(1-\beta)(r-1)L\Delta s\le288\,\varepsilon^3\Lambda\,N
\quad\text{or}\quad
(1-\beta)^2(r-1)s^2\le24\,\varepsilon^2N,
\]
that is,
\[
N\ \ge\ (r-1)\cdot\min\Big\{\frac{(1-\beta)Q\,(s/\varepsilon)}{288\,\Lambda},\ \frac{(1-\beta)^2(s/\varepsilon)^2}{24}\Big\}.
\]

The second alternative is the case where the batch alone is already that large. Both terms are linear in \(r\) (up to the \(\log r\) inside \(\Lambda\)). No width threshold \(r_0\) is needed.

**Quantifier order.** The order is the same as in the repository's earlier `MuonAdamSgdSeparation` / `MuonNoiseSeparation` comparisons:
- for every hyperparameter choice and every algorithm of the family, **there exists** an instance satisfying exactly `BatchedSpectralSmooth.spec.admissible`, with the public \(m,n,L,\Delta,s,\varepsilon,X_0\);
- success on that instance at the full budget forces the inequality.

The instance may depend on \(\beta,(\eta_t),B,T\). It cannot depend on the realized noise.

**Width separation.** Fix \(L,\Delta,s>0,\varepsilon,\beta\). Then \(N_{\rm Muon}\) is constant in \(r\), while every SGD-M and NSGD-M algorithm of the stated family needs \(N=\Omega(r)\) (respectively \(\Omega(r/\log r)\)). The Lean statement gives the following crossover widths beyond which the lower bound exceeds \(N_{\rm Muon}\). They come from the explicit constants above and are not optimized.

| \(Q\) | \(s/\varepsilon\) | \(\beta\) | \(N_{\rm Muon}\) | SGD-M needs more for \(r\ge\) | NSGD-M needs more for \(r\ge\) |
|---|---|---|---|---|---|
| 72 | 1 | 0 | \(9.8\cdot10^3\) | \(1.1\cdot10^4\) | \(3.3\cdot10^5\) |
| 72 | 1 | 0.9 | \(9.8\cdot10^3\) | \(1.1\cdot10^5\) | \(2.4\cdot10^7\) |
| \(10^4\) | 1 | 0 | \(1.4\cdot10^6\) | \(1.1\cdot10^4\) | \(3.3\cdot10^7\) |
| \(10^4\) | 1 | 0.9 | \(1.4\cdot10^6\) | \(1.1\cdot10^5\) | \(3.3\cdot10^9\) |

The SGD-M crossover is about \(81\cdot18\cdot8/(1-\beta)\approx1.2\cdot10^4/(1-\beta)\) for every \(Q\). The NSGD-M crossovers are dominated by the large-batch alternative, which does not scale with \(Q\). They are far beyond practical widths. The NSGD-M statement should be read as an asymptotic width separation, not a numerical prediction.

## Hard instances and proof mechanism

The hard instance is the diagonal "stiff + flat valleys" witness of the repository's `SeparationInstance`, with different parameters. Put \(c=3\varepsilon/(r-1)\), \(w=6\varepsilon/L\), \(D=\Delta/(3\varepsilon)\), and \(\mathrm{valley}(u)=\sqrt{w^2+(u-D)^2}\). The objective is
\[
f(X)=\tfrac L4\,(X_{11}-X^0_{11})^2+\sum_{i=2}^{r}c\,\mathrm{valley}(X_{ii}-X^0_{ii}),
\]
with Gaussian noise of standard deviation \(s\) on the stiff entry only. [`witness_admissible`](../Proofs/ScheduledMomentumWitness.lean) proves:
- spectral smoothness exactly \(L/2+(r-1)c/w=L\);
- gap at most \((r-1)cD=\Delta\);
- the row noise profile with value \(s\).

Under either comparator, the run reduces exactly (`reduction`) to a four-dimensional scalar process: stiff coordinate \(x_t\), common flat coordinate \(y_t\), and momenta \(a_t,b_t\). The nuclear norm of the gradient is \(\frac L2|x_t|+(r-1)c|\mathrm{valley}'(y_t)|\).

1. **Success forces travel (`flat_penalty`, `travel_bound`).** Let \(V=\sum_{u<T}|y_{u+1}-y_u|\). Pathwise, \((r-1)c|\mathrm{valley}'(y_t)|\ge\frac{3\varepsilon}2(1-V/(D-w))\), because \(y_t\le V\) and \(|\mathrm{valley}'|\ge\frac12\) left of \(D-w\). Summing over the uniform output gives
\[
\textstyle\sum_t\mathbb E\,\tfrac L2|x_t|+\tfrac{(T+1)\varepsilon}2\le\tfrac{3\varepsilon}2(T+1)\,\mathbb E V/(D-w).
\]
The flats must travel distance \(\approx\Delta/\varepsilon\), and every unit of step length paid on the flats is also paid on the stiff coordinate.
2. **SGD-M: last-step noise.** The stiff coordinate is a linear Gaussian functional of the samples with deterministic coefficients (`sgd_linear`). Its newest block enters with weight \(-\eta_t(1-\beta)s/B\) per sample. Hence \(\mathbb E|x_{t+1}|\ge\frac49|\eta_t|(1-\beta)s/\sqrt B\), however the earlier terms combine (`stiff_step_lower`). The flats move at most \(c|\eta_t|\) per step because \(|b_t|\le c\).
3. **NSGD-M: kick pairing with a one-step fresh density.** Conditional on the past, the stiff momentum is \(a_{t+1}=A_t+(1-\beta)s\,Z_t\), where \(Z_t\sim N(0,1/B)\) is fresh and \(A_t\) is past-measurable (`condition_scalar`). Put \(\tau=\sqrt{r-1}\,c\).
   - If \(|a_{t+1}|\ge\tau\), the normalized step moves the stiff coordinate by at least \(|\eta_t|/2\) (`dir_kick`). The Gaussian small-ball bound makes this happen with probability at least \(1/2\) unless the batch is very large.
   - The flat step is at most \(|\eta_t|c/\max(|a_{t+1}|,\tau)\) (`dir_flat`), whose conditional mean is \(O(|\eta_t|c\Lambda\sqrt B/((1-\beta)s))\) (`inv_max_integral`).
   - The pairing \(|x_t|+|x_{t+1}|\ge|x_{t+1}-x_t|\) turns kicks into stationarity error.
   - Only one fresh Gaussian per step is used, so no multi-step density control is needed.

Every estimate is per step and weighted by \(|\eta_t|\), so it is insensitive to how the schedule distributes step length over time. This is the technical point that makes the bounds schedule-robust. Constant-step separations, in contrast, are proved through stationary-variance formulas that schedules can defeat.

## Comparison with prior work

- **Tao–Yu–Zhang, arXiv 2605.06615v1** (NeurIPS 2026 list).
  - Thm 4 is the Muon upper bound used here.
  - Thm 3 is a vector SGD lower bound in ℓ1 stationarity with \(B=1\) and a **constant** step, without momentum.
  - Our SGD-M bound allows any fixed \(\beta\), any batch and any deterministic schedule. It is stated for matrices with nuclear stationarity.
- **Jiang–Maladkar–Mokhtari, COLT 2025.** SignSGD vs SGD separation with constant-step SGD, no momentum. It is the vector analogue of the constant-step case.
- **Repository `MuonNoiseSeparation` lower-bound module (`SeparationLower`).**
  - It covers \(\beta=0\) and a constant step for both SGD and NSGD, with rates \(\Omega(rQs^2/\varepsilon^2)\) and \(\Omega(rQs^2/(\varepsilon^2\log))\).
  - Our bounds have a weaker \(s\)-exponent: \(s/\varepsilon\) instead of \((s/\varepsilon)^2\). In exchange they cover momentum and arbitrary schedules.
  - Schedules are exactly what defeats the constant-step bounds: a burst-then-anneal schedule improves SGD's cost on the old witness. That is why only one power of \(s/\varepsilon\) survives.
- **Hübler–Pethick–Sra, arXiv 2606.14560v1, and Zhang–Lin, arXiv 2605.18528v4.**
  - They give class lower bounds under **nuclear-norm p-moment** noise, where a factor \(\min(m,n)\) is unavoidable even for Muon.
  - Under the row-profile (one-sided covariance) noise used here, Muon is width-free, and the width factor is specific to the Euclidean methods.
- **Xie–Wang–Wu–Li, ICLR 2026 (arXiv 2511.20584), Thm 4.9.** A fixed-hyperparameter lower bound for SignGD-M in ℓ∞. It is vector-valued and covers neither schedules nor normalized SGD.
- **Drori–Shamir, arXiv 1910.01845v3, Thm 2.** SGD lower bounds with adaptive (norm and inner-product) step sizes in the Euclidean setting. They are dimension-free and compare neither geometries nor Muon.
- **Davis–Drusvyatskiy, arXiv 2512.04299v2.** A one-step deterministic comparison of spectral and Euclidean descent, with no multi-step complexity bounds.
- **Yadav–Xie–Wang–Li, arXiv 2512.00763v2.** This paper explicitly lists a lower bound for normalized GD as open in its softmax model. Our NSGD-M bound is in a different (smooth, stochastic, spectral) model and does not resolve that question.

**Standard-reduction check.**
- No known theorem, rescaling or composition gives a lower bound on SGD-M or NSGD-M that holds uniformly over all deterministic schedules in a spectral class.
- The \(\beta=0\) constant-step proofs rely on the momentum-free stationary-variance formula of the stiff coordinate. With momentum and a schedule, that formula changes, so those bounds do not transfer.

## Limitations

- **Output.** Uniform-average output over \(X_0,\dots,X_T\) only. With last-iterate or best-iterate output, a burst-then-anneal schedule removes the separation on these witnesses.
- **Momentum.** \(\beta\) is fixed but arbitrary. Both bounds degrade as \(\beta\to1\), through \((1-\beta)\) and \((1-\beta)^2\). A bound uniform over \(\beta\), for instance with \(\beta\) tuned to \(1-1/r\), is not proved.
- **Schedules.** The step schedule must be deterministic. Gradient-adaptive step rules (AdaGrad-norm, line search) and variable or adaptive batch sizes are not covered by the Lean statement. They are not claimed here.
- **Nesterov.** Nesterov-form momentum is not covered.
- **Noise.** \(s>0\) is required. At \(s=0\) the bounds are vacuous, and deterministic scheduled GD is not width-limited on these witnesses.
- **Witness.** The hard instances are separable and diagonal. The upper bound holds on the whole class.
- **Tightness.** The \(s\)-dependence of the lower bounds (first power) is what the schedule-robust argument certifies. Tightness of the linear-in-\(r\) rate over all schedules is not proved.
- **Constants.** The crossover widths in the table are large because the constants are not optimized.

## Lean map

- Setup, comparator family, and lower-bound statements: [`ScheduledMomentumComparison`](../Setups/ScheduledMomentumComparison.lean).
- Concrete comparators: [`Algorithms/ScheduledMomentum`](../Algorithms/ScheduledMomentum.lean). Execution correspondence and uniform output: [`ScheduledMomentumExecution`](../Proofs/ScheduledMomentumExecution.lean).
- Witness reduction, travel bound, and conditioning: [`ScheduledMomentumWitness`](../Proofs/ScheduledMomentumWitness.lean).
- Lower bounds: [`ScheduledMomentumSgd.sgd_momentum_lower`](../Proofs/ScheduledMomentumSgd.lean), [`ScheduledMomentumNsgd.nsgd_momentum_lower`](../Proofs/ScheduledMomentumNsgd.lean).
- Main theorem: [`MuonWidthSeparation.result`](MuonWidthSeparation.lean), `Convergence ScheduledMomentumComparison.spec budget`.
