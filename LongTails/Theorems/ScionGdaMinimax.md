# Single-sample Scion descent–ascent for stochastic nonconvex–strongly-concave minimax under \((L_0,L_1)\)-smoothness

## Result and scope

[The theorem](ScionGdaMinimax.lean) gives an in-expectation, single-sample \(O(\varepsilon^{-4})\) guarantee for stochastic nonconvex–strongly-concave (NC-SC) minimax. The objective is *locally* \((L_0,L_1)\)-smooth, and the noise has bounded variance only. The method is a descent–ascent scheme: a Scion/uSCG momentum-LMO step on \(x\) in an arbitrary norm, and a clipped stochastic gradient ascent step on \(y\). For \(\Phi(x)=\max_y f(x,y)\) it proves \(\mathbb E\,\|\nabla\Phi(x_J)\|_\star\le\varepsilon\), with \(J\) uniform on \(\{0,\dots,T\}\) and one joint sample per iteration. The number of oracle calls is
\[
T=\Bigl\lceil 2^{39}(1+\kappa)\,\bigl(1+\ell(1+y)\bigr)^4\,(d+\omega+q+\vartheta_x)\,\bigl(\vartheta_x^2+\kappa^2(1+y+\vartheta_y^2)\bigr)\Bigr\rceil .
\]
Every quantity in it is dimensionless:

| Group | Definition |
|---|---|
| \(\kappa\) | \(L_0/\mu\) |
| \(d\) | \(32L_0\Delta/\varepsilon^2+1\) |
| \(q\) | \(\sqrt{(1+\kappa)d}\) |
| \(\vartheta_x,\ \vartheta_y\) | \(\zeta\sigma_x/\varepsilon,\ \sigma_y/\varepsilon\) |
| \(\omega\) | \(L_0W/\varepsilon\) |
| \(\ell\) | \(L_1\varepsilon/L_0\) |
| \(y\) | \(q+L_x\), with \(L_x=40\log\bigl(2^{20}(2+\kappa+32L_0\Delta/\varepsilon^2+\vartheta_x+\vartheta_y+\omega+\ell)\bigr)\) |

So the budget is invariant under the rescalings \(f\mapsto af\) and \((x,y)\mapsto b(x,y)\). Expanding the product, as \(\varepsilon\to0\),
\[
T\;\le\;2^{44}(1+\kappa)\,\Lambda^4\,\frac{L_0\Delta\,(\zeta^2\sigma_x^2+\kappa^2\sigma_y^2)}{\varepsilon^4}
\;+\;O\!\Bigl(\mathrm{poly}(\kappa,\Lambda)\,\varepsilon^{-3}\log\tfrac1\varepsilon\Bigr),
\qquad
\Lambda=1+L_1\sqrt{\tfrac{32(1+\kappa)\Delta}{L_0}}+o(1).
\]
This uses \(\ell(1+y)=L_1\sqrt{(1+\kappa)(32\Delta/L_0+\varepsilon^2/L_0^2)}+O(\varepsilon\log\frac1\varepsilon)\). So:
- the \(x\)-noise term carries \(\kappa^1\);
- the \(y\)-noise term carries \(\kappa^3\);
- the generalized-smoothness price is the fourth power of the single group \(1+L_1\sqrt{\kappa\Delta/L_0}\).

The log factor only enters terms of order \(\varepsilon^{-3}\) and lower. The rate does not depend on a batch, on a confidence level \(\delta\), or on any bound on \(\nabla\Phi\) along the iterates.

This is the guarantee that [Gao–Liu, arXiv:2603.04940](https://arxiv.org/abs/2603.04940) claimed in v1 (March 2026) for the Euclidean NSGDA-M method. Their v2 (August 2026) replaces it, without an explicit retraction notice, and proves only \(\mathbb E\)-rate \(O(T^{-1/7})\) (Thm 3.6). That result also needs the algorithm-dependent assumption \(\|\nabla\Phi(x_t)\|\le G_\Phi\) a.s. along the iterates; v2 states that the \(G_\Phi\delta\) term "cannot be omitted" in their analysis.

## Setup

The [specification](../Setups/MinimaxLmo.lean) (`GeneralizedMinimax`) has the following ingredients.

**Geometry.**
- \(x\in\mathbb R^{d_1}\) carries an arbitrary definite norm \(N\), with dual norm \(\|\cdot\|_\star\).
- `lmo` is an exact LMO for the \(N\)-ball of radius \(\rho\).
- The unit \(N\)-ball is contained in an \(\ell_2\)-ball, and \(\|u\|_\star\le\zeta\|u\|_2\).
- \(y\in\mathbb R^{d_2}\) is unconstrained and Euclidean.

**Local \((L_0,L_1)\)-smoothness in mixed norms.** Let \(d(u,u')=N(x-x')+\|y-y'\|\). Whenever \(L_1 d(u,u')\le1\),
\[
\|\nabla_xf(u)-\nabla_xf(u')\|_\star\le(L_0+L_1\|\nabla_xf(u)\|_\star)\,d(u,u'),
\]
and the same holds for \(\nabla_y f\) in \(\ell_2\). This is implied by the anchor's Assumption 3 (Gao–Liu, Euclidean \(x\)) when \(N\) is Euclidean. Take \(L_0=\max(L_{x,0},L_{y,0})\) and \(L_1=\max(L_{x,1},L_{y,1})\). The sum distance \(N(\Delta x)+\|\Delta y\|\) dominates the Euclidean joint distance, so the activation radius here is smaller and the right-hand side larger. Hence every instance of their Assumption 3 satisfies this one. Their compact-\(Y\) case (\(B>0\) in their Assumption 4) is **not** covered: \(y\) is unconstrained here.

**Curvature and initial gaps.**
- \(f(x,\cdot)\) is \(\mu\)-strongly concave, with \(0<\mu\le L_0\).
- \(\Phi(x_1)-\Phi(x)\le\Delta\) for all \(x\).
- Warm start: \(\|y_1-y^*(x_1)\|\le W\) with \(32L_1W\le1\).

**Oracle.**
- Fresh IID samples, given by an abstract IID stream.
- Jointly measurable and unbiased in both blocks.
- Bounded variance: \(\mathbb E\|g_x-\nabla_xf\|_2^2\le\sigma_x^2\) and \(\mathbb E\|g_y-\nabla_yf\|_2^2\le\sigma_y^2\).
- There is no bounded-noise, sub-Gaussian or bounded-gradient assumption.

**Success criterion.** \(\mathbb E\|\nabla(x\mapsto f(x,y_s(x)))(\text{output})\|_\star\le\varepsilon\) for *every* maximizer selection \(y_s\). The proof shows \(y^*\) exists and is unique, and that \(\Phi\) is differentiable with \(\nabla\Phi(x)=\nabla_xf(x,y^*(x))\) (Danskin). This holds under *local* smoothness only.

**Algorithms admitted.** `allowedAlgorithm` admits the family `lmoGda` with free schedules:
\[
m_{k+1}=\alpha_kg^x_k+(1-\alpha_k)m_k,\qquad x_{k+1}=x_k+\gamma_k\,\mathrm{lmo}(m_{k+1}),\qquad y_{k+1}=y_k+\beta_k\,\mathrm{clip}_{\delta_k}(g^y_k).
\]
Each iteration uses one joint sample, and the output distribution is non-adaptive.

## Main theorem

The [witness](../Algorithms/MinimaxLmoGda.lean) `constantGda` uses constant schedules and a uniform output. Write \(u=\varepsilon/L_0\) for the natural length, and set
\[
\theta^{-1}=1024(1+\ell)(1+\ell y)^2,\qquad
i_b=\kappa^2(2^{16}\vartheta_y^2+3y+1)\,\theta^{-1},\qquad
x_r=\tfrac43\omega+\tfrac{y}{48(1+\ell y)} .
\]
The tuning is:
- \(\gamma\rho=s=d\,u/(T+1)\);
- \(\alpha=1/(8192\vartheta_x^2+1)\), with \(\alpha_1=1\);
- \(\beta\mu=1/i_b\);
- the clip level is \(\delta=c=\varepsilon\,\kappa(192x_r+192\vartheta_y^2/x_r+512\vartheta_y^2)\).

The proof also uses:
- the tracking radius \(r=x_r u\);
- the Bernstein parameter \(\lambda=1/(\beta c+\kappa s)\).

Lengths are multiples of \(u\), \(\beta\) is a multiple of \(1/\mu\), and \(c\) is a multiple of \(\varepsilon\), so every choice is scale-consistent. The theorem `result : Convergence spec budget` uses exactly `budget` \(=T\) oracle calls.

## Proof structure

The proof modules are `Proofs/MinimaxLmo*.lean`.

1. **Structure (local smoothness only).** The proof establishes:
   - existence and uniqueness of \(y^*\), and \(\mu D\le\|\nabla_yf\|\);
   - local \(\kappa\)-Lipschitzness of \(y^*\);
   - Danskin's formula;
   - local smoothness of \(\Phi\) with modulus \((1+\kappa)(L_0+L_1\|\nabla\Phi\|_\star)\);
   - the bias bound \(\|\nabla_xf(x,y)-\nabla\Phi(x)\|_\star\le(L_0+L_1\|\nabla\Phi(x)\|_\star)\|y-y^*(x)\|\);
   - \(\|\nabla\Phi(x_1)\|_\star\le\varepsilon(5q+\ell q^2)/12\), from \(\Delta\) via a test step of length \(qu/(2(1+\kappa)(1+\ell q))\).
2. **Pathwise LMO descent against \(\nabla\Phi\).** The momentum error is measured against \(\nabla\Phi(x_k)\), not \(\nabla_xf(x_k,y_k)\). It splits exactly into a weighted noise martingale, the \(y\)-bias, and the drift of \(\nabla\Phi\). LMO steps have \(N\)-length \(\gamma\rho\), so every local-smoothness condition holds deterministically. All \(L_1\|\nabla\Phi\|_\star\) terms are absorbed when \(16(1+\kappa)L_1\gamma\rho\le\alpha\) and the tracking radius satisfies \(16L_1r\le1\). There is no bound on \(\|\nabla\Phi\|\).
3. **Noise.** The weighted martingale has \(\mathbb E\|\cdot\|\le\sqrt2\sigma_x((1-\alpha)^k+\sqrt\alpha)\), by the conditional square-function inequality.
4. **Tracking with clipping.** On the region \(\{\|y-y^*(x)\|\le r\}\), the clipped SGA step contracts \(\mathbb E D^2\) at rate \(\beta\mu/2\). This holds because there \(\|\nabla_yf\|\le c/2\), so the clip bias is at most \(2\sigma_y^2/c\). The stopped second moment \(\mathbb E[\mathbf 1_{\text{good}}D_k^2]\) then decays geometrically to \(O(\sigma_y^4/(\mu^2c^2)+\beta\sigma_y^2/\mu+(\kappa s/\beta\mu)^2)\).
5. **Exit probability (Bernstein).** Clipping makes each increment of \(D_k\) bounded by \(B=\beta c+\kappa s\). On the band \([r/2,r]\), \(e^{D_k/B}\) is a supermartingale. A union bound over start times gives
\[
\mathbb P(\text{leave } r\text{ before } T)\le (T+1)\bigl(e^{(W-r)/B}+(T+1)e^{1-r/(2B)}\bigr).
\]
6. **Bad event.** On the bad event, \(\|\nabla\Phi(x_k)\|_\star\) is bounded *deterministically* by \((\|\nabla\Phi(x_1)\|_\star+(1+\kappa)L_0sk)(1+(1+\kappa)L_1sk)^k\). This bound is exponential in \(L_1sT=O(L_1\Delta/\varepsilon)\). With \(s(T+1)=du\), the bad-event exponent is exactly \(\ell q^2\). The tuning gives \(\lambda r/4\ge\ell q^2+L_x\), so the exit factor cancels the growth. The remaining polynomial \(32(g+q^2)(T+2)^2\) is dominated by \(e^{L_x}=(2^{20}\hat G)^{40}\).
   The ratio \(r/(\beta c)\) comes from two ingredients:
   - the factor \(\theta\), which depends only on \(\ell\) and \(\ell y\);
   - the bound \(x_r\ge y/(48(1+\ell y))\).
7. **Algebra.** `MinimaxLmoParameters.lean` proves the conditions in three steps:
   - in dimensionless form (`tune_lambda`, `tune_cond`);
   - transferred to physical units through \(L_0=\varepsilon/u\), \(\mu=\varepsilon/(\kappa u)\), \(L_1=\ell/u\) (`tune_phys`, `tune_sum`, `tune_exit`, `tune_G0`);
   - each step-count requirement is dominated by the single budget line (`tune_budget`, `tune_crude`).

## Comparison with the closest results

| Work | Smoothness | Noise | Batch | Extra assumptions | Guarantee |
|---|---|---|---|---|---|
| [Lin–Jin–Jordan, ICML 2020](https://arxiv.org/abs/1906.00331) | Lipschitz | bounded variance | \(O(\kappa\sigma^2\varepsilon^{-2})\) | bounded \(Y\) | \(O(\kappa^3\varepsilon^{-4})\), expectation |
| [Xian–Chen–Huang, ICML 2024](https://proceedings.mlr.press/v235/) | generalized \(\ell\)-smooth | bounded variance | \(b_x=O(\varepsilon^{-2})\), \(b_y=O(\kappa\varepsilon^{-2})\) | warm start; \(\delta\)-dependent | \(O(\kappa^3\varepsilon^{-4})\), probability \(1-\delta\) with poly\((1/\delta)\) |
| [Gao–Liu 2603.04940v2](https://arxiv.org/abs/2603.04940), Thm 3.5 | local \((L_0,L_1)\) | **a.s. bounded** \(x\)-noise, **sub-Gaussian** \(y\)-noise | 1 | warm start \(\le1/(16L_1)\) | \(O(\varepsilon^{-4}\log(1/(\varepsilon\delta)))\) w.h.p. |
| Gao–Liu v2, Thm 3.6 | local \((L_0,L_1)\) | bounded variance | 1 | \(\|\nabla\Phi(x_t)\|\le G_\Phi\) a.s. along iterates; warm start \(\sqrt\delta/(16L_{x,1})\) | \(\mathbb E\)-rate \(O(T^{-1/7})\), i.e. \(\varepsilon^{-7}\) |
| [Wu et al. 2610.00229](https://arxiv.org/abs/2610.00229) (preprint) | Lipschitz | bounded variance | multi-loop | — | \(\tilde\Theta(\kappa L\Delta\sigma^2\varepsilon^{-4}+\dots)\), with a matching lower bound; lists generalized smoothness as open |
| SAPD+ (Zhang–Aybat–Gürbüzbalaban, NeurIPS 2022, [arXiv 2205.15084](https://arxiv.org/abs/2205.15084)); [SPDE, Zhang–Zhang–Xu–Dai 2609.21747](https://arxiv.org/abs/2609.21747) | Lipschitz | bounded variance | SAPD+: multi-loop; SPDE: single-loop, \(O(\sqrt\kappa\varepsilon^{-2})\) iterations with batch \(\asymp\sqrt\kappa\sigma^2\varepsilon^{-2}\) | SPDE: compact \(Y\); Moreau-envelope (SAPD+) / game (SPDE) stationarity | \(O(\kappa L\Delta\sigma^2\varepsilon^{-4})\) |
| Stoc-Smoothed-AGDA, [Yang et al. 2112.05604](https://arxiv.org/abs/2112.05604) | Lipschitz | bounded variance | 1 sample per block (two i.i.d. samples per iteration, alternating) | PL in \(y\) | \(O(\kappa^2L\Delta\sigma^2\varepsilon^{-4})+\tilde O(\kappa^{5/2}\sigma^2\varepsilon^{-2})\) for \(\mathbb E\|\nabla\Phi\|\) via post-processing (Cor. 4.1); unconstrained \(y\) |
| **This theorem** | local \((L_0,L_1)\), arbitrary norm on \(x\) | bounded variance | **1** | warm start \(32L_1W\le1\) | \(O\bigl(\kappa\Lambda^4L_0\Delta(\zeta^2\sigma_x^2+\kappa^2\sigma_y^2)\varepsilon^{-4}\bigr)\), **expectation** |

Honest comparison:
- **Regime.** The result is new for generalized smoothness with \(L_1>0\), bounded variance, single sample, in expectation. There the only prior expectation bound is Gao–Liu Thm 3.6's \(\varepsilon^{-7}\), which also needs \(G_\Phi\). Xian et al. (peer-reviewed) need \(\varepsilon^{-2}\)-size batches and give only poly\((1/\delta)\) high-probability guarantees.
- **Main contribution.** The \(\varepsilon\)-rate improves from \(\varepsilon^{-7}\) (Gao–Liu v2 Thm 3.6, which also needs a bounded-\(\nabla\Phi\) assumption) to \(\varepsilon^{-4}\) in expectation. The noise assumption is bounded variance only, with one sample per step. This also extends from Euclidean NSGDA-M to the LMO/Scion family in an arbitrary norm.
- **Tracked dependence, and the case \(L_1=0\).** With \(L_1=0\) we have \(\Lambda=1\), and the leading term is \(2^{44}(1+\kappa)L_0\Delta(\zeta^2\sigma_x^2+\kappa^2\sigma_y^2)\varepsilon^{-4}\).
  - In the \(y\)-noise, this matches the \(\kappa^3L\Delta\sigma^2\varepsilon^{-4}\) of single-loop SGDA (Lin–Jin–Jordan, who also need batches).
  - It is \(\kappa\)-linear in the \(x\)-noise.
  - In the Euclidean case the method is zero-respecting: normalized momentum and clipping preserve supports, so known zero-respecting lower bounds apply.
  - The \(y\)-noise term is a factor \(\kappa^2\) above the \(\kappa\)-linear rate \(\tilde\Theta(\kappa L\Delta\sigma^2\varepsilon^{-4})\), which has a matching lower bound (Wu et al.).
  - The \(x\)-noise term is \(\kappa\)-linear, one factor \(\kappa\) above the best known \(\kappa\)-free lower bound \(\Omega(L\Delta\sigma_x^2\varepsilon^{-4})\) ([Arjevani et al. 1912.02365](https://arxiv.org/abs/1912.02365), via \(f(x,y)=h(x)-\mu\|y\|^2/2\)). Whether that factor is necessary is open.
  - In \(\varepsilon\), both terms are optimal.
  - In the Lipschitz case, \(\kappa\)-linear rates are known under Moreau-envelope or game stationarity: SAPD+, and SPDE, which is single-loop but needs compact \(Y\) and an \(\varepsilon\)-dependent batch. For \(\mathbb E\|\nabla\Phi\|\) with unconstrained \(y\), a \(\kappa\)-linear rate comes from a multi-loop method (Wu et al.).
  - Single-sample Stoc-Smoothed-AGDA reduces the gap to one factor \(\kappa\) (\(\kappa^2\)). It pays an \(\tilde O(\kappa^{5/2}\sigma^2\varepsilon^{-2})\) post-processing term, which is lower order only for small \(\varepsilon\).
  - The constant \(2^{44}\) is not optimized.
  - For \(L_1>0\) the extra price is \(\Lambda^4\), a power of \(1+L_1\sqrt{(1+\kappa)\Delta/L_0}\). Here \(\sqrt{\Delta/L_0}\) is the natural length over which \(\Phi\) can decrease.
- **Algorithmic change.** The \(y\)-update is clipped. Gao–Liu's NSGDA-M uses plain SGA on \(y\). Clipping makes the increments of the tracking error bounded, which drives the Bernstein exit argument. Whether plain SGA attains \(\varepsilon^{-4}\) in expectation under bounded variance remains open.
- **Warm start.** The warm start \(32L_1W\le1\), with \(L_1=\max(L_{x,1},L_{y,1})\), is assumed. It is not achieved by the algorithm or charged to the budget.
  - It is a factor of at least 2 stronger than Gao–Liu Thm 3.5's \(1/(16L_{x,1})\).
  - It is weaker than the \(\sqrt\delta/(16L_{x,1})\) that their expectation result (Thm 3.6) needs.
  - Xian et al. also assume a warm start.
  - With \(L_1=0\) it is vacuous.

## Limitations

- **Constants and lower-order terms.** The absolute constants (\(2^{39}\) in the budget; 40 and \(2^{20}\) in \(L_x\)) are loose. The \(\varepsilon^{-3}\log\) terms come from the exit-probability union bound. Whether \(\Lambda^4\) can be reduced is open.
- **Tuning.** The tuning needs all constants \((L_0,L_1,\mu,\zeta\sigma_x,\sigma_y,\Delta,W,\varepsilon)\).
- **Noise geometry.** The \(x\)-noise is measured in \(\ell_2\) and converted by \(\zeta\), as in the Scion baseline. For \(\ell_\infty\) or spectral norms \(\zeta\) carries dimension factors.
- **Scope.** The guarantee is in expectation only, for unconstrained \(y\) and finite variance (\(p=2\)). There are no high-probability or heavy-tailed versions.
- **The \(\kappa\)-gap under \((L_0,L_1)\) is open.** All known \(\kappa\)-improved methods use a proximal centre (Smoothed-AGDA, SPDE, SAPD+). Our unpublished analysis of a localized, clipped Smoothed-AGDA found the following obstruction.
  - The proximal weight must dominate the local modulus \(L_0+L_1\|\nabla f\|\), which needs an a-priori gradient bound from the potential.
  - For this potential under bounded variance, the upper tail is only \(\exp(-\tilde\Theta(\varepsilon^{-1}))\). A two-point noise law shows the potential admits no better tail.
  - With an uncapped centre, the worst-case centre path is \(\Theta(\varepsilon^{-2})\), so the deterministic bad-event bound grows as \(\exp(\Theta(\varepsilon^{-2}))\). This is a bound used in the proof, not a demonstrated blow-up.
  - In a paper-level analysis, not formally verified, capping the centre step restores the \(\varepsilon^{-1}\) versus \(\varepsilon^{-1}\) balance. The potential-based gradient bound then holds only for \(\Lambda-1\lesssim1/8\); beyond that, a separate dual argument is needed, and it yields a rate worse than this theorem's.
  - The resulting rate \([\kappa^2+\kappa^3(\Lambda-1)^2]\cdot\mathrm{polylog}\cdot L_0\Delta\sigma^2\varepsilon^{-4}\) beats this theorem only for \(\Lambda-1\lesssim1/(\sqrt\kappa\,\mathrm{polylog})\), and only when the \(y\)-noise dominates and \(x\) is Euclidean.
  - Whether \(\kappa^1\) or \(\kappa^2\) on the \(y\)-noise is attainable under \((L_0,L_1)\)-smoothness with bounded variance and one sample is open. Under sub-Gaussian noise the tail obstruction disappears; that analysis is not carried out here.
- **Exponential absorption.** The deterministic bad-event bound grows like \(e^{O(L_1\Delta/\varepsilon)}\). It is beaten only because the exit probability decays at a faster exponential rate. This forces the clip level \(c\propto\kappa\sigma_y^2/\varepsilon\) and the factor \(\theta\).
