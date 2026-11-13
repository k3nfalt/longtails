# Linear condition-number complexity for gradient-only BBVI over every sparse-Cholesky Gaussian family

**Lean files.**
- Theorem: [`StructuredGaussianVI.lean`](StructuredGaussianVI.lean) (`result : Convergence spec budget`).
- Setup: [`../Setups/StructuredGaussianVariationalInference.lean`](../Setups/StructuredGaussianVariationalInference.lean).
- Algorithm: [`../Algorithms/StructuredReparameterizedSgd.lean`](../Algorithms/StructuredReparameterizedSgd.lean).
- Proofs: `../Proofs/StructuredGaussianVariational{Geometry,Noise,Convergence}.lean`.

The full-rank analysis of [`ReparameterizedGaussianVI.md`](ReparameterizedGaussianVI.md) (repository PR #148) is reused
for its Gaussian moment, energy, prox and weighted-averaging lemmas.

## Problem

**Target.** Let $\pi\propto e^{-V}$ on $\mathbb R^d$, where $V$ is differentiable and $\nabla V$ is $L$-Lipschitz and
$\mu$-strongly monotone, so $\pi$ is $\mu$-strongly log-concave and $L$-log-smooth. Write $\kappa=L/\mu$.

**Variational family.** A sparsity pattern is a choice of row supports $S_i\subseteq\{1,\dots,i\}$ with $i\in S_i$.
Let $w\ge\max_i|S_i|$. The structured Gaussian family is

$$\mathcal G_S=\{\mathcal N(m,CC^\top):\ C \text{ lower triangular},\ C_{ii}>0,\ C_{ij}=0 \text{ for } j\notin S_i\}.$$

| Family | Pattern | $w$ |
|---|---|---|
| Mean-field | $S_i=\{i\}$ | $1$ |
| Banded, bandwidth $b$ | $S_i=\{i-b,\dots,i\}$ | $b+1$ |
| Block-diagonal, blocks of size $b$ | — | $b$ |
| Bordered block-diagonal: $g$ global variables ordered first, local blocks of size $b$ (the hierarchical-model structure of Tan 2021 and [Ko et al., ICML 2024](https://arxiv.org/abs/2401.10989)) | — | $g+b$ |
| Full-rank Cholesky | $S_i=\{1,\dots,i\}$ | $d$ |

**Ordering caveat.** $w$ depends on how the variables are ordered. In bordered block-diagonal models the global
variables must come first. If they come last, the global rows are dense, $w=d$, and the gain over the full-rank bound
disappears.

**Objective.** BBVI minimizes, over $\lambda=(m,C)$ with $C\in\mathcal G_S$,

$$F(\lambda)=\mathbb E_{\xi\sim\mathcal N(0,I_d)}V(m+C\xi)-\sum_i\log C_{ii},$$

which equals $\mathrm{KL}(q_\lambda\|\pi)$ plus a constant.

**Oracle and cost.** The algorithm chooses points $x$ and receives $\nabla V(x)$: pointwise first-order black-box access,
with no Hessians and no closed-form Gaussian expectations. Cost is the number of gradient evaluations. The algorithm
draws its own standard Gaussian base samples. In BBVI these are Monte Carlo randomization chosen by the algorithm, not
an oracle sampling model, so the oracle is deterministic. This is the same design as PR #148. The pattern $S$ and the
constants $L,\mu,d,w,R,\varepsilon$ are public.

**Accuracy.** Expected excess reverse KL within the family:

$$\mathbb E[F(\hat\lambda)]-\min_{\mathcal G_S}F\le\varepsilon,$$

given a family minimizer $\lambda^\star=(m^\star,C^\star)$ with $\|m_0-m^\star\|^2+\|C_0-C^\star\|_F^2\le R^2$. The Lean
`successful` predicate states this gap with respect to every family minimizer, and requires the output to be measurable
and to lie in $\mathcal G_S$.

Because $F$ is $\mu$-strongly convex on $\mathcal G_S$, this also gives
$\mathbb E\|\hat\lambda-\lambda^\star\|^2\le 2\varepsilon/\mu$. That is the parameter-distance criterion of Kim et al.,
and it bounds $\mathbb E\,W_2^2(q_{\hat\lambda},q_{\lambda^\star})$ as well.

**Assumptions.** These are the standard hypotheses of:
- Domke–Gower–Garrigos ([NeurIPS 2023](https://arxiv.org/abs/2306.03638));
- Kim et al. ([NeurIPS 2023](https://arxiv.org/abs/2305.15349));
- Kim–Ma–Campbell–Gardner ([NeurIPS 2025, arXiv 2505.21721](https://arxiv.org/abs/2505.21721));
- Park–Jang–Chen ([arXiv 2610.21020](https://arxiv.org/abs/2610.21020), Assumption 1.1).

Nothing is added. In particular, there is no Hessian-Lipschitz assumption and no twice differentiability. The pattern
and $w$ are design choices of the user, not assumptions on $\pi$.

## Algorithm and output

The algorithm is the standard proximal SGD with the single-sample reparameterization gradient, restricted to the
pattern. At step $k$:
1. Draw $\xi_k\sim\mathcal N(0,I_d)$ and query $x_k=m_k+C_k\xi_k$.
2. Receive $g_k=\nabla V(x_k)$.
3. Update

$$m_{k+1}=m_k-\eta_kg_k,\qquad C_{k+1}=\mathrm{prox}_{\eta_k(-\log\det)}\big(C_k-\eta_k\,\mathrm{mask}_S(g_k\xi_k^\top)\big).$$

Here $\mathrm{mask}_S(g\xi^\top)_{ij}=g_i\xi_j\,\mathbf 1\{j\in S_i\}$ is the exact reparameterization gradient of the free
entries, and the prox acts on the diagonal by $y\mapsto(y+\sqrt{y^2+4\eta})/2$.

Parameters, as named in the algorithm file:
- step sizes $\eta_k=2/(\mu(k+a))$ (`stepSize`);
- $a=16L(2+\tau)/\mu+2$ (`patternOffset`);
- $\tau=3w+8\log(48d\kappa)$ (`patternTau`).

The output is the weighted average $\hat\lambda_K=\sum_{j=1}^K(j+a-2)\lambda_j/\sum_{j=1}^K(j+a-2)$, which lies in
$\mathcal G_S$. Each iteration uses one gradient evaluation.

## Guarantee

With

$$K=\max\Big\{1,\Big\lceil\big(2+3w+8\log(48dL/\mu)\big)\Big(\frac{26LR}{\sqrt{\mu\varepsilon}}+\frac{32dL}{\mu\varepsilon}\Big)\Big\rceil\Big\}$$

gradient evaluations, $\mathbb E[F(\hat\lambda_K)]-\min_{\mathcal G_S}F\le\varepsilon$. In order notation,

$$K=O\Big((w+\log d\kappa)\Big(\sqrt\kappa\sqrt{LR^2/\varepsilon}+\frac{d\,\kappa}{\varepsilon}\Big)\Big).$$

## Proof mechanism

Write $\hat g(\lambda)$ for the masked estimator, $X^\star=m^\star+C^\star\xi$, $D(\lambda)$ for the Bregman
divergence of the energy $\mathcal E(\lambda)=\mathbb E\,V(m+C\xi)$ at $\lambda^\star$, and $\tau=3w+8\log(48d\kappa)$.

1. **Row-wise expected smoothness** (`pattern_expected_smoothness`). For $\lambda\in\mathcal G_S$,
   $\mathbb E\|\hat g(\lambda)-\hat g(\lambda^\star)\|^2\le 2L(2+\tau)D(\lambda)$.
   - Row $i$ of the masked scale gradient has squared norm $g_i^2\sum_{j\in S_i}\xi_j^2$. So the estimator error is at
     most $(1+M)\|\nabla V(X)-\nabla V(X^\star)\|^2$, where $M=\max_i\sum_{j\in S_i}\xi_j^2$ is a maximum of $d$
     variables, each distributed as $\chi^2_{|S_i|}$.
   - Every row of $C-C^\star$ is supported in $S_i$, so $\|(C-C^\star)\xi\|^2\le M\|C-C^\star\|_F^2$.
   - Split on $M\le\tau$. On that event, use cocoercivity of $\nabla V$. Otherwise, use
     $(1+M)^2\mathbf 1\{M>\tau\}\le\frac{64}{e}e^{-\tau/8}\sum_ie^{\sum_{j\in S_i}\xi_j^2/4}$, whose mean is
     $\frac{64}{e}e^{-\tau/8}\sum_i2^{|S_i|/2}\le1/(2\kappa)$ (`pattern_tail_mass`). Strong convexity,
     $D\ge\frac\mu2\|\lambda-\lambda^\star\|^2$, absorbs the tail.
   - The resulting constant $L(w+\log d\kappa)$ compares with:
     - $L\kappa(d+k_\varphi)$ in Kim et al. 2023, Lemma 3;
     - $L(d+\log\kappa)$ from the full-rank split $M\le\|\xi\|^2$ of PR #148, which loses a factor $d/(w+\log d)$.
2. **Noise at the optimum without $\kappa$** (`pattern_variance`). $\mathbb E\|\hat g(\lambda^\star)\|^2\le(2+\tau)Ld$.
   - $\mathcal G_S$ is closed under $C^\star\mapsto C^\star+tU$ for every $U$ supported on $S$. The first-order
     optimality conditions inside the family (`pattern_opt_pinner`) therefore give $\mathbb E\nabla V(X^\star)=0$ and
     $\mathbb E\langle\nabla V(X^\star),C^\star\xi\rangle=d$.
   - Cocoercivity then gives $\mathbb E\|\nabla V(X^\star)\|^2\le Ld$, $\|\nabla V(m^\star)\|^2\le Ld$ and
     $\|C^\star\|_F^2\le d/\mu$.
   - The row-wise tail split finishes the bound. This replaces the bound
     $\sigma^2\lesssim L^2(\|\bar z-m^\star\|^2+\|C^\star\|_F^2)$ of Domke 2019, Kim et al. 2023 and Ko et al. 2024,
     which can be $\kappa$ times larger.
3. **Masked prox-SGD step and averaging** (`masked_step_expectation`, `patternPot_bound`, `patternAvg_bound`).
   - $\mathbb E\,\hat g$ is the masked mean gradient. Every difference of family members is supported on $S$, so all
     inner products in the PR #148 step inequality are unchanged by the mask.
   - The family-optimality conditions supply the fixed point
     $\lambda^\star=\mathrm{prox}_\eta(\lambda^\star-\eta\,\mathrm{diag}(1/C^\star_{ii}))$.
   - With lemmas 1 and 2, PR #148's weighted potential argument, with weights $k+a-1$, gives the KL bound. The budget
     algebra lemma `budget_algebra` is reused verbatim, with $\tau$ replaced.

## Comparison with prior work

All rows assume strongly log-concave, log-smooth targets. $\epsilon$ is the accuracy in
$\mu\,\mathbb E\|\lambda-\lambda^\star\|^2$; for the last two rows, which are stated in KL, this follows from their
KL bounds with $\epsilon=2\varepsilon$. We use $\mathrm{tr}(\mu\Sigma^\star)\in[d/\kappa,d]$, and drop constants and
$\log(1/\epsilon)$ factors.

| Work | Family | Oracle | Leading $1/\epsilon$ term |
|---|---|---|---|
| Domke et al. 2023; Kim et al. 2023 | full-rank | $\nabla V$ | $d\,\kappa^2\,\mathrm{tr}(\mu\Sigma^\star)/\epsilon$ |
| Kim–Ma–Campbell–Gardner 2025 (Thm 3.2, Prop 3.4, Gaussian base) | mean-field | $\nabla V$ | $(\log d)\,\kappa^2\,\mathrm{tr}(\mu\Sigma^\star)/\epsilon$ |
| Ko et al. 2024 (Thm 2–3, Cor 2) | bordered block-diagonal, finite-sum $V=\sum_n\ell_n$ | $M$ of $N$ component gradients | $(N/M)(d_z+d_y+k_\varphi)\sum_n\kappa_n^2/\epsilon$ (their distance units), $\kappa_n=L_n/\mu$ |
| Kim–Fu–Ma–Gardner–Campbell [2602.18718](https://arxiv.org/abs/2602.18718) (Table 1, row "SPGD, Reparam.") | full-rank | $\nabla V$ | $d\,\kappa^2\,\mathrm{tr}(\mu\Sigma^\star)/\epsilon$ |
| same (Table 1, row "SPGD, Bonnet–Price", Thm 3.3) | full-rank | $\nabla V,\nabla^2V$ | $d\,\kappa/\epsilon$ |
| Diao et al. 2023 (FB-GVI; Table 1 of 2602.18718) | full-rank (BW) | $\nabla V,\nabla^2V$ | $d\,\kappa\log(1/\epsilon)/\epsilon$ |
| Park–Jang–Chen 2026 (Thms 4.1–4.2) | full-rank | $\nabla V$ (finite differences) | needs a Hessian-Lipschitz assumption (extra) |
| Repository PR #148 | full-rank | $\nabla V$ | $(d+\log\kappa)\,d\,\kappa/\epsilon$ (KL) |
| **This result** | any $\mathcal G_S$ | $\nabla V$ | $(w+\log d\kappa)\,d\,\kappa/\epsilon$ (KL) |

How to read the Ko et al. row:
- At $M=N$, each iteration costs one full $\nabla V$. Since $L\le\sum_nL_n$, we have
  $N\sum_n\kappa_n^2\ge(\sum_n\kappa_n)^2\ge\kappa^2$, so their bound is quadratic in the condition numbers.
- Their analysis uses the finite-sum structure, in which each $\ell_n$ touches only $d_z+d_y$ coordinates. We do not
  assume that structure, and our $d\kappa/\epsilon$ term contains $d=d_z+Nd_y$.
- In the hierarchical regime where all $\kappa_n$ are small, their $N$-dependence can therefore be better than ours. Our
  improvement is in $\kappa$, for general coupled $V$.

Jiang–Chewi–Pooladian (COLT 2024) treat mean-field VI over all product measures with exact expectations, which is a
different family and a different oracle.

**What is new.**
1. **Linear $\kappa$ for gradient-only structured families.** For mean-field, banded, block and bordered
   block-diagonal families, and every sparse-Cholesky family other than full-rank, this is the first gradient-oracle guarantee for
   Gaussian VI whose condition-number dependence is linear up to logarithms. It is attained by plain SPGD with the
   reparameterization gradient.
   - **Kim et al. 2025.** Their §5 says of their $\kappa^2$ mean-field bound that "it is currently unclear whether the
     dependence on κ is tight or improvable". It is improvable to linear $\kappa$: in the units above, from
     $(\log d)\kappa^2\mathrm{tr}(\mu\Sigma^\star)/\epsilon$ to $(1+\log d\kappa)d\kappa/\epsilon$.
     - The gain is a factor $\kappa\log d/\log(d\kappa)$ when $\Sigma^\star\approx I/\mu$.
     - There is no gain when $\Sigma^\star\approx I/L$.
     - Our criterion, KL, is stronger than theirs, last-iterate distance. Our output is an average rather than the last
       iterate.
   - **Kim et al. 2026.** They attribute the $d\kappa/\epsilon$ rate to Hessian-based Price gradients and list $\kappa^2$
     for the reparameterization gradient. We show that the gradient-only reparameterization estimator also reaches
     $d\kappa/\epsilon$, up to the factor $w+\log d\kappa$.
2. **What is new beyond the full-rank case.** The full-rank case $w=d$ is repository PR #148, with factor
   $(d+\log\kappa)$, and is not claimed here. What is new is:
   - every pattern, with the factor reduced to $w+\log d\kappa$;
   - the row-wise maximum-of-$\chi^2_{|S_i|}$ tail split that makes this possible. The masked estimator analysed with
     the full-rank split only gets $\tau\approx d$, which loses $d/\log d$ for mean-field;
   - the family-restricted optimality identity.
3. **Tightness in $\kappa$.** This is from the literature, not formalized.
   - Park–Jang–Chen, Theorem 3.1, construct targets $V_v$ in dimension $d=\Theta((\log\kappa)^2)$, normalized so
     that $I_d\preceq\nabla^2V_v\preceq\kappa I_d$. That is, $\mu=1$ and $L=\kappa$, and the targets satisfy the
     assumptions of this setup. For those targets, any randomized algorithm using pointwise derivatives of any fixed
     order, and returning a Gaussian with $\sup_v\mathbb E[F_v(q)-F_v^\star]\le\varepsilon_0$, needs
     $\kappa^{1-o(1)}$ queries.
   - The near-optimal Gaussians of their Proposition B.3 are mean shifts $\mathcal N(-\frac{\log R}{R}v,I_d)$, with
     $F_v-F_v^\star=o(1)$. These lie in every $\mathcal G_S$, so $\min_{\mathcal G_S}F_v-F_v^\star=o(1)$.
   - A $\mathcal G_S$-valued algorithm is a Gaussian-valued algorithm. So reaching $\mathcal G_S$-accuracy
     $\varepsilon_0/2$ requires $\kappa^{1-o(1)}$ queries for every pattern once $\kappa$ is large.
   - Hence the $\kappa$-dependence of this result is optimal up to $\kappa^{o(1)}$ and logarithmic factors. This is
     tightness in $\kappa$ only, at fixed accuracy and polylogarithmic $d$. Optimality of the joint $d\kappa/\epsilon$
     term is not established.

## Limitations

- **Ordering of variables.** $w$ is ordering-dependent; see the caveat after the family table.
- **Kim et al.'s Hessian-adaptive regime.** Their refined bound (Theorem 3.2 and §3.2, for twice-differentiable $V$
  with nearly constant Hessian) has no $\log d$ factor. Ours always keeps $w+\log d\kappa$, so for near-Gaussian targets with
  $\kappa\lesssim\log d$ their bound can be smaller. Their bound also covers non-Gaussian location-scale bases.
- **Initialization term.** It is $\sqrt\kappa\sqrt{LR^2/\varepsilon}$ times the log factor, which is polynomial rather
  than logarithmic in $1/\varepsilon$, because of the $1/k$ step sizes. The leading $1/\varepsilon$ term is unaffected.
- **Scope of the setting.**
  - Gaussian base distribution only.
  - Single-sample estimator, without the sticking-the-landing variant.
  - The step sizes use $L,\mu,d,w$, as in the compared works.
- **Averaged output.** The output is a weighted average, not the last iterate.
- **Comparison with Ko et al.** Ko et al. exploit finite-sum structure and component subsampling, which we do not model.
  In that setting the two results are complementary rather than ordered.
