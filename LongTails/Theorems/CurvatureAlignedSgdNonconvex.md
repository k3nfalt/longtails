# SGD under curvature-aligned noise: replacing L-smoothness by two measured curvatures

The standard nonconvex SGD analysis charges both the deterministic and the stochastic parts of the bound to one global smoothness constant \(L\):
\[
T=O\Big(\frac{L\Delta}{\epsilon^2}+\frac{L\sigma^2\Delta}{\epsilon^4}\Big)
\quad\text{calls for}\quad \mathbb E\|\nabla f(\hat x)\|\le\epsilon .
\]
Here \(L\) bounds the curvature in *every* direction (\(\lambda_{\max}\) of the Hessian). The descent lemma, however, only uses two directional quantities:
- the curvature seen by the gradient;
- the curvature seen by the gradient noise.

In a small transformer language model both are much smaller than \(\lambda_{\max}\) (measurements below). This note formalizes the class defined by these two quantities, keeps the standard stochastic-gradient model (unbiased samples with variance \(\sigma^2\)), and proves that plain SGD needs
\[
T=\Big\lceil \frac{4L_g\Delta}{\epsilon^2}+\frac{8L_\xi\sigma^2\Delta}{\epsilon^4}\Big\rceil+1
\]
oracle calls. The quantities are:
- \(L_g\) is the curvature along the gradient;
- \(L_\xi\) is the curvature along the noise, normalized by the variance;
- no global Lipschitz-gradient constant appears.

On a natural subclass this complexity is minimax-optimal up to constants; that lower bound is a paper-level argument, not formalized. The proof of the upper bound is the textbook descent argument. The contribution is the realistic, measurable parameterization and its minimax characterization, not a new proof technique.

## Lean files

- Theorem: [`CurvatureAlignedSgdNonconvex.lean`](CurvatureAlignedSgdNonconvex.lean) (`OracleTemplate.CurvatureAligned.result : Convergence spec budget`).
- Setup: [`../Setups/CurvatureAlignedNoiseNonconvex.lean`](../Setups/CurvatureAlignedNoiseNonconvex.lean).
- Algorithm: [`../Algorithms/WindowSgd.lean`](../Algorithms/WindowSgd.lean) (existing). It is constant-step SGD with a uniformly random output iterate, used here with window start \(0\).
- Proofs:
  - [`CurvatureAlignedStep`](../Proofs/CurvatureAlignedStep.lean) gives the one-sample descent inequality and \(\|\nabla f\|^2\le 2L_g(f-\inf f)\).
  - [`CurvatureAlignedRun`](../Proofs/CurvatureAlignedRun.lean) handles the SGD process, conditioning on the past and integrability.
  - [`CurvatureAlignedConvergence`](../Proofs/CurvatureAlignedConvergence.lean) handles the window sum, the uniform output, the tuning algebra and assembly with `execute`.
  - The proofs reuse the repository's IID and `WindowSgd` execution lemmas (`PLHessianRun`, `PLHessianConvergence`, `TwoSidedPLSampling`, `HessianNcscProcess`).

## Setup

\(E\) is a finite-dimensional real inner-product space and \(f:E\to\mathbb R\) is differentiable. `admissible` requires the following.

1. **Pointwise curvature model.** There is a family of bounded linear maps \(Q(x):E\to E\) such that, for all \(x,u\),
   \[f(x+u)\le f(x)+\langle\nabla f(x),u\rangle+\tfrac12\langle Q(x)u,u\rangle.\]
   \(Q(x)\) need not be symmetric, PSD or bounded uniformly in \(x\).
2. **Gradient-direction curvature.** \(\langle Q(x)\nabla f(x),\nabla f(x)\rangle\le L_g\|\nabla f(x)\|^2\) for all \(x\).
3. **Lower bound.** \(f\ge f_{\rm low}\) and \(f(x_0)-f_{\rm low}\le\Delta\).
4. **Standard stochastic oracle.** Each call at \(x\) returns \(g(x,\xi_k)\), where:
   - \(g\) is jointly measurable;
   - the \(\xi_k\) are i.i.d. with law \(P_0\) (`StochasticGeneralizedSmoothAndConvex.IID`; the product structure is derived, not assumed);
   - \(\int g(x,\cdot)\,dP_0=\nabla f(x)\) and \(\int\|g(x,\cdot)-\nabla f(x)\|^2dP_0\le\sigma^2\).
5. **Curvature alignment of the noise.** With \(\zeta=g(x,\xi)-\nabla f(x)\),
   \[\int\langle Q(x)\zeta,\zeta\rangle\,dP_0\le L_\xi\int\|\zeta\|^2dP_0 .\]
   This is a joint problem–oracle condition, in the same spirit as expected smoothness. It says that the noise sees, on average, curvature at most \(L_\xi\).

Valid parameters are \(L_g>0\), \(L_\xi\ge0\), \(\sigma\ge0\), \(\Delta\ge0\), \(\epsilon>0\). The **accuracy criterion** (`successful`) is that the output is measurable, \(\|\nabla f(\hat x)\|\) is integrable, and \(\int\|\nabla f(\hat x)\|\,d\mathbb P\le\epsilon\) under the product of the seed law and the oracle law. There is **one oracle call per iteration**, and the budget is the number of calls. No algorithm restriction is imposed (`allowedAlgorithm` is the default); the theorem constructs SGD.

**Relation to \(L\)-smooth SGD.** If \(\nabla f\) is \(L\)-Lipschitz, take \(Q\equiv L\,I\); then \(L_g=L_\xi=L\) and the theorem is the classical bound. In general only the two directional curvatures enter. If the noise lies in directions of curvature \(\le L_\xi\ll L\), the leading \(\epsilon^{-4}\) term shrinks by the factor \(L/L_\xi\).

## Algorithm and guarantee

The algorithm is SGD with constant step and uniform output:
\[
x_{t+1}=x_t-\eta\,g(x_t,\xi_t),\qquad \eta=\frac{\epsilon^2}{L_g\epsilon^2+2L_\xi\sigma^2},
\]
and it returns \(x_\tau\) with \(\tau\) uniform on \(\{0,\dots,T-1\}\). The step size depends only on public parameters, and one oracle call is made per step. The proof has three steps:
1. Apply (1) at \(u=-\eta g\). The cross term \(\langle Q(x)\nabla f,\zeta\rangle\) has zero mean, which gives \(\mathbb E f(x_{t+1})\le f(x_t)-\eta(1-\eta L_g/2)\|\nabla f(x_t)\|^2+\tfrac{\eta^2}{2}L_\xi\sigma^2\).
2. Average over the window: \(\frac1T\sum_t\mathbb E\|\nabla f(x_t)\|^2\le \frac{2\Delta}{\eta T}+\eta L_\xi\sigma^2\le\epsilon^2\).
3. Conclude with \(\|v\|\le \|v\|^2/(2\epsilon)+\epsilon/2\).

The public budget is the single line above, i.e. \(O(L_g\Delta\epsilon^{-2}+L_\xi\sigma^2\Delta\epsilon^{-4})\).

## Optimality (paper-level, not formalized)

For \(0<L_\xi\le L_g\) and \(\epsilon\le c\sqrt{L_\xi\Delta}\), every algorithm needs
\[\Omega\Big(\frac{L_g\Delta}{\epsilon^2}+\frac{L_\xi\sigma^2\Delta}{\epsilon^4}\Big)\]
oracle calls on this class, in sufficiently high dimension. Both terms come from known hard instances placed in the class:
- **Deterministic term.** The \(L_g\)-smooth hard functions of Carmon, Duchi, Hinder and Sidford ([Lower bounds for finding stationary points I](https://arxiv.org/abs/1710.11606), Math. Program. 2020, Thm. 1/2), with \(Q\equiv L_gI\) and a noiseless oracle, give \(\Omega(L_g\Delta/\epsilon^2)\).
- **Stochastic term.** The bounded-variance hard instances of Arjevani, Carmon, Duchi, Foster, Srebro and Woodworth ([Lower bounds for non-convex stochastic optimization](https://arxiv.org/abs/1912.02365), Math. Program. 2023) are \(L_\xi\)-smooth. Theorem 1 covers zero-respecting algorithms, with dimension \(O(\Delta L/\epsilon^2)\); the randomized-algorithm statement is Theorem 3 of the introduction. With \(Q\equiv L_\xi I\), so that conditions 2 and 5 hold with \(L_\xi\le L_g\), they give \(\Omega(L_\xi\sigma^2\Delta/\epsilon^4)\). The success criterion \(\mathbb E\|\nabla F(x)\|\le\epsilon\) is the same as here.

Hence SGD is minimax-optimal over the class parameterized by \((\Delta,L_g,L_\xi,\sigma)\) in this regime. Two caveats apply:
- The hard instances are isotropic. The statement says nothing about methods that know or estimate \(Q\), such as preconditioning, on anisotropic instances.
- For \(L_\xi>L_g\) the upper and lower bounds differ (\(L_\xi\) versus \(L_g\) in the \(\epsilon^{-4}\) term). Whether a better method exists there is open; that regime is not the one measured below.

## Realism: measurements on a small transformer LM

**Model.** A character-level 2-layer pre-LayerNorm GPT (width 64, 4 heads, context 64, about 0.1M parameters) trained on TinyShakespeare.

**Method.** The population proxy is a fixed set of 512 sequences, with exact Hessian-vector products. The noise is a minibatch gradient minus the population gradient. Reported ratios:
- \(R_g=g^\top Hg/\|g\|^2\);
- \(R_\xi=\mathbb E\,\zeta^\top H\zeta/\mathbb E\|\zeta\|^2\);
- \(\lambda_{\max}\), by power iteration.

**SGD trajectory (momentum 0.9, lr 0.3, gradient clipping 1.0, batches of 8 sequences):**

| step | \(\lambda_{\max}\) | \(R_g\) | \(R_\xi\) | \(\lambda_{\max}/R_\xi\) |
|---|---|---|---|---|
| 0 | 0.48 | 0.145 | 0.040 | 12 |
| 150 | 4.62 | 2.78 | 0.53 | 9 |
| 500 | 3.90 | 1.18 | 0.45 | 9 |
| 1000 | 3.49 | 1.29 | 0.32 | 11 |
| 1500 | 2.80 | 0.78 | 0.25 | 11 |
| 2250 | 1.80 | 0.95 | 0.20 | 9 |
| 3000 | 2.07 | 0.59 | 0.17 | 12 |

**Checks against artefacts.**
- *Remainder along actual steps.* The finite-difference secant curvature \(2(f(x+u)-f(x)-\langle\nabla f,u\rangle)/\|u\|^2\) along real SGD noise steps \(u=\eta\zeta\), with \(\eta\in\{0.03,0.3\}\), agrees with \(R_\xi\) to two or three digits. It agrees equally at randomly perturbed points. So the quadratic model is accurate for SGD-size noise steps.
- *Learning rate and batch size.* A second run (lr 0.1, noise from batches of 32 sequences) has larger \(\lambda_{\max}\) (5.5 to 11), as expected from the lower learning rate. The ratio \(\lambda_{\max}/R_\xi\) stays at 8 to 15, so the gap is not an edge-of-stability artefact of one step size.
- *Optimizer.* Along an AdamW trajectory (lr \(3\cdot10^{-3}\), steps 75 to 1500), \(\lambda_{\max}/R_\xi\) takes the values 5.5, 6.7, 6.1, 9.3, 6.9 and 11.4. \(\lambda_{\max}/R_g\) is 1.7 to 3.7.

**Exact instance class: softmax output layer.** For the softmax output layer on fixed features \(h\) (multinomial logistic regression on the unembedding), the Hessian satisfies \(\nabla^2 f\preceq \tfrac12 I_K\otimes\mathbb E[hh^\top]\). So condition 1 holds globally with the constant \(Q=\tfrac12 I_K\otimes \mathbb E[hh^\top]\): \(\operatorname{Var}_p(v)\le\tfrac12\|v\|^2\) for the softmax Jacobian. For this class we measured \(L_g\), \(L_\xi\) and \(L=\lambda_{\max}(Q)\) on the GPT's actual final-layer features (with bias) and predictions:

| trajectory, step | \(L\) | \(L_g\) | \(L_\xi\) | \(L/L_\xi\) | \(L/L_g\) | stable rank of \(\mathbb E hh^\top\) |
|---|---|---|---|---|---|---|
| SGD, 300 | 5.74 | 4.41 | 2.48 | 2.3 | 1.3 | 3.6 |
| SGD, 1500 | 3.83 | 2.41 | 1.56 | 2.5 | 1.6 | 5.3 |
| SGD, 3000 | 3.29 | 1.96 | 1.26 | 2.6 | 1.7 | 5.6 |
| AdamW, 150 | 16.1 | 12.5 | 8.21 | 2.0 | 1.3 | 2.8 |
| AdamW, 750 | 14.9 | 9.65 | 7.16 | 2.1 | 1.5 | 3.9 |
| AdamW, 1500 | 15.8 | 10.3 | 7.74 | 2.0 | 1.5 | 4.0 |

For this exactly certified class the gain is a modest \(2\)–\(2.6\times\) on the noise term and \(1.3\)–\(1.7\times\) on the deterministic term. The larger \(\approx10\times\) gaps above hold for the local Hessian of the whole network.

**Honest size of the gain.**
- The \(\epsilon\)-exponents do not change. The improvement is an instance-dependent constant:
  - about \(5\)–\(15\times\) on the leading noise term for the whole-network local model (SGD and AdamW trajectories);
  - \(2\)–\(2.6\times\) for the globally certified softmax head;
  - \(1.3\)–\(4\times\) on the deterministic term.
- In Fisher-type models where the noise covariance is proportional to \(Q\), the gain is \(\lambda_{\max}\operatorname{tr}Q/\operatorname{tr}Q^2\). That is about \(\log d\) for a \(1/k\) spectrum and \(O(1)\) for faster decay. Larger gains require noise that is spread more isotropically than the curvature.
- The whole-network measurements validate the model only locally, along SGD-size steps. Condition 1 is assumed globally. It holds exactly for GLM- and softmax-type objectives, and with \(Q\equiv LI\) for any \(L\)-smooth function.

## Relation to prior work (to our knowledge)

- **Folklore weighted descent lemma.** The descent lemma with a smoothness matrix is classical:
  - matrix smoothness and expected separable overapproximation in coordinate and compressed methods: Qu–Richtárik 2016; Safaryan–Hanzely–Richtárik, [NeurIPS 2021](https://arxiv.org/abs/2102.07245); Det-CGD (ICLR 2024).
  - In these works the weighted variance measures sampling or compression noise.
- **The \(\eta\operatorname{tr}(H\Sigma)\) noise term.** This term and its stationary loss floor are standard in SDE and quadratic analyses (Li–Tai–E; Mandt–Hoffman–Blei; Bach–Moulines; Défossez–Bach). Stability analyses use the same quantity: Wu–Ma–E (NeurIPS 2018); Lee–Jang, "interaction-aware sharpness" (ICLR 2023); Andreyev–Beneventano, [edge of stochastic stability](https://arxiv.org/abs/2412.20553).
- **Directional smoothness.** Mishkin et al. (NeurIPS 2024) treat deterministic, path-dependent directional smoothness.
- **Lower-bound side.** Tao–Yu–Zhang ([2605.06615](https://arxiv.org/abs/2605.06615), Thm. 3) build SGD hard instances with curvature aligned to noise (\(L_i\propto\sigma_i^2\)), showing that worst-case \(L\)-smooth instances put the noise in high-curvature directions.
- **What we did not find.** We did not find a stated nonconvex stochastic complexity theorem for the class \((L_g,L_\xi,\sigma,\Delta)\) with a matching minimax lower bound, nor measurements of \(L_\xi/\lambda_{\max}\) along transformer training. The search was not exhaustive, so this is stated as "to our knowledge".

## Limitations

- The upper-bound proof is routine. Significance rests on the realistic parameterization, the measurements and the minimax characterization, which is not formalized.
- Condition 1 is global in \(u\). For deep networks it is validated only locally; a local-radius variant would need an extra noise moment.
- Parameters \(L_g,L_\xi,\sigma,\Delta\) are assumed known for the step size and budget, as in standard SGD theory.
- The measurements come from a 0.1M-parameter model and are evidence of the phenomenon, not a scaling claim.
