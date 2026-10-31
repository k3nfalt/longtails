# A single gradient-descent stepsize sequence that is accelerated for every condition number and every horizon

The [main theorem](UniversalSilverQuadraticGrowth.lean) concerns plain gradient descent (GD) with one **predetermined** stepsize sequence that depends only on the smoothness constant \(L\). On every \(L\)-smooth convex function with quadratic growth \(\mu\), the last iterate reaches \(f(x_T)-f^\star\le\varepsilon\) after
\[
T=\Big\lceil 2\,(1+2\kappa)^{\log 2/\log(1+\sqrt2)}\,\big(\ell+1\big)\,\big(\log_2(1+2\kappa)+\log_2(\ell+1)+3\big)\Big\rceil,
\qquad \kappa=\frac L\mu,\quad \ell=\log_2\!\Big(1+\frac{LR^2}{\varepsilon}\Big)
\]
gradient calls, that is \(O\big(\kappa^{\log_{1+\sqrt2}2}\,\log\tfrac{LR^2}{\varepsilon}\,(\log\kappa+\log\log\tfrac{LR^2}{\varepsilon})\big)\), with \(\log_{1+\sqrt2}2\approx0.7864\).
The algorithm knows neither \(\mu\), nor \(R\), nor \(\varepsilon\), nor the horizon \(T\). So the same sequence is anytime and adapts to the unknown curvature.

The Lean statement `result` asserts the accuracy at the budget horizon for every \(\varepsilon\). The proof module lemma `UniversalSilverRate.accuracy` shows it at *every* step count \(K\) beyond the internal threshold \((a+1)2^a\). Since the stepsize sequence does not depend on \(\varepsilon\), this is an anytime guarantee.

## Setup ([SmoothConvexQuadraticGrowth](../Setups/SmoothConvexQuadraticGrowth.lean))

- **Problem.** \(f:E\to\mathbb R\) on a real Hilbert space is convex and differentiable, and its gradient is \(L\)-Lipschitz.
- **Minimizer.** Some minimizer \(x^\star\) satisfies \(\|x_0-x^\star\|\le R\).
- **Quadratic growth.** For every \(x\) there is a minimizer \(z\) with \(\tfrac\mu2\|x-z\|^2\le f(x)-f(z)\). This is equivalent to \(f(x)-f^\star\ge\frac\mu2\operatorname{dist}(x,X^\star)^2\), the "quadratic functional growth" condition of Necoara–Nesterov–Glineur (Math. Program. 175, 2019) and the QG condition of Karimi–Nutini–Schmidt (ECML 2016). It is strictly weaker than \(\mu\)-strong convexity: it covers least squares with a rank-deficient matrix, where the minimizer set is an affine subspace.
- **Oracle.** It returns exact gradients. Every call is counted.
- **Public information.** The algorithm receives only \(E\), \(L\) and \(x_0\). The parameters \(\mu\), \(R\) and \(\varepsilon\) appear only in validity conditions, assumptions and the budget.
- **Accuracy.** \(f(x_T)-f(x^\star)\le\varepsilon\) for the last iterate.
- **Admissible algorithms.** `allowedAlgorithm` requires the method to be GD, \(x_{t+1}=x_t-\eta_t\nabla f(x_t)\), with a positive sequence \((\eta_t)\) fixed at construction from the public input. It returns the last iterate. This encodes "predetermined stepsizes" in the sense of Kornowski–Shamir and Altschuler–Parrilo, with no dependence on \(\mu\) or on the horizon.

## Algorithm ([UniversalSilver](../Algorithms/UniversalSilver.lean))

Let \(s_k\) be the order-\(k\) convex silver schedule of Altschuler–Parrilo: \(s_0=[\,]\) and \(s_{k+1}=s_k,\,1+\rho^{k}/\rho,\,s_k\) with \(\rho=1+\sqrt2\). It has \(2^k-1\) steps and sum \(\rho^k-1\) (repository: `SilverSchedule.steps`).

The universal schedule concatenates *fresh* silver blocks, with no join steps between blocks, in ruler order (the Luby–Sinclair–Zuckerman universal restart sequence, IPL 1993, used for scheduled restarts of accelerated methods by Roulet–d'Aspremont, NeurIPS 2017, and in the restart analysis of Fercoq–Qu, IMA J. Numer. Anal. 2019): block \(i=1,2,\dots\) has order \(1+v_2(i)\), where \(v_2\) is the 2-adic valuation. The block orders begin \(1,2,1,3,1,2,1,4,\dots\) (`ruler`). GD uses \(\eta_t=h_t/L\), where \(h_t\) is the \(t\)-th entry of this infinite list (`stepsize`).

## Proof idea (all steps formalized)

1. **Silver certificate** (repository `SilverTrace.endpoint_bound`, here [`certificate`](../Proofs/SilverNonexpansive.lean)). For a block of order \(k\) started at \(x\), with end \(y\), any minimizer \(z\) and \(S_k=\rho^k-1\),
\(\|y-z\|^2+S_k(S_k+1)\|\nabla f(y)/L\|^2+2S_k(f(y)-f^\star)/L\le\|x-z\|^2\).
2. **New: silver blocks never leave the initial ball** ([`nonexpansive`](../Proofs/SilverNonexpansive.lean)). *Every* GD iterate inside a silver block satisfies \(\|u-z\|\le\|x-z\|\) for every minimizer \(z\). The proof is by induction over the recursion \(s_{k+1}=s_k,\mu_k,s_k\).
   - Only the long join step \(\mu_k=1+\rho^{k-1}\) needs an argument.
   - Combining the certificate with \(\langle g,y-z\rangle\ge (f(y)-f^\star)/L+\tfrac12\|g\|^2\) and \((f(y)-f^\star)/L\ge\frac12\|g\|^2\), where \(g=\nabla f(y)/L\), gives
\(\|y-\mu_kg-z\|^2\le\|x-z\|^2+\big((\mu_k-1)^2-(S_k+1)^2\big)\|g\|^2=\|x-z\|^2+(\rho^{2k-2}-\rho^{2k})\|g\|^2\le\|x-z\|^2.\)
   - Consequence: \(f(u)-f^\star\le\frac L2\|x-z\|^2\) at every intermediate iterate. This absolute-constant overshoot bound is what an anytime guarantee needs. Kornowski–Shamir (Cor. 4) show that silver's intermediate gaps do **not** tend to zero; the lemma shows they stay bounded by the gap bound at the block start.
3. **Halving under quadratic growth** ([`block_contract`](../Proofs/UniversalSilverConvergence.lean)). If \(S_k\ge2\kappa\), the certificate and QG give a minimizer \(z'\) with \(\|y-z'\|^2\le\frac12\|x-z\|^2\). Blocks of lower order are non-expansive by step 2.
4. **Accounting** ([UniversalSilverSchedule](../Proofs/UniversalSilverSchedule.lean), [UniversalSilverRate](../Proofs/UniversalSilverRate.lean)).
   - The first \(2^a\) blocks contain exactly \((a+1)2^a\) steps.
   - At least \(2^{a+1-m}\) of them have order \(\ge m\), where \(m=\lceil\log_\rho(1+2\kappa)\rceil\).
   - Choosing \(a=m-1+\lceil\log_2\lceil\ell\rceil\rceil\) gives at least \(\ell\) halvings before step \((a+1)2^a\).
   - Any later stopping time lies inside a later block, where step 2 bounds the gap by \(\frac L2 R^22^{-\ell}\le\varepsilon\).
   - `budget_ge` proves that the displayed one-line budget dominates \((a+1)2^a\). Every gradient call, including those in the partially completed last block, is counted by the execution lemma `iterate_method`.

## What is known and what is new

| Result | Stepsizes may depend on | Class | Iterations to \(\varepsilon\) |
|---|---|---|---|
| Constant step \(1/L\) (textbook) | \(L\) | smooth convex + QG/PL | \(O(\kappa\log\frac1\varepsilon)\), anytime |
| Silver, strongly convex version (Altschuler–Parrilo, J. ACM 2025, arXiv 2309.07879) | \(L,\mu\); horizon \(2^k-1\) | smooth strongly convex | \(O(\kappa^{0.7864}\log\frac1\varepsilon)\) at special horizons |
| Periodic silver blocks (Altschuler–Parrilo 2025a, Thm 1/Cor 2; noted in Ye–Liu, arXiv 2609.26873, footnote 4) | \(L,\mu\) | smooth strongly convex | contraction per block; no intermediate-iterate control was stated |
| Zhang–Lee–Du–Chen, COLT 2025 (PMLR 291), Thm 11 | \(L,\mu\), not \(T\) | smooth strongly convex | \(O(\kappa^{0.893}\log\frac1\varepsilon)\), anytime |
| **This theorem** | \(L\) only | smooth convex + QG | \(O(\kappa^{0.7864}\log\frac{LR^2}{\varepsilon}(\log\kappa+\log\log\frac{LR^2}\varepsilon))\), anytime, \(\mu\)-oblivious |
| Lower bound, any predetermined nonnegative schedule (Ye–Liu, arXiv 2609.26873) | — | smooth strongly convex | \(\Omega(\kappa^{0.7864-o(1)}\log\frac1\delta)\) |
| Nesterov / restarted AGD | — (not GD) | smooth strongly convex / QG | \(O(\sqrt\kappa\log\frac1\varepsilon)\) |

**New.**
1. *The non-expansion lemma for silver schedules.* We could not find it in Altschuler–Parrilo I/II, Grimmer–Shu–Wang (arXiv 2403.14045, 2410.16249), Zhang–Jiang (arXiv 2410.12395), Zhang et al. (COLT 2025), arXiv 2609.09152, 2609.26873, 2609.13765, 2609.04032, 2607.02053, 2608.10418 or 2609.02855. It is elementary, but it replaces the more complicated overshoot bound of Zhang et al. (Lemma 10, constant 432).
2. *Anytime acceleration of GD under strong convexity at the optimal polynomial exponent.* Kornowski–Shamir (COLT 2024 open problem, §1) raised the strongly convex anytime question. Zhang et al. answered it with exponent \(\approx0.893\). The theorem reaches \(\log_{1+\sqrt2}2\approx0.786\), which matches the Ye–Liu lower bound up to the \(\kappa^{o(1)}\) factor allowed there and up to logarithmic factors.
   - In the smooth convex case anytime and fixed-horizon exponents differ strictly: \(2\log_2\rho/(1+\log_2\rho)\approx1.119\) versus \(\log_2\rho\approx1.271\) (arXiv 2609.09152, 2609.02855).
   - Under strong convexity or QG there is no anytime price in the exponent.
3. *A \(\mu\)-oblivious accelerated GD schedule.* To our knowledge, every previously accelerated GD stepsize schedule for strongly convex functions needs \(\kappa\). The only known universal predetermined schedule, the constant step, pays \(\kappa\).
4. *Quadratic growth instead of strong convexity.* The analysis uses convexity only through the smooth-convex interpolation inequalities, and \(\mu\) only through QG.

## Limitations

- **Not a problem-class improvement.** Nesterov's method and restarted AGD achieve \(\sqrt\kappa\). This is a statement about what plain GD can do with predetermined stepsizes.
- **Logarithmic overhead.** The universal schedule pays an extra factor \(\log_2(1+2\kappa)+\log_2(\ell+1)+3\) relative to a \(\kappa\)-tuned schedule.
  - Against Zhang et al.'s \(\kappa^{0.893}\log\frac1\varepsilon\), the polynomial exponent improves, but the displayed bound is smaller only for astronomically large \(\kappa\): about \(\kappa\approx10^{20}\), ignoring Zhang et al.'s constants. The comparison is \(\kappa^{0.107}\) against \(2(\log_2\kappa+3)\).
  - Against the constant step \(1/L\), the displayed bound is smaller once \(\kappa^{0.214}\gtrsim2(\log_2\kappa+3)\), i.e. \(\kappa\gtrsim10^{9}\).
  - Relative to the Ye–Liu lower bound, the remaining overhead is the factor \(\log\kappa+\log\log\frac{LR^2}{\varepsilon}\) (the \(\log\log\) term comes from the universal interleaving).
  - The constants are not optimized.
- **Known-\(\kappa\) variant (not formalized).** With \(\kappa\) known, repeating one block \(s_m\) with \(\rho^m-1\ge2\kappa\) and using step 2 gives \(f(x_T)-f^\star\le\frac L2R^2\,2^{-\lfloor T/(2^m-1)\rfloor}\) for all \(T\), i.e. \(O(\kappa^{0.7864}\log\frac{LR^2}\varepsilon)\) anytime. This follows from the same lemmas but is not the formalized theorem.
- **No convex anytime result.** Without growth (\(\mu=0\)), the guarantee degenerates to \(f(x_T)-f^\star\le\frac L2R^2\).
- **Exact gradients only.** Robustness of silver blocks to noise is not addressed.
