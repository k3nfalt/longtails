# Log-free accelerated residual rate for cohypomonotone inclusions on the full range ρL < 1

This note explains the contribution formalized in
[MultiStepAnchoredCohypomonotone.lean](MultiStepAnchoredCohypomonotone.lean).

The theorem concerns the inclusion 0 ∈ F(x) + H(x) with F an L-Lipschitz operator, H maximally monotone, and F + H ρ-cohypomonotone. For every ρ with ρL < 1, an anchored forward-backward method with a fixed number of inner steps returns a point whose residual is at most ε after

  O( (L R / ε) · (1 − ρL)⁻² · log(e / (1 − ρL)) )

evaluations of F and of the resolvent of H. There is no logarithm of 1/ε. The method has an inner loop of fixed length, so it is not a single-loop method. To our knowledge, an O(1/ε) bound without a logarithmic factor was previously available only for ρ < 1/(2L), and the full range ρ < 1/L was covered only with an extra logarithmic factor or with the unaccelerated rate ε⁻².

## Setup and proved guarantee

The [setup](../Setups/CohypomonotoneInclusion.lean) is the composite inclusion on a real inner-product space E, which may be any real inner-product space: no completeness or finite dimension is used. It is the deterministic setting of Assumptions 1 and 2 of Alacaoglu, Kim and Wright, with one relaxation: they assume that F + H is maximally ρ-cohypomonotone, and maximality of the sum is not needed here.

- **Operators.** F : E → E satisfies ‖F x − F y‖ ≤ L‖x − y‖. H : E → Set E is monotone and has a resolvent J_γ for every γ > 0, meaning (z − J_γ z)/γ ∈ H(J_γ z); by Minty's theorem this is maximal monotonicity. The sum is ρ-cohypomonotone: for all a ∈ H(x), b ∈ H(y),

    ⟨(F x + a) − (F y + b), x − y⟩ ≥ −ρ ‖(F x + a) − (F y + b)‖².

- **Parameters.** L > 0, ρ ≥ 0, ρL < 1, a solution x* with −F(x*) ∈ H(x*) and ‖x0 − x*‖ ≤ R, and ε > 0.
- **Oracle and cost.** A call either evaluates F at a point or evaluates a resolvent J_γ at a point. Both kinds are counted, each as one call.
- **Success.** The returned point x has some ξ ∈ H(x) with ‖F(x) + ξ‖ ≤ ε, so dist(0, F(x) + H(x)) ≤ ε.
- **Information.** The algorithm is built from (L, ρ, x0) only. R and ε enter the budget and nowhere else.

With H = 0 and J_γ the identity this is the root-finding problem F(x) = 0 for a cohypomonotone (negatively comonotone) Lipschitz operator. With H the normal cone of a closed convex set it is the constrained problem, and J_γ is the projection. No new assumption is introduced.

**Algorithm.** The [algorithm](../Algorithms/MultiStepAnchoredForwardBackward.lean) uses the constants

  η = (1 + ρL)/(2L),  s = (1 − ρL)/(2L),  m = ⌈(2/(1 − ρL)) · ln(16/(1 − ρL))⌉.

It keeps a point u together with the argument c of the resolvent that produced it, so that ξ = (c − u)/η ∈ H(u) is known. Write g = F(u) + ξ and y = c + ηF(u) = u + ηg.

- Start: c_1 = x0 − ηF(x0), u_1 = J_η(c_1), and the anchor is y_1.
- Outer step k ≥ 1, with β_k = 1/(k + 1):
  - target t_k = β_k y_1 + (1 − β_k)(y_k − s g_k);
  - predictor v_0 = t_k − η(1 − β_k) g_k;
  - m + 1 forward-backward steps v_{j+1} = J_η(t_k − ηF(v_j));
  - u_{k+1} = v_{m+1}, with c_{k+1} = t_k − ηF(v_m).

The output is the current u. The inner loop has a fixed length that depends only on ρL. It does not grow with the iteration counter or with 1/ε.

**Guarantee.** For every n ≥ 0 the point u_{n+1} is available after exactly 2 + (2m + 3)n calls, and

  ‖F(u_{n+1}) + ξ_{n+1}‖ ≤ 16 L ‖x0 − x*‖ / ((1 − ρL)(n + 1)).

The public budget is

  2 + (2⌈(2/(1 − ρL)) ln(16/(1 − ρL))⌉ + 3) · ⌈16 L R / ((1 − ρL) ε)⌉,

and the Lean theorem states that the execution with this budget returns a point with residual at most ε.

**Lean layout.**
- [MultiStepAnchoredStep](../Proofs/MultiStepAnchoredStep.lean): nonexpansiveness of the resolvent, the contraction error lemma, the potential identity and the one-step potential decrease.
- [MultiStepAnchoredRun](../Proofs/MultiStepAnchoredRun.lean): the run, the residual bound, the parameter inequalities, and the proof that the algorithm's execution equals the analysed recursion with every call counted.

## Mechanism

Let μ = η − ρ, μ' = s/2 and q = ηL < 1.

1. **Cocoercivity on realised points.** For any two realised triples, ⟨g_i − g_j, y_i − y_j⟩ ≥ μ ‖g_i − g_j‖². This is cohypomonotonicity rewritten in the variable y = u + ηg. The values g are exact; only the points y are perturbed.
2. **Error identity.** The realised point is y_{k+1} = t_k + e_k with e_k = η(F(v_{m+1}) − F(v_m)). With the predictor above, v_{m+1} − v_0 = e_k − η w_k, where w_k = g_{k+1} − (1 − β_k) g_k.
3. **Relative error from a fixed number of steps.** The map v ↦ J_η(t_k − ηF(v)) is a q-contraction. Without using its fixed point, this gives (1 − q^{m+1}(2 + q)) ‖e_k‖ ≤ q^{m+1}(1 + q) η ‖w_k‖. So the error is a small multiple of ‖w_k‖ once q^{m+1} is a small constant.
4. **Potential.** The quantity V_k = k(kμ' − μ)‖g_k‖² + k⟨g_k, y_k − y_1⟩ satisfies the exact identity

    V_k − V_{k+1} = k(k + 1)(⟨g_{k+1} − g_k, y_{k+1} − y_k⟩ − μ‖g_{k+1} − g_k‖²) + (k + 1)²((μ − μ')‖w_k‖² − ⟨w_k, e_k⟩).

   The error enters only through ⟨w_k, e_k⟩, and ‖w_k‖² has a positive coefficient. Step 3 makes the last bracket nonnegative, so V_k is nonincreasing and V_1 ≤ 0.
5. **Rate.** V_n ≤ 0 and step 1 applied to the solution give nμ'‖g_n‖ ≤ ‖y_1 − x*‖ ≤ 4‖x0 − x*‖.

Earlier inexact Halpern analyses need a resolvent accuracy that tightens with the iteration counter. Diakonikolas (2020) uses absolute tolerances. Alacaoglu, Kim and Wright use the relative criterion (2.1), ε_k = γ‖R(x_k)‖/(√(k + 2) log(k + 2)), where R is the fixed-point residual; the factor decays in k, which gives about log k inner steps at iteration k. Here the predictor makes the error proportional to w_k, the one vector the anchored potential can absorb, so a relative accuracy that is constant in k is enough and only shrinks the step s.

## Relation to prior results

| Result | Range | Constraints | Calls for residual ≤ ε |
|---|---|---|---|
| Lee–Kim, FEG, [arXiv:2106.02326](https://arxiv.org/abs/2106.02326), Theorem 4.1 | ρ < 1/(2L) | no | 4LR/((1 − 2ρL)ε) |
| Cai–Oikonomou–Zheng, [arXiv:2206.05248](https://arxiv.org/abs/2206.05248) (ICML 2024) | ρ < 1/(2L) | yes | O(1/ε) |
| Tran-Dinh, [arXiv:2302.04099](https://arxiv.org/abs/2302.04099); Tran-Dinh and Nguyen-Trung, [arXiv:2501.04585](https://arxiv.org/abs/2501.04585) | 2ρL < 1 or smaller | yes | O(1/ε) |
| Cai–Alacaoglu–Diakonikolas, [arXiv:2310.02987](https://arxiv.org/abs/2310.02987) (ICLR 2024), Corollary 4.5 | ρ < 1/(√2 L) | no | O(1/ε) with a log factor |
| Alacaoglu–Kim–Wright, [arXiv:2402.05071](https://arxiv.org/abs/2402.05071) (ICML 2024), Theorem 2.1 | ρ < 1/L | yes | O(1/ε) with a log factor, for the fixed-point residual; their Remark 2.3 converts it to dist(0, F(x) + H(x)) |
| Pethick–Mavrothalassitis–Cevher (ICLR 2025), Corollary 6.3 | ρ < 1/L, weak MVI | yes | O(1/ε²), best iterate, no log |
| Jiang–Yoon, AEP, [arXiv:2609.30212](https://arxiv.org/abs/2609.30212), Theorem 3.2 | monotone (ρ = 0) | yes | O(LR/ε) |
| This theorem | ρ < 1/L | yes | O((LR/ε)(1 − ρL)⁻² log(e/(1 − ρL))), last iterate, no log in ε |

- **The open question.** Cai, Oikonomou and Zheng state in a footnote that the methods for ρ > −1/L (their sign convention) are double-loop and lose a log factor, and that designing a single-loop algorithm without the log factor is open. Pethick, Mavrothalassitis and Cevher remove the log for the unaccelerated rate and write in their conclusion that integrating their approach with Halpern iteration "could permit an optimal method in the regime ρ ∈ (−1/L, −1/2L] without suffering a logarithmic factor". The theorem here gives the accelerated O(1/ε) rate without the log factor on that regime. It does so with an inner loop of fixed length, so it is not a single-loop method in the sense of the footnote.
- **Alacaoglu–Kim–Wright.** Same assumptions and same full range. Their Theorem 2.1 uses N_k = ⌈4(1 + ηL)/(1 − ηL) · log(98√(k + 2) log(k + 2))⌉ inner steps at iteration k. The inner count here is constant in k. The improvement over their result is the logarithmic factor only: the range, the constraints and the order of the dependence on 1 − ρL are the same.
- **Jiang–Yoon (concurrent, 24 September 2026, unreviewed).** Their anchored extra-proximal framework proves the O(1/k) residual rate for monotone inclusions when the anchored proximal step is solved to a relative error measured against the distance to the extrapolated point. The whole theorem of this note, in its composite form and not only for root finding, can also be derived from their Theorem 3.2: apply it to the monotone operator w ↦ g defined on the realised points w = u + ρg with g ∈ F(u) + H(u), with constant step η − ρ; the anchored subproblem is then solved by the forward-backward contraction, and the contraction lemma of step 3 verifies their relative-error condition. So the relative-error anchoring mechanism is not claimed as new here. Their paper treats the monotone case only and lists the extension to weakly nonmonotone inclusions as future work. The cohypomonotone statement on the full range, with explicit parameters and call count, is the contribution of this note, and its proof here is direct and self-contained.
- **Fast extragradient methods.** For ρL < 1/2 the methods of Lee–Kim and Cai–Oikonomou–Zheng use two calls per iteration and have smaller constants. With the constants proved here, the theorem improves on them only for ρL above roughly 0.498, where their constant 1/(1 − 2ρL) blows up or they do not apply.

## Instances

- Any operator F = M ∘ (I − ρM)⁻¹, with M monotone and ℓ-Lipschitz and ρℓ < 1, is ρ-cohypomonotone and ℓ/(1 − ρℓ)-Lipschitz. This gives nonlinear instances in every dimension with interacting coordinates, for example M the saddle operator of a smooth convex-concave function.
- Interaction-dominant nonconvex-nonconcave min-max problems have negatively comonotone saddle operators (Grimmer, Lu, Worah and Mirrokni; discussed in Lee and Kim).
- Linear maps A = −aI + bJ with J a rotation by a quarter turn have ρL = a/√(a² + b²). For a > 0 they are not monotone, and for a ≥ b they fall in the range ρL ≥ 1/√2 where only the log-factor methods applied.

In one dimension the inner error e_k is collinear with w_k. In higher dimension the two are not aligned and only the norm bound of step 3 is available, which is what the potential uses.

## Limitations

- The dependence (1 − ρL)⁻² log(e/(1 − ρL)) is not claimed to be optimal. The constants 16 and the choice η = (1 + ρL)/(2L) are not optimised.
- The method needs L and ρ, and uses an inner loop of fixed length m + 1.
- The assumption is two-point cohypomonotonicity. The weak Minty condition, which Pethick et al. treat, is not covered.
- Whether ρ < 1/L is the limit for first-order methods is a conjecture in the literature, not a result of this note.
- The result is deterministic. Stochastic oracles are not treated.
- The comparison with Fan, Li and Chen (ICLR 2024), Lee and Kim (2024) and Chen and Luo (2022) relies on the statements reported in the tables of Alacaoglu et al. and Pethick et al.; those papers give unaccelerated or log-factor rates there.
