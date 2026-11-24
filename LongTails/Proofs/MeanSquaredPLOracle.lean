import LongTails.Proofs.MeanSquaredPLSecret
import LongTails.Proofs.ThirdOrderMaskedScaling

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.MeanSquaredPLOracle

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open LongTails.Proofs.ThirdOrderMaskedOracle LongTails.Proofs.ThirdOrderMaskedScaling
open LongTails.Proofs.MeanSquaredPLMask LongTails.Proofs.MeanSquaredPLSecret
open LongTails.Proofs.RelativeHessianSimulation (axes axes_orthonormal)
open LongTails.Proofs.AbcHardOracle (coin unif Scale toUnit coin_integral coin_integrable
  coin_measurable toUnit_norm_sub)

variable {d n : ℕ}

noncomputable def plReply (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d)
    (ω : ℝ) : Space d :=
  (S.a / S.lam) • unitReply π (toUnit S x0 x) (coin q ω)

noncomputable def plSim (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (R : ℕ) (x0 x : Space d)
    (ω : ℝ) : Space d :=
  (S.a / S.lam) • unitSim R π (toUnit S x0 x) (coin q ω)

noncomputable def scaledSecret (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    Space d :=
  (S.a / S.lam) • secret π (toUnit S x0 x)

lemma plReply_eq (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) (ω : ℝ) :
    plReply S q π x0 x ω = objGrad S π x0 x + (coin q ω - 1) • scaledSecret S π x0 x := by
  unfold plReply unitReply objGrad scaledSecret
  rw [smul_add, smul_comm]

lemma scaledSecret_norm (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    ‖scaledSecret S π x0 x‖ ≤ 2 ^ 51 * (S.a / S.lam) := by
  have hpos : 0 ≤ S.a / S.lam := by have := S.ha; have := S.hlam; positivity
  unfold scaledSecret
  rw [norm_smul, Real.norm_of_nonneg hpos, mul_comm]
  exact mul_le_mul_of_nonneg_right (secret_bound' π _) hpos

lemma scaledSecret_lipschitz (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x y : Space d) :
    ‖scaledSecret S π x0 x - scaledSecret S π x0 y‖ ≤ 2 ^ 58 * S.a / S.lam ^ 2 * ‖x - y‖ := by
  have ha := S.ha
  have hl := S.hlam
  unfold scaledSecret
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
  have h := secret_lipschitz π (toUnit S x0 x) (toUnit S x0 y)
  rw [toUnit_norm_sub] at h
  calc _ ≤ S.a / S.lam * (2 ^ 58 * (‖x - y‖ / S.lam)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

lemma coin_sq (q ω : ℝ) : coin q ω ^ 2 = coin q ω * (1 / q) := by
  unfold coin
  split_ifs <;> ring

lemma coin_expand (q ω : ℝ) (u v : Space d) :
    ‖u + (coin q ω - 1) • v‖ ^ 2 =
      ‖u - v‖ ^ 2 + coin q ω * (2 * ⟪u - v, v⟫ + ‖v‖ ^ 2 / q) := by
  have he : u + (coin q ω - 1) • v = (u - v) + coin q ω • v := by
    rw [sub_smul, one_smul]
    abel
  rw [he, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    coin_sq]
  ring

lemma coin_second_moment (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (u v : Space d) :
    Integrable (fun ω => ‖u + (coin q ω - 1) • v‖ ^ 2) unif ∧
      ∫ ω, ‖u + (coin q ω - 1) • v‖ ^ 2 ∂unif = ‖u‖ ^ 2 + (1 / q - 1) * ‖v‖ ^ 2 := by
  have he : (fun ω => ‖u + (coin q ω - 1) • v‖ ^ 2) = fun ω =>
      ‖u - v‖ ^ 2 + coin q ω * (2 * ⟪u - v, v⟫ + ‖v‖ ^ 2 / q) :=
    funext (fun ω => coin_expand q ω u v)
  have hi : Integrable (fun ω => coin q ω * (2 * ⟪u - v, v⟫ + ‖v‖ ^ 2 / q)) unif :=
    (coin_integrable q).mul_const _
  rw [he]
  refine ⟨(integrable_const _).add hi, ?_⟩
  rw [integral_add (integrable_const _) hi, integral_mul_const, coin_integral q hq0 hq1]
  simp only [integral_const, probReal_univ, one_smul, one_mul]
  rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq]
  ring

lemma plReply_integrable (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    Integrable (plReply S q π x0 x) unif := by
  have he : plReply S q π x0 x = fun ω =>
      objGrad S π x0 x + (coin q ω - 1) • scaledSecret S π x0 x :=
    funext (fun ω => plReply_eq S q π x0 x ω)
  rw [he]
  exact (integrable_const _).add (((coin_integrable q).sub (integrable_const 1)).smul_const _)

lemma plReply_integral (S : Scale) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    ∫ ω, plReply S q π x0 x ω ∂unif = objGrad S π x0 x := by
  have he : plReply S q π x0 x = fun ω =>
      objGrad S π x0 x + (coin q ω - 1) • scaledSecret S π x0 x :=
    funext (fun ω => plReply_eq S q π x0 x ω)
  have hc1 : Integrable (fun ω => coin q ω - 1) unif :=
    (coin_integrable q).sub (integrable_const 1)
  rw [he]
  calc ∫ ω, (objGrad S π x0 x + (coin q ω - 1) • scaledSecret S π x0 x) ∂unif
      = ∫ ω, objGrad S π x0 x ∂unif + ∫ ω, (coin q ω - 1) • scaledSecret S π x0 x ∂unif :=
        integral_add (integrable_const _) (hc1.smul_const _)
    _ = objGrad S π x0 x + (∫ ω, (coin q ω - 1) ∂unif) • scaledSecret S π x0 x := by
        rw [integral_smul_const]
        simp
    _ = objGrad S π x0 x := by
        rw [integral_sub (coin_integrable q) (integrable_const 1), coin_integral q hq0 hq1]
        simp

lemma plReply_variance (S : Scale) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    Integrable (fun ω => ‖plReply S q π x0 x ω - objGrad S π x0 x‖ ^ 2) unif ∧
      ∫ ω, ‖plReply S q π x0 x ω - objGrad S π x0 x‖ ^ 2 ∂unif ≤
        (1 / q - 1) * (2 ^ 51 * (S.a / S.lam)) ^ 2 := by
  have he : (fun ω => ‖plReply S q π x0 x ω - objGrad S π x0 x‖ ^ 2) = fun ω =>
      ‖(0 : Space d) + (coin q ω - 1) • scaledSecret S π x0 x‖ ^ 2 := by
    funext ω
    rw [plReply_eq, add_sub_cancel_left, zero_add]
  obtain ⟨h1, h2⟩ := coin_second_moment q hq0 hq1 (0 : Space d) (scaledSecret S π x0 x)
  rw [he]
  refine ⟨h1, ?_⟩
  rw [h2, norm_zero]
  have hq : 0 ≤ 1 / q - 1 := by
    rw [sub_nonneg, le_div_iff₀ hq0]
    linarith
  have hs := scaledSecret_norm S π x0 x
  have hs0 := norm_nonneg (scaledSecret S π x0 x)
  have hsq : ‖scaledSecret S π x0 x‖ ^ 2 ≤ (2 ^ 51 * (S.a / S.lam)) ^ 2 :=
    pow_le_pow_left₀ hs0 hs 2
  nlinarith [mul_le_mul_of_nonneg_left hsq hq]

lemma plReply_mss (S : Scale) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (π : Fin (n + 1) ↪ Fin d) (x0 x y : Space d) :
    Integrable (fun ω => ‖plReply S q π x0 x ω - plReply S q π x0 y ω‖ ^ 2) unif ∧
      ∫ ω, ‖plReply S q π x0 x ω - plReply S q π x0 y ω‖ ^ 2 ∂unif ≤
        (2 ^ 59 * S.a / S.lam ^ 2) ^ 2 / q * ‖x - y‖ ^ 2 := by
  have ha := S.ha
  have hl := S.hlam
  have he : (fun ω => ‖plReply S q π x0 x ω - plReply S q π x0 y ω‖ ^ 2) = fun ω =>
      ‖(objGrad S π x0 x - objGrad S π x0 y) +
        (coin q ω - 1) • (scaledSecret S π x0 x - scaledSecret S π x0 y)‖ ^ 2 := by
    funext ω
    rw [plReply_eq, plReply_eq, smul_sub]
    congr 2
    abel
  obtain ⟨h1, h2⟩ := coin_second_moment q hq0 hq1 (objGrad S π x0 x - objGrad S π x0 y)
    (scaledSecret S π x0 x - scaledSecret S π x0 y)
  rw [he]
  refine ⟨h1, ?_⟩
  rw [h2]
  have hq : 0 ≤ 1 / q - 1 := by
    rw [sub_nonneg, le_div_iff₀ hq0]
    linarith
  have hG : ‖objGrad S π x0 x - objGrad S π x0 y‖ ≤ 2 ^ 55 * S.a / S.lam ^ 2 * ‖x - y‖ := by
    have h := objective_gradient_lipschitz S π x0 x y
    rwa [objective_gradient, objective_gradient] at h
  have hSec := scaledSecret_lipschitz S π x0 x y
  have hG2 : ‖objGrad S π x0 x - objGrad S π x0 y‖ ^ 2 ≤
      (2 ^ 55 * S.a / S.lam ^ 2 * ‖x - y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG 2
  have hS2 : ‖scaledSecret S π x0 x - scaledSecret S π x0 y‖ ^ 2 ≤
      (2 ^ 58 * S.a / S.lam ^ 2 * ‖x - y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hSec 2
  set ρ := S.a / S.lam ^ 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have e1 : (2 : ℝ) ^ 55 * S.a / S.lam ^ 2 = 2 ^ 55 * ρ := by rw [hρ]; ring
  have e2 : (2 : ℝ) ^ 58 * S.a / S.lam ^ 2 = 2 ^ 58 * ρ := by rw [hρ]; ring
  have e3 : (2 : ℝ) ^ 59 * S.a / S.lam ^ 2 = 2 ^ 59 * ρ := by rw [hρ]; ring
  rw [e1] at hG2
  rw [e2] at hS2
  rw [e3]
  set X := ‖x - y‖ ^ 2 with hX
  have hX0 : 0 ≤ X := sq_nonneg _
  have t1 : ‖objGrad S π x0 x - objGrad S π x0 y‖ ^ 2 ≤ 2 ^ 110 * ρ ^ 2 * X := by
    refine hG2.trans (le_of_eq ?_)
    rw [hX]
    ring
  have t2 : (1 / q - 1) * ‖scaledSecret S π x0 x - scaledSecret S π x0 y‖ ^ 2 ≤
      (1 / q - 1) * (2 ^ 116 * ρ ^ 2 * X) := by
    apply mul_le_mul_of_nonneg_left _ hq
    refine hS2.trans (le_of_eq ?_)
    rw [hX]
    ring
  have hinv : 1 ≤ 1 / q := by
    rw [le_div_iff₀ hq0]
    linarith
  have hρX : 0 ≤ ρ ^ 2 * X := by positivity
  have t3 : (2 ^ 59 * ρ) ^ 2 / q * X = 2 ^ 118 * (1 / q) * (ρ ^ 2 * X) := by
    ring
  rw [t3]
  nlinarith [mul_le_mul_of_nonneg_right hinv hρX]

lemma scaledSecret_continuous (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d) :
    Continuous (scaledSecret S π x0) := by
  unfold scaledSecret
  exact ((secret_continuous π).comp (toUnit_continuous S x0)).const_smul (S.a / S.lam)

lemma plReply_measurable (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d) :
    Measurable (Function.uncurry (plReply S q π x0)) := by
  have he : Function.uncurry (plReply S q π x0) = fun z : Space d × ℝ =>
      objGrad S π x0 z.1 + (coin q z.2 - 1) • scaledSecret S π x0 z.1 := by
    funext z
    exact plReply_eq S q π x0 z.1 z.2
  rw [he]
  have ho : Measurable (fun z : Space d × ℝ => objGrad S π x0 z.1) :=
    (objGrad_continuous S π x0).measurable.comp measurable_fst
  have hs : Measurable (fun z : Space d × ℝ => scaledSecret S π x0 z.1) :=
    (scaledSecret_continuous S π x0).measurable.comp measurable_fst
  have hc : Measurable (fun z : Space d × ℝ => coin q z.2 - 1) :=
    ((coin_measurable q).comp measurable_snd).sub_const 1
  exact ho.add (hc.smul hs)

end LongTails.Proofs.MeanSquaredPLOracle
