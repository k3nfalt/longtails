import LongTails.Proofs.StochasticQuasarEnvelope
import LongTails.Proofs.NearZeroSumProjection
import LongTails.Algorithms.StochasticQuasarInner
import LongTails.Proofs.FiniteVarianceBatch

open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.StochasticQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma regularized_projection_fixed {Q : Set E} {P : E → E} {f : E → ℝ}
    {g v c : E} {L η : ℝ} (hQ : Convex ℝ Q) (hP : ConstrainedMonotone.Proj Q P)
    (hv : v ∈ Q) (hg : HasGradientAt f g v) (hη : 0 ≤ η)
    (hm : IsMinOn (fun y => f y + L * ‖y - c‖ ^ 2) Q v) :
    P (v - η • (g + (2 * L) • (v - c))) = v := by
  have hn : ConstrainedMonotone.Normal Q v (-(g + (2 * L) • (v - c))) := by
    intro w hw
    rw [inner_neg_left]
    exact neg_nonpos.mpr (regularized_minimizer_normal hQ hv hw hg hm)
  simpa only [smul_neg, sub_eq_add_neg] using NearZeroSum.projection_fixed_of_normal hP hv hn hη

omit [CompleteSpace E] in
lemma inner_noisy_squared {Q : Set E} {P : E → E} {g : E → E}
    {u v c e : E} {L : ℝ} (hP : ConstrainedMonotone.Proj Q P) (hL : 0 < L)
    (hlip : ‖g u - g v‖ ≤ L * ‖u - v‖)
    (hfix : P (v - (1 / (3 * L)) • (g v + (2 * L) • (v - c))) = v) :
    ‖P (u - (1 / (3 * L)) • (g u + (2 * L) • (u - c) + e)) - v‖ ^ 2 ≤
      (4 / 9 : ℝ) * ‖u - v‖ ^ 2 - 2 * (1 / (3 * L)) *
        ⟪(u - (1 / (3 * L)) • (g u + (2 * L) • (u - c))) -
          (v - (1 / (3 * L)) • (g v + (2 * L) • (v - c))), e⟫ +
        (1 / (3 * L)) ^ 2 * ‖e‖ ^ 2 := by
  let d := (u - (1 / (3 * L)) • (g u + (2 * L) • (u - c))) -
    (v - (1 / (3 * L)) • (g v + (2 * L) • (v - c)))
  have hn := NearZeroSum.projection_nonexpansive hP
    (u - (1 / (3 * L)) • (g u + (2 * L) • (u - c) + e))
    (v - (1 / (3 * L)) • (g v + (2 * L) • (v - c)))
  rw [hfix] at hn
  have he : (u - (1 / (3 * L)) • (g u + (2 * L) • (u - c) + e)) -
      (v - (1 / (3 * L)) • (g v + (2 * L) • (v - c))) = d - (1 / (3 * L)) • e := by
    dsimp [d]
    module
  rw [he] at hn
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hd := regularized_gradient_contraction (x := c) hL hlip
  change ‖d‖ ≤ (2 / 3 : ℝ) * ‖u - v‖ at hd
  have hd2 := pow_le_pow_left₀ (norm_nonneg d) hd 2
  rw [norm_sub_sq_real d ((1 / (3 * L)) • e), real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs] at hn2
  change _ ≤ (4 / 9 : ℝ) * ‖u - v‖ ^ 2 - 2 * (1 / (3 * L)) * ⟪d, e⟫ +
    (1 / (3 * L)) ^ 2 * ‖e‖ ^ 2
  nlinarith

lemma inner_integral_squared [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Set E} {P : E → E} {g : E → E} {u v c : E} {L V : ℝ}
    (hP : ConstrainedMonotone.Proj Q P) (hPm : Measurable P) (hL : 0 < L)
    (hlip : ‖g u - g v‖ ≤ L * ‖u - v‖)
    (hfix : P (v - (1 / (3 * L)) • (g v + (2 * L) • (v - c))) = v)
    {e : Ω → E} (hem : Measurable e) (hei : Integrable e μ)
    (he0 : (∫ ω, e ω ∂μ) = 0) (he2 : Integrable (fun ω => ‖e ω‖ ^ 2) μ)
    (hev : (∫ ω, ‖e ω‖ ^ 2 ∂μ) ≤ V) :
    (∫ ω, ‖P (u - (1 / (3 * L)) • (g u + (2 * L) • (u - c) + e ω)) - v‖ ^ 2 ∂μ) ≤
      (4 / 9 : ℝ) * ‖u - v‖ ^ 2 + (1 / (3 * L)) ^ 2 * V := by
  let η := 1 / (3 * L)
  let d := (u - η • (g u + (2 * L) • (u - c))) -
    (v - η • (g v + (2 * L) • (v - c)))
  let C := (4 / 9 : ℝ) * ‖u - v‖ ^ 2
  let F : Ω → ℝ := fun ω => ‖P (u - η • (g u + (2 * L) • (u - c) + e ω)) - v‖ ^ 2
  let B : Ω → ℝ := fun ω => C - 2 * η * ⟪d, e ω⟫ + η ^ 2 * ‖e ω‖ ^ 2
  have hBi : Integrable B μ :=
    ((integrable_const C).sub ((hei.const_inner d).const_mul _)).add (he2.const_mul _)
  have hpt (ω : Ω) : F ω ≤ B ω := inner_noisy_squared hP hL hlip hfix
  have hFm : Measurable F := by
    dsimp [F]
    exact ((hPm.comp (measurable_const.sub
      ((measurable_const.add hem).const_smul η))).sub measurable_const).norm.pow_const 2
  have hFi : Integrable F μ := by
    apply hBi.mono' hFm.aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  have hc : (∫ ω, ⟪d, e ω⟫ ∂μ) = 0 := by
    rw [integral_inner hei, he0, inner_zero_right]
  have hi := integral_mono hFi hBi hpt
  dsimp [B] at hi
  have hadd := integral_add ((integrable_const C).sub
    ((hei.const_inner d).const_mul (2 * η))) (he2.const_mul (η ^ 2))
  have hsub := integral_sub (integrable_const C) ((hei.const_inner d).const_mul (2 * η))
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul, integral_const_mul, hc] at hi
  simp only [integral_const, probReal_univ, one_smul, mul_zero, sub_zero, integral_const_mul] at hi
  exact hi.trans (add_le_add_right (mul_le_mul_of_nonneg_left hev (sq_nonneg η)) C)

lemma inner_batch_integral [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Set E} {P : E → E} {g : E → E} {u v c : E} {L σ : ℝ}
    (hP : ConstrainedMonotone.Proj Q P) (hPm : Measurable P) (hL : 0 < L)
    (hlip : ‖g u - g v‖ ≤ L * ‖u - v‖)
    (hfix : P (v - (1 / (3 * L)) • (g v + (2 * L) • (v - c))) = v)
    {G : Ω → E} (hGm : Measurable G) (hGi : Integrable G μ)
    (hmean : (∫ ω, G ω ∂μ) = g u)
    (hG2 : Integrable (fun ω => ‖G ω - g u‖ ^ 2) μ)
    (hvar : (∫ ω, ‖G ω - g u‖ ^ 2 ∂μ) ≤ σ ^ 2) (b : ℕ) (hb : 0 < b) :
    (∫ ξ : Fin b → Ω, ‖P (u - (1 / (3 * L)) •
      ((1 / (b : ℝ)) • ∑ i, G (ξ i) + (2 * L) • (u - c))) - v‖ ^ 2
      ∂Measure.pi (fun _ : Fin b => μ)) ≤
      (4 / 9 : ℝ) * ‖u - v‖ ^ 2 + (1 / (3 * L)) ^ 2 * (σ ^ 2 / b) := by
  have hm := LightTail.finite_mean_integral hGi b hb
  have hv := RobustGradient.finite_mean_variance hGm hGi (g u) hG2 hmean b hb
  let e : (Fin b → Ω) → E := fun ξ => (1 / (b : ℝ)) • ∑ i, G (ξ i) - g u
  have hem : Measurable e := by
    apply Measurable.sub _ measurable_const
    apply Measurable.const_smul
    exact Finset.measurable_sum _ (fun i _ => hGm.comp (measurable_pi_apply i))
  have hei : Integrable e (Measure.pi fun _ : Fin b => μ) := hm.1.sub (integrable_const _)
  have he0 : (∫ ξ, e ξ ∂Measure.pi (fun _ : Fin b => μ)) = 0 := by
    dsimp [e]
    rw [integral_sub hm.1 (integrable_const _), hm.2, hmean]
    simp
  have hev : (∫ ξ, ‖e ξ‖ ^ 2 ∂Measure.pi (fun _ : Fin b => μ)) ≤ σ ^ 2 / b := by
    rw [hv.2]
    exact div_le_div_of_nonneg_right hvar (Nat.cast_nonneg b)
  have hh := inner_integral_squared hP hPm hL hlip hfix hem hei he0 hv.1 hev
  have he (ξ : Fin b → Ω) : g u + (2 * L) • (u - c) + e ξ =
      (1 / (b : ℝ)) • ∑ i, G (ξ i) + (2 * L) • (u - c) := by dsimp [e]; abel
  simpa only [he] using hh

lemma two_step_radius {r a b d : ℝ} (ha : a ≤ 4 * r ^ 2)
    (hb : b ≤ (4 / 9 : ℝ) * a + r ^ 2 / 9)
    (hd : d ≤ (4 / 9 : ℝ) * b + r ^ 2 / 9) : d ≤ (77 / 81 : ℝ) * r ^ 2 := by
  linarith

lemma inner_stage_target {D r : ℝ} (hr : 0 < r) :
    D / (2 : ℝ) ^ innerStageCount D r ≤ r := by
  have hn := Nat.le_pow_clog (by decide : 1 < 2) ⌈D / r⌉₊
  have hc : D / r ≤ (2 : ℝ) ^ innerStageCount D r := by
    calc
      D / r ≤ (⌈D / r⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (2 : ℝ) ^ innerStageCount D r := by exact_mod_cast hn
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ innerStageCount D r)).2
  have hh := (div_le_iff₀ hr).1 hc
  nlinarith

lemma inner_stage_zero {D r : ℝ} (hr : 0 < r) (hDr : D ≤ r) :
    innerStageCount D r = 0 := by
  apply Nat.clog_of_right_le_one
  apply Nat.ceil_le.mpr
  simpa using (div_le_one hr).mpr hDr

lemma inner_batch_positive (L σ D : ℝ) (j : ℕ) : 0 < innerBatch L σ D j := by
  unfold innerBatch
  omega

lemma inner_batch_noise {L σ D : ℝ} {j : ℕ} (hL : 0 < L) (hD : 0 < D) :
    σ ^ 2 / (innerBatch L σ D j : ℝ) ≤ L ^ 2 * innerRadius D j ^ 2 := by
  have hr : 0 < innerRadius D j := by unfold innerRadius; positivity
  have hb : (0 : ℝ) < innerBatch L σ D j := by exact_mod_cast inner_batch_positive L σ D j
  have hc : σ ^ 2 / (L ^ 2 * innerRadius D j ^ 2) ≤ (innerBatch L σ D j : ℝ) := by
    apply (Nat.le_ceil _).trans
    apply Nat.cast_le.mpr
    exact le_max_right _ _
  have hh := (div_le_iff₀ (by positivity : 0 < L ^ 2 * innerRadius D j ^ 2)).1 hc
  exact (div_le_iff₀ hb).2 (by nlinarith)

lemma inner_stage_calls_bound (L σ D : ℝ) (j : ℕ) :
    (innerStageCalls L σ D j : ℝ) ≤ 4 + 2 * σ ^ 2 / (L ^ 2 * innerRadius D j ^ 2) := by
  have hv : 0 ≤ σ ^ 2 / (L ^ 2 * innerRadius D j ^ 2) := by positivity
  have hc := (Nat.ceil_lt_add_one hv).le
  have hb : (innerBatch L σ D j : ℝ) ≤ 1 + σ ^ 2 / (L ^ 2 * innerRadius D j ^ 2) := by
    unfold innerBatch
    rw [Nat.cast_max, Nat.cast_one]
    apply max_le
    · linarith
    · linarith
  unfold innerStageCalls
  push_cast
  have he : 2 * σ ^ 2 / (L ^ 2 * innerRadius D j ^ 2) =
      2 * (σ ^ 2 / (L ^ 2 * innerRadius D j ^ 2)) := by ring
  rw [he]
  linarith

lemma inner_calls_geometric {L σ D : ℝ} (hL : 0 < L) (hD : 0 < D) (k : ℕ) :
    (innerCalls L σ D k : ℝ) ≤ 4 * k +
      (8 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * D ^ 2) * ((4 : ℝ) ^ k - 1) := by
  induction k with
  | zero => simp [innerCalls]
  | succ k ih =>
    have hs := inner_stage_calls_bound L σ D k
    have he : 2 * σ ^ 2 / (L ^ 2 * innerRadius D k ^ 2) =
        8 * σ ^ 2 / (L ^ 2 * D ^ 2) * (4 : ℝ) ^ k := by
      unfold innerRadius
      have hp : ((2 : ℝ) ^ (k + 1)) ^ 2 = 4 * (4 : ℝ) ^ k := by
        rw [← pow_mul, Nat.mul_comm (k + 1) 2, pow_mul]
        norm_num
        ring
      rw [div_pow]
      field_simp
      rw [hp]
      ring
    rw [he] at hs
    rw [innerCalls, Nat.cast_add]
    push_cast
    rw [pow_succ (4 : ℝ) k]
    ring_nf at hs ih ⊢
    linarith

lemma inner_stage_power_lt {D r : ℝ} (hr : 0 < r) (hDr : r < D) :
    (2 : ℝ) ^ innerStageCount D r < 2 * D / r := by
  have hx : (1 : ℝ) < D / r := (one_lt_div hr).mpr hDr
  have hn : 1 < ⌈D / r⌉₊ := Nat.lt_ceil.mpr (by simpa using hx)
  have hk : 0 < innerStageCount D r := Nat.clog_pos (by decide) hn
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn
  have hc : (2 : ℝ) ^ (innerStageCount D r).pred < D / r := by
    have hh := Nat.lt_ceil.mp hp
    simpa only [innerStageCount, Nat.cast_pow, Nat.cast_ofNat] using hh
  have he : innerStageCount D r = (innerStageCount D r).pred + 1 :=
    (Nat.succ_pred_eq_of_pos hk).symm
  rw [he, pow_succ]
  have hm := mul_lt_mul_of_pos_left hc (by norm_num : (0 : ℝ) < 2)
  convert hm using 1 <;> ring

lemma inner_calls_accuracy {L σ D r : ℝ} (hL : 0 < L) (hr : 0 < r) (hDr : r < D) :
    (innerCalls L σ D (innerStageCount D r) : ℝ) ≤
      4 * innerStageCount D r + (32 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * r ^ 2) := by
  have hD : 0 < D := hr.trans hDr
  have hg := inner_calls_geometric (σ := σ) hL hD (innerStageCount D r)
  have hp := inner_stage_power_lt hr hDr
  have hp2 := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ) ^ innerStageCount D r) hp.le 2
  have he : ((2 : ℝ) ^ innerStageCount D r) ^ 2 = (4 : ℝ) ^ innerStageCount D r := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [he] at hp2
  have hm := mul_le_mul_of_nonneg_left hp2
    (by positivity : 0 ≤ (8 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * D ^ 2))
  have hb : (8 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * D ^ 2) * (2 * D / r) ^ 2 =
      (32 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * r ^ 2) := by
    field_simp
    ring
  rw [hb] at hm
  have hn : 0 ≤ (8 / 3 : ℝ) * σ ^ 2 / (L ^ 2 * D ^ 2) := by positivity
  nlinarith

end OracleTemplate.StochasticQuasar
