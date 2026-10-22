import LongTails.Proofs.ScentExpectation
import LongTails.Proofs.ScentAveraging


namespace OracleTemplate.Scent

open MeasureTheory Real
open LongTails.Setups.CompositionalEntropicRisk
open scoped RealInnerProductSpace BigOperators

variable {q : Params} (I : Instance q) {projection : q.E → q.E} {wstar : q.E} (η α : ℝ)
  (h : SysHyp I projection wstar)

section Totals

noncomputable def V1 (q : Params) : ℝ :=
  min (2 * exp (q.c1 - q.c0) * q.σ ^ 2) (exp (2 * (q.c1 - q.c0)) * q.G ^ 2)

noncomputable def vv (projection : q.E → q.E) (wstar : q.E) (ξ : ℕ → Seed q) (t b : ℕ) : ℝ :=
  Vobj I projection η α ξ t b - Fstar I wstar

include h in
lemma Zsq_le_V1 (hα : 0 ≤ α) (t b : ℕ) :
    (∫ ξ, ‖Z I projection η α ξ t b‖ ^ 2 ∂(PP I)) ≤
      V1 q * (1 + ∫ ξ, Vgap I projection η α ξ t b ∂(PP I)) := by
  obtain ⟨_, h1, h2⟩ := Zsq_bounds I η α h hα t b
  have hg : 0 ≤ ∫ ξ, Vgap I projection η α ξ t b ∂(PP I) :=
    integral_nonneg fun ξ => SysHyp.virtualGap_nonneg (q := q) (I := I) α _ _
  unfold V1
  rcases le_total (2 * exp (q.c1 - q.c0) * q.σ ^ 2) (exp (2 * (q.c1 - q.c0)) * q.G ^ 2) with hle | hle
  · rw [min_eq_left hle]; exact h1
  · rw [min_eq_right hle]
    calc _ ≤ exp (2 * (q.c1 - q.c0)) * q.G ^ 2 := h2
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (exp_pos (2 * (q.c1 - q.c0))).le (sq_nonneg q.G)) hg]

include h in
lemma gg_le_vv (hα : 0 ≤ α) (t b : ℕ) :
    (∫ ξ, Vgap I projection η α ξ t b ∂(PP I)) ≤ ∫ ξ, vv I η α projection wstar ξ t b ∂(PP I) :=
  integral_mono (Vgap_int I η α h hα t b) ((Vobj_int I η α h hα t b).sub (integrable_const _))
    (fun ξ => Vgap_le_Vobj I η α h hα ξ t b)

lemma gg_nonneg (t b : ℕ) : 0 ≤ ∫ ξ, Vgap I projection η α ξ t b ∂(PP I) :=
  integral_nonneg fun _ => SysHyp.virtualGap_nonneg (q := q) (I := I) α _ _

include h in
lemma primal_total (hα : 0 ≤ α) (hη : 0 < η) (hB : 0 < q.B) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B,
      (∫ ξ, ⟪Z I projection η α ξ t b, W I projection η α ξ t - wstar⟫ ∂(PP I)) ≤
    (q.B / (2 * η)) * ‖q.w0 - wstar‖ ^ 2 +
    (η / (2 * q.B)) * ∑ t ∈ Finset.range T,
      (2 * ∑ b ∈ Finset.range q.B, (∫ ξ, ‖Z I projection η α ξ t b‖ ^ 2 ∂(PP I)) +
       2 * q.B * ∑ b ∈ Finset.range q.B, ∫ ξ, ‖M I projection η α ξ t b‖ ^ 2 ∂(PP I)) := by
  have hstep : ∀ t, ∑ b ∈ Finset.range q.B,
      (∫ ξ, ⟪Z I projection η α ξ t b, W I projection η α ξ t - wstar⟫ ∂(PP I)) ≤
      (q.B / (2 * η)) * ((∫ ξ, ‖W I projection η α ξ t - wstar‖ ^ 2 ∂(PP I)) -
        ∫ ξ, ‖W I projection η α ξ (t + 1) - wstar‖ ^ 2 ∂(PP I)) +
      (η / (2 * q.B)) * (2 * ∑ b ∈ Finset.range q.B, (∫ ξ, ‖Z I projection η α ξ t b‖ ^ 2 ∂(PP I)) +
       2 * q.B * ∑ b ∈ Finset.range q.B, ∫ ξ, ‖M I projection η α ξ t b‖ ^ 2 ∂(PP I)) := by
    intro t
    rw [sum_inner_eq I η α h hα t]
    have h1 := inner_Acc_le I η α h hα hη hB t
    have h2 := Accsq_total I η α h hα t
    have hηB : 0 ≤ η / (2 * q.B) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hηB]
  have htel : ∀ T', ∑ t ∈ Finset.range T', ∑ b ∈ Finset.range q.B,
      (∫ ξ, ⟪Z I projection η α ξ t b, W I projection η α ξ t - wstar⟫ ∂(PP I)) ≤
      (q.B / (2 * η)) * ((∫ ξ, ‖W I projection η α ξ 0 - wstar‖ ^ 2 ∂(PP I)) -
        ∫ ξ, ‖W I projection η α ξ T' - wstar‖ ^ 2 ∂(PP I)) +
      (η / (2 * q.B)) * ∑ t ∈ Finset.range T',
        (2 * ∑ b ∈ Finset.range q.B, (∫ ξ, ‖Z I projection η α ξ t b‖ ^ 2 ∂(PP I)) +
         2 * q.B * ∑ b ∈ Finset.range q.B, ∫ ξ, ‖M I projection η α ξ t b‖ ^ 2 ∂(PP I)) := by
    intro T'
    induction T' with
    | zero => simp
    | succ T' ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun t => 2 * ∑ b ∈ Finset.range q.B,
        (∫ ξ, ‖Z I projection η α ξ t b‖ ^ 2 ∂(PP I)) + 2 * q.B * ∑ b ∈ Finset.range q.B,
        ∫ ξ, ‖M I projection η α ξ t b‖ ^ 2 ∂(PP I))]
      have := hstep T'
      nlinarith
  have hT := htel T
  have hW0 : (∫ ξ, ‖W I projection η α ξ 0 - wstar‖ ^ 2 ∂(PP I)) = ‖q.w0 - wstar‖ ^ 2 := by
    simp [W_zero]
  have hnn : 0 ≤ ∫ ξ, ‖W I projection η α ξ T - wstar‖ ^ 2 ∂(PP I) :=
    integral_nonneg fun ξ => sq_nonneg _
  have hBη : 0 ≤ q.B / (2 * η) := by positivity
  rw [hW0] at hT
  nlinarith [mul_le_mul_of_nonneg_left hnn hBη]

include h in
lemma total_bound (hα : 0 < α) {ρ : ℝ} (hρ : α * exp q.c1 ≤ ρ) (hη : 0 < η) (hB : 0 < q.B) (T : ℕ) :
    let K2 := 2 * (1 + ρ) * (q.κ - 1) * exp q.c1
    let C := (1 + ρ) * (1 + (q.c1 - q.c0))
    let D0 := dualPot (nuStar I wstar) (fun _ => q.c1)
    let Vtot := ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B, ∫ ξ, vv I η α projection wstar ξ t b ∂(PP I)
    let qq := η * V1 q / q.B + 4 * η * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 + C * α * K2
    Vtot ≤ q.B * ‖q.w0 - wstar‖ ^ 2 / (2 * η) +
      (T * q.B) * (η * V1 q / q.B + 2 * η * q.κ * q.G ^ 2 + C * α * K2) + D0 / α + qq * Vtot := by
  intro K2 C D0 Vtot qq
  have hα0 : 0 ≤ α := hα.le
  set gg : ℕ → ℕ → ℝ := fun t b => ∫ ξ, Vgap I projection η α ξ t b ∂(PP I) with hgg
  have hgg_le : ∀ t b, gg t b ≤ ∫ ξ, vv I η α projection wstar ξ t b ∂(PP I) := fun t b => gg_le_vv I η α h hα0 t b
  have hgg_nn : ∀ t b, 0 ≤ gg t b := fun t b => gg_nonneg I η α t b
  set Gtot := ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B, gg t b with hGtot
  have hG_le : Gtot ≤ Vtot := Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun b _ => hgg_le t b
  have h1 : Vtot ≤ ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B,
      (∫ ξ, ⟪Z I projection η α ξ t b, W I projection η α ξ t - wstar⟫ ∂(PP I)) +
      ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B, ∫ ξ, Reg I projection η α wstar ξ t b ∂(PP I) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro t _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro b _
    exact vv_le_inner_reg I η α h hα0 t b
  have h2 := primal_total I η α h hα0 hη hB T
  have hZ : ∀ t b, (∫ ξ, ‖Z I projection η α ξ t b‖ ^ 2 ∂(PP I)) ≤ V1 q * (1 + gg t b) :=
    fun t b => Zsq_le_V1 I η α h hα0 t b
  have hM : ∀ t b, (∫ ξ, ‖M I projection η α ξ t b‖ ^ 2 ∂(PP I)) ≤
      2 * q.κ * q.G ^ 2 + 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 * gg t b :=
    fun t b => (Msq_bound I η α h hα0 t b).2
  have hV1 : 0 ≤ V1 q := by
    unfold V1; exact le_min (by positivity) (by positivity)
  set gt : ℕ → ℝ := fun t => ∑ b ∈ Finset.range q.B, gg t b with hgt
  have hGtot' : Gtot = ∑ t ∈ Finset.range T, gt t := rfl
  have hinner : ∀ t, 2 * ∑ b ∈ Finset.range q.B, (∫ ξ, ‖Z I projection η α ξ t b‖ ^ 2 ∂(PP I)) +
      2 * q.B * ∑ b ∈ Finset.range q.B, ∫ ξ, ‖M I projection η α ξ t b‖ ^ 2 ∂(PP I) ≤
      2 * V1 q * (q.B + gt t) + 2 * q.B * (2 * q.κ * q.G ^ 2 * q.B +
        4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 * gt t) := by
    intro t
    have hz : ∑ b ∈ Finset.range q.B, (∫ ξ, ‖Z I projection η α ξ t b‖ ^ 2 ∂(PP I)) ≤
        V1 q * (q.B + gt t) := by
      calc _ ≤ ∑ b ∈ Finset.range q.B, V1 q * (1 + gg t b) := Finset.sum_le_sum fun b _ => hZ t b
        _ = V1 q * (q.B + gt t) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
              nsmul_eq_mul, mul_one]
    have hm : ∑ b ∈ Finset.range q.B, (∫ ξ, ‖M I projection η α ξ t b‖ ^ 2 ∂(PP I)) ≤
        2 * q.κ * q.G ^ 2 * q.B + 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 * gt t := by
      calc _ ≤ ∑ b ∈ Finset.range q.B, (2 * q.κ * q.G ^ 2 + 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 * gg t b) :=
            Finset.sum_le_sum fun b _ => hM t b
        _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
            ring
    have hBnn : (0 : ℝ) ≤ q.B := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 2 * q.B)]
  have hsumQ : ∑ t ∈ Finset.range T,
      (2 * ∑ b ∈ Finset.range q.B, (∫ ξ, ‖Z I projection η α ξ t b‖ ^ 2 ∂(PP I)) +
       2 * q.B * ∑ b ∈ Finset.range q.B, ∫ ξ, ‖M I projection η α ξ t b‖ ^ 2 ∂(PP I)) ≤
      2 * V1 q * (T * q.B + Gtot) + 2 * q.B * (2 * q.κ * q.G ^ 2 * (T * q.B) +
        4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 * Gtot) := by
    calc _ ≤ ∑ t ∈ Finset.range T, (2 * V1 q * (q.B + gt t) + 2 * q.B * (2 * q.κ * q.G ^ 2 * q.B +
          4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 * gt t)) := Finset.sum_le_sum fun t _ => hinner t
      _ = _ := by
          rw [hGtot', Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
          ring
  have h4 := dual_telescope I η α h hα0 hρ T
  have hDn : ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B, (∫ ξ, Dnoise I projection η α ξ t b ∂(PP I)) ≤
      K2 * (T * q.B + Gtot) := by
    have hper : ∀ t b, (∫ ξ, Dnoise I projection η α ξ t b ∂(PP I)) ≤ K2 * (1 + gg t b) :=
      fun t b => (Dnoise_bound I η α h hα0 hρ t b).2
    have := Finset.sum_le_sum fun t (_ : t ∈ Finset.range T) =>
      Finset.sum_le_sum fun b (_ : b ∈ Finset.range q.B) => hper t b
    have heq : ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B, K2 * (1 + gg t b) =
        K2 * (T * q.B + Gtot) := by
      simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one, hGtot]
      simp only [hgt, Finset.mul_sum]
      ring
    rw [heq] at this
    exact this
  have hK2 : 0 ≤ K2 := by
    have := h.hκ
    have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
    positivity
  have hC : 0 ≤ C := by
    have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
    have := h.hc
    positivity
  have hreg : ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B, (∫ ξ, Reg I projection η α wstar ξ t b ∂(PP I)) ≤
      D0 / α + C * α * K2 * (T * q.B + Gtot) := by
    have hα' := hα
    have h4' : α * ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B,
        (∫ ξ, Reg I projection η α wstar ξ t b ∂(PP I)) ≤ D0 + C * α ^ 2 * (K2 * (T * q.B + Gtot)) := by
      have := mul_le_mul_of_nonneg_left hDn (by positivity : 0 ≤ (1 + ρ) * (1 + (q.c1 - q.c0)) * α ^ 2)
      linarith
    rw [← le_div_iff₀' hα'] at h4'
    calc _ ≤ (D0 + C * α ^ 2 * (K2 * (T * q.B + Gtot))) / α := h4'
      _ = D0 / α + C * α * K2 * (T * q.B + Gtot) := by field_simp
  have hBpos : (0 : ℝ) < q.B := by exact_mod_cast hB
  have hcomb : Vtot ≤ q.B * ‖q.w0 - wstar‖ ^ 2 / (2 * η) +
      (η / (2 * q.B)) * (2 * V1 q * (T * q.B + Gtot) + 2 * q.B * (2 * q.κ * q.G ^ 2 * (T * q.B) +
        4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 * Gtot)) +
      (D0 / α + C * α * K2 * (T * q.B + Gtot)) := by
    have hηB : 0 ≤ η / (2 * q.B) := by positivity
    have := mul_le_mul_of_nonneg_left hsumQ hηB
    have e : q.B / (2 * η) * ‖q.w0 - wstar‖ ^ 2 = q.B * ‖q.w0 - wstar‖ ^ 2 / (2 * η) := by ring
    linarith
  have hexp : (η / (2 * q.B)) * (2 * V1 q * (T * q.B + Gtot) + 2 * q.B * (2 * q.κ * q.G ^ 2 * (T * q.B) +
      4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 * Gtot)) + (D0 / α + C * α * K2 * (T * q.B + Gtot)) =
      (T * q.B) * (η * V1 q / q.B + 2 * η * q.κ * q.G ^ 2 + C * α * K2) + D0 / α + qq * Gtot := by
    simp only [qq]
    field_simp
    ring
  have hqq : 0 ≤ qq := by
    simp only [qq]
    have := h.hκ
    positivity
  have hG' := mul_le_mul_of_nonneg_left hG_le hqq
  linarith [hcomb, hexp, hG']

include h in
lemma D0_le : dualPot (nuStar I wstar) (fun _ => q.c1) ≤ q.n * exp (-q.c0) := by
  unfold dualPot
  calc ∑ i, breg (nuStar I wstar i) q.c1 ≤ ∑ _i : Fin q.n, exp (-q.c0) := by
        apply Finset.sum_le_sum; intro i _
        have hm := h.nuStar_mem i
        unfold breg
        have h1 : exp (-(nuStar I wstar i)) ≤ exp (-q.c0) := exp_le_exp.mpr (by linarith [hm.1])
        have h2 : exp (-q.c1) * (nuStar I wstar i - q.c1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (by linarith [hm.2])
        linarith [exp_pos (-q.c1)]
    _ = q.n * exp (-q.c0) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

include h in
lemma average_mem (hT : 0 < T) (ξ : ℕ → Seed q) : average I projection η α ξ T ∈ I.domain := by
  unfold average
  rw [Finset.smul_sum]
  refine h.convex.sum_mem (fun k _ => inv_nonneg.mpr (Nat.cast_nonneg _)) ?_
    (fun k _ => W_mem I η α h ξ k)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast hT.ne')

include h in
lemma expected_gap (hα : 0 < α) {ρ : ℝ} (hρ : α * exp q.c1 ≤ ρ) (hη : 0 < η) (hB : 0 < q.B)
    {T : ℕ} (hT : 0 < T)
    (hqq : η * V1 q / q.B + 4 * η * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 +
      (1 + ρ) * (1 + (q.c1 - q.c0)) * α * (2 * (1 + ρ) * (q.κ - 1) * exp q.c1) ≤ 1 / 2) :
    Integrable (fun ξ => objective I (average I projection η α ξ T) - objective I wstar) (PP I) ∧
    (∫ ξ, objective I (average I projection η α ξ T) - objective I wstar ∂(PP I)) ≤
      ‖q.w0 - wstar‖ ^ 2 / (η * T) +
      2 * (η * V1 q / q.B + 2 * η * q.κ * q.G ^ 2 +
        (1 + ρ) * (1 + (q.c1 - q.c0)) * α * (2 * (1 + ρ) * (q.κ - 1) * exp q.c1)) +
      2 * q.n * exp (-q.c0) / (α * T * q.B) := by
  have hα0 : 0 ≤ α := hα.le
  have hmeas : Measurable (fun ξ => average I projection η α ξ T) := measurable_average I η α h T
  have hint : Integrable (fun ξ => objective I (average I projection η α ξ T) - objective I wstar) (PP I) := by
    refine Integrable.of_bound (((measurable_objective I h).comp hmeas).sub measurable_const).aestronglyMeasurable
      (2 * (|q.c0| + |q.c1|)) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]
    have h1 := objective_bounds I h (average_mem I η α h hT ξ)
    have h2 := objective_bounds I h h.wstar_mem
    rw [abs_le]; constructor <;> cases abs_cases q.c0 <;> cases abs_cases q.c1 <;> linarith
  refine ⟨hint, ?_⟩
  set s := Finset.range T ×ˢ Finset.range q.B with hs
  have hcard : (s.card : ℝ) = T * q.B := by rw [hs, Finset.card_product, Finset.card_range, Finset.card_range]; push_cast; rfl
  have hTB : (0 : ℝ) < T * q.B := by
    have : (0 : ℝ) < T := by exact_mod_cast hT
    have : (0 : ℝ) < q.B := by exact_mod_cast hB
    positivity
  have hpt : ∀ ξ, 1 + objective I (average I projection η α ξ T) ≤
      (T * q.B : ℝ)⁻¹ * ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B, Vobj I projection η α ξ t b := by
    intro ξ
    have hb := h.average_bound s (by rw [hs, Finset.card_product, Finset.card_range, Finset.card_range]; positivity)
      (fun p => W I projection η α ξ p.1) (fun p _ => W_mem I η α h ξ p.1)
      (fun p => Nb I projection η α ξ p.1 p.2) hα0 (fun p _ i => Nb_mem I η α h hα0 ξ p.1 p.2 i)
    have havg : (s.card : ℝ)⁻¹ • ∑ p ∈ s, W I projection η α ξ p.1 = average I projection η α ξ T := by
      rw [hs, Finset.sum_product]
      simp only [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ]
      rw [← Finset.smul_sum, smul_smul, ← hs, hcard]
      unfold average W
      congr 1
      field_simp
    rw [havg, hcard, hs, Finset.sum_product] at hb
    exact hb
  have hVint : ∀ t b, Integrable (fun ξ => Vobj I projection η α ξ t b) (PP I) := fun t b => Vobj_int I η α h hα0 t b
  have hsum_int : Integrable (fun ξ => (T * q.B : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B, Vobj I projection η α ξ t b) (PP I) :=
    (integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun b _ => hVint t b).const_mul _
  have hint1 : Integrable (fun ξ => 1 + objective I (average I projection η α ξ T)) (PP I) := by
    have : (fun ξ => 1 + objective I (average I projection η α ξ T)) =
        fun ξ => (objective I (average I projection η α ξ T) - objective I wstar) + (1 + objective I wstar) := by
      funext ξ; ring
    rw [this]; exact hint.add (integrable_const _)
  have hmono := integral_mono hint1 hsum_int hpt
  have hL : (∫ ξ, (1 + objective I (average I projection η α ξ T)) ∂(PP I)) =
      (∫ ξ, objective I (average I projection η α ξ T) - objective I wstar ∂(PP I)) + Fstar I wstar := by
    have e1 : (∫ ξ, ((objective I (average I projection η α ξ T) - objective I wstar) +
        (1 + objective I wstar)) ∂(PP I)) =
        (∫ ξ, objective I (average I projection η α ξ T) - objective I wstar ∂(PP I)) +
        ∫ _ξ, (1 + objective I wstar) ∂(PP I) := integral_add hint (integrable_const _)
    rw [integral_const, probReal_univ, one_smul] at e1
    have e2 : (fun ξ => 1 + objective I (average I projection η α ξ T)) =
        fun ξ => (objective I (average I projection η α ξ T) - objective I wstar) + (1 + objective I wstar) := by
      funext ξ; ring
    rw [e2, e1]
    unfold Fstar
    rw [h.fstar_eq]
  have hR : (∫ ξ, (T * q.B : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B, Vobj I projection η α ξ t b ∂(PP I)) =
      (T * q.B : ℝ)⁻¹ * ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B,
        ∫ ξ, Vobj I projection η α ξ t b ∂(PP I) := by
    rw [integral_const_mul, integral_finsetSum _ (fun t _ => integrable_finsetSum _ fun b _ => hVint t b)]
    congr 1
    apply Finset.sum_congr rfl; intro t _
    rw [integral_finsetSum _ fun b _ => hVint t b]
  have hvv : ∀ t b, (∫ ξ, vv I η α projection wstar ξ t b ∂(PP I)) =
      (∫ ξ, Vobj I projection η α ξ t b ∂(PP I)) - Fstar I wstar := by
    intro t b
    unfold vv
    rw [integral_sub (hVint t b) (integrable_const _), integral_const, probReal_univ, one_smul]
  set Vtot := ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B,
    ∫ ξ, vv I η α projection wstar ξ t b ∂(PP I) with hVtot
  have hVtot_eq : Vtot = (∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B,
      ∫ ξ, Vobj I projection η α ξ t b ∂(PP I)) - (T * q.B) * Fstar I wstar := by
    rw [hVtot]
    simp only [hvv, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hgap : (∫ ξ, objective I (average I projection η α ξ T) - objective I wstar ∂(PP I)) ≤
      (T * q.B : ℝ)⁻¹ * Vtot := by
    rw [hVtot_eq, mul_sub, ← mul_assoc, inv_mul_cancel₀ hTB.ne', one_mul]
    linarith [hmono, hL, hR]
  have hVnn : 0 ≤ Vtot := by
    rw [hVtot]
    refine Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun b _ => ?_
    exact le_trans (gg_nonneg I η α t b) (gg_le_vv I η α h hα0 t b)
  have htot := total_bound I η α h hα hρ hη hB T
  simp only at htot
  set X := q.B * ‖q.w0 - wstar‖ ^ 2 / (2 * η) +
      (T * q.B) * (η * V1 q / q.B + 2 * η * q.κ * q.G ^ 2 +
        (1 + ρ) * (1 + (q.c1 - q.c0)) * α * (2 * (1 + ρ) * (q.κ - 1) * exp q.c1)) +
      dualPot (nuStar I wstar) (fun _ => q.c1) / α with hX
  have hV2 : Vtot ≤ 2 * X := by
    have hq0 : 0 ≤ η * V1 q / q.B + 4 * η * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 +
        (1 + ρ) * (1 + (q.c1 - q.c0)) * α * (2 * (1 + ρ) * (q.κ - 1) * exp q.c1) := by
      have := h.hκ
      have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
      have := h.hc
      have hV1 : 0 ≤ V1 q := by unfold V1; exact le_min (by positivity) (by positivity)
      positivity
    have := mul_le_mul_of_nonneg_right hqq hVnn
    rw [hX]
    linarith [htot]
  have hD := D0_le I h
  have hBpos : (0 : ℝ) < q.B := by exact_mod_cast hB
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  calc (∫ ξ, objective I (average I projection η α ξ T) - objective I wstar ∂(PP I))
      ≤ (T * q.B : ℝ)⁻¹ * Vtot := hgap
    _ ≤ (T * q.B : ℝ)⁻¹ * (2 * X) := mul_le_mul_of_nonneg_left hV2 (inv_nonneg.mpr hTB.le)
    _ = ‖q.w0 - wstar‖ ^ 2 / (η * T) +
        2 * (η * V1 q / q.B + 2 * η * q.κ * q.G ^ 2 +
          (1 + ρ) * (1 + (q.c1 - q.c0)) * α * (2 * (1 + ρ) * (q.κ - 1) * exp q.c1)) +
        2 * dualPot (nuStar I wstar) (fun _ => q.c1) / (α * T * q.B) := by
        rw [hX]; field_simp
    _ ≤ _ := by
        have h2 : 2 * dualPot (nuStar I wstar) (fun _ => q.c1) / (α * T * q.B) ≤
            2 * q.n * exp (-q.c0) / (α * T * q.B) :=
          div_le_div_of_nonneg_right (by linarith [hD]) (by positivity)
        linarith

lemma tuning {ε L1 L2 K C e1 D Dbar R B T : ℝ} (hε : 0 < ε) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (he1 : 0 < e1) (hD : 0 ≤ D) (hDbar : D ≤ Dbar) (_hR : 0 ≤ R)
    (hB : 0 < B) (hT0 : 0 < T)
    (hT : 32 * L1 * R ^ 2 / ε ^ 2 + 16 * L2 * R ^ 2 / ε + 8 * Dbar * e1 / (B * ε) +
      64 * C * K * Dbar / (B * ε ^ 2) + 32 * C * K * Dbar / (B * ε) ≤ T) :
    let η := 1 / (8 * L1 / ε + 4 * L2)
    let α := 1 / (e1 + 8 * C * K / ε + 4 * C * K)
    0 < η ∧ 0 < α ∧ α * e1 ≤ 1 ∧ η * L2 + C * α * K ≤ 1 / 2 ∧
    R ^ 2 / (η * T) + 2 * (η * L1 + C * α * K) + 2 * D / (α * T * B) ≤ ε := by
  intro η α
  set dη := 8 * L1 / ε + 4 * L2 with hdη
  set dα := e1 + 8 * C * K / ε + 4 * C * K with hdα
  have hdηpos : 0 < dη := by rw [hdη]; positivity
  have hdαpos : 0 < dα := by rw [hdα]; positivity
  have hη : 0 < η := by simp only [η]; positivity
  have hα : 0 < α := by simp only [α]; positivity
  have hη1 : η * dη = 1 := by show 1 / dη * dη = 1; exact one_div_mul_cancel hdηpos.ne'
  have hα1 : α * dα = 1 := by show 1 / dα * dα = 1; exact one_div_mul_cancel hdαpos.ne'
  have eη : ε * dη = 8 * L1 + ε * (4 * L2) := by
    have : ε * (8 * L1 / ε) = 8 * L1 := by field_simp
    rw [hdη, mul_add, this]
  have eα : ε * dα = ε * e1 + 8 * C * K + ε * (4 * C * K) := by
    have : ε * (8 * C * K / ε) = 8 * C * K := by field_simp
    rw [hdα, mul_add, mul_add, this]
  have hCK : 0 ≤ C * K := mul_nonneg hC hK
  have hDbar0 : 0 ≤ Dbar := le_trans hD hDbar
  have hq1 : 0 ≤ 8 * L1 / ε := by positivity
  have hq2 : 0 ≤ 8 * C * K / ε := by positivity
  have hεL2 : 0 ≤ ε * L2 := mul_nonneg hε.le hL2.le
  have hεCK : 0 ≤ ε * (C * K) := mul_nonneg hε.le hCK
  have hεe1 : 0 ≤ ε * e1 := mul_nonneg hε.le he1.le
  have hαe : α * e1 ≤ 1 := by
    have : e1 ≤ dα := by rw [hdα]; linarith
    calc α * e1 ≤ α * dα := mul_le_mul_of_nonneg_left this hα.le
      _ = 1 := hα1
  have hηL2 : η * L2 ≤ 1 / 4 := by
    have h1 : 4 * L2 ≤ dη := by rw [hdη]; linarith
    calc η * L2 = η * (4 * L2) / 4 := by ring
      _ ≤ η * dη / 4 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hη.le) (by norm_num)
      _ = 1 / 4 := by rw [hη1]
  have hαCK : C * α * K ≤ 1 / 4 := by
    have h2 : 4 * (C * K) ≤ dα := by rw [hdα]; linarith
    calc C * α * K = α * (4 * (C * K)) / 4 := by ring
      _ ≤ α * dα / 4 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hα.le) (by norm_num)
      _ = 1 / 4 := by rw [hα1]
  have hA : η * L1 ≤ ε / 8 := by
    have h8 : 8 * L1 ≤ ε * dη := by rw [eη]; linarith
    calc η * L1 = η * (8 * L1) / 8 := by ring
      _ ≤ η * (ε * dη) / 8 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h8 hη.le) (by norm_num)
      _ = ε / 8 := by rw [show η * (ε * dη) = ε * (η * dη) by ring, hη1, mul_one]
  have hBd : C * α * K ≤ ε / 8 := by
    have h8 : 8 * (C * K) ≤ ε * dα := by rw [eα]; linarith
    calc C * α * K = α * (8 * (C * K)) / 8 := by ring
      _ ≤ α * (ε * dα) / 8 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h8 hα.le) (by norm_num)
      _ = ε / 8 := by rw [show α * (ε * dα) = ε * (α * dα) by ring, hα1, mul_one]
  have hrest : 0 ≤ 8 * Dbar * e1 / (B * ε) + 64 * C * K * Dbar / (B * ε ^ 2) +
      32 * C * K * Dbar / (B * ε) := by positivity
  have hfirst : 0 ≤ 32 * L1 * R ^ 2 / ε ^ 2 + 16 * L2 * R ^ 2 / ε := by positivity
  have hT1 : 4 * R ^ 2 * dη ≤ ε * T := by
    have e : ε * (32 * L1 * R ^ 2 / ε ^ 2 + 16 * L2 * R ^ 2 / ε) = 4 * R ^ 2 * dη := by
      rw [hdη]; field_simp
      try ring
    calc 4 * R ^ 2 * dη = ε * (32 * L1 * R ^ 2 / ε ^ 2 + 16 * L2 * R ^ 2 / ε) := e.symm
      _ ≤ ε * T := by apply mul_le_mul_of_nonneg_left _ hε.le; linarith
  have hT2 : 8 * Dbar * dα ≤ ε * T * B := by
    have e : ε * B * (8 * Dbar * e1 / (B * ε) + 64 * C * K * Dbar / (B * ε ^ 2) +
        32 * C * K * Dbar / (B * ε)) = 8 * Dbar * dα := by
      rw [hdα]; field_simp
      try ring
    calc 8 * Dbar * dα = ε * B * (8 * Dbar * e1 / (B * ε) + 64 * C * K * Dbar / (B * ε ^ 2) +
          32 * C * K * Dbar / (B * ε)) := e.symm
      _ ≤ ε * B * T := by apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ = ε * T * B := by ring
  have hC1 : R ^ 2 / (η * T) ≤ ε / 4 := by
    rw [div_le_iff₀ (by positivity)]
    calc R ^ 2 = η * (4 * R ^ 2 * dη) / 4 := by
          rw [show η * (4 * R ^ 2 * dη) / 4 = R ^ 2 * (η * dη) by ring, hη1, mul_one]
      _ ≤ η * (ε * T) / 4 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hT1 hη.le) (by norm_num)
      _ = ε / 4 * (η * T) := by ring
  have hC2 : 2 * D / (α * T * B) ≤ ε / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have hDd : 8 * D * dα ≤ 8 * Dbar * dα :=
      mul_le_mul_of_nonneg_right (by linarith) hdαpos.le
    calc 2 * D = α * (8 * D * dα) / 4 := by
          rw [show α * (8 * D * dα) / 4 = 2 * D * (α * dα) by ring, hα1, mul_one]
      _ ≤ α * (ε * T * B) / 4 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (le_trans hDd hT2) hα.le) (by norm_num)
      _ = ε / 4 * (α * T * B) := by ring
  refine ⟨hη, hα, hαe, by linarith, by linarith⟩

end Totals

section Tuning

noncomputable def horizon (q : Params) : ℕ :=
  ⌈(64 * q.κ * q.G ^ 2 * q.R ^ 2 * (1 + exp (q.c1 - q.c0) * q.ε) +
    32 * min (2 * exp (q.c1 - q.c0) * q.σ ^ 2) (exp (2 * (q.c1 - q.c0)) * q.G ^ 2) * q.R ^ 2 * (1 + q.ε) / q.B +
    8 * q.n * exp (q.c1 - q.c0) * (1 + 64 * (1 + (q.c1 - q.c0)) * (q.κ - 1)) * (1 + q.ε) / q.B) / q.ε ^ 2⌉₊

noncomputable def stepSize (q : Params) : ℝ :=
  1 / (8 * (V1 q / q.B + 2 * q.κ * q.G ^ 2) / q.ε + 4 * (V1 q / q.B + 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2))

noncomputable def dualStep (q : Params) : ℝ :=
  1 / (exp q.c1 + 8 * (2 * (1 + (q.c1 - q.c0))) * (4 * (q.κ - 1) * exp q.c1) / q.ε +
    4 * (2 * (1 + (q.c1 - q.c0))) * (4 * (q.κ - 1) * exp q.c1))

lemma horizon_bound (q : Params) (hB : 0 < q.B) (hc : q.c0 ≤ q.c1) (hG : 0 < q.G) (hκ : 1 ≤ q.κ)
    (_hσ : 0 ≤ q.σ) (_hR : 0 ≤ q.R) (hε : 0 < q.ε) :
    0 < horizon q ∧
    32 * (V1 q / q.B + 2 * q.κ * q.G ^ 2) * q.R ^ 2 / q.ε ^ 2 +
      16 * (V1 q / q.B + 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2) * q.R ^ 2 / q.ε +
      8 * (q.n * exp (-q.c0)) * exp q.c1 / (q.B * q.ε) +
      64 * (2 * (1 + (q.c1 - q.c0))) * (4 * (q.κ - 1) * exp q.c1) * (q.n * exp (-q.c0)) / (q.B * q.ε ^ 2) +
      32 * (2 * (1 + (q.c1 - q.c0))) * (4 * (q.κ - 1) * exp q.c1) * (q.n * exp (-q.c0)) / (q.B * q.ε) ≤
      horizon q := by
  have hBr : (0 : ℝ) < q.B := by exact_mod_cast hB
  have hn : (1 : ℝ) ≤ q.n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q.n)
  have hV : 0 ≤ V1 q := by unfold V1; exact le_min (by positivity) (by positivity)
  have hΔ : 0 ≤ q.c1 - q.c0 := sub_nonneg.mpr hc
  have hκ' : 0 ≤ q.κ - 1 := sub_nonneg.mpr hκ
  have hE : exp (q.c1 - q.c0) = exp q.c1 * exp (-q.c0) := by rw [← exp_add]; ring_nf
  set X := (64 * q.κ * q.G ^ 2 * q.R ^ 2 * (1 + exp (q.c1 - q.c0) * q.ε) +
    32 * min (2 * exp (q.c1 - q.c0) * q.σ ^ 2) (exp (2 * (q.c1 - q.c0)) * q.G ^ 2) * q.R ^ 2 * (1 + q.ε) / q.B +
    8 * q.n * exp (q.c1 - q.c0) * (1 + 64 * (1 + (q.c1 - q.c0)) * (q.κ - 1)) * (1 + q.ε) / q.B) / q.ε ^ 2 with hX
  have hXV : X = (64 * q.κ * q.G ^ 2 * q.R ^ 2 * (1 + exp (q.c1 - q.c0) * q.ε) +
      32 * V1 q * q.R ^ 2 * (1 + q.ε) / q.B +
      8 * q.n * exp (q.c1 - q.c0) * (1 + 64 * (1 + (q.c1 - q.c0)) * (q.κ - 1)) * (1 + q.ε) / q.B) / q.ε ^ 2 := rfl
  have hhor : horizon q = ⌈X⌉₊ := rfl
  set E1 := exp q.c1 with hE1
  set E0 := exp (-q.c0) with hE0
  have hE1p : 0 < E1 := exp_pos _
  have hE0p : 0 < E0 := exp_pos _
  have hdiff : X - (32 * (V1 q / q.B + 2 * q.κ * q.G ^ 2) * q.R ^ 2 / q.ε ^ 2 +
      16 * (V1 q / q.B + 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2) * q.R ^ 2 / q.ε +
      8 * (q.n * E0) * E1 / (q.B * q.ε) +
      64 * (2 * (1 + (q.c1 - q.c0))) * (4 * (q.κ - 1) * E1) * (q.n * E0) / (q.B * q.ε ^ 2) +
      32 * (2 * (1 + (q.c1 - q.c0))) * (4 * (q.κ - 1) * E1) * (q.n * E0) / (q.B * q.ε)) =
      (16 * V1 q * q.R ^ 2 * q.ε + 8 * q.n * (E1 * E0) +
        256 * (1 + (q.c1 - q.c0)) * (q.κ - 1) * q.n * (E1 * E0) * q.ε) / (q.B * q.ε ^ 2) := by
    rw [hXV, hE]
    field_simp
    ring
  have hpos : 0 ≤ (16 * V1 q * q.R ^ 2 * q.ε + 8 * q.n * (E1 * E0) +
        256 * (1 + (q.c1 - q.c0)) * (q.κ - 1) * q.n * (E1 * E0) * q.ε) / (q.B * q.ε ^ 2) := by
    apply div_nonneg _ (by positivity)
    have h1 : 0 ≤ 16 * V1 q * q.R ^ 2 * q.ε := by positivity
    have h2 : 0 ≤ 8 * q.n * (E1 * E0) := by positivity
    have h3 : 0 ≤ 256 * (1 + (q.c1 - q.c0)) * (q.κ - 1) * q.n * (E1 * E0) * q.ε := by
      have : 0 ≤ 1 + (q.c1 - q.c0) := by linarith
      positivity
    linarith
  have hXpos : 0 < X := by
    have h3 : 0 < 8 * q.n * exp (q.c1 - q.c0) * (1 + 64 * (1 + (q.c1 - q.c0)) * (q.κ - 1)) * (1 + q.ε) / q.B := by
      have : 0 ≤ 1 + (q.c1 - q.c0) := by linarith
      have : 0 < 1 + 64 * (1 + (q.c1 - q.c0)) * (q.κ - 1) := by positivity
      positivity
    have h1 : 0 ≤ 64 * q.κ * q.G ^ 2 * q.R ^ 2 * (1 + exp (q.c1 - q.c0) * q.ε) := by positivity
    have h2 : 0 ≤ 32 * V1 q * q.R ^ 2 * (1 + q.ε) / q.B := by positivity
    rw [hXV]
    positivity
  refine ⟨?_, ?_⟩
  · rw [hhor]; exact Nat.ceil_pos.mpr hXpos
  · rw [hhor]
    have := Nat.le_ceil X
    linarith [hdiff, hpos]

end Tuning

end OracleTemplate.Scent
