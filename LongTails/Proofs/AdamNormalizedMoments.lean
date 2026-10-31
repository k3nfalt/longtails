import LongTails.Proofs.AdamNormalizedKernel
import LongTails.Proofs.AdamHeavyTailedTrajectory
import LongTails.Proofs.TerminalClippingEnergy
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdamNormalizedMoments

open OracleTemplate.Adam AdamNormalizedKernel

noncomputable def normalized {d : ℕ} (a : Fin d → ℝ) (γ τ : ℝ) (x : Point d) : Point d :=
  WithLp.toLp 2 (fun i => kernel (a i) γ τ (x i))

lemma norm_le_coordinate_sum {d : ℕ} (x : Point d) : ‖x‖ ≤ ∑ i, |x i| := by
  have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (x i))
  have he : ‖x‖ ^ 2 = ∑ i, |x i| ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs]
  have hn : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  nlinarith [norm_nonneg x]

lemma measurable_normalized {d : ℕ} (a : Fin d → ℝ) (γ τ : ℝ) :
    Measurable (normalized a γ τ) := by
  apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
  apply Measurable.of_eval
  intro i
  dsimp [kernel]
  fun_prop

lemma normalized_square_bound {d : ℕ} {a : Fin d → ℝ} {γ τ : ℝ}
    (ha : ∀ i, 0 < a i) (hγ : 0 < γ) (hτ : 0 ≤ τ) (x : Point d) :
    ‖normalized a γ τ x‖ ^ 2 ≤ (d : ℝ) / γ := by
  have hr := Real.sq_sqrt hγ.le
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ _i : Fin d, (1 / Real.sqrt γ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _)
        (abs_kernel_le (ha i) hγ hτ (x i)) 2
    _ = _ := by simp [hr, div_eq_mul_inv]

lemma normalized_sub_square {d : ℕ} {a : Fin d → ℝ} {A γ τ : ℝ}
    (hA : 0 < A) (ha : ∀ i, A ≤ a i) (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    (x y : Point d) :
    ‖normalized a γ τ x - normalized a γ τ y‖ ^ 2 ≤ ‖x - y‖ ^ 2 / A := by
  have hai (i) : 0 < a i := hA.trans_le (ha i)
  have hAi : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hcoord (i) : |kernel (a i) γ τ (x i) - kernel (a i) γ τ (y i)| ≤
      (1 / Real.sqrt A) * |x i - y i| := by
    apply (kernel_sub_le (hai i) hγ hτ (x i) (y i)).trans
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact one_div_le_one_div_of_le hAi (Real.sqrt_le_sqrt (ha i))
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have hh := pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2
  simpa only [normalized, PiLp.sub_apply, PiLp.toLp_apply, mul_pow, div_pow,
    one_pow, Real.sq_sqrt hA.le, one_div_mul_eq_div] using hh

lemma integrable_normalized {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → Point d} (hg : Measurable g) (hi : Integrable g P)
    {a : Fin d → ℝ} {γ τ : ℝ} (ha : ∀ i, 0 < a i) (hγ : 0 ≤ γ) (hτ : 0 ≤ τ) :
    Integrable (fun ω => normalized a γ τ (g ω)) P := by
  apply Integrable.of_eval_piLp
  intro i
  exact integrable_kernel ((measurable_coordinate i).comp hg) (hi.eval_piLp i) (ha i) hγ hτ

lemma coordinate_noise_integrable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → Point d} (hg : Measurable g) (h : Point d)
    (h2 : Integrable (fun ω => ‖g ω - h‖ ^ 2) P) (i : Fin d) :
    Integrable (fun ω => (g ω i - h i) ^ 2) P := by
  apply h2.mono'
    ((((measurable_coordinate i).comp hg).sub_const (h i)).pow_const 2).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hh := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (g ω - h) i) 2
  simpa only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs, Function.comp_def] using hh

lemma integral_normalized_bias {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {g : Ω → Point d} (hg : Measurable g) (hi : Integrable g P)
    {h : Point d} (hmean : (∫ ω, g ω ∂P) = h)
    (h2 : Integrable (fun ω => ‖g ω - h‖ ^ 2) P)
    {a : Fin d → ℝ} {A γ τ : ℝ} (hA : 0 < A) (ha : ∀ i, A ≤ a i)
    (hγ : 0 ≤ γ) (hτ : 0 ≤ τ) :
    ‖(∫ ω, normalized a γ τ (g ω) ∂P) - normalized a γ τ h‖ ≤
      (3 * Real.sqrt γ / A) * ∫ ω, ‖g ω - h‖ ^ 2 ∂P := by
  have hai (i) : 0 < a i := hA.trans_le (ha i)
  have hk := integrable_normalized hg hi hai hγ hτ
  have hcoord (i : Fin d) :
      |((∫ ω, normalized a γ τ (g ω) ∂P) - normalized a γ τ h) i| ≤
        (3 * Real.sqrt γ / A) * ∫ ω, (g ω i - h i) ^ 2 ∂P := by
    have hp := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).integral_comp_comm hi
    have hmean' : (∫ ω, g ω i ∂P) = h i := by
      change (∫ ω, g ω i ∂P) = (∫ ω, g ω ∂P) i at hp
      simpa only [hmean] using hp
    have hb := integral_kernel_bias ((measurable_coordinate i).comp hg) (hi.eval_piLp i)
      (hai i) hγ hτ hmean' (coordinate_noise_integrable hg h h2 i)
    have hp' := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).integral_comp_comm hk
    change (∫ ω, kernel (a i) γ τ (g ω i) ∂P) =
      (∫ ω, normalized a γ τ (g ω) ∂P) i at hp'
    change |(∫ ω, normalized a γ τ (g ω) ∂P) i - kernel (a i) γ τ (h i)| ≤ _
    rw [← hp']
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun ω => sq_nonneg _)
    exact div_le_div_of_nonneg_left (by positivity) hA (ha i)
  calc
    _ ≤ ∑ i, |((∫ ω, normalized a γ τ (g ω) ∂P) - normalized a γ τ h) i| :=
      norm_le_coordinate_sum _
    _ ≤ ∑ i, (3 * Real.sqrt γ / A) * ∫ ω, (g ω i - h i) ^ 2 ∂P :=
      Finset.sum_le_sum (fun i _ => hcoord i)
    _ = (3 * Real.sqrt γ / A) * ∫ ω, ‖g ω - h‖ ^ 2 ∂P := by
      rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => coordinate_noise_integrable hg h h2 i)]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ω
      simp only [PiLp.norm_sq_eq_of_L2, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]

lemma integral_normalized_variance {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {g : Ω → Point d} (hg : Measurable g) (hi : Integrable g P)
    (h : Point d) (h2 : Integrable (fun ω => ‖g ω - h‖ ^ 2) P)
    {a : Fin d → ℝ} {A γ τ : ℝ} (hA : 0 < A) (ha : ∀ i, A ≤ a i)
    (hγ : 0 ≤ γ) (hτ : 0 ≤ τ) :
    Integrable (fun ω => ‖normalized a γ τ (g ω) -
      ∫ u, normalized a γ τ (g u) ∂P‖ ^ 2) P ∧
    (∫ ω, ‖normalized a γ τ (g ω) - ∫ u, normalized a γ τ (g u) ∂P‖ ^ 2 ∂P) ≤
      (∫ ω, ‖g ω - h‖ ^ 2 ∂P) / A := by
  let Y := fun ω => normalized a γ τ (g ω) - normalized a γ τ h
  have hk := integrable_normalized hg hi (fun i => hA.trans_le (ha i)) hγ hτ
  have hYi : Integrable Y P := hk.sub (integrable_const _)
  have hYm : Measurable Y := ((measurable_normalized a γ τ).comp hg).sub measurable_const
  have hY2 : Integrable (fun ω => ‖Y ω‖ ^ 2) P := (h2.div_const A).mono'
    (hYm.norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact normalized_sub_square hA ha hγ hτ (g ω) h)
  have hh := OracleTemplate.TerminalClipping.centered_second_moment hYi hY2
  have he (ω) : Y ω - ∫ u, Y u ∂P =
      normalized a γ τ (g ω) - ∫ u, normalized a γ τ (g u) ∂P := by
    dsimp [Y]
    rw [integral_sub hk (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
    abel
  simp only [he] at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hb := integral_mono hY2 (h2.div_const A)
    (fun ω => normalized_sub_square hA ha hγ hτ (g ω) h)
  simpa only [integral_div] using hb

lemma inner_normalized {d : ℕ} (a : Fin d → ℝ) (γ τ : ℝ) (h : Point d) :
    ⟪h, normalized a γ τ h⟫ = ∑ i, (h i) ^ 2 / (Real.sqrt (a i + γ * (h i) ^ 2) + τ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, normalized, kernel]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma inner_normalized_nonneg {d : ℕ} {a : Fin d → ℝ} {γ τ : ℝ}
    (hτ : 0 ≤ τ) (h : Point d) : 0 ≤ ⟪h, normalized a γ τ h⟫ := by
  rw [inner_normalized]
  exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (by positivity))

lemma gradient_square_from_signal {d : ℕ} {a : Fin d → ℝ} {γ τ D : ℝ} (h : Point d)
    (hden : ∀ i, 0 < Real.sqrt (a i + γ * (h i) ^ 2) + τ)
    (hD : ∀ i, Real.sqrt (a i + γ * (h i) ^ 2) + τ ≤ D) :
    ‖h‖ ^ 2 ≤ D * ⟪h, normalized a γ τ h⟫ := by
  rw [inner_normalized, Finset.mul_sum, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro i _
  simp only [Real.norm_eq_abs, sq_abs]
  have hh := mul_le_mul_of_nonneg_right (hD i)
    (div_nonneg (sq_nonneg (h i)) (hden i).le)
  have he : (Real.sqrt (a i + γ * (h i) ^ 2) + τ) *
      ((h i) ^ 2 / (Real.sqrt (a i + γ * (h i) ^ 2) + τ)) = (h i) ^ 2 := by
    field_simp [(hden i).ne']
  rwa [he] at hh

section Pairing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma centered_pairing_mean {Y : Ω → E} (hY : Integrable Y P) (u : E) (α : ℝ) :
    (∫ ω, -α * ⟪u, Y ω - ∫ v, Y v ∂P⟫ ∂P) = 0 := by
  have hcenter : Integrable (fun ω => Y ω - ∫ v, Y v ∂P) P :=
    hY.sub (integrable_const _)
  rw [integral_const_mul, integral_inner hcenter u,
    integral_sub hY (integrable_const (∫ v, Y v ∂P))]
  simp

omit [CompleteSpace E] in
lemma centered_pairing_variance {Y : Ω → E} (hY : Integrable Y P)
    (h2 : Integrable (fun ω => ‖Y ω - ∫ v, Y v ∂P‖ ^ 2) P)
    {V : ℝ} (hV : (∫ ω, ‖Y ω - ∫ v, Y v ∂P‖ ^ 2 ∂P) ≤ V) (u : E) (α : ℝ) :
    Integrable (fun ω => (-α * ⟪u, Y ω - ∫ v, Y v ∂P⟫) ^ 2) P ∧
      (∫ ω, (-α * ⟪u, Y ω - ∫ v, Y v ∂P⟫) ^ 2 ∂P) ≤ α ^ 2 * ‖u‖ ^ 2 * V := by
  have hc : 0 ≤ α ^ 2 * ‖u‖ ^ 2 := by positivity
  have hp (ω) : (-α * ⟪u, Y ω - ∫ v, Y v ∂P⟫) ^ 2 ≤
      (α ^ 2 * ‖u‖ ^ 2) * ‖Y ω - ∫ v, Y v ∂P‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm u (Y ω - ∫ v, Y v ∂P)) 2
    rw [sq_abs, mul_pow] at hh
    have ht := mul_le_mul_of_nonneg_left hh (sq_nonneg α)
    nlinarith
  have hcenter : Integrable (fun ω => Y ω - ∫ v, Y v ∂P) P :=
    hY.sub (integrable_const _)
  have hui : Integrable (fun ω => -α * ⟪u, Y ω - ∫ v, Y v ∂P⟫) P :=
    (hcenter.const_inner u).const_mul (-α)
  have hmeas := hui.aestronglyMeasurable
  have hi := (h2.const_mul (α ^ 2 * ‖u‖ ^ 2)).mono' (hmeas.pow 2)
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hp ω)
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi (h2.const_mul (α ^ 2 * ‖u‖ ^ 2)) hp
  rw [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hV hc)

omit [CompleteSpace E] in
lemma centered_pairing_abs {Y : Ω → E} {B : ℝ}
    (hB : ∀ ω, ‖Y ω‖ ≤ B) (u : E) (α : ℝ) (ω : Ω) :
    |-α * ⟪u, Y ω - ∫ v, Y v ∂P⟫| ≤ 2 * |α| * ‖u‖ * B := by
  have hm : ‖∫ v, Y v ∂P‖ ≤ B := by
    have hh := norm_integral_le_of_norm_le (f := Y) (μ := P) (integrable_const B) (Filter.Eventually.of_forall hB)
    simpa using hh
  have hd : ‖Y ω - ∫ v, Y v ∂P‖ ≤ 2 * B :=
    (norm_sub_le _ _).trans (by linarith [hB ω])
  have hh := mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm u _).trans
    (mul_le_mul_of_nonneg_left hd (norm_nonneg u))) (abs_nonneg α)
  rw [abs_mul, abs_neg]
  nlinarith

end Pairing

end LongTails.Proofs.AdamNormalizedMoments
