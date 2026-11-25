import LongTails.Setups.FiniteLogisticTwoTap
import LongTails.Proofs.GatedEscapeGaussian
import LongTails.Proofs.NormalizedStormMoments

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.TwoTapGaussianBounds

lemma normalized_slab {x a b R k : ℝ} (ha : 1 / 2 ≤ |a|) (hb : |b| ≤ R)
    (hk : 0 ≤ k) (hk' : k ≤ 1 / 4) (h : |a*x + b| ≤ k * (|x| + R)) :
    |x + b/a| ≤ 12*k*R := by
  have hR := (abs_nonneg b).trans hb
  have h₁ : |a| * |x| ≤ |a*x+b| + R := by
    rw [← abs_mul]
    have ht := abs_sub (a*x+b) b
    rw [add_sub_cancel_right] at ht
    linarith
  have hab : |a*x+b| ≤ 6*k*R := by
    have hx' : |x| ≤ 2 * |a*x+b| + 2*R := by
      nlinarith [mul_le_mul_of_nonneg_right ha (abs_nonneg x)]
    nlinarith [mul_le_mul_of_nonneg_left hx' hk,
      mul_le_mul_of_nonneg_right hk' (abs_nonneg (a*x+b))]
  have ha' : a ≠ 0 := abs_pos.mp (by linarith)
  have he : x + b/a = (a*x+b)/a := by field_simp
  rw [he, abs_div, div_le_iff₀ (abs_pos.mpr ha')]
  nlinarith [mul_le_mul_of_nonneg_right ha (show 0 ≤ 12*k*R by positivity)]

lemma fiber_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Set (ℝ × Ω)) (hS : MeasurableSet S) (R : Ω → ℝ) (hR : Integrable R P)
    (hR₀ : ∀ y, 0 ≤ R y) (hdiam : ∀ y a a', (a,y) ∈ S → (a',y) ∈ S → |a-a'| ≤ 2 * R y) :
    ((gaussianReal 0 1).prod P) S ≤ ENNReal.ofReal (∫ y, R y ∂P) := by
  rw [Measure.prod_apply_symm hS, ofReal_integral_eq_lintegral_ofReal hR
    (Filter.Eventually.of_forall hR₀)]
  apply lintegral_mono
  intro y
  simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
    GatedEscapeGaussian.gaussianReal_le_of_diam ((fun a => (a,y)) ⁻¹' S) (fun a ha a' ha' => hdiam y a a' ha ha')

lemma mean_norm_pi (n : ℕ) :
    (∫ y : Fin n → ℝ, ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤ Real.sqrt n := by
  let E := EuclideanSpace ℝ (Fin n)
  have hm := @map_pi_eq_stdGaussian (Fin n) _
  rw [← integral_map (by fun_prop : AEMeasurable (WithLp.toLp 2 : (Fin n → ℝ) → E) _)
    (by fun_prop : AEStronglyMeasurable (fun x : E => ‖x‖) _), hm]
  have hb := OracleTemplate.NormalizedStorm.integral_norm_le_sqrt
    (μ := stdGaussian E) (f := fun x : E => x) (by fun_prop)
    ((IsGaussian.memLp_two_id (μ := stdGaussian E)).integrable_norm_pow (by norm_num))
  simpa [GatedEscapeGaussian.integral_norm_sq_stdGaussian, E] using hb

lemma angular_strip {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}
    (b : OrthonormalBasis (Fin (n+1)) ℝ E) (j : Fin (n+1)) (L : E →L[ℝ] ℝ)
    (hL : ‖L‖ ≤ 1) (hj : 1 / 2 ≤ |L (b j)|) {k : ℝ} (hk : 0 ≤ k) (hk' : k ≤ 1 / 4) :
    stdGaussian E {w | |L w| ≤ k * ‖w‖} ≤ ENNReal.ofReal (12*k*Real.sqrt n) := by
  classical
  let P := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j
  let v := fun y : Fin n → ℝ => ∑ t, y t • b (j.succAbove t)
  let R := fun y : Fin n → ℝ => ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖
  have hv (y) : ‖v y‖ = R y := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖v y‖ ^ 2 = ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ ^ 2
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
    have ho := b.orthonormal.comp j.succAbove j.succAbove_right_injective
    simpa [v, pow_two] using ho.inner_sum y y Finset.univ
  let f := fun x : Fin (n+1) → ℝ => ∑ t, x t • b t
  have hf : Measurable f := by dsimp [f]; fun_prop
  let S := {w : E | |L w| ≤ k * ‖w‖}
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) (by fun_prop)
  change stdGaussian E S ≤ _
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, Measure.map_apply hf hS]
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) j).symm
  rw [← hp.measure_preimage (hf hS).nullMeasurableSet]
  change ((gaussianReal 0 1).prod P) (e.symm ⁻¹' (f ⁻¹' S)) ≤ _
  have hR : Integrable R P := by
    have hm : P.map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin n)) :=
      map_pi_eq_stdGaussian
    apply (integrable_map_measure (μ := P) (f := WithLp.toLp 2)
      (g := fun w : EuclideanSpace ℝ (Fin n) => ‖w‖) (by fun_prop) (by fun_prop)).mp
    rw [hm]
    exact IsGaussian.integrable_id.norm
  refine (fiber_bound P _ (e.symm.measurable (hf hS)) (fun y => 12*k*R y)
    (hR.const_mul _) (fun _ => mul_nonneg (by positivity) (norm_nonneg _)) ?_).trans ?_
  · intro y a a' ha ha'
    have H (t : ℝ) (ht : (t,y) ∈ e.symm ⁻¹' (f ⁻¹' S)) :
        |t + L (v y) / L (b j)| ≤ 12*k*R y := by
      have hsum : f (e.symm (t,y)) = t • b j + v y := by
        unfold f v
        rw [Fin.sum_univ_succAbove _ j]
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      change |L (f (e.symm (t,y)))| ≤ k * ‖f (e.symm (t,y))‖ at ht
      rw [hsum, map_add, map_smul, smul_eq_mul, mul_comm t] at ht
      refine normalized_slab hj ?_ hk hk' ?_
      · calc |L (v y)| ≤ ‖L‖ * ‖v y‖ := L.le_opNorm _
             _ ≤ R y := by rw [hv]; nlinarith [mul_le_mul_of_nonneg_right hL (norm_nonneg (v y)), hv y]
      · refine ht.trans (mul_le_mul_of_nonneg_left ?_ hk)
        simpa [norm_smul, hv] using norm_add_le (t • b j) (v y)
    have h₁ := abs_le.mp (H a ha)
    have h₂ := abs_le.mp (H a' ha')
    exact abs_le.mpr ⟨by linarith [h₁.1,h₂.2], by linarith [h₁.2,h₂.1]⟩
  · apply ENNReal.ofReal_le_ofReal
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (mean_norm_pi n) (by positivity)

open LongTails.Setups.FiniteLogisticTwoTap
open scoped RealInnerProductSpace

noncomputable def mode {d : ℕ} (i : Fin d) (τ : ℝ) : Weights d :=
  (1 / 2 : ℝ) • (EuclideanSpace.single (.inl 0) 1 - EuclideanSpace.single (.inr i) 1 +
    τ • (EuclideanSpace.single (.inl 1) 1 - EuclideanSpace.single (.inr (finRotate d i)) 1))

lemma mode_inner {d : ℕ} (i : Fin d) (τ : ℝ) (w : Weights d) :
    ⟪mode i τ, w⟫ = ((w (.inl 0) - w (.inr i)) +
      τ * (w (.inl 1) - w (.inr (finRotate d i)))) / 2 := by
  simp [mode, real_inner_smul_left, inner_add_left, inner_sub_left, EuclideanSpace.inner_single_left]
  ring

lemma mode_unit {d : ℕ} (i : Fin d) (hi : finRotate d i ≠ i) {τ : ℝ} (hτ : τ ^ 2 = 1) :
    ‖mode i τ‖ = 1 := by
  have h := mode_inner i τ (mode i τ)
  rw [real_inner_self_eq_norm_sq] at h
  conv_rhs at h => simp [mode, -finRotate_apply, hi, Ne.symm hi]
  nlinarith [norm_nonneg (mode i τ)]

lemma mode_strip {d : ℕ} (i : Fin d) (hi : finRotate d i ≠ i) {τ k : ℝ}
    (hτ : τ ^ 2 = 1) (hk : 0 ≤ k) (hk' : k ≤ 1 / 4) :
    stdGaussian (Weights d) {w | |⟪mode i τ, w⟫| ≤ k * ‖w‖} ≤
      ENNReal.ofReal (12*k*Real.sqrt (d+1)) := by
  let e : (Fin 2 ⊕ Fin d) ≃ Fin ((d+1)+1) := finSumFinEquiv.trans (finCongr (by omega))
  let b := (EuclideanSpace.basisFun (Fin 2 ⊕ Fin d) ℝ).reindex e
  have hj : b (e (.inl 0)) = EuclideanSpace.single (.inl 0) 1 := by
    simp [b, OrthonormalBasis.reindex_apply, EuclideanSpace.basisFun_apply]
  rw [← Nat.cast_succ]
  refine angular_strip b (e (.inl 0)) (innerSL ℝ (mode i τ)) ?_ ?_ hk hk'
  · simp [innerSL_apply_norm, mode_unit i hi hτ]
  · rw [hj, innerSL_apply_apply, mode_inner]
    norm_num

lemma initial_modes {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (hi : finRotate d i ≠ i)
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρ' : ρ ≤ 1) :
    let k := ρ / (32 * Real.sqrt d)
    stdGaussian (Weights d) {g | ¬(‖start r g‖ = r ∧
      k * r < |⟪mode i 1, start r g⟫| ∧ k * r < |⟪mode i (-1), start r g⟫|)} ≤
        ENNReal.ofReal ρ := by
  intro k
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hroot : 1 ≤ Real.sqrt d := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ d by linarith)
  have hden : 0 < 32 * Real.sqrt d := by linarith
  have hk : 0 ≤ k := (div_pos hρ hden).le
  have hk' : k ≤ 1 / 4 := (div_le_iff₀ hden).mpr (by linarith)
  let bad := fun τ : ℝ => {g : Weights d | |⟪mode i τ, g⟫| ≤ k * ‖g‖}
  have hsub : {g | ¬(‖start r g‖ = r ∧ k*r < |⟪mode i 1, start r g⟫| ∧
      k*r < |⟪mode i (-1), start r g⟫|)} ⊆ bad 1 ∪ bad (-1) := by
    intro g hg
    by_contra! h
    have ha : k * ‖g‖ < |⟪mode i 1, g⟫| := lt_of_not_ge (fun H => h (Or.inl H))
    have hb : k * ‖g‖ < |⟪mode i (-1), g⟫| := lt_of_not_ge (fun H => h (Or.inr H))
    have hg₀ : g ≠ 0 := by rintro rfl; simp at ha
    have hn := norm_pos_iff.mpr hg₀
    have he : (r / ‖g‖) * ‖g‖ = r := div_mul_cancel₀ _ hn.ne'
    have hdir (τ : ℝ) (H : k * ‖g‖ < |⟪mode i τ, g⟫|) :
        k*r < |⟪mode i τ, start r g⟫| := by
      rw [start, real_inner_smul_right, abs_mul, abs_of_pos (div_pos hr hn)]
      nlinarith [mul_lt_mul_of_pos_left H (div_pos hr hn), congrArg (fun z => k*z) he]
    exact hg ⟨by rwa [start, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hn)],
      hdir 1 ha, hdir (-1) hb⟩
  have hsize : Real.sqrt ((d : ℝ) + 1) ≤ 4 / 3 * Real.sqrt d := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg d), Real.sq_sqrt (show (0 : ℝ) ≤ d + 1 by positivity),
      Real.sqrt_nonneg ((d : ℝ) + 1)]
  have hρeq : k * (32 * Real.sqrt d) = ρ := div_mul_cancel₀ _ hden.ne'
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (mode_strip i hi (by norm_num : (1 : ℝ)^2=1) hk hk')
    (mode_strip i hi (by norm_num : (-1 : ℝ)^2=1) hk hk')).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [mul_le_mul_of_nonneg_left hsize hk]

end LongTails.Proofs.TwoTapGaussianBounds
