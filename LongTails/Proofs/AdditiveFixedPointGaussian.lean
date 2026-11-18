import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace LongTails.Proofs.AdditiveFixedPointGaussian

lemma density_square (a b : ℝ) {v : NNReal} (hv : v ≠ 0) (z : ℝ) :
    gaussianPDFReal b v z ^ 2 =
      Real.exp ((b - a) ^ 2 / v) * gaussianPDFReal a v z * gaussianPDFReal (2 * b - a) v z := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have halg : 2 * (-(z - b) ^ 2 / (2 * (v : ℝ))) =
      (b - a) ^ 2 / v + (-(z - a) ^ 2 / (2 * v)) + (-(z - (2 * b - a)) ^ 2 / (2 * v)) := by
    field_simp
    ring
  simp only [gaussianPDFReal_def, mul_pow]
  rw [sq (Real.exp _), ← Real.exp_add, ← two_mul, halg, Real.exp_add, Real.exp_add]
  ring

noncomputable def density {d : ℕ} (v : NNReal) (u z : Fin d → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal (u i) v (z i)

lemma vector_density_square {d : ℕ} (u w : Fin d → ℝ) {v : NNReal} (hv : v ≠ 0)
    (z : Fin d → ℝ) :
    density v w z ^ 2 = Real.exp (∑ i, (w i - u i) ^ 2 / v) *
      density v u z * density v (fun i => 2 * w i - u i) z := by
  classical
  unfold density
  rw [← Finset.prod_pow]
  rw [Real.exp_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => density_square (u i) (w i) hv (z i)

lemma density_nonneg {d : ℕ} (v : NNReal) (u z : Fin d → ℝ) : 0 ≤ density v u z :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg (u i) v (z i)

lemma density_measurable {d : ℕ} (v : NNReal) :
    Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => density v p.1 p.2) := by
  unfold density
  apply Finset.measurable_prod
  intro i _
  have hm : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => (p.1 i, v, p.2 i)) := by fun_prop
  exact measurable_uncurry_gaussianPDFReal.comp hm

lemma density_integral {d : ℕ} {v : NNReal} (hv : v ≠ 0) (u : Fin d → ℝ) :
    ∫ z, density v u z = 1 := by
  simp only [density, integral_fin_nat_prod_volume_eq_prod, integral_gaussianPDFReal_eq_one _ hv,
    Finset.prod_const_one]

lemma density_mass {d : ℕ} {v : NNReal} (hv : v ≠ 0) (u : Fin d → ℝ) :
    ∫⁻ z, ENNReal.ofReal (density v u z) = 1 := by
  have hi : Integrable (density v u) := by
    by_contra hn
    simpa [integral_undef hn] using density_integral hv u
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (density_nonneg v u)),
    density_integral hv, ENNReal.ofReal_one]

lemma half_pow_square (x : ℝ≥0∞) : (x ^ 2) ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_natCast_mul]
  norm_num

lemma integral_compare {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f p q r : α → ℝ≥0∞} {C : ℝ≥0∞} (hf : Measurable f) (hq : Measurable q)
    (hr : Measurable r) (hm : ∫⁻ z, r z ∂μ = 1)
    (hbound : ∀ z, p z ^ 2 ≤ C * q z * r z) :
    (∫⁻ z, p z * f z ∂μ) ^ 2 ≤ C * ∫⁻ z, q z * f z ^ 2 ∂μ := by
  let t : ℝ := 1 / 2
  have ht : 0 ≤ t := by norm_num [t]
  have ht2 (x : ℝ≥0∞) : (x ^ t) ^ 2 = x := by
    rw [← ENNReal.rpow_mul_natCast]
    norm_num [t]
  have hg : Measurable (fun z => q z * f z ^ 2) := hq.mul (hf.pow_const _)
  have hi : (∫⁻ z, p z * f z ∂μ) ≤
      C ^ t * (∫⁻ z, q z * f z ^ 2 ∂μ) ^ t := by
    calc
      _ ≤ ∫⁻ z, C ^ t * ((q z * f z ^ 2) ^ t * r z ^ t) ∂μ := by
        apply lintegral_mono
        intro z
        have hh := ENNReal.rpow_le_rpow (hbound z) ht
        change (p z ^ 2) ^ (1 / 2 : ℝ) ≤ _ at hh
        rw [half_pow_square] at hh
        calc
          _ ≤ (C * q z * r z) ^ t * f z := by
            change p z * f z ≤ _
            gcongr
          _ = _ := by
            simp only [ENNReal.mul_rpow_of_nonneg _ _ ht, t, half_pow_square]
            ac_rfl
      _ = C ^ t * ∫⁻ z, (q z * f z ^ 2) ^ t * r z ^ t ∂μ := by
        exact lintegral_const_mul _ ((hg.pow_const t).mul (hr.pow_const t))
      _ ≤ _ := by
        gcongr
        simpa only [hm, ENNReal.one_rpow, mul_one] using
          ENNReal.lintegral_mul_norm_pow_le (μ := μ) hg.aemeasurable hr.aemeasurable ht ht (by norm_num [t])
  simpa only [mul_pow, ht2] using pow_le_pow_left' hi 2

noncomputable def weight {d : ℕ} (v : NNReal) (u z : Fin d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (density v u z)

lemma weight_measurable {d : ℕ} (v : NNReal) :
    Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => weight v p.1 p.2) :=
  ENNReal.measurable_ofReal.comp (density_measurable v)

lemma compare_shift {d : ℕ} {v : NNReal} (hv : v ≠ 0) (u w : Fin d → ℝ)
    {f : (Fin d → ℝ) → ℝ≥0∞} (hf : Measurable f) {B : ℝ}
    (hb : ∑ i, (w i - u i) ^ 2 / v ≤ B) :
    (∫⁻ z, weight v w z * f z) ^ 2 ≤
      ENNReal.ofReal (Real.exp B) * ∫⁻ z, weight v u z * f z ^ 2 := by
  let t : Fin d → ℝ := fun i => 2 * w i - u i
  have hm (b : Fin d → ℝ) : Measurable (weight v b) := by
    unfold weight density
    exact ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal (b i) v).comp (measurable_pi_apply i))
  apply integral_compare (p := weight v w) (q := weight v u) (r := weight v t)
    hf (hm u) (hm t) (density_mass hv t)
  intro z
  unfold weight
  rw [← ENNReal.ofReal_pow (density_nonneg _ _ _), vector_density_square u w hv,
    ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (density_nonneg _ _ _)),
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  gcongr

noncomputable def run {S : Type*} {d : ℕ} (v : NNReal) (mean : S → Fin d → ℝ)
    (update : S → (Fin d → ℝ) → S) (pay : S → ℝ≥0∞) : ℕ → S → ℝ≥0∞
  | 0, s => pay s
  | n + 1, s => ∫⁻ z, weight v (mean s) z * run v mean update pay n (update s z)

lemma run_measurable {S : Type*} [MeasurableSpace S] {d : ℕ} (v : NNReal)
    {mean : S → Fin d → ℝ} {update : S → (Fin d → ℝ) → S} {pay : S → ℝ≥0∞}
    (hm : Measurable mean) (hu : Measurable update.uncurry) (hp : Measurable pay)
    (n : ℕ) : Measurable (run v mean update pay n) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    apply Measurable.lintegral_prod_right
    exact ((weight_measurable v).comp ((hm.comp measurable_fst).prodMk measurable_snd)).mul
      (ih.comp hu)

lemma adaptive_compare {S : Type*} [MeasurableSpace S] {d : ℕ} {v : NNReal} (hv : v ≠ 0)
    {a b : S → Fin d → ℝ} (hb : Measurable b) {update : S → (Fin d → ℝ) → S}
    (hu : Measurable update.uncurry) {pay : S → ℝ≥0∞} (hp : Measurable pay)
    {B : ℝ} (he : ∀ s, ∑ i, (b s i - a s i) ^ 2 / v ≤ B) (n : ℕ) (s : S) :
    run v b update pay n s ^ 2 ≤ ENNReal.ofReal (Real.exp B) ^ n *
      run v a update (fun s => pay s ^ 2) n s := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    let K := ENNReal.ofReal (Real.exp B)
    have hu' : Measurable (fun z => update s z) :=
      hu.comp (show Measurable (fun z : Fin d → ℝ => (s, z)) by fun_prop)
    have hm := (run_measurable v hb hu hp n).comp hu'
    refine (compare_shift hv (a s) (b s) hm (he s)).trans ?_
    change K * _ ≤ K ^ (n + 1) * _
    rw [pow_succ, mul_comm (K ^ n) K, mul_assoc]
    gcongr
    simp only [run]
    rw [← lintegral_const_mul' (K ^ n) _ (by finiteness)]
    apply lintegral_mono
    intro z
    have hh := ih (update s z)
    dsimp only [Function.comp_apply]
    calc
      _ ≤ weight v (a s) z * (K ^ n * run v a update (fun s => pay s ^ 2) n (update s z)) := by
        gcongr
      _ = _ := by ac_rfl

end LongTails.Proofs.AdditiveFixedPointGaussian
