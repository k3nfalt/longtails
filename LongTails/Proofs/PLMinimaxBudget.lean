import LongTails.Proofs.PLMinimaxTuning
import Mathlib.Analysis.Complex.ExponentialBounds

open LongTails.Setups.NonconvexPLSecondOrder

namespace OracleTemplate.PLMinimax

lemma tuning_condition {p : Params} (hv : spec.valid p) : 1 ≤ p.L / p.μ :=
  (le_div_iff₀ hv.1).mpr (by simpa using hv.2.1)

lemma tuning_smoothness_formula {p : Params} (hv : spec.valid p) :
    (tuning p).smoothness = 6 * p.ρ * Real.sqrt (p.L / p.μ) * (4 + 32 * (p.L / p.μ)) := by
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have he : p.L / Real.sqrt (p.L * p.μ) = Real.sqrt (p.L / p.μ) := by
    rw [Real.sqrt_mul hL.le, ← div_div, Real.div_sqrt, ← Real.sqrt_div hL.le]
  calc
    (tuning p).smoothness = 6 * p.ρ * (p.L / Real.sqrt (p.L * p.μ)) * (4 + 32 * (p.L / p.μ)) := by
      dsimp [tuning]
      ring
    _ = _ := by rw [he]

lemma tuning_smoothness_bounds {p : Params} (hv : spec.valid p) :
    192 * p.ρ * (p.L / p.μ) * Real.sqrt (p.L / p.μ) ≤ (tuning p).smoothness ∧
      (tuning p).smoothness ≤ 216 * p.ρ * (p.L / p.μ) * Real.sqrt (p.L / p.μ) := by
  have hk := tuning_condition hv
  have hρ := hv.2.2.1
  have hC : 4 + 32 * (p.L / p.μ) ≤ 36 * (p.L / p.μ) := by linarith only [hk]
  have hlo : 32 * (p.L / p.μ) ≤ 4 + 32 * (p.L / p.μ) := by linarith
  have hc : 0 ≤ 6 * p.ρ * Real.sqrt (p.L / p.μ) := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hlo hc
  have h₂ := mul_le_mul_of_nonneg_left hC hc
  rw [tuning_smoothness_formula hv]
  constructor <;> nlinarith only [h₁, h₂]

lemma tuning_curvature_square {p : Params} (hv : spec.valid p) :
    (tuning p).curvature ^ 2 = 100 * p.ρ * Real.sqrt (p.L / p.μ) * (4 + p.L / p.μ) * p.ε := by
  have hρ := hv.2.2.1
  have hε := hv.2.2.2.2.2
  have hk := tuning_condition hv
  change (Real.sqrt _) ^ 2 = _
  exact Real.sq_sqrt (by positivity)

lemma tuning_curvature_cap {p : Params} (hv : spec.valid p) :
    p.ε / 8 ≤ (tuning p).curvature ^ 2 / (4 * (tuning p).smoothness) := by
  have hp := tuning_positive hv
  have hM := hp.1
  have hk := tuning_condition hv
  have hρ := hv.2.2.1
  have hε := hv.2.2.2.2.2
  apply (le_div_iff₀ (show 0 < 4 * (tuning p).smoothness by positivity)).mpr
  rw [tuning_smoothness_formula hv, tuning_curvature_square hv]
  have hc : 6 * (4 + 32 * (p.L / p.μ)) ≤ 200 * (4 + p.L / p.μ) := by linarith only [hk]
  have hh := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ p.ρ * Real.sqrt (p.L / p.μ) * p.ε by positivity)
  nlinarith only [hh]

lemma tuning_mesh_cap {p : Params} (hv : spec.valid p) :
    16 * (tuning p).smoothness * (tuning p).mesh ^ 2 =
      3 * p.μ ^ 2 * Real.sqrt (p.L / p.μ) / (512 * p.ρ) := by
  have hρ := hv.2.2.1
  have hk := tuning_condition hv
  rw [tuning_smoothness_formula hv]
  change 16 * (6 * p.ρ * Real.sqrt (p.L / p.μ) * (4 + 32 * (p.L / p.μ))) *
    (p.μ / (128 * p.ρ * Real.sqrt (4 + 32 * (p.L / p.μ)))) ^ 2 = _
  generalize p.L / p.μ = k at hk ⊢
  have hC : 0 < 4 + 32 * k := by linarith only [hk]
  have hs : 0 < Real.sqrt (4 + 32 * k) := Real.sqrt_pos.mpr hC
  have he := Real.sq_sqrt hC.le
  field_simp
  rw [he]
  ring

lemma tuning_accuracy_lower {p : Params} (hv : spec.valid p) :
    min (p.ε / 8) (3 * p.μ ^ 2 * Real.sqrt (p.L / p.μ) / (512 * p.ρ)) ≤ (tuning p).accuracy := by
  have he := hv.2.2.2.2.2
  change _ ≤ min p.ε (min ((tuning p).curvature ^ 2 / (4 * (tuning p).smoothness))
    (16 * (tuning p).smoothness * (tuning p).mesh ^ 2))
  refine le_min ?_ (le_min ?_ ?_)
  · exact (min_le_left _ _).trans (by linarith only [he])
  · exact (min_le_left _ _).trans (tuning_curvature_cap hv)
  · rw [tuning_mesh_cap hv]
    exact min_le_right _ _

noncomputable def budgetRadius (p : Params) : ℝ :=
  2 + p.L / p.μ + p.ρ ^ 2 * (p.Δ + p.D) / p.μ ^ 3 +
    p.ρ * p.ε / p.μ ^ 2 + p.μ ^ 2 / (p.ρ * p.ε)

lemma budgetRadius_bounds {p : Params} (hv : spec.valid p) :
    3 ≤ budgetRadius p ∧ p.L / p.μ ≤ budgetRadius p ∧
      p.ρ ^ 2 * (p.Δ + p.D) / p.μ ^ 3 ≤ budgetRadius p ∧
      p.ρ * p.ε / p.μ ^ 2 ≤ budgetRadius p ∧
      p.μ ^ 2 / (p.ρ * p.ε) ≤ budgetRadius p := by
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hΔ := hv.2.2.2.1
  have hD := hv.2.2.2.2.1
  have hε := hv.2.2.2.2.2
  have hk := tuning_condition hv
  have ha : 0 ≤ p.ρ ^ 2 * (p.Δ + p.D) / p.μ ^ 3 := by positivity
  have hn : 0 ≤ p.ρ * p.ε / p.μ ^ 2 := by positivity
  have hi : 0 ≤ p.μ ^ 2 / (p.ρ * p.ε) := by positivity
  dsimp [budgetRadius]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hk, ha, hn, hi]

lemma budgetRadius_log {p : Params} (hv : spec.valid p) : 1 ≤ Real.log (budgetRadius p) := by
  have hR := (budgetRadius_bounds hv).1
  apply (Real.le_log_iff_exp_le (by linarith only [hR])).mpr
  exact Real.exp_one_lt_three.le.trans hR

lemma tuning_smoothness_radius {p : Params} (hv : spec.valid p) :
    192 * p.ρ ≤ (tuning p).smoothness ∧
      (tuning p).smoothness ≤ 216 * p.ρ * budgetRadius p ^ 2 := by
  have hk := tuning_condition hv
  have hR := budgetRadius_bounds hv
  have hρ := hv.2.2.1
  have hs : 1 ≤ Real.sqrt (p.L / p.μ) := by
    simpa using Real.sqrt_le_sqrt hk
  have hsR : Real.sqrt (p.L / p.μ) ≤ budgetRadius p := by
    apply (Real.sqrt_le_left (by linarith only [hR.1])).mpr
    nlinarith only [hR.1, hR.2.1]
  have hlo := mul_le_mul hk hs (by norm_num) (by linarith only [hk])
  have hhi := mul_le_mul hR.2.1 hsR (Real.sqrt_nonneg _) (by linarith only [hR.1])
  have hb := tuning_smoothness_bounds hv
  have h₁ := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 192 * p.ρ by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hhi (show 0 ≤ 216 * p.ρ by positivity)
  constructor <;> nlinarith only [h₁, h₂, hb.1, hb.2]

lemma tuning_accuracy_radius {p : Params} (hv : spec.valid p) :
    3 * p.μ ^ 2 / (512 * p.ρ * budgetRadius p) ≤ (tuning p).accuracy := by
  have hR := budgetRadius_bounds hv
  have hRpos : 0 < budgetRadius p := by linarith only [hR.1]
  have hρ := hv.2.2.1
  have hε := hv.2.2.2.2.2
  have hi := (div_le_iff₀ (mul_pos hρ hε)).mp hR.2.2.2.2
  have hu : p.μ ^ 2 / (p.ρ * budgetRadius p) ≤ p.ε :=
    (div_le_iff₀ (mul_pos hρ hRpos)).mpr (by nlinarith only [hi])
  apply le_trans _ (tuning_accuracy_lower hv)
  apply le_min
  · have hh := mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 3 / 512)
    have hh' : 3 * p.μ ^ 2 / (512 * p.ρ * budgetRadius p) ≤ (3 / 512 : ℝ) * p.ε := by
      convert hh using 1; ring
    linarith only [hh', hε]
  · have hk := tuning_condition hv
    have hs : 1 ≤ Real.sqrt (p.L / p.μ) := by simpa using Real.sqrt_le_sqrt hk
    have h₁ := div_le_self (show 0 ≤ 3 * p.μ ^ 2 / (512 * p.ρ) by positivity)
      (show 1 ≤ budgetRadius p by linarith only [hR.1])
    have h₂ := mul_le_mul_of_nonneg_left hs (show 0 ≤ 3 * p.μ ^ 2 / (512 * p.ρ) by positivity)
    simp only [mul_one] at h₂
    convert h₁.trans h₂ using 1 <;> ring

lemma tuning_gradient_tolerance_formula {p : Params} (hv : spec.valid p) :
    (tuning p).gradientTolerance = (tuning p).accuracy / 384 := by
  have hM := (tuning_positive hv).1
  have he := (tuning_positive hv).2.2.2.1
  change (tuning p).smoothness * (Real.sqrt ((tuning p).accuracy / (16 * (tuning p).smoothness))) ^ 2 / 24 = _
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  ring

lemma tuning_gradient_tolerance_radius {p : Params} (hv : spec.valid p) :
    p.μ ^ 2 / (65536 * p.ρ * budgetRadius p) ≤ (tuning p).gradientTolerance := by
  have hh := div_le_div_of_nonneg_right (tuning_accuracy_radius hv) (by norm_num : (0 : ℝ) ≤ 384)
  rw [tuning_gradient_tolerance_formula hv]
  convert hh using 1; ring

lemma tuning_threshold_identity {p : Params} (hv : spec.valid p) :
    (tuning p).smoothness * (tuning p).threshold ^ 2 = (tuning p).accuracy / 16 := by
  have hM := (tuning_positive hv).1
  have he := (tuning_positive hv).2.2.2.1
  change (tuning p).smoothness * (Real.sqrt ((tuning p).accuracy / (16 * (tuning p).smoothness))) ^ 2 = _
  rw [Real.sq_sqrt (by positivity)]
  field_simp

lemma tuning_threshold_radius {p : Params} (hv : spec.valid p) :
    p.μ / (1000 * p.ρ * budgetRadius p ^ 2) ≤ (tuning p).threshold := by
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hR := (budgetRadius_bounds hv).1
  have hRpos : 0 < budgetRadius p := by linarith only [hR]
  have hp := tuning_positive hv
  have hM := hp.1
  have hs := hp.2.2.2.2.1
  have hupper := (tuning_smoothness_radius hv).2
  have hcalc : (216 * p.ρ * budgetRadius p ^ 2) * (p.μ / (1000 * p.ρ * budgetRadius p ^ 2)) ^ 2 ≤
      (3 * p.μ ^ 2 / (512 * p.ρ * budgetRadius p)) / 16 := by
    field_simp
    nlinarith only [hR]
  apply (sq_le_sq₀ (by positivity) hs.le).mp
  apply (mul_le_mul_iff_right₀ hM).mp
  calc
    _ ≤ (216 * p.ρ * budgetRadius p ^ 2) * (p.μ / (1000 * p.ρ * budgetRadius p ^ 2)) ^ 2 :=
      mul_le_mul_of_nonneg_right hupper (sq_nonneg _)
    _ ≤ (3 * p.μ ^ 2 / (512 * p.ρ * budgetRadius p)) / 16 := hcalc
    _ ≤ (tuning p).accuracy / 16 := div_le_div_of_nonneg_right (tuning_accuracy_radius hv) (by norm_num)
    _ = _ := (tuning_threshold_identity hv).symm

lemma tuning_mesh_upper {p : Params} (hv : spec.valid p) :
    (tuning p).mesh ≤ p.μ / p.ρ := by
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hk := tuning_condition hv
  have hs : 1 ≤ Real.sqrt (4 + 32 * (p.L / p.μ)) := by
    have hh : 1 ≤ 4 + 32 * (p.L / p.μ) := by linarith only [hk]
    simpa using Real.sqrt_le_sqrt hh
  change p.μ / (128 * p.ρ * Real.sqrt (4 + 32 * (p.L / p.μ))) ≤ p.μ / p.ρ
  apply div_le_div_of_nonneg_left hμ.le hρ
  nlinarith only [hs, hρ]

lemma tuning_hessian_tolerance_radius {p : Params} (hv : spec.valid p) :
    p.μ / (64 * budgetRadius p ^ 2) ≤ (tuning p).hessianTolerance ∧
      (tuning p).hessianTolerance ≤ 18 * p.μ * budgetRadius p ^ 2 := by
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hR := (budgetRadius_bounds hv).1
  have hRpos : 0 < budgetRadius p := by linarith only [hR]
  have hp := tuning_positive hv
  have hM := hp.1
  have hs := hp.2.2.2.2.1
  have hMb := tuning_smoothness_radius hv
  have hsb := tuning_threshold_radius hv
  have hsu := (tuning_threshold_bounds hv).2.2.trans (tuning_mesh_upper hv)
  have hlo := mul_le_mul hMb.1 hsb (by positivity : 0 ≤ p.μ / (1000 * p.ρ * budgetRadius p ^ 2)) hM.le
  have hhi := mul_le_mul hMb.2 hsu hs.le (by positivity : 0 ≤ 216 * p.ρ * budgetRadius p ^ 2)
  change p.μ / (64 * budgetRadius p ^ 2) ≤ (tuning p).smoothness * (tuning p).threshold / 12 ∧
    (tuning p).smoothness * (tuning p).threshold / 12 ≤ 18 * p.μ * budgetRadius p ^ 2
  constructor
  · apply le_trans _ (div_le_div_of_nonneg_right hlo (by norm_num : (0 : ℝ) ≤ 12))
    field_simp
    norm_num
  · apply (div_le_div_of_nonneg_right hhi (by norm_num : (0 : ℝ) ≤ 12)).trans
    have he : (216 * p.ρ * budgetRadius p ^ 2) * (p.μ / p.ρ) / 12 =
        18 * p.μ * budgetRadius p ^ 2 := by field_simp; ring
    exact he.le

lemma tuning_regularization_radius {p : Params} (hv : spec.valid p) :
    p.μ ^ 2 / (2 ^ 42 * budgetRadius p ^ 12) ≤ (tuning p).regularization := by
  have hμ := hv.1
  have hL : 0 < p.L := hμ.trans_le hv.2.1
  have hR := budgetRadius_bounds hv
  have hRpos : 0 < budgetRadius p := by linarith only [hR.1]
  have hk := tuning_condition hv
  have hb := (tuning_positive hv).2.2.2.2.2.2.1
  have hC : 0 < 4 + 32 * (p.L / p.μ) := by linarith only [hk]
  have hLbound : p.L ≤ p.μ * budgetRadius p := by
    have hh := (div_le_iff₀ hμ).mp hR.2.1
    nlinarith only [hh]
  have hCbound : 4 + 32 * (p.L / p.μ) ≤ 36 * budgetRadius p := by linarith only [hR.1, hR.2.1]
  have hnum := pow_le_pow_left₀ (show 0 ≤ p.μ / (64 * budgetRadius p ^ 2) by positivity)
    (tuning_hessian_tolerance_radius hv).1 4
  have hden : 64 * p.L ^ 2 * (4 + 32 * (p.L / p.μ)) ^ 2 ≤
      64 * (p.μ * budgetRadius p) ^ 2 * (36 * budgetRadius p) ^ 2 := by
    gcongr
  have hh := div_le_div₀ (pow_nonneg hb.le 4) hnum
    (show 0 < 64 * p.L ^ 2 * (4 + 32 * (p.L / p.μ)) ^ 2 by positivity) hden
  change _ ≤ (tuning p).hessianTolerance ^ 4 / (64 * p.L ^ 2 * (4 + 32 * (p.L / p.μ)) ^ 2)
  apply le_trans _ hh
  field_simp
  norm_num

lemma tuning_regularization_inverse_radius {p : Params} (hv : spec.valid p) :
    (tuning p).regularization⁻¹ ≤ 2 ^ 42 * budgetRadius p ^ 12 / p.μ ^ 2 := by
  have hμ := hv.1
  have hR := (budgetRadius_bounds hv).1
  have hRpos : 0 < budgetRadius p := by linarith only [hR]
  have hh := one_div_le_one_div_of_le
    (show 0 < p.μ ^ 2 / (2 ^ 42 * budgetRadius p ^ 12) by positivity)
    (tuning_regularization_radius hv)
  convert hh using 1 <;> simp [one_div]

lemma tuning_resolvent_radius {p : Params} (hv : spec.valid p) :
    (tuning p).regularization⁻¹ + 18 * p.L ^ 2 * (tuning p).regularization⁻¹ ^ 2 ≤
      2 ^ 89 * budgetRadius p ^ 26 / p.μ ^ 2 := by
  have hμ := hv.1
  have hL : 0 < p.L := hμ.trans_le hv.2.1
  have hR := budgetRadius_bounds hv
  have hRpos : 0 < budgetRadius p := by linarith only [hR.1]
  have hθ := (tuning_positive hv).2.2.2.2.2.2.2.1
  have hi := tuning_regularization_inverse_radius hv
  have hLbound : p.L ≤ p.μ * budgetRadius p := by
    have hh := (div_le_iff₀ hμ).mp hR.2.1
    nlinarith only [hh]
  have hp := pow_le_pow_right₀ (show 1 ≤ budgetRadius p by linarith only [hR.1]) (by decide : 12 ≤ 26)
  have hfirst : 2 ^ 42 * budgetRadius p ^ 12 / p.μ ^ 2 ≤
      2 ^ 84 * budgetRadius p ^ 26 / p.μ ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg p.μ)
    exact mul_le_mul (by norm_num : (2 : ℝ) ^ 42 ≤ 2 ^ 84) hp
      (pow_nonneg hRpos.le _) (by positivity)
  have hsecond : 18 * p.L ^ 2 * (tuning p).regularization⁻¹ ^ 2 ≤
      18 * 2 ^ 84 * budgetRadius p ^ 26 / p.μ ^ 2 := by
    calc
      _ ≤ 18 * (p.μ * budgetRadius p) ^ 2 * (2 ^ 42 * budgetRadius p ^ 12 / p.μ ^ 2) ^ 2 := by
        gcongr
      _ = _ := by field_simp
  have hsum := add_le_add (hi.trans hfirst) hsecond
  apply hsum.trans
  have hh : (2 : ℝ) ^ 84 + 18 * 2 ^ 84 ≤ 2 ^ 89 := by norm_num
  have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ budgetRadius p ^ 26 / p.μ ^ 2 by positivity)
  convert hh' using 1 <;> ring

lemma distance_radius_weaken {p : Params} (hv : spec.valid p) {c : ℝ} {n : ℕ}
    (hc : 0 < c) (hcb : c ≤ 2 ^ 100) (hn : n ≤ 30) :
    p.μ / (2 ^ 100 * p.ρ * budgetRadius p ^ 30) ≤ p.μ / (c * p.ρ * budgetRadius p ^ n) := by
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hR := (budgetRadius_bounds hv).1
  have hRpos : 0 < budgetRadius p := by linarith only [hR]
  apply div_le_div_of_nonneg_left hμ.le (by positivity)
  have hp := pow_le_pow_right₀ (show 1 ≤ budgetRadius p by linarith only [hR]) hn
  exact mul_le_mul (mul_le_mul_of_nonneg_right hcb hρ.le) hp
    (pow_nonneg hRpos.le _) (by positivity)

lemma tuning_hessian_distance_radius {p : Params} (hv : spec.valid p) :
    p.μ / (2 ^ 98 * p.ρ * budgetRadius p ^ 30) ≤
      (tuning p).hessianTolerance / (8 * p.L ^ 2 * p.ρ *
        ((tuning p).regularization⁻¹ + 18 * p.L ^ 2 * (tuning p).regularization⁻¹ ^ 2)) := by
  have hμ := hv.1
  have hL : 0 < p.L := hμ.trans_le hv.2.1
  have hρ := hv.2.2.1
  have hR := budgetRadius_bounds hv
  have hRpos : 0 < budgetRadius p := by linarith only [hR.1]
  have hθ := (tuning_positive hv).2.2.2.2.2.2.2.1
  have hb := (tuning_positive hv).2.2.2.2.2.2.1
  have hLbound : p.L ≤ p.μ * budgetRadius p := by
    have hh := (div_le_iff₀ hμ).mp hR.2.1
    nlinarith only [hh]
  have hQ := tuning_resolvent_radius hv
  have hden : 8 * p.L ^ 2 * p.ρ *
      ((tuning p).regularization⁻¹ + 18 * p.L ^ 2 * (tuning p).regularization⁻¹ ^ 2) ≤
        8 * (p.μ * budgetRadius p) ^ 2 * p.ρ * (2 ^ 89 * budgetRadius p ^ 26 / p.μ ^ 2) := by
    gcongr
  have hh := div_le_div₀ hb.le (tuning_hessian_tolerance_radius hv).1 (by positivity) hden
  convert hh using 1
  field_simp
  ring

lemma budgetRadius_accuracy {p : Params} (hv : spec.valid p) :
    p.μ ^ 2 / (p.ρ * budgetRadius p) ≤ p.ε := by
  have hR := budgetRadius_bounds hv
  have hRpos : 0 < budgetRadius p := by linarith only [hR.1]
  have hρ := hv.2.2.1
  have hε := hv.2.2.2.2.2
  have hi := (div_le_iff₀ (mul_pos hρ hε)).mp hR.2.2.2.2
  exact (div_le_iff₀ (mul_pos hρ hRpos)).mpr (by nlinarith only [hi])

lemma tuning_curvature_radius {p : Params} (hv : spec.valid p) :
    p.μ / budgetRadius p ≤ (tuning p).curvature := by
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hε := hv.2.2.2.2.2
  have hR := budgetRadius_bounds hv
  have hRpos : 0 < budgetRadius p := by linarith only [hR.1]
  have hk := tuning_condition hv
  have hs : 1 ≤ Real.sqrt (p.L / p.μ) := by simpa using Real.sqrt_le_sqrt hk
  have hη := (tuning_positive hv).2.1
  have hi := (div_le_iff₀ (mul_pos hρ hε)).mp hR.2.2.2.2
  have h₁ : p.μ ^ 2 / budgetRadius p ^ 2 ≤ p.μ ^ 2 / budgetRadius p :=
    div_le_div_of_nonneg_left (sq_nonneg _) hRpos (by nlinarith only [hR.1])
  have h₂ : p.μ ^ 2 / budgetRadius p ≤ p.ρ * p.ε :=
    (div_le_iff₀ hRpos).mpr (by nlinarith only [hi])
  have hc : 1 ≤ 100 * Real.sqrt (p.L / p.μ) * (4 + p.L / p.μ) := by nlinarith only [hk, hs]
  have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg hρ.le hε.le)
  have h₃ : p.ρ * p.ε ≤ (tuning p).curvature ^ 2 := by
    rw [tuning_curvature_square hv]
    nlinarith only [hh]
  apply (sq_le_sq₀ (by positivity) hη.le).mp
  simpa only [div_pow] using h₁.trans (h₂.trans h₃)

lemma tuning_gradient_distance_radius {p : Params} (hv : spec.valid p) :
    p.μ / (2 ^ 17 * p.ρ * budgetRadius p ^ 2) ≤ (tuning p).gradientTolerance / (2 * p.L) := by
  have hμ := hv.1
  have hL : 0 < p.L := hμ.trans_le hv.2.1
  have hρ := hv.2.2.1
  have hR := budgetRadius_bounds hv
  have hRpos : 0 < budgetRadius p := by linarith only [hR.1]
  have hLbound : p.L ≤ p.μ * budgetRadius p := by
    have hh := (div_le_iff₀ hμ).mp hR.2.1
    nlinarith only [hh]
  have ha := (tuning_positive hv).2.2.2.2.2.1
  have hh := div_le_div₀ ha.le (tuning_gradient_tolerance_radius hv)
    (show 0 < 2 * p.L by positivity) (mul_le_mul_of_nonneg_left hLbound (by norm_num : (0 : ℝ) ≤ 2))
  convert hh using 1
  field_simp
  ring

lemma tuning_output_distance_radius {p : Params} (hv : spec.valid p) :
    p.μ / (8 * p.ρ * budgetRadius p ^ 3) ≤ p.ε / (8 * p.L * (p.L / p.μ)) := by
  have hμ := hv.1
  have hL : 0 < p.L := hμ.trans_le hv.2.1
  have hρ := hv.2.2.1
  have hε := hv.2.2.2.2.2
  have hR := budgetRadius_bounds hv
  have hRpos : 0 < budgetRadius p := by linarith only [hR.1]
  have hLbound : p.L ≤ p.μ * budgetRadius p := by
    have hh := (div_le_iff₀ hμ).mp hR.2.1
    nlinarith only [hh]
  have hden : 8 * p.L * (p.L / p.μ) ≤ 8 * (p.μ * budgetRadius p) * budgetRadius p := by
    gcongr
    exact hR.2.1
  have hh := div_le_div₀ hε.le (budgetRadius_accuracy hv) (by positivity) hden
  convert hh using 1
  field_simp

lemma tuning_curvature_distance_radius {p : Params} (hv : spec.valid p) :
    p.μ / (2 ^ 14 * p.ρ * budgetRadius p ^ 6) ≤ (tuning p).curvature /
      (2 * (tuning p).smoothness * (1 + 2 * (p.L / p.μ)) ^ 3) := by
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hk := tuning_condition hv
  have hR := budgetRadius_bounds hv
  have hRpos : 0 < budgetRadius p := by linarith only [hR.1]
  have hM := (tuning_positive hv).1
  have hη := (tuning_positive hv).2.1
  have hA : 0 < 1 + 2 * (p.L / p.μ) := by linarith only [hk]
  have hAb : 1 + 2 * (p.L / p.μ) ≤ 3 * budgetRadius p := by linarith only [hR.1, hR.2.1]
  have hMb := (tuning_smoothness_radius hv).2
  have hden : 2 * (tuning p).smoothness * (1 + 2 * (p.L / p.μ)) ^ 3 ≤
      2 * (216 * p.ρ * budgetRadius p ^ 2) * (3 * budgetRadius p) ^ 3 := by gcongr
  have hh := div_le_div₀ hη.le (tuning_curvature_radius hv) (by positivity) hden
  apply le_trans _ hh
  field_simp
  norm_num

lemma tuning_distance_radius {p : Params} (hv : spec.valid p) :
    p.μ / (2 ^ 100 * p.ρ * budgetRadius p ^ 30) ≤ (tuning p).distanceTolerance := by
  have h₁ := distance_radius_weaken hv (by norm_num : (0 : ℝ) < 128)
    (by norm_num : (128 : ℝ) ≤ 2 ^ 100) (by decide : 0 ≤ 30)
  have h₂ := (distance_radius_weaken hv (by positivity : (0 : ℝ) < 2 ^ 17)
    (by norm_num : (2 : ℝ) ^ 17 ≤ 2 ^ 100) (by decide : 2 ≤ 30)).trans (tuning_gradient_distance_radius hv)
  have h₃ := (distance_radius_weaken hv (by positivity : (0 : ℝ) < 2 ^ 98)
    (by norm_num : (2 : ℝ) ^ 98 ≤ 2 ^ 100) (by decide : 30 ≤ 30)).trans (tuning_hessian_distance_radius hv)
  have h₄ := (distance_radius_weaken hv (by norm_num : (0 : ℝ) < 8)
    (by norm_num : (8 : ℝ) ≤ 2 ^ 100) (by decide : 3 ≤ 30)).trans (tuning_output_distance_radius hv)
  have h₅ := (distance_radius_weaken hv (by positivity : (0 : ℝ) < 2 ^ 14)
    (by norm_num : (2 : ℝ) ^ 14 ≤ 2 ^ 100) (by decide : 6 ≤ 30)).trans (tuning_curvature_distance_radius hv)
  change _ ≤ min (p.μ / (128 * p.ρ)) (min ((tuning p).gradientTolerance / (2 * p.L))
    (min ((tuning p).hessianTolerance / (8 * p.L ^ 2 * p.ρ *
      ((tuning p).regularization⁻¹ + 18 * p.L ^ 2 * (tuning p).regularization⁻¹ ^ 2)))
      (min (p.ε / (8 * p.L * (p.L / p.μ))) ((tuning p).curvature /
        (2 * (tuning p).smoothness * (1 + 2 * (p.L / p.μ)) ^ 3)))))
  exact le_min (by simpa using h₁) (le_min h₂ (le_min h₃ (le_min h₄ h₅)))

lemma tuning_residual_radius {p : Params} (hv : spec.valid p) :
    p.μ ^ 2 / (2 ^ 103 * p.ρ * budgetRadius p ^ 30) ≤ (tuning p).residualTolerance := by
  have hh := mul_le_mul_of_nonneg_left (tuning_distance_radius hv) (div_nonneg hv.1.le (by norm_num : (0 : ℝ) ≤ 8))
  change _ ≤ p.μ * (tuning p).distanceTolerance / 8
  convert hh using 1 <;> ring

lemma log_polynomial_radius {R x : ℝ} (hR : 2 ≤ R) (hx : 0 < x) (a b : ℕ)
    (hbound : x ≤ 2 ^ a * R ^ b) : Real.log x ≤ ((a + b : ℕ) : ℝ) * Real.log R := by
  have hRpos : 0 < R := by linarith only [hR]
  have hh := Real.log_le_log hx hbound
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ a ≠ 0) (by positivity : R ^ b ≠ 0),
    Real.log_pow, Real.log_pow] at hh
  have htwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hR
  have hs := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  push_cast
  nlinarith only [hh, hs]

lemma ceil_padding_bound {x y : ℝ} (hx : 0 ≤ x) (n : ℕ) (hbound : x + n + 1 ≤ y) :
    ((⌈x⌉₊ + n : ℕ) : ℝ) ≤ y := by
  have hh := (Nat.ceil_lt_add_one hx).le
  push_cast
  linarith only [hh, hbound]

lemma tuning_primal_log_bound {p : Params} (hv : spec.valid p) :
    ((tuning p).primalSteps + 1 : ℕ) ≤ 83 * Real.log (budgetRadius p) := by
  have hk := tuning_condition hv
  have hR := budgetRadius_bounds hv
  have hRpos : 0 < budgetRadius p := by linarith only [hR.1]
  have hlog := budgetRadius_log hv
  have hs : 1 ≤ Real.sqrt (p.L / p.μ) := by simpa using Real.sqrt_le_sqrt hk
  have hsR : Real.sqrt (p.L / p.μ) ≤ budgetRadius p := by
    apply (Real.sqrt_le_left hRpos.le).mpr
    nlinarith only [hR.1, hR.2.1]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hR.1 3
  have harg : 12 * Real.sqrt (p.L / p.μ) ≤ budgetRadius p ^ 4 := by
    calc
      _ ≤ 12 * budgetRadius p := mul_le_mul_of_nonneg_left hsR (by norm_num)
      _ ≤ budgetRadius p ^ 3 * budgetRadius p := mul_le_mul_of_nonneg_right (by norm_num at hpow ⊢; linarith only [hpow]) hRpos.le
      _ = _ := by ring
  have hargpos : 0 < 12 * Real.sqrt (p.L / p.μ) := by positivity
  have harglog := Real.log_le_log hargpos harg
  rw [Real.log_pow] at harglog
  have hnonneg : 0 ≤ Real.log (12 * Real.sqrt (p.L / p.μ)) := Real.log_nonneg (by linarith only [hs])
  change ((⌈18 * Real.log (12 * Real.sqrt (p.L / p.μ))⌉₊ + 1 : ℕ) : ℝ) ≤ _
  apply ceil_padding_bound (mul_nonneg (by norm_num) hnonneg) 1
  norm_num
  linarith only [harglog, hlog]

lemma tuning_dual_log_argument {p : Params} (hv : spec.valid p) :
    1 + 64 * p.L * (32 * (p.L / p.μ) * (p.Δ + p.D)) / (tuning p).residualTolerance ^ 2 ≤
      2 ^ 218 * budgetRadius p ^ 63 := by
  have hμ := hv.1
  have hL : 0 < p.L := hμ.trans_le hv.2.1
  have hρ := hv.2.2.1
  have hΔ := hv.2.2.2.1
  have hD := hv.2.2.2.2.1
  have hR := budgetRadius_bounds hv
  have hRpos : 0 < budgetRadius p := by linarith only [hR.1]
  have hLbound : p.L ≤ p.μ * budgetRadius p := by
    have hh := (div_le_iff₀ hμ).mp hR.2.1
    nlinarith only [hh]
  have hsum : p.Δ + p.D ≤ p.μ ^ 3 * budgetRadius p / p.ρ ^ 2 := by
    have hh := (div_le_iff₀ (pow_pos hμ 3)).mp hR.2.2.1
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
    nlinarith only [hh]
  have hnum : 64 * p.L * (32 * (p.L / p.μ) * (p.Δ + p.D)) ≤
      64 * (p.μ * budgetRadius p) * (32 * budgetRadius p * (p.μ ^ 3 * budgetRadius p / p.ρ ^ 2)) := by
    gcongr
    exact hR.2.1
  have hden := pow_le_pow_left₀
    (show 0 ≤ p.μ ^ 2 / (2 ^ 103 * p.ρ * budgetRadius p ^ 30) by positivity)
    (tuning_residual_radius hv) 2
  have hh := div_le_div₀ (show 0 ≤ 64 * (p.μ * budgetRadius p) *
      (32 * budgetRadius p * (p.μ ^ 3 * budgetRadius p / p.ρ ^ 2)) by positivity) hnum
    (show 0 < (p.μ ^ 2 / (2 ^ 103 * p.ρ * budgetRadius p ^ 30)) ^ 2 by positivity) hden
  have hratio : 64 * p.L * (32 * (p.L / p.μ) * (p.Δ + p.D)) / (tuning p).residualTolerance ^ 2 ≤
      2 ^ 217 * budgetRadius p ^ 63 := by
    convert hh using 1
    field_simp
    ring
  have hp : 1 ≤ budgetRadius p ^ 63 := one_le_pow₀ (by linarith only [hR.1])
  have hpow : (2 : ℝ) ^ 218 = 2 * 2 ^ 217 := by norm_num
  rw [hpow]
  nlinarith only [hratio, hp]

lemma tuning_dual_log_bound {p : Params} (hv : spec.valid p) :
    ((tuning p).dualSteps + 1 : ℕ) ≤ 1126 * (p.L / p.μ) * Real.log (budgetRadius p) := by
  let A := 1 + 64 * p.L * (32 * (p.L / p.μ) * (p.Δ + p.D)) / (tuning p).residualTolerance ^ 2
  have hμ := hv.1
  have hL : 0 < p.L := hμ.trans_le hv.2.1
  have hΔ := hv.2.2.2.1
  have hD := hv.2.2.2.2.1
  have hA : 1 ≤ A := by dsimp [A]; exact le_add_of_nonneg_right (by positivity)
  have hR := (budgetRadius_bounds hv).1
  have hk := tuning_condition hv
  have hlog := budgetRadius_log hv
  have hh := log_polynomial_radius (show 2 ≤ budgetRadius p by linarith only [hR])
    (show 0 < A by linarith only [hA]) 218 63 (tuning_dual_log_argument hv)
  norm_num at hh
  have hs := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4 * (p.L / p.μ) by positivity)
  have hprod := mul_le_mul hk hlog (by norm_num) (by linarith only [hk])
  change ((⌈4 * (p.L / p.μ) * Real.log A⌉₊ + 1 : ℕ) : ℝ) ≤ _
  apply ceil_padding_bound (mul_nonneg (by positivity) (Real.log_nonneg hA)) 1
  norm_num
  nlinarith only [hs, hprod]

lemma tuning_refinement_log_argument {p : Params} (hv : spec.valid p) :
    1 + p.ρ * (p.μ / (64 * p.ρ)) ^ 2 / (tuning p).residualTolerance ≤
      2 ^ 92 * budgetRadius p ^ 30 := by
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hR := (budgetRadius_bounds hv).1
  have hRpos : 0 < budgetRadius p := by linarith only [hR]
  have hh := div_le_div_of_nonneg_left (show 0 ≤ p.ρ * (p.μ / (64 * p.ρ)) ^ 2 by positivity)
    (show 0 < p.μ ^ 2 / (2 ^ 103 * p.ρ * budgetRadius p ^ 30) by positivity)
    (tuning_residual_radius hv)
  have hratio : p.ρ * (p.μ / (64 * p.ρ)) ^ 2 / (tuning p).residualTolerance ≤
      2 ^ 91 * budgetRadius p ^ 30 := by
    convert hh using 1
    field_simp
    ring
  have hp : 1 ≤ budgetRadius p ^ 30 := one_le_pow₀ (by linarith only [hR])
  have he : (2 : ℝ) ^ 92 = 2 * 2 ^ 91 := by norm_num
  rw [he]
  nlinarith only [hratio, hp]

lemma tuning_refinement_log_bound {p : Params} (hv : spec.valid p) :
    ((tuning p).refinementSteps + 1 : ℕ) ≤ 247 * Real.log (budgetRadius p) := by
  let A := 1 + p.ρ * (p.μ / (64 * p.ρ)) ^ 2 / (tuning p).residualTolerance
  have hρ := hv.2.2.1
  have hτ := (tuning_positive hv).2.2.2.2.2.2.2.2.2
  have hA : 1 ≤ A := by dsimp [A]; exact le_add_of_nonneg_right (by positivity)
  have hR := (budgetRadius_bounds hv).1
  have hlog := budgetRadius_log hv
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hh := log_polynomial_radius (show 2 ≤ budgetRadius p by linarith only [hR])
    (show 0 < A by linarith only [hA]) 92 30 (tuning_refinement_log_argument hv)
  norm_num at hh
  have hdiv : Real.log A / Real.log 2 ≤ 244 * Real.log (budgetRadius p) := by
    apply (div_le_iff₀ htwo).mpr
    have hs := mul_le_mul_of_nonneg_left hhalf
      (show 0 ≤ 244 * Real.log (budgetRadius p) by linarith only [hlog])
    nlinarith only [hh, hs]
  change ((⌈Real.log A / Real.log 2⌉₊ + 2 : ℕ) : ℝ) ≤ _
  apply ceil_padding_bound (div_nonneg (Real.log_nonneg hA) htwo.le) 2
  norm_num
  linarith only [hdiv, hlog]

lemma tuning_accuracy_convenient {p : Params} (hv : spec.valid p) :
    min (p.ε / 16) (p.μ ^ 2 * Real.sqrt (p.L / p.μ) / (256 * p.ρ)) ≤ (tuning p).accuracy := by
  have hε := hv.2.2.2.2.2
  have hρ := hv.2.2.1
  apply le_trans _ (tuning_accuracy_lower hv)
  apply min_le_min (by linarith only [hε])
  have hh : 0 ≤ p.μ ^ 2 * Real.sqrt (p.L / p.μ) / p.ρ := by positivity
  have ht := mul_le_mul_of_nonneg_right (by norm_num : (1 / 256 : ℝ) ≤ 3 / 512) hh
  convert ht using 1 <;> ring

lemma tuning_threshold_formula {p : Params} (hv : spec.valid p) :
    (tuning p).threshold = Real.sqrt (tuning p).accuracy / (4 * Real.sqrt (tuning p).smoothness) := by
  have ha := (tuning_positive hv).2.2.2.1
  change Real.sqrt ((tuning p).accuracy / (16 * (tuning p).smoothness)) = _
  rw [Real.sqrt_div ha.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
  norm_num

lemma tuning_cubic_inverse {p : Params} (hv : spec.valid p) :
    1 / ((tuning p).smoothness * (tuning p).threshold ^ 3) =
      64 * Real.sqrt (tuning p).smoothness / ((tuning p).accuracy * Real.sqrt (tuning p).accuracy) := by
  have he : (tuning p).smoothness * (tuning p).threshold ^ 3 =
      ((tuning p).accuracy / 16) * (Real.sqrt (tuning p).accuracy / (4 * Real.sqrt (tuning p).smoothness)) := by
    calc
      _ = ((tuning p).smoothness * (tuning p).threshold ^ 2) * (tuning p).threshold := by ring
      _ = _ := by rw [tuning_threshold_identity hv, tuning_threshold_formula hv]
  rw [he]
  ring_nf
  simp only [inv_inv]
  ring

lemma tuning_smoothness_sqrt {p : Params} (hv : spec.valid p) :
    Real.sqrt (tuning p).smoothness ≤
      15 * Real.sqrt p.ρ * Real.sqrt ((p.L / p.μ) * Real.sqrt (p.L / p.μ)) := by
  have hρ := hv.2.2.1
  have hk := tuning_condition hv
  have hκ : 0 ≤ p.L / p.μ := by linarith only [hk]
  have hh := (tuning_smoothness_bounds hv).2
  apply (Real.sqrt_le_left (by positivity)).mpr
  rw [mul_pow, mul_pow, Real.sq_sqrt hρ.le, Real.sq_sqrt (mul_nonneg hκ (Real.sqrt_nonneg _))]
  have hn := mul_nonneg hρ.le (mul_nonneg hκ (Real.sqrt_nonneg (p.L / p.μ)))
  nlinarith only [hh, hn]

lemma tuning_mesh_inverse {p : Params} (hv : spec.valid p) :
    1 / ((tuning p).smoothness * (tuning p).mesh ^ 3) ≤ 2097152 * p.ρ ^ 2 / p.μ ^ 3 := by
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hk := tuning_condition hv
  have hκ : 0 < p.L / p.μ := by linarith only [hk]
  have hsκ : 0 < Real.sqrt (p.L / p.μ) := Real.sqrt_pos.mpr hκ
  have hC : 0 < 4 + 32 * (p.L / p.μ) := by linarith only [hk]
  have hsC : 0 < Real.sqrt (4 + 32 * (p.L / p.μ)) := Real.sqrt_pos.mpr hC
  have hratio : Real.sqrt (4 + 32 * (p.L / p.μ)) / Real.sqrt (p.L / p.μ) ≤ 6 := by
    apply (div_le_iff₀ hsκ).mpr
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow, Real.sq_sqrt hκ.le]
    nlinarith only [hk]
  have he : 1 / ((tuning p).smoothness * (tuning p).mesh ^ 3) =
      (2097152 * p.ρ ^ 2 / (6 * p.μ ^ 3)) *
        (Real.sqrt (4 + 32 * (p.L / p.μ)) / Real.sqrt (p.L / p.μ)) := by
    rw [tuning_smoothness_formula hv]
    change 1 / ((6 * p.ρ * Real.sqrt (p.L / p.μ) * (4 + 32 * (p.L / p.μ))) *
      (p.μ / (128 * p.ρ * Real.sqrt (4 + 32 * (p.L / p.μ)))) ^ 3) = _
    generalize p.L / p.μ = k at hκ hsκ hC hsC ⊢
    field_simp
    rw [Real.sq_sqrt hC.le]
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2097152 * p.ρ ^ 2 / (6 * p.μ ^ 3) by positivity)
  convert hh using 1; ring

lemma tuning_cubic_inverse_bound {p : Params} (hv : spec.valid p) :
    1 / ((tuning p).smoothness * (tuning p).threshold ^ 3) ≤
      61440 * Real.sqrt p.ρ * Real.sqrt ((p.L / p.μ) * Real.sqrt (p.L / p.μ)) /
        (p.ε * Real.sqrt p.ε) + 3932160 * p.ρ ^ 2 / p.μ ^ 3 := by
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hε := hv.2.2.2.2.2
  have hk := tuning_condition hv
  have hκ : 0 < p.L / p.μ := by linarith only [hk]
  have hsκ : 0 < Real.sqrt (p.L / p.μ) := Real.sqrt_pos.mpr hκ
  have hssκ : 0 < Real.sqrt (Real.sqrt (p.L / p.μ)) := Real.sqrt_pos.mpr hsκ
  have hsρ : 0 < Real.sqrt p.ρ := Real.sqrt_pos.mpr hρ
  have ha := (tuning_positive hv).2.2.2.1
  have hbound (b : ℝ) (hb : 0 < b) (hba : b ≤ (tuning p).accuracy) :
      1 / ((tuning p).smoothness * (tuning p).threshold ^ 3) ≤
        64 * (15 * Real.sqrt p.ρ * Real.sqrt ((p.L / p.μ) * Real.sqrt (p.L / p.μ))) / (b * Real.sqrt b) := by
    rw [tuning_cubic_inverse hv]
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left (tuning_smoothness_sqrt hv) (by norm_num : (0 : ℝ) ≤ 64))
      (mul_pos hb (Real.sqrt_pos.mpr hb))
      (mul_le_mul hba (Real.sqrt_le_sqrt hba) (Real.sqrt_nonneg _) ha.le)
  have hmin := tuning_accuracy_convenient hv
  by_cases hcase : p.ε / 16 ≤ p.μ ^ 2 * Real.sqrt (p.L / p.μ) / (256 * p.ρ)
  · rw [min_eq_left hcase] at hmin
    have hh := hbound (p.ε / 16) (by positivity) hmin
    have he : 64 * (15 * Real.sqrt p.ρ * Real.sqrt ((p.L / p.μ) * Real.sqrt (p.L / p.μ))) /
        (p.ε / 16 * Real.sqrt (p.ε / 16)) =
          61440 * Real.sqrt p.ρ * Real.sqrt ((p.L / p.μ) * Real.sqrt (p.L / p.μ)) / (p.ε * Real.sqrt p.ε) := by
      rw [Real.sqrt_div hε.le]
      norm_num
      ring
    rw [he] at hh
    exact hh.trans (le_add_of_nonneg_right (by positivity))
  · rw [min_eq_right (lt_of_not_ge hcase).le] at hmin
    have hh := hbound (p.μ ^ 2 * Real.sqrt (p.L / p.μ) / (256 * p.ρ)) (by positivity) hmin
    have hs : Real.sqrt (p.μ ^ 2 * Real.sqrt (p.L / p.μ) / (256 * p.ρ)) =
        p.μ * Real.sqrt (Real.sqrt (p.L / p.μ)) / (16 * Real.sqrt p.ρ) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_mul (sq_nonneg p.μ), Real.sqrt_sq hμ.le,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 256)]
      norm_num
    have he : 64 * (15 * Real.sqrt p.ρ * Real.sqrt ((p.L / p.μ) * Real.sqrt (p.L / p.μ))) /
        ((p.μ ^ 2 * Real.sqrt (p.L / p.μ) / (256 * p.ρ)) *
          Real.sqrt (p.μ ^ 2 * Real.sqrt (p.L / p.μ) / (256 * p.ρ))) =
            3932160 * p.ρ ^ 2 / p.μ ^ 3 := by
      rw [hs, Real.sqrt_mul hκ.le]
      generalize p.L / p.μ = k at hsκ hssκ ⊢
      field_simp
      rw [Real.sq_sqrt hρ.le]
      ring
    rw [he] at hh
    exact hh.trans (le_add_of_nonneg_left (by positivity))

lemma sqrt_three_quarters {x : ℝ} (hx : 0 < x) :
    Real.sqrt (x * Real.sqrt x) = x ^ (3 / 4 : ℝ) := by
  rw [Real.sqrt_mul hx.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
  norm_num

lemma mul_sqrt_three_halves {x : ℝ} (hx : 0 < x) : x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
  calc
    x * Real.sqrt x = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
    _ = x ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hx _ _).symm
    _ = _ := by norm_num

lemma explicit_execution_budget {p : Params} (hv : spec.valid p) :
    (((tuning p).primalSteps + 1) * ((tuning p).dualSteps + 1) : ℕ) +
      ((tuning p).refinementSteps + 1 : ℕ) *
      (1 + (8 / ((tuning p).smoothness * (tuning p).threshold ^ 3) +
        4 / ((tuning p).smoothness * (tuning p).mesh ^ 3)) * p.Δ) ≤
    10000000000 * (1 + p.L / p.μ + p.Δ * Real.sqrt p.ρ * (p.L / p.μ) ^ (3 / 4 : ℝ) /
      p.ε ^ (3 / 2 : ℝ) + p.Δ * p.ρ ^ 2 / p.μ ^ 3) * Real.log (budgetRadius p) ^ 2 := by
  let l := Real.log (budgetRadius p)
  let G := Real.sqrt p.ρ * Real.sqrt ((p.L / p.μ) * Real.sqrt (p.L / p.μ)) / (p.ε * Real.sqrt p.ε)
  let H := p.ρ ^ 2 / p.μ ^ 3
  let A := p.Δ * G
  let B := p.Δ * H
  let P := 1 + 491520 * A + 39845888 * B
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hε := hv.2.2.2.2.2
  have hΔ := hv.2.2.2.1
  have hk := tuning_condition hv
  have hκ : 0 < p.L / p.μ := by linarith only [hk]
  have hl : 1 ≤ l := budgetRadius_log hv
  have hl0 : 0 ≤ l := by linarith only [hl]
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hA : 0 ≤ A := mul_nonneg hΔ hG
  have hB : 0 ≤ B := mul_nonneg hΔ hH
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hinit : ((((tuning p).primalSteps + 1) * ((tuning p).dualSteps + 1) : ℕ) : ℝ) ≤
      93458 * (p.L / p.μ) * l ^ 2 := by
    have hh := mul_le_mul (tuning_primal_log_bound hv) (tuning_dual_log_bound hv)
      (Nat.cast_nonneg ((tuning p).dualSteps + 1) : (0 : ℝ) ≤ ((tuning p).dualSteps + 1 : ℕ))
      (show 0 ≤ 83 * Real.log (budgetRadius p) by linarith only [hl])
    rw [Nat.cast_mul]
    convert hh using 1; dsimp [l]; ring
  have hcinv : 1 / ((tuning p).smoothness * (tuning p).threshold ^ 3) ≤ 61440 * G + 3932160 * H := by
    convert tuning_cubic_inverse_bound hv using 1; dsimp [G, H]; ring
  have hminv : 1 / ((tuning p).smoothness * (tuning p).mesh ^ 3) ≤ 2097152 * H := by
    convert tuning_mesh_inverse hv using 1; dsimp [H]; ring
  have hc := mul_le_mul_of_nonneg_right hcinv hΔ
  have hm := mul_le_mul_of_nonneg_right hminv hΔ
  have hseg : 1 + (8 / ((tuning p).smoothness * (tuning p).threshold ^ 3) +
      4 / ((tuning p).smoothness * (tuning p).mesh ^ 3)) * p.Δ ≤ P := by
    have hh : 1 + (8 * (1 / ((tuning p).smoothness * (tuning p).threshold ^ 3)) +
        4 * (1 / ((tuning p).smoothness * (tuning p).mesh ^ 3))) * p.Δ ≤
        1 + 491520 * (p.Δ * G) + 39845888 * (p.Δ * H) := by
      nlinarith only [hc, hm]
    convert hh using 1; ring
  have hM := (tuning_positive hv).1
  have hs := (tuning_positive hv).2.2.2.2.1
  have hmesh := (tuning_positive hv).2.2.1
  have houter := mul_le_mul (tuning_refinement_log_bound hv) hseg
    (show 0 ≤ 1 + (8 / ((tuning p).smoothness * (tuning p).threshold ^ 3) +
      4 / ((tuning p).smoothness * (tuning p).mesh ^ 3)) * p.Δ by positivity)
    (show 0 ≤ 247 * Real.log (budgetRadius p) by linarith only [hl])
  have hscale := mul_le_mul_of_nonneg_right (show l ≤ l ^ 2 by nlinarith only [hl])
    (show 0 ≤ 247 * P by positivity)
  have hcoef : 93458 * (p.L / p.μ) + 247 * P ≤ 10000000000 * (1 + p.L / p.μ + A + B) := by
    dsimp [P]
    nlinarith only [hk, hA, hB]
  have hlast := mul_le_mul_of_nonneg_right hcoef (sq_nonneg l)
  have hraw := add_le_add hinit houter
  have hfinal : (((tuning p).primalSteps + 1) * ((tuning p).dualSteps + 1) : ℕ) +
      ((tuning p).refinementSteps + 1 : ℕ) *
      (1 + (8 / ((tuning p).smoothness * (tuning p).threshold ^ 3) +
        4 / ((tuning p).smoothness * (tuning p).mesh ^ 3)) * p.Δ) ≤
      10000000000 * (1 + p.L / p.μ + A + B) * l ^ 2 := by
    change _ ≤ 93458 * (p.L / p.μ) * l ^ 2 + (247 * l) * P at hraw
    nlinarith only [hraw, hscale, hlast]
  convert hfinal using 1
  dsimp [A, B, G, H, l]
  rw [sqrt_three_quarters hκ, mul_sqrt_three_halves hε]
  ring

end OracleTemplate.PLMinimax
