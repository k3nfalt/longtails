import LongTails.Algorithms.LogFreeProxNewton

namespace LongTails.Proofs.LogFreeParameters

open LongTails.Setups.ThirdDerivativeSmoothNonconvex LongTails.Algorithms.LogFreeProxNewton

variable (p : Params)

lemma scale_pos (hp : spec.valid p) : 0 < scale p := by
  obtain ⟨hL, -, -, hε⟩ := hp
  unfold scale
  exact Real.rpow_pos_of_pos (div_pos hε hL) _

lemma scale_cube (hp : spec.valid p) : p.L₃ * scale p ^ 3 = p.ε := by
  obtain ⟨hL, -, -, hε⟩ := hp
  unfold scale
  have h : ((p.ε / p.L₃) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = p.ε / p.L₃ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hε hL).le]
    norm_num
  rw [h]; field_simp

lemma unit_eq (hp : spec.valid p) : unit p = p.L₃ * scale p ^ 4 := by
  unfold unit
  rw [← scale_cube p hp]; ring

lemma unit_pos (hp : spec.valid p) : 0 < unit p := by
  rw [unit_eq p hp]; have := scale_pos p hp; have := hp.1; positivity

lemma weight_eq : weight p = 256 * p.L₃ * scale p ^ 2 := rfl

lemma weight_pos (hp : spec.valid p) : 0 < weight p := by
  rw [weight_eq]; have := scale_pos p hp; have := hp.1; positivity

lemma weight_scale (hp : spec.valid p) : weight p * scale p ^ 2 = 256 * unit p := by
  rw [weight_eq, unit_eq p hp]; ring

lemma weight_unit_sq (hp : spec.valid p) : weight p * unit p = 256 * p.ε ^ 2 := by
  rw [weight_eq, unit_eq p hp, ← scale_cube p hp]; ring

lemma complexity_eq (hp : spec.valid p) : complexity p = p.Δ / unit p := by
  obtain ⟨hL, hΔ, -, hε⟩ := hp
  unfold complexity unit scale
  rw [Real.div_rpow hε.le hL.le]
  have h43 : p.ε ^ (4 / 3 : ℝ) = p.ε * p.ε ^ (1 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hε, Real.rpow_one]
  have hL3 : 0 < p.L₃ ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hL _
  have hε3 : 0 < p.ε ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hε _
  rw [h43]; field_simp

lemma complexity_cube (hp : spec.valid p) :
    complexity p ^ 3 = p.L₃ * p.Δ ^ 3 / p.ε ^ 4 := by
  rw [complexity_eq p hp, unit_eq p hp]
  have hL := hp.1
  have hε := hp.2.2.2
  have hr := scale_pos p hp
  have hc := scale_cube p hp
  rw [← hc]; field_simp
  try ring

lemma logArgument_ge (hp : spec.valid p) : 2 ≤ logArgument p := by
  obtain ⟨hL, hΔ, hH, hε⟩ := hp
  unfold logArgument; have : 0 ≤ p.H₀ * p.Δ / p.ε ^ 2 := by positivity
  have : 0 ≤ p.L₃ * p.Δ ^ 3 / p.ε ^ 4 := by positivity
  linarith

lemma complexity_le_log (hp : spec.valid p) : complexity p ≤ logArgument p := by
  have hc := complexity_cube p hp
  have hS : 0 ≤ complexity p := by
    rw [complexity_eq p hp]; exact div_nonneg hp.2.1.le (unit_pos p hp).le
  have hΓ := logArgument_ge p hp
  have hle : complexity p ^ 3 ≤ logArgument p := by
    rw [hc]; unfold logArgument
    have : 0 ≤ p.H₀ * p.Δ / p.ε ^ 2 := by
      have := hp.2.2.1; have := hp.2.1; have := hp.2.2.2; positivity
    linarith
  by_contra h
  have h' : logArgument p < complexity p := lt_of_not_ge h
  have h1 : 1 < complexity p := by linarith
  have h2 : complexity p < complexity p ^ 2 := by nlinarith
  have : complexity p < complexity p ^ 3 := by nlinarith
  linarith

end LongTails.Proofs.LogFreeParameters
