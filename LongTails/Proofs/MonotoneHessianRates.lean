import LongTails.Proofs.MonotoneHessianParameters

namespace LongTails.Proofs.MonotoneHessianRates

open LongTails.Setups.HessianLipschitzSecondOrder LongTails.Algorithms.MonotoneHessianReuse

noncomputable def size (p : Params) : ℝ := p.Δ * Real.sqrt p.H / (p.ε * Real.sqrt p.ε)
noncomputable def rootCost (p : Params) : ℝ := p.m ^ (1 / 3 : ℝ)
noncomputable def logArgument (p : Params) : ℝ :=
  2 + (Module.finrank ℝ p.E + 1 : ℝ) * p.m * (1 + size p) / p.ρ

lemma size_nonneg (p : Params) (hp : spec.valid p) : 0 ≤ size p := by
  unfold size
  exact div_nonneg (mul_nonneg hp.2.1 (Real.sqrt_nonneg _))
    (mul_nonneg hp.2.2.1.le (Real.sqrt_nonneg _))

lemma rootCost_ge_one (p : Params) (hp : spec.valid p) : 1 ≤ rootCost p :=
  Real.one_le_rpow hp.2.2.2.1 (by norm_num)

lemma rootCost_pos (p : Params) (hp : spec.valid p) : 0 < rootCost p :=
  zero_lt_one.trans_le (rootCost_ge_one p hp)

lemma rootCost_cube (p : Params) (hp : spec.valid p) : rootCost p ^ 3 = p.m := by
  have hm : 0 ≤ p.m := zero_le_one.trans hp.2.2.2.1
  rw [rootCost, ← Real.rpow_natCast, ← Real.rpow_mul hm]
  norm_num

lemma rootCost_le_m (p : Params) (hp : spec.valid p) : rootCost p ≤ p.m := by
  have hr := rootCost_ge_one p hp
  have he := rootCost_cube p hp
  have hh := mul_le_mul_of_nonneg_left (show 1 ≤ rootCost p ^ 2 by nlinarith) (zero_le_one.trans hr)
  nlinarith

lemma scale_bounds (p : Params) (hp : spec.valid p) : rootCost p ≤ scale p ∧ scale p ≤ 2 * rootCost p := by
  have hr := rootCost_ge_one p hp
  have hceil := Nat.le_ceil (rootCost p)
  have hupper := Nat.ceil_lt_add_one (rootCost_pos p hp).le
  constructor
  · exact hceil.trans (le_max_right _ _)
  · apply max_le
    · linarith
    · change (⌈rootCost p⌉₊ : ℝ) ≤ 2 * rootCost p
      linarith

lemma size_progress (p : Params) (hp : spec.valid p) : p.Δ / progress p = 2 ^ 60 * size p := by
  have hH : 0 < Real.sqrt p.H := Real.sqrt_pos.mpr hp.1
  have hε : 0 < Real.sqrt p.ε := Real.sqrt_pos.mpr hp.2.2.1
  have hγ : gamma p = Real.sqrt p.H * Real.sqrt p.ε := Real.sqrt_mul hp.1.le _
  have he : p.Δ / ((Real.sqrt p.H * Real.sqrt p.ε) *
      ((Real.sqrt p.H * Real.sqrt p.ε) / (2 ^ 30 * (Real.sqrt p.H) ^ 2)) ^ 2) =
      2 ^ 60 * (p.Δ * Real.sqrt p.H / ((Real.sqrt p.ε) ^ 2 * Real.sqrt p.ε)) := by
    field_simp
  simpa only [Real.sq_sqrt hp.1.le, Real.sq_sqrt hp.2.2.1.le, ← hγ, progress, size] using he

lemma stages_bound (p : Params) (hp : spec.valid p) : (stages p : ℝ) ≤ 2 ^ 61 * (1 + size p) := by
  have hs := size_nonneg p hp
  have hq := MonotoneHessianParameters.progress_pos p hp
  have hh := Nat.ceil_lt_add_one (div_nonneg hp.2.1 hq.le)
  rw [size_progress p hp] at hh
  simp only [stages, Nat.cast_add, Nat.cast_one]
  rw [size_progress p hp]
  nlinarith

lemma logArgument_bounds (p : Params) (hp : spec.valid p) :
    2 ≤ logArgument p ∧ (Module.finrank ℝ p.E + 1 : ℝ) * p.m ≤ logArgument p ∧
      (1 + size p) / p.ρ ≤ logArgument p := by
  have hs := size_nonneg p hp
  have hm := hp.2.2.2.1
  have hρ := hp.2.2.2.2.1
  have hρ₁ := hp.2.2.2.2.2
  have hd : 0 ≤ (Module.finrank ℝ p.E : ℝ) := Nat.cast_nonneg _
  have hdm : 1 ≤ (Module.finrank ℝ p.E + 1 : ℝ) * p.m := by nlinarith
  have hratio : 1 ≤ (1 + size p) / p.ρ := (le_div_iff₀ hρ).mpr (by linarith)
  have hprod := mul_le_mul_of_nonneg_left hratio (show 0 ≤ (Module.finrank ℝ p.E + 1 : ℝ) * p.m by linarith)
  have hother := mul_le_mul_of_nonneg_right hdm (show 0 ≤ (1 + size p) / p.ρ by positivity)
  simp only [← mul_div_assoc, one_mul, mul_one] at hprod hother
  unfold logArgument
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  constructor <;> nlinarith

lemma log_lower (p : Params) (hp : spec.valid p) : (1 : ℝ) / 2 ≤ Real.log (logArgument p) := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (logArgument_bounds p hp).1
  norm_num at hh
  linarith

lemma log_monomial (p : Params) (hp : spec.valid p) (x : ℝ) (hx : 0 < x) (a b : ℕ)
    (hb : x ≤ (2 : ℝ) ^ a * logArgument p ^ b) :
    Real.log x ≤ (a + b : ℝ) * Real.log (logArgument p) := by
  have hA : 0 < logArgument p := lt_of_lt_of_le (by norm_num) (logArgument_bounds p hp).1
  have hlog₂ := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (logArgument_bounds p hp).1
  have hh := Real.log_le_log hx hb
  rw [Real.log_mul (by positivity) (pow_pos hA b).ne', Real.log_pow, Real.log_pow] at hh
  have hm := mul_le_mul_of_nonneg_left hlog₂ (Nat.cast_nonneg a)
  nlinarith

lemma horizon_bound (p : Params) (hp : spec.valid p) :
    (LongTails.Algorithms.MonotoneCurvatureStage.horizon (scale p) : ℝ) ≤
      2 ^ 16 * rootCost p * Real.log (logArgument p) := by
  have ht := MonotoneHessianParameters.scale_ge_one p
  have ht0 := MonotoneHessianParameters.scale_pos p
  have hr := rootCost_ge_one p hp
  have hscale := (scale_bounds p hp).2
  have hm := rootCost_le_m p hp
  have hA := logArgument_bounds p hp
  have hd : 0 ≤ (Module.finrank ℝ p.E : ℝ) := Nat.cast_nonneg _
  have hm0 : 0 ≤ p.m := zero_le_one.trans hp.2.2.2.1
  have hmA : p.m ≤ logArgument p := by nlinarith [mul_nonneg hd hm0]
  have hl := log_lower p hp
  have hlog := log_monomial p hp (2 + scale p) (by positivity) 2 1 (by norm_num; linarith)
  norm_num at hlog
  have hlog0 : 0 ≤ Real.log (2 + scale p) := Real.log_nonneg (by linarith)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (2 : ℝ) ^ 13 * scale p * Real.log (2 + scale p) by positivity)
  change (LongTails.Algorithms.MonotoneCurvatureStage.horizon (scale p) : ℝ) < _ at hceil
  have hh := mul_le_mul hscale hlog hlog0 (show 0 ≤ 2 * rootCost p by linarith)
  have hprod : (1 : ℝ) / 2 ≤ rootCost p * Real.log (logArgument p) := by nlinarith
  nlinarith

lemma degree_bound (p : Params) (hp : spec.valid p) :
    (degree p : ℝ) ≤ 2 ^ 10 * rootCost p * Real.log (logArgument p) := by
  have ht := MonotoneHessianParameters.scale_pos p
  have ht₁ := MonotoneHessianParameters.scale_ge_one p
  have hr := rootCost_ge_one p hp
  have hm := rootCost_le_m p hp
  have hs := (scale_bounds p hp).2
  have ha := MonotoneHessianParameters.relative_tolerance_range p hp
  have hA := logArgument_bounds p hp
  have hA0 : 0 ≤ logArgument p := (by norm_num : (0 : ℝ) ≤ 2).trans hA.1
  have hd : 0 ≤ (Module.finrank ℝ p.E : ℝ) := Nat.cast_nonneg _
  have hm₁ := hp.2.2.2.1
  have hm0 : 0 ≤ p.m := zero_le_one.trans hm₁
  have hmA : p.m ≤ logArgument p := by nlinarith [mul_nonneg hd hm0]
  have hmax : max 1 (Module.finrank ℝ p.E : ℝ) ≤ (Module.finrank ℝ p.E : ℝ) + 1 := by
    apply max_le <;> linarith
  have hmax0 : 0 ≤ max 1 (Module.finrank ℝ p.E : ℝ) := le_trans zero_le_one (le_max_left _ _)
  have harg : 16 * max 1 (Module.finrank ℝ p.E : ℝ) / relativeTolerance p =
      1024 * max 1 (Module.finrank ℝ p.E : ℝ) * scale p ^ 2 := by
    rw [MonotoneHessianParameters.relative_tolerance p hp]
    field_simp
    ring
  have ht₂ : scale p ^ 2 ≤ 4 * p.m ^ 2 := by nlinarith
  have hprod := mul_le_mul hmax ht₂ (sq_nonneg _) (show 0 ≤ (Module.finrank ℝ p.E : ℝ) + 1 by positivity)
  have hprodA := mul_le_mul hA.2.1 hmA hm0 hA0
  have hargBound : 16 * max 1 (Module.finrank ℝ p.E : ℝ) / relativeTolerance p ≤
      (2 : ℝ) ^ 12 * logArgument p ^ 2 := by rw [harg]; nlinarith
  have harg₁ : 1 ≤ 16 * max 1 (Module.finrank ℝ p.E : ℝ) / relativeTolerance p := by
    apply (le_div_iff₀ ha.1).mpr
    have hh := le_max_left (1 : ℝ) (Module.finrank ℝ p.E)
    nlinarith [ha.2]
  have hlog := log_monomial p hp _ (zero_lt_one.trans_le harg₁) 12 2 hargBound
  norm_num at hlog
  have hlog0 := Real.log_nonneg harg₁
  have hsqrt : Real.sqrt (relativeTolerance p) = 1 / (8 * scale p) := by
    apply (Real.sqrt_eq_iff_eq_sq ha.1.le (by positivity)).mpr
    rw [MonotoneHessianParameters.relative_tolerance p hp]
    field_simp
    ring
  have he : 2 * Real.log (16 * max 1 (Module.finrank ℝ p.E : ℝ) / relativeTolerance p) /
      Real.sqrt (relativeTolerance p) =
      16 * scale p * Real.log (16 * max 1 (Module.finrank ℝ p.E : ℝ) / relativeTolerance p) := by
    rw [hsqrt]
    field_simp
    ring
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.log
    (16 * max 1 (Module.finrank ℝ p.E : ℝ) / relativeTolerance p) / Real.sqrt (relativeTolerance p) by positivity)
  change (degree p : ℝ) < _ at hceil
  rw [he] at hceil
  have hh := mul_le_mul hs hlog hlog0 (show 0 ≤ 2 * rootCost p by linarith)
  have hl := log_lower p hp
  have hprod : (1 : ℝ) / 2 ≤ rootCost p * Real.log (logArgument p) := by nlinarith
  nlinarith

lemma repetitions_bound (p : Params) (hp : spec.valid p) :
    (repetitions p : ℝ) ≤ 2 ^ 12 * Real.log (logArgument p) := by
  have hρ := hp.2.2.2.2.1
  have hρ₁ := hp.2.2.2.2.2
  have hK : 1 ≤ (stages p : ℝ) := by unfold stages; simp only [Nat.cast_add, Nat.cast_one]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have harg₁ : 1 ≤ (stages p : ℝ) / p.ρ := (le_div_iff₀ hρ).mpr (by linarith)
  have hbound := div_le_div_of_nonneg_right (stages_bound p hp) hρ.le
  have hA := (logArgument_bounds p hp).2.2
  have hb : (stages p : ℝ) / p.ρ ≤ (2 : ℝ) ^ 61 * logArgument p ^ 1 := by
    have hh := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ (2 : ℝ) ^ 61)
    rw [← mul_div_assoc] at hh
    simpa only [pow_one] using hbound.trans hh
  have hlog := log_monomial p hp _ (zero_lt_one.trans_le harg₁) 61 1 hb
  norm_num at hlog
  have hlog0 := Real.log_nonneg harg₁
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 16 * Real.log ((stages p : ℝ) / p.ρ) by positivity)
  change (repetitions p : ℝ) < _ at hceil
  have hl := log_lower p hp
  nlinarith

lemma total_calls_bound (p : Params) (hp : spec.valid p) :
    ((stageCalls p + searchCalls p + 2) * stages p + 1 : ℕ) ≤
      ⌈2 ^ 120 * rootCost p * (1 + size p) * Real.log (logArgument p) ^ 2⌉₊ := by
  have hr := rootCost_ge_one p hp
  have hs := size_nonneg p hp
  have hl := log_lower p hp
  have hN := horizon_bound p hp
  have hD := degree_bound p hp
  have hR := repetitions_bound p hp
  have hK := stages_bound p hp
  have hprod : (1 : ℝ) / 2 ≤ rootCost p * Real.log (logArgument p) := by nlinarith
  have hstage : (stageCalls p : ℝ) ≤ 2 ^ 18 * rootCost p * Real.log (logArgument p) := by
    simp only [stageCalls, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hdeg : (degree p : ℝ) + 1 ≤ 2 ^ 11 * rootCost p * Real.log (logArgument p) := by nlinarith
  have hsearch := mul_le_mul hdeg hR (Nat.cast_nonneg (repetitions p)) (by positivity :
    0 ≤ 2 ^ 11 * rootCost p * Real.log (logArgument p))
  have hstep : (stageCalls p + searchCalls p + 2 : ℕ) ≤
      2 ^ 25 * rootCost p * Real.log (logArgument p) ^ 2 := by
    simp only [Nat.cast_add, Nat.cast_ofNat, searchCalls, Nat.cast_mul, Nat.cast_one] at hsearch ⊢
    have hlift := mul_le_mul_of_nonneg_left hl (show 0 ≤ rootCost p * Real.log (logArgument p) by positivity)
    nlinarith
  have htotal := mul_le_mul hstep hK (Nat.cast_nonneg (stages p))
    (show 0 ≤ 2 ^ 25 * rootCost p * Real.log (logArgument p) ^ 2 by positivity)
  apply (Nat.cast_le (α := ℝ)).mp
  apply le_trans ?_ (Nat.le_ceil _)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at htotal ⊢
  have hpositive : (1 : ℝ) / 4 ≤ rootCost p * (1 + size p) * Real.log (logArgument p) ^ 2 := by
    have h₁ : 1 ≤ rootCost p * (1 + size p) := by nlinarith
    have h₂ : (1 : ℝ) / 4 ≤ Real.log (logArgument p) ^ 2 := by nlinarith
    nlinarith
  nlinarith

end LongTails.Proofs.MonotoneHessianRates
