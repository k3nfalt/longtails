import LongTails.Algorithms.CovarianceSoftCutMethod
import Mathlib.Analysis.SpecialFunctions.Log.Base

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutTuning

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCutMethod

lemma ceil_power_two_bounds (x : ℝ) (hx : 1 ≤ x) :
    x ≤ (2 : ℝ)^⌈Real.log x/Real.log 2⌉₊ ∧
    (2 : ℝ)^⌈Real.log x/Real.log 2⌉₊ < 2*x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 ≤ Real.log x/Real.log 2 := div_nonneg (Real.log_nonneg hx) (Real.log_nonneg (by norm_num))
  have he : (2 : ℝ)^(Real.log x/Real.log 2) = x :=
    Real.rpow_logb (by norm_num) (by norm_num) hxpos
  constructor
  · calc
      x = (2 : ℝ)^(Real.log x/Real.log 2) := he.symm
      _ ≤ (2 : ℝ)^((⌈Real.log x/Real.log 2⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = _ := Real.rpow_natCast _ _
  · have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (Nat.ceil_lt_add_one hlog)
    rw [Real.rpow_natCast, Real.rpow_add (by norm_num : (0 : ℝ) < 2), he, Real.rpow_one] at hh
    simpa only [mul_comm] using hh

lemma max_ceil_lower (x : ℝ) : x ≤ (max 1 ⌈x⌉₊ : ℕ) :=
  (Nat.le_ceil x).trans (by exact_mod_cast (le_max_right 1 ⌈x⌉₊))

lemma max_ceil_upper (x : ℝ) (hx : 0 ≤ x) : (max 1 ⌈x⌉₊ : ℕ) ≤ x+1 := by
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (Nat.ceil_lt_add_one hx).le

lemma tuned_batch_pos (q : Params) : 0 < (tunedConfig q).b ∧ 0 < (tunedConfig q).n ∧ 0 < (tunedConfig q).m := by
  unfold tunedConfig
  dsimp only
  exact ⟨lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _),
    lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _), Nat.succ_pos _⟩

lemma rounded_horizon (D z : ℝ) (hD : 0 ≤ D) (hz : 1 ≤ z) :
    let X := 24*(1+D*Real.log (16*z))
    let H := ⌈Real.log X/Real.log 2⌉₊
    0 < H ∧ D*Real.log (16*z) ≤ ((2^H : ℕ) : ℝ)/24 ∧
      ((2^H : ℕ) : ℝ) ≤ 48*(1+D*Real.log (16*z)) := by
  dsimp only
  have hlog : 0 ≤ Real.log (16*z) := Real.log_nonneg (by linarith)
  have hX : 1 < 24*(1+D*Real.log (16*z)) := by nlinarith [mul_nonneg hD hlog]
  have hH : 0 < ⌈Real.log (24*(1+D*Real.log (16*z)))/Real.log 2⌉₊ :=
    Nat.one_le_ceil_iff.mpr (div_pos (Real.log_pos hX) (Real.log_pos (by norm_num)))
  have hp := ceil_power_two_bounds (24*(1+D*Real.log (16*z))) hX.le
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact ⟨hH, by linarith [hp.1], by linarith [hp.2]⟩

lemma rounded_bisection (L R τ : ℝ) (hL : 0 < L) (hR : 0 < R) (hτ : 0 < τ)
    (hlarge : τ ≤ 4*L*R) :
    4*L*R ≤ τ*(2 : ℝ)^⌈Real.log (4*L*R/τ)/Real.log 2⌉₊ := by
  have hx : 1 ≤ 4*L*R/τ := (le_div_iff₀ hτ).mpr (by simpa using hlarge)
  have hp := (ceil_power_two_bounds _ hx).1
  have hh := mul_le_mul_of_nonneg_left hp hτ.le
  have he : τ*(4*L*R/τ) = 4*L*R := by field_simp
  simpa only [he] using hh

lemma rounded_mom_failure (C : ℕ) :
    (C : ℝ)*Real.exp (-((2*⌈4*Real.log (12*(max 1 C : ℕ))⌉₊+1 : ℕ) : ℝ)/8) ≤ 1/12 := by
  let M : ℝ := (max 1 C : ℕ)
  have hM : 0 < M := by dsimp [M]; exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left 1 C))
  have hC : (C : ℝ) ≤ M := by dsimp [M]; exact_mod_cast (le_max_right 1 C)
  have hceil := Nat.le_ceil (4*Real.log (12*M))
  have he : Real.exp (-((2*⌈4*Real.log (12*(max 1 C : ℕ))⌉₊+1 : ℕ) : ℝ)/8) ≤
      (12*M)⁻¹ := by
    calc
      _ ≤ Real.exp (-Real.log (12*M)) := by
        apply Real.exp_le_exp.mpr
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        change -(2*(⌈4*Real.log (12*M)⌉₊ : ℝ)+1)/8 ≤ -Real.log (12*M)
        linarith
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 12*M)]
  calc
    _ ≤ M*(12*M)⁻¹ := mul_le_mul hC he (Real.exp_pos _).le hM.le
    _ = 1/12 := by field_simp

lemma tuned_generator_batch (q : Params) (hd : 0 < q.d) (hε : 0 < q.ε) :
    1024*q.σ^2*q.R^2 ≤ (q.d : ℝ)*(tunedConfig q).b*(q.ε/2)^2 := by
  have hd' : (0 : ℝ) < q.d := by exact_mod_cast hd
  have hden : 0 < (q.d : ℝ)*q.ε^2 := mul_pos hd' (sq_pos_of_pos hε)
  have hc := max_ceil_lower (4096*q.σ^2*q.R^2/((q.d : ℝ)*q.ε^2))
  change 4096*q.σ^2*q.R^2/((q.d : ℝ)*q.ε^2) ≤ ((tunedConfig q).b : ℝ) at hc
  have hh := (div_le_iff₀ hden).mp hc
  nlinarith

lemma tuned_selection_batch (q : Params) (hd : 0 < q.d) (ha : 0 < (tunedConfig q).a) :
    8*q.σ^2 ≤ (q.d : ℝ)*(tunedConfig q).n*(tunedConfig q).a^2 := by
  have hd' : (0 : ℝ) < q.d := by exact_mod_cast hd
  have hden : 0 < (q.d : ℝ)*(tunedConfig q).a^2 := mul_pos hd' (sq_pos_of_pos ha)
  have hc := max_ceil_lower (8*q.σ^2/((q.d : ℝ)*(tunedConfig q).a^2))
  change 8*q.σ^2/((q.d : ℝ)*(tunedConfig q).a^2) ≤ ((tunedConfig q).n : ℝ) at hc
  have hh := (div_le_iff₀ hden).mp hc
  nlinarith

lemma tuned_height (q : Params) (hε : 0 < q.ε) (hsmall : q.ε < q.L*q.R) :
    0 < (tunedConfig q).H ∧
    (q.d : ℝ)*Real.log (8*q.L*q.R/(q.ε/2)) ≤ ((2^(tunedConfig q).H : ℕ) : ℝ)/24 ∧
    ((2^(tunedConfig q).H : ℕ) : ℝ) ≤ 48*(1+(q.d : ℝ)*Real.log (16*q.L*q.R/q.ε)) := by
  have hz : 1 ≤ q.L*q.R/q.ε := (le_div_iff₀ hε).mpr (by linarith)
  have hp := rounded_horizon (q.d : ℝ) (q.L*q.R/q.ε) (Nat.cast_nonneg _) hz
  have he : 16*(q.L*q.R/q.ε) = 16*q.L*q.R/q.ε := by ring
  dsimp only at hp
  rw [he] at hp
  have hα : 8*q.L*q.R/(q.ε/2) = 16*q.L*q.R/q.ε := by field_simp; ring
  rw [hα]
  exact hp

lemma tuned_accuracy_parameters (q : Params) (hL : 0 < q.L) (hR : 0 < q.R)
    (hε : 0 < q.ε) (hsmall : q.ε < q.L*q.R) :
    let τ := q.ε/(2*((tunedConfig q).H : ℝ))
    0 < τ ∧ 0 < (tunedConfig q).a ∧ (tunedConfig q).a = τ/(12*q.R) ∧
      4*q.L*q.R ≤ τ*(2 : ℝ)^(tunedConfig q).K ∧
      q.ε/2+((tunedConfig q).H : ℝ)*τ = q.ε := by
  let τ := q.ε/(2*((tunedConfig q).H : ℝ))
  have hH := (tuned_height q hε hsmall).1
  have hH' : (0 : ℝ) < (tunedConfig q).H := by exact_mod_cast hH
  have hHone : (1 : ℝ) ≤ (tunedConfig q).H := by exact_mod_cast hH
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτbound : τ ≤ q.ε/2 := by
    dsimp [τ]
    apply (div_le_iff₀ (by positivity : 0 < 2*((tunedConfig q).H : ℝ))).mpr
    nlinarith
  have ha : (tunedConfig q).a = τ/(12*q.R) := rfl
  have hapos : 0 < (tunedConfig q).a := by rw [ha]; positivity
  have hpower : 4*q.L*q.R ≤ τ*(2 : ℝ)^(tunedConfig q).K :=
    rounded_bisection q.L q.R τ hL hR hτ (by nlinarith [mul_pos hL hR])
  refine ⟨hτ, hapos, ha, hpower, ?_⟩
  field_simp
  ring

end LongTails.Proofs.CovarianceSoftCutTuning
