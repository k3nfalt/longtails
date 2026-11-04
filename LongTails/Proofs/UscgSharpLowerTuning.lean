import Mathlib

namespace LongTails.Proofs.UscgSharpLowerTuning

lemma log_memory {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1 / 2) :
    -2 * α ≤ Real.log (1 - α) := by
  have hb : 0 < 1 - α := by linarith
  have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hb)
  rw [Real.log_inv] at hh
  have hi : (1 - α)⁻¹ - 1 ≤ 2 * α := by
    apply (sub_le_iff_le_add).mpr
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hb).mpr
    nlinarith
  linarith

lemma decay_lower {α ell : ℝ} {k : ℕ} (ha : 0 < α) (ha1 : α ≤ 1 / 2)
    (hk : (k : ℝ) ≤ ell / (8 * α)) :
    Real.exp (-ell / 4) ≤ (1 - α) ^ k := by
  have hb : 0 < 1 - α := by linarith
  have ht := (le_div_iff₀ (show 0 < 8 * α by positivity)).mp hk
  have hm := mul_le_mul_of_nonneg_left (log_memory ha ha1) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  calc
    _ ≤ Real.exp ((k : ℝ) * Real.log (1 - α)) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hb]

noncomputable def excursionLength (T : ℕ) (ell α : ℝ) : ℕ :=
  ⌊min ((T : ℝ) / 2) (ell / (8 * α))⌋₊

lemma length_bounds {T : ℕ} {ell α : ℝ} (hT : 4 ≤ T) (ha : 0 < α)
    (hell : 16 * α ≤ ell) :
    0 < excursionLength T ell α ∧ excursionLength T ell α < T ∧
    (excursionLength T ell α : ℝ) ≤ ell / (8 * α) ∧
    min ((T : ℝ) / 4) (ell / (16 * α)) ≤ excursionLength T ell α := by
  have hT' : (4 : ℝ) ≤ T := by exact_mod_cast hT
  have he : (2 : ℝ) ≤ ell / (8 * α) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hmin : (2 : ℝ) ≤ min ((T : ℝ) / 2) (ell / (8 * α)) := le_min (by linarith) he
  have hfloor := Nat.floor_le (le_trans (by norm_num : (0 : ℝ) ≤ 2) hmin)
  have hnear := Nat.lt_floor_add_one (min ((T : ℝ) / 2) (ell / (8 * α)))
  have hl : min ((T : ℝ) / 2) (ell / (8 * α)) / 2 ≤ excursionLength T ell α := by
    unfold excursionLength
    linarith
  have hpos : 0 < excursionLength T ell α := by
    have : (0 : ℝ) < excursionLength T ell α := by linarith
    exact_mod_cast this
  refine ⟨hpos, ?_, ?_, ?_⟩
  · have hh := hfloor.trans (min_le_left _ _)
    change (excursionLength T ell α : ℝ) ≤ (T : ℝ) / 2 at hh
    have : (excursionLength T ell α : ℝ) < T := by linarith
    exact_mod_cast this
  · exact hfloor.trans (min_le_right _ _)
  · have heq : min ((T : ℝ) / 2) (ell / (8 * α)) / 2 =
        min ((T : ℝ) / 4) (ell / (16 * α)) := by
      rw [← min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1 <;> field_simp <;> ring
    rwa [heq] at hl

lemma log_large {ell : ℝ} (hell : 256 ≤ ell) : Real.log ell ≤ ell / 16 := by
  have hp : 0 < ell := by linarith
  have hh := Real.log_le_sub_one_of_pos (div_pos hp (by norm_num : (0 : ℝ) < 256))
  rw [Real.log_div hp.ne' (by norm_num)] at hh
  have htwo : Real.log 2 ≤ 1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); norm_num at hh; exact hh
  have h256 : Real.log 256 ≤ 8 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
    linarith
  linarith

lemma horizon_log {A D ell : ℝ} {T : ℕ} (hA : 1 ≤ A) (hD : 1 ≤ D) (hT : 0 < T)
    (hell : 256 * (1 + Real.log A + Real.log D) ≤ ell)
    (horizon : (T : ℝ) ≤ A * Real.sqrt D * ell) :
    256 ≤ ell ∧ Real.log (T : ℝ) ≤ 17 * ell / 256 := by
  have hAp : 0 < A := by linarith
  have hDp : 0 < D := by linarith
  have hla := Real.log_nonneg hA
  have hld := Real.log_nonneg hD
  have he : 256 ≤ ell := by linarith
  have hep : 0 < ell := by linarith
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDp
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hh := Real.log_le_log ht horizon
  rw [Real.log_mul (mul_pos hAp hs).ne' hep.ne', Real.log_mul hAp.ne' hs.ne', Real.log_sqrt hDp.le] at hh
  have hl := log_large he
  exact ⟨he, by linarith⟩

lemma confidence_small {ell : ℝ} {T : ℕ} (he : 256 ≤ ell) (hT : 0 < T)
    (ht : Real.log (T : ℝ) ≤ 17 * ell / 256) :
    (T : ℝ) * Real.exp (-ell) ≤ 1 / 16 ∧
    Real.exp (-ell / 4) ≤ 1 / (16 * (T : ℝ) ^ 3) := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have htwo : Real.log 2 ≤ 1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); norm_num at hh; exact hh
  have h16 : Real.log 16 ≤ 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hfirst : 16 * (T : ℝ) * Real.exp (-ell) ≤ 1 := by
    calc
      _ = Real.exp (Real.log 16 + Real.log T + -ell) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hTp]
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsecond : 16 * (T : ℝ) ^ 3 * Real.exp (-ell / 4) ≤ 1 := by
    calc
      _ = Real.exp (Real.log 16 + 3 * Real.log T + -ell / 4) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
        have hh : Real.exp (3 * Real.log (T : ℝ)) = (T : ℝ) ^ 3 := by
          simpa using (Real.exp_nat_mul (Real.log (T : ℝ)) 3).trans (by rw [Real.exp_log hTp])
        rw [hh]
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  refine ⟨by linarith, ?_⟩
  apply (le_div_iff₀ (show 0 < 16 * (T : ℝ) ^ 3 by positivity)).mpr
  nlinarith

lemma length_geometry {D ell α : ℝ} {T : ℕ} (hD : 256 ≤ D) (hT : 4 ≤ T)
    (ha : 0 < α) (hell : 16 * α ≤ ell)
    (horizon : 64 * α * T ≤ Real.sqrt D * ell) :
    16 * (T : ℝ) ^ 2 ≤ D * (excursionLength T ell α : ℝ) ^ 2 := by
  have hs : (16 : ℝ) ≤ Real.sqrt D := by
    have hh := Real.sqrt_le_sqrt hD
    norm_num at hh
    exact hh
  have hsp : 0 < Real.sqrt D := by linarith
  have h₁ : 4 * (T : ℝ) / Real.sqrt D ≤ (T : ℝ) / 4 := by
    apply (div_le_iff₀ hsp).mpr
    nlinarith [mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  have h₂ : 4 * (T : ℝ) / Real.sqrt D ≤ ell / (16 * α) := by
    apply (div_le_div_iff₀ hsp (show 0 < 16 * α by positivity)).mpr
    nlinarith
  have hk := (le_min h₁ h₂).trans (length_bounds hT ha hell).2.2.2
  have hm := (div_le_iff₀ hsp).mp hk
  have hsq := pow_le_pow_left₀ (show 0 ≤ 4 * (T : ℝ) by positivity) hm 2
  rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith : 0 ≤ D)] at hsq
  nlinarith

lemma sqrt_exp_negative (ell : ℝ) : Real.sqrt (Real.exp (-ell)) = Real.exp (-ell / 2) := by
  apply (Real.sqrt_eq_iff_eq_sq (Real.exp_pos _).le (Real.exp_pos _).le).mpr
  rw [sq, ← Real.exp_add]
  congr 1
  ring

lemma shock_amplitude {ell σ ε L η α : ℝ} {k T : ℕ}
    (hσ : ε ≤ σ) (he : 0 < ε) (hL : 0 ≤ L) (hη : 0 ≤ η) (hT : 0 < T)
    (hk : k ≤ T) (hstep : L * η ≤ ε * T)
    (hsmall : Real.exp (-ell / 4) ≤ 1 / (16 * (T : ℝ) ^ 3))
    (hdecay : Real.exp (-ell / 4) ≤ (1 - α) ^ k) :
    2 * L * η * (k : ℝ) ^ 2 ≤
      (σ / (2 * Real.sqrt (Real.exp (-ell)))) * (1 - α) ^ k := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have hσp : 0 < σ := by linarith
  have hroot := sqrt_exp_negative ell
  have heq : Real.exp (-ell / 2) = Real.exp (-ell / 4) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hbase : (σ / (2 * Real.sqrt (Real.exp (-ell)))) * Real.exp (-ell / 4) =
      σ / (2 * Real.exp (-ell / 4)) := by
    rw [hroot, heq]
    field_simp
  have hs := (le_div_iff₀ (show 0 < 16 * (T : ℝ) ^ 3 by positivity)).mp hsmall
  have hbound : 2 * ε * (T : ℝ) ^ 3 ≤ σ / (2 * Real.exp (-ell / 4)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.exp (-ell / 4))).mpr
    have hh := mul_le_mul_of_nonneg_left hs he.le
    nlinarith
  have hk' : (k : ℝ) ≤ T := by exact_mod_cast hk
  have hksq : (k : ℝ) ^ 2 ≤ (T : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hm := mul_le_mul_of_nonneg_left hksq (show 0 ≤ L * η by positivity)
  have hn := mul_le_mul_of_nonneg_right hstep (sq_nonneg (T : ℝ))
  have harea : 2 * L * η * (k : ℝ) ^ 2 ≤ 2 * ε * (T : ℝ) ^ 3 := by nlinarith
  apply (harea.trans hbound).trans
  rw [← hbase]
  exact mul_le_mul_of_nonneg_left hdecay (by positivity)

end LongTails.Proofs.UscgSharpLowerTuning
