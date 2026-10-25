import LongTails.Algorithms.CachedJacobian
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace LongTails.Proofs.CachedJacobianTuning

open LongTails.Setups.LipschitzJacobianMonotone
open LongTails.Algorithms.CachedJacobian

lemma initialStep_pos {p : Params} (hL : 0 < p.L) (hD : 0 < p.D) (hm : 1 ≤ p.m) :
    0 < initialStep p := by
  have hm' : (0 : ℝ) < p.m := by exact_mod_cast (show 0 < p.m by omega)
  unfold initialStep
  positivity

lemma outerCount_pos (p : Params) : 0 < outerCount p := by unfold outerCount; omega

lemma initialStep_scale {p : Params} (hL : 0 < p.L) (hD : 0 < p.D) (hm : 1 ≤ p.m) :
    initialStep p * p.L * p.D ≤ 1 / 16384 := by
  have hm' : (1 : ℝ) ≤ p.m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < p.m := by linarith
  have heq : initialStep p * p.L * p.D = 1 / (16384 * p.m : ℝ) := by
    unfold initialStep
    field_simp
  rw [heq]
  apply one_div_le_one_div_of_le (by norm_num)
  linarith

lemma stepSize_pos {p : Params} (hL : 0 < p.L) (hD : 0 < p.D) (hm : 1 ≤ p.m) (t : ℕ) :
    0 < stepSize p t := by
  have ha := initialStep_pos hL hD hm
  unfold stepSize
  positivity

lemma stepSize_mono {p : Params} (ha : 0 ≤ initialStep p) {i j : ℕ} (hij : i ≤ j) :
    stepSize p i ≤ stepSize p j := by
  unfold stepSize
  gcongr

lemma cacheRadius_pos {p : Params} (hL : 0 < p.L) (hD : 0 < p.D) (hm : 1 ≤ p.m) :
    0 < cacheRadius p := by
  have hη := stepSize_pos hL hD hm (outerCount p - 1)
  unfold cacheRadius
  positivity

lemma cache_scale {p : Params} (hL : 0 < p.L) (hD : 0 < p.D) (hm : 1 ≤ p.m)
    {t : ℕ} (ht : t < outerCount p) : stepSize p t * p.L * cacheRadius p ≤ 1 / 16 := by
  have ha := initialStep_pos hL hD hm
  have hη := stepSize_pos hL hD hm (outerCount p - 1)
  have hR := cacheRadius_pos hL hD hm
  have hmon := stepSize_mono ha.le (show t ≤ outerCount p - 1 by omega)
  have heq : stepSize p (outerCount p - 1) * p.L * cacheRadius p = 1 / 16 := by
    unfold cacheRadius
    field_simp
  rw [← heq]
  gcongr

lemma initial_root_scale {p : Params} (hL : 0 < p.L) (hD : 0 < p.D) (hm : 1 ≤ p.m) :
    stepSize p 0 * p.L * p.D ≤ 1 / 64 := by
  have h := initialStep_scale hL hD hm
  simp only [stepSize, Nat.cast_zero, zero_add, mul_div_cancel_right₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
  linarith

lemma warm_root_scale {p : Params} (hL : 0 < p.L) (hD : 0 < p.D) (hm : 1 ≤ p.m)
    {t : ℕ} (ht : 1 ≤ t) {r : ℝ} (hr : r ≤ 56 * p.D / t) :
    stepSize p t * p.L * r ≤ 1 / 64 := by
  have ha := initialStep_pos hL hD hm
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htp : (0 : ℝ) < t := by linarith
  have hs := initialStep_scale hL hD hm
  have hη := stepSize_pos hL hD hm t
  have hbound : stepSize p t * p.L * r ≤ 75 * (initialStep p * p.L * p.D) := by
    apply le_trans (mul_le_mul_of_nonneg_left hr (mul_nonneg hη.le hL.le))
    unfold stepSize
    apply (mul_le_mul_iff_left₀ htp).mp
    have heq : initialStep p * (t + 3) / 3 * p.L * (56 * p.D / t) * t =
        (initialStep p * p.L * p.D) * (56 / 3) * (t + 3) := by field_simp
    rw [heq]
    have hc : (56 / 3 : ℝ) * (t + 3) ≤ 75 * t := by linarith
    have hh := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ initialStep p * p.L * p.D by positivity)
    nlinarith only [hh]
  linarith

lemma accuracy_budget {p : Params} (hL : 0 < p.L) (hD : 0 < p.D)
    (hε : 0 < p.ε) (hm : 1 ≤ p.m) :
    40 * p.D / (initialStep p * (outerCount p : ℝ) ^ 2) ≤ p.ε := by
  have hm' : (0 : ℝ) < p.m := by exact_mod_cast (show 0 < p.m by omega)
  have ha := initialStep_pos hL hD hm
  have hT : (0 : ℝ) < outerCount p := by exact_mod_cast outerCount_pos p
  let A := (p.m : ℝ) * p.L * p.D ^ 2 / p.ε
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc : 1024 * Real.sqrt A ≤ (outerCount p : ℝ) := by
    have hh := Nat.le_ceil (1024 * Real.sqrt A)
    dsimp [outerCount, A] at *
    push_cast
    linarith
  have hs := mul_self_le_mul_self (show 0 ≤ 1024 * Real.sqrt A by positivity) hc
  have hsq := Real.sq_sqrt hA
  have hp : 1048576 * A ≤ (outerCount p : ℝ) ^ 2 := by nlinarith
  have hmulp := mul_le_mul_of_nonneg_right hp hε.le
  have hAe : A * p.ε = (p.m : ℝ) * p.L * p.D ^ 2 := by dsimp [A]; field_simp
  have hmain : 655360 * p.m * p.L * p.D ^ 2 ≤ p.ε * (outerCount p : ℝ) ^ 2 := by
    nlinarith [mul_pos (mul_pos hm' hL) (sq_pos_of_pos hD)]
  apply (div_le_iff₀ (by positivity : 0 < initialStep p * (outerCount p : ℝ) ^ 2)).mpr
  unfold initialStep
  apply (mul_le_mul_iff_left₀ (show 0 < 16384 * (p.m : ℝ) * p.L * p.D by positivity)).mp
  field_simp
  nlinarith only [hmain]

lemma error_sums {E : Type*} [SeminormedAddCommGroup E] {D : ℝ} {T k : ℕ} {e : ℕ → E}
    (hD : 0 ≤ D) (hT : 0 < T) (hk : k < T)
    (he : ∀ t ≤ k, ‖e t‖ ≤ D / (T : ℝ) ^ 2) :
    (∑ t ∈ Finset.range (k + 1), ‖e t‖ ≤ D) ∧
      (∑ t ∈ Finset.range (k + 1), (t + 1 : ℝ) ^ 2 * ‖e t‖ ^ 2 ≤ D ^ 2) := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have hT₁ : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hkT : ((k + 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast (show k + 1 ≤ T by omega)
  have hδ : 0 ≤ D / (T : ℝ) ^ 2 := by positivity
  have hsum₁ : ∑ t ∈ Finset.range (k + 1), ‖e t‖ ≤ (T : ℝ) * (D / (T : ℝ) ^ 2) := by
    calc
      _ ≤ ∑ _t ∈ Finset.range (k + 1), D / (T : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun t ht => he t (by simpa using ht))
      _ = (k + 1 : ℝ) * (D / (T : ℝ) ^ 2) := by simp
      _ ≤ _ := by gcongr; exact_mod_cast hkT
  have hsum₂ : ∑ t ∈ Finset.range (k + 1), (t + 1 : ℝ) ^ 2 * ‖e t‖ ^ 2 ≤
      (T : ℝ) * ((T : ℝ) ^ 2 * (D / (T : ℝ) ^ 2) ^ 2) := by
    calc
      _ ≤ ∑ _t ∈ Finset.range (k + 1), (T : ℝ) ^ 2 * (D / (T : ℝ) ^ 2) ^ 2 := by
        apply Finset.sum_le_sum
        intro t ht
        have htk : t ≤ k := by simpa using ht
        have htT : (t + 1 : ℝ) ≤ T := by exact_mod_cast (show t + 1 ≤ T by omega)
        gcongr
        exact he t htk
      _ = (k + 1 : ℝ) * ((T : ℝ) ^ 2 * (D / (T : ℝ) ^ 2) ^ 2) := by simp
      _ ≤ _ := by gcongr; exact_mod_cast hkT
  constructor
  · apply hsum₁.trans
    have heq : (T : ℝ) * (D / (T : ℝ) ^ 2) = D / T := by field_simp
    rw [heq]
    apply (div_le_iff₀ hTp).mpr
    nlinarith
  · apply hsum₂.trans
    have heq : (T : ℝ) * ((T : ℝ) ^ 2 * (D / (T : ℝ) ^ 2) ^ 2) = D ^ 2 / T := by field_simp
    rw [heq]
    apply (div_le_iff₀ hTp).mpr
    nlinarith [mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hT₁)]

lemma inner_precision (p : Params) :
    (1 / 4 : ℝ) ^ innerCount p ≤ 1 / (outerCount p : ℝ) ^ 2 := by
  have hlog := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (outerCount p + 1)
  have hTpow : (outerCount p) ^ 2 ≤ 4 ^ innerCount p := by
    calc
      (outerCount p) ^ 2 ≤ (2 ^ (Nat.log 2 (outerCount p + 1) + 1)) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      _ = 4 ^ (Nat.log 2 (outerCount p + 1) + 1) := by
        rw [← pow_mul, Nat.mul_comm _ 2, pow_mul]
        norm_num
      _ ≤ 4 ^ innerCount p := Nat.pow_le_pow_right (by norm_num) (by unfold innerCount; omega)
  have hreal : (outerCount p : ℝ) ^ 2 ≤ (4 : ℝ) ^ innerCount p := by exact_mod_cast hTpow
  rw [one_div_pow]
  apply one_div_le_one_div_of_le _ hreal
  have hT : (0 : ℝ) < outerCount p := by exact_mod_cast outerCount_pos p
  positivity

lemma warm_distance_bound {a D : ℝ} {t : ℕ} (ha : 0 < a) (hD : 0 ≤ D) (ht : 1 ≤ t) :
    (2 / (t + 2 : ℝ)) * D + (a * (t + 3) / 3) * (40 * D / (a * (t : ℝ) ^ 2)) ≤
      56 * D / t := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htp : (0 : ℝ) < t := by linarith
  have h₁ : (2 / (t + 2 : ℝ)) * D ≤ 2 * D / t := by
    have hh : 2 / (t + 2 : ℝ) ≤ 2 / t := by
      apply div_le_div_of_nonneg_left (by norm_num) htp
      linarith
    simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right hh hD
  have heq : (a * (t + 3) / 3) * (40 * D / (a * (t : ℝ) ^ 2)) =
      ((40 / 3 : ℝ) * D / t) * ((t + 3) / t) := by field_simp
  have hratio : ((t : ℝ) + 3) / t ≤ 4 := (div_le_iff₀ htp).mpr (by linarith)
  have h₂ := mul_le_mul_of_nonneg_left hratio (show 0 ≤ (40 / 3 : ℝ) * D / t by positivity)
  rw [heq]
  have hnonneg : 0 ≤ D / t := by positivity
  ring_nf at h₁ h₂ hnonneg ⊢
  linarith

end LongTails.Proofs.CachedJacobianTuning
