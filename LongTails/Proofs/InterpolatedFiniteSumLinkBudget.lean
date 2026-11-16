import LongTails.Proofs.InterpolatedFiniteSumLinkParameters

namespace LongTails.Proofs.InterpolatedFiniteSumLinkBudget

lemma cost_bound (g T : ℕ) (hg : 0 < g) (hT : 0 < T) (δ η ε L R : ℝ)
    (hδ : 0 < δ) (hη : 0 < η) (hε : 0 < ε) (hL : 0 < L) (hR : 0 < R)
    (hexp : δ * Real.exp η = δ + 2 * g * ε)
    (hderiv : 128 * η * Real.sqrt T ≤ L * R) :
    (δ / (g : ℝ)) * (256 * ((2 * η * Real.exp η / (R / Real.sqrt T)) / L) *
      (1 + max 0 (Real.log (256 * ((2 * η * Real.exp η / (R / Real.sqrt T)) / L))))) ≤
      4096 * ε * (1 + η) ^ 2 * Real.sqrt T / (L * R) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  let z := 256 * ((2 * η * Real.exp η / (R / Real.sqrt T)) / L)
  have hz : 0 < z := by dsimp [z]; positivity
  have he : z = 512 * η * Real.exp η * Real.sqrt T / (L * R) := by
    dsimp [z]; field_simp; ring
  have hzupper : z ≤ 4 * Real.exp η := by
    rw [he]
    apply (div_le_iff₀ (mul_pos hL hR)).mpr
    have hh := mul_le_mul_of_nonneg_right hderiv (Real.exp_pos η).le
    nlinarith only [hh]
  have hlog : Real.log z ≤ η + 3 := by
    calc
      _ ≤ Real.log (4 * Real.exp η) := Real.log_le_log hz hzupper
      _ = Real.log 4 + η := by rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos η)), Real.log_exp]
      _ ≤ _ := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
  have hJ : 1 + max 0 (Real.log z) ≤ 4 * (1 + η) := by
    have hh : max 0 (Real.log z) ≤ η + 3 := max_le (by linarith) hlog
    linarith
  have hscalar : δ * η * Real.exp η ≤ 2 * g * ε * (1 + η) := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp η) hδ.le
    have heη := congrArg (fun x : ℝ => x * η) hexp
    nlinarith only [hh, hexp, heη]
  have hcoeff : δ / (g : ℝ) * z ≤ 1024 * ε * (1 + η) * Real.sqrt T / (L * R) := by
    rw [he]
    have hid : δ / (g : ℝ) * (512 * η * Real.exp η * Real.sqrt T / (L * R)) =
        512 * (δ * η * Real.exp η) * Real.sqrt T / (g * (L * R)) := by field_simp
    rw [hid]
    apply (div_le_iff₀ (by positivity : 0 < (g : ℝ) * (L * R))).mpr
    have hh := mul_le_mul_of_nonneg_right hscalar (show 0 ≤ 512 * Real.sqrt T by positivity)
    have hid' : (1024 * ε * (1 + η) * Real.sqrt T / (L * R)) * (g * (L * R)) =
        1024 * ε * (1 + η) * Real.sqrt T * g := by field_simp
    rw [hid']
    nlinarith only [hh]
  change δ / (g : ℝ) * (z * (1 + max 0 (Real.log z))) ≤ _
  have hh := mul_le_mul hcoeff hJ (by positivity : 0 ≤ 1 + max 0 (Real.log z))
    (by positivity : 0 ≤ 1024 * ε * (1 + η) * Real.sqrt T / (L * R))
  convert hh using 1 <;> ring

lemma small_budget (g T b : ℕ) (hg : 0 < g) (hT : 0 < T) (δ η ε L R t : ℝ)
    (hδ : 0 < δ) (hη : 0 < η) (hε : 0 < ε) (hL : 0 < L) (hR : 0 < R)
    (ht : 0 < t) (hexp : δ * Real.exp η = δ + 2 * g * ε)
    (hderiv : 128 * η * Real.sqrt T ≤ L * R)
    (hs : Real.sqrt T ≤ 2 * Real.sqrt t) (hid : L * R = 64 * t * Real.sqrt t)
    (hb : (b : ℝ) ≤ g * t / (4096 * (1 + η) ^ 2)) :
    (δ / (g : ℝ)) * (256 * ((2 * η * Real.exp η / (R / Real.sqrt T)) / L) *
      (1 + max 0 (Real.log (256 * ((2 * η * Real.exp η / (R / Real.sqrt T)) / L))))) *
      (4 * b / g) ≤ 7 * ε / 16 := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hη1 : 0 < 1 + η := by linarith
  have hcoef := cost_bound g T hg hT δ η ε L R hδ hη hε hL hR hexp hderiv
  have hh := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ 4 * (b : ℝ) / g by positivity)
  have hb' := (le_div_iff₀ (show 0 < 4096 * (1 + η) ^ 2 by positivity)).mp hb
  have hbmul := mul_le_mul_of_nonneg_right hb' (show 0 ≤ 4 * ε * Real.sqrt T by positivity)
  have hsmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * ε * g * t by positivity)
  have htarget : (4096 * ε * (1 + η) ^ 2 * Real.sqrt T / (L * R)) * (4 * b / g) ≤ ε / 8 := by
    apply (mul_le_mul_iff_right₀ (show 0 < (g : ℝ) * (L * R) by positivity)).mp
    have he : ((4096 * ε * (1 + η) ^ 2 * Real.sqrt T / (L * R)) * (4 * b / g)) *
        ((g : ℝ) * (L * R)) = 4096 * (1 + η) ^ 2 * b * (4 * ε * Real.sqrt T) := by field_simp
    rw [mul_comm ((g : ℝ) * (L * R)) _, he, hid]
    nlinarith only [hbmul, hsmul]
  linarith only [hh, htarget, hε]

end LongTails.Proofs.InterpolatedFiniteSumLinkBudget
