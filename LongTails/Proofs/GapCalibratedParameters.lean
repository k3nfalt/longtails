import LongTails.Proofs.GapCalibratedConjugate

open scoped BigOperators

namespace LongTails.Proofs.GapCalibratedParameters

open GeneralizedSmoothHardTransfer GapCalibratedWeights

lemma old_shift_bound {m : ℕ} (L₀ L₁ g t w : ℝ)
    (hL₁ : 0 < L₁) (hg : 0 < g) (ht : 0 < t) (ht1 : t ≤ 1) (hw : 1 ≤ w)
    (hmt : (m : ℝ) * t ^ 2 ≤ 1)
    (hlog : Real.log (1 + L₁ * peak m g t / L₀) ≤ 2 * w + (m : ℝ) * t)
    (hs : Real.log (1 + Real.sqrt m) ≤ w) (i : Fin m) :
    shiftCoordinate L₀ L₁ (peak m g t) (weight m g t) i ≤ 16 * w / (L₁ * t) := by
  have hwi := weight_pos m g t hg i
  have htail := tail_bound m g t hg.le ht i
  have hc : 0 ≤ 4 / L₁ * Real.log (1 + Real.sqrt m) := by
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg (by linarith [Real.sqrt_nonneg (m : ℝ)])
  have hp := mul_le_mul_of_nonneg_left htail (div_nonneg hc hwi.le)
  have he : (4 / L₁ * Real.log (1 + Real.sqrt m)) / weight m g t i *
      ((1 + 1 / t) * weight m g t i) =
      (4 / L₁ * Real.log (1 + Real.sqrt m)) * (1 + 1 / t) := by
    field_simp [hwi.ne']
  rw [he] at hp
  have hlog' := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 / L₁ by positivity)
  have hs' := mul_le_mul_of_nonneg_right hs (show 0 ≤ 4 / L₁ * (1 + 1 / t) by positivity)
  have hbound : shiftCoordinate L₀ L₁ (peak m g t) (weight m g t) i ≤
      2 * ((2 * w + (m : ℝ) * t) / L₁) + 2 / L₁ +
        (4 / L₁ * w) * (1 + 1 / t) := by
    unfold shiftCoordinate
    simp only [one_div_one_div]
    simp only [div_eq_mul_inv] at hp hlog' hs' ⊢
    nlinarith only [hp, hlog', hs']
  apply hbound.trans
  apply (le_div_iff₀ (mul_pos hL₁ ht)).mpr
  have he' : (2 * ((2 * w + (m : ℝ) * t) / L₁) + 2 / L₁ +
      (4 / L₁ * w) * (1 + 1 / t)) * (L₁ * t) =
      8 * w * t + 2 * (m : ℝ) * t ^ 2 + 2 * t + 4 * w := by
    field_simp
    ring
  rw [he']
  have hwt := mul_le_mul_of_nonneg_left ht1 (show 0 ≤ w by linarith)
  nlinarith only [hwt, hmt, ht1, hw]

lemma total_shift_bound {m : ℕ} (L₀ L₁ g t w : ℝ)
    (hL₁ : 0 < L₁) (hg : 0 < g) (ht : 0 < t) (ht1 : t ≤ 1) (hw : 1 ≤ w)
    (hmt : (m : ℝ) * t ^ 2 ≤ 1)
    (hlog : Real.log (1 + L₁ * peak m g t / L₀) ≤ 2 * w + (m : ℝ) * t)
    (hs : Real.log (1 + Real.sqrt m) ≤ w) (i : Fin m) :
    100 * w / (L₁ * t) + shiftCoordinate L₀ L₁ (peak m g t) (weight m g t) i ≤
      116 * w / (L₁ * t) := by
  have hh := old_shift_bound L₀ L₁ g t w hL₁ hg ht ht1 hw hmt hlog hs i
  calc
    _ ≤ 100 * w / (L₁ * t) + 16 * w / (L₁ * t) := add_le_add le_rfl hh
    _ = _ := by ring

lemma origin_score_bound {m : ℕ} (L₀ L₁ ε t w : ℝ)
    (hL₁ : 0 < L₁) (hε : 0 < ε) (ht : 0 < t) (ht1 : t ≤ 1) (hw : 1 ≤ w)
    (hmt : (m : ℝ) * t ^ 2 ≤ 1)
    (hlog : Real.log (1 + L₁ * peak m (ε * L₁ * t / (25 * w)) t / L₀) ≤
      2 * w + (m : ℝ) * t)
    (hs : Real.log (1 + Real.sqrt m) ≤ w) (i : Fin m) :
    weight m (ε * L₁ * t / (25 * w)) t i *
      (100 * w / (L₁ * t) +
        shiftCoordinate L₀ L₁ (peak m (ε * L₁ * t / (25 * w)) t)
          (weight m (ε * L₁ * t / (25 * w)) t) i) ≤
      5 * ε * Real.exp ((m : ℝ) * t) := by
  let g := ε * L₁ * t / (25 * w)
  have hw0 : 0 < w := by linarith
  have hg : 0 < g := by dsimp [g]; positivity
  have hh := total_shift_bound L₀ L₁ g t w hL₁ hg ht ht1 hw hmt hlog hs i
  have h1 := mul_le_mul_of_nonneg_left hh (weight_pos m g t hg i).le
  have h2 := mul_le_mul_of_nonneg_right (weight_le_peak m g t hg.le ht.le i)
    (show 0 ≤ 116 * w / (L₁ * t) by positivity)
  have h3 := mul_le_mul_of_nonneg_right (peak_bound m g t hg.le ht.le)
    (show 0 ≤ 116 * w / (L₁ * t) by positivity)
  have he : (g * Real.exp ((m : ℝ) * t)) * (116 * w / (L₁ * t)) =
      (116 / 25 : ℝ) * ε * Real.exp ((m : ℝ) * t) := by
    dsimp [g]
    field_simp
  rw [he] at h3
  have hp : 0 ≤ ε * Real.exp ((m : ℝ) * t) := by positivity
  change weight m g t i * _ ≤ _
  nlinarith only [h1, h2, h3, hp]

lemma smoothed_origin_score {m : ℕ} (L₀ L₁ ε t w ρ : ℝ)
    (hL₁ : 0 < L₁) (hε : 0 < ε) (ht : 0 < t) (ht1 : t ≤ 1) (hw : 1 ≤ w)
    (hρ : ρ ≤ w / (L₁ * t)) (hmt : (m : ℝ) * t ^ 2 ≤ 1)
    (hlog : Real.log (1 + L₁ * peak m (ε * L₁ * t / (25 * w)) t / L₀) ≤
      2 * w + (m : ℝ) * t)
    (hs : Real.log (1 + Real.sqrt m) ≤ w) (i : Fin m) :
    weight m (ε * L₁ * t / (25 * w)) t i *
      (100 * w / (L₁ * t) +
        shiftCoordinate L₀ L₁ (peak m (ε * L₁ * t / (25 * w)) t)
          (weight m (ε * L₁ * t / (25 * w)) t) i + ρ) ≤
      8 * ε * Real.exp ((m : ℝ) * t) := by
  let g := ε * L₁ * t / (25 * w)
  have hw0 : 0 < w := by linarith
  have hg : 0 < g := by dsimp [g]; positivity
  have ho := origin_score_bound L₀ L₁ ε t w hL₁ hε ht ht1 hw hmt hlog hs i
  have hwi := (weight_le_peak m g t hg.le ht.le i).trans (peak_bound m g t hg.le ht.le)
  have hp := mul_le_mul_of_nonneg_left hρ (weight_pos m g t hg i).le
  have hp' := mul_le_mul_of_nonneg_right hwi (show 0 ≤ w / (L₁ * t) by positivity)
  have he : (g * Real.exp ((m : ℝ) * t)) * (w / (L₁ * t)) =
      ε * Real.exp ((m : ℝ) * t) / 25 := by
    dsimp [g]
    field_simp
  rw [he] at hp'
  change weight m g t i * _ ≤ _ at ho ⊢
  have hn : 0 ≤ ε * Real.exp ((m : ℝ) * t) := by positivity
  nlinarith only [ho, hp, hp', hn]

lemma hidden_score {m : ℕ} (L₁ ε t w τ ρ : ℝ)
    (hL₁ : 0 < L₁) (hε : 0 < ε) (ht : 0 < t) (hw : 0 < w)
    (hnoise : τ + ρ ≤ 2 / L₁) (i : Fin m) :
    4 * ε ≤ weight m (ε * L₁ * t / (25 * w)) t i *
      (100 * w / (L₁ * t) + 2 / L₁ - τ - ρ) := by
  let g := ε * L₁ * t / (25 * w)
  have hg : 0 < g := by dsimp [g]; positivity
  have hi := weight_lower m g t hg.le ht.le i
  have hwi := weight_pos m g t hg i
  have hm := mul_le_mul_of_nonneg_right hi (show 0 ≤ 100 * w / (L₁ * t) by positivity)
  have he : g * (100 * w / (L₁ * t)) = 4 * ε := by dsimp [g]; field_simp; ring
  rw [he] at hm
  change 4 * ε ≤ weight m g t i * _
  nlinarith [mul_nonneg hwi.le (show 0 ≤ 2 / L₁ - τ - ρ by linarith)]

lemma log_peak_bound (m : ℕ) (L₀ L₁ g t q w : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hg : 0 < g) (ht : 0 ≤ t) (hq : 0 ≤ q)
    (hratio : L₁ * g / L₀ ≤ q ^ 2) (hw : Real.log (1 + q) ≤ w) :
    Real.log (1 + L₁ * peak m g t / L₀) ≤ 2 * w + (m : ℝ) * t := by
  have he := Real.one_le_exp_iff.mpr (mul_nonneg (Nat.cast_nonneg m) ht)
  have hp := mul_le_mul_of_nonneg_left (peak_bound m g t hg.le ht)
    (div_nonneg hL₁.le hL₀.le)
  have hr := mul_le_mul_of_nonneg_right hratio (Real.exp_pos ((m : ℝ) * t)).le
  have hb : 1 + L₁ * peak m g t / L₀ ≤ (1 + q) ^ 2 * Real.exp ((m : ℝ) * t) := by
    have hq' := mul_nonneg hq (Real.exp_pos ((m : ℝ) * t)).le
    simp only [div_eq_mul_inv] at hp hr ⊢
    nlinarith only [he, hp, hr, hq']
  have hl : 0 < 1 + L₁ * peak m g t / L₀ := by
    have hpeak := peak_pos m g t hg
    positivity
  have hh := Real.log_le_log hl hb
  rw [Real.log_mul (by positivity : (1 + q) ^ 2 ≠ 0) (Real.exp_ne_zero _),
    Real.log_pow, Real.log_exp] at hh
  norm_num at hh
  linarith

lemma shift_nonnegative {m : ℕ} (L₀ L₁ B : ℝ) (hL₀ : 0 < L₀)
    (hL₁ : 0 < L₁) (hB : 0 ≤ B) (G : Fin m → ℝ) (hG : ∀ i, 0 < G i) (i : Fin m) :
    0 ≤ shiftCoordinate L₀ L₁ B G i := by
  have hl : 0 ≤ Real.log (1 + L₁ * B / L₀) :=
    Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have hs : 0 ≤ Real.log (1 + Real.sqrt m) :=
    Real.log_nonneg (by linarith [Real.sqrt_nonneg (m : ℝ)])
  have ht : 0 ≤ tailSum G i := by
    unfold tailSum
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact (hG j).le
    · exact le_rfl
  have hGi := hG i
  unfold shiftCoordinate
  simp only [one_div_one_div]
  positivity


noncomputable def spacing (m : ℕ) (h : ℝ) : ℝ :=
  min (1 / Real.sqrt m) (h / (2 * (m : ℝ)))

lemma spacing_pos {m : ℕ} (hm : 0 < m) (h : ℝ) (hh : 0 < h) :
    0 < spacing m h := by unfold spacing; positivity

lemma spacing_bounds {m : ℕ} (hm : 0 < m) (h : ℝ) (hh : 0 < h) :
    spacing m h ≤ 1 ∧ (m : ℝ) * spacing m h ^ 2 ≤ 1 ∧
      (m : ℝ) * spacing m h ≤ h / 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hs1 : 1 ≤ Real.sqrt m := (Real.one_le_sqrt).mpr hm1
  have ht0 := spacing_pos hm h hh
  have ht := min_le_left (1 / Real.sqrt m) (h / (2 * (m : ℝ)))
  change spacing m h ≤ 1 / Real.sqrt m at ht
  have htm := (le_div_iff₀ hs0).mp ht
  have hsq := Real.sq_sqrt hm0.le
  have ht' := min_le_right (1 / Real.sqrt m) (h / (2 * (m : ℝ)))
  change spacing m h ≤ h / (2 * (m : ℝ)) at ht'
  have htm' := (le_div_iff₀ (by positivity : 0 < 2 * (m : ℝ))).mp ht'
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · have hpow := sq_le_sq₀ (by positivity : 0 ≤ spacing m h * Real.sqrt m)
      (by norm_num : (0 : ℝ) ≤ 1) |>.mpr htm
    nlinarith only [hpow, hsq]
  · linarith

lemma calibrated_radius {m : ℕ} (hm : 0 < m) (L₁ R h w : ℝ)
    (hL₁ : 0 < L₁) (hR : 0 < R) (hh : 0 < h)
    (hlinear : 4096 * (m : ℝ) * w ≤ L₁ * R)
    (hgap : 8192 * (m : ℝ) * Real.sqrt m * w ≤ L₁ * R * h) :
    Real.sqrt m * (128 * w / (L₁ * spacing m h)) ≤ R / 32 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hsq := Real.sq_sqrt hm0.le
  have ht0 := spacing_pos hm h hh
  have ht : 4096 * Real.sqrt m * w / (L₁ * R) ≤ spacing m h := by
    apply le_min
    · apply (le_div_iff₀ hs0).mpr
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (mul_pos hL₁ hR)).mpr
      nlinarith only [hlinear, congrArg (fun u => 4096 * u * w) hsq]
    · apply (le_div_iff₀ (by positivity : 0 < 2 * (m : ℝ))).mpr
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (mul_pos hL₁ hR)).mpr
      nlinarith only [hgap]
  have ht' := (div_le_iff₀ (mul_pos hL₁ hR)).mp ht
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr
  have he : Real.sqrt m * (128 * w / (L₁ * spacing m h)) * 32 =
      4096 * Real.sqrt m * w / (L₁ * spacing m h) := by ring
  rw [he]
  apply (div_le_iff₀ (mul_pos hL₁ ht0)).mpr
  nlinarith only [ht']

end LongTails.Proofs.GapCalibratedParameters
