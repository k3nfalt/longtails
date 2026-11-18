import LongTails.Proofs.GeneralizedSmoothHardChainRadius

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped BigOperators

namespace LongTails.Proofs.KnownGapChainWeights

open GeneralizedSmoothHardTransfer GeneralizedSmoothHardChainRadius

noncomputable def weight (m : ℕ) (L₁ ε h : ℝ) (i : Fin m) : ℝ :=
  2 * ε * L₁ * Real.exp (((m : ℝ) - 1 - i.val) * h)

noncomputable def peak (m : ℕ) (L₁ ε h : ℝ) : ℝ :=
  2 * ε * L₁ * Real.exp (((m : ℝ) - 1) * h)

noncomputable def margin (L₁ h : ℝ) : ℝ := min h 1 / (8 * L₁)

lemma margin_pos (L₁ h : ℝ) (hL₁ : 0 < L₁) (hh : 0 < h) : 0 < margin L₁ h := by
  unfold margin
  have : 0 < min h 1 := lt_min hh one_pos
  positivity

lemma margin_le (L₁ h : ℝ) (hL₁ : 0 < L₁) : margin L₁ h ≤ 1 / (8 * L₁) := by
  unfold margin
  apply div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)

lemma weight_pos (m : ℕ) (L₁ ε h : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε) (i : Fin m) :
    0 < weight m L₁ ε h i := by unfold weight; positivity

lemma peak_pos (m : ℕ) (L₁ ε h : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε) :
    0 < peak m L₁ ε h := by unfold peak; positivity

lemma weight_le_peak {m : ℕ} (L₁ ε h : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε) (hh : 0 ≤ h)
    (i : Fin m) : weight m L₁ ε h i ≤ peak m L₁ ε h := by
  unfold weight peak
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ hh
  linarith [(Nat.cast_nonneg i.val : (0 : ℝ) ≤ i.val)]

lemma weight_lower {m : ℕ} (L₁ ε h : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε) (hh : 0 ≤ h)
    (i : Fin m) : 2 * ε * L₁ ≤ weight m L₁ ε h i := by
  have hi : (i.val : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
  have he : 1 ≤ Real.exp (((m : ℝ) - 1 - i.val) * h) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) hh)
  have hh' := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * ε * L₁ by positivity)
  simpa only [mul_one, weight] using hh'

lemma weight_ratio {m : ℕ} (L₁ ε h : ℝ) (j l : Fin m) :
    weight m L₁ ε h j = weight m L₁ ε h l * Real.exp (((l.val : ℝ) - j.val) * h) := by
  unfold weight
  rw [mul_assoc (2 * ε * L₁), ← Real.exp_add]
  congr 2
  ring

lemma weight_ratio_lower {m : ℕ} (L₁ ε h : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε) (hh : 0 ≤ h)
    (j l : Fin m) (hjl : j < l) :
    weight m L₁ ε h l * (1 + h) ≤ weight m L₁ ε h j := by
  have hjl' : (j.val : ℝ) + 1 ≤ l.val := by exact_mod_cast hjl
  have hr : h ≤ ((l.val : ℝ) - j.val) * h := by nlinarith
  have he := Real.add_one_le_exp (((l.val : ℝ) - j.val) * h)
  rw [weight_ratio L₁ ε h j l]
  apply mul_le_mul_of_nonneg_left _ (weight_pos m L₁ ε h hL₁ hε l).le
  linarith

lemma weight_strict_order {m : ℕ} (L₁ ε h : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε) (hh : 0 < h)
    (j l : Fin m) (hjl : j < l) : weight m L₁ ε h l < weight m L₁ ε h j := by
  have hh' := weight_ratio_lower L₁ ε h hL₁ hε hh.le j l hjl
  have hb := weight_pos m L₁ ε h hL₁ hε l
  nlinarith [mul_pos hb hh]

lemma weight_margin {m : ℕ} (L₁ ε h : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε) (hh : 0 < h)
    (j l : Fin m) (hjl : j < l) :
    margin L₁ h * (weight m L₁ ε h j + weight m L₁ ε h l) <
      2 * (weight m L₁ ε h j - weight m L₁ ε h l) / L₁ := by
  set Gj := weight m L₁ ε h j
  set Gl := weight m L₁ ε h l
  have hGl : 0 < Gl := weight_pos m L₁ ε h hL₁ hε l
  have hr : Gl * (1 + h) ≤ Gj := weight_ratio_lower L₁ ε h hL₁ hε hh.le j l hjl
  have hD : h * Gl ≤ Gj - Gl := by linarith
  have hDpos : 0 < Gj - Gl := lt_of_lt_of_le (mul_pos hh hGl) hD
  have hmin : min h 1 * (h + 2) ≤ 3 * h := by
    rcases le_total h 1 with h1 | h1
    · rw [min_eq_left h1]; nlinarith
    · rw [min_eq_right h1]; linarith
  have hmin0 : 0 ≤ min h 1 := le_min hh.le zero_le_one
  have hsum : Gj + Gl ≤ (Gj - Gl) * (1 + 2 / h) := by
    have hGl' : Gl ≤ (Gj - Gl) / h := by
      rw [le_div_iff₀ hh]; linarith
    have : (Gj - Gl) * (1 + 2 / h) = (Gj - Gl) + 2 * ((Gj - Gl) / h) := by ring
    linarith
  have hL : margin L₁ h * (Gj + Gl) ≤ margin L₁ h * ((Gj - Gl) * (1 + 2 / h)) :=
    mul_le_mul_of_nonneg_left hsum (by unfold margin; positivity)
  have hkey : margin L₁ h * ((Gj - Gl) * (1 + 2 / h)) ≤ 3 * (Gj - Gl) / (8 * L₁) := by
    unfold margin
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
    have : min h 1 * ((Gj - Gl) * (1 + 2 / h)) = (Gj - Gl) * (min h 1 * (h + 2) / h) := by
      field_simp
    rw [this]
    have hq : min h 1 * (h + 2) / h ≤ 3 := by
      rw [div_le_iff₀ hh]; linarith
    nlinarith
  have hfin : 3 * (Gj - Gl) / (8 * L₁) < 2 * (Gj - Gl) / L₁ := by
    rw [show 2 * (Gj - Gl) / L₁ = 16 * (Gj - Gl) / (8 * L₁) by field_simp; ring]
    exact (div_lt_div_iff_of_pos_right (by positivity)).mpr (by linarith)
  linarith

lemma tailSum_bound {m : ℕ} (L₁ ε h : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε) (hh : 0 < h)
    (i : Fin m) : tailSum (weight m L₁ ε h) i ≤ (1 + 1 / h) * weight m L₁ ε h i := by
  apply tailSum_geometric_bound _ (1 / h) (by positivity)
    (fun j => (weight_pos m L₁ ε h hL₁ hε j).le)
  intro j k hjk
  have hh' := weight_ratio_lower L₁ ε h hL₁ hε hh.le j k hjk
  rwa [one_div_one_div]

lemma shiftCoordinate_bounds {m : ℕ} (L₀ L₁ ε h : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (hh : 0 < h) (i : Fin m) :
    0 ≤ shiftCoordinate L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h) i ∧
    shiftCoordinate L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h) i ≤
      2 * (Real.log (1 + L₁ * peak m L₁ ε h / L₀) / L₁) + 2 / L₁ +
        (4 / L₁ * Real.log (1 + Real.sqrt m)) * (1 + 1 / h) := by
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hp := peak_pos m L₁ ε h hL₁ hε
  have hC : 0 ≤ 4 / L₁ * Real.log (1 + Real.sqrt m) := by
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg (by linarith [Real.sqrt_nonneg (m : ℝ)])
  have hlog : 0 ≤ Real.log (1 + L₁ * peak m L₁ ε h / L₀) := by
    apply Real.log_nonneg
    have hh' : 0 ≤ L₁ * peak m L₁ ε h / L₀ := by positivity
    linarith
  have ht := mul_le_mul_of_nonneg_left (tailSum_bound L₁ ε h hL₁ hε hh i)
    (div_nonneg hC (hG i).le)
  have he : (4 / L₁ * Real.log (1 + Real.sqrt m)) / weight m L₁ ε h i *
      ((1 + 1 / h) * weight m L₁ ε h i) =
        (4 / L₁ * Real.log (1 + Real.sqrt m)) * (1 + 1 / h) := by
    field_simp [(hG i).ne']
  rw [he] at ht
  have htail : 0 ≤ tailSum (weight m L₁ ε h) i :=
    (hG i).le.trans (GeneralizedSmoothHardChain.tailSum_lower _ (fun j => (hG j).le) i)
  simp only [shiftCoordinate, one_div_one_div]
  constructor
  · exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) (div_nonneg hlog hL₁.le))
      (by positivity)) (mul_nonneg (div_nonneg hC (hG i).le) htail)
  · linarith

lemma peak_log_bound {m : ℕ} (hm : 0 < m) (L₀ L₁ ε h : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (hh : 0 ≤ h) :
    Real.log (1 + L₁ * peak m L₁ ε h / L₀) ≤
      Real.log (1 + 2 * ε * L₁ ^ 2 / L₀) + ((m : ℝ) - 1) * h := by
  let a := 2 * ε * L₁ ^ 2 / L₀
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnn : 0 ≤ ((m : ℝ) - 1) * h := mul_nonneg (by linarith) hh
  have hone : 1 ≤ Real.exp (((m : ℝ) - 1) * h) := Real.one_le_exp_iff.mpr hnn
  have hp : 1 + L₁ * peak m L₁ ε h / L₀ ≤ (1 + a) * Real.exp (((m : ℝ) - 1) * h) := by
    unfold peak
    have hmul : L₁ * (2 * ε * L₁ * Real.exp (((m : ℝ) - 1) * h)) / L₀ =
        a * Real.exp (((m : ℝ) - 1) * h) := by dsimp [a]; ring
    rw [hmul]
    nlinarith
  have hlog := Real.log_le_log (by have hh' := peak_pos m L₁ ε h hL₁ hε; positivity) hp
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hlog
  exact hlog

lemma shift_norm_bound {m : ℕ} (hm : 0 < m) (L₀ L₁ ε h : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (hh : 0 < h) :
    ‖shift L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h)‖ ≤
      Real.sqrt m * (2 * (Real.log (1 + L₁ * peak m L₁ ε h / L₀) / L₁) + 2 / L₁ +
        (4 / L₁ * Real.log (1 + Real.sqrt m)) * (1 + 1 / h)) := by
  have hc := shiftCoordinate_bounds (m := m) L₀ L₁ ε h hL₀ hL₁ hε hh
  have h0 := hc ⟨0, hm⟩
  apply norm_bound_of_coordinate_bound _ _ (h0.1.trans h0.2)
  intro i
  change |shiftCoordinate L₀ L₁ (peak m L₁ ε h) (weight m L₁ ε h) i| ≤ _
  rw [abs_of_nonneg (hc i).1]
  exact (hc i).2

end LongTails.Proofs.KnownGapChainWeights
