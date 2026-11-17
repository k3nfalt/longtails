import LongTails.Proofs.RelativeHessianGate

namespace LongTails.Proofs.RelativeHessianCutoff

open RelativeHessianGate

noncomputable def profile (t : ℝ) : ℝ := 1 - gate ((t + 2) / 30)
noncomputable def first (t : ℝ) : ℝ := -gateSlope ((t + 2) / 30) / 30
noncomputable def second (t : ℝ) : ℝ := -gateCurvature ((t + 2) / 30) / 900
noncomputable def third (t : ℝ) : ℝ := -gateThird ((t + 2) / 30) / 27000

lemma smooth : ContDiff ℝ 3 profile := by
  apply contDiff_const.sub
  apply gate_contDiff.comp
  fun_prop

lemma profile_derivative (t : ℝ) : HasDerivAt profile (first t) t := by
  have h := ((gate_hasDerivAt ((t + 2) / 30)).comp t
    (((hasDerivAt_id t).add_const 2).div_const 30)).const_sub 1
  convert h using 1
  · funext y; rfl
  · simp only [first]
    ring

lemma first_derivative (t : ℝ) : HasDerivAt first (second t) t := by
  have h := (((gateSlope_hasDerivAt ((t + 2) / 30)).comp t
    (((hasDerivAt_id t).add_const 2).div_const 30)).neg).div_const 30
  convert h using 1
  · funext y; rfl
  · simp only [second]
    ring

lemma second_derivative (t : ℝ) : HasDerivAt second (third t) t := by
  have h := (((gateCurvature_hasDerivAt ((t + 2) / 30)).comp t
    (((hasDerivAt_id t).add_const 2).div_const 30)).neg).div_const 900
  convert h using 1
  · funext y; rfl
  · simp only [third]
    ring

lemma bounds (t : ℝ) : 0 ≤ profile t ∧ profile t ≤ 1 := by
  have h := gate_bounds ((t + 2) / 30)
  unfold profile
  constructor <;> linarith

lemma flat {t : ℝ} (ht : t ≤ 1) :
    profile t = 1 ∧ first t = 0 ∧ second t = 0 ∧ third t = 0 := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := gate_flat (show (t + 2) / 30 ≤ 1 / 10 by linarith)
  simp [profile, first, second, third, h₀, h₁, h₂, h₃]

lemma outside {t : ℝ} (ht : 4 ≤ t) :
    profile t = 0 ∧ first t = 0 ∧ second t = 0 ∧ third t = 0 := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := gate_saturated (show 1 / 5 ≤ (t + 2) / 30 by linarith)
  simp [profile, first, second, third, h₀, h₁, h₂, h₃]

lemma jet_bounds (t : ℝ) : |first t| ≤ 2 ^ 24 ∧ |second t| ≤ 2 ^ 24 ∧ |third t| ≤ 2 ^ 24 := by
  obtain ⟨h₁, h₂, h₃⟩ := gate_jet_bounds ((t + 2) / 30)
  unfold first second third
  rw [abs_div, abs_div, abs_div]
  norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 30),
    abs_of_pos (by norm_num : (0 : ℝ) < 900), abs_of_pos (by norm_num : (0 : ℝ) < 27000)]
  constructor
  · linarith
  constructor <;> linarith

end LongTails.Proofs.RelativeHessianCutoff
