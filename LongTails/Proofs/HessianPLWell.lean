import LongTails.Proofs.RelativeHessianChain
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds

namespace LongTails.Proofs.HessianPLWell

open RelativeHessianArctan RelativeHessianGate

noncomputable def well (t : ℝ) : ℝ := coefficient / 2 * t ^ 2 - profile t

noncomputable def bottom : ℝ := well balance

lemma coefficient_bounds : 1 ≤ coefficient ∧ coefficient ≤ 13 / 10 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  unfold coefficient
  constructor <;> nlinarith

lemma well_hasDerivAt (t : ℝ) : HasDerivAt well (slope coefficient t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have h := (h1.const_mul (coefficient / 2)).sub (profile_derivative t)
  have he : RelativeHessianArctan.slope coefficient t = coefficient / 2 * (2 * t) - density t := by
    unfold RelativeHessianArctan.slope
    ring
  rw [he]
  exact h

lemma slope_hasDerivAt (t : ℝ) :
    HasDerivAt (slope coefficient) (coefficient - densitySlope t) t := by
  have h := ((hasDerivAt_id t).const_mul coefficient).sub (density_derivative t)
  convert h using 1
  · funext y
    simp [RelativeHessianArctan.slope]
  · ring

lemma slope_balance : slope coefficient balance = 0 := by
  obtain ⟨_, _, _, _, hab⟩ := balance_parameters
  rw [slope_factor hab]
  simp

lemma slope_nonneg {t : ℝ} (ht : balance ≤ t) : 0 ≤ slope coefficient t := by
  obtain ⟨ha, hb0, _, _, hab⟩ := balance_parameters
  rw [slope_factor hab]
  have hQ : 0 ≤ t ^ 2 + balance * t + balance ^ 2 + 1 := by
    nlinarith [sq_nonneg (t + balance / 2), sq_nonneg balance]
  have hd : 0 < 1 + t ^ 2 := by positivity
  exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hQ) hd.le

lemma slope_nonpos {t : ℝ} (ht : t ≤ balance) : slope coefficient t ≤ 0 := by
  obtain ⟨ha, hb0, _, _, hab⟩ := balance_parameters
  rw [slope_factor hab]
  have hQ : 0 ≤ t ^ 2 + balance * t + balance ^ 2 + 1 := by
    nlinarith [sq_nonneg (t + balance / 2), sq_nonneg balance]
  have hd : 0 < 1 + t ^ 2 := by positivity
  apply div_nonpos_of_nonpos_of_nonneg _ hd.le
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) hQ

lemma well_continuous : Continuous well :=
  continuous_iff_continuousAt.mpr (fun t => (well_hasDerivAt t).continuousAt)

lemma bottom_le_well (t : ℝ) : bottom ≤ well t := by
  rcases le_total balance t with h | h
  · have hm : MonotoneOn well (Set.Ici balance) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici _) well_continuous.continuousOn
      · exact fun x _ => (well_hasDerivAt x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ici] at hx
        rw [(well_hasDerivAt x).deriv]
        exact slope_nonneg (le_of_lt hx)
    exact hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h
  · have hm : AntitoneOn well (Set.Iic balance) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic _) well_continuous.continuousOn
      · exact fun x _ => (well_hasDerivAt x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Iic] at hx
        rw [(well_hasDerivAt x).deriv]
        exact slope_nonpos (le_of_lt hx)
    exact hm (Set.mem_Iic.mpr h) (Set.mem_Iic.mpr le_rfl) h

noncomputable def excess (t : ℝ) : ℝ := 1 / 2 * slope coefficient t ^ 2 - (well t - bottom)

lemma excess_hasDerivAt (t : ℝ) :
    HasDerivAt excess (slope coefficient t * (coefficient - densitySlope t - 1)) t := by
  have h := (((slope_hasDerivAt t).pow 2).const_mul (1 / 2 : ℝ)).sub
    ((well_hasDerivAt t).sub_const bottom)
  convert h using 1
  · funext y
    simp [excess]
  · simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring

lemma excess_continuous : Continuous excess :=
  continuous_iff_continuousAt.mpr (fun t => (excess_hasDerivAt t).continuousAt)

lemma curvature_margin {t : ℝ} (ht : 0 ≤ t) : 0 ≤ coefficient - densitySlope t - 1 := by
  have ha := coefficient_bounds.1
  have hd : 0 < (1 + t ^ 2) ^ 2 := by positivity
  have hs : densitySlope t ≤ 0 := by
    unfold densitySlope
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hd.le
  linarith

lemma balance_pos : 0 < balance := by
  unfold balance
  have := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)
  positivity

lemma excess_balance : excess balance = 0 := by
  simp [excess, slope_balance, bottom]

lemma excess_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ excess t := by
  rw [← excess_balance]
  rcases le_total balance t with h | h
  · have hm : MonotoneOn excess (Set.Ici balance) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici _) excess_continuous.continuousOn
      · exact fun x _ => (excess_hasDerivAt x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ici] at hx
        rw [(excess_hasDerivAt x).deriv]
        exact mul_nonneg (slope_nonneg (le_of_lt hx))
          (curvature_margin (balance_pos.le.trans (le_of_lt hx)))
    exact hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h
  · have hm : AntitoneOn excess (Set.Icc 0 balance) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) excess_continuous.continuousOn
      · exact fun x _ => (excess_hasDerivAt x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(excess_hasDerivAt x).deriv]
        exact mul_nonpos_of_nonpos_of_nonneg (slope_nonpos (le_of_lt hx.2))
          (curvature_margin (le_of_lt hx.1))
    exact hm (Set.mem_Icc.mpr ⟨ht, h⟩) (Set.mem_Icc.mpr ⟨balance_pos.le, le_rfl⟩) h

lemma well_gap_le {t : ℝ} (ht : 0 ≤ t) : well t - bottom ≤ 1 / 2 * slope coefficient t ^ 2 := by
  have h := excess_nonneg ht
  unfold excess at h
  linarith

lemma bottom_bounds : -4 ≤ bottom ∧ bottom ≤ -1 := by
  obtain ⟨_, _, _, hb, _⟩ := balance_parameters
  have ha := coefficient_bounds
  have hp := profile_bounds balance
  have h0 : Real.arctan 0 < Real.arctan balance := Real.arctan_strictMono balance_pos
  rw [Real.arctan_zero] at h0
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  unfold bottom well
  rw [hb]
  constructor
  · nlinarith
  · unfold profile
    nlinarith

lemma link_bracket (s t : ℝ) :
    bottom ≤ coefficient / 2 * t ^ 2 + RelativeHessianChain.link s t := by
  have h := bottom_le_well t
  have h1 := mul_nonneg (gate_bounds (-s)).1 (profile_bounds (-t)).1.le
  have h2 := mul_le_mul_of_nonneg_right (gate_bounds s).2 (profile_bounds t).1.le
  unfold well at h
  unfold RelativeHessianChain.link
  linarith

lemma link_flat {s : ℝ} (hs : |s| ≤ 1 / 10) (t : ℝ) : RelativeHessianChain.link s t = 0 := by
  have h := abs_le.mp hs
  have h1 := (gate_flat (show s ≤ 1 / 10 by linarith)).1
  have h2 := (gate_flat (show -s ≤ 1 / 10 by linarith)).1
  simp [RelativeHessianChain.link, h1, h2]

lemma link_saturated {s : ℝ} (hs : 1 / 5 ≤ s) (t : ℝ) :
    RelativeHessianChain.link s t = -profile t := by
  have h1 := (gate_saturated hs).1
  have h2 := (gate_flat (show -s ≤ 1 / 10 by linarith)).1
  simp [RelativeHessianChain.link, h1, h2]

lemma link_le (s t : ℝ) : RelativeHessianChain.link s t ≤ 4 :=
  (RelativeHessianChain.link_bounds s t).2.trans Real.pi_lt_four.le

lemma gate_pair_le_one (t : ℝ) : gate t + gate (-t) ≤ 1 := by
  by_cases h : t ≤ 1 / 10
  · rw [(gate_flat h).1]
    linarith [(gate_bounds (-t)).2]
  · rw [(gate_flat (show -t ≤ 1 / 10 by linarith)).1]
    linarith [(gate_bounds t).2]

lemma outgoing_plateau {s : ℝ} (hs : 1 / 5 ≤ |s|) (t : ℝ) :
    RelativeHessianChain.outgoing s t = 0 := by
  rcases le_or_gt 0 s with h | h
  · rw [abs_of_nonneg h] at hs
    have h1 := (gate_saturated hs).2.1
    have h2 := (gate_flat (show -s ≤ 1 / 10 by linarith)).2.1
    simp [RelativeHessianChain.outgoing, h1, h2]
  · rw [abs_of_neg h] at hs
    have h1 := (gate_saturated hs).2.1
    have h2 := (gate_flat (show s ≤ 1 / 10 by linarith)).2.1
    simp [RelativeHessianChain.outgoing, h1, h2]

lemma half_le_sq_mul {r : ℝ} (hr : 0 ≤ r) : coefficient / 2 * r ≤ coefficient ^ 2 * r := by
  have ha := coefficient_bounds
  have h : coefficient / 2 ≤ coefficient ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right h hr

lemma anchor_bracket_le (t : ℝ) : well t - bottom ≤ t ^ 2 + 8 := by
  have ha := coefficient_bounds
  have hb := bottom_bounds
  have hp := (profile_bounds t).1
  have h := mul_nonneg (show (0 : ℝ) ≤ 1 - coefficient / 2 by linarith) (sq_nonneg t)
  unfold well
  linarith

lemma link_bracket_le (s t : ℝ) :
    coefficient / 2 * t ^ 2 + RelativeHessianChain.link s t - bottom ≤ t ^ 2 + 8 := by
  have ha := coefficient_bounds
  have hb := bottom_bounds
  have hl := link_le s t
  have h := mul_nonneg (show (0 : ℝ) ≤ 1 - coefficient / 2 by linarith) (sq_nonneg t)
  linarith

lemma coordinate_sq_le {y c g : ℝ} (hg : g = coefficient * y + c) (hc0 : c ≤ 0)
    (hc2 : -2 ≤ c) : y ^ 2 ≤ 2 * g ^ 2 + 8 := by
  have ha := coefficient_bounds
  have hcsq : c ^ 2 ≤ 4 := by nlinarith
  have hay : (coefficient * y) ^ 2 ≤ 2 * g ^ 2 + 2 * c ^ 2 := by
    rw [hg]
    nlinarith [sq_nonneg (coefficient * y + 2 * c)]
  have hyy : y ^ 2 ≤ (coefficient * y) ^ 2 := by
    rw [mul_pow]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ coefficient ^ 2 - 1 by nlinarith) (sq_nonneg y)]
  linarith

lemma small_sq_le {y : ℝ} (h : |y| < 1 / 5) (g : ℝ) : y ^ 2 ≤ 2 * g ^ 2 + 8 := by
  have hab := abs_nonneg y
  have h2 : y ^ 2 ≤ 1 / 25 := by
    rw [← sq_abs]
    nlinarith
  nlinarith [sq_nonneg g]

lemma negative_coordinate {y c : ℝ} (hy : y < -(1 / 5)) (hc : c ≤ 0) :
    coefficient * y + c ≤ -(1 / 5) := by
  have ha := coefficient_bounds
  have h := mul_nonneg (sub_nonneg.mpr ha.1) (show (0 : ℝ) ≤ -y by linarith)
  linarith

lemma sq_lower {c r : ℝ} (hc : 0 ≤ c) (h : c ≤ r) : c ^ 2 ≤ r ^ 2 :=
  pow_le_pow_left₀ hc h 2

end LongTails.Proofs.HessianPLWell
