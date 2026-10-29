import LongTails.Proofs.CohypomonotoneNewtonSearch

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CohypomonotoneNewtonOuter

open LongTails.Setups.CohypomonotoneNewton
open LongTails.Algorithms.CohypomonotoneNewton
open LongTails.Proofs.CohypomonotoneNewtonGeometry
open LongTails.Proofs.CohypomonotoneNewtonEnergy
open LongTails.Proofs.CohypomonotoneNewtonSearch
open OracleTemplate.ComponentEnvelope (Program)

universe u

lemma weighted_anchorMix (p : Public.{u}) (st : OuterState p.E) {a : ℝ}
    (hden : st.mass + a ≠ 0) :
    (st.mass + a) • anchorMix p st a = a • p.x0 + st.mass • currentPoint p st := by
  unfold anchorMix
  rw [smul_add, smul_smul, smul_smul]
  congr 1 <;> congr 1 <;> field_simp

lemma step_energy (p : Public.{u}) (st : OuterState p.E) {a : ℝ} (hA : 0 ≤ st.mass)
    (ha : 0 < a) (z h : p.E)
    (hmono : 0 ≤ st.mass * ⟪h - currentValue p st, z - currentPoint p st⟫)
    (herr : ‖z + a • h - anchorMix p st a‖ ≤ ‖z - midpoint p st a‖ / 4 + errorScale p st a) :
    (st.mass + a) * ⟪h, z - p.x0⟫ + (st.mass + a) ^ 2 / 2 * ‖h‖ ^ 2 +
      7 / 16 * ((st.mass + a) / a) ^ 2 * ‖z - midpoint p st a‖ ^ 2 ≤
      st.mass * ⟪currentValue p st, currentPoint p st - p.x0⟫ +
        st.mass ^ 2 / 2 * ‖currentValue p st‖ ^ 2 + p.R ^ 2 / ((st.k : ℝ) + 1) ^ 2 := by
  have hB : 0 < st.mass + a := by positivity
  have hc := weighted_anchorMix p st hB.ne'
  have hd : (st.mass + a) • (z - midpoint p st a) =
      (st.mass + a) • (z - p.x0) - st.mass • (currentPoint p st - p.x0) +
        (a * st.mass) • currentValue p st := by
    unfold LongTails.Algorithms.CohypomonotoneNewton.midpoint
    rw [smul_sub, smul_sub, hc, smul_smul]
    have he : (st.mass + a) * (a * st.mass / (st.mass + a)) = a * st.mass := by field_simp
    rw [he]
    module
  have hr : (st.mass + a) • (z + a • h - anchorMix p st a) =
      (st.mass + a) • (z - p.x0) - st.mass • (currentPoint p st - p.x0) +
        (a * (st.mass + a)) • h := by
    rw [smul_sub, smul_add, hc, smul_smul]
    module
  have hmono' : 0 ≤ st.mass * ⟪h - currentValue p st, (z - p.x0) - (currentPoint p st - p.x0)⟫ := by
    have he : (z - p.x0) - (currentPoint p st - p.x0) = z - currentPoint p st := by abel
    rwa [he]
  have hh := perturbed_energy_step hA ha.le hmono' hd hr herr
  exact normalized_energy_step ha st.k hh hB.ne'

lemma weighted_monotonicity (p : Public.{u}) (st : OuterState p.E) (G : p.E → p.E)
    (hA : 0 ≤ st.mass) (hzero : st.k = 0 → st.mass = 0)
    (hvalue : st.k ≠ 0 → currentValue p st = G (currentPoint p st))
    (hmono : ∀ x y, 0 ≤ ⟪G x - G y, x - y⟫) (z : p.E) :
    0 ≤ st.mass * ⟪G z - currentValue p st, z - currentPoint p st⟫ := by
  by_cases hk : st.k = 0
  · rw [hzero hk, zero_mul]
  · rw [hvalue hk]
    exact mul_nonneg hA (hmono z (currentPoint p st))

lemma endpoint_bounds (p : Public.{u}) (st : OuterState p.E) (G : p.E → p.E)
    (D : p.E → p.E →L[ℝ] p.E) (hH : 0 < p.H) (hR : 0 < p.R)
    (hG : ∀ x, HasFDerivAt G (D x) x)
    (hDL : ∀ x y, ‖D x - D y‖ ≤ p.H * ‖x - y‖)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ (p.H * p.R) * ‖x - y‖)
    {a : ℝ} (ha : 0 < a) (n w z : p.E)
    (hmodel : w + a • (G n + D n (w - n)) = anchorMix p st a)
    (hcenter : ‖n - midpoint p st a‖ ≤ centerTolerance p st a)
    (hendpoint : ‖z - w‖ ≤ endpointTolerance p st a)
    (hmerit : a * p.H * ‖w - n‖ ≤ 1 / 32) :
    ‖z + a • G z - anchorMix p st a‖ ≤ ‖z - midpoint p st a‖ / 4 + errorScale p st a ∧
      (1 / 64 ≤ a * p.H * ‖w - n‖ → 1 / 128 ≤ a * p.H * ‖z - midpoint p st a‖) := by
  have hrem := OracleTemplate.RiverValley.taylor_lip hG hH.le hDL n (w - n)
  rw [add_sub_cancel] at hrem
  have hc : ‖n - midpoint p st a‖ ≤ errorScale p st a / 64 := hcenter.trans (min_le_left _ _)
  have he : (1 + a * (p.H * p.R)) * ‖z - w‖ ≤ errorScale p st a / 64 := by
    apply LongTails.Proofs.CohypomonotoneNewtonBudget.scaled_endpoint_tolerance ha.le
      (mul_nonneg hH.le hR.le)
    have hh := hendpoint.trans (min_le_left _ _)
    simpa only [mul_assoc] using hh
  have he0 : 0 ≤ errorScale p st a := by nlinarith [norm_nonneg (n - midpoint p st a)]
  refine ⟨inexact_affine_residual ha.le (mul_nonneg hH.le hR.le) he0
    (anchorMix p st a) (midpoint p st a) n w z hmodel hrem (hlip z w) hmerit hc he, ?_⟩
  intro hlarge
  have hc' := LongTails.Proofs.CohypomonotoneNewtonBudget.scaled_small_tolerance ha hH
    (hcenter.trans (min_le_right _ _))
  have he' := LongTails.Proofs.CohypomonotoneNewtonBudget.scaled_small_tolerance ha hH
    (hendpoint.trans (min_le_right _ _))
  exact inexact_large_step (mul_nonneg ha.le hH.le) (midpoint p st a) n w z hlarge hc' he'

lemma errorScale_le_radius (p : Public.{u}) (st : OuterState p.E)
    (hR : 0 ≤ p.R) (hA : 0 ≤ st.mass) {a : ℝ} (ha : 0 < a) : errorScale p st a ≤ p.R := by
  have hden : 0 < st.mass + a := by positivity
  have halpha : a / (st.mass + a) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right halpha hR
  unfold errorScale
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (st.k : ℝ) + 1)).mpr
  have hk : 0 ≤ (st.k : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hR hk]

lemma step_radius_recurrence (p : Public.{u}) (st : OuterState p.E) (root z h : p.E)
    (hA : 0 ≤ st.mass) {a : ℝ} (ha : 0 < a) (hroot : ‖p.x0 - root‖ ≤ p.R)
    (hmono : 0 ≤ ⟪h, z - root⟫)
    (herr : ‖z + a • h - anchorMix p st a‖ ≤ ‖z - midpoint p st a‖ / 4 + errorScale p st a) :
    (st.mass + a) * ‖z - root‖ ≤ st.mass * ‖currentPoint p st - root‖ +
      2 * a * p.R + (st.mass + a) * ‖z - midpoint p st a‖ / 4 := by
  have hR : 0 ≤ p.R := (norm_nonneg _).trans hroot
  have hB : 0 < st.mass + a := by positivity
  have hc := weighted_anchorMix p st hB.ne'
  have hid : (st.mass + a) • (anchorMix p st a - root) =
      a • (p.x0 - root) + st.mass • (currentPoint p st - root) := by
    rw [smul_sub, hc]
    module
  have hcn := congrArg norm hid
  have hct := norm_add_le (a • (p.x0 - root)) (st.mass • (currentPoint p st - root))
  rw [← hcn] at hct
  simp only [norm_smul, Real.norm_of_nonneg hB.le, Real.norm_of_nonneg ha.le,
    Real.norm_of_nonneg hA] at hct
  have hanchor := mul_le_mul_of_nonneg_left hroot ha.le
  have hz := shifted_norm_lower (ρ := 0) (γ := a) (by simpa using ha.le) ha.le (by simpa using hmono)
  have he : (z - root) + a • h =
      (anchorMix p st a - root) + (z + a • h - anchorMix p st a) := by abel
  rw [he] at hz
  have ht := norm_add_le (anchorMix p st a - root) (z + a • h - anchorMix p st a)
  have hzn : ‖z - root‖ ≤ ‖anchorMix p st a - root‖ + ‖z + a • h - anchorMix p st a‖ := hz.trans ht
  have h1 := mul_le_mul_of_nonneg_left hzn hB.le
  have h2 := mul_le_mul_of_nonneg_left herr hB.le
  have hee : (st.mass + a) * errorScale p st a = a * p.R / ((st.k : ℝ) + 1) := by
    unfold errorScale
    field_simp
  have hee' : (st.mass + a) * errorScale p st a ≤ a * p.R := by
    rw [hee]
    apply div_le_self (mul_nonneg ha.le hR)
    have hk : 0 ≤ (st.k : ℝ) := Nat.cast_nonneg _
    linarith
  nlinarith only [hct, hanchor, h1, h2, hee']

lemma terminal_endpoint_residual (p : Public.{u}) (st : OuterState p.E) (G : p.E → p.E)
    (D : p.E → p.E →L[ℝ] p.E) (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hA : 0 ≤ st.mass) (hg : st.mass * ‖currentValue p st‖ ≤ 4 * p.R)
    (hG : ∀ x, HasFDerivAt G (D x) x)
    (hDL : ∀ x y, ‖D x - D y‖ ≤ p.H * ‖x - y‖)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ (p.H * p.R) * ‖x - y‖)
    (n w z : p.E)
    (hmodel : w + maxStep p • (G n + D n (w - n)) = anchorMix p st (maxStep p))
    (hcenter : ‖n - midpoint p st (maxStep p)‖ ≤ centerTolerance p st (maxStep p))
    (hendpoint : ‖z - w‖ ≤ endpointTolerance p st (maxStep p))
    (hmerit : maxStep p * p.H * ‖w - n‖ ≤ 1 / 32) : ‖G z‖ ≤ p.ε := by
  have ht := tuning_positive p hH hR hε
  have ha : 0 < maxStep p := ht.1.trans_le ht.2
  have hden : 0 < st.mass + maxStep p := by positivity
  have hrem := OracleTemplate.RiverValley.taylor_lip hG hH.le hDL n (w - n)
  rw [add_sub_cancel] at hrem
  have hc := anchor_midpoint_distance p st hA ha
  have halpha : maxStep p / (st.mass + maxStep p) ≤ 1 :=
    (div_le_one hden).mpr (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hg (div_pos ha hden).le
  have h2 := mul_le_mul_of_nonneg_right halpha (by positivity : 0 ≤ 4 * p.R)
  have hc' : ‖anchorMix p st (maxStep p) - midpoint p st (maxStep p)‖ ≤ 4 * p.R := by
    nlinarith only [hc, h1, h2]
  have he := errorScale_le_radius p st hR.le hA ha
  have hcenter' : ‖n - midpoint p st (maxStep p)‖ ≤ p.R / 64 := by
    have hh := hcenter.trans (min_le_left _ _)
    linarith
  have hepoint : (1 + maxStep p * (p.H * p.R)) * ‖z - w‖ ≤ errorScale p st (maxStep p) / 64 := by
    apply LongTails.Proofs.CohypomonotoneNewtonBudget.scaled_endpoint_tolerance ha.le
      (mul_nonneg hH.le hR.le)
    simpa only [mul_assoc] using hendpoint.trans (min_le_left _ _)
  have hdelta : maxStep p * (p.H * p.R) * ‖z - w‖ ≤ p.R / 64 := by
    nlinarith only [hepoint, he, norm_nonneg (z - w)]
  have hestimate := terminal_residual_estimate (D n) ha.le (midpoint p st (maxStep p)) n w z
    (anchorMix p st (maxStep p)) hmodel hrem (hlip z w)
  have hscalar : maxStep p * ‖G z‖ ≤ 4 * p.R + ‖n - midpoint p st (maxStep p)‖ +
      ‖w - n‖ + maxStep p * p.H * ‖w - n‖ ^ 2 + maxStep p * (p.H * p.R) * ‖z - w‖ := by
    linarith
  have hfinal := terminal_scalar_bound ha hH hR.le (norm_nonneg (w - n)) hmerit hcenter' hdelta hscalar
  have haR : 16 * p.R / p.ε ≤ maxStep p := by
    unfold maxStep
    have hb : 0 ≤ baseStep p := ht.1.le
    have hs : 0 ≤ 2 / Real.sqrt (p.H * p.ε) := by positivity
    linarith
  have haH : 2 / Real.sqrt (p.H * p.ε) ≤ maxStep p := by
    unfold maxStep
    have hb : 0 ≤ baseStep p := ht.1.le
    have hs : 0 ≤ 16 * p.R / p.ε := by positivity
    linarith
  exact LongTails.Proofs.CohypomonotoneNewtonBudget.terminal_step_accuracy hH hε ha haR haH hfinal

lemma endpoint_warm_start (p : Public.{u}) (st : OuterState p.E)
    (hH : 0 ≤ p.H) (hR : 0 ≤ p.R) (hA : 0 ≤ st.mass) {a : ℝ} (ha : 0 < a)
    (n w z : p.E) (hcenter : ‖n - midpoint p st a‖ ≤ centerTolerance p st a)
    (hendpoint : ‖z - w‖ ≤ endpointTolerance p st a)
    (hdisp : ((st.mass + a) / a) * ‖z - midpoint p st a‖ ≤ 3 * p.R) :
    ‖w - n‖ ≤ 4 * p.R * (a / (st.mass + a)) := by
  have hB : 0 < st.mass + a := by positivity
  have halpha : 0 ≤ a / (st.mass + a) := (div_pos ha hB).le
  have he : errorScale p st a ≤ p.R * (a / (st.mass + a)) := by
    unfold errorScale
    have hh := div_le_self (mul_nonneg halpha hR)
      (show (1 : ℝ) ≤ (st.k : ℝ) + 1 by have := Nat.cast_nonneg (α := ℝ) st.k; linarith)
    nlinarith only [hh]
  have hc := hcenter.trans (min_le_left _ _)
  have hscaled := LongTails.Proofs.CohypomonotoneNewtonBudget.scaled_endpoint_tolerance
    ha.le (mul_nonneg hH hR)
    (show ‖z - w‖ ≤ errorScale p st a / (64 * (1 + a * (p.H * p.R))) by
      simpa only [mul_assoc] using hendpoint.trans (min_le_left _ _))
  have hd : ‖z - midpoint p st a‖ ≤ 3 * p.R * (a / (st.mass + a)) := by
    have hh := mul_le_mul_of_nonneg_left hdisp halpha
    have hid : a / (st.mass + a) * ((st.mass + a) / a) = 1 := by field_simp
    rw [← mul_assoc, hid, one_mul] at hh
    nlinarith only [hh]
  have ht := norm_add_le (w - z) (z - midpoint p st a)
  have ht' := norm_add_le (w - midpoint p st a) (midpoint p st a - n)
  rw [sub_add_sub_cancel, norm_sub_rev w z] at ht
  rw [sub_add_sub_cancel, norm_sub_rev (midpoint p st a) n] at ht'
  have hn := mul_nonneg (mul_nonneg ha.le (mul_nonneg hH hR)) (norm_nonneg (z - w))
  have hp := mul_nonneg hR halpha
  nlinarith only [hc, he, hscaled, hd, ht, ht', hn, hp]

lemma step_displacement_radius (p : Public.{u}) (st : OuterState p.E)
    (root z g : p.E) (hA : 0 ≤ st.mass) {a : ℝ} (ha : 0 < a)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hmono : 0 ≤ ⟪g, z - root⟫)
    (hradius : ‖currentPoint p st - root‖ ≤ 3 * p.R)
    (hV : st.mass * ⟪currentValue p st, currentPoint p st - p.x0⟫ +
      st.mass ^ 2 / 2 * ‖currentValue p st‖ ^ 2 ≤ 2 * p.R ^ 2)
    (hstep : (st.mass + a) * ⟪g, z - p.x0⟫ + (st.mass + a) ^ 2 / 2 * ‖g‖ ^ 2 +
      7 / 16 * ((st.mass + a) / a) ^ 2 * ‖z - midpoint p st a‖ ^ 2 ≤
      st.mass * ⟪currentValue p st, currentPoint p st - p.x0⟫ +
        st.mass ^ 2 / 2 * ‖currentValue p st‖ ^ 2 + p.R ^ 2 / ((st.k : ℝ) + 1) ^ 2)
    (herr : ‖z + a • g - anchorMix p st a‖ ≤ ‖z - midpoint p st a‖ / 4 + errorScale p st a) :
    ((st.mass + a) / a) * ‖z - midpoint p st a‖ ≤ 3 * p.R ∧ ‖z - root‖ ≤ 3 * p.R := by
  have hR : 0 ≤ p.R := (norm_nonneg _).trans hroot
  have hB : 0 ≤ st.mass + a := by positivity
  have hroot' : ‖root - p.x0‖ ≤ p.R := by rwa [norm_sub_rev]
  have hfloor := potential_floor hB hmono hroot'
  have he : p.R ^ 2 / ((st.k : ℝ) + 1) ^ 2 ≤ p.R ^ 2 := by
    apply div_le_self (sq_nonneg _)
    have hk : 0 ≤ (st.k : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg (st.k : ℝ)]
  have hd := local_displacement_bound (t := ((st.mass + a) / a) * ‖z - midpoint p st a‖)
    hR hV hfloor he (by simpa only [mul_pow, mul_assoc] using hstep)
  refine ⟨hd, ?_⟩
  have hr := step_radius_recurrence p st root z g hA ha hroot hmono herr
  apply local_radius_bound hA ha hR hradius hd
  have hid : a * ((st.mass + a) / a * ‖z - midpoint p st a‖) =
      (st.mass + a) * ‖z - midpoint p st a‖ := by field_simp
  rwa [hid]

noncomputable def potential (p : Public.{u}) (st : OuterState p.E) : ℝ :=
  st.mass * ⟪currentValue p st, currentPoint p st - p.x0⟫ +
    st.mass ^ 2 / 2 * ‖currentValue p st‖ ^ 2

noncomputable def errorBudget (p : Public.{u}) (k : ℕ) : ℝ :=
  p.R ^ 2 * ∑ i ∈ Finset.range k, 1 / ((i : ℝ) + 1) ^ 2

structure StateInvariant (p : Public.{u}) (F : p.E → p.E) (root : p.E)
    (st : OuterState p.E) : Prop where
  mass_nonneg : 0 ≤ st.mass
  mass_case : baseStep p ≤ st.mass ∨ st.k = 0 ∧ st.mass = 0
  zero_mass : st.k = 0 → st.mass = 0
  previous_bounds : baseStep p ≤ st.previous ∧ st.previous ≤ maxStep p
  value_exact : st.value = F st.point
  radius : ‖currentPoint p st - root‖ ≤ 3 * p.R
  energy : potential p st ≤ errorBudget p st.k

lemma errorBudget_bound (p : Public.{u}) (k : ℕ) : errorBudget p k ≤ 2 * p.R ^ 2 := by
  have hh := mul_le_mul_of_nonneg_left (reciprocal_square_sum k) (sq_nonneg p.R)
  simpa only [errorBudget, mul_comm (p.R ^ 2) 2] using hh

lemma errorBudget_succ (p : Public.{u}) (k : ℕ) :
    errorBudget p (k + 1) = errorBudget p k + p.R ^ 2 / ((k : ℝ) + 1) ^ 2 := by
  unfold errorBudget
  rw [Finset.sum_range_succ, mul_add]
  ring

lemma invariant_initial (p : Public.{u}) (F : p.E → p.E) (root x : p.E)
    (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hroot : ‖p.x0 - root‖ ≤ p.R) :
    StateInvariant p F root ⟨0, 0, baseStep p, x, F x⟩ := by
  refine ⟨le_rfl, Or.inr ⟨rfl, rfl⟩, fun _ => rfl,
    ⟨le_rfl, (tuning_positive p hH hR hε).2⟩, rfl, ?_, ?_⟩
  · simpa only [currentPoint, ite_eq_left True.intro] using hroot.trans
      (show p.R ≤ 3 * p.R by linarith)
  · simp [potential, errorBudget]

lemma invariant_value_bounds (p : Public.{u}) (F G : p.E → p.E) (root : p.E)
    (st : OuterState p.E) (hH : 0 ≤ p.H) (hR : 0 ≤ p.R)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hGroot : G root = 0)
    (hmono : ∀ x y, 0 ≤ ⟪G x - G y, x - y⟫)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ p.H * p.R * ‖x - y‖)
    (hgraph : ∀ x, G (x + shift p • F x) = F x)
    (hs : StateInvariant p F root st) :
    st.mass * ‖currentValue p st‖ ≤ 4 * p.R ∧
      ‖currentValue p st‖ ≤ 3 * (p.H * p.R) * p.R := by
  by_cases hk : st.k = 0
  · simp only [currentValue, ite_eq_left hk, norm_zero, mul_zero]
    constructor <;> positivity
  · have hv : currentValue p st = G (currentPoint p st) := by
      simp only [currentValue, currentPoint, ite_eq_right hk, hs.value_exact, hgraph]
    have hm := hmono (currentPoint p st) root
    rw [hGroot, sub_zero, ← hv] at hm
    have hr : ‖root - p.x0‖ ≤ p.R := by rwa [norm_sub_rev]
    refine ⟨potential_residual_bound hs.mass_nonneg hm hr (hs.energy.trans (errorBudget_bound p st.k)), ?_⟩
    have hh := hlip (currentPoint p st) root
    rw [hGroot, sub_zero, ← hv] at hh
    have ht := mul_le_mul_of_nonneg_left hs.radius (mul_nonneg hH hR)
    nlinarith only [hh, ht]

lemma invariant_step (p : Public.{u}) (F G : p.E → p.E) (root : p.E)
    (st : OuterState p.E) (hs : StateInvariant p F root st)
    (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hGroot : G root = 0)
    (hmono : ∀ x y, 0 ≤ ⟪G x - G y, x - y⟫)
    (hgraph : ∀ x, G (x + shift p • F x) = F x)
    {a : ℝ} (ha : baseStep p ≤ a) (haMax : a ≤ maxStep p) (x : p.E)
    (herr : ‖(x + shift p • F x) + a • F x - anchorMix p st a‖ ≤
      ‖(x + shift p • F x) - midpoint p st a‖ / 4 + errorScale p st a) :
    StateInvariant p F root ⟨st.k + 1, st.mass + a, a, x, F x⟩ ∧
      ((st.mass + a) / a) * ‖(x + shift p • F x) - midpoint p st a‖ ≤ 3 * p.R := by
  have ha0 := (tuning_positive p hH hR hε).1.trans_le ha
  let z := x + shift p • F x
  have hv : ∀ _ : st.k ≠ 0, currentValue p st = G (currentPoint p st) := by
    intro hk
    simp only [currentValue, currentPoint, ite_eq_right hk, hs.value_exact, hgraph]
  have hm := weighted_monotonicity p st G hs.mass_nonneg hs.zero_mass hv hmono z
  rw [hgraph] at hm
  have he := step_energy p st hs.mass_nonneg ha0 z (F x) hm herr
  have hrootmono := hmono z root
  rw [hGroot, sub_zero, hgraph] at hrootmono
  have hb := step_displacement_radius p st root z (F x) hs.mass_nonneg ha0 hroot
    hrootmono hs.radius (hs.energy.trans (errorBudget_bound p st.k)) he herr
  refine ⟨?_, hb.1⟩
  constructor
  · linarith [hs.mass_nonneg]
  · exact Or.inl (by linarith [hs.mass_nonneg])
  · simp
  · exact ⟨ha, haMax⟩
  · rfl
  · simpa only [currentPoint, Nat.add_one_ne_zero, ite_false] using hb.2
  · have hn : 0 ≤ 7 / 16 * ((st.mass + a) / a) ^ 2 * ‖z - midpoint p st a‖ ^ 2 := by positivity
    have hprev := hs.energy
    change potential p st ≤ errorBudget p st.k at hprev
    unfold potential at hprev ⊢
    simp only [currentValue, currentPoint, Nat.add_one_ne_zero, ite_false]
    rw [errorBudget_succ]
    dsimp only [z] at he hn
    linarith only [he, hn, hprev]

end LongTails.Proofs.CohypomonotoneNewtonOuter
