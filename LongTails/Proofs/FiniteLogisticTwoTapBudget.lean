import Mathlib.Analysis.Complex.ExponentialBounds
import LongTails.Proofs.FiniteLogisticTwoTapTrajectory
import LongTails.Proofs.FiniteLogisticTwoTapHittingTime

open scoped RealInnerProductSpace
open LongTails.Proofs.TwoTapGaussianBounds
open LongTails.Proofs.FiniteLogisticTwoTapExecution
open LongTails.Proofs.FiniteLogisticTwoTapCoordinates
open LongTails.Proofs.FiniteLogisticTwoTapHittingTime
open LongTails.Setups.FiniteLogisticTwoTap
open LongTails.Proofs.FiniteLogisticTwoTapTrajectory
open LongTails.Proofs.FiniteLogisticTwoTapPhase
open LongTails.Proofs.FiniteLogisticPerceptronWarmup

namespace LongTails.Proofs.FiniteLogisticTwoTapBudget

lemma logarithmic_stage {δ c M : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hδ' : δ ≤ c) (hM : 1 ≤ M) :
    (⌈Real.log M / Real.log (1+δ/c)⌉₊:ℝ)*δ ≤ 2*c*Real.log M+δ := by
  have hx := div_pos hδ hc
  have hx' := (div_le_one hc).mpr hδ'
  have hlog := Real.le_log_one_add_of_nonneg hx.le
  have hlow : δ/c/2 ≤ Real.log (1+δ/c) := by
    apply le_trans _ hlog
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hx' hx.le]
  have hlog' : 0 < Real.log (1+δ/c) := by linarith
  have hm := Real.log_nonneg hM
  have H := Nat.ceil_lt_add_one (div_nonneg hm hlog'.le)
  have hfrac : Real.log M/Real.log (1+δ/c)*δ ≤ 2*c*Real.log M := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hlog']
    have H₁ : δ ≤ 2*c*Real.log (1+δ/c) := by
      have H₂ := (div_le_iff₀ hc).mp (show δ/c ≤ 2*Real.log (1+δ/c) by linarith)
      linarith
    nlinarith only [mul_le_mul_of_nonneg_left H₁ hm]
  nlinarith only [hfrac,mul_le_mul_of_nonneg_right H.le hδ.le]

lemma phase_budget (p : Params) (hp : spec.valid p) :
    let δ := stepsize p.d*p.μ
    let n := ⌈Real.log (16384*(p.d:ℝ)/p.ρ)/Real.log (1+δ/4)⌉₊
    let m := ⌈Real.log (4096*(p.d:ℝ)/p.r)/Real.log (1+δ/336)⌉₊
    let l := ⌈52/δ⌉₊
    n+m+l ≤ ⌈2^52*Real.sqrt p.d/p.μ * Real.log (16384*(p.d:ℝ)/(p.ρ*p.r))⌉₊ := by
  intro δ n m l
  have hpvalid := hp
  obtain ⟨hd,hμ,hμ',hρ,hρ',hr,hcap⟩ := hpvalid
  have hD : (3:ℝ) ≤ p.d := by exact_mod_cast hd
  have hd₀ : (0:ℝ) < p.d := by linarith
  have hS : 1 ≤ Real.sqrt p.d := by simpa using Real.sqrt_le_sqrt (show (1:ℝ) ≤ p.d by linarith)
  have hs₀ : 0 < Real.sqrt p.d := by linarith
  have hδ : 0 < δ := by dsimp [δ,stepsize]; positivity
  have hδ' : δ ≤ 1 := by
    have H := (div_le_one hs₀).mpr hS
    dsimp [δ,stepsize]
    nlinarith [mul_le_mul_of_nonneg_right H hμ.le]
  have hs : Real.sqrt (p.μ*p.ρ) ≤ 1 := by
    nlinarith [Real.sq_sqrt (mul_nonneg hμ.le hρ.le),
      mul_le_mul_of_nonneg_left hρ'.le hμ.le]
  have hr' : p.r ≤ 1 := by
    apply hcap.trans
    apply (div_le_one (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hs hρ.le,sq_nonneg ((p.d:ℝ)-1)]
  let V := 16384*(p.d:ℝ)/(p.ρ*p.r)
  have hV : 3 ≤ V := by
    apply (le_div_iff₀ (mul_pos hρ hr)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hr' hρ.le]
  have hlog : 1 ≤ Real.log V := (Real.le_log_iff_exp_le (by linarith)).mpr (Real.exp_one_lt_three.le.trans hV)
  have hA : 16384*(p.d:ℝ)/p.ρ ≤ V := by
    dsimp [V]
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hρ hr)
      (by nlinarith [mul_le_mul_of_nonneg_left hr' hρ.le])
  have hB : 4096*(p.d:ℝ)/p.r ≤ V := by
    dsimp [V]
    apply (div_le_div_iff₀ hr (mul_pos hρ hr)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hρ'.le (mul_nonneg hd₀.le hr.le),mul_pos hd₀ hr]
  have hA' : 1 ≤ 16384*(p.d:ℝ)/p.ρ := (le_div_iff₀ hρ).mpr (by linarith)
  have hB' : 1 ≤ 4096*(p.d:ℝ)/p.r := (le_div_iff₀ hr).mpr (by linarith)
  have H₁ := logarithmic_stage hδ (by norm_num : (0:ℝ) < 4) (by linarith) hA'
  have H₂ := logarithmic_stage hδ (by norm_num : (0:ℝ) < 336) (by linarith) hB'
  have H₃ := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (by positivity : 0 ≤ 52/δ)).le hδ.le
  rw [add_mul,div_mul_cancel₀ _ hδ.ne',one_mul] at H₃
  change (n:ℝ)*δ ≤ _ at H₁
  change (m:ℝ)*δ ≤ _ at H₂
  change (l:ℝ)*δ ≤ _ at H₃
  have Htotal : (n+m+l:ℝ)*δ ≤ 4096*Real.log V := by
    linarith [Real.log_le_log (by positivity) hA,Real.log_le_log (by positivity) hB]
  have H : 4096/δ = 2^52*Real.sqrt p.d/p.μ := by dsimp [δ,stepsize]; field_simp; ring
  apply (Nat.cast_le (α := ℝ)).mp
  apply le_trans _ (Nat.le_ceil _)
  push_cast
  rw [← H,div_mul_eq_mul_div]
  exact (le_div_iff₀ hδ).mpr Htotal

lemma oriented_hit (p : Params) (hp : spec.valid p) (i : Fin p.d) (hi : finRotate p.d i ≠ i)
    (w : Weights p.d) (hw : ‖w‖ ≤ p.r)
    (hplus : p.ρ/(32*Real.sqrt p.d)*p.r < ⟪mode i 1,w⟫)
    (hminus : p.ρ/(32*Real.sqrt p.d)*p.r < |⟪mode i (-1),w⟫|) :
    ∃ k ≤ ⌈2^52*Real.sqrt p.d/p.μ * Real.log (16384*(p.d:ℝ)/(p.ρ*p.r))⌉₊,
      Separates p.μ i ((step p.μ (stepsize p.d) i)^[k] w) := by
  let s := scales p hp
  let δ := stepsize p.d*p.μ
  let n := ⌈Real.log (16384*(p.d:ℝ)/p.ρ)/Real.log (1+δ/4)⌉₊
  let m := ⌈Real.log (4096*(p.d:ℝ)/p.r)/Real.log (1+δ/336)⌉₊
  let l := ⌈52/δ⌉₊
  let f := step p.μ (stepsize p.d) i
  let z := fun k : ℕ => coords i (f^[k] (f^[n] w))
  have H := warm_entry p hp i hi w hw hplus hminus
  change Cone s (z 0) ∧ (z 0).q ≤ 0 ∧ p.r ≤ mass (z 0) ∧ mass (z 0) ≤ 4096*s.k at H
  have hstep (t : ℕ) : z (t+1) = advance s (z t) := by
    dsimp only [z]
    rw [Function.iterate_succ_apply']
    exact coordinate_step p hp i hi _
  have hδ : 0 < δ := mul_pos s.hη s.hμ
  have hδ' : δ ≤ 1 := by
    obtain ⟨_,H₁,H₂,_,_,_⟩ := scale_bounds s
    change s.η*s.μ ≤ 1
    nlinarith [mul_le_mul_of_nonneg_left H₁ s.hη.le]
  have hpvalid := hp
  obtain ⟨hd,hμ,hμ',hρ,hρ',hr,hcap⟩ := hpvalid
  have hD : (3:ℝ) ≤ p.d := by exact_mod_cast hd
  have hs : 1 ≤ Real.sqrt p.d := by simpa using Real.sqrt_le_sqrt (show (1:ℝ) ≤ p.d by linarith)
  have hsk : s.k ≤ 1 := (div_le_one (by linarith : 0 < Real.sqrt p.d)).mpr hs
  have hD₀ : (0:ℝ) < p.d := by linarith
  have hsmall := H.2.2.1.trans H.2.2.2
  have hM : 1 ≤ 4096*(p.d:ℝ)/p.r := (le_div_iff₀ hr).mpr (by linarith)
  obtain ⟨hlo,_⟩ := warmup_horizon (show 1 < 1+δ/336 by linarith)
    (by linarith : 1+δ/336 ≤ 2) hM
  change _ ≤ (1+δ/336)^m at hlo
  have hm : 4096*s.k ≤ (1+s.η*s.μ/336)^m*mass (z 0) := by
    have H₁ := (div_le_iff₀ hr).mp hlo
    have H₂ := mul_le_mul_of_nonneg_left H.2.2.1 (by positivity : 0 ≤ (1+δ/336)^m)
    change _ ≤ (1+δ/336)^m*mass (z 0)
    linarith
  have hl : 52 ≤ (l:ℝ)*s.η*s.μ := by
    have H₁ := (div_le_iff₀ hδ).mp (Nat.le_ceil (52/δ))
    change 52 ≤ (l:ℝ)*(s.η)*s.μ
    convert H₁ using 1
    dsimp [δ,s,scales]
    ring
  obtain ⟨t,ht,hq,hit⟩ := exists_crossing s z hstep H.1 H.2.1 H.2.2.2 m l hm hl
  have Hhit := crossing_separates s z hstep H.1 H.2.2.2 t hq hit
  have Htotal := phase_budget p hp
  change n+m+l ≤ _ at Htotal
  refine ⟨(t+1)+n,by omega,?_⟩
  rw [Function.iterate_add_apply]
  exact coordinate_separates p hp i _ Hhit

lemma radius_budget (p : Params) (hp : spec.valid p) :
    ⌈2^52*Real.sqrt p.d/p.μ * Real.log (16384*(p.d:ℝ)/(p.ρ*p.r))⌉₊ ≤
      ⌈2^53*Real.sqrt p.d/p.μ * Real.log (1/p.r)⌉₊ := by
  obtain ⟨hd,hμ,hμ',hρ,hρ',hr,hcap⟩ := hp
  have hD : (3:ℝ) ≤ p.d := by exact_mod_cast hd
  have hd₀ : (0:ℝ) < p.d := by linarith
  have hs : Real.sqrt (p.μ*p.ρ) ≤ 1 := by
    nlinarith [Real.sq_sqrt (mul_nonneg hμ.le hρ.le),mul_le_mul_of_nonneg_left hρ'.le hμ.le]
  have hR : p.r*(2^24*(p.d:ℝ)^2) ≤ p.ρ := by
    exact ((le_div_iff₀ (by positivity)).mp hcap).trans (by nlinarith [mul_le_mul_of_nonneg_right hs hρ.le])
  have hM : 16384*(p.d:ℝ)/(p.ρ*p.r) ≤ (1/p.r)^2 := by
    rw [div_pow,one_pow,div_le_div_iff₀ (mul_pos hρ hr) (sq_pos_of_pos hr)]
    have H : 16384*(p.d:ℝ)*p.r ≤ p.ρ := by
      nlinarith [mul_nonneg (mul_nonneg hd₀.le hr.le) (sub_nonneg.mpr hD),mul_nonneg hd₀.le hr.le]
    nlinarith only [mul_le_mul_of_nonneg_right H hr.le]
  have H := Real.log_le_log (by positivity) hM
  rw [Real.log_pow] at H
  apply Nat.ceil_mono
  have hh := mul_le_mul_of_nonneg_left H (show 0 ≤ 2^52*Real.sqrt p.d/p.μ by positivity)
  apply hh.trans_eq
  push_cast
  ring

lemma reaches (p : Params) (hp : spec.valid p) (i : Fin p.d) (hi : finRotate p.d i ≠ i)
    (w : Weights p.d) (hw : ‖w‖ ≤ p.r)
    (hplus : p.ρ/(32*Real.sqrt p.d)*p.r < |⟪mode i 1,w⟫|)
    (hminus : p.ρ/(32*Real.sqrt p.d)*p.r < |⟪mode i (-1),w⟫|) :
    Separates p.μ i ((stoppedStep p.μ (stepsize p.d) i)^[
      ⌈2^53*Real.sqrt p.d/p.μ * Real.log (1/p.r)⌉₊] w) := by
  by_cases h : 0 ≤ ⟪mode i 1,w⟫
  · rw [abs_of_nonneg h] at hplus
    obtain ⟨k,hk,H⟩ := oriented_hit p hp i hi w hw hplus hminus
    exact stopped_reaches (hk.trans (radius_budget p hp)) H
  · rw [abs_of_nonpos (le_of_not_ge h)] at hplus
    obtain ⟨k,hk,H⟩ := oriented_hit p hp i hi (-w) (by simpa using hw)
      (by simpa using hplus) (by simpa using hminus)
    rw [trajectory_neg,separates_neg] at H
    exact stopped_reaches (hk.trans (radius_budget p hp)) H

end LongTails.Proofs.FiniteLogisticTwoTapBudget
