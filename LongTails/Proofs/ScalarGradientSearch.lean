import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Calculus.Deriv.Mul

open MeasureTheory Set
open scoped NNReal ENNReal

namespace OracleTemplate.ScalarGradientSearch

lemma derivative_integral_lower {f g : ℝ → ℝ} {x R lower Δ : ℝ}
    (hg : ∀ y, HasDerivAt f (g y) y)
    (hi : IntervalIntegrable g volume x (x + R))
    (hlower : ∀ y, lower ≤ f y) (hgap : f x - lower ≤ Δ) :
    -Δ ≤ ∫ y in x..x + R, g y := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hg y) hi]
  linarith [hlower (x + R)]

lemma abs_le_of_bracket {g : ℝ → ℝ} {lo hi x ε : ℝ}
    (hlo : g lo ≤ 0) (hhi : 0 ≤ g hi)
    (hl : |g x - g lo| ≤ ε) (hr : |g x - g hi| ≤ ε) :
    |g x| ≤ ε := by
  rw [abs_le] at hl hr ⊢
  constructor <;> linarith

lemma accurate_sign_or_small {value estimate ε : ℝ}
    (he : |estimate - value| ≤ ε / 4)
    (haccept : -ε / 2 ≤ estimate) :
    |value| ≤ ε ∨ 0 < value := by
  rcases le_or_gt estimate (ε / 2) with h | h
  · left
    have hε : 0 ≤ ε := by linarith [abs_nonneg (estimate - value)]
    rw [abs_le] at he ⊢
    constructor <;> linarith
  · right
    have hε : 0 ≤ ε := by linarith [abs_nonneg (estimate - value)]
    rw [abs_le] at he
    linarith

lemma reliable_initial_orientation {value estimate ε : ℝ} (hε : 0 < ε)
    (he : |estimate - value| ≤ ε / 16) (hcontinue : ε / 2 < |estimate|) :
    (if estimate ≤ 0 then (1 : ℝ) else -1) = (if value ≤ 0 then 1 else -1) ∧
      (if estimate ≤ 0 then (1 : ℝ) else -1) * value < 0 := by
  rw [abs_le] at he
  by_cases hs : estimate ≤ 0
  · rw [abs_of_nonpos hs] at hcontinue
    have hv : value < 0 := by linarith
    simp only [hs, hv.le, ite_true, one_mul]
    exact ⟨True.intro, hv⟩
  · have hs' : 0 < estimate := lt_of_not_ge hs
    rw [abs_of_pos hs'] at hcontinue
    have hv : 0 < value := by linarith
    simp only [hs, not_le_of_gt hv, ite_false, neg_one_mul]
    exact ⟨True.intro, neg_neg_of_pos hv⟩

lemma reliable_initial_acceptance {value estimate ε : ℝ}
    (he : |estimate - value| ≤ ε / 16) (hstop : |estimate| ≤ ε / 2) :
    |value| ≤ 9 * ε / 16 := by
  rw [abs_le] at he hstop ⊢
  constructor <;> linarith

lemma weighted_cover_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] (events : ι → Set Ω) (weights : ι → ℝ)
    (hm : ∀ i, MeasurableSet (events i))
    {g : Ω → ℝ} (hg : Integrable g P) {a b : ℝ}
    (hmean : -b ≤ ∫ ω, g ω ∂P)
    (hcover : ∀ᵐ ω ∂P, g ω ≤ -a + ∑ i, weights i * (events i).indicator (fun _ => (1 : ℝ)) ω) :
    a - b ≤ ∑ i, weights i * P.real (events i) := by
  classical
  have hi (i : ι) : Integrable
      (fun ω => weights i * (events i).indicator (fun _ => (1 : ℝ)) ω) P :=
    ((integrable_const 1).indicator (hm i)).const_mul (weights i)
  have hb := integral_mono_ae hg ((integrable_const (-a)).add
    (integrable_finsetSum Finset.univ (fun i _ => hi i))) hcover
  simp only [Pi.add_apply] at hb
  rw [integral_add (integrable_const (-a))
      (integrable_finsetSum Finset.univ (fun i _ => hi i)),
    integral_finsetSum _ (fun i _ => hi i)] at hb
  simp_rw [integral_const_mul] at hb
  have he (i : ι) : (∫ ω, (events i).indicator (fun _ => (1 : ℝ)) ω ∂P) = P.real (events i) := by
    exact integral_indicator_one (hm i)
  simp_rw [he] at hb
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hb
  linarith

lemma exists_large_weighted_event {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) {mass : ℝ} (h : mass ≤ ∑ i, w i) :
    ∃ i, mass / Fintype.card ι ≤ w i := by
  classical
  by_contra hn
  push Not at hn
  have hs := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    (fun i (_ : i ∈ Finset.univ) => hn i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  rw [mul_div_cancel₀ _ hc] at hs
  linarith

lemma dyadic_majorant {a t : ℝ} (ha : 0 ≤ a) (n : ℕ)
    (ht : t ≤ a * 2 ^ n) :
    t ≤ a + ∑ j ∈ Finset.range n,
      if a * 2 ^ j ≤ t then 2 * (a * 2 ^ j) else 0 := by
  induction n with
  | zero => simpa using ht
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases h : t ≤ a * 2 ^ n
    · have hp : 0 ≤ if a * 2 ^ n ≤ t then 2 * (a * 2 ^ n) else 0 := by
        split_ifs <;> positivity
      linarith [ih h]
    · rw [ite_eq_left (le_of_lt (lt_of_not_ge h))]
      have hs : 0 ≤ ∑ j ∈ Finset.range n,
          if a * 2 ^ j ≤ t then 2 * (a * 2 ^ j) else 0 := by
        apply Finset.sum_nonneg
        intro j hj
        split_ifs <;> positivity
      rw [pow_succ] at ht
      nlinarith

lemma dyadic_signed_majorant {a t : ℝ} (ha : 0 ≤ a) (n : ℕ)
    (ht : t ≤ a * 2 ^ n) :
    t ≤ -a + (if -a ≤ t then 2 * a else 0) +
      ∑ j ∈ Finset.range n,
        if a * 2 ^ j ≤ t then 2 * (a * 2 ^ j) else 0 := by
  by_cases h : -a ≤ t
  · rw [ite_eq_left h]
    linarith [dyadic_majorant ha n ht]
  · rw [ite_eq_right h]
    have hs : 0 ≤ ∑ j ∈ Finset.range n,
        if a * 2 ^ j ≤ t then 2 * (a * 2 ^ j) else 0 := by
      apply Finset.sum_nonneg
      intro j hj
      split_ifs <;> positivity
    linarith [lt_of_not_ge h]

lemma peak_interval_positive {g : ℝ → ℝ} {H ν S w z : ℝ}
    (hH : 0 ≤ H) (hν : 0 ≤ ν) (hw : 0 ≤ w)
    (hscale : H * w ^ ν ≤ S) (hpeak : 2 * S ≤ g z)
    (hholder : ∀ x y, |g x - g y| ≤ H * |x - y| ^ ν) :
    ∀ x ∈ Icc (z - w) z, S ≤ g x := by
  intro x hx
  have hd : |x - z| ≤ w := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have he := (hholder x z).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hd hν) hH)
  rw [abs_le] at he
  linarith [he.1]

lemma peak_interval_left_nonneg {g : ℝ → ℝ} {H ν S w z : ℝ}
    (hH : 0 ≤ H) (hν : 0 ≤ ν) (_hw : 0 ≤ w) (hS : 0 < S)
    (hz : 0 ≤ z) (hscale : H * w ^ ν ≤ S)
    (hzero : g 0 ≤ 0) (hpeak : 2 * S ≤ g z)
    (hholder : ∀ x y, |g x - g y| ≤ H * |x - y| ^ ν) :
    0 ≤ z - w := by
  by_contra hn
  have hzw : z ≤ w := by linarith
  have he := hholder z 0
  simp only [sub_zero, abs_of_nonneg hz] at he
  have hb := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz hzw hν) hH
  rw [abs_le] at he
  linarith [he.2]

lemma oriented_error {s a b r : ℝ} (hs : |s| = 1) (he : |a - b| ≤ r) :
    |s * a - s * b| ≤ r := by
  rw [← mul_sub, abs_mul, hs, one_mul]
  exact he

lemma oriented_holder {g : ℝ → ℝ} {H ν s x0 : ℝ} (hs : |s| = 1)
    (hg : ∀ x y, |g x - g y| ≤ H * |x - y| ^ ν) (a b : ℝ) :
    |s * g (x0 + s * a) - s * g (x0 + s * b)| ≤ H * |a - b| ^ ν := by
  rw [← mul_sub, abs_mul, hs, one_mul]
  have h := hg (x0 + s * a) (x0 + s * b)
  have he : x0 + s * a - (x0 + s * b) = s * (a - b) := by ring
  simpa only [he, abs_mul, hs, one_mul] using h

set_option backward.isDefEq.respectTransparency false in
lemma oriented_derivative {f g : ℝ → ℝ} (hg : ∀ x, HasDerivAt f (g x) x)
    (x0 s t : ℝ) :
    HasDerivAt (fun y => f (x0 + s * y)) (s * g (x0 + s * t)) t := by
  have h := (hg (x0 + s * t)).comp t (((hasDerivAt_id t).const_mul s).const_add x0)
  simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using h

lemma continuous_of_holder {g : ℝ → ℝ} {H ν : ℝ} (hH : 0 ≤ H) (hν : 0 < ν)
    (hg : ∀ x y, |g x - g y| ≤ H * |x - y| ^ ν) : Continuous g := by
  let C : NNReal := ⟨H, hH⟩
  have hh : HolderWith C ⟨ν, hν.le⟩ g := by
    intro x y
    have hc : (C : ENNReal) = ENNReal.ofReal H := by
      exact (ENNReal.ofReal_coe_nnreal).symm
    change edist (g x) (g y) ≤ (C : ENNReal) * edist x y ^ ν
    rw [hc, edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hν.le, ← ENNReal.ofReal_mul hH]
    exact ENNReal.ofReal_le_ofReal (hg x y)
  exact hh.continuous hν

lemma unit_interval_mean (g : ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ t in Set.Icc (0 : ℝ) 1, g (R * t)) =
      (1 / R) * ∫ t in (0 : ℝ)..R, g t := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_mul_left g hR.ne']
  simp only [mul_zero, mul_one, smul_eq_mul, one_div]

lemma uniform_derivative_lower {f g : ℝ → ℝ} {R lower Δ : ℝ}
    (hR : 0 < R) (hg : ∀ y, HasDerivAt f (g y) y) (hgc : Continuous g)
    (hlower : ∀ y, lower ≤ f y) (hgap : f 0 - lower ≤ Δ) :
    -Δ / R ≤ ∫ t in Set.Icc (0 : ℝ) 1, g (R * t) := by
  rw [unit_interval_mean g hR]
  have h := derivative_integral_lower (x := 0) (R := R) hg
    (hgc.intervalIntegrable _ _) hlower hgap
  simp only [zero_add] at h
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt (one_div_pos.mpr hR))
  simpa only [one_div, div_eq_mul_inv, mul_one, mul_comm] using hmul

lemma unit_interval_mass {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Icc a b) = b - a := by
  have hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨ha.trans hx.1, hx.2.trans hb⟩
  rw [measureReal_def, Measure.restrict_apply measurableSet_Icc, Set.inter_eq_left.mpr hsub,
    Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma uniform_peak_mass {g : ℝ → ℝ} {H ν S w z R : ℝ}
    (hH : 0 ≤ H) (hν : 0 ≤ ν) (hw : 0 ≤ w) (hS : 0 < S) (hR : 0 < R)
    (hz : z ∈ Set.Icc 0 R) (hscale : H * w ^ ν ≤ S)
    (hzero : g 0 ≤ 0) (hpeak : 2 * S ≤ g z)
    (hholder : ∀ x y, |g x - g y| ≤ H * |x - y| ^ ν) :
    w / R ≤ (volume.restrict (Set.Icc (0 : ℝ) 1)).real {u | S ≤ g (R * u)} := by
  have hleft := peak_interval_left_nonneg hH hν hw hS hz.1 hscale hzero hpeak hholder
  have hpositive := peak_interval_positive hH hν hw hscale hpeak hholder
  have hm := unit_interval_mass (div_nonneg hleft hR.le)
    (div_le_div_of_nonneg_right (by linarith : z - w ≤ z) hR.le) ((div_le_one hR).mpr hz.2)
  have he : z / R - (z - w) / R = w / R := by ring
  rw [he] at hm
  rw [← hm]
  refine measureReal_mono ?_ (by finiteness)
  intro u hu
  apply hpositive
  constructor
  · have h := (div_le_iff₀ hR).mp hu.1
    nlinarith
  · have h := (le_div_iff₀ hR).mp hu.2
    nlinarith

lemma dyadic_cover_mass {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {g : Ω → ℝ} (hg : Measurable g) (hi : Integrable g P) {a b : ℝ} (ha : 0 ≤ a)
    (n : ℕ) (hmean : -b ≤ ∫ ω, g ω ∂P) (hcap : ∀ᵐ ω ∂P, g ω ≤ a * 2 ^ n) :
    a - b ≤ 2 * a * P.real {ω | -a ≤ g ω} +
      ∑ j : Fin n, 2 * (a * 2 ^ j.val) * P.real {ω | a * 2 ^ j.val ≤ g ω} := by
  let events : Option (Fin n) → Set Ω
    | none => {ω | -a ≤ g ω}
    | some j => {ω | a * 2 ^ j.val ≤ g ω}
  let weights : Option (Fin n) → ℝ
    | none => 2 * a
    | some j => 2 * (a * 2 ^ j.val)
  have hm (i : Option (Fin n)) : MeasurableSet (events i) := by
    cases i <;> exact measurableSet_le measurable_const hg
  have hcover : ∀ᵐ ω ∂P, g ω ≤ -a + ∑ i, weights i * (events i).indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hcap] with ω hω
    have h := dyadic_signed_majorant ha n hω
    simp only [Fintype.sum_option, weights, events, Set.indicator_apply, Set.mem_ofPred_eq,
      mul_ite, mul_one, mul_zero]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if a * 2 ^ j ≤ g ω then 2 * (a * 2 ^ j) else 0)]
    simpa only [add_assoc] using h
  have h := weighted_cover_integral events weights hm hi hmean hcover
  simpa only [Fintype.sum_option, weights, events] using h

lemma characteristic_power {H Δ ν : ℝ} (hH : 0 < H) (hΔ : 0 < Δ) (hν : 0 < ν) :
    (H ^ (1 / (1 + ν)) * Δ ^ (ν / (1 + ν))) ^ (1 + ν) = H * Δ ^ ν := by
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hH.le, ← Real.rpow_mul hΔ.le]
  have hne : 1 + ν ≠ 0 := by positivity
  rw [div_mul_cancel₀ _ hne, div_mul_cancel₀ _ hne, Real.rpow_one]

lemma peak_width_gap {H Δ ν S : ℝ} (hH : 0 < H) (hΔ : 0 < Δ) (hν : 0 < ν)
    (hS : H ^ (1 / (1 + ν)) * Δ ^ (ν / (1 + ν)) ≤ S) :
    Δ ≤ S * (S / H) ^ (1 / ν) := by
  have hSp : 0 < S := lt_of_lt_of_le (by positivity) hS
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ H ^ (1 / (1 + ν)) * Δ ^ (ν / (1 + ν)))
    hS (by positivity : 0 ≤ 1 + ν)
  rw [characteristic_power hH hΔ hν] at hp
  have hw : ((S / H) ^ (1 / ν)) ^ ν = S / H := by
    rw [one_div, Real.rpow_inv_rpow (by positivity) hν.ne']
  have he : (S * (S / H) ^ (1 / ν)) ^ ν = S ^ (1 + ν) / H := by
    rw [Real.mul_rpow hSp.le (by positivity), hw, Real.rpow_add hSp, Real.rpow_one]
    ring
  apply (Real.rpow_le_rpow_iff hΔ.le (by positivity : 0 ≤ S * (S / H) ^ (1 / ν)) hν).mp
  rw [he]
  apply (le_div_iff₀ hH).mpr
  simpa only [mul_comm] using hp

end OracleTemplate.ScalarGradientSearch
