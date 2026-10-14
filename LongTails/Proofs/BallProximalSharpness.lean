import LongTails.Proofs.BallProximalExact
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OracleTemplate.BallProximal

open LongTails.Setups.ConvexBallProximal

noncomputable section

def twoPhaseSlope (n m : ℕ) (r q : ℝ) (i : ℕ) : ℝ :=
  if i < n then (1 - q) * q ^ i else r / m

def twoPhaseGap (n m : ℕ) (r q : ℝ) (i : ℕ) : ℝ :=
  if i ≤ n then q ^ i else r + ((n + m : ℕ) - (i : ℝ)) * r / m

def twoPhaseEnergy (n m : ℕ) (q : ℝ) (i : ℕ) : ℝ :=
  if i < n then ((n : ℝ) - i) * (1 + q) / (1 - q) + 4 * (m : ℝ) ^ 2
  else ((n + m : ℕ) - (i : ℝ) + m) ^ 2

lemma twoPhaseGap_tail {n m i : ℕ} {r q : ℝ} (hm : 0 < m) (hqn : q ^ n = 2 * r)
    (hi : n ≤ i) : twoPhaseGap n m r q i = r + ((n + m : ℕ) - (i : ℝ)) * r / m := by
  by_cases he : i = n
  · subst i
    simp only [twoPhaseGap, le_rfl, ite_true, hqn, Nat.cast_add]
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  · simp [twoPhaseGap, show ¬i ≤ n by omega]

lemma twoPhaseEnergy_head {n m i : ℕ} {q : ℝ} (hi : i ≤ n) :
    twoPhaseEnergy n m q i = ((n : ℝ) - i) * (1 + q) / (1 - q) + 4 * (m : ℝ) ^ 2 := by
  by_cases hlt : i < n
  · simp [twoPhaseEnergy, hlt]
  · have he : i = n := by omega
    subst i
    simp [twoPhaseEnergy, Nat.cast_add]
    ring

lemma twoPhaseGap_step {n m i : ℕ} {r q : ℝ} (hm : 0 < m) (hqn : q ^ n = 2 * r)
    (_hi : i < n + m) :
    twoPhaseGap n m r q i = twoPhaseGap n m r q (i + 1) + twoPhaseSlope n m r q i := by
  by_cases hpre : i < n
  · simp only [twoPhaseGap, twoPhaseSlope, ite_eq_left hpre, ite_eq_left hpre.le,
      ite_eq_left (show i + 1 ≤ n by omega), pow_succ]
    ring
  · have hge : n ≤ i := by omega
    rw [twoPhaseGap_tail hm hqn hge, twoPhaseGap_tail hm hqn (by omega)]
    simp only [twoPhaseSlope, ite_eq_right hpre, Nat.cast_add, Nat.cast_one]
    ring

lemma twoPhaseEnergy_step {n m i : ℕ} {r q : ℝ} (hm : 0 < m)
    (hr : 0 < r) (hq : 0 < q) (hq1 : q < 1) (hqn : q ^ n = 2 * r)
    (_hi : i < n + m) :
    twoPhaseEnergy n m q i = 1 +
      2 * twoPhaseGap n m r q (i + 1) / twoPhaseSlope n m r q i +
      twoPhaseEnergy n m q (i + 1) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hq0 : q ≠ 0 := ne_of_gt hq
  have h1q : 1 - q ≠ 0 := by linarith
  have hr0 := ne_of_gt hr
  by_cases hpre : i < n
  · rw [twoPhaseEnergy_head hpre.le, twoPhaseEnergy_head (by omega)]
    simp only [twoPhaseGap, twoPhaseSlope, ite_eq_left hpre,
      ite_eq_left (show i + 1 ≤ n by omega), pow_succ, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  · have hge : n ≤ i := by omega
    rw [twoPhaseGap_tail hm hqn (by omega : n ≤ i + 1)]
    simp only [twoPhaseEnergy, twoPhaseSlope, ite_eq_right hpre,
      ite_eq_right (show ¬i + 1 < n by omega), Nat.cast_add, Nat.cast_one]
    field_simp
    ring

lemma twoPhaseSlope_positive {n m : ℕ} {r q : ℝ} (hm : 0 < m)
    (hr : 0 < r) (hq : 0 < q) (hq1 : q < 1) (i : ℕ) : 0 < twoPhaseSlope n m r q i := by
  unfold twoPhaseSlope
  split_ifs
  · exact mul_pos (by linarith) (pow_pos hq _)
  · exact div_pos hr (by positivity)

lemma twoPhaseSlope_antitone {n m : ℕ} {r q : ℝ} (hn : 0 < n)
    (hq : 0 < q) (hq1 : q < 1) (hboundary : r / m ≤ (1 - q) * q ^ (n - 1)) :
    Antitone (twoPhaseSlope n m r q) := by
  intro i j hij
  by_cases hj : j < n
  · have hi : i < n := by omega
    simp only [twoPhaseSlope, ite_eq_left hi, ite_eq_left hj]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq.le hq1.le hij) (by linarith)
  · by_cases hi : i < n
    · simp only [twoPhaseSlope, ite_eq_left hi, ite_eq_right hj]
      exact le_trans hboundary (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hq.le hq1.le (show i ≤ n - 1 by omega)) (by linarith))
    · simp [twoPhaseSlope, hi, hj]

lemma two_phase_profile {n m : ℕ} {r q : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hr : 0 < r) (hq : 0 < q) (hq1 : q < 1) (hqn : q ^ n = 2 * r)
    (hboundary : r / m ≤ (1 - q) * q ^ (n - 1)) :
    profileFeasible (n + m) r ((n : ℝ) * (1 + q) / (1 - q) + 4 * (m : ℝ) ^ 2) := by
  have hgap := fun i (hi : i < n + m) => twoPhaseGap_step hm hqn hi
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hr0 := ne_of_gt hr
  have hF0 : twoPhaseGap n m r q 0 = 1 := by simp [twoPhaseGap]
  have hFN : twoPhaseGap n m r q (n + m) = r := by
    rw [twoPhaseGap_tail hm hqn (by omega)]
    simp
  have hDN : twoPhaseEnergy n m q (n + m) = (m : ℝ) ^ 2 := by simp [twoPhaseEnergy]
  have hD0 : twoPhaseEnergy n m q 0 = (n : ℝ) * (1 + q) / (1 - q) + 4 * (m : ℝ) ^ 2 := by
    simp [twoPhaseEnergy, hn]
  have hlast : twoPhaseSlope n m r q (n + m - 1) = r / m := by
    simp [twoPhaseSlope, show ¬n + m - 1 < n by omega]
  have hmass := radialProfile_mass_eq (t := 1) (c := twoPhaseSlope n m r q)
    (N := n + m) (F := twoPhaseGap n m r q) (by intro i hi; simpa using hgap i hi)
  have henergy := radialProfile_energy_eq (t := 1) (c := twoPhaseSlope n m r q)
    (N := n + m) (F := twoPhaseGap n m r q) (D := twoPhaseEnergy n m q)
    (by norm_num) (by intro i hi; simpa using hgap i hi)
    (by intro i hi; simpa using twoPhaseEnergy_step hm hr hq hq1 hqn hi)
  rw [hF0, hFN] at hmass
  rw [hFN, hDN, hD0] at henergy
  refine ⟨twoPhaseSlope n m r q, fun i _ => twoPhaseSlope_positive hm hr hq hq1 i,
    fun i j hij _ => twoPhaseSlope_antitone hn hq hq1 hboundary hij, hmass, ?_⟩
  rw [hlast]
  have he : r / (r / (m : ℝ)) = m := by field_simp
  rw [he]
  exact henergy.le


lemma exp_ratio_bound {x : ℝ} (hx : 0 < x) :
    (1 + Real.exp (-x)) / (1 - Real.exp (-x)) ≤ 1 + 2 / x := by
  have hb : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have hb0 := Real.exp_pos x
  have he : (1 + Real.exp (-x)) / (1 - Real.exp (-x)) = 1 + 2 / (Real.exp x - 1) := by
    rw [Real.exp_neg]
    have hne : Real.exp x - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [he]
  have hxexp := Real.add_one_le_exp x
  have hd := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hx
    (show x ≤ Real.exp x - 1 by linarith)
  linarith

lemma exponential_phase_parameters {n m : ℕ} {r h : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hr : 0 < r) (hh : 0 < h) (hrel : Real.exp (-h) = 2 * r)
    (hbalance : (n : ℝ) ≤ 2 * h * m) :
    let q := Real.exp (-h / n)
    0 < q ∧ q < 1 ∧ q ^ n = 2 * r ∧ r / m ≤ (1 - q) * q ^ (n - 1) ∧
      (n : ℝ) * (1 + q) / (1 - q) + 4 * (m : ℝ) ^ 2 ≤
        n + 2 * (n : ℝ) ^ 2 / h + 4 * (m : ℝ) ^ 2 := by
  let q := Real.exp (-h / n)
  have hnR : 0 < (n : ℝ) := by positivity
  have hmR : 0 < (m : ℝ) := by positivity
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hnR)
  have hqn : q ^ n = 2 * r := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    convert hrel using 2
    field_simp
  have hpow : q ^ (n - 1) * q = 2 * r := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    exact hqn
  have hqe : q * Real.exp (h / n) = 1 := by
    dsimp [q]
    rw [← Real.exp_add, show -h / (n : ℝ) + h / n = 0 by ring, Real.exp_zero]
  have hboundary : r / m ≤ (1 - q) * q ^ (n - 1) := by
    have hExp := Real.add_one_le_exp (h / n)
    have hl : 1 / (2 * (m : ℝ)) ≤ h / n :=
      (div_le_div_iff₀ (by positivity) hnR).mpr (by nlinarith [hbalance])
    have hl' : r / m ≤ 2 * r * (Real.exp (h / n) - 1) := by
      have hm := mul_le_mul_of_nonneg_left (show 1 / (2 * (m : ℝ)) ≤ Real.exp (h / n) - 1 by linarith)
        (show 0 ≤ 2 * r by positivity)
      convert hm using 1
      field_simp
    have he : (1 - q) * q ^ (n - 1) = 2 * r * (Real.exp (h / n) - 1) := by
      have hh' := congrArg (fun z : ℝ => z * q ^ (n - 1)) hqe
      nlinarith [hpow]
    rwa [he]
  have hratio := exp_ratio_bound (div_pos hh hnR)
  rw [← neg_div] at hratio
  have hm := mul_le_mul_of_nonneg_left hratio hnR.le
  have hcost : (n : ℝ) * (1 + q) / (1 - q) + 4 * (m : ℝ) ^ 2 ≤
      n + 2 * (n : ℝ) ^ 2 / h + 4 * (m : ℝ) ^ 2 := by
    change (n : ℝ) * ((1 + q) / (1 - q)) ≤ n * (1 + 2 / (h / n)) at hm
    have he : (n : ℝ) * (1 + 2 / (h / n)) = n + 2 * (n : ℝ) ^ 2 / h := by field_simp
    rw [he] at hm
    calc
      _ = (n : ℝ) * ((1 + q) / (1 - q)) + 4 * (m : ℝ) ^ 2 := by ring
      _ ≤ _ := add_le_add hm le_rfl
  exact ⟨hq, hq1, hqn, hboundary, hcost⟩

lemma rounded_phase_energy {K m h : ℝ} (hh : 0 < h)
    (hm : (m - K / (1 + 2 * h)) ^ 2 ≤ 1) (hn : K - m ≤ K) :
    K - m + 2 * (K - m) ^ 2 / h + 4 * m ^ 2 ≤
      4 * K ^ 2 / (1 + 2 * h) + K + (4 + 2 / h) := by
  have hd : 0 < 1 + 2 * h := by linarith
  have he : 2 * (K - m) ^ 2 / h + 4 * m ^ 2 =
      4 * K ^ 2 / (1 + 2 * h) + (4 + 2 / h) * (m - K / (1 + 2 * h)) ^ 2 := by
    field_simp
    ring
  have hb := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4 + 2 / h by positivity)
  linarith


lemma sharp_low_gap_family {r : ℝ} (hr : 0 < r) (hrh : r < 1 / 2) (K : ℕ)
    (hK : ⌈(K : ℝ) / (1 + 2 * Real.log (1 / (2 * r)))⌉₊ < K) :
    executionFeasible K r (4 * (K : ℝ) ^ 2 / (1 + 2 * Real.log (1 / (2 * r))) +
      K + (4 + 2 / Real.log (1 / (2 * r)))) := by
  let h := Real.log (1 / (2 * r))
  have hh : 0 < h := Real.log_pos ((one_lt_div (by positivity)).mpr (by linarith))
  let m := ⌈(K : ℝ) / (1 + 2 * h)⌉₊
  let n := K - m
  have hmK : m < K := hK
  have hKp : 0 < K := by omega
  have hKR : 0 < (K : ℝ) := by positivity
  have hd : 0 < 1 + 2 * h := by linarith
  have hm : 0 < m := Nat.ceil_pos.mpr (div_pos hKR hd)
  have hn : 0 < n := Nat.sub_pos_of_lt hmK
  have hnm : n + m = K := Nat.sub_add_cancel hmK.le
  have hcast : (n : ℝ) + m = K := by exact_mod_cast hnm
  have hceil : (K : ℝ) / (1 + 2 * h) ≤ m := Nat.le_ceil _
  have hbalance : (n : ℝ) ≤ 2 * h * m := by
    have hmul := (div_le_iff₀ hd).mp hceil
    nlinarith
  have hrel : Real.exp (-h) = 2 * r := by
    dsimp [h]
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  obtain ⟨hq, hq1, hqn, hb, hcost⟩ := exponential_phase_parameters hn hm hr hh hrel hbalance
  have hp := two_phase_profile hn hm hr hq hq1 hqn hb
  have hround : ((m : ℝ) - (K : ℝ) / (1 + 2 * h)) ^ 2 ≤ 1 := by
    have hu : (m : ℝ) < (K : ℝ) / (1 + 2 * h) + 1 :=
      Nat.ceil_lt_add_one (div_nonneg hKR.le hd.le)
    nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) - (K : ℝ) / (1 + 2 * h) by linarith)
      (show 0 ≤ 1 - ((m : ℝ) - (K : ℝ) / (1 + 2 * h)) by linarith)]
  have hrounded := rounded_phase_energy hh hround
    (show (K : ℝ) - m ≤ K by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hc : (n : ℝ) * (1 + Real.exp (-h / n)) / (1 - Real.exp (-h / n)) + 4 * (m : ℝ) ^ 2 ≤
      4 * (K : ℝ) ^ 2 / (1 + 2 * h) + K + (4 + 2 / h) := by
    have he : (K : ℝ) - m = n := by linarith
    rw [he] at hrounded
    exact le_trans hcost hrounded
  obtain ⟨a, hap, ham, hmass, he⟩ := hp
  have hp' : profileFeasible (n + m) r
      (4 * (K : ℝ) ^ 2 / (1 + 2 * h) + K + (4 + 2 / h)) :=
    ⟨a, hap, ham, hmass, le_trans he hc⟩
  rw [hnm] at hp'
  exact execution_of_profile hKp hr.le hp'

lemma constant_profile_mass (a : ℝ) (N : ℕ) :
    profileMass (radialProfile 1 (fun _ => a) N) = N * a := by
  induction N with
  | zero => simp [radialProfile, profileMass]
  | succ N ih => simp only [radialProfile, profileMass, one_mul, mul_one, ih, Nat.cast_add, Nat.cast_one]; ring

lemma constant_profile_work {a : ℝ} (ha : a ≠ 0) (N : ℕ) (r : ℝ) :
    profileWork r (radialProfile 1 (fun _ => a) N) = (N : ℝ) ^ 2 + 2 * r * N / a := by
  induction N with
  | zero => simp [radialProfile, profileWork]
  | succ N ih =>
      simp only [radialProfile, profileWork, mul_one, one_pow,
        constant_profile_mass, ih, Nat.cast_add, Nat.cast_one]
      field_simp
      ring

lemma sharp_constant_family {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {K : ℕ} (hK : 0 < K) :
    executionFeasible K r ((K : ℝ) ^ 2 / (1 - r) ^ 2) := by
  have hKR : 0 < (K : ℝ) := by positivity
  let a := (1 - r) / K
  have ha : 0 < a := div_pos (by linarith) hKR
  apply execution_of_profile hK hr.le
  refine ⟨fun _ => a, fun _ _ => ha, fun _ _ _ _ => le_rfl, ?_, ?_⟩
  · rw [constant_profile_mass]
    dsimp [a]
    field_simp
  · rw [constant_profile_work (ne_of_gt ha)]
    have hn := ne_of_gt hKR
    have hrn : 1 - r ≠ 0 := by linarith
    dsimp [a]
    apply le_of_eq
    field_simp
    ring


lemma ceil_phase_lt {h : ℝ} (hh : 0 < h) {K : ℕ}
    (hK : 1 + 2 * h ≤ 2 * h * K) : ⌈(K : ℝ) / (1 + 2 * h)⌉₊ < K := by
  have hKp : 0 < K := by
    by_contra hbad
    have he : K = 0 := by omega
    subst K
    norm_num at hK
    linarith
  have hc : ⌈(K : ℝ) / (1 + 2 * h)⌉₊ ≤ K - 1 := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (show 0 < 1 + 2 * h by linarith)).mpr
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    nlinarith
  omega

lemma execution_lower_high {N : ℕ} (hN : 0 < N) {r S : ℝ} (hr : 0 < r)
    (hrh : 1 / 2 ≤ r) (hex : executionFeasible N r S) :
    (N : ℝ) ^ 2 ≤ (1 - r) ^ 2 * S := by
  obtain ⟨a, hap, ham, hmass, he⟩ := profile_of_execution hN hr hex
  let qs := radialProfile 1 a N
  let m := a (N - 1)
  have hm : 0 < m := hap _ (by omega)
  have hqt : ∀ q ∈ qs, 0 ≤ q.1 := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := radialProfile_mem hq
    norm_num
  have hqa : ∀ q ∈ qs, m ≤ q.2 := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := radialProfile_mem hq
    simpa using ham i (N - 1) (by omega) (by omega)
  have hA : 0 < profileMass qs := by
    cases N with
    | zero => omega
    | succ N => exact radialProfile_mass_pos (by norm_num) hap
  have hh := profile_high_gap (r := r) hm hqt hqa hA (by rw [hmass]; linarith)
  have hmul := mul_le_mul_of_nonneg_left he (sq_nonneg (profileMass qs))
  have ht : profileTime qs = N := by simpa using radialProfile_time 1 a N
  change profileMass qs = 1 - r at hmass
  rw [ht, hmass] at hh
  rw [hmass] at hmul
  dsimp [m] at hh
  nlinarith

lemma execution_lower_low {N : ℕ} (hN : 0 < N) {r S : ℝ} (hr : 0 < r)
    (hrh : r < 1 / 2) (hex : executionFeasible N r S) :
    4 * (N : ℝ) ^ 2 ≤ (1 + 2 * Real.log (1 / (2 * r))) * S := by
  obtain ⟨a, hap, ham, hmass, he⟩ := profile_of_execution hN hr hex
  let qs := radialProfile 1 a N
  let m := a (N - 1)
  have hm : 0 < m := hap _ (by omega)
  have hqt : ∀ q ∈ qs, 0 ≤ q.1 := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := radialProfile_mem hq
    norm_num
  have hqa : ∀ q ∈ qs, m ≤ q.2 := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := radialProfile_mem hq
    simpa using ham i (N - 1) (by omega) (by omega)
  have hh := profile_low_gap hm hqt hqa hr (by rw [hmass]; linarith)
  have ht : profileTime qs = N := by simpa using radialProfile_time 1 a N
  change profileMass qs = 1 - r at hmass
  rw [ht, hmass, show 1 - r + r = 1 by ring] at hh
  have hl : 0 < Real.log (1 / (2 * r)) := Real.log_pos ((one_lt_div (by positivity)).mpr (by linarith))
  have hmul := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 + 2 * Real.log (1 / (2 * r)) by linarith)
  exact le_trans hh hmul

end

end OracleTemplate.BallProximal
