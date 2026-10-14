import LongTails.Proofs.FiniteMarkovOperators
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Algebra.Order.Floor.Semifield

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators Topology
open Filter

namespace OracleTemplate.MarkovProduct

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]

lemma ritt_second_difference_split (T : B →L[ℂ] B)
    (hR : ∀ n : ℕ, ((n : ℝ) + 1) * ‖(1 - T) * T ^ n‖ ≤ 5) (k l : ℕ) :
    ((k : ℝ) + 1) * ((l : ℝ) + 1) * ‖(1 - T) ^ 2 * T ^ (k + l)‖ ≤ 25 := by
  have hcomm : T ^ k * (1 - T) = (1 - T) * T ^ k := by
    rw [mul_sub, sub_mul, mul_one, one_mul, ← pow_succ, ← pow_succ']
  have he : ((1 - T) * T ^ k) * ((1 - T) * T ^ l) = (1 - T) ^ 2 * T ^ (k + l) := by
    calc
      _ = (1 - T) * (T ^ k * (1 - T)) * T ^ l := by noncomm_ring
      _ = _ := by rw [hcomm, pow_add]; noncomm_ring
  have hb := norm_mul_le ((1 - T) * T ^ k) ((1 - T) * T ^ l)
  rw [he] at hb
  have hm := mul_le_mul (hR k) (hR l)
    (mul_nonneg (by positivity) (norm_nonneg _)) (by norm_num : (0 : ℝ) ≤ 5)
  have hc : 0 ≤ ((k : ℝ) + 1) * ((l : ℝ) + 1) := by positivity
  have hh := mul_le_mul_of_nonneg_left hb hc
  nlinarith

lemma ritt_second_difference (T : B →L[ℂ] B)
    (hR : ∀ n : ℕ, ((n : ℝ) + 1) * ‖(1 - T) * T ^ n‖ ≤ 5) (n : ℕ) :
    ((n : ℝ) + 1) * ((n : ℝ) + 2) * ‖(1 - T) ^ 2 * T ^ n‖ ≤ 100 := by
  obtain ⟨k, hk | hk⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by
    exact ⟨n / 2, by omega⟩
  · have hb := ritt_second_difference_split T hR k k
    have he : k + k = n := by omega
    rw [he] at hb
    have hn : (n : ℝ) = 2 * (k : ℝ) := by exact_mod_cast hk
    rw [hn]
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      (norm_nonneg ((1 - T) ^ 2 * T ^ n)), norm_nonneg ((1 - T) ^ 2 * T ^ n)]
  · have hb := ritt_second_difference_split T hR k (k + 1)
    have he : k + (k + 1) = n := by omega
    rw [he] at hb
    have hn : (n : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
    simp only [Nat.cast_add, Nat.cast_one] at hb
    rw [hn]
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      (norm_nonneg ((1 - T) ^ 2 * T ^ n)), norm_nonneg ((1 - T) ^ 2 * T ^ n)]

lemma reciprocal_pair_sum (N m : ℕ) :
    (∑ j ∈ Finset.range m, 1 / (((N : ℝ) + j + 1) * ((N : ℝ) + j + 2))) =
      1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h1 : (N : ℝ) + m + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + m + 2 ≠ 0 := by positivity
    have h3 : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

lemma reciprocal_pair_hasSum (N : ℕ) :
    HasSum (fun j : ℕ => 1 / (((N : ℝ) + j + 1) * ((N : ℝ) + j + 2)))
      (1 / ((N : ℝ) + 1)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity) _).mpr
  simp_rw [reciprocal_pair_sum]
  have ht : Tendsto (fun m : ℕ => (N : ℝ) + m + 1) atTop atTop :=
    (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop).atTop_add tendsto_const_nhds
  simpa using tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp ht)

lemma ritt_second_difference_series_bound (T : B →L[ℂ] B)
    (hR : ∀ n : ℕ, ((n : ℝ) + 1) * ‖(1 - T) * T ^ n‖ ≤ 5)
    (c : ℕ → ℂ) (hc : ∀ j, ‖c j‖ ≤ 1) (N : ℕ) :
    ‖∑' j : ℕ, c j • ((1 - T) ^ 2 * T ^ (N + j))‖ ≤ 100 / ((N : ℝ) + 1) := by
  have hs := (reciprocal_pair_hasSum N).mul_left 100
  simp only [mul_one_div] at hs
  apply tsum_of_norm_bounded hs
  intro j
  rw [norm_smul]
  calc
    _ ≤ ‖(1 - T) ^ 2 * T ^ (N + j)‖ := by
      simpa using mul_le_mul_of_nonneg_right (hc j) (norm_nonneg _)
    _ ≤ 100 / (((N : ℝ) + j + 1) * ((N : ℝ) + j + 2)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      have h := ritt_second_difference T hR (N + j)
      push_cast at h
      nlinarith

lemma scaled_resolvent_expansion (A R : B →L[ℂ] B) (s : ℂ)
    (hR : R * (s • 1 + A) = 1) (V : B →L[ℂ] B) :
    s ^ 2 • (R * V) = s • V - A * V + R * A ^ 2 * V := by
  have h1 : s • R + R * A = 1 := by
    simpa only [mul_add, mul_smul_comm, mul_one] using hR
  have h2 : s • (R * A) + R * A ^ 2 = A := by
    have h := congrArg (fun X : B →L[ℂ] B => X * A) h1
    simpa only [add_mul, smul_mul_assoc, one_mul, pow_two, mul_assoc] using h
  have h3 : s ^ 2 • R = s • (1 : B →L[ℂ] B) - A + R * A ^ 2 := by
    calc
      _ = s • (s • R + R * A) - (s • (R * A) + R * A ^ 2) + R * A ^ 2 := by
        simp only [smul_add, smul_smul, pow_two]
        abel
      _ = _ := by rw [h1, h2]
  have h := congrArg (fun X : B →L[ℂ] B => X * V) h3
  simpa only [add_mul, sub_mul, smul_mul_assoc, one_mul] using h

lemma discrete_resolvent_isUnit [CompleteSpace B] (T : B →L[ℂ] B) (hT : ‖T‖ ≤ 1)
    (z : ℂ) (hz : 1 < ‖z‖) : IsUnit (z • (1 : B →L[ℂ] B) - T) := by
  have hb : ‖T‖ * ‖(1 : B →L[ℂ] B)‖ < ‖z‖ := by
    have hi : ‖(1 : B →L[ℂ] B)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    nlinarith [norm_nonneg T, norm_nonneg (1 : B →L[ℂ] B)]
  simpa only [resolventSet, Set.mem_ofPred_eq, Algebra.algebraMap_eq_smul_one] using
    (spectrum.mem_resolventSet_of_norm_lt_mul (𝕜 := ℂ) hb)

lemma discrete_resolvent_hasSum [CompleteSpace B] (T : B →L[ℂ] B) (hT : ‖T‖ ≤ 1)
    (z : ℂ) (hz : 1 < ‖z‖) :
    HasSum (fun n : ℕ => (z⁻¹) ^ (n + 1) • T ^ n) (Ring.inverse (z • 1 - T)) := by
  have hzpos : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hzpos)
  have hn : ‖z⁻¹ • T‖ < 1 := by
    rw [norm_smul, norm_inv]
    have hh := mul_le_mul_of_nonneg_left hT (inv_nonneg.mpr (norm_nonneg z))
    have hi : ‖z‖⁻¹ < 1 := (inv_lt_one₀ hzpos).mpr hz
    simp only [mul_one] at hh
    exact hh.trans_lt hi
  have hu := isUnit_one_sub_of_norm_lt_one hn
  have hzunit := discrete_resolvent_isUnit T hT z hz
  have hfac : z • (1 - z⁻¹ • T) = z • (1 : B →L[ℂ] B) - T := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hz0, one_smul]
  have hmul : (z⁻¹ • Ring.inverse (1 - z⁻¹ • T)) * (z • 1 - T) = 1 := by
    rw [← hfac, smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hz0, one_smul,
      Ring.inverse_mul_cancel _ hu]
  have he : z⁻¹ • Ring.inverse (1 - z⁻¹ • T) = Ring.inverse (z • 1 - T) := by
    simpa only [one_mul] using
      (Ring.eq_mul_inverse_iff_mul_eq _ 1 _ hzunit).mpr hmul
  have h := (hasSum_geom_series_inverse (z⁻¹ • T) hn).const_smul z⁻¹
  rw [he] at h
  simpa only [smul_pow, smul_smul, ← pow_succ'] using h

lemma discrete_resolvent_shift_hasSum [CompleteSpace B] (T : B →L[ℂ] B) (hT : ‖T‖ ≤ 1)
    (z : ℂ) (hz : 1 < ‖z‖) (N : ℕ) :
    HasSum (fun j : ℕ => (z⁻¹) ^ (j + N + 1) • T ^ (j + N))
      ((z⁻¹) ^ N • (Ring.inverse (z • 1 - T) * T ^ N)) := by
  have h := ((discrete_resolvent_hasSum T hT z hz).mul_right (T ^ N)).const_smul ((z⁻¹) ^ N)
  convert h using 1
  funext j
  simp only [smul_mul_assoc, smul_smul, pow_add, pow_succ]
  congr 1
  ring

lemma discrete_resolvent_split [CompleteSpace B] (T : B →L[ℂ] B) (hT : ‖T‖ ≤ 1)
    (z : ℂ) (hz : 1 < ‖z‖) (N : ℕ) :
    Ring.inverse (z • 1 - T) =
      (∑ j ∈ Finset.range N, (z⁻¹) ^ (j + 1) • T ^ j) +
      (z⁻¹) ^ N • (Ring.inverse (z • 1 - T) * T ^ N) := by
  have h := (discrete_resolvent_hasSum T hT z hz).summable.sum_add_tsum_nat_add N
  rw [(discrete_resolvent_hasSum T hT z hz).tsum_eq,
    (discrete_resolvent_shift_hasSum T hT z hz N).tsum_eq] at h
  exact h.symm

lemma discrete_resolvent_second_tail_hasSum [CompleteSpace B] (T : B →L[ℂ] B)
    (hT : ‖T‖ ≤ 1) (z : ℂ) (hz : 1 < ‖z‖) (N : ℕ) :
    HasSum (fun j : ℕ => (z⁻¹) ^ (j + 1) • ((1 - T) ^ 2 * T ^ (N + j)))
      (Ring.inverse (z • 1 - T) * (1 - T) ^ 2 * T ^ N) := by
  have hcomm : Commute T (1 - T) := by show T * (1 - T) = (1 - T) * T; noncomm_ring
  have h := (discrete_resolvent_hasSum T hT z hz).mul_right ((1 - T) ^ 2 * T ^ N)
  rw [← mul_assoc] at h
  convert h using 1
  funext j
  rw [smul_mul_assoc, ← mul_assoc, ((hcomm.pow_left j).pow_right 2).eq,
    mul_assoc, ← pow_add, Nat.add_comm j N]

lemma norm_discrete_resolvent_second_tail_le [CompleteSpace B] (T : B →L[ℂ] B)
    (hT : ‖T‖ ≤ 1) (hR : ∀ n : ℕ, ((n : ℝ) + 1) * ‖(1 - T) * T ^ n‖ ≤ 5)
    (z : ℂ) (hz : 1 < ‖z‖) (N : ℕ) :
    ‖Ring.inverse (z • 1 - T) * (1 - T) ^ 2 * T ^ N‖ ≤ 100 / ((N : ℝ) + 1) := by
  rw [← (discrete_resolvent_second_tail_hasSum T hT z hz N).tsum_eq]
  apply ritt_second_difference_series_bound T hR
  intro j
  rw [norm_pow, norm_inv]
  apply pow_le_one₀ (inv_nonneg.mpr (norm_nonneg z))
  exact inv_le_one_of_one_le₀ hz.le

lemma norm_discrete_resolvent_scaled_tail [CompleteSpace B] (T : B →L[ℂ] B)
    (hT : ‖T‖ ≤ 1) (hR : ∀ n : ℕ, ((n : ℝ) + 1) * ‖(1 - T) * T ^ n‖ ≤ 5)
    (z : ℂ) (hz : 1 < ‖z‖) (N : ℕ) :
    ‖z - 1‖ ^ 2 * ‖Ring.inverse (z • 1 - T) * T ^ N‖ ≤ ‖z - 1‖ + 105 / ((N : ℝ) + 1) := by
  let R := Ring.inverse (z • 1 - T)
  have hu := discrete_resolvent_isUnit T hT z hz
  have hh : R * ((z - 1) • 1 + (1 - T)) = 1 := by
    have he : (z - 1) • (1 : B →L[ℂ] B) + (1 - T) = z • 1 - T := by
      simp only [sub_smul, one_smul]
      abel
    rw [he]
    exact Ring.inverse_mul_cancel _ hu
  have he := scaled_resolvent_expansion (1 - T) R (z - 1) hh (T ^ N)
  have hfirst : ‖(1 - T) * T ^ N‖ ≤ 5 / ((N : ℝ) + 1) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [hR N]
  calc
    _ = ‖(z - 1) ^ 2 • (R * T ^ N)‖ := by rw [norm_smul, norm_pow]
    _ = ‖(z - 1) • T ^ N - (1 - T) * T ^ N + R * (1 - T) ^ 2 * T ^ N‖ := congrArg norm he
    _ ≤ ‖z - 1‖ * ‖T ^ N‖ + ‖(1 - T) * T ^ N‖ + ‖R * (1 - T) ^ 2 * T ^ N‖ := by
      rw [← norm_smul]
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ‖z - 1‖ * 1 + 5 / ((N : ℝ) + 1) + 100 / ((N : ℝ) + 1) := by
      gcongr
      · exact norm_power_contraction T hT N
      · exact norm_discrete_resolvent_second_tail_le T hT hR z hz N
    _ = _ := by ring

lemma norm_discrete_resolvent_scaled_split [CompleteSpace B] (T : B →L[ℂ] B)
    (hT : ‖T‖ ≤ 1) (hR : ∀ n : ℕ, ((n : ℝ) + 1) * ‖(1 - T) * T ^ n‖ ≤ 5)
    (z : ℂ) (hz : 1 < ‖z‖) (N : ℕ) :
    ‖z - 1‖ ^ 2 * ‖Ring.inverse (z • 1 - T)‖ ≤
      (N : ℝ) * ‖z - 1‖ ^ 2 + ‖z - 1‖ + 105 / ((N : ℝ) + 1) := by
  have hi : ‖z⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hz.le
  have hp : ‖∑ j ∈ Finset.range N, (z⁻¹) ^ (j + 1) • T ^ j‖ ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, ‖(z⁻¹) ^ (j + 1) • T ^ j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul, norm_pow]
        exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) hi) (norm_power_contraction T hT j)
          (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
      _ = _ := by simp
  have ht : ‖(z⁻¹) ^ N • (Ring.inverse (z • 1 - T) * T ^ N)‖ ≤
      ‖Ring.inverse (z • 1 - T) * T ^ N‖ := by
    rw [norm_smul, norm_pow]
    simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hi) (norm_nonneg _)
  have hb : ‖Ring.inverse (z • 1 - T)‖ ≤ (N : ℝ) + ‖Ring.inverse (z • 1 - T) * T ^ N‖ := by
    calc
      _ = _ := congrArg norm (discrete_resolvent_split T hT z hz N)
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hp ht)
  have hc := norm_discrete_resolvent_scaled_tail T hT hR z hz N
  calc
    _ ≤ ‖z - 1‖ ^ 2 * ((N : ℝ) + ‖Ring.inverse (z • 1 - T) * T ^ N‖) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ ≤ _ := by rw [mul_add]; nlinarith [hc]

lemma norm_discrete_resolvent_le [CompleteSpace B] (T : B →L[ℂ] B)
    (hT : ‖T‖ ≤ 1) (hR : ∀ n : ℕ, ((n : ℝ) + 1) * ‖(1 - T) * T ^ n‖ ≤ 5)
    (z : ℂ) (hz : 1 < ‖z‖) :
    ‖Ring.inverse (z • 1 - T)‖ ≤ 32 / ‖z - 1‖ := by
  have hd : 0 < ‖z - 1‖ := by
    apply norm_pos_iff.mpr
    intro he
    have hz1 := sub_eq_zero.mp he
    subst z
    norm_num at hz
  have hb : ‖z - 1‖ ^ 2 * ‖Ring.inverse (z • 1 - T)‖ ≤ 32 * ‖z - 1‖ := by
    by_cases hd10 : ‖z - 1‖ ≤ 10
    · let N : ℕ := ⌈10 / ‖z - 1‖⌉₊
      have hlo : 10 / ‖z - 1‖ ≤ (N : ℝ) := Nat.le_ceil _
      have hx : (2 : ℝ)⁻¹ ≤ 10 / ‖z - 1‖ := by
        apply (le_div_iff₀ hd).mpr
        norm_num
        linarith
      have hhi : (N : ℝ) ≤ 20 / ‖z - 1‖ := by
        have h := Nat.ceil_le_two_mul hx
        change (N : ℝ) ≤ _ at h
        convert h using 1
        ring
      have hnl : 10 ≤ (N : ℝ) * ‖z - 1‖ := (div_le_iff₀ hd).mp hlo
      have hnu : (N : ℝ) * ‖z - 1‖ ≤ 20 := (le_div_iff₀ hd).mp hhi
      have hnpos : 0 < (N : ℝ) + 1 := by positivity
      have htail : 105 / ((N : ℝ) + 1) ≤ (21 / 2 : ℝ) * ‖z - 1‖ := by
        apply (div_le_iff₀ hnpos).mpr
        nlinarith
      have hquad := mul_le_mul_of_nonneg_right hnu hd.le
      have hbase := norm_discrete_resolvent_scaled_split T hT hR z hz N
      nlinarith
    · have hbase := norm_discrete_resolvent_scaled_split T hT hR z hz 0
      norm_num at hbase
      nlinarith
  apply (le_div_iff₀ hd).mpr
  have hh : ‖z - 1‖ * (‖Ring.inverse (z • 1 - T)‖ * ‖z - 1‖) ≤ ‖z - 1‖ * 32 := by
    nlinarith [hb]
  exact le_of_mul_le_mul_left hh hd

lemma norm_inverse_one_sub_le [CompleteSpace B] (T : B →L[ℂ] B) {c : ℝ}
    (hc : c < 1) (hT : ‖T‖ ≤ c) :
    ‖Ring.inverse (1 - T)‖ ≤ (1 - c)⁻¹ := by
  have hn : ‖T‖ < 1 := hT.trans_lt hc
  rw [← geom_series_eq_inverse T hn]
  have h := tsum_geometric_le_of_norm_lt_one T hn
  have hi : ‖(1 : B →L[ℂ] B)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hd : (1 - ‖T‖)⁻¹ ≤ (1 - c)⁻¹ := by
    apply inv_anti₀ (by linarith : 0 < 1 - c)
    linarith
  linarith

lemma inverse_add_source_bound [CompleteSpace B] (X Y Z : B →L[ℂ] B) (hX : IsUnit X)
    {c : ℝ} (hc : c < 1) (hsmall : ‖Ring.inverse X * Y‖ ≤ c) :
    IsUnit (X + Y) ∧ ‖Ring.inverse (X + Y) * Z‖ ≤ (1 - c)⁻¹ * ‖Ring.inverse X * Z‖ := by
  have hn : ‖-(Ring.inverse X * Y)‖ < 1 := by simpa only [norm_neg] using hsmall.trans_lt hc
  have hu : IsUnit (1 + Ring.inverse X * Y) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hn
  have hfac : X * (1 + Ring.inverse X * Y) = X + Y := by
    rw [mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel _ hX, one_mul]
  have hnorm : ‖Ring.inverse (1 + Ring.inverse X * Y)‖ ≤ (1 - c)⁻¹ := by
    simpa only [sub_neg_eq_add] using norm_inverse_one_sub_le (-(Ring.inverse X * Y)) hc
      (by simpa only [norm_neg] using hsmall)
  constructor
  · rw [← hfac]
    exact hX.mul hu
  · rw [← hfac, Ring.inverse_mul (Or.inl hX), mul_assoc]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

lemma norm_one_add_complex_gt_one {z : ℂ} (hz : z ≠ 0) (hr : 0 ≤ z.re) : 1 < ‖1 + z‖ := by
  have hsq : ‖1 + z‖ ^ 2 = 1 + 2 * z.re + ‖z‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im]
    ring
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  nlinarith [norm_nonneg (1 + z), sq_pos_of_pos hn]

lemma ritt_resolvent_right_halfplane [CompleteSpace B] (T : B →L[ℂ] B)
    (hT : ‖T‖ ≤ 1) (hR : ∀ n : ℕ, ((n : ℝ) + 1) * ‖(1 - T) * T ^ n‖ ≤ 5)
    (z : ℂ) (hz : z ≠ 0) (hr : 0 ≤ z.re) :
    IsUnit (z • (1 : B →L[ℂ] B) + (1 - T)) ∧
      ‖Ring.inverse (z • 1 + (1 - T))‖ ≤ 32 / ‖z‖ := by
  have hnorm := norm_one_add_complex_gt_one hz hr
  have he : (1 + z) • (1 : B →L[ℂ] B) - T = z • 1 + (1 - T) := by
    rw [add_smul, one_smul]
    abel
  constructor
  · rw [← he]
    exact discrete_resolvent_isUnit T hT (1 + z) hnorm
  · have h := norm_discrete_resolvent_le T hT hR (1 + z) hnorm
    simpa only [he, add_sub_cancel_left] using h

lemma ritt_resolvent_sector [CompleteSpace B] (T : B →L[ℂ] B)
    (hT : ‖T‖ ≤ 1) (hR : ∀ n : ℕ, ((n : ℝ) + 1) * ‖(1 - T) * T ^ n‖ ≤ 5)
    (z : ℂ) (hz : z ≠ 0) (hsector : -( |z.im| / 128) ≤ z.re) :
    IsUnit (z • (1 : B →L[ℂ] B) + (1 - T)) ∧
      ‖Ring.inverse (z • 1 + (1 - T))‖ ≤ 128 / ‖z‖ := by
  by_cases hr : 0 ≤ z.re
  · obtain ⟨hu, hn⟩ := ritt_resolvent_right_halfplane T hT hR z hz hr
    exact ⟨hu, hn.trans (by gcongr; norm_num)⟩
  have hre : z.re < 0 := lt_of_not_ge hr
  have hy : 0 < |z.im| := by
    by_contra hy
    have he : |z.im| = 0 := le_antisymm (le_of_not_gt hy) (abs_nonneg _)
    rw [he] at hsector
    linarith
  let w : ℂ := (z.im : ℂ) * Complex.I
  have hwre : w.re = 0 := by simp [w]
  have hwn : ‖w‖ = |z.im| := by simp [w]
  have hw : w ≠ 0 := norm_pos_iff.mp (by rwa [hwn])
  let X : B →L[ℂ] B := w • 1 + (1 - T)
  let Y : B →L[ℂ] B := (z.re : ℂ) • 1
  obtain ⟨hX, hXn⟩ := ritt_resolvent_right_halfplane T hT hR w hw (by rw [hwre])
  change IsUnit X at hX
  change ‖Ring.inverse X‖ ≤ 32 / ‖w‖ at hXn
  rw [hwn] at hXn
  have hry : |z.re| ≤ |z.im| / 128 := by rw [abs_of_neg hre]; linarith
  have hYn : ‖Y‖ ≤ |z.re| := by
    change ‖(z.re : ℂ) • (1 : B →L[ℂ] B)‖ ≤ _
    rw [norm_smul]
    have hc : ‖(z.re : ℂ)‖ = |z.re| := by simp
    rw [hc]
    have hi : ‖(1 : B →L[ℂ] B)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    nlinarith [abs_nonneg z.re]
  have hsmall : ‖Ring.inverse X * Y‖ ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ ‖Ring.inverse X‖ * ‖Y‖ := norm_mul_le _ _
      _ ≤ (32 / |z.im|) * (|z.im| / 128) :=
        mul_le_mul hXn (hYn.trans hry) (norm_nonneg _) (by positivity)
      _ ≤ 1 / 2 := by field_simp; norm_num
  have he : X + Y = z • (1 : B →L[ℂ] B) + (1 - T) := by
    change w • (1 : B →L[ℂ] B) + (1 - T) + (z.re : ℂ) • 1 = _
    have hzsplit : w + (z.re : ℂ) = z := by
      apply Complex.ext <;> simp [w]
    rw [add_right_comm, ← add_smul, hzsplit]
  have hb := inverse_add_source_bound X Y (1 : B →L[ℂ] B) hX
    (by norm_num : (1 / 2 : ℝ) < 1) hsmall
  simp only [mul_one] at hb
  norm_num at hb
  have hzn : ‖z‖ ≤ 2 * |z.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    linarith
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  constructor
  · rw [← he]
    exact hb.1
  · rw [← he]
    calc
      _ ≤ 2 * ‖Ring.inverse X‖ := hb.2
      _ ≤ 2 * (32 / |z.im|) := mul_le_mul_of_nonneg_left hXn (by norm_num)
      _ ≤ 128 / ‖z‖ := by
        apply (le_div_iff₀ hzpos).mpr
        rw [← mul_div_assoc, div_mul_eq_mul_div]
        apply (div_le_iff₀ hy).mpr
        nlinarith

end OracleTemplate.MarkovProduct
