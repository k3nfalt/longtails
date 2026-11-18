import LongTails.Proofs.SublevelPLTrajectory

namespace OracleTemplate.SublevelWeighted

private def total (e : ℕ → ℝ) (k : ℕ) := ∑ j ∈ Finset.range k, e j

private lemma total_mono {e : ℕ → ℝ} (he : ∀ j, 0 ≤ e j) : Monotone (total e) :=
  monotone_nat_of_le_succ fun j => by simp [total, Finset.sum_range_succ, he]

private lemma prefix_bound {e : ℕ → ℝ} (he : ∀ j, 0 ≤ e j) {k K : ℕ} (hk : k ≤ K) :
    total e k ≤ k * total (fun j => e j / (j + 1)) K := by
  have h := total_mono (e := fun j => e j / (j + 1)) (fun j => div_nonneg (he j) (by positivity)) hk
  calc
    total e k ≤ ∑ j ∈ Finset.range k, (k : ℝ) * (e j / (j + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : ((j : ℝ) + 1) ≤ k := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
      calc
        e j = ((j : ℝ) + 1) * (e j / (j + 1)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hjk (div_nonneg (he j) (by positivity))
    _ = k * total (fun j => e j / (j + 1)) k := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

lemma weighted_descent {g e : ℕ → ℝ} {K : ℕ} {c p ε : ℝ}
    (he : ∀ j, 0 ≤ e j) (hc : 0 < c) (hp : 1 < p) (hp2 : p ≤ 2) (hε : 0 < ε)
    (hstep : ∀ j < K, g (j + 1) ≤ g j + e j)
    (hlocal : ∀ j < K, g j ≤ g 0 → g (j + 1) ≤ g j - c * g j ^ p + e j)
    (hK : ε ^ (-(p - 1)) < (p - 1) * c * K) :
    g K ≤ ε + 3 * (∑ j ∈ Finset.range K, e j) +
      (2 ^ p / (c * ε ^ (p - 1))) * ∑ j ∈ Finset.range K, e j / (j + 1) := by
  let z := fun j => g j - total e j
  let U := total (fun j => e j / (j + 1)) K
  have hU : 0 ≤ U := Finset.sum_nonneg fun j _ => div_nonneg (he j) (by positivity)
  have hW : ∀ k, 0 ≤ total e k := fun k => Finset.sum_nonneg fun j _ => he j
  have hcoeff : 0 ≤ (2 : ℝ) ^ p / (c * ε ^ (p - 1)) := by positivity
  have hcorr := mul_nonneg hcoeff hU
  change g K ≤ ε + 3 * total e K + _ * U
  have hz : ∀ j < K, z (j + 1) ≤ z j := by
    intro j hj
    dsimp [z, total]
    rw [Finset.sum_range_succ]
    linarith [hstep j hj]
  have hmono : ∀ {i j}, i ≤ j → j ≤ K → z j ≤ z i := by
    intro i j hij
    induction hij with
    | refl => exact fun _ => le_rfl
    | step h ih => exact fun hK' => (hz _ (by omega)).trans (ih (by omega))
  have hz0 : z 0 = g 0 := by simp [z, total]
  have hglob := hmono (Nat.zero_le K) le_rfl
  rw [hz0] at hglob
  change g K - total e K ≤ g 0 at hglob
  by_cases hsmall : g 0 ≤ ε
  · linarith [hW K]
  have hg0 : 0 < g 0 := by linarith
  by_cases hin : ∀ j ≤ K, g j ≤ g 0
  · by_contra! hbad
    have hk : ε < z K := by dsimp [z]; linarith [hW K]
    have hpos : ∀ j, j ≤ K → 0 < z j := fun j hj => hε.trans (hk.trans_le (hmono hj le_rfl))
    have hrec : ∀ j < K, z (j + 1) ≤ z j - c * z j ^ p := by
      intro j hj
      have hle : z j ≤ g j := sub_le_self _ (hW j)
      have hpow := Real.rpow_le_rpow (hpos j hj.le).le hle (by linarith : 0 ≤ p)
      have hs := hlocal j hj (hin j hj.le)
      change g (j + 1) - total e (j + 1) ≤ g j - total e j - c * z j ^ p
      simp only [total, Finset.sum_range_succ]
      linarith [mul_le_mul_of_nonneg_left hpow hc.le]
    exact (not_lt_of_ge ((SublevelRobustGradient.recursion_sum hc hp hp2 z K hpos hrec).trans
      (Real.rpow_le_rpow_of_nonpos hε hk.le (by linarith)))) hK
  push Not at hin
  obtain ⟨t, ht, hex⟩ := hin
  by_cases hhalf : ∃ j ≤ t, g j ≤ g 0 / 2
  · obtain ⟨j, hj, hlow⟩ := hhalf
    have hcomp := hmono hj ht
    change g t - total e t ≤ g j - total e j at hcomp
    linarith [hW j, total_mono he ht]
  push Not at hhalf
  let n := Nat.find (show ∃ n, n ≤ t ∧ g 0 < g n from ⟨t, le_rfl, hex⟩)
  have hn : n ≤ t ∧ g 0 < g n := Nat.find_spec (show ∃ k : ℕ, k ≤ t ∧ g 0 < g k from ⟨t, le_rfl, hex⟩)
  have hbefore : ∀ j < n, g j ≤ g 0 := by
    intro j hj
    have h := Nat.find_min (show ∃ n, n ≤ t ∧ g 0 < g n from ⟨t, le_rfl, hex⟩) hj
    exact le_of_not_gt fun hgt => h ⟨by omega, hgt⟩
  have hsum : ∀ k ≤ n, z k ≤ g 0 - k * (c * (g 0 / 2) ^ p) := by
    intro k
    induction k with
    | zero => simp [hz0]
    | succ k ih =>
      intro hkn
      have hk : k < n := by omega
      have hs := hlocal k (by omega) (hbefore k hk)
      have hpw := Real.rpow_le_rpow (by positivity : 0 ≤ g 0 / 2)
        (hhalf k (by omega)).le (by linarith : 0 ≤ p)
      have hi := ih hk.le
      change g k - total e k ≤ _ at hi
      change g (k + 1) - total e (k + 1) ≤ _
      simp only [total, Finset.sum_range_succ, Nat.cast_succ, add_mul, one_mul] at *
      linarith [mul_le_mul_of_nonneg_left hpw hc.le]
  have hsn := hsum n le_rfl
  change g n - total e n ≤ _ at hsn
  have hpr := prefix_bound he (hn.1.trans ht)
  change total e n ≤ n * U at hpr
  have hprod : (n : ℝ) * (c * (g 0 / 2) ^ p) < n * U := by linarith [hn.2]
  have hUbig := lt_of_mul_lt_mul_left hprod (by positivity)
  have hpow : g 0 * ε ^ (p - 1) ≤ g 0 ^ p := by
    rw [show g 0 ^ p = g 0 * g 0 ^ (p - 1) by
      rw [mul_comm, ← Real.rpow_add_one hg0.ne', sub_add_cancel]]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε.le (by linarith) (by linarith)) hg0.le
  rw [Real.div_rpow hg0.le (by norm_num)] at hUbig
  have h2 : 0 < (2 : ℝ) ^ p := by positivity
  have hgt : g 0 ≤ (2 : ℝ) ^ p / (c * ε ^ (p - 1)) * U := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have hbig : c * g 0 ^ p < U * 2 ^ p := by
      rw [← div_lt_iff₀ h2, mul_div_assoc]
      exact hUbig
    nlinarith [mul_le_mul_of_nonneg_left hpow hc.le]
  linarith [hW K]

end OracleTemplate.SublevelWeighted
