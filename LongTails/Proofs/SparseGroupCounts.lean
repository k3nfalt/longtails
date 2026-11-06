import LongTails.Proofs.SparseGroupEmpirical
import LongTails.Proofs.SparseConfidenceCertificate

open scoped BigOperators

namespace LongTails.Proofs.SparseGroupCounts

open LongTails.Setups.OptimumGapGroupDro LongTails.Algorithms.SparseGroupSampling
open SparseGroupEmpirical

lemma radius_count_bound (q : Public) (n : ℕ) (a : ℝ) (ha : 0 < a)
    (hL : 0 ≤ confidenceLog q)
    (hr : a ≤ 4 * (q.d + 1 : ℝ) * radius q n) :
    (n : ℝ) ≤ 128 * (q.d + 1 : ℝ) ^ 2 * confidenceLog q / a ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero]
    positivity
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsqrt : radius q n ≤ Real.sqrt (8 * confidenceLog q / n) := by
    simp only [radius, ite_eq_right hn]
    exact min_le_right _ _
  have hr' : a ≤ 4 * (q.d + 1 : ℝ) * Real.sqrt (8 * confidenceLog q / n) :=
    hr.trans (mul_le_mul_of_nonneg_left hsqrt (by positivity))
  have hsq : a ^ 2 ≤ 16 * (q.d + 1 : ℝ) ^ 2 * (8 * confidenceLog q / n) := by
    have ht := sq_le_sq₀ ha.le (by positivity : 0 ≤ 4 * (q.d + 1 : ℝ) * Real.sqrt (8 * confidenceLog q / n))
    have h := ht.mpr hr'
    rw [mul_pow, Real.sq_sqrt (by positivity)] at h
    nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  have hmul := (mul_le_mul_of_nonneg_right hsq hnpos.le)
  have he : (16 * (q.d + 1 : ℝ) ^ 2 * (8 * confidenceLog q / n)) * n =
      128 * (q.d + 1 : ℝ) ^ 2 * confidenceLog q := by
    field_simp
    ring
  rw [he] at hmul
  nlinarith

lemma selected_radius_bound {ι : Type*} [Fintype ι]
    (w r Δ : ι → ℝ) (S : Finset ι) (i : ι) (s ε E : ℝ)
    (hs : 1 ≤ s) (hε : 0 < ε) (hcard : (S.card : ℝ) ≤ s)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1)
    (hr : ∀ j, 0 ≤ r j) (hΔ : ∀ j, 0 ≤ Δ j)
    (hsupport : ∀ j, j ∉ S → w j = 0)
    (hmax : ∀ j, w j * r j ≤ w i * r i)
    (hcert : ∑ j, w j * Δ j ≤ 2 * ∑ j, w j * r j + E)
    (hE : E ≤ ε / (8 * s)) (hactive : ε / (4 * s) < w i * r i) :
    max (Δ i) ε ≤ 4 * s * r i := by
  have hspos : 0 < s := by linarith
  have hprod : 0 < w i * r i := (div_pos hε (by positivity)).trans hactive
  have hwi : 0 < w i := (mul_pos_iff.mp hprod).resolve_right (by intro h; linarith [hw i]) |>.1
  have hwle : w i ≤ 1 := by
    calc
      w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
      _ = 1 := hsum
  have herror : E ≤ w i * r i := by
    have hfrac : ε / (8 * s) ≤ ε / (4 * s) := by
      apply div_le_div_of_nonneg_left hε.le (by positivity)
      linarith
    exact hE.trans (hfrac.trans hactive.le)
  have hgap := SparseConfidenceCertificate.selected_gap_bound w r Δ S i E hw hΔ hwi
    hsupport (fun j _ => hmax j) hcert herror
  have hgap' : Δ i ≤ 4 * s * r i := by
    have hcoef : 2 * (S.card : ℝ) + 1 ≤ 4 * s := by linarith
    exact hgap.trans (mul_le_mul_of_nonneg_right hcoef (hr i))
  have heps : ε ≤ 4 * s * r i := by
    have hri : w i * r i ≤ r i := by simpa using mul_le_mul_of_nonneg_right hwle (hr i)
    simpa only [mul_comm (r i)] using ((div_lt_iff₀ (by positivity : 0 < 4 * s)).mp (hactive.trans_le hri)).le
  exact max_le hgap' heps

end LongTails.Proofs.SparseGroupCounts
