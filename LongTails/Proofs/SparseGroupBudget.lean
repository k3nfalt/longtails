import LongTails.Proofs.SparseGroupGeometry
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped BigOperators

namespace LongTails.Proofs.SparseGroupBudget

open LongTails.Setups.OptimumGapGroupDro LongTails.Algorithms.SparseGroupSampling
open SparseGroupGeometry

lemma log_scales (q : Public) (hR : 0 ≤ q.R) (hG : 0 ≤ q.G)
    (hε : 0 < q.ε) (hε1 : q.ε ≤ 1) (hδ : 0 < q.δ) (hδ4 : q.δ ≤ 1 / 4) :
    1 ≤ confidenceLog q ∧
    512 * q.K * (q.d + 1 : ℝ) / q.ε ≤ Real.exp (confidenceLog q) ∧
    1 / q.δ ≤ Real.exp (confidenceLog q) := by
  let A := 128 * q.K * (q.d + 1 : ℝ) / (q.ε * q.δ)
  let B := 8 + 4096 * q.R * (q.d + 1 : ℝ) ^ 2 * (1 + q.G) / q.ε
  have hK : (1 : ℝ) ≤ q.K := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q.K)
  have hs : (1 : ℝ) ≤ q.d + 1 := by have := Nat.cast_nonneg (α := ℝ) q.d; linarith
  have hnum : 512 ≤ 512 * q.K * (q.d + 1 : ℝ) := by nlinarith
  have hden : q.ε * q.δ ≤ 1 / 4 := by nlinarith
  have hA512 : 512 ≤ A := by
    apply (le_div_iff₀ (mul_pos hε hδ)).mpr
    nlinarith
  have hA : 0 < A := by linarith
  have hB : 1 ≤ B := by
    have hn : 0 ≤ 4096 * q.R * (q.d + 1 : ℝ) ^ 2 * (1 + q.G) / q.ε := by positivity
    dsimp [B]
    linarith
  have hlogB : 0 ≤ q.d * Real.log B := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hB)
  have hlogA : 1 ≤ Real.log A :=
    (Real.le_log_iff_exp_le hA).mpr (Real.exp_one_lt_three.le.trans (by linarith))
  have hLA : Real.log A ≤ confidenceLog q := by change Real.log A ≤ Real.log A + q.d * Real.log B; linarith
  have hexpA : A ≤ Real.exp (confidenceLog q) := by
    simpa only [Real.exp_log hA] using Real.exp_le_exp.mpr hLA
  refine ⟨by change 1 ≤ Real.log A + q.d * Real.log B; linarith, ?_, ?_⟩
  · apply le_trans _ hexpA
    dsimp [A]
    apply (div_le_div_iff₀ hε (mul_pos hε hδ)).mpr
    nlinarith [mul_nonneg (by nlinarith : 0 ≤ 128 - 512 * q.δ)
      (by positivity : 0 ≤ (q.K : ℝ) * (q.d + 1 : ℝ) * q.ε)]
  · apply le_trans _ hexpA
    dsimp [A]
    apply (div_le_div_iff₀ hδ (mul_pos hε hδ)).mpr
    nlinarith

lemma mesh_card_le_exp_log (q : Public) (hR : 0 ≤ q.R) (hG : 0 ≤ q.G)
    (hε : 0 < q.ε) (hε1 : q.ε ≤ 1) (hδ : 0 < q.δ) (hδ4 : q.δ ≤ 1 / 4)
    (hx0 : q.x0 ∈ q.domain) (hbound : ∀ x ∈ q.domain, ‖x - q.x0‖ ≤ q.R) :
    ((primalMesh q).card : ℝ) ≤ Real.exp (confidenceLog q) := by
  let A := 128 * q.K * (q.d + 1 : ℝ) / (q.ε * q.δ)
  let B := 8 + 4096 * q.R * (q.d + 1 : ℝ) ^ 2 * (1 + q.G) / q.ε
  have ha := coordinateScale_pos q hε hG
  have hratio : 0 ≤ q.R / coordinateScale q := div_nonneg hR ha.le
  have hceil := Nat.ceil_lt_add_one hratio
  have he : 8 * (q.R / coordinateScale q) =
      4096 * q.R * (q.d + 1 : ℝ) ^ 2 * (1 + q.G) / q.ε := by
    unfold coordinateScale
    field_simp
    ring
  have hcell : (2 * (Nat.ceil (q.R / coordinateScale q) + 1) + 1 : ℝ) ≤ B := by
    dsimp [B]
    rw [← he]
    linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 1 ≤ A := by
    have hK : (1 : ℝ) ≤ q.K := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q.K)
    dsimp [A]
    apply (le_div_iff₀ (mul_pos hε hδ)).mpr
    have hden : q.ε * q.δ ≤ 1 / 4 := by nlinarith
    nlinarith [Nat.cast_nonneg (α := ℝ) q.d]
  have heL : Real.exp (confidenceLog q) = A * B ^ q.d := by
    change Real.exp (Real.log A + q.d * Real.log B) = A * B ^ q.d
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by linarith : 0 < A), Real.exp_log hB]
  have hm := (primalMesh_valid q hε hG hx0 hbound).2.1
  calc
    ((primalMesh q).card : ℝ) ≤ (meshCardBound q : ℝ) := by exact_mod_cast hm
    _ = (2 * (Nat.ceil (q.R / coordinateScale q) + 1) + 1 : ℝ) ^ q.d := by
      simp [meshCardBound]
    _ ≤ B ^ q.d := pow_le_pow_left₀ (by positivity) hcell _
    _ ≤ A * B ^ q.d := by nlinarith [pow_pos hB q.d]
    _ = _ := heL.symm

lemma horizon_confidence_bound (L δ : ℝ) (K M : ℕ)
    (hL : 1 ≤ L) (hδ : 0 < δ) (hK : (K : ℝ) ≤ Real.exp L)
    (hM : (M : ℝ) ≤ Real.exp L) (hd : 1 / δ ≤ Real.exp L) :
    2 * K * M * (Nat.ceil (Real.exp (4 * L)) + 1 : ℝ) * Real.exp (-16 * L) ≤ δ := by
  have hE : 1 ≤ Real.exp (4 * L) := Real.one_le_exp_iff.mpr (by linarith)
  have hceil := Nat.ceil_lt_add_one (Real.exp_pos (4 * L)).le
  have hT : (Nat.ceil (Real.exp (4 * L)) + 1 : ℝ) ≤ 3 * Real.exp (4 * L) := by linarith
  have hprod : 2 * K * M * (Nat.ceil (Real.exp (4 * L)) + 1 : ℝ) * Real.exp (-16 * L) ≤
      6 * Real.exp (-10 * L) := by
    calc
      _ ≤ 2 * Real.exp L * Real.exp L * (3 * Real.exp (4 * L)) * Real.exp (-16 * L) := by
        gcongr
      _ = _ := by
        have he : Real.exp L * Real.exp L * Real.exp (4 * L) * Real.exp (-16 * L) =
            Real.exp (-10 * L) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        nlinarith [he]
  have h6 : 6 ≤ Real.exp (9 * L) := by linarith [Real.add_one_le_exp (9 * L)]
  have hsmall : 6 * Real.exp (-10 * L) ≤ Real.exp (-L) := by
    calc
      _ ≤ Real.exp (9 * L) * Real.exp (-10 * L) :=
        mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hd' : Real.exp (-L) ≤ δ := by
    have h := (div_le_iff₀ hδ).mp hd
    have he : Real.exp L * Real.exp (-L) = 1 := by rw [← Real.exp_add]; simp
    have hp := mul_le_mul_of_nonneg_right h (Real.exp_pos (-L)).le
    nlinarith [he]
  exact hprod.trans (hsmall.trans hd')

lemma inverse_gap_sum_bounds {K : ℕ} (Δ : Fin K → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hΔ : ∀ i, 0 ≤ Δ i ∧ Δ i ≤ 1) :
    (K : ℝ) ≤ ∑ i, 1 / max (Δ i) ε ^ 2 ∧
      (∑ i, 1 / max (Δ i) ε ^ 2) ≤ K / ε ^ 2 := by
  have hlo (i : Fin K) : 1 ≤ 1 / max (Δ i) ε ^ 2 := by
    have hp : 0 < max (Δ i) ε := hε.trans_le (le_max_right _ _)
    have hu : max (Δ i) ε ≤ 1 := max_le (hΔ i).2 hε1
    apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
    nlinarith
  have hhi (i : Fin K) : 1 / max (Δ i) ε ^ 2 ≤ 1 / ε ^ 2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos hε)
    exact (sq_le_sq₀ hε.le (by positivity)).mpr (le_max_right _ _)
  constructor
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlo i)
    simpa using h
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hhi i)
    simpa [div_eq_mul_inv] using h

lemma budget_le_horizon {K : ℕ} (Δ : Fin K → ℝ) (s ε L : ℝ)
    (hK : (1 : ℝ) ≤ K) (hs : 1 ≤ s) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hΔ : ∀ i, 0 ≤ Δ i ∧ Δ i ≤ 1) (hL : 1 ≤ L)
    (hscale : 512 * K * s / ε ≤ Real.exp L) :
    Nat.ceil (512 * s ^ 2 * L * ∑ i, 1 / max (Δ i) ε ^ 2) ≤
      Nat.ceil (Real.exp (4 * L)) := by
  apply Nat.ceil_mono
  have hsum := (inverse_gap_sum_bounds Δ ε hε hε1 hΔ).2
  have hcoeff : 0 ≤ 512 * s ^ 2 * K / ε ^ 2 := by positivity
  have hsq : 512 * s ^ 2 * K / ε ^ 2 ≤ (512 * K * s / ε) ^ 2 := by
    have he : (512 * K * s / ε) ^ 2 = (512 * s ^ 2 * K / ε ^ 2) * (512 * K) := by
      ring
    rw [he]
    nlinarith
  have hsq' : (512 * K * s / ε) ^ 2 ≤ Real.exp L ^ 2 :=
    (sq_le_sq₀ (by positivity) (Real.exp_pos L).le).mpr hscale
  have hLe : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hE : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr (by linarith)
  calc
    _ ≤ 512 * s ^ 2 * L * (K / ε ^ 2) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = L * (512 * s ^ 2 * K / ε ^ 2) := by ring
    _ ≤ L * Real.exp L ^ 2 := mul_le_mul_of_nonneg_left (hsq.trans hsq') (by linarith)
    _ ≤ Real.exp L * Real.exp L ^ 2 := mul_le_mul_of_nonneg_right hLe (sq_nonneg _)
    _ ≤ Real.exp L ^ 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hE) (pow_nonneg (Real.exp_pos L).le 3)]
    _ = Real.exp (4 * L) := by rw [← Real.exp_nat_mul]; norm_num

lemma budget_dominates_counts {K : ℕ} (Δ : Fin K → ℝ) (s ε L : ℝ)
    (hK : (1 : ℝ) ≤ K) (hs : 1 ≤ s) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hΔ : ∀ i, 0 ≤ Δ i ∧ Δ i ≤ 1) (hL : 1 ≤ L) :
    (∑ i, (128 * s ^ 2 * L / max (Δ i) ε ^ 2 + 1)) <
      (Nat.ceil (512 * s ^ 2 * L * ∑ i, 1 / max (Δ i) ε ^ 2) : ℝ) := by
  let S := ∑ i, 1 / max (Δ i) ε ^ 2
  have hS : (K : ℝ) ≤ S := (inverse_gap_sum_bounds Δ ε hε hε1 hΔ).1
  have hSpos : 0 < S := by linarith
  have hs2 : 1 ≤ s ^ 2 := by nlinarith
  have hsL : 1 ≤ s ^ 2 * L := by nlinarith
  have hmass : (K : ℝ) ≤ s ^ 2 * L * S := by nlinarith
  have hsum : (∑ i, (128 * s ^ 2 * L / max (Δ i) ε ^ 2 + 1)) =
      128 * s ^ 2 * L * S + K := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    simp only [S, div_eq_mul_inv, one_mul, Finset.mul_sum]
  have hstrict : 128 * s ^ 2 * L * S + K < 512 * s ^ 2 * L * S := by
    have hp : 0 < s ^ 2 * L * S := by positivity
    nlinarith
  rw [hsum]
  exact hstrict.trans_le (Nat.le_ceil _)

end LongTails.Proofs.SparseGroupBudget
