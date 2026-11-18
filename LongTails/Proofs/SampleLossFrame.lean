import LongTails.Setups.NonnegativeSmoothSampleLossEuclidean
import LongTails.Proofs.SampleLossFrontier

open scoped RealInnerProductSpace BigOperators
open LongTails.Setups.NonnegativeSmoothSampleLossEuclidean
open LongTails.Proofs.SampleLossRadial LongTails.Proofs.SampleLossChain
open LongTails.Proofs.SampleLossMixture

namespace LongTails.Proofs.SampleLossFrame

variable {n m d : ℕ}

abbrev Table (n m d : ℕ) := Fin n × Fin m → Fin d

noncomputable def proj (j : ℕ) : Space n m d →L[ℝ] Block m d :=
  if h : j < n then PiLp.proj 2 _ ⟨j,h⟩ else 0

noncomputable def basis (π : Table n m d) (j : ℕ) (i : Fin m) : Block m d :=
  if h : j < n then EuclideanSpace.single (i, π (⟨j,h⟩,i)) 1 else 0

noncomputable def direction (π : Table n m d) (j : ℕ) : Block m d :=
  (Real.sqrt m)⁻¹ • ∑ i : Fin m, basis π j i

noncomputable def row (π : Table n m d) (i : Fin m) (j : ℕ) : Block m d :=
  Real.sqrt m • basis π j i

noncomputable def payload (π : Table n m d) (i : Fin m) (j : ℕ) : Block m d :=
  (1 + Real.sqrt m)⁻¹ • (direction π j - row π i j)

lemma basis_inner (π : Table n m d) {j : ℕ} (hj : j < n) (i l : Fin m) :
    ⟪basis π j i, basis π j l⟫ = if i=l then 1 else 0 := by
  by_cases h : i=l
  · subst l
    simp [basis,hj]
  · simp [basis,hj, EuclideanSpace.inner_single_left, h]

lemma direction_norm (π : Table n m d) {j : ℕ} (hj : j < n) (hm : 0 < m) :
    ‖direction π j‖ = 1 := by
  have hh : ⟪(∑ i : Fin m, basis π j i), (∑ i : Fin m, basis π j i)⟫ = (m:ℝ) := by
    simp only [sum_inner, inner_sum, basis_inner π hj]
    simp
  rw [real_inner_self_eq_norm_sq] at hh
  have hs : ‖∑ i : Fin m, basis π j i‖ = Real.sqrt m := by
    rw [← hh, Real.sqrt_sq (norm_nonneg _)]
  simp [direction, norm_smul, hs, abs_of_nonneg (Real.sqrt_nonneg _), (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)).ne']

lemma direction_le (π : Table n m d) (hm : 0 < m) (j : ℕ) : ‖direction π j‖ ≤ 1 := by
  by_cases hj : j < n
  · exact (direction_norm π hj hm).le
  · simp [direction,basis,hj]

lemma row_le (π : Table n m d) (i : Fin m) (j : ℕ) : ‖row π i j‖ ≤ Real.sqrt m := by
  by_cases hj : j < n
  · simp [row,basis,hj,PiLp.norm_single,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  · simp [row,basis,hj]

lemma payload_le (π : Table n m d) (hm : 0 < m) (i : Fin m) (j : ℕ) : ‖payload π i j‖ ≤ 1 := by
  have h := (norm_sub_le (direction π j) (row π i j)).trans (add_le_add (direction_le π hm j) (row_le π i j))
  have hp : 0 < 1 + Real.sqrt m := by positivity
  simp only [payload,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hp]
  rw [← div_eq_inv_mul, div_le_one hp]
  exact h

lemma payload_signal (π : Table n m d) (i : Fin m) (j : ℕ) (x : Space n m d) :
    (1+Real.sqrt m) * signal proj (payload π i) j x =
      signal proj (direction π) j x - alignment (row π i j) (proj j x) := by
  have hp : 0 < 1 + Real.sqrt m := by positivity
  simp [signal,alignment,payload,real_inner_smul_left,inner_sub_left,hp.ne']

lemma proj_energy (v : Space n m d) :
    ∑ j ∈ Finset.range n, ‖(proj j) v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [← Fin.sum_univ_eq_sum_range, PiLp.norm_sq_eq_of_L2]
  simp [proj]

lemma payload_centered (π : Table n m d) (hm : 0 < m) (j : ℕ) :
    ∑ i : Fin m, payload π i j = 0 := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)
  have he : (m:ℝ) * (Real.sqrt m)⁻¹ = Real.sqrt m := by
    rw [← div_eq_mul_inv, div_eq_iff hs.ne']
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg m)]
  simp only [payload, ← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, direction, row, ← Nat.cast_smul_eq_nsmul ℝ m, smul_smul, mul_comm (Real.sqrt m)⁻¹, he, sub_self, smul_zero]

lemma perturbation_centered (π : Table n m d) (hm : 0 < m) (x : Space n m d) (t : ℕ) :
    ∑ i : Fin m, perturbation proj (direction π) (payload π i) t x = 0 := by
  induction t with
  | zero => simp [perturbation,mixture]
  | succ t ih =>
    change ∑ i : Fin m, ((1 - incoming proj (direction π) t x) *
      perturbation proj (direction π) (payload π i) t x +
      incoming proj (direction π) t x * signal proj (payload π i) t x) = 0
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ih]
    simp [signal,alignment,← sum_inner,payload_centered π hm]

end LongTails.Proofs.SampleLossFrame
