import LongTails.Proofs.SampleLossFrame
import LongTails.Proofs.InterpolatedFiniteSumHiding

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace BigOperators
open LongTails.Setups.NonnegativeSmoothSampleLossEuclidean
open LongTails.Proofs.SampleLossFrame LongTails.Proofs.SampleLossRadial
open LongTails.Proofs.SoftRadialProjection LongTails.Proofs.InterpolatedFiniteSumHiding

namespace LongTails.Proofs.SampleLossHiding

variable {n m d : ℕ}

noncomputable def slice (y : Block m d) (i : Fin m) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun t => y (i,t))

lemma slice_small (y : Block m d) (i : Fin m) : ‖slice y i‖ ≤ ‖y‖ := by
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin m => ∑ t : Fin d, y (j,t)^2)
    (fun j _ => Finset.sum_nonneg fun t _ => sq_nonneg _) (Finset.mem_univ i)
  rw [← Real.sqrt_sq (norm_nonneg (slice y i)), ← Real.sqrt_sq (norm_nonneg y)]
  apply Real.sqrt_le_sqrt
  simpa [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, slice] using h

noncomputable def large (t : ℝ) (y : Block m d) (i : Fin m) : Finset (Fin d) :=
  SmoothConvexFiniteHiding.largeSet 1 t (slice y i)

lemma large_size {t : ℝ} (ht : 0 < t) (y : Block m d) (i : Fin m) :
    ((large t y i).card : ℝ) ≤ 1 / t^2 := by
  simpa [large] using SmoothConvexFiniteHiding.largeSet_bound 1 t zero_le_one ht (slice y i)

lemma large_out {t : ℝ} {y : Block m d} (hy : ‖y‖ ≤ 1) {i : Fin m} {a : Fin d}
    (ha : a ∉ large t y i) : |y (i,a)| ≤ t :=
  SmoothConvexFiniteHiding.not_largeSet_small 1 t _ ((slice_small _ _).trans hy) _ ha

lemma partial_norm (π : Table n m d) (j : Fin n) (s : Finset (Fin m)) :
    ‖∑ i ∈ s, basis π j i‖ = Real.sqrt s.card := by
  have h : ⟪(∑ i ∈ s, basis π j i), (∑ i ∈ s, basis π j i)⟫ = (s.card:ℝ) := by
    simp only [sum_inner, inner_sum, basis_inner π j.isLt]
    simp
  rw [real_inner_self_eq_norm_sq] at h
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

lemma hidden_alignment (π : Table n m d) (j : Fin n) (s : Finset (Fin m))
    (hm : 0 < m) (y : Block m d) (hy : ‖y‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t)
    (hout : ∀ i ∉ s, π (j,i) ∉ large t y i) :
    |⟪direction π j, y⟫| ≤ (Real.sqrt s.card + (m:ℝ) * t) / Real.sqrt m := by
  classical
  have hs := abs_real_inner_le_norm (∑ i ∈ s, basis π j i) y
  rw [partial_norm, sum_inner] at hs
  have hs' := hs.trans (mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _))
  rw [mul_one] at hs'
  have hc : |∑ i ∈ sᶜ, ⟪basis π j i, y⟫| ≤ (m:ℝ)*t := by
    calc
      _ ≤ ∑ i ∈ sᶜ, |⟪basis π j i,y⟫| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ sᶜ, t := Finset.sum_le_sum fun i hi => by
        simpa [basis,j.isLt,EuclideanSpace.inner_single_left] using
          large_out hy (hout i (Finset.mem_compl.mp hi))
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show (sᶜ : Finset (Fin m)).card ≤ m by simpa using Finset.card_le_univ (sᶜ : Finset (Fin m)))) ht
  have hadd := abs_add_le (∑ i ∈ s, ⟪basis π j i,y⟫) (∑ i ∈ sᶜ, ⟪basis π j i,y⟫)
  rw [Finset.sum_add_sum_compl] at hadd
  have h := hadd.trans (add_le_add hs' hc)
  have hr := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)
  simp only [direction,real_inner_smul_left,abs_mul,abs_inv,abs_of_pos hr, sum_inner]
  simpa only [div_eq_inv_mul] using mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hr.le)

lemma observation_bound {J : Type} [Fintype J] (seen : J → Finset (Fin n × Fin m))
    (y : J → Table n m d → Fin n → Block m d)
    (stable : ∀ a π ρ, (∀ l ∈ seen a, π l = ρ l) → y a π = y a ρ)
    {t : ℝ} (ht : 0 < t) :
    (d:ℝ) * (∑ π : Table n m d, if ∃ a : J, ∃ l : Fin n × Fin m,
      l ∉ seen a ∧ π l ∈ large t (y a π l.1) l.2 then (1:ℝ) else 0) ≤
      Fintype.card J * (n:ℝ) * m * (1/t^2) * Fintype.card (Table n m d) := by
  classical
  let bad (z : J × (Fin n × Fin m)) (π : Table n m d) :=
    z.2 ∉ seen z.1 ∧ π z.2 ∈ large t (y z.1 π z.2.1) z.2.2
  have h (a : J) (l : Fin n × Fin m) :=
    unseen_coordinate_bound (fun _ : Table n m d => seen a) (fun π => large t (y a π l.1) l.2)
      (1/t^2) (by positivity) (fun π => large_size ht _ _)
      (fun π ρ eq => ⟨rfl, by rw [stable a π ρ eq]⟩) l
  have hh := finite_union_bound (d:ℝ) (Nat.cast_nonneg d) bad
    (fun _ => (1/t^2) * (Fintype.card (Table n m d) : ℝ)) (fun z => by
      have hh := h z.1 z.2
      simp only [Fintype.card_fin] at hh
      apply le_trans (le_of_eq ?_) hh
      congr 1
      apply Finset.sum_congr rfl
      intro π _
      by_cases hz : z.2 ∉ seen z.1 ∧ π z.2 ∈ large t (y z.1 π z.2.1) z.2.2 <;> simp [bad,hz])
  simpa [bad, Prod.exists, Fintype.card_prod, mul_assoc, mul_left_comm, mul_comm] using hh

end LongTails.Proofs.SampleLossHiding
