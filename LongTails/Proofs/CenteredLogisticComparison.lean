import LongTails.Proofs.CenteredLogisticPairs
import LongTails.Proofs.ClusteredConvolutionalPerceptronInstances

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CenteredLogisticComparison

open LongTails.Setups.CenteredLogisticClassification
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open CenteredLogisticGeometry CenteredLogisticPairs

variable {d : ℕ} {n : ℕ+}

noncomputable def offset (e : Features d) (u : Fin n → Features d) (μ : ℝ) (j : Fin n) :
    Features d := μ • (u j - (1 / 2 : ℝ) • e)

noncomputable def samples (e : Features d) (u : Fin n → Features d) (μ : ℝ) :
    Data (params d n) := pairedData (1 + μ / 2) e (offset e u μ)

lemma dup_apply {α β : Type*} (f : Fin n → α) (g : α → β) (i : Fin ((n : ℕ) + n)) :
    duplicate (fun j => g (f j)) i = g (duplicate f i) := by
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j <;> simp only [duplicate, at_pair, Sum.elim_inl, Sum.elim_inr]

noncomputable def instanceGeometry (e : Features d) (u : Fin n → Features d) {μ κ : ℝ}
    (he : ‖e‖ = 1) (hc : ∀ j, ⟪e, u j⟫ = 0) (hu : ∀ j, ‖u j‖ ≤ 2 / 3)
    (hκ : ∀ i j, κ ≤ ⟪u i, u j⟫) (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 64)
    (hsmall : 8 * (9 + 17 * ‖LongTails.Setups.TwoSampleQuadraticPerceptron.shift e - e‖) * μ < κ) : Geometry (params d n) (samples e u μ) := by
  apply pairGeometry (B := 1 + μ / 2) (δ := 2 * μ) (offset e u μ) he
    (by positivity) (by positivity) (by linarith)
  · intro j
    have h := norm_sub_le (u j) ((1 / 2 : ℝ) • e)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), he] at h
    rw [offset, norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
    exact mul_comm 2 μ ▸ (mul_le_mul_of_nonneg_left (by linarith [hu j] :
      ‖u j - (1 / 2 : ℝ) • e‖ ≤ 2) hμ.le)
  · dsimp only
    intro i
    let v := 𝔼 j, duplicate u j
    have hv : ⟪e,v⟫ = 0 := by
      rw [show v = 𝔼 j, duplicate u j from rfl, ← mean_inner]
      exact Finset.expect_eq_zero (fun j _ => bounds_pair (P := fun x => ⟪e,x⟫ = 0) u hc j)
    have hdup (j : Fin ((n : ℕ) + n)) : duplicate (offset e u μ) j =
        μ • (duplicate u j - (1 / 2 : ℝ) • e) := dup_apply u (fun x => μ • (x - (1 / 2 : ℝ) • e)) j
    have hm : (𝔼 j, duplicate (offset e u μ) j) = μ • (v - (1 / 2 : ℝ) • e) := by
      simp_rw [hdup, ← Finset.smul_expect, Finset.expect_sub_distrib, Fintype.expect_const]
      rfl
    have ht : μ • (v - (1 / 2 : ℝ) • e) -
        ⟪e, μ • (v - (1 / 2 : ℝ) • e)⟫ • e = μ • v := by
      simp only [real_inner_smul_right, inner_sub_right, hv, real_inner_self_eq_norm_sq,
        he, one_pow, mul_one]
      module
    have hik : κ ≤ ⟪duplicate u i,v⟫ := by
      change κ ≤ ⟪duplicate u i, 𝔼 j, duplicate u j⟫
      rw [← mean_inner]
      exact Finset.le_expect Finset.univ_nonempty (fun j _ =>
        bounds_pair (P := fun x => κ ≤ ⟪x, duplicate u j⟫) u
          (fun a => bounds_pair (P := fun x => κ ≤ ⟪u a,x⟫) u (hκ a) j) i)
    rw [hm, ht, hdup, real_inner_smul_left, real_inner_smul_right, inner_sub_left,
      real_inner_smul_left, hv, mul_zero, sub_zero]
    have hkpos : 0 < κ := lt_trans (by positivity) hsmall
    have h1 := mul_lt_mul_of_pos_right hsmall (sq_pos_of_pos hμ)
    have h2 := mul_le_mul_of_nonneg_right hik (sq_nonneg μ)
    have h3 := mul_nonneg (div_nonneg hμ.le (by norm_num : (0 : ℝ) ≤ 2))
      (mul_nonneg hμ.le (mul_nonneg hμ.le (le_trans (by linarith) hik)))
    nlinarith

noncomputable def linearFamily (e : Features d) (u : Fin n → Features d)
    (he : ‖e‖ = 1) (hc : ∀ j, ⟪e, u j⟫ = 0) (hu : ∀ j, ‖u j‖ ≤ 2 / 3) :
    TwoSidedPerceptronLinearComparison.Family (Features d) n where
  e := e
  u := Sum.elim u u
  e_unit := he
  centered := by intro i; cases i <;> apply hc
  u_norm := by
    intro i
    have h : (2 / 3 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by
      rw [← one_div, le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_nonneg (Real.sqrt 2 - 3 / 2)]
    cases i <;> exact (hu _).trans h

lemma matched_sample (e : Features d) (u : Fin n → Features d) (μ : ℝ)
    (he : ‖e‖ = 1) (hc : ∀ j, ⟪e, u j⟫ = 0) (hu : ∀ j, ‖u j‖ ≤ 2 / 3)
    (j : Fin n ⊕ Fin n) :
    samples e u μ (finSumFinEquiv j) =
      TwoSidedPerceptronLinearComparison.sample (linearFamily e u he hc hu) μ j := by
  cases j <;> simp only [samples, pairedData, label, duplicate, at_pair, Sum.elim_inl,
    Sum.elim_inr, offset, TwoSidedPerceptronLinearComparison.sample,
    TwoSidedPerceptronLinearComparison.weight, linearFamily] <;> module

lemma batch_delay (e : Features d) (u : Fin n → Features d) {μ ϕ : ℝ}
    (he : ‖e‖ = 1) (hc : ∀ j, ⟪e, u j⟫ = 0) (hu : ∀ j, ‖u j‖ ≤ 2 / 3)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 4) (hϕ : 0 < ϕ) (t : ℕ) (ht : (t : ℝ) * μ ≤ 1) :
    let F := linearFamily e u he hc hu
    ∃ i, ⟪samples e u μ i, (TwoSidedPerceptronLinearComparison.batchStep F μ ϕ)^[t] 0⟫ ≤ 0 := by
  obtain ⟨j,h⟩ := TwoSidedPerceptronLinearComparison.batch_not_separated
    (linearFamily e u he hc hu) n.pos hμ hμ1 hϕ t ht
  exact ⟨finSumFinEquiv j, by rwa [matched_sample e u μ he hc hu]⟩

end LongTails.Proofs.CenteredLogisticComparison
