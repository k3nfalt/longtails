import LongTails.Proofs.FiniteSumNondualLowerComponents

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.SmoothConvexFiniteChain

open FiniteSumNondualLowerComponents FiniteSumNondualLowerGeometry

lemma hiddenPoint_norm_sq {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (a : ℝ) :
    ‖hiddenPoint π a‖ ^ 2 = ((k : ℝ) + 1) * a ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i : Fin d, (if i ∈ Finset.univ.map π then a else 0) ^ 2) = _
  simp only [ite_pow, zero_pow (by decide : 2 ≠ 0)]
  rw [Finset.sum_ite_mem]
  simp

lemma chain_upper {d k : ℕ} (δ a : ℝ) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    hardComponent 1 δ a π (fun _ => (0 : Fin 1)) 0 x ≤ ‖x‖ ^ 2 + a ^ 2 / 4 := by
  have he := hardComponent_sum 1 δ a π (fun _ => (0 : Fin 1)) x
  simp only [Fin.sum_univ_one] at he
  rw [he]
  have hz (t : ℝ) : deadZone δ t ^ 2 ≤ t ^ 2 := by
    have h : deadZone δ t ≤ |t| := max_le (by linarith) (abs_nonneg t)
    have hh := pow_le_pow_left₀ (deadZone_nonneg δ t) h 2
    simpa only [sq_abs] using hh
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) =>
    hz (x (π j.castSucc) - x (π j.succ)))
  have hc := chain_difference_energy_fin k (fun j => x (π j))
  have hp := coordinateMap_norm π x
  have hp' : (∑ j : Fin (k + 1), x (π j) ^ 2) ≤ ‖x‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg (coordinateMap π x)) hp 2
    rw [EuclideanSpace.real_norm_sq_eq] at hh
    exact hh
  have hsum : 0 ≤ ∑ j : Fin k, (x (π j.castSucc) - x (π j.succ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [sq_nonneg (x (π 0) + a)]

lemma chain_gradient_hiddenPoint {d k : ℕ} (δ a : ℝ) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) :
    hardGradient 1 δ a π (fun _ => (0 : Fin 1)) 0 (hiddenPoint π a) = 0 := by
  have hz : separableSlope
      (fun j : Fin (k + 1) => maskedSlope true
        (Fin.cases (0 : ℝ) (fun _ => δ) j) (Fin.cases a (fun _ => 0) j))
      (selectedChain π (hiddenPoint π a)) = 0 := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [separableSlope, maskedSlope, selectedChain_apply_zero, hiddenPoint_apply,
        softThreshold]
    · simp [separableSlope, maskedSlope, selectedChain_apply_succ, hiddenPoint_apply,
        softThreshold, max_eq_right (neg_nonpos.mpr hδ)]
  simp only [hardGradient, Fin.isValue, decide_true, hz, map_zero, smul_zero]

lemma chain_gradient_bound {d k : ℕ} (δ a R : ℝ) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (hR : ‖hiddenPoint π a‖ ≤ R)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖hardGradient 1 δ a π (fun _ => (0 : Fin 1)) 0 x‖ ≤ ‖x‖ + R := by
  have h := hardGradient_lipschitz 1 δ a (by norm_num) hδ π
    (fun _ => (0 : Fin 1)) 0 x (hiddenPoint π a)
  rw [chain_gradient_hiddenPoint δ a hδ π, sub_zero, one_mul] at h
  exact h.trans ((norm_sub_le _ _).trans (add_le_add le_rfl hR))

end LongTails.Proofs.SmoothConvexFiniteChain
