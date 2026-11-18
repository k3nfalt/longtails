import LongTails.Proofs.RelativeHessianJetBounds

namespace LongTails.Proofs.RelativeHessianChainBounds

open scoped RealInnerProductSpace BigOperators
open RelativeHessianArctan RelativeHessianGate RelativeHessianGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma value_bound {m : ℕ} (v : Fin (m + 1) → E) (x : E) : |chain v x| ≤ 4 * (m + 1 : ℕ) := by
  have he (i : Fin m) : |edge (v i.castSucc) (v i.succ) x| ≤ Real.pi := by
    rw [edge_eq, abs_le]
    exact RelativeHessianChain.link_bounds _ _
  have hp : |RidgeJets.value profile (v 0) x| ≤ Real.pi := by
    rw [RidgeJets.value, abs_of_pos (profile_bounds _).1]
    exact (profile_bounds _).2.le
  have hs : |∑ i : Fin m, edge (v i.castSucc) (v i.succ) x| ≤ (m : ℝ) * Real.pi := by
    calc
      _ ≤ ∑ i : Fin m, |edge (v i.castSucc) (v i.succ) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin m, Real.pi := Finset.sum_le_sum (fun i _ => he i)
      _ = _ := by simp
  unfold chain
  have ht := abs_add_le (-RidgeJets.value profile (v 0) x)
    (∑ i : Fin m, edge (v i.castSucc) (v i.succ) x)
  rw [abs_neg] at ht
  have hm := mul_le_mul_of_nonneg_left Real.pi_lt_four.le (show (0 : ℝ) ≤ m by positivity)
  push_cast
  linarith [Real.pi_lt_four]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma value_zero {m : ℕ} (v : Fin (m + 1) → E) : chain v 0 = -Real.pi / 2 := by
  have hg := (gate_flat (by norm_num : (0 : ℝ) ≤ 1 / 10)).1
  simp [chain, edge, RidgeJets.value, profile, hg]
  ring

omit [FiniteDimensional ℝ E] in
lemma gate_bounds (a x : E) (ha : ‖a‖ ≤ 1) :
    |RidgeJets.value gate a x| ≤ 2 ^ 24 ∧ ‖gradient (RidgeJets.value gate a) x‖ ≤ 2 ^ 24 ∧
    ‖fderiv ℝ (gradient (RidgeJets.value gate a)) x‖ ≤ 2 ^ 24 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [RidgeJets.value, abs_of_nonneg (RelativeHessianGate.gate_bounds _).1]
    exact (RelativeHessianGate.gate_bounds _).2.trans (by norm_num)
  · rw [RidgeJets.gradient_eq gate_hasDerivAt, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul (gate_jet_bounds _).1 ha (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  · exact RidgeJets.hessian_norm gate_contDiff gate_hasDerivAt gateSlope_hasDerivAt a x
      (by positivity) ha (gate_jet_bounds _).2.1

omit [FiniteDimensional ℝ E] in
lemma profile_bounds (a x : E) (ha : ‖a‖ ≤ 1) :
    |RidgeJets.value profile a x| ≤ 2 ^ 24 ∧ ‖gradient (RidgeJets.value profile a) x‖ ≤ 2 ^ 24 ∧
    ‖fderiv ℝ (gradient (RidgeJets.value profile a)) x‖ ≤ 2 ^ 24 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [RidgeJets.value, abs_of_pos (RelativeHessianArctan.profile_bounds _).1]
    exact (RelativeHessianArctan.profile_bounds _).2.le.trans (Real.pi_lt_four.le.trans (by norm_num))
  · rw [RidgeJets.gradient_eq profile_derivative, norm_smul, Real.norm_eq_abs]
    have h := mul_le_mul (profile_jet_bounds ⟪a, x⟫).1 ha (norm_nonneg a) (by norm_num : (0 : ℝ) ≤ 1)
    exact h.trans (by norm_num)
  · exact (RidgeJets.hessian_norm profile_contDiff profile_derivative density_derivative a x
      (by norm_num : (0 : ℝ) ≤ 2) ha (profile_jet_bounds _).2.1).trans (by norm_num)

lemma product_bounds (a b x : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖gradient (fun y => RidgeJets.value gate a y * RidgeJets.value profile b y) x‖ ≤ 2 ^ 49 ∧
    ‖fderiv ℝ (gradient (fun y => RidgeJets.value gate a y * RidgeJets.value profile b y)) x‖ ≤ 2 ^ 50 := by
  have hg := gate_bounds a x ha
  have hp := profile_bounds b x hb
  constructor
  · convert ProductCompositionJets.product_gradient_bound (RidgeJets.smooth gate_contDiff a)
      (RidgeJets.smooth profile_contDiff b) x (by norm_num : (0 : ℝ) ≤ 2 ^ 24)
      ⟨hg.1, hp.1⟩ ⟨hg.2.1, hp.2.1⟩ using 1
    norm_num
  · convert ProductCompositionJets.product_hessian_bound (RidgeJets.smooth gate_contDiff a)
      (RidgeJets.smooth profile_contDiff b) x (by norm_num : (0 : ℝ) ≤ 2 ^ 24)
      ⟨hg.1, hp.1⟩ ⟨hg.2.1, hp.2.1⟩ ⟨hg.2.2, hp.2.2⟩ using 1
    norm_num

lemma edge_bounds (a b x : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖gradient (edge a b) x‖ ≤ 2 ^ 50 ∧ ‖fderiv ℝ (gradient (edge a b)) x‖ ≤ 2 ^ 51 := by
  have hp := product_bounds a b x ha hb
  have hn := product_bounds (-a) (-b) x (by simpa using ha) (by simpa using hb)
  have hf := (RidgeJets.smooth gate_contDiff (-a)).mul (RidgeJets.smooth profile_contDiff (-b))
  have hg := (RidgeJets.smooth gate_contDiff a).mul (RidgeJets.smooth profile_contDiff b)
  unfold edge
  rw [ThirdOrderAffineCalculus.difference_gradient hf hg, ThirdOrderAffineCalculus.difference_hessian hf hg]
  exact ⟨(norm_sub_le _ _).trans (by linarith [hn.1, hp.1]),
    (norm_sub_le _ _).trans (by linarith [hn.2, hp.2])⟩

lemma gradient_bound {m : ℕ} (v : Fin (m + 1) → E) (hn : ∀ i, ‖v i‖ ≤ 1) (x : E) :
    ‖gradient (chain v) x‖ ≤ 2 ^ 52 * (m + 1 : ℕ) := by
  have he : gradient (chain v) x = -density ⟪v 0, x⟫ • v 0 +
      ∑ i : Fin m, gradient (edge (v i.castSucc) (v i.succ)) x := by
    rw [chain_gradient]
    simp_rw [edge_gradient]
  have ha : ‖-density ⟪v 0, x⟫ • v 0‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    exact (mul_le_mul (profile_jet_bounds _).1 (hn 0) (norm_nonneg _) (by norm_num)).trans_eq (mul_one _)
  have hs : ‖∑ i : Fin m, gradient (edge (v i.castSucc) (v i.succ)) x‖ ≤ (m : ℝ) * 2 ^ 50 := by
    calc
      _ ≤ ∑ i : Fin m, ‖gradient (edge (v i.castSucc) (v i.succ)) x‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin m, (2 : ℝ) ^ 50 := Finset.sum_le_sum (fun i _ => (edge_bounds _ _ _ (hn _) (hn _)).1)
      _ = _ := by simp
  rw [he]
  exact (norm_add_le _ _).trans (by push_cast; nlinarith [ha, hs, Nat.cast_nonneg (α := ℝ) m])

lemma hessian_bound {m : ℕ} (v : Fin (m + 1) → E) (hn : ∀ i, ‖v i‖ ≤ 1) (x : E) :
    ‖fderiv ℝ (gradient (chain v)) x‖ ≤ 2 ^ 52 * (m + 1 : ℕ) := by
  have hf := RidgeJets.smooth profile_contDiff (v 0)
  have hg : ContDiff ℝ 3 (fun y => ∑ i : Fin m, edge (v i.castSucc) (v i.succ) y) :=
    ContDiff.sum (fun i _ => edge_smooth _ _)
  have he : chain v = fun y => (-1 : ℝ) * RidgeJets.value profile (v 0) y +
      1 * (∑ i : Fin m, edge (v i.castSucc) (v i.succ) y) := by
    funext y
    simp [chain]
  have ha := RidgeJets.hessian_norm profile_contDiff profile_derivative density_derivative
    (v 0) x (by norm_num : (0 : ℝ) ≤ 2) (hn 0) (profile_jet_bounds _).2.1
  have hs : ‖∑ i : Fin m, fderiv ℝ (gradient (edge (v i.castSucc) (v i.succ))) x‖ ≤
      (m : ℝ) * 2 ^ 51 := by
    calc
      _ ≤ ∑ i : Fin m, ‖fderiv ℝ (gradient (edge (v i.castSucc) (v i.succ))) x‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin m, (2 : ℝ) ^ 51 := Finset.sum_le_sum (fun i _ => (edge_bounds _ _ _ (hn _) (hn _)).2)
      _ = _ := by simp
  rw [he, ThirdOrderAffineCalculus.combination_hessian hf hg,
    ThirdOrderAffineCalculus.sum_hessian Finset.univ (fun i _ => edge_smooth _ _)]
  simp only [neg_one_smul, one_smul]
  have ht := norm_add_le (-fderiv ℝ (gradient (RidgeJets.value profile (v 0))) x)
    (∑ i : Fin m, fderiv ℝ (gradient (edge (v i.castSucc) (v i.succ))) x)
  rw [norm_neg] at ht
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

end LongTails.Proofs.RelativeHessianChainBounds
