import LongTails.Proofs.RelativeHessianGeometry
import Mathlib.Analysis.Real.Pi.Bounds

namespace LongTails.Proofs.RelativeHessianJetBounds

open scoped RealInnerProductSpace BigOperators
open RelativeHessianArctan RelativeHessianGate RelativeHessianGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def energy (a b u : E) : ℝ := |⟪a, u⟫| + |⟪b, u⟫|

lemma product_bound (a b x u v : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ (gradient (fun y =>
      RidgeJets.value gate a y * RidgeJets.value profile b y))) x u v‖ ≤
      2 ^ 51 * energy a b u * energy a b v := by
  have hU : 0 ≤ energy a b u := by unfold energy; positivity
  have hV : 0 ≤ energy a b v := by unfold energy; positivity
  have hau : |⟪a, u⟫| ≤ energy a b u := le_add_of_nonneg_right (abs_nonneg _)
  have hav : |⟪a, v⟫| ≤ energy a b v := le_add_of_nonneg_right (abs_nonneg _)
  have hbu : |⟪b, u⟫| ≤ energy a b u := le_add_of_nonneg_left (abs_nonneg _)
  have hbv : |⟪b, v⟫| ≤ energy a b v := le_add_of_nonneg_left (abs_nonneg _)
  have hgate : |gate ⟪a, x⟫| ≤ (2 : ℝ) ^ 24 := by
    rw [abs_of_nonneg (gate_bounds _).1]
    exact (gate_bounds _).2.trans (by norm_num)
  have hp : |profile ⟪b, x⟫| ≤ (2 : ℝ) ^ 24 := by
    rw [abs_of_pos (profile_bounds _).1]
    exact (profile_bounds _).2.le.trans ((Real.pi_lt_four).le.trans (by norm_num))
  have hg := RidgeJets.jet_bounds gate_contDiff gate_hasDerivAt gateSlope_hasDerivAt
    gateCurvature_hasDerivAt a x u v (by norm_num : (0 : ℝ) ≤ 2 ^ 24) hU hV ha hau hav
    hgate (gate_jet_bounds _).1 (gate_jet_bounds _).2.1 (gate_jet_bounds _).2.2
  have hpj := RidgeJets.jet_bounds profile_contDiff profile_derivative density_derivative
    densitySlope_derivative b x u v (by norm_num : (0 : ℝ) ≤ 2 ^ 24) hU hV hb hbu hbv
    hp ((profile_jet_bounds _).1.trans (by norm_num))
    ((profile_jet_bounds _).2.1.trans (by norm_num))
    ((profile_jet_bounds _).2.2.trans (by norm_num))
  have h := ProductCompositionJets.product_third_bound (RidgeJets.smooth gate_contDiff a)
    (RidgeJets.smooth profile_contDiff b) x u v (by norm_num : (0 : ℝ) ≤ 2 ^ 24) hU hV
    ⟨hg.1, hpj.1⟩ ⟨hg.2.1, hpj.2.1⟩ ⟨hg.2.2.1, hpj.2.2.1⟩
    ⟨hg.2.2.2.1, hpj.2.2.2.1⟩ ⟨hg.2.2.2.2.1, hpj.2.2.2.2.1⟩
    ⟨hg.2.2.2.2.2.1, hpj.2.2.2.2.2.1⟩
    ⟨hg.2.2.2.2.2.2.1, hpj.2.2.2.2.2.2.1⟩
    ⟨hg.2.2.2.2.2.2.2, hpj.2.2.2.2.2.2.2⟩
  convert h using 1
  norm_num

lemma edge_bound (a b x u v : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ (gradient (edge a b))) x u v‖ ≤
      2 ^ 52 * energy a b u * energy a b v := by
  have hp := product_bound a b x u v ha hb
  have hn := product_bound (-a) (-b) x u v (by simpa using ha) (by simpa using hb)
  simp only [energy, inner_neg_left, abs_neg] at hp hn ⊢
  unfold edge
  rw [ThirdOrderAffineCalculus.difference_third
    ((RidgeJets.smooth gate_contDiff (-a)).mul (RidgeJets.smooth profile_contDiff (-b)))
    ((RidgeJets.smooth gate_contDiff a).mul (RidgeJets.smooth profile_contDiff b))]
  simp only [sub_apply]
  exact (norm_sub_le _ _).trans (by linarith)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma energy_square (a b u : E) :
    energy a b u ^ 2 ≤ 2 * (⟪a, u⟫ ^ 2 + ⟪b, u⟫ ^ 2) := by
  unfold energy
  nlinarith [sq_nonneg (|⟪a, u⟫| - |⟪b, u⟫|), sq_abs ⟪a, u⟫, sq_abs ⟪b, u⟫]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma chain_energy {m : ℕ} (v : Fin (m + 1) → E)
    (hv : ∀ u, ∑ i, ⟪v i, u⟫ ^ 2 ≤ ‖u‖ ^ 2) (u : E) :
    ∑ i : Fin m, energy (v i.castSucc) (v i.succ) u ^ 2 ≤ 4 * ‖u‖ ^ 2 := by
  calc
    _ ≤ ∑ i : Fin m, 2 * (⟪v i.castSucc, u⟫ ^ 2 + ⟪v i.succ, u⟫ ^ 2) :=
      Finset.sum_le_sum (fun i _ => energy_square _ _ _)
    _ = 2 * ∑ i : Fin m, (⟪v i.castSucc, u⟫ ^ 2 + ⟪v i.succ, u⟫ ^ 2) := by rw [Finset.mul_sum]
    _ ≤ 2 * (2 * ∑ i : Fin (m + 1), ⟪v i, u⟫ ^ 2) :=
      mul_le_mul_of_nonneg_left (SparseTensorBounds.pair_energy m (fun i => ⟪v i, u⟫)) (by norm_num)
    _ ≤ 4 * ‖u‖ ^ 2 := by nlinarith [hv u]

lemma edge_sum_bound {m : ℕ} (v : Fin (m + 1) → E)
    (hn : ∀ i, ‖v i‖ ≤ 1) (hv : ∀ u, ∑ i, ⟪v i, u⟫ ^ 2 ≤ ‖u‖ ^ 2) (x : E) :
    ‖∑ i : Fin m, fderiv ℝ (fderiv ℝ (gradient (edge (v i.castSucc) (v i.succ)))) x‖ ≤
      (2 : ℝ) ^ 54 := by
  have h := SparseTensorBounds.sum_tensor_bound
    (fun i : Fin m => fderiv ℝ (fderiv ℝ (gradient (edge (v i.castSucc) (v i.succ)))) x)
    (fun i => energy (v i.castSucc) (v i.succ))
    (by norm_num : (0 : ℝ) ≤ 2 ^ 52) (by norm_num : (0 : ℝ) ≤ 4)
    (chain_energy v hv) (fun i u w => edge_bound _ _ _ _ _ (hn _) (hn _))
  norm_num at h ⊢
  exact h

lemma chain_bound {m : ℕ} (v : Fin (m + 1) → E)
    (hn : ∀ i, ‖v i‖ ≤ 1) (hv : ∀ u, ∑ i, ⟪v i, u⟫ ^ 2 ≤ ‖u‖ ^ 2) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (chain v))) x‖ ≤ (2 : ℝ) ^ 55 := by
  have ha := RidgeJets.third_norm profile_contDiff profile_derivative density_derivative
    densitySlope_derivative (v 0) x (by norm_num : (0 : ℝ) ≤ 8) (hn 0) (profile_jet_bounds _).2.2
  have hs := edge_sum_bound v hn hv x
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) 55) (norm_nonneg u))
  intro w
  have heval (T : E →L[ℝ] E →L[ℝ] E) {C : ℝ} (hT : ‖T‖ ≤ C) :
      ‖T u w‖ ≤ C * ‖u‖ * ‖w‖ :=
    ((T u).le_opNorm w).trans (mul_le_mul_of_nonneg_right
      ((T.le_opNorm u).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg u))) (norm_nonneg w))
  have hsa := heval _ hs
  have haa := heval _ ha
  rw [chain_third_apply]
  have hnorm := norm_add_le
    (-fderiv ℝ (fderiv ℝ (gradient (RidgeJets.value profile (v 0)))) x u w)
    (∑ i : Fin m, fderiv ℝ (fderiv ℝ (gradient (edge (v i.castSucc) (v i.succ)))) x u w)
  simp only [norm_neg] at hnorm
  simp only [sum_apply] at hsa
  calc
    _ ≤ 8 * ‖u‖ * ‖w‖ + 2 ^ 54 * ‖u‖ * ‖w‖ := hnorm.trans (add_le_add haa hsa)
    _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg w)]

end LongTails.Proofs.RelativeHessianJetBounds
