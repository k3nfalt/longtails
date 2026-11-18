import LongTails.Proofs.RelativeHessianChain
import LongTails.Proofs.RidgeJets
import LongTails.Proofs.ProductCompositionJets
import LongTails.Proofs.ThirdOrderAffineCalculus
import LongTails.Proofs.SparseTensorBounds

namespace LongTails.Proofs.RelativeHessianGeometry

open scoped RealInnerProductSpace BigOperators
open RelativeHessianArctan RelativeHessianGate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def edge (a b x : E) : ℝ :=
  RidgeJets.value gate (-a) x * RidgeJets.value profile (-b) x -
    RidgeJets.value gate a x * RidgeJets.value profile b x

noncomputable def chain {m : ℕ} (v : Fin (m + 1) → E) (x : E) : ℝ :=
  -RidgeJets.value profile (v 0) x + ∑ i : Fin m, edge (v i.castSucc) (v i.succ) x

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma edge_eq (a b x : E) : edge a b x = RelativeHessianChain.link ⟪a, x⟫ ⟪b, x⟫ := by
  simp [edge, RidgeJets.value, RelativeHessianChain.link]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma edge_smooth (a b : E) : ContDiff ℝ 3 (edge a b) :=
  ((RidgeJets.smooth gate_contDiff (-a)).mul (RidgeJets.smooth profile_contDiff (-b))).sub
    ((RidgeJets.smooth gate_contDiff a).mul (RidgeJets.smooth profile_contDiff b))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma chain_smooth {m : ℕ} (v : Fin (m + 1) → E) : ContDiff ℝ 3 (chain v) := by
  unfold chain
  exact (RidgeJets.smooth profile_contDiff _).neg.add
    (ContDiff.sum (fun (i : Fin m) _ => edge_smooth (v i.castSucc) (v i.succ)))

lemma edge_gradient (a b x : E) :
    gradient (edge a b) x =
      RelativeHessianChain.outgoing ⟪a, x⟫ ⟪b, x⟫ • a -
        ((gate ⟪a, x⟫ + gate (-⟪a, x⟫)) * density ⟪b, x⟫) • b := by
  unfold edge
  rw [ThirdOrderAffineCalculus.difference_gradient
    ((RidgeJets.smooth gate_contDiff (-a)).mul (RidgeJets.smooth profile_contDiff (-b)))
    ((RidgeJets.smooth gate_contDiff a).mul (RidgeJets.smooth profile_contDiff b))]
  rw [ProductCompositionJets.product_gradient (RidgeJets.smooth gate_contDiff (-a))
    (RidgeJets.smooth profile_contDiff (-b)),
    ProductCompositionJets.product_gradient (RidgeJets.smooth gate_contDiff a)
    (RidgeJets.smooth profile_contDiff b)]
  simp only [RidgeJets.gradient_eq gate_hasDerivAt, RidgeJets.gradient_eq profile_derivative,
    RidgeJets.value, inner_neg_left, density_neg, RelativeHessianChain.outgoing]
  module

lemma chain_gradient {m : ℕ} (v : Fin (m + 1) → E) (x : E) :
    gradient (chain v) x = -density ⟪v 0, x⟫ • v 0 +
      ∑ i : Fin m, (RelativeHessianChain.outgoing ⟪v i.castSucc, x⟫ ⟪v i.succ, x⟫ • v i.castSucc -
        ((gate ⟪v i.castSucc, x⟫ + gate (-⟪v i.castSucc, x⟫)) * density ⟪v i.succ, x⟫) • v i.succ) := by
  have hanchor := ((GradientDependentLocal.derivative_chain (RidgeJets.smooth profile_contDiff (v 0))).1 x).neg
  have hsum := HasFDerivAt.sum (u := Finset.univ)
    (fun (i : Fin m) _ => (GradientDependentLocal.derivative_chain (edge_smooth (v i.castSucc) (v i.succ))).1 x)
  have hh : HasGradientAt (chain v) (-gradient (RidgeJets.value profile (v 0)) x +
      ∑ i : Fin m, gradient (edge (v i.castSucc) (v i.succ)) x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert hanchor.add hsum using 1
    · funext y
      simp [chain]
    · ext u
      simp
  rw [hh.gradient, RidgeJets.gradient_eq profile_derivative]
  simp only [neg_smul, edge_gradient]

lemma chain_third_apply {m : ℕ} (v : Fin (m + 1) → E) (x u w : E) :
    fderiv ℝ (fderiv ℝ (gradient (chain v))) x u w =
      -fderiv ℝ (fderiv ℝ (gradient (RidgeJets.value profile (v 0)))) x u w +
      ∑ i : Fin m, fderiv ℝ (fderiv ℝ (gradient (edge (v i.castSucc) (v i.succ)))) x u w := by
  have hf := RidgeJets.smooth profile_contDiff (v 0)
  have hg : ContDiff ℝ 3 (fun y => ∑ i : Fin m, edge (v i.castSucc) (v i.succ) y) :=
    ContDiff.sum (fun i _ => edge_smooth _ _)
  have he : chain v = fun y => (-1 : ℝ) * RidgeJets.value profile (v 0) y +
      1 * (∑ i : Fin m, edge (v i.castSucc) (v i.succ) y) := by
    funext y
    simp [chain]
  rw [he, ThirdOrderAffineCalculus.combination_third hf hg,
    ThirdOrderAffineCalculus.sum_third Finset.univ (fun i _ => edge_smooth _ _)]
  simp

lemma plateau_jets {t : ℝ} (ht : 1 / 5 ≤ |t|) :
    gateSlope t = 0 ∧ gateCurvature t = 0 ∧ gateThird t = 0 ∧
    gateSlope (-t) = 0 ∧ gateCurvature (-t) = 0 ∧ gateThird (-t) = 0 := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht
    obtain ⟨_, hs, hc, hT⟩ := gate_saturated ht
    obtain ⟨_, hs', hc', hT'⟩ := gate_flat (show -t ≤ 1 / 10 by linarith)
    exact ⟨hs, hc, hT, hs', hc', hT'⟩
  · rw [abs_of_neg h] at ht
    obtain ⟨_, hs', hc', hT'⟩ := gate_saturated ht
    obtain ⟨_, hs, hc, hT⟩ := gate_flat (show t ≤ 1 / 10 by linarith)
    exact ⟨hs, hc, hT, hs', hc', hT'⟩

lemma edge_gradient_plateau (a b x : E) (ha : 1 / 5 ≤ |⟪a, x⟫|) :
    gradient (edge a b) x = -density ⟪b, x⟫ • b := by
  have hj := plateau_jets ha
  rw [edge_gradient, RelativeHessianChain.saturated_pair ha]
  simp [RelativeHessianChain.outgoing, hj.1, hj.2.2.2.1]

lemma edge_third_plateau (a b x u v : E) (ha : 1 / 5 ≤ |⟪a, x⟫|) :
    fderiv ℝ (fderiv ℝ (gradient (edge a b))) x u v =
      -(densityCurvature ⟪b, x⟫ * ⟪b, u⟫ * ⟪b, v⟫) • b := by
  have hj := plateau_jets ha
  have hp := RelativeHessianChain.saturated_pair ha
  unfold edge
  rw [ThirdOrderAffineCalculus.difference_third
    ((RidgeJets.smooth gate_contDiff (-a)).mul (RidgeJets.smooth profile_contDiff (-b)))
    ((RidgeJets.smooth gate_contDiff a).mul (RidgeJets.smooth profile_contDiff b))]
  simp only [sub_apply]
  rw [ProductCompositionJets.product_third_apply (RidgeJets.smooth gate_contDiff (-a))
    (RidgeJets.smooth profile_contDiff (-b)),
    ProductCompositionJets.product_third_apply (RidgeJets.smooth gate_contDiff a)
    (RidgeJets.smooth profile_contDiff b)]
  simp only [RidgeJets.gradient_eq gate_hasDerivAt, RidgeJets.gradient_eq profile_derivative,
    RidgeJets.hessian_apply gate_contDiff gate_hasDerivAt gateSlope_hasDerivAt,
    RidgeJets.hessian_apply profile_contDiff profile_derivative density_derivative,
    RidgeJets.third_apply gate_contDiff gate_hasDerivAt gateSlope_hasDerivAt gateCurvature_hasDerivAt,
    RidgeJets.third_apply profile_contDiff profile_derivative density_derivative densitySlope_derivative,
    RidgeJets.value, inner_neg_left, densityCurvature_neg, hj.1, hj.2.1, hj.2.2.1,
    hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2, zero_mul, zero_smul, inner_zero_left,
    add_zero, smul_zero]
  have hg : gate (-⟪a, x⟫) = 1 - gate ⟪a, x⟫ := by linarith
  rw [hg]
  module

lemma chain_gradient_plateau {m : ℕ} (v : Fin (m + 1) → E) (x : E)
    (hv : ∀ i, 1 / 5 ≤ |⟪v i, x⟫|) :
    gradient (chain v) x = -∑ i : Fin (m + 1), density ⟪v i, x⟫ • v i := by
  rw [chain_gradient]
  have he (i : Fin m) :
      RelativeHessianChain.outgoing ⟪v i.castSucc, x⟫ ⟪v i.succ, x⟫ • v i.castSucc -
        ((gate ⟪v i.castSucc, x⟫ + gate (-⟪v i.castSucc, x⟫)) * density ⟪v i.succ, x⟫) • v i.succ =
      -density ⟪v i.succ, x⟫ • v i.succ := by
    rw [← edge_gradient]
    exact edge_gradient_plateau _ _ _ (hv _)
  simp_rw [he]
  rw [Fin.sum_univ_succ]
  simp [neg_smul, Finset.sum_neg_distrib, add_comm]

lemma chain_third_plateau {m : ℕ} (v : Fin (m + 1) → E) (x u w : E)
    (hv : ∀ i, 1 / 5 ≤ |⟪v i, x⟫|) :
    fderiv ℝ (fderiv ℝ (gradient (chain v))) x u w =
      -∑ i : Fin (m + 1), (densityCurvature ⟪v i, x⟫ * ⟪v i, u⟫ * ⟪v i, w⟫) • v i := by
  rw [chain_third_apply, RidgeJets.third_apply profile_contDiff profile_derivative
    density_derivative densitySlope_derivative]
  simp_rw [edge_third_plateau _ _ _ _ _ (hv _)]
  rw [Fin.sum_univ_succ]
  simp [neg_smul, Finset.sum_neg_distrib, add_comm]

end LongTails.Proofs.RelativeHessianGeometry
