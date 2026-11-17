import LongTails.Proofs.RelativeHessianFirstSmall
import LongTails.Proofs.RelativeHessianChainBounds
import LongTails.Proofs.RelativeHessianCutoffBounds

set_option maxRecDepth 2000

namespace LongTails.Proofs.RelativeHessianLocalized

open scoped RealInnerProductSpace BigOperators
open RelativeHessianArctan RelativeHessianGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def radius (m : ℕ) : ℝ := 2 ^ 60 * (m + 1 : ℕ)
noncomputable def perturbation {m : ℕ} (v : Fin (m + 1) → E) (x : E) : ℝ :=
  RelativeHessianCutoffSpatial.value (radius m) x * chain v x
noncomputable def value {m : ℕ} (v : Fin (m + 1) → E) (x : E) : ℝ :=
  perturbation v x + FullGeneralizedSmoothZeroQuery.quadratic coefficient 0 x

lemma radius_pos (m : ℕ) : 0 < radius m := by unfold radius; positivity
lemma radius_large (m : ℕ) : 2 ≤ radius m := by
  unfold radius
  have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
  nlinarith

lemma count_div_radius (m : ℕ) : (m + 1 : ℕ) / radius m = (1 : ℝ) / 2 ^ 60 := by
  unfold radius
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma count_div_radius_pow (m k : ℕ) (hk : 1 ≤ k) :
    (m + 1 : ℕ) / radius m ^ k ≤ (1 : ℝ) / 2 ^ 60 := by
  calc
    _ ≤ (m + 1 : ℕ) / radius m := div_le_div_of_nonneg_left (by positivity)
      (radius_pos m) (le_self_pow₀ (by linarith [radius_large m]) (by omega : k ≠ 0))
    _ = _ := count_div_radius m

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma perturbation_smooth {m : ℕ} (v : Fin (m + 1) → E) : ContDiff ℝ 3 (perturbation v) :=
  (RelativeHessianCutoffSpatial.smooth _).mul (chain_smooth v)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma smooth {m : ℕ} (v : Fin (m + 1) → E) : ContDiff ℝ 3 (value v) :=
  (perturbation_smooth v).add (RelativeHessianGuard.quadratic_smooth _)

lemma gradient_eq {m : ℕ} (v : Fin (m + 1) → E) (x : E) :
    gradient (value v) x = gradient (perturbation v) x + coefficient • x := by
  unfold value
  have h := ThirdOrderAffineCalculus.combination_gradient (perturbation_smooth v)
    (RelativeHessianGuard.quadratic_smooth coefficient) 1 1 x
  simpa only [one_mul, one_smul, RelativeHessianGuard.quadratic_gradient] using h

lemma third_eq {m : ℕ} (v : Fin (m + 1) → E) (x : E) :
    fderiv ℝ (fderiv ℝ (gradient (value v))) x =
      fderiv ℝ (fderiv ℝ (gradient (perturbation v))) x := by
  unfold value
  have h := ThirdOrderAffineCalculus.combination_third (perturbation_smooth v)
    (RelativeHessianGuard.quadratic_smooth coefficient) 1 1 x
  simpa only [one_mul, one_smul, RelativeHessianGuard.quadratic_third, add_zero] using h

lemma inside_gradient {m : ℕ} (v : Fin (m + 1) → E) (x : E) (hx : ‖x‖ ≤ radius m) :
    gradient (value v) x = gradient (RelativeHessianGuard.value v) x := by
  obtain ⟨hc, hg, _, _⟩ := RelativeHessianCutoffSpatial.inside_jets (radius_pos m) x hx
  rw [gradient_eq, RelativeHessianGuard.gradient_eq]
  unfold perturbation
  rw [ProductCompositionJets.product_gradient (RelativeHessianCutoffSpatial.smooth _) (chain_smooth v)]
  simp [hc, hg]

lemma inside_third {m : ℕ} (v : Fin (m + 1) → E) (x : E) (hx : ‖x‖ ≤ radius m) :
    fderiv ℝ (fderiv ℝ (gradient (value v))) x =
      fderiv ℝ (fderiv ℝ (gradient (RelativeHessianGuard.value v))) x := by
  obtain ⟨hc, hg, hH, hT⟩ := RelativeHessianCutoffSpatial.inside_jets (radius_pos m) x hx
  rw [third_eq, RelativeHessianGuard.third_eq]
  ext u w
  unfold perturbation
  rw [ProductCompositionJets.product_third_apply (RelativeHessianCutoffSpatial.smooth _) (chain_smooth v)]
  simp [hc, hg, hH, hT]

lemma perturbation_gradient_bound {m : ℕ} {v : Fin (m + 1) → E}
    (hv : Orthonormal ℝ v) (x : E) : ‖gradient (perturbation v) x‖ ≤ 2 ^ 53 * (m + 1 : ℕ) := by
  have hcut := (RelativeHessianCutoffBounds.bounds (radius_pos m) x).1
  have hval : |RelativeHessianCutoffSpatial.value (radius m) x| ≤ 1 := by
    have h := RelativeHessianCutoff.bounds (RelativeHessianCutoffSpatial.argument (radius m) x)
    exact (abs_of_nonneg h.1).trans_le h.2
  have hg := RelativeHessianChainBounds.gradient_bound v (fun i => (hv.norm_eq_one i).le) x
  have hc := RelativeHessianChainBounds.value_bound v x
  unfold perturbation
  rw [ProductCompositionJets.product_gradient (RelativeHessianCutoffSpatial.smooth _) (chain_smooth v)]
  calc
    _ ≤ ‖RelativeHessianCutoffSpatial.value (radius m) x • gradient (chain v) x‖ +
        ‖chain v x • gradient (RelativeHessianCutoffSpatial.value (radius m)) x‖ := norm_add_le _ _
    _ = |RelativeHessianCutoffSpatial.value (radius m) x| * ‖gradient (chain v) x‖ +
        |chain v x| * ‖gradient (RelativeHessianCutoffSpatial.value (radius m)) x‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * (2 ^ 52 * (m + 1 : ℕ)) + (4 * (m + 1 : ℕ)) * (2 ^ 32 / radius m) :=
      add_le_add (mul_le_mul hval hg (norm_nonneg _) (by norm_num))
        (mul_le_mul hc hcut (norm_nonneg _) (by positivity))
    _ = 2 ^ 52 * (m + 1 : ℕ) + (4 * 2 ^ 32) * ((m + 1 : ℕ) / radius m) := by ring
    _ ≤ 2 ^ 53 * (m + 1 : ℕ) := by
      rw [count_div_radius]
      have hn : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
      norm_num
      nlinarith

lemma absolute_third {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (value v))) x‖ ≤ (2 : ℝ) ^ 56 := by
  have hR : 0 < radius m := radius_pos m
  have hcut := RelativeHessianCutoffBounds.bounds hR x
  have hval : |RelativeHessianCutoffSpatial.value (radius m) x| ≤ 1 := by
    have h := RelativeHessianCutoff.bounds (RelativeHessianCutoffSpatial.argument (radius m) x)
    exact (abs_of_nonneg h.1).trans_le h.2
  have hg := RelativeHessianChainBounds.gradient_bound v (fun i => (hv.norm_eq_one i).le) x
  have hH := RelativeHessianChainBounds.hessian_bound v (fun i => (hv.norm_eq_one i).le) x
  have hT := RelativeHessianJetBounds.chain_bound v (fun i => (hv.norm_eq_one i).le)
    (RelativeHessianGuard.bessel hv) x
  have hc := RelativeHessianChainBounds.value_bound v x
  rw [third_eq]
  have hp := ProductCompositionJets.product_third_norm (RelativeHessianCutoffSpatial.smooth (radius m))
    (chain_smooth v) x
  change ‖fderiv ℝ (fderiv ℝ (gradient (perturbation v))) x‖ ≤ _ at hp
  calc
    _ ≤ |RelativeHessianCutoffSpatial.value (radius m) x| * ‖fderiv ℝ (fderiv ℝ (gradient (chain v))) x‖ +
        |chain v x| * ‖fderiv ℝ (fderiv ℝ (gradient (RelativeHessianCutoffSpatial.value (radius m)))) x‖ +
        3 * ‖gradient (RelativeHessianCutoffSpatial.value (radius m)) x‖ * ‖fderiv ℝ (gradient (chain v)) x‖ +
        3 * ‖gradient (chain v) x‖ * ‖fderiv ℝ (gradient (RelativeHessianCutoffSpatial.value (radius m))) x‖ := hp
    _ ≤ 1 * 2 ^ 55 + (4 * (m + 1 : ℕ)) * (2 ^ 32 / radius m ^ 3) +
        3 * (2 ^ 32 / radius m) * (2 ^ 52 * (m + 1 : ℕ)) +
        3 * (2 ^ 52 * (m + 1 : ℕ)) * (2 ^ 32 / radius m ^ 2) := by
      gcongr <;> first | exact hval | exact hT | exact hc | exact hcut.2.2 | exact hcut.1 | exact hH | exact hg | exact hcut.2.1
    _ = 2 ^ 55 + (4 * 2 ^ 32) * ((m + 1 : ℕ) / radius m ^ 3) +
        (3 * 2 ^ 32 * 2 ^ 52) * ((m + 1 : ℕ) / radius m) +
        (3 * 2 ^ 52 * 2 ^ 32) * ((m + 1 : ℕ) / radius m ^ 2) := by ring
    _ ≤ 2 ^ 55 + (4 * 2 ^ 32) * (1 / 2 ^ 60) +
        (3 * 2 ^ 32 * 2 ^ 52) * (1 / 2 ^ 60) +
        (3 * 2 ^ 52 * 2 ^ 32) * (1 / 2 ^ 60) := by
      exact add_le_add (add_le_add (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (count_div_radius_pow m 3 (by omega)) (by positivity)))
        (mul_le_mul_of_nonneg_left (count_div_radius m).le (by positivity)))
        (mul_le_mul_of_nonneg_left (count_div_radius_pow m 2 (by omega)) (by positivity))
    _ ≤ _ := by norm_num

lemma outside_gradient {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v)
    (x : E) (hx : radius m ≤ ‖x‖) : ‖x‖ / 2 ≤ ‖gradient (value v) x‖ := by
  have hp := perturbation_gradient_bound hv x
  have ha := balance_parameters.1
  have hc : 0 ≤ coefficient := by linarith
  have he : coefficient • x = gradient (value v) x - gradient (perturbation v) x := by
    rw [gradient_eq]
    module
  have h : ‖coefficient • x‖ ≤ ‖gradient (value v) x‖ + ‖gradient (perturbation v) x‖ := by
    rw [he]
    exact norm_sub_le _ _
  rw [norm_smul, Real.norm_of_nonneg hc] at h
  have hm := mul_le_mul_of_nonneg_right ha (norm_nonneg x)
  unfold radius at hx
  nlinarith [show (0 : ℝ) ≤ (m + 1 : ℕ) by positivity]

lemma relative_third {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (value v))) x‖ ≤ (2 : ℝ) ^ 56 * ‖gradient (value v) x‖ := by
  by_cases hx : ‖x‖ ≤ radius m
  · rw [inside_gradient v x hx, inside_third v x hx]
    exact RelativeHessianFirstSmall.relative_third hv x
  · have hg := outside_gradient hv x (le_of_not_ge hx)
    have hR := radius_large m
    have hnorm : 1 ≤ ‖gradient (value v) x‖ := by linarith [le_of_not_ge hx]
    exact (absolute_third hv x).trans (by nlinarith)

lemma hidden_gradient {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v)
    (x : E) (hex : ∃ i, |⟪v i, x⟫| ≤ 1 / 5) : 7 / 10 ≤ ‖gradient (value v) x‖ := by
  by_cases hx : ‖x‖ ≤ radius m
  · rw [inside_gradient v x hx]
    exact RelativeHessianFirstSmall.gradient_norm hv x hex
  · have hg := outside_gradient hv x (le_of_not_ge hx)
    linarith [radius_large m, le_of_not_ge hx]

lemma initial_gradient {m : ℕ} (v : Fin (m + 1) → E) : gradient (value v) 0 = -v 0 := by
  rw [inside_gradient v 0 (by simpa using (radius_pos m).le)]
  exact RelativeHessianFirstSmall.initial_gradient v

lemma initial_value {m : ℕ} (v : Fin (m + 1) → E) : value v 0 = -Real.pi / 2 := by
  have hc := (RelativeHessianCutoffSpatial.inside_jets (radius_pos m) (0 : E)
    (by simpa using (radius_pos m).le)).1
  simp [value, perturbation, hc, RelativeHessianChainBounds.value_zero,
    FullGeneralizedSmoothZeroQuery.quadratic]

lemma gap {m : ℕ} (v : Fin (m + 1) → E) (x : E) : value v 0 - value v x ≤ 4 * (m + 1 : ℕ) := by
  have hc := RelativeHessianChainBounds.value_bound v x
  have hχ := RelativeHessianCutoff.bounds (RelativeHessianCutoffSpatial.argument (radius m) x)
  change 0 ≤ RelativeHessianCutoffSpatial.value (radius m) x ∧
    RelativeHessianCutoffSpatial.value (radius m) x ≤ 1 at hχ
  have hprod : |perturbation v x| ≤ 4 * (m + 1 : ℕ) := by
    unfold perturbation
    rw [abs_mul, abs_of_nonneg hχ.1]
    exact (mul_le_mul hχ.2 hc (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
  have hq := FullGeneralizedSmoothZeroQuery.quadratic_nonneg coefficient
    (show 0 ≤ coefficient by linarith [balance_parameters.1]) (0 : E) x
  rw [initial_value]
  unfold value
  linarith [(abs_le.mp hprod).1, Real.pi_pos]

end LongTails.Proofs.RelativeHessianLocalized
