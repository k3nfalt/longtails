import LongTails.Proofs.InterpolatedFiniteSumLinkReplies

open scoped BigOperators RealInnerProductSpace
open Classical

namespace LongTails.Proofs.InterpolatedFiniteSumLinkFamily

open InterpolatedFiniteSumLinkGeometry InterpolatedFiniteSumLinkReplies
open InterpolatedFiniteSumLinkPlacement InterpolatedFiniteSumExponentialFamily
open LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum

lemma family_nonnegative {d g T : ℕ} (θ : Fin T ↪ Fin g) (π : Fin T → Fin d) (η a L r G W : ℝ)
    (hη : 0 ≤ η) (hW : 0 < W) (i : Fin g) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ family θ π η a L r G W i x := by
  apply assigned_property θ _ _ (fun f : EuclideanSpace ℝ (Fin d) → ℝ => 0 ≤ f x)
  · intro j
    exact InterpolatedFiniteSumLinks.shielded_nonnegative _ _ _ _ _ _ (coefficient_nonnegative η hη j) hW x
  · exact InterpolatedFiniteSumLinks.shielded_nonnegative _ _ _ _ _ _ (by norm_num) hW x

lemma family_minimizer_value {d g T : ℕ} (θ : Fin T ↪ Fin g) (π : Fin T ↪ Fin d) (η a L r G W : ℝ)
    (hη : 0 ≤ η) (ha : 0 < a) (hr : 0 < r) (hG : 0 ≤ G) (hW : 0 < W)
    (hz : ‖minimizer π a‖ ≤ r) (i : Fin g) : family θ π η a L r G W i (minimizer π a) = 0 := by
  apply assigned_property θ _ _ (fun f : EuclideanSpace ℝ (Fin d) → ℝ => f (minimizer π a) = 0)
  · intro j
    exact InterpolatedFiniteSumLinks.shielded_minimizer_value _ _ _ _ _ _ (coefficient_nonnegative η hη j)
      hr hG hW (minimizer π a) hz (vector_minimizer π a L (ne_of_gt ha) j)
  · exact InterpolatedFiniteSumLinks.shielded_minimizer_value _ _ _ _ _ _ (by norm_num)
      hr hG hW (minimizer π a) hz (by simp)

lemma admissible (p : Params) (hp : spec.valid p) {g k : ℕ} (h : 2 * g ≤ p.n)
    (θ : Fin (k + 1) ↪ Fin g) (π : Fin (k + 1) ↪ Fin p.d) (v : Point p)
    (C η a r G W : ℝ) (hC : 0 ≤ C) (hη : 0 ≤ η) (ha : 0 < a) (hr : 0 < r)
    (hG : 0 ≤ G) (hW : 0 < W)
    (hwidth : 64 * G ^ 2 ≤ W * (4 * p.L1 ^ 2 / 49))
    (hrad : 4 * G / r ≤ (4 * p.L1 ^ 2 / 49) / 3)
    (hgrad : ∀ j : Fin (k + 1), coefficient η j * ‖vector π a p.L1 j‖ ≤ G)
    (hcurv : ∀ j : Fin (k + 1), 3 * coefficient η j * ‖vector π a p.L1 j‖ ^ 2 ≤ (4 * p.L1 ^ 2 / 49) / 3)
    (hGsmall : 2 * G ≤ p.L1 / 7) (hv : ‖v‖ = 2 * p.L1 / 7)
    (hadd : 2 * C * p.L1 ^ 2 / 7 ≤ p.L0)
    (hzr : ‖minimizer π a‖ ≤ r) (hzR : ‖minimizer π a‖ ≤ p.R) (hvz : ⟪v, minimizer π a⟫ = 0)
    (hgap : (2 * C / p.n) * (Real.exp η - 1) ≤ p.Δ) :
    spec.admissible p (components h (family θ π η a p.L1 r G W) v C)
      (InterpolatedFiniteSumHiddenComponent.exactOracle p
        (components h (family θ π η a p.L1 r G W) v C)
        (fields h (family θ π η a p.L1 r G W) (familyField θ π η a p.L1 r G W) v C)) := by
  apply InterpolatedFiniteSumExponentialFamily.admissible p hp h _ _ v (minimizer π a) C hC
    (family_gradient θ π η a p.L1 r G W hr hW)
  · intro i
    apply assigned_property θ _ _ (fun f : Point p → Point p => Differentiable ℝ f)
    · intro j
      exact InterpolatedFiniteSumLinks.shielded_differentiable _ _ _ _ _ _ hr
    · exact InterpolatedFiniteSumLinks.shielded_differentiable _ _ _ _ _ _ hr
  · intro i
    apply assigned_property θ _ _ (fun f : Point p → ℝ => ConvexOn ℝ Set.univ f)
    · intro j
      exact InterpolatedFiniteSumLinks.shielded_convex _ _ _ _ _ _ (coefficient_nonnegative η hη j) hr hG hW
    · exact InterpolatedFiniteSumLinks.shielded_convex _ _ _ _ _ _ (by norm_num) hr hG hW
  · intro i x
    apply assigned_property θ _ _ (fun f : Point p → Point p => ‖f x‖ ≤ p.L1 / 7)
    · intro j
      exact (InterpolatedFiniteSumLinks.shieldedField_norm _ _ _ _ _ _ (coefficient_nonnegative η hη j)
        hr hG (hgrad j) x).trans hGsmall
    · exact (InterpolatedFiniteSumLinks.shieldedField_norm _ _ _ _ _ _ (by norm_num)
        hr hG (by simpa using hG) x).trans hGsmall
  · exact hv
  · intro i x
    apply assigned_property θ _ _ (fun f : Point p → Point p => ‖fderiv ℝ f x‖ ≤ 4 * p.L1 ^ 2 / 49)
    · intro j
      exact InterpolatedFiniteSumLinks.shieldedField_curvature _ _ _ _ _ _ _ (coefficient_nonnegative η hη j)
        hr hG hW (by positivity) hwidth hrad (hgrad j) (hcurv j) x
    · exact InterpolatedFiniteSumLinks.shieldedField_curvature _ _ _ _ _ _ _ (by norm_num)
        hr hG hW (by positivity) hwidth hrad (by simpa using hG) (by simp; positivity) x
  · exact hadd
  · exact family_nonnegative θ π η a p.L1 r G W hη hW
  · exact family_minimizer_value θ π η a p.L1 r G W hη ha hr hG hW hzr
  · exact hvz
  · exact hzR
  · rw [initial_sum θ π η a p.L1 r G W hη hr hG hW]
    convert hgap using 1
    ring

lemma objective_lower {d n g T : ℕ} (h : 2 * g ≤ n) (θ : Fin T ↪ Fin g) (π : Fin T → Fin d)
    (v : EuclideanSpace ℝ (Fin d)) (C η a L r G W D : ℝ) (hC : 0 ≤ C) (hW : 0 < W)
    (x : EuclideanSpace ℝ (Fin d))
    (hD : D ≤ ∑ j : Fin T, (Real.exp (latent π η a L r G W j x) - 1)) :
    (2 * C / n) * D ≤ (n : ℝ)⁻¹ * ∑ i, components h (family θ π η a L r G W) v C i x := by
  have hz : 0 ≤ Real.exp (empty r G W x) - 1 := sub_nonneg.mpr (Real.one_le_exp
    (InterpolatedFiniteSumLinks.shielded_nonnegative _ _ _ _ _ _ (by norm_num) hW x))
  have hs := sum_assigned_lower θ (latent π η a L r G W) (empty r G W)
    (fun f => Real.exp (f x) - 1) hz
  have hp := InterpolatedFiniteSumExponentialFamily.components_sum_lower h (family θ π η a L r G W) v C hC x
  have hm := mul_le_mul_of_nonneg_left (hD.trans hs) (by positivity : 0 ≤ 2 * C)
  have hb := mul_le_mul_of_nonneg_left (hm.trans hp) (show 0 ≤ (n : ℝ)⁻¹ by positivity)
  convert hb using 1
  ring

lemma latent_sum_lower {d k : ℕ} (π : Fin (k + 1) → Fin d) (η a L r G W B α : ℝ)
    (hη : 0 ≤ η) (ha : 0 < a) (hL : 0 < L) (hr : 0 ≤ r) (hG : 0 < G) (hW : 0 < W) (hα : 0 ≤ α)
    (hB : 4 * r + (η + W) / G ≤ B) (ℓ : ℕ) (hℓ : ℓ ≤ k + 1)
    (hterminal : Real.exp η - 1 ≤ (k + 1 : ℕ) * (256 * ((2 * η * Real.exp η / a) / L) *
      (1 + max 0 (Real.log (256 * ((2 * η * Real.exp η / a) / L))))))
    (x : EuclideanSpace ℝ (Fin d))
    (hx : ‖x‖ ≤ B → ∀ j : Fin (k + 1), ℓ ≤ j.val → |x (π j)| ≤ α) :
    let s := 2 * η * Real.exp η / a
    let K := 256 * (s / L) * (1 + max 0 (Real.log (256 * (s / L))))
    Real.exp η - 1 - s * α - ℓ * K ≤ ∑ j : Fin (k + 1), (Real.exp (latent π η a L r G W j x) - 1) := by
  dsimp only
  let s := 2 * η * Real.exp η / a
  let K := 256 * (s / L) * (1 + max 0 (Real.log (256 * (s / L))))
  change Real.exp η - 1 - s * α - ℓ * K ≤ _
  have hnon (j : Fin (k + 1)) : 0 ≤ Real.exp (latent π η a L r G W j x) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (InterpolatedFiniteSumLinks.shielded_nonnegative _ _ _ _ _ _
      (coefficient_nonnegative η hη j) hW x))
  by_cases hnear : ‖x‖ ≤ B
  · have hy : ℓ < k + 1 → sequence π x ℓ ≤ α := by
      intro hlt
      have hh := (abs_le.mp (hx hnear ⟨ℓ, hlt⟩ le_rfl)).2
      simpa only [InterpolatedFiniteSumLinkGeometry.sequence, dite_eq_left hlt] using hh
    have hh := InterpolatedFiniteSumLinkResidual.total_lower η L a α (sequence π x) hη ha hL
      (k + 1) ℓ hℓ hterminal hα hy
    have he : (∑ j : Fin (k + 1), (Real.exp (raw π η a L j x) - 1)) =
        ∑ j ∈ Finset.range (k + 1), InterpolatedFiniteSumLinkResidual.loss η L a (sequence π x) j := by
      simp_rw [loss_eq]
      exact Fin.sum_univ_eq_sum_range _ _
    have hs : (∑ j : Fin (k + 1), (Real.exp (raw π η a L j x) - 1)) ≤
        ∑ j : Fin (k + 1), (Real.exp (latent π η a L r G W j x) - 1) := by
      apply Finset.sum_le_sum
      intro j _
      apply sub_le_sub_right
      apply Real.exp_le_exp.mpr
      exact (InterpolatedFiniteSumProfiles.smoothMax_above W _ _ hW).1
    rw [he] at hs
    exact hh.trans hs
  · have hfirst : η ≤ latent π η a L r G W (0 : Fin (k + 1)) x :=
      InterpolatedFiniteSumLinks.shielded_far_lower _ _ _ _ _ _ η B hr hG hW hη hB x (lt_of_not_ge hnear).le
    have hh : Real.exp η - 1 ≤ ∑ j : Fin (k + 1), (Real.exp (latent π η a L r G W j x) - 1) :=
      (sub_le_sub_right (Real.exp_le_exp.mpr hfirst) 1).trans
        (Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ (0 : Fin (k + 1))))
    have hs : 0 ≤ s * α := by dsimp [s]; positivity
    have hK : 0 ≤ (ℓ : ℝ) * K := by dsimp [K, s]; positivity
    linarith only [hh, hs, hK]

lemma output_lower {d n g k : ℕ} (h : 2 * g ≤ n) (θ : Fin (k + 1) ↪ Fin g)
    (π : Fin (k + 1) → Fin d) (v : EuclideanSpace ℝ (Fin d)) (C η a L r G W B α : ℝ)
    (hC : 0 ≤ C) (hη : 0 ≤ η) (ha : 0 < a) (hL : 0 < L) (hr : 0 ≤ r)
    (hG : 0 < G) (hW : 0 < W) (hα : 0 ≤ α) (hB : 4 * r + (η + W) / G ≤ B)
    (ℓ : ℕ) (hℓ : ℓ ≤ k + 1)
    (hterminal : Real.exp η - 1 ≤ (k + 1 : ℕ) * (256 * ((2 * η * Real.exp η / a) / L) *
      (1 + max 0 (Real.log (256 * ((2 * η * Real.exp η / a) / L))))))
    (x : EuclideanSpace ℝ (Fin d))
    (hx : ‖x‖ ≤ B → ∀ j : Fin (k + 1), ℓ ≤ j.val → |x (π j)| ≤ α) :
    let s := 2 * η * Real.exp η / a
    let K := 256 * (s / L) * (1 + max 0 (Real.log (256 * (s / L))))
    (2 * C / n) * (Real.exp η - 1 - s * α) - ((2 * C / n) * K) * ℓ ≤
      (n : ℝ)⁻¹ * ∑ i, components h (family θ π η a L r G W) v C i x := by
  have hh := objective_lower h θ π v C η a L r G W _ hC hW x
    (latent_sum_lower π η a L r G W B α hη ha hL hr hG hW hα hB ℓ hℓ hterminal x hx)
  dsimp only at *
  convert hh using 1
  ring

end LongTails.Proofs.InterpolatedFiniteSumLinkFamily
