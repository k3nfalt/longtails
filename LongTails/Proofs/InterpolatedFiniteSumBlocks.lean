import LongTails.Proofs.InterpolatedFiniteSumChains
import LongTails.Proofs.InterpolatedFiniteSumShield
import LongTails.Proofs.InterpolatedFiniteSumHiddenComponent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.InterpolatedFiniteSumBlocks

open InterpolatedFiniteSumChains InterpolatedFiniteSumShield FiniteSumNondualLowerComponents

noncomputable def block {d n k : ℕ} (π : (Fin n × Fin (k + 1)) ↪ Fin d) (i : Fin n) :
    Fin (k + 1) ↪ Fin d where
  toFun j := π (i, j)
  inj' _ _ h := (Prod.mk.inj (π.injective h)).2

noncomputable def blockVector (n k : ℕ) (σ : ℝ) : EuclideanSpace ℝ (Fin n × Fin (k + 1)) :=
  WithLp.toLp 2 (fun ij => descendingVector k σ ij.2)

noncomputable def minimizer {d n k : ℕ} (π : (Fin n × Fin (k + 1)) ↪ Fin d) (σ : ℝ) :
    EuclideanSpace ℝ (Fin d) := (coordinateMap π).adjoint (blockVector n k σ)

lemma minimizer_coordinates {d n k : ℕ} (π : (Fin n × Fin (k + 1)) ↪ Fin d) (σ : ℝ)
    (i : Fin n) : coordinateMap (block π i) (minimizer π σ) = descendingVector k σ := by
  ext j
  change (coordinateMap π).adjoint (blockVector n k σ) (π (i, j)) = descendingVector k σ j
  rw [coordinateMap_adjoint_coordinate]
  rfl

lemma blockVector_norm_sq (n k : ℕ) (σ : ℝ) :
    ‖blockVector n k σ‖ ^ 2 = (n : ℝ) * ‖descendingVector k σ‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  change (∑ _ : Fin n, ∑ j : Fin (k + 1), (descendingVector k σ j) ^ 2) = _
  simp

lemma minimizer_norm_sq {d n k : ℕ} (π : (Fin n × Fin (k + 1)) ↪ Fin d) (σ : ℝ)
    (hσ : 0 ≤ σ) :
    ‖minimizer π σ‖ ^ 2 ≤ (n : ℝ) * (k + 1 : ℕ) ^ 3 * σ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (coordinateMap_adjoint_norm π (blockVector n k σ)) 2
  rw [blockVector_norm_sq] at h
  have hd := pow_le_pow_left₀ (norm_nonneg _) (descendingVector_norm k σ hσ) 2
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (k + 1 : ℕ) by positivity)
  have hb := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simp only [mul_pow, hs] at hb
  dsimp [minimizer]
  nlinarith only [h, hb]

lemma rawChain_minimizer {d n k : ℕ} (π : (Fin n × Fin (k + 1)) ↪ Fin d) (c σ : ℝ)
    (hσ : σ ≠ 0) (i : Fin n) :
    rawChain (block π i) c σ (minimizer π σ) = -((k + 1 : ℕ) : ℝ) * c / 2 := by
  rw [rawChain, selected_sequence, minimizer_coordinates]
  rw [sequence_congr c σ (k + 1) _ _ (descendingVector_sequence k σ)]
  exact sequence_minimizer c σ hσ (k + 1)

noncomputable def shifted {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ := rawChain π c σ x + (k + 1 : ℕ) * c / 2

lemma shifted_gradient {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : HasGradientAt (shifted π c σ) (rawField π c σ x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (rawChain_gradient π c σ x).hasFDerivAt.add_const ((k + 1 : ℕ) * c / 2)

lemma shifted_nonnegative {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ) (hc : 0 ≤ c)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ shifted π c σ x := by
  have h := rawChain_lower π c σ hc x
  dsimp [shifted]
  linarith

lemma shifted_convex {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ) (hc : 0 ≤ c) :
    ConvexOn ℝ Set.univ (shifted π c σ) := (rawChain_convex π c σ hc).add_const _

noncomputable def shielded {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ r G W : ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ := envelope (shifted π c σ) (radialWall r G 0 W) W

noncomputable def shieldedField {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ r G W : ℝ) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  envelopeField (shifted π c σ) (radialWall r G 0 W) (rawField π c σ) (radialField r G) W

lemma shielded_gradient {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ r G W : ℝ)
    (hr : 0 < r) (hW : 0 < W) (x : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (shielded π c σ r G W) (shieldedField π c σ r G W x) x :=
  envelope_hasGradientAt _ _ _ _ W hW x (shifted_gradient π c σ x)
    (radialWall_hasGradientAt r G 0 W hr x)

lemma shielded_convex {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ r G W : ℝ)
    (hc : 0 ≤ c) (hr : 0 < r) (hG : 0 ≤ G) (hW : 0 < W) :
    ConvexOn ℝ Set.univ (shielded π c σ r G W) :=
  envelope_convex _ _ _ _ W hW (shifted_convex π c σ hc)
    (radialWall_convex r G 0 W hr hG) (shifted_gradient π c σ)
    (radialWall_hasGradientAt r G 0 W hr)

lemma shielded_nonnegative {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ r G W : ℝ)
    (hc : 0 ≤ c) (hW : 0 < W) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ shielded π c σ r G W x :=
  (shifted_nonnegative π c σ hc x).trans
    (InterpolatedFiniteSumProfiles.smoothMax_above W _ _ hW).1

lemma shielded_zero {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ r G W : ℝ)
    (hc : 0 ≤ c) (hr : 0 < r) (hG : 0 ≤ G) (hW : 0 < W) :
    shielded π c σ r G W 0 = (k + 1 : ℕ) * c / 2 := by
  rw [shielded, envelope_radial_interior _ r G 0 W hr hG hW
    (shifted_nonnegative π c σ hc) 0 (by simpa using hr.le)]
  simp only [shifted, rawChain_zero, zero_add]

lemma shielded_minimizer_value {d n k : ℕ} (π : (Fin n × Fin (k + 1)) ↪ Fin d)
    (c σ r G W : ℝ) (hc : 0 ≤ c) (hσ : 0 < σ) (hr : 0 < r) (hG : 0 ≤ G) (hW : 0 < W)
    (hz : ‖minimizer π σ‖ ≤ r) (i : Fin n) :
    shielded (block π i) c σ r G W (minimizer π σ) = 0 := by
  rw [shielded, envelope_radial_interior _ r G 0 W hr hG hW
    (shifted_nonnegative (block π i) c σ hc) _ hz]
  rw [shifted, rawChain_minimizer π c σ (ne_of_gt hσ) i]
  ring

lemma shielded_minimizer {d n k : ℕ} (π : (Fin n × Fin (k + 1)) ↪ Fin d)
    (c σ r G W : ℝ) (hc : 0 ≤ c) (hσ : 0 < σ) (hr : 0 < r) (hG : 0 ≤ G) (hW : 0 < W)
    (hz : ‖minimizer π σ‖ ≤ r) (i : Fin n) :
    IsMinOn (shielded (block π i) c σ r G W) Set.univ (minimizer π σ) := by
  intro x _
  change shielded (block π i) c σ r G W (minimizer π σ) ≤ _
  rw [shielded_minimizer_value π c σ r G W hc hσ hr hG hW hz i]
  exact shielded_nonnegative (block π i) c σ r G W hc hW x

lemma shieldedField_differentiable {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ r G W : ℝ)
    (hr : 0 < r) : Differentiable ℝ (shieldedField π c σ r G W) :=
  envelopeField_differentiable _ _ _ _ W (shifted_gradient π c σ)
    (radialWall_hasGradientAt r G 0 W hr) (rawField_differentiable π c σ)
    (radialField_differentiable r G hr)

lemma shieldedField_curvature {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ r G W L : ℝ)
    (hc : 0 ≤ c) (hσ : 0 < σ) (hr : 0 < r) (hG : 0 ≤ G) (hW : 0 < W) (hL : 0 ≤ L)
    (hwidth : 64 * G ^ 2 ≤ W * L) (hrad : 4 * G / r ≤ L / 3)
    (hgrad : (c / σ) * (1 + 2 * Real.sqrt (k + 1 : ℕ)) ≤ G)
    (hcurv : 12 * c / σ ^ 2 ≤ L / 3) (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (shieldedField π c σ r G W) x‖ ≤ L :=
  envelope_radial_curvature _ _ r G 0 W L hr hG hW hL hwidth hrad x
    (shifted_gradient π c σ x) (rawField_differentiable π c σ x)
    ((rawField_norm π c σ hc hσ x).trans hgrad)
    ((rawField_curvature π c σ hc hσ x).trans hcurv)

lemma shifted_growth {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ G : ℝ)
    (hc : 0 ≤ c) (hσ : 0 < σ)
    (hgrad : (c / σ) * (1 + 2 * Real.sqrt (k + 1 : ℕ)) ≤ G)
    (x : EuclideanSpace ℝ (Fin d)) : shifted π c σ x ≤ shifted π c σ 0 + G * ‖x‖ := by
  have h := OracleTemplate.Gradient.convex_support (shifted_convex π c σ hc)
    (shifted_gradient π c σ) x 0
  have hi := real_inner_le_norm (rawField π c σ x) x
  have hg := mul_le_mul_of_nonneg_right ((rawField_norm π c σ hc hσ x).trans hgrad) (norm_nonneg x)
  simp only [zero_sub, inner_neg_right] at h
  linarith only [h, hi, hg]

lemma shielded_gradient_eq {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ r G W : ℝ)
    (hr : 0 < r) (hW : 0 < W) :
    gradient (shielded π c σ r G W) = shieldedField π c σ r G W :=
  funext (fun x => (shielded_gradient π c σ r G W hr hW x).gradient)

lemma admissible (p : LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.Params)
    (hp : LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.spec.valid p) {k : ℕ}
    (π : (Fin p.n × Fin (k + 1)) ↪ Fin p.d) (c σ r G W : ℝ)
    (hc : 0 ≤ c) (hσ : 0 < σ) (hr : 0 < r) (hG : 0 ≤ G) (hW : 0 < W)
    (hwidth : 64 * G ^ 2 ≤ W * p.L0) (hrad : 4 * G / r ≤ p.L0 / 3)
    (hgrad : (c / σ) * (1 + 2 * Real.sqrt (k + 1 : ℕ)) ≤ G)
    (hcurv : 12 * c / σ ^ 2 ≤ p.L0 / 3)
    (hzr : ‖minimizer π σ‖ ≤ r) (hzR : ‖minimizer π σ‖ ≤ p.R)
    (hgap : (k + 1 : ℕ) * c / 2 ≤ p.Δ) :
    LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.spec.admissible p
      (fun i => shielded (block π i) c σ r G W)
      (InterpolatedFiniteSumHiddenComponent.exactOracle p
        (fun i => shielded (block π i) c σ r G W)
        (fun i => shieldedField (block π i) c σ r G W)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, minimizer π σ, ?_, hzR, ?_⟩
  · exact fun i => shielded_convex (block π i) c σ r G W hc hr hG hW
  · intro i x
    rw [shielded_gradient_eq _ _ _ _ _ _ hr hW]
    exact shielded_gradient (block π i) c σ r G W hr hW x
  · intro i
    rw [shielded_gradient_eq _ _ _ _ _ _ hr hW]
    exact shieldedField_differentiable (block π i) c σ r G W hr
  · intro i x
    rw [shielded_gradient_eq _ _ _ _ _ _ hr hW]
    exact (shieldedField_curvature (block π i) c σ r G W p.L0 hc hσ hr hG hW hp.1.le
      hwidth hrad hgrad hcurv x).trans
      (le_add_of_nonneg_right (mul_nonneg hp.2.1 (norm_nonneg _)))
  · intro history seed i x
    simp only [InterpolatedFiniteSumHiddenComponent.exactOracle,
      shielded_gradient_eq _ _ _ _ _ _ hr hW]
  · intro i
    exact shielded_minimizer π c σ r G W hc hσ hr hG hW hzr i
  · have hn : (p.n : ℝ) ≠ 0 := by
      have hh : 0 < p.n := by have := hp.2.2.2.2.1; omega
      exact_mod_cast ne_of_gt hh
    simpa only [id_eq, LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.objective,
      shielded_zero _ _ _ _ _ _ hc hr hG hW,
      shielded_minimizer_value π c σ r G W hc hσ hr hG hW hzr,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_zero, sub_zero, ← mul_assoc, inv_mul_cancel₀ hn, one_mul] using hgap

lemma shifted_prefix_lower {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ θ : ℝ)
    (hc : 0 ≤ c) (hσ : 0 < σ) (hθ : 0 ≤ θ) (ℓ : ℕ) (hℓ : ℓ ≤ k + 1)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ j : Fin (k + 1), ℓ ≤ j.val → |x (π j)| ≤ θ) :
    (k + 1 : ℕ) * c / 2 - c * ℓ / 2 - c * θ / σ ≤ shifted π c σ x := by
  by_cases hlt : ℓ < k + 1
  · have hy : extended (coordinateMap π x) ℓ ≤ θ := by
      have hh := (abs_le.mp (hx ⟨ℓ, hlt⟩ le_rfl)).2
      simpa [extended, hlt, coordinateMap] using hh
    have h := sequence_prefix_gap c σ hc hσ (k + 1) ℓ hℓ
      (extended (coordinateMap π x)) θ hy
    rw [shifted, rawChain, selected_sequence]
    nlinarith only [h]
  · have he : ℓ = k + 1 := by omega
    subst ℓ
    have h := shifted_nonnegative π c σ hc x
    have hp : 0 ≤ c * θ / σ := by positivity
    nlinarith only [h, hp]

lemma shielded_far_lower {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ r G W B : ℝ)
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hG : 0 < G) (hW : 0 < W)
    (hB : 4 * r + ((k + 1 : ℕ) * c / 2 + W) / G ≤ B)
    (x : EuclideanSpace ℝ (Fin d)) (hx : B ≤ ‖x‖) :
    (k + 1 : ℕ) * c / 2 ≤ shielded π c σ r G W x := by
  have hh : (k + 1 : ℕ) * c / 2 + W ≤ (B - 4 * r) * G := by
    apply (div_le_iff₀ hG).mp
    linarith only [hB]
  have hs := (radiusNorm_ge r x).2
  have hw := (InterpolatedFiniteSumProfiles.smoothMax_above W (shifted π c σ x)
    (radialWall r G 0 W x) hW).2
  change radialWall r G 0 W x ≤ shielded π c σ r G W x at hw
  dsimp [radialWall] at hw
  have hGr := mul_nonneg hG.le hr
  have htc : 0 ≤ ((k + 1 : ℕ) : ℝ) * c := mul_nonneg (Nat.cast_nonneg _) hc
  have hnorm := mul_le_mul_of_nonneg_left (hx.trans hs) hG.le
  nlinarith only [hh, hw, hGr, htc, hW, hnorm]

lemma shielded_output_lower {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ r G W B θ : ℝ)
    (hc : 0 ≤ c) (hσ : 0 < σ) (hr : 0 ≤ r) (hG : 0 < G) (hW : 0 < W) (hθ : 0 ≤ θ)
    (hB : 4 * r + ((k + 1 : ℕ) * c / 2 + W) / G ≤ B)
    (ℓ : ℕ) (hℓ : ℓ ≤ k + 1) (x : EuclideanSpace ℝ (Fin d))
    (hx : ‖x‖ ≤ B → ∀ j : Fin (k + 1), ℓ ≤ j.val → |x (π j)| ≤ θ) :
    (k + 1 : ℕ) * c / 2 - c * ℓ / 2 - c * θ / σ ≤ shielded π c σ r G W x := by
  by_cases hn : ‖x‖ ≤ B
  · exact (shifted_prefix_lower π c σ θ hc hσ hθ ℓ hℓ x (hx hn)).trans
      (InterpolatedFiniteSumProfiles.smoothMax_above W (shifted π c σ x)
        (radialWall r G 0 W x) hW).1
  · have h := shielded_far_lower π c σ r G W B hc hr hG hW hB x (lt_of_not_ge hn).le
    have h₁ : 0 ≤ c * ℓ / 2 := by positivity
    have h₂ : 0 ≤ c * θ / σ := by positivity
    linarith only [h, h₁, h₂]

lemma shieldedField_norm {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ r G W : ℝ)
    (hc : 0 ≤ c) (hσ : 0 < σ) (hr : 0 < r) (hG : 0 ≤ G)
    (hgrad : (c / σ) * (1 + 2 * Real.sqrt (k + 1 : ℕ)) ≤ G)
    (x : EuclideanSpace ℝ (Fin d)) : ‖shieldedField π c σ r G W x‖ ≤ 2 * G := by
  apply envelopeField_norm
  · exact ((rawField_norm π c σ hc hσ x).trans hgrad).trans (by linarith)
  · exact radialField_norm r G hr hG x

end LongTails.Proofs.InterpolatedFiniteSumBlocks
