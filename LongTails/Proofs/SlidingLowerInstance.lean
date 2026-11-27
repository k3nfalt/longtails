import LongTails.Proofs.SlidingLowerObjective
import LongTails.Proofs.SlidingLowerMask
import LongTails.Proofs.SharpChainLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SlidingLowerInstance

open SlidingLowerChain SlidingLowerGeometry SlidingLowerObjective SlidingLowerMask
open SoftRadialProjection FrontierChainProfiles FrontierChain FrontierChainGeometry

variable {d T : ℕ}

noncomputable def kap (R : ℝ) (T : ℕ) : ℝ := 192 * Real.sqrt T / R

noncomputable def fbar (R : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) : ℝ :=
  gateObj π (project R w) + (1 / 20 - kap R T) / 2 * ‖w‖ ^ 2

noncomputable def hbar (R : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) : ℝ :=
  coupObj 8 π (project R w) + kap R T / 2 * ‖w‖ ^ 2

noncomputable def fgrad (R : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) : Point d :=
  derivative R w (gateField π (project R w)) + (1 / 20 - kap R T) • w

noncomputable def hgrad (R : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) : Point d :=
  derivative R w (coupField 8 π (project R w)) + kap R T • w

noncomputable def fpart (R : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (V : ℕ) (w : Point d) : Point d :=
  derivative R w (gateV π V (project R w)) + (1 / 20 - kap R T) • w

noncomputable def hpart (p R : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (V : ℕ) (b : Bool)
    (w : Point d) : Point d :=
  derivative R w (coupV p π V b (project R w)) + kap R T • w

lemma sq_gradient (c : ℝ) (w : Point d) :
    HasGradientAt (fun v : Point d => c / 2 * ‖v‖ ^ 2) (c • w) w := by
  have h := (hasStrictFDerivAt_norm_sq w).hasFDerivAt.const_mul (c / 2)
  rw [hasGradientAt_iff_hasFDerivAt]
  refine h.congr_fderiv ?_
  ext v
  simp [InnerProductSpace.toDual_apply_apply]
  ring

lemma fbar_gradient {R : ℝ} (hR : 0 < R) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) :
    HasGradientAt (fbar R π) (fgrad R π w) w :=
  grad_add (composition_gradient hR w (gateObj_gradient π (project R w))) (sq_gradient _ w)

lemma hbar_gradient {R : ℝ} (hR : 0 < R) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) :
    HasGradientAt (hbar R π) (hgrad R π w) w :=
  grad_add (composition_gradient hR w (coupObj_gradient 8 π (project R w))) (sq_gradient _ w)

lemma inner_single (j : Fin d) (v : Point d) :
    ⟪EuclideanSpace.single j (1 : ℝ), v⟫ = v j := by
  simp [EuclideanSpace.inner_single_left]

lemma coupObj_support (π : Fin (2 * T + 1) ↪ Fin d) (a b : Point d) :
    coupObj 8 π a + ⟪coupField 8 π a, b - a⟫ ≤ coupObj 8 π b := by
  unfold coupObj coupField
  rw [sum_inner, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  unfold coupTerm
  rw [inner_smul_left, inner_sub_left, inner_smul_left, inner_single, inner_single]
  simp only [conj_trivial, PiLp.sub_apply]
  have h := (hub_model (a (π (xi i.castSucc)) - a (π (zi i)) / 2)
    (b (π (xi i.castSucc)) - b (π (zi i)) / 2)).1
  nlinarith

lemma hbar_support {R : ℝ} (hR : 0 < R) (π : Fin (2 * T + 1) ↪ Fin d) (x y : Point d) :
    hbar R π x + ⟪hgrad R π x, y - x⟫ ≤ hbar R π y := by
  have h := compressed_support (R := R) (G := 16 * Real.sqrt T) hR (by positivity)
    (H := coupObj 8 π) (gH := coupField 8 π) (coupObj_support π)
    (fun a => by
      have := coupField_norm (by norm_num : (0 : ℝ) ≤ 8) π a
      linarith) x y
  have hk : kap R T / 2 = 6 * (16 * Real.sqrt T) / R := by unfold kap; ring
  have hk2 : kap R T = 12 * (16 * Real.sqrt T) / R := by unfold kap; ring
  unfold hbar hgrad
  rw [hk, hk2]
  exact h

lemma hbar_convex {R : ℝ} (hR : 0 < R) (π : Fin (2 * T + 1) ↪ Fin d) :
    ConvexOn ℝ Set.univ (hbar R π) :=
  LongTails.Proofs.SharpChainLowerBound.convexOn_of_subgradient _ (hgrad R π) (hbar_support hR π)

lemma radius_facts {R : ℝ} (hR : 5280 * (1 + Real.sqrt T) ≤ R) :
    0 < R ∧ kap R T ≤ 1 / 25 ∧ 0 ≤ kap R T ∧ 6 * (1 + 17 * Real.sqrt T) / R ≤ 1 / 10 ∧
      6 * (16 * Real.sqrt T) / R ≤ 1 / 10 := by
  have hs := Real.sqrt_nonneg (T : ℝ)
  have hR0 : 0 < R := by nlinarith
  refine ⟨hR0, ?_, by unfold kap; positivity, ?_, ?_⟩
  · unfold kap
    rw [div_le_iff₀ hR0]
    nlinarith
  · rw [div_le_iff₀ hR0]
    nlinarith
  · rw [div_le_iff₀ hR0]
    nlinarith

lemma fgrad_lipschitz {R : ℝ} (hR : 5280 * (1 + Real.sqrt T) ≤ R)
    (π : Fin (2 * T + 1) ↪ Fin d) (x y : Point d) :
    ‖fgrad R π x - fgrad R π y‖ ≤ 2200 * ‖x - y‖ := by
  obtain ⟨hR0, hk1, hk0, hg, _⟩ := radius_facts hR
  have h1 := composition_field_lipschitz (R := R) (L := 530) (G := 1 + 17 * Real.sqrt T) hR0
    (by norm_num) (gateField π) (gateField_norm π) (gateField_lipschitz π) x y
  have e : fgrad R π x - fgrad R π y =
      (derivative R x (gateField π (project R x)) - derivative R y (gateField π (project R y))) +
        (1 / 20 - kap R T) • (x - y) := by
    unfold fgrad; rw [smul_sub]; abel
  rw [e]
  have h2 : ‖(1 / 20 - kap R T) • (x - y)‖ ≤ 1 / 10 * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [abs_le]; constructor <;> linarith
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (4 * 530 + 6 * (1 + 17 * Real.sqrt T) / R) * ‖x - y‖ + 1 / 10 * ‖x - y‖ :=
        add_le_add h1 h2
    _ ≤ _ := by nlinarith [norm_nonneg (x - y)]

lemma hgrad_lipschitz {R : ℝ} (hR : 5280 * (1 + Real.sqrt T) ≤ R)
    (π : Fin (2 * T + 1) ↪ Fin d) (x y : Point d) :
    ‖hgrad R π x - hgrad R π y‖ ≤ 2200 * ‖x - y‖ := by
  obtain ⟨hR0, hk1, hk0, _, hg⟩ := radius_facts hR
  have h1 := composition_field_lipschitz (R := R) (L := 96) (G := 16 * Real.sqrt T) hR0
    (by norm_num) (coupField 8 π)
    (fun a => by have := coupField_norm (by norm_num : (0 : ℝ) ≤ 8) π a; linarith)
    (coupField_lipschitz π) x y
  have e : hgrad R π x - hgrad R π y =
      (derivative R x (coupField 8 π (project R x)) -
        derivative R y (coupField 8 π (project R y))) + kap R T • (x - y) := by
    unfold hgrad; rw [smul_sub]; abel
  rw [e]
  have h2 : ‖kap R T • (x - y)‖ ≤ 1 / 10 * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk0]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    linarith
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (4 * 96 + 6 * (16 * Real.sqrt T) / R) * ‖x - y‖ + 1 / 10 * ‖x - y‖ :=
        add_le_add h1 h2
    _ ≤ _ := by nlinarith [norm_nonneg (x - y)]

lemma total_gradient (R : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) :
    fgrad R π w + hgrad R π w = totalField R (1 / 20) π w := by
  unfold fgrad hgrad totalField chainField
  rw [map_add]
  module

lemma project_zero (R : ℝ) : project R (0 : Point d) = 0 := by
  simp [project]

lemma gateObj_zero (π : Fin (2 * T + 1) ↪ Fin d) : gateObj π 0 = -potential 0 := by
  unfold gateObj
  simp only [PiLp.zero_apply]
  rw [Finset.sum_eq_zero (fun i _ => (edge_flat (by norm_num)).1)]
  ring

lemma coupObj_zero (π : Fin (2 * T + 1) ↪ Fin d) : coupObj 8 π 0 = 0 := by
  unfold coupObj
  simp [hub_zero]

lemma gateObj_lower (π : Fin (2 * T + 1) ↪ Fin d) (u : Point d) : -4 - 4 * T ≤ gateObj π u := by
  unfold gateObj
  have h0 := (potential_bounds (u (π (xi 0)))).2
  have hs : -(4 * (T : ℝ)) ≤ ∑ i : Fin T, edge (u (π (zi i))) (u (π (xi i.succ))) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin T))) =>
      (edge_bounds (u (π (zi i))) (u (π (xi i.succ)))).1)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  linarith

lemma coupObj_nonneg (π : Fin (2 * T + 1) ↪ Fin d) (u : Point d) : 0 ≤ coupObj 8 π u := by
  unfold coupObj
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => hub_nonneg _))

lemma gap_bound (R : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) :
    fbar R π 0 + hbar R π 0 - (fbar R π w + hbar R π w) ≤ 4 + 4 * T := by
  unfold fbar hbar
  rw [project_zero, gateObj_zero, coupObj_zero]
  have h1 := gateObj_lower π (project R w)
  have h2 := coupObj_nonneg π (project R w)
  have h3 := (potential_bounds 0).1
  have h4 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  have e : (1 / 20 - kap R T) / 2 * ‖w‖ ^ 2 + kap R T / 2 * ‖w‖ ^ 2 = 1 / 40 * ‖w‖ ^ 2 := by ring
  simp only [norm_zero]
  nlinarith

end LongTails.Proofs.SlidingLowerInstance
