import LongTails.Proofs.SlidingWireSplit
import LongTails.Proofs.GdConvex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SlidingWireConvex

open LongTails.Proofs.SlidingLowerChain (Point)

open SlidingWireChain SlidingWireGeometry SlidingWireLocal SlidingWireSplit
open FrontierChainProfiles FrontierChain SmoothConvexFiniteGeometry SmoothConvexFiniteWall
open Classical

variable {d : ℕ}

lemma gate_lower {T : ℕ} (π : Fin (2 * T + 1) ↪ Fin d) (u v : Point d) :
    SlidingLowerChain.gateObj π u + ⟪SlidingLowerChain.gateField π u, v - u⟫ - 265 * ‖v - u‖ ^ 2 ≤
      SlidingLowerChain.gateObj π v := by
  have hg : ∀ z, HasGradientAt (fun z => -SlidingLowerChain.gateObj π z)
      (-SlidingLowerChain.gateField π z) z := fun z => SlidingLowerChain.grad_neg (SlidingLowerChain.gateObj_gradient π z)
  have hl : ∀ a b : Point d, ‖-SlidingLowerChain.gateField π a - -SlidingLowerChain.gateField π b‖ ≤
      530 * ‖a - b‖ := by
    intro a b
    rw [neg_sub_neg, norm_sub_rev]
    exact SlidingLowerChain.gateField_lipschitz π a b
  have h := OracleTemplate.Gradient.smooth_upper_bound hg hl u v
  rw [inner_neg_left] at h
  linarith

lemma linkL_split (r : ℕ) (δ : ℝ) (l : ℕ) (s t : ℝ) :
    linkL r δ l s t = (if phase r l = r ^ 2 + 1 then edgeLeft s t else 0) +
      (if phase r l = r ^ 2 + 1 then 0 else cA r l * spS δ (stretch r l s t)) := by
  unfold linkL; split_ifs <;> simp

lemma linkR_split (r : ℕ) (δ : ℝ) (l : ℕ) (s t : ℝ) :
    linkR r δ l s t = (if phase r l = r ^ 2 + 1 then edgeRight s t else 0) +
      (if phase r l = r ^ 2 + 1 then 0 else cB r l * spS δ (stretch r l s t)) := by
  unfold linkR; split_ifs <;> simp

lemma spring_term (r : ℕ) (δ : ℝ) (l : ℕ) (s t s' t' : ℝ) :
    0 ≤ (if phase r l = r ^ 2 + 1 then 0 else sp δ (stretch r l s' t')) -
      (if phase r l = r ^ 2 + 1 then 0 else sp δ (stretch r l s t)) -
      ((if phase r l = r ^ 2 + 1 then 0 else cA r l * spS δ (stretch r l s t)) * (s' - s) +
        (if phase r l = r ^ 2 + 1 then 0 else cB r l * spS δ (stretch r l s t)) * (t' - t)) := by
  split_ifs
  · simp
  · have h := (sp_model δ (stretch r l s t) (stretch r l s' t')).1
    have e : stretch r l s' t' - stretch r l s t = cA r l * (s' - s) + cB r l * (t' - t) := by
      unfold stretch; ring
    rw [e] at h
    nlinarith

lemma obj_weak (r : ℕ) (δ : ℝ) {T : ℕ} (π : Fin (T * (r ^ 2 + 2) + 1) ↪ Fin d) (u v : Point d) :
    obj r δ π u + ⟪field r δ π u, v - u⟫ - 265 * ‖v - u‖ ^ 2 ≤ obj r δ π v := by
  set π' := (gEmb r T).trans π
  have hgate := gate_lower π' u v
  have hgin : ⟪SlidingLowerChain.gateField π' u, v - u⟫ =
      -potentialSlope (u (π 0)) * (v (π 0) - u (π 0)) +
        ∑ i : Fin T, (edgeLeft (u (π (gateLink r T i).castSucc)) (u (π (gateLink r T i).succ)) *
            (v (π (gateLink r T i).castSucc) - u (π (gateLink r T i).castSucc)) +
          edgeRight (u (π (gateLink r T i).castSucc)) (u (π (gateLink r T i).succ)) *
            (v (π (gateLink r T i).succ) - u (π (gateLink r T i).succ))) := by
    unfold SlidingLowerChain.gateField
    rw [inner_add_left, sum_inner]
    simp only [π', Function.Embedding.trans_apply, gate_pos_z, gate_pos_x, gate_pos_0,
      inner_neg_left, inner_smul_left, EuclideanSpace.inner_single_left, conj_trivial,
      one_mul, PiLp.sub_apply, edgeField, inner_add_left]
    ring_nf
  have hobj : SlidingLowerChain.gateObj π' v =
      -potential (v (π 0)) + ∑ i : Fin T,
        edge (v (π (gateLink r T i).castSucc)) (v (π (gateLink r T i).succ)) := by
    unfold SlidingLowerChain.gateObj
    simp only [π', Function.Embedding.trans_apply, gate_pos_z, gate_pos_x, gate_pos_0]
  have hobju : SlidingLowerChain.gateObj π' u =
      -potential (u (π 0)) + ∑ i : Fin T,
        edge (u (π (gateLink r T i).castSucc)) (u (π (gateLink r T i).succ)) := by
    unfold SlidingLowerChain.gateObj
    simp only [π', Function.Embedding.trans_apply, gate_pos_z, gate_pos_x, gate_pos_0]
  rw [hgin, hobj, hobju] at hgate
  have hinner := field_inner r δ π u (v - u)
  simp only [PiLp.sub_apply] at hinner
  have hspring : 0 ≤ ∑ l : Fin (T * (r ^ 2 + 2)),
      ((if phase r l.val = r ^ 2 + 1 then 0 else sp δ (stretch r l.val (v (π l.castSucc)) (v (π l.succ)))) -
      (if phase r l.val = r ^ 2 + 1 then 0 else sp δ (stretch r l.val (u (π l.castSucc)) (u (π l.succ)))) -
      ((if phase r l.val = r ^ 2 + 1 then 0 else
          cA r l.val * spS δ (stretch r l.val (u (π l.castSucc)) (u (π l.succ)))) *
          (v (π l.castSucc) - u (π l.castSucc)) +
        (if phase r l.val = r ^ 2 + 1 then 0 else
          cB r l.val * spS δ (stretch r l.val (u (π l.castSucc)) (u (π l.succ)))) *
          (v (π l.succ) - u (π l.succ)))) :=
    Finset.sum_nonneg (fun l _ => spring_term r δ l.val _ _ _ _)
  have hgsum := gate_sum (M := ℝ) r T (fun l =>
      edge (v (π l.castSucc)) (v (π l.succ)) - edge (u (π l.castSucc)) (u (π l.succ)) -
        (edgeLeft (u (π l.castSucc)) (u (π l.succ)) * (v (π l.castSucc) - u (π l.castSucc)) +
          edgeRight (u (π l.castSucc)) (u (π l.succ)) * (v (π l.succ) - u (π l.succ))))
  have hdecomp : obj r δ π v - obj r δ π u - ⟪field r δ π u, v - u⟫ =
      (-potential (v (π 0)) + potential (u (π 0)) + potentialSlope (u (π 0)) * (v (π 0) - u (π 0))) +
      ∑ l : Fin (T * (r ^ 2 + 2)), (if phase r l.val = r ^ 2 + 1 then
        (edge (v (π l.castSucc)) (v (π l.succ)) - edge (u (π l.castSucc)) (u (π l.succ)) -
          (edgeLeft (u (π l.castSucc)) (u (π l.succ)) * (v (π l.castSucc) - u (π l.castSucc)) +
            edgeRight (u (π l.castSucc)) (u (π l.succ)) * (v (π l.succ) - u (π l.succ)))) else 0) +
      ∑ l : Fin (T * (r ^ 2 + 2)),
      ((if phase r l.val = r ^ 2 + 1 then 0 else sp δ (stretch r l.val (v (π l.castSucc)) (v (π l.succ)))) -
      (if phase r l.val = r ^ 2 + 1 then 0 else sp δ (stretch r l.val (u (π l.castSucc)) (u (π l.succ)))) -
      ((if phase r l.val = r ^ 2 + 1 then 0 else
          cA r l.val * spS δ (stretch r l.val (u (π l.castSucc)) (u (π l.succ)))) *
          (v (π l.castSucc) - u (π l.castSucc)) +
        (if phase r l.val = r ^ 2 + 1 then 0 else
          cB r l.val * spS δ (stretch r l.val (u (π l.castSucc)) (u (π l.succ)))) *
          (v (π l.succ) - u (π l.succ)))) := by
    rw [hinner]
    unfold obj
    have hterm : ∀ l : Fin (T * (r ^ 2 + 2)),
        link r δ l.val (v (π l.castSucc)) (v (π l.succ)) - link r δ l.val (u (π l.castSucc)) (u (π l.succ)) -
          (linkL r δ l.val (u (π l.castSucc)) (u (π l.succ)) * (v (π l.castSucc) - u (π l.castSucc)) +
            linkR r δ l.val (u (π l.castSucc)) (u (π l.succ)) * (v (π l.succ) - u (π l.succ))) =
        (if phase r l.val = r ^ 2 + 1 then
          (edge (v (π l.castSucc)) (v (π l.succ)) - edge (u (π l.castSucc)) (u (π l.succ)) -
            (edgeLeft (u (π l.castSucc)) (u (π l.succ)) * (v (π l.castSucc) - u (π l.castSucc)) +
              edgeRight (u (π l.castSucc)) (u (π l.succ)) * (v (π l.succ) - u (π l.succ)))) else 0) +
        ((if phase r l.val = r ^ 2 + 1 then 0 else sp δ (stretch r l.val (v (π l.castSucc)) (v (π l.succ)))) -
        (if phase r l.val = r ^ 2 + 1 then 0 else sp δ (stretch r l.val (u (π l.castSucc)) (u (π l.succ)))) -
        ((if phase r l.val = r ^ 2 + 1 then 0 else
            cA r l.val * spS δ (stretch r l.val (u (π l.castSucc)) (u (π l.succ)))) *
            (v (π l.castSucc) - u (π l.castSucc)) +
          (if phase r l.val = r ^ 2 + 1 then 0 else
            cB r l.val * spS δ (stretch r l.val (u (π l.castSucc)) (u (π l.succ)))) *
            (v (π l.succ) - u (π l.succ)))) := by
      intro l
      unfold link linkL linkR
      split_ifs <;> ring
    have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin (T * (r ^ 2 + 2)))) = _)
      (fun l (_ : l ∈ Finset.univ) => hterm l)
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum
    linarith [hsum]
  rw [hgsum] at hdecomp
  have hsplit : ∑ i : Fin T, (edge (v (π (gateLink r T i).castSucc)) (v (π (gateLink r T i).succ)) -
      edge (u (π (gateLink r T i).castSucc)) (u (π (gateLink r T i).succ)) -
      (edgeLeft (u (π (gateLink r T i).castSucc)) (u (π (gateLink r T i).succ)) *
          (v (π (gateLink r T i).castSucc) - u (π (gateLink r T i).castSucc)) +
        edgeRight (u (π (gateLink r T i).castSucc)) (u (π (gateLink r T i).succ)) *
          (v (π (gateLink r T i).succ) - u (π (gateLink r T i).succ)))) =
      ∑ i : Fin T, edge (v (π (gateLink r T i).castSucc)) (v (π (gateLink r T i).succ)) -
      ∑ i : Fin T, edge (u (π (gateLink r T i).castSucc)) (u (π (gateLink r T i).succ)) -
      ∑ i : Fin T, (edgeLeft (u (π (gateLink r T i).castSucc)) (u (π (gateLink r T i).succ)) *
          (v (π (gateLink r T i).castSucc) - u (π (gateLink r T i).castSucc)) +
        edgeRight (u (π (gateLink r T i).castSucc)) (u (π (gateLink r T i).succ)) *
          (v (π (gateLink r T i).succ) - u (π (gateLink r T i).succ))) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  linarith [hgate, hsplit, hspring, hdecomp]

lemma wF_weak (r : ℕ) (δ : ℝ) {R Λ : ℝ} (hR : 0 < R) (hΛ : 1 ≤ Λ) {T : ℕ}
    (π : Fin (T * (r ^ 2 + 2) + 1) ↪ Fin d) (u v : Point d) :
    wF r δ R Λ π u + ⟪wG r δ R Λ π u, v - u⟫ - 265 * ‖v - u‖ ^ 2 ≤ wF r δ R Λ π v := by
  have hs := smoothMax_support (R ^ 2) (obj r δ π u / Λ) (wall R u) (obj r δ π v / Λ) (wall R v)
    (by positivity)
  have ho := obj_weak r δ π u v
  have hw : wall R v - wall R u ≥ ⟪(4 : ℝ) • u, v - u⟫ := by
    unfold wall
    rw [real_inner_smul_left]
    have e : ‖v‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, v - u⟫ + ‖v - u‖ ^ 2 := by
      have : v = u + (v - u) := by abel
      conv_lhs => rw [this]
      rw [norm_add_sq_real]
    nlinarith [sq_nonneg ‖v - u‖]
  set lw := weight (R ^ 2) (obj r δ π u / Λ) (wall R u)
  have hlw0 : 0 ≤ lw := weight_nonneg _ _ _
  have hlw1 : lw ≤ 1 := weight_le_one _ _ _
  have hΛ0 : 0 < Λ := by linarith
  unfold wF wG localized
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left]
  have h1 : obj r δ π v / Λ - obj r δ π u / Λ ≥
      (⟪field r δ π u, v - u⟫ - 265 * ‖v - u‖ ^ 2) / Λ := by
    rw [← sub_div]; apply div_le_div_of_nonneg_right _ hΛ0.le; linarith
  have h2 : lw * (obj r δ π v / Λ - obj r δ π u / Λ) ≥
      lw * ((⟪field r δ π u, v - u⟫ - 265 * ‖v - u‖ ^ 2) / Λ) :=
    mul_le_mul_of_nonneg_left h1 hlw0
  have h3 : (1 - lw) * (wall R v - wall R u) ≥ (1 - lw) * ⟪(4 : ℝ) • u, v - u⟫ :=
    mul_le_mul_of_nonneg_left hw (by linarith)
  rw [real_inner_smul_left] at h3
  have h4 : Λ * (smoothMax (R ^ 2) (obj r δ π v / Λ) (wall R v) -
      smoothMax (R ^ 2) (obj r δ π u / Λ) (wall R u)) ≥
      lw * (⟪field r δ π u, v - u⟫ - 265 * ‖v - u‖ ^ 2) + (1 - lw) * (4 * Λ * ⟪u, v - u⟫) := by
    have := mul_le_mul_of_nonneg_left hs hΛ0.le
    have e : Λ * (lw * ((⟪field r δ π u, v - u⟫ - 265 * ‖v - u‖ ^ 2) / Λ)) =
        lw * (⟪field r δ π u, v - u⟫ - 265 * ‖v - u‖ ^ 2) := by field_simp
    nlinarith
  have h5 : lw * (265 * ‖v - u‖ ^ 2) ≤ 265 * ‖v - u‖ ^ 2 := by
    have := sq_nonneg ‖v - u‖
    nlinarith
  nlinarith

end LongTails.Proofs.SlidingWireConvex
