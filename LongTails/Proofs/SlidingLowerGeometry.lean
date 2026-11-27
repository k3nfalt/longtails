import LongTails.Proofs.SlidingLowerChain
import LongTails.Proofs.FrontierChainWall

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SlidingLowerGeometry

open SmoothConvexFiniteGeometry FrontierChainProfiles FrontierChain FrontierChainGeometry
open SlidingLowerChain SoftRadialProjection FrontierChainWall

variable {d T : ℕ}

lemma scatter_apply_ne {m : ℕ} (π : Fin m ↪ Fin d) (c : Fin m → ℝ) (a : Fin d)
    (h : ∀ i, π i ≠ a) : scatter π c a = 0 := by
  unfold scatter
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  simp [Ne.symm (h i)]

lemma xi_ne_zi (j : Fin (T + 1)) (i : Fin T) : xi j ≠ zi i := by
  intro h
  simp only [xi, zi, Fin.mk.injEq] at h
  omega

lemma single_apply_ne (a b : Fin d) (h : a ≠ b) :
    (EuclideanSpace.single a (1 : ℝ) : Point d) b = 0 := by
  simp [Ne.symm h]

noncomputable def chainField (γ : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (q : Point d) : Point d :=
  gateField π q + coupField γ π q

lemma emb_ne {a b : Fin (2 * T + 1)} (π : Fin (2 * T + 1) ↪ Fin d) (h : a ≠ b) : π a ≠ π b :=
  π.injective.ne h

lemma field_x0 (γ : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (q : Point d) :
    chainField γ π q (π (xi 0)) = -potentialSlope (q (π (xi 0))) +
      (if h : 0 < T then γ * hubSlope (q (π (xi 0)) - q (π (zi ⟨0, h⟩)) / 2) else 0) := by
  unfold chainField
  rw [gateField_eq, coupField_eq]
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  have hz : ∀ i : Fin T, (zEmb.trans π) i ≠ π (xi 0) := fun i =>
    emb_ne π (Ne.symm (xi_ne_zi 0 i))
  have hx : ∀ i : Fin T, (xNext.trans π) i ≠ π (xi 0) := fun i => emb_ne π (by
    simp [xNext, xEmb, xi, Fin.ext_iff])
  rw [scatter_apply_ne _ _ _ hz, scatter_apply_ne _ _ _ hx, scatter_apply_ne _ _ _ hz]
  simp only [esingle_apply, ite_true, mul_one, add_zero, sub_zero]
  by_cases hT : 0 < T
  · rw [dite_eq_left hT]
    have he : (xPrev.trans π) ⟨0, hT⟩ = π (xi 0) := by
      simp [xPrev, xEmb, xi]
    rw [← he, scatter_apply]
    simp [xi, zi, xPrev, xEmb]
  · rw [dite_eq_right hT]
    have hx2 : ∀ i : Fin T, (xPrev.trans π) i ≠ π (xi 0) := fun i => absurd i.isLt (by omega)
    rw [scatter_apply_ne _ _ _ hx2]

lemma field_xs (γ : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (q : Point d) (i : Fin T) :
    chainField γ π q (π (xi i.succ)) = edgeRight (q (π (zi i))) (q (π (xi i.succ))) +
      (if h : i.val + 1 < T then
        γ * hubSlope (q (π (xi i.succ)) - q (π (zi ⟨i.val + 1, h⟩)) / 2) else 0) := by
  unfold chainField
  rw [gateField_eq, coupField_eq]
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  have h0 : π (xi 0) ≠ π (xi i.succ) := emb_ne π (by
    simp only [xi, ne_eq, Fin.mk.injEq, Fin.val_zero, Fin.val_succ]; omega)
  have hz : ∀ j : Fin T, (zEmb.trans π) j ≠ π (xi i.succ) := fun j =>
    emb_ne π (Ne.symm (xi_ne_zi i.succ j))
  have hxn : (xNext.trans π) i = π (xi i.succ) := rfl
  rw [scatter_apply_ne _ _ _ hz, scatter_apply_ne _ _ _ hz, ← hxn, scatter_apply]
  rw [hxn, esingle_apply, ite_eq_right (Ne.symm h0)]
  by_cases hT : i.val + 1 < T
  · rw [dite_eq_left hT]
    have he : (xPrev.trans π) ⟨i.val + 1, hT⟩ = π (xi i.succ) := by
      simp [xPrev, xEmb, xi]
    rw [← he, scatter_apply]
    simp only [xPrev, xEmb, Function.Embedding.trans_apply, Fin.castSuccEmb_apply,
      Function.Embedding.coeFn_mk] at he ⊢
    have hc : xi (Fin.castSucc (⟨i.val + 1, hT⟩ : Fin T)) = xi i.succ := by
      simp [xi]
    rw [hc]
    ring
  · rw [dite_eq_right hT]
    have hx2 : ∀ j : Fin T, (xPrev.trans π) j ≠ π (xi i.succ) := fun j => emb_ne π (by
      simp only [xPrev, xEmb, Function.Embedding.trans_apply, Fin.castSuccEmb_apply,
        Function.Embedding.coeFn_mk, xi, ne_eq, Fin.mk.injEq, Fin.val_castSucc, Fin.val_succ]
      omega)
    rw [scatter_apply_ne _ _ _ hx2]
    ring

lemma field_z (γ : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (q : Point d) (i : Fin T) :
    chainField γ π q (π (zi i)) = edgeLeft (q (π (zi i))) (q (π (xi i.succ))) -
      (1 / 2) * (γ * hubSlope (q (π (xi i.castSucc)) - q (π (zi i)) / 2)) := by
  unfold chainField
  rw [gateField_eq, coupField_eq]
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  have h0 : π (xi 0) ≠ π (zi i) := emb_ne π (xi_ne_zi 0 i)
  have hx : ∀ j : Fin T, (xNext.trans π) j ≠ π (zi i) := fun j => emb_ne π (xi_ne_zi j.succ i)
  have hx2 : ∀ j : Fin T, (xPrev.trans π) j ≠ π (zi i) := fun j =>
    emb_ne π (xi_ne_zi j.castSucc i)
  have hzn : (zEmb.trans π) i = π (zi i) := rfl
  rw [scatter_apply_ne _ _ _ hx, scatter_apply_ne _ _ _ hx2, ← hzn, scatter_apply,
    scatter_apply, hzn, esingle_apply, ite_eq_right (Ne.symm h0)]
  ring

lemma gate_part_bounds_x0 (q : Point d) (π : Fin (2 * T + 1) ↪ Fin d) :
    -1 ≤ -potentialSlope (q (π (xi 0))) ∧ -potentialSlope (q (π (xi 0))) ≤ 0 := by
  have := potentialSlope_bounds (q (π (xi 0)))
  constructor <;> linarith [this.1, this.2]

lemma chain_deficient (π : Fin (2 * T + 1) ↪ Fin d) (q : Point d)
    (htail : |q (π (xi (Fin.last T)))| < 1) :
    (∃ a b : Fin d, a ≠ b ∧ |q a| < 1 ∧ |q b| < 1 ∧
        chainField 8 π q a + 2 * chainField 8 π q b ≤ -1) ∨
      (∃ a : Fin d, 1 ≤ |q a| ∧ (1 ≤ q a → 1 ≤ chainField 8 π q a) ∧
        (q a ≤ -1 → chainField 8 π q a ≤ -1)) ∨
      (∃ a : Fin d, |q a| < 1 ∧ chainField 8 π q a ≤ -1) := by
  classical
  by_cases hex : ∃ n, ∃ h : n < T, |q (π (zi ⟨n, h⟩))| < 1
  · let n := Nat.find hex
    obtain ⟨hn, hsmall⟩ := Nat.find_spec hex
    have hmin : ∀ m < n, ∀ h : m < T, 1 ≤ |q (π (zi ⟨m, h⟩))| := by
      intro m hm h
      by_contra hc
      exact Nat.find_min hex hm ⟨h, lt_of_not_ge hc⟩
    set i : Fin T := ⟨n, hn⟩ with hi
    set v := π (xi i.castSucc)
    set z := π (zi i)
    have hvz : v ≠ z := emb_ne π (xi_ne_zi _ _)
    obtain ⟨P, hgv, hP0, hP1, hPeq⟩ : ∃ P : ℝ,
        chainField 8 π q v = P + 8 * hubSlope (q v - q z / 2) ∧ -1 ≤ P ∧ P ≤ 0 ∧
          (|q v| ≤ 1 → P = -1) := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · have hv0 : v = π (xi 0) := by simp [v, xi, i, h0]
        have hz0 : zi (⟨0, by omega⟩ : Fin T) = zi i := by simp [zi, i, h0]
        refine ⟨-potentialSlope (q (π (xi 0))), ?_, (gate_part_bounds_x0 q π).1,
          (gate_part_bounds_x0 q π).2, ?_⟩
        · rw [hv0, field_x0, dite_eq_left (by omega)]
          congr 3
          · rw [hz0]
        · intro hv
          rw [hv0] at hv
          rw [potentialSlope_one hv]
      · obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        set j : Fin T := ⟨m, by omega⟩
        have hvj : v = π (xi j.succ) := by simp [v, xi, i, j, hm]
        have hzj : zi (⟨m + 1, by omega⟩ : Fin T) = zi i := by simp [zi, i, hm]
        have hlarge := hmin m (by omega) (by omega)
        refine ⟨edgeRight (q (π (zi j))) (q (π (xi j.succ))), ?_,
          (edgeRight_bounds _ _).1, (edgeRight_bounds _ _).2, ?_⟩
        · rw [hvj, field_xs, dite_eq_left (show (j : ℕ) + 1 < T from by
            rw [show (j : ℕ) = m from rfl]; omega)]
          congr 3
          · rw [hzj]
        · intro hv
          rw [hvj] at hv
          exact edgeRight_large hlarge hv
    have hgz : chainField 8 π q z = edgeLeft (q z) (q (π (xi i.succ))) -
        (1 / 2) * (8 * hubSlope (q v - q z / 2)) := field_z 8 π q i
    by_cases hv : |q v| < 1
    · left
      refine ⟨v, z, hvz, hv, hsmall, ?_⟩
      have hP := hPeq hv.le
      have hl := (edgeLeft_bounds (q z) (q (π (xi i.succ)))).2
      rw [hgv, hgz, hP]
      linarith
    · right; left
      refine ⟨v, le_of_not_gt hv, ?_, ?_⟩
      · intro h1
        have hzs := (abs_lt.mp hsmall)
        have hs := hubSlope_ge (t := q v - q z / 2) (by linarith [hzs.2])
        rw [hgv]
        linarith
      · intro h1
        have hzs := (abs_lt.mp hsmall)
        have hs := hubSlope_le (t := q v - q z / 2) (by linarith [hzs.1])
        rw [hgv]
        linarith
  · right; right
    push Not at hex
    refine ⟨π (xi (Fin.last T)), htail, ?_⟩
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT
      have hl : (Fin.last 0 : Fin (0 + 1)) = 0 := rfl
      rw [hl, field_x0, dite_eq_right (by omega)]
      rw [hl] at htail
      rw [potentialSlope_one htail.le]
      norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, T = m + 1 := ⟨T - 1, by omega⟩
      have hlast : (Fin.last (m + 1) : Fin (m + 1 + 1)) = (Fin.last m).succ := rfl
      rw [hlast, field_xs, dite_eq_right (by simp)]
      rw [hlast] at htail
      have hz := hex m (by omega)
      have hz' : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
      rw [hz'] at hz
      rw [edgeRight_large hz htail.le]
      norm_num

lemma chainField_norm (π : Fin (2 * T + 1) ↪ Fin d) (q : Point d) :
    ‖chainField 8 π q‖ ≤ 1 + 33 * Real.sqrt T := by
  unfold chainField
  calc _ ≤ ‖gateField π q‖ + ‖coupField 8 π q‖ := norm_add_le _ _
    _ ≤ (1 + 17 * Real.sqrt T) + 2 * 8 * Real.sqrt T :=
        add_le_add (gateField_norm π q) (coupField_norm (by norm_num) π q)
    _ = _ := by ring

noncomputable def totalField (R η : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) : Point d :=
  derivative R w (chainField 8 π (project R w)) + η • w

lemma component_formula (R η : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) (a : Fin d) :
    totalField R η π w a = (scale R w)⁻¹ * chainField 8 π (project R w) a +
      (η - ⟪w, chainField 8 π (project R w)⟫ / (R ^ 2 * scale R w ^ 3)) *
        (scale R w * project R w a) := by
  rw [← coordinate_scale R w a]
  simp only [totalField, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, derivative_apply,
    PiLp.sub_apply]
  ring

lemma total_lower (π : Fin (2 * T + 1) ↪ Fin d) {R : ℝ}
    (hR : 80 * (2 * (1 + 33 * Real.sqrt T) + 1) ≤ R) (w : Point d)
    (htail : |project R w (π (xi (Fin.last T)))| < 1) :
    1 / 6 ≤ ‖totalField R (1 / 20) π w‖ := by
  set G := 1 + 33 * Real.sqrt T with hG
  have hG1 : 1 ≤ G := by have := Real.sqrt_nonneg (T : ℝ); linarith
  have hRpos : 0 < R := by linarith
  set g := chainField 8 π (project R w)
  have hg : ‖g‖ ≤ G := chainField_norm π _
  by_cases hw : ‖w‖ ≤ R / 2
  · have hs1 := scale_one_le R w
    have hs2 := small_scale hRpos w hw
    have hsp := scale_pos R w
    set s := scale R w
    set c := ⟪w, g⟫ / (R ^ 2 * s ^ 3)
    have hc : |c| ≤ 1 / 160 := by
      have hd : 0 < R ^ 2 * s ^ 3 := by positivity
      have hi : |⟪w, g⟫| ≤ R / 2 * G :=
        (abs_real_inner_le_norm w g).trans (mul_le_mul hw hg (norm_nonneg _) (by positivity))
      rw [abs_div, abs_of_pos hd, div_le_iff₀ hd]
      have hs3 : 1 ≤ s ^ 3 := one_le_pow₀ hs1
      have hR2 : R * (80 * G) ≤ R * R := mul_le_mul_of_nonneg_left (by linarith) hRpos.le
      nlinarith
    have hinv : 4 / 5 ≤ s⁻¹ := by
      rw [← one_div, le_div_iff₀ hsp]; linarith
    have hinv1 : s⁻¹ ≤ 1 := (inv_le_one₀ hsp).mpr hs1
    have hcomp := component_formula R (1 / 20) π w
    rcases chain_deficient π (project R w) htail with ⟨a, b, hab, ha, hb, hsum⟩ |
      ⟨a, ha, hpos, hneg⟩ | ⟨a, ha, hga⟩
    · have hta := hcomp a
      have htb := hcomp b
      have hca := abs_lt.mp ha
      have hcb := abs_lt.mp hb
      have hcomb : totalField R (1 / 20) π w a + 2 * totalField R (1 / 20) π w b ≤ -1 / 2 := by
        rw [hta, htb]
        have hc' := abs_le.mp hc
        have e : s⁻¹ * g a + (1 / 20 - c) * (s * project R w a) +
            2 * (s⁻¹ * g b + (1 / 20 - c) * (s * project R w b)) =
            s⁻¹ * (g a + 2 * g b) + (1 / 20 - c) * s * (project R w a + 2 * project R w b) := by
          ring
        rw [e]
        have h1 : s⁻¹ * (g a + 2 * g b) ≤ -(4 / 5) := by nlinarith
        have h2 : |(1 / 20 - c) * s * (project R w a + 2 * project R w b)| ≤ 3 / 10 := by
          rw [abs_mul, abs_mul]
          have e1 : |1 / 20 - c| ≤ 1 / 20 + 1 / 160 := by
            calc _ ≤ |(1 : ℝ) / 20| + |c| := abs_sub _ _
              _ ≤ _ := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 20)]; linarith
          have e2 : |s| ≤ 5 / 4 := by rw [abs_of_pos hsp]; exact hs2
          have e3 : |project R w a + 2 * project R w b| ≤ 3 := by
            calc _ ≤ |project R w a| + |2 * project R w b| := abs_add_le _ _
              _ ≤ 1 + 2 * 1 := by
                rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
                linarith [ha.le, hb.le]
              _ = 3 := by norm_num
          exact (mul_le_mul (mul_le_mul e1 e2 (abs_nonneg _) (by norm_num)) e3
            (abs_nonneg _) (by norm_num)).trans (by norm_num)
        linarith [neg_abs_le ((1 / 20 - c) * s * (project R w a + 2 * project R w b)),
          le_abs_self ((1 / 20 - c) * s * (project R w a + 2 * project R w b))]
      have hna := PiLp.norm_apply_le (totalField R (1 / 20) π w) a
      have hnb := PiLp.norm_apply_le (totalField R (1 / 20) π w) b
      rw [Real.norm_eq_abs] at hna hnb
      have := neg_abs_le (totalField R (1 / 20) π w a)
      have := neg_abs_le (totalField R (1 / 20) π w b)
      linarith
    · have hta := hcomp a
      have hc' := abs_le.mp hc
      have hna := PiLp.norm_apply_le (totalField R (1 / 20) π w) a
      rw [Real.norm_eq_abs] at hna
      rcases le_abs'.mp ha with hneg' | hpos'
      · have hg' := hneg (by linarith)
        have hval : totalField R (1 / 20) π w a ≤ -(4 / 5) := by
          rw [hta]
          have h1 : s⁻¹ * g a ≤ -(4 / 5) := by nlinarith
          have h2 : (1 / 20 - c) * (s * project R w a) ≤ 0 := by
            apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
            nlinarith
          linarith
        have := neg_abs_le (totalField R (1 / 20) π w a)
        linarith
      · have hg' := hpos hpos'
        have hval : 4 / 5 ≤ totalField R (1 / 20) π w a := by
          rw [hta]
          have h1 : 4 / 5 ≤ s⁻¹ * g a := by nlinarith
          have h2 : 0 ≤ (1 / 20 - c) * (s * project R w a) := by
            apply mul_nonneg (by linarith)
            nlinarith
          linarith
        have := le_abs_self (totalField R (1 / 20) π w a)
        linarith
    · have hta := hcomp a
      have hc' := abs_le.mp hc
      have hca := abs_lt.mp ha
      have hna := PiLp.norm_apply_le (totalField R (1 / 20) π w) a
      rw [Real.norm_eq_abs] at hna
      have hval : totalField R (1 / 20) π w a ≤ -(1 / 2) := by
        rw [hta]
        have h1 : s⁻¹ * g a ≤ -(4 / 5) := by nlinarith
        have h2 : |(1 / 20 - c) * (s * project R w a)| ≤ 1 / 10 := by
          rw [abs_mul, abs_mul, abs_of_pos hsp]
          have e1 : |1 / 20 - c| ≤ 1 / 20 + 1 / 160 := by
            calc _ ≤ |(1 : ℝ) / 20| + |c| := abs_sub _ _
              _ ≤ _ := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 20)]; linarith
          calc _ ≤ (1 / 20 + 1 / 160) * ((5 / 4) * 1) :=
                mul_le_mul e1 (mul_le_mul hs2 ha.le (abs_nonneg _) (by norm_num))
                  (by positivity) (by norm_num)
            _ ≤ 1 / 10 := by norm_num
        linarith [le_abs_self ((1 / 20 - c) * (s * project R w a))]
      have := neg_abs_le (totalField R (1 / 20) π w a)
      linarith
  · have hcomp := derivative_norm_le hRpos w g
    have he : (1 / 20 : ℝ) • w = totalField R (1 / 20) π w - derivative R w g := by
      simp only [totalField, g]
      abel
    have hn := norm_sub_le (totalField R (1 / 20) π w) (derivative R w g)
    rw [← he, norm_smul] at hn
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 20)] at hn
    push Not at hw
    have : 1 / 20 * (R / 2) ≤ 1 / 20 * ‖w‖ := by linarith
    nlinarith

end LongTails.Proofs.SlidingLowerGeometry
