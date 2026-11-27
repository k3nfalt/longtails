import LongTails.Proofs.FrontierChain
import LongTails.Proofs.SmoothConvexFiniteGeometry
import LongTails.Proofs.FrontierChainGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SlidingLowerChain

open SmoothConvexFiniteGeometry FrontierChainProfiles FrontierChain FrontierChainGeometry

section GradHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma grad_add {f g : E → ℝ} {a b x : E} (hf : HasGradientAt f a x) (hg : HasGradientAt g b x) :
    HasGradientAt (fun y => f y + g y) (a + b) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hf hg ⊢
  rw [map_add]
  exact hf.add hg

lemma grad_neg {f : E → ℝ} {a x : E} (hf : HasGradientAt f a x) :
    HasGradientAt (fun y => -f y) (-a) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hf ⊢
  rw [map_neg]
  exact hf.neg

lemma grad_const_mul {f : E → ℝ} {a x : E} (c : ℝ) (hf : HasGradientAt f a x) :
    HasGradientAt (fun y => c * f y) (c • a) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hf ⊢
  rw [map_smul]
  exact hf.const_mul c

end GradHelpers

lemma esingle_apply {d : ℕ} (i : Fin d) (a : ℝ) (j : Fin d) :
    (EuclideanSpace.single i a : EuclideanSpace ℝ (Fin d)) j = if j = i then a else 0 :=
  PiLp.single_apply _ _ _ _ _

noncomputable def hub (t : ℝ) : ℝ := ramp (t - 1 / 4) + ramp (-t - 1 / 4)

noncomputable def hubSlope (t : ℝ) : ℝ := rampSlope (t - 1 / 4) - rampSlope (-t - 1 / 4)

lemma hub_hasDerivAt (t : ℝ) : HasDerivAt hub (hubSlope t) t := by
  have h := (QuasarHardProfiles.ramp_affine_hasDerivAt 1 (-(1 / 4)) t).add
    (QuasarHardProfiles.ramp_affine_hasDerivAt (-1) (-(1 / 4)) t)
  convert h using 1
  · funext x
    simp only [hub]
    congr 1 <;> congr 1 <;> ring
  · simp only [hubSlope]
    rw [show 1 * t + -(1 / 4) = t - 1 / 4 by ring, show -1 * t + -(1 / 4) = -t - 1 / 4 by ring]
    ring

lemma hub_flat {t : ℝ} (h : |t| ≤ 1 / 4) : hub t = 0 ∧ hubSlope t = 0 := by
  have h1 : t - 1 / 4 ≤ 0 := by linarith [le_abs_self t]
  have h2 : -t - 1 / 4 ≤ 0 := by linarith [neg_abs_le t]
  refine ⟨?_, ?_⟩
  · unfold hub
    rw [QuasarHardProfiles.ramp_of_nonpos h1, QuasarHardProfiles.ramp_of_nonpos h2]
    ring
  · unfold hubSlope
    rw [QuasarHardProfiles.rampSlope_of_nonpos h1, QuasarHardProfiles.rampSlope_of_nonpos h2]
    ring

lemma hubSlope_abs (t : ℝ) : |hubSlope t| ≤ 1 := by
  unfold hubSlope
  have a1 := rampSlope_nonneg (t - 1 / 4)
  have a2 := rampSlope_le_one (t - 1 / 4)
  have b1 := rampSlope_nonneg (-t - 1 / 4)
  have b2 := rampSlope_le_one (-t - 1 / 4)
  rw [abs_le]
  constructor <;> linarith

lemma hubSlope_ge {t : ℝ} (h : 1 / 2 ≤ t) : 1 / 4 ≤ hubSlope t := by
  have h1 : 1 / 4 ≤ rampSlope (t - 1 / 4) := by
    unfold rampSlope
    exact le_min (by norm_num) (le_max_of_le_right (by linarith))
  have h2 : rampSlope (-t - 1 / 4) = 0 := by
    unfold rampSlope
    rw [max_eq_left (by linarith)]
    norm_num
  unfold hubSlope
  linarith

lemma hubSlope_le {t : ℝ} (h : t ≤ -(1 / 2)) : hubSlope t ≤ -(1 / 4) := by
  have h1 : 1 / 4 ≤ rampSlope (-t - 1 / 4) := by
    unfold rampSlope
    exact le_min (by norm_num) (le_max_of_le_right (by linarith))
  have h2 : rampSlope (t - 1 / 4) = 0 := by
    unfold rampSlope
    rw [max_eq_left (by linarith)]
    norm_num
  unfold hubSlope
  linarith

lemma hub_model (x y : ℝ) :
    0 ≤ hub y - hub x - hubSlope x * (y - x) ∧
      hub y - hub x - hubSlope x * (y - x) ≤ (y - x) ^ 2 := by
  have h1 := ramp_model (x - 1 / 4) (y - 1 / 4)
  have h2 := ramp_model (-x - 1 / 4) (-y - 1 / 4)
  have e1 : (y - 1 / 4) - (x - 1 / 4) = y - x := by ring
  have e2 : (-y - 1 / 4) - (-x - 1 / 4) = -(y - x) := by ring
  rw [e1] at h1
  rw [e2] at h2
  simp only [hub, hubSlope]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

lemma hub_nonneg (t : ℝ) : 0 ≤ hub t := by
  unfold hub
  linarith [QuasarHardProfiles.ramp_nonneg (t - 1 / 4), QuasarHardProfiles.ramp_nonneg (-t - 1 / 4)]

lemma hub_zero : hub 0 = 0 := (hub_flat (by norm_num)).1

variable {d T : ℕ}

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

def xi (i : Fin (T + 1)) : Fin (2 * T + 1) := ⟨2 * i.val, by omega⟩

def zi (i : Fin T) : Fin (2 * T + 1) := ⟨2 * i.val + 1, by omega⟩

noncomputable def gateObj (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) : ℝ :=
  -potential (w (π (xi 0))) + ∑ i : Fin T, edge (w (π (zi i))) (w (π (xi i.succ)))

noncomputable def gateField (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) : Point d :=
  -(potentialSlope (w (π (xi 0))) • EuclideanSpace.single (π (xi 0)) (1 : ℝ)) +
    ∑ i : Fin T, edgeField (π (zi i)) (π (xi i.succ)) w

lemma gateObj_gradient (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) :
    HasGradientAt (gateObj π) (gateField π w) w := by
  have hs := HasFDerivAt.sum (u := Finset.univ)
    (fun (i : Fin T) _ => (edge_gradient (π (zi i)) (π (xi i.succ)) w).hasFDerivAt)
  have hp := (coordinate_gradient (π (xi 0)) w (potential_deriv (w (π (xi 0))))).hasFDerivAt.neg
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hp.add hs using 1
  · ext y
    simp [gateObj]
  · simp [gateField]

noncomputable def coupObj (γ : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) : ℝ :=
  γ * ∑ i : Fin T, hub (w (π (xi i.castSucc)) - w (π (zi i)) / 2)

noncomputable def coupTerm (γ : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (i : Fin T) (w : Point d) :
    Point d :=
  (γ * hubSlope (w (π (xi i.castSucc)) - w (π (zi i)) / 2)) •
    (EuclideanSpace.single (π (xi i.castSucc)) (1 : ℝ) -
      (1 / 2 : ℝ) • EuclideanSpace.single (π (zi i)) (1 : ℝ))

noncomputable def coupField (γ : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) : Point d :=
  ∑ i : Fin T, coupTerm γ π i w

lemma comp_linear_gradient {φ : ℝ → ℝ} {φ' : ℝ} (L : Point d →L[ℝ] ℝ) (v w : Point d)
    (hL : ∀ y, L y = ⟪v, y⟫) (hφ : HasDerivAt φ φ' (L w)) :
    HasGradientAt (fun y => φ (L y)) (φ' • v) w := by
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (hφ.hasFDerivAt.comp w L.hasFDerivAt).congr_fderiv ?_
  ext u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    InnerProductSpace.toDual_apply_apply, inner_smul_left, hL, smul_eq_mul, conj_trivial]
  ring

lemma coupTerm_gradient (γ : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (i : Fin T) (w : Point d) :
    HasGradientAt (fun y : Point d => γ * hub (y (π (xi i.castSucc)) - y (π (zi i)) / 2))
      (coupTerm γ π i w) w := by
  set v : Point d := EuclideanSpace.single (π (xi i.castSucc)) (1 : ℝ) -
    (1 / 2 : ℝ) • EuclideanSpace.single (π (zi i)) (1 : ℝ) with hv
  have hLy : ∀ y : Point d, innerSL ℝ v y = y (π (xi i.castSucc)) - y (π (zi i)) / 2 := by
    intro y
    rw [innerSL_apply_apply, hv, inner_sub_left, inner_smul_left, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_left]
    simp only [conj_trivial, map_one, one_mul]
    ring
  have h := comp_linear_gradient (innerSL ℝ v) v w (fun y => innerSL_apply_apply (𝕜 := ℝ) v y)
    ((hub_hasDerivAt (innerSL ℝ v w)).const_mul γ)
  have hf : (fun y : Point d => γ * hub (y (π (xi i.castSucc)) - y (π (zi i)) / 2)) =
      fun y => γ * hub (innerSL ℝ v y) := funext fun y => by rw [hLy]
  rw [hf]
  unfold coupTerm
  rw [← hLy w]
  exact h

lemma coupObj_gradient (γ : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) :
    HasGradientAt (coupObj γ π) (coupField γ π w) w := by
  have hs := HasFDerivAt.sum (u := Finset.univ)
    (fun (i : Fin T) _ => (coupTerm_gradient γ π i w).hasFDerivAt)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hs using 1
  · ext y
    simp [coupObj, Finset.mul_sum]
  · simp [coupField]

def xEmb : Fin (T + 1) ↪ Fin (2 * T + 1) := ⟨xi, fun a b h => by
  simp only [xi, Fin.mk.injEq] at h; ext; omega⟩

def zEmb : Fin T ↪ Fin (2 * T + 1) := ⟨zi, fun a b h => by
  simp only [zi, Fin.mk.injEq] at h; ext; omega⟩

def xNext : Fin T ↪ Fin (2 * T + 1) := (Fin.succEmb T).trans xEmb

def xPrev : Fin T ↪ Fin (2 * T + 1) := Fin.castSuccEmb.trans xEmb

lemma gateField_eq (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) :
    gateField π w = -(potentialSlope (w (π (xi 0))) • EuclideanSpace.single (π (xi 0)) (1 : ℝ)) +
      scatter (zEmb.trans π) (fun i => edgeLeft (w (π (zi i))) (w (π (xi i.succ)))) +
      scatter (xNext.trans π) (fun i => edgeRight (w (π (zi i))) (w (π (xi i.succ)))) := by
  simp [gateField, scatter, edgeField, Finset.sum_add_distrib, add_assoc, xNext, zEmb, xEmb]

lemma coupField_eq (γ : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) :
    coupField γ π w =
      scatter (xPrev.trans π) (fun i => γ * hubSlope (w (π (xi i.castSucc)) - w (π (zi i)) / 2)) -
      scatter (zEmb.trans π)
        (fun i => (1 / 2 : ℝ) * (γ * hubSlope (w (π (xi i.castSucc)) - w (π (zi i)) / 2))) := by
  unfold coupField coupTerm scatter
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [xPrev, zEmb, xEmb, Function.Embedding.trans_apply, Fin.castSuccEmb_apply,
    Function.Embedding.coeFn_mk]
  module

lemma gateField_norm (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) :
    ‖gateField π w‖ ≤ 1 + 17 * Real.sqrt T := by
  rw [gateField_eq]
  have h0 : ‖-(potentialSlope (w (π (xi 0))) • EuclideanSpace.single (π (xi 0)) (1 : ℝ))‖ ≤ 1 := by
    rw [norm_neg, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    have := potentialSlope_bounds (w (π (xi 0)))
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have h1 := scatter_norm_le (zEmb.trans π) (fun i => edgeLeft (w (π (zi i))) (w (π (xi i.succ))))
    (by norm_num : (0 : ℝ) ≤ 16) (fun i => by
      have := edgeLeft_bounds (w (π (zi i))) (w (π (xi i.succ)))
      rw [abs_le]; constructor <;> linarith [this.1, this.2])
  have h2 := scatter_norm_le (xNext.trans π) (fun i => edgeRight (w (π (zi i))) (w (π (xi i.succ))))
    (by norm_num : (0 : ℝ) ≤ 1) (fun i => by
      have := edgeRight_bounds (w (π (zi i))) (w (π (xi i.succ)))
      rw [abs_le]; constructor <;> linarith [this.1, this.2])
  calc _ ≤ ‖-(potentialSlope (w (π (xi 0))) • EuclideanSpace.single (π (xi 0)) (1 : ℝ))‖ +
        ‖scatter (zEmb.trans π) (fun i => edgeLeft (w (π (zi i))) (w (π (xi i.succ))))‖ +
        ‖scatter (xNext.trans π) (fun i => edgeRight (w (π (zi i))) (w (π (xi i.succ))))‖ :=
        norm_add₃_le
    _ ≤ 1 + 16 * Real.sqrt T + 1 * Real.sqrt T := by linarith
    _ = _ := by ring

lemma coupField_norm {γ : ℝ} (hγ : 0 ≤ γ) (π : Fin (2 * T + 1) ↪ Fin d) (w : Point d) :
    ‖coupField γ π w‖ ≤ 2 * γ * Real.sqrt T := by
  rw [coupField_eq]
  have h1 := scatter_norm_le (xPrev.trans π)
    (fun i => γ * hubSlope (w (π (xi i.castSucc)) - w (π (zi i)) / 2)) hγ (fun i => by
      rw [abs_mul, abs_of_nonneg hγ]
      exact mul_le_of_le_one_right hγ (hubSlope_abs _))
  have h2 := scatter_norm_le (zEmb.trans π)
    (fun i => (1 / 2 : ℝ) * (γ * hubSlope (w (π (xi i.castSucc)) - w (π (zi i)) / 2))) hγ
    (fun i => by
      rw [abs_mul, abs_mul, abs_of_nonneg hγ]
      have := hubSlope_abs (w (π (xi i.castSucc)) - w (π (zi i)) / 2)
      have : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
      nlinarith [abs_nonneg (hubSlope (w (π (xi i.castSucc)) - w (π (zi i)) / 2))])
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ γ * Real.sqrt T + γ * Real.sqrt T := add_le_add h1 h2
    _ = _ := by ring

lemma hubSlope_lipschitz (s t : ℝ) : |hubSlope s - hubSlope t| ≤ 2 * |s - t| := by
  have h1 := rampSlope_lipschitz (s - 1 / 4) (t - 1 / 4)
  have h2 := rampSlope_lipschitz (-s - 1 / 4) (-t - 1 / 4)
  have e1 : (s - 1 / 4) - (t - 1 / 4) = s - t := by ring
  have e2 : (-s - 1 / 4) - (-t - 1 / 4) = -(s - t) := by ring
  rw [e1] at h1
  rw [e2, abs_neg] at h2
  unfold hubSlope
  calc _ = |(rampSlope (s - 1 / 4) - rampSlope (t - 1 / 4)) -
        (rampSlope (-s - 1 / 4) - rampSlope (-t - 1 / 4))| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith

lemma coord_le (x : Point d) (j : Fin d) : |x j| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j

lemma gateField_lipschitz (π : Fin (2 * T + 1) ↪ Fin d) (x y : Point d) :
    ‖gateField π x - gateField π y‖ ≤ 530 * ‖x - y‖ := by
  rw [gateField_eq, gateField_eq]
  set α := zEmb.trans π
  set β := xNext.trans π
  have hl : ‖scatter α (fun i => edgeLeft (x (π (zi i))) (x (π (xi i.succ)))) -
      scatter α (fun i => edgeLeft (y (π (zi i))) (y (π (xi i.succ))))‖ ≤ 512 * ‖x - y‖ := by
    have h := scatter_increment α α β _ _ (x - y) (by norm_num : (0 : ℝ) ≤ 256) (fun i => by
      simpa [α, β, xNext, zEmb, xEmb] using edgeLeft_lipschitz
        (x (π (zi i))) (x (π (xi i.succ))) (y (π (zi i))) (y (π (xi i.succ))))
    norm_num at h
    exact h
  have hr : ‖scatter β (fun i => edgeRight (x (π (zi i))) (x (π (xi i.succ)))) -
      scatter β (fun i => edgeRight (y (π (zi i))) (y (π (xi i.succ))))‖ ≤ 16 * ‖x - y‖ := by
    have h := scatter_increment β α β _ _ (x - y) (by norm_num : (0 : ℝ) ≤ 8) (fun i => by
      simpa [α, β, xNext, zEmb, xEmb] using edgeRight_lipschitz
        (x (π (zi i))) (x (π (xi i.succ))) (y (π (zi i))) (y (π (xi i.succ))))
    norm_num at h
    exact h
  have hs : ‖-(potentialSlope (x (π (xi 0))) • EuclideanSpace.single (π (xi 0)) (1 : ℝ)) -
      -(potentialSlope (y (π (xi 0))) • EuclideanSpace.single (π (xi 0)) (1 : ℝ))‖ ≤
        2 * ‖x - y‖ := by
    have he : -(potentialSlope (x (π (xi 0))) • EuclideanSpace.single (π (xi 0)) (1 : ℝ)) -
        -(potentialSlope (y (π (xi 0))) • EuclideanSpace.single (π (xi 0)) (1 : ℝ)) =
        -(potentialSlope (x (π (xi 0))) - potentialSlope (y (π (xi 0)))) •
          EuclideanSpace.single (π (xi 0)) (1 : ℝ) := by module
    rw [he]
    simp only [norm_smul, norm_neg, PiLp.norm_single, norm_one, mul_one,
      Real.norm_eq_abs]
    have hc : |x (π (xi 0)) - y (π (xi 0))| ≤ ‖x - y‖ := by
      simpa using coord_le (x - y) (π (xi 0))
    have hp := potentialSlope_lipschitz (x (π (xi 0))) (y (π (xi 0)))
    linarith
  have hadd (a b c a' b' c' : Point d) :
      ‖a + b + c - (a' + b' + c')‖ ≤ ‖a - a'‖ + ‖b - b'‖ + ‖c - c'‖ := by
    rw [show a + b + c - (a' + b' + c') = (a - a') + (b - b') + (c - c') by abel]
    exact norm_add₃_le
  refine (hadd _ _ _ _ _ _).trans ?_
  linarith

lemma coupField_lipschitz (π : Fin (2 * T + 1) ↪ Fin d) (x y : Point d) :
    ‖coupField 8 π x - coupField 8 π y‖ ≤ 96 * ‖x - y‖ := by
  rw [coupField_eq, coupField_eq]
  set α := xPrev.trans π
  set β := zEmb.trans π
  have hc (i : Fin T) : |8 * hubSlope (x (π (xi i.castSucc)) - x (π (zi i)) / 2) -
      8 * hubSlope (y (π (xi i.castSucc)) - y (π (zi i)) / 2)| ≤
        16 * (|(x - y) (α i)| + |(x - y) (β i)|) := by
    have h := hubSlope_lipschitz (x (π (xi i.castSucc)) - x (π (zi i)) / 2)
      (y (π (xi i.castSucc)) - y (π (zi i)) / 2)
    have e : (x (π (xi i.castSucc)) - x (π (zi i)) / 2) - (y (π (xi i.castSucc)) - y (π (zi i)) / 2)
        = (x - y) (α i) - (x - y) (β i) / 2 := by
      simp [α, β, xPrev, zEmb, xEmb]; ring
    rw [e] at h
    have h2 : |(x - y) (α i) - (x - y) (β i) / 2| ≤ |(x - y) (α i)| + |(x - y) (β i)| := by
      calc _ ≤ |(x - y) (α i)| + |(x - y) (β i) / 2| := abs_sub _ _
        _ ≤ _ := by rw [abs_div, abs_two]; linarith [abs_nonneg ((x - y) (β i))]
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    linarith
  have h1 := scatter_increment α α β _ _ (x - y) (by norm_num : (0 : ℝ) ≤ 16) hc
  have h2 := scatter_increment β α β
    (fun i => (1 / 2 : ℝ) * (8 * hubSlope (x (π (xi i.castSucc)) - x (π (zi i)) / 2)))
    (fun i => (1 / 2 : ℝ) * (8 * hubSlope (y (π (xi i.castSucc)) - y (π (zi i)) / 2)))
    (x - y) (by norm_num : (0 : ℝ) ≤ 16) (fun i => by
      have := hc i
      rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      nlinarith [abs_nonneg (8 * hubSlope (x (π (xi i.castSucc)) - x (π (zi i)) / 2) -
        8 * hubSlope (y (π (xi i.castSucc)) - y (π (zi i)) / 2))])
  have hadd (a b a' b' : Point d) : ‖a - b - (a' - b')‖ ≤ ‖a - a'‖ + ‖b - b'‖ := by
    rw [show a - b - (a' - b') = (a - a') - (b - b') by abel]
    exact norm_sub_le _ _
  refine (hadd _ _ _ _).trans ?_
  calc _ ≤ 2 * 16 * ‖x - y‖ + 2 * 16 * ‖x - y‖ := add_le_add h1 h2
    _ ≤ 96 * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]

end LongTails.Proofs.SlidingLowerChain
