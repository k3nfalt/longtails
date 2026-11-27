import LongTails.Proofs.SlidingLowerInstance
import LongTails.Proofs.QuasarHardAdmissible

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SlidingLowerOracle

open SlidingLowerChain SlidingLowerMask SlidingLowerInstance SoftRadialProjection
open QuasarCoinLaw QuasarHardAdmissible

variable {d T : ℕ}

noncomputable def rescale (s : ℝ) (x0 x : Point d) : Point d := s⁻¹ • (x - x0)

noncomputable def fS (a s R : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (x0 x : Point d) : ℝ :=
  a * fbar R π (rescale s x0 x)

noncomputable def hS (a s R : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (x0 x : Point d) : ℝ :=
  a * hbar R π (rescale s x0 x)

noncomputable def hO (p a s R : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (x0 x : Point d) (b : Bool) :
    Point d :=
  (a / s) • hpart p R π (2 * T + 1) b (rescale s x0 x)

lemma scaled_gradient {F : Point d → ℝ} {G : Point d → Point d} (a s : ℝ) (x0 x : Point d)
    (hF : HasGradientAt F (G (rescale s x0 x)) (rescale s x0 x)) :
    HasGradientAt (fun y => a * F (rescale s x0 y)) ((a / s) • G (rescale s x0 x)) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hF ⊢
  have hA : HasFDerivAt (fun y : Point d => rescale s x0 y)
      (s⁻¹ • ContinuousLinearMap.id ℝ (Point d)) x := by
    unfold rescale
    exact ((hasFDerivAt_id x).sub_const x0).const_smul s⁻¹
  have h := (hF.comp x hA).const_mul a
  refine h.congr_fderiv ?_
  ext v
  simp [InnerProductSpace.toDual_apply_apply]
  field_simp

lemma fS_gradient {a s R : ℝ} (hR : 0 < R) (π : Fin (2 * T + 1) ↪ Fin d) (x0 x : Point d) :
    HasGradientAt (fS a s R π x0) ((a / s) • fgrad R π (rescale s x0 x)) x :=
  scaled_gradient a s x0 x (fbar_gradient hR π _)

lemma hS_gradient {a s R : ℝ} (hR : 0 < R) (π : Fin (2 * T + 1) ↪ Fin d) (x0 x : Point d) :
    HasGradientAt (hS a s R π x0) ((a / s) • hgrad R π (rescale s x0 x)) x :=
  scaled_gradient a s x0 x (hbar_gradient hR π _)

lemma scaled_lipschitz {G : Point d → Point d} {a s C : ℝ} (ha : 0 ≤ a) (hs : 0 < s)
    (hG : ∀ u v, ‖G u - G v‖ ≤ C * ‖u - v‖) (x0 x y : Point d) :
    ‖(a / s) • G (rescale s x0 x) - (a / s) • G (rescale s x0 y)‖ ≤
      (a / s ^ 2 * C) * ‖x - y‖ := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hs.le)]
  have h := hG (rescale s x0 x) (rescale s x0 y)
  have he : rescale s x0 x - rescale s x0 y = s⁻¹ • (x - y) := by
    unfold rescale; rw [← smul_sub]; congr 1; abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)] at h
  calc a / s * ‖G (rescale s x0 x) - G (rescale s x0 y)‖
      ≤ a / s * (C * (s⁻¹ * ‖x - y‖)) := mul_le_mul_of_nonneg_left h (div_nonneg ha hs.le)
    _ = _ := by field_simp

lemma scale_continuous (R : ℝ) : Continuous (fun w : Point d => scale R w) := by
  unfold scale; fun_prop

lemma project_continuous (R : ℝ) : Continuous (fun w : Point d => project R w) := by
  unfold project
  exact ((scale_continuous R).inv₀ (fun w => (scale_pos R w).ne')).smul continuous_id

lemma derivative_continuous {R : ℝ} (hR : 0 < R) {G : Point d → Point d} (hG : Continuous G) :
    Continuous (fun w : Point d => derivative R w (G w)) := by
  simp_rw [derivative_apply]
  have hs := scale_continuous (d := d) R
  exact ((hs.inv₀ (fun w => (scale_pos R w).ne')).smul hG).sub
    ((Continuous.div (continuous_id.inner hG) (continuous_const.mul (hs.pow 3)) (fun w =>
      (mul_pos (pow_pos hR 2) (pow_pos (scale_pos R w) 3)).ne')).smul continuous_id)

lemma top_measurable (π : Fin (2 * T + 1) ↪ Fin d) (V : ℕ) (R : ℝ) :
    Measurable (fun w : Point d => top π V (project R w)) := by
  let Φ : (Fin (2 * T + 1) → Bool) → ℕ := fun c =>
    ((Finset.univ : Finset (Fin (2 * T + 1))).filter
      (fun j => j.val < V ∧ c j = true)).sup (fun j => j.val + 1)
  have hp : Continuous (fun w : Point d => project R w) := project_continuous R
  have he : (fun w : Point d => top π V (project R w)) =
      Φ ∘ (fun (w : Point d) (j : Fin (2 * T + 1)) =>
        if 1 / 8 < |project R w (π j)| then true else false) := by
    funext w
    simp only [Function.comp_apply, Φ, top]
    congr 1
    apply Finset.filter_congr
    intro j _
    by_cases h : 1 / 8 < |project R w (π j)|
    · simp
    · simp
  rw [he]
  apply (measurable_of_countable Φ).comp
  apply Measurable.of_eval
  intro j
  have hm : Measurable (fun w : Point d => |project R w (π j)|) :=
    (continuous_abs.comp ((PiLp.continuous_apply 2 _ (π j)).comp hp)).measurable
  exact Measurable.ite (measurableSet_lt measurable_const hm) measurable_const measurable_const

lemma coupTerm_norm (π : Fin (2 * T + 1) ↪ Fin d) (i : Fin T) (q : Point d) :
    ‖coupTerm 8 π i q‖ ≤ 12 := by
  unfold coupTerm
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  have h1 := hubSlope_abs (q (π (xi i.castSucc)) - q (π (zi i)) / 2)
  have h2 : ‖EuclideanSpace.single (π (xi i.castSucc)) (1 : ℝ) -
      (1 / 2 : ℝ) • EuclideanSpace.single (π (zi i)) (1 : ℝ)‖ ≤ 3 / 2 := by
    calc _ ≤ ‖EuclideanSpace.single (π (xi i.castSucc)) (1 : ℝ)‖ +
          ‖(1 / 2 : ℝ) • EuclideanSpace.single (π (zi i)) (1 : ℝ)‖ := norm_sub_le _ _
      _ = 3 / 2 := by
        rw [norm_smul]; simp; norm_num
  have h3 := norm_nonneg (EuclideanSpace.single (π (xi i.castSucc)) (1 : ℝ) -
      (1 / 2 : ℝ) • EuclideanSpace.single (π (zi i)) (1 : ℝ))
  nlinarith [abs_nonneg (hubSlope (q (π (xi i.castSucc)) - q (π (zi i)) / 2))]

noncomputable def frontier (π : Fin (2 * T + 1) ↪ Fin d) (q : Point d) : Point d :=
  ∑ i : Fin T, if top π (2 * T + 1) q = 2 * i.val + 1 then coupTerm 8 π i q else 0

lemma frontier_norm (π : Fin (2 * T + 1) ↪ Fin d) (q : Point d) : ‖frontier π q‖ ≤ 12 := by
  unfold frontier
  by_cases h : ∃ i : Fin T, top π (2 * T + 1) q = 2 * i.val + 1
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left hi]; exact coupTerm_norm π i q
    · intro j _ hj
      rw [ite_eq_right]
      intro hj'
      apply hj
      ext
      omega
    · intro hi'; exact absurd (Finset.mem_univ i) hi'
  · push Not at h
    rw [Finset.sum_eq_zero (fun i _ => by rw [ite_eq_right (h i)])]
    simp

lemma hpart_split (p R : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (b : Bool) (w : Point d) :
    hpart p R π (2 * T + 1) b w =
      hgrad R π w + (coin p b - 1) • derivative R w (frontier π (project R w)) := by
  unfold hpart hgrad frontier
  rw [coupV_split, map_add, ← map_smul, Finset.smul_sum]
  have : (∑ i : Fin T, if top π (2 * T + 1) (project R w) = 2 * i.val + 1 then
        (coin p b - 1) • coupTerm 8 π i (project R w) else 0) =
      ∑ i : Fin T, (coin p b - 1) • (if top π (2 * T + 1) (project R w) = 2 * i.val + 1 then
        coupTerm 8 π i (project R w) else 0) := by
    apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp
  rw [this]
  abel

lemma hubSlope_continuous : Continuous hubSlope := by
  apply LipschitzWith.continuous (K := 2)
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [Real.dist_eq, NNReal.coe_ofNat]
  exact hubSlope_lipschitz s t

lemma coupTerm_continuous (π : Fin (2 * T + 1) ↪ Fin d) (i : Fin T) :
    Continuous (fun q : Point d => coupTerm 8 π i q) := by
  unfold coupTerm
  exact (continuous_const.mul (hubSlope_continuous.comp (by fun_prop))).smul continuous_const

lemma coupField_continuous (π : Fin (2 * T + 1) ↪ Fin d) :
    Continuous (fun q : Point d => coupField 8 π q) := by
  unfold coupField
  exact continuous_finsetSum _ (fun i _ => coupTerm_continuous π i)

lemma hpart_measurable (p : ℝ) {R : ℝ} (hR : 0 < R) (π : Fin (2 * T + 1) ↪ Fin d) (b : Bool) :
    Measurable (fun w : Point d => hpart p R π (2 * T + 1) b w) := by
  have he : (fun w : Point d => hpart p R π (2 * T + 1) b w) = fun w =>
      hgrad R π w + (coin p b - 1) • ∑ i : Fin T,
        (if top π (2 * T + 1) (project R w) = 2 * i.val + 1 then
          derivative R w (coupTerm 8 π i (project R w)) else 0) := by
    funext w
    rw [hpart_split]
    congr 2
    unfold frontier
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [he]
  have h1 : Measurable (fun w : Point d => hgrad R π w) := by
    unfold hgrad
    exact ((derivative_continuous hR ((coupField_continuous π).comp (project_continuous R))).add
      (continuous_id.const_smul (kap R T))).measurable
  have h2 : Measurable (fun w : Point d => ∑ i : Fin T,
      (if top π (2 * T + 1) (project R w) = 2 * i.val + 1 then
        derivative R w (coupTerm 8 π i (project R w)) else 0)) := by
    apply Finset.measurable_sum
    intro i _
    exact Measurable.ite ((top_measurable π (2 * T + 1) R) (measurableSet_singleton _))
      (derivative_continuous hR ((coupTerm_continuous π i).comp (project_continuous R))).measurable
      measurable_const
  exact h1.add (h2.const_smul (coin p b - 1))

lemma hO_measurable (p a s : ℝ) {R : ℝ} (hR : 0 < R) (π : Fin (2 * T + 1) ↪ Fin d)
    (x0 : Point d) :
    Measurable (Function.uncurry (hO p a s R π x0)) := by
  apply measurable_from_prod_countable_left
  intro b
  have hn : Continuous (fun x : Point d => rescale s x0 x) := by unfold rescale; fun_prop
  exact ((hpart_measurable p hR π b).comp hn.measurable).const_smul (a / s)

lemma coin_mean {p : ℝ} (hp : 0 < p) : p * (coin p true - 1) + (1 - p) * (coin p false - 1) = 0 := by
  unfold coin
  simp only [ite_true, Bool.false_eq_true, ite_false]
  field_simp
  ring

lemma coin_var {p : ℝ} (hp : 0 < p) :
    p * (coin p true - 1) ^ 2 + (1 - p) * (coin p false - 1) ^ 2 = 1 / p - 1 := by
  unfold coin
  simp only [ite_true, Bool.false_eq_true, ite_false]
  field_simp
  ring

lemma hO_mean {p a s R : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (π : Fin (2 * T + 1) ↪ Fin d)
    (x0 x : Point d) :
    ∫ ω, hO p a s R π x0 x ω ∂((coinLaw p hp.le hp1 : ProbabilityMeasure Bool) : Measure Bool) =
      (a / s) • hgrad R π (rescale s x0 x) := by
  rw [coin_integral]
  unfold hO
  rw [hpart_split, hpart_split]
  have hc := coin_mean hp
  set D := derivative R (rescale s x0 x) (frontier π (project R (rescale s x0 x)))
  set H := hgrad R π (rescale s x0 x)
  calc p • ((a / s) • (H + (coin p true - 1) • D)) +
        (1 - p) • ((a / s) • (H + (coin p false - 1) • D)) =
      (a / s) • (H + (p * (coin p true - 1) + (1 - p) * (coin p false - 1)) • D) := by module
    _ = (a / s) • H := by rw [hc, zero_smul, add_zero]

lemma hO_variance {p a s R : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hR : 0 < R)
    (π : Fin (2 * T + 1) ↪ Fin d) (x0 x : Point d) :
    ∫ ω, ‖hO p a s R π x0 x ω - (a / s) • hgrad R π (rescale s x0 x)‖ ^ 2
        ∂((coinLaw p hp.le hp1 : ProbabilityMeasure Bool) : Measure Bool) ≤
      576 * (a / s) ^ 2 * (1 / p - 1) := by
  rw [coin_integral]
  unfold hO
  rw [hpart_split, hpart_split]
  set D := derivative R (rescale s x0 x) (frontier π (project R (rescale s x0 x)))
  set H := hgrad R π (rescale s x0 x)
  have hD : ‖D‖ ≤ 24 := by
    calc ‖D‖ ≤ ‖derivative R (rescale s x0 x)‖ * ‖frontier π (project R (rescale s x0 x))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 2 * 12 := mul_le_mul (derivative_opNorm_le hR _) (frontier_norm π _) (norm_nonneg _)
          (by norm_num)
      _ = 24 := by norm_num
  have e (c : ℝ) : ‖(a / s) • (H + c • D) - (a / s) • H‖ ^ 2 = (a / s) ^ 2 * c ^ 2 * ‖D‖ ^ 2 := by
    rw [← smul_sub, add_sub_cancel_left, smul_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  simp only [smul_eq_mul]
  rw [e, e]
  have hv := coin_var hp
  have hD2 : ‖D‖ ^ 2 ≤ 576 := by nlinarith [norm_nonneg D]
  have hq : 0 ≤ (a / s) ^ 2 := sq_nonneg _
  have h1 : p * ((a / s) ^ 2 * (coin p true - 1) ^ 2 * ‖D‖ ^ 2) +
      (1 - p) * ((a / s) ^ 2 * (coin p false - 1) ^ 2 * ‖D‖ ^ 2) =
      (a / s) ^ 2 * ‖D‖ ^ 2 * (1 / p - 1) := by rw [← hv]; ring
  rw [h1]
  have h3 : 0 ≤ 1 / p - 1 := by rw [sub_nonneg, le_div_iff₀ hp]; linarith
  calc (a / s) ^ 2 * ‖D‖ ^ 2 * (1 / p - 1) ≤ (a / s) ^ 2 * 576 * (1 / p - 1) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD2 hq) h3
    _ = _ := by ring

end LongTails.Proofs.SlidingLowerOracle
