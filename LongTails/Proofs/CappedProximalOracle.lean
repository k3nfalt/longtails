import LongTails.Setups.CappedHessianSimilarConvex
import LongTails.Proofs.CappedProximalGeometry
import LongTails.Proofs.SvrgConvex
import LongTails.Proofs.ComponentEnvelopeProx

open Set
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.CappedProximalOracle

open LongTails.Setups.CappedHessianSimilarConvex

lemma prox_stationary {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (i : Fin p.m) {a : ℝ} (ha : 0 < a) (z : p.E) :
    gradient (inst.components i) (inst.prox i a z) + a • (inst.prox i a z - z) = 0 := by
  apply OracleTemplate.ComponentEnvelope.regularized_minimum_stationary (h.2.1 i) a z
  intro y
  exact h.2.2.2.2.1 i a ha z (mem_univ y)

lemma corrected_prox_stationary {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (i : Fin p.m) {a : ℝ} (ha : 0 < a) (x g : p.E) :
    let u := inst.prox i a (x + a⁻¹ • (gradient (inst.components i) x - g))
    gradient (inst.components i) u + a • (u - x) = gradient (inst.components i) x - g := by
  dsimp
  have hs := prox_stationary h i ha (x + a⁻¹ • (gradient (inst.components i) x - g))
  have he (u : p.E) : a • (u - (x + a⁻¹ • (gradient (inst.components i) x - g))) =
      a • (u - x) - (gradient (inst.components i) x - g) := by
    rw [show u - (x + a⁻¹ • (gradient (inst.components i) x - g)) =
      (u - x) - a⁻¹ • (gradient (inst.components i) x - g) by abel,
      smul_sub, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  rw [he] at hs
  apply sub_eq_zero.mp
  convert hs using 1
  abel

lemma regularized_corrected_stationary {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (i : Fin p.m) {lam rho : ℝ} (ht : 0 < lam + rho)
    (center x g : p.E) :
    let u := inst.prox i (lam + rho)
      (x + (lam + rho)⁻¹ • (gradient (inst.components i) x - g))
    gradient (inst.components i) u + rho • (u - center) + lam • (u - x) =
      gradient (inst.components i) x + rho • (x - center) - g := by
  dsimp
  have hs := corrected_prox_stationary h i ht x g
  dsimp at hs
  calc
    _ = (gradient (inst.components i)
          (inst.prox i (lam + rho) (x + (lam + rho)⁻¹ •
            (gradient (inst.components i) x - g))) +
        (lam + rho) • (inst.prox i (lam + rho)
          (x + (lam + rho)⁻¹ • (gradient (inst.components i) x - g)) - x)) +
        rho • (x - center) := by module
    _ = _ := by rw [hs]; abel

lemma component_bregman_nonneg {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (i : Fin p.m) (u v : p.E) :
    0 ≤ inst.components i u - inst.components i v -
      ⟪gradient (inst.components i) v, u - v⟫ := by
  exact sub_nonneg.mpr (OracleTemplate.Gradient.convex_support (h.1 i) (h.2.1 i) v u)

lemma component_reverse_support {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (i : Fin p.m) (u v : p.E) :
    inst.components i u - inst.components i v ≤
      ⟪gradient (inst.components i) u, u - v⟫ := by
  have hs := OracleTemplate.Gradient.convex_support (h.1 i) (h.2.1 i) u v
  simp only [inner_sub_right] at hs ⊢
  linarith

lemma centered_gradient_lipschitz {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) (i : Fin p.m) (x y : p.E) :
    ‖centeredGradient inst i x - centeredGradient inst i y‖ ≤
      Real.sqrt p.m * p.δ * ‖x - y‖ := by
  have hm : 0 < (p.m : ℝ) := by exact_mod_cast NeZero.pos p.m
  have hs := h.2.2.2.1 x y
  have hi : ‖centeredGradient inst i x - centeredGradient inst i y‖ ^ 2 ≤
      ∑ j : Fin p.m, ‖centeredGradient inst j x - centeredGradient inst j y‖ ^ 2 := by
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖centeredGradient inst j x - centeredGradient inst j y‖) (Finset.mem_univ i)
  have ht : (∑ j : Fin p.m,
      ‖centeredGradient inst j x - centeredGradient inst j y‖ ^ 2) ≤
      (p.δ ^ 2 * ‖x - y‖ ^ 2) * p.m := by
    apply (div_le_iff₀ hm).mp
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hs
  have hroot := Real.sq_sqrt hm.le
  have htarget : 0 ≤ Real.sqrt p.m * p.δ * ‖x - y‖ := by positivity
  have he : (Real.sqrt p.m * p.δ * ‖x - y‖) ^ 2 =
      (p.δ ^ 2 * ‖x - y‖ ^ 2) * p.m := by rw [mul_pow, mul_pow, hroot]; ring
  nlinarith [norm_nonneg (centeredGradient inst i x - centeredGradient inst i y)]

lemma translated_centered_second_moment {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (U t : p.E) :
    (𝔼 i, ‖centeredGradient inst i U - centeredGradient inst i (U + t)‖ ^ 2) ≤
      p.δ ^ 2 * ‖t‖ ^ 2 := by
  have hs := h.2.2.2.1 U (U + t)
  simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, one_div_mul_eq_div,
    show U - (U + t) = -t by abel, norm_neg] using hs

lemma translated_centered_lipschitz {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) (U : p.E) (i : Fin p.m) (x y : p.E) :
    ‖(centeredGradient inst i U - centeredGradient inst i (U + x)) -
      (centeredGradient inst i U - centeredGradient inst i (U + y))‖ ≤
      Real.sqrt p.m * p.δ * ‖x - y‖ := by
  rw [show (centeredGradient inst i U - centeredGradient inst i (U + x)) -
      (centeredGradient inst i U - centeredGradient inst i (U + y)) =
      centeredGradient inst i (U + y) - centeredGradient inst i (U + x) by abel]
  simpa only [add_sub_add_left_eq_sub, norm_sub_rev] using
    centered_gradient_lipschitz h hd i (U + y) (U + x)

lemma objective_hasGradient {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (x : p.E) :
    HasGradientAt (objective inst) (gradient (objective inst) x) x := by
  have hg := OracleTemplate.FiniteSum.objective_gradient
    (f := inst.components)
    (oracle := fun z : Fin p.m × p.E => gradient (inst.components z.1) z.2) (h.2.1) x
  rw [← hg.gradient] at hg
  exact hg

lemma objective_gradient_eq {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (x : p.E) :
    gradient (objective inst) x = (p.m : ℝ)⁻¹ • ∑ i, gradient (inst.components i) x := by
  exact (OracleTemplate.FiniteSum.objective_gradient
    (f := inst.components)
    (oracle := fun z : Fin p.m × p.E => gradient (inst.components z.1) z.2) (h.2.1) x).gradient

lemma centered_gradient_sum {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (x : p.E) :
    ∑ i, centeredGradient inst i x = 0 := by
  have hm : (p.m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p.m
  simp only [centeredGradient, objective_gradient_eq h x, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hm, one_smul, sub_self]

lemma centered_difference_sum {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (x w : p.E) :
    ∑ i, (centeredGradient inst i x - centeredGradient inst i w) = 0 := by
  rw [Finset.sum_sub_distrib, centered_gradient_sum h x, centered_gradient_sum h w, sub_self]

lemma centered_hasGradient {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (i : Fin p.m) (x : p.E) :
    HasGradientAt (fun y => inst.components i y - objective inst y)
      (centeredGradient inst i x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! (h.2.1 i x).hasFDerivAt.sub (objective_hasGradient h x).hasFDerivAt using 1
  simp [centeredGradient]

lemma reverse_bregman_upper {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) (i : Fin p.m) (U z : p.E) :
    -((objective inst U - inst.components i U) -
      (objective inst z - inst.components i z) -
      ⟪gradient (objective inst) z - gradient (inst.components i) z, U - z⟫) ≤
        (Real.sqrt p.m * p.δ) / 2 * ‖U - z‖ ^ 2 := by
  have hu := OracleTemplate.Gradient.smooth_upper_bound (centered_hasGradient h i)
    (centered_gradient_lipschitz h hd i) z U
  simp only [centeredGradient, inner_sub_left] at hu ⊢
  linarith

lemma averaged_reverse_bregman_upper {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) {s : ℕ} (hs : 0 < s)
    (indices : Fin s → Fin p.m) (U z : p.E) :
    -((1 / (s : ℝ)) * ∑ j,
      ((objective inst U - inst.components (indices j) U) -
        (objective inst z - inst.components (indices j) z) -
        ⟪gradient (objective inst) z - gradient (inst.components (indices j)) z, U - z⟫)) ≤
      (Real.sqrt p.m * p.δ) / 2 * ‖U - z‖ ^ 2 := by
  have ht := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    reverse_bregman_upper h hd (indices j) U z)
  have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ 1 / (s : ℝ) by positivity)
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  simpa only [Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_neg, ← mul_assoc, one_div_mul_cancel hs', one_mul]
    using hm

lemma sampled_primal_upper {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) {s : ℕ} (hs : 0 < s)
    (indices : Fin s → Fin p.m) (u : Fin p.m → p.E) (U z : p.E)
    (hz : ∑ j, (1 / (s : ℝ)) • u (indices j) = z) :
    objective inst z - objective inst U ≤
      (1 / (s : ℝ)) * (∑ j, (inst.components (indices j) (u (indices j)) -
        inst.components (indices j) U -
        ⟪gradient (inst.components (indices j)) U, u (indices j) - U⟫)) +
      ⟪gradient (objective inst) U, z - U⟫ +
      (1 / (s : ℝ)) * (∑ j, ⟪centeredGradient inst (indices j) U -
        centeredGradient inst (indices j) z, u (indices j) - U⟫) +
      (Real.sqrt p.m * p.δ) / 2 * ‖U - z‖ ^ 2 := by
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hg := CappedProximalGeometry.sampled_primal_certificate
    (fun _ : Fin s => 1 / (s : ℝ)) (fun j => u (indices j))
    (fun j => gradient (inst.components (indices j)) U)
    (fun j => gradient (inst.components (indices j)) z)
    (fun j => inst.components (indices j) (u (indices j)))
    (fun j => inst.components (indices j) U)
    (fun j => inst.components (indices j) z) U z
    (gradient (objective inst) U) (gradient (objective inst) z)
    (objective inst U) (objective inst z) (fun _ => by positivity)
    (by simp [hs']) hz (fun j => component_reverse_support h (indices j) z (u (indices j)))
  have he (j : Fin s) :
      (gradient (objective inst) z - gradient (inst.components (indices j)) z) -
        (gradient (objective inst) U - gradient (inst.components (indices j)) U) =
      centeredGradient inst (indices j) U - centeredGradient inst (indices j) z := by
    unfold centeredGradient
    abel
  simp_rw [he] at hg
  simp only [← Finset.mul_sum] at hg
  have hr := averaged_reverse_bregman_upper h hd hs indices U z
  linarith

lemma common_point_bregman {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) (u : Fin p.m → p.E)
    (U x g : p.E) (lam : ℝ)
    (hU : ∑ i, (1 / (p.m : ℝ)) • u i = U)
    (hs : ∀ i, gradient (inst.components i) (u i) + lam • (u i - x) =
      gradient (inst.components i) x - g) :
    (1 / (p.m : ℝ)) * ∑ i, (inst.components i (u i) - inst.components i U -
      ⟪gradient (inst.components i) U, u i - U⟫) ≤
      p.δ * ‖x - U‖ * Real.sqrt ((1 / (p.m : ℝ)) * ∑ i, ‖u i - U‖ ^ 2) -
        lam * ((1 / (p.m : ℝ)) * ∑ i, ‖u i - U‖ ^ 2) := by
  have hm : 0 < (p.m : ℝ) := by exact_mod_cast NeZero.pos p.m
  apply CappedProximalGeometry.common_point_bregman_bound u
    (fun i => gradient (inst.components i) (u i))
    (fun i => gradient (inst.components i) x)
    (fun i => gradient (inst.components i) U)
    (fun i => inst.components i (u i)) (fun i => inst.components i U)
    U x g (gradient (objective inst) x - gradient (objective inst) U) hm hd
    (by simp [hm.ne']) hU (fun i => component_reverse_support h i (u i) U) hs
  have he (i : Fin p.m) :
      (gradient (inst.components i) x - gradient (inst.components i) U) -
        (gradient (objective inst) x - gradient (objective inst) U) =
      centeredGradient inst i x - centeredGradient inst i U := by
    unfold centeredGradient
    abel
  simp_rw [he]
  exact h.2.2.2.1 x U

lemma common_point_reverse_bregman {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) (u : Fin p.m → p.E)
    (U x g : p.E) (lam : ℝ)
    (hU : ∑ i, (1 / (p.m : ℝ)) • u i = U)
    (hs : ∀ i, gradient (inst.components i) (u i) + lam • (u i - x) =
      gradient (inst.components i) x - g) :
    (1 / (p.m : ℝ)) * ∑ i, (inst.components i U - inst.components i (u i) -
      ⟪gradient (inst.components i) (u i), U - u i⟫) ≤
      p.δ * ‖x - U‖ * Real.sqrt ((1 / (p.m : ℝ)) * ∑ i, ‖u i - U‖ ^ 2) -
        lam * ((1 / (p.m : ℝ)) * ∑ i, ‖u i - U‖ ^ 2) := by
  have hm : 0 < (p.m : ℝ) := by exact_mod_cast NeZero.pos p.m
  apply CappedProximalGeometry.common_point_reverse_bregman_bound u
    (fun i => gradient (inst.components i) (u i))
    (fun i => gradient (inst.components i) x)
    (fun i => gradient (inst.components i) U)
    (fun i => inst.components i (u i)) (fun i => inst.components i U)
    U x g (gradient (objective inst) x - gradient (objective inst) U) hm hd
    (by simp [hm.ne']) hU (fun i => OracleTemplate.Gradient.convex_support (h.1 i) (h.2.1 i) U (u i)) hs
  have he (i : Fin p.m) :
      (gradient (inst.components i) x - gradient (inst.components i) U) -
        (gradient (objective inst) x - gradient (objective inst) U) =
      centeredGradient inst i x - centeredGradient inst i U := by
    unfold centeredGradient
    abel
  simp_rw [he]
  exact h.2.2.2.1 x U

lemma common_point_comparison {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) (u : Fin p.m → p.E)
    (U x g v : p.E) (lam : ℝ)
    (hU : ∑ i, (1 / (p.m : ℝ)) • u i = U)
    (hs : ∀ i, gradient (inst.components i) (u i) + lam • (u i - x) =
      gradient (inst.components i) x - g) :
    objective inst U - objective inst v ≤
      ⟪gradient (objective inst) x - g + lam • (x - U), U - v⟫ +
      p.δ * ‖x - U‖ * Real.sqrt ((1 / (p.m : ℝ)) * ∑ i, ‖u i - U‖ ^ 2) -
        lam * ((1 / (p.m : ℝ)) * ∑ i, ‖u i - U‖ ^ 2) := by
  have hm : (p.m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p.m
  have hg := CappedProximalGeometry.mean_proximal_gradient
    (fun _ : Fin p.m => 1 / (p.m : ℝ)) u
    (fun i => gradient (inst.components i) (u i))
    (fun i => gradient (inst.components i) x) U x g lam (by simp [hm]) hU hs
  have hx : (∑ i : Fin p.m, (1 / (p.m : ℝ)) • gradient (inst.components i) x) =
      gradient (objective inst) x := by
    rw [objective_gradient_eq h x, ← Finset.smul_sum, one_div]
  rw [hx] at hg
  have hc := CappedProximalGeometry.weighted_reverse_support
    (fun _ : Fin p.m => 1 / (p.m : ℝ)) u
    (fun i => gradient (inst.components i) (u i))
    (fun i => inst.components i (u i)) (fun i => inst.components i U)
    (fun i => inst.components i v) U v (fun _ => by positivity)
    (fun i => component_reverse_support h i (u i) v)
  rw [hg] at hc
  simp only [← Finset.mul_sum] at hc
  have hb := common_point_reverse_bregman h hd u U x g lam hU hs
  have he : (1 / (p.m : ℝ)) * (∑ i, (inst.components i U - inst.components i v)) =
      objective inst U - objective inst v := by
    simp only [objective, LongTails.Setups.FiniteSumSmoothAndConvex.objective,
      Finset.sum_sub_distrib, mul_sub, one_div]
  rw [he] at hc
  linarith

lemma common_point_variance {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) (u : Fin p.m → p.E)
    (U x g : p.E) {lam : ℝ} (hl : 0 < lam)
    (hU : ∑ i, (1 / (p.m : ℝ)) • u i = U)
    (hs : ∀ i, gradient (inst.components i) (u i) + lam • (u i - x) =
      gradient (inst.components i) x - g) :
    (1 / (p.m : ℝ)) * ∑ i, ‖u i - U‖ ^ 2 ≤ p.δ ^ 2 * ‖x - U‖ ^ 2 / lam ^ 2 := by
  apply CappedProximalGeometry.proximal_variance_bound
    (B := (1 / (p.m : ℝ)) * ∑ i, (inst.components i (u i) - inst.components i U -
      ⟪gradient (inst.components i) U, u i - U⟫))
    (mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun i _ => component_bregman_nonneg h i (u i) U)))
    (by positivity) (norm_nonneg _) hd hl
  exact common_point_bregman h hd u U x g lam hU hs

lemma regularized_hasGradient {p : Params} {f : p.E → ℝ} {g : p.E}
    {x : p.E} (hf : HasGradientAt f g x) (rho : ℝ) (center : p.E) :
    HasGradientAt (fun y => f y + rho / 2 * ‖y - center‖ ^ 2)
      (g + rho • (x - center)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! hf.hasFDerivAt.add
    (((hasFDerivAt_id x).sub_const center).norm_sq.const_mul (rho / 2)) using 1
  ext v
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    InnerProductSpace.toDual_apply_apply, innerSL_apply_apply, id_eq, real_inner_smul_left, inner_add_left,
    smul_eq_mul]
  ring

lemma regularized_centered_gradient {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (rho : ℝ) (center x : p.E) (i : Fin p.m) :
    gradient (fun y => inst.components i y + rho / 2 * ‖y - center‖ ^ 2) x -
      gradient (fun y => objective inst y + rho / 2 * ‖y - center‖ ^ 2) x =
      centeredGradient inst i x := by
  rw [(regularized_hasGradient (h.2.1 i x) rho center).gradient,
    (regularized_hasGradient (objective_hasGradient h x) rho center).gradient]
  dsimp [centeredGradient]
  abel

lemma regularized_convex {p : Params} {f : p.E → ℝ}
    (hf : ConvexOn ℝ univ f) {rho : ℝ} (hr : 0 ≤ rho) (center : p.E) :
    ConvexOn ℝ univ (fun y => f y + rho / 2 * ‖y - center‖ ^ 2) := by
  have hq := (convexOn_univ_dist center).pow (fun x _ => dist_nonneg (x := x)) 2
  have hc := hq.smul (show 0 ≤ rho / 2 by positivity)
  simpa only [Pi.pow_apply, dist_eq_norm, smul_eq_mul] using! hf.add hc

lemma regularized_strongConvex {p : Params} {f : p.E → ℝ} {mu : ℝ}
    (hf : StrongConvexOn univ mu f) (rho : ℝ) (center : p.E) :
    StrongConvexOn univ (mu + rho) (fun y => f y + rho / 2 * ‖y - center‖ ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hfxy := hf.2 hx hy ha hb hab
  have hq := CappedProximalGeometry.squared_convex_combination x y center ha hb hab
  dsimp only at hfxy ⊢
  simp only [smul_eq_mul] at hfxy ⊢
  rw [hq]
  nlinarith only [hfxy]

lemma shifted_prox_stationary {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (i : Fin p.m) {a rho : ℝ} (ht : 0 < a + rho)
    (center z : p.E) :
    let u := inst.prox i (a + rho) ((a + rho)⁻¹ • (a • z + rho • center))
    gradient (inst.components i) u + rho • (u - center) + a • (u - z) = 0 := by
  dsimp only
  have hp := prox_stationary h i ht ((a + rho)⁻¹ • (a • z + rho • center))
  have he : (a + rho) • ((a + rho)⁻¹ • (a • z + rho • center)) =
      a • z + rho • center := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul]
  rw [smul_sub, he] at hp
  convert hp using 1
  module

lemma regularized_prox_minimum {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (i : Fin p.m) {a rho : ℝ}
    (ha : 0 < a) (hr : 0 ≤ rho) (center z : p.E) :
    IsMinOn (fun y => (inst.components i y + rho / 2 * ‖y - center‖ ^ 2) +
      a / 2 * ‖y - z‖ ^ 2) univ
      (inst.prox i (a + rho) ((a + rho)⁻¹ • (a • z + rho • center))) := by
  let u := inst.prox i (a + rho) ((a + rho)⁻¹ • (a • z + rho • center))
  have hc := regularized_convex (regularized_convex (h.1 i) hr center) ha.le z
  have hg (y : p.E) := regularized_hasGradient
    (regularized_hasGradient (h.2.1 i y) rho center) a z
  have hs : gradient (inst.components i) u + rho • (u - center) + a • (u - z) = 0 :=
    shifted_prox_stationary h i (by linarith) center z
  intro y _
  have hb := OracleTemplate.Gradient.convex_support hc hg u y
  change inst.components i u + rho / 2 * ‖u - center‖ ^ 2 + a / 2 * ‖u - z‖ ^ 2 ≤
    inst.components i y + rho / 2 * ‖y - center‖ ^ 2 + a / 2 * ‖y - z‖ ^ 2
  apply sub_nonneg.mp
  simpa only [hs, inner_zero_left] using hb

noncomputable abbrev regularizedParams (p : Params) (rho : ℝ) (center : p.E) : Params :=
  { p with μ := p.μ + rho, Δ := p.Δ + rho / 2 * ‖p.x0 - center‖ ^ 2 }

noncomputable def regularizedInstance {p : Params} (inst : Instance p)
    (rho : ℝ) (center : p.E) : Instance (regularizedParams p rho center) where
  components i y := inst.components i y + rho / 2 * ‖y - center‖ ^ 2
  prox i a z := inst.prox i (a + rho) ((a + rho)⁻¹ • (a • z + rho • center))

lemma regularized_objective {p : Params} (inst : Instance p) (rho : ℝ) (center x : p.E) :
    objective (regularizedInstance inst rho center) x =
      objective inst x + rho / 2 * ‖x - center‖ ^ 2 := by
  have hm : (p.m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p.m
  simp only [objective, LongTails.Setups.FiniteSumSmoothAndConvex.objective,
    regularizedInstance, regularizedParams, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma regularized_minimum_exists {p : Params} {inst : Instance p}
    (h : Assumptions p inst) {rho : ℝ} (hr : 0 < rho) (center : p.E) :
    ∃ u, IsMinOn (fun y => objective inst y + rho / 2 * ‖y - center‖ ^ 2) univ u ∧
      (objective inst p.x0 + rho / 2 * ‖p.x0 - center‖ ^ 2) -
        (objective inst u + rho / 2 * ‖u - center‖ ^ 2) ≤
          p.Δ + rho / 2 * ‖p.x0 - center‖ ^ 2 := by
  obtain ⟨xs, hxs, hgap⟩ := h.2.2.2.2.2
  have hc : Continuous (objective inst) := continuous_iff_continuousAt.mpr
    (fun x => (objective_hasGradient h x).differentiableAt.continuousAt)
  obtain ⟨u, hu⟩ := OracleTemplate.ComponentEnvelope.exists_regularized_minimum
    hc hr (fun y => hxs (mem_univ y)) center
  refine ⟨u, ?_, ?_⟩
  · intro y _
    exact hu y
  · have hlow : objective inst xs ≤ objective inst u := hxs (mem_univ u)
    have hn : 0 ≤ rho / 2 * ‖u - center‖ ^ 2 := by positivity
    linarith

lemma regularized_centering {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (rho : ℝ) (center x : p.E) (i : Fin p.m) :
    centeredGradient (regularizedInstance inst rho center) i x = centeredGradient inst i x := by
  have ho : objective (regularizedInstance inst rho center) =
      fun y => objective inst y + rho / 2 * ‖y - center‖ ^ 2 :=
    funext (regularized_objective inst rho center)
  change gradient (fun y => inst.components i y + rho / 2 * ‖y - center‖ ^ 2) x -
    gradient (objective (regularizedInstance inst rho center)) x = _
  rw [ho]
  exact regularized_centered_gradient h rho center x i

lemma regularized_assumptions {p : Params} {inst : Instance p}
    (h : Assumptions p inst) {rho : ℝ} (hr : 0 < rho) (center : p.E) :
    Assumptions (regularizedParams p rho center) (regularizedInstance inst rho center) := by
  have ho : objective (regularizedInstance inst rho center) =
      fun y => objective inst y + rho / 2 * ‖y - center‖ ^ 2 :=
    funext (regularized_objective inst rho center)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact regularized_convex (h.1 i) hr.le center
  · intro i x
    have hg := regularized_hasGradient (h.2.1 i x) rho center
    change HasGradientAt (fun y => inst.components i y + rho / 2 * ‖y - center‖ ^ 2)
      (gradient (fun y => inst.components i y + rho / 2 * ‖y - center‖ ^ 2) x) x
    rw [hg.gradient]
    exact hg
  · rw [ho]
    exact regularized_strongConvex h.2.2.1 rho center
  · intro x y
    simp only [regularized_centering h]
    exact h.2.2.2.1 x y
  · intro i a ha z
    exact regularized_prox_minimum h i ha hr.le center z
  · rw [ho]
    exact regularized_minimum_exists h hr center

end LongTails.Proofs.CappedProximalOracle
