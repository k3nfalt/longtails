import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped RealInnerProductSpace

namespace LongTails.Proofs.GradientDependentCurvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma endpoint_interpolation {v v' v'' : ℝ → E} {G M t : ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' (v'' x) x)
    (hG : 0 ≤ G) (hM : 0 ≤ M)
    (h0 : ‖v 0‖ ≤ G) (h1 : ‖v 1‖ ≤ G)
    (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖v'' x‖ ≤ M)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖v t‖ ≤ G + M / 8 := by
  let u := v t
  let c := ‖u‖ * M
  let q := fun x : ℝ => ⟪u, v x⟫ + c / 2 * x ^ 2
  let q' := fun x : ℝ => ⟪u, v' x⟫ + c * x
  let q'' := fun x : ℝ => ⟪u, v'' x⟫ + c
  have hq (x : ℝ) : HasDerivAt q (q' x) x := by
    convert ((hasDerivAt_const x u).inner ℝ (hv x)).add
      (((hasDerivAt_id x).pow 2).const_mul (c / 2)) using 1 <;>
      simp [q, q', Pi.add_def]; ring
  have hq' (x : ℝ) : HasDerivAt q' (q'' x) x := by
    convert ((hasDerivAt_const x u).inner ℝ (hv' x)).add
      ((hasDerivAt_id x).const_mul c) using 1 <;> simp [q', q'', Pi.add_def]
  have hqc : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) q := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun x _ => (hq x).continuousAt.continuousWithinAt)
      (fun x _ => (hq x).hasDerivWithinAt)
      (fun x _ => (hq' x).hasDerivWithinAt)
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := interior_subset hx
    have hi := (abs_le.mp (abs_real_inner_le_norm u (v'' x))).1
    have hm := mul_le_mul_of_nonneg_left (hb x hx') (norm_nonneg u)
    dsimp [q'', c]
    linarith
  have hh := hqc.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
    (show 0 ≤ 1 - t by linarith [ht.2]) ht.1 (by ring : 1 - t + t = 1)
  have hi0 := (real_inner_le_norm u (v 0)).trans
    (mul_le_mul_of_nonneg_left h0 (norm_nonneg u))
  have hi1 := (real_inner_le_norm u (v 1)).trans
    (mul_le_mul_of_nonneg_left h1 (norm_nonneg u))
  have he0 := mul_le_mul_of_nonneg_left hi0 (show 0 ≤ 1 - t by linarith [ht.2])
  have he1 := mul_le_mul_of_nonneg_left hi1 ht.1
  simp [q] at hh
  have hu : ⟪u, v t⟫ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
  rw [hu] at hh
  have hc : 0 ≤ c := mul_nonneg (norm_nonneg u) hM
  have hs := mul_nonneg hc (sq_nonneg (t - 1 / 2))
  have hn : ‖u‖ ^ 2 ≤ ‖u‖ * (G + M / 8) := by
    dsimp [c] at hh hs
    nlinarith
  by_cases hz : ‖u‖ = 0
  · change ‖u‖ ≤ _
    rw [hz]
    positivity
  · have hp : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hz)
    change ‖u‖ ≤ _
    nlinarith

lemma gradient_dependent_segment_bound {v v' v'' : ℝ → E} {G L₀ L₁ r : ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' (v'' x) x)
    (hG : 0 ≤ G) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
    (h0 : ‖v 0‖ ≤ G) (h1 : ‖v 1‖ ≤ G)
    (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖v'' x‖ ≤ r ^ 2 * (L₀ + L₁ * ‖v x‖))
    (hr : L₁ * r ^ 2 ≤ 4) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖v t‖ ≤ 2 * G + L₀ * r ^ 2 / 4 := by
  have hc : Continuous (fun x => ‖v x‖) :=
    (continuous_iff_continuousAt.mpr (fun x => (hv x).continuousAt)).norm
  obtain ⟨a, ha, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩) hc.continuousOn
  have hbound (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      ‖v'' x‖ ≤ r ^ 2 * (L₀ + L₁ * ‖v a‖) := by
    apply (hb x hx).trans
    gcongr
    exact hmax hx
  have h := endpoint_interpolation hv hv' hG (by positivity) h0 h1 hbound ha
  have hm := mul_le_mul_of_nonneg_right hr (norm_nonneg (v a))
  have ha_bound : ‖v a‖ ≤ 2 * G + L₀ * r ^ 2 / 4 := by nlinarith
  exact fun t ht => (hmax ht).trans ha_bound

lemma capped_step_estimates {r δ σ μ g h L₀ L₁ change : ℝ}
    (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hσ : 0 ≤ σ) (hμ : 0 ≤ μ)
    (hh : 0 ≤ h)
    (hcap : L₁ * r ^ 2 ≤ 1 / 10000)
    (htune : 100 * (L₀ + L₁ * g) ≤ σ)
    (hgrad : h ≤ (5 * δ / 2 + μ) * r + σ * r ^ 2 +
      2 * (L₀ + L₁ * g + L₁ * h) * r ^ 2)
    (hchange : change ≤ -(3 * δ * r ^ 2 / 4) - σ * r ^ 3 / 2 - μ * r ^ 2 / 2 +
      2 * (L₀ + L₁ * g + L₁ * h) * r ^ 3) :
    h ≤ 4 * (σ * r ^ 2 + δ * r + μ * r) ∧
      change ≤ -(σ * r ^ 3 + δ * r ^ 2 + μ * r ^ 2) / 3 := by
  have hcap_h := mul_le_mul_of_nonneg_right hcap hh
  have htune_r := mul_le_mul_of_nonneg_right htune (sq_nonneg r)
  have hs : 0 ≤ σ * r ^ 2 := mul_nonneg hσ (sq_nonneg r)
  have hd : 0 ≤ δ * r := mul_nonneg hδ hr
  have hm : 0 ≤ μ * r := mul_nonneg hμ hr
  have hbound : h ≤ 4 * (σ * r ^ 2 + δ * r + μ * r) := by
    nlinarith
  refine ⟨hbound, ?_⟩
  have hbound_r := mul_le_mul_of_nonneg_right hbound hr
  have hcap_hr := mul_le_mul_of_nonneg_right hcap (mul_nonneg hh hr)
  have htune_r3 := mul_le_mul_of_nonneg_right htune (pow_nonneg hr 3)
  have hs3 : 0 ≤ σ * r ^ 3 := mul_nonneg hσ (pow_nonneg hr 3)
  have hd2 : 0 ≤ δ * r ^ 2 := mul_nonneg hδ (sq_nonneg r)
  have hm2 : 0 ≤ μ * r ^ 2 := mul_nonneg hμ (sq_nonneg r)
  nlinarith

lemma second_order_vector_remainder {v v' v'' : ℝ → E} {M t : ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' (v'' x) x)
    (hM : 0 ≤ M)
    (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖v'' x‖ ≤ M)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖v t - v 0 - t • v' 0‖ ≤ M * t ^ 2 := by
  have hfirst (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      ‖v' x - v' 0‖ ≤ M * x := by
    simpa using norm_image_sub_le_of_norm_deriv_le_segment'
      (fun y (_ : y ∈ Set.Icc (0 : ℝ) 1) => (hv' y).hasDerivWithinAt)
      (fun y hy => hb y ⟨hy.1, hy.2.le⟩) x hx
  have hR (x : ℝ) : HasDerivAt (fun y => v y - v 0 - y • v' 0)
      (v' x - v' 0) x := by
    simpa [Pi.sub_def] using ((hv x).sub_const (v 0)).sub ((hasDerivAt_id x).smul_const (v' 0))
  have hbound (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) t) :
      ‖v' x - v' 0‖ ≤ M * t :=
    (hfirst x ⟨hx.1, hx.2.le.trans ht.2⟩).trans
      (mul_le_mul_of_nonneg_left hx.2.le hM)
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x (_ : x ∈ Set.Icc (0 : ℝ) t) => (hR x).hasDerivWithinAt)
    hbound t (show t ∈ Set.Icc (0 : ℝ) t from ⟨ht.1, le_rfl⟩)
  simpa [pow_two, mul_assoc] using h

lemma third_order_scalar_remainder {f : ℝ → ℝ} {v v' v'' : ℝ → E}
    {M : ℝ} (s : E)
    (hf : ∀ x, HasDerivAt f ⟪v x, s⟫ x)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' (v'' x) x)
    (hM : 0 ≤ M)
    (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖v'' x‖ ≤ M) :
    |f 1 - f 0 - ⟪v 0, s⟫ - ⟪v' 0, s⟫ / 2| ≤ M * ‖s‖ := by
  let R := fun x : ℝ => f x - f 0 - x * ⟪v 0, s⟫ - x ^ 2 * (⟪v' 0, s⟫ / 2)
  have hR (x : ℝ) : HasDerivAt R ⟪v x - v 0 - x • v' 0, s⟫ x := by
    convert (((hf x).sub_const (f 0)).sub
      ((hasDerivAt_id x).mul_const ⟪v 0, s⟫)).sub
      (((hasDerivAt_id x).pow 2).mul_const (⟪v' 0, s⟫ / 2)) using 1
    · rfl
    · simp only [inner_sub_left, real_inner_smul_left, id_eq]
      ring
  have hbound (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) :
      ‖⟪v x - v 0 - x • v' 0, s⟫‖ ≤ M * ‖s‖ := by
    have hrem := second_order_vector_remainder hv hv' hM hb ⟨hx.1, hx.2.le⟩
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
    have hb' : ‖v x - v 0 - x • v' 0‖ ≤ M :=
      hrem.trans (by nlinarith)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hb' (norm_nonneg s))
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun x _ => (hR x).hasDerivWithinAt) hbound
  simpa [R, Real.norm_eq_abs] using hh

end LongTails.Proofs.GradientDependentCurvature
