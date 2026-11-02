import LongTails.Setups.UscgConstant
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.NormBallLMO

open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO Problem ConstrainedProblem State lmoMethod uscg scg
  constantMomentum vanishingMomentum)

variable {d : ℕ} {N : Seminorm ℝ (Space d)} {R : ℝ}

lemma seminorm_le_norm {d : ℕ} (N : Seminorm ℝ (Space d)) (x : Space d) :
    N x ≤ (∑ i, N (EuclideanSpace.single i (1 : ℝ))) * ‖x‖ := by
  have hx := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hx
  calc N x = N (∑ i, x i • EuclideanSpace.single i (1 : ℝ)) := by rw [hx]
    _ ≤ ∑ i, N (x i • EuclideanSpace.single i (1 : ℝ)) :=
        Finset.le_sum_of_subadditive N (map_zero N).le (map_add_le_add N) _ _
    _ = ∑ i, |x i| * N (EuclideanSpace.single i (1 : ℝ)) := by
        simp [map_smul_eq_mul, Real.norm_eq_abs]
    _ ≤ ∑ i, ‖x‖ * N (EuclideanSpace.single i (1 : ℝ)) := by
        gcongr with i
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i
    _ = (∑ i, N (EuclideanSpace.single i (1 : ℝ))) * ‖x‖ := by rw [← Finset.mul_sum, mul_comm]

lemma seminorm_continuous {d : ℕ} (N : Seminorm ℝ (Space d)) : Continuous N := by
  have hC : 0 ≤ ∑ i, N (EuclideanSpace.single i (1 : ℝ)) := Finset.sum_nonneg fun i _ => apply_nonneg N _
  refine (LipschitzWith.of_le_add_mul (f := N) ⟨_, hC⟩ fun x y => ?_).continuous
  have h1 : N x ≤ N y + N (x - y) := by
    have := map_add_le_add N y (x - y); rwa [add_sub_cancel] at this
  have h2 := seminorm_le_norm N (x - y)
  simp only [dist_eq_norm]
  show N x ≤ N y + (∑ i, N (EuclideanSpace.single i (1 : ℝ))) * ‖x - y‖
  linarith

lemma measurable_gradient_space {d : ℕ} (f : Space d → ℝ) : Measurable (gradient f) := by
  have : gradient f = fun x => (InnerProductSpace.toDual ℝ (Space d)).symm (fderiv ℝ f x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

lemma dual_set_bdd (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (u : Space d) :
    BddAbove ((fun v => ⟪u, v⟫) '' {v | N v ≤ 1}) := by
  refine ⟨‖u‖ * R, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact (real_inner_le_norm u v).trans (mul_le_mul_of_nonneg_left (hR v hv) (norm_nonneg u))

lemma inner_le_dualNorm (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (u : Space d) {v : Space d}
    (hv : N v ≤ 1) : ⟪u, v⟫ ≤ dualNorm N u := by
  exact le_csSup (dual_set_bdd hR u) ⟨v, hv, rfl⟩

lemma dualNorm_le_of {u : Space d} {c : ℝ} (h : ∀ v, N v ≤ 1 → ⟪u, v⟫ ≤ c) :
    dualNorm N u ≤ c := by
  open scoped RealInnerProductSpace in
  (
    refine csSup_le ⟨⟪u, 0⟫, 0, by simp, rfl⟩ ?_
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv)

lemma dualNorm_nonneg (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (u : Space d) : 0 ≤ dualNorm N u := by
  have h := inner_le_dualNorm hR u (v := 0) (by simp)
  simpa using h

lemma dualNorm_le_norm (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (u : Space d) :
    dualNorm N u ≤ R * ‖u‖ := by
  open scoped RealInnerProductSpace in
  (
    refine dualNorm_le_of fun v hv => ?_
    calc ⟪u, v⟫ ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
      _ ≤ ‖u‖ * R := mul_le_mul_of_nonneg_left (hR v hv) (norm_nonneg u)
      _ = R * ‖u‖ := mul_comm _ _)

lemma dualNorm_add_le (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (u w : Space d) :
    dualNorm N (u + w) ≤ dualNorm N u + dualNorm N w := by
  refine dualNorm_le_of fun v hv => ?_
  rw [inner_add_left]
  exact add_le_add (inner_le_dualNorm hR u hv) (inner_le_dualNorm hR w hv)

lemma dualNorm_sub_le (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (u w : Space d) :
    dualNorm N u ≤ dualNorm N w + dualNorm N (u - w) := by
  have h := dualNorm_add_le hR w (u - w)
  rwa [add_sub_cancel] at h

lemma dualNorm_lipschitz (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R) :
    LipschitzWith ⟨R, hR0⟩ (dualNorm N) := by
  refine LipschitzWith.of_le_add_mul _ fun u w => ?_
  have h := dualNorm_sub_le hR u w
  have h2 := dualNorm_le_norm hR (u - w)
  simp only [dist_eq_norm]
  show dualNorm N u ≤ dualNorm N w + R * ‖u - w‖
  linarith

lemma continuous_dualNorm (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R) :
    Continuous (dualNorm N) := by
  exact (dualNorm_lipschitz hR hR0).continuous

lemma inner_le_dualNorm_mul (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0)
    (u h : Space d) : ⟪u, h⟫ ≤ dualNorm N u * N h := by
  by_cases h0 : N h = 0
  · simp [hdef h h0]
  · have hpos : 0 < N h := lt_of_le_of_ne (apply_nonneg N h) (Ne.symm h0)
    have hv : N ((N h)⁻¹ • h) ≤ 1 := by
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ h0]
    have hle := inner_le_dualNorm hR u hv
    rw [inner_smul_right] at hle
    have := mul_le_mul_of_nonneg_left hle hpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ h0, one_mul, mul_comm] at this

lemma lmo_dualNorm {ρ : ℝ} {lmo : Space d → Space d} (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo)
    (s : Space d) : ρ * dualNorm N s ≤ -⟪s, lmo s⟫ := by
  open scoped RealInnerProductSpace in
  (
    have h : dualNorm N s ≤ -⟪s, lmo s⟫ / ρ := by
      refine dualNorm_le_of fun v hv => ?_
      have hm : N (-(ρ • v)) ≤ ρ := by
        rw [map_neg_eq_map, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hρ]
        nlinarith
      have hmin := hlmo.minimal s _ hm
      rw [inner_neg_right, inner_smul_right] at hmin
      rw [le_div_iff₀ hρ]
      linarith
    rwa [le_div_iff₀ hρ, mul_comm] at h)

lemma lmo_dualNorm_eq {ρ : ℝ} {lmo : Space d → Space d} (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hρ : 0 < ρ)
    (hlmo : IsBallLMO N ρ lmo) (s : Space d) : ⟪s, lmo s⟫ = -(ρ * dualNorm N s) := by
  open scoped RealInnerProductSpace in
  (
    have h1 := lmo_dualNorm hρ hlmo s
    have hv : N (-(ρ⁻¹ • lmo s)) ≤ 1 := by
      rw [map_neg_eq_map, map_smul_eq_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ]
      rw [inv_mul_le_iff₀ hρ, mul_one]
      exact hlmo.feasible s
    have h2 := inner_le_dualNorm hR s hv
    rw [inner_neg_right, inner_smul_right] at h2
    have h3 : -⟪s, lmo s⟫ ≤ ρ * dualNorm N s := by
      have := mul_le_mul_of_nonneg_left h2 hρ.le
      rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul] at this
      exact this
    linarith)

lemma descent_on {f : Space d → ℝ} {L : ℝ} {K : Set (Space d)} (hKc : Convex ℝ K)
    (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R)
    (hdef : ∀ x, N x = 0 → x = 0) (hgrad : ∀ x ∈ K, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ K, ∀ y ∈ K, dualNorm N (gradient f x - gradient f y) ≤ L * N (x - y))
    {x y : Space d} (hx : x ∈ K) (hy : y ∈ K) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * N (y - x) ^ 2 := by
  open scoped RealInnerProductSpace in
  (
    set h := y - x
    let φ : ℝ → ℝ := fun t => f (x + t • h) - t * ⟪gradient f x, h⟫ - L / 2 * t ^ 2 * N h ^ 2
    have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • h) h t := by
      intro t
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • h ∈ K := by
      intro t ht
      have := hKc.add_smul_sub_mem hx hy ht
      simpa [h] using this
    have hφ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ
        (⟪gradient f (x + t • h), h⟫ - ⟪gradient f x, h⟫ - L / 2 * (2 * t) * N h ^ 2) t := by
      intro t ht
      have hf := ((hgrad (x + t • h) (hseg t ht)).hasFDerivAt.comp_hasDerivAt t (hline t))
      have hf' : HasDerivAt (fun t : ℝ => f (x + t • h)) ⟪gradient f (x + t • h), h⟫ t := by
        convert hf using 1
        · rfl
        · rw [InnerProductSpace.toDual_apply_apply]
      have h2 : HasDerivAt (fun t : ℝ => t * ⟪gradient f x, h⟫) ⟪gradient f x, h⟫ t := by
        simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, h⟫
      have h3 : HasDerivAt (fun t : ℝ => L / 2 * t ^ 2 * N h ^ 2) (L / 2 * (2 * t) * N h ^ 2) t := by
        have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (N h ^ 2)
        simpa using this
      exact (hf'.sub h2).sub h3
    have hmono : AntitoneOn φ (Set.Icc 0 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
      · exact fun t ht => (hφ t ht).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (hφ t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hφ t (Set.Ioo_subset_Icc_self ht)).deriv]
        have hh := inner_le_dualNorm_mul hR hdef (gradient f (x + t • h) - gradient f x) h
        have hl := hlip (x + t • h) (hseg t (Set.Ioo_subset_Icc_self ht)) x hx
        rw [add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ht.1] at hl
        rw [inner_sub_left] at hh
        have hN := apply_nonneg N h
        have hd := dualNorm_nonneg hR (gradient f (x + t • h) - gradient f x)
        have : dualNorm N (gradient f (x + t • h) - gradient f x) * N h ≤ L * (t * N h) * N h :=
          mul_le_mul_of_nonneg_right hl hN
        nlinarith
    have h01 := hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
      zero_le_one
    simp only [φ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_pow, mul_one, one_mul,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h01
    have hxy : x + h = y := by simp [h]
    rw [hxy] at h01
    linarith)

lemma descent {f : Space d → ℝ} {L : ℝ} (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R)
    (hdef : ∀ x, N x = 0 → x = 0) (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, dualNorm N (gradient f x - gradient f y) ≤ L * N (x - y))
    (x y : Space d) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * N (y - x) ^ 2 := by
  exact descent_on convex_univ hR hdef (fun x _ => hgrad x) (fun x _ y _ => hlip x y)
    (Set.mem_univ x) (Set.mem_univ y)

end OracleTemplate.NormBallLMO
