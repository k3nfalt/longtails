import LongTails.Setups.NonsmoothHiddenConvex
import LongTails.Proofs.HiddenConvexGeometry
import Mathlib.Analysis.Convex.Continuous

open Set Metric InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.NonsmoothHidden

open LongTails.Setups.NonsmoothHiddenConvex LocalHiddenConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma derivative_lower_bound {c : E → E} {J : E → E →L[ℝ] E} {μ LJ : ℝ}
    (hLJ : 0 ≤ LJ) (hd : ∀ x, HasFDerivAt c (J x) x)
    (hl : ∀ x y, ‖J x - J y‖ ≤ LJ * ‖x - y‖)
    (hc : ∀ x y, μ * ‖x - y‖ ≤ ‖c x - c y‖) (x v : E) :
    μ * ‖v‖ ≤ ‖J x v‖ := by
  by_contra hn
  have hgap : 0 < μ * ‖v‖ - ‖J x v‖ := by linarith
  let t := (μ * ‖v‖ - ‖J x v‖) / (2 * (1 + LJ * ‖v‖ ^ 2))
  have ht : 0 < t := by dsimp [t]; positivity
  have hTaylor := taylor_bound hLJ convex_univ (fun y _ => hd y)
    (fun y _ z _ => hl y z) (x := x) (y := x + t • v) (mem_univ _) (mem_univ _)
  have hLow := hc (x + t • v) x
  have hTriangle := norm_le_norm_add_norm_sub (J x (t • v)) (c (x + t • v) - c x)
  rw [norm_sub_rev (J x (t • v))] at hTriangle
  simp only [add_sub_cancel_left, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht] at hTaylor hLow
  have hSum : ‖c (x + t • v) - c x‖ ≤ t * ‖J x v‖ + LJ * (t * ‖v‖) ^ 2 := by
    calc ‖c (x + t • v) - c x‖ ≤ ‖J x (t • v)‖ +
        ‖c (x + t • v) - c x - J x (t • v)‖ := hTriangle
      _ ≤ t * ‖J x v‖ + LJ * (t * ‖v‖) ^ 2 := by
        simpa only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht, add_comm] using
          add_le_add_left hTaylor ‖J x (t • v)‖
  have hDiv : μ * ‖v‖ ≤ ‖J x v‖ + LJ * t * ‖v‖ ^ 2 := by
    nlinarith [hLow.trans hSum]
  have htEq : t * (2 * (1 + LJ * ‖v‖ ^ 2)) = μ * ‖v‖ - ‖J x v‖ := by
    dsimp [t]
    exact div_mul_cancel₀ _ (by positivity)
  nlinarith [mul_nonneg hLJ (sq_nonneg ‖v‖)]

lemma hidden_continuous [FiniteDimensional ℝ E] {F H : E → ℝ} {c : E ≃ₜ E}
    (heq : ∀ x, F x = H (c x)) (hH : ConvexOn ℝ univ H) : Continuous F := by
  have hc : Continuous H := continuousOn_univ.mp (hH.continuousOn isOpen_univ)
  have hF : F = H ∘ c := funext heq
  rw [hF]
  exact hc.comp c.continuous

lemma subgradient_support {F H : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E}
    {g : E → E} {x u : E} (heq : ∀ y, F y = H (c y))
    (hg : IsPulledSubgradient H c J g x) (hpre : ∃ v, J x v = c u - c x) :
    F x + ⟪g x, u - x⟫ + ⟪g x, corr c J x u⟫ ≤ F u := by
  obtain ⟨s, hs, hp⟩ := hg
  have h := hs (c u)
  rw [← corr_spec hpre, ← hp, inner_add_right] at h
  rw [heq x, heq u]
  linarith

lemma averaged_support {F H : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E}
    {g : E → E} {x old z u : E} {t : ℝ}
    (hx : t • x = (t - 1) • old + z) (heq : ∀ y, F y = H (c y))
    (hg : IsPulledSubgradient H c J g x)
    (hpreu : ∃ v, J x v = c u - c x) (hpreold : ∃ v, J x v = c old - c x)
    (ht1 : 1 ≤ t) :
    t * (F x - F u) - (t - 1) * (F old - F u) ≤
      ⟪g x, z - u⟫ - ⟪g x, corr c J x u⟫ -
        (t - 1) * ⟪g x, corr c J x old⟫ := by
  have hu := subgradient_support heq hg hpreu
  have ho := subgradient_support heq hg hpreold
  have ho' := mul_le_mul_of_nonneg_left ho (sub_nonneg.mpr ht1)
  have hv : (u - x) + (t - 1) • (old - x) = u - z := by
    have hz : z = t • x - (t - 1) • old := by rw [hx]; abel
    rw [hz]
    simp only [smul_sub, sub_smul, one_smul]
    abel
  have hi := congrArg (fun v => ⟪g x, v⟫) hv
  simp only [inner_add_right, inner_smul_right, inner_sub_right] at hi
  simp only [inner_sub_right] at hu ho' ⊢
  linarith

lemma corrected_projected_step {b z u g q : E} {r D : ℝ}
    (hr : 0 ≤ r) (hD : 0 < D) (hu : ‖u - b‖ ≤ r) (hq : ‖q‖ ≤ r) :
    let z' := ballProj b (2 * r) (z - D⁻¹ • g)
    ⟪g, z - u - q⟫ ≤ D / 2 * (‖z - u‖ ^ 2 - ‖z' - u‖ ^ 2) +
      ‖g‖ ^ 2 / (2 * D) - D * ⟪z - z', q⟫ := by
  dsimp only
  let z' := ballProj b (2 * r) (z - D⁻¹ • g)
  let n := z - D⁻¹ • g - z'
  have hm := ballProj_margin b (z - D⁻¹ • g) u (by positivity : 0 ≤ 2 * r)
    (by simpa using hu)
  have hm' : r * ‖n‖ ≤ ⟪n, z' - u⟫ := by
    simpa only [show 2 * r / 2 = r by ring] using hm
  have hnq : ⟪n, q⟫ ≤ r * ‖n‖ := by
    calc ⟪n, q⟫ ≤ ‖n‖ * ‖q‖ := real_inner_le_norm _ _
      _ ≤ ‖n‖ * r := mul_le_mul_of_nonneg_left hq (norm_nonneg _)
      _ = r * ‖n‖ := mul_comm _ _
  have hn : ⟪n, z' - u - q⟫ ≥ 0 := by rw [inner_sub_right]; linarith
  have hg : g = D • (z - z' - n) := by
    dsimp [n]
    have hv : z - z' - (z - D⁻¹ • g - z') = D⁻¹ • g := by abel
    rw [hv, smul_smul, mul_inv_cancel₀ hD.ne', one_smul]
  have hid : ⟪z - z', z' - u⟫ =
      (‖z - u‖ ^ 2 - ‖z' - u‖ ^ 2 - ‖z - z'‖ ^ 2) / 2 := by
    have hv : z - u = (z - z') + (z' - u) := by abel
    rw [hv, norm_add_sq_real]
    ring
  have hc := real_inner_le_norm g (z - z')
  have hs := sq_nonneg (‖g‖ - D * ‖z - z'‖)
  have hy : ⟪g, z - z'⟫ - D / 2 * ‖z - z'‖ ^ 2 ≤ ‖g‖ ^ 2 / (2 * D) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * D)).2
    nlinarith
  have he : ⟪g, z - u - q⟫ = ⟪g, z - z'⟫ +
      D * (⟪z - z', z' - u⟫ - ⟪z - z', q⟫ - ⟪n, z' - u - q⟫) := by
    have hv : z - u - q = (z - z') + (z' - u - q) := by abel
    rw [hv, inner_add_right]
    conv_lhs => arg 2; rw [hg, inner_smul_left, inner_sub_left, inner_sub_right]
    simp
  change ⟪g, z - u - q⟫ ≤ _
  rw [he, hid]
  nlinarith [mul_nonneg hD.le hn]

end OracleTemplate.NonsmoothHidden
