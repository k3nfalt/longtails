import LongTails.Setups.CompositeLipschitzHessian
import LongTails.Proofs.CubicRegularization
import LongTails.Proofs.CompositeExtrapolation
import Mathlib.Analysis.LocallyConvex.Separation

namespace LongTails.Proofs.CompositeModel

open LongTails.Setups.CompositeLipschitzHessian
open LongTails.Proofs.CubicRegularization
open scoped RealInnerProductSpace

noncomputable def smoothValue {p : Params} (q : Model p) (z : p.E) : ℝ :=
  ⟪q.linear, z - q.center⟫ + ⟪z - q.center, q.quadratic (z - q.center)⟫ / 2 +
    q.cubic * cubic (z - q.center)

lemma quadratic_bregman {p : Params} (q : Model p)
    (hs : ∀ x y, ⟪x, q.quadratic y⟫ = ⟪q.quadratic x, y⟫) (z u : p.E) :
    smoothValue q u - smoothValue q z - ⟪q.derivative z, u - z⟫ =
      ⟪u - z, q.quadratic (u - z)⟫ / 2 +
        q.cubic * (cubic (u - q.center) - cubic (z - q.center) -
          ⟪cubicGradient (z - q.center), u - z⟫) := by
  have ht (x y : p.E) : ⟪x, q.quadratic y⟫ = ⟪y, q.quadratic x⟫ :=
    (hs x y).trans (real_inner_comm _ _)
  simp only [smoothValue, Model.derivative, cubicGradient, inner_add_left,
    inner_sub_left, inner_sub_right, real_inner_smul_left, map_sub]
  simp only [← hs]
  rw [ht u z, ht u q.center, ht z q.center]
  ring

lemma solution_growth {p : Params} (q : Model p) (F : Problem p)
    (hv : q.valid) {z u : p.E} (hz : q.solution F z) (hu : u ∈ F.domain) :
    q.cubic * ‖u - z‖ ^ 3 / 6 + ⟪u - z, q.quadratic (u - z)⟫ / 2 ≤
      smoothValue q u + q.scale * F.ψ u - (smoothValue q z + q.scale * F.ψ z) := by
  have hb := cubic_bregman_lower (u - q.center) (z - q.center)
  have hd : u - q.center - (z - q.center) = u - z := by abel
  rw [hd] at hb
  have hm := mul_le_mul_of_nonneg_left hb hv.2.1
  have he := quadratic_bregman q hv.2.2.1 z u
  have hc := hz.2 u hu
  nlinarith

lemma solution_unique {p : Params} (q : Model p) (F : Problem p)
    (hv : q.valid) {z u : p.E} (hz : q.solution F z) (hu : q.solution F u) : z = u := by
  have h₁ := solution_growth q F hv hz hu.1
  have h₂ := solution_growth q F hv hu hz.1
  have hq₁ := hv.2.2.2.1 (u - z)
  have hq₂ := hv.2.2.2.1 (z - u)
  have hn : 0 ≤ ‖u - z‖ ^ 3 := pow_nonneg (norm_nonneg _) _
  rw [norm_sub_rev z u] at h₂
  rcases hv.2.2.2.2 with hc | ⟨μ, hμ, hl⟩
  · have hz0 : ‖u - z‖ ^ 3 = 0 := by nlinarith
    have hnorm : ‖u - z‖ = 0 := (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hz0
    exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm
  · have hlower := hl (u - z)
    have hc := mul_nonneg hv.2.1 hn
    have hqle : μ * ‖u - z‖ ^ 2 ≤ 0 := by linarith
    have hsq : ‖u - z‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hμ).mp (by simpa using hqle)
    have hnorm : ‖u - z‖ = 0 := sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
    exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

lemma smoothValue_hasGradientAt {p : Params} (q : Model p)
    (hs : ∀ x y, ⟪x, q.quadratic y⟫ = ⟪q.quadratic x, y⟫) (z : p.E) :
    HasGradientAt (smoothValue q) (q.derivative z) z := by
  have hd := (hasFDerivAt_id (𝕜 := ℝ) z).sub_const q.center
  have hl := (innerSL ℝ q.linear).hasFDerivAt.comp z hd
  have hq := (hd.inner ℝ (q.quadratic.hasFDerivAt.comp z hd)).const_mul (1 / 2 : ℝ)
  have hc := ((cubic_hasFDerivAt (z - q.center)).comp z hd).const_mul q.cubic
  have h := (hl.add hq).add hc
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · ext w
    simp [smoothValue, Function.comp_def]
    ring
  · ext v
    simp [Model.derivative, cubicGradient, InnerProductSpace.toDual_apply_apply]
    have ht (w : p.E) : ⟪v, q.quadratic w⟫ = ⟪w, q.quadratic v⟫ :=
      (hs v w).trans (real_inner_comm _ _)
    simp only [inner_sub_left, inner_sub_right, ← hs, ht]
    ring

lemma solution_iff_minimizer {p : Params} (q : Model p) (F : Problem p)
    (hv : q.valid) (hψ : ConvexOn ℝ F.domain F.ψ) (z : p.E) :
    q.solution F z ↔ z ∈ F.domain ∧ ∀ u ∈ F.domain,
      smoothValue q z + q.scale * F.ψ z ≤ smoothValue q u + q.scale * F.ψ u := by
  constructor
  · intro hz
    refine ⟨hz.1, fun u hu => ?_⟩
    have h := solution_growth q F hv hz hu
    have hc := mul_nonneg hv.2.1 (pow_nonneg (norm_nonneg (u - z)) 3)
    have hq := hv.2.2.2.1 (u - z)
    linarith
  · rintro ⟨hz, hm⟩
    refine ⟨hz, fun u hu => ?_⟩
    have hp : ConvexOn ℝ F.domain (fun w => q.scale * F.ψ w) := hψ.smul hv.1.le
    have h := CompositeExtrapolation.composite_optimality hp hz
      (smoothValue_hasGradientAt q hv.2.2.1 z) hm hu
    linarith

lemma affine_minorant {p : Params} (F : Problem p)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    {x0 : p.E} (hx0 : x0 ∈ F.domain) :
    ∃ (a : p.E →L[ℝ] ℝ) (c : ℝ), ∀ x ∈ F.domain, c + a x ≤ F.ψ x := by
  let T : Set (p.E × ℝ) := {z | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2}
  have hnot : (x0, F.ψ x0 - 1) ∉ T := by simp [T]
  obtain ⟨l, α, hlow, hhigh⟩ := geometric_hahn_banach_point_closed hψ.convex_epigraph hclosed hnot
  let b := l (0, 1)
  have hexpand (x : p.E) (t : ℝ) : l (x, t) = l (x, 0) + t * b := by
    have he : (x, t) = (x, 0) + t • (0, (1 : ℝ)) := by simp
    rw [he, map_add, map_smul]
    rfl
  have hb : 0 < b := by
    have ht := hhigh (x0, F.ψ x0) ⟨hx0, le_rfl⟩
    rw [hexpand] at hlow ht
    linarith
  let a : p.E →L[ℝ] ℝ := (-b⁻¹) • l.comp (ContinuousLinearMap.inl ℝ p.E ℝ)
  refine ⟨a, α / b, fun x hx => ?_⟩
  have ht := (hhigh (x, F.ψ x) ⟨hx, le_rfl⟩).le
  rw [hexpand] at ht
  have he : b * (α / b + a x) = α - l (x, 0) := by
    simp only [a, smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul]
    field_simp
    ring
  apply (mul_le_mul_iff_right₀ hb).mp
  rw [he]
  linarith

lemma closed_model_epigraph {p : Params} (q : Model p) (F : Problem p) (hv : q.valid)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2}) :
    IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧
      smoothValue q z.1 + q.scale * F.ψ z.1 ≤ z.2} := by
  have hcont : Continuous (smoothValue q) := continuous_iff_continuousAt.mpr
    (fun z => (smoothValue_hasGradientAt q hv.2.2.1 z).hasFDerivAt.continuousAt)
  have ht : Continuous (fun z : p.E × ℝ => (z.1, (z.2 - smoothValue q z.1) / q.scale)) :=
    continuous_fst.prodMk ((continuous_snd.sub (hcont.comp continuous_fst)).div_const q.scale)
  convert hclosed.preimage ht using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  apply and_congr_right
  intro _
  rw [le_div_iff₀ hv.1]
  constructor <;> intro h <;> nlinarith

lemma epigraph_attainment {p : Params} {C : Set p.E} {M : p.E → ℝ} {x0 center : p.E}
    (hx0 : x0 ∈ C) (hepi : IsClosed {z : p.E × ℝ | z.1 ∈ C ∧ M z.1 ≤ z.2})
    {c K R : ℝ} (hK : 0 ≤ K)
    (hlower : ∀ x ∈ C, c - K * ‖x - center‖ ≤ M x)
    (hradius : ∀ x ∈ C, M x ≤ M x0 → ‖x - center‖ ≤ R) :
    ∃ z ∈ C, ∀ u ∈ C, M z ≤ M u := by
  let S : Set (p.E × ℝ) := {z | z.1 ∈ C ∧ M z.1 ≤ z.2 ∧ z.2 ≤ M x0}
  have hsclosed : IsClosed S := by
    convert hepi.inter (isClosed_le continuous_snd (continuous_const : Continuous (fun _ : p.E × ℝ => M x0))) using 1
    ext z
    simp [S, and_assoc]
  have hsubset : S ⊆ Metric.closedBall center R ×ˢ Set.Icc (c - K * R) (M x0) := by
    intro z hz
    have hr := hradius z.1 hz.1 (hz.2.1.trans hz.2.2)
    have hl := hlower z.1 hz.1
    have hm := mul_le_mul_of_nonneg_left hr hK
    refine ⟨?_, ⟨by linarith [hz.2.1], hz.2.2⟩⟩
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hr
  have hscompact : IsCompact S :=
    ((isCompact_closedBall center R).prod isCompact_Icc).of_isClosed_subset hsclosed hsubset
  have hsnonempty : S.Nonempty := ⟨(x0, M x0), hx0, le_rfl, le_rfl⟩
  obtain ⟨z, hz, hmin⟩ := hscompact.exists_isMinOn hsnonempty continuous_snd.continuousOn
  refine ⟨z.1, hz.1, fun u hu => ?_⟩
  by_cases h : M u ≤ M x0
  · exact hz.2.1.trans (hmin (show (u, M u) ∈ S from ⟨hu, le_rfl, h⟩))
  · exact hz.2.1.trans (hz.2.2.trans (le_of_not_ge h))

lemma model_coercive_bounds {p : Params} (q : Model p) (F : Problem p) (hv : q.valid)
    {a : p.E →L[ℝ] ℝ} {c : ℝ} (ha : ∀ x ∈ F.domain, c + a x ≤ F.ψ x) :
    ∃ c₀ K k : ℝ, 0 ≤ K ∧ 0 < k ∧
      (∀ x ∈ F.domain, c₀ - K * ‖x - q.center‖ ≤ smoothValue q x + q.scale * F.ψ x) ∧
      (∀ x ∈ F.domain, 1 ≤ ‖x - q.center‖ →
        c₀ - K * ‖x - q.center‖ + k * ‖x - q.center‖ ^ 2 ≤
          smoothValue q x + q.scale * F.ψ x) := by
  let c₀ := q.scale * (c + a q.center)
  let K := ‖q.linear‖ + q.scale * ‖a‖
  have hK : 0 ≤ K := by
    have hs := hv.1.le
    dsimp [K]
    positivity
  have hbase (x : p.E) (hx : x ∈ F.domain) :
      c₀ - K * ‖x - q.center‖ + ⟪x - q.center, q.quadratic (x - q.center)⟫ / 2 +
        q.cubic * ‖x - q.center‖ ^ 3 / 3 ≤ smoothValue q x + q.scale * F.ψ x := by
    have hl := (abs_le.mp (abs_real_inner_le_norm q.linear (x - q.center))).1
    have hn := a.le_opNorm (x - q.center)
    have hlowa : -‖a‖ * ‖x - q.center‖ ≤ a (x - q.center) := by
      have hab : -‖a (x - q.center)‖ ≤ a (x - q.center) := neg_abs_le _
      linarith
    have hm := mul_le_mul_of_nonneg_left (ha x hx) hv.1.le
    have hma := mul_le_mul_of_nonneg_left hlowa hv.1.le
    rw [map_sub] at hma
    dsimp [c₀, K, smoothValue, cubic]
    nlinarith only [hl, hm, hma]
  have hglobal (x : p.E) (hx : x ∈ F.domain) :
      c₀ - K * ‖x - q.center‖ ≤ smoothValue q x + q.scale * F.ψ x := by
    have h := hbase x hx
    have hq := hv.2.2.2.1 (x - q.center)
    have hc := mul_nonneg hv.2.1 (pow_nonneg (norm_nonneg (x - q.center)) 3)
    linarith
  rcases hv.2.2.2.2 with hc | ⟨μ, hμ, hl⟩
  · refine ⟨c₀, K, q.cubic / 3, hK, by positivity, hglobal, fun x hx hr => ?_⟩
    have h := hbase x hx
    have hq := hv.2.2.2.1 (x - q.center)
    have hm := mul_le_mul_of_nonneg_right hr (sq_nonneg ‖x - q.center‖)
    have hm' := mul_le_mul_of_nonneg_left hm hc.le
    nlinarith only [h, hq, hm']
  · refine ⟨c₀, K, μ / 2, hK, by positivity, hglobal, fun x hx _ => ?_⟩
    have h := hbase x hx
    have hq := hl (x - q.center)
    have hc := mul_nonneg hv.2.1 (pow_nonneg (norm_nonneg (x - q.center)) 3)
    nlinarith only [h, hq, hc]

lemma scalar_sublevel_radius {c K k M r : ℝ} (hK : 0 ≤ K) (hk : 0 < k)
    (hgrowth : 1 ≤ r → c - K * r + k * r ^ 2 ≤ M) :
    r ≤ 1 + (K + |M - c| + 1) / k := by
  by_contra h
  have hr : 1 + (K + |M - c| + 1) / k < r := lt_of_not_ge h
  have hR : 1 ≤ 1 + (K + |M - c| + 1) / k := by
    have hd : 0 ≤ (K + |M - c| + 1) / k := by positivity
    linarith
  have hr1 : 1 ≤ r := hR.trans hr.le
  have hmul := (div_lt_iff₀ hk).mp (show (K + |M - c| + 1) / k < r by linarith)
  have hmul' := mul_lt_mul_of_pos_right hmul (by linarith : 0 < r)
  have hlin := mul_le_mul_of_nonneg_left hr1 (by positivity : 0 ≤ |M - c| + 1)
  have hgap := le_abs_self (M - c)
  have hg := hgrowth hr1
  nlinarith only [hmul', hlin, hgap, hg]

lemma solution_exists {p : Params} (q : Model p) (F : Problem p) (hv : q.valid)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    {x0 : p.E} (hx0 : x0 ∈ F.domain) : ∃ z, q.solution F z := by
  obtain ⟨a, c, ha⟩ := affine_minorant F hψ hclosed hx0
  obtain ⟨c₀, K, k, hK, hk, hlow, hgrow⟩ := model_coercive_bounds q F hv ha
  let M := fun x => smoothValue q x + q.scale * F.ψ x
  let R := 1 + (K + |M x0 - c₀| + 1) / k
  have hr (x : p.E) (hx : x ∈ F.domain) (hm : M x ≤ M x0) : ‖x - q.center‖ ≤ R := by
    exact scalar_sublevel_radius hK hk (fun h => (hgrow x hx h).trans hm)
  obtain ⟨z, hz, hm⟩ := epigraph_attainment hx0 (closed_model_epigraph q F hv hclosed)
    hK hlow hr
  exact ⟨z, (solution_iff_minimizer q F hv hψ z).mpr ⟨hz, hm⟩⟩

end LongTails.Proofs.CompositeModel
