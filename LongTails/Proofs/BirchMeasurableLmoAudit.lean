import LongTails.Proofs.NormBallGeometry
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.Sequences

namespace LongTails.Proofs.BirchLmoExistence

open MeasureTheory Filter
open scoped Topology
open LongTails.Setups.UscgConstant (Space)

noncomputable def projection {d : ℕ} (K : Set (Space d)) (hne : K.Nonempty)
    (hK : IsCompact K) (hconv : Convex ℝ K) (u : Space d) : Space d :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hK.isClosed.isComplete hconv u)

lemma projection_mem {d : ℕ} (K : Set (Space d)) (hne : K.Nonempty)
    (hK : IsCompact K) (hconv : Convex ℝ K) (u : Space d) :
    projection K hne hK hconv u ∈ K :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hne hK.isClosed.isComplete hconv u)).1

lemma projection_inner {d : ℕ} (K : Set (Space d)) (hne : K.Nonempty)
    (hK : IsCompact K) (hconv : Convex ℝ K) (u w : Space d) (hw : w ∈ K) :
    inner ℝ (u - projection K hne hK hconv u) (w - projection K hne hK hconv u) ≤ 0 := by
  have h := (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hne hK.isClosed.isComplete hconv u)).2
  exact (norm_eq_iInf_iff_real_inner_le_zero hconv (projection_mem K hne hK hconv u)).mp h w hw

lemma projection_nonexpansive {d : ℕ} (K : Set (Space d)) (hne : K.Nonempty)
    (hK : IsCompact K) (hconv : Convex ℝ K) (u v : Space d) :
    ‖projection K hne hK hconv u - projection K hne hK hconv v‖ ≤ ‖u - v‖ := by
  let x := projection K hne hK hconv u
  let y := projection K hne hK hconv v
  have hx : inner ℝ (u - x) (y - x) ≤ 0 :=
    projection_inner K hne hK hconv u y (projection_mem K hne hK hconv v)
  have hy : inner ℝ (v - y) (x - y) ≤ 0 :=
    projection_inner K hne hK hconv v x (projection_mem K hne hK hconv u)
  have hxy : ‖x - y‖ ^ 2 ≤ inner ℝ (u - v) (x - y) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right] at hx hy ⊢
    have hcomm := real_inner_comm y x
    linarith
  have hnorm := real_inner_le_norm (u - v) (x - y)
  have hx0 := norm_nonneg (x - y)
  have huv0 := norm_nonneg (u - v)
  change ‖x - y‖ ≤ ‖u - v‖
  nlinarith

lemma continuous_projection {d : ℕ} (K : Set (Space d)) (hne : K.Nonempty)
    (hK : IsCompact K) (hconv : Convex ℝ K) : Continuous (projection K hne hK hconv) := by
  apply LipschitzWith.continuous (K := 1)
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro u v
  simpa using projection_nonexpansive K hne hK hconv u v

lemma projection_ray_bound {d : ℕ} (K : Set (Space d)) (hne : K.Nonempty)
    (hK : IsCompact K) (hconv : Convex ℝ K) (v z : Space d)
    (hz : z ∈ K) (hmin : ∀ x ∈ K, inner ℝ v z ≤ inner ℝ v x)
    (t : ℝ) (ht : 0 ≤ t) :
    let x := projection K hne hK hconv (-t • v)
    ‖x‖ ^ 2 ≤ ‖z‖ ^ 2 ∧ t * (inner ℝ v x - inner ℝ v z) ≤ ‖z‖ ^ 2 := by
  let x := projection K hne hK hconv (-t • v)
  have h := projection_inner K hne hK hconv (-t • v) z hz
  have h0 : 0 ≤ inner ℝ v x - inner ℝ v z := sub_nonneg.mpr
    (hmin x (projection_mem K hne hK hconv (-t • v)))
  have hi : t * (inner ℝ v x - inner ℝ v z) + ‖x‖ ^ 2 ≤ inner ℝ x z := by
    change inner ℝ (-t • v - x) (z - x) ≤ 0 at h
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left] at h
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith
  have hcs := real_inner_le_norm x z
  have hprod := mul_nonneg ht h0
  have hx0 := norm_nonneg x
  have hz0 := norm_nonneg z
  have hnorm : ‖x‖ ≤ ‖z‖ := by nlinarith
  exact ⟨(sq_le_sq₀ hx0 hz0).mpr hnorm, by nlinarith⟩

def minimumFace {d : ℕ} (K : Set (Space d)) (v : Space d) : Set (Space d) :=
  {x | x ∈ K ∧ ∀ y ∈ K, inner ℝ v x ≤ inner ℝ v y}

lemma minimumFace_nonempty {d : ℕ} (K : Set (Space d)) (hne : K.Nonempty)
    (hK : IsCompact K) (v : Space d) : (minimumFace K v).Nonempty := by
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne (f := fun x => inner ℝ v x)
    (continuous_const.inner continuous_id).continuousOn
  exact ⟨x, hx, hmin⟩

lemma minimumFace_compact {d : ℕ} (K : Set (Space d)) (hK : IsCompact K)
    (v : Space d) : IsCompact (minimumFace K v) := by
  have hclosed : IsClosed {x : Space d | ∀ y ∈ K, inner ℝ v x ≤ inner ℝ v y} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_le (continuous_const.inner continuous_id) continuous_const
  exact hK.inter_right hclosed

lemma minimumFace_convex {d : ℕ} (K : Set (Space d)) (hconv : Convex ℝ K)
    (v : Space d) : Convex ℝ (minimumFace K v) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hconv hx.1 hy.1 ha hb hab, ?_⟩
  intro z hz
  simp only [inner_add_right, real_inner_smul_right]
  calc
    a * inner ℝ v x + b * inner ℝ v y ≤ a * inner ℝ v z + b * inner ℝ v z :=
      add_le_add (mul_le_mul_of_nonneg_left (hx.2 z hz) ha)
        (mul_le_mul_of_nonneg_left (hy.2 z hz) hb)
    _ = inner ℝ v z := by rw [← add_mul, hab, one_mul]

noncomputable def selector {d : ℕ} (K : Set (Space d)) (hne : K.Nonempty)
    (hK : IsCompact K) (hconv : Convex ℝ K) (v : Space d) : Space d :=
  projection (minimumFace K v) (minimumFace_nonempty K hne hK v)
    (minimumFace_compact K hK v) (minimumFace_convex K hconv v) 0

lemma selector_mem {d : ℕ} (K : Set (Space d)) (hne : K.Nonempty)
    (hK : IsCompact K) (hconv : Convex ℝ K) (v : Space d) :
    selector K hne hK hconv v ∈ minimumFace K v :=
  projection_mem _ _ _ _ _

lemma selector_unique_of_norm_le {d : ℕ} (K : Set (Space d)) (hne : K.Nonempty)
    (hK : IsCompact K) (hconv : Convex ℝ K) (v y : Space d)
    (hy : y ∈ minimumFace K v) (hnorm : ‖y‖ ^ 2 ≤ ‖selector K hne hK hconv v‖ ^ 2) :
    y = selector K hne hK hconv v := by
  let z := selector K hne hK hconv v
  have h := projection_inner (minimumFace K v) (minimumFace_nonempty K hne hK v)
    (minimumFace_compact K hK v) (minimumFace_convex K hconv v) 0 y hy
  change inner ℝ (0 - z) (y - z) ≤ 0 at h
  simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at h
  have heq : ‖y - z‖ ^ 2 = ‖y‖ ^ 2 - 2 * inner ℝ z y + ‖z‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm]
  have hzero : ‖y - z‖ = 0 := by nlinarith [sq_nonneg ‖y - z‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

lemma projection_ray_tendsto {d : ℕ} (K : Set (Space d)) (hne : K.Nonempty)
    (hK : IsCompact K) (hconv : Convex ℝ K) (v : Space d) :
    Tendsto (fun n : ℕ => projection K hne hK hconv (-((n : ℝ) + 1) • v))
      atTop (𝓝 (selector K hne hK hconv v)) := by
  let z := selector K hne hK hconv v
  let x : ℕ → Space d := fun n => projection K hne hK hconv (-((n : ℝ) + 1) • v)
  have hz := selector_mem K hne hK hconv v
  have hb (n : ℕ) := projection_ray_bound K hne hK hconv v z hz.1 hz.2
    ((n : ℝ) + 1) (by positivity)
  apply hK.tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun n => projection_mem K hne hK hconv _)
  intro y hy hcluster
  have hynorm : ‖y‖ ^ 2 ≤ ‖z‖ ^ 2 :=
    (isClosed_le (continuous_norm.pow 2) continuous_const).mem_of_mapClusterPt hcluster
      (Filter.Eventually.of_forall fun n => (hb n).1)
  obtain ⟨φ, hφ, hlim⟩ := hcluster.tendsto_subseq
  have hden : Tendsto (fun n : ℕ => (φ n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hupper : Tendsto (fun n : ℕ => ‖z‖ ^ 2 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hgap : Tendsto (fun n => inner ℝ v (x (φ n)) - inner ℝ v z) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sub_nonneg.mpr (hz.2 _ (projection_mem K hne hK hconv _)))
      (fun n => ?_) hupper
    exact (le_div_iff₀ (by positivity : 0 < (φ n : ℝ) + 1)).mpr (by
      simpa only [mul_comm] using (hb (φ n)).2)
  have hgap' : Tendsto (fun n => inner ℝ v (x (φ n)) - inner ℝ v z) atTop
      (𝓝 (inner ℝ v y - inner ℝ v z)) :=
    (tendsto_const_nhds.inner hlim).sub tendsto_const_nhds
  have heq : inner ℝ v y = inner ℝ v z := sub_eq_zero.mp (tendsto_nhds_unique hgap' hgap)
  apply selector_unique_of_norm_le K hne hK hconv v y ⟨hy, ?_⟩ hynorm
  intro w hw
  rw [heq]
  exact hz.2 w hw

lemma measurable_selector {d : ℕ} (K : Set (Space d)) (hne : K.Nonempty)
    (hK : IsCompact K) (hconv : Convex ℝ K) : Measurable (selector K hne hK hconv) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n : ℕ => fun v => projection K hne hK hconv (-((n : ℝ) + 1) • v))
  · intro n
    have hc : Continuous (fun v : Space d => -((n : ℝ) + 1) • v) :=
      (continuous_const : Continuous (fun _ : Space d => -((n : ℝ) + 1))).smul continuous_id
    exact ((continuous_projection K hne hK hconv).comp hc).measurable
  · exact tendsto_pi_nhds.mpr (projection_ray_tendsto K hne hK hconv)

lemma exists_norm_le_seminorm {d : ℕ} (N : Seminorm ℝ (Space d))
    (hdef : ∀ x, N x = 0 → x = 0) (hcont : Continuous N) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ≤ C * N x := by
  by_cases hs : (Metric.sphere (0 : Space d) 1).Nonempty
  · obtain ⟨y, hy, hmin⟩ := (isCompact_sphere (0 : Space d) 1).exists_isMinOn hs hcont.continuousOn
    have hy1 : ‖y‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hy
    have hy0 : y ≠ 0 := by intro h; simp [h] at hy1
    have hNy : 0 < N y := lt_of_le_of_ne (apply_nonneg N y)
      (fun h => hy0 (hdef y h.symm))
    refine ⟨(N y)⁻¹, inv_pos.mpr hNy, ?_⟩
    intro x
    by_cases hx : x = 0
    · simp [hx]
    have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Space d) 1 := by
      simpa [Metric.mem_sphere] using (norm_smul_inv_norm (𝕜 := ℝ) hx)
    have h : N y ≤ N (‖x‖⁻¹ • x) := hmin hu
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hx0] at h
    have hmul := mul_le_mul_of_nonneg_left h hx0.le
    have hbound : ‖x‖ * N y ≤ N x := by
      simpa only [← mul_assoc, mul_inv_cancel₀ hx0.ne', one_mul] using hmul
    have hres := mul_le_mul_of_nonneg_left hbound (inv_pos.mpr hNy).le
    calc
      ‖x‖ = (N y)⁻¹ * (‖x‖ * N y) := by field_simp
      _ ≤ _ := hres
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x
    have hx : x = 0 := by
      by_contra hx
      apply hs
      exact ⟨‖x‖⁻¹ • x, by simpa [Metric.mem_sphere]
        using (norm_smul_inv_norm (𝕜 := ℝ) hx)⟩
    simp [hx]

lemma compact_unit_ball {d : ℕ} (N : Seminorm ℝ (Space d))
    (hdef : ∀ x, N x = 0 → x = 0) (hcont : Continuous N) : IsCompact {x | N x ≤ 1} := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_le_seminorm N hdef hcont
  apply (isCompact_closedBall (0 : Space d) C).of_isClosed_subset (isClosed_le hcont continuous_const)
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact (hbound x).trans (by simpa using mul_le_mul_of_nonneg_left hx hC.le)

lemma convex_unit_ball {d : ℕ} (N : Seminorm ℝ (Space d)) : Convex ℝ {x | N x ≤ 1} := by
  intro x hx y hy a b ha hb hab
  change N (a • x + b • y) ≤ 1
  calc
    N (a • x + b • y) ≤ N (a • x) + N (b • y) := map_add_le_add N _ _
    _ = a * N x + b * N y := by
      simp only [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := add_le_add
      (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = 1 := by simpa using hab

lemma exists_measurable_lmo {d : ℕ} (N : Seminorm ℝ (Space d))
    (hdef : ∀ x, N x = 0 → x = 0) (hcont : Continuous N) :
    ∃ lmo : Space d → Space d, LongTails.Setups.UscgConstant.IsBallLMO N 1 lmo := by
  let K := {x | N x ≤ 1}
  have hne : K.Nonempty := ⟨0, by simp [K]⟩
  have hK : IsCompact K := compact_unit_ball N hdef hcont
  have hconv : Convex ℝ K := convex_unit_ball N
  refine ⟨selector K hne hK hconv, ?_⟩
  exact ⟨measurable_selector K hne hK hconv,
    fun v => (selector_mem K hne hK hconv v).1,
    fun v x hx => (selector_mem K hne hK hconv v).2 x hx⟩

end LongTails.Proofs.BirchLmoExistence
