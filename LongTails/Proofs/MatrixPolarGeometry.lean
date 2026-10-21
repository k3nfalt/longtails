import LongTails.Algorithms.MatrixPolar
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

namespace LongTails.Algorithms.MatrixPolar

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma supportFace_compact {K : Set E} (hK : IsCompact K) (g : E →L[ℝ] ℝ) :
    IsCompact (supportFace K g) := by
  have hc : IsClosed {x : E | ∀ y ∈ K, g y ≤ g x} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun y => isClosed_iInter (fun _ =>
      isClosed_le continuous_const g.continuous))
  exact hK.inter_right hc

lemma supportFace_nonempty {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (g : E →L[ℝ] ℝ) : (supportFace K g).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne g.continuous.continuousOn
  exact ⟨x, hx, hmax⟩

lemma exists_minimumNormSupport {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (g : E →L[ℝ] ℝ) :
    ∃ x ∈ supportFace K g, ∀ y ∈ supportFace K g, ‖x‖ ≤ ‖y‖ := by
  exact (supportFace_compact hK g).exists_isMinOn (supportFace_nonempty hK hne g)
    continuous_norm.continuousOn

lemma minimumNormSupport_spec (K : Set E) (hK : IsCompact K)
    (hne : K.Nonempty) (g : E →L[ℝ] ℝ) :
    minimumNormSupport K g ∈ supportFace K g ∧
      ∀ y ∈ supportFace K g, ‖minimumNormSupport K g‖ ≤ ‖y‖ :=
  Classical.epsilon_spec (exists_minimumNormSupport hK hne g)

lemma supportFace_convex {K : Set E} (hK : Convex ℝ K) (g : E →L[ℝ] ℝ) :
    Convex ℝ (supportFace K g) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hK hx.1 hy.1 ha hb hab, ?_⟩
  intro z hz
  simp only [map_add, map_smul, smul_eq_mul]
  have hxz := mul_le_mul_of_nonneg_left (hx.2 z hz) ha
  have hyz := mul_le_mul_of_nonneg_left (hy.2 z hz) hb
  calc
    g z = a * g z + b * g z := by rw [← add_mul, hab, one_mul]
    _ ≤ a * g x + b * g y := add_le_add hxz hyz

lemma minimum_norm_unique {K : Set E} (hK : Convex ℝ K) {x y : E}
    (hx : x ∈ K) (hy : y ∈ K)
    (hminx : ∀ z ∈ K, ‖x‖ ≤ ‖z‖) (hminy : ∀ z ∈ K, ‖y‖ ≤ ‖z‖) : x = y := by
  have heq : ‖x‖ = ‖y‖ := le_antisymm (hminx y hy) (hminy x hx)
  have hm : (1 / 2 : ℝ) • (x + y) ∈ K := by
    rw [smul_add]
    exact hK hx hy (by norm_num) (by norm_num) (by norm_num)
  have hb := hminx _ hm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hb
  have hp := parallelogram_law_with_norm ℝ x y
  have hs : 4 * ‖x‖ ^ 2 ≤ ‖x + y‖ ^ 2 := by
    nlinarith [norm_nonneg x, norm_nonneg (x + y)]
  rw [← heq] at hp
  have hsq : ‖x - y‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x - y‖]
  have hz : ‖x - y‖ = 0 := (sq_eq_zero_iff).mp hsq
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma minimumNormSupport_unique {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hconvex : Convex ℝ K) (g : E →L[ℝ] ℝ) {x : E}
    (hx : x ∈ supportFace K g) (hmin : ∀ y ∈ supportFace K g, ‖x‖ ≤ ‖y‖) :
    x = minimumNormSupport K g :=
  minimum_norm_unique (supportFace_convex hconvex g) hx
    (minimumNormSupport_spec K hK hne g).1 hmin (minimumNormSupport_spec K hK hne g).2

lemma minimumNormSupport_zero {K : Set E} (hK : IsCompact K) (hzero : (0 : E) ∈ K)
    (hconvex : Convex ℝ K) : minimumNormSupport K 0 = 0 := by
  symm
  apply minimumNormSupport_unique hK ⟨0, hzero⟩ hconvex 0
  · exact ⟨hzero, by simp⟩
  · intro y _
    simp

omit [InnerProductSpace ℝ E] in
lemma closestPoint_spec {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) (u : E) :
    closestPoint K u ∈ K ∧ ∀ y ∈ K, ‖u - closestPoint K u‖ ≤ ‖u - y‖ := by
  exact Classical.epsilon_spec (hK.exists_isMinOn hne
    (show ContinuousOn (fun x : E => ‖u - x‖) K by fun_prop))

lemma closestPoint_variational {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hconvex : Convex ℝ K) (u : E) {y : E} (hy : y ∈ K) :
    inner ℝ (u - closestPoint K u) (y - closestPoint K u) ≤ 0 := by
  have hp := closestPoint_spec hK hne u
  let : Nonempty K := hne.to_subtype
  apply (norm_eq_iInf_iff_real_inner_le_zero hconvex hp.1).mp ?_ y hy
  apply le_antisymm
  · exact le_ciInf (fun z : K => hp.2 z z.property)
  · exact ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩
      (⟨closestPoint K u, hp.1⟩ : K)

lemma closestPoint_lipschitz {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hconvex : Convex ℝ K) : LipschitzWith 1 (closestPoint K) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  let p := closestPoint K u
  let q := closestPoint K v
  have hp := closestPoint_variational hK hne hconvex u (closestPoint_spec hK hne v).1
  have hq := closestPoint_variational hK hne hconvex v (closestPoint_spec hK hne u).1
  change inner ℝ (u - p) (q - p) ≤ 0 at hp
  change inner ℝ (v - q) (p - q) ≤ 0 at hq
  have hid : inner ℝ (u - v) (p - q) - ‖p - q‖ ^ 2 =
      -inner ℝ (u - p) (q - p) - inner ℝ (v - q) (p - q) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hc := abs_real_inner_le_norm (u - v) (p - q)
  have hn : ‖p - q‖ ≤ ‖u - v‖ := by
    have hi := le_abs_self (inner ℝ (u - v) (p - q))
    nlinarith [norm_nonneg (p - q), norm_nonneg (u - v)]
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using hn

lemma closestPoint_scaled_gap {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (u : E) (t : ℝ) {y : E} (hy : y ∈ K) :
    2 * t * (inner ℝ u y - inner ℝ u (closestPoint K (t • u))) ≤
      ‖y‖ ^ 2 - ‖closestPoint K (t • u)‖ ^ 2 := by
  have hp := (closestPoint_spec hK hne (t • u)).2 y hy
  have hs := pow_le_pow_left₀ (norm_nonneg _) hp 2
  simp only [norm_sub_sq_real, real_inner_smul_left] at hs
  nlinarith

lemma closestPoint_scaled_norm_le {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (u : E) {t : ℝ} (ht : 0 ≤ t) {y : E}
    (hy : y ∈ supportFace K (innerSL ℝ u)) :
    ‖closestPoint K (t • u)‖ ≤ ‖y‖ := by
  have hg := closestPoint_scaled_gap hK hne u t hy.1
  have hp := hy.2 _ (closestPoint_spec hK hne (t • u)).1
  change inner ℝ u (closestPoint K (t • u)) ≤ inner ℝ u y at hp
  have hnonneg : 0 ≤ 2 * t * (inner ℝ u y - inner ℝ u (closestPoint K (t • u))) := by
    positivity
  nlinarith [norm_nonneg y, norm_nonneg (closestPoint K (t • u))]

lemma closestPoint_scaled_support_gap {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (u : E) {t : ℝ} (ht : 0 < t) {y : E} (hy : y ∈ K) :
    inner ℝ u y ≤ inner ℝ u (closestPoint K (t • u)) + ‖y‖ ^ 2 / (2 * t) := by
  have hg := closestPoint_scaled_gap hK hne u t hy
  have hh : 2 * t * (inner ℝ u y - inner ℝ u (closestPoint K (t • u))) ≤ ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖closestPoint K (t • u)‖]
  have hd : inner ℝ u y - inner ℝ u (closestPoint K (t • u)) ≤ ‖y‖ ^ 2 / (2 * t) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * t)).mpr
    nlinarith
  linarith

lemma closestPoint_scaled_tendsto {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hconvex : Convex ℝ K) (u : E) :
    Tendsto (fun n : ℕ => closestPoint K (((n : ℝ) + 1) • u)) atTop
      (𝓝 (minimumNormSupport K (innerSL ℝ u))) := by
  apply hK.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall (fun n : ℕ => (closestPoint_spec hK hne (((n : ℝ) + 1) • u)).1))
  intro z hz hc
  obtain ⟨φ, hφ, hlim⟩ := hc.tendsto_subseq
  simp only [Function.comp_def] at hlim
  have hzface : z ∈ supportFace K (innerSL ℝ u) := by
    refine ⟨hz, ?_⟩
    intro y hy
    have hr : Tendsto (fun n : ℕ => ‖y‖ ^ 2 / (2 * ((φ n : ℝ) + 1))) atTop (𝓝 0) := by
      have hh := (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).const_mul
        (‖y‖ ^ 2 / 2)
      convert hh using 1
      · funext n
        dsimp only [Function.comp_def]
        rw [div_mul_eq_div_div]
        ring
      · simp
    have hg := ((innerSL ℝ u).continuous.tendsto z).comp hlim
    have hb := ge_of_tendsto (hg.add hr) (Eventually.of_forall (fun n =>
      closestPoint_scaled_support_gap hK hne u (by positivity : 0 < (φ n : ℝ) + 1) hy))
    simpa only [innerSL_apply_apply, add_zero] using hb
  apply minimumNormSupport_unique hK hne hconvex (innerSL ℝ u) hzface
  intro y hy
  exact le_of_tendsto hlim.norm (Eventually.of_forall (fun n =>
    closestPoint_scaled_norm_le hK hne u (by positivity : 0 ≤ (φ n : ℝ) + 1) hy))

lemma measurable_minimumNormSupport_inner [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) (hconvex : Convex ℝ K) :
    Measurable (fun u : E => minimumNormSupport K (innerSL ℝ u)) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n : ℕ => fun u : E => closestPoint K (((n : ℝ) + 1) • u))
  · intro n
    exact ((closestPoint_lipschitz hK hne hconvex).continuous.comp
      (continuous_const.smul continuous_id)).measurable
  · exact tendsto_pi_nhds.mpr (fun u => closestPoint_scaled_tendsto hK hne hconvex u)

open LongTails.Algorithms.MatrixPolar

lemma spectralBall_eq_preimage (m n : ℕ) : spectralBall m n =
    operatorEquiv m n ⁻¹' Metric.closedBall 0 1 := by
  ext X
  simp [spectralBall, spectralNorm, Metric.mem_closedBall, dist_eq_norm]

lemma spectralBall_compact (m n : ℕ) : IsCompact (spectralBall m n) := by
  rw [spectralBall_eq_preimage]
  exact (operatorEquiv m n).toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall 0 1)

lemma spectralBall_convex (m n : ℕ) : Convex ℝ (spectralBall m n) := by
  rw [spectralBall_eq_preimage]
  exact (convex_closedBall (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) 1).linear_preimage
    (operatorEquiv m n).toLinearEquiv.toLinearMap

lemma zero_mem_spectralBall (m n : ℕ) : (0 : Space m n) ∈ spectralBall m n := by
  simp [spectralBall, spectralNorm]

lemma polar_mem {m n : ℕ} (X : Space m n) : polar X ∈ spectralBall m n :=
  (minimumNormSupport_spec _ (spectralBall_compact m n)
    ⟨0, zero_mem_spectralBall m n⟩ (innerSL ℝ X)).1.1

lemma polar_maximizes {m n : ℕ} (X : Space m n) {Y : Space m n}
    (hY : Y ∈ spectralBall m n) : inner ℝ X Y ≤ inner ℝ X (polar X) :=
  (minimumNormSupport_spec _ (spectralBall_compact m n)
    ⟨0, zero_mem_spectralBall m n⟩ (innerSL ℝ X)).1.2 Y hY

lemma polar_zero (m n : ℕ) : polar (0 : Space m n) = 0 := by
  simp only [polar, map_zero]
  exact minimumNormSupport_zero (spectralBall_compact m n) (zero_mem_spectralBall m n)
    (spectralBall_convex m n)

lemma measurable_polar (m n : ℕ) : Measurable (polar (m := m) (n := n)) :=
  measurable_minimumNormSupport_inner (spectralBall_compact m n)
    ⟨0, zero_mem_spectralBall m n⟩ (spectralBall_convex m n)

lemma nuclearNorm_nonneg {m n : ℕ} (X : Space m n) : 0 ≤ nuclearNorm X := by
  unfold nuclearNorm
  positivity

lemma nuclearNorm_neg {m n : ℕ} (X : Space m n) : nuclearNorm (-X) = nuclearNorm X := by
  unfold nuclearNorm
  rw [map_neg]
  have he : (-(innerSL ℝ X)).comp (operatorEquiv m n).symm.toContinuousLinearMap =
      -((innerSL ℝ X).comp (operatorEquiv m n).symm.toContinuousLinearMap) := by
    ext U
    rfl
  exact (congrArg norm he).trans (norm_neg
    ((innerSL ℝ X).comp (operatorEquiv m n).symm.toContinuousLinearMap))

lemma nuclearNorm_add_le {m n : ℕ} (X Y : Space m n) :
    nuclearNorm (X + Y) ≤ nuclearNorm X + nuclearNorm Y := by
  simpa only [nuclearNorm, map_add, ContinuousLinearMap.add_comp] using
    norm_add_le ((innerSL ℝ X).comp (operatorEquiv m n).symm.toContinuousLinearMap)
      ((innerSL ℝ Y).comp (operatorEquiv m n).symm.toContinuousLinearMap)

lemma inner_le_nuclear_mul_spectral {m n : ℕ} (X Y : Space m n) :
    |inner ℝ X Y| ≤ nuclearNorm X * spectralNorm Y := by
  have hh := ((innerSL ℝ X).comp (operatorEquiv m n).symm.toContinuousLinearMap).le_opNorm
    (operatorEquiv m n Y)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, innerSL_apply_apply, Real.norm_eq_abs,
    nuclearNorm, spectralNorm] using hh

lemma polar_pairing_eq_nuclear {m n : ℕ} (X : Space m n) :
    inner ℝ X (polar X) = nuclearNorm X := by
  have hnonneg : 0 ≤ inner ℝ X (polar X) := by
    simpa using polar_maximizes X (zero_mem_spectralBall m n)
  apply le_antisymm
  · have hh := inner_le_nuclear_mul_spectral X (polar X)
    have hp : spectralNorm (polar X) ≤ 1 := polar_mem X
    have hn : 0 ≤ nuclearNorm X := by unfold nuclearNorm; positivity
    have ha := le_abs_self (inner ℝ X (polar X))
    nlinarith
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm hnonneg
    intro U hU
    let Y := (operatorEquiv m n).symm U
    have hy : Y ∈ spectralBall m n := by
      simp [Y, spectralBall, spectralNorm, hU]
    have hny : -Y ∈ spectralBall m n := by
      simpa only [spectralBall, Set.mem_ofPred_eq, spectralNorm, map_neg, norm_neg] using hy
    have hu := polar_maximizes X hy
    have hl := polar_maximizes X hny
    change ‖inner ℝ X Y‖ ≤ inner ℝ X (polar X)
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    simp only [inner_neg_right] at hl
    exact ⟨by linarith, hu⟩

lemma operatorEquiv_apply_coordinate {m n : ℕ} (X : Space m n)
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    operatorEquiv m n X v i = ∑ j, X (i, j) * v j := rfl

lemma operatorEquiv_apply_basis {m n : ℕ} (X : Space m n) (i : Fin m) (j : Fin n) :
    operatorEquiv m n X (EuclideanSpace.basisFun (Fin n) ℝ j) i = X (i, j) := by
  rw [operatorEquiv_apply_coordinate, EuclideanSpace.basisFun_apply]
  simp

lemma inner_eq_trace_pair {m n : ℕ} (X Y : Space m n) : inner ℝ X Y =
    ((operatorEquiv m n X).comp (operatorEquiv m n Y).adjoint).toLinearMap.trace ℝ
      (EuclideanSpace ℝ (Fin m)) := by
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm',
    ← ContinuousLinearMap.toLinearMap_comp,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    operatorEquiv_apply_basis, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end LongTails.Algorithms.MatrixPolar
