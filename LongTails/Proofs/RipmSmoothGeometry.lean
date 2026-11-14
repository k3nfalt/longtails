import Mathlib.Tactic
import LongTails.Setups.RipmGeneral
import LongTails.Proofs.GdConvex
import LongTails.Proofs.LinearDecaySgdStep
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.MetricSpace.HausdorffDistance

open MeasureTheory
open LongTails.Setups.RipmGeneral

namespace LongTails.Proofs.RipmSmoothGeometry

noncomputable section

lemma smooth_upper {d : ℕ} (phi : Core.Vec d → ℝ) (H : Core.Vec d → Core.Vec d) (L : ℝ) (hL : 0 < L)
    (hg : ∀ x, HasGradientAt phi (H x) x)
    (hlip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖) (x y : Core.Vec d) :
    phi y ≤ phi x + inner ℝ (H x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  have hnorm : |L| = L := abs_of_pos hL
  have hbound : ∀ a b, ‖H a - H b‖ ≤ |L| * ‖a - b‖ := by
    simpa only [hnorm] using hlip
  simpa only [hnorm] using OracleTemplate.Gradient.smooth_upper_bound hg hbound x y


lemma convex_lower {d : ℕ} (phi : Core.Vec d → ℝ) (H : Core.Vec d → Core.Vec d)
    (hc : ConvexOn ℝ Set.univ phi) (hg : ∀ x, HasGradientAt phi (H x) x)
    (x y : Core.Vec d) : phi x + inner ℝ (H x) (y - x) ≤ phi y := by
  have hs := OracleTemplate.Gradient.convex_support hc hg x y
  linarith


lemma cocoercivity {d : ℕ} (phi : Core.Vec d → ℝ) (H : Core.Vec d → Core.Vec d) (L : ℝ) (hL : 0 < L)
    (hg : ∀ x, HasGradientAt phi (H x) x)
    (hlip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (hc : ConvexOn ℝ Set.univ phi) (x y : Core.Vec d) :
    ‖H x - H y‖ ^ 2 ≤ 2 * L * (phi x - phi y - inner ℝ (H y) (x - y)) := by
  exact OracleTemplate.SampledConvex.cocoercive hL hc hg hlip x y


lemma component_gradient_memLp {d m : ℕ} (I : Core.Problem d m) (L Lg : ℝ)
    (xs : Core.Vec d) (sigmaSq : ℝ) (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (x : Core.Vec d) :
    MemLp (fun i => I.grad i x) 2 (I.law : Measure I.Sample) := by
  obtain ⟨z, _, hz, _⟩ := hS.solutionMoment
  have hm (y : Core.Vec d) : Measurable (fun i => I.grad i y) :=
    hS.gradientMeasurable.comp (measurable_id.prodMk measurable_const)
  have hb : MemLp (fun i => I.grad i z) 2 I.law.toMeasure :=
    (memLp_two_iff_integrable_sq_norm (hm z).aestronglyMeasurable).mpr hz
  have hc : MemLp (fun _ : I.Sample => L * ‖x - z‖) 2 I.law.toMeasure :=
    memLp_const _
  have hd : MemLp (fun i => I.grad i x - I.grad i z) 2 I.law.toMeasure := by
    apply hc.mono' ((hm x).fun_sub (hm z)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun i => hS.componentSmooth i x z)
  simpa only [Pi.add_def, sub_add_cancel] using hd.add hb


lemma mean_hasGradient {d m : ℕ} (I : Core.Problem d m) (L Lg : ℝ)
    (xs : Core.Vec d) (sigmaSq : ℝ) (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (x : Core.Vec d) :
    HasGradientAt I.average (Core.meanGradient I x) x := by
  let A : Core.Vec d →L[ℝ] (Core.Vec d →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ (Core.Vec d)).toContinuousLinearEquiv.toContinuousLinearMap
  have hgI := MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    (component_gradient_memLp I L Lg xs sigmaSq hS x)
  have hgm : Measurable (fun i => I.grad i x) :=
    hS.gradientMeasurable.comp (measurable_id.prodMk measurable_const)
  have hbound : ∀ᵐ i ∂I.law.toMeasure, ∀ z ∈ Metric.ball x 1,
      ‖A (I.grad i z)‖ ≤ ‖I.grad i x‖ + L := by
    filter_upwards [] with i
    intro z hz
    change ‖InnerProductSpace.toDual ℝ (Core.Vec d) (I.grad i z)‖ ≤ _
    rw [(InnerProductSpace.toDual ℝ (Core.Vec d)).norm_map]
    have hz' : ‖z - x‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have ht := norm_add_le (I.grad i z - I.grad i x) (I.grad i x)
    rw [sub_add_cancel] at ht
    have hs := hS.componentSmooth i z x
    have hscale := mul_le_mul_of_nonneg_left hz'.le hS.smoothPos.le
    linarith
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z i => I.component i z) (F' := fun z i => A (I.grad i z))
    (μ := I.law.toMeasure) (bound := fun i => ‖I.grad i x‖ + L)
    (Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall (fun z => (hS.componentIntegrable z).aestronglyMeasurable))
    (hS.componentIntegrable x)
    (A.continuous.comp_aestronglyMeasurable hgm.aestronglyMeasurable)
    hbound (hgI.norm.fun_add (integrable_const L))
    (Filter.Eventually.of_forall (fun i z _ => (hS.componentGradient i z).hasFDerivAt))
  rw [A.integral_comp_comm hgI] at hd
  rw [hasGradientAt_iff_hasFDerivAt]
  rw [show I.average = (fun z => ∫ i, I.component i z ∂I.law.toMeasure) by
    funext z
    exact hS.averageEq z]
  exact hd


lemma mean_convex {d m : ℕ} (I : Core.Problem d m) (L Lg : ℝ)
    (xs : Core.Vec d) (sigmaSq : ℝ) (hS : Core.SourceAssumptions I L Lg xs sigmaSq) : ConvexOn ℝ Set.univ I.average := by
  refine ⟨convex_univ, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rw [hS.averageEq, hS.averageEq x, hS.averageEq y]
  have hi := ((hS.componentIntegrable x).const_mul a).fun_add
    ((hS.componentIntegrable y).const_mul b)
  calc
    (∫ i, I.component i (a • x + b • y) ∂I.law.toMeasure) ≤
        ∫ i, a * I.component i x + b * I.component i y ∂I.law.toMeasure := by
      apply integral_mono_ae (hS.componentIntegrable _) hi
      filter_upwards [] with i
      simpa only [smul_eq_mul] using
        (hS.componentConvex i).2 hx hy ha hb hab
    _ = _ := by
      rw [integral_add ((hS.componentIntegrable x).const_mul a)
        ((hS.componentIntegrable y).const_mul b), integral_const_mul, integral_const_mul]


lemma mean_lipschitz {d m : ℕ} (I : Core.Problem d m) (L Lg : ℝ)
    (xs : Core.Vec d) (sigmaSq : ℝ) (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (x y : Core.Vec d) :
    ‖Core.meanGradient I x - Core.meanGradient I y‖ ≤ L * ‖x - y‖ := by
  have hx := MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    (component_gradient_memLp I L Lg xs sigmaSq hS x)
  have hy := MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    (component_gradient_memLp I L Lg xs sigmaSq hS y)
  change ‖(∫ i, I.grad i x ∂I.law.toMeasure) -
    (∫ i, I.grad i y ∂I.law.toMeasure)‖ ≤ L * ‖x - y‖
  rw [← integral_sub hx hy]
  have hb := norm_integral_le_of_norm_le_const (μ := I.law.toMeasure)
    (Filter.Eventually.of_forall (fun i => hS.componentSmooth i x y))
  simpa only [MeasureTheory.probReal_univ, mul_one] using hb


lemma composite_optimality {d m : ℕ} (I : Core.Problem d m) (L Lg : ℝ)
    (xs : Core.Vec d) (sigmaSq : ℝ) (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (y x : Core.Vec d)
    (hy : IsMinOn (Core.objective I) Set.univ y) :
    Core.regularizer I y - inner ℝ (Core.meanGradient I y) (x - y) ≤ Core.regularizer I x := by
  have hL := hS.smoothPos
  classical
  have hgconv : ConvexOn ℝ Set.univ (Core.regularizer I) := by
    refine ⟨convex_univ, fun u hu v hv a b ha hb hab => ?_⟩
    change (∑ j, I.regularizers j (a • u + b • v)) ≤
      a * (∑ j, I.regularizers j u) + b * (∑ j, I.regularizers j v)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [smul_eq_mul] using (hS.regularizerConvex j).2 hu hv ha hb hab
  let c := L / 2 * ‖x - y‖ ^ 2
  let b := Core.regularizer I x - Core.regularizer I y +
    inner ℝ (Core.meanGradient I y) (x - y)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hb : 0 ≤ b := by
    apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    let t := min 1 (epsilon / (c + 1))
    have ht : 0 < t := lt_min (by norm_num) (div_pos hepsilon (by positivity))
    have ht1 : t ≤ 1 := min_le_left _ _
    have htb : t * (c + 1) ≤ epsilon :=
      (le_div_iff₀ (by positivity : 0 < c + 1)).mp (min_le_right _ _)
    have hct : c * t ≤ epsilon := by nlinarith
    let z := (1 - t) • y + t • x
    have hz : z - y = t • (x - y) := by dsimp [z]; module
    have hsm := smooth_upper I.average (Core.meanGradient I) L hS.smoothPos
      (mean_hasGradient I L Lg xs sigmaSq hS)
      (mean_lipschitz I L Lg xs sigmaSq hS) y z
    rw [hz, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hsm
    have hgc := hgconv.2 (Set.mem_univ y) (Set.mem_univ x)
      (sub_nonneg.mpr ht1) ht.le (by ring : 1 - t + t = 1)
    change Core.regularizer I z ≤ (1 - t) * Core.regularizer I y +
      t * Core.regularizer I x at hgc
    have hmin := hy (Set.mem_univ z)
    change I.average y + Core.regularizer I y ≤
      I.average z + Core.regularizer I z at hmin
    have he : 0 ≤ t * (b + c * t) := by dsimp [b, c]; nlinarith
    have hp : 0 ≤ b + c * t := (mul_nonneg_iff_of_pos_left ht).mp he
    linarith
  dsimp [b] at hb
  linarith


lemma solution_gradient_difference {d m : ℕ} (I : Core.Problem d m) (L Lg : ℝ)
    (xs : Core.Vec d) (sigmaSq : ℝ) (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (y z : Core.Vec d)
    (hy : IsMinOn (Core.objective I) Set.univ y)
    (hz : IsMinOn (Core.objective I) Set.univ z) :
    (∫ i, ‖I.grad i y - I.grad i z‖ ^ 2 ∂(I.law : Measure I.Sample)) = 0 ∧
      (∀ᵐ i ∂(I.law : Measure I.Sample), I.grad i y = I.grad i z) := by
  have hL := hS.smoothPos
  have hmy := component_gradient_memLp I L Lg xs sigmaSq hS y
  have hmz := component_gradient_memLp I L Lg xs sigmaSq hS z
  have hzI := MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hmz
  have hd : MemLp (fun i => I.grad i y - I.grad i z) 2 I.law.toMeasure := by
    simpa only [Pi.sub_def] using hmy.sub hmz
  have hdI := (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd
  have hiI := hzI.inner_const (𝕜 := ℝ) (y - z)
  have hrI := ((hS.componentIntegrable y).sub' (hS.componentIntegrable z)).sub' hiI
  have hinter :
      (∫ i, inner ℝ (I.grad i z) (y - z) ∂I.law.toMeasure) =
        inner ℝ (Core.meanGradient I z) (y - z) := by
    calc
      _ = ∫ i, inner ℝ (y - z) (I.grad i z) ∂I.law.toMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun i => real_inner_comm _ _)
      _ = inner ℝ (y - z) (Core.meanGradient I z) := integral_inner hzI (y - z)
      _ = _ := real_inner_comm _ _
  have hb := integral_mono_ae hdI (hrI.const_mul (2 * L))
    (Filter.Eventually.of_forall (fun i =>
      cocoercivity (I.component i) (I.grad i) L hS.smoothPos
        (hS.componentGradient i) (hS.componentSmooth i) (hS.componentConvex i) y z))
  rw [integral_const_mul, integral_sub
      ((hS.componentIntegrable y).sub' (hS.componentIntegrable z)) hiI,
    integral_sub (hS.componentIntegrable y) (hS.componentIntegrable z), hinter,
    ← hS.averageEq y, ← hS.averageEq z] at hb
  have hopt := composite_optimality I L Lg xs sigmaSq hS z y hz
  have heq : Core.objective I y = Core.objective I z :=
    le_antisymm (hy (Set.mem_univ z)) (hz (Set.mem_univ y))
  change I.average y + Core.regularizer I y =
    I.average z + Core.regularizer I z at heq
  have hbreg : I.average y - I.average z -
      inner ℝ (Core.meanGradient I z) (y - z) ≤ 0 := by linarith
  have hnonneg : 0 ≤ (∫ i, ‖I.grad i y - I.grad i z‖ ^ 2 ∂I.law.toMeasure) :=
    integral_nonneg (fun i => sq_nonneg _)
  have hzero : (∫ i, ‖I.grad i y - I.grad i z‖ ^ 2 ∂I.law.toMeasure) = 0 := by
    have hm := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * L) hbreg
    linarith
  refine ⟨hzero, ?_⟩
  have hae := (integral_eq_zero_iff_of_nonneg (fun i => sq_nonneg _) hdI).mp hzero
  filter_upwards [hae] with i hi
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hi))


lemma solution_moment_transfer {d m : ℕ} (I : Core.Problem d m) (L Lg : ℝ)
    (xs : Core.Vec d) (sigmaSq : ℝ) (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (y : Core.Vec d)
    (hy : IsMinOn (Core.objective I) Set.univ y) :
    Integrable (fun i => ‖I.grad i y‖ ^ 2) (I.law : Measure I.Sample) ∧
      (∫ i, ‖I.grad i y‖ ^ 2 ∂(I.law : Measure I.Sample)) = sigmaSq := by
  obtain ⟨z, hzmin, hzI, hzEq⟩ := hS.solutionMoment
  have he := (solution_gradient_difference I L Lg xs sigmaSq hS y z hy hzmin).2
  have he2 : (fun i => ‖I.grad i y‖ ^ 2) =ᵐ[I.law.toMeasure]
      (fun i => ‖I.grad i z‖ ^ 2) := by
    filter_upwards [he] with i hi
    rw [hi]
  exact ⟨hzI.congr he2.symm, (integral_congr_ae he2).trans hzEq⟩


lemma nearest_minimizer {d m : ℕ} (I : Core.Problem d m) (L Lg : ℝ)
    (xs : Core.Vec d) (sigmaSq : ℝ) (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (x0 : Core.Vec d) :
    (Core.solutionSet I).Nonempty ∧ IsClosed (Core.solutionSet I) ∧
      ∃ y, IsMinOn (Core.objective I) Set.univ y ∧ ‖x0 - y‖ ^ 2 = Core.distanceSq I x0 := by
  classical
  have hf : Continuous I.average := continuous_iff_continuousAt.mpr
    (fun x => (mean_hasGradient I L Lg xs sigmaSq hS x).differentiableAt.continuousAt)
  have hg : Continuous (Core.regularizer I) := by
    change Continuous (fun x => ∑ j, I.regularizers j x)
    apply continuous_finsetSum
    intro j hj
    exact continuousOn_univ.mp
      (ConvexOn.continuousOn isOpen_univ (hS.regularizerConvex j))
  have hh : Continuous (Core.objective I) := hf.add hg
  have heq : Core.solutionSet I = {x | Core.objective I x = Core.objective I xs} := by
    ext x
    change IsMinOn (Core.objective I) Set.univ x ↔ _
    constructor
    · intro hx
      exact le_antisymm (hx (Set.mem_univ xs)) (hS.minimizer (Set.mem_univ x))
    · intro hx y hy
      rw [hx]
      exact hS.minimizer hy
  have hclosed : IsClosed (Core.solutionSet I) := by
    rw [heq]
    exact isClosed_eq hh continuous_const
  have hne : (Core.solutionSet I).Nonempty := ⟨xs, hS.minimizer⟩
  obtain ⟨y, hy, hdist⟩ := hclosed.exists_infDist_eq_dist hne x0
  refine ⟨hne, hclosed, y, hy, ?_⟩
  change ‖x0 - y‖ ^ 2 = (Metric.infDist x0 (Core.solutionSet I)) ^ 2
  rw [hdist, dist_eq_norm]


end

end LongTails.Proofs.RipmSmoothGeometry
