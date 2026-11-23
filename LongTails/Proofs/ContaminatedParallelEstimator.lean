import LongTails.Proofs.DistributedContaminationConcentration
import LongTails.Proofs.DistributedContaminationMoments
import LongTails.Proofs.DistributedContaminationTuning
import LongTails.Proofs.LeonSampling

namespace LongTails.Proofs.ContaminatedParallelEstimator

open MeasureTheory ProbabilityTheory
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonTuning (resolution)
open OracleTemplate.RobustGradient
open DistributedContaminationMoments DistributedContaminationTuning DistributedContaminationConcentration

abbrev BatchIndex (p : Params) (q : ℕ) := (i : Fin p.n) × Fin (freshCount p q i)

noncomputable def centeredSum (p : Params) (q : ℕ) (c u : Fin p.n → Point p)
    (G : Fin p.n → p.Ω → Point p) (samples : Samples p) : Point p :=
  ∑ z : BatchIndex p q, ((p.n : ℝ) * freshCount p q z.1)⁻¹ •
    (centeredClip (radius p q z.1) (c z.1) (G z.1 (samples z.1 z.2)) - u z.1)

lemma fixed_centers (p : Params) (hp : spec.valid p) (q : ℕ) (hq : 1 ≤ q)
    (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ ν : Fin p.n → ProbabilityMeasure p.Ω)
    (hind : iIndepFun (fun v : Fin p.n × ℕ => fun s : Samples p => s v.1 v.2) P)
    (law : ∀ i k, HasLaw (fun s : Samples p => s i k) (mixture (p.η i) (μ i) (ν i)) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
    (x : Point p) (c : Fin p.n → Point p) (hc : ∀ i, ‖c i - gradient (f i) x‖ ≤ 12 * p.σ i) :
    P.real {s | resolution (network p) < ‖centeredSum p q c (fun i => gradient (f i) x)
      (fun i => g i x) s‖} ≤ Real.exp (-(q : ℝ)) := by
  rcases hp with ⟨hworker, _, _, hε, hpar, _, _, hfloor⟩
  let s := resolution (network p)
  let n := (p.n : ℝ)
  let m := freshCount p q
  let h (i : Fin p.n) := (p.h i : ℝ)
  let cap (i : Fin p.n) := n * s * m i / (2048 * q)
  let w (i : Fin p.n) := (n * m i)⁻¹
  let u (i : Fin p.n) := gradient (f i) x
  let Z (i : Fin p.n) (y : p.Ω) := centeredClip (radius p q i) (c i) (g i x y) - u i
  let N (i : Fin p.n) (y : p.Ω) := w i • Z i y
  let Y (z : BatchIndex p q) (ω : Samples p) := N z.1 (ω z.1 z.2)
  let M (i : Fin p.n) : Measure p.Ω := mixture (p.η i) (μ i) (ν i)
  have hs : 0 < s := by change 0 < p.ε / 512; positivity
  have hn : 0 < n := by dsimp only [n]; exact_mod_cast p.n.pos
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hi (i) : 0 < h i := by exact_mod_cast hworker i
  have hm (i) : 0 < m i := by unfold m freshCount; omega
  have hmr (i) : (0 : ℝ) < m i := by exact_mod_cast hm i
  have hweight (i) : 0 ≤ w i := inv_nonneg.mpr (mul_nonneg hn.le (hmr i).le)
  have hcap (i) : 0 < cap i := div_pos (mul_pos (mul_pos hn hs) (hmr i)) (by positivity)
  have hbatch (i) : 16777216 * (q : ℝ) * (1 + (∑ j, h j * p.σ j ^ 2) /
      ((n * s) ^ 2 * h i)) ≤ m i := by simpa only [mul_pow] using fresh_lower p q i
  have hscale (i) : 24 * p.σ i ≤ cap i := fresh_geometry (mul_pos hn hs) (hi i) (hpar i).1 hq0
    (Finset.single_le_sum (fun j _ => mul_nonneg (hi j).le (sq_nonneg (p.σ j))) (Finset.mem_univ i)) (hbatch i)
  have hrad (i) := radius_bounds (hpar i).1 (hpar i).2.1 (hpar i).2.2 (hcap i) (hscale i)
  have hR (i) : 0 ≤ radius p q i := (mul_nonneg (by norm_num) (hpar i).1).trans (hrad i).1
  have hclose (i) : ‖u i - c i‖ ≤ radius p q i / 2 := by
    rw [norm_sub_rev]
    have hh : 24 * p.σ i ≤ radius p q i := (hrad i).1
    linarith [hc i]
  have hzm (i) : Measurable (Z i) := ((measurable_centeredClip _ _).comp
    ((hg i).measurable.comp (measurable_const.prodMk measurable_id))).sub_const _
  have hzbound (i y) : ‖Z i y‖ ≤ 3 * radius p q i / 2 := centeredClip_error_bounded (hR i) (hclose i) _
  have hcM (i) := clipped_mixture (ν := (ν i : Measure _))
    ((hg i).measurable.comp (measurable_const.prodMk measurable_id))
    ((hg i).integrable x) ((hg i).unbiased x) (hR i) (hclose i) (hpar i).2.1
    (show p.η i ≤ 1 by linarith [(hpar i).2.2]) ((hg i).variance_integrable x) ((hg i).variance x)
  have hN (i) : Measurable (N i) := (hzm i).fun_const_smul _
  have hNI (i) : Integrable (N i) (M i) := (hcM i).1.fun_smul _
  have hN2 (i) : Integrable (fun y => ‖N i y‖^2) (M i) := by
    simp only [N, norm_smul, mul_pow]
    exact (hcM i).2.1.const_mul _
  let idx (z : BatchIndex p q) : Fin p.n × ℕ := (z.1, z.2)
  have hinj : Function.Injective idx := by
    rintro ⟨i,j⟩ ⟨i',j'⟩ h
    obtain rfl : i = i' := congrArg Prod.fst h
    obtain rfl : j = j' := Fin.ext (congrArg Prod.snd h)
    rfl
  have hInd : iIndepFun Y P := (hind.precomp hinj).comp (fun z => N z.1) (fun z => hN _)
  let bound (i : Fin p.n) := 13 * p.σ i * Real.sqrt (p.η i) + 2 * p.σ i ^ 2 / cap i
  have hbias (z : BatchIndex p q) : ‖∫ ω, Y z ω ∂P‖ ≤ w z.1 * bound z.1 := by
    rw [show (∫ ω, Y z ω ∂P) = ∫ y, N z.1 y ∂M z.1 from
      (law z.1 z.2).integral_comp (hNI z.1).aestronglyMeasurable]
    simp only [N, integral_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hweight _)]
    exact mul_le_mul_of_nonneg_left ((hcM z.1).2.2.1.trans (hrad z.1).2.2.1) (hweight _)
  have hsecond (z : BatchIndex p q) : (∫ ω, ‖Y z ω‖^2 ∂P) ≤ w z.1 ^ 2 * (145 * p.σ z.1 ^ 2) := by
    rw [show (∫ ω, ‖Y z ω‖ ^ 2 ∂P) = ∫ y, ‖N z.1 y‖ ^ 2 ∂M z.1 from
      (law z.1 z.2).integral_comp (hN2 z.1).aestronglyMeasurable]
    simp only [N, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, integral_const_mul]
    exact mul_le_mul_of_nonneg_left ((hcM z.1).2.2.2.trans (hrad z.1).2.2.2) (sq_nonneg _)
  have hpv := pooled_variance h p.σ (fun i => (m i : ℝ)) (mul_pos hn hs) hq0 hi hmr hbatch
  apply pooled_bernstein (Y := Y) (fun z => (hN _).comp ((measurable_pi_apply _).comp (measurable_pi_apply _)))
    hInd (fun z => (law z.1 z.2).integrable_comp (hNI _)) (fun z => (law z.1 z.2).integrable_comp (hN2 _))
    hs hq'
  · intro z ω
    change ‖w z.1 • Z z.1 _‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hweight _)]
    have hr : radius p q z.1 ≤ cap z.1 := (hrad z.1).2.1
    have hb := hzbound z.1 (ω z.1 z.2)
    apply (mul_le_mul_of_nonneg_left (hb.trans (by linarith : 3*radius p q z.1/2 ≤ 3*cap z.1/2)) (hweight _)).trans_eq
    dsimp only [w,cap]
    field_simp [ne_of_gt (hmr z.1)]
    ring
  · apply (Finset.sum_le_sum (fun z _ => hbias z)).trans
    rw [sum_repetitions m hm hn bound]
    apply pooled_bias hs hn hq0 _ _ _ hmr _ hpv
    change 512 * _ ≤ (p.n : ℝ) * (p.ε / 512)
    nlinarith only [hfloor]
  · apply (Finset.sum_le_sum (fun z _ => hsecond z)).trans
    rw [sum_square_weights m hm hn (fun i => 145 * p.σ i ^ 2)]
    simp_rw [mul_div_assoc, ← Finset.mul_sum]
    apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
    have he : 145 * (s ^ 2 / (16777216 * q)) * n ^ 2 =
        145 * ((n*s)^2/(16777216*q)) := by ring
    rw [he]
    linarith

end LongTails.Proofs.ContaminatedParallelEstimator
