import LongTails.Proofs.SphericalPreferenceIntegration

open MeasureTheory Metric Set Filter
open scoped RealInnerProductSpace NNReal

namespace LongTails.Proofs.SphericalPreferenceOracle

open OracleTemplate LongTails.Setups.SphericalRandomUtility LongTails.Algorithms.SphericalPreferenceDescent
open LongTails.Proofs.SphericalPreferenceStep LongTails.Proofs.SphericalPreferenceIntegration
open LongTails.Proofs.SphericalPreferenceSecant LongTails.Proofs.SphericalPreferenceDirection

abbrev Sample (p : Params) := Draw p.d × Point p.d

noncomputable def sampleLaw (p : Params) (n : ℕ) (μ : ProbabilityMeasure (Point p.d)) :
    ProbabilityMeasure (Sample p) :=
  ⟨(drawLaw p n : Measure _).prod (μ : Measure (Point p.d)), inferInstance⟩

noncomputable def response (p : Params) (n : ℕ) (f : Point p.d → ℝ) (x : Feasible p) (a : Sample p) : Bool :=
  comparePair f (pair p n x a.1) a.2

noncomputable def gain (p : Params) (n : ℕ) (f : Point p.d → ℝ) (x o : Feasible p) (a : Sample p) : ℝ :=
  (if response p n f x a then 1 else -1) * ⟪a.1.2,x.val-o.val⟫

lemma direction_map {d : ℕ} [NeZero d] :
    (directionLaw d : Measure (Point d)) =
      (ZerothOrder.sphereLaw (Point d) : Measure (sphere (0 : Point d) 1)).map Subtype.val := by
  simp [directionLaw, NeZero.ne d]

lemma unfold_integral (p : Params) [NeZero p.d] (n : ℕ) (μ : ProbabilityMeasure (Point p.d))
    (g : Sample p → ℝ) (hm : Measurable g) (hi : Integrable g (sampleLaw p n μ : Measure (Sample p))) :
    (∫ a, g a ∂(sampleLaw p n μ : Measure (Sample p))) =
      ∫ w, ∫ u : sphere (0 : Point p.d) 1, ∫ z, g ((w,u),z) ∂(μ : Measure (Point p.d))
      ∂(ZerothOrder.sphereLaw (Point p.d) : Measure _) ∂(jitterLaw p.d (radius p n) : Measure _) := by
  let J : Measure (Point p.d) := jitterLaw p.d (radius p n)
  let D : Measure (Point p.d) := directionLaw p.d
  change (∫ a, g a ∂(J.prod D).prod (μ : Measure _)) = _
  change Integrable g ((J.prod D).prod (μ : Measure _)) at hi
  rw [integral_prod _ hi, integral_prod _ hi.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [] with w
  dsimp only [D]
  rw [direction_map, integral_map measurable_subtype_coe.aemeasurable]
  · exact ((hm.comp (show Measurable (fun q : Point p.d × Point p.d => ((w,q.1),q.2)) by fun_prop)).stronglyMeasurable.integral_prod_right').aestronglyMeasurable

lemma measurable_pair (p : Params) (n : ℕ) :
    Measurable (fun q : Feasible p × Draw p.d => pair p n q.1 q.2) := by
  have hp : Measurable (project p) := (measurable_clip (E := Point p.d) p.R).subtype_mk
  unfold pair
  fun_prop

lemma measurable_response (p : Params) (n : ℕ) (f : Point p.d → ℝ)
    (hm : Measurable (Function.uncurry (comparePair (p := p) f))) :
    Measurable (fun q : Feasible p × Sample p => response p n f q.1 q.2) := by
  exact hm.comp ( ((measurable_pair p n).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
    (measurable_snd.comp measurable_snd))

lemma measurable_gain (p : Params) (n : ℕ) (f : Point p.d → ℝ) (x o : Feasible p)
    (hm : Measurable (Function.uncurry (comparePair (p := p) f))) : Measurable (gain p n f x o) := by
  have hr := (measurable_response p n f hm).comp (measurable_const (a := x) |>.prodMk measurable_id)
  unfold gain
  apply Measurable.mul _ (by fun_prop)
  exact Measurable.ite (hr (measurableSet_singleton true)) measurable_const measurable_const

lemma direction_ae (p : Params) [NeZero p.d] (n : ℕ) (μ : ProbabilityMeasure (Point p.d)) :
    ∀ᵐ a ∂(sampleLaw p n μ : Measure (Sample p)), ‖a.1.2‖ = 1 := by
  have hd : ∀ᵐ u ∂(directionLaw p.d : Measure (Point p.d)), ‖u‖ = 1 := by
    rw [direction_map]
    exact ae_map_iff measurable_subtype_coe.aemeasurable (measurable_norm (measurableSet_singleton 1)) |>.mpr
      (Eventually.of_forall fun u => mem_sphere_zero_iff_norm.mp u.property)
  exact Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae hd)

lemma gain_integrable (p : Params) [NeZero p.d] (n : ℕ) (μ : ProbabilityMeasure (Point p.d))
    (f : Point p.d → ℝ) (x o : Feasible p) (hm : Measurable (Function.uncurry (comparePair (p := p) f))) :
    Integrable (gain p n f x o) (sampleLaw p n μ : Measure (Sample p)) := by
  apply Integrable.of_bound (measurable_gain p n f x o hm).aestronglyMeasurable ‖x.val-o.val‖
  filter_upwards [direction_ae p n μ] with a ha
  have h := abs_real_inner_le_norm a.1.2 (x.val-o.val)
  rw [ha, one_mul] at h
  cases hb : response p n f x a <;> simpa [gain,hb] using h

lemma gain_bound (p : Params) [NeZero p.d] {n : ℕ} (hn : 0 < n) (hd : 2 ≤ p.d)
    (hR : 0 < p.R) (hB : 0 < p.B) (μ : ProbabilityMeasure (Point p.d))
    (hs : Spherical (μ : Measure (Point p.d))) (hq : 1/2 ≤ (μ : Measure (Point p.d)).real (closedBall 0 (2*p.B)))
    (f F : Point p.d → ℝ) (he : EqOn f F (closedBall 0 p.R)) (hL : LipschitzWith ⟨p.B,hB.le⟩ F)
    (hc : ConvexOn ℝ (closedBall 0 p.R) F) (x o : Feasible p) (hmin : IsMinOn F (closedBall 0 p.R) o.val)
    (hm : Measurable (Function.uncurry (comparePair (p := p) f))) :
    (F x-F o)/(192*p.B*Real.sqrt p.d) - 3*radius p n -
      p.B*(3*radius p n)/(192*p.B*Real.sqrt p.d) - 2*(p.d : ℝ)*probe p n/radius p n*‖x.val-o.val‖ ≤
      ∫ a, gain p n f x o a ∂(sampleLaw p n μ : Measure (Sample p)) := by
  let r := radius p n
  let h := probe p n
  let m := (1-2*r/p.R) • x.val
  obtain ⟨_, hr, hrR, hh, hhr⟩ := tuning p hn hd hR
  have geom (w : Point p.d) (hw : w ∈ ball (0 : Point p.d) r) (u : sphere (0 : Point p.d) 1) :=
    jitter_geometry (show 0 < (p.R : ℝ) from hR) hr.le hrR hh.le hhr.le x.val w (u : Point p.d)
      (mem_closedBall_zero_iff.mp x.property) (mem_ball_zero_iff.mp hw).le (mem_sphere_zero_iff_norm.mp u.property)
  let e : sphere (0 : Point p.d) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hy (w) (hw : w ∈ ball (0 : Point p.d) r) :
      m+w ∈ closedBall 0 (p.R : ℝ) ∧ ‖x.val-(m+w)‖ ≤ 3*r := by
    have hgeo := geom w hw e
    exact ⟨mem_closedBall_zero_iff.mpr (hgeo.1.trans (sub_le_self _ hr.le)),hgeo.2.1⟩
  have hfeet (u : sphere (0 : Point p.d) 1) (w) (hw : w ∈ ball (0 : Point p.d) r) :
      m+w-h • (u : Point p.d) ∈ closedBall 0 p.R ∧ m+w+h • (u : Point p.d) ∈ closedBall 0 p.R :=
    ⟨mem_closedBall_zero_iff.mpr (geom w hw u).2.2.1, mem_closedBall_zero_iff.mpr (geom w hw u).2.2.2⟩
  have hb := sample_drift (μ : Measure (Point p.d)) hs (B := ⟨p.B,hB.le⟩) (show 0 < (⟨p.B,hB.le⟩ : ℝ≥0) from hB)
    hd hq hL hc o.val x.val m o.property hmin hr hh hhr hy hfeet
  rw [unfold_integral p n μ _ (measurable_gain p n f x o hm) (gain_integrable p n μ f x o hm)]
  apply hb.trans_eq
  apply integral_congr_ae
  have hJ : (jitterLaw p.d r : Measure (Point p.d)) = ProbabilityTheory.cond volume (ball 0 r) := by simp [jitterLaw,show 0 < r from hr]
  change ∀ᵐ w ∂(jitterLaw p.d r : Measure (Point p.d)), _
  rw [hJ]
  filter_upwards [ProbabilityTheory.ae_cond_mem (μ := (volume : Measure (Point p.d))) (s := ball 0 r) measurableSet_ball] with w hw
  apply integral_congr_ae
  filter_upwards [] with u
  apply integral_congr_ae
  filter_upwards [] with z
  have hp := hfeet u w hw
  have hproj (v : Point p.d) (hv : v ∈ closedBall 0 p.R) : (project p v).val = v :=
    clip_eq_self (mem_closedBall_zero_iff.mp hv)
  unfold gain response pair comparePair secantBit bitSign
  dsimp only [m,r,h] at hp ⊢
  simp only [sampleUtility, hproj _ hp.1, hproj _ hp.2, he hp.1, he hp.2,
    decide_eq_true_eq, sub_nonneg]

end LongTails.Proofs.SphericalPreferenceOracle
