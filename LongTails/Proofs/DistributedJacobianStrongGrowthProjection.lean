import LongTails.Algorithms.DistributedLocalExtragradient

open MeasureTheory

namespace LongTails.Proofs.DistributedJacobianStrongGrowthProjection

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradient

lemma measurable_projectBall (p : Params) (r : ℝ) :
    Measurable (fun z : Point p × Point p => projectBall p z.1 r z.2) :=
  measurable_fst.add ((OracleTemplate.measurable_clip r).comp (measurable_snd.sub measurable_fst))

lemma projectBall_mem (p : Params) (c x : Point p) {r : ℝ} (hr : 0 ≤ r) :
    ‖projectBall p c r x - c‖ ≤ r := by
  simpa [projectBall] using OracleTemplate.norm_clip_le hr (x - c)

lemma projectBall_distance (p : Params) (c x y : Point p) {r : ℝ}
    (hr : 0 ≤ r) (hy : ‖y - c‖ ≤ r) :
    ‖projectBall p c r x - y‖ ≤ ‖x - y‖ := by
  have he : projectBall p c r x - y = OracleTemplate.clip r (x - c) - (y - c) := by
    dsimp [projectBall]
    abel
  rw [he]
  have hh := OracleTemplate.norm_clip_sub_le hr hy (x - c)
  simpa only [sub_sub_sub_cancel_right] using hh

lemma measurable_localizedOutput (p : Params) (r : ℝ) :
    Measurable (fun z : Point p × Point p => localizedOutput p z.1 r z.2) :=
  (measurable_projectBall p p.R).comp
    (measurable_const.prodMk (measurable_projectBall p (r / 2)))

lemma localized_mem_global (p : Params) (c x : Point p) {r : ℝ} (hR : 0 ≤ p.R) :
    ‖localizedOutput p c r x - p.x0‖ ≤ p.R :=
  projectBall_mem p p.x0 _ hR

lemma localized_mem_local (p : Params) (c x : Point p) {r : ℝ}
    (hR : 0 ≤ p.R) (hr : 0 ≤ r) (hc : ‖c - p.x0‖ ≤ p.R) :
    ‖localizedOutput p c r x - c‖ ≤ r / 2 :=
  (projectBall_distance p p.x0 (projectBall p c (r / 2) x) c hR hc).trans
    (projectBall_mem p c x (by positivity))

lemma localized_distance (p : Params) (c x y : Point p) {r : ℝ}
    (hR : 0 ≤ p.R) (hr : 0 ≤ r)
    (hyR : ‖y - p.x0‖ ≤ p.R) (hyr : ‖y - c‖ ≤ r / 2) :
    ‖localizedOutput p c r x - y‖ ≤ ‖x - y‖ :=
  (projectBall_distance p p.x0 (projectBall p c (r / 2) x) y hR hyR).trans
    (projectBall_distance p c x y (by positivity) hyr)

lemma localized_root_bound (p : Params) (c x y : Point p) {r : ℝ}
    (hR : 0 ≤ p.R) (hr : 0 ≤ r) (hc : ‖c - p.x0‖ ≤ p.R)
    (hcy : ‖c - y‖ ≤ 3 * r / 8) :
    ‖localizedOutput p c r x - y‖ ≤ r := by
  have hh := (show ‖localizedOutput p c r x - y‖ ≤ ‖localizedOutput p c r x - c‖ + ‖c - y‖ from by simpa only [← dist_eq_norm] using dist_triangle (localizedOutput p c r x) c y).trans
    (add_le_add (localized_mem_local p c x hR hr hc) hcy)
  linarith

lemma localized_global_root_bound (p : Params) (c x y : Point p) {r : ℝ}
    (hR : 0 ≤ p.R) (hy : ‖p.x0 - y‖ ≤ p.R) :
    ‖localizedOutput p c r x - y‖ ≤ 2 * p.R := by
  have hh := (show ‖localizedOutput p c r x - y‖ ≤ ‖localizedOutput p c r x - p.x0‖ + ‖p.x0 - y‖ from by simpa only [← dist_eq_norm] using dist_triangle (localizedOutput p c r x) p.x0 y).trans
    (add_le_add (localized_mem_global p c x hR) hy)
  linarith

lemma rounded_distance_sq (p : Params) (x z y : Point p) {a θ : ℝ}
    (ha : 0 ≤ a) (hθ : 0 < θ) (hxz : ‖x - z‖ ≤ a) :
    ‖x - y‖ ^ 2 ≤ (1 + θ) * ‖z - y‖ ^ 2 + (1 + 1 / θ) * a ^ 2 := by
  have hh : ‖x - y‖ ≤ ‖z - y‖ + a := by
    have hh := (show ‖x - y‖ ≤ ‖x - z‖ + ‖z - y‖ from by simpa only [← dist_eq_norm] using dist_triangle x z y).trans (add_le_add hxz le_rfl)
    simpa [add_comm] using hh
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖z - y‖ + a)).mpr hh
  have hyoung : 2 * ‖z - y‖ * a ≤ θ * ‖z - y‖ ^ 2 + a ^ 2 / θ := by
    apply (mul_le_mul_iff_right₀ hθ).mp
    have he : a ^ 2 / θ * θ = a ^ 2 := div_mul_cancel₀ _ hθ.ne'
    nlinarith [sq_nonneg (θ * ‖z - y‖ - a)]
  have he : a ^ 2 / θ = (1 / θ) * a ^ 2 := by ring
  rw [he] at hyoung
  nlinarith

lemma rounded_contraction_algebra {c e a v : ℝ} (he : 0 ≤ e)
    (hv : v ≤ (1 + c / 2) * ((1 - c) * e) + (1 + 2 / c) * a ^ 2) :
    v ≤ (1 - c / 2) * e + (1 + 2 / c) * a ^ 2 := by
  nlinarith [mul_nonneg (sq_nonneg c) he]

lemma rounded_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (p : Params)
    (X Z : Ω → Point p) (y : Point p) (E : Set Ω) (hE : MeasurableSet E)
    (hX : Measurable X) {a θ : ℝ}
    (ha : 0 ≤ a) (hθ : 0 < θ) (hXZ : ∀ ω ∈ E, ‖X ω - Z ω‖ ≤ a)
    (hZi : Integrable (E.indicator (fun ω => ‖Z ω - y‖ ^ 2)) P) :
    Integrable (E.indicator (fun ω => ‖X ω - y‖ ^ 2)) P ∧
      (∫ ω, E.indicator (fun ω => ‖X ω - y‖ ^ 2) ω ∂P) ≤
        (1 + θ) * (∫ ω, E.indicator (fun ω => ‖Z ω - y‖ ^ 2) ω ∂P) +
          (1 + 1 / θ) * a ^ 2 := by
  classical
  let V := E.indicator (fun ω => ‖X ω - y‖ ^ 2)
  let W := E.indicator (fun ω => ‖Z ω - y‖ ^ 2)
  have hV0 (ω : Ω) : 0 ≤ V ω := Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
  have hm : Measurable V := ((hX.sub_const y).norm.pow_const 2).indicator hE
  have hi : Integrable (fun ω => (1 + θ) * W ω + (1 + 1 / θ) * a ^ 2) P :=
    (hZi.const_mul (1 + θ)).add (integrable_const _)
  have hb (ω : Ω) : V ω ≤ (1 + θ) * W ω + (1 + 1 / θ) * a ^ 2 := by
    by_cases hω : ω ∈ E
    · simpa only [V, W, Set.indicator_of_mem hω] using
        rounded_distance_sq p (X ω) (Z ω) y ha hθ (hXZ ω hω)
    · simp only [V, W, Set.indicator_of_notMem hω, mul_zero, zero_add]
      positivity
  have hVi : Integrable V P := hi.mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_of_nonneg (hV0 ω)]; exact hb ω)
  refine ⟨hVi, ?_⟩
  calc
    _ ≤ ∫ ω, (1 + θ) * W ω + (1 + 1 / θ) * a ^ 2 ∂P := integral_mono hVi hi hb
    _ = _ := by rw [integral_add (hZi.const_mul _) (integrable_const _), integral_const_mul]; simp

lemma localized_rounded_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (p : Params)
    (C X Z : Ω → Point p) (y : Point p) (E : Set Ω) (hE : MeasurableSet E)
    (hC : Measurable C) (hX : Measurable X) {r a θ : ℝ}
    (hR : 0 ≤ p.R) (hr : 0 ≤ r) (hyR : ‖y - p.x0‖ ≤ p.R)
    (hyC : ∀ ω ∈ E, ‖y - C ω‖ ≤ r / 2)
    (ha : 0 ≤ a) (hθ : 0 < θ) (hXZ : ∀ ω ∈ E, ‖X ω - Z ω‖ ≤ a)
    (hZi : Integrable (E.indicator (fun ω => ‖Z ω - y‖ ^ 2)) P) :
    Integrable (E.indicator (fun ω => ‖localizedOutput p (C ω) r (X ω) - y‖ ^ 2)) P ∧
      (∫ ω, E.indicator (fun ω => ‖localizedOutput p (C ω) r (X ω) - y‖ ^ 2) ω ∂P) ≤
        (1 + θ) * (∫ ω, E.indicator (fun ω => ‖Z ω - y‖ ^ 2) ω ∂P) +
          (1 + 1 / θ) * a ^ 2 := by
  classical
  have hb := rounded_event_bound P p X Z y E hE hX ha hθ hXZ hZi
  let V := E.indicator (fun ω => ‖localizedOutput p (C ω) r (X ω) - y‖ ^ 2)
  have hm : Measurable V :=
    ((((measurable_localizedOutput p r).comp (hC.prodMk hX)).sub_const y).norm.pow_const 2).indicator hE
  have hV0 (ω : Ω) : 0 ≤ V ω := Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
  have hle (ω : Ω) : V ω ≤ E.indicator (fun ω => ‖X ω - y‖ ^ 2) ω := by
    by_cases hω : ω ∈ E
    · simp only [V, Set.indicator_of_mem hω]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (localized_distance p (C ω) (X ω) y hR hr hyR (hyC ω hω))
    · simp only [V, Set.indicator_of_notMem hω, le_refl]
  have hi : Integrable V P := hb.1.mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_of_nonneg (hV0 ω)]; exact hle ω)
  exact ⟨hi, (integral_mono hi hb.1 hle).trans hb.2⟩

end LongTails.Proofs.DistributedJacobianStrongGrowthProjection
