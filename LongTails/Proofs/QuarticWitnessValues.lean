import LongTails.Proofs.QuarticStageTransition
import LongTails.Proofs.QuarticWitnessGeometry

namespace LongTails.Proofs.QuarticWitnessValues

open LongTails.Algorithms.QuarticMetricStage
open LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.QuarticStageInvariant
open LongTails.Proofs.QuarticStageTransition
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma interpolation_on_line {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L q Fc θ : ℝ} (hL : 0 ≤ L) (hq : 0 ≤ q) (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x -
      fderiv ℝ (fderiv ℝ (_root_.gradient f)) y‖ ≤ L * ‖x - y‖)
    (x previous : E) (hx : f x ≤ Fc) (hp : f previous ≤ Fc)
    (hhalf : Fc - q ≤ f ((1 / 2 : ℝ) • (x + previous)))
    (hthree : Fc - q ≤ f ((-2 : ℝ) • x + (3 : ℝ) • previous)) :
    f (x + θ • (x - previous)) ≤ Fc + 13 * q + 24 * L * ‖x - previous‖ ^ 4 := by
  let d := x - previous
  have he₁ : x + (-1 : ℝ) • d = previous := by dsimp [d]; module
  have he₂ : x + (-(1 / 2) : ℝ) • d = (1 / 2 : ℝ) • (x + previous) := by dsimp [d]; module
  have he₃ : x + (-3 : ℝ) • d = (-2 : ℝ) • x + (3 : ℝ) • previous := by dsimp [d]; module
  have ht (s : ℝ) : |(f (x + s • d) - Fc) - ((f x - Fc) +
      ⟪_root_.gradient f x, d⟫ * s + (⟪fderiv ℝ (_root_.gradient f) x d, d⟫ / 2) * s ^ 2 +
      (⟪fderiv ℝ (fderiv ℝ (_root_.gradient f)) x d d, d⟫ / 6) * s ^ 3)| ≤
      (L * ‖d‖ ^ 4) * s ^ 4 := by
    have hh := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT x d s
    have he : |s| ^ 4 = s ^ 4 := by nlinarith only [sq_abs s, sq_abs (s ^ 2)]
    rw [he] at hh
    convert hh using 1
    congr 1
    ring
  have hh := QuarticEscapeGeometry.interpolation_bound (h := fun s => f (x + s • d) - Fc)
    (by positivity : 0 ≤ L * ‖d‖ ^ 4) hq hθ hθ₁ ht
    (by simpa using sub_nonpos.mpr hx) (by rw [he₁]; linarith)
    (by rw [he₂]; linarith) (by rw [he₃]; linarith)
  dsimp [d] at hh
  linarith

lemma plane_value_bound (p : Parameters E) (f : E → ℝ) {A τ L : ℝ} {plane : Plane E}
    (hi : PlaneGeometry p f A τ plane) (hf : ContDiff ℝ 3 f)
    (hL : 0 ≤ L) (hα : 0 ≤ p.α) (hq : 0 ≤ p.q) (ha : 0 ≤ p.a) (ha₁ : p.a ≤ 1)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x -
      fderiv ℝ (fderiv ℝ (_root_.gradient f)) y‖ ≤ L * ‖x - y‖)
    (hhalf : p.center.value - p.q ≤ f ((1 / 2 : ℝ) • (plane.accepted.x + plane.previous.x)))
    (hthree : p.center.value - p.q ≤ f ((-2 : ℝ) • plane.accepted.x + (3 : ℝ) • plane.previous.x))
    (hsmall : 384 * L * τ ^ 4 ≤ p.q) :
    f plane.point.x ≤ p.center.value + 14 * p.q := by
  have hx : f plane.accepted.x ≤ p.center.value := by
    rw [← hi.accepted_faithful.1]
    have hh : plane.accepted.value ≤ value p plane.accepted := by
      unfold value regularizedValue
      exact le_add_of_nonneg_right (by positivity)
    exact hh.trans hi.accepted_value
  have hp : f plane.previous.x ≤ p.center.value := by
    rw [← hi.previous_faithful.1]
    have hh : plane.previous.value ≤ value p plane.previous := by
      unfold value regularizedValue
      exact le_add_of_nonneg_right (by positivity)
    exact hh.trans hi.previous_value
  have hθ : 0 ≤ (1 - p.a) / (1 + p.a) := div_nonneg (sub_nonneg.mpr ha₁) (by positivity)
  have hθ₁ : (1 - p.a) / (1 + p.a) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hh := interpolation_on_line hf hL hq hθ hθ₁ hT plane.accepted.x plane.previous.x hx hp hhalf hthree
  rw [← hi.extrapolation] at hh
  have hd : ‖plane.accepted.x - plane.previous.x‖ ≤ 2 * τ := by
    calc
      _ = ‖(plane.accepted.x - p.center.x) - (plane.previous.x - p.center.x)‖ := by congr 1; abel
      _ ≤ ‖plane.accepted.x - p.center.x‖ + ‖plane.previous.x - p.center.x‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [hi.accepted_distance, hi.previous_distance]
  have hd₄ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd 4) hL
  nlinarith

lemma witness_failed_support (p : Parameters E) (f : E → ℝ) {A τ β : ℝ} {w : Witness E}
    (hi : WitnessInvariant p f A τ w) (hα : 0 ≤ p.α) (hβ : 0 < β)
    (hμ : 0 ≤ p.μ) (hμ₁ : p.μ ≤ 1 / 8) (htune : p.μ * β ≤ p.α / 64)
    (hlower : 7 / 16 * ‖p.S (w.point.x - w.plane.point.x)‖ ^ 2 -
      4 * β * ‖w.point.x - w.plane.point.x‖ ^ 2 ≤
      f w.point.x - f w.plane.point.x - ⟪_root_.gradient f w.plane.point.x, w.point.x - w.plane.point.x⟫) :
    w.point.x ≠ w.plane.point.x ∧
      ‖p.S (w.point.x - w.plane.point.x)‖ ^ 2 ≤ 20 * β * ‖w.point.x - w.plane.point.x‖ ^ 2 ∧
      f w.point.x - f w.plane.point.x - ⟪_root_.gradient f w.plane.point.x, w.point.x - w.plane.point.x⟫ ≤
        -p.α * ‖w.point.x - w.plane.point.x‖ ^ 2 / 2 := by
  have hfailure := lt_of_not_ge hi.failure
  change value p w.point < value p w.plane.point + ⟪gradient p w.plane.point, w.point.x - w.plane.point.x⟫ +
    p.μ / 2 * ‖p.S (w.point.x - w.plane.point.x)‖ ^ 2 at hfailure
  simp only [value, LongTails.Algorithms.QuarticMetricStage.gradient,
    hi.point_faithful.1, hi.plane_geometry.point_faithful.1, hi.plane_geometry.point_faithful.2] at hfailure
  exact QuarticWitnessGeometry.failed_support p.S p.center.x w.point.x w.plane.point.x
    hα hβ hμ hμ₁ htune hlower hfailure

lemma witness_escape (p : Parameters E) (f : E → ℝ) {A τ L β : ℝ} {w : Witness E}
    (hi : WitnessInvariant p f A τ w) (hf : ContDiff ℝ 3 f)
    (hL : 0 ≤ L) (hα : 0 ≤ p.α) (hβ : 0 < β) (hμ : 0 ≤ p.μ) (hμ₁ : p.μ ≤ 1 / 8)
    (htune : p.μ * β ≤ p.α / 64) (ha : 0 ≤ p.a) (ha₁ : p.a ≤ 1)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x -
      fderiv ℝ (fderiv ℝ (_root_.gradient f)) y‖ ≤ L * ‖x - y‖)
    (hlower : 7 / 16 * ‖p.S (w.point.x - w.plane.point.x)‖ ^ 2 -
      4 * β * ‖w.point.x - w.plane.point.x‖ ^ 2 ≤
      f w.point.x - f w.plane.point.x - ⟪_root_.gradient f w.plane.point.x, w.point.x - w.plane.point.x⟫)
    (hshort : 48 * L * τ ^ 2 ≤ p.α / 4) (hη : L * p.η ^ 2 ≤ p.α / 16)
    (hescape : 15 * p.q ≤ p.α * p.η ^ 2 / 4) (hq : 0 ≤ p.q)
    (hv : f w.plane.point.x ≤ p.center.value + 14 * p.q) :
    ∃ i : Fin 4, f (escapePoints p.η w.point.x w.plane.point.x i) ≤ p.center.value - p.q := by
  obtain ⟨hne, _, hdef⟩ := witness_failed_support p f hi hα hβ hμ hμ₁ htune hlower
  have hd : ‖w.point.x - w.plane.point.x‖ ≤ 4 * τ := by
    calc
      _ = ‖(w.point.x - p.center.x) - (w.plane.point.x - p.center.x)‖ := by congr 1; abel
      _ ≤ ‖w.point.x - p.center.x‖ + ‖w.plane.point.x - p.center.x‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [hi.point_distance, plane_distance p f hi.plane_geometry ha ha₁]
  have hds := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd 2) hL
  have hu : f w.point.x ≤ p.center.value := by
    rw [← hi.point_faithful.1]
    have hh : w.point.value ≤ value p w.point := by
      unfold value regularizedValue
      exact le_add_of_nonneg_right (by positivity)
    exact hh.trans hi.point_value
  have he := QuarticWitnessGeometry.escape_values_bound hf hL hα hT w.point.x w.plane.point.x hne
    hdef (by nlinarith) hη
  have hm : max (f w.point.x) (f w.plane.point.x) ≤ p.center.value + 14 * p.q :=
    max_le (by linarith) hv
  have he' : min (min (f (escapePoints p.η w.point.x w.plane.point.x 0))
      (f (escapePoints p.η w.point.x w.plane.point.x 1)))
      (min (f (escapePoints p.η w.point.x w.plane.point.x 2))
      (f (escapePoints p.η w.point.x w.plane.point.x 3))) ≤ p.center.value - p.q := by linarith
  rcases min_le_iff.mp he' with h | h
  · rcases min_le_iff.mp h with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · rcases min_le_iff.mp h with h | h
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩

lemma finish_witness_value (p : Parameters E) (f : E → ℝ) (g : Fin 2 × E → Reply E)
    (horacle : ∀ x, g (0, x) = .inl (f x, _root_.gradient f x)) (w : Witness E) (i : Fin 6) :
    ((finish p (.witness w)).eval g).value ≤ f (candidates p w i) := by
  rw [finish, OracleTemplate.QueryPlan.eval_map, OracleTemplate.QueryPlan.eval_traverse]
  simp only [OracleTemplate.QueryPlan.eval, horacle, readPoint]
  exact QuarticStageExecution.fold_value_le_member _ w.point
    ⟨candidates p w i, f (candidates p w i), _root_.gradient f (candidates p w i)⟩
    (List.mem_ofFn.mpr ⟨i, rfl⟩)

lemma finish_witness_faithful (p : Parameters E) (f : E → ℝ) (g : Fin 2 × E → Reply E)
    (horacle : ∀ x, g (0, x) = .inl (f x, _root_.gradient f x)) (w : Witness E)
    (hw : Faithful f w.point) : Faithful f ((finish p (.witness w)).eval g) := by
  rw [finish, OracleTemplate.QueryPlan.eval_map, OracleTemplate.QueryPlan.eval_traverse]
  simp only [OracleTemplate.QueryPlan.eval, horacle, readPoint]
  rcases QuarticStageExecution.fold_member
    (List.ofFn (fun i : Fin 6 => (⟨candidates p w i, f (candidates p w i),
      _root_.gradient f (candidates p w i)⟩ : Point E))) w.point with h | h
  · rw [h]
    exact hw
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    rw [← hi]
    exact ⟨rfl, rfl⟩

omit [FiniteDimensional ℝ E] in
lemma candidate_progress (p : Parameters E) (f : E → ℝ) (w : Witness E)
    (hescape : p.center.value - p.q ≤ f ((1 / 2 : ℝ) • (w.plane.accepted.x + w.plane.previous.x)) →
      p.center.value - p.q ≤ f ((-2 : ℝ) • w.plane.accepted.x + (3 : ℝ) • w.plane.previous.x) →
      ∃ i : Fin 4, f (escapePoints p.η w.point.x w.plane.point.x i) ≤ p.center.value - p.q) :
    ∃ i : Fin 6, f (candidates p w i) ≤ p.center.value - p.q := by
  by_cases hh : f ((1 / 2 : ℝ) • (w.plane.accepted.x + w.plane.previous.x)) ≤ p.center.value - p.q
  · exact ⟨0, hh⟩
  by_cases ht : f ((-2 : ℝ) • w.plane.accepted.x + (3 : ℝ) • w.plane.previous.x) ≤ p.center.value - p.q
  · exact ⟨1, ht⟩
  obtain ⟨i, hi⟩ := hescape (le_of_not_ge hh) (le_of_not_ge ht)
  fin_cases i
  · exact ⟨2, hi⟩
  · exact ⟨3, hi⟩
  · exact ⟨4, hi⟩
  · exact ⟨5, hi⟩

end LongTails.Proofs.QuarticWitnessValues
