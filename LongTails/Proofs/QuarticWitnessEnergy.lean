import LongTails.Proofs.QuarticWitnessValues

namespace LongTails.Proofs.QuarticWitnessEnergy

open LongTails.Algorithms.QuarticMetricStage
open LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.QuarticStageInvariant
open LongTails.Proofs.QuarticStageTransition
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma perturbation_radius (S : E ≃L[ℝ] E) (u c d : E) {A B : ℝ}
    (hu : ‖S (u - c)‖ ≤ A) (hd : ‖S d‖ ^ 2 ≤ B) :
    ‖S (u + d - c)‖ ^ 2 ≤ 2 * A ^ 2 + 2 * B := by
  have he : u + d - c = (u - c) + d := by abel
  rw [he, map_add]
  have hn := norm_add_le (S (u - c)) (S d)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have ha := pow_le_pow_left₀ (norm_nonneg _) hu 2
  nlinarith [sq_nonneg (‖S (u - c)‖ - ‖S d‖)]

omit [FiniteDimensional ℝ E] in
lemma escape_radius (S : E ≃L[ℝ] E) (u v c : E) {A β η : ℝ}
    (hA : 0 ≤ A) (hu : ‖S (u - c)‖ ≤ 2 * A) (hv : ‖S (v - c)‖ ≤ A)
    (hne : u ≠ v) (hmetric : ‖S (u - v)‖ ^ 2 ≤ 20 * β * ‖u - v‖ ^ 2) (i : Fin 4) :
    ‖S (escapePoints η u v i - c)‖ ^ 2 ≤ 8 * A ^ 2 + 40 * β * η ^ 2 := by
  let d := (η / ‖u - v‖) • (u - v)
  have hd : ‖S d‖ ^ 2 ≤ 20 * β * η ^ 2 := by
    have hh := QuarticWitnessGeometry.direction_metric S u v hne hmetric
    have he : d = η • (‖u - v‖⁻¹ • (u - v)) := by simp only [d, div_eq_mul_inv, smul_smul]
    rw [he, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg η)]
  have hdn : ‖S (-d)‖ ^ 2 ≤ 20 * β * η ^ 2 := by simpa only [map_neg, norm_neg] using hd
  have hv' : ‖S (v - c)‖ ≤ 2 * A := hv.trans (by linarith)
  have h₀ := perturbation_radius S u c d hu hd
  have h₁ := perturbation_radius S u c (-d) hu hdn
  have h₂ := perturbation_radius S v c d hv' hd
  have h₃ := perturbation_radius S v c (-d) hv' hdn
  fin_cases i
  · change ‖S (u + d - c)‖ ^ 2 ≤ _
    nlinarith only [h₀]
  · change ‖S (u - d - c)‖ ^ 2 ≤ _
    rw [sub_eq_add_neg u d]
    nlinarith only [h₁]
  · change ‖S (v + d - c)‖ ^ 2 ≤ _
    nlinarith only [h₂]
  · change ‖S (v - d - c)‖ ^ 2 ≤ _
    rw [sub_eq_add_neg v d]
    nlinarith only [h₃]

omit [FiniteDimensional ℝ E] in
lemma interpolation_radius (S : E ≃L[ℝ] E) (x previous c : E) {A : ℝ}
    (hx : ‖S (x - c)‖ ≤ A) (hp : ‖S (previous - c)‖ ≤ A) :
    ‖S ((1 / 2 : ℝ) • (x + previous) - c)‖ ≤ A ∧
    ‖S ((-2 : ℝ) • x + (3 : ℝ) • previous - c)‖ ≤ 5 * A := by
  have he₁ : (1 / 2 : ℝ) • (x + previous) - c =
      (1 / 2 : ℝ) • (x - c) + (1 / 2 : ℝ) • (previous - c) := by module
  have he₂ : (-2 : ℝ) • x + (3 : ℝ) • previous - c =
      (-2 : ℝ) • (x - c) + (3 : ℝ) • (previous - c) := by module
  rw [he₁, he₂, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
  constructor
  · have hh := norm_add_le ((1 / 2 : ℝ) • S (x - c)) ((1 / 2 : ℝ) • S (previous - c))
    norm_num only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hh
    linarith
  · have hh := norm_add_le ((-2 : ℝ) • S (x - c)) ((3 : ℝ) • S (previous - c))
    norm_num only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos (by norm_num : (0 : ℝ) < 3)] at hh
    linarith

lemma candidates_energy (p : Parameters E) (f : E → ℝ) {A τ β : ℝ} {w : Witness E}
    (hi : WitnessInvariant p f A τ w) (hμ : 0 ≤ p.μ) (hA : 0 ≤ A)
    (hA₂ : p.μ * A ^ 2 = 2 * p.q)
    (hne : w.point.x ≠ w.plane.point.x)
    (hmetric : ‖p.S (w.point.x - w.plane.point.x)‖ ^ 2 ≤
      20 * β * ‖w.point.x - w.plane.point.x‖ ^ 2)
    (hscale : p.μ * (8 * A ^ 2 + 40 * β * p.η ^ 2) ≤ 256 * p.q) (i : Fin 6) :
    p.μ * ‖p.S (candidates p w i - p.center.x)‖ ^ 2 ≤ 256 * p.q := by
  have hq : 0 ≤ p.q := by nlinarith [sq_nonneg A]
  have hh := interpolation_radius p.S w.plane.accepted.x w.plane.previous.x p.center.x
    hi.plane_geometry.accepted_radius hi.plane_geometry.previous_radius
  have he (j : Fin 4) := mul_le_mul_of_nonneg_left
    (escape_radius p.S w.point.x w.plane.point.x p.center.x (η := p.η) hA hi.point_radius
      hi.plane_geometry.point_radius hne hmetric j) hμ
  fin_cases i
  · have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh.1 2) hμ
    change p.μ * ‖p.S ((1 / 2 : ℝ) • (w.plane.accepted.x + w.plane.previous.x) - p.center.x)‖ ^ 2 ≤ _
    nlinarith
  · have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh.2 2) hμ
    change p.μ * ‖p.S ((-2 : ℝ) • w.plane.accepted.x + (3 : ℝ) • w.plane.previous.x - p.center.x)‖ ^ 2 ≤ _
    nlinarith
  · exact (he 0).trans hscale
  · exact (he 1).trans hscale
  · exact (he 2).trans hscale
  · exact (he 3).trans hscale

lemma finish_witness_energy (p : Parameters E) (f : E → ℝ) (g : Fin 2 × E → Reply E)
    (horacle : ∀ x, g (0, x) = .inl (f x, _root_.gradient f x)) (w : Witness E)
    (hw : p.μ * ‖p.S (w.point.x - p.center.x)‖ ^ 2 ≤ 256 * p.q)
    (hc : ∀ i : Fin 6, p.μ * ‖p.S (candidates p w i - p.center.x)‖ ^ 2 ≤ 256 * p.q)
    (hp : ∃ i : Fin 6, f (candidates p w i) ≤ p.center.value - p.q) :
    p.μ * ‖p.S (((finish p (.witness w)).eval g).x - p.center.x)‖ ^ 2 ≤
      256 * (p.center.value - ((finish p (.witness w)).eval g).value) := by
  obtain ⟨i, hi⟩ := hp
  have hv := (QuarticWitnessValues.finish_witness_value p f g horacle w i).trans hi
  suffices hh : p.μ * ‖p.S (((finish p (.witness w)).eval g).x - p.center.x)‖ ^ 2 ≤ 256 * p.q by linarith
  rw [finish, OracleTemplate.QueryPlan.eval_map, OracleTemplate.QueryPlan.eval_traverse]
  simp only [OracleTemplate.QueryPlan.eval, horacle, readPoint]
  rcases QuarticStageExecution.fold_member
    (List.ofFn (fun i : Fin 6 => (⟨candidates p w i, f (candidates p w i),
      _root_.gradient f (candidates p w i)⟩ : Point E))) w.point with h | h
  · rw [h]
    exact hw
  · obtain ⟨j, hj⟩ := List.mem_ofFn.mp h
    rw [← hj]
    exact hc j

end LongTails.Proofs.QuarticWitnessEnergy
