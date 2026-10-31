import LongTails.Proofs.MonotoneHessianSnapshot
import LongTails.Proofs.RelativeCurvatureDetection
import LongTails.Proofs.RelativeCurvatureProducts

namespace LongTails.Proofs.MonotoneHessianDetection

open OracleTemplate LongTails.Setups.HessianLipschitzSecondOrder
open LongTails.Algorithms.MonotoneHessianReuse LongTails.Algorithms.QuarticMetricStage
open scoped RealInnerProductSpace

lemma fold_none_iff {α : Type} (xs : List (Option α)) (prior : Option α) :
    xs.foldl (fun prev next => prev.orElse (fun _ => next)) prior = none ↔
      prior = none ∧ ∀ x ∈ xs, x = none := by
  induction xs generalizing prior with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    cases prior <;> cases x <;> simp

lemma fold_some_mem {α : Type} (xs : List (Option α)) (prior : Option α) (v : α)
    (h : xs.foldl (fun prev next => prev.orElse (fun _ => next)) prior = some v) :
    prior = some v ∨ some v ∈ xs := by
  induction xs generalizing prior with
  | nil => exact Or.inl h
  | cons x xs ih =>
    obtain h | h := ih _ h
    · cases prior with
      | none => exact Or.inr (List.mem_cons.mpr (Or.inl h.symm))
      | some w => exact Or.inl h
    · exact Or.inr (List.mem_cons.mpr (Or.inr h))

lemma detect_some (p : Params) (O : Fin 2 × p.E → Reply p.E) (S : p.E ≃L[ℝ] p.E)
    (x : Point p.E) (signs : Block p) (v : p.E) (hv : (detect p S x signs).eval O = some v) :
    ∃ j, (LongTails.Algorithms.RelativeCurvatureSearch.search S.symm.toContinuousLinearMap x p.H
      (relativeTolerance p) (LongTails.Algorithms.RelativeCurvatureSearch.seed (signs j)) (degree p)).eval O = some v := by
  classical
  simp only [detect, searchCalls, QueryPlan.eval_map, QueryPlan.eval_traverse] at hv
  have hh := fold_some_mem _ none v hv
  rcases hh with hh | hh
  · simp at hh
  · simpa only [List.mem_ofFn] using hh

lemma detect_none (p : Params) (O : Fin 2 × p.E → Reply p.E) (S : p.E ≃L[ℝ] p.E)
    (x : Point p.E) (signs : Block p) : (detect p S x signs).eval O = none ↔
    ∀ j, (LongTails.Algorithms.RelativeCurvatureSearch.search S.symm.toContinuousLinearMap x p.H
      (relativeTolerance p) (LongTails.Algorithms.RelativeCurvatureSearch.seed (signs j)) (degree p)).eval O = none := by
  simp only [detect, searchCalls, QueryPlan.eval_map, QueryPlan.eval_traverse, fold_none_iff, true_and]
  simp

lemma search_sound (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hg : Differentiable ℝ (_root_.gradient f))
    (hLip : ∀ x y, ‖fderiv ℝ (_root_.gradient f) x - fderiv ℝ (_root_.gradient f) y‖ ≤ p.H * ‖x - y‖)
    (S : p.E ≃L[ℝ] p.E) (x : Point p.E) (hx : x.gradient = _root_.gradient f x.x)
    (hmetric : ∀ v, 3 * delta p * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2)
    (O : Fin 2 × p.E → Reply p.E) (hO : ∀ y, O (0, y) = .inl (f y, _root_.gradient f y))
    (u v : p.E) (hs : (LongTails.Algorithms.RelativeCurvatureSearch.search S.symm.toContinuousLinearMap
      x p.H (relativeTolerance p) u (degree p)).eval O = some v) :
    v ≠ 0 ∧ ⟪v, fderiv ℝ (_root_.gradient f) x.x v⟫ ≤
      -(7 * gamma p / 1024) * ‖v‖ ^ 2 := by
  let C := MonotoneHessianSnapshot.relative S (fderiv ℝ (_root_.gradient f) x.x)
  have ha := (MonotoneHessianParameters.relative_tolerance_range p hp).1
  have hprod (z : p.E) := RelativeCurvatureProducts.product_error hp.1
    (show 0 < relativeTolerance p / 4 by positivity) hg hLip S.symm.toContinuousLinearMap x hx O f hO z
  have hprod' (z : p.E) :
      ‖(LongTails.Algorithms.RelativeCurvatureSearch.product S.symm.toContinuousLinearMap x p.H
        (relativeTolerance p / 4) z).eval O - C z‖ ≤ relativeTolerance p / 16 := by
    simpa only [C, MonotoneHessianSnapshot.relative, ContinuousLinearMap.comp_apply, div_div,
      show (4 : ℝ) * 4 = 16 by norm_num] using hprod z
  obtain ⟨z, hz, hv, hcurv⟩ := RelativeCurvatureExecution.search_sound
    S.symm.toContinuousLinearMap C x p.H (relativeTolerance p) u O (degree p) v hprod' hs
  have hv0 : v ≠ 0 := by
    rw [hv]
    intro hh
    have he : z = 0 := S.symm.injective (by simpa using hh)
    simp [he] at hz
  refine ⟨hv0, ?_⟩
  have hh := MonotoneHessianSnapshot.returned_absolute_curvature S
    (fderiv ℝ (_root_.gradient f) x.x) ha.le hmetric z hz hcurv
  have he : 21 * relativeTolerance p * delta p / 16 = 21 * gamma p / 1024 := by
    have hd := (MonotoneHessianParameters.delta_pos p hp).ne'
    unfold relativeTolerance
    field_simp
    ring
  rw [he] at hh
  rw [hv]
  change ⟪S.symm z, fderiv ℝ (_root_.gradient f) x.x (S.symm z)⟫ ≤
    -(7 * gamma p / 1024) * ‖S.symm z‖ ^ 2
  have hγ := MonotoneHessianParameters.gamma_pos p hp
  nlinarith [mul_nonneg hγ.le (sq_nonneg ‖S.symm z‖)]

lemma detect_sound (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hg : Differentiable ℝ (_root_.gradient f))
    (hLip : ∀ x y, ‖fderiv ℝ (_root_.gradient f) x - fderiv ℝ (_root_.gradient f) y‖ ≤ p.H * ‖x - y‖)
    (S : p.E ≃L[ℝ] p.E) (x : Point p.E) (hx : x.gradient = _root_.gradient f x.x)
    (hmetric : ∀ v, 3 * delta p * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2)
    (O : Fin 2 × p.E → Reply p.E) (hO : ∀ y, O (0, y) = .inl (f y, _root_.gradient f y))
    (signs : Block p) (v : p.E) (hs : (detect p S x signs).eval O = some v) :
    v ≠ 0 ∧ ⟪v, fderiv ℝ (_root_.gradient f) x.x v⟫ ≤
      -(7 * gamma p / 1024) * ‖v‖ ^ 2 := by
  obtain ⟨j, hj⟩ := detect_some p O S x signs v hs
  exact search_sound p hp f hg hLip S x hx hmetric O hO _ v hj

lemma single_probability (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hg : Differentiable ℝ (_root_.gradient f))
    (hLip : ∀ x y, ‖fderiv ℝ (_root_.gradient f) x - fderiv ℝ (_root_.gradient f) y‖ ≤ p.H * ‖x - y‖)
    (S : p.E ≃L[ℝ] p.E) (x : Point p.E) (hx : x.gradient = _root_.gradient f x.x)
    (hA : (fderiv ℝ (_root_.gradient f) x.x).toLinearMap.IsSymmetric)
    (hmetric : ∀ v, 3 * delta p * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2)
    (hlo : ∀ v, ‖S v‖ ^ 2 - 6 * delta p * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (_root_.gradient f) x.x v⟫)
    (hhi : ∀ v, ⟪v, fderiv ℝ (_root_.gradient f) x.x v⟫ ≤ ‖S v‖ ^ 2)
    (O : Fin 2 × p.E → Reply p.E) (hO : ∀ y, O (0, y) = .inl (f y, _root_.gradient f y))
    (v : p.E) (hv : ⟪v, fderiv ℝ (_root_.gradient f) x.x v⟫ < -gamma p * ‖v‖ ^ 2) :
    ((PMF.uniformOfFintype (Sign p)).toMeasure).real
      {s | ∃ out, (LongTails.Algorithms.RelativeCurvatureSearch.search S.symm.toContinuousLinearMap
        x p.H (relativeTolerance p) (LongTails.Algorithms.RelativeCurvatureSearch.seed s) (degree p)).eval O = some out}
      ≥ 1 / 16 := by
  let A := fderiv ℝ (_root_.gradient f) x.x
  let C := MonotoneHessianSnapshot.relative S A
  have ha := MonotoneHessianParameters.relative_tolerance_range p hp
  have ha0 := ha.1
  have hδ := MonotoneHessianParameters.delta_pos p hp
  have hγ := MonotoneHessianParameters.gamma_pos p hp
  have hC := MonotoneHessianSnapshot.relative_symmetric S A hA
  have hnorm := MonotoneHessianSnapshot.relative_norm S A hA hmetric hlo hhi
  have htune : 2 * relativeTolerance p * (6 * delta p) ≤ gamma p := by
    have he : 2 * relativeTolerance p * (6 * delta p) = 3 * gamma p / 16 := by
      unfold relativeTolerance
      field_simp [hδ.ne']
      ring
    rw [he]
    linarith
  have hb : ⟪S v, C (S v)⟫ < -(2 * relativeTolerance p) * ‖S v‖ ^ 2 := by
    rw [MonotoneHessianSnapshot.relative_pairing, ContinuousLinearEquiv.symm_apply_apply]
    have hn : ⟪v, A v⟫ < 0 := hv.trans_le
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ.le) (sq_nonneg _))
    have he := mul_le_mul_of_nonneg_left (hlo v) (show 0 ≤ 2 * relativeTolerance p by positivity)
    have hh := mul_le_mul_of_nonneg_right htune (sq_nonneg ‖v‖)
    have hz := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2 * relativeTolerance p by positivity) hn.le
    change ⟪v, A v⟫ < _ at hv
    change 2 * relativeTolerance p * (_ - _) ≤ 2 * relativeTolerance p * ⟪v, A v⟫ at he
    nlinarith

  obtain ⟨i, hi⟩ := RelativeCurvatureSpectrum.negative_eigenvalue C hC (S v) hb
  have hd : 0 < Module.finrank ℝ p.E := Nat.zero_lt_of_lt i.isLt
  have heig (j : Fin (Module.finrank ℝ p.E)) : hC.eigenvalues rfl j ≤ 1 := by
    have hbnd := MonotoneHessianSnapshot.relative_quadratic_bounds S A hmetric hlo hhi
    exact (OracleTemplate.TemporalDiscrepancy.spectral_eigenvalue_bounds C hC (μ := -2) (L := 1)
      (fun z => by rw [real_inner_comm z (C z)]; exact (hbnd z).1)
      (fun z => by rw [real_inner_comm z (C z), one_mul]; exact (hbnd z).2) j).2
  have hprod (τ : ℝ) (hτ : 0 < τ) (z : p.E) :
      ‖(LongTails.Algorithms.RelativeCurvatureSearch.product S.symm.toContinuousLinearMap x p.H τ z).eval O - C z‖ ≤ τ / 4 := by
    exact RelativeCurvatureProducts.product_error hp.1 hτ hg hLip S.symm.toContinuousLinearMap x hx O f hO z
  have hn : 2 * Real.log (16 * (Module.finrank ℝ p.E : ℝ) / relativeTolerance p) /
      Real.sqrt (relativeTolerance p) ≤ degree p := by
    have he : max 1 (Module.finrank ℝ p.E : ℝ) = (Module.finrank ℝ p.E : ℝ) :=
      max_eq_right (by exact_mod_cast hd)
    simpa only [he] using MonotoneHessianParameters.degree_sufficient p
  refine RelativeCurvatureDetection.detection_probability S.symm.toContinuousLinearMap C
    (hC.eigenvectorBasis rfl) (hC.eigenvalues rfl) (RelativeCurvatureSpectrum.symmetric_coordinates C hC)
    heig hnorm hd x p.H ha.1 ha.2 O (degree p) hn ?_ ?_ i (by nlinarith [hi])
  · intro z
    exact hprod _ (by positivity) z
  · intro z
    convert hprod (relativeTolerance p / 4) (by positivity) z using 1; ring

lemma detect_failure_probability (p : Params) (hp : spec.valid p)
    (O : Fin 2 × p.E → Reply p.E) (S : p.E ≃L[ℝ] p.E) (x : Point p.E)
    (hsingle : ((PMF.uniformOfFintype (Sign p)).toMeasure).real
      {s | ∃ v, (LongTails.Algorithms.RelativeCurvatureSearch.search S.symm.toContinuousLinearMap
        x p.H (relativeTolerance p) (LongTails.Algorithms.RelativeCurvatureSearch.seed s) (degree p)).eval O = some v}
      ≥ 1 / 16) :
    (MeasureTheory.Measure.pi fun _ : Fin (repetitions p) =>
      (PMF.uniformOfFintype (Sign p)).toMeasure).real
      {signs | (detect p S x signs).eval O = none} ≤ p.ρ / stages p := by
  let Q := (PMF.uniformOfFintype (Sign p)).toMeasure
  let good := {s : Sign p | ∃ v, (LongTails.Algorithms.RelativeCurvatureSearch.search
    S.symm.toContinuousLinearMap x p.H (relativeTolerance p)
    (LongTails.Algorithms.RelativeCurvatureSearch.seed s) (degree p)).eval O = some v}
  have hh := HeavyTailedSospDetection.independent_block_failure Q good
    (Set.toFinite good).measurableSet (repetitions p) (1 / 16) hsingle
  have he : {signs : Block p | (detect p S x signs).eval O = none} =
      {signs | ∀ j, signs j ∉ good} := by
    ext signs
    simp only [Set.mem_ofPred_eq, detect_none, good]
    apply forall_congr'
    intro j
    cases (LongTails.Algorithms.RelativeCurvatureSearch.search S.symm.toContinuousLinearMap
      x p.H (relativeTolerance p) (LongTails.Algorithms.RelativeCurvatureSearch.seed (signs j)) (degree p)).eval O <;> simp
  rw [he]
  have hK : 0 < (stages p : ℝ) := by unfold stages; positivity
  have hρ := hp.2.2.2.2.1
  have ht := RelativeCurvatureInitialization.repeated_failure_tuning hρ hK (repetitions p)
    (MonotoneHessianParameters.repetitions_sufficient p)
  exact hh.trans (by convert ht using 1; congr 1; ring)

end LongTails.Proofs.MonotoneHessianDetection
