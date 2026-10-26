import LongTails.Proofs.CachedJacobianGeometry
import LongTails.Proofs.CachedJacobianTuning
import LongTails.Proofs.EnergyHessianExecution

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CachedJacobianExecution

open OracleTemplate LongTails.Setups.LipschitzJacobianMonotone
open LongTails.Algorithms.CachedJacobian
open CachedJacobianGeometry CachedJacobianTuning

attribute [local instance] Classical.propDecidable

noncomputable def replies (p : Params) (F : p.E → p.E) (q : Fin 2 × p.E) : Reply p :=
  if q.1 = 0 then .inl (F q.2) else .inr (fderiv ℝ F q.2)

structure Correct (p : Params) (F : p.E → p.E) (a : State p) : Prop where
  point_mem : a.point ∈ p.X
  value_eq : a.value = F a.point
  normal_mem : ∀ z ∈ p.X, ⟪a.normal, z - a.point⟫ ≤ 0
  snapshot_mem : a.snapshot ∈ p.X
  matrix_eq : a.matrix = fderiv ℝ F a.snapshot

noncomputable def cached (p : Params) (F : p.E → p.E) (a : State p) : State p := by
  classical
  exact replaceCache p a (replies p F ((if refresh p a then 1 else 0), a.point))

lemma cached_correct {p : Params} {F : p.E → p.E} {a : State p} (ha : Correct p F a) :
    Correct p F (cached p F a) := by
  classical
  by_cases h : refresh p a
  · simpa [cached, replaceCache, h, replies, readJacobian] using
      (show Correct p F { a with snapshot := a.point, matrix := fderiv ℝ F a.point } from
        ⟨ha.point_mem, ha.value_eq, ha.normal_mem, ha.point_mem, rfl⟩)
  · simpa [cached, replaceCache, h] using ha

lemma cached_point (p : Params) (F : p.E → p.E) (a : State p) :
    (cached p F a).point = a.point := by
  classical
  simp only [cached, replaceCache]
  split_ifs <;> rfl

lemma cached_value (p : Params) (F : p.E → p.E) (a : State p) :
    (cached p F a).value = a.value := by
  classical
  simp only [cached, replaceCache]
  split_ifs <;> rfl

lemma cached_distance {p : Params} (F : p.E → p.E) (a : State p) (hR : 0 ≤ cacheRadius p) :
    ‖(cached p F a).point - (cached p F a).snapshot‖ ≤ cacheRadius p := by
  classical
  by_cases h : refresh p a
  · simpa [cached, replaceCache, h] using hR
  · simpa [cached, replaceCache, h] using (not_lt.mp h)

lemma affinePoint_spec {p : Params} {B : p.E →L[ℝ] p.E} (b : p.E) {μ : ℝ}
    (hv : spec.valid p) (hμ : 0 < μ)
    (hB : ∀ u ∈ p.X, ∀ v ∈ p.X, 0 ≤ ⟪B (u - v), u - v⟫) :
    affinePoint p B b μ ∈ p.X ∧
      ∀ z ∈ p.X, 0 ≤ ⟪b + B (affinePoint p B b μ) + μ • affinePoint p B b μ,
        z - affinePoint p B b μ⟫ := by
  obtain ⟨_, _, _, _, hX, hc, hx, _⟩ := hv
  have hex := affine_vi_exists b hX hc ⟨p.x0, hx⟩ hμ hB
  simp only [affinePoint, dite_eq_left hex]
  exact Classical.choose_spec hex

lemma nextPoint_spec {p : Params} {F : p.E → p.E} {a : State p} (t : ℕ) (center : p.E)
    (hv : spec.valid p) (ha : Correct p F a)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ y ∈ p.X, 0 ≤ ⟪F x - F y, x - y⟫) :
    nextPoint p t center a ∈ p.X ∧ ∀ z ∈ p.X,
      0 ≤ ⟪a.value + a.matrix (nextPoint p t center a - a.point) +
        (stepSize p t)⁻¹ • (nextPoint p t center a - center), z - nextPoint p t center a⟫ := by
  have hvalid := hv
  obtain ⟨hL, hD, _, hm, _, hc, _, _⟩ := hv
  have hη := stepSize_pos hL hD hm t
  have hB : ∀ u ∈ p.X, ∀ v ∈ p.X, 0 ≤ ⟪a.matrix (u - v), u - v⟫ := by
    intro u hu v hv
    rw [ha.matrix_eq]
    exact derivative_monotone_on_differences hc ha.snapshot_mem hu hv
      (hF _ ha.snapshot_mem) hmono
  have h := affinePoint_spec
    (a.value - a.matrix a.point - (stepSize p t)⁻¹ • center) hvalid (inv_pos.mpr hη) hB
  refine ⟨h.1, fun z hz => ?_⟩
  have heq : a.value - a.matrix a.point - (stepSize p t)⁻¹ • center +
      a.matrix (nextPoint p t center a) + (stepSize p t)⁻¹ • nextPoint p t center a =
      a.value + a.matrix (nextPoint p t center a - a.point) +
        (stepSize p t)⁻¹ • (nextPoint p t center a - center) := by
    simp only [map_sub, smul_sub]
    module
  rw [← heq]
  simpa only [nextPoint] using h.2 z hz

lemma innerStep_eval (p : Params) (F : p.E → p.E) (t : ℕ) (center : p.E) (a : State p) :
    QueryPlan.eval (replies p F) (innerStep p t center a) =
      move p t center (cached p F a) (nextPoint p t center (cached p F a))
        (F (nextPoint p t center (cached p F a))) := by
  classical
  simp [innerStep, QueryPlan.eval, cached, replies, readValue]

lemma innerStep_correct {p : Params} {F : p.E → p.E} {a : State p} (t : ℕ) (center : p.E)
    (hv : spec.valid p) (ha : Correct p F a)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ y ∈ p.X, 0 ≤ ⟪F x - F y, x - y⟫) :
    Correct p F (QueryPlan.eval (replies p F) (innerStep p t center a)) := by
  rw [innerStep_eval]
  have hc := cached_correct ha
  have hn := nextPoint_spec t center hv hc hF hmono
  refine ⟨hn.1, rfl, ?_, hc.snapshot_mem, hc.matrix_eq⟩
  intro z hz
  change ⟪-(_), _⟫ ≤ 0
  rw [inner_neg_left]
  exact neg_nonpos.mpr (hn.2 z hz)

lemma innerStep_counts_jacobian (p : Params) (F : p.E → p.E) (t : ℕ)
    (center : p.E) (a : State p) :
    EnergyHessianExecution.counts (replies p F) (innerStep p t center a) 1 =
      if refresh p a then 1 else 0 := by
  classical
  by_cases h : refresh p a <;> simp [innerStep, EnergyHessianExecution.counts, h]

lemma innerStep_cache_ledger {p : Params} (F : p.E → p.E) (t : ℕ)
    (center : p.E) (a : State p) :
    cacheRadius p * (EnergyHessianExecution.counts (replies p F) (innerStep p t center a) 1 : ℝ) +
      ‖(QueryPlan.eval (replies p F) (innerStep p t center a)).point -
        (QueryPlan.eval (replies p F) (innerStep p t center a)).snapshot‖ ≤
      ‖a.point - a.snapshot‖ +
        ‖(QueryPlan.eval (replies p F) (innerStep p t center a)).point - a.point‖ := by
  classical
  rw [innerStep_counts_jacobian, innerStep_eval]
  by_cases h : refresh p a
  · simp only [h, ite_true, Nat.cast_one, mul_one, move]
    simp only [cached, replaceCache, h, ite_true]
    exact add_le_add (le_of_lt h) le_rfl
  · simp only [h, ite_false, Nat.cast_zero, mul_zero, zero_add, move]
    simp only [cached, replaceCache, h, ite_false]
    have hh := norm_sub_le_norm_sub_add_norm_sub (nextPoint p t center a) a.point a.snapshot
    linarith

lemma contracted_travel {E : Type*} [SeminormedAddCommGroup E] {u v y : E}
    (h : ‖v - y‖ ≤ ‖u - y‖ / 4) :
    ‖v - u‖ + (5 / 3 : ℝ) * ‖v - y‖ ≤ (5 / 3 : ℝ) * ‖u - y‖ := by
  have hh := norm_sub_le_norm_sub_add_norm_sub v y u
  rw [norm_sub_rev y u] at hh
  linarith

lemma innerStep_contraction {p : Params} {F : p.E → p.E} {a : State p}
    (t : ℕ) (center y : p.E) (r : ℝ)
    (hv : spec.valid p) (ha : Correct p F a)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ z ∈ p.X, 0 ≤ ⟪F x - F z, x - z⟫)
    (hJ : ∀ x ∈ p.X, ∀ z ∈ p.X,
      ‖fderiv ℝ F x - fderiv ℝ F z‖ ≤ p.L * ‖x - z‖)
    (ht : t < outerCount p) (hy : y ∈ p.X)
    (hyvi : ∀ z ∈ p.X, 0 ≤ ⟪F y + (stepSize p t)⁻¹ • (y - center), z - y⟫)
    (hr : ‖a.point - y‖ ≤ r) (hsmall : stepSize p t * p.L * r ≤ 1 / 64) :
    ‖(QueryPlan.eval (replies p F) (innerStep p t center a)).point - y‖ ≤
      ‖a.point - y‖ / 4 := by
  have hvalid := hv
  obtain ⟨hL, hD, _, hm, _, hc, _, _⟩ := hv
  have hb := cached_correct ha
  have hn := nextPoint_spec t center hvalid hb hF hmono
  have hdist := cached_distance F a (cacheRadius_pos hL hD hm).le
  have hroot : ‖(cached p F a).point - y‖ ≤ r := by simpa only [cached_point] using hr
  have hh := chord_contraction hc hb.point_mem hn.1 hy hb.snapshot_mem
    (stepSize_pos hL hD hm t) hL.le hF hmono hJ hdist hroot
    (cache_scale hL hD hm ht) hsmall
    (by simpa only [hb.value_eq, hb.matrix_eq] using hn.2) hyvi
  rw [innerStep_eval]
  simpa only [move, cached_point] using hh

lemma innerStep_certificate {p : Params} {F : p.E → p.E} {a : State p}
    (t : ℕ) (center y : p.E) (r : ℝ)
    (hv : spec.valid p) (ha : Correct p F a)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ z ∈ p.X, 0 ≤ ⟪F x - F z, x - z⟫)
    (hJ : ∀ x ∈ p.X, ∀ z ∈ p.X,
      ‖fderiv ℝ F x - fderiv ℝ F z‖ ≤ p.L * ‖x - z‖)
    (ht : t < outerCount p) (hy : y ∈ p.X)
    (hyvi : ∀ z ∈ p.X, 0 ≤ ⟪F y + (stepSize p t)⁻¹ • (y - center), z - y⟫)
    (hr : ‖a.point - y‖ ≤ r) (hsmall : stepSize p t * p.L * r ≤ 1 / 64) :
    let b := QueryPlan.eval (replies p F) (innerStep p t center a)
    ‖b.point - center + stepSize p t • (F b.point + b.normal)‖ ≤ ‖a.point - y‖ / 4 := by
  have hvalid := hv
  obtain ⟨hL, hD, _, hm, _, hc, _, _⟩ := hv
  have hb := cached_correct ha
  have hn := nextPoint_spec t center hvalid hb hF hmono
  have hdist := cached_distance F a (cacheRadius_pos hL hD hm).le
  have hroot : ‖(cached p F a).point - y‖ ≤ r := by simpa only [cached_point] using hr
  have hcontract := innerStep_contraction t center y r hvalid ha hF hmono hJ ht hy hyvi hr hsmall
  rw [innerStep_eval] at hcontract
  change ‖nextPoint p t center (cached p F a) - y‖ ≤ ‖a.point - y‖ / 4 at hcontract
  have hη := stepSize_pos hL hD hm t
  have hcert := chord_certificate hc hb.point_mem hn.1 hb.snapshot_mem hη hL.le hF hJ
    hdist hroot (cache_scale hL hD hm ht) hsmall
    (by simpa only [cached_point] using hcontract)
  rw [← hb.value_eq, ← hb.matrix_eq] at hcert
  dsimp only
  rw [innerStep_eval]
  let b := cached p F a
  let z := nextPoint p t center b
  have heq : z - center + stepSize p t •
      (F z + -(b.value + b.matrix (z - b.point) + (stepSize p t)⁻¹ • (z - center))) =
      stepSize p t • (F z - b.value - b.matrix (z - b.point)) := by
    simp only [smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hη.ne', one_smul, smul_sub]
    module
  change ‖z - center + stepSize p t •
      (F z + -(b.value + b.matrix (z - b.point) + (stepSize p t)⁻¹ • (z - center)))‖ ≤ _
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  simpa only [b, z, cached_point] using hcert

lemma repeatInner_correct {p : Params} {F : p.E → p.E} (t : ℕ) (center : p.E)
    (hv : spec.valid p)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ y ∈ p.X, 0 ≤ ⟪F x - F y, x - y⟫)
    (n : ℕ) (a : State p) (ha : Correct p F a) :
    Correct p F (QueryPlan.eval (replies p F) (repeatInner p t center n a)) := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih =>
    rw [repeatInner, QueryPlan.eval_bind]
    exact ih _ (innerStep_correct t center hv ha hF hmono)

section InnerBounds

variable {p : Params} {F : p.E → p.E}
variable (t : ℕ) (center y : p.E) (r : ℝ)
variable (hv : spec.valid p)
variable (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
variable (hmono : ∀ x ∈ p.X, ∀ z ∈ p.X, 0 ≤ ⟪F x - F z, x - z⟫)
variable (hJ : ∀ x ∈ p.X, ∀ z ∈ p.X,
  ‖fderiv ℝ F x - fderiv ℝ F z‖ ≤ p.L * ‖x - z‖)
variable (ht : t < outerCount p) (hy : y ∈ p.X)
variable (hyvi : ∀ z ∈ p.X, 0 ≤ ⟪F y + (stepSize p t)⁻¹ • (y - center), z - y⟫)
variable (hsmall : stepSize p t * p.L * r ≤ 1 / 64)

include hv hF hmono hJ ht hy hyvi hsmall

lemma repeatInner_distance (n : ℕ) (a : State p) (ha : Correct p F a) (hr : ‖a.point - y‖ ≤ r) :
    ‖(QueryPlan.eval (replies p F) (repeatInner p t center n a)).point - y‖ ≤
      (1 / 4 : ℝ) ^ n * ‖a.point - y‖ := by
  induction n generalizing a with
  | zero => simp [repeatInner, QueryPlan.eval]
  | succ n ih =>
    rw [repeatInner, QueryPlan.eval_bind]
    have hnext := innerStep_correct t center hv ha hF hmono
    have hd := innerStep_contraction t center y r hv ha hF hmono hJ ht hy hyvi hr hsmall
    have hnextroot : ‖(QueryPlan.eval (replies p F) (innerStep p t center a)).point - y‖ ≤ r := by
      nlinarith [norm_nonneg (a.point - y)]
    have hh := ih _ hnext hnextroot
    have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ (1 / 4 : ℝ) ^ n by positivity)
    rw [pow_succ]
    nlinarith

lemma repeatInner_ledger (n : ℕ) (a : State p) (ha : Correct p F a) (hr : ‖a.point - y‖ ≤ r) :
    let b := QueryPlan.eval (replies p F) (repeatInner p t center n a)
    cacheRadius p * (EnergyHessianExecution.counts (replies p F) (repeatInner p t center n a) 1 : ℝ) +
      ‖b.point - b.snapshot‖ + (5 / 3 : ℝ) * ‖b.point - y‖ ≤
      ‖a.point - a.snapshot‖ + (5 / 3 : ℝ) * ‖a.point - y‖ := by
  induction n generalizing a with
  | zero => simp [repeatInner, QueryPlan.eval, EnergyHessianExecution.counts]
  | succ n ih =>
    dsimp only
    rw [repeatInner, QueryPlan.eval_bind, EnergyHessianExecution.counts_bind]
    have hnext := innerStep_correct t center hv ha hF hmono
    have hd := innerStep_contraction t center y r hv ha hF hmono hJ ht hy hyvi hr hsmall
    have hnextroot : ‖(QueryPlan.eval (replies p F) (innerStep p t center a)).point - y‖ ≤ r := by
      nlinarith [norm_nonneg (a.point - y)]
    have hh := ih _ hnext hnextroot
    have hc := innerStep_cache_ledger F t center a
    have htravel := contracted_travel hd
    dsimp only at hh
    push_cast
    linarith

lemma repeatInner_certificate (n : ℕ) (hn : 0 < n) (a : State p)
    (ha : Correct p F a) (hr : ‖a.point - y‖ ≤ r) :
    let b := QueryPlan.eval (replies p F) (repeatInner p t center n a)
    ‖b.point - center + stepSize p t • (F b.point + b.normal)‖ ≤
      (1 / 4 : ℝ) ^ n * ‖a.point - y‖ := by
  induction n generalizing a with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simpa [repeatInner, QueryPlan.eval_bind, QueryPlan.eval, div_eq_mul_inv, mul_comm] using
        innerStep_certificate t center y r hv ha hF hmono hJ ht hy hyvi hr hsmall
    | succ n =>
      dsimp only
      rw [repeatInner, QueryPlan.eval_bind]
      have hnext := innerStep_correct t center hv ha hF hmono
      have hd := innerStep_contraction t center y r hv ha hF hmono hJ ht hy hyvi hr hsmall
      have hnextroot : ‖(QueryPlan.eval (replies p F) (innerStep p t center a)).point - y‖ ≤ r := by
        nlinarith [norm_nonneg (a.point - y)]
      have hh := ih (by omega) _ hnext hnextroot
      dsimp only at hh
      have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ (1 / 4 : ℝ) ^ (n + 1) by positivity)
      rw [pow_succ _ (n + 1)]
      nlinarith

end InnerBounds

end LongTails.Proofs.CachedJacobianExecution
