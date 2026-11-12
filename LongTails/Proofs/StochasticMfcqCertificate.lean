import LongTails.Proofs.StochasticMfcqGeometry

open scoped RealInnerProductSpace

namespace LongTails.Proofs.StochasticMfcqCertificate

open Classical
open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcqDirection
open StochasticMfcqGeometry

lemma weights_nonneg (p : Params) (hp : spec.valid p) (v : Primitive p) :
    0 ≤ objectiveWeight p v ∧ ∀ i, 0 ≤ constraintWeight p v i := by
  classical
  have h := (coefficients_simplex p hp v).1
  constructor
  · unfold objectiveWeight
    apply add_nonneg (h 0)
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact le_rfl
    · exact h i.succ
  · intro i
    unfold constraintWeight
    split_ifs
    · exact h i.succ
    · exact le_rfl

lemma weights_sum (p : Params) (hp : spec.valid p) (v : Primitive p) :
    objectiveWeight p v + ∑ i, constraintWeight p v i = 1 := by
  classical
  have hs := (coefficients_simplex p hp v).2
  rw [Fin.sum_univ_succ] at hs
  unfold objectiveWeight constraintWeight
  rw [add_assoc, ← Finset.sum_add_distrib]
  convert hs using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma weighted_identity (p : Params) (v : Primitive p) (g : p.E) (J : Fin p.m → p.E) :
    (∑ i : Fin (p.m + 1), coefficients p v i •
      Fin.cases g (fun j => if active p v j then J j else g) i) =
      objectiveWeight p v • g + ∑ i, constraintWeight p v i • J i := by
  classical
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, objectiveWeight, constraintWeight,
    add_smul, Finset.sum_smul]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma true_residual_bound (p : Params) (I : Problem p) (hp : spec.valid p)
    (x : p.E) (v : Primitive p)
    (hg : ‖v.1 - gradient I.f x‖ ≤ precision p)
    (hJ : ∀ i, ‖v.2.2 i - I.J x i‖ ≤ precision p)
    (hr : ‖residual p v‖ ≤ 4 * precision p) :
    ‖objectiveWeight p v • gradient I.f x + ∑ i, constraintWeight p v i • I.J x i‖ ≤
      5 * precision p := by
  classical
  let u : Fin (p.m + 1) → p.E :=
    Fin.cases (gradient I.f x) (fun j => if active p v j then I.J x j else gradient I.f x)
  have he : ∀ i, ‖u i - vectors p v i‖ ≤ precision p := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [u, vectors, norm_sub_rev] using hg
    · simp only [u, vectors, Fin.cases_succ]
      split_ifs
      · simpa [norm_sub_rev] using hJ j
      · simpa [norm_sub_rev] using hg
  have hpert := ActiveDirectionCertificates.convex_error_bound u (vectors p v)
    (coefficients p v) (precision p) (coefficients_simplex p hp v).1
      (coefficients_simplex p hp v).2 he
  have hid : (∑ i, coefficients p v i • u i) =
      objectiveWeight p v • gradient I.f x + ∑ i, constraintWeight p v i • I.J x i :=
    weighted_identity p v (gradient I.f x) (fun i => I.J x i)
  rw [hid] at hpert
  change ‖_ - residual p v‖ ≤ precision p at hpert
  have ht := norm_le_norm_sub_add
    (objectiveWeight p v • gradient I.f x + ∑ i, constraintWeight p v i • I.J x i)
    (residual p v)
  linarith

lemma active_value_bound (p : Params) (I : Problem p) (x : p.E) (v : Primitive p)
    (hc : ∀ i, |v.2.1 i - I.c x i| ≤ precision p)
    (i : Fin p.m) (hi : active p v i) : -5 * precision p ≤ I.c x i := by
  have he := (abs_le.mp (hc i)).2
  change -4 * precision p ≤ v.2.1 i at hi
  linarith

lemma objective_weight_certificate (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (hx : feasible p I x) (v : Primitive p)
    (hg : ‖v.1 - gradient I.f x‖ ≤ precision p)
    (hc : ∀ i, |v.2.1 i - I.c x i| ≤ precision p)
    (hJ : ∀ i, ‖v.2.2 i - I.J x i‖ ≤ precision p)
    (hr : ‖residual p v‖ ≤ 4 * precision p) :
    0 < objectiveWeight p v ∧ p.μ ≤ 4 * p.H * objectiveWeight p v := by
  classical
  obtain ⟨z, hz, hzJ⟩ := H.bandMfcq x hx
  have hw := weights_nonneg p hp v
  have hd := StochasticMfcqTuning.precision_bounds p hp
  have hμ := hp.2.2.2.2.1
  have hμH := hp.2.2.2.2.2.1
  have hinner (i : Fin p.m) (hi : 0 < constraintWeight p v i) : ⟪I.J x i, z⟫ ≤ -p.μ := by
    have ha : active p v i := by
      by_contra h
      simp [constraintWeight, h] at hi
    apply hzJ i
    have hv := active_value_bound p I x v hc i ha
    linarith [hd.2.2.2.1]
  have hb := ActiveDirectionCertificates.objective_weight_bound (gradient I.f x) z
    (fun i => I.J x i) (objectiveWeight p v) (constraintWeight p v) p.H p.μ (5 * precision p)
    hw.1 hw.2 (weights_sum p hp v) (H.gradientBound x hx) hz hinner
    (true_residual_bound p I hp x v hg hJ hr)
  have hprod := mul_nonneg hw.1 (sub_nonneg.mpr hμH)
  have hl : p.μ ≤ 4 * p.H * objectiveWeight p v := by nlinarith [hd.2.2.1]
  refine ⟨?_, hl⟩
  by_contra ha
  have hz' : objectiveWeight p v = 0 := le_antisymm (le_of_not_gt ha) hw.1
  rw [hz'] at hl
  linarith

lemma normalized_precision (p : Params) (hp : spec.valid p) (a : ℝ)
    (ha : 0 < a) (hweight : p.μ ≤ 4 * p.H * a) : 5 * precision p / a ≤ p.ε := by
  have hε := hp.2.2.2.2.2.2.2.2.1
  have ht := (StochasticMfcqTuning.precision_bounds p hp).2.2.2.2
  have hmul := mul_le_mul_of_nonneg_right hweight hε.le
  apply (div_le_iff₀ ha).2
  have hH : 0 < p.H := by linarith [hp.2.1]
  nlinarith

lemma stopping_stationarity (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (hx : feasible p I x) (v : Primitive p)
    (hg : ‖v.1 - gradient I.f x‖ ≤ precision p)
    (hc : ∀ i, |v.2.1 i - I.c x i| ≤ precision p)
    (hJ : ∀ i, ‖v.2.2 i - I.J x i‖ ≤ precision p)
    (hr : ‖residual p v‖ ≤ 4 * precision p) :
    ‖gradient I.f x + transposeAction p (I.J x) (multipliers p v)‖ ≤ p.ε := by
  have hw := objective_weight_certificate p I hp H x hx v hg hc hJ hr
  have hn := ActiveDirectionCertificates.normalized_residual (gradient I.f x)
    (fun i => I.J x i) (objectiveWeight p v) (constraintWeight p v) (5 * precision p)
    hw.1 (true_residual_bound p I hp x v hg hJ hr)
  exact hn.trans (normalized_precision p hp _ hw.1 hw.2)

lemma stopping_complementarity (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (hx : feasible p I x) (v : Primitive p)
    (hg : ‖v.1 - gradient I.f x‖ ≤ precision p)
    (hc : ∀ i, |v.2.1 i - I.c x i| ≤ precision p)
    (hJ : ∀ i, ‖v.2.2 i - I.J x i‖ ≤ precision p)
    (hr : ‖residual p v‖ ≤ 4 * precision p) :
    ∑ i, |multipliers p v i * I.c x i| ≤ p.ε := by
  classical
  have hw := objective_weight_certificate p I hp H x hx v hg hc hJ hr
  have hδ := (StochasticMfcqTuning.precision_bounds p hp).1
  have hn := weights_nonneg p hp v
  have hterm (i : Fin p.m) : |multipliers p v i * I.c x i| ≤
      constraintWeight p v i / objectiveWeight p v * (5 * precision p) := by
    by_cases hi : active p v i
    · have hc' : |I.c x i| ≤ 5 * precision p :=
        abs_le.mpr ⟨by linarith [active_value_bound p I x v hc i hi], by linarith [hx i]⟩
      change |(constraintWeight p v i / objectiveWeight p v) * I.c x i| ≤ _
      rw [abs_mul, abs_of_nonneg (div_nonneg (hn.2 i) hw.1.le)]
      exact mul_le_mul_of_nonneg_left hc' (div_nonneg (hn.2 i) hw.1.le)
    · simp [multipliers, constraintWeight, hi]
  have hsum : (∑ i, constraintWeight p v i) ≤ 1 := by
    linarith [weights_sum p hp v]
  calc
    _ ≤ ∑ i, constraintWeight p v i / objectiveWeight p v * (5 * precision p) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i, constraintWeight p v i) * (5 * precision p / objectiveWeight p v) := by
      rw [← Finset.sum_mul, ← Finset.sum_div]
      ring
    _ ≤ 5 * precision p / objectiveWeight p v := by
      simpa using mul_le_mul_of_nonneg_right hsum
        (div_nonneg (mul_nonneg (by norm_num) hδ.le) hw.1.le)
    _ ≤ p.ε := normalized_precision p hp _ hw.1 hw.2

lemma stopping_accurate (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (hx : feasible p I x) (v : Primitive p)
    (hg : ‖v.1 - gradient I.f x‖ ≤ precision p)
    (hc : ∀ i, |v.2.1 i - I.c x i| ≤ precision p)
    (hJ : ∀ i, ‖v.2.2 i - I.J x i‖ ≤ precision p)
    (hr : ‖residual p v‖ ≤ 4 * precision p) : accurate p I (x, multipliers p v) := by
  have hw := objective_weight_certificate p I hp H x hx v hg hc hJ hr
  refine ⟨?_, stopping_stationarity p I hp H x hx v hg hc hJ hr, hx,
    stopping_complementarity p I hp H x hx v hg hc hJ hr⟩
  intro i
  exact div_nonneg ((weights_nonneg p hp v).2 i) hw.1.le

end LongTails.Proofs.StochasticMfcqCertificate
