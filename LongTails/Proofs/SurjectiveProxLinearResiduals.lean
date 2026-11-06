import LongTails.Proofs.SurjectiveProxLinearCertificate

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SurjectiveProxLinearResiduals

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearModel
open LongTails.Proofs.SurjectiveProxLinearCertificate

noncomputable def positivePart (p : Params) (c : Constraint p) : Constraint p :=
  WithLp.toLp 2 (fun i => max (c i) 0)

lemma positivePart_nonexpansive (p : Params) (a b : Constraint p) :
    ‖positivePart p a - positivePart p b‖ ≤ ‖a - b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  change (max (a i) 0 - max (b i) 0) ^ 2 ≤ (a i - b i) ^ 2
  have h := pow_le_pow_left₀ (abs_nonneg (max (a i) 0 - max (b i) 0))
    (abs_max_sub_max_le_abs (a i) (b i) 0) 2
  simpa only [sq_abs] using h

lemma positivePart_norm_of_upper (p : Params) (r ℓ : Constraint p) {τ : ℝ}
    (hτ : 0 ≤ τ) (hℓ : ∀ i, 0 ≤ ℓ i) (hupper : ∀ i, r i ≤ τ * ℓ i) :
    ‖positivePart p r‖ ≤ τ * ‖ℓ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hτ (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change max (r i) 0 ^ 2 ≤ τ ^ 2 * (ℓ i) ^ 2
  have hi : max (r i) 0 ≤ τ * ℓ i := max_le (hupper i) (mul_nonneg hτ (hℓ i))
  have hh := pow_le_pow_left₀ (le_max_right (r i) 0) hi 2
  simpa only [mul_pow] using hh

lemma feasibility_residual_bound (p : Params) (c r ℓ : Constraint p) {τ : ℝ}
    (hτ : 0 ≤ τ) (hℓ : ∀ i, 0 ≤ ℓ i) (hupper : ∀ i, r i ≤ τ * ℓ i) :
    ‖positivePart p c‖ ≤ ‖c - r‖ + τ * ‖ℓ‖ := by
  have h := norm_add_le (positivePart p c - positivePart p r) (positivePart p r)
  rw [sub_add_cancel] at h
  exact h.trans (add_le_add (positivePart_nonexpansive p c r)
    (positivePart_norm_of_upper p r ℓ hτ hℓ hupper))

lemma sampled_residual_bounds (p : Params) (I : Problem p) (hp : spec.valid p)
    (x : p.E) (v : Primitive p) (hinside : ∀ i, dualPoint p v i < rho p) :
    ‖positivePart p (I.c x)‖ ≤ ‖v.2.1 - I.c x‖ + p.H * ‖modelStep p v‖ +
      ridge p * ‖dualPoint p v‖ ∧
    (∑ i, |dualPoint p v i * I.c x i|) ≤ ridge p * ‖dualPoint p v‖ ^ 2 +
      ‖dualPoint p v‖ * (‖v.2.1 - I.c x‖ + p.H * ‖modelStep p v‖) := by
  have hpos := valid_tuning_positive p hp
  have hcomp := sampled_complementarity p v hpos.1.le hinside
  have hnon := (dualPoint_spec p v hpos.1.le).1
  have hdiff := true_linearized_difference p I hp x v
  constructor
  · have h := feasibility_residual_bound p (I.c x) (sampledLinearized p v) (dualPoint p v)
      hpos.2.2.2.le (fun i => (hnon i).1) (fun i => (hcomp i).1)
    linarith
  · have h := complementarity_residual_bound p (dualPoint p v) (sampledLinearized p v)
      (I.c x) hpos.2.2.2.le (fun i => (hcomp i).2)
    exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)))

lemma stationarity_residual_bound (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (v : Primitive p) :
    ‖gradient I.f x + transposeAction p (I.J x) (dualPoint p v)‖ ≤
      ‖modelStep p v‖ / eta p + ‖v.1 - gradient I.f x‖ +
        ‖v.2.2 - I.J x‖ * ‖dualPoint p v‖ := by
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  have hη := (valid_tuning_positive p hp).2.2.1
  let ℓ := dualPoint p v
  let a := OracleTemplate.clip p.H v.1
  let S := transposeContinuous p (OracleTemplate.clip p.H v.2.2)
  let T := transposeContinuous p (I.J x)
  have hg : ‖gradient I.f x - a‖ ≤ ‖v.1 - gradient I.f x‖ := by
    rw [norm_sub_rev]
    exact OracleTemplate.norm_clip_sub_le hH (H.gradientBound x) _
  have hJ : ‖T - S‖ ≤ ‖v.2.2 - I.J x‖ := by
    apply (norm_transposeContinuous_sub_le p _ _).trans
    rw [norm_sub_rev]
    exact OracleTemplate.norm_clip_sub_le hH (H.jacobianBound x) _
  have hd : ‖T ℓ - S ℓ‖ ≤ ‖v.2.2 - I.J x‖ * ‖ℓ‖ :=
    ((T - S).le_opNorm ℓ).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
  have hn : ‖modelStep p v‖ = eta p * ‖a + S ℓ‖ := by
    simp only [modelStep, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hη.le]
    rfl
  have hq : ‖modelStep p v‖ / eta p = ‖a + S ℓ‖ := by
    rw [hn, mul_div_cancel_left₀ _ hη.ne']
  rw [hq]
  change ‖gradient I.f x + T ℓ‖ ≤ _
  have hid : gradient I.f x + T ℓ = (a + S ℓ) +
      (gradient I.f x - a) + (T ℓ - S ℓ) := by abel
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add le_rfl hg)) hd)

end LongTails.Proofs.SurjectiveProxLinearResiduals
