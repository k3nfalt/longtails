import LongTails.Proofs.SurjectiveProxLinearStability

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SurjectiveProxLinearCertificate

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearModel

noncomputable def coordinateReplacement (p : Params) (ℓ : Constraint p) (i : Fin p.m)
    (t : ℝ) : Constraint p := WithLp.toLp 2 (Function.update ℓ.ofLp i t)

lemma coordinateReplacement_mem (p : Params) {ℓ : Constraint p} (hℓ : ℓ ∈ dualBox p)
    (i : Fin p.m) {t : ℝ} (ht : 0 ≤ t) (htρ : t ≤ rho p) :
    coordinateReplacement p ℓ i t ∈ dualBox p := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [coordinateReplacement] using And.intro ht htρ
  · simpa [coordinateReplacement, Function.update_of_ne hji] using hℓ j

lemma coordinateReplacement_inner (p : Params) (q ℓ : Constraint p) (i : Fin p.m) (t : ℝ) :
    ⟪q, coordinateReplacement p ℓ i t - ℓ⟫ = (t - ℓ i) * q i := by
  classical
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Finset.sum_eq_single i]
  · simp [coordinateReplacement]
  · intro j _ hji
    simp [coordinateReplacement, Function.update_of_ne hji]
  · simp

lemma box_coordinate_optimality (p : Params) (q ℓ : Constraint p)
    (hℓ : ℓ ∈ dualBox p) (hρ : 0 ≤ rho p)
    (hinside : ∀ i, ℓ i < rho p)
    (hvi : ∀ z ∈ dualBox p, 0 ≤ ⟪q, z - ℓ⟫) :
    ∀ i, 0 ≤ q i ∧ ℓ i * q i = 0 := by
  intro i
  have hup := hvi (coordinateReplacement p ℓ i (rho p))
    (coordinateReplacement_mem p hℓ i hρ le_rfl)
  have hlo := hvi (coordinateReplacement p ℓ i 0)
    (coordinateReplacement_mem p hℓ i le_rfl hρ)
  rw [coordinateReplacement_inner] at hup hlo
  have hpos : 0 < rho p - ℓ i := sub_pos.mpr (hinside i)
  have hq : 0 ≤ q i := nonneg_of_mul_nonneg_right hup hpos
  refine ⟨hq, ?_⟩
  have hn := mul_nonneg (hℓ i).1 hq
  nlinarith

noncomputable def sampledLinearized (p : Params) (v : Primitive p) : Constraint p :=
  WithLp.toLp 2 (fun i => v.2.1 i +
    ⟪OracleTemplate.clip p.H v.2.2 i, modelStep p v⟫)

lemma sampled_linearized_pairing (p : Params) (v : Primitive p) (d : Constraint p) :
    ⟪sampledLinearized p v, d⟫ = ⟪v.2.1, d⟫ +
      ⟪transposeAction p (OracleTemplate.clip p.H v.2.2) d, modelStep p v⟫ := by
  simp [sampledLinearized, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    transposeAction, sum_inner, real_inner_smul_left, mul_add, Finset.sum_add_distrib]

lemma sampled_direction_identity (p : Params) (v : Primitive p) (d : Constraint p) :
    ⟪ProxLinearDualSensitivity.quadraticGradient
      (transposeContinuous p (OracleTemplate.clip p.H v.2.2)) (OracleTemplate.clip p.H v.1)
      v.2.1 (eta p) (ridge p) (dualPoint p v), d⟫ =
      ⟪ridge p • dualPoint p v - sampledLinearized p v, d⟫ := by
  rw [ProxLinearDualSensitivity.quadraticGradient_direction, inner_sub_left,
    real_inner_smul_left, sampled_linearized_pairing]
  simp only [modelStep, real_inner_smul_right, transposeContinuous_apply]
  rw [real_inner_comm (transposeAction p (OracleTemplate.clip p.H v.2.2) d)]
  ring

lemma sampled_complementarity (p : Params) (v : Primitive p) (hρ : 0 ≤ rho p)
    (hinside : ∀ i, dualPoint p v i < rho p) :
    ∀ i, sampledLinearized p v i ≤ ridge p * dualPoint p v i ∧
      dualPoint p v i * sampledLinearized p v i = ridge p * (dualPoint p v i) ^ 2 := by
  have hopt := box_coordinate_optimality p
    (ridge p • dualPoint p v - sampledLinearized p v) (dualPoint p v)
    (dualPoint_spec p v hρ).1 hρ hinside (by
      intro z hz
      rw [← sampled_direction_identity]
      exact dualPoint_vi p v hρ hz)
  intro i
  have hi := hopt i
  change 0 ≤ ridge p * dualPoint p v i - sampledLinearized p v i ∧
    dualPoint p v i * (ridge p * dualPoint p v i - sampledLinearized p v i) = 0 at hi
  constructor <;> nlinarith [hi.1, hi.2]

lemma multiplier_inside_of_norm (p : Params) (v : Primitive p) (hρ : 0 < rho p)
    (hdual : ‖dualPoint p v‖ ≤ rho p / 2) : ∀ i, dualPoint p v i < rho p := by
  intro i
  have hi : dualPoint p v i ≤ ‖dualPoint p v‖ :=
    (le_abs_self _).trans (PiLp.norm_apply_le (dualPoint p v) i)
  linarith

lemma multiplier_norm_from_step (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (v : Primitive p) {e : ℝ}
    (he : ‖v.2.2 - I.J x‖ ≤ e) (hsmall : p.H * e ≤ 1 / 2) :
    ‖dualPoint p v‖ ≤ 2 * p.H * (p.H + ‖modelStep p v‖ / eta p) := by
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  have hη := (valid_tuning_positive p hp).2.2.1
  let ℓ := dualPoint p v
  let T := transposeContinuous p (I.J x)
  let S := transposeContinuous p (OracleTemplate.clip p.H v.2.2)
  let a := OracleTemplate.clip p.H v.1
  have hJ : ‖I.J x - OracleTemplate.clip p.H v.2.2‖ ≤ e := by
    rw [norm_sub_rev]
    exact (OracleTemplate.norm_clip_sub_le hH (H.jacobianBound x) v.2.2).trans he
  have hTS : ‖T - S‖ ≤ e := (norm_transposeContinuous_sub_le p _ _).trans hJ
  have hdiff : ‖T ℓ - S ℓ‖ ≤ e * ‖ℓ‖ :=
    ((T - S).le_opNorm ℓ).trans (mul_le_mul_of_nonneg_right hTS (norm_nonneg _))
  have hsum : ‖T ℓ‖ ≤ ‖S ℓ‖ + e * ‖ℓ‖ := by
    have hh := norm_add_le (S ℓ) (T ℓ - S ℓ)
    have hid : S ℓ + (T ℓ - S ℓ) = T ℓ := by abel
    rw [hid] at hh
    linarith
  have ha : ‖a‖ ≤ p.H := OracleTemplate.norm_clip_le hH _
  have hS : ‖S ℓ‖ ≤ ‖a + S ℓ‖ + p.H := by
    have hh := norm_sub_le (a + S ℓ) a
    have hid : a + S ℓ - a = S ℓ := by abel
    rw [hid] at hh
    linarith
  have hlower : ‖ℓ‖ ≤ p.H * ‖T ℓ‖ := H.surjective x ℓ
  have hscaled := mul_le_mul_of_nonneg_left hsum hH
  have hscaledS := mul_le_mul_of_nonneg_left hS hH
  have hsmallL := mul_le_mul_of_nonneg_right hsmall (norm_nonneg ℓ)
  have hnorm : ‖modelStep p v‖ = eta p * ‖a + S ℓ‖ := by
    simp only [modelStep, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hη.le]
    rfl
  have hquot : ‖modelStep p v‖ / eta p = ‖a + S ℓ‖ := by
    rw [hnorm, mul_div_cancel_left₀ _ hη.ne']
  rw [hquot]
  change ‖ℓ‖ ≤ _
  nlinarith

lemma sampled_linearized_eq (p : Params) (v : Primitive p) :
    sampledLinearized p v = v.2.1 +
      (transposeContinuous p (OracleTemplate.clip p.H v.2.2)).adjoint (modelStep p v) := by
  apply ext_inner_right ℝ
  intro d
  rw [sampled_linearized_pairing, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    transposeContinuous_apply]
  congr 1
  exact real_inner_comm _ _

lemma sampled_linearized_difference (p : Params) (hp : spec.valid p) (v : Primitive p) :
    ‖sampledLinearized p v - v.2.1‖ ≤ p.H * ‖modelStep p v‖ := by
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  let T := transposeContinuous p (OracleTemplate.clip p.H v.2.2)
  have hT : ‖T.adjoint‖ ≤ p.H := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact (norm_transposeContinuous_le p _).trans (OracleTemplate.norm_clip_le hH _)
  rw [sampled_linearized_eq, add_sub_cancel_left]
  exact (T.adjoint.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))

lemma true_linearized_difference (p : Params) (I : Problem p) (hp : spec.valid p)
    (x : p.E) (v : Primitive p) :
    ‖I.c x - sampledLinearized p v‖ ≤ ‖v.2.1 - I.c x‖ + p.H * ‖modelStep p v‖ := by
  have heq : I.c x - sampledLinearized p v =
      (I.c x - v.2.1) - (sampledLinearized p v - v.2.1) := by abel
  rw [heq]
  have h := norm_sub_le (I.c x - v.2.1) (sampledLinearized p v - v.2.1)
  rw [norm_sub_rev (I.c x) v.2.1] at h
  exact h.trans (add_le_add le_rfl (sampled_linearized_difference p hp v))

lemma absolute_pairing_le (p : Params) (u v : Constraint p) :
    (∑ i, |u i * v i|) ≤ ‖u‖ * ‖v‖ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖u i‖) (fun i => ‖v i‖)
  rw [← PiLp.norm_sq_eq_of_L2 (fun _ : Fin p.m => ℝ) u,
    ← PiLp.norm_sq_eq_of_L2 (fun _ : Fin p.m => ℝ) v] at h
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.norm_eq_abs, ← abs_mul] using h

lemma complementarity_residual_bound (p : Params) (ℓ r c : Constraint p) {τ : ℝ}
    (hτ : 0 ≤ τ) (hcomp : ∀ i, ℓ i * r i = τ * (ℓ i) ^ 2) :
    (∑ i, |ℓ i * c i|) ≤ τ * ‖ℓ‖ ^ 2 + ‖ℓ‖ * ‖c - r‖ := by
  have hsum : (∑ i, |ℓ i * c i|) ≤
      (∑ i, τ * (ℓ i) ^ 2) + ∑ i, |ℓ i * (c - r) i| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hid : ℓ i * c i = τ * (ℓ i) ^ 2 + ℓ i * (c - r) i := by
      change ℓ i * c i = τ * (ℓ i) ^ 2 + ℓ i * (c i - r i)
      nlinarith [hcomp i]
    rw [hid]
    exact (abs_add_le (τ * (ℓ i) ^ 2) (ℓ i * (c - r) i)).trans
      (add_le_add (le_of_eq (abs_of_nonneg (mul_nonneg hτ (sq_nonneg (ℓ i))))) le_rfl)
  rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq] at hsum
  exact hsum.trans (add_le_add le_rfl (absolute_pairing_le p ℓ (c - r)))

end LongTails.Proofs.SurjectiveProxLinearCertificate
