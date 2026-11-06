import LongTails.Proofs.SurjectiveProxLinearModel

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SurjectiveProxLinearExactModel

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.ProxLinearDualSensitivity
open LongTails.Proofs.SurjectiveProxLinearModel

noncomputable def linearModel (p : Params) (I : Problem p) (x y : p.E) : ℝ :=
  I.f x + ⟪gradient I.f x, y - x⟫ +
    rho p * ∑ i, max (I.c x i + ⟪I.J x i, y - x⟫) 0

noncomputable def exactObjective (p : Params) (I : Problem p) (x : p.E)
    (ℓ : Constraint p) : ℝ :=
  eta p / 2 * ‖gradient I.f x + transposeAction p (I.J x) ℓ‖ ^ 2 - ⟪I.c x, ℓ⟫

noncomputable def exactDualPoint (p : Params) (I : Problem p) (x : p.E) : Constraint p := by
  classical
  exact if h : ∃ ℓ ∈ dualBox p, ∀ z ∈ dualBox p,
      exactObjective p I x ℓ ≤ exactObjective p I x z
    then Classical.choose h else 0

noncomputable def exactModelStep (p : Params) (I : Problem p) (x : p.E) : p.E :=
  (-eta p) • (gradient I.f x + transposeAction p (I.J x) (exactDualPoint p I x))

lemma continuous_exactObjective (p : Params) (I : Problem p) (x : p.E) :
    Continuous (exactObjective p I x) := by
  have h := continuous_transposeAction p (I.J x)
  unfold exactObjective
  fun_prop

lemma exists_exact_minimum (p : Params) (I : Problem p) (x : p.E) (hρ : 0 ≤ rho p) :
    ∃ ℓ ∈ dualBox p, ∀ z ∈ dualBox p, exactObjective p I x ℓ ≤ exactObjective p I x z := by
  exact (compact_dualBox p).exists_isMinOn ⟨0, zero_mem_dualBox p hρ⟩
    (continuous_exactObjective p I x).continuousOn

lemma exactDualPoint_spec (p : Params) (I : Problem p) (x : p.E) (hρ : 0 ≤ rho p) :
    exactDualPoint p I x ∈ dualBox p ∧
      ∀ z ∈ dualBox p, exactObjective p I x (exactDualPoint p I x) ≤ exactObjective p I x z := by
  have h := exists_exact_minimum p I x hρ
  unfold exactDualPoint
  rw [dite_eq_left h]
  exact Classical.choose_spec h

lemma exact_minimum_vi (p : Params) (I : Problem p) (x : p.E) {u : Constraint p}
    (hu : u ∈ dualBox p)
    (hmin : ∀ z ∈ dualBox p, exactObjective p I x u ≤ exactObjective p I x z)
    {z : Constraint p} (hz : z ∈ dualBox p) :
    0 ≤ ⟪quadraticGradient (transposeContinuous p (I.J x)) (gradient I.f x)
      (I.c x) (eta p) 0 u, z - u⟫ := by
  rw [quadraticGradient_direction]
  apply quadratic_min_directional
  intro t ht ht1
  have hseg := (convex_dualBox p).add_smul_sub_mem hu hz ⟨ht.le, ht1⟩
  simpa only [exactObjective, transposeContinuous_apply, zero_div, zero_mul, add_zero]
    using hmin _ hseg

lemma exactDualPoint_vi (p : Params) (I : Problem p) (x : p.E) (hρ : 0 ≤ rho p)
    {z : Constraint p} (hz : z ∈ dualBox p) :
    0 ≤ ⟪quadraticGradient (transposeContinuous p (I.J x)) (gradient I.f x)
      (I.c x) (eta p) 0 (exactDualPoint p I x), z - exactDualPoint p I x⟫ := by
  exact exact_minimum_vi p I x (exactDualPoint_spec p I x hρ).1
    (exactDualPoint_spec p I x hρ).2 hz

lemma exact_minimum_unique (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) {u v : Constraint p}
    (hu : u ∈ dualBox p) (hv : v ∈ dualBox p)
    (hminu : ∀ z ∈ dualBox p, exactObjective p I x u ≤ exactObjective p I x z)
    (hminv : ∀ z ∈ dualBox p, exactObjective p I x v ≤ exactObjective p I x z) : u = v := by
  let T := transposeContinuous p (I.J x)
  have hη := (valid_tuning_positive p hp).2.2.1
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  have hT : ∀ ℓ, ‖ℓ‖ ≤ p.H * ‖T ℓ‖ := by
    intro ℓ
    exact H.surjective x ℓ
  have hd := fullrank_dual_distance T T (gradient I.f x) (gradient I.f x)
    (I.c x) (I.c x) u v hη.le hH hT
    (exact_minimum_vi p I x hu hminu hv) (exact_minimum_vi p I x hv hminv hu)
  simp only [sub_self, norm_zero, mul_zero] at hd
  have hn : ‖u - v‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    exact (not_lt_of_ge hd) (mul_pos hη hpos)
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

lemma scalar_box_mul_le_hinge {ρ a b : ℝ} (ha : 0 ≤ a) (haρ : a ≤ ρ) :
    a * b ≤ ρ * max b 0 := by
  by_cases hb : 0 ≤ b
  · rw [max_eq_left hb]
    exact mul_le_mul_of_nonneg_right haρ hb
  · have hb' : b ≤ 0 := le_of_lt (lt_of_not_ge hb)
    rw [max_eq_right hb', mul_zero]
    exact mul_nonpos_of_nonneg_of_nonpos ha hb'

lemma box_pairing_le_hinge (p : Params) (r : Constraint p) {ℓ : Constraint p}
    (hℓ : ℓ ∈ dualBox p) : ⟪r, ℓ⟫ ≤ rho p * ∑ i, max (r i) 0 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact scalar_box_mul_le_hinge (hℓ i).1 (hℓ i).2

lemma box_support_equality (p : Params) (r : Constraint p) {ℓ : Constraint p}
    (hρ : 0 ≤ rho p) (hℓ : ℓ ∈ dualBox p)
    (hvi : ∀ z ∈ dualBox p, 0 ≤ ⟪-r, z - ℓ⟫) :
    ⟪r, ℓ⟫ = rho p * ∑ i, max (r i) 0 := by
  classical
  let z : Constraint p := WithLp.toLp 2 (fun i => if 0 < r i then rho p else 0)
  have hz : z ∈ dualBox p := by
    intro i
    change 0 ≤ (if 0 < r i then rho p else 0) ∧ (if 0 < r i then rho p else 0) ≤ rho p
    split_ifs <;> exact ⟨by positivity, by simp_all⟩
  have hzval : ⟪r, z⟫ = rho p * ∑ i, max (r i) 0 := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (if 0 < r i then rho p else 0) * r i = rho p * max (r i) 0
    split_ifs with hi
    · rw [max_eq_left hi.le]
    · rw [max_eq_right (le_of_not_gt hi)]
      ring
  have h := hvi z hz
  rw [inner_neg_left, inner_sub_right, hzval] at h
  exact le_antisymm (box_pairing_le_hinge p r hℓ) (by linarith)

noncomputable def linearizedConstraints (p : Params) (I : Problem p) (x s : p.E) : Constraint p :=
  WithLp.toLp 2 (fun i => I.c x i + ⟪I.J x i, s⟫)

lemma linearized_pairing (p : Params) (I : Problem p) (x s : p.E) (ℓ : Constraint p) :
    ⟪linearizedConstraints p I x s, ℓ⟫ =
      ⟪I.c x, ℓ⟫ + ⟪transposeAction p (I.J x) ℓ, s⟫ := by
  simp [linearizedConstraints, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    transposeAction, sum_inner, real_inner_smul_left, mul_add, Finset.sum_add_distrib]

lemma gradient_continuous (p : Params) (I : Problem p) (H : Regularity p I) (hH : 0 ≤ p.H) :
    Continuous (gradient I.f) := by
  have h : LipschitzWith ⟨p.H, hH⟩ (gradient I.f) :=
    LipschitzWith.of_dist_le_mul (K := ⟨p.H, hH⟩) fun x y => by
      simp only [dist_eq_norm]
      change ‖gradient I.f x - gradient I.f y‖ ≤ p.H * ‖x - y‖
      exact H.gradientLipschitz x y
  exact h.continuous

lemma jacobian_continuous (p : Params) (I : Problem p) (H : Regularity p I) (hH : 0 ≤ p.H) :
    Continuous I.J := by
  have h : LipschitzWith ⟨p.H, hH⟩ I.J :=
    LipschitzWith.of_dist_le_mul (K := ⟨p.H, hH⟩) fun x y => by
      simp only [dist_eq_norm]
      change ‖I.J x - I.J y‖ ≤ p.H * ‖x - y‖
      exact H.jacobianLipschitz x y
  exact h.continuous

lemma constraints_continuous (p : Params) (I : Problem p) (H : Regularity p I) :
    Continuous I.c := by
  have hi (i : Fin p.m) : Continuous (fun x => I.c x i) :=
    continuous_iff_continuousAt.mpr fun x => (H.constraintGradient x i).differentiableAt.continuousAt
  have h := (PiLp.continuous_toLp 2 (fun _ : Fin p.m => ℝ)).comp (continuous_pi hi)
  convert h using 1
  funext x
  ext i
  rfl

lemma continuous_exactObjective_joint (p : Params) (I : Problem p) (H : Regularity p I)
    (hH : 0 ≤ p.H) :
    Continuous (fun z : p.E × Constraint p => exactObjective p I z.1 z.2) := by
  have hg := gradient_continuous p I H hH
  have hJ := jacobian_continuous p I H hH
  have hc := constraints_continuous p I H
  unfold exactObjective transposeAction
  fun_prop

set_option maxHeartbeats 800000 in
lemma continuous_exactDualPoint (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) : Continuous (exactDualPoint p I) := by
  have hρ := (valid_tuning_positive p hp).1.le
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  let : CompactSpace (dualBox p) := isCompact_iff_compactSpace.mp (compact_dualBox p)
  let f : p.E → dualBox p := fun x => ⟨exactDualPoint p I x, (exactDualPoint_spec p I x hρ).1⟩
  have hq : Continuous (fun z : p.E × dualBox p => exactObjective p I z.1 z.2.val) :=
    (continuous_exactObjective_joint p I H hH).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hmin : ∀ (x : p.E) (u : dualBox p),
      exactObjective p I x (f x).val ≤ exactObjective p I x u.val := by
    intro x u
    exact (exactDualPoint_spec p I x hρ).2 u.val u.property
  have hunique : ∀ x (u : dualBox p),
      (∀ z : dualBox p, exactObjective p I x u.val ≤ exactObjective p I x z.val) → f x = u := by
    intro x u hminu
    apply Subtype.ext
    apply exact_minimum_unique p I hp H x (exactDualPoint_spec p I x hρ).1 u.property
      (exactDualPoint_spec p I x hρ).2
    intro z hz
    exact hminu ⟨z, hz⟩
  have hf := continuous_unique_minimizer (fun x (u : dualBox p) => exactObjective p I x u.val)
    f hq hmin hunique
  exact continuous_subtype_val.comp hf

lemma continuous_exactModelStep (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) : Continuous (exactModelStep p I) := by
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  have hg := gradient_continuous p I H hH
  have hJ := jacobian_continuous p I H hH
  have hℓ := continuous_exactDualPoint p I hp H
  unfold exactModelStep transposeAction
  fun_prop

end LongTails.Proofs.SurjectiveProxLinearExactModel
