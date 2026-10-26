import LongTails.Algorithms.LazyAnchoredExtraProximal
import LongTails.Proofs.FrozenJacobianSplitting

open scoped RealInnerProductSpace

namespace LongTails.Proofs.LazyAnchoredInner

open LongTails.Setups.UnconstrainedLipschitzJacobianMonotone
open LongTails.Algorithms.LazyAnchoredExtraProximal
open LongTails.Proofs.FrozenJacobianSplitting

noncomputable section

variable {p : Params}

structure Regular (p : Params) (F : p.E → p.E) : Prop where
  L_nonneg : 0 ≤ p.L
  deriv : ∀ x, HasFDerivAt F (fderiv ℝ F x) x
  lip : ∀ x y, ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ p.L * ‖x - y‖
  mono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫

def reply (F : p.E → p.E) (q : Fin 2 × p.E) : p.E ⊕ (p.E →L[ℝ] p.E) :=
  if q.1 = 1 then .inr (fderiv ℝ F q.2) else .inl (F q.2)

def trueStep (F : p.E → p.E) (s : State p) : State p := update s (reply F (query s))

def tstate (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j i : ℕ) (zi Azi : p.E) : State p :=
  ⟨.trial, k, z, Fz, fderiv ℝ F (center p k z Fz), F (center p k z Fz), j, i, zi, Azi, p.x0, 0⟩

def withTrial (F : p.E → p.E) (s : State p) : State p :=
  { s with phase := .correction, y := s.trialPoint, Fy := F s.trialPoint }

lemma step_trial_accept (F : p.E → p.E) (s : State p) (hs : s.phase = .trial)
    (hacc : accepted (withTrial F s)) :
    trueStep F s = outerStart (s.k + 1) s.trialPoint (F s.trialPoint) := by
  classical
  simp only [trueStep, update, query, hs, reply]
  simp only [Fin.isValue, zero_ne_one, ↓reduceIte, readValue, afterTrial]
  unfold withTrial at hacc
  simp only [hacc, ↓reduceIte]

lemma step_trial_reject (F : p.E → p.E) (s : State p) (hs : s.phase = .trial)
    (hacc : ¬ accepted (withTrial F s)) :
    trueStep F s = withTrial F s := by
  classical
  simp only [trueStep, update, query, hs, reply]
  simp only [Fin.isValue, zero_ne_one, ↓reduceIte, readValue, afterTrial]
  unfold withTrial at hacc ⊢
  simp only [hacc, ↓reduceIte]

lemma scale_pos (hp : 0 < p.D ∧ 0 < p.ε) : 0 < scale p := by
  unfold scale
  have : (0 : ℝ) < outerCount p := by unfold outerCount; positivity
  have := hp.1; have := hp.2
  positivity

lemma step_pos (hp : 0 < p.D ∧ 0 < p.ε) (k : ℕ) : 0 < step p k := by
  unfold step; have := scale_pos hp; positivity

lemma cumulative_succ (k : ℕ) : cumulative p (k + 1) = cumulative p k + step p k := by
  unfold cumulative step; push_cast; ring

lemma cumulative_nonneg (hp : 0 < p.D ∧ 0 < p.ε) (k : ℕ) : 0 ≤ cumulative p k := by
  unfold cumulative; have := scale_pos hp; positivity

lemma cumulative_succ_pos (hp : 0 < p.D ∧ 0 < p.ε) (k : ℕ) : 0 < cumulative p (k + 1) := by
  rw [cumulative_succ]; have := cumulative_nonneg hp k; have := step_pos hp k; linarith

lemma guess_nonneg (hp : 0 < p.D ∧ 0 < p.ε) (k j : ℕ) : 0 ≤ guess p k j := by
  unfold guess radiusBound
  have := step_pos hp k; have := cumulative_succ_pos hp k; have := hp.1
  positivity

lemma condition_ge_one (hL : 0 ≤ p.L) (hp : 0 < p.D ∧ 0 < p.ε) (k j : ℕ) :
    1 ≤ condition p k j := by
  unfold condition
  have := step_pos hp k; have := guess_nonneg hp k j
  nlinarith [mul_nonneg (mul_nonneg hL (step_pos hp k).le) (guess_nonneg hp k j)]

lemma innerStep_pos (hL : 0 ≤ p.L) (hp : 0 < p.D ∧ 0 < p.ε) (k j : ℕ) : 0 < innerStep p k j := by
  unfold innerStep
  have := step_pos hp k; have := condition_ge_one hL hp k j
  positivity

lemma solve_spec (J : p.E →L[ℝ] p.E) (hJ : ∀ v, 0 ≤ ⟪J v, v⟫) {β τ : ℝ} (hβ : 0 < β)
    (hτ : 0 ≤ τ) (r : p.E) :
    (β • ContinuousLinearMap.id ℝ p.E + τ • J) (solve p J β τ r) = r := by
  unfold solve
  exact Function.invFun_eq (op_surjective J hJ hβ hτ r)

lemma solve_lipschitz (J : p.E →L[ℝ] p.E) (hJ : ∀ v, 0 ≤ ⟪J v, v⟫) {β τ : ℝ} (hβ : 1 ≤ β)
    (hτ : 0 ≤ τ) (r r' : p.E) :
    ‖solve p J β τ r - solve p J β τ r'‖ ≤ ‖r - r'‖ := by
  have hβ0 : (0 : ℝ) < β := by linarith
  have h1 := solve_spec J hJ hβ0 hτ r
  have h2 := solve_spec J hJ hβ0 hτ r'
  have h := op_norm_ge J hJ (β := β) hτ (solve p J β τ r - solve p J β τ r')
  rw [map_sub, h1, h2] at h
  nlinarith [norm_nonneg (solve p J β τ r - solve p J β τ r')]

lemma fbf_exact (J : p.E →L[ℝ] p.E) (y zi Azi Fc Fy c w : p.E) (a τ : ℝ) (ha : 0 < a)
    (hτ : 0 < τ)
    (hy : ((1 + τ / a) • ContinuousLinearMap.id ℝ p.E + τ • J) y =
      zi - τ • Azi - τ • (Fc - J c - a⁻¹ • w)) :
    (a / τ) • (zi - (y - τ • ((Fy - Fc - J (y - c)) - Azi))) = a • Fy + y - w := by
  have hX : zi - (y - τ • ((Fy - Fc - J (y - c)) - Azi)) = τ • (Fy + a⁻¹ • (y - w)) := by
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, map_sub] at hy ⊢
    linear_combination (norm := module) -hy
  rw [hX, smul_smul, div_mul_cancel₀ _ hτ.ne', smul_add, smul_smul, mul_inv_cancel₀ ha.ne',
    one_smul]
  abel

lemma contraction_arith {e q1 q2 X K t : ℝ} (hK : 1 ≤ K) (ht : 3 / 4 ≤ t)
    (hX : X ≤ e - 2 / K * q1 - t * q2) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hsplit : e ≤ 2 * (q1 + q2)) :
    X ≤ (1 - 3 / (8 * K)) * e := by
  have hK0 : 0 < K := by linarith
  have h1 : 3 / (4 * K) * q1 ≤ 2 / K * q1 := by
    apply mul_le_mul_of_nonneg_right _ hq1
    rw [div_le_div_iff₀ (by positivity) hK0]; linarith
  have h2 : 3 / (4 * K) * q2 ≤ t * q2 := by
    apply mul_le_mul_of_nonneg_right _ hq2
    have : 3 / (4 * K) ≤ 3 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have h3 : 3 / (8 * K) * e ≤ 3 / (4 * K) * (q1 + q2) := by
    have : 3 / (8 * K) * e = 3 / (4 * K) * (e / 2) := by field_simp; ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  nlinarith [h1, h2, h3]

lemma norm_sq_add_le (u v : p.E) : ‖u + v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have h := norm_add_le u v
  have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

lemma fbf_residual (J : p.E →L[ℝ] p.E) (F : p.E → p.E) (c w zi Azi y z1 : p.E) {a τ : ℝ}
    (hy : ((1 + τ / a) • ContinuousLinearMap.id ℝ p.E + τ • J) y =
      zi - τ • Azi - τ • (F c - J c - a⁻¹ • w))
    (hz1 : z1 = y - τ • ((F y - F c - J (y - c)) - Azi)) :
    zi - z1 = τ • (F y + a⁻¹ • (y - w)) := by
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply] at hy
  rw [hz1, map_sub]
  linear_combination (norm := module) -hy

lemma fbf_iteration (F : p.E → p.E) (hreg : Regular p F) {c w zs zi Azi y z1 : p.E}
    {a ρ K τ : ℝ} (ha : 0 < a) (hρ : 0 ≤ ρ) (hK : K = 5 * p.L * a * ρ + 1) (hτ : τ = a / K)
    (hzs : a • F zs + zs = w) (hR : ‖c - zs‖ ≤ ρ) (hzi : ‖zi - zs‖ ≤ ‖c - zs‖)
    (hAzi : Azi = F zi - F c - fderiv ℝ F c (zi - c))
    (hy : ((1 + τ / a) • ContinuousLinearMap.id ℝ p.E + τ • fderiv ℝ F c) y =
      zi - τ • Azi - τ • (F c - fderiv ℝ F c c - a⁻¹ • w))
    (hz1 : z1 = y - τ • ((F y - F c - fderiv ℝ F c (y - c)) - Azi)) :
    ‖y - zs‖ ≤ 7 / 5 * ‖zi - zs‖ ∧
      ‖z1 - zs‖ ^ 2 ≤ (1 - 3 / (8 * K)) * ‖zi - zs‖ ^ 2 ∧
      ‖(a / τ) • (zi - z1)‖ ≤ 2 * K * ‖zi - zs‖ := by
  set J := fderiv ℝ F c with hJdef
  have hL := hreg.L_nonneg
  have hLaρ : 0 ≤ 5 * p.L * a * ρ := by positivity
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hK0 : 0 < K := by linarith
  have hτ0 : 0 < τ := by rw [hτ]; exact div_pos ha hK0
  have hτL : τ * (5 * p.L * ρ) ≤ 1 := by
    have : τ * (5 * p.L * ρ) = (5 * p.L * a * ρ) / K := by rw [hτ]; field_simp
    rw [this, div_le_one hK0, hK]; linarith
  have hJ : ∀ v, 0 ≤ ⟪J v, v⟫ := jacobian_monotone hreg.mono (hreg.deriv c)
  set A : p.E → p.E := fun u => F u - F c - J (u - c) with hA
  have hAlip : ∀ u u' r, ‖u - c‖ ≤ r → ‖u' - c‖ ≤ r → ‖A u - A u'‖ ≤ p.L * r * ‖u - u'‖ := by
    intro u u' r hu hu'
    have : A u - A u' = (F u - J u) - (F u' - J u') := by simp only [hA, map_sub]; abel
    rw [this]
    exact remainder_lipschitz hL hreg.deriv hreg.lip c u u' hu hu'
  have hzsc : ‖zs - c‖ ≤ ρ := by rw [norm_sub_rev]; exact hR
  have hzic : ‖zi - c‖ ≤ 2 * ρ := by
    calc ‖zi - c‖ = ‖(zi - zs) + (zs - c)‖ := by congr 1; abel
      _ ≤ ‖zi - zs‖ + ‖zs - c‖ := norm_add_le _ _
      _ ≤ 2 * ρ := by linarith
  have hw : w = a • F zs + zs := hzs.symm
  have hdiff : ((1 + τ / a) • ContinuousLinearMap.id ℝ p.E + τ • J) (y - zs) =
      (zi - zs) - τ • (Azi - A zs) := by
    rw [map_sub, hy]
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, hA, hw, map_sub]
    rw [smul_add, smul_smul, inv_mul_cancel₀ ha.ne', one_smul, div_eq_mul_inv τ a]
    module
  have hyzs : ‖y - zs‖ ≤ 7 / 5 * ‖zi - zs‖ := by
    have h1 := op_norm_ge J hJ (β := 1 + τ / a) hτ0.le (y - zs)
    rw [hdiff] at h1
    have h2 : ‖Azi - A zs‖ ≤ p.L * (2 * ρ) * ‖zi - zs‖ := by
      rw [hAzi]; exact hAlip zi zs (2 * ρ) hzic (by linarith)
    have h3 : ‖(zi - zs) - τ • (Azi - A zs)‖ ≤ ‖zi - zs‖ + τ * (p.L * (2 * ρ) * ‖zi - zs‖) := by
      calc _ ≤ ‖zi - zs‖ + ‖τ • (Azi - A zs)‖ := norm_sub_le _ _
        _ ≤ _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ0]; gcongr
    have h4 : 0 ≤ τ / a := by positivity
    have h5 : τ * (p.L * (2 * ρ) * ‖zi - zs‖) ≤ 2 / 5 * ‖zi - zs‖ := by
      have : τ * (p.L * (2 * ρ) * ‖zi - zs‖) = (2 / 5) * (τ * (5 * p.L * ρ)) * ‖zi - zs‖ := by
        ring
      rw [this]
      have := norm_nonneg (zi - zs)
      nlinarith
    have h6 : ‖y - zs‖ ≤ (1 + τ / a) * ‖y - zs‖ := by
      have := norm_nonneg (y - zs); nlinarith
    linarith
  have hyc : ‖y - c‖ ≤ 12 / 5 * ρ := by
    calc ‖y - c‖ = ‖(y - zs) + (zs - c)‖ := by congr 1; abel
      _ ≤ ‖y - zs‖ + ‖zs - c‖ := norm_add_le _ _
      _ ≤ 12 / 5 * ρ := by linarith
  have hlip : ‖A y - A zi‖ ≤ p.L * (12 / 5 * ρ) * ‖y - zi‖ :=
    hAlip y zi _ hyc (by linarith)
  set G : p.E → p.E := fun u => F u + a⁻¹ • (u - w) with hG
  have hGs : G zs = 0 := by
    simp only [hG, hw]
    rw [show zs - (a • F zs + zs) = -(a • F zs) by abel, smul_neg, smul_smul,
      inv_mul_cancel₀ ha.ne', one_smul, add_neg_cancel]
  have hsm : a⁻¹ * ‖y - zs‖ ^ 2 ≤ ⟪G y - G zs, y - zs⟫ := by
    have : G y - G zs = (F y - F zs) + a⁻¹ • (y - zs) := by simp only [hG]; module
    rw [this, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [hreg.mono y zs]
  have hres : zi - z1 = τ • G y := fbf_residual J F c w zi Azi y z1 hy hz1
  have hz1' : z1 = y - τ • (A y - A zi) := by rw [hz1, hAzi]
  have hstep := fbf_step G A zi zs y z1 hτ0 hz1' hres hGs hsm hlip
  have hτℓ : τ * (p.L * (12 / 5 * ρ)) ≤ 12 / 25 := by
    have : τ * (p.L * (12 / 5 * ρ)) = 12 / 25 * (τ * (5 * p.L * ρ)) := by ring
    rw [this]; linarith
  have hτℓ0 : 0 ≤ τ * (p.L * (12 / 5 * ρ)) := by positivity
  have hsq : τ ^ 2 * (p.L * (12 / 5 * ρ)) ^ 2 ≤ 1 / 4 := by
    have h := mul_le_mul hτℓ hτℓ hτℓ0 (by norm_num)
    have : τ ^ 2 * (p.L * (12 / 5 * ρ)) ^ 2 =
        (τ * (p.L * (12 / 5 * ρ))) * (τ * (p.L * (12 / 5 * ρ))) := by ring
    rw [this]; linarith
  have hsplit : ‖zi - zs‖ ^ 2 ≤ 2 * (‖y - zs‖ ^ 2 + ‖zi - y‖ ^ 2) := by
    have : zi - zs = (y - zs) + (zi - y) := by abel
    rw [this]; exact norm_sq_add_le _ _
  have h2τ : 2 * τ * a⁻¹ = 2 / K := by rw [hτ]; field_simp
  have hcontr : ‖z1 - zs‖ ^ 2 ≤ (1 - 3 / (8 * K)) * ‖zi - zs‖ ^ 2 := by
    rw [h2τ, norm_sub_rev zi y] at hstep
    exact contraction_arith hK1 (by linarith) hstep (sq_nonneg _) (sq_nonneg _)
      (by rw [norm_sub_rev zi y] at hsplit; exact hsplit)
  refine ⟨hyzs, hcontr, ?_⟩
  have hz1n : ‖z1 - zs‖ ≤ ‖zi - zs‖ := by
    have h8 : 0 ≤ 3 / (8 * K) := by positivity
    have : ‖z1 - zs‖ ^ 2 ≤ ‖zi - zs‖ ^ 2 := by nlinarith [sq_nonneg ‖zi - zs‖]
    exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num) |>.mp this
  have haτ : a / τ = K := by rw [hτ]; field_simp
  rw [haτ, norm_smul, Real.norm_eq_abs, abs_of_pos hK0]
  have : ‖zi - z1‖ ≤ ‖zi - zs‖ + ‖z1 - zs‖ := by
    calc ‖zi - z1‖ = ‖(zi - zs) - (z1 - zs)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have h1 := mul_le_mul_of_nonneg_left this hK0.le
  have h2 := mul_le_mul_of_nonneg_left hz1n hK0.le
  linarith


def zseq (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j : ℕ) : ℕ → p.E × p.E
  | 0 => (center p k z Fz, 0)
  | i + 1 =>
      let t := withTrial F (tstate F k z Fz j i (zseq F k z Fz j i).1 (zseq F k z Fz j i).2)
      (t.corrected, t.remainder t.corrected (F t.corrected))

def trialAt (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j i : ℕ) : State p :=
  tstate F k z Fz j i (zseq F k z Fz j i).1 (zseq F k z Fz j i).2

def acc (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j i : ℕ) : Prop :=
  accepted (withTrial F (trialAt F k z Fz j i))

lemma trialAt_phase (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j i : ℕ) :
    (trialAt F k z Fz j i).phase = .trial := rfl

lemma step_correction (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j i : ℕ) :
    trueStep F (withTrial F (trialAt F k z Fz j i)) =
      if i + 1 = iterations p k j then trialAt F k z Fz (j + 1) 0
      else trialAt F k z Fz j (i + 1) := by
  have e : trueStep F (withTrial F (trialAt F k z Fz j i)) =
      afterCorrection (withTrial F (trialAt F k z Fz j i))
        (F (withTrial F (trialAt F k z Fz j i)).corrected) := by
    simp only [trueStep, update, query, withTrial, reply, Fin.isValue, zero_ne_one, ↓reduceIte,
      readValue]
  rw [e]
  unfold afterCorrection
  by_cases h : i + 1 = iterations p k j
  · have h' : (withTrial F (trialAt F k z Fz j i)).i + 1 =
        iterations p (withTrial F (trialAt F k z Fz j i)).k
          (withTrial F (trialAt F k z Fz j i)).j := h
    simp only [h', h, ↓reduceIte]
    rfl
  · have h' : ¬ (withTrial F (trialAt F k z Fz j i)).i + 1 =
        iterations p (withTrial F (trialAt F k z Fz j i)).k
          (withTrial F (trialAt F k z Fz j i)).j := h
    simp only [h', h, ↓reduceIte]
    rfl

lemma step_jacobian (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (hk : k ≠ outerCount p) :
    trueStep F (trueStep F (outerStart k z Fz)) = trialAt F k z Fz 0 0 := by
  have hph : (outerStart (p := p) k z Fz).phase = .jacobian := by
    simp only [outerStart, nextPhase, hk, ↓reduceIte]
  simp only [trueStep, update, query, hph, reply, Fin.isValue, ↓reduceIte, readJacobian]
  rfl

lemma step_finished (F : p.E → p.E) (z Fz : p.E) :
    trueStep F (outerStart (outerCount p) z Fz) = outerStart (outerCount p) z Fz := by
  have hph : (outerStart (p := p) (outerCount p) z Fz).phase = .finished := by
    simp only [outerStart, nextPhase, ↓reduceIte]
  simp only [trueStep, update, hph]

lemma zseq_snd (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j i : ℕ) :
    (zseq F k z Fz j i).2 = F (zseq F k z Fz j i).1 - F (center p k z Fz) -
      fderiv ℝ F (center p k z Fz) ((zseq F k z Fz j i).1 - center p k z Fz) := by
  cases i with
  | zero => simp [zseq]
  | succ i => simp only [zseq, State.remainder, withTrial, tstate, State.c]

lemma trialAt_solve (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε)
    (k : ℕ) (z Fz : p.E) (j i : ℕ) :
    ((1 + innerStep p k j / step p k) • ContinuousLinearMap.id ℝ p.E +
        innerStep p k j • fderiv ℝ F (center p k z Fz)) (trialAt F k z Fz j i).trialPoint =
      (zseq F k z Fz j i).1 - innerStep p k j • (zseq F k z Fz j i).2 -
        innerStep p k j • (F (center p k z Fz) -
          fderiv ℝ F (center p k z Fz) (center p k z Fz) - (step p k)⁻¹ • anchor p k z) := by
  have hτ := innerStep_pos hreg.L_nonneg hp k j
  have ha := step_pos hp k
  exact solve_spec _ (jacobian_monotone hreg.mono (hreg.deriv _)) (by positivity) hτ.le _

lemma acceptance_of_close (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε)
    {k : ℕ} {z Fz zs : p.E} {j i : ℕ}
    (hzs : step p k • F zs + zs = anchor p k z)
    (hR : ‖center p k z Fz - zs‖ ≤ guess p k j)
    (hzi : ‖(zseq F k z Fz j i).1 - zs‖ ≤ ‖center p k z Fz - zs‖)
    (hclose : ‖(zseq F k z Fz j i).1 - zs‖ ≤ ‖center p k z Fz - zs‖ / (6 * condition p k j)) :
    acc F k z Fz j i := by
  have ha := step_pos hp k
  have hK1 := condition_ge_one hreg.L_nonneg hp k j
  obtain ⟨hy, -, hcert⟩ := fbf_iteration F hreg (zs := zs) (zi := (zseq F k z Fz j i).1)
    (Azi := (zseq F k z Fz j i).2) (c := center p k z Fz) (w := anchor p k z)
    (y := (trialAt F k z Fz j i).trialPoint)
    (z1 := (withTrial F (trialAt F k z Fz j i)).corrected) ha (guess_nonneg hp k j) rfl rfl hzs hR hzi
    (zseq_snd F k z Fz j i) (trialAt_solve F hreg hp k z Fz j i) rfl
  set R := ‖center p k z Fz - zs‖
  set K := condition p k j
  set e := ‖(zseq F k z Fz j i).1 - zs‖
  have hK0 : 0 < K := by linarith
  have hR0 : 0 ≤ R := norm_nonneg _
  have he : e * (6 * K) ≤ R := by rwa [le_div_iff₀ (by positivity)] at hclose
  unfold acc accepted
  have hcert' : ‖(withTrial F (trialAt F k z Fz j i)).certificate‖ ≤ 2 * K * e := hcert
  have hyc : R - 7 / 5 * e ≤ ‖(withTrial F (trialAt F k z Fz j i)).y -
      (withTrial F (trialAt F k z Fz j i)).c‖ := by
    have h1 : R ≤ ‖(trialAt F k z Fz j i).trialPoint - center p k z Fz‖ +
        ‖(trialAt F k z Fz j i).trialPoint - zs‖ := by
      calc R = ‖(center p k z Fz - (trialAt F k z Fz j i).trialPoint) +
          ((trialAt F k z Fz j i).trialPoint - zs)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev]
    change R - 7 / 5 * e ≤ ‖(trialAt F k z Fz j i).trialPoint - center p k z Fz‖
    linarith
  have h7 : 7 / 5 * e ≤ 7 / 30 * R := by nlinarith
  nlinarith

lemma geometric_small {θ : ℝ} {n : ℕ} {B : ℝ} (hθ1 : θ ≤ 1) (hB : 1 ≤ B)
    (hn : Real.log B ≤ θ * n) : (1 - θ) ^ n ≤ B⁻¹ := by
  have h1 : 1 - θ ≤ Real.exp (-θ) := by linarith [Real.add_one_le_exp (-θ)]
  have h2 : (1 - θ) ^ n ≤ Real.exp (-θ) ^ n := pow_le_pow_left₀ (by linarith) h1 n
  have h3 : Real.exp (-θ) ^ n = Real.exp (-(θ * n)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h4 : Real.exp (-(θ * n)) ≤ Real.exp (-Real.log B) := Real.exp_le_exp.mpr (by linarith)
  have h5 : Real.exp (-Real.log B) = B⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (by linarith)]
  rw [h3] at h2
  linarith

lemma zseq_contract (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε)
    {k : ℕ} {z Fz zs : p.E} {j : ℕ}
    (hzs : step p k • F zs + zs = anchor p k z)
    (hR : ‖center p k z Fz - zs‖ ≤ guess p k j) (i : ℕ) :
    ‖(zseq F k z Fz j i).1 - zs‖ ^ 2 ≤
        (1 - 3 / (8 * condition p k j)) ^ i * ‖center p k z Fz - zs‖ ^ 2 ∧
      ‖(zseq F k z Fz j i).1 - zs‖ ≤ ‖center p k z Fz - zs‖ := by
  have ha := step_pos hp k
  have hK1 := condition_ge_one hreg.L_nonneg hp k j
  have hθ : 0 ≤ 1 - 3 / (8 * condition p k j) := by
    have : 3 / (8 * condition p k j) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  induction i with
  | zero => simp [zseq]
  | succ i ih =>
    obtain ⟨-, hcontr, -⟩ := fbf_iteration F hreg (zs := zs) (zi := (zseq F k z Fz j i).1)
      (Azi := (zseq F k z Fz j i).2) (c := center p k z Fz) (w := anchor p k z)
      (y := (trialAt F k z Fz j i).trialPoint)
      (z1 := (withTrial F (trialAt F k z Fz j i)).corrected) ha (guess_nonneg hp k j) rfl rfl
      hzs hR ih.2 (zseq_snd F k z Fz j i) (trialAt_solve F hreg hp k z Fz j i) rfl
    have hz : (zseq F k z Fz j (i + 1)).1 = (withTrial F (trialAt F k z Fz j i)).corrected := rfl
    rw [hz]
    constructor
    · calc _ ≤ (1 - 3 / (8 * condition p k j)) * ‖(zseq F k z Fz j i).1 - zs‖ ^ 2 := hcontr
        _ ≤ (1 - 3 / (8 * condition p k j)) *
            ((1 - 3 / (8 * condition p k j)) ^ i * ‖center p k z Fz - zs‖ ^ 2) :=
          mul_le_mul_of_nonneg_left ih.1 hθ
        _ = _ := by ring
    · have h8 : 0 ≤ 3 / (8 * condition p k j) := by positivity
      have hcontr' : ‖(withTrial F (trialAt F k z Fz j i)).corrected - zs‖ ^ 2 ≤
          (1 - 3 / (8 * condition p k j)) * ‖(zseq F k z Fz j i).1 - zs‖ ^ 2 := hcontr
      have : ‖(withTrial F (trialAt F k z Fz j i)).corrected - zs‖ ^ 2 ≤
          ‖center p k z Fz - zs‖ ^ 2 := by
        have h2 := pow_le_pow_left₀ (norm_nonneg _) ih.2 2
        have h3 : (1 - 3 / (8 * condition p k j)) * ‖(zseq F k z Fz j i).1 - zs‖ ^ 2 ≤
            ‖(zseq F k z Fz j i).1 - zs‖ ^ 2 := by nlinarith [sq_nonneg ‖(zseq F k z Fz j i).1 - zs‖]
        linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp this

lemma attempt_success (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε)
    {k : ℕ} {z Fz zs : p.E} {j : ℕ}
    (hzs : step p k • F zs + zs = anchor p k z)
    (hR : ‖center p k z Fz - zs‖ ≤ guess p k j) :
    ∃ i < iterations p k j, acc F k z Fz j i := by
  set K := condition p k j
  have hK1 : 1 ≤ K := condition_ge_one hreg.L_nonneg hp k j
  set n := ⌈8 / 3 * K * Real.log (36 * K ^ 2)⌉₊
  refine ⟨n, by simp only [iterations, n, K]; omega, ?_⟩
  obtain ⟨hsq, hle⟩ := zseq_contract F hreg hp hzs hR n
  apply acceptance_of_close F hreg hp hzs hR hle
  set R := ‖center p k z Fz - zs‖
  have hθ0 : 0 ≤ 3 / (8 * K) := by positivity
  have hθ1 : 3 / (8 * K) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hB : 1 ≤ 36 * K ^ 2 := by nlinarith
  have hn : Real.log (36 * K ^ 2) ≤ 3 / (8 * K) * n := by
    have h1 : 8 / 3 * K * Real.log (36 * K ^ 2) ≤ n := Nat.le_ceil _
    have h2 : 3 / (8 * K) * (8 / 3 * K * Real.log (36 * K ^ 2)) = Real.log (36 * K ^ 2) := by
      field_simp
    rw [← h2]
    exact mul_le_mul_of_nonneg_left h1 hθ0
  have hg := geometric_small hθ1 hB hn
  have hsq' : ‖(zseq F k z Fz j n).1 - zs‖ ^ 2 ≤ (R / (6 * K)) ^ 2 := by
    calc _ ≤ _ := hsq
      _ ≤ (36 * K ^ 2)⁻¹ * R ^ 2 := mul_le_mul_of_nonneg_right hg (sq_nonneg _)
      _ = (R / (6 * K)) ^ 2 := by field_simp; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hsq'


lemma iterate_trial (F : p.E → p.E) {k : ℕ} {z Fz : p.E} {j : ℕ} :
    ∀ i, i < iterations p k j → (∀ i' < i, ¬ acc F k z Fz j i') →
      (trueStep F)^[2 * i] (trialAt F k z Fz j 0) = trialAt F k z Fz j i
  | 0, _, _ => rfl
  | i + 1, hi, hno => by
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, Function.iterate_succ_apply',
      Function.iterate_succ_apply',
      iterate_trial F i (by omega) (fun i' hi' => hno i' (by omega)),
      step_trial_reject F _ rfl (hno i (by omega)), step_correction]
    simp only [show ¬ i + 1 = iterations p k j by omega, ↓reduceIte]

lemma iterate_attempt_fail (F : p.E → p.E) {k : ℕ} {z Fz : p.E} {j : ℕ}
    (hno : ∀ i < iterations p k j, ¬ acc F k z Fz j i) :
    (trueStep F)^[2 * iterations p k j] (trialAt F k z Fz j 0) = trialAt F k z Fz (j + 1) 0 := by
  obtain ⟨n, hn⟩ : ∃ n, iterations p k j = n + 1 := ⟨iterations p k j - 1, by
    unfold iterations; omega⟩
  rw [hn, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Function.iterate_succ_apply',
    Function.iterate_succ_apply',
    iterate_trial F n (by omega) (fun i' hi' => hno i' (by omega)),
    step_trial_reject F _ rfl (hno n (by omega)), step_correction]
  simp only [hn.symm, ↓reduceIte]

lemma iterate_attempt_success (F : p.E → p.E) {k : ℕ} {z Fz : p.E} {j i : ℕ}
    (hi : i < iterations p k j) (hno : ∀ i' < i, ¬ acc F k z Fz j i')
    (hacc : acc F k z Fz j i) :
    (trueStep F)^[2 * i + 1] (trialAt F k z Fz j 0) =
      outerStart (k + 1) (trialAt F k z Fz j i).trialPoint
        (F (trialAt F k z Fz j i).trialPoint) := by
  rw [Function.iterate_succ_apply', iterate_trial F i hi hno]
  exact step_trial_accept F _ rfl hacc

def attemptTicks (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 2 * iterations p k j + attemptTicks k j

lemma iterate_attempts (F : p.E → p.E) {k : ℕ} {z Fz : p.E} :
    ∀ J, (∀ j < J, ∀ i < iterations p k j, ¬ acc F k z Fz j i) →
      (trueStep F)^[attemptTicks (p := p) k J] (trialAt F k z Fz 0 0) = trialAt F k z Fz J 0
  | 0, _ => rfl
  | J + 1, hno => by
    rw [attemptTicks, Function.iterate_add_apply,
      iterate_attempts F J (fun j hj => hno j (by omega)),
      iterate_attempt_fail F (hno J (by omega))]

end

end LongTails.Proofs.LazyAnchoredInner
