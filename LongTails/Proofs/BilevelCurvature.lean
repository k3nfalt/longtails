import LongTails.Proofs.GdConvex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option maxSynthPendingDepth 5

namespace LongTails.Proofs.BilevelCurvature

open scoped RealInnerProductSpace

lemma nonnegative_derivative_sq {h d : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hd : ∀ x, HasDerivAt h (d x) x)
    (hlip : ∀ x y, ‖d x - d y‖ ≤ L * ‖x - y‖)
    (hnonneg : ∀ x, 0 ≤ h x) (x : ℝ) :
    (d x) ^ 2 ≤ 2 * L * h x := by
  have hg : ∀ x, HasGradientAt h (d x) x := by
    intro x
    simpa using (hd x).hasGradientAt
  have hs := OracleTemplate.Gradient.descent hL hg hlip x
  have hn := hnonneg (x - (1 / L) • d x)
  have hq : ‖d x‖ ^ 2 / (2 * L) ≤ h x := by linarith
  have := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp hq
  simpa only [Real.norm_eq_abs, sq_abs, mul_comm] using this

lemma nonnegative_derivative_abs {h d : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hd : ∀ x, HasDerivAt h (d x) x)
    (hlip : ∀ x y, ‖d x - d y‖ ≤ L * ‖x - y‖)
    (hnonneg : ∀ x, 0 ≤ h x) (x : ℝ) :
    |d x| ≤ Real.sqrt (2 * L * h x) := by
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt (mul_nonneg (by positivity) (hnonneg x))]
  exact nonnegative_derivative_sq hL hd hlip hnonneg x

lemma bilinear_mixed_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (P : Seminorm ℝ E) {C : ℝ} (hC : 0 ≤ C)
    (hsym : ∀ a b, B a b = B b a)
    (hdiag : ∀ a, |B a a| ≤ C * ‖a‖ * P a) (a b : E) :
    |B a b| ≤ C * (‖a‖ * P b + ‖b‖ * P a) := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hb : b = 0
  · subst b
    simp
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  let t := ‖a‖ / ‖b‖
  have ht : 0 < t := div_pos han hbn
  have htb : t * ‖b‖ = ‖a‖ := div_mul_cancel₀ _ hbn.ne'
  have htn : ‖t • b‖ = ‖a‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, htb]
  have hp : ‖a + t • b‖ ≤ 2 * ‖a‖ := by
    simpa only [htn, two_mul] using norm_add_le a (t • b)
  have hm : ‖a - t • b‖ ≤ 2 * ‖a‖ := by
    simpa only [htn, two_mul] using norm_sub_le a (t • b)
  have hPp : P (a + t • b) ≤ P a + t * P b := by
    simpa only [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ht] using
      map_add_le_add P a (t • b)
  have hPm : P (a - t • b) ≤ P a + t * P b := by
    simpa only [sub_eq_add_neg, map_neg_eq_map, map_smul_eq_mul,
      Real.norm_eq_abs, abs_of_pos ht] using map_add_le_add P a (-(t • b))
  have hplus : |B (a + t • b) (a + t • b)| ≤
      C * (2 * ‖a‖) * (P a + t * P b) := by
    refine (hdiag _).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp hC) hPp
      (apply_nonneg P _) (by positivity)
  have hminus : |B (a - t • b) (a - t • b)| ≤
      C * (2 * ‖a‖) * (P a + t * P b) := by
    refine (hdiag _).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hm hC) hPm
      (apply_nonneg P _) (by positivity)
  have hid : B (a + t • b) (a + t • b) - B (a - t • b) (a - t • b) =
      4 * t * B a b := by
    simp only [map_add, map_sub, map_smul, add_apply,
      sub_apply, smul_apply, smul_eq_mul]
    rw [hsym b a]
    ring
  have habs := norm_sub_le (B (a + t • b) (a + t • b)) (B (a - t • b) (a - t • b))
  simp only [Real.norm_eq_abs] at habs
  rw [hid, abs_mul, abs_of_pos (by positivity : 0 < 4 * t)] at habs
  have htarget : 4 * t * (C * (‖a‖ * P b + ‖b‖ * P a)) =
      2 * (C * (2 * ‖a‖) * (P a + t * P b)) := by
    calc
      _ = 4 * C * (‖a‖ * t * P b + (t * ‖b‖) * P a) := by ring
      _ = _ := by rw [htb]; ring
  nlinarith

lemma positive_field_derivative_sq {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {H : X → E →L[ℝ] E} {D : X → X →L[ℝ] E →L[ℝ] E} {L : ℝ}
    (hL : 0 < L) (hD : ∀ x, HasFDerivAt H (D x) x)
    (hLip : ∀ x y, ‖D x - D y‖ ≤ L * ‖x - y‖)
    (hpos : ∀ x a, 0 ≤ ⟪H x a, a⟫) (x w : X) (a : E) :
    ⟪D x w a, a⟫ ^ 2 ≤ 2 * L * ‖w‖ ^ 2 * ‖a‖ ^ 2 * ⟪H x a, a⟫ := by
  by_cases hw : w = 0
  · subst w
    simp
  by_cases ha : a = 0
  · subst a
    simp
  let h := fun t : ℝ => ⟪H (x + t • w) a, a⟫
  let d := fun t : ℝ => ⟪D (x + t • w) w a, a⟫
  have hd : ∀ t, HasDerivAt h (d t) t := by
    intro t
    have hc := (hD (x + t • w)).comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const w |>.const_add x)
    have hi := HasDerivAt.inner ℝ (hc.clm_apply (hasDerivAt_const t a))
      (hasDerivAt_const t a)
    simpa [h, d] using hi
  have hl : ∀ s t, ‖d s - d t‖ ≤ (L * ‖w‖ ^ 2 * ‖a‖ ^ 2) * ‖s - t‖ := by
    intro s t
    have hid : d s - d t = ⟪(D (x + s • w) - D (x + t • w)) w a, a⟫ := by
      simp [d, inner_sub_left]
    have hdist : ‖(x + s • w) - (x + t • w)‖ = ‖s - t‖ * ‖w‖ := by
      rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul]
    rw [hid]
    calc
      _ ≤ ‖(D (x + s • w) - D (x + t • w)) w a‖ * ‖a‖ := norm_inner_le_norm _ _
      _ ≤ (‖D (x + s • w) - D (x + t • w)‖ * ‖w‖ * ‖a‖) * ‖a‖ := by
        gcongr
        exact ((D (x + s • w) - D (x + t • w)) w).le_opNorm a |>.trans
          (mul_le_mul_of_nonneg_right
            ((D (x + s • w) - D (x + t • w)).le_opNorm w) (norm_nonneg a))
      _ ≤ (L * (‖s - t‖ * ‖w‖) * ‖w‖ * ‖a‖) * ‖a‖ := by
        gcongr
        simpa only [hdist] using hLip (x + s • w) (x + t • w)
      _ = _ := by ring
  have hc : 0 < L * ‖w‖ ^ 2 * ‖a‖ ^ 2 := by
    exact mul_pos (mul_pos hL (sq_pos_of_pos (norm_pos_iff.mpr hw)))
      (sq_pos_of_pos (norm_pos_iff.mpr ha))
  have hs := nonnegative_derivative_sq hc hd hl (fun t => hpos _ _) 0
  simpa [h, d, mul_assoc] using hs

noncomputable def energySeminorm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (H : E →L[ℝ] E)
    (hsym : ∀ a b, ⟪H a, b⟫ = ⟪H b, a⟫)
    (hpos : ∀ a, 0 ≤ ⟪H a, a⟫) : Seminorm ℝ E := by
  letI : PreInnerProductSpace.Core ℝ E := {
    inner := fun a b => ⟪H a, b⟫
    conj_inner_symm := fun a b => by simpa using hsym b a
    re_inner_nonneg := hpos
    add_left := fun a b c => by simp [inner_add_left]
    smul_left := fun a b r => by simp [real_inner_smul_left] }
  exact @normSeminorm ℝ E _ InnerProductSpace.Core.toSeminormedAddCommGroup
    InnerProductSpace.Core.toNormedSpace

lemma energySeminorm_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (H : E →L[ℝ] E)
    (hsym : ∀ a b, ⟪H a, b⟫ = ⟪H b, a⟫)
    (hpos : ∀ a, 0 ≤ ⟪H a, a⟫) (a : E) :
    energySeminorm H hsym hpos a = Real.sqrt ⟪H a, a⟫ := rfl

lemma positive_field_derivative_abs {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {H : X → E →L[ℝ] E} {D : X → X →L[ℝ] E →L[ℝ] E} {L : ℝ}
    (hL : 0 < L) (hD : ∀ x, HasFDerivAt H (D x) x)
    (hLip : ∀ x y, ‖D x - D y‖ ≤ L * ‖x - y‖)
    (hpos : ∀ x a, 0 ≤ ⟪H x a, a⟫) (x w : X) (a : E) :
    |⟪D x w a, a⟫| ≤ Real.sqrt (2 * L) * ‖w‖ * ‖a‖ * Real.sqrt ⟪H x a, a⟫ := by
  have hs := positive_field_derivative_sq hL hD hLip hpos x w a
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (hpos x a),
    Real.sq_sqrt (by positivity : 0 ≤ 2 * L)]
  simpa only [mul_assoc] using hs

lemma symmetric_field_derivative {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {H : X → E →L[ℝ] E} {D : X → X →L[ℝ] E →L[ℝ] E}
    (hD : ∀ x, HasFDerivAt H (D x) x)
    (hsym : ∀ x a b, ⟪H x a, b⟫ = ⟪H x b, a⟫)
    (x w : X) (a b : E) : ⟪D x w a, b⟫ = ⟪D x w b, a⟫ := by
  have hc := (hD (x + (0 : ℝ) • w)).comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_id 0).smul_const w |>.const_add x)
  have hab := HasDerivAt.inner ℝ (hc.clm_apply (hasDerivAt_const 0 a))
    (hasDerivAt_const 0 b)
  have hba := HasDerivAt.inner ℝ (hc.clm_apply (hasDerivAt_const 0 b))
    (hasDerivAt_const 0 a)
  simp only [id_eq, Function.comp_apply, one_smul, zero_smul, map_zero, add_zero,
    inner_zero_right, zero_add] at hab hba
  have he : (fun t : ℝ => ⟪H (x + t • w) a, b⟫) =
      (fun t : ℝ => ⟪H (x + t • w) b, a⟫) := funext fun t => hsym _ a b
  rw [he] at hab
  exact hab.unique hba

lemma positive_field_derivative_mixed {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {H : X → E →L[ℝ] E} {D : X → X →L[ℝ] E →L[ℝ] E} {L : ℝ}
    (hL : 0 < L) (hD : ∀ x, HasFDerivAt H (D x) x)
    (hLip : ∀ x y, ‖D x - D y‖ ≤ L * ‖x - y‖)
    (hpos : ∀ x a, 0 ≤ ⟪H x a, a⟫)
    (hsym : ∀ x a b, ⟪H x a, b⟫ = ⟪H x b, a⟫)
    (x w : X) (a b : E) :
    |⟪D x w a, b⟫| ≤ Real.sqrt (2 * L) * ‖w‖ *
      (‖a‖ * Real.sqrt ⟪H x b, b⟫ + ‖b‖ * Real.sqrt ⟪H x a, a⟫) := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ).comp (D x w)
  let P := energySeminorm (H x) (hsym x) (hpos x)
  have hd : ∀ v, |B v v| ≤ (Real.sqrt (2 * L) * ‖w‖) * ‖v‖ * P v := by
    intro v
    exact positive_field_derivative_abs hL hD hLip hpos x w v
  exact bilinear_mixed_bound B P (by positivity) (symmetric_field_derivative hD hsym x w) hd a b


lemma normalized_positive_field_mixed {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {H : X → E →L[ℝ] E} {D : X → X →L[ℝ] E →L[ℝ] E} {L : ℝ}
    (hL : 0 < L) (hD : ∀ x, HasFDerivAt H (D x) x)
    (hLip : ∀ x y, ‖D x - D y‖ ≤ L * ‖x - y‖)
    (hpos : ∀ x a, 0 ≤ ⟪H x a, a⟫)
    (hsym : ∀ x a b, ⟪H x a, b⟫ = ⟪H x b, a⟫)
    (x w : X) (a b : E) :
    |L⁻¹ * ⟪D x w a, b⟫| ≤ 2 * ‖w‖ *
      (‖a‖ * Real.sqrt ⟪(L⁻¹ • H x) b, b⟫ +
        ‖b‖ * Real.sqrt ⟪(L⁻¹ • H x) a, a⟫) := by
  have hDn : ∀ x, HasFDerivAt (fun z => L⁻¹ • H z) (L⁻¹ • D x) x :=
    fun x => (hD x).const_smul L⁻¹
  have hLn : ∀ x y, ‖L⁻¹ • D x - L⁻¹ • D y‖ ≤ (1 : ℝ) * ‖x - y‖ := by
    intro x y
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hL.le)]
    calc
      _ ≤ L⁻¹ * (L * ‖x - y‖) := mul_le_mul_of_nonneg_left (hLip x y) (by positivity)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hL.ne']
  have hpn : ∀ x a, 0 ≤ ⟪(L⁻¹ • H x) a, a⟫ := by
    intro x a
    simpa only [smul_apply, inner_smul_left, conj_trivial] using
      mul_nonneg (inv_nonneg.mpr hL.le) (hpos x a)
  have hsn : ∀ x a b, ⟪(L⁻¹ • H x) a, b⟫ = ⟪(L⁻¹ • H x) b, a⟫ := by
    intro x a b
    simp only [smul_apply, inner_smul_left, conj_trivial, hsym x a b]
  have hh := positive_field_derivative_mixed (by norm_num : (0 : ℝ) < 1)
    hDn hLn hpn hsn x w a b
  simp only [smul_apply, inner_smul_left, conj_trivial, mul_one] at hh
  simp only [smul_apply, inner_smul_left, conj_trivial]
  refine hh.trans ?_
  gcongr
  norm_num

lemma coercive_norm_le_energy {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (H : E →L[ℝ] E) {μ : ℝ} (hμ : 0 < μ)
    (hco : ∀ a, μ * ‖a‖ ^ 2 ≤ ⟪H a, a⟫) (a : E) :
    Real.sqrt μ * ‖a‖ ≤ Real.sqrt ⟪H a, a⟫ := by
  have hp : 0 ≤ ⟪H a, a⟫ := (by positivity : 0 ≤ μ * ‖a‖ ^ 2).trans (hco a)
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt hμ.le, Real.sq_sqrt hp]
  exact hco a

lemma coercive_solution_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (H : E →L[ℝ] E) {μ : ℝ}
    (hco : ∀ a, μ * ‖a‖ ^ 2 ≤ ⟪H a, a⟫) {a b : E} (he : H a = b) :
    μ * ‖a‖ ≤ ‖b‖ := by
  have hc := hco a
  rw [he] at hc
  have hi := real_inner_le_norm b a
  by_cases hz : a = 0
  · simp [hz]
  have hp : 0 < ‖a‖ := norm_pos_iff.mpr hz
  nlinarith

lemma coercive_solution_energy {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (H : E →L[ℝ] E) {μ : ℝ} (hμ : 0 < μ)
    (hco : ∀ a, μ * ‖a‖ ^ 2 ≤ ⟪H a, a⟫) {a b : E} (he : H a = b) :
    μ * ⟪H a, a⟫ ≤ ‖b‖ ^ 2 := by
  have hn := coercive_solution_norm H hco he
  have hi := mul_le_mul_of_nonneg_left (real_inner_le_norm b a) hμ.le
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg b)]


lemma coercive_isInvertible {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (H : E →L[ℝ] E) {μ : ℝ} (hμ : 0 < μ)
    (hc : ∀ a, μ * ‖a‖ ^ 2 ≤ ⟪H a, a⟫) : H.IsInvertible := by
  have hinj : Function.Injective H := by
    intro a b hab
    have h := hc (a - b)
    rw [map_sub, hab, sub_self, inner_zero_left] at h
    have hn : ‖a - b‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖a - b‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  exact ⟨(LinearEquiv.ofInjectiveEndo H.toLinearMap hinj).toContinuousLinearEquiv, rfl⟩


lemma coercive_inverse_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (H : E →L[ℝ] E) {μ : ℝ} (hμ : 0 < μ)
    (hc : ∀ a, μ * ‖a‖ ^ 2 ≤ ⟪H a, a⟫) : ‖H.inverse‖ ≤ μ⁻¹ := by
  have hi := coercive_isInvertible H hμ hc
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hμ.le)
  intro v
  have h := coercive_solution_norm H hc (hi.self_apply_inverse v)
  apply (mul_le_mul_iff_right₀ hμ).mp
  calc
    _ ≤ ‖v‖ := h
    _ = μ * (μ⁻¹ * ‖v‖) := by rw [← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul]

lemma inverse_inner_swap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (hi : H.IsInvertible)
    (hs : ∀ a b, ⟪H a, b⟫ = ⟪H b, a⟫) (a b : E) :
    ⟪H.inverse a, b⟫ = ⟪a, H.inverse b⟫ := by
  have h := hs (H.inverse a) (H.inverse b)
  rw [hi.self_apply_inverse, hi.self_apply_inverse] at h
  exact (real_inner_comm _ _).trans h.symm

end LongTails.Proofs.BilevelCurvature
