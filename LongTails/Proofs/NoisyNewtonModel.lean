import LongTails.Algorithms.NoisyDampedNewton
import LongTails.Proofs.NoisyCubicStability
import LongTails.Proofs.HessianLipschitzModel
import LongTails.Proofs.GdConvex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units

namespace LongTails.Proofs.NoisyNewtonModel

open LongTails.Algorithms.NoisyDampedNewton
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma shifted_nonnegative (A H : E →L[ℝ] E) (hA : ∀ v, 0 ≤ ⟪A v, v⟫)
    (δ : ℝ) (hH : ‖H - A‖ ≤ δ) (v : E) :
    0 ≤ ⟪shifted H δ v, v⟫ := by
  have hb : ‖(H - A) v‖ ≤ δ * ‖v‖ :=
    ((H - A).le_opNorm v).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg v))
  have hi := (abs_le.mp (abs_real_inner_le_norm ((H - A) v) v)).1
  have hn := mul_le_mul_of_nonneg_right hb (norm_nonneg v)
  simp only [sub_apply, inner_sub_left] at hi
  simp only [sub_apply] at hn
  simp only [shifted, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  nlinarith only [hi, hn, hA v]

omit [FiniteDimensional ℝ E] in
lemma shifted_error (A H : E →L[ℝ] E) (δ : ℝ) (hδ : 0 ≤ δ) (hH : ‖H - A‖ ≤ δ) :
    ‖shifted H δ - A‖ ≤ 2 * δ := by
  have hi := mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)) hδ
  calc
    _ = ‖(H - A) + δ • ContinuousLinearMap.id ℝ E‖ := by unfold shifted; congr 1; abel
    _ ≤ ‖H - A‖ + ‖δ • ContinuousLinearMap.id ℝ E‖ := norm_add_le _ _
    _ ≤ 2 * δ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]; linarith

lemma shifted_invertible (H : E →L[ℝ] E) (hH : ∀ v, 0 ≤ ⟪H v, v⟫)
    (τ : ℝ) (hτ : 0 < τ) : (shifted H τ).IsInvertible := by
  have hi : Function.Injective (shifted H τ).toLinearMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hh := congrArg (fun w => ⟪w, v⟫) hv
    change ⟪(shifted H τ) v, v⟫ = ⟪0, v⟫ at hh
    simp only [shifted, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, inner_zero_left] at hh
    have hp := hH v
    have hn : ‖v‖ = 0 := by
      by_contra hn
      have hpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hn)
      have hhpos := mul_pos hτ (sq_pos_of_pos hpos)
      linarith
    exact norm_eq_zero.mp hn
  have hb : Function.Bijective (shifted H τ).toLinearMap :=
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  refine ⟨(LinearEquiv.ofBijective (shifted H τ).toLinearMap hb).toContinuousLinearEquiv, ?_⟩
  rfl

lemma response_equation (H : E →L[ℝ] E) (hH : ∀ v, 0 ≤ ⟪H v, v⟫)
    (τ : ℝ) (hτ : 0 < τ) (g : E) :
    H (response H τ g) + τ • response H τ g + g = 0 := by
  have hh := (shifted_invertible H hH τ hτ).self_apply_inverse (-g)
  change H (response H τ g) + τ • response H τ g = -g at hh
  rw [hh]
  exact neg_add_cancel g

lemma response_norm (H : E →L[ℝ] E) (hH : ∀ v, 0 ≤ ⟪H v, v⟫)
    (τ : ℝ) (hτ : 0 < τ) (g : E) : ‖response H τ g‖ ≤ ‖g‖ / τ := by
  have hh := response_equation H hH τ hτ g
  have he : H (response H τ g) + τ • response H τ g +
      (0 / 2 : ℝ) • LongTails.Proofs.CubicRegularization.cubicGradient (response H τ g) + 0 + g = 0 := by
    simpa using hh
  have hz : H 0 + τ • (0 : E) +
      (0 / 2 : ℝ) • LongTails.Proofs.CubicRegularization.cubicGradient (0 : E) + 0 = 0 := by simp
  simpa using NoisyCubicStability.response_lipschitz H hH τ 0 hτ (le_refl 0) 0 g
    (response H τ g) 0 he hz

lemma response_doubling (H : E →L[ℝ] E) (hH : ∀ v, 0 ≤ ⟪H v, v⟫)
    (τ : ℝ) (hτ : 0 < τ) (g : E) :
    ‖response H τ g‖ ≤ 2 * ‖response H (2 * τ) g‖ := by
  let s := response H τ g
  let t := response H (2 * τ) g
  have hs := response_equation H hH τ hτ g
  have ht := response_equation H hH (2 * τ) (by positivity) g
  have hs' : H s + τ • s + (0 / 2 : ℝ) • LongTails.Proofs.CubicRegularization.cubicGradient s +
      (g + τ • t) + -(τ • t) = 0 := by
    calc
      _ = H s + τ • s + g := by simp only [zero_div, zero_smul, add_zero]; abel
      _ = 0 := hs
  have ht' : H t + τ • t + (0 / 2 : ℝ) • LongTails.Proofs.CubicRegularization.cubicGradient t +
      (g + τ • t) = 0 := by
    calc
      _ = H t + (2 * τ) • t + g := by simp only [zero_div, zero_smul, add_zero]; module
      _ = 0 := ht
  have hh := NoisyCubicStability.response_lipschitz H hH τ 0 hτ (le_refl 0)
    (g + τ • t) (-(τ • t)) s t hs' ht'
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hτ, mul_div_cancel_left₀ _ hτ.ne'] at hh
  have hn : ‖s‖ ≤ ‖s - t‖ + ‖t‖ := by simpa using norm_add_le (s - t) t
  change ‖s‖ ≤ 2 * ‖t‖
  linarith

omit [FiniteDimensional ℝ E] in
lemma backtrack_curvature_lower (M₀ M₁ ρ δ α η : ℝ) (H : E →L[ℝ] E) (g : E)
    (hη : 0 ≤ η) : η ≤ backtrackCurvature M₀ M₁ ρ δ α η H g := by
  unfold backtrackCurvature
  exact le_mul_of_one_le_right hη (one_le_pow₀ (by norm_num))

omit [FiniteDimensional ℝ E] in
lemma backtrack_curvature_rejected (M₀ M₁ ρ δ α η : ℝ) (H : E →L[ℝ] E) (g : E)
    (hη : 0 ≤ η) (hne : backtrackCurvature M₀ M₁ ρ δ α η H g ≠ η) :
    2 * η ≤ backtrackCurvature M₀ M₁ ρ δ α η H g := by
  have hj : 0 < backtrackIndex M₀ M₁ ρ δ α η H g := by
    by_contra hh
    have hz : backtrackIndex M₀ M₁ ρ δ α η H g = 0 := by omega
    exact hne (by simp [backtrackCurvature, hz])
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
  have hm := mul_le_mul_of_nonneg_left hp hη
  simpa only [backtrackCurvature, pow_one, mul_comm 2 η] using hm

lemma backtracking_exists (H : E →L[ℝ] E) (hH : ∀ v, 0 ≤ ⟪H v, v⟫)
    (g : E) (M₀ M₁ ρ δ α η : ℝ) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hρ : 0 < ρ) (hα : 0 < α) (hη : 0 < η) :
    ∃ j : ℕ, Certified M₀ M₁ ρ δ α (η * 2 ^ j) (response H (η * 2 ^ j) g) := by
  let r := min ρ (min 1 (α / (4 * (M₁ + 1))))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrρ : r ≤ ρ := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hra : r ≤ α / (4 * (M₁ + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hra' := (le_div_iff₀ (show 0 < 4 * (M₁ + 1) by positivity)).mp hra
  have hrr : M₁ * r ^ 2 ≤ α / 4 := by
    have hh := mul_nonneg hM₁ (show 0 ≤ r * (1 - r) by positivity)
    nlinarith only [hh, hra', hr.le]
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt
    (max (‖g‖ / r) (4 * (δ + M₀ * r) / α) / η) (show (1 : ℝ) < 2 by norm_num)
  have ht : 0 < η * (2 : ℝ) ^ j := by positivity
  have hb : max (‖g‖ / r) (4 * (δ + M₀ * r) / α) ≤ η * 2 ^ j := by
    have hh := (div_lt_iff₀ hη).mp hj
    nlinarith only [hh]
  have hgτ := (div_le_iff₀ hr).mp ((le_max_left _ _).trans hb)
  have hs : ‖response H (η * 2 ^ j) g‖ ≤ r :=
    (response_norm H hH _ ht g).trans ((div_le_iff₀ ht).mpr (by nlinarith only [hgτ]))
  refine ⟨j, hs.trans hrρ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hs 2) hM₁).trans hrr
  · have hb' := (div_le_iff₀ hα).mp ((le_max_right _ _).trans hb)
    have hm := mul_le_mul_of_nonneg_left hs hM₀
    nlinarith only [hb', hm]

lemma backtrack_certified (H : E →L[ℝ] E) (hH : ∀ v, 0 ≤ ⟪H v, v⟫)
    (g : E) (M₀ M₁ ρ δ α η : ℝ) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hρ : 0 < ρ) (hα : 0 < α) (hη : 0 < η) :
    let τ := backtrackCurvature M₀ M₁ ρ δ α η H g
    Certified M₀ M₁ ρ δ α τ (response H τ g) := by
  classical
  have hex := backtracking_exists H hH g M₀ M₁ ρ δ α η hM₀ hM₁ hρ hα hη
  simpa only [backtrackCurvature, backtrackIndex, dite_eq_left hex] using Nat.find_spec hex

lemma rejected_doubling (H : E →L[ℝ] E) (hH : ∀ v, 0 ≤ ⟪H v, v⟫)
    (g : E) (M₀ M₁ ρ δ α τ : ℝ) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hτ : 0 < τ) (hbad : ¬ Certified M₀ M₁ ρ δ α τ (response H τ g)) :
    ρ / 2 < ‖response H (2 * τ) g‖ ∨
      α / 16 < M₁ * ‖response H (2 * τ) g‖ ^ 2 ∨
      α * (2 * τ) < 8 * δ + 16 * M₀ * ‖response H (2 * τ) g‖ := by
  by_contra hh
  push Not at hh
  have hr := response_doubling H hH τ hτ g
  apply hbad
  refine ⟨by linarith [hh.1], ?_, ?_⟩
  · have hs := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hr 2) hM₁
    nlinarith only [hs, hh.2.1]
  · have hs := mul_le_mul_of_nonneg_left hr hM₀
    nlinarith only [hs, hh.2.2]

lemma backtrack_movement (H : E →L[ℝ] E) (hH : ∀ v, 0 ≤ ⟪H v, v⟫)
    (g : E) (M₀ M₁ ρ δ α η : ℝ) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hρ : 0 < ρ) (hα : 0 < α) (hη : 0 < η)
    (hindex : 0 < backtrackIndex M₀ M₁ ρ δ α η H g) :
    let τ := backtrackCurvature M₀ M₁ ρ δ α η H g
    ρ / 2 < ‖response H τ g‖ ∨ α / 16 < M₁ * ‖response H τ g‖ ^ 2 ∨
      α * τ < 8 * δ + 16 * M₀ * ‖response H τ g‖ := by
  classical
  have hex := backtracking_exists H hH g M₀ M₁ ρ δ α η hM₀ hM₁ hρ hα hη
  have hi : backtrackIndex M₀ M₁ ρ δ α η H g = Nat.find hex := by
    simp only [backtrackIndex, dite_eq_left hex]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hindex)
  have hbad : ¬ Certified M₀ M₁ ρ δ α (η * 2 ^ k) (response H (η * 2 ^ k) g) := by
    apply Nat.find_min hex
    rw [← hi, hk]
    exact Nat.lt_succ_self k
  have hm := rejected_doubling H hH g M₀ M₁ ρ δ α (η * 2 ^ k) hM₀ hM₁
    (by positivity) hbad
  have he : backtrackCurvature M₀ M₁ ρ δ α η H g = 2 * (η * 2 ^ k) := by
    rw [backtrackCurvature, hk, pow_succ]
    ring
  simpa only [he] using hm

lemma prepare_residual {g : E → E} {A : E → E →L[ℝ] E}
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hA : ∀ x v, 0 ≤ ⟪A x v, v⟫)
    (M₀ M₁ ρ δ α : ℝ) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hα : 0 < α) (hα₁ : α ≤ 1 / 2)
    (hLip : ∀ x y, ‖y - x‖ ≤ ρ → ‖A y - A x‖ ≤ (M₀ + M₁ * ‖g x‖) * ‖y - x‖)
    (s : OracleTemplate.GeneralizedAccelerated.Iterate E) (hη : 0 < s.guess)
    (H : E →L[ℝ] E) (hH : ‖H - A (OracleTemplate.GeneralizedAccelerated.coupling s)‖ ≤ δ)
    (e : E) :
    let t := prepare M₀ M₁ ρ δ α s H (g (OracleTemplate.GeneralizedAccelerated.coupling s) + e)
    ‖g (trialPoint t) + t.curvature • t.displacement‖ ≤
      α * t.curvature * ‖t.displacement‖ + 2 * ‖e‖ := by
  let x := OracleTemplate.GeneralizedAccelerated.coupling s
  let B := shifted H δ
  let G := g x + e
  let τ := backtrackCurvature M₀ M₁ ρ (2 * δ) α s.guess B G
  let d := response B τ G
  have hB : ∀ v, 0 ≤ ⟪B v, v⟫ := shifted_nonnegative (A x) H (hA x) δ hH
  have ht : 0 < τ := by dsimp [τ, backtrackCurvature]; positivity
  have hc := backtrack_certified B hB G M₀ M₁ ρ (2 * δ) α s.guess hM₀ hM₁ hρ hα hη
  change Certified M₀ M₁ ρ (2 * δ) α τ d at hc
  have he := response_equation B hB τ ht G
  have hmodel : B ((x + d) - x) + τ • ((x + d) - x) + g x + e = 0 := by
    simp only [add_sub_cancel_left]
    change B d + τ • d + G = 0 at he
    dsimp [G] at he
    simpa only [add_assoc] using he
  have hb : ‖A x - B‖ ≤ 2 * δ := by
    rw [norm_sub_rev]
    exact shifted_error (A x) H δ hδ hH
  have hh := NoisyCubicStability.local_model_residual hg x (x + d) e B
    M₀ M₁ ρ (2 * δ) τ α hM₁ (by positivity) ht.le hα₁ hLip hb
    (by simpa only [add_sub_cancel_left] using hc.1) hmodel
    (by simpa only [add_sub_cancel_left] using hc.2.1)
    (by simpa only [add_sub_cancel_left] using hc.2.2)
  change ‖g (x + d) + τ • d‖ ≤ α * τ * ‖d‖ + 2 * ‖e‖
  simpa only [add_sub_cancel_left] using hh

lemma measurable_inverse : Measurable (fun H : E →L[ℝ] E => H.inverse) := by
  classical
  have hc : ContinuousOn (Ring.inverse : (E →L[ℝ] E) → E →L[ℝ] E) {H | IsUnit H} := by
    rintro H ⟨u, rfl⟩
    exact (NormedRing.inverse_continuousAt u).continuousWithinAt
  have hm := hc.measurable_piecewise
    (continuous_const : Continuous (fun _ : E →L[ℝ] E => (0 : E →L[ℝ] E))).continuousOn
    Units.isOpen.measurableSet
  rw [← ContinuousLinearMap.ringInverse_eq_inverse]
  convert hm using 1
  ext H
  by_cases hu : IsUnit H
  · simp [Set.piecewise, hu]
  · simp [Set.piecewise, hu, Ring.inverse_non_unit]

variable [MeasurableSpace E] [BorelSpace E]

lemma measurable_response {X : Type*} [MeasurableSpace X]
    (H : X → E →L[ℝ] E) (τ : X → ℝ) (g : X → E)
    (hH : Measurable H) (hτ : Measurable τ) (hg : Measurable g) :
    Measurable (fun x => response (H x) (τ x) (g x)) := by
  have heval : Continuous (fun w : (E →L[ℝ] E) × E => w.1 w.2) :=
    continuous_fst.clm_apply continuous_snd
  exact heval.measurable.comp
    ((measurable_inverse.comp (hH.add (hτ.smul measurable_const))).prodMk hg.neg)

lemma measurable_backtrackIndex {X : Type*} [MeasurableSpace X]
    (H : X → E →L[ℝ] E) (η : X → ℝ) (g : X → E)
    (hH : Measurable H) (hη : Measurable η) (hg : Measurable g)
    (M₀ M₁ ρ δ α : ℝ) :
    Measurable (fun x => backtrackIndex M₀ M₁ ρ δ α (η x) (H x) (g x)) := by
  classical
  let P := fun x j => Certified M₀ M₁ ρ δ α (η x * 2 ^ j)
    (response (H x) (η x * 2 ^ j) (g x))
  have hm (j : ℕ) : MeasurableSet {x | P x j} := by
    have hs := (measurable_response H (fun x => η x * 2 ^ j) g hH (hη.mul_const _) hg).norm
    exact (measurableSet_le hs measurable_const).inter
      ((measurableSet_le ((hs.pow_const 2).const_mul M₁) measurable_const).inter
        (measurableSet_le ((hs.const_mul M₀).const_add δ |>.const_mul 4)
          ((hη.mul_const _).const_mul α)))
  let Q := fun x j => P x j ∨ (¬ ∃ k, P x k) ∧ j = 0
  have hex (x : X) : ∃ j, Q x j := by
    by_cases hh : ∃ j, P x j
    · obtain ⟨j, hj⟩ := hh
      exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr ⟨hh, rfl⟩⟩
  have hmex : MeasurableSet {x | ∃ k, P x k} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion hm
  have hmQ (j : ℕ) : MeasurableSet {x | Q x j} :=
    (hm j).union (hmex.compl.inter (MeasurableSet.const _))
  have he (x : X) : backtrackIndex M₀ M₁ ρ δ α (η x) (H x) (g x) = Nat.find (hex x) := by
    unfold backtrackIndex
    by_cases hh : ∃ j, P x j
    · rw [dite_eq_left hh]
      exact Nat.find_congr' (by intro j; change P x j ↔ Q x j; simp only [Q, hh, not_true_eq_false, false_and, or_false])
    · rw [dite_eq_right hh]
      exact ((Nat.find_eq_zero (hex x)).mpr (Or.inr ⟨hh, rfl⟩)).symm
  simpa only [he] using measurable_find hex hmQ

omit [MeasurableSpace E] [BorelSpace E] in
lemma convex_hessian_facts [CompleteSpace E] {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : ConvexOn ℝ Set.univ f) :
    (∀ x y, f x + ⟪gradient f x, y - x⟫ ≤ f y) ∧
      (∀ x v, 0 ≤ ⟪fderiv ℝ (gradient f) x v, v⟫) := by
  have hg : ∀ x, HasGradientAt f (gradient f x) x :=
    fun x => (hf.differentiable (by norm_num) x).hasGradientAt
  have hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ +
      (0 : ℝ) / 2 * ‖y - x‖ ^ 2 ≤ f y := by
    intro x y
    have h := OracleTemplate.Gradient.convex_support hc hg x y
    simpa only [zero_div, zero_mul, add_zero, add_comm] using (le_sub_iff_add_le.mp h)
  constructor
  · intro x y
    simpa using hs x y
  · intro x v
    simpa using OracleTemplate.NonlinearTemporalDiscrepancy.hessian_lower_bound
      ((OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one hf).differentiable
        (by norm_num)) hs x v

end LongTails.Proofs.NoisyNewtonModel
