import LongTails.Proofs.AbcHardGeometry
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.AbcHardOracle

open LongTails.Proofs.AbcChain LongTails.Proofs.AbcChainMask LongTails.Proofs.AbcHardFunction
open LongTails.Proofs.AbcHardGeometry

variable {d n : ℕ}

noncomputable def stage (u : Chain n) : ℕ :=
  Finset.univ.sup (fun i : Fin (n + 1) => if 1 / 4 < |u i| then i.val + 1 else 0)

noncomputable def stageUpTo (r : ℕ) (u : Chain n) : ℕ :=
  Finset.univ.sup (fun i : Fin (n + 1) => if i.val < r ∧ 1 / 4 < |u i| then i.val + 1 else 0)

lemma small_of_stage (u : Chain n) (i : Fin (n + 1)) (hi : stage u ≤ i.val) : |u i| ≤ 1 / 4 := by
  by_contra h
  push Not at h
  have hle : (if 1 / 4 < |u i| then i.val + 1 else 0) ≤ stage u :=
    Finset.le_sup (f := fun i : Fin (n + 1) => if 1 / 4 < |u i| then i.val + 1 else 0)
      (Finset.mem_univ i)
  rw [ite_eq_left h] at hle
  omega

lemma stage_le (u : Chain n) : stage u ≤ n + 1 := by
  apply Finset.sup_le
  intro i _
  split_ifs <;> omega

lemma stageUpTo_le (r : ℕ) (u : Chain n) : stageUpTo r u ≤ r := by
  apply Finset.sup_le
  intro i _
  split_ifs with h <;> omega

lemma stageUpTo_eq (r : ℕ) (u : Chain n) (h : ∀ i : Fin (n + 1), r ≤ i.val → |u i| ≤ 1 / 4) :
    stageUpTo r u = stage u := by
  unfold stageUpTo stage
  congr 1
  funext i
  by_cases hi : i.val < r
  · simp only [hi, true_and]
  · have := h i (by omega)
    simp only [hi, false_and, ↓reduceIte, show ¬ (1 / 4 : ℝ) < |u i| by linarith]

lemma stageUpTo_congr (r : ℕ) (u v : Chain n) (h : ∀ i : Fin (n + 1), i.val < r → u i = v i) :
    stageUpTo r u = stageUpTo r v := by
  unfold stageUpTo
  congr 1
  funext i
  by_cases hi : i.val < r
  · rw [h i hi]
  · simp only [hi, false_and, ↓reduceIte]

lemma last_small_of_stage (u : Chain n) (h : stage u < n + 1) : |u (Fin.last n)| < 1 := by
  have := small_of_stage u (Fin.last n) (by simp; omega)
  linarith

noncomputable def coin (q ω : ℝ) : ℝ := if ω ≤ q then 1 / q else 0

noncomputable def unif : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unif := by
  constructor
  simp [unif]

lemma setOf_le_measurable (q : ℝ) : MeasurableSet {ω : ℝ | ω ≤ q} := measurableSet_Iic

lemma unif_le (q : ℝ) (h1 : q ≤ 1) : unif {ω | ω ≤ q} = ENNReal.ofReal q := by
  have hs : {ω : ℝ | ω ≤ q} ∩ Set.Icc 0 1 = Set.Icc 0 q := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc]; constructor
    · rintro ⟨h, h', _⟩; exact ⟨h', h⟩
    · rintro ⟨h', h⟩; exact ⟨h, h', h.trans h1⟩
  rw [unif, Measure.restrict_apply (setOf_le_measurable q), hs, Real.volume_Icc, sub_zero]

lemma unif_real_le (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : unif.real {ω | ω ≤ q} = q := by
  rw [Measure.real, unif_le q h1, ENNReal.toReal_ofReal h0]

lemma coin_measurable (q : ℝ) : Measurable (coin q) := by
  unfold coin
  exact Measurable.ite (setOf_le_measurable q) measurable_const measurable_const

lemma coin_integral (q : ℝ) (h0 : 0 < q) (h1 : q ≤ 1) : ∫ ω, coin q ω ∂unif = 1 := by
  have he : coin q = Set.indicator {ω | ω ≤ q} (fun _ => 1 / q) := by
    funext ω; simp [coin, Set.indicator]
  rw [he, integral_indicator (setOf_le_measurable _), setIntegral_const, unif_real_le q h0.le h1,
    smul_eq_mul]
  field_simp

lemma coin_sq_integral (q : ℝ) (h0 : 0 < q) (h1 : q ≤ 1) :
    ∫ ω, (coin q ω - 1) ^ 2 ∂unif = 1 / q - 1 := by
  have he : (fun ω => (coin q ω - 1) ^ 2) =
      fun ω => Set.indicator {ω | ω ≤ q} (fun _ => (1 / q - 1) ^ 2 - 1) ω + 1 := by
    funext ω; simp only [coin, Set.indicator, Set.mem_ofPred_eq]; split_ifs <;> ring
  rw [he, integral_add (by
      exact (integrable_const ((1 / q - 1) ^ 2 - 1)).indicator (setOf_le_measurable q))
    (integrable_const 1), integral_indicator (setOf_le_measurable _), setIntegral_const,
    unif_real_le q h0.le h1, integral_const, probReal_univ, smul_eq_mul, smul_eq_mul]
  field_simp
  try ring

lemma coin_integrable (q : ℝ) : Integrable (coin q) unif := by
  have he : coin q = Set.indicator {ω | ω ≤ q} (fun _ => 1 / q) := by
    funext ω; simp [coin, Set.indicator]
  rw [he]
  exact (integrable_const _).indicator (setOf_le_measurable _)

structure Scale where
  a : ℝ
  lam : ℝ
  ha : 0 < a
  hlam : 0 < lam

noncomputable def toUnit (S : Scale) (x0 x : Space d) : Space d := (1 / S.lam) • (x - x0)

noncomputable def objective (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) : ℝ :=
  S.a * hardValue π (toUnit S x0 x)

noncomputable def objGrad (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) : Space d :=
  (S.a / S.lam) • hardGrad π (toUnit S x0 x)

noncomputable def knownPart (S : Scale) (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (x0 x : Space d) :
    Space d :=
  (S.a / S.lam) • knownGrad π m (toUnit S x0 x)

noncomputable def reply (S : Scale) (qf : ℕ → ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d)
    (ω : ℝ) : Space d :=
  knownPart S π (stage (sel π (toUnit S x0 x))) x0 x +
    coin (qf (stage (sel π (toUnit S x0 x)))) ω •
      (objGrad S π x0 x - knownPart S π (stage (sel π (toUnit S x0 x))) x0 x)

lemma toUnit_hasFDerivAt (S : Scale) (x0 x : Space d) :
    HasFDerivAt (toUnit S x0) ((1 / S.lam) • ContinuousLinearMap.id ℝ (Space d)) x := by
  have h := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const x0).const_smul (1 / S.lam)
  have he : toUnit S x0 = fun y => (1 / S.lam) • (y - x0) := rfl
  rw [he]
  exact h

lemma objective_hasGradientAt (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    HasGradientAt (objective S π x0) (objGrad S π x0 x) x := by
  have hd := ((hardValue_hasGradientAt π (toUnit S x0 x)).hasFDerivAt.comp x
    (toUnit_hasFDerivAt S x0 x)).const_mul S.a
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · rfl
  · ext v
    simp only [objGrad, InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
      smul_apply, smul_eq_mul,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_id', id_eq,
      ContinuousLinearMap.map_smul]
    ring

lemma objective_gradient (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    gradient (objective S π x0) x = objGrad S π x0 x :=
  (objective_hasGradientAt S π x0 x).gradient

lemma toUnit_sub (S : Scale) (x0 x y : Space d) :
    toUnit S x0 x - toUnit S x0 y = (1 / S.lam) • (x - y) := by
  simp only [toUnit, ← smul_sub, sub_sub_sub_cancel_right]

lemma toUnit_norm_sub (S : Scale) (x0 x y : Space d) :
    ‖toUnit S x0 x - toUnit S x0 y‖ = ‖x - y‖ / S.lam := by
  rw [toUnit_sub, norm_smul, Real.norm_of_nonneg (by have := S.hlam; positivity)]
  ring

lemma objGrad_lipschitz (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x y : Space d) :
    ‖objGrad S π x0 x - objGrad S π x0 y‖ ≤ 1024 * S.a / S.lam ^ 2 * ‖x - y‖ := by
  have hl := hardGrad_lipschitz π (toUnit S x0 x) (toUnit S x0 y)
  rw [toUnit_norm_sub] at hl
  rw [objGrad, objGrad, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (by have := S.ha; have := S.hlam; positivity)]
  have hpos : 0 ≤ S.a / S.lam := by have := S.ha; have := S.hlam; positivity
  calc _ ≤ S.a / S.lam * (1024 * (‖x - y‖ / S.lam)) := mul_le_mul_of_nonneg_left hl hpos
    _ = _ := by field_simp

lemma secret_norm (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    ‖objGrad S π x0 x - knownPart S π (stage (sel π (toUnit S x0 x))) x0 x‖ ≤
      29 * (S.a / S.lam) := by
  rw [objGrad, knownPart, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (by have := S.ha; have := S.hlam; positivity), mul_comm]
  exact mul_le_mul_of_nonneg_right (secret_bound π _ _ (fun i hi => small_of_stage _ i hi))
    (by have := S.ha; have := S.hlam; positivity)

lemma reply_integral (S : Scale) (qf : ℕ → ℝ) (hq0 : ∀ m, 0 < qf m) (hq1 : ∀ m, qf m ≤ 1)
    (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    ∫ ω, reply S qf π x0 x ω ∂unif = objGrad S π x0 x := by
  unfold reply
  rw [integral_add (integrable_const _) ((coin_integrable _).smul_const _), integral_const,
    probReal_univ, one_smul, integral_smul_const, coin_integral _ (hq0 _) (hq1 _), one_smul]
  abel

lemma reply_integrable (S : Scale) (qf : ℕ → ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    Integrable (reply S qf π x0 x) unif := by
  unfold reply
  exact (integrable_const _).add ((coin_integrable _).smul_const _)

lemma reply_variance (S : Scale) (qf : ℕ → ℝ) (hq0 : ∀ m, 0 < qf m) (hq1 : ∀ m, qf m ≤ 1)
    (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    ∫ ω, ‖reply S qf π x0 x ω - objGrad S π x0 x‖ ^ 2 ∂unif =
      (1 / qf (stage (sel π (toUnit S x0 x))) - 1) *
        ‖objGrad S π x0 x - knownPart S π (stage (sel π (toUnit S x0 x))) x0 x‖ ^ 2 := by
  set m := stage (sel π (toUnit S x0 x))
  set v := objGrad S π x0 x - knownPart S π m x0 x
  have he : (fun ω => ‖reply S qf π x0 x ω - objGrad S π x0 x‖ ^ 2) =
      fun ω => (coin (qf m) ω - 1) ^ 2 * ‖v‖ ^ 2 := by
    funext ω
    have : reply S qf π x0 x ω - objGrad S π x0 x = (coin (qf m) ω - 1) • v := by
      simp only [reply, v, m, sub_smul, one_smul]
      abel
    rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [he, integral_mul_const, coin_sq_integral _ (hq0 m) (hq1 m)]

lemma reply_variance_integrable (S : Scale) (qf : ℕ → ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x0 x : Space d) :
    Integrable (fun ω => ‖reply S qf π x0 x ω - objGrad S π x0 x‖ ^ 2) unif := by
  set m := stage (sel π (toUnit S x0 x))
  set v := objGrad S π x0 x - knownPart S π m x0 x
  have he : (fun ω => ‖reply S qf π x0 x ω - objGrad S π x0 x‖ ^ 2) =
      fun ω => Set.indicator {ω | ω ≤ qf m} (fun _ => ((1 / qf m - 1) ^ 2 - 1) * ‖v‖ ^ 2) ω +
        ‖v‖ ^ 2 := by
    funext ω
    have : reply S qf π x0 x ω - objGrad S π x0 x = (coin (qf m) ω - 1) • v := by
      simp only [reply, v, m, sub_smul, one_smul]
      abel
    rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    simp only [coin, Set.indicator, Set.mem_ofPred_eq]
    split_ifs <;> ring
  rw [he]
  exact ((integrable_const _).indicator (setOf_le_measurable _)).add (integrable_const _)

end LongTails.Proofs.AbcHardOracle
