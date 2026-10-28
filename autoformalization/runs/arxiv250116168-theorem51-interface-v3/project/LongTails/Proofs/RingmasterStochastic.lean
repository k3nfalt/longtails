import LongTails.Algorithms.RingmasterAsgd
import LongTails.Proofs.RennalaStochastic
import LongTails.Proofs.AdaptiveIID
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.RingmasterAsgd

open Rennala

variable {d : ℕ} {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]

omit [MeasurableSpace Ω] [MeasurableSpace Ξ] in
theorem history_stable (g : Point d → Ω → Point d) (gamma : ℝ) (a : ℕ → ℕ) (x0 : Point d)
    (ξ : ℕ → Ω) (k j : ℕ) (hj : j ≤ k) :
    history g gamma a x0 ξ k j = delayedIterate g gamma a x0 ξ j := by
  induction k with
  | zero =>
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    rfl
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · have h' : j ≤ k := Nat.lt_succ_iff.mp h
      change (if j ≤ k then history g gamma a x0 ξ k j
        else history g gamma a x0 ξ k k - gamma • g (history g gamma a x0 ξ k (a k)) (ξ k)) = _
      rw [ite_eq_left h', ih h']
    · obtain rfl : j = k + 1 := le_antisymm hj h
      rfl

omit [MeasurableSpace Ω] [MeasurableSpace Ξ] in
theorem delayedIterate_succ (g : Point d → Ω → Point d) (gamma : ℝ) (a : ℕ → ℕ) (x0 : Point d)
    (ξ : ℕ → Ω) (k : ℕ) (hk : a k ≤ k) :
    delayedIterate g gamma a x0 ξ (k + 1) =
      delayedIterate g gamma a x0 ξ k - gamma • g (delayedIterate g gamma a x0 ξ (a k)) (ξ k) := by
  change (if k + 1 ≤ k then history g gamma a x0 ξ k (k + 1)
    else history g gamma a x0 ξ k k - gamma • g (history g gamma a x0 ξ k (a k)) (ξ k)) = _
  rw [ite_eq_right (Nat.not_succ_le_self k), history_stable g gamma a x0 ξ k (a k) hk]
  rfl

omit [MeasurableSpace Ω] [MeasurableSpace Ξ] in
theorem delayedIterate_zero (g : Point d → Ω → Point d) (gamma : ℝ) (a : ℕ → ℕ) (x0 : Point d)
    (ξ : ℕ → Ω) : delayedIterate g gamma a x0 ξ 0 = x0 := by
  rfl

omit [MeasurableSpace Ω] [MeasurableSpace Ξ] in
theorem history_congr (g : Point d → Ω → Point d) (gamma : ℝ) (a : ℕ → ℕ) (x0 : Point d)
    (ξ ξ' : ℕ → Ω) (k : ℕ) (h : ∀ j < k, ξ j = ξ' j) (j : ℕ) :
    history g gamma a x0 ξ k j = history g gamma a x0 ξ' k j := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    have ih' := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    change (if j ≤ k then history g gamma a x0 ξ k j
        else history g gamma a x0 ξ k k - gamma • g (history g gamma a x0 ξ k (a k)) (ξ k)) =
      (if j ≤ k then history g gamma a x0 ξ' k j
        else history g gamma a x0 ξ' k k - gamma • g (history g gamma a x0 ξ' k (a k)) (ξ' k))
    rw [ih' j, ih' k, ih' (a k), h k (Nat.lt_succ_self k)]

omit [MeasurableSpace Ω] [MeasurableSpace Ξ] in
theorem delayedIterate_congr (g : Point d → Ω → Point d) (gamma : ℝ) (a : ℕ → ℕ) (x0 : Point d)
    (ξ ξ' : ℕ → Ω) (k : ℕ) (h : ∀ j < k, ξ j = ξ' j) :
    delayedIterate g gamma a x0 ξ k = delayedIterate g gamma a x0 ξ' k := by
  exact history_congr g gamma a x0 ξ ξ' k h k

omit [MeasurableSpace Ξ] in
theorem history_measurable (g : Point d → Ω → Point d) (hg : Measurable (Function.uncurry g))
    (gamma : ℝ) (a : ℕ → ℕ) (x0 : Point d) (k j : ℕ) :
    Measurable (fun ξ : ℕ → Ω => history g gamma a x0 ξ k j) := by
  induction k generalizing j with
  | zero => exact measurable_const
  | succ k ih =>
    change Measurable (fun ξ : ℕ → Ω => if j ≤ k then history g gamma a x0 ξ k j
        else history g gamma a x0 ξ k k - gamma • g (history g gamma a x0 ξ k (a k)) (ξ k))
    by_cases hj : j ≤ k
    · simp only [ite_eq_left hj]
      exact ih j
    · simp only [ite_eq_right hj]
      exact (ih k).sub ((hg.comp ((ih (a k)).prodMk (measurable_pi_apply k))).const_smul gamma)

omit [MeasurableSpace Ξ] in
theorem delayedIterate_measurable (g : Point d → Ω → Point d) (hg : Measurable (Function.uncurry g))
    (gamma : ℝ) (a : ℕ → ℕ) (x0 : Point d) (k : ℕ) :
    Measurable (fun ξ : ℕ → Ω => delayedIterate g gamma a x0 ξ k) := by
  exact history_measurable g hg gamma a x0 k k

omit [MeasurableSpace Ω] [MeasurableSpace Ξ] in
theorem delayedIterate_telescope (g : Point d → Ω → Point d) (gamma : ℝ) (a : ℕ → ℕ) (x0 : Point d)
    (ξ : ℕ → Ω) (ha : ∀ k, a k ≤ k) (b m : ℕ) (hbm : b ≤ m) :
    delayedIterate g gamma a x0 ξ m = delayedIterate g gamma a x0 ξ b -
      gamma • ∑ j ∈ Finset.Ico b m, g (delayedIterate g gamma a x0 ξ (a j)) (ξ j) := by
  induction m, hbm using Nat.le_induction with
  | base => simp
  | succ m hbm ih =>
    rw [delayedIterate_succ g gamma a x0 ξ m (ha m), ih, Finset.sum_Ico_succ_top hbm, smul_add]
    exact sub_sub _ _ _

theorem step_integral (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ))
    (k : ℕ) (Φ : (ℕ → Ω) → Ω → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    (hk : ∀ s s' b, (∀ j < k, s j = s' j) → Φ s b = Φ s' b) :
    (Integrable (fun ω => Φ (fun j => ξ j ω) (ξ k ω)) (P : Measure Ξ) ↔
      (∀ᵐ ω ∂(P : Measure Ξ), Integrable (fun b => Φ (fun j => ξ j ω) b) (μ : Measure Ω)) ∧
        Integrable (fun ω => ∫ b, ‖Φ (fun j => ξ j ω) b‖ ∂(μ : Measure Ω)) (P : Measure Ξ)) ∧
    (Integrable (fun ω => Φ (fun j => ξ j ω) (ξ k ω)) (P : Measure Ξ) →
      (∫ ω, Φ (fun j => ξ j ω) (ξ k ω) ∂(P : Measure Ξ)) =
        ∫ ω, (∫ b, Φ (fun j => ξ j ω) b ∂(μ : Measure Ω)) ∂(P : Measure Ξ)) := by
  classical
  have hne : Nonempty Ξ := nonempty_of_isProbabilityMeasure (P : Measure Ξ)
  obtain ⟨ω0⟩ := hne
  let c : Ω := ξ 0 ω0
  let ext : (Fin k → Ω) → ℕ → Ω := fun a j => if h : j < k then a ⟨j, h⟩ else c
  have hext : Measurable ext := by
    refine Measurable.of_eval (fun j => ?_)
    by_cases h : j < k
    · simp only [ext, dite_eq_left h]
      exact measurable_pi_apply _
    · simp only [ext, dite_eq_right h]
      exact measurable_const
  let X : Ξ → Fin k → Ω := fun ω i => ξ i ω
  let Y : Ξ → Ω := ξ k
  have hXm : Measurable X := Measurable.of_eval (fun i => hiid.measurable i)
  have hYm : Measurable Y := hiid.measurable k
  let Ψ : (Fin k → Ω) × Ω → ℝ := fun z => Φ (ext z.1) z.2
  have hΨ : Measurable Ψ := hΦ.comp ((hext.comp measurable_fst).prodMk measurable_snd)
  have hagree (ω : Ξ) (b : Ω) : Φ (fun j => ξ j ω) b = Ψ (X ω, b) := by
    apply hk
    intro j hj
    simp only [ext, X, dite_eq_left hj]
  have hind : IndepFun X Y (P : Measure Ξ) := by
    have h := (hiid.prefix_tail_independent k).comp measurable_id (measurable_pi_apply 0)
    exact h
  have hlaw : (P : Measure Ξ).map (fun ω => (X ω, Y ω)) =
      ((P : Measure Ξ).map X).prod (μ : Measure Ω) := by
    rw [hind.map_prod_eq_prod_map_map hXm.aemeasurable hYm.aemeasurable, hiid.marginal k]
  have hXYm : Measurable (fun ω => (X ω, Y ω)) := hXm.prodMk hYm
  have hcomp : (fun ω => Φ (fun j => ξ j ω) (ξ k ω)) = Ψ ∘ (fun ω => (X ω, Y ω)) := by
    funext ω
    exact hagree ω (ξ k ω)
  have hiff : Integrable (fun ω => Φ (fun j => ξ j ω) (ξ k ω)) (P : Measure Ξ) ↔
      Integrable Ψ (((P : Measure Ξ).map X).prod (μ : Measure Ω)) := by
    rw [hcomp, ← hlaw]
    exact (integrable_map_measure hΨ.aestronglyMeasurable hXYm.aemeasurable).symm
  have hinner_m : StronglyMeasurable (fun a => ∫ b, Ψ (a, b) ∂(μ : Measure Ω)) :=
    hΨ.stronglyMeasurable.integral_prod_right'
  have hinner_norm_m : StronglyMeasurable (fun a => ∫ b, ‖Ψ (a, b)‖ ∂(μ : Measure Ω)) :=
    hΨ.norm.stronglyMeasurable.integral_prod_right'
  refine ⟨?_, ?_⟩
  · rw [hiff, integrable_prod_iff hΨ.aestronglyMeasurable]
    have h1 : (∀ᵐ a ∂((P : Measure Ξ).map X), Integrable (fun b => Ψ (a, b)) (μ : Measure Ω)) ↔
        ∀ᵐ ω ∂(P : Measure Ξ), Integrable (fun b => Φ (fun j => ξ j ω) b) (μ : Measure Ω) := by
      simp_rw [hagree]
      exact ae_map_iff hXm.aemeasurable (measurableSet_integrable hΨ.stronglyMeasurable)
    have h2 : Integrable (fun a => ∫ b, ‖Ψ (a, b)‖ ∂(μ : Measure Ω)) ((P : Measure Ξ).map X) ↔
        Integrable (fun ω => ∫ b, ‖Φ (fun j => ξ j ω) b‖ ∂(μ : Measure Ω)) (P : Measure Ξ) := by
      simp_rw [hagree]
      exact integrable_map_measure hinner_norm_m.aestronglyMeasurable hXm.aemeasurable
    rw [h1, h2]
  · intro hint
    have hΨi := hiff.mp hint
    rw [hcomp]
    change (∫ ω, Ψ (X ω, Y ω) ∂(P : Measure Ξ)) = _
    rw [← integral_map hXYm.aemeasurable (by rw [hlaw]; exact hΨ.aestronglyMeasurable), hlaw,
      integral_prod Ψ hΨi]
    simp_rw [hagree]
    exact integral_map hXm.aemeasurable hinner_m.aestronglyMeasurable

omit [MeasurableSpace Ξ] in
theorem oracle_moments (f : Point d → ℝ) (g : Point d → Ω → Point d) (μ : ProbabilityMeasure Ω)
    (sigma : ℝ)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g sigma) (y : Point d) :
    Integrable (fun b => ‖g y b‖ ^ 2) (μ : Measure Ω) ∧
      (∫ b, ‖g y b‖ ^ 2 ∂(μ : Measure Ω)) ≤ sigma ^ 2 + ‖gradient f y‖ ^ 2 := by
  have hdec (b : Ω) : ‖g y b‖ ^ 2 = ‖g y b - gradient f y‖ ^ 2 +
      (2 * (inner ℝ (gradient f y) (g y b)) - ‖gradient f y‖ ^ 2) := by
    rw [norm_sub_sq_real, real_inner_comm]
    ring
  have hi1 := ho.variance_integrable y
  have hi2 : Integrable (fun b => 2 * (inner ℝ (gradient f y) (g y b)) - ‖gradient f y‖ ^ 2) (μ : Measure Ω) :=
    ((Integrable.const_inner (gradient f y) (ho.integrable y)).const_mul 2).sub (integrable_const _)
  have hfun : (fun b => ‖g y b‖ ^ 2) = fun b => ‖g y b - gradient f y‖ ^ 2 +
      (2 * (inner ℝ (gradient f y) (g y b)) - ‖gradient f y‖ ^ 2) := funext hdec
  refine ⟨by rw [hfun]; exact hi1.add hi2, ?_⟩
  rw [hfun, integral_add hi1 hi2, integral_sub ((Integrable.const_inner (gradient f y)
    (ho.integrable y)).const_mul 2) (integrable_const _), integral_const_mul,
    integral_inner (ho.integrable y), ho.unbiased y, real_inner_self_eq_norm_sq]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have := ho.variance y
  linarith

theorem step_bound (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ))
    (k : ℕ) (Φ : (ℕ → Ω) → Ω → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    (hk : ∀ s s' b, (∀ j < k, s j = s' j) → Φ s b = Φ s' b)
    (hnn : ∀ s b, 0 ≤ Φ s b) (hint : ∀ s, Integrable (Φ s) (μ : Measure Ω))
    (B : Ξ → ℝ) (hB : Integrable B (P : Measure Ξ))
    (hle : ∀ ω, (∫ b, Φ (fun j => ξ j ω) b ∂(μ : Measure Ω)) ≤ B ω) :
    Integrable (fun ω => Φ (fun j => ξ j ω) (ξ k ω)) (P : Measure Ξ) ∧
      (∫ ω, Φ (fun j => ξ j ω) (ξ k ω) ∂(P : Measure Ξ)) ≤ ∫ ω, B ω ∂(P : Measure Ξ) := by
  obtain ⟨hiff, heq⟩ := step_integral μ P ξ hiid k Φ hΦ hk
  have hS : Measurable (fun ω j => ξ j ω) := Measurable.of_eval (fun j => hiid.measurable j)
  have hnorm (s : ℕ → Ω) : (∫ b, ‖Φ s b‖ ∂(μ : Measure Ω)) = ∫ b, Φ s b ∂(μ : Measure Ω) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun b => by
      simp only [Real.norm_eq_abs, abs_of_nonneg (hnn s b)])
  have hm : AEStronglyMeasurable (fun ω => ∫ b, Φ (fun j => ξ j ω) b ∂(μ : Measure Ω))
      (P : Measure Ξ) := by
    have h1 : StronglyMeasurable (fun s : ℕ → Ω => ∫ b, Φ s b ∂(μ : Measure Ω)) :=
      hΦ.stronglyMeasurable.integral_prod_right' (f := Function.uncurry Φ)
    exact (h1.comp_measurable hS).aestronglyMeasurable
  have hinner : Integrable (fun ω => ∫ b, Φ (fun j => ξ j ω) b ∂(μ : Measure Ω)) (P : Measure Ξ) := by
    apply hB.mono' hm
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun b => hnn _ b))]
      exact hle ω)
  have hI : Integrable (fun ω => Φ (fun j => ξ j ω) (ξ k ω)) (P : Measure Ξ) := by
    rw [hiff]
    refine ⟨Filter.Eventually.of_forall (fun ω => hint _), ?_⟩
    simp only [hnorm]
    exact hinner
  refine ⟨hI, ?_⟩
  rw [heq hI]
  exact integral_mono hinner hB hle

theorem iterate_moments (f : Point d → ℝ) (g : Point d → Ω → Point d) (μ : ProbabilityMeasure Ω)
    (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω) (L sigma gamma : ℝ) (x0 : Point d) (a : ℕ → ℕ)
    (hL : 0 < L) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g sigma)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ))
    (ha : ∀ k, a k ≤ k) (k : ℕ) :
    Measurable (fun ω => delayedIterate g gamma a x0 (fun i => ξ i ω) k) ∧
      Integrable (fun ω => ‖delayedIterate g gamma a x0 (fun i => ξ i ω) k‖ ^ 2) (P : Measure Ξ) ∧
      Integrable (fun ω => ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) k)‖ ^ 2)
        (P : Measure Ξ) ∧
      Integrable (fun ω => f (delayedIterate g gamma a x0 (fun i => ξ i ω) k)) (P : Measure Ξ) := by
  have hS : Measurable (fun ω j => ξ j ω) := Measurable.of_eval (fun j => hiid.measurable j)
  have hX (j : ℕ) : Measurable (fun ω => delayedIterate g gamma a x0 (fun i => ξ i ω) j) :=
    (delayedIterate_measurable g ho.measurable gamma a x0 j).comp hS
  have hsm := smooth_growth f L hg hlip
  have hgc : Continuous (gradient f) := (lipschitzWith_iff_norm_sub_le.mpr hlip :
    LipschitzWith ⟨L, hL.le⟩ (gradient f)).continuous
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).hasFDerivAt.continuousAt)
  have hsub (x y : Point d) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    have hn : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
    have hh := pow_le_pow_left₀ (norm_nonneg (x - y)) hn 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have hsq : ∀ m, Integrable (fun ω => ‖delayedIterate g gamma a x0 (fun i => ξ i ω) m‖ ^ 2)
      (P : Measure Ξ) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases m with _ | k
      · exact integrable_const (‖x0‖ ^ 2)
      · let D : (ℕ → Ω) → Point d := fun s => delayedIterate g gamma a x0 s (a k)
        have hD : Measurable D := delayedIterate_measurable g ho.measurable gamma a x0 (a k)
        let Φ : (ℕ → Ω) → Ω → ℝ := fun s b => ‖g (D s) b‖ ^ 2
        have hΦ : Measurable (Function.uncurry Φ) :=
          (ho.measurable.comp ((hD.comp measurable_fst).prodMk measurable_snd)).norm.pow_const 2
        have hk : ∀ s s' b, (∀ j < k, s j = s' j) → Φ s b = Φ s' b := by
          intro s s' b h
          change ‖g (delayedIterate g gamma a x0 s (a k)) b‖ ^ 2 =
            ‖g (delayedIterate g gamma a x0 s' (a k)) b‖ ^ 2
          rw [delayedIterate_congr g gamma a x0 s s' (a k)
            (fun j hj => h j (lt_of_lt_of_le hj (ha k)))]
        have hB : Integrable (fun ω => sigma ^ 2 + (2 * ‖gradient f 0‖ ^ 2 +
            2 * L ^ 2 * ‖delayedIterate g gamma a x0 (fun i => ξ i ω) (a k)‖ ^ 2)) (P : Measure Ξ) :=
          (integrable_const _).add ((integrable_const _).add
            ((ih (a k) (Nat.lt_succ_of_le (ha k))).const_mul _))
        have hle : ∀ ω, (∫ b, Φ (fun j => ξ j ω) b ∂(μ : Measure Ω)) ≤ sigma ^ 2 +
            (2 * ‖gradient f 0‖ ^ 2 +
              2 * L ^ 2 * ‖delayedIterate g gamma a x0 (fun i => ξ i ω) (a k)‖ ^ 2) := by
          intro ω
          have h1 := (oracle_moments f g μ sigma ho (D (fun j => ξ j ω))).2
          have h2 := hsm.2.2 (D (fun j => ξ j ω))
          change (∫ b, ‖g (D (fun j => ξ j ω)) b‖ ^ 2 ∂(μ : Measure Ω)) ≤ _
          change _ ≤ sigma ^ 2 + (2 * ‖gradient f 0‖ ^ 2 + 2 * L ^ 2 * ‖D (fun j => ξ j ω)‖ ^ 2)
          linarith
        obtain ⟨hGi, -⟩ := step_bound μ P ξ hiid k Φ hΦ hk (fun _ _ => sq_nonneg _)
          (fun s => (oracle_moments f g μ sigma ho (D s)).1) _ hB hle
        have hbound : Integrable (fun ω => 2 * ‖delayedIterate g gamma a x0 (fun i => ξ i ω) k‖ ^ 2 +
            2 * gamma ^ 2 * Φ (fun j => ξ j ω) (ξ k ω)) (P : Measure Ξ) :=
          ((ih k (Nat.lt_succ_self k)).const_mul 2).add (hGi.const_mul _)
        apply hbound.mono' ((hX (k + 1)).norm.pow_const 2).aestronglyMeasurable
        refine Filter.Eventually.of_forall (fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
          delayedIterate_succ g gamma a x0 (fun i => ξ i ω) k (ha k)]
        have h := hsub (delayedIterate g gamma a x0 (fun i => ξ i ω) k)
          (gamma • g (delayedIterate g gamma a x0 (fun i => ξ i ω) (a k)) (ξ k ω))
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
        change _ ≤ 2 * ‖delayedIterate g gamma a x0 (fun i => ξ i ω) k‖ ^ 2 +
          2 * gamma ^ 2 * ‖g (delayedIterate g gamma a x0 (fun i => ξ i ω) (a k)) (ξ k ω)‖ ^ 2
        linarith
  have hx2 := hsq k
  have hxnorm : Integrable (fun ω => ‖delayedIterate g gamma a x0 (fun i => ξ i ω) k‖) (P : Measure Ξ) :=
    (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
      ((memLp_two_iff_integrable_sq_norm (hX k).aestronglyMeasurable).mpr hx2)).norm
  refine ⟨hX k, hx2, ?_, ?_⟩
  · apply ((integrable_const (2 * ‖gradient f 0‖ ^ 2)).add
      (hx2.const_mul (2 * L ^ 2))).mono' ((hgc.measurable.comp (hX k)).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hsm.2.2 _)
  · apply (((integrable_const |f 0|).add (hxnorm.const_mul ‖gradient f 0‖)).add
      (hx2.const_mul (L / 2))).mono' (hfc.measurable.comp (hX k)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs]
      exact hsm.2.1 _)

omit [MeasurableSpace Ξ] in
theorem descent_lemma (f : Point d → ℝ) (g : Point d → Ω → Point d) (μ : ProbabilityMeasure Ω)
    (L sigma gamma : ℝ) (hL : 0 < L) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g sigma)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ 1 / (2 * L)) (x y : Point d) :
    Integrable (fun b => f (x - gamma • g y b)) (μ : Measure Ω) ∧
      (∫ b, f (x - gamma • g y b) ∂(μ : Measure Ω)) ≤ f x - gamma / 2 * ‖gradient f x‖ ^ 2 -
        gamma / 4 * ‖gradient f y‖ ^ 2 + gamma * L ^ 2 / 2 * ‖x - y‖ ^ 2 +
        gamma ^ 2 * L / 2 * sigma ^ 2 := by
  have hsm := smooth_growth f L hg hlip
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).hasFDerivAt.continuousAt)
  have hgm : Measurable (g y) := ho.measurable.of_uncurry_left
  have hG := ho.integrable y
  obtain ⟨hG2, hG2le⟩ := oracle_moments f g μ sigma ho y
  have hzm : Measurable (fun b => x - gamma • g y b) := measurable_const.sub (hgm.const_smul gamma)
  have hup (b : Ω) : f (x - gamma • g y b) ≤ f x - gamma * (inner ℝ (gradient f x) (g y b)) +
      L / 2 * gamma ^ 2 * ‖g y b‖ ^ 2 := by
    have h := hsm.1 x (x - gamma • g y b)
    have he : x - gamma • g y b - x = -(gamma • g y b) := sub_sub_cancel_left _ _
    rw [he, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs] at h
    linarith
  have hupi : Integrable (fun b => f x - gamma * (inner ℝ (gradient f x) (g y b)) +
      L / 2 * gamma ^ 2 * ‖g y b‖ ^ 2) (μ : Measure Ω) :=
    ((integrable_const _).sub ((Integrable.const_inner (gradient f x) hG).const_mul gamma)).add
      (hG2.const_mul _)
  have hint : Integrable (fun b => f (x - gamma • g y b)) (μ : Measure Ω) := by
    have hzn : Integrable (fun b => ‖x - gamma • g y b‖) (μ : Measure Ω) :=
      ((integrable_const x).sub (hG.smul gamma)).norm
    have hz2 : Integrable (fun b => 2 * ‖x‖ ^ 2 + 2 * gamma ^ 2 * ‖g y b‖ ^ 2) (μ : Measure Ω) :=
      (integrable_const _).add (hG2.const_mul _)
    apply (((integrable_const |f 0|).add (hzn.const_mul ‖gradient f 0‖)).add
      (hz2.const_mul (L / 2))).mono' (hfc.measurable.comp hzm).aestronglyMeasurable
    refine Filter.Eventually.of_forall (fun b => ?_)
    rw [Real.norm_eq_abs]
    have h1 := hsm.2.1 (x - gamma • g y b)
    have h2 : ‖x - gamma • g y b‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * gamma ^ 2 * ‖g y b‖ ^ 2 := by
      have hn : ‖x - gamma • g y b‖ ≤ ‖x‖ + ‖gamma • g y b‖ := norm_sub_le _ _
      have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
      rw [norm_smul, Real.norm_eq_abs] at hh
      have : |gamma| ^ 2 = gamma ^ 2 := sq_abs gamma
      nlinarith [sq_nonneg (‖x‖ - |gamma| * ‖g y b‖), abs_nonneg gamma, norm_nonneg (g y b)]
    have hL2 : 0 ≤ L / 2 := by positivity
    have := mul_le_mul_of_nonneg_left h2 hL2
    change |f (x - gamma • g y b)| ≤ |f 0| + ‖gradient f 0‖ * ‖x - gamma • g y b‖ +
      L / 2 * (2 * ‖x‖ ^ 2 + 2 * gamma ^ 2 * ‖g y b‖ ^ 2)
    linarith
  refine ⟨hint, ?_⟩
  have hmono := integral_mono hint hupi hup
  have hI1 : Integrable (fun b => gamma * (inner ℝ (gradient f x) (g y b))) (μ : Measure Ω) :=
    (Integrable.const_inner (gradient f x) hG).const_mul gamma
  have hI2 : Integrable (fun b => f x - gamma * (inner ℝ (gradient f x) (g y b))) (μ : Measure Ω) :=
    (integrable_const _).sub hI1
  have hI3 : Integrable (fun b => L / 2 * gamma ^ 2 * ‖g y b‖ ^ 2) (μ : Measure Ω) := hG2.const_mul _
  have hval : (∫ b, (f x - gamma * (inner ℝ (gradient f x) (g y b)) + L / 2 * gamma ^ 2 * ‖g y b‖ ^ 2)
      ∂(μ : Measure Ω)) = f x - gamma * (inner ℝ (gradient f x) (gradient f y)) +
        L / 2 * gamma ^ 2 * ∫ b, ‖g y b‖ ^ 2 ∂(μ : Measure Ω) := by
    rw [integral_add hI2 hI3, integral_sub (integrable_const _) hI1, integral_const_mul,
      integral_const_mul, integral_inner hG, ho.unbiased y]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [hval] at hmono
  have hip : (inner ℝ (gradient f x) (gradient f y)) = (‖gradient f x‖ ^ 2 + ‖gradient f y‖ ^ 2 -
      ‖gradient f x - gradient f y‖ ^ 2) / 2 := by
    rw [norm_sub_sq_real]
    ring
  have hl := hlip x y
  have hl2 : ‖gradient f x - gradient f y‖ ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hl 2
    rw [mul_pow] at this
    exact this
  have hLg : L * gamma ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * L)] at hgamma
    linarith
  have hA := mul_le_mul_of_nonneg_left hl2 hgamma0
  have hB : L / 2 * gamma ^ 2 * ‖gradient f y‖ ^ 2 ≤ gamma / 4 * ‖gradient f y‖ ^ 2 := by
    have : L / 2 * gamma ^ 2 = gamma / 2 * (L * gamma) := by ring
    rw [this]
    have hy := sq_nonneg ‖gradient f y‖
    nlinarith [mul_le_mul_of_nonneg_left hLg (mul_nonneg hgamma0 hy)]
  have hC := mul_le_mul_of_nonneg_left hG2le (by positivity : (0 : ℝ) ≤ L / 2 * gamma ^ 2)
  rw [hip] at hmono
  nlinarith

theorem diff_sq_integrable (f : Point d → ℝ) (g : Point d → Ω → Point d) (μ : ProbabilityMeasure Ω)
    (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω) (L sigma gamma : ℝ) (x0 : Point d) (a : ℕ → ℕ)
    (hL : 0 < L) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g sigma)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ))
    (ha : ∀ k, a k ≤ k) (i j : ℕ) :
    Integrable (fun ω => ‖delayedIterate g gamma a x0 (fun l => ξ l ω) i -
      delayedIterate g gamma a x0 (fun l => ξ l ω) j‖ ^ 2) (P : Measure Ξ) := by
  have hi := iterate_moments f g μ P ξ L sigma gamma x0 a hL hg hlip ho hiid ha i
  have hj := iterate_moments f g μ P ξ L sigma gamma x0 a hL hg hlip ho hiid ha j
  apply ((hi.2.1.const_mul 2).add (hj.2.1.const_mul 2)).mono'
    ((hi.1.sub hj.1).norm.pow_const 2).aestronglyMeasurable
  refine Filter.Eventually.of_forall (fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hn := norm_sub_le (delayedIterate g gamma a x0 (fun l => ξ l ω) i)
    (delayedIterate g gamma a x0 (fun l => ξ l ω) j)
  have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
  change ‖delayedIterate g gamma a x0 (fun l => ξ l ω) i -
      delayedIterate g gamma a x0 (fun l => ξ l ω) j‖ ^ 2 ≤
    2 * ‖delayedIterate g gamma a x0 (fun l => ξ l ω) i‖ ^ 2 +
    2 * ‖delayedIterate g gamma a x0 (fun l => ξ l ω) j‖ ^ 2
  nlinarith [sq_nonneg (‖delayedIterate g gamma a x0 (fun l => ξ l ω) i‖ -
    ‖delayedIterate g gamma a x0 (fun l => ξ l ω) j‖)]

theorem expected_descent (f : Point d → ℝ) (g : Point d → Ω → Point d) (μ : ProbabilityMeasure Ω)
    (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω) (L sigma gamma : ℝ) (x0 : Point d) (a : ℕ → ℕ)
    (hL : 0 < L) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g sigma)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ))
    (ha : ∀ k, a k ≤ k) (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ 1 / (2 * L)) (k : ℕ) :
    (∫ ω, f (delayedIterate g gamma a x0 (fun i => ξ i ω) (k + 1)) ∂(P : Measure Ξ)) ≤
      (∫ ω, f (delayedIterate g gamma a x0 (fun i => ξ i ω) k) ∂(P : Measure Ξ)) -
      gamma / 2 * (∫ ω, ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) k)‖ ^ 2
        ∂(P : Measure Ξ)) -
      gamma / 4 * (∫ ω, ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a k))‖ ^ 2
        ∂(P : Measure Ξ)) +
      gamma * L ^ 2 / 2 * (∫ ω, ‖delayedIterate g gamma a x0 (fun i => ξ i ω) k -
        delayedIterate g gamma a x0 (fun i => ξ i ω) (a k)‖ ^ 2 ∂(P : Measure Ξ)) +
      gamma ^ 2 * L / 2 * sigma ^ 2 := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).hasFDerivAt.continuousAt)
  have hS : Measurable (fun ω j => ξ j ω) := Measurable.of_eval (fun j => hiid.measurable j)
  let Dk : (ℕ → Ω) → Point d := fun s => delayedIterate g gamma a x0 s k
  let Da : (ℕ → Ω) → Point d := fun s => delayedIterate g gamma a x0 s (a k)
  have hDk : Measurable Dk := delayedIterate_measurable g ho.measurable gamma a x0 k
  have hDa : Measurable Da := delayedIterate_measurable g ho.measurable gamma a x0 (a k)
  let Φ : (ℕ → Ω) → Ω → ℝ := fun s b => f (Dk s - gamma • g (Da s) b)
  have hΦ : Measurable (Function.uncurry Φ) :=
    hfc.measurable.comp ((hDk.comp measurable_fst).sub
      ((ho.measurable.comp ((hDa.comp measurable_fst).prodMk measurable_snd)).const_smul gamma))
  have hk : ∀ s s' b, (∀ j < k, s j = s' j) → Φ s b = Φ s' b := by
    intro s s' b h
    change f (delayedIterate g gamma a x0 s k - gamma • g (delayedIterate g gamma a x0 s (a k)) b) =
      f (delayedIterate g gamma a x0 s' k - gamma • g (delayedIterate g gamma a x0 s' (a k)) b)
    rw [delayedIterate_congr g gamma a x0 s s' k h,
      delayedIterate_congr g gamma a x0 s s' (a k) (fun j hj => h j (lt_of_lt_of_le hj (ha k)))]
  have hfun : (fun ω => f (delayedIterate g gamma a x0 (fun i => ξ i ω) (k + 1))) =
      fun ω => Φ (fun j => ξ j ω) (ξ k ω) := by
    funext ω
    rw [delayedIterate_succ g gamma a x0 (fun i => ξ i ω) k (ha k)]
  have hm := iterate_moments f g μ P ξ L sigma gamma x0 a hL hg hlip ho hiid ha
  have hint : Integrable (fun ω => Φ (fun j => ξ j ω) (ξ k ω)) (P : Measure Ξ) := by
    rw [← hfun]
    exact (hm (k + 1)).2.2.2
  obtain ⟨hiff, heq⟩ := step_integral μ P ξ hiid k Φ hΦ hk
  have hinner : Integrable (fun ω => ∫ b, Φ (fun j => ξ j ω) b ∂(μ : Measure Ω)) (P : Measure Ξ) := by
    have h2 := ((hiff.mp hint).2)
    have h1 : StronglyMeasurable (fun s : ℕ → Ω => ∫ b, Φ s b ∂(μ : Measure Ω)) :=
      hΦ.stronglyMeasurable.integral_prod_right' (f := Function.uncurry Φ)
    exact h2.mono' (h1.comp_measurable hS).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => norm_integral_le_integral_norm _))
  have hd := diff_sq_integrable f g μ P ξ L sigma gamma x0 a hL hg hlip ho hiid ha k (a k)
  have hBi : Integrable (fun ω => f (delayedIterate g gamma a x0 (fun i => ξ i ω) k) -
      gamma / 2 * ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) k)‖ ^ 2 -
      gamma / 4 * ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a k))‖ ^ 2 +
      gamma * L ^ 2 / 2 * ‖delayedIterate g gamma a x0 (fun i => ξ i ω) k -
        delayedIterate g gamma a x0 (fun i => ξ i ω) (a k)‖ ^ 2 +
      gamma ^ 2 * L / 2 * sigma ^ 2) (P : Measure Ξ) :=
    ((((hm k).2.2.2.sub ((hm k).2.2.1.const_mul _)).sub ((hm (a k)).2.2.1.const_mul _)).add
      (hd.const_mul _)).add (integrable_const _)
  have hle : ∀ ω, (∫ b, Φ (fun j => ξ j ω) b ∂(μ : Measure Ω)) ≤
      f (delayedIterate g gamma a x0 (fun i => ξ i ω) k) -
      gamma / 2 * ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) k)‖ ^ 2 -
      gamma / 4 * ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a k))‖ ^ 2 +
      gamma * L ^ 2 / 2 * ‖delayedIterate g gamma a x0 (fun i => ξ i ω) k -
        delayedIterate g gamma a x0 (fun i => ξ i ω) (a k)‖ ^ 2 +
      gamma ^ 2 * L / 2 * sigma ^ 2 := fun ω =>
    (descent_lemma f g μ L sigma gamma hL hg hlip ho hgamma0 hgamma
      (Dk (fun j => ξ j ω)) (Da (fun j => ξ j ω))).2
  rw [hfun, heq hint]
  refine (integral_mono hinner hBi hle).trans (le_of_eq ?_)
  rw [integral_add _ (integrable_const _), integral_add _ (hd.const_mul _), integral_sub _
    ((hm (a k)).2.2.1.const_mul _), integral_sub (hm k).2.2.2 ((hm k).2.2.1.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  · exact (hm k).2.2.2.sub ((hm k).2.2.1.const_mul _)
  · exact ((hm k).2.2.2.sub ((hm k).2.2.1.const_mul _)).sub ((hm (a k)).2.2.1.const_mul _)
  · exact (((hm k).2.2.2.sub ((hm k).2.2.1.const_mul _)).sub ((hm (a k)).2.2.1.const_mul _)).add
      (hd.const_mul _)

theorem noise_sum (f : Point d → ℝ) (g : Point d → Ω → Point d) (μ : ProbabilityMeasure Ω)
    (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω) (L sigma gamma : ℝ) (x0 : Point d) (a : ℕ → ℕ)
    (hL : 0 < L) (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g sigma)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ))
    (ha : ∀ k, a k ≤ k) (b m : ℕ) (hbm : b ≤ m) :
    Integrable (fun ω => ‖∑ j ∈ Finset.Ico b m,
      (g (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j)) (ξ j ω) -
        gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j)))‖ ^ 2) (P : Measure Ξ) ∧
      (∫ ω, ‖∑ j ∈ Finset.Ico b m,
        (g (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j)) (ξ j ω) -
          gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j)))‖ ^ 2 ∂(P : Measure Ξ)) ≤
        ((m : ℝ) - b) * sigma ^ 2 := by
  have hgc : Continuous (gradient f) := (lipschitzWith_iff_norm_sub_le.mpr hlip :
    LipschitzWith ⟨L, hL.le⟩ (gradient f)).continuous
  have hD (j : ℕ) : Measurable (fun s : ℕ → Ω => delayedIterate g gamma a x0 s j) :=
    delayedIterate_measurable g ho.measurable gamma a x0 j
  induction m, hbm using Nat.le_induction with
  | base => simp
  | succ m hbm ih =>
    obtain ⟨ihi, ihle⟩ := ih
    let Da : (ℕ → Ω) → Point d := fun s => delayedIterate g gamma a x0 s (a m)
    let Ssum : (ℕ → Ω) → Point d := fun s => ∑ j ∈ Finset.Ico b m,
      (g (delayedIterate g gamma a x0 s (a j)) (s j) - gradient f (delayedIterate g gamma a x0 s (a j)))
    have hSm : Measurable Ssum := Finset.measurable_sum _ (fun j _ =>
      (ho.measurable.comp ((hD (a j)).prodMk (measurable_pi_apply j))).sub (hgc.measurable.comp (hD (a j))))
    have hSk : ∀ s s' : ℕ → Ω, (∀ j < m, s j = s' j) → Ssum s = Ssum s' := by
      intro s s' h
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjm : j < m := (Finset.mem_Ico.mp hj).2
      rw [delayedIterate_congr g gamma a x0 s s' (a j)
        (fun i hi => h i (lt_of_lt_of_le hi ((ha j).trans hjm.le))), h j hjm]
    have hDak : ∀ s s' : ℕ → Ω, (∀ j < m, s j = s' j) → Da s = Da s' := fun s s' h =>
      delayedIterate_congr g gamma a x0 s s' (a m) (fun i hi => h i (lt_of_lt_of_le hi (ha m)))
    let Φ1 : (ℕ → Ω) → Ω → ℝ := fun s c => ‖g (Da s) c - gradient f (Da s)‖ ^ 2
    have hΦ1 : Measurable (Function.uncurry Φ1) :=
      ((ho.measurable.comp (((hD (a m)).comp measurable_fst).prodMk measurable_snd)).sub
        (hgc.measurable.comp ((hD (a m)).comp measurable_fst))).norm.pow_const 2
    obtain ⟨hNi, hNle⟩ := step_bound μ P ξ hiid m Φ1 hΦ1
      (fun s s' c h => by change ‖g (Da s) c - gradient f (Da s)‖ ^ 2 = ‖g (Da s') c - gradient f (Da s')‖ ^ 2
                          rw [hDak s s' h])
      (fun _ _ => sq_nonneg _) (fun s => ho.variance_integrable (Da s)) (fun _ => sigma ^ 2)
      (integrable_const _) (fun ω => ho.variance _)
    let Φ2 : (ℕ → Ω) → Ω → ℝ := fun s c => (inner ℝ (Ssum s) (g (Da s) c - gradient f (Da s)))
    have hΦ2 : Measurable (Function.uncurry Φ2) :=
      Measurable.inner (hSm.comp measurable_fst)
        ((ho.measurable.comp (((hD (a m)).comp measurable_fst).prodMk
        measurable_snd)).sub (hgc.measurable.comp ((hD (a m)).comp measurable_fst)))
    have hk2 : ∀ s s' c, (∀ j < m, s j = s' j) → Φ2 s c = Φ2 s' c := by
      intro s s' c h
      change (inner ℝ (Ssum s) (g (Da s) c - gradient f (Da s))) = (inner ℝ (Ssum s') (g (Da s') c - gradient f (Da s')))
      rw [hSk s s' h, hDak s s' h]
    have hS : Measurable (fun ω j => ξ j ω) := Measurable.of_eval (fun j => hiid.measurable j)
    have hI2 : Integrable (fun ω => Φ2 (fun j => ξ j ω) (ξ m ω)) (P : Measure Ξ) := by
      apply (ihi.add hNi).mono' (hΦ2.comp (hS.prodMk (hiid.measurable m))).aestronglyMeasurable
      refine Filter.Eventually.of_forall (fun ω => ?_)
      have h1 := abs_real_inner_le_norm (Ssum (fun j => ξ j ω))
        (g (Da (fun j => ξ j ω)) (ξ m ω) - gradient f (Da (fun j => ξ j ω)))
      rw [Real.norm_eq_abs]
      change |(inner ℝ (Ssum (fun j => ξ j ω)) (g (Da (fun j => ξ j ω)) (ξ m ω) - gradient f (Da (fun j => ξ j ω))))| ≤
        ‖Ssum (fun j => ξ j ω)‖ ^ 2 + ‖g (Da (fun j => ξ j ω)) (ξ m ω) - gradient f (Da (fun j => ξ j ω))‖ ^ 2
      nlinarith [sq_nonneg (‖Ssum (fun j => ξ j ω)‖ -
        ‖g (Da (fun j => ξ j ω)) (ξ m ω) - gradient f (Da (fun j => ξ j ω))‖)]
    have hE2 : (∫ ω, Φ2 (fun j => ξ j ω) (ξ m ω) ∂(P : Measure Ξ)) = 0 := by
      rw [(step_integral μ P ξ hiid m Φ2 hΦ2 hk2).2 hI2]
      have hz (s : ℕ → Ω) : (∫ c, Φ2 s c ∂(μ : Measure Ω)) = 0 := by
        change (∫ c, (inner ℝ (Ssum s) (g (Da s) c - gradient f (Da s))) ∂(μ : Measure Ω)) = 0
        have hgi : Integrable (fun c => g (Da s) c - gradient f (Da s)) (μ : Measure Ω) :=
          (ho.integrable (Da s)).sub (integrable_const _)
        rw [integral_inner hgi, integral_sub (ho.integrable (Da s)) (integrable_const _), ho.unbiased]
        simp
      simp only [hz, integral_zero]
    have hsplit (ω : Ξ) : ‖∑ j ∈ Finset.Ico b (m + 1),
        (g (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j)) (ξ j ω) -
          gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j)))‖ ^ 2 =
        ‖Ssum (fun j => ξ j ω)‖ ^ 2 + 2 * Φ2 (fun j => ξ j ω) (ξ m ω) + Φ1 (fun j => ξ j ω) (ξ m ω) := by
      rw [Finset.sum_Ico_succ_top hbm, norm_add_sq_real]
    have hfun : (fun ω => ‖∑ j ∈ Finset.Ico b (m + 1),
        (g (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j)) (ξ j ω) -
          gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j)))‖ ^ 2) =
        fun ω => ‖Ssum (fun j => ξ j ω)‖ ^ 2 + 2 * Φ2 (fun j => ξ j ω) (ξ m ω) +
          Φ1 (fun j => ξ j ω) (ξ m ω) := funext hsplit
    have hA : Integrable (fun ω => ‖Ssum (fun j => ξ j ω)‖ ^ 2 + 2 * Φ2 (fun j => ξ j ω) (ξ m ω))
        (P : Measure Ξ) := ihi.add (hI2.const_mul 2)
    rw [hfun]
    refine ⟨hA.add hNi, ?_⟩
    rw [integral_add hA hNi, integral_add ihi (hI2.const_mul 2), integral_const_mul, hE2]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hNle
    have : ((↑(m + 1) : ℝ) - b) * sigma ^ 2 = ((m : ℝ) - b) * sigma ^ 2 + sigma ^ 2 := by
      push_cast
      ring
    rw [this]
    change (∫ ω, ‖Ssum (fun j => ξ j ω)‖ ^ 2 ∂(P : Measure Ξ)) + 2 * 0 +
      (∫ ω, Φ1 (fun j => ξ j ω) (ξ m ω) ∂(P : Measure Ξ)) ≤ _
    linarith

omit [MeasurableSpace Ω] [MeasurableSpace Ξ] in
theorem window_count (a : ℕ → ℕ) (R K : ℕ) (hR : ∀ k, k < a k + R)
    (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j) :
    ∑ k ∈ Finset.range (K + 1), ∑ j ∈ Finset.Ico (a k) k, c j ≤
      (R : ℝ) * ∑ j ∈ Finset.range (K + 1), c j := by
  classical
  have h1 : ∀ k ∈ Finset.range (K + 1), ∑ j ∈ Finset.Ico (a k) k, c j =
      ∑ j ∈ Finset.range (K + 1), if j ∈ Finset.Ico (a k) k then c j else 0 := by
    intro k hk
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr]
    intro j hj
    have := Finset.mem_range.mp hk
    have := (Finset.mem_Ico.mp hj).2
    exact Finset.mem_range.mpr (by omega)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsub : (Finset.range (K + 1)).filter (fun k => j ∈ Finset.Ico (a k) k) ⊆ Finset.Ioo j (j + R) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Ico] at hk
    have := hR k
    exact Finset.mem_Ioo.mpr ⟨hk.2.2, by omega⟩
  have hc' := Finset.card_le_card hsub
  rw [Nat.card_Ioo] at hc'
  have : (((Finset.range (K + 1)).filter (fun k => j ∈ Finset.Ico (a k) k)).card : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hc'.trans (by omega)
  nlinarith [hc j]

theorem residual_step (f : Point d → ℝ) (g : Point d → Ω → Point d) (μ : ProbabilityMeasure Ω)
    (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω) (L sigma gamma : ℝ) (x0 : Point d) (a : ℕ → ℕ)
    (hL : 0 < L) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g sigma)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ))
    (ha : ∀ k, a k ≤ k) (k : ℕ) :
    (∫ ω, ‖delayedIterate g gamma a x0 (fun i => ξ i ω) k -
        delayedIterate g gamma a x0 (fun i => ξ i ω) (a k)‖ ^ 2 ∂(P : Measure Ξ)) ≤
      2 * ((k : ℝ) - a k) * gamma ^ 2 * ∑ j ∈ Finset.Ico (a k) k,
        (∫ ω, ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j))‖ ^ 2 ∂(P : Measure Ξ)) +
      2 * ((k : ℝ) - a k) * gamma ^ 2 * sigma ^ 2 := by
  have hm := iterate_moments f g μ P ξ L sigma gamma x0 a hL hg hlip ho hiid ha
  obtain ⟨hNi, hNle⟩ := noise_sum f g μ P ξ L sigma gamma x0 a hL hlip ho hiid ha (a k) k (ha k)
  have hcard : ((Finset.Ico (a k) k).card : ℝ) = (k : ℝ) - a k := by
    rw [Nat.card_Ico, Nat.cast_sub (ha k)]
  have hpt (ω : Ξ) : ‖delayedIterate g gamma a x0 (fun i => ξ i ω) k -
      delayedIterate g gamma a x0 (fun i => ξ i ω) (a k)‖ ^ 2 ≤
      2 * ((k : ℝ) - a k) * gamma ^ 2 * ∑ j ∈ Finset.Ico (a k) k,
        ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j))‖ ^ 2 +
      2 * gamma ^ 2 * ‖∑ j ∈ Finset.Ico (a k) k,
        (g (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j)) (ξ j ω) -
          gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j)))‖ ^ 2 := by
    set D : ℕ → Point d := fun j => gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j))
    set N : ℕ → Point d := fun j => g (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j)) (ξ j ω) -
      gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j))
    have htel := delayedIterate_telescope g gamma a x0 (fun i => ξ i ω) ha (a k) k (ha k)
    have hG : ∑ j ∈ Finset.Ico (a k) k, g (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j)) (ξ j ω) =
        ∑ j ∈ Finset.Ico (a k) k, D j + ∑ j ∈ Finset.Ico (a k) k, N j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [D, N]
      rw [add_sub_cancel]
    have hdiff : delayedIterate g gamma a x0 (fun i => ξ i ω) k -
        delayedIterate g gamma a x0 (fun i => ξ i ω) (a k) =
        -(gamma • (∑ j ∈ Finset.Ico (a k) k, D j + ∑ j ∈ Finset.Ico (a k) k, N j)) := by
      rw [htel, ← hG]
      exact sub_sub_cancel_left _ _
    rw [hdiff, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have h2 : ‖∑ j ∈ Finset.Ico (a k) k, D j + ∑ j ∈ Finset.Ico (a k) k, N j‖ ^ 2 ≤
        2 * ‖∑ j ∈ Finset.Ico (a k) k, D j‖ ^ 2 + 2 * ‖∑ j ∈ Finset.Ico (a k) k, N j‖ ^ 2 := by
      have hn := norm_add_le (∑ j ∈ Finset.Ico (a k) k, D j) (∑ j ∈ Finset.Ico (a k) k, N j)
      have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
      nlinarith [sq_nonneg (‖∑ j ∈ Finset.Ico (a k) k, D j‖ - ‖∑ j ∈ Finset.Ico (a k) k, N j‖)]
    have h3 : ‖∑ j ∈ Finset.Ico (a k) k, D j‖ ^ 2 ≤
        ((k : ℝ) - a k) * ∑ j ∈ Finset.Ico (a k) k, ‖D j‖ ^ 2 := by
      have hn := norm_sum_le (Finset.Ico (a k) k) D
      have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
      have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ico (a k) k) (fun j => ‖D j‖) (fun _ => (1 : ℝ))
      simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at hc
      rw [hcard] at hc
      nlinarith
    have hg2 := sq_nonneg gamma
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * gamma ^ 2),
      mul_le_mul_of_nonneg_left h2 hg2]
  have hsumi : Integrable (fun ω => ∑ j ∈ Finset.Ico (a k) k,
      ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j))‖ ^ 2) (P : Measure Ξ) :=
    integrable_finsetSum _ (fun j _ => (hm (a j)).2.2.1)
  have hRi : Integrable (fun ω => 2 * ((k : ℝ) - a k) * gamma ^ 2 * ∑ j ∈ Finset.Ico (a k) k,
        ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j))‖ ^ 2 +
      2 * gamma ^ 2 * ‖∑ j ∈ Finset.Ico (a k) k,
        (g (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j)) (ξ j ω) -
          gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j)))‖ ^ 2) (P : Measure Ξ) :=
    (hsumi.const_mul (2 * ((k : ℝ) - a k) * gamma ^ 2)).add (hNi.const_mul (2 * gamma ^ 2))
  refine (integral_mono (diff_sq_integrable f g μ P ξ L sigma gamma x0 a hL hg hlip ho hiid ha k (a k))
    hRi hpt).trans ?_
  rw [integral_add (hsumi.const_mul _) (hNi.const_mul _), integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun j _ => (hm (a j)).2.2.1)]
  have hkk : (0 : ℝ) ≤ (k : ℝ) - a k := by
    have : ((a k : ℕ) : ℝ) ≤ k := by exact_mod_cast ha k
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hNle (by positivity : (0 : ℝ) ≤ 2 * gamma ^ 2)]

theorem residual_lemma (f : Point d → ℝ) (g : Point d → Ω → Point d) (μ : ProbabilityMeasure Ω)
    (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω) (L sigma gamma : ℝ) (x0 : Point d) (a : ℕ → ℕ)
    (R : ℕ) (hL : 0 < L) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g sigma)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ))
    (ha : ∀ k, a k ≤ k) (hR : ∀ k, k < a k + R) (hgamma0 : 0 ≤ gamma)
    (hgamma : gamma ≤ 1 / (2 * R * L)) (K : ℕ) :
    1 / ((K : ℝ) + 1) * ∑ k ∈ Finset.range (K + 1),
        (∫ ω, ‖delayedIterate g gamma a x0 (fun i => ξ i ω) k -
          delayedIterate g gamma a x0 (fun i => ξ i ω) (a k)‖ ^ 2 ∂(P : Measure Ξ)) ≤
      1 / (2 * L ^ 2 * ((K : ℝ) + 1)) * ∑ k ∈ Finset.range (K + 1),
        (∫ ω, ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a k))‖ ^ 2 ∂(P : Measure Ξ)) +
      gamma / L * sigma ^ 2 := by
  set c : ℕ → ℝ := fun j =>
    ∫ ω, ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a j))‖ ^ 2 ∂(P : Measure Ξ)
  have hc : ∀ j, 0 ≤ c j := fun j => integral_nonneg (fun _ => sq_nonneg _)
  have hR1 : 1 ≤ R := by
    have := hR 0
    have := ha 0
    omega
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR1
  have hRL : 2 * R * L * gamma ≤ 1 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * R * L)] at hgamma
    linarith
  have hδ (k : ℕ) : (k : ℝ) - a k ≤ R := by
    have := hR k
    have : (k : ℝ) < (a k : ℝ) + R := by exact_mod_cast this
    linarith
  have hδ0 (k : ℕ) : 0 ≤ (k : ℝ) - a k := by
    have : ((a k : ℕ) : ℝ) ≤ k := by exact_mod_cast ha k
    linarith
  have hstep (k : ℕ) : (∫ ω, ‖delayedIterate g gamma a x0 (fun i => ξ i ω) k -
        delayedIterate g gamma a x0 (fun i => ξ i ω) (a k)‖ ^ 2 ∂(P : Measure Ξ)) ≤
      2 * R * gamma ^ 2 * ∑ j ∈ Finset.Ico (a k) k, c j + 2 * R * gamma ^ 2 * sigma ^ 2 := by
    have h := residual_step f g μ P ξ L sigma gamma x0 a hL hg hlip ho hiid ha k
    have hs : 0 ≤ ∑ j ∈ Finset.Ico (a k) k, c j := Finset.sum_nonneg (fun j _ => hc j)
    have hg2 := sq_nonneg gamma
    have hs2 := sq_nonneg sigma
    nlinarith [mul_le_mul_of_nonneg_right (hδ k) (mul_nonneg hg2 hs),
      mul_le_mul_of_nonneg_right (hδ k) (mul_nonneg hg2 hs2)]
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (K + 1)) => hstep k)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hw := window_count a R K hR c hc
  have hcs : 0 ≤ ∑ j ∈ Finset.range (K + 1), c j := Finset.sum_nonneg (fun j _ => hc j)
  have hA : 2 * R * gamma ^ 2 * ∑ k ∈ Finset.range (K + 1), ∑ j ∈ Finset.Ico (a k) k, c j ≤
      1 / (2 * L ^ 2) * ∑ j ∈ Finset.range (K + 1), c j := by
    have h1 := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ 2 * R * gamma ^ 2)
    have h2 : 2 * R * gamma ^ 2 * R ≤ 1 / (2 * L ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 2 * R * L * gamma) hRL]
    nlinarith [mul_le_mul_of_nonneg_right h2 hcs]
  have hB : 2 * R * gamma ^ 2 * sigma ^ 2 ≤ gamma / L * sigma ^ 2 := by
    have h1 : 2 * R * gamma ^ 2 ≤ gamma / L := by
      rw [le_div_iff₀ hL]
      nlinarith
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have htot : ∑ k ∈ Finset.range (K + 1), (∫ ω, ‖delayedIterate g gamma a x0 (fun i => ξ i ω) k -
        delayedIterate g gamma a x0 (fun i => ξ i ω) (a k)‖ ^ 2 ∂(P : Measure Ξ)) ≤
      1 / (2 * L ^ 2) * ∑ j ∈ Finset.range (K + 1), c j + ((K : ℝ) + 1) * (gamma / L * sigma ^ 2) := by
    push_cast at hsum
    nlinarith
  calc _ ≤ 1 / ((K : ℝ) + 1) * (1 / (2 * L ^ 2) * ∑ j ∈ Finset.range (K + 1), c j +
        ((K : ℝ) + 1) * (gamma / L * sigma ^ 2)) :=
        mul_le_mul_of_nonneg_left htot (by positivity)
    _ = _ := by
        field_simp

theorem iteration_bound (f : Point d → ℝ) (g : Point d → Ω → Point d) (μ : ProbabilityMeasure Ω)
    (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω) (L sigma gamma lower : ℝ) (x0 : Point d)
    (a : ℕ → ℕ) (R : ℕ) (hL : 0 < L) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hlower : ∀ x, lower ≤ f x)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g sigma)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ))
    (ha : ∀ k, a k ≤ k) (hR : ∀ k, k < a k + R) (hgamma0 : 0 < gamma)
    (hgamma : gamma ≤ 1 / (2 * R * L)) (K : ℕ) :
    1 / ((K : ℝ) + 1) * ∑ k ∈ Finset.range (K + 1),
        (∫ ω, ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) k)‖ ^ 2 ∂(P : Measure Ξ)) ≤
      2 * (f x0 - lower) / (gamma * ((K : ℝ) + 1)) + 2 * gamma * L * sigma ^ 2 := by
  set A : ℕ → ℝ := fun k =>
    ∫ ω, ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) k)‖ ^ 2 ∂(P : Measure Ξ)
  set B : ℕ → ℝ := fun k =>
    ∫ ω, ‖gradient f (delayedIterate g gamma a x0 (fun i => ξ i ω) (a k))‖ ^ 2 ∂(P : Measure Ξ)
  set C : ℕ → ℝ := fun k => ∫ ω, ‖delayedIterate g gamma a x0 (fun i => ξ i ω) k -
    delayedIterate g gamma a x0 (fun i => ξ i ω) (a k)‖ ^ 2 ∂(P : Measure Ξ)
  set F : ℕ → ℝ := fun k => ∫ ω, f (delayedIterate g gamma a x0 (fun i => ξ i ω) k) ∂(P : Measure Ξ)
  have hR1 : 1 ≤ R := by
    have := hR 0
    have := ha 0
    omega
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hgamma2 : gamma ≤ 1 / (2 * L) := by
    refine hgamma.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hdesc (k : ℕ) : F (k + 1) ≤ F k - gamma / 2 * A k - gamma / 4 * B k + gamma * L ^ 2 / 2 * C k +
      gamma ^ 2 * L / 2 * sigma ^ 2 :=
    expected_descent f g μ P ξ L sigma gamma x0 a hL hg hlip ho hiid ha hgamma0.le hgamma2 k
  have htel : ∀ N, F (N + 1) ≤ F 0 - ∑ k ∈ Finset.range (N + 1),
      (gamma / 2 * A k + gamma / 4 * B k - gamma * L ^ 2 / 2 * C k - gamma ^ 2 * L / 2 * sigma ^ 2) := by
    intro N
    induction N with
    | zero =>
      simp only [zero_add, Finset.range_one, Finset.sum_singleton]
      linarith [hdesc 0]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [hdesc (N + 1)]
  have hF0 : F 0 = f x0 := by
    change (∫ ω, f x0 ∂(P : Measure Ξ)) = f x0
    simp
  have hFK : lower ≤ F (K + 1) := by
    have hm := (iterate_moments f g μ P ξ L sigma gamma x0 a hL hg hlip ho hiid ha (K + 1)).2.2.2
    have := integral_mono (integrable_const lower) hm (fun ω => hlower _)
    simpa using this
  have hres := residual_lemma f g μ P ξ L sigma gamma x0 a R hL hg hlip ho hiid ha hR hgamma0.le
    hgamma K
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hCsum : ∑ k ∈ Finset.range (K + 1), C k ≤
      1 / (2 * L ^ 2) * ∑ k ∈ Finset.range (K + 1), B k + ((K : ℝ) + 1) * (gamma / L * sigma ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hres hK.le
    have e1 : ((K : ℝ) + 1) * (1 / ((K : ℝ) + 1) * ∑ k ∈ Finset.range (K + 1), C k) =
        ∑ k ∈ Finset.range (K + 1), C k := by field_simp
    have e2 : ((K : ℝ) + 1) * (1 / (2 * L ^ 2 * ((K : ℝ) + 1)) * ∑ k ∈ Finset.range (K + 1), B k +
        gamma / L * sigma ^ 2) = 1 / (2 * L ^ 2) * ∑ k ∈ Finset.range (K + 1), B k +
        ((K : ℝ) + 1) * (gamma / L * sigma ^ 2) := by field_simp
    rw [e1, e2] at h
    exact h
  have ht := htel K
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hF0] at ht
  push_cast at ht
  have hmain : gamma / 2 * ∑ k ∈ Finset.range (K + 1), A k ≤
      f x0 - lower + ((K : ℝ) + 1) * (gamma ^ 2 * L * sigma ^ 2) := by
    have hC2 := mul_le_mul_of_nonneg_left hCsum (by positivity : (0 : ℝ) ≤ gamma * L ^ 2 / 2)
    have e : gamma * L ^ 2 / 2 * (1 / (2 * L ^ 2) * ∑ k ∈ Finset.range (K + 1), B k +
        ((K : ℝ) + 1) * (gamma / L * sigma ^ 2)) = gamma / 4 * ∑ k ∈ Finset.range (K + 1), B k +
        ((K : ℝ) + 1) * (gamma ^ 2 * L * sigma ^ 2) / 2 := by
      field_simp
      ring
    rw [e] at hC2
    nlinarith
  calc 1 / ((K : ℝ) + 1) * ∑ k ∈ Finset.range (K + 1), A k =
        (gamma / 2 * ∑ k ∈ Finset.range (K + 1), A k) * (2 / (gamma * ((K : ℝ) + 1))) := by
          field_simp
    _ ≤ (f x0 - lower + ((K : ℝ) + 1) * (gamma ^ 2 * L * sigma ^ 2)) *
        (2 / (gamma * ((K : ℝ) + 1))) := mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = _ := by
          field_simp

theorem iteration_accuracy (f : Point d → ℝ) (g : Point d → Ω → Point d) (μ : ProbabilityMeasure Ω)
    (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω) (L sigma eps lower : ℝ) (x0 : Point d)
    (a : ℕ → ℕ) (R K : ℕ) (hL : 0 < L) (hsigma : 0 ≤ sigma) (heps : 0 < eps)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hlower : ∀ x, lower ≤ f x)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g sigma)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ))
    (ha : ∀ k, a k ≤ k) (hR : ∀ k, k < a k + R)
    (hK : 8 * R * L * (f x0 - lower) / eps + 16 * sigma ^ 2 * L * (f x0 - lower) / eps ^ 2 ≤ K) :
    1 / ((K : ℝ) + 1) * ∑ k ∈ Finset.range (K + 1),
        (∫ ω, ‖gradient f (delayedIterate g (stepSize L sigma eps R) a x0 (fun i => ξ i ω) k)‖ ^ 2
          ∂(P : Measure Ξ)) ≤ eps := by
  have hR1 : 1 ≤ R := by
    have := hR 0
    have := ha 0
    omega
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR1
  set Δ := f x0 - lower with hΔ
  have hΔ0 : 0 ≤ Δ := by linarith [hlower x0]
  set gamma := stepSize L sigma eps R with hgdef
  have hsd : stepSize L sigma eps R = if sigma = 0 then 1 / (2 * R * L)
      else min (1 / (2 * R * L)) (eps / (4 * L * sigma ^ 2)) := rfl
  have hA : 0 < 1 / (2 * R * L) := by positivity
  have hgpos : 0 < gamma := by
    rw [hgdef, hsd]
    split_ifs with h
    · exact hA
    · have : 0 < sigma := lt_of_le_of_ne hsigma (Ne.symm h)
      exact lt_min hA (by positivity)
  have hgle : gamma ≤ 1 / (2 * R * L) := by
    rw [hgdef, hsd]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hb := iteration_bound f g μ P ξ L sigma gamma lower x0 a R hL hg hlip hlower ho hiid ha hR hgpos
    hgle K
  refine hb.trans ?_
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hT1 : 0 ≤ 16 * sigma ^ 2 * L * Δ / eps ^ 2 := by positivity
  have hT2 : 0 ≤ 8 * R * L * Δ / eps := by positivity
  have hnoise : 2 * gamma * L * sigma ^ 2 ≤ eps / 2 := by
    rw [hgdef, hsd]
    split_ifs with h
    · rw [h]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      linarith
    · have hs : 0 < sigma := lt_of_le_of_ne hsigma (Ne.symm h)
      have h1 : min (1 / (2 * R * L)) (eps / (4 * L * sigma ^ 2)) ≤ eps / (4 * L * sigma ^ 2) :=
        min_le_right _ _
      have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 * L * sigma ^ 2)
      have h3 : eps / (4 * L * sigma ^ 2) * (2 * L * sigma ^ 2) = eps / 2 := by
        field_simp
        ring
      nlinarith
  have hgap : 2 * Δ / (gamma * ((K : ℝ) + 1)) ≤ eps / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hcaseA : 4 * Δ ≤ eps * (1 / (2 * R * L)) * ((K : ℝ) + 1) := by
      have h1 : 8 * R * L * Δ / eps ≤ (K : ℝ) + 1 := by linarith
      rw [div_le_iff₀ heps] at h1
      have e : eps * (1 / (2 * R * L)) * ((K : ℝ) + 1) = ((K : ℝ) + 1) * eps / (2 * R * L) := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      nlinarith
    rw [hgdef, hsd]
    split_ifs with h
    · nlinarith
    · have hs : 0 < sigma := lt_of_le_of_ne hsigma (Ne.symm h)
      have hcaseB : 4 * Δ ≤ eps * (eps / (4 * L * sigma ^ 2)) * ((K : ℝ) + 1) := by
        have h1 : 16 * sigma ^ 2 * L * Δ / eps ^ 2 ≤ (K : ℝ) + 1 := by linarith
        rw [div_le_iff₀ (by positivity)] at h1
        have e : eps * (eps / (4 * L * sigma ^ 2)) * ((K : ℝ) + 1) =
            ((K : ℝ) + 1) * eps ^ 2 / (4 * L * sigma ^ 2) := by
          field_simp
        rw [e, le_div_iff₀ (by positivity)]
        nlinarith
      rcases min_choice (1 / (2 * R * L)) (eps / (4 * L * sigma ^ 2)) with hm | hm
      · rw [hm]
        nlinarith
      · rw [hm]
        nlinarith
  linarith

omit [MeasurableSpace Ω] [MeasurableSpace Ξ] in
theorem initial_stationary (f : Point d → ℝ) (L lower : ℝ) (x0 : Point d) (hL : 0 < L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hlower : ∀ x, lower ≤ f x) :
    ‖gradient f x0‖ ^ 2 ≤ 2 * L * (f x0 - lower) := by
  have h := (smooth_growth f L hg hlip).1 x0 (x0 - (1 / L) • gradient f x0)
  have he : x0 - (1 / L) • gradient f x0 - x0 = -((1 / L) • gradient f x0) := sub_sub_cancel_left _ _
  rw [he, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / L), mul_pow] at h
  have hlo := hlower (x0 - (1 / L) • gradient f x0)
  have e : L / 2 * ((1 / L) ^ 2 * ‖gradient f x0‖ ^ 2) = 1 / L * ‖gradient f x0‖ ^ 2 / 2 := by
    field_simp
  rw [e] at h
  have h2 : 1 / L * ‖gradient f x0‖ ^ 2 / 2 ≤ f x0 - lower := by linarith
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), one_div_mul_eq_div, div_le_iff₀ hL] at h2
  linarith

end OracleTemplate.RingmasterAsgd
