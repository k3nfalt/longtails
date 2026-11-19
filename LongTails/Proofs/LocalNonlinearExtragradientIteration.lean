import LongTails.Proofs.LocalNonlinearExtragradientMoments
import LongTails.Proofs.LocalNonlinearExtragradientSampling
import Mathlib.Probability.HasLaw
import LongTails.Proofs.AuxiliaryInner

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.LocalNonlinearExtragradientIteration

variable {E Ω Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] [MeasurableSpace Ξ]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma actual_fresh_second_moment (P : Measure Ξ) (Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p : E) (g : E → Ω → E) (X : Ξ → E) (ξ : Ξ → Ω) {C : ℝ}
    (hX : Measurable X) (hξ : Measurable ξ)
    (hg : Measurable (Function.uncurry g)) (hind : IndepFun X ξ P) (hmarg : P.map ξ = Q)
    (hX2 : Integrable (fun ω => ‖X ω - p‖ ^ 2) P)
    (hg2 : ∀ x, Integrable (fun ω => ‖g x ω‖ ^ 2) Q)
    (hb : ∀ x, (∫ ω, ‖g x ω‖ ^ 2 ∂Q) ≤ C * ‖x - p‖ ^ 2) :
    Integrable (fun ω => ‖g (X ω) (ξ ω)‖ ^ 2) P ∧
      (∫ ω, ‖g (X ω) (ξ ω)‖ ^ 2 ∂P) ≤ C * ∫ ω, ‖X ω - p‖ ^ 2 ∂P := by
  have hxlaw : HasLaw X (P.map X) P := ⟨hX.aemeasurable, rfl⟩
  have hxi : Integrable (fun x : E => ‖x - p‖ ^ 2) (P.map X) :=
    (integrable_map_measure (by fun_prop) hX.aemeasurable).mpr hX2
  have hp := LocalNonlinearExtragradientSampling.fresh_pair_law P Q X ξ hX hξ hind hmarg
  have hpair : HasLaw (fun ω => (X ω, ξ ω)) ((P.map X).prod Q) P :=
    ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  have hs := LocalNonlinearExtragradientMoments.fresh_oracle_second_moment
    (P := P.map X) (Q := Q) (X := id) p g measurable_id hg hxi hg2 hb
  refine ⟨hpair.integrable_comp hs.1, ?_⟩
  have he := hpair.integral_comp hs.1.aestronglyMeasurable
  have hx := hxlaw.integral_comp hxi.aestronglyMeasurable
  change (∫ ω, ‖g (X ω) (ξ ω)‖ ^ 2 ∂P) = _ at he
  change (∫ ω, ‖X ω - p‖ ^ 2 ∂P) = _ at hx
  rw [he, hx]
  exact hs.2

omit [CompleteSpace E] in
lemma actual_fresh_oracle (P : Measure Ξ) (Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p : E) (F : E → E) (g : E → Ω → E) (X : Ξ → E) (ξ : Ξ → Ω) {C : ℝ}
    (hX : Measurable X) (hξ : Measurable ξ) (hF : Measurable F)
    (hg : Measurable (Function.uncurry g)) (hind : IndepFun X ξ P) (hmarg : P.map ξ = Q)
    (hX2 : Integrable (fun ω => ‖X ω - p‖ ^ 2) P)
    (hg2 : ∀ x, Integrable (fun ω => ‖g x ω‖ ^ 2) Q)
    (hb : ∀ x, (∫ ω, ‖g x ω‖ ^ 2 ∂Q) ≤ C * ‖x - p‖ ^ 2)
    (hmean : ∀ x, (∫ ω, g x ω ∂Q) = F x) :
    Integrable (fun ω => g (X ω) (ξ ω)) P ∧
      Integrable (fun ω => ‖g (X ω) (ξ ω)‖ ^ 2) P ∧
      (∫ ω, ‖g (X ω) (ξ ω)‖ ^ 2 ∂P) ≤ C * ∫ ω, ‖X ω - p‖ ^ 2 ∂P ∧
      (∫ ω, g (X ω) (ξ ω) ∂P) = ∫ ω, F (X ω) ∂P := by
  have hxlaw : HasLaw X (P.map X) P := ⟨hX.aemeasurable, rfl⟩
  have hxi : Integrable (fun x : E => ‖x - p‖ ^ 2) (P.map X) :=
    (integrable_map_measure (by fun_prop) hX.aemeasurable).mpr hX2
  have hp := LocalNonlinearExtragradientSampling.fresh_pair_law P Q X ξ hX hξ hind hmarg
  have hpair : HasLaw (fun ω => (X ω, ξ ω)) ((P.map X).prod Q) P :=
    ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  have hsecond := LocalNonlinearExtragradientMoments.fresh_oracle_second_moment
    (P := P.map X) (Q := Q) (X := id) p g measurable_id hg hxi hg2 hb
  have hfirst := LocalNonlinearExtragradientMoments.fresh_oracle_mean
    (P := P.map X) (Q := Q) (X := id) p F g measurable_id hg hxi hg2 hb hmean
  refine ⟨hpair.integrable_comp hfirst.1, hpair.integrable_comp hsecond.1, ?_, ?_⟩
  · have he := hpair.integral_comp hsecond.1.aestronglyMeasurable
    have hx := hxlaw.integral_comp hxi.aestronglyMeasurable
    change (∫ ω, ‖g (X ω) (ξ ω)‖ ^ 2 ∂P) = _ at he
    change (∫ ω, ‖X ω - p‖ ^ 2 ∂P) = _ at hx
    rw [he, hx]
    exact hsecond.2
  · have he := hpair.integral_comp hfirst.1.aestronglyMeasurable
    have hx := hxlaw.integral_comp hF.aestronglyMeasurable
    change (∫ ω, g (X ω) (ξ ω) ∂P) = _ at he
    change (∫ ω, F (X ω) ∂P) = _ at hx
    exact he.trans (hfirst.2.trans hx.symm)

lemma random_sgd_contraction (P : Measure Ξ) (Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p : E) (F : E → E) (g : E → Ω → E) (X : Ξ → E) (ξ : Ξ → Ω) {L μ ρ : ℝ}
    (hL : 0 < L) (hρ : 0 < ρ) (hμ : 0 ≤ μ)
    (hX : Measurable X) (hξ : Measurable ξ) (hg : Measurable (Function.uncurry g))
    (hind : IndepFun X ξ P) (hmarg : P.map ξ = Q)
    (hX2 : Integrable (fun ω => ‖X ω - p‖ ^ 2) P)
    (hgi : ∀ x, Integrable (g x) Q)
    (hg2 : ∀ x, Integrable (fun ω => ‖g x ω‖ ^ 2) Q)
    (hmean : ∀ x, (∫ ω, g x ω ∂Q) = F x)
    (hsgc : ∀ x, (∫ ω, ‖g x ω‖ ^ 2 ∂Q) ≤ ρ * ‖F x‖ ^ 2)
    (hmono : ∀ x, μ * ‖x - p‖ ^ 2 ≤ ⟪x - p, F x⟫)
    (hlip : ∀ x, ‖F x‖ ^ 2 ≤ L ^ 2 * ‖x - p‖ ^ 2) :
    Integrable (fun ω => ‖X ω - (μ / (ρ * L ^ 2)) • g (X ω) (ξ ω) - p‖ ^ 2) P ∧
      (∫ ω, ‖X ω - (μ / (ρ * L ^ 2)) • g (X ω) (ξ ω) - p‖ ^ 2 ∂P) ≤
        (1 - μ ^ 2 / (ρ * L ^ 2)) * ∫ ω, ‖X ω - p‖ ^ 2 ∂P := by
  let η := μ / (ρ * L ^ 2)
  let K : E → Ω → E := fun x ω => x - η • g x ω - p
  have hK : Measurable (Function.uncurry K) :=
    (measurable_fst.sub (hg.const_smul η)).sub_const p
  have hKi (x : E) : Integrable (fun ω => ‖K x ω‖ ^ 2) Q :=
    (LocalNonlinearExtragradientMoments.integral_update_square x p η (hgi x) (hg2 x)).1
  exact actual_fresh_second_moment P Q p K X ξ hX hξ hK hind hmarg hX2 hKi
    (fun x => LocalNonlinearExtragradientMoments.stochastic_gradient_contraction
      x p (F x) hL hρ hμ (hgi x) (hg2 x) (hmean x) (hsgc x) (hmono x) (hlip x))

lemma warm_run_bound (P : Measure Ξ) (Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p x : E) (F : E → E) (g : E → Ω → E) (ξ : ℕ → Ξ → Ω) {L μ ρ : ℝ}
    (hL : 0 < L) (hρ : 1 ≤ ρ) (hμ : 0 ≤ μ) (hμL : μ ≤ L)
    (hg : Measurable (Function.uncurry g))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ Q P)
    (hgi : ∀ y, Integrable (g y) Q)
    (hg2 : ∀ y, Integrable (fun ω => ‖g y ω‖ ^ 2) Q)
    (hmean : ∀ y, (∫ ω, g y ω ∂Q) = F y)
    (hsgc : ∀ y, (∫ ω, ‖g y ω‖ ^ 2 ∂Q) ≤ ρ * ‖F y‖ ^ 2)
    (hmono : ∀ y, μ * ‖y - p‖ ^ 2 ≤ ⟪y - p, F y⟫)
    (hlip : ∀ y, ‖F y‖ ^ 2 ≤ L ^ 2 * ‖y - p‖ ^ 2) (k : ℕ) :
    Integrable (fun ω => ‖LongTails.Algorithms.LocalNonlinearExtragradient.warmRun
      (μ / (ρ * L ^ 2)) g x (fun j => ξ j ω) k - p‖ ^ 2) P ∧
      (∫ ω, ‖LongTails.Algorithms.LocalNonlinearExtragradient.warmRun
        (μ / (ρ * L ^ 2)) g x (fun j => ξ j ω) k - p‖ ^ 2 ∂P) ≤
        (1 - μ ^ 2 / (ρ * L ^ 2)) ^ k * ‖x - p‖ ^ 2 := by
  classical
  let η := μ / (ρ * L ^ 2)
  let c := 1 - μ ^ 2 / (ρ * L ^ 2)
  have hρ0 : 0 < ρ := by linarith
  have hc : 0 ≤ c := by
    have hm2 : μ ^ 2 ≤ L ^ 2 := (sq_le_sq₀ hμ hL.le).mpr hμL
    have hr := mul_le_mul_of_nonneg_right hρ (sq_nonneg L)
    have hh : μ ^ 2 / (ρ * L ^ 2) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
    dsimp [c]
    linarith
  let default : Ω := Classical.choice (nonempty_of_isProbabilityMeasure Q)
  have hstream : Measurable (fun ω j => ξ j ω) := Measurable.of_eval hIID.measurable
  induction k with
  | zero => simp [LongTails.Algorithms.LocalNonlinearExtragradient.warmRun]
  | succ k ih =>
      let X : Ξ → E := fun ω => LongTails.Algorithms.LocalNonlinearExtragradient.warmRun
        η g x (fun j => ξ j ω) k
      have hX : Measurable X :=
        (LocalNonlinearExtragradientSampling.measurable_warmRun η g x hg k).comp hstream
      have hind := LocalNonlinearExtragradientSampling.warmRun_independent_fresh
        η g x default hg ξ P hIID.independent hIID.measurable k k le_rfl
      have hs := random_sgd_contraction P Q p F g X (ξ k) hL hρ0 hμ hX
        (hIID.measurable k) hg hind (hIID.marginal k) ih.1 hgi hg2 hmean hsgc hmono hlip
      refine ⟨hs.1, ?_⟩
      change (∫ ω, ‖X ω - η • g (X ω) (ξ k ω) - p‖ ^ 2 ∂P) ≤ c ^ (k + 1) * ‖x - p‖ ^ 2
      calc
        _ ≤ c * ∫ ω, ‖X ω - p‖ ^ 2 ∂P := hs.2
        _ ≤ c * (c ^ k * ‖x - p‖ ^ 2) := mul_le_mul_of_nonneg_left ih.2 hc
        _ = _ := by rw [pow_succ]; ring

lemma random_half_growth (P : Measure Ξ) (Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p : E) (F : E → E) (g : E → Ω → E) (X : Ξ → E) (ξ : Ξ → Ω) {L ρ : ℝ}
    (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hX : Measurable X) (hξ : Measurable ξ) (hg : Measurable (Function.uncurry g))
    (hind : IndepFun X ξ P) (hmarg : P.map ξ = Q)
    (hX2 : Integrable (fun ω => ‖X ω - p‖ ^ 2) P)
    (hgi : ∀ x, Integrable (g x) Q)
    (hg2 : ∀ x, Integrable (fun ω => ‖g x ω‖ ^ 2) Q)
    (hmean : ∀ x, (∫ ω, g x ω ∂Q) = F x)
    (hsgc : ∀ x, (∫ ω, ‖g x ω‖ ^ 2 ∂Q) ≤ ρ * ‖F x‖ ^ 2)
    (hmono : ∀ x, 0 ≤ ⟪x - p, F x⟫)
    (hlip : ∀ x, ‖F x‖ ^ 2 ≤ L ^ 2 * ‖x - p‖ ^ 2) :
    Integrable (fun ω => ‖X ω - (1 / (4 * L)) • g (X ω) (ξ ω) - p‖ ^ 2) P ∧
      (∫ ω, ‖X ω - (1 / (4 * L)) • g (X ω) (ξ ω) - p‖ ^ 2 ∂P) ≤
        (1 + ρ / 16) * ∫ ω, ‖X ω - p‖ ^ 2 ∂P := by
  let η : ℝ := 1 / (4 * L)
  let K : E → Ω → E := fun x ω => x - η • g x ω - p
  have hK : Measurable (Function.uncurry K) :=
    (measurable_fst.sub (hg.const_smul η)).sub_const p
  have hKi (x : E) : Integrable (fun ω => ‖K x ω‖ ^ 2) Q :=
    (LocalNonlinearExtragradientMoments.integral_update_square x p η (hgi x) (hg2 x)).1
  exact actual_fresh_second_moment P Q p K X ξ hX hξ hK hind hmarg hX2 hKi
    (fun x => LocalNonlinearExtragradientMoments.stochastic_half_growth
      x p (F x) hL hρ (hgi x) (hg2 x) (hmean x) (hsgc x) (hmono x) (hlip x))

omit [CompleteSpace E] in
lemma random_update_bound (P : Measure Ξ) (p : E) (η : ℝ) (X q : Ξ → E)
    (hX : Measurable X) (hq : Measurable q)
    (hX2 : Integrable (fun ω => ‖X ω - p‖ ^ 2) P)
    (hq2 : Integrable (fun ω => ‖q ω‖ ^ 2) P) :
    Integrable (fun ω => ‖X ω - η • q ω - p‖ ^ 2) P ∧
      (∫ ω, ‖X ω - η • q ω - p‖ ^ 2 ∂P) ≤
        2 * (∫ ω, ‖X ω - p‖ ^ 2 ∂P) + 2 * η ^ 2 * ∫ ω, ‖q ω‖ ^ 2 ∂P := by
  have hb (ω : Ξ) : ‖X ω - η • q ω - p‖ ^ 2 ≤
      2 * ‖X ω - p‖ ^ 2 + 2 * η ^ 2 * ‖q ω‖ ^ 2 := by
    rw [show X ω - η • q ω - p = (X ω - p) - η • q ω by abel]
    simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc] using
      AuxiliaryInner.norm_sub_sq_le (X ω - p) (η • q ω)
  have hm : Measurable (fun ω => ‖X ω - η • q ω - p‖ ^ 2) := by fun_prop
  have hi : Integrable (fun ω => 2 * ‖X ω - p‖ ^ 2 + 2 * η ^ 2 * ‖q ω‖ ^ 2) P :=
    (hX2.const_mul 2).add (hq2.const_mul (2 * η ^ 2))
  have hs : Integrable (fun ω => ‖X ω - η • q ω - p‖ ^ 2) P :=
    hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hb ω)
  refine ⟨hs, ?_⟩
  have ht := integral_mono hs hi hb
  rw [integral_add (hX2.const_mul 2) (hq2.const_mul (2 * η ^ 2)),
    integral_const_mul 2, integral_const_mul (2 * η ^ 2)] at ht
  exact ht

lemma run_second_moment (P : Measure Ξ) (Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p x : E) (F : E → E) (g : E → Ω → E) (ξ : ℕ → Ξ → Ω) {L ρ : ℝ}
    (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hg : Measurable (Function.uncurry g))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ Q P)
    (hgi : ∀ y, Integrable (g y) Q)
    (hg2 : ∀ y, Integrable (fun ω => ‖g y ω‖ ^ 2) Q)
    (hmean : ∀ y, (∫ ω, g y ω ∂Q) = F y)
    (hsgc : ∀ y, (∫ ω, ‖g y ω‖ ^ 2 ∂Q) ≤ ρ * ‖F y‖ ^ 2)
    (hmono : ∀ y, 0 ≤ ⟪y - p, F y⟫)
    (hlip : ∀ y, ‖F y‖ ^ 2 ≤ L ^ 2 * ‖y - p‖ ^ 2) (k : ℕ) :
    Integrable (fun ω => ‖LongTails.Algorithms.LocalNonlinearExtragradient.run
      (1 / (4 * L)) g x (fun j => ξ j ω) k - p‖ ^ 2) P ∧
      (∫ ω, ‖LongTails.Algorithms.LocalNonlinearExtragradient.run
        (1 / (4 * L)) g x (fun j => ξ j ω) k - p‖ ^ 2 ∂P) ≤
        (2 + ρ / 8 + ρ ^ 2 / 128) ^ k * ‖x - p‖ ^ 2 := by
  classical
  let η : ℝ := 1 / (4 * L)
  let G : ℝ := 2 + ρ / 8 + ρ ^ 2 / 128
  have hG : 0 ≤ G := by dsimp [G]; positivity
  let default : Ω := Classical.choice (nonempty_of_isProbabilityMeasure Q)
  have hstream : Measurable (fun ω j => ξ j ω) := Measurable.of_eval hIID.measurable
  have hb (y : E) : (∫ ω, ‖g y ω‖ ^ 2 ∂Q) ≤ (ρ * L ^ 2) * ‖y - p‖ ^ 2 :=
    (hsgc y).trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hlip y) hρ)
  induction k with
  | zero => simp [LongTails.Algorithms.LocalNonlinearExtragradient.run]
  | succ k ih =>
      let X : Ξ → E := fun ω => LongTails.Algorithms.LocalNonlinearExtragradient.run
        η g x (fun j => ξ j ω) k
      let Y : Ξ → E := fun ω => X ω - η • g (X ω) (ξ (2 * k) ω)
      let q : Ξ → E := fun ω => g (Y ω) (ξ (2 * k + 1) ω)
      have hX : Measurable X :=
        (LocalNonlinearExtragradientSampling.measurable_run η g x hg k).comp hstream
      have hY : Measurable Y :=
        hX.sub ((hg.comp (hX.prodMk (hIID.measurable (2 * k)))).const_smul η)
      have hq : Measurable q := hg.comp (hY.prodMk (hIID.measurable (2 * k + 1)))
      have hindX := LocalNonlinearExtragradientSampling.run_independent_fresh
        η g x default hg ξ P hIID.independent hIID.measurable k (2 * k) le_rfl
      have hy := random_half_growth P Q p F g X (ξ (2 * k)) hL hρ hX
        (hIID.measurable (2 * k)) hg hindX (hIID.marginal (2 * k))
        ih.1 hgi hg2 hmean hsgc hmono hlip
      have hindY := LocalNonlinearExtragradientSampling.half_independent_fresh
        η g x default hg ξ P hIID.independent hIID.measurable k (2 * k + 1) le_rfl
      have hqs := actual_fresh_second_moment P Q p g Y (ξ (2 * k + 1)) hY
        (hIID.measurable (2 * k + 1)) hg hindY (hIID.marginal (2 * k + 1)) hy.1 hg2 hb
      have hn := random_update_bound P p η X q hX hq ih.1 hqs.1
      refine ⟨hn.1, ?_⟩
      change (∫ ω, ‖X ω - η • q ω - p‖ ^ 2 ∂P) ≤ G ^ (k + 1) * ‖x - p‖ ^ 2
      calc
        _ ≤ 2 * (∫ ω, ‖X ω - p‖ ^ 2 ∂P) +
            2 * η ^ 2 * ((ρ * L ^ 2) * ∫ ω, ‖Y ω - p‖ ^ 2 ∂P) :=
          hn.2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hqs.2
            (show 0 ≤ 2 * η ^ 2 by positivity)))
        _ ≤ 2 * (∫ ω, ‖X ω - p‖ ^ 2 ∂P) +
            2 * η ^ 2 * ((ρ * L ^ 2) * ((1 + ρ / 16) * ∫ ω, ‖X ω - p‖ ^ 2 ∂P)) := by
          gcongr
          exact hy.2
        _ = G * ∫ ω, ‖X ω - p‖ ^ 2 ∂P := by
          dsimp [η, G]
          field_simp
          ring
        _ ≤ G * (G ^ k * ‖x - p‖ ^ 2) := mul_le_mul_of_nonneg_left ih.2 hG
        _ = _ := by rw [pow_succ]; ring

lemma random_mean_recursion (P : Measure Ξ) (Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p : E) (F : E → E) (J : E → E →L[ℝ] E) (g : E → Ω → E)
    (X : Ξ → E) (ξ ζ : Ξ → Ω) {L ρ M : ℝ}
    (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hd : ∀ z, HasFDerivAt F (J z) z)
    (hJ : ∀ u v, ‖J u - J v‖ ≤ M * ‖u - v‖) (hp : F p = 0)
    (hX : Measurable X) (hξ : Measurable ξ) (hζ : Measurable ζ)
    (hg : Measurable (Function.uncurry g))
    (hindX : IndepFun X ξ P)
    (hindY : IndepFun (fun ω => X ω - (1 / (4 * L)) • g (X ω) (ξ ω)) ζ P)
    (hmξ : P.map ξ = Q) (hmζ : P.map ζ = Q)
    (hX2 : Integrable (fun ω => ‖X ω - p‖ ^ 2) P)
    (hgi : ∀ y, Integrable (g y) Q)
    (hg2 : ∀ y, Integrable (fun ω => ‖g y ω‖ ^ 2) Q)
    (hmean : ∀ y, (∫ ω, g y ω ∂Q) = F y)
    (hsgc : ∀ y, (∫ ω, ‖g y ω‖ ^ 2 ∂Q) ≤ ρ * ‖F y‖ ^ 2)
    (hmono : ∀ y, 0 ≤ ⟪y - p, F y⟫)
    (hlip : ∀ y, ‖F y‖ ^ 2 ≤ L ^ 2 * ‖y - p‖ ^ 2) :
    let η : ℝ := 1 / (4 * L)
    let Y : Ξ → E := fun ω => X ω - η • g (X ω) (ξ ω)
    (∫ ω, X ω - η • g (Y ω) (ζ ω) - p ∂P) =
      (∫ ω, X ω - p ∂P) - η • J p (∫ ω, X ω - p ∂P) +
        η ^ 2 • J p (J p (∫ ω, X ω - p ∂P)) +
        η ^ 2 • J p (∫ ω, F (X ω) - J p (X ω - p) ∂P) -
        η • (∫ ω, F (Y ω) - J p (Y ω - p) ∂P) := by
  dsimp only
  let η : ℝ := 1 / (4 * L)
  let Y : Ξ → E := fun ω => X ω - η • g (X ω) (ξ ω)
  have hY : Measurable Y := hX.sub ((hg.comp (hX.prodMk hξ)).const_smul η)
  have hF : Measurable F :=
    (continuous_iff_continuousAt.mpr fun z => (hd z).continuousAt).measurable
  have hb (y : E) : (∫ ω, ‖g y ω‖ ^ 2 ∂Q) ≤ (ρ * L ^ 2) * ‖y - p‖ ^ 2 :=
    (hsgc y).trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hlip y) hρ)
  have hy := random_half_growth P Q p F g X ξ hL hρ hX hξ hg hindX hmξ
    hX2 hgi hg2 hmean hsgc hmono hlip
  have hfirst := actual_fresh_oracle P Q p F g X ξ hX hξ hF hg hindX hmξ hX2 hg2 hb hmean
  have hsecond := actual_fresh_oracle P Q p F g Y ζ hY hζ hF hg hindY hmζ hy.1 hg2 hb hmean
  have hXi : Integrable (fun ω => X ω - p) P := by
    apply ((integrable_const (1 : ℝ)).add hX2).mono' (hX.sub_const p).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    dsimp
    nlinarith [sq_nonneg (‖X ω - p‖ - 1 / 2)]
  have hRX := LocalNonlinearExtragradientMoments.integral_root_remainder F J p hd hJ hp
    hX.aestronglyMeasurable hX2
  have hRY := LocalNonlinearExtragradientMoments.integral_root_remainder F J p hd hJ hp
    hY.aestronglyMeasurable hy.1
  exact LocalNonlinearExtragradientMoments.extragradient_mean_recursion F (J p) p η
    hXi hfirst.1 hsecond.1 (fun _ => rfl) hRX.1 hRY.1 hfirst.2.2.2 hsecond.2.2.2

end LongTails.Proofs.LocalNonlinearExtragradientIteration
