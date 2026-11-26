import LongTails.Proofs.AbcSgdRate
import LongTails.Proofs.GdConvex

open MeasureTheory Set InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.BiasedSgdRate

open OracleTemplate.StochasticGradient LongTails.Proofs.AbcSgdRate

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

structure BiasedModel (f : E → ℝ) (g : E → Ω → E) (p : Measure Ω) (L m M σ ζ fstar : ℝ) :
    Prop where
  grad : ∀ x, HasGradientAt f (gradient f x) x
  lip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖
  lower : ∀ x, fstar ≤ f x
  meas : Measurable (Function.uncurry g)
  int : ∀ x, Integrable (g x) p
  bias : ∀ x, ‖(∫ ω, g x ω ∂p) - gradient f x‖ ^ 2 ≤ m * ‖gradient f x‖ ^ 2 + ζ ^ 2
  varint : ∀ x, Integrable (fun ω => ‖g x ω - ∫ ω', g x ω' ∂p‖ ^ 2) p
  var : ∀ x, ∫ ω, ‖g x ω - ∫ ω', g x ω' ∂p‖ ^ 2 ∂p ≤ M * ‖∫ ω, g x ω ∂p‖ ^ 2 + σ ^ 2

lemma one_step_biased {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω} [IsProbabilityMeasure p]
    {L m M σ ζ fstar η : ℝ} (hM : BiasedModel f g p L m M σ ζ fstar) (hL : 0 < L)
    (hη : 0 ≤ η) (hηL : L * η * (1 + M) ≤ 1) (x : E) :
    Integrable (fun ω => f (x - η • g x ω) - fstar) p ∧
    (∫ ω, f (x - η • g x ω) - fstar ∂p) ≤
      (f x - fstar) - η / 2 * (1 - m) * ‖gradient f x‖ ^ 2 + η / 2 * ζ ^ 2 +
        L * η ^ 2 * σ ^ 2 / 2 := by
  set v := gradient f x with hvdef
  set μ := ∫ ω, g x ω ∂p with hμdef
  let noise := fun ω => g x ω - μ
  have hn : Integrable noise p := (hM.int x).sub (integrable_const _)
  have hz : (∫ ω, noise ω ∂p) = 0 := by
    rw [integral_sub (hM.int x) (integrable_const _), integral_const]
    simp [μ]
  let U := fun ω => (f x - fstar) - η * ⟪v, μ⟫ - η * ⟪v, noise ω⟫ +
    L / 2 * η ^ 2 * (‖μ‖ ^ 2 + 2 * ⟪μ, noise ω⟫ + ‖noise ω‖ ^ 2)
  have hpt : ∀ ω, f (x - η • g x ω) - fstar ≤ U ω := by
    intro ω
    have hs := OracleTemplate.Gradient.smooth_upper_bound hM.grad hM.lip x (x - η • g x ω)
    have hg : μ + noise ω = g x ω := by simp [noise]
    have he : x - η • g x ω - x = -(η • (μ + noise ω)) := by rw [hg]; abel
    rw [he, ← hvdef, inner_neg_right, inner_smul_right, inner_add_right, norm_neg, norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs, norm_add_sq_real] at hs
    dsimp only [U]
    linarith
  have hU : Integrable U p := by
    have h1 : Integrable (fun ω => ⟪v, noise ω⟫) p := hn.const_inner v
    have h1' : Integrable (fun ω => ⟪μ, noise ω⟫) p := hn.const_inner μ
    have h2 : Integrable (fun ω => ‖noise ω‖ ^ 2) p := hM.varint x
    exact ((((integrable_const _).sub (integrable_const _)).sub (h1.const_mul η)).add
      ((((integrable_const _).add (h1'.const_mul 2)).add h2).const_mul _))
  have hmeas : Measurable (fun ω => f (x - η • g x ω) - fstar) :=
    ((f_continuous hM.grad).measurable.comp (measurable_const.sub
      ((hM.meas.comp (measurable_const.prodMk measurable_id)).const_smul η))).sub_const _
  have hi : Integrable (fun ω => f (x - η • g x ω) - fstar) p :=
    hU.mono_nonneg hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => sub_nonneg.mpr (hM.lower _)))
      (Filter.Eventually.of_forall hpt)
  refine ⟨hi, ?_⟩
  have hIU : ∫ ω, U ω ∂p = (f x - fstar) - η * ⟪v, μ⟫ +
      L / 2 * η ^ 2 * (‖μ‖ ^ 2 + ∫ ω, ‖noise ω‖ ^ 2 ∂p) := by
    have h1 : Integrable (fun ω => ⟪v, noise ω⟫) p := hn.const_inner v
    have h1' : Integrable (fun ω => ⟪μ, noise ω⟫) p := hn.const_inner μ
    have h2 : Integrable (fun ω => ‖noise ω‖ ^ 2) p := hM.varint x
    have hin : ∫ ω, ⟪v, noise ω⟫ ∂p = 0 := by rw [integral_inner hn, hz, inner_zero_right]
    have hin' : ∫ ω, ⟪μ, noise ω⟫ ∂p = 0 := by rw [integral_inner hn, hz, inner_zero_right]
    have hUe : U = fun ω => (f x - fstar - η * ⟪v, μ⟫ + L / 2 * η ^ 2 * ‖μ‖ ^ 2) +
        ((-η) * ⟪v, noise ω⟫ + ((L * η ^ 2) * ⟪μ, noise ω⟫ + L / 2 * η ^ 2 * ‖noise ω‖ ^ 2)) := by
      funext ω; dsimp only [U]; ring
    have hC : Integrable (fun ω => (L * η ^ 2) * ⟪μ, noise ω⟫ + L / 2 * η ^ 2 * ‖noise ω‖ ^ 2) p :=
      (h1'.const_mul _).add (h2.const_mul _)
    have hB : Integrable (fun ω => (-η) * ⟪v, noise ω⟫ +
        ((L * η ^ 2) * ⟪μ, noise ω⟫ + L / 2 * η ^ 2 * ‖noise ω‖ ^ 2)) p :=
      (h1.const_mul _).add hC
    have hB1 : Integrable (fun ω => (-η) * ⟪v, noise ω⟫) p := h1.const_mul _
    have hC1 : Integrable (fun ω => (L * η ^ 2) * ⟪μ, noise ω⟫) p := h1'.const_mul _
    have hC2 : Integrable (fun ω => L / 2 * η ^ 2 * ‖noise ω‖ ^ 2) p := h2.const_mul _
    rw [hUe, integral_add (integrable_const _) hB, integral_add hB1 hC, integral_add hC1 hC2,
      integral_const, integral_const_mul, integral_const_mul, integral_const_mul, hin, hin']
    simp only [probReal_univ, one_smul]
    ring
  have hgv : (∫ ω, ‖noise ω‖ ^ 2 ∂p) ≤ M * ‖μ‖ ^ 2 + σ ^ 2 := hM.var x
  have hb : ‖μ - v‖ ^ 2 ≤ m * ‖v‖ ^ 2 + ζ ^ 2 := hM.bias x
  have hid : ‖μ - v‖ ^ 2 = ‖μ‖ ^ 2 - 2 * ⟪v, μ⟫ + ‖v‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm]
  calc _ ≤ ∫ ω, U ω ∂p := integral_mono hi hU hpt
    _ = _ := hIU
    _ ≤ _ := by
      have hk : 0 ≤ L / 2 * η ^ 2 := by positivity
      have h3 := mul_le_mul_of_nonneg_left hgv hk
      have hμ2 : L / 2 * η ^ 2 * ((1 + M) * ‖μ‖ ^ 2) ≤ η / 2 * ‖μ‖ ^ 2 := by
        have : L / 2 * η ^ 2 * (1 + M) ≤ η / 2 := by nlinarith
        nlinarith [sq_nonneg ‖μ‖]
      nlinarith [sq_nonneg ‖v‖]

lemma gradLoss_bound_biased {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω} [IsProbabilityMeasure p]
    {L m M σ ζ fstar η : ℝ} (hM : BiasedModel f g p L m M σ ζ fstar) (hL : 0 < L)
    (hm : m < 1) (hη : 0 < η) (hηL : L * η * (1 + M) ≤ 1) (K : ℕ) (x : E) :
    Integrable (gradLoss f g η K x) (Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, gradLoss f g η K x ξ ∂Measure.pi (fun _ : Fin K => p)) ≤
      2 / (η * (1 - m)) * (f x - fstar) + K * ((ζ ^ 2 + L * η * σ ^ 2) / (1 - m)) := by
  have h1m : 0 < 1 - m := by linarith
  induction K generalizing x with
  | zero =>
    have h0 : gradLoss f g η 0 x = fun _ => 0 := by funext ξ; rfl
    rw [h0]
    refine ⟨integrable_zero _ _ _, ?_⟩
    simp only [integral_zero, Nat.cast_zero, zero_mul, add_zero]
    have := sub_nonneg.mpr (hM.lower x)
    positivity
  | succ K ih =>
    have hmp : Measurable (gradLoss f g η (K + 1) x) :=
      (measurable_gradLoss hM.lip hM.meas η (K + 1)).of_uncurry_left
    let q := Measure.pi (fun _ : Fin K => p)
    let c : ℝ := (ζ ^ 2 + L * η * σ ^ 2) / (1 - m)
    let F := fun z : Ω × (Fin K → Ω) =>
      ‖gradient f x‖ ^ 2 + gradLoss f g η K (x - η • g x z.1) z.2
    let Bd := fun ω => ‖gradient f x‖ ^ 2 + (2 / (η * (1 - m)) * (f (x - η • g x ω) - fstar) +
      K * c)
    have hstep := one_step_biased hM hL hη.le hηL x
    have hBd : Integrable Bd p :=
      (integrable_const _).add ((hstep.1.const_mul _).add (integrable_const _))
    have hF : Measurable F := by
      have hx : Measurable (fun z : Ω × (Fin K → Ω) => x - η • g x z.1) :=
        measurable_const.sub ((hM.meas.comp (measurable_const.prodMk measurable_fst)).const_smul η)
      exact measurable_const.add ((measurable_gradLoss hM.lip hM.meas η K).comp
        (hx.prodMk measurable_snd))
    have hnonneg : ∀ z, 0 ≤ F z := fun z => add_nonneg (sq_nonneg _) (gradLoss_nonneg _ _ _ _ _ _)
    have hsection : ∀ ω, Integrable (fun ξ => F (ω, ξ)) q :=
      fun ω => (integrable_const _).add (ih (x - η • g x ω)).1
    have hbound : ∀ ω, (∫ ξ, F (ω, ξ) ∂q) ≤ Bd ω := by
      intro ω
      dsimp only [F, Bd]
      rw [integral_add (integrable_const _) (ih _).1, integral_const, probReal_univ, one_smul]
      linarith [(ih (x - η • g x ω)).2]
    have hint : Integrable (fun ω => ∫ ξ, ‖F (ω, ξ)‖ ∂q) p := by
      apply hBd.mono_nonneg hF.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun ω => integral_nonneg (fun ξ => norm_nonneg _))
      · apply Filter.Eventually.of_forall
        intro ω
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] using hbound ω
    have hFi : Integrable F (p.prod q) := (integrable_prod_iff hF.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hsection, hint⟩
    have heq : (fun z : Ω × (Fin K → Ω) => gradLoss f g η (K + 1) x (Fin.cons z.1 z.2)) = F := by
      funext z
      simp only [gradLoss, Fin.cons_zero, Fin.cons_succ, F]
    have hcons := cons_measurePreserving p K
    have hpi : Integrable (gradLoss f g η (K + 1) x) (Measure.pi (fun _ : Fin (K + 1) => p)) :=
      (hcons.integrable_comp hmp.aestronglyMeasurable).mp (by
        simpa only [Function.comp_def, heq] using hFi)
    refine ⟨hpi, ?_⟩
    calc
      _ = ∫ z, F z ∂p.prod q := by
        rw [← hcons.map_eq, integral_map hcons.measurable.aemeasurable hmp.aestronglyMeasurable]
        rw [heq]
      _ = ∫ ω, ∫ ξ, F (ω, ξ) ∂q ∂p := integral_prod F hFi
      _ ≤ ∫ ω, Bd ω ∂p := integral_mono hFi.integral_prod_left hBd hbound
      _ = ‖gradient f x‖ ^ 2 + (2 / (η * (1 - m)) * ∫ ω, f (x - η • g x ω) - fstar ∂p +
            K * c) := by
        have hA1 : Integrable (fun ω => 2 / (η * (1 - m)) * (f (x - η • g x ω) - fstar)) p :=
          hstep.1.const_mul _
        have hA2 : Integrable (fun ω => 2 / (η * (1 - m)) * (f (x - η • g x ω) - fstar) +
            K * c) p := hA1.add (integrable_const _)
        dsimp only [Bd]
        rw [integral_add (integrable_const _) hA2, integral_add hA1 (integrable_const _),
          integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
      _ ≤ _ := by
        have h2 := hstep.2
        have hk : 0 ≤ 2 / (η * (1 - m)) := by positivity
        have h3 := mul_le_mul_of_nonneg_left h2 hk
        have he1 : 2 / (η * (1 - m)) * (η / 2 * (1 - m) * ‖gradient f x‖ ^ 2) =
            ‖gradient f x‖ ^ 2 := by
          field_simp
        have he2 : 2 / (η * (1 - m)) * (η / 2 * ζ ^ 2 + L * η ^ 2 * σ ^ 2 / 2) = c := by
          dsimp only [c]
          field_simp
        push_cast
        nlinarith [he1, he2]

end LongTails.Proofs.BiasedSgdRate
