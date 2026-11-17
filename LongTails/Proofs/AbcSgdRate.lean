import LongTails.Proofs.SgdConvex
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory Set InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AbcSgdRate

open OracleTemplate.StochasticGradient

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

structure AbcModel (f : E → ℝ) (g : E → Ω → E) (p : Measure Ω) (L A B C fstar : ℝ) : Prop where
  grad : ∀ x, HasGradientAt f (gradient f x) x
  lip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖
  lower : ∀ x, fstar ≤ f x
  meas : Measurable (Function.uncurry g)
  int : ∀ x, Integrable (g x) p
  mean : ∀ x, ∫ ω, g x ω ∂p = gradient f x
  varint : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p
  var : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤
    2 * A * (f x - fstar) + B * ‖gradient f x‖ ^ 2 + C

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma f_continuous {f : E → ℝ} (hg : ∀ x, HasGradientAt f (gradient f x) x) : Continuous f :=
  continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma gradient_continuous {f : E → ℝ} {L : ℝ}
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) : Continuous (gradient f) := by
  apply LipschitzWith.continuous (K := ⟨max L 0, le_max_right _ _⟩)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  exact (hlip x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

lemma one_step {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω} [IsProbabilityMeasure p]
    {L A B C fstar η : ℝ} (hM : AbcModel f g p L A B C fstar) (hL : 0 < L)
    (hη : 0 ≤ η) (hηL : L * η * (1 + B) ≤ 1) (x : E) :
    Integrable (fun ω => f (x - η • g x ω) - fstar) p ∧
    (∫ ω, f (x - η • g x ω) - fstar ∂p) ≤
      (1 + L * A * η ^ 2) * (f x - fstar) - η / 2 * ‖gradient f x‖ ^ 2 + L * η ^ 2 * C / 2 := by
  set v := gradient f x with hvdef
  let noise := fun ω => g x ω - v
  have hn : Integrable noise p := (hM.int x).sub (integrable_const _)
  have hz : (∫ ω, noise ω ∂p) = 0 := by
    rw [integral_sub (hM.int x) (integrable_const _), hM.mean, integral_const]
    simp [v]
  let U := fun ω => (f x - fstar) - η * ‖v‖ ^ 2 - η * ⟪v, noise ω⟫ +
    L / 2 * η ^ 2 * (‖v‖ ^ 2 + 2 * ⟪v, noise ω⟫ + ‖noise ω‖ ^ 2)
  have hpt : ∀ ω, f (x - η • g x ω) - fstar ≤ U ω := by
    intro ω
    have hs := OracleTemplate.Gradient.smooth_upper_bound hM.grad hM.lip x (x - η • g x ω)
    have hg : v + noise ω = g x ω := by simp [noise]
    have he : x - η • g x ω - x = -(η • (v + noise ω)) := by rw [hg]; abel
    rw [he, ← hvdef, inner_neg_right, inner_smul_right, inner_add_right,
      real_inner_self_eq_norm_sq, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      norm_add_sq_real] at hs
    dsimp only [U]
    linarith
  have hU : Integrable U p := by
    have h1 : Integrable (fun ω => ⟪v, noise ω⟫) p := hn.const_inner v
    have h2 : Integrable (fun ω => ‖noise ω‖ ^ 2) p := hM.varint x
    exact ((((integrable_const _).sub (integrable_const _)).sub (h1.const_mul η)).add
      ((((integrable_const _).add (h1.const_mul 2)).add h2).const_mul _))
  have hmeas : Measurable (fun ω => f (x - η • g x ω) - fstar) :=
    ((f_continuous hM.grad).measurable.comp (measurable_const.sub
      ((hM.meas.comp (measurable_const.prodMk measurable_id)).const_smul η))).sub_const _
  have hi : Integrable (fun ω => f (x - η • g x ω) - fstar) p :=
    hU.mono_nonneg hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => sub_nonneg.mpr (hM.lower _)))
      (Filter.Eventually.of_forall hpt)
  refine ⟨hi, ?_⟩
  have hIU : ∫ ω, U ω ∂p = (f x - fstar) - η * ‖v‖ ^ 2 +
      L / 2 * η ^ 2 * (‖v‖ ^ 2 + ∫ ω, ‖noise ω‖ ^ 2 ∂p) := by
    have h1 : Integrable (fun ω => ⟪v, noise ω⟫) p := hn.const_inner v
    have h2 : Integrable (fun ω => ‖noise ω‖ ^ 2) p := hM.varint x
    have hin : ∫ ω, ⟪v, noise ω⟫ ∂p = 0 := by rw [integral_inner hn, hz, inner_zero_right]
    have hUe : U = fun ω => ((f x - fstar) - η * ‖v‖ ^ 2 + L / 2 * η ^ 2 * ‖v‖ ^ 2 +
        (L * η ^ 2 - η) * ⟪v, noise ω⟫) + L / 2 * η ^ 2 * ‖noise ω‖ ^ 2 := by
      funext ω; dsimp only [U]; ring
    have hA1 : Integrable (fun ω => (f x - fstar) - η * ‖v‖ ^ 2 + L / 2 * η ^ 2 * ‖v‖ ^ 2 +
        (L * η ^ 2 - η) * ⟪v, noise ω⟫) p := (integrable_const _).add (h1.const_mul _)
    have hA2 : Integrable (fun ω => L / 2 * η ^ 2 * ‖noise ω‖ ^ 2) p := h2.const_mul _
    rw [hUe, integral_add hA1 hA2, integral_add (integrable_const _) (h1.const_mul _),
      integral_const_mul, integral_const_mul, hin, integral_const]
    simp only [probReal_univ, one_smul]
    ring
  have hv := hM.var x
  have hgv : (∫ ω, ‖noise ω‖ ^ 2 ∂p) ≤ 2 * A * (f x - fstar) + B * ‖v‖ ^ 2 + C := hv
  have hfx : 0 ≤ f x - fstar := sub_nonneg.mpr (hM.lower x)
  calc _ ≤ ∫ ω, U ω ∂p := integral_mono hi hU hpt
    _ = _ := hIU
    _ ≤ _ := by
      have hk : 0 ≤ L / 2 * η ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hgv hk
      have hη2 : L * η ^ 2 * (1 + B) ≤ η := by nlinarith
      nlinarith [sq_nonneg ‖v‖]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
noncomputable def gradLoss (f : E → ℝ) (g : E → Ω → E) (η : ℝ) :
    (K : ℕ) → E → (Fin K → Ω) → ℝ
  | 0, _, _ => 0
  | K + 1, x, ξ => ‖gradient f x‖ ^ 2 + gradLoss f g η K (x - η • g x (ξ 0)) (fun i => ξ i.succ)

lemma measurable_gradLoss {f : E → ℝ} {g : E → Ω → E} {L : ℝ}
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (h : Measurable (Function.uncurry g)) (η : ℝ) (K : ℕ) :
    Measurable (fun z : E × (Fin K → Ω) => gradLoss f g η K z.1 z.2) := by
  have hgr := (gradient_continuous hlip).measurable
  induction K with
  | zero => exact measurable_const
  | succ K ih =>
    have ht : Measurable (fun z : E × (Fin (K + 1) → Ω) =>
        (z.1 - η • g z.1 (z.2 0), fun i : Fin K => z.2 i.succ)) := by
      have hg : Measurable (fun z : E × (Fin (K + 1) → Ω) => g z.1 (z.2 0)) :=
        h.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
      exact (measurable_fst.sub (hg.const_smul η)).prodMk (by fun_prop)
    exact ((hgr.comp measurable_fst).norm.pow_const 2).add (ih.comp ht)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma gradLoss_nonneg (f : E → ℝ) (g : E → Ω → E) (η : ℝ) (K : ℕ) (x : E) (ξ : Fin K → Ω) :
    0 ≤ gradLoss f g η K x ξ := by
  induction K generalizing x with
  | zero => exact le_rfl
  | succ K ih => exact add_nonneg (sq_nonneg _) (ih _ _)

lemma gradLoss_bound {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω} [IsProbabilityMeasure p]
    {L A B C fstar η : ℝ} (hM : AbcModel f g p L A B C fstar) (hL : 0 < L) (hA : 0 ≤ A)
    (hC : 0 ≤ C) (hη : 0 < η) (hηL : L * η * (1 + B) ≤ 1) (K : ℕ) (x : E) :
    Integrable (gradLoss f g η K x) (Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, gradLoss f g η K x ξ ∂Measure.pi (fun _ : Fin K => p)) ≤
      2 / η * (1 + L * A * η ^ 2) ^ K * (f x - fstar) +
        L * η * C * K * (1 + L * A * η ^ 2) ^ K := by
  set ρ := 1 + L * A * η ^ 2
  have hρ : 1 ≤ ρ := by have : 0 ≤ L * A * η ^ 2 := by positivity
                        linarith
  induction K generalizing x with
  | zero =>
    have h0 : gradLoss f g η 0 x = fun _ => 0 := by funext ξ; rfl
    rw [h0]
    refine ⟨integrable_zero _ _ _, ?_⟩
    simp only [integral_zero, pow_zero, mul_one, Nat.cast_zero, mul_zero, add_zero]
    have := sub_nonneg.mpr (hM.lower x)
    positivity
  | succ K ih =>
    have hmp : Measurable (gradLoss f g η (K + 1) x) :=
      (measurable_gradLoss hM.lip hM.meas η (K + 1)).of_uncurry_left
    let q := Measure.pi (fun _ : Fin K => p)
    let F := fun z : Ω × (Fin K → Ω) =>
      ‖gradient f x‖ ^ 2 + gradLoss f g η K (x - η • g x z.1) z.2
    let Bd := fun ω => ‖gradient f x‖ ^ 2 + (2 / η * ρ ^ K * (f (x - η • g x ω) - fstar) +
      L * η * C * K * ρ ^ K)
    have hstep := one_step hM hL hη.le hηL x
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
    have hfx : 0 ≤ f x - fstar := sub_nonneg.mpr (hM.lower x)
    have hρK : 1 ≤ ρ ^ K := one_le_pow₀ hρ
    calc
      _ = ∫ z, F z ∂p.prod q := by
        rw [← hcons.map_eq, integral_map hcons.measurable.aemeasurable hmp.aestronglyMeasurable]
        rw [heq]
      _ = ∫ ω, ∫ ξ, F (ω, ξ) ∂q ∂p := integral_prod F hFi
      _ ≤ ∫ ω, Bd ω ∂p := integral_mono hFi.integral_prod_left hBd hbound
      _ = ‖gradient f x‖ ^ 2 + (2 / η * ρ ^ K * ∫ ω, f (x - η • g x ω) - fstar ∂p +
            L * η * C * K * ρ ^ K) := by
        have hA1 : Integrable (fun ω => 2 / η * ρ ^ K * (f (x - η • g x ω) - fstar)) p :=
          hstep.1.const_mul _
        have hA2 : Integrable (fun ω => 2 / η * ρ ^ K * (f (x - η • g x ω) - fstar) +
            L * η * C * K * ρ ^ K) p := hA1.add (integrable_const _)
        dsimp only [Bd]
        rw [integral_add (integrable_const _) hA2, integral_add hA1 (integrable_const _),
          integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
      _ ≤ _ := by
        have h2 := hstep.2
        rw [show (1 + L * A * η ^ 2) = ρ from rfl] at h2
        have hk : 0 ≤ 2 / η * ρ ^ K := by positivity
        have h3 := mul_le_mul_of_nonneg_left h2 hk
        have hηinv : 2 / η * ρ ^ K * (η / 2 * ‖gradient f x‖ ^ 2) = ρ ^ K * ‖gradient f x‖ ^ 2 := by
          field_simp
        have hηinv2 : 2 / η * ρ ^ K * (L * η ^ 2 * C / 2) = L * η * C * ρ ^ K := by
          field_simp
        have hpow : ρ ^ (K + 1) = ρ ^ K * ρ := pow_succ ρ K
        rw [hpow]
        push_cast
        have hC' : 0 ≤ L * η * C := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hρK (sq_nonneg ‖gradient f x‖),
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by linarith) hρ : ρ ^ K ≤ ρ ^ K * ρ)
            (by positivity : (0 : ℝ) ≤ L * η * C * ((K : ℝ) + 1)),
          mul_nonneg hC' (by positivity : (0 : ℝ) ≤ ρ ^ K)]

lemma iid_prefix_law {p : Measure Ω} {P : Measure (ℕ → Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (K : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun i : Fin K => ξ i) P (Measure.pi fun _ : Fin K => p) := by
  refine ⟨by fun_prop, ?_⟩
  have hi := h.independent.precomp (g := fun i : Fin K => (i : ℕ)) Fin.val_injective
  have hp := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i : Fin K => (h.measurable (i : ℕ)).aemeasurable)).mp hi
  simpa only [h.marginal] using hp

end LongTails.Proofs.AbcSgdRate
