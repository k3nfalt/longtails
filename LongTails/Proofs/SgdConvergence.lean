import LongTails.Proofs.SgdStep
import LongTails.Algorithms.RandomSgd
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.StochasticNonconvex

open LongTails.Setups.StochasticSmoothNonconvex

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

noncomputable def energy (f : E → ℝ) (g : E → Ω → E) (η lower : ℝ) :
    (K : ℕ) → E → (Fin K → Ω) → ℝ
  | 0, x, _ => f x - lower
  | K + 1, x, ξ => η / 2 * ‖gradient f x‖ ^ 2 +
      energy f g η lower K (x - η • g x (ξ 0)) (fun i => ξ i.succ)

noncomputable def cost (f : E → ℝ) (g : E → Ω → E) (η : ℝ) :
    (K : ℕ) → E → (Fin K → Ω) → ℝ
  | 0, _, _ => 0
  | K + 1, x, ξ => ‖gradient f x‖ ^ 2 +
      cost f g η K (x - η • g x (ξ 0)) (fun i => ξ i.succ)

lemma measurable_energy {f : E → ℝ} {g : E → Ω → E}
    (hf : Measurable f) (hd : Measurable (gradient f)) (ho : Measurable (Function.uncurry g))
    (η lower : ℝ) (K : ℕ) :
    Measurable (fun z : E × (Fin K → Ω) => energy f g η lower K z.1 z.2) := by
  induction K with
  | zero => exact (hf.comp measurable_fst).sub_const _
  | succ K ih =>
    have ht : Measurable (fun z : E × (Fin (K + 1) → Ω) =>
        (z.1 - η • g z.1 (z.2 0), fun i : Fin K => z.2 i.succ)) := by
      have hh : Measurable (fun z : E × (Fin (K + 1) → Ω) => g z.1 (z.2 0)) :=
        ho.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
      exact (measurable_fst.sub (hh.const_smul η)).prodMk (by fun_prop)
    exact (((hd.comp measurable_fst).norm.pow_const 2).const_mul _).add (ih.comp ht)

lemma measurable_cost {f : E → ℝ} {g : E → Ω → E}
    (hd : Measurable (gradient f)) (ho : Measurable (Function.uncurry g)) (η : ℝ) (K : ℕ) :
    Measurable (fun z : E × (Fin K → Ω) => cost f g η K z.1 z.2) := by
  induction K with
  | zero => exact measurable_const
  | succ K ih =>
    have ht : Measurable (fun z : E × (Fin (K + 1) → Ω) =>
        (z.1 - η • g z.1 (z.2 0), fun i : Fin K => z.2 i.succ)) := by
      have hh : Measurable (fun z : E × (Fin (K + 1) → Ω) => g z.1 (z.2 0)) :=
        ho.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
      exact (measurable_fst.sub (hh.const_smul η)).prodMk (by fun_prop)
    exact ((hd.comp measurable_fst).norm.pow_const 2).add (ih.comp ht)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma cost_nonneg (f : E → ℝ) (g : E → Ω → E) (η : ℝ) (K : ℕ) (x : E) (ξ) :
    0 ≤ cost f g η K x ξ := by
  induction K generalizing x with
  | zero => exact le_rfl
  | succ K ih => exact add_nonneg (sq_nonneg _) (ih _ _)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma cost_le_energy {f : E → ℝ} (g : E → Ω → E) (η lower : ℝ)
    (hb : ∀ x, lower ≤ f x) (K : ℕ) (x : E) (ξ) :
    η / 2 * cost f g η K x ξ ≤ energy f g η lower K x ξ := by
  induction K generalizing x with
  | zero => simpa [energy, cost] using hb x
  | succ K ih =>
    simp only [energy, cost, mul_add]
    exact add_le_add le_rfl (ih _ _)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma energy_nonneg {f : E → ℝ} (g : E → Ω → E) {η lower : ℝ}
    (hη : 0 ≤ η) (hb : ∀ x, lower ≤ f x) (K : ℕ) (x : E) (ξ) :
    0 ≤ energy f g η lower K x ξ :=
  (mul_nonneg (by positivity) (cost_nonneg f g η K x ξ)).trans
    (cost_le_energy g η lower hb K x ξ)

set_option maxHeartbeats 800000 in
lemma expected_energy {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L σ η lower : ℝ}
    (hL : 0 < L) (hη : 0 ≤ η) (hηL : η * L ≤ 1)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hb : ∀ x, lower ≤ f x) (ho : StochasticGradient E Ω p f g σ) (K : ℕ) (x : E) :
    Integrable (energy f g η lower K x) (Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, energy f g η lower K x ξ ∂Measure.pi (fun _ : Fin K => p)) ≤
      f x - lower + K * (L * η ^ 2 / 2 * σ ^ 2) := by
  have hf : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)).measurable
  have hd := gradient_measurable hL.le hlip
  induction K generalizing x with
  | zero => simp [energy]
  | succ K ih =>
    let q := Measure.pi (fun _ : Fin K => p)
    let c := η / 2 * ‖gradient f x‖ ^ 2
    let F := fun z : Ω × (Fin K → Ω) =>
      c + energy f g η lower K (x - η • g x z.1) z.2
    let B := fun ω => c + (f (x - η • g x ω) - lower) + K * (L * η ^ 2 / 2 * σ ^ 2)
    have hstep := expected_step hL hη hηL hg hlip hb ho x
    have hB : Integrable B p := ((integrable_const c).add hstep.1).add (integrable_const _)
    have hF : Measurable F := by
      have hx : Measurable (fun z : Ω × (Fin K → Ω) => x - η • g x z.1) :=
        measurable_const.sub ((ho.measurable.comp (measurable_const.prodMk measurable_fst)).const_smul η)
      exact ((measurable_energy hf hd ho.measurable η lower K).comp
        (hx.prodMk measurable_snd)).const_add c
    have hn (z) : 0 ≤ F z :=
      add_nonneg (by dsimp [c]; positivity) (energy_nonneg g hη hb K _ _)
    have hsection (ω) : Integrable (fun ξ => F (ω, ξ)) q := by
      dsimp [F, q]
      exact (integrable_const c).add (ih (x - η • g x ω)).1
    have hbound (ω) : (∫ ξ, F (ω, ξ) ∂q) ≤ B ω := by
      dsimp [F, B]
      rw [integral_add (integrable_const c) (ih _).1]
      simpa only [q, integral_const, probReal_univ, one_smul, add_assoc] using
        (add_le_add (le_refl c) (ih (x - η • g x ω)).2)
    have hint : Integrable (fun ω => ∫ ξ, ‖F (ω, ξ)‖ ∂q) p := by
      apply hB.mono_nonneg hF.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun ω => integral_nonneg (fun ξ => norm_nonneg _))
      · exact Filter.Eventually.of_forall (fun ω => by
          simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _)] using hbound ω)
    have hFi : Integrable F (p.prod q) :=
      (integrable_prod_iff hF.aestronglyMeasurable).mpr ⟨Filter.Eventually.of_forall hsection, hint⟩
    have hcons : MeasurePreserving (fun z : Ω × (Fin K → Ω) => Fin.cons z.1 z.2)
        (p.prod q) (Measure.pi fun _ : Fin (K + 1) => p) := by
      simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero,
        Fin.zero_succAbove, q] using
        (measurePreserving_piFinSuccAbove (fun _ : Fin (K + 1) => p) 0).symm
    have hall : Measurable (Function.uncurry (energy f g η lower (K + 1))) :=
      measurable_energy hf hd ho.measurable η lower (K + 1)
    have hm : Measurable (energy f g η lower (K + 1) x) := hall.of_uncurry_left
    have heq : (fun z : Ω × (Fin K → Ω) =>
        energy f g η lower (K + 1) x (Fin.cons z.1 z.2)) = F := by
      funext z
      simp [energy, F, c]
    refine ⟨(hcons.integrable_comp hm.aestronglyMeasurable).mp
      (by simpa only [Function.comp_def, heq] using hFi), ?_⟩
    calc
      _ = ∫ z, F z ∂p.prod q := by
        rw [← hcons.map_eq, integral_map hcons.measurable.aemeasurable hm.aestronglyMeasurable, heq]
      _ = ∫ ω, ∫ ξ, F (ω, ξ) ∂q ∂p := integral_prod F hFi
      _ ≤ ∫ ω, B ω ∂p := integral_mono hFi.integral_prod_left hB hbound
      _ ≤ f x - lower + (K + 1 : ℕ) * (L * η ^ 2 / 2 * σ ^ 2) := by
        dsimp [B]
        have hB1 : Integrable (fun ω => c + (f (x - η • g x ω) - lower)) p :=
          (integrable_const c).add hstep.1
        rw [integral_add hB1 (integrable_const ((K : ℝ) * (L * η ^ 2 / 2 * σ ^ 2))),
          integral_add (integrable_const c) hstep.1]
        simp only [integral_const, probReal_univ, one_smul, Nat.cast_add, Nat.cast_one]
        dsimp [c]
        nlinarith [hstep.2]

lemma expected_cost {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L σ η lower : ℝ}
    (hL : 0 < L) (hη : 0 < η) (hηL : η * L ≤ 1)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hb : ∀ x, lower ≤ f x) (ho : StochasticGradient E Ω p f g σ) (K : ℕ) (x : E) :
    Integrable (cost f g η K x) (Measure.pi fun _ : Fin K => p) ∧
    η / 2 * (∫ ξ, cost f g η K x ξ ∂Measure.pi (fun _ : Fin K => p)) ≤
      f x - lower + K * (L * η ^ 2 / 2 * σ ^ 2) := by
  have h := expected_energy hL hη.le hηL hg hlip hb ho K x
  have hall : Measurable (Function.uncurry (cost f g η K)) :=
    measurable_cost (gradient_measurable hL.le hlip) ho.measurable η K
  have hm : Measurable (cost f g η K x) := hall.of_uncurry_left
  have hi : Integrable (fun ξ => η / 2 * cost f g η K x ξ) (Measure.pi fun _ : Fin K => p) :=
    h.1.mono_nonneg (hm.const_mul _).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => mul_nonneg (by positivity) (cost_nonneg f g η K x ξ)))
      (Filter.Eventually.of_forall (cost_le_energy g η lower hb K x))
  refine ⟨(integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (by positivity : η / 2 ≠ 0)) _).mp hi, ?_⟩
  have hb' := integral_mono hi h.1 (cost_le_energy g η lower hb K x)
  rw [integral_const_mul] at hb'
  exact hb'.trans h.2

end OracleTemplate.StochasticNonconvex
