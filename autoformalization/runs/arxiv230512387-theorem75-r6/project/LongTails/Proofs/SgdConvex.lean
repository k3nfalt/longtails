import LongTails.Algorithms.Sgd
import LongTails.Setups.StochasticSmoothAndConvex
import LongTails.Proofs.GdConvex
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticGradient

open LongTails.Setups.StochasticSmoothAndConvex

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma deterministic_step {f : E → ℝ} {L η : ℝ} {xstar : E}
    (hL : 0 < L) (hη : 0 ≤ η) (hηL : η * L ≤ 1 / 2)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hm : IsMinOn f univ xstar) (x : E) :
    ‖x - η • gradient f x - xstar‖ ^ 2 + η * (f x - f xstar) ≤ ‖x - xstar‖ ^ 2 := by
  have hd := Gradient.descent hL hg hlip x
  have hmin := hm (by trivial : x - (1 / L) • gradient f x ∈ univ)
  change f xstar ≤ f (x - (1 / L) • gradient f x) at hmin
  have hgrad : ‖gradient f x‖ ^ 2 ≤ 2 * L * (f x - f xstar) := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp
      (show ‖gradient f x‖ ^ 2 / (2 * L) ≤ f x - f xstar by linarith)
    nlinarith
  have hs := Gradient.convex_support hc hg x xstar
  have hi : ⟪x - xstar, gradient f x⟫ = -⟪gradient f x, xstar - x⟫ := by
    rw [real_inner_comm, ← inner_neg_right]
    congr 1
    module
  rw [show x - η • gradient f x - xstar = (x - xstar) - η • gradient f x by module,
    norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right, hi]
  have hp := mul_le_mul_of_nonneg_left hgrad (sq_nonneg η)
  have hgap := hm (by trivial : x ∈ univ)
  change f xstar ≤ f x at hgap
  have hcoef : 2 * L * η ^ 2 ≤ η := by nlinarith
  have := mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hgap)
  nlinarith [mul_le_mul_of_nonneg_left hs hη]

omit [BorelSpace E] [SecondCountableTopology E] in
lemma stochastic_step {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L σ η : ℝ} {xstar : E}
    (hL : 0 < L) (hη : 0 ≤ η) (hηL : η * L ≤ 1 / 2)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hm : IsMinOn f univ xstar) (ho : IsStochasticGradient E Ω p f g σ) (x : E) :
    Integrable (fun ω => ‖x - η • g x ω - xstar‖ ^ 2) p ∧
    (∫ ω, ‖x - η • g x ω - xstar‖ ^ 2 ∂p) + η * (f x - f xstar) ≤
      ‖x - xstar‖ ^ 2 + η ^ 2 * σ ^ 2 := by
  let v := x - η • gradient f x - xstar
  let noise := fun ω => g x ω - gradient f x
  have hn : Integrable noise p := (ho.integrable x).sub (integrable_const _)
  have hz : (∫ ω, noise ω ∂p) = 0 := by
    rw [integral_sub (ho.integrable x) (integrable_const _), ho.unbiased, integral_const]
    simp
  have he : (fun ω => ‖x - η • g x ω - xstar‖ ^ 2) =
      fun ω => ‖v‖ ^ 2 - 2 * η * ⟪v, noise ω⟫ + η ^ 2 * ‖noise ω‖ ^ 2 := by
    funext ω
    have h : x - η • g x ω - xstar = v - η • noise ω := by dsimp [v, noise]; module
    rw [h, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      inner_smul_right]
    ring
  have hi1 : Integrable (fun ω => ‖v‖ ^ 2 - 2 * η * ⟪v, noise ω⟫) p :=
    (integrable_const _).sub ((hn.const_inner v).const_mul _)
  have hi2 : Integrable (fun ω => η ^ 2 * ‖noise ω‖ ^ 2) p :=
    (ho.variance_integrable x).const_mul _
  rw [he]
  refine ⟨hi1.add hi2, ?_⟩
  rw [integral_add hi1 hi2,
    integral_sub (integrable_const (‖v‖ ^ 2)) ((hn.const_inner v).const_mul (2 * η)),
    integral_const_mul, integral_const_mul, integral_inner hn, hz]
  simp only [inner_zero_right, mul_zero, sub_zero, integral_const, probReal_univ, one_smul]
  have hv := mul_le_mul_of_nonneg_left (ho.variance x) (sq_nonneg η)
  have hd := deterministic_step hL hη hηL hc hg hlip hm x
  dsimp [v, noise] at *
  linarith

noncomputable def loss (f : E → ℝ) (g : E → Ω → E) (η : ℝ) (xstar : E) :
    (K : ℕ) → E → (Fin K → Ω) → ℝ
  | 0, _, _ => 0
  | K + 1, x, ξ => f x - f xstar + loss f g η xstar K
      (x - η • g x (ξ 0)) (fun i => ξ i.succ)

noncomputable def potential (f : E → ℝ) (g : E → Ω → E) (η : ℝ) (xstar : E)
    (K : ℕ) (x : E) (ξ : Fin K → Ω) : ℝ :=
  ‖(run g η K x ξ).1 - xstar‖ ^ 2 + η * loss f g η xstar K x ξ

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma potential_succ (f : E → ℝ) (g : E → Ω → E) (η : ℝ) (xstar : E)
    (K : ℕ) (x : E) (ξ : Fin (K + 1) → Ω) :
    potential f g η xstar (K + 1) x ξ =
      potential f g η xstar K (x - η • g x (ξ 0)) (fun i => ξ i.succ) +
        η * (f x - f xstar) := by
  simp only [potential, run, loss]
  ring

omit [CompleteSpace E] in
lemma measurable_run {g : E → Ω → E} (h : Measurable (Function.uncurry g)) (η : ℝ) (K : ℕ) :
    Measurable (fun z : E × (Fin K → Ω) => run g η K z.1 z.2) := by
  induction K with
  | zero => exact measurable_fst.prodMk measurable_const
  | succ K ih =>
    have ht : Measurable (fun z : E × (Fin (K + 1) → Ω) =>
        (z.1 - η • g z.1 (z.2 0), fun i : Fin K => z.2 i.succ)) := by
      have hg : Measurable (fun z : E × (Fin (K + 1) → Ω) => g z.1 (z.2 0)) := h.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
      exact (measurable_fst.sub (hg.const_smul η)).prodMk (by fun_prop)
    exact (ih.comp ht).fst.prodMk (measurable_fst.add (ih.comp ht).snd)

omit [CompleteSpace E] in
lemma measurable_loss {f : E → ℝ} {g : E → Ω → E} (hf : Measurable f)
    (h : Measurable (Function.uncurry g)) (η : ℝ) (xstar : E) (K : ℕ) :
    Measurable (fun z : E × (Fin K → Ω) => loss f g η xstar K z.1 z.2) := by
  induction K with
  | zero => exact measurable_const
  | succ K ih =>
    have ht : Measurable (fun z : E × (Fin (K + 1) → Ω) =>
        (z.1 - η • g z.1 (z.2 0), fun i : Fin K => z.2 i.succ)) := by
      have hg : Measurable (fun z : E × (Fin (K + 1) → Ω) => g z.1 (z.2 0)) := h.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
      exact (measurable_fst.sub (hg.const_smul η)).prodMk (by fun_prop)
    exact ((hf.comp measurable_fst).sub_const _).add (ih.comp ht)

omit [CompleteSpace E] in
lemma measurable_potential {f : E → ℝ} {g : E → Ω → E} (hf : Measurable f)
    (h : Measurable (Function.uncurry g)) (η : ℝ) (xstar : E) (K : ℕ) :
    Measurable (fun z : E × (Fin K → Ω) => potential f g η xstar K z.1 z.2) :=
  (((measurable_run h η K).fst.sub_const xstar).norm.pow_const 2).add
    ((measurable_loss hf h η xstar K).const_mul η)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma loss_nonneg {f : E → ℝ} (g : E → Ω → E) (η : ℝ) {xstar : E}
    (hm : IsMinOn f univ xstar) (K : ℕ) (x : E) (ξ : Fin K → Ω) :
    0 ≤ loss f g η xstar K x ξ := by
  induction K generalizing x with
  | zero => exact le_rfl
  | succ K ih => exact add_nonneg (sub_nonneg.mpr (hm (by trivial))) (ih _ _)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma potential_nonneg {f : E → ℝ} (g : E → Ω → E) {η : ℝ} (hη : 0 ≤ η)
    {xstar : E} (hm : IsMinOn f univ xstar) (K : ℕ) (x : E) (ξ : Fin K → Ω) :
    0 ≤ potential f g η xstar K x ξ :=
  add_nonneg (sq_nonneg _) (mul_nonneg hη (loss_nonneg g η hm K x ξ))

lemma cons_measurePreserving (p : Measure Ω) [IsProbabilityMeasure p] (K : ℕ) :
    MeasurePreserving (fun z : Ω × (Fin K → Ω) => Fin.cons z.1 z.2)
      (p.prod (Measure.pi fun _ : Fin K => p)) (Measure.pi fun _ : Fin (K + 1) => p) := by
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero,
    Fin.zero_succAbove] using (measurePreserving_piFinSuccAbove (fun _ : Fin (K + 1) => p) 0).symm

lemma potential_bound {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L σ η : ℝ} {xstar : E}
    (hL : 0 < L) (hη : 0 ≤ η) (hηL : η * L ≤ 1 / 2)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hm : IsMinOn f univ xstar) (ho : IsStochasticGradient E Ω p f g σ) (K : ℕ) (x : E) :
    Integrable (potential f g η xstar K x) (Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, potential f g η xstar K x ξ ∂Measure.pi (fun _ : Fin K => p)) ≤
      ‖x - xstar‖ ^ 2 + K * η ^ 2 * σ ^ 2 := by
  have hf : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hg x).continuousAt)).measurable
  induction K generalizing x with
  | zero => simp [potential, run, loss]
  | succ K ih =>
    have hmp : Measurable (potential f g η xstar (K + 1) x) :=
      (measurable_potential (f := f) (g := g) hf ho.measurable η xstar (K + 1)).of_uncurry_left
    let q := Measure.pi (fun _ : Fin K => p)
    let F := fun z : Ω × (Fin K → Ω) =>
      potential f g η xstar K (x - η • g x z.1) z.2 + η * (f x - f xstar)
    let B := fun ω => ‖x - η • g x ω - xstar‖ ^ 2 + K * η ^ 2 * σ ^ 2 + η * (f x - f xstar)
    have hstep := stochastic_step hL hη hηL hc hg hlip hm ho x
    have hB : Integrable B p := (hstep.1.add (integrable_const _)).add (integrable_const _)
    have hF : Measurable F := by
      have hx : Measurable (fun z : Ω × (Fin K → Ω) => x - η • g x z.1) :=
        measurable_const.sub ((ho.measurable.comp (measurable_const.prodMk measurable_fst)).const_smul η)
      exact ((measurable_potential hf ho.measurable η xstar K).comp
        (hx.prodMk measurable_snd)).add_const _
    have hnonneg : ∀ z, 0 ≤ F z := fun z => add_nonneg
      (potential_nonneg g hη hm K _ _) (mul_nonneg hη (sub_nonneg.mpr (hm (by trivial))))
    have hsection : ∀ ω, Integrable (fun ξ => F (ω, ξ)) q :=
      fun ω => (ih (x - η • g x ω)).1.add (integrable_const _)
    have hbound : ∀ ω, (∫ ξ, F (ω, ξ) ∂q) ≤ B ω := by
      intro ω
      dsimp [F, B]
      rw [integral_add (ih _).1 (integrable_const _)]
      simpa using add_le_add_right (ih (x - η • g x ω)).2 (η * (f x - f xstar))
    have hint : Integrable (fun ω => ∫ ξ, ‖F (ω, ξ)‖ ∂q) p := by
      apply hB.mono_nonneg hF.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun ω => integral_nonneg (fun ξ => norm_nonneg _))
      · apply Filter.Eventually.of_forall
        intro ω
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] using hbound ω
    have hFi : Integrable F (p.prod q) := (integrable_prod_iff hF.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hsection, hint⟩
    have heq : (fun z : Ω × (Fin K → Ω) =>
        potential f g η xstar (K + 1) x (Fin.cons z.1 z.2)) = F := by
      funext z
      simp only [potential_succ, Fin.cons_zero, Fin.cons_succ, F]
    have hcons := cons_measurePreserving p K
    have hpi : Integrable (potential f g η xstar (K + 1) x)
        (Measure.pi (fun _ : Fin (K + 1) => p)) :=
      (hcons.integrable_comp hmp.aestronglyMeasurable).mp (by
        simpa only [Function.comp_def, heq] using hFi)
    refine ⟨hpi, ?_⟩
    calc
      _ = ∫ z, F z ∂p.prod q := by
        rw [← hcons.map_eq, integral_map hcons.measurable.aemeasurable hmp.aestronglyMeasurable]
        rw [heq]
      _ = ∫ ω, ∫ ξ, F (ω, ξ) ∂q ∂p := integral_prod F hFi
      _ ≤ ∫ ω, B ω ∂p := integral_mono hFi.integral_prod_left hB hbound
      _ ≤ ‖x - xstar‖ ^ 2 + (K + 1 : ℕ) * η ^ 2 * σ ^ 2 := by
        dsimp [B]
        have hi : Integrable (fun ω => ‖x - η • g x ω - xstar‖ ^ 2 +
            (K : ℝ) * η ^ 2 * σ ^ 2) p := hstep.1.add (integrable_const _)
        have he := integral_add hi (integrable_const (η * (f x - f xstar)))
        rw [he, integral_add hstep.1 (integrable_const ((K : ℝ) * η ^ 2 * σ ^ 2))]
        simp only [integral_const, probReal_univ, one_smul, Nat.cast_add, Nat.cast_one]
        nlinarith [hstep.2]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma sum_support {f : E → ℝ} (g : E → Ω → E) (η : ℝ) (xstar : E)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (K : ℕ) (x v : E) (ξ : Fin K → Ω) :
    ⟪gradient f v, (run g η K x ξ).2 - (K : ℝ) • v⟫ ≤
      loss f g η xstar K x ξ - K * (f v - f xstar) := by
  induction K generalizing x with
  | zero => simp [run, loss]
  | succ K ih =>
    have hs := Gradient.convex_support hc hg v x
    have hi := ih (x - η • g x (ξ 0)) (fun i => ξ i.succ)
    simp only [run, loss, Nat.cast_add, Nat.cast_one]
    rw [show x + (run g η K (x - η • g x (ξ 0)) (fun i => ξ i.succ)).2 -
        ((K : ℝ) + 1) • v =
        (x - v) + ((run g η K (x - η • g x (ξ 0)) (fun i => ξ i.succ)).2 - (K : ℝ) • v) by module,
      inner_add_right]
    linarith

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma average_bound {f : E → ℝ} (g : E → Ω → E) (η : ℝ) (xstar : E)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (K : ℕ) (hK : 0 < K) (x : E) (ξ : Fin K → Ω) :
    (K : ℝ) * (f ((K : ℝ)⁻¹ • (run g η K x ξ).2) - f xstar) ≤
      loss f g η xstar K x ξ := by
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have h := sum_support g η xstar hc hg K x ((K : ℝ)⁻¹ • (run g η K x ξ).2) ξ
  simp only [smul_smul, mul_inv_cancel₀ hKr, one_smul, sub_self, inner_zero_right] at h
  linarith

lemma expected_average {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L σ η : ℝ} {xstar : E}
    (hL : 0 < L) (hη : 0 < η) (hηL : η * L ≤ 1 / 2)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hm : IsMinOn f univ xstar) (ho : IsStochasticGradient E Ω p f g σ)
    (K : ℕ) (hK : 0 < K) (x : E) :
    Integrable (fun ξ => f ((K : ℝ)⁻¹ • (run g η K x ξ).2) - f xstar)
      (Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, f ((K : ℝ)⁻¹ • (run g η K x ξ).2) - f xstar ∂Measure.pi (fun _ : Fin K => p)) ≤
      ‖x - xstar‖ ^ 2 / (η * K) + η * σ ^ 2 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hpos : 0 < η * (K : ℝ) := mul_pos hη hKr
  have hf : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hg x).continuousAt)).measurable
  have hr : Measurable (fun ξ : Fin K → Ω => (K : ℝ)⁻¹ • (run g η K x ξ).2) :=
    (((measurable_run ho.measurable η K).comp
      (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin K → Ω => (x, ξ)))).snd).const_smul _
  have hp := potential_bound hL hη.le hηL hc hg hlip hm ho K x
  have hpoint : ∀ ξ, f ((K : ℝ)⁻¹ • (run g η K x ξ).2) - f xstar ≤
      (η * K)⁻¹ * potential f g η xstar K x ξ := by
    intro ξ
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hpos).mpr
    have h := mul_le_mul_of_nonneg_left (average_bound g η xstar hc hg K hK x ξ) hη.le
    dsimp [potential]
    nlinarith [sq_nonneg ‖(run g η K x ξ).1 - xstar‖]
  have hi : Integrable (fun ξ => f ((K : ℝ)⁻¹ • (run g η K x ξ).2) - f xstar)
      (Measure.pi fun _ : Fin K => p) :=
    (hp.1.const_mul ((η * K)⁻¹)).mono_nonneg ((hf.comp hr).sub_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => sub_nonneg.mpr (hm (by trivial))))
      (Filter.Eventually.of_forall hpoint)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ξ, (η * K)⁻¹ * potential f g η xstar K x ξ ∂Measure.pi (fun _ : Fin K => p) :=
      integral_mono hi (hp.1.const_mul _) hpoint
    _ = (η * K)⁻¹ * ∫ ξ, potential f g η xstar K x ξ ∂Measure.pi (fun _ : Fin K => p) :=
      integral_const_mul _ _
    _ ≤ (η * K)⁻¹ * (‖x - xstar‖ ^ 2 + K * η ^ 2 * σ ^ 2) :=
      mul_le_mul_of_nonneg_left hp.2 (inv_nonneg.mpr hpos.le)
    _ = _ := by field_simp

lemma prefix_measurePreserving (p : Measure Ω) [IsProbabilityMeasure p] (K : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun i : Fin K => ξ i)
      (Measure.infinitePi fun _ : ℕ => p) (Measure.pi fun _ : Fin K => p) := by
  refine ⟨by fun_prop, ?_⟩
  have hi : ProbabilityTheory.iIndepFun (fun k : ℕ => fun ξ : ℕ → Ω => ξ k)
      (Measure.infinitePi fun _ : ℕ => p) :=
    ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)
  have hp := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i : Fin K => (measurable_pi_apply (i : ℕ)).aemeasurable)).mp
      (hi.precomp (g := fun i : Fin K => (i : ℕ)) Fin.val_injective)
  simpa only [Measure.infinitePi_map_eval] using hp

end OracleTemplate.StochasticGradient
