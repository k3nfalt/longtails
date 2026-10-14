import LongTails.Algorithms.AcceleratedStochastic
import LongTails.Proofs.AcceleratedConvex
import LongTails.Proofs.SgdConvex

open Set InnerProductSpace MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticGradient

open LongTails.Setups.StochasticSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma inexact_descent {f : E → ℝ} {L D : ℝ}
    (hD : 0 < D) (hLD : 2 * L ≤ D)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (y g : E) :
    f (y - (1 / D) • g) ≤ f y - ‖g‖ ^ 2 / (2 * D) +
      ‖g - gradient f y‖ ^ 2 / D := by
  have hd := Gradient.smooth_upper_bound hg hlip y (y - (1 / D) • g)
  have he : y - (1 / D) • g - y = -(1 / D) • g := by module
  rw [he] at hd
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg,
    mul_pow, sq_abs] at hd
  have hn := sq_nonneg ‖g - (2 : ℝ) • (g - gradient f y)‖
  rw [norm_sub_sq_real] at hn
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_sub_right, real_inner_self_eq_norm_sq] at hn
  rw [← real_inner_comm g (gradient f y)] at hn
  have hcoef := mul_le_mul_of_nonneg_right hLD (sq_nonneg ‖g‖)
  have hD0 := hD.ne'
  field_simp at hd ⊢
  nlinarith

lemma accelerated_inexact_step {f : E → ℝ} {L D : ℝ}
    (hD : 0 < D) (hLD : 2 * L ≤ D) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x z u g : E) {A a : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hB : 0 < A + a) (haB : a ^ 2 ≤ A + a) :
    let y := (A / (A + a)) • x + (a / (A + a)) • z
    (A + a) * (f (y - (1 / D) • g) - f u) +
        D / 2 * ‖z - (a / D) • g - u‖ ^ 2 ≤
      A * (f x - f u) + D / 2 * ‖z - u‖ ^ 2 -
        a * ⟪g - gradient f y, z - u⟫ + (A + a) / D * ‖g - gradient f y‖ ^ 2 := by
  dsimp only
  let y := (A / (A + a)) • x + (a / (A + a)) • z
  have hx := Gradient.convex_support hc hg y x
  have hu := Gradient.convex_support hc hg y u
  have hid : A • (x - y) + a • (u - y) = a • (u - z) := by
    dsimp [y]
    match_scalars
    all_goals field_simp [hB.ne'] <;> ring
  have hi := congrArg (fun v => ⟪gradient f y, v⟫) hid
  simp only [inner_add_right, inner_smul_right] at hi
  have hw : (A + a) * (f y - f u) ≤
      A * (f x - f u) + a * ⟪gradient f y, z - u⟫ := by
    have hx' := mul_le_mul_of_nonneg_left hx hA
    have hu' := mul_le_mul_of_nonneg_left hu ha
    rw [show u - z = -(z - u) by module, inner_neg_right] at hi
    nlinarith
  have hd0 := inexact_descent hD hLD hg hlip y g
  have hD0 := hD.ne'
  field_simp at hd0
  have hd := mul_le_mul_of_nonneg_left hd0 hB.le
  have hw' := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2 * D by positivity)
  have hn : z - (a / D) • g - u = (z - u) - (a / D) • g := by module
  change (A + a) * (f (y - (1 / D) • g) - f u) +
    D / 2 * ‖z - (a / D) • g - u‖ ^ 2 ≤
      A * (f x - f u) + D / 2 * ‖z - u‖ ^ 2 -
        a * ⟪g - gradient f y, z - u⟫ + (A + a) / D * ‖g - gradient f y‖ ^ 2
  rw [hn, norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← real_inner_comm (z - u) g, inner_sub_left]
  have hcoef := mul_le_mul_of_nonneg_right haB (sq_nonneg ‖g‖)
  field_simp
  nlinarith only [hd, hw', hcoef]

variable {Ω : Type} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]

lemma accelerated_stochastic_step {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L D σ : ℝ}
    (hD : 0 < D) (hLD : 2 * L ≤ D) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : IsStochasticGradient E Ω p f g σ)
    (x z u : E) (hm : IsMinOn f univ u)
    {A a : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hB : 0 < A + a) (haB : a ^ 2 ≤ A + a) :
    let y := (A / (A + a)) • x + (a / (A + a)) • z
    let F := fun ω => (A + a) * (f (y - (1 / D) • g y ω) - f u) +
      D / 2 * ‖z - (a / D) • g y ω - u‖ ^ 2
    Integrable F p ∧ (∫ ω, F ω ∂p) ≤
      A * (f x - f u) + D / 2 * ‖z - u‖ ^ 2 + (A + a) / D * σ ^ 2 := by
  dsimp only
  let y := (A / (A + a)) • x + (a / (A + a)) • z
  let noise := fun ω => g y ω - gradient f y
  let C := A * (f x - f u) + D / 2 * ‖z - u‖ ^ 2
  let F := fun ω => (A + a) * (f (y - (1 / D) • g y ω) - f u) +
    D / 2 * ‖z - (a / D) • g y ω - u‖ ^ 2
  let B := fun ω => C - a * ⟪z - u, noise ω⟫ + (A + a) / D * ‖noise ω‖ ^ 2
  have hn : Integrable noise p := (ho.integrable y).sub (integrable_const _)
  have hz : (∫ ω, noise ω ∂p) = 0 := by
    rw [integral_sub (ho.integrable y) (integrable_const _), ho.unbiased]
    simp
  have hi1 : Integrable (fun ω => C - a * ⟪z - u, noise ω⟫) p :=
    (integrable_const _).sub ((hn.const_inner (z - u)).const_mul a)
  have hi2 : Integrable (fun ω => (A + a) / D * ‖noise ω‖ ^ 2) p :=
    (ho.variance_integrable y).const_mul _
  have hBint : Integrable B p := hi1.add hi2
  have hbound : ∀ ω, F ω ≤ B ω := by
    intro ω
    have h := accelerated_inexact_step hD hLD hc hg hlip x z u (g y ω) hA ha hB haB
    simpa only [F, B, C, noise, real_inner_comm] using h
  have hf : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hg x).continuousAt)).measurable
  have hgm : Measurable (g y) := ho.measurable.comp (measurable_const.prodMk measurable_id)
  have hFm : Measurable F :=
    (((hf.comp (measurable_const.sub (hgm.const_smul (1 / D)))).sub_const _).const_mul _).add
      ((((measurable_const.sub (hgm.const_smul (a / D))).sub_const u).norm.pow_const 2).const_mul _)
  have hpos : ∀ ω, 0 ≤ F ω := by
    intro ω
    dsimp [F]
    have : 0 ≤ f (y - (1 / D) • g y ω) - f u := sub_nonneg.mpr (hm (by trivial))
    positivity
  have hFi : Integrable F p := hBint.mono_nonneg hFm.aestronglyMeasurable
    (Filter.Eventually.of_forall hpos) (Filter.Eventually.of_forall hbound)
  refine ⟨hFi, (integral_mono hFi hBint hbound).trans ?_⟩
  change (∫ ω, (C - a * ⟪z - u, noise ω⟫) + (A + a) / D * ‖noise ω‖ ^ 2 ∂p) ≤ _
  rw [integral_add hi1 hi2,
    integral_sub (integrable_const C) ((hn.const_inner (z - u)).const_mul a),
    integral_const_mul, integral_const_mul, integral_inner hn, hz]
  simp only [inner_zero_right, mul_zero, sub_zero, integral_const, probReal_univ, one_smul]
  exact add_le_add (le_refl C) (mul_le_mul_of_nonneg_left (ho.variance y)
    (show 0 ≤ (A + a) / D by positivity))

noncomputable def acceleratedWeight (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) + 1) / 4

noncomputable def acceleratedEnergy (f : E → ℝ) (D : ℝ) (u : E) (k : ℕ) (s : E × E) : ℝ :=
  acceleratedWeight k * (f s.1 - f u) + D / 2 * ‖s.2 - u‖ ^ 2

lemma acceleratedWeight_nonneg (k : ℕ) : 0 ≤ acceleratedWeight k := by
  unfold acceleratedWeight
  positivity

lemma acceleratedWeight_mono {k l : ℕ} (h : k ≤ l) :
    acceleratedWeight k ≤ acceleratedWeight l := by
  have h' : (k : ℝ) ≤ l := Nat.cast_le.mpr h
  unfold acceleratedWeight
  nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] in
lemma acceleratedEnergy_nonneg {f : E → ℝ} {D : ℝ} {u : E}
    (hD : 0 ≤ D) (hm : IsMinOn f univ u) (k : ℕ) (s : E × E) :
    0 ≤ acceleratedEnergy f D u k s := by
  unfold acceleratedEnergy
  exact add_nonneg (mul_nonneg (acceleratedWeight_nonneg k) (sub_nonneg.mpr (hm (by trivial))))
    (by positivity)

omit [CompleteSpace E] in
lemma measurable_acceleratedRun {g : E → Ω → E}
    (h : Measurable (Function.uncurry g)) (D : ℝ) (K k : ℕ) :
    Measurable (fun v : (E × E) × (Fin K → Ω) =>
      acceleratedRun g D K k v.1.1 v.1.2 v.2) := by
  induction K generalizing k with
  | zero => exact measurable_fst
  | succ K ih =>
    let y := fun v : (E × E) × (Fin (K + 1) → Ω) => Gradient.acceleratedQuery (k, v.1.1, v.1.2)
    have hy : Measurable y := by
      dsimp [y, Gradient.acceleratedQuery]
      fun_prop
    have hr : Measurable (fun v : (E × E) × (Fin (K + 1) → Ω) => g (y v) (v.2 0)) :=
      h.comp (hy.prodMk ((measurable_pi_apply 0).comp measurable_snd))
    exact (ih (k + 1)).comp
      (((hy.sub (hr.const_smul _)).prodMk (measurable_fst.snd.sub (hr.const_smul _))).prodMk
        (Measurable.of_eval (fun i => (measurable_pi_apply i.succ).comp measurable_snd)))

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma measurable_acceleratedEnergy {f : E → ℝ} (hf : Measurable f) (D : ℝ) (u : E) (k : ℕ) :
    Measurable (acceleratedEnergy f D u k) :=
  (((hf.comp measurable_fst).sub_const _).const_mul _).add
    (((measurable_snd.sub_const u).norm.pow_const 2).const_mul _)

lemma accelerated_energy_step {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L D σ : ℝ}
    (hD : 0 < D) (hLD : 2 * L ≤ D) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : IsStochasticGradient E Ω p f g σ)
    (x z u : E) (hm : IsMinOn f univ u) (k : ℕ) :
    let y := Gradient.acceleratedQuery (k, x, z)
    let step := fun ω => (y - (1 / D) • g y ω,
      z - (((k : ℝ) + 1) / (2 * D)) • g y ω)
    Integrable (fun ω => acceleratedEnergy f D u (k + 1) (step ω)) p ∧
      (∫ ω, acceleratedEnergy f D u (k + 1) (step ω) ∂p) ≤
        acceleratedEnergy f D u k (x, z) + acceleratedWeight (k + 1) / D * σ ^ 2 := by
  have he : ((k : ℝ) + 1) * ((k : ℝ) + 1 + 1) / 4 =
      (k : ℝ) * ((k : ℝ) + 1) / 4 + ((k : ℝ) + 1) / 2 := by ring
  have hs := accelerated_stochastic_step hD hLD hc hg hlip ho x z u hm
    (A := (k : ℝ) * ((k : ℝ) + 1) / 4) (a := ((k : ℝ) + 1) / 2)
    (by positivity) (by positivity) (by positivity) (by nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k])
  simpa only [acceleratedEnergy, acceleratedWeight, Gradient.acceleratedQuery,
    Nat.cast_add, Nat.cast_one, he, div_div] using hs

lemma accelerated_energy_bound {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L D σ : ℝ}
    (hD : 0 < D) (hLD : 2 * L ≤ D) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : IsStochasticGradient E Ω p f g σ)
    (u : E) (hm : IsMinOn f univ u) (K k : ℕ) (x z : E) :
    Integrable (fun ξ => acceleratedEnergy f D u (k + K) (acceleratedRun g D K k x z ξ))
      (Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, acceleratedEnergy f D u (k + K) (acceleratedRun g D K k x z ξ)
      ∂Measure.pi (fun _ : Fin K => p)) ≤
      acceleratedEnergy f D u k (x, z) + K * (acceleratedWeight (k + K) / D * σ ^ 2) := by
  have hf : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hg x).continuousAt)).measurable
  induction K generalizing k x z with
  | zero => simp [acceleratedRun]
  | succ K ih =>
    let q := Measure.pi (fun _ : Fin K => p)
    let y := Gradient.acceleratedQuery (k, x, z)
    let step := fun ω => (y - (1 / D) • g y ω,
      z - (((k : ℝ) + 1) / (2 * D)) • g y ω)
    let C := (K : ℝ) * (acceleratedWeight (k + (K + 1)) / D * σ ^ 2)
    let B := fun ω => acceleratedEnergy f D u (k + 1) (step ω) + C
    let F := fun v : Ω × (Fin K → Ω) =>
      acceleratedEnergy f D u (k + (K + 1))
        (acceleratedRun g D (K + 1) k x z (Fin.cons v.1 v.2))
    have hmp : Measurable (fun ξ : Fin (K + 1) → Ω =>
        acceleratedEnergy f D u (k + (K + 1)) (acceleratedRun g D (K + 1) k x z ξ)) :=
      (measurable_acceleratedEnergy hf D u _).comp
        ((measurable_acceleratedRun ho.measurable D (K + 1) k).comp
          (measurable_const.prodMk measurable_id :
            Measurable (fun ξ : Fin (K + 1) → Ω => ((x, z), ξ))))
    have hcons := cons_measurePreserving p K
    have hFm : Measurable F := hmp.comp hcons.measurable
    have hFeq (ω : Ω) : (fun ξ => F (ω, ξ)) =
        fun ξ => acceleratedEnergy f D u (k + 1 + K)
          (acceleratedRun g D K (k + 1) (step ω).1 (step ω).2 ξ) := by
      funext ξ
      simp only [F, acceleratedRun, Fin.cons_zero, Fin.cons_succ, step, y]
      congr 1
      omega
    have hstep := accelerated_energy_step hD hLD hc hg hlip ho x z u hm k
    have hBint : Integrable B p := hstep.1.add (integrable_const C)
    have hsection : ∀ ω, Integrable (fun ξ => F (ω, ξ)) q := by
      intro ω
      rw [hFeq]
      exact (ih (k + 1) (step ω).1 (step ω).2).1
    have hbound : ∀ ω, (∫ ξ, F (ω, ξ) ∂q) ≤ B ω := by
      intro ω
      rw [hFeq]
      simpa only [B, C, show k + 1 + K = k + (K + 1) by omega] using
        (ih (k + 1) (step ω).1 (step ω).2).2
    have hnonneg : ∀ v, 0 ≤ F v := fun v => acceleratedEnergy_nonneg hD.le hm _ _
    have hint : Integrable (fun ω => ∫ ξ, ‖F (ω, ξ)‖ ∂q) p := by
      apply hBint.mono_nonneg hFm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun ω => integral_nonneg (fun ξ => norm_nonneg _))
      · exact Filter.Eventually.of_forall (fun ω => by
          simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] using hbound ω)
    have hFi : Integrable F (p.prod q) := (integrable_prod_iff hFm.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hsection, hint⟩
    have hi : Integrable (fun ξ =>
        acceleratedEnergy f D u (k + (K + 1)) (acceleratedRun g D (K + 1) k x z ξ))
        (Measure.pi fun _ : Fin (K + 1) => p) :=
      (hcons.integrable_comp hmp.aestronglyMeasurable).mp hFi
    refine ⟨hi, ?_⟩
    calc
      _ = ∫ v, F v ∂p.prod q := by
        rw [← hcons.map_eq, integral_map hcons.measurable.aemeasurable hmp.aestronglyMeasurable]
      _ = ∫ ω, ∫ ξ, F (ω, ξ) ∂q ∂p := integral_prod F hFi
      _ ≤ ∫ ω, B ω ∂p := integral_mono hFi.integral_prod_left hBint hbound
      _ = (∫ ω, acceleratedEnergy f D u (k + 1) (step ω) ∂p) + C := by
        rw [integral_add hstep.1 (integrable_const C)]
        simp only [integral_const, probReal_univ, one_smul]
        rfl
      _ ≤ acceleratedEnergy f D u k (x, z) +
          acceleratedWeight (k + 1) / D * σ ^ 2 + C := add_le_add hstep.2 (le_refl C)
      _ ≤ _ := by
        have hweight := mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (acceleratedWeight_mono
            (show k + 1 ≤ k + (K + 1) by omega)) hD.le) (sq_nonneg σ)
        dsimp [C]
        push_cast
        nlinarith only [hweight]

lemma accelerated_expected_rate {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L D σ : ℝ}
    (hD : 0 < D) (hLD : 2 * L ≤ D) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : IsStochasticGradient E Ω p f g σ)
    (x0 u : E) (hm : IsMinOn f univ u) (K : ℕ) (hK : 0 < K) :
    Integrable (fun ξ => f (acceleratedRun g D K 0 x0 x0 ξ).1 - f u)
      (Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, f (acceleratedRun g D K 0 x0 x0 ξ).1 - f u
      ∂Measure.pi (fun _ : Fin K => p)) ≤
      2 * D * ‖x0 - u‖ ^ 2 / ((K : ℝ) * ((K : ℝ) + 1)) + K * σ ^ 2 / D := by
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hA : 0 < acceleratedWeight K := by unfold acceleratedWeight; positivity
  have hb := accelerated_energy_bound hD hLD hc hg hlip ho u hm K 0 x0 x0
  simp only [zero_add] at hb
  let V := fun ξ => acceleratedEnergy f D u K (acceleratedRun g D K 0 x0 x0 ξ)
  let F := fun ξ => f (acceleratedRun g D K 0 x0 x0 ξ).1 - f u
  have hf : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hg x).continuousAt)).measurable
  have hFm : Measurable F :=
    (hf.comp (((measurable_acceleratedRun ho.measurable D K 0).comp
      (measurable_const.prodMk measurable_id :
        Measurable (fun ξ : Fin K → Ω => ((x0, x0), ξ)))).fst)).sub_const _
  have hbound : ∀ ξ, F ξ ≤ (acceleratedWeight K)⁻¹ * V ξ := by
    intro ξ
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hA).mpr
    dsimp [F, V, acceleratedEnergy]
    have : 0 ≤ D / 2 * ‖(acceleratedRun g D K 0 x0 x0 ξ).2 - u‖ ^ 2 := by positivity
    nlinarith only [this]
  have hFi : Integrable F (Measure.pi fun _ : Fin K => p) :=
    (hb.1.const_mul ((acceleratedWeight K)⁻¹)).mono_nonneg hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => sub_nonneg.mpr (hm (by trivial))))
      (Filter.Eventually.of_forall hbound)
  refine ⟨hFi, ?_⟩
  calc
    _ ≤ ∫ ξ, (acceleratedWeight K)⁻¹ * V ξ ∂Measure.pi (fun _ : Fin K => p) :=
      integral_mono hFi (hb.1.const_mul _) hbound
    _ = (acceleratedWeight K)⁻¹ * ∫ ξ, V ξ ∂Measure.pi (fun _ : Fin K => p) := integral_const_mul _ _
    _ ≤ (acceleratedWeight K)⁻¹ *
        (acceleratedEnergy f D u 0 (x0, x0) + K * (acceleratedWeight K / D * σ ^ 2)) :=
      mul_le_mul_of_nonneg_left hb.2 (inv_nonneg.mpr hA.le)
    _ = _ := by
      simp only [acceleratedEnergy, acceleratedWeight, Nat.cast_zero, zero_mul, zero_div, zero_add]
      field_simp
      ring

lemma accelerated_tuning_bound (L R σ ε r : ℝ) (K : ℕ)
    (hL : 0 < L) (hε : 0 < ε) (hr : 0 ≤ r) (hrR : r ≤ R) (hK : 0 < K)
    (hdet : Real.sqrt (16 * L * R ^ 2 / ε) ≤ (K : ℝ))
    (hnoise : 64 * σ ^ 2 * R ^ 2 / ε ^ 2 ≤ (K : ℝ)) :
    let D := 2 * L + 8 * (K : ℝ) * σ ^ 2 / ε
    2 * D * r ^ 2 / ((K : ℝ) * ((K : ℝ) + 1)) + (K : ℝ) * σ ^ 2 / D ≤ ε := by
  let D := 2 * L + 8 * (K : ℝ) * σ ^ 2 / ε
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hD : 0 < D := by dsimp [D]; positivity
  have hr2 : r ^ 2 ≤ R ^ 2 := by nlinarith
  have hinit : 2 * D * r ^ 2 / ((K : ℝ) * ((K : ℝ) + 1)) ≤
      2 * D * R ^ 2 / (K : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have h1 := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ 2 * D by positivity)
    have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (K : ℝ))
    have h3 : 0 ≤ 2 * D * R ^ 2 * (K : ℝ) := by positivity
    nlinarith only [h2, h3]
  have hsqrt := Real.sq_sqrt (show 0 ≤ 16 * L * R ^ 2 / ε by positivity)
  have hsq : 16 * L * R ^ 2 / ε ≤ (K : ℝ) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (16 * L * R ^ 2 / ε)]
  have h1 : 4 * L * R ^ 2 / (K : ℝ) ^ 2 ≤ ε / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < (K : ℝ) ^ 2)).mpr
    have h := (div_le_iff₀ hε).mp hsq
    nlinarith only [h]
  have h2 : 16 * σ ^ 2 * R ^ 2 / (ε * (K : ℝ)) ≤ ε / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < ε * (K : ℝ))).mpr
    have h := (div_le_iff₀ (sq_pos_of_pos hε)).mp hnoise
    nlinarith only [h]
  have h3 : (K : ℝ) * σ ^ 2 / D ≤ ε / 8 := by
    apply (div_le_iff₀ hD).mpr
    have he : D * ε = 2 * L * ε + 8 * (K : ℝ) * σ ^ 2 := by
      dsimp [D]
      field_simp
    nlinarith [mul_pos hL hε]
  have he : 2 * D * R ^ 2 / (K : ℝ) ^ 2 =
      4 * L * R ^ 2 / (K : ℝ) ^ 2 + 16 * σ ^ 2 * R ^ 2 / (ε * (K : ℝ)) := by
    dsimp [D]
    field_simp
    ring
  change 2 * D * r ^ 2 / ((K : ℝ) * ((K : ℝ) + 1)) + (K : ℝ) * σ ^ 2 / D ≤ ε
  rw [he] at hinit
  linarith

end OracleTemplate.StochasticGradient

section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticGradient

open LongTails.Setups.StochasticSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma coupled_accelerated_step {f : E → ℝ} {L A a γ : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x z y u G : E) (hy : (A+a) • y=A • x+a • z) :
    (A+a)*(f (y-γ • G)-f u)+‖z-a • G-u‖^2/2 ≤
      A*(f x-f u)+‖z-u‖^2/2+a*⟪gradient f y-G,z-u⟫-
        (A+a)*γ*⟪gradient f y,G⟫+((A+a)*L*γ^2+a^2)/2*‖G‖^2 := by
  have hnorm : ‖z-a • G-u‖^2=‖z-u‖^2-2*a*⟪G,z-u⟫+a^2*‖G‖^2 := by
    rw [show z-a • G-u=(z-u)-a • G by abel,norm_sub_sq_real]
    rw [inner_smul_right,real_inner_comm (z-u) G,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  have hs := Gradient.smooth_upper_bound hg hlip y (y-γ • G)
  have hsub : y-γ • G-y=-(γ • G) := by abel
  rw [hsub,inner_neg_right,inner_smul_right,norm_neg,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hs
  have hcx := Gradient.convex_support hc hg y x
  have hcu := Gradient.convex_support hc hg y u
  have hvec : A • (x-y)+a • (u-y)=a • (u-z) := by
    calc
      _ = A • x+a • u-(A+a) • y := by simp only [smul_sub,add_smul]; abel
      _ = _ := by rw [hy]; simp only [smul_sub]; abel
  have hin : A*⟪gradient f y,x-y⟫+a*⟪gradient f y,u-y⟫ = -a*⟪gradient f y,z-u⟫ := by
    rw [← inner_smul_right,← inner_smul_right,← inner_add_right,hvec,inner_smul_right]
    rw [show u-z=-(z-u) by abel,inner_neg_right]
    ring
  have hconv : (A+a)*f y ≤ A*f x+a*f u+a*⟪gradient f y,z-u⟫ := by
    have hx := mul_le_mul_of_nonneg_left hcx hA
    have hu := mul_le_mul_of_nonneg_left hcu ha
    nlinarith only [hx,hu,hin]
  have hdes := mul_le_mul_of_nonneg_left hs (add_nonneg hA ha)
  rw [hnorm,inner_sub_left]
  nlinarith only [hconv,hdes]

lemma coupled_accelerated_expected_step {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {L A a γ θ v : ℝ}
    (hL : 0 ≤ L) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x z y u : E) (hy : (A+a) • y=A • x+a • z)
    (G : Ω → E) (hGi : Integrable G p) (hmean : (∫ ω, G ω ∂p)=gradient f y)
    (hG2 : Integrable (fun ω => ‖G ω‖^2) p)
    (hmoment : (∫ ω, ‖G ω‖^2 ∂p) ≤ θ*‖gradient f y‖^2+v)
    (hcancel : ((A+a)*L*γ^2+a^2)*θ ≤ 2*(A+a)*γ)
    (hEi : Integrable (fun ω => (A+a)*(f (y-γ • G ω)-f u)+‖z-a • G ω-u‖^2/2) p) :
    (∫ ω, (A+a)*(f (y-γ • G ω)-f u)+‖z-a • G ω-u‖^2/2 ∂p) ≤
      A*(f x-f u)+‖z-u‖^2/2+((A+a)*L*γ^2+a^2)/2*v := by
  let C := ((A+a)*L*γ^2+a^2)/2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnoise : Integrable (fun ω => a*⟪gradient f y-G ω,z-u⟫) p :=
    (((integrable_const _).sub hGi).inner_const _).const_mul a
  have hdes : Integrable (fun ω => (A+a)*γ*⟪gradient f y,G ω⟫) p :=
    (hGi.const_inner _).const_mul _
  have hconst : Integrable (fun _ : Ω => A*(f x-f u)+‖z-u‖^2/2) p := integrable_const _
  have hsum : Integrable (fun ω => A*(f x-f u)+‖z-u‖^2/2+a*⟪gradient f y-G ω,z-u⟫) p := hconst.add hnoise
  have hdiff : Integrable (fun ω => A*(f x-f u)+‖z-u‖^2/2+a*⟪gradient f y-G ω,z-u⟫-(A+a)*γ*⟪gradient f y,G ω⟫) p := hsum.sub hdes
  have hright := hdiff.add (hG2.const_mul C)
  have hint := integral_mono hEi hright (fun ω => coupled_accelerated_step hA ha hc hg hlip x z y u (G ω) hy)
  have hei : Integrable (fun ω => gradient f y-G ω) p := (integrable_const _).sub hGi
  have hnoiseint : (∫ ω, a*⟪gradient f y-G ω,z-u⟫ ∂p)=0 := by
    rw [integral_const_mul]
    simp_rw [real_inner_comm (z-u)]
    rw [integral_inner (𝕜 := ℝ) hei (z-u)]
    rw [integral_sub (integrable_const (gradient f y)) hGi]
    simp [hmean]
  have hdesint : (∫ ω, (A+a)*γ*⟪gradient f y,G ω⟫ ∂p)=(A+a)*γ*‖gradient f y‖^2 := by
    rw [integral_const_mul,integral_inner (𝕜 := ℝ) hGi (gradient f y),hmean,real_inner_self_eq_norm_sq]
  simp only [Pi.add_apply] at hint
  rw [integral_add hdiff (hG2.const_mul C),
    integral_sub hsum hdes,
    integral_add hconst hnoise,hnoiseint,hdesint,integral_const_mul] at hint
  simp only [integral_const,probReal_univ,one_smul,add_zero] at hint
  have hv := mul_le_mul_of_nonneg_left hmoment hC
  have hc' := mul_le_mul_of_nonneg_right hcancel (sq_nonneg ‖gradient f y‖)
  change _ ≤ A*(f x-f u)+‖z-u‖^2/2+C*v
  dsimp [C] at *
  nlinarith only [hint,hv,hc']

lemma coupled_energy_integrable {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E]
    {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {L A a γ c : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hlo : ∀ x, c ≤ f x) (x z y u : E) (hy : (A+a) • y=A • x+a • z)
    (G : Ω → E) (hG : Measurable G) (hGi : Integrable G p)
    (hG2 : Integrable (fun ω => ‖G ω‖^2) p) :
    Integrable (fun ω => (A+a)*(f (y-γ • G ω)-c)+‖z-a • G ω-u‖^2/2) p := by
  let B := fun ω => A*(f x-f u)+‖z-u‖^2/2+a*⟪gradient f y-G ω,z-u⟫-
    (A+a)*γ*⟪gradient f y,G ω⟫+((A+a)*L*γ^2+a^2)/2*‖G ω‖^2+(A+a)*(f u-c)
  have hi : Integrable B p :=
    (((((integrable_const _).add ((((integrable_const _).sub hGi).inner_const _).const_mul a)).sub
      ((hGi.const_inner _).const_mul _)).add (hG2.const_mul _)).add (integrable_const _))
  have hf : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)).measurable
  have hmeas : Measurable (fun ω => (A+a)*(f (y-γ • G ω)-c)+‖z-a • G ω-u‖^2/2) := by fun_prop
  apply hi.mono_nonneg hmeas.aestronglyMeasurable
  · filter_upwards [] with ω
    exact add_nonneg (mul_nonneg (add_nonneg hA ha) (sub_nonneg.mpr (hlo _))) (by positivity)
  · filter_upwards [] with ω
    have hh := coupled_accelerated_step (γ := γ) hA ha hc hg hlip x z y u (G ω) hy
    dsimp [B]
    nlinarith only [hh]

lemma coupled_lower_energy_step {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E]
    {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {L A a γ θ v c : ℝ}
    (hL : 0 ≤ L) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hlo : ∀ x, c ≤ f x) (x z y u : E) (hy : (A+a) • y=A • x+a • z)
    (G : Ω → E) (hG : Measurable G) (hGi : Integrable G p)
    (hmean : (∫ ω, G ω ∂p)=gradient f y)
    (hG2 : Integrable (fun ω => ‖G ω‖^2) p)
    (hmoment : (∫ ω, ‖G ω‖^2 ∂p) ≤ θ*‖gradient f y‖^2+v)
    (hcancel : ((A+a)*L*γ^2+a^2)*θ ≤ 2*(A+a)*γ) :
    Integrable (fun ω => (A+a)*(f (y-γ • G ω)-c)+‖z-a • G ω-u‖^2/2) p ∧
    (∫ ω, (A+a)*(f (y-γ • G ω)-c)+‖z-a • G ω-u‖^2/2 ∂p) ≤
      A*(f x-c)+‖z-u‖^2/2+a*(f u-c)+((A+a)*L*γ^2+a^2)/2*v := by
  have hi := coupled_energy_integrable (γ := γ) hA ha hc hg hlip hlo x z y u hy G hG hGi hG2
  refine ⟨hi,?_⟩
  have he (ω : Ω) : (A+a)*(f (y-γ • G ω)-f u)+‖z-a • G ω-u‖^2/2 =
      ((A+a)*(f (y-γ • G ω)-c)+‖z-a • G ω-u‖^2/2)-(A+a)*(f u-c) := by ring
  have hEi : Integrable (fun ω => (A+a)*(f (y-γ • G ω)-f u)+‖z-a • G ω-u‖^2/2) p := by
    simp_rw [he]
    exact hi.sub (integrable_const _)
  have hh := coupled_accelerated_expected_step hL hA ha hc hg hlip x z y u hy G hGi hmean hG2 hmoment hcancel hEi
  simp_rw [he] at hh
  rw [integral_sub hi (integrable_const _)] at hh
  simp only [integral_const,probReal_univ,one_smul] at hh
  nlinarith only [hh]

end OracleTemplate.StochasticGradient

end

section

namespace OracleTemplate.StochasticGradient

open LongTails.Setups.StochasticSmoothAndConvex

lemma coupled_parameters {L M θ t : ℝ} (hM : 0 < M) (hθ : 0 ≤ θ)
    (ht : 0 ≤ t) (hLM : 2*L*θ^2 ≤ M) :
    let A := t*(t+1)/(2*M)
    let a := (t+1)/M
    let γ := 2*θ/M
    ((A+a)*L*γ^2+a^2)*θ ≤ 2*(A+a)*γ ∧
      ((A+a)*L*γ^2+a^2)/2 ≤ (t+1)*(t+2)/M^2 := by
  dsimp only
  have hcoef := mul_le_mul_of_nonneg_right hLM (show 0 ≤ (t+1)*(t+2) by positivity)
  constructor
  · apply (mul_le_mul_iff_left₀ (show 0 < M^3 by positivity)).mp
    field_simp
    nlinarith [mul_nonneg hθ (show 0 ≤ M*(t+1) by positivity),
      mul_le_mul_of_nonneg_left hcoef hθ]
  · apply (mul_le_mul_iff_left₀ (show 0 < M^3 by positivity)).mp
    field_simp
    nlinarith [mul_nonneg hM.le (show 0 ≤ t+1 by positivity)]

end OracleTemplate.StochasticGradient

end
