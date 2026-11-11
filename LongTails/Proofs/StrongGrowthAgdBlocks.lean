import LongTails.Proofs.AdaptiveIID

namespace LongTails.Proofs.StrongGrowthAgdBlocks

open MeasureTheory ProbabilityTheory OracleTemplate.StochasticGeneralized

variable {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
variable (step : S → X → S) (s0 : S)

noncomputable def run (β : ℕ → X) : ℕ → S
  | 0 => s0
  | t + 1 => step (run β t) (β t)

omit [MeasurableSpace S] [MeasurableSpace X] in
lemma run_zero (β : ℕ → X) : run step s0 β 0 = s0 := rfl

omit [MeasurableSpace S] [MeasurableSpace X] in
lemma run_succ (β : ℕ → X) (t : ℕ) : run step s0 β (t + 1) = step (run step s0 β t) (β t) := rfl

omit [MeasurableSpace S] [MeasurableSpace X] in
lemma run_congr {β β' : ℕ → X} : ∀ t, (∀ n, n < t → β n = β' n) → run step s0 β t = run step s0 β' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    rw [run_succ, run_succ, ih (fun n hn => h n (by omega)), h t (by omega)]

lemma run_measurable (hstep : Measurable (Function.uncurry step)) :
    ∀ t, Measurable (fun β : ℕ → X => run step s0 β t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact hstep.comp (ih.prodMk (measurable_pi_apply t))

variable (ν : Measure X) [IsProbabilityMeasure ν]

noncomputable def runPre (t : ℕ) (pre : Fin t → X) : S :=
  haveI : Nonempty X := Measure.nonempty_of_neZero ν
  run step s0 (fun n => if h : n < t then pre ⟨n, h⟩ else Classical.arbitrary X) t

omit [MeasurableSpace S] in
lemma runPre_eq (t : ℕ) (β : ℕ → X) : runPre step s0 ν t (fun i : Fin t => β i) = run step s0 β t := by
  unfold runPre
  apply run_congr
  intro n hn
  simp [hn]

lemma runPre_measurable (hstep : Measurable (Function.uncurry step)) (t : ℕ) :
    Measurable (runPre step s0 ν t) := by
  unfold runPre
  have : Nonempty X := Measure.nonempty_of_neZero ν
  apply (run_measurable step s0 hstep t).comp
  refine measurable_pi_iff.mpr (fun n => ?_)
  by_cases h : n < t
  · simp only [h, ↓reduceDIte]; exact measurable_pi_apply _
  · simp only [h, ↓reduceDIte]; exact measurable_const

omit [MeasurableSpace S] in
lemma split_rewrite (t : ℕ) (F : S → X → ℝ) (β : ℕ → X) :
    F (run step s0 β t) (β t) =
      (fun z : (Fin t → X) × (ℕ → X) => F (runPre step s0 ν t z.1) (z.2 0)) (splitStream t β) := by
  simp only [splitStream, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Nat.add_zero]
  rw [runPre_eq]

lemma tail_eval_preserving :
    MeasurePreserving (fun tail : ℕ → X => tail 0) (Measure.infinitePi fun _ : ℕ => ν) ν :=
  measurePreserving_eval_infinitePi (fun _ : ℕ => ν) 0

lemma integral_eval (F : X → ℝ) (hF : Measurable F) :
    ∫ tail, F (tail 0) ∂(Measure.infinitePi fun _ : ℕ => ν) = ∫ x, F x ∂ν := by
  have h := (tail_eval_preserving ν).map_eq
  have := integral_map (μ := Measure.infinitePi fun _ : ℕ => ν) (measurable_pi_apply 0).aemeasurable
    (f := F) hF.aestronglyMeasurable
  rw [h] at this
  exact this.symm

theorem step_integral (hstep : Measurable (Function.uncurry step)) (t : ℕ) (F : S → X → ℝ)
    (hF : Measurable (Function.uncurry F))
    (hint : Integrable (fun β => F (run step s0 β t) (β t)) (Measure.infinitePi fun _ : ℕ => ν)) :
    ∫ β, F (run step s0 β t) (β t) ∂(Measure.infinitePi fun _ : ℕ => ν) =
      ∫ β, (∫ x, F (run step s0 β t) x ∂ν) ∂(Measure.infinitePi fun _ : ℕ => ν) := by
  set G : (Fin t → X) × (ℕ → X) → ℝ := fun z => F (runPre step s0 ν t z.1) (z.2 0) with hG
  have hsplit := splitStream_preserving ν t
  have hrw : (fun β => F (run step s0 β t) (β t)) = fun β => G (splitStream t β) := by
    funext β; exact split_rewrite step s0 ν t F β
  have hGm : Measurable G :=
    hF.comp (((runPre_measurable step s0 ν hstep t).comp measurable_fst).prodMk
      ((measurable_pi_apply 0).comp measurable_snd))
  have hGint : Integrable G ((Measure.pi fun _ : Fin t => ν).prod (Measure.infinitePi fun _ : ℕ => ν)) := by
    rw [hrw] at hint
    exact (hsplit.integrable_comp hGm.aestronglyMeasurable).mp hint
  rw [hrw, hsplit.integral_comp' G, integral_prod _ hGint]
  have hinner (pre : Fin t → X) : (∫ tail, G (pre, tail) ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      ∫ x, F (runPre step s0 ν t pre) x ∂ν := by
    simp only [hG]
    exact integral_eval ν (fun x => F (runPre step s0 ν t pre) x)
      (hF.comp (measurable_const.prodMk measurable_id))
  simp_rw [hinner]
  have hrw2 : (fun β => ∫ x, F (run step s0 β t) x ∂ν) =
      fun β => (fun z : (Fin t → X) × (ℕ → X) => ∫ x, F (runPre step s0 ν t z.1) x ∂ν) (splitStream t β) := by
    funext β
    simp only [splitStream, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
    rw [runPre_eq]
  rw [hrw2, hsplit.integral_comp' (fun z : (Fin t → X) × (ℕ → X) => ∫ x, F (runPre step s0 ν t z.1) x ∂ν)]
  have hH : Integrable (fun z : (Fin t → X) × (ℕ → X) => ∫ x, F (runPre step s0 ν t z.1) x ∂ν)
      ((Measure.pi fun _ : Fin t => ν).prod (Measure.infinitePi fun _ : ℕ => ν)) := by
    have h1 := hGint.integral_prod_left
    have : (fun z : (Fin t → X) × (ℕ → X) => ∫ x, F (runPre step s0 ν t z.1) x ∂ν) =
        (fun pre : Fin t → X => ∫ tail, G (pre, tail) ∂(Measure.infinitePi fun _ : ℕ => ν)) ∘ Prod.fst := by
      funext z; simp only [Function.comp_apply, hinner]
    rw [this]
    exact h1.comp_fst (Measure.infinitePi fun _ : ℕ => ν)
  rw [integral_prod _ hH]
  simp

theorem step_integrable (hstep : Measurable (Function.uncurry step)) (t : ℕ) (F : S → X → ℝ)
    (hF : Measurable (Function.uncurry F))
    (hFs : ∀ s, Integrable (fun x => F s x) ν)
    (G : S → ℝ) (hGm : Measurable G)
    (hbound : ∀ s, ∫ x, |F s x| ∂ν ≤ G s)
    (hGint : Integrable (fun β => G (run step s0 β t)) (Measure.infinitePi fun _ : ℕ => ν)) :
    Integrable (fun β => F (run step s0 β t) (β t)) (Measure.infinitePi fun _ : ℕ => ν) := by
  set Gf : (Fin t → X) × (ℕ → X) → ℝ := fun z => F (runPre step s0 ν t z.1) (z.2 0) with hGf
  have hsplit := splitStream_preserving ν t
  have hrw : (fun β => F (run step s0 β t) (β t)) = Gf ∘ splitStream t := by
    funext β; exact split_rewrite step s0 ν t F β
  have hGm' : Measurable Gf :=
    hF.comp (((runPre_measurable step s0 ν hstep t).comp measurable_fst).prodMk
      ((measurable_pi_apply 0).comp measurable_snd))
  rw [hrw, hsplit.integrable_comp hGm'.aestronglyMeasurable]
  rw [integrable_prod_iff hGm'.aestronglyMeasurable]
  constructor
  · refine Filter.Eventually.of_forall (fun pre => ?_)
    simp only [hGf]
    exact (tail_eval_preserving ν).integrable_comp_of_integrable (hFs _)
  · have hG1 : Integrable (fun pre : Fin t → X => G (runPre step s0 ν t pre)) (Measure.pi fun _ : Fin t => ν) := by
      have hpre := prefix_preserving ν t
      have : (fun β : ℕ → X => G (run step s0 β t)) =
          (fun pre : Fin t → X => G (runPre step s0 ν t pre)) ∘ (fun β : ℕ → X => fun i : Fin t => β i) := by
        funext β; simp only [Function.comp_apply, runPre_eq]
      rw [this] at hGint
      exact (hpre.integrable_comp (hGm.comp (runPre_measurable step s0 ν hstep t)).aestronglyMeasurable).mp hGint
    refine hG1.mono' ?_ (Filter.Eventually.of_forall (fun pre => ?_))
    · exact (hGm'.norm.aestronglyMeasurable.integral_prod_right' (ν := Measure.infinitePi fun _ : ℕ => ν))
    · simp only [hGf, Real.norm_eq_abs]
      have hm : Measurable (fun x => |F (runPre step s0 ν t pre) x|) := by
        have h0 : Measurable (fun x => F (runPre step s0 ν t pre) x) :=
          hF.comp (measurable_const.prodMk measurable_id)
        exact h0.norm
      have h1 : (∫ tail, |F (runPre step s0 ν t pre) (tail 0)| ∂(Measure.infinitePi fun _ : ℕ => ν)) =
          ∫ x, |F (runPre step s0 ν t pre) x| ∂ν :=
        integral_eval ν (fun x => |F (runPre step s0 ν t pre) x|) hm
      rw [abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _)), h1]
      exact hbound _

theorem run_dominated (hstep : Measurable (Function.uncurry step)) (W : S → ℝ) (hW : Measurable W)
    (hW0 : ∀ s, 0 ≤ W s) (A C : ℝ) (_hA : 0 ≤ A)
    (hint : ∀ s, Integrable (fun x => W (step s x)) ν)
    (hdom : ∀ s, ∫ x, W (step s x) ∂ν ≤ A * W s + C) :
    ∀ t, Integrable (fun β => W (run step s0 β t)) (Measure.infinitePi fun _ : ℕ => ν) := by
  intro t
  induction t with
  | zero =>
    show Integrable (fun _ : ℕ → X => W s0) (Measure.infinitePi fun _ : ℕ => ν)
    exact integrable_const _
  | succ t ih =>
    have hF : Measurable (Function.uncurry fun s x => W (step s x)) := hW.comp hstep
    have hres : Integrable (fun β => W (step (run step s0 β t) (β t))) (Measure.infinitePi fun _ : ℕ => ν) :=
      step_integrable step s0 ν hstep t (fun s x => W (step s x)) hF hint
      (fun s => A * W s + C) ((hW.const_mul A).add_const C)
      (fun s => by
        have : ∫ x, |W (step s x)| ∂ν = ∫ x, W (step s x) ∂ν :=
          integral_congr_ae (Filter.Eventually.of_forall (fun x => abs_of_nonneg (hW0 _)))
        rw [this]; exact hdom s)
      ((ih.const_mul A).add (integrable_const C :
        Integrable (fun _ : ℕ → X => C) (Measure.infinitePi fun _ : ℕ => ν)))
    exact hres

end LongTails.Proofs.StrongGrowthAgdBlocks
