import LongTails.Proofs.StrongGrowthAgdBlocks

namespace LongTails.Proofs.StrongGrowthAgdBlocks

open MeasureTheory ProbabilityTheory OracleTemplate.StochasticGeneralized

variable {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
variable (step : S → X → S) (s0 : S)

def shift (t : ℕ) (β : ℕ → X) : ℕ → X := fun n => β (t + n)

lemma shift_measurable (t : ℕ) : Measurable (shift (X := X) t) :=
  measurable_pi_iff.mpr (fun n => measurable_pi_apply (t + n))

omit [MeasurableSpace S] [MeasurableSpace X] in
lemma run_add (β : ℕ → X) (t n : ℕ) :
    run step s0 β (t + n) = run step (run step s0 β t) (shift t β) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← add_assoc, run_succ, ih, run_succ]; rfl

lemma run_measurable₂ (hstep : Measurable (Function.uncurry step)) :
    ∀ m, Measurable (fun z : S × (ℕ → X) => run step z.1 z.2 m) := by
  intro m
  induction m with
  | zero => exact measurable_fst
  | succ m ih => exact hstep.comp (ih.prodMk ((measurable_pi_apply m).comp measurable_snd))

omit [MeasurableSpace S] [MeasurableSpace X] in
lemma run_mem_inv (Inv : ℕ → Set S) (hInv : ∀ t, ∀ s ∈ Inv t, ∀ x, step s x ∈ Inv (t + 1))
    (hs0 : s0 ∈ Inv 0) (β : ℕ → X) : ∀ t, run step s0 β t ∈ Inv t := by
  intro t
  induction t with
  | zero => exact hs0
  | succ t ih => exact hInv t _ ih _

variable (ν : Measure X) [IsProbabilityMeasure ν]

omit [MeasurableSpace S] in
lemma tail_rewrite (t : ℕ) (F : S → (ℕ → X) → ℝ) (β : ℕ → X) :
    F (run step s0 β t) (shift t β) =
      (fun z : (Fin t → X) × (ℕ → X) => F (runPre step s0 ν t z.1) z.2) (splitStream t β) := by
  simp only [splitStream, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [runPre_eq]
  rfl

theorem tail_integral (hstep : Measurable (Function.uncurry step)) (t : ℕ) (F : S → (ℕ → X) → ℝ)
    (hF : Measurable (Function.uncurry F))
    (hint : Integrable (fun β => F (run step s0 β t) (shift t β)) (Measure.infinitePi fun _ : ℕ => ν)) :
    ∫ β, F (run step s0 β t) (shift t β) ∂(Measure.infinitePi fun _ : ℕ => ν) =
      ∫ β, (∫ tail, F (run step s0 β t) tail ∂(Measure.infinitePi fun _ : ℕ => ν))
        ∂(Measure.infinitePi fun _ : ℕ => ν) := by
  set G : (Fin t → X) × (ℕ → X) → ℝ := fun z => F (runPre step s0 ν t z.1) z.2 with hG
  have hsplit := splitStream_preserving ν t
  have hrw : (fun β => F (run step s0 β t) (shift t β)) = fun β => G (splitStream t β) := by
    funext β; exact tail_rewrite step s0 ν t F β
  have hGm : Measurable G :=
    hF.comp (((runPre_measurable step s0 ν hstep t).comp measurable_fst).prodMk measurable_snd)
  have hGint : Integrable G ((Measure.pi fun _ : Fin t => ν).prod (Measure.infinitePi fun _ : ℕ => ν)) := by
    rw [hrw] at hint
    exact (hsplit.integrable_comp hGm.aestronglyMeasurable).mp hint
  rw [hrw, hsplit.integral_comp' G, integral_prod _ hGint]
  have hrw2 : (fun β => ∫ tail, F (run step s0 β t) tail ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      fun β => (fun z : (Fin t → X) × (ℕ → X) =>
        ∫ tail, F (runPre step s0 ν t z.1) tail ∂(Measure.infinitePi fun _ : ℕ => ν)) (splitStream t β) := by
    funext β
    simp only [splitStream, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
    rw [runPre_eq]
  rw [hrw2, hsplit.integral_comp' (fun z : (Fin t → X) × (ℕ → X) =>
    ∫ tail, F (runPre step s0 ν t z.1) tail ∂(Measure.infinitePi fun _ : ℕ => ν))]
  have hH : Integrable (fun z : (Fin t → X) × (ℕ → X) =>
      ∫ tail, F (runPre step s0 ν t z.1) tail ∂(Measure.infinitePi fun _ : ℕ => ν))
      ((Measure.pi fun _ : Fin t => ν).prod (Measure.infinitePi fun _ : ℕ => ν)) := by
    have h1 := hGint.integral_prod_left
    have : (fun z : (Fin t → X) × (ℕ → X) =>
        ∫ tail, F (runPre step s0 ν t z.1) tail ∂(Measure.infinitePi fun _ : ℕ => ν)) =
        (fun pre : Fin t → X => ∫ tail, G (pre, tail) ∂(Measure.infinitePi fun _ : ℕ => ν)) ∘ Prod.fst := by
      funext z; rfl
    rw [this]
    exact h1.comp_fst (Measure.infinitePi fun _ : ℕ => ν)
  rw [integral_prod _ hH]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show ∫ y, G (x, y) ∂(Measure.infinitePi fun _ : ℕ => ν) =
    ∫ y, (fun _ : ℕ → X => ∫ tail, F (runPre step s0 ν t x) tail ∂(Measure.infinitePi fun _ : ℕ => ν)) y
      ∂(Measure.infinitePi fun _ : ℕ => ν)
  rw [integral_const, probReal_univ, one_smul]

theorem tail_inner_integrable (hstep : Measurable (Function.uncurry step)) (t : ℕ) (F : S → (ℕ → X) → ℝ)
    (hF : Measurable (Function.uncurry F))
    (hint : Integrable (fun β => F (run step s0 β t) (shift t β)) (Measure.infinitePi fun _ : ℕ => ν)) :
    Integrable (fun β => ∫ tail, F (run step s0 β t) tail ∂(Measure.infinitePi fun _ : ℕ => ν))
      (Measure.infinitePi fun _ : ℕ => ν) := by
  set G : (Fin t → X) × (ℕ → X) → ℝ := fun z => F (runPre step s0 ν t z.1) z.2 with hG
  have hsplit := splitStream_preserving ν t
  have hrw : (fun β => F (run step s0 β t) (shift t β)) = G ∘ splitStream t := by
    funext β; exact tail_rewrite step s0 ν t F β
  have hGm : Measurable G :=
    hF.comp (((runPre_measurable step s0 ν hstep t).comp measurable_fst).prodMk measurable_snd)
  have hGint : Integrable G ((Measure.pi fun _ : Fin t => ν).prod (Measure.infinitePi fun _ : ℕ => ν)) := by
    rw [hrw] at hint
    exact (hsplit.integrable_comp hGm.aestronglyMeasurable).mp hint
  have hrw2 : (fun β => ∫ tail, F (run step s0 β t) tail ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      (fun pre : Fin t → X => ∫ tail, G (pre, tail) ∂(Measure.infinitePi fun _ : ℕ => ν)) ∘
        (fun β : ℕ → X => fun i : Fin t => β i) := by
    funext β
    simp only [Function.comp_apply, hG]
    rw [runPre_eq]
  rw [hrw2]
  have h1 := hGint.integral_prod_left
  have hpre := prefix_preserving ν t
  exact (hpre.integrable_comp (by
    have := h1.aestronglyMeasurable
    exact this)).mpr h1

theorem tail_integrable (hstep : Measurable (Function.uncurry step)) (t : ℕ) (F : S → (ℕ → X) → ℝ)
    (hF : Measurable (Function.uncurry F))
    (hFs : ∀ s, Integrable (F s) (Measure.infinitePi fun _ : ℕ => ν))
    (G : S → ℝ) (hGm : Measurable G)
    (hbound : ∀ s, ∫ tail, |F s tail| ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ G s)
    (hGint : Integrable (fun β => G (run step s0 β t)) (Measure.infinitePi fun _ : ℕ => ν)) :
    Integrable (fun β => F (run step s0 β t) (shift t β)) (Measure.infinitePi fun _ : ℕ => ν) := by
  set Gf : (Fin t → X) × (ℕ → X) → ℝ := fun z => F (runPre step s0 ν t z.1) z.2 with hGf
  have hsplit := splitStream_preserving ν t
  have hrw : (fun β => F (run step s0 β t) (shift t β)) = Gf ∘ splitStream t := by
    funext β; exact tail_rewrite step s0 ν t F β
  have hGm' : Measurable Gf :=
    hF.comp (((runPre_measurable step s0 ν hstep t).comp measurable_fst).prodMk measurable_snd)
  rw [hrw, hsplit.integrable_comp hGm'.aestronglyMeasurable]
  rw [integrable_prod_iff hGm'.aestronglyMeasurable]
  constructor
  · exact Filter.Eventually.of_forall (fun pre => hFs (runPre step s0 ν t pre))
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
      rw [abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
      exact hbound _

theorem run_dominated_bound (hstep : Measurable (Function.uncurry step)) (W : S → ℝ) (hW : Measurable W)
    (hW0 : ∀ s, 0 ≤ W s) (A C : ℝ) (hA : 1 ≤ A) (hC : 0 ≤ C)
    (hint : ∀ s, Integrable (fun x => W (step s x)) ν)
    (hdom : ∀ s, ∫ x, W (step s x) ∂ν ≤ A * W s + C) (s : S) :
    ∀ j, ∫ β, W (run step s β j) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ A ^ j * (W s + j * C) := by
  intro j
  induction j with
  | zero =>
    have : (fun β : ℕ → X => W (run step s β 0)) = fun _ => W s := rfl
    rw [this]; simp
  | succ j ih =>
    have hint' := run_dominated step s ν hstep W hW hW0 A C (by linarith) hint hdom
    have hF : Measurable (Function.uncurry fun s' x => W (step s' x)) := hW.comp hstep
    have h1 := step_integral step s ν hstep j (fun s' x => W (step s' x)) hF (hint' (j + 1))
    simp only [run_succ]
    rw [h1]
    have h2 : ∫ β, (∫ x, W (step (run step s β j) x) ∂ν) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
        ∫ β, (A * W (run step s β j) + C) ∂(Measure.infinitePi fun _ : ℕ => ν) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun β => integral_nonneg (fun _ => hW0 _)))
        (((hint' j).const_mul A).add (integrable_const C :
          Integrable (fun _ : ℕ → X => C) (Measure.infinitePi fun _ : ℕ => ν)))
        (Filter.Eventually.of_forall (fun β => hdom _))
    rw [integral_add ((hint' j).const_mul A) (integrable_const C :
      Integrable (fun _ : ℕ → X => C) (Measure.infinitePi fun _ : ℕ => ν)), integral_const_mul] at h2
    simp only [integral_const, probReal_univ, one_smul] at h2
    have hAj : 0 ≤ A ^ j := pow_nonneg (by linarith) j
    have hAj1 : 1 ≤ A ^ (j + 1) := one_le_pow₀ hA
    have hC' : C ≤ A ^ (j + 1) * C := le_mul_of_one_le_left hC hAj1
    have hC'' : C ≤ A ^ j * A * C := by rw [← pow_succ]; exact hC'
    calc _ ≤ A * (A ^ j * (W s + j * C)) + C := by linarith [mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ A)]
      _ ≤ A ^ (j + 1) * (W s + (j + 1 : ℕ) * C) := by
        rw [pow_succ]; push_cast
        have e : A ^ j * A * (W s + (j + 1) * C) = A * (A ^ j * (W s + j * C)) + A ^ j * A * C := by ring
        rw [e]; linarith

theorem drift (hstep : Measurable (Function.uncurry step)) (m : ℕ) (Inv : ℕ → Set S)
    (hInv : ∀ t, ∀ s ∈ Inv t, ∀ x, step s x ∈ Inv (t + 1)) (hs0 : s0 ∈ Inv 0)
    (Y c : S → ℝ) (D : S → (ℕ → X) → ℝ) (hY : Measurable Y) (_hc : Measurable c)
    (hD : Measurable (Function.uncurry D))
    (hYint : ∀ t, Integrable (fun β => Y (run step s0 β t)) (Measure.infinitePi fun _ : ℕ => ν))
    (hcint : ∀ t, Integrable (fun β => c (run step s0 β t)) (Measure.infinitePi fun _ : ℕ => ν))
    (hDint : ∀ e, Integrable (fun β => D (run step s0 β (e * m)) (shift (e * m) β))
      (Measure.infinitePi fun _ : ℕ => ν)) (n : ℕ)
    (hdrift : ∀ e < n, ∀ s ∈ Inv (e * m),
      ∫ tail, (Y (run step s tail m) + D s tail) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ Y s + c s) :
    ∫ β, Y (run step s0 β (n * m)) ∂(Measure.infinitePi fun _ : ℕ => ν) +
      ∑ e ∈ Finset.range n, ∫ β, D (run step s0 β (e * m)) (shift (e * m) β)
        ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      Y s0 + ∑ e ∈ Finset.range n, ∫ β, c (run step s0 β (e * m)) ∂(Measure.infinitePi fun _ : ℕ => ν) := by
  induction n with
  | zero =>
    have : (fun β : ℕ → X => Y (run step s0 β (0 * m))) = fun _ => Y s0 := by
      funext β; rw [zero_mul]; rfl
    rw [this]; simp
  | succ n ih =>
    have ih := ih (fun e he => hdrift e (by omega))
    set F : S → (ℕ → X) → ℝ := fun s tail => Y (run step s tail m) + D s tail with hF
    have hFm : Measurable (Function.uncurry F) :=
      (hY.comp (run_measurable₂ step hstep m)).add hD
    have hrun : ∀ β, run step s0 β ((n + 1) * m) = run step (run step s0 β (n * m)) (shift (n * m) β) m := by
      intro β; rw [add_mul, one_mul, run_add]
    have hint : Integrable (fun β => F (run step s0 β (n * m)) (shift (n * m) β))
        (Measure.infinitePi fun _ : ℕ => ν) := by
      simp only [hF]
      refine Integrable.add ?_ (hDint n)
      have := hYint ((n + 1) * m)
      simp_rw [hrun] at this
      exact this
    have h1 := tail_integral step s0 ν hstep (n * m) F hFm hint
    have h2 := tail_inner_integrable step s0 ν hstep (n * m) F hFm hint
    have h3 : ∫ β, (∫ tail, F (run step s0 β (n * m)) tail ∂(Measure.infinitePi fun _ : ℕ => ν))
        ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
        ∫ β, (Y (run step s0 β (n * m)) + c (run step s0 β (n * m))) ∂(Measure.infinitePi fun _ : ℕ => ν) := by
      refine integral_mono h2 ((hYint _).add (hcint _)) (fun β => ?_)
      exact hdrift n (by omega) _ (run_mem_inv step s0 Inv hInv hs0 β _)
    rw [integral_add (hYint _) (hcint _)] at h3
    have h4 : ∫ β, Y (run step s0 β ((n + 1) * m)) ∂(Measure.infinitePi fun _ : ℕ => ν) +
        ∫ β, D (run step s0 β (n * m)) (shift (n * m) β) ∂(Measure.infinitePi fun _ : ℕ => ν) =
        ∫ β, F (run step s0 β (n * m)) (shift (n * m) β) ∂(Measure.infinitePi fun _ : ℕ => ν) := by
      rw [← integral_add (hYint _) (hDint n)]
      congr 1; funext β; simp only [hF, hrun]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

theorem drift_mul (hstep : Measurable (Function.uncurry step)) (m : ℕ) (Inv : ℕ → Set S)
    (hInv : ∀ t, ∀ s ∈ Inv t, ∀ x, step s x ∈ Inv (t + 1)) (hs0 : s0 ∈ Inv 0)
    (Y : S → ℝ) (hY : Measurable Y) (a : ℕ → ℝ) (ha : ∀ e, 0 ≤ a e)
    (hYint : ∀ t, Integrable (fun β => Y (run step s0 β t)) (Measure.infinitePi fun _ : ℕ => ν))
    (n : ℕ)
    (hdrift : ∀ e < n, ∀ s ∈ Inv (e * m),
      ∫ tail, Y (run step s tail m) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ a e * Y s) :
    ∫ β, Y (run step s0 β (n * m)) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      (∏ e ∈ Finset.range n, a e) * Y s0 := by
  induction n with
  | zero =>
    have : (fun β : ℕ → X => Y (run step s0 β (0 * m))) = fun _ => Y s0 := by
      funext β; rw [zero_mul]; rfl
    rw [this]; simp
  | succ n ih =>
    have ih := ih (fun e he => hdrift e (by omega))
    set F : S → (ℕ → X) → ℝ := fun s tail => Y (run step s tail m) with hF
    have hFm : Measurable (Function.uncurry F) := hY.comp (run_measurable₂ step hstep m)
    have hrun : ∀ β, run step s0 β ((n + 1) * m) = run step (run step s0 β (n * m)) (shift (n * m) β) m := by
      intro β; rw [add_mul, one_mul, run_add]
    have hint : Integrable (fun β => F (run step s0 β (n * m)) (shift (n * m) β))
        (Measure.infinitePi fun _ : ℕ => ν) := by
      have := hYint ((n + 1) * m)
      simp_rw [hrun] at this
      exact this
    have h1 := tail_integral step s0 ν hstep (n * m) F hFm hint
    have h2 := tail_inner_integrable step s0 ν hstep (n * m) F hFm hint
    have h3 : ∫ β, (∫ tail, F (run step s0 β (n * m)) tail ∂(Measure.infinitePi fun _ : ℕ => ν))
        ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
        ∫ β, a n * Y (run step s0 β (n * m)) ∂(Measure.infinitePi fun _ : ℕ => ν) := by
      refine integral_mono h2 ((hYint _).const_mul (a n)) (fun β => ?_)
      exact hdrift n (by omega) _ (run_mem_inv step s0 Inv hInv hs0 β _)
    rw [integral_const_mul] at h3
    have h4 : ∫ β, Y (run step s0 β ((n + 1) * m)) ∂(Measure.infinitePi fun _ : ℕ => ν) =
        ∫ β, F (run step s0 β (n * m)) (shift (n * m) β) ∂(Measure.infinitePi fun _ : ℕ => ν) := by
      congr 1; funext β; simp only [hF, hrun]
    rw [h4, h1, Finset.prod_range_succ]
    calc _ ≤ a n * ∫ β, Y (run step s0 β (n * m)) ∂(Measure.infinitePi fun _ : ℕ => ν) := h3
      _ ≤ a n * ((∏ e ∈ Finset.range n, a e) * Y s0) := mul_le_mul_of_nonneg_left ih (ha n)
      _ = (∏ e ∈ Finset.range n, a e) * a n * Y s0 := by ring

end LongTails.Proofs.StrongGrowthAgdBlocks
