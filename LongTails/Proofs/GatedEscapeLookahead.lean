import LongTails.Proofs.StrongGrowthAgdDrift

namespace LongTails.Proofs.GatedEscapeLookahead

open MeasureTheory ProbabilityTheory LongTails.Proofs.StrongGrowthAgdBlocks

variable {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
variable (step : S → X → S) (ν : Measure X) [IsProbabilityMeasure ν]
variable (rem : S → ℕ) (G : S → X → ℝ)

noncomputable def look (s : S) : ℝ :=
  ∫ tail, G (run step s tail (rem s - 1)) (tail (rem s - 1)) ∂(Measure.infinitePi fun _ : ℕ => ν)

lemma look_measurable (hstep : Measurable (Function.uncurry step)) (hrem : Measurable rem)
    (hG : Measurable (Function.uncurry G)) : Measurable (look step ν rem G) := by
  have h2 : Measurable (fun w : (S × (ℕ → X)) × ℕ => G (run step w.1.1 w.1.2 w.2) (w.1.2 w.2)) := by
    refine measurable_from_prod_countable_left (fun m => ?_)
    exact hG.comp ((run_measurable₂ step hstep m).prodMk ((measurable_pi_apply m).comp measurable_snd))
  have h3 : Measurable (fun z : S × (ℕ → X) =>
      G (run step z.1 z.2 (rem z.1 - 1)) (z.2 (rem z.1 - 1))) :=
    h2.comp (measurable_id.prodMk ((hrem.comp measurable_fst).sub_const 1))
  exact (h3.stronglyMeasurable.integral_prod_right' (ν := Measure.infinitePi fun _ : ℕ => ν)).measurable

omit [MeasurableSpace S] in
lemma look_bounds (hG0 : ∀ s y, 0 ≤ G s y) (hG1 : ∀ s y, G s y ≤ 1) (s : S) :
    0 ≤ look step ν rem G s ∧ look step ν rem G s ≤ 1 := by
  unfold look
  refine ⟨integral_nonneg fun _ => hG0 _ _, ?_⟩
  calc ∫ tail, G (run step s tail (rem s - 1)) (tail (rem s - 1)) ∂(Measure.infinitePi fun _ : ℕ => ν)
      ≤ ∫ _tail, (1 : ℝ) ∂(Measure.infinitePi fun _ : ℕ => ν) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => hG0 _ _)
          (integrable_const _) (Filter.Eventually.of_forall fun _ => hG1 _ _)
    _ = 1 := by simp

lemma look_one (hG : Measurable (Function.uncurry G)) (s : S) (hs : rem s = 1) :
    look step ν rem G s = ∫ y, G s y ∂ν := by
  unfold look
  rw [hs]
  exact integral_eval ν (fun y => G s y) (hG.comp (measurable_const.prodMk measurable_id))

lemma look_succ (hstep : Measurable (Function.uncurry step)) (hrem : Measurable rem)
    (hG : Measurable (Function.uncurry G)) (hG0 : ∀ s y, 0 ≤ G s y) (hG1 : ∀ s y, G s y ≤ 1)
    (s : S) (m : ℕ) (hs : rem s = m + 2) (hnext : ∀ y, rem (step s y) = m + 1) :
    look step ν rem G s = ∫ y, look step ν rem G (step s y) ∂ν := by
  set F : S → (ℕ → X) → ℝ := fun s' tail => G (run step s' tail m) (tail m) with hFdef
  have hF : Measurable (Function.uncurry F) :=
    hG.comp ((run_measurable₂ step hstep m).prodMk ((measurable_pi_apply m).comp measurable_snd))
  have hint : Integrable (fun β => F (run step s β 1) (shift 1 β)) (Measure.infinitePi fun _ : ℕ => ν) := by
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun β => ?_)
    · exact (hF.comp ((run_measurable step s hstep 1).prodMk (shift_measurable 1))).aestronglyMeasurable
    · simp only [hFdef]
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 _ _)]; exact hG1 _ _
  have h1 : look step ν rem G s = ∫ β, F (run step s β 1) (shift 1 β) ∂(Measure.infinitePi fun _ : ℕ => ν) := by
    unfold look
    rw [hs]
    refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
    simp only [hFdef, shift]
    rw [show m + 2 - 1 = 1 + m by omega, run_add]
  rw [h1, tail_integral step s ν hstep 1 F hF hint]
  have h2 : ∀ β : ℕ → X, (∫ tail, F (run step s β 1) tail ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      look step ν rem G (step s (β 0)) := by
    intro β
    unfold look
    rw [hnext]
    rfl
  simp_rw [h2]
  exact integral_eval ν (fun y => look step ν rem G (step s y))
    ((look_measurable step ν rem G hstep hrem hG).comp (hstep.comp (measurable_const.prodMk measurable_id)))

noncomputable def endBad (s : S) (tail : ℕ → X) : ℝ := if rem s = 1 then G s (tail 0) else 0

theorem phase_count (hstep : Measurable (Function.uncurry step)) (hrem : Measurable rem)
    (hG : Measurable (Function.uncurry G)) (hG0 : ∀ s y, 0 ≤ G s y) (hG1 : ∀ s y, G s y ≤ 1)
    (s0 : S) (Inv : Set S) (hInv : ∀ s ∈ Inv, ∀ y, step s y ∈ Inv) (hs0 : s0 ∈ Inv)
    {p : ℝ} {M Lmax : ℕ} (hp : 0 ≤ p) (hLmax : ∀ s ∈ Inv, rem s ≤ Lmax)
    (hcase : ∀ s ∈ Inv, ((∀ y, step s y = s) ∧ rem s = 0) ∨
      (2 ≤ rem s ∧ ∀ y, rem (step s y) = rem s - 1) ∨
      (rem s = 1 ∧ ∀ y, look step ν rem G (step s y) ≤ (p / M) * rem (step s y)))
    (hstart : look step ν rem G s0 ≤ p) (N : ℕ) :
    ∑ e ∈ Finset.range N, ∫ β, endBad rem G (run step s0 β e) (shift e β)
        ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ p + N * (p / M) + Lmax * (p / M) := by
  set Y : S → ℝ := fun s => look step ν rem G s - (p / M) * rem s with hY
  have hlm := look_measurable step ν rem G hstep hrem hG
  have hYm : Measurable Y := hlm.sub (measurable_const.mul (measurable_from_top.comp hrem))
  have hDm : Measurable (Function.uncurry (endBad rem G)) := by
    unfold endBad
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (hrem.comp measurable_fst) (measurableSet_singleton 1)
    · exact hG.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  have hpM : 0 ≤ p / M := div_nonneg hp (Nat.cast_nonneg _)
  set Invt : ℕ → Set S := fun _ => Inv
  have hInvt : ∀ t, ∀ s ∈ Invt t, ∀ x, step s x ∈ Invt (t + 1) := fun _ s hs x => hInv s hs x
  have hmem : ∀ β t, run step s0 β t ∈ Inv := fun β t => run_mem_inv step s0 Invt hInvt hs0 β t
  have hYbd : ∀ s ∈ Inv, |Y s| ≤ 1 + (p / M) * Lmax := by
    intro s hs
    obtain ⟨l0, l1⟩ := look_bounds step ν rem G hG0 hG1 s
    have hr : (rem s : ℝ) ≤ Lmax := by exact_mod_cast hLmax s hs
    have hr0 : (0 : ℝ) ≤ rem s := Nat.cast_nonneg _
    rw [abs_le]
    simp only [hY]
    constructor <;> nlinarith
  have hYint : ∀ t, Integrable (fun β => Y (run step s0 β t)) (Measure.infinitePi fun _ : ℕ => ν) := by
    intro t
    refine Integrable.of_bound (C := 1 + (p / M) * Lmax)
      (hYm.comp (run_measurable step s0 hstep t)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => ?_)
    rw [Real.norm_eq_abs]; exact hYbd _ (hmem β t)
  have hDint : ∀ e, Integrable (fun β => endBad rem G (run step s0 β (e * 1)) (shift (e * 1) β))
      (Measure.infinitePi fun _ : ℕ => ν) := by
    intro e
    refine Integrable.of_bound (C := 1)
      (hDm.comp ((run_measurable step s0 hstep _).prodMk (shift_measurable _))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => ?_)
    simp only [endBad]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (hG0 _ _)]; exact hG1 _ _
    · simp
  have hdr := drift step s0 ν hstep 1 Invt hInvt hs0 Y (fun _ => p / M) (endBad rem G) hYm
    measurable_const hDm hYint (fun _ => integrable_const _) hDint N (by
      intro e _ s hs
      have hrun1 : ∀ tail : ℕ → X, run step s tail 1 = step s (tail 0) := fun _ => rfl
      simp_rw [hrun1]
      have hfun : Measurable (fun y => Y (step s y) + (if rem s = 1 then G s y else 0)) := by
        refine (hYm.comp (hstep.comp (measurable_const.prodMk measurable_id))).add ?_
        split_ifs
        · exact hG.comp (measurable_const.prodMk measurable_id)
        · exact measurable_const
      have hev := integral_eval ν (fun y => Y (step s y) + (if rem s = 1 then G s y else 0)) hfun
      simp only [endBad]
      rw [hev]
      have hbd2 : ∀ y, |Y (step s y)| ≤ 1 + (p / M) * Lmax := fun y => hYbd _ (hInv s hs y)
      have hYi : Integrable (fun y => Y (step s y)) ν :=
        Integrable.of_bound (C := 1 + (p / M) * Lmax)
          (hYm.comp (hstep.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hbd2 y)
      have hlook_i : Integrable (fun y => look step ν rem G (step s y)) ν :=
        Integrable.of_bound (C := 1)
          (hlm.comp (hstep.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => by
            obtain ⟨l0, l1⟩ := look_bounds step ν rem G hG0 hG1 (step s y)
            rw [Real.norm_eq_abs, abs_of_nonneg l0]; exact l1)
      have hGi : Integrable (fun y => G s y) ν :=
        Integrable.of_bound (C := 1)
          (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hG0 _ _)]; exact hG1 _ _)
      rcases hcase s hs with ⟨habs, h0⟩ | ⟨h2, hnext⟩ | ⟨h1, hnew⟩
      · have h01 : ¬ rem s = 1 := by omega
        simp only [ite_eq_right h01, add_zero, habs]
        rw [integral_const]; simp only [probReal_univ, one_smul]
        linarith
      · have h1 : ¬ rem s = 1 := by omega
        simp only [ite_eq_right h1, add_zero]
        obtain ⟨m, hm⟩ : ∃ m, rem s = m + 2 := ⟨rem s - 2, by omega⟩
        have hnext' : ∀ y, rem (step s y) = m + 1 := fun y => by rw [hnext y, hm]; rfl
        have hls := look_succ step ν rem G hstep hrem hG hG0 hG1 s m hm hnext'
        have hYeq : ∀ y, Y (step s y) = look step ν rem G (step s y) - (p / M) * (m + 1 : ℕ) := by
          intro y; simp only [hY, hnext' y]
        simp_rw [hYeq]
        rw [integral_sub hlook_i (integrable_const _), ← hls, integral_const]
        simp only [probReal_univ, one_smul, hY, hm]
        push_cast
        linarith
      · simp only [ite_eq_left h1]
        rw [integral_add hYi hGi, ← look_one step ν rem G hG s h1]
        have hYle : ∫ y, Y (step s y) ∂ν ≤ ∫ _y, (0 : ℝ) ∂ν := by
          refine integral_mono hYi (integrable_const _) (fun y => ?_)
          have hl := hnew y
          simp only [hY]; linarith
        simp only [integral_zero] at hYle
        simp only [hY, h1, Nat.cast_one]
        linarith)
  simp only [mul_one, integral_const, probReal_univ, one_smul, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hdr
  have hYN : -((p / M) * Lmax) ≤ ∫ β, Y (run step s0 β N) ∂(Measure.infinitePi fun _ : ℕ => ν) := by
    have : ∫ _β, (-((p / M) * Lmax)) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
        ∫ β, Y (run step s0 β N) ∂(Measure.infinitePi fun _ : ℕ => ν) := by
      refine integral_mono (integrable_const _) (hYint N) (fun β => ?_)
      have hs := hmem β N
      obtain ⟨l0, _⟩ := look_bounds step ν rem G hG0 hG1 (run step s0 β N)
      have hr : (rem (run step s0 β N) : ℝ) ≤ Lmax := by exact_mod_cast hLmax _ hs
      simp only [hY]
      nlinarith
    simpa using this
  have hY0 : Y s0 ≤ p := by
    simp only [hY]
    have : 0 ≤ (p / M) * rem s0 := mul_nonneg hpM (Nat.cast_nonneg _)
    linarith
  nlinarith

end LongTails.Proofs.GatedEscapeLookahead
