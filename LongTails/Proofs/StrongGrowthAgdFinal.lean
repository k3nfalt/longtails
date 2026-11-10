import LongTails.Proofs.StrongGrowthAgdTrial

namespace LongTails.Proofs.StrongGrowthAgdFinal

open MeasureTheory LongTails.Algorithms.StrongGrowthRestartedAgd LongTails.Proofs.StrongGrowthAgdProcess
  LongTails.Proofs.StrongGrowthAgdMoments LongTails.Proofs.StrongGrowthAgdMeasurable
  LongTails.Proofs.StrongGrowthAgdWeights LongTails.Proofs.StrongGrowthAgdModel
  LongTails.Proofs.StrongGrowthAgdEpochEnd LongTails.Proofs.StrongGrowthAgdInvariant
  LongTails.Proofs.StrongGrowthAgdEpoch LongTails.Proofs.StrongGrowthAgdBlocks
  LongTails.Proofs.StrongGrowthAgdEpochRun LongTails.Proofs.StrongGrowthAgdCounting
  LongTails.Proofs.StrongGrowthAgdValidation LongTails.Proofs.StrongGrowthAgdTrial
open scoped RealInnerProductSpace
open Classical

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {cfg : Config} {x0 : E} {g : E → Ω → E} {f : E → ℝ} {L ρ κ Δ εi : ℝ}
variable (H : Hyps cfg x0 g f p L ρ κ Δ εi)
include H

noncomputable abbrev s₀ (_cfg : Config) (x0 : E) : State E × E := (initState x0, 0)

omit H [MeasurableSpace E] [BorelSpace E] in
lemma s₀_inv (hc : CfgHyp cfg) : Inv cfg x0 f ρ (s₀ cfg x0) := inv_init cfg x0 f ρ hc 0

omit H [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma out_step (sN : State E × E) (ω : Fin cfg.b → Ω) (hd : (astep cfg x0 g f sN ω).1.done = false) :
    (astep cfg x0 g f sN ω).1.out = sN.1.out := by
  obtain ⟨s, N⟩ := sN
  rw [astep_fst] at hd ⊢
  by_cases hs : s.done = true
  · rw [blockStep_of_done cfg x0 g hs]
  have hs' : s.done = false := by simpa using hs
  unfold blockStep batchUpdate restart
  simp only [hs', Bool.false_eq_true, ↓reduceIte]
  unfold blockStep batchUpdate restart at hd
  simp only [hs', Bool.false_eq_true, ↓reduceIte] at hd
  split_ifs at hd ⊢ <;> rfl

omit H [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma out_run (tail : ℕ → (Fin cfg.b → Ω)) (t : ℕ)
    (hd : (run (astep cfg x0 g f) (s₀ cfg x0) tail t).1.done = false) :
    (run (astep cfg x0 g f) (s₀ cfg x0) tail t).1.out = x0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ] at hd ⊢
    rw [out_step _ _ hd, ih (not_done_of_step hd)]

omit H in
lemma first_switch (d : ℕ → Bool) (_hmono : ∀ i j, i ≤ j → d i = true → d j = true) :
    ∀ n, d 0 = false → d n = true → ∃ e < n, d e = false ∧ d (e + 1) = true := by
  intro n
  induction n with
  | zero => intro h0 hn; rw [h0] at hn; exact Bool.noConfusion hn
  | succ n ih =>
    intro h0 hn
    by_cases hdn : d n = true
    · obtain ⟨e, he, h1, h2⟩ := ih h0 hdn
      exact ⟨e, by omega, h1, h2⟩
    · exact ⟨n, by omega, by simpa using hdn, hn⟩

theorem fail_all (hq : ∀ sN : State E × E, TrialStart (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN →
      sN.1.done = false →
      ∫ tail, (if (run (astep cfg x0 g f) sN tail (cfg.N1 * cfg.Eb)).1.done = false then (1 : ℝ) else 0)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤ 1 / 4) (R : ℕ) :
    ∫ tail, (if (run (astep cfg x0 g f) (s₀ cfg x0) tail (R * (cfg.N1 * cfg.Eb))).1.done = false
        then (1 : ℝ) else 0) ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      (1 / 4) ^ R := by
  set ν := (Measure.pi fun _ : Fin cfg.b => p) with hν
  let Y : State E × E → ℝ := fun sN => if sN.1.done = false then 1 else 0
  have hY : Measurable Y :=
    Measurable.ite ((measurable_done.comp measurable_fst) (MeasurableSet.of_discrete (s := {false})))
      measurable_const measurable_const
  have hYint : ∀ t, Integrable (fun tail => Y (run (astep cfg x0 g f) (s₀ cfg x0) tail t))
      (Measure.infinitePi fun _ : ℕ => ν) := fun t =>
    (integrable_const (1 : ℝ)).mono' (hY.comp (run_measurable _ _ (measurable_astep' H) t)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun tail => by simp only [Y]; split_ifs <;> simp)
  have hdr := drift_mul (astep cfg x0 g f) (s₀ cfg x0) ν (measurable_astep' H) (cfg.N1 * cfg.Eb)
    (InvE (s₀ cfg x0)) (fun t sN' h ω => InvE_step H _ t sN' h ω) ⟨s₀_inv H.hc, fun _ => rfl⟩ Y hY
    (fun _ => 1 / 4) (fun _ => by norm_num) hYint R (fun e _ sN' h => by
      by_cases hd : sN'.1.done = true
      · have hrun : ∀ tail, run (astep cfg x0 g f) sN' tail (cfg.N1 * cfg.Eb) = sN' := fun tail => run_of_done hd tail _
        simp only [hrun, Y, hd, Bool.true_eq_false, ↓reduceIte, integral_const, probReal_univ,
          one_smul, mul_zero, le_refl]
      · have hd' : sN'.1.done = false := by simpa using hd
        have hts : TrialStart (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN' := by
          refine ⟨h.1, ?_⟩
          rw [h.2 hd']
          show (0 + e * (cfg.N1 * cfg.Eb)) % (cfg.N1 * cfg.Eb) = 0
          rw [zero_add, Nat.mul_mod_left]
        have := hq sN' hts hd'
        simp only [Y, hd', ↓reduceIte, mul_one]
        exact this)
  rw [Finset.prod_const, Finset.card_range] at hdr
  simp only [Y, s₀, initState, ↓reduceIte, mul_one] at hdr
  exact hdr

noncomputable def accInd (tail : ℕ → (Fin cfg.b → Ω)) (e : ℕ) : ℝ :=
  if (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.done = false ∧
      (run (astep cfg x0 g f) (s₀ cfg x0) tail ((e + 1) * cfg.Eb)).1.done = true then 1 else 0

omit H [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma sum_accInd_le (tail : ℕ → (Fin cfg.b → Ω)) (n : ℕ) :
    ∑ e ∈ Finset.range n, accInd (cfg := cfg) (x0 := x0) (g := g) (f := f) tail e ≤ 1 := by
  let d : ℕ → ℝ := fun k => if (run (astep cfg x0 g f) (s₀ cfg x0) tail (k * cfg.Eb)).1.done = true then 1 else 0
  have hmono : ∀ k, d k ≤ d (k + 1) := by
    intro k
    simp only [d]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exfalso
      exact h2 (run_done_of_done _ tail (Nat.mul_le_mul_right _ (Nat.le_succ k)) h1)
    · norm_num
    · exact le_rfl
  have heq : ∀ e, accInd (cfg := cfg) (x0 := x0) (g := g) (f := f) tail e = d (e + 1) - d e := by
    intro e
    simp only [accInd, d]
    by_cases h1 : (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.done = true
    · have h2 : (run (astep cfg x0 g f) (s₀ cfg x0) tail ((e + 1) * cfg.Eb)).1.done = true :=
        run_done_of_done _ tail (Nat.mul_le_mul_right _ (Nat.le_succ e)) h1
      rw [ite_eq_left h1, ite_eq_left h2,
        ite_eq_right (fun h => by rw [h.1] at h1; exact Bool.noConfusion h1)]
      norm_num
    · have h1' : (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.done = false := by simpa using h1
      rw [ite_eq_right h1]
      by_cases h2 : (run (astep cfg x0 g f) (s₀ cfg x0) tail ((e + 1) * cfg.Eb)).1.done = true
      · rw [ite_eq_left h2, ite_eq_left ⟨h1', h2⟩]; norm_num
      · rw [ite_eq_right h2, ite_eq_right (fun h => h2 h.2)]; norm_num
  simp_rw [heq]
  rw [Finset.sum_range_sub]
  have h0 : d 0 = 0 := by simp [d, initState, run_zero]
  have h1 : d n ≤ 1 := by simp only [d]; split_ifs <;> norm_num
  linarith

omit [IsProbabilityMeasure p] [BorelSpace E] in
theorem output_pointwise (R : ℕ) (tail : ℕ → (Fin cfg.b → Ω)) :
    ‖gradient f (run (astep cfg x0 g f) (s₀ cfg x0) tail (R * cfg.N1 * cfg.Eb)).1.out‖ ≤
      ‖gradient f x0‖ * (if (run (astep cfg x0 g f) (s₀ cfg x0) tail (R * cfg.N1 * cfg.Eb)).1.done = false
          then (1 : ℝ) else 0) +
      ∑ e ∈ Finset.range (R * cfg.N1), (3 * εi * accInd (cfg := cfg) (x0 := x0) (g := g) (f := f) tail e +
        wbadE cfg x0 g f εi (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)) := by
  set T := R * cfg.N1 * cfg.Eb with hT
  have hnn : ∀ e ∈ Finset.range (R * cfg.N1), 0 ≤ 3 * εi * accInd (cfg := cfg) (x0 := x0) (g := g) (f := f) tail e +
      wbadE cfg x0 g f εi (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail) := by
    intro e _
    have := H.hεi
    unfold accInd wbadE
    split_ifs <;> positivity
  by_cases hd : (run (astep cfg x0 g f) (s₀ cfg x0) tail T).1.done = false
  · rw [ite_eq_left hd, mul_one, out_run tail T hd]
    linarith [Finset.sum_nonneg hnn]
  · have hd' : (run (astep cfg x0 g f) (s₀ cfg x0) tail T).1.done = true := by simpa using hd
    rw [ite_eq_right hd, mul_zero, zero_add]
    let d : ℕ → Bool := fun k => (run (astep cfg x0 g f) (s₀ cfg x0) tail (k * cfg.Eb)).1.done
    have hmono : ∀ i j, i ≤ j → d i = true → d j = true := fun i j hij h =>
      run_done_of_done _ tail (Nat.mul_le_mul_right _ hij) h
    obtain ⟨e, he, h1, h2⟩ := first_switch d hmono (R * cfg.N1) (by simp [d, initState, run_zero])
      (by simp only [d]; rw [show R * cfg.N1 * cfg.Eb = T by rw [hT]]; exact hd')
    simp only [d] at h1 h2
    set sE := run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb) with hsE
    have hinvE : Inv cfg x0 f ρ sE := run_inv H.hc H.h (s₀_inv H.hc) tail _
    have hposE : cfg.pos sE.1.t = 0 :=
      pos_epoch_start ⟨s₀_inv H.hc, by simp [initState]⟩ e (InvE_run H _ tail (s₀_inv H.hc) _) h1
    have hrunE : run (astep cfg x0 g f) (s₀ cfg x0) tail ((e + 1) * cfg.Eb) =
        run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.Eb := by
      rw [add_mul, one_mul, run_add]
    rw [hrunE] at h2
    obtain ⟨hiff, hout⟩ := done_run_Eb cfg x0 g f H hinvE hposE h1 (shift (e * cfg.Eb) tail)
    have hacc := hiff.mp h2
    have houtE := hout hacc
    have hfrozen : (run (astep cfg x0 g f) (s₀ cfg x0) tail T).1.out =
        (run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.Eb).1.out := by
      have hle : (e + 1) * cfg.Eb ≤ T := by
        rw [hT]; exact Nat.mul_le_mul_right _ (by omega)
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk, run_add, run_of_done (by rw [hrunE]; exact h2), hrunE]
    rw [hfrozen, houtE]
    have hacce : accInd (cfg := cfg) (x0 := x0) (g := g) (f := f) tail e = 1 := by
      unfold accInd; rw [ite_eq_left ⟨h1, by rw [hrunE]; exact h2⟩]
    have hterm : ‖gradient f (run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.K).1.ybar‖ ≤
        3 * εi * accInd (cfg := cfg) (x0 := x0) (g := g) (f := f) tail e +
          wbadE cfg x0 g f εi sE (shift (e * cfg.Eb) tail) := by
      rw [hacce, mul_one]
      unfold wbadE
      split_ifs with hw
      · linarith [H.hεi]
      · push Not at hw
        have := hw h1 h2
        linarith
    calc _ ≤ 3 * εi * accInd (cfg := cfg) (x0 := x0) (g := g) (f := f) tail e +
          wbadE cfg x0 g f εi sE (shift (e * cfg.Eb) tail) := hterm
      _ ≤ _ := Finset.single_le_sum hnn (Finset.mem_range.mpr he)

omit H [MeasurableSpace E] [BorelSpace E] in
lemma grad_le_gap (h : Hyp f L ρ) (fLow : ℝ) (hlow : ∀ x, fLow ≤ f x) (x : E) :
    ‖gradient f x‖ ^ 2 ≤ 2 * L * (f x - fLow) := by
  have h1 := OracleTemplate.Gradient.descent h.hL h.hasGrad h.lip x
  have h2 := hlow (x - (1 / L) • gradient f x)
  have hL := h.hL
  have : ‖gradient f x‖ ^ 2 / (2 * L) ≤ f x - fLow := by linarith
  rwa [div_le_iff₀ (by positivity), mul_comm] at this

omit H [MeasurableSpace E] [BorelSpace E] in
lemma grad_le_tau (h : Hyp f L ρ) (fLow : ℝ) (hlow : ∀ x, fLow ≤ f x) (τ : ℝ) (hτ : 0 < τ) (x : E) :
    ‖gradient f x‖ ≤ τ / 2 + L / τ * (f x - fLow) := by
  have h1 := grad_le_gap h fLow hlow x
  have h2 : ‖gradient f x‖ ≤ τ / 2 + ‖gradient f x‖ ^ 2 / (2 * τ) := by
    have hc : ‖gradient f x‖ ^ 2 / (2 * τ) * (2 * τ) = ‖gradient f x‖ ^ 2 :=
      div_mul_cancel₀ _ (by positivity)
    have key : ‖gradient f x‖ * (2 * τ) ≤ (τ / 2 + ‖gradient f x‖ ^ 2 / (2 * τ)) * (2 * τ) := by
      rw [add_mul, hc]
      nlinarith [sq_nonneg (‖gradient f x‖ - τ)]
    exact le_of_mul_le_mul_right key (by positivity)
  have h3 : ‖gradient f x‖ ^ 2 / (2 * τ) ≤ L / τ * (f x - fLow) := by
    rw [div_le_iff₀ (by positivity)]
    have : L / τ * (f x - fLow) * (2 * τ) = 2 * L * (f x - fLow) := by field_simp
    rw [this]; exact h1
  linarith

theorem gap_all (e : ℕ) :
    ∫ tail, (if (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.done = false then
        f (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.x - (f x0 - Δ) else 0)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      Δ + cfg.N1 * cEpoch cfg ρ := by
  set ν := (Measure.pi fun _ : Fin cfg.b => p) with hν
  have hN1 := H.hN1
  set r' := e / cfg.N1 with hr'
  set j := e % cfg.N1 with hj
  have hej : e = r' * cfg.N1 + j := by rw [hr', hj, Nat.mul_comm]; exact (Nat.div_add_mod e cfg.N1).symm
  have hjN : j < cfg.N1 := Nat.mod_lt _ hN1
  have hsplit : e * cfg.Eb = r' * (cfg.N1 * cfg.Eb) + j * cfg.Eb := by rw [hej]; ring
  let F : State E × E → (ℕ → (Fin cfg.b → Ω)) → ℝ := fun s tail =>
    if (run (astep cfg x0 g f) s tail (j * cfg.Eb)).1.done = false then
      f (run (astep cfg x0 g f) s tail (j * cfg.Eb)).1.x - (f x0 - Δ) else 0
  have hFm : Measurable (Function.uncurry F) := by
    have hrun := run_measurable₂ (astep cfg x0 g f) (measurable_astep' H) (j * cfg.Eb)
    refine Measurable.ite ((measurable_done.comp (measurable_fst.comp hrun))
      (MeasurableSet.of_discrete (s := {false}))) ?_ measurable_const
    exact (H.h.hf.continuous.measurable.comp (measurable_x.comp (measurable_fst.comp hrun))).sub_const _
  have hrw : ∀ tail, (if (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.done = false then
      f (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.x - (f x0 - Δ) else 0) =
      F (run (astep cfg x0 g f) (s₀ cfg x0) tail (r' * (cfg.N1 * cfg.Eb))) (shift (r' * (cfg.N1 * cfg.Eb)) tail) := by
    intro tail; simp only [F]; rw [hsplit, run_add]
  simp_rw [hrw]
  have hFint : Integrable (fun tail => F (run (astep cfg x0 g f) (s₀ cfg x0) tail (r' * (cfg.N1 * cfg.Eb)))
      (shift (r' * (cfg.N1 * cfg.Eb)) tail)) (Measure.infinitePi fun _ : ℕ => ν) := by
    have hYi := Yep_run_integrable H (s₀ cfg x0) (e * cfg.Eb)
    refine ((hYi.add (integrable_const Δ)).add (integrable_const (|f x0 - Δ| + Δ))).mono'
      (hFm.comp ((run_measurable _ _ (measurable_astep' H) _).prodMk (shift_measurable _))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun tail => ?_)
    rw [← hrw tail, Real.norm_eq_abs]
    simp only [Pi.add_apply]
    unfold Yep
    set sX := run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb) with hsX
    have hx : f x0 - Δ ≤ f sX.1.x := by linarith [H.hΔ sX.1.x]
    have hite : (if isStart cfg sX.1 then Δ else 0) ≤ Δ := by split_ifs <;> linarith [H.hΔ0]
    by_cases h1 : sX.1.done = false
    · rw [ite_eq_left h1, abs_of_nonneg (by linarith)]
      linarith [abs_nonneg (f x0 - Δ), H.hΔ0]
    · rw [ite_eq_right h1, abs_zero]
      linarith [abs_nonneg (f x0 - Δ), H.hΔ0]
  rw [tail_integral (astep cfg x0 g f) (s₀ cfg x0) ν (measurable_astep' H) _ F hFm hFint]
  have hinner : ∀ tail, ∫ tail', F (run (astep cfg x0 g f) (s₀ cfg x0) tail (r' * (cfg.N1 * cfg.Eb))) tail'
      ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ Δ + cfg.N1 * cEpoch cfg ρ := by
    intro tail
    set sR := run (astep cfg x0 g f) (s₀ cfg x0) tail (r' * (cfg.N1 * cfg.Eb)) with hsR
    by_cases hd : sR.1.done = false
    · have hts : TrialStart (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sR := by
        refine ⟨run_inv H.hc H.h (s₀_inv H.hc) tail _, ?_⟩
        have := (InvE_run H (s₀ cfg x0) tail (s₀_inv H.hc) (r' * (cfg.N1 * cfg.Eb))).2 hd
        rw [this]
        show (0 + r' * (cfg.N1 * cfg.Eb)) % (cfg.N1 * cfg.Eb) = 0
        rw [zero_add, Nat.mul_mod_left]
      have hgap := trial_gap H hts hd j hjN
      refine le_trans ?_ hgap
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun tail' => ?_) ?_
        (Filter.Eventually.of_forall fun tail' => ?_)
      · simp only [F, Pi.zero_apply]; split_ifs
        · linarith [H.hΔ (run (astep cfg x0 g f) sR tail' (j * cfg.Eb)).1.x]
        · exact le_rfl
      · have := Yep_run_integrable H sR (j * cfg.Eb)
        have heq : ∀ tail', f (run (astep cfg x0 g f) sR tail' (j * cfg.Eb)).1.x - (f x0 - Δ) =
            Yep cfg x0 f Δ (run (astep cfg x0 g f) sR tail' (j * cfg.Eb)) +
              (if isStart cfg (run (astep cfg x0 g f) sR tail' (j * cfg.Eb)).1 then Δ else 0) := by
          intro tail'; unfold Yep; ring
        simp_rw [heq]
        refine this.add ?_
        refine (integrable_const Δ).mono' ?_ (Filter.Eventually.of_forall fun tail' => ?_)
        · exact (Measurable.ite (MeasurableSet.inter ((measurable_done.comp (measurable_fst.comp
            (run_measurable _ _ (measurable_astep' H) _))) (MeasurableSet.of_discrete (s := {false})))
            ((measurable_t.comp (measurable_fst.comp (run_measurable _ _ (measurable_astep' H) _)))
              (MeasurableSet.of_discrete (s := {n | n % (cfg.N1 * cfg.Eb) = 0}))))
            measurable_const measurable_const).aestronglyMeasurable
        · rw [Real.norm_eq_abs]; split_ifs <;> simp [abs_of_nonneg H.hΔ0, H.hΔ0]
      · simp only [F]; split_ifs
        · exact le_rfl
        · linarith [H.hΔ (run (astep cfg x0 g f) sR tail' (j * cfg.Eb)).1.x]
    · have hd' : sR.1.done = true := by simpa using hd
      have heq : ∀ tail', F sR tail' = 0 := by
        intro tail'; simp only [F]; rw [run_of_done hd', ite_eq_right (by simp [hd'])]
      simp_rw [heq]
      rw [integral_zero]
      have := cEpoch_nonneg H
      have := H.hΔ0
      positivity
  calc _ ≤ ∫ tail, (Δ + cfg.N1 * cEpoch cfg ρ) ∂(Measure.infinitePi fun _ : ℕ => ν) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun tail => integral_nonneg fun tail' => by
          simp only [F, Pi.zero_apply]; split_ifs
          · linarith [H.hΔ (run (astep cfg x0 g f) (run (astep cfg x0 g f) (s₀ cfg x0) tail
              (r' * (cfg.N1 * cfg.Eb))) tail' (j * cfg.Eb)).1.x]
          · exact le_rfl) (integrable_const _) (Filter.Eventually.of_forall hinner)
    _ = _ := by simp

theorem wbad_sum (τ : ℝ) (hτ : 0 < τ) (n : ℕ) :
    ∑ e ∈ Finset.range n, ∫ tail, wbadE cfg x0 g f εi (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb))
        (shift (e * cfg.Eb) tail) ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      n * (((1 + 3 * (4 * ((κ - 1) / cfg.b))) / 2) ^ cfg.m *
        (τ / 2 + L / τ * (Δ + cfg.N1 * cEpoch cfg ρ) + 2 * L * cfg.B)) := by
  set ν := (Measure.pi fun _ : Fin cfg.b => p) with hν
  set r := ((1 + 3 * (4 * ((κ - 1) / cfg.b))) / 2) ^ cfg.m with hr
  have hq0 : 0 ≤ (κ - 1) / cfg.b := div_nonneg (by linarith [H.hκ]) (Nat.cast_nonneg _)
  have hr0 : 0 ≤ r := by rw [hr]; exact pow_nonneg (div_nonneg (by linarith) (by norm_num)) _
  have hL := H.h.hL
  have hB := H.hc.hB
  have hlow : ∀ x, f x0 - Δ ≤ f x := fun x => by linarith [H.hΔ x]
  let Ge : State E × E → ℝ := fun s => if s.1.done = false then ‖gradient f s.1.x‖ + 2 * L * cfg.B else 0
  have hGe : Measurable Ge :=
    Measurable.ite ((measurable_done.comp measurable_fst) (MeasurableSet.of_discrete (s := {false})))
      (((gradient_measurable f H.h).comp (measurable_x.comp measurable_fst)).norm.add_const _) measurable_const
  have hGeW : ∀ sN, |Ge sN| ≤ (2 * ‖gradient f x0‖ ^ 2 + 2 * L ^ 2 + 1 + 2 * L * cfg.B) * W x0 sN := by
    intro sN
    have hW := W_pos x0 sN
    simp only [Ge]
    split_ifs
    · rw [abs_of_nonneg (by positivity)]
      have h1 := gradf_sq_le x0 f H.h sN.1.x
      have hWx : ‖sN.1.x - x0‖ ^ 2 ≤ W x0 sN := by
        unfold W; nlinarith [sq_nonneg ‖sN.1.xPrev - x0‖, sq_nonneg ‖sN.1.xStart - x0‖, sq_nonneg ‖sN.1.glast‖,
          sq_nonneg ‖sN.1.ybar‖, sq_nonneg ‖sN.2‖]
      have h2 : ‖gradient f sN.1.x‖ ≤ (‖gradient f sN.1.x‖ ^ 2 + 1) / 2 := by
        nlinarith [sq_nonneg (‖gradient f sN.1.x‖ - 1)]
      have t1 : ‖gradient f x0‖ ^ 2 ≤ ‖gradient f x0‖ ^ 2 * W x0 sN := le_mul_of_one_le_right (sq_nonneg _) hW
      have t2 : L ^ 2 * ‖sN.1.x - x0‖ ^ 2 ≤ L ^ 2 * W x0 sN := mul_le_mul_of_nonneg_left hWx (sq_nonneg _)
      have t3 : 2 * L * cfg.B ≤ 2 * L * cfg.B * W x0 sN := le_mul_of_one_le_right (by positivity) hW
      have t4 := mul_nonneg (sq_nonneg ‖gradient f x0‖) (by linarith : (0:ℝ) ≤ W x0 sN)
      have t5 := mul_nonneg (sq_nonneg L) (by linarith : (0:ℝ) ≤ W x0 sN)
      linarith
    · rw [abs_zero]; positivity
  have hGeint : ∀ e, Integrable (fun tail => Ge (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)))
      (Measure.infinitePi fun _ : ℕ => ν) := fun e => integrable_of_le_W H Ge hGe _ hGeW _ _
  have hWi : ∀ e, Integrable (fun tail => wbadE cfg x0 g f εi (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb))
      (shift (e * cfg.Eb) tail)) (Measure.infinitePi fun _ : ℕ => ν) := by
    intro e
    refine (hGeint e).mono' ((wbadE_measurable H).comp ((run_measurable _ _ (measurable_astep' H) _).prodMk
      (shift_measurable _))).aestronglyMeasurable (Filter.Eventually.of_forall fun tail => ?_)
    rw [Real.norm_eq_abs]
    set sE := run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb) with hsE
    unfold wbadE
    simp only [Ge]
    split_ifs with h1 h2 h2
    · rw [abs_of_nonneg (norm_nonneg _)]
      obtain ⟨hd, hdone, _⟩ := h1
      have hinvE : Inv cfg x0 f ρ sE := run_inv H.hc H.h (s₀_inv H.hc) tail _
      have hposE : cfg.pos sE.1.t = 0 :=
        pos_epoch_start ⟨s₀_inv H.hc, by simp [initState]⟩ e (InvE_run H _ tail (s₀_inv H.hc) _) hd
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := run_val_fields cfg x0 g f H hinvE hposE hd (shift (e * cfg.Eb) tail)
        cfg.K le_rfl (by have := K_lt_Eb cfg; omega)
      have hposK : cfg.pos (run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.K).1.t = cfg.K := by
        rw [a5]; exact pos_add_of_zero cfg hposE (K_lt_Eb cfg)
      have hinvK : Inv cfg x0 f ρ (run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.K) :=
        run_inv H.hc H.h hinvE (shift (e * cfg.Eb) tail) cfg.K
      have htrK : (run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.K).1.trig = false := by
        obtain ⟨b1, _, _, _, _, _⟩ := run_val_fields cfg x0 g f H hinvE hposE hd (shift (e * cfg.Eb) tail)
          (cfg.Eb - 1) (by have := K_lt_Eb cfg; omega) le_rfl
        obtain ⟨hiff, _⟩ := done_run_Eb cfg x0 g f H hinvE hposE hd (shift (e * cfg.Eb) tail)
        have hacc := hiff.mp hdone
        rw [← b1]; exact hacc.1
      have hA := hinvK.hagd a4 (by rw [hposK]) htrK
      have hK2 : 2 ≤ cfg.K := by have := H.hc.hK; omega
      have hyb := hA.hyb
      have hws : wsum cfg cfg.K = 1 := sum_pw hK2
      rw [hposK, hws, one_smul, mul_one] at hyb
      have hxS : (run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.K).1.xStart = sE.1.x := by
        rw [a3]
        exact ((hinvE.hagd hd (by rw [hposE]; exact Nat.zero_le _) (hinvE.hfresh hd hposE)).hstart hposE).2.1.symm
      rw [hxS] at hyb
      have hl := H.h.lip (run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.K).1.ybar sE.1.x
      have hn := norm_sub_norm_le (gradient f (run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.K).1.ybar)
        (gradient f sE.1.x)
      nlinarith
    · exact absurd h1.1 h2
    · rw [abs_zero]; positivity
    · rw [abs_zero]
  have hterm : ∀ e, ∫ tail, wbadE cfg x0 g f εi (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb))
      (shift (e * cfg.Eb) tail) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      r * (τ / 2 + L / τ * (Δ + cfg.N1 * cEpoch cfg ρ) + 2 * L * cfg.B) := by
    intro e
    rw [tail_integral (astep cfg x0 g f) (s₀ cfg x0) ν (measurable_astep' H) _ _ (wbadE_measurable H) (hWi e)]
    have hinner : ∀ tail, ∫ tail', wbadE cfg x0 g f εi (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)) tail'
        ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ r * Ge (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)) := by
      intro tail
      set sE := run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb) with hsE
      by_cases hd : sE.1.done = false
      · have hinvE : Inv cfg x0 f ρ sE := run_inv H.hc H.h (s₀_inv H.hc) tail _
        have hposE : cfg.pos sE.1.t = 0 :=
          pos_epoch_start ⟨s₀_inv H.hc, by simp [initState]⟩ e (InvE_run H _ tail (s₀_inv H.hc) _) hd
        have := wbad_bound H hinvE hposE hd
        simp only [Ge, hd, ↓reduceIte]
        exact this
      · have heq : ∀ tail', wbadE cfg x0 g f εi sE tail' = 0 := by
          intro tail'; unfold wbadE; rw [ite_eq_right]; intro h'; exact hd h'.1
        simp_rw [heq]
        rw [integral_zero]
        have hd' : sE.1.done = true := by simpa using hd
        simp only [Ge, hd', Bool.true_eq_false, ↓reduceIte, mul_zero, le_refl]
    have h1 := integral_mono_of_nonneg (Filter.Eventually.of_forall fun tail => integral_nonneg fun tail' => by
      unfold wbadE; split_ifs <;> positivity) ((hGeint e).const_mul r) (Filter.Eventually.of_forall hinner)
    rw [integral_const_mul] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hr0)
    have hpt : ∀ tail, Ge (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)) ≤
        (τ / 2 + 2 * L * cfg.B) + L / τ *
          (if (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.done = false then
            f (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.x - (f x0 - Δ) else 0) := by
      intro tail
      simp only [Ge]
      split_ifs with hd
      · have := grad_le_tau H.h (f x0 - Δ) hlow τ hτ (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.x
        linarith
      · rw [mul_zero, add_zero]; positivity
    have hgint : Integrable (fun tail => if (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.done = false then
        f (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.x - (f x0 - Δ) else 0)
        (Measure.infinitePi fun _ : ℕ => ν) := by
      have hYi := Yep_run_integrable H (s₀ cfg x0) (e * cfg.Eb)
      refine ((hYi.add (integrable_const Δ))).mono' ?_ (Filter.Eventually.of_forall fun tail => ?_)
      · exact (Measurable.ite ((measurable_done.comp (measurable_fst.comp (run_measurable _ _ (measurable_astep' H) _)))
          (MeasurableSet.of_discrete (s := {false})))
          ((H.h.hf.continuous.measurable.comp (measurable_x.comp (measurable_fst.comp
            (run_measurable _ _ (measurable_astep' H) _)))).sub_const _) measurable_const).aestronglyMeasurable
      · rw [Real.norm_eq_abs]
        simp only [Pi.add_apply]
        unfold Yep
        set sX := run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb) with hsX
        have hx := hlow sX.1.x
        have hite : (if isStart cfg sX.1 then Δ else 0) ≤ Δ := by split_ifs <;> linarith [H.hΔ0]
        by_cases h1 : sX.1.done = false
        · rw [ite_eq_left h1, abs_of_nonneg (by linarith)]; linarith
        · rw [ite_eq_right h1, abs_zero]; linarith
    have hg1 : Integrable (fun tail => L / τ *
        (if (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.done = false then
          f (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.x - (f x0 - Δ) else 0))
        (Measure.infinitePi fun _ : ℕ => ν) := hgint.const_mul _
    have hR : Integrable (fun tail => (τ / 2 + 2 * L * cfg.B) + L / τ *
        (if (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.done = false then
          f (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)).1.x - (f x0 - Δ) else 0))
        (Measure.infinitePi fun _ : ℕ => ν) := (integrable_const _).add hg1
    have h2 := integral_mono (hGeint e) hR hpt
    rw [integral_add (integrable_const _) hg1, integral_const, integral_const_mul] at h2
    simp only [probReal_univ, one_smul] at h2
    have h3 := gap_all H e
    have hLτ : 0 ≤ L / τ := by positivity
    linarith [mul_le_mul_of_nonneg_left h3 hLτ]
  calc _ ≤ ∑ e ∈ Finset.range n, r * (τ / 2 + L / τ * (Δ + cfg.N1 * cEpoch cfg ρ) + 2 * L * cfg.B) :=
        Finset.sum_le_sum (fun e _ => hterm e)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem output_expectation (hcert : cert cfg ρ < εi)
    (hq : (1 / cfg.N1) * ((2 / (cfg.θ ^ 2 * cfg.B ^ 2 / (32 * cfg.η)) + kap1 cfg ρ εi κ) * (Δ + cfg.N1 * cEpoch cfg ρ) +
        cfg.N1 * kap2 cfg ρ εi κ + cfg.N1 * ((1 + 3 * (4 * ((κ - 1) / cfg.b))) / 2) ^ cfg.m) ≤ 1 / 4)
    (τ : ℝ) (hτ : 0 < τ) (R : ℕ) :
    Integrable (fun tail => ‖gradient f (run (astep cfg x0 g f) (s₀ cfg x0) tail (R * cfg.N1 * cfg.Eb)).1.out‖)
      (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ∧
    ∫ tail, ‖gradient f (run (astep cfg x0 g f) (s₀ cfg x0) tail (R * cfg.N1 * cfg.Eb)).1.out‖
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      ‖gradient f x0‖ * (1 / 4) ^ R + 3 * εi + (R * cfg.N1) * (((1 + 3 * (4 * ((κ - 1) / cfg.b))) / 2) ^ cfg.m *
        (τ / 2 + L / τ * (Δ + cfg.N1 * cEpoch cfg ρ) + 2 * L * cfg.B)) := by
  set ν := (Measure.pi fun _ : Fin cfg.b => p) with hν
  set T := R * cfg.N1 * cfg.Eb with hT
  have hq' : ∀ sN : State E × E, TrialStart (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN → sN.1.done = false →
      ∫ tail, (if (run (astep cfg x0 g f) sN tail (cfg.N1 * cfg.Eb)).1.done = false then (1 : ℝ) else 0)
        ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ 1 / 4 := fun sN hts hd => (trial_fail H hcert hts hd).trans hq
  have hfail := fail_all H hq' R
  rw [← mul_assoc] at hfail
  have hind : Integrable (fun tail => ‖gradient f x0‖ *
      (if (run (astep cfg x0 g f) (s₀ cfg x0) tail T).1.done = false then (1 : ℝ) else 0))
      (Measure.infinitePi fun _ : ℕ => ν) := by
    refine ((integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun tail => by split_ifs <;> simp)).const_mul _
    exact (Measurable.ite ((measurable_done.comp (measurable_fst.comp (run_measurable _ _ (measurable_astep' H) _)))
      (MeasurableSet.of_discrete (s := {false}))) measurable_const measurable_const).aestronglyMeasurable
  have hacc : ∀ e, Integrable (fun tail => accInd (cfg := cfg) (x0 := x0) (g := g) (f := f) tail e)
      (Measure.infinitePi fun _ : ℕ => ν) := by
    intro e
    refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun tail => by
      unfold accInd; split_ifs <;> simp)
    unfold accInd
    exact (Measurable.ite (MeasurableSet.inter
      ((measurable_done.comp (measurable_fst.comp (run_measurable _ _ (measurable_astep' H) _)))
        (MeasurableSet.of_discrete (s := {false})))
      ((measurable_done.comp (measurable_fst.comp (run_measurable _ _ (measurable_astep' H) _)))
        (MeasurableSet.of_discrete (s := {true})))) measurable_const measurable_const).aestronglyMeasurable
  have hwb : ∀ e, Integrable (fun tail => wbadE cfg x0 g f εi (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb))
      (shift (e * cfg.Eb) tail)) (Measure.infinitePi fun _ : ℕ => ν) := by
    intro e
    have hG : Integrable (fun tail => (2 * ‖gradient f x0‖ ^ 2 + 2 * L ^ 2 + 1 + 2 * L * cfg.B) *
        W x0 (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb))) (Measure.infinitePi fun _ : ℕ => ν) :=
      (W_run_integrable H _ _).const_mul _
    refine hG.mono' ((wbadE_measurable H).comp ((run_measurable _ _ (measurable_astep' H) _).prodMk
      (shift_measurable _))).aestronglyMeasurable (Filter.Eventually.of_forall fun tail => ?_)
    rw [Real.norm_eq_abs]
    set sE := run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb) with hsE
    have hW := W_pos x0 sE
    have hL := H.h.hL
    have hB := H.hc.hB
    unfold wbadE
    split_ifs with h1
    · rw [abs_of_nonneg (norm_nonneg _)]
      obtain ⟨hd, hdone, _⟩ := h1
      have hinvE : Inv cfg x0 f ρ sE := run_inv H.hc H.h (s₀_inv H.hc) tail _
      have hposE : cfg.pos sE.1.t = 0 :=
        pos_epoch_start ⟨s₀_inv H.hc, by simp [initState]⟩ e (InvE_run H _ tail (s₀_inv H.hc) _) hd
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := run_val_fields cfg x0 g f H hinvE hposE hd (shift (e * cfg.Eb) tail)
        cfg.K le_rfl (by have := K_lt_Eb cfg; omega)
      have hposK : cfg.pos (run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.K).1.t = cfg.K := by
        rw [a5]; exact pos_add_of_zero cfg hposE (K_lt_Eb cfg)
      have hinvK : Inv cfg x0 f ρ (run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.K) :=
        run_inv H.hc H.h hinvE (shift (e * cfg.Eb) tail) cfg.K
      have htrK : (run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.K).1.trig = false := by
        obtain ⟨b1, _, _, _, _, _⟩ := run_val_fields cfg x0 g f H hinvE hposE hd (shift (e * cfg.Eb) tail)
          (cfg.Eb - 1) (by have := K_lt_Eb cfg; omega) le_rfl
        obtain ⟨hiff, _⟩ := done_run_Eb cfg x0 g f H hinvE hposE hd (shift (e * cfg.Eb) tail)
        rw [← b1]; exact (hiff.mp hdone).1
      have hA := hinvK.hagd a4 (by rw [hposK]) htrK
      have hK2 : 2 ≤ cfg.K := by have := H.hc.hK; omega
      have hyb := hA.hyb
      have hws : wsum cfg cfg.K = 1 := sum_pw hK2
      rw [hposK, hws, one_smul, mul_one] at hyb
      have hxS : (run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.K).1.xStart = sE.1.x := by
        rw [a3]
        exact ((hinvE.hagd hd (by rw [hposE]; exact Nat.zero_le _) (hinvE.hfresh hd hposE)).hstart hposE).2.1.symm
      rw [hxS] at hyb
      have hl := H.h.lip (run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.K).1.ybar sE.1.x
      have hn := norm_sub_norm_le (gradient f (run (astep cfg x0 g f) sE (shift (e * cfg.Eb) tail) cfg.K).1.ybar)
        (gradient f sE.1.x)
      have hg1 := gradf_sq_le x0 f H.h sE.1.x
      have hWx : ‖sE.1.x - x0‖ ^ 2 ≤ W x0 sE := by
        unfold W; nlinarith [sq_nonneg ‖sE.1.xPrev - x0‖, sq_nonneg ‖sE.1.xStart - x0‖, sq_nonneg ‖sE.1.glast‖,
          sq_nonneg ‖sE.1.ybar‖, sq_nonneg ‖sE.2‖]
      have h2 : ‖gradient f sE.1.x‖ ≤ (‖gradient f sE.1.x‖ ^ 2 + 1) / 2 := by
        nlinarith [sq_nonneg (‖gradient f sE.1.x‖ - 1)]
      have t1 : ‖gradient f x0‖ ^ 2 ≤ ‖gradient f x0‖ ^ 2 * W x0 sE := le_mul_of_one_le_right (sq_nonneg _) hW
      have t2 : L ^ 2 * ‖sE.1.x - x0‖ ^ 2 ≤ L ^ 2 * W x0 sE := mul_le_mul_of_nonneg_left hWx (sq_nonneg _)
      have t3 : 2 * L * cfg.B ≤ 2 * L * cfg.B * W x0 sE := le_mul_of_one_le_right (by positivity) hW
      have t4 := mul_nonneg (sq_nonneg ‖gradient f x0‖) (by linarith : (0:ℝ) ≤ W x0 sE)
      have t5 := mul_nonneg (sq_nonneg L) (by linarith : (0:ℝ) ≤ W x0 sE)
      have t6 := mul_le_mul_of_nonneg_left hyb hL.le
      linarith
    · rw [abs_zero]; positivity
  have hti : ∀ e, Integrable (fun tail => 3 * εi * accInd (cfg := cfg) (x0 := x0) (g := g) (f := f) tail e +
      wbadE cfg x0 g f εi (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail))
      (Measure.infinitePi fun _ : ℕ => ν) := fun e => ((hacc e).const_mul _).add (hwb e)
  have hS : Integrable (fun tail => ∑ e ∈ Finset.range (R * cfg.N1),
      (3 * εi * accInd (cfg := cfg) (x0 := x0) (g := g) (f := f) tail e +
        wbadE cfg x0 g f εi (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)))
      (Measure.infinitePi fun _ : ℕ => ν) := integrable_finsetSum _ (fun e _ => hti e)
  have hRHS : Integrable (fun tail => ‖gradient f x0‖ *
      (if (run (astep cfg x0 g f) (s₀ cfg x0) tail T).1.done = false then (1 : ℝ) else 0) +
      ∑ e ∈ Finset.range (R * cfg.N1), (3 * εi * accInd (cfg := cfg) (x0 := x0) (g := g) (f := f) tail e +
        wbadE cfg x0 g f εi (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)))
      (Measure.infinitePi fun _ : ℕ => ν) := hind.add hS
  have hmeas : Measurable (fun tail => ‖gradient f (run (astep cfg x0 g f) (s₀ cfg x0) tail T).1.out‖) :=
    ((gradient_measurable f H.h).comp (measurable_out.comp (measurable_fst.comp
      (run_measurable _ _ (measurable_astep' H) T)))).norm
  have hLHS : Integrable (fun tail => ‖gradient f (run (astep cfg x0 g f) (s₀ cfg x0) tail T).1.out‖)
      (Measure.infinitePi fun _ : ℕ => ν) :=
    hRHS.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun tail => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact output_pointwise H R tail)
  refine ⟨hLHS, ?_⟩
  have h1 := integral_mono hLHS hRHS (fun tail => output_pointwise H R tail)
  rw [integral_add hind hS, integral_const_mul, integral_finsetSum _ (fun e _ => hti e)] at h1
  have hsplit : ∀ e, ∫ tail, (3 * εi * accInd (cfg := cfg) (x0 := x0) (g := g) (f := f) tail e +
      wbadE cfg x0 g f εi (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail))
      ∂(Measure.infinitePi fun _ : ℕ => ν) =
      3 * εi * ∫ tail, accInd (cfg := cfg) (x0 := x0) (g := g) (f := f) tail e ∂(Measure.infinitePi fun _ : ℕ => ν) +
      ∫ tail, wbadE cfg x0 g f εi (run (astep cfg x0 g f) (s₀ cfg x0) tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)
        ∂(Measure.infinitePi fun _ : ℕ => ν) := fun e => by
    rw [integral_add ((hacc e).const_mul _) (hwb e), integral_const_mul]
  simp_rw [hsplit] at h1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← integral_finsetSum _ (fun e _ => hacc e)] at h1
  have hsumacc : ∫ tail, ∑ e ∈ Finset.range (R * cfg.N1), accInd (cfg := cfg) (x0 := x0) (g := g) (f := f) tail e
      ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ 1 := by
    calc _ ≤ ∫ tail, (1 : ℝ) ∂(Measure.infinitePi fun _ : ℕ => ν) :=
          integral_mono (integrable_finsetSum _ (fun e _ => hacc e)) (integrable_const _)
            (fun tail => sum_accInd_le tail _)
      _ = 1 := by simp
  have hws := wbad_sum H τ hτ (R * cfg.N1)
  have hg0 := norm_nonneg (gradient f x0)
  have hε := H.hεi
  push_cast at hws
  nlinarith [mul_le_mul_of_nonneg_left hfail hg0, mul_le_mul_of_nonneg_left hsumacc (by positivity : (0:ℝ) ≤ 3 * εi)]

end LongTails.Proofs.StrongGrowthAgdFinal
