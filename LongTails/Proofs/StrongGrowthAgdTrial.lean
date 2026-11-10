import LongTails.Proofs.StrongGrowthAgdValidation

namespace LongTails.Proofs.StrongGrowthAgdTrial

open MeasureTheory LongTails.Algorithms.StrongGrowthRestartedAgd LongTails.Proofs.StrongGrowthAgdProcess
  LongTails.Proofs.StrongGrowthAgdMoments LongTails.Proofs.StrongGrowthAgdMeasurable
  LongTails.Proofs.StrongGrowthAgdWeights LongTails.Proofs.StrongGrowthAgdModel
  LongTails.Proofs.StrongGrowthAgdEpochEnd LongTails.Proofs.StrongGrowthAgdInvariant
  LongTails.Proofs.StrongGrowthAgdEpoch LongTails.Proofs.StrongGrowthAgdBlocks
  LongTails.Proofs.StrongGrowthAgdEpochRun LongTails.Proofs.StrongGrowthAgdCounting
  LongTails.Proofs.StrongGrowthAgdValidation
open scoped RealInnerProductSpace
open Classical

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {cfg : Config} {x0 : E} {g : E → Ω → E} {f : E → ℝ} {L ρ κ Δ εi : ℝ}
variable (H : Hyps cfg x0 g f p L ρ κ Δ εi)
include H

def TrialStart (sN : State E × E) : Prop :=
  Inv cfg x0 f ρ sN ∧ sN.1.t % (cfg.N1 * cfg.Eb) = 0

omit H [MeasurableSpace E] [BorelSpace E] in
lemma TrialStart.pos {sN : State E × E} (h : TrialStart (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN) :
    cfg.pos sN.1.t = 0 :=
  pos_zero_of_trial cfg _ h.2

def InvE (sN : State E × E) (t : ℕ) : Set (State E × E) :=
  {sN' | Inv cfg x0 f ρ sN' ∧ (sN'.1.done = false → sN'.1.t = sN.1.t + t)}

omit [IsProbabilityMeasure p] [BorelSpace E] in
lemma InvE_step (sN : State E × E) (t : ℕ) (sN' : State E × E)
    (h : sN' ∈ InvE (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN t) (ω : Fin cfg.b → Ω) :
    astep cfg x0 g f sN' ω ∈ InvE (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN (t + 1) := by
  refine ⟨inv_preserved cfg x0 g f ρ H.hc H.h h.1 ω, fun hd => ?_⟩
  rw [t_succ_of_not_done _ _ hd, h.2 (not_done_of_step hd)]
  ring

omit [IsProbabilityMeasure p] [BorelSpace E] in
lemma InvE_run (sN : State E × E) (tail : ℕ → (Fin cfg.b → Ω)) (hinv : Inv cfg x0 f ρ sN) (t : ℕ) :
    run (astep cfg x0 g f) sN tail t ∈ InvE (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN t :=
  run_mem_inv (astep cfg x0 g f) sN (InvE sN) (fun t sN' h ω => InvE_step H sN t sN' h ω)
    ⟨hinv, fun _ => rfl⟩ tail t

omit [MeasurableSpace Ω] [IsProbabilityMeasure p] H [MeasurableSpace E] [BorelSpace E] in
lemma pos_epoch_start {sN : State E × E} (hts : TrialStart (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN)
    (e : ℕ) {sN' : State E × E} (h : sN' ∈ InvE (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN (e * cfg.Eb))
    (hd : sN'.1.done = false) : cfg.pos sN'.1.t = 0 := by
  rw [h.2 hd]
  have hp : sN.1.t % cfg.Eb = 0 := hts.pos
  unfold Config.pos
  rw [Nat.add_mod, hp, Nat.mul_mod_left, zero_add, Nat.zero_mod]

omit [BorelSpace E] [IsProbabilityMeasure p] in
lemma not_start_mid {sN : State E × E} (hts : TrialStart (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN)
    {e : ℕ} (he0 : 0 < e) (heN : e < cfg.N1) {sN' : State E × E}
    (h : sN' ∈ InvE (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN (e * cfg.Eb)) :
    ¬ isStart cfg sN'.1 := by
  intro ⟨hd, hmod⟩
  rw [h.2 hd, Nat.add_mod, hts.2, zero_add, Nat.mod_mod] at hmod
  have hEb : 0 < cfg.Eb := by have := H.hc.hK; unfold Config.Eb; omega
  have hlt : e * cfg.Eb < cfg.N1 * cfg.Eb := Nat.mul_lt_mul_of_pos_right heN hEb
  rw [Nat.mod_eq_of_lt hlt] at hmod
  have : 0 < e * cfg.Eb := Nat.mul_pos he0 hEb
  omega

omit [IsProbabilityMeasure p] in
lemma Yep_measurable : Measurable (Yep cfg x0 f Δ) := by
  unfold Yep isStart
  refine ((H.h.hf.continuous.measurable.comp (measurable_x.comp measurable_fst)).sub measurable_const).sub ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact MeasurableSet.inter ((measurable_done.comp measurable_fst) (MeasurableSet.of_discrete (s := {false})))
    ((measurable_t.comp measurable_fst) (MeasurableSet.of_discrete (s := {n | n % (cfg.N1 * cfg.Eb) = 0})))

omit [IsProbabilityMeasure p] [BorelSpace E] in
lemma Yep_abs_le (sN' : State E × E) :
    |Yep cfg x0 f Δ sN'| ≤ (|f x0| + ‖gradient f x0‖ ^ 2 / 2 + (1 / 2 + 3 / 2 * L) + |f x0 - Δ| + Δ) * W x0 sN' := by
  have hW := W_pos x0 sN'
  have h1 := f_sub_abs_le x0 f H.h sN'.1.x
  have h2 : |f sN'.1.x| ≤ |f x0| + |f sN'.1.x - f x0| := by
    have := abs_add_le (f x0) (f sN'.1.x - f x0); rwa [add_sub_cancel] at this
  have h3 : ‖gradient f x0‖ * ‖sN'.1.x - x0‖ ≤ ‖gradient f x0‖ ^ 2 / 2 + ‖sN'.1.x - x0‖ ^ 2 / 2 := by
    nlinarith [sq_nonneg (‖gradient f x0‖ - ‖sN'.1.x - x0‖)]
  have hWx : ‖sN'.1.x - x0‖ ^ 2 ≤ W x0 sN' := by
    unfold W; nlinarith [sq_nonneg ‖sN'.1.xPrev - x0‖, sq_nonneg ‖sN'.1.xStart - x0‖, sq_nonneg ‖sN'.1.glast‖,
      sq_nonneg ‖sN'.1.ybar‖, sq_nonneg ‖sN'.2‖]
  have hL := H.h.hL
  have hA : 0 ≤ |f x0| + ‖gradient f x0‖ ^ 2 / 2 + (1 / 2 + 3 / 2 * L) := by positivity
  unfold Yep
  have h4 : |(if isStart cfg sN'.1 then Δ else 0)| ≤ Δ := by split_ifs <;> simp [abs_of_nonneg H.hΔ0, H.hΔ0]
  have h5 := abs_sub (f sN'.1.x - (f x0 - Δ)) (if isStart cfg sN'.1 then Δ else 0)
  have h6 := abs_sub (f sN'.1.x) (f x0 - Δ)
  have t0 : 3 / 2 * L * ‖sN'.1.x - x0‖ ^ 2 ≤ 3 / 2 * L * W x0 sN' :=
    mul_le_mul_of_nonneg_left hWx (by positivity)
  have t1 : |f x0| ≤ |f x0| * W x0 sN' := le_mul_of_one_le_right (abs_nonneg _) hW
  have t2 : ‖gradient f x0‖ ^ 2 / 2 ≤ ‖gradient f x0‖ ^ 2 / 2 * W x0 sN' :=
    le_mul_of_one_le_right (by positivity) hW
  have t3 : |f x0 - Δ| ≤ |f x0 - Δ| * W x0 sN' := le_mul_of_one_le_right (abs_nonneg _) hW
  have t4 : Δ ≤ Δ * W x0 sN' := le_mul_of_one_le_right H.hΔ0 hW
  linarith

lemma Yep_run_integrable (sN : State E × E) (t : ℕ) :
    Integrable (fun tail => Yep cfg x0 f Δ (run (astep cfg x0 g f) sN tail t))
      (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) :=
  integrable_of_le_W H _ (Yep_measurable H) _ (Yep_abs_le H) sN t

omit [MeasurableSpace Ω] [IsProbabilityMeasure p] H [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma cep_measurable : Measurable (cep cfg ρ Δ : State E × E → ℝ) := by
  unfold cep isStart
  refine measurable_const.add (Measurable.ite ?_ measurable_const measurable_const)
  exact MeasurableSet.inter ((measurable_done.comp measurable_fst) (MeasurableSet.of_discrete (s := {false})))
    ((measurable_t.comp measurable_fst) (MeasurableSet.of_discrete (s := {n | n % (cfg.N1 * cfg.Eb) = 0})))

lemma cep_run_integrable (sN : State E × E) (t : ℕ) :
    Integrable (fun tail => cep cfg ρ Δ (run (astep cfg x0 g f) sN tail t))
      (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) := by
  refine integrable_of_le_W H _ cep_measurable (cEpoch cfg ρ + Δ) (fun sN' => ?_) sN t
  have hW := W_pos x0 sN'
  have hc := cEpoch_nonneg H
  unfold cep
  have : |cEpoch cfg ρ + (if isStart cfg sN'.1 then Δ else 0)| ≤ cEpoch cfg ρ + Δ := by
    by_cases hs : isStart cfg sN'.1
    · rw [ite_eq_left hs, abs_of_nonneg (by linarith [H.hΔ0])]
    · rw [ite_eq_right hs, add_zero, abs_of_nonneg hc]; linarith [H.hΔ0]
  nlinarith [H.hΔ0]

omit [IsProbabilityMeasure p] in
lemma Dep_measurable : Measurable (Function.uncurry (Dep cfg x0 g f)) := by
  unfold Function.uncurry Dep
  refine Finset.measurable_sum _ (fun t _ => ?_)
  exact (Dblk_measurable H).comp ((run_measurable₂ (astep cfg x0 g f) (measurable_astep' H) t).prodMk
    ((measurable_pi_apply t).comp measurable_snd))

lemma Dep_run_integrable (sN : State E × E) (e : ℕ) :
    Integrable (fun tail => Dep cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail))
      (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) := by
  unfold Dep
  refine integrable_finsetSum _ (fun t _ => ?_)
  have hrw : ∀ tail : ℕ → (Fin cfg.b → Ω),
      Dblk cfg x0 g f (run (astep cfg x0 g f) (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail) t)
        (shift (e * cfg.Eb) tail t) =
      Dblk cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb + t)) (tail (e * cfg.Eb + t)) := by
    intro tail; rw [run_add]; rfl
  simp_rw [hrw]
  exact Dblk_run_integrable H sN _

theorem trial_drift {sN : State E × E} (hts : TrialStart (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN)
    (hd : sN.1.done = false) (n : ℕ) (hn : n ≤ cfg.N1) :
    ∫ tail, Yep cfg x0 f Δ (run (astep cfg x0 g f) sN tail (n * cfg.Eb))
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) +
      ∑ e ∈ Finset.range n, ∫ tail, Dep cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      Δ + n * cEpoch cfg ρ := by
  set ν := (Measure.pi fun _ : Fin cfg.b => p) with hν
  have hdr := drift (astep cfg x0 g f) sN ν (measurable_astep' H) cfg.Eb (InvE sN)
    (fun t sN' h ω => InvE_step H sN t sN' h ω) ⟨hts.1, fun _ => rfl⟩ (Yep cfg x0 f Δ) (cep cfg ρ Δ)
    (Dep cfg x0 g f) (Yep_measurable H) cep_measurable (Dep_measurable H) (Yep_run_integrable H sN)
    (cep_run_integrable H sN) (Dep_run_integrable H sN) n (fun e _ sN' h => by
      by_cases hd' : sN'.1.done = true
      · have hrun : ∀ tail, run (astep cfg x0 g f) sN' tail cfg.Eb = sN' := fun tail => run_of_done hd' tail _
        have hD : ∀ tail, Dep cfg x0 g f sN' tail = 0 := by
          intro tail; unfold Dep
          refine Finset.sum_eq_zero (fun t _ => ?_)
          rw [run_of_done hd']
          unfold Dblk; rw [ite_eq_right]; simp [hd']
        simp only [hrun, hD, add_zero, integral_const, probReal_univ, one_smul]
        unfold cep
        have : 0 ≤ (if isStart cfg sN'.1 then Δ else 0) := by split_ifs <;> linarith [H.hΔ0]
        linarith [cEpoch_nonneg H]
      · exact epoch_ineq H h.1 (pos_epoch_start hts e h (by simpa using hd')))
  have hY0 : Yep cfg x0 f Δ sN = 0 := by
    unfold Yep
    have hst : isStart cfg sN.1 := ⟨hd, hts.2⟩
    rw [ite_eq_left hst, hts.1.hx0 hd hts.2]; ring
  have hcsum : ∑ e ∈ Finset.range n, ∫ tail, cep cfg ρ Δ (run (astep cfg x0 g f) sN tail (e * cfg.Eb))
      ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ n * cEpoch cfg ρ + Δ := by
    have hterm : ∀ e ∈ Finset.range n, ∫ tail, cep cfg ρ Δ (run (astep cfg x0 g f) sN tail (e * cfg.Eb))
        ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ cEpoch cfg ρ + (if e = 0 then Δ else 0) := by
      intro e he
      have he' : e < n := Finset.mem_range.mp he
      have hpt : ∀ tail, cep cfg ρ Δ (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) ≤
          cEpoch cfg ρ + (if e = 0 then Δ else 0) := by
        intro tail
        unfold cep
        split_ifs with h1 h2 h2
        · exact le_rfl
        · exfalso
          exact not_start_mid H hts (Nat.pos_of_ne_zero h2) (by omega) (InvE_run H sN tail hts.1 _) h1
        · linarith [H.hΔ0]
        · exact le_rfl
      calc _ ≤ ∫ tail, (cEpoch cfg ρ + (if e = 0 then Δ else 0)) ∂(Measure.infinitePi fun _ : ℕ => ν) :=
            integral_mono (cep_run_integrable H sN _) (integrable_const _) hpt
        _ = _ := by simp
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : ∑ e ∈ Finset.range n, (if e = 0 then Δ else 0) ≤ Δ := by
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · subst hn0; simp [H.hΔ0]
      · rw [Finset.sum_ite_eq' (Finset.range n) 0 (fun _ => Δ), ite_eq_left (Finset.mem_range.mpr hn0)]
    linarith
  rw [hY0, zero_add] at hdr
  linarith

omit [BorelSpace E] [IsProbabilityMeasure p] in
lemma Yep_nonneg {sN : State E × E} (hinv : Inv cfg x0 f ρ sN) : 0 ≤ Yep cfg x0 f Δ sN := by
  unfold Yep
  split_ifs with h
  · rw [hinv.hx0 h.1 h.2]; ring_nf; exact le_rfl
  · linarith [H.hΔ sN.1.x]

theorem trial_decrease {sN : State E × E} (hts : TrialStart (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN)
    (hd : sN.1.done = false) :
    ∑ e ∈ Finset.range cfg.N1, ∫ tail, Dep cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      Δ + cfg.N1 * cEpoch cfg ρ := by
  have h1 := trial_drift H hts hd cfg.N1 le_rfl
  have h2 : 0 ≤ ∫ tail, Yep cfg x0 f Δ (run (astep cfg x0 g f) sN tail (cfg.N1 * cfg.Eb))
      ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) :=
    integral_nonneg (fun tail => Yep_nonneg H (run_inv H.hc H.h hts.1 tail _))
  linarith

theorem trial_gap {sN : State E × E} (hts : TrialStart (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN)
    (hd : sN.1.done = false) (j : ℕ) (hj : j < cfg.N1) :
    ∫ tail, (f (run (astep cfg x0 g f) sN tail (j * cfg.Eb)).1.x - (f x0 - Δ))
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      Δ + cfg.N1 * cEpoch cfg ρ := by
  have hc := cEpoch_nonneg H
  have hN1 : (j : ℝ) ≤ cfg.N1 := by exact_mod_cast hj.le
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · subst hj0
    simp only [zero_mul, run_zero, integral_const, probReal_univ, one_smul]
    rw [hts.1.hx0 hd hts.2]
    nlinarith [Nat.cast_nonneg (α := ℝ) cfg.N1]
  · have h1 := trial_drift H hts hd j hj.le
    have h2 : 0 ≤ ∑ e ∈ Finset.range j, ∫ tail, Dep cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb))
        (shift (e * cfg.Eb) tail) ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) :=
      Finset.sum_nonneg (fun e _ => integral_nonneg (fun tail => Dep_nonneg H.hc _ _))
    have h3 : ∀ tail, f (run (astep cfg x0 g f) sN tail (j * cfg.Eb)).1.x - (f x0 - Δ) =
        Yep cfg x0 f Δ (run (astep cfg x0 g f) sN tail (j * cfg.Eb)) := by
      intro tail
      unfold Yep
      rw [ite_eq_right (not_start_mid H hts hj0 hj (InvE_run H sN tail hts.1 _)), sub_zero]
    simp_rw [h3]
    nlinarith [mul_le_mul_of_nonneg_right hN1 hc]

section fail

omit [BorelSpace E] [IsProbabilityMeasure p] H [MeasurableSpace E] [MeasurableSpace Ω] in
lemma run_epoch_shift (sN : State E × E) (tail : ℕ → (Fin cfg.b → Ω)) (e k : ℕ) :
    run (astep cfg x0 g f) (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail) k =
      run (astep cfg x0 g f) sN tail (e * cfg.Eb + k) := by
  rw [run_add]

omit [IsProbabilityMeasure p] in
lemma trigE_measurable : Measurable (Function.uncurry (trigE cfg x0 g f)) := by
  unfold Function.uncurry trigE
  refine Measurable.ite ?_ measurable_const measurable_const
  refine MeasurableSet.inter ((measurable_done.comp (measurable_fst.comp measurable_fst))
    (MeasurableSet.of_discrete (s := {false}))) ?_
  exact (measurable_trig.comp (measurable_fst.comp (run_measurable₂ (astep cfg x0 g f) (measurable_astep' H) cfg.K)))
    (MeasurableSet.of_discrete (s := {true}))

omit [IsProbabilityMeasure p] in
lemma badE_measurable : Measurable (Function.uncurry (badE cfg x0 g f εi)) := by
  unfold Function.uncurry badE
  refine Measurable.ite ?_ measurable_const measurable_const
  have hrun := run_measurable₂ (astep cfg x0 g f) (measurable_astep' H) cfg.K
  refine MeasurableSet.inter ((measurable_done.comp (measurable_fst.comp measurable_fst))
    (MeasurableSet.of_discrete (s := {false}))) ?_
  refine MeasurableSet.inter ((measurable_trig.comp (measurable_fst.comp hrun))
    (MeasurableSet.of_discrete (s := {false}))) ?_
  exact measurableSet_lt measurable_const
    ((gradient_measurable f H.h).comp (measurable_ybar.comp (measurable_fst.comp hrun))).norm

omit [IsProbabilityMeasure p] in
lemma rejE_measurable : Measurable (Function.uncurry (rejE cfg x0 g f εi)) := by
  unfold Function.uncurry rejE
  refine Measurable.ite ?_ measurable_const measurable_const
  have hrun := run_measurable₂ (astep cfg x0 g f) (measurable_astep' H) cfg.K
  have hrunE := run_measurable₂ (astep cfg x0 g f) (measurable_astep' H) cfg.Eb
  refine MeasurableSet.inter ((measurable_done.comp (measurable_fst.comp measurable_fst))
    (MeasurableSet.of_discrete (s := {false}))) ?_
  refine MeasurableSet.inter ((measurable_trig.comp (measurable_fst.comp hrun))
    (MeasurableSet.of_discrete (s := {false}))) ?_
  refine MeasurableSet.inter (measurableSet_le
    ((gradient_measurable f H.h).comp (measurable_ybar.comp (measurable_fst.comp hrun))).norm measurable_const) ?_
  exact (measurable_done.comp (measurable_fst.comp hrunE)) (MeasurableSet.of_discrete (s := {false}))

omit [IsProbabilityMeasure p] in
lemma wbadE_measurable : Measurable (Function.uncurry (wbadE cfg x0 g f εi)) := by
  unfold Function.uncurry wbadE
  have hrun := run_measurable₂ (astep cfg x0 g f) (measurable_astep' H) cfg.K
  have hrunE := run_measurable₂ (astep cfg x0 g f) (measurable_astep' H) cfg.Eb
  have hG : Measurable (fun z : (State E × E) × (ℕ → (Fin cfg.b → Ω)) =>
      ‖gradient f (run (astep cfg x0 g f) z.1 z.2 cfg.K).1.ybar‖) :=
    ((gradient_measurable f H.h).comp (measurable_ybar.comp (measurable_fst.comp hrun))).norm
  refine Measurable.ite ?_ hG measurable_const
  refine MeasurableSet.inter ((measurable_done.comp (measurable_fst.comp measurable_fst))
    (MeasurableSet.of_discrete (s := {false}))) ?_
  refine MeasurableSet.inter ((measurable_done.comp (measurable_fst.comp hrunE))
    (MeasurableSet.of_discrete (s := {true}))) ?_
  exact measurableSet_lt measurable_const hG

noncomputable def nsqE (sN : State E × E) (tail : ℕ → (Fin cfg.b → Ω)) : ℝ :=
  if sN.1.done = false then ‖(run (astep cfg x0 g f) sN tail cfg.K).2‖ ^ 2 else 0

omit [IsProbabilityMeasure p] in
lemma nsqE_measurable : Measurable (Function.uncurry (nsqE (cfg := cfg) (x0 := x0) (g := g) (f := f))) := by
  unfold Function.uncurry nsqE
  have hrun := run_measurable₂ (astep cfg x0 g f) (measurable_astep' H) cfg.K
  refine Measurable.ite ((measurable_done.comp (measurable_fst.comp measurable_fst))
    (MeasurableSet.of_discrete (s := {false}))) ?_ measurable_const
  exact (measurable_snd.comp hrun).norm.pow_const 2

omit H [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma nsqE_nonneg (sN : State E × E) (tail : ℕ → (Fin cfg.b → Ω)) : 0 ≤ nsqE (cfg := cfg) (x0 := x0) (g := g) (f := f) sN tail := by
  unfold nsqE; split_ifs <;> positivity

omit [MeasurableSpace Ω] [IsProbabilityMeasure p] H [MeasurableSpace E] [BorelSpace E] in
lemma nsqE_le_W (sN : State E × E) (tail : ℕ → (Fin cfg.b → Ω)) :
    nsqE (cfg := cfg) (x0 := x0) (g := g) (f := f) sN tail ≤ W x0 (run (astep cfg x0 g f) sN tail cfg.K) := by
  unfold nsqE
  split_ifs
  · unfold W
    nlinarith [sq_nonneg ‖(run (astep cfg x0 g f) sN tail cfg.K).1.x - x0‖,
      sq_nonneg ‖(run (astep cfg x0 g f) sN tail cfg.K).1.xPrev - x0‖,
      sq_nonneg ‖(run (astep cfg x0 g f) sN tail cfg.K).1.xStart - x0‖,
      sq_nonneg ‖(run (astep cfg x0 g f) sN tail cfg.K).1.glast‖,
      sq_nonneg ‖(run (astep cfg x0 g f) sN tail cfg.K).1.ybar‖]
  · exact W_nonneg x0 _

noncomputable def kap1 (cfg : Config) (ρ εi : ℝ) (κ : ℝ) : ℝ :=
  (2 / cfg.K) ^ 2 * ((κ - 1) / cfg.b) * (64 / cfg.η) / (εi - cert cfg ρ) ^ 2

noncomputable def kap2 (cfg : Config) (ρ εi : ℝ) (κ : ℝ) : ℝ :=
  (2 / cfg.K) ^ 2 * ((κ - 1) / cfg.b) * (2 * cfg.K * Dm cfg ρ ^ 2) / (εi - cert cfg ρ) ^ 2

theorem trial_fail (hcert : cert cfg ρ < εi) {sN : State E × E}
    (hts : TrialStart (cfg := cfg) (x0 := x0) (f := f) (ρ := ρ) sN) (hd : sN.1.done = false) :
    ∫ tail, (if (run (astep cfg x0 g f) sN tail (cfg.N1 * cfg.Eb)).1.done = false then (1 : ℝ) else 0)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      (1 / cfg.N1) * ((2 / (cfg.θ ^ 2 * cfg.B ^ 2 / (32 * cfg.η)) + kap1 cfg ρ εi κ) * (Δ + cfg.N1 * cEpoch cfg ρ) +
        cfg.N1 * kap2 cfg ρ εi κ + cfg.N1 * ((1 + 3 * (4 * ((κ - 1) / cfg.b))) / 2) ^ cfg.m) := by
  set ν := (Measure.pi fun _ : Fin cfg.b => p) with hν
  have hEb : 1 < cfg.Eb := Eb_gt cfg (by have := H.hc.hK; omega)
  have hN1 : (0 : ℝ) < cfg.N1 := by exact_mod_cast H.hN1
  set a0 := cfg.θ ^ 2 * cfg.B ^ 2 / (32 * cfg.η) with ha0def
  have ha0 : 0 < a0 := by have := H.hc.hθ0; have := H.hc.hη; have := H.hc.hB; positivity
  have hδ0 : 0 ≤ (κ - 1) / cfg.b := div_nonneg (by linarith [H.hκ]) (Nat.cast_nonneg _)
  have hcpos : 0 < εi - cert cfg ρ := by linarith
  set r := ((1 + 3 * (4 * ((κ - 1) / cfg.b))) / 2) ^ cfg.m with hr
  have hr0 : 0 ≤ r := by positivity
  let Xe : ℕ → (ℕ → (Fin cfg.b → Ω)) → ℝ := fun e tail =>
    trigE cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail) +
    badE cfg x0 g f εi (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail) +
    rejE cfg x0 g f εi (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)
  have hpt : ∀ tail, (if (run (astep cfg x0 g f) sN tail (cfg.N1 * cfg.Eb)).1.done = false then (1 : ℝ) else 0) ≤
      (1 / cfg.N1) * ∑ e ∈ Finset.range cfg.N1, Xe e tail := by
    intro tail
    split_ifs with hfail
    · have hone : ∀ e ∈ Finset.range cfg.N1, (1 : ℝ) ≤ Xe e tail := by
        intro e he
        have he' : e < cfg.N1 := Finset.mem_range.mp he
        have hnd : (run (astep cfg x0 g f) (run (astep cfg x0 g f) sN tail (e * cfg.Eb))
            (shift (e * cfg.Eb) tail) cfg.Eb).1.done = false := by
          rw [run_epoch_shift]
          by_contra hcon
          have hcon' : (run (astep cfg x0 g f) sN tail (e * cfg.Eb + cfg.Eb)).1.done = true := by simpa using hcon
          have := run_done_of_done (cfg := cfg) (x0 := x0) (g := g) (f := f) sN tail
            (show e * cfg.Eb + cfg.Eb ≤ cfg.N1 * cfg.Eb by nlinarith) hcon'
          rw [this] at hfail; exact Bool.noConfusion hfail
        have hd' : (run (astep cfg x0 g f) sN tail (e * cfg.Eb)).1.done = false := by
          by_contra hcon
          have hcon' : (run (astep cfg x0 g f) sN tail (e * cfg.Eb)).1.done = true := by simpa using hcon
          rw [run_of_done hcon'] at hnd
          rw [hcon'] at hnd; exact Bool.noConfusion hnd
        exact epoch_trichotomy _ _ hd' hnd
      have hsum := Finset.sum_le_sum hone
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
      calc (1 : ℝ) = (1 / cfg.N1) * cfg.N1 := by field_simp
        _ ≤ (1 / cfg.N1) * ∑ e ∈ Finset.range cfg.N1, Xe e tail :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
    · refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun e _ => ?_))
      simp only [Xe, trigE, badE, rejE]
      split_ifs <;> norm_num
  have hrunm : ∀ e, Measurable (fun tail : ℕ → (Fin cfg.b → Ω) =>
      (run (astep cfg x0 g f) sN tail (e * cfg.Eb), shift (e * cfg.Eb) tail)) := fun e =>
    (run_measurable _ sN (measurable_astep' H) _).prodMk (shift_measurable _)
  have hbnd : ∀ (X : (State E × E) → (ℕ → (Fin cfg.b → Ω)) → ℝ), Measurable (Function.uncurry X) →
      (∀ a b, |X a b| ≤ 1) → ∀ e, Integrable (fun tail => X (run (astep cfg x0 g f) sN tail (e * cfg.Eb))
        (shift (e * cfg.Eb) tail)) (Measure.infinitePi fun _ : ℕ => ν) := by
    intro X hX hX1 e
    refine (integrable_const (1 : ℝ)).mono' (hX.comp (hrunm e)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun tail => ?_)
    rw [Real.norm_eq_abs]; exact hX1 _ _
  have hT1 : ∀ a b, |trigE cfg x0 g f a b| ≤ 1 := by intro a b; unfold trigE; split_ifs <;> simp
  have hB1 : ∀ a b, |badE cfg x0 g f εi a b| ≤ 1 := by intro a b; unfold badE; split_ifs <;> simp
  have hR1 : ∀ a b, |rejE cfg x0 g f εi a b| ≤ 1 := by intro a b; unfold rejE; split_ifs <;> simp
  have hTi := hbnd _ (trigE_measurable H) hT1
  have hBi := hbnd _ (badE_measurable H) hB1
  have hRi := hbnd _ (rejE_measurable H) hR1
  have hXi : ∀ e, Integrable (Xe e) (Measure.infinitePi fun _ : ℕ => ν) := fun e => ((hTi e).add (hBi e)).add (hRi e)
  have hfi : Integrable (fun tail => if (run (astep cfg x0 g f) sN tail (cfg.N1 * cfg.Eb)).1.done = false
      then (1 : ℝ) else 0) (Measure.infinitePi fun _ : ℕ => ν) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun tail => by split_ifs <;> simp)
    exact (Measurable.ite ((measurable_done.comp (measurable_fst.comp
      (run_measurable _ sN (measurable_astep' H) _))) (MeasurableSet.of_discrete (s := {false})))
      measurable_const measurable_const).aestronglyMeasurable
  have h1 := integral_mono hfi ((integrable_finsetSum _ (fun e _ => hXi e)).const_mul _) hpt
  rw [integral_const_mul, integral_finsetSum _ (fun e _ => hXi e)] at h1
  have hDe : ∀ e, Integrable (fun tail => Dep cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb))
      (shift (e * cfg.Eb) tail)) (Measure.infinitePi fun _ : ℕ => ν) := Dep_run_integrable H sN
  have hstart : ∀ e tail, (run (astep cfg x0 g f) sN tail (e * cfg.Eb)).1.done = false →
      Inv cfg x0 f ρ (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) ∧
      cfg.pos (run (astep cfg x0 g f) sN tail (e * cfg.Eb)).1.t = 0 := by
    intro e tail hd'
    refine ⟨run_inv H.hc H.h hts.1 tail _, pos_epoch_start hts e (InvE_run H sN tail hts.1 _) hd'⟩
  have hTe : ∀ e, ∫ tail, trigE cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)
      ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      (2 / a0) * ∫ tail, Dep cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)
        ∂(Measure.infinitePi fun _ : ℕ => ν) := by
    intro e
    rw [← integral_const_mul]
    refine integral_mono (hTi e) ((hDe e).const_mul _) (fun tail => ?_)
    unfold trigE
    split_ifs with h
    · obtain ⟨hinv', hpos'⟩ := hstart e tail h.1
      have := trig_decrease H hinv' hpos' h.1 _ h.2
      rw [← ha0def] at this
      rw [div_mul_eq_mul_div, le_div_iff₀ ha0]
      linarith
    · exact mul_nonneg (by positivity) (Dep_nonneg H.hc _ _)
  have hNm : Measurable (Function.uncurry (nsqE (cfg := cfg) (x0 := x0) (g := g) (f := f))) := nsqE_measurable H
  have hNi : ∀ e, Integrable (fun tail => nsqE (cfg := cfg) (x0 := x0) (g := g) (f := f)
      (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)) (Measure.infinitePi fun _ : ℕ => ν) := by
    intro e
    refine (W_run_integrable H sN (e * cfg.Eb + cfg.K)).mono' (hNm.comp (hrunm e)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun tail => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (nsqE_nonneg _ _)]
    have := nsqE_le_W (cfg := cfg) (x0 := x0) (g := g) (f := f)
      (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)
    rwa [run_epoch_shift] at this
  have hBe : ∀ e, ∫ tail, badE cfg x0 g f εi (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)
      ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      kap1 cfg ρ εi κ * (∫ tail, Dep cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)
        ∂(Measure.infinitePi fun _ : ℕ => ν)) + kap2 cfg ρ εi κ := by
    intro e
    have hpt2 : ∀ tail, badE cfg x0 g f εi (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail) ≤
        (1 / (εi - cert cfg ρ) ^ 2) * nsqE (cfg := cfg) (x0 := x0) (g := g) (f := f)
          (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail) := by
      intro tail
      unfold badE nsqE
      split_ifs with h h2 h2
      · obtain ⟨hd', htr, hbig⟩ := h
        obtain ⟨hinv', hpos'⟩ := hstart e tail hd'
        set sK := run (astep cfg x0 g f) (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail) cfg.K
        obtain ⟨_, _, _, hdK, htK, _⟩ := run_val_fields cfg x0 g f H hinv' hpos' hd' (shift (e * cfg.Eb) tail)
          cfg.K le_rfl (by have := K_lt_Eb cfg; omega)
        have hposK : cfg.pos sK.1.t = cfg.K := by rw [htK]; exact pos_add_of_zero cfg hpos' (K_lt_Eb cfg)
        have hinvK : Inv cfg x0 f ρ sK := run_inv H.hc H.h hinv' (shift (e * cfg.Eb) tail) cfg.K
        have hcp := certificate_pathwise H.hc H.h hinvK hdK hposK htr
        have hN : εi - cert cfg ρ < ‖sK.2‖ := by linarith
        rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
        nlinarith [norm_nonneg sK.2]
      · exact absurd h.1 h2
      · positivity
      · positivity
    have h2 := integral_mono (hBi e) ((hNi e).const_mul _) hpt2
    rw [integral_const_mul] at h2
    have hti := tail_integral (astep cfg x0 g f) sN ν (measurable_astep' H) (e * cfg.Eb) _ hNm (hNi e)
    have hDti := tail_integral (astep cfg x0 g f) sN ν (measurable_astep' H) (e * cfg.Eb) _ (Dep_measurable H) (hDe e)
    have hDinner := tail_inner_integrable (astep cfg x0 g f) sN ν (measurable_astep' H) (e * cfg.Eb) _
      (Dep_measurable H) (hDe e)
    have hinner : ∀ tail, ∫ tail', nsqE (cfg := cfg) (x0 := x0) (g := g) (f := f)
        (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) tail' ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
        (2 / cfg.K) ^ 2 * ((κ - 1) / cfg.b) *
          ((64 / cfg.η) * ∫ tail', Dep cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) tail'
              ∂(Measure.infinitePi fun _ : ℕ => ν) + 2 * cfg.K * Dm cfg ρ ^ 2) := by
      intro tail
      by_cases hd' : (run (astep cfg x0 g f) sN tail (e * cfg.Eb)).1.done = false
      · obtain ⟨hinv', hpos'⟩ := hstart e tail hd'
        have := noise_second_moment H hinv' hpos' hd'
        have heq : ∀ tail', nsqE (cfg := cfg) (x0 := x0) (g := g) (f := f)
            (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) tail' =
            ‖(run (astep cfg x0 g f) (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) tail' cfg.K).2‖ ^ 2 := by
          intro tail'; unfold nsqE; rw [ite_eq_left hd']
        simp_rw [heq]
        exact this
      · have heq : ∀ tail', nsqE (cfg := cfg) (x0 := x0) (g := g) (f := f)
            (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) tail' = 0 := by
          intro tail'; unfold nsqE; rw [ite_eq_right hd']
        simp_rw [heq]
        rw [integral_zero]
        have hDm := sq_nonneg (Dm cfg ρ)
        have hη := H.hc.hη
        have hK := Nat.cast_nonneg (α := ℝ) cfg.K
        have hDn : 0 ≤ ∫ tail', Dep cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) tail'
            ∂(Measure.infinitePi fun _ : ℕ => ν) := integral_nonneg (fun _ => Dep_nonneg H.hc _ _)
        positivity
    rw [hti] at h2
    have h3 : ∫ tail, (∫ tail', nsqE (cfg := cfg) (x0 := x0) (g := g) (f := f)
        (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) tail' ∂(Measure.infinitePi fun _ : ℕ => ν))
        ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
        ∫ tail, (2 / cfg.K) ^ 2 * ((κ - 1) / cfg.b) *
          ((64 / cfg.η) * ∫ tail', Dep cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) tail'
              ∂(Measure.infinitePi fun _ : ℕ => ν) + 2 * cfg.K * Dm cfg ρ ^ 2)
          ∂(Measure.infinitePi fun _ : ℕ => ν) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun tail => integral_nonneg fun _ => nsqE_nonneg _ _)
        (((hDinner.const_mul _).add (integrable_const _)).const_mul _) (Filter.Eventually.of_forall hinner)
    rw [integral_const_mul, integral_add (hDinner.const_mul _) (integrable_const _), integral_const_mul,
      integral_const, ← hDti] at h3
    simp only [probReal_univ, one_smul] at h3
    unfold kap1 kap2
    have hc2 : 0 < (εi - cert cfg ρ) ^ 2 := by positivity
    calc _ ≤ _ := h2
      _ ≤ 1 / (εi - cert cfg ρ) ^ 2 * ((2 / cfg.K) ^ 2 * ((κ - 1) / cfg.b) *
          ((64 / cfg.η) * ∫ tail, Dep cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)
            ∂(Measure.infinitePi fun _ : ℕ => ν) + 2 * cfg.K * Dm cfg ρ ^ 2)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by field_simp
  have hRe : ∀ e, ∫ tail, rejE cfg x0 g f εi (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) (shift (e * cfg.Eb) tail)
      ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ r := by
    intro e
    rw [tail_integral (astep cfg x0 g f) sN ν (measurable_astep' H) (e * cfg.Eb) _ (rejE_measurable H) (hRi e)]
    have hinner : ∀ tail, ∫ tail', rejE cfg x0 g f εi (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) tail'
        ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ r := by
      intro tail
      by_cases hd' : (run (astep cfg x0 g f) sN tail (e * cfg.Eb)).1.done = false
      · obtain ⟨hinv', hpos'⟩ := hstart e tail hd'
        exact rej_bound H hinv' hpos' hd'
      · have heq : ∀ tail', rejE cfg x0 g f εi (run (astep cfg x0 g f) sN tail (e * cfg.Eb)) tail' = 0 := by
          intro tail'; unfold rejE; rw [ite_eq_right]; intro h'; exact hd' h'.1
        simp_rw [heq]; rw [integral_zero]; exact hr0
    calc _ ≤ ∫ tail, r ∂(Measure.infinitePi fun _ : ℕ => ν) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun tail => integral_nonneg fun _ => by
            unfold rejE; split_ifs <;> norm_num) (integrable_const _) (Filter.Eventually.of_forall hinner)
      _ = r := by simp
  have hsumD := trial_decrease H hts hd
  have hX : ∀ e, ∫ tail, Xe e tail ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      (2 / a0 + kap1 cfg ρ εi κ) * (∫ tail, Dep cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb))
        (shift (e * cfg.Eb) tail) ∂(Measure.infinitePi fun _ : ℕ => ν)) + kap2 cfg ρ εi κ + r := by
    intro e
    simp only [Xe]
    have hTB : Integrable (fun tail => trigE cfg x0 g f (run (astep cfg x0 g f) sN tail (e * cfg.Eb))
        (shift (e * cfg.Eb) tail) + badE cfg x0 g f εi (run (astep cfg x0 g f) sN tail (e * cfg.Eb))
        (shift (e * cfg.Eb) tail)) (Measure.infinitePi fun _ : ℕ => ν) := (hTi e).add (hBi e)
    rw [integral_add hTB (hRi e), integral_add (hTi e) (hBi e)]
    linarith [hTe e, hBe e, hRe e]
  have hXsum := Finset.sum_le_sum (fun e (_ : e ∈ Finset.range cfg.N1) => hX e)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, nsmul_eq_mul] at hXsum
  have hk1 : 0 ≤ 2 / a0 + kap1 cfg ρ εi κ := by
    unfold kap1; have := H.hc.hη; positivity
  have hDsum0 := mul_le_mul_of_nonneg_left hsumD hk1
  have hfin : ∑ e ∈ Finset.range cfg.N1, ∫ tail, Xe e tail ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      (2 / a0 + kap1 cfg ρ εi κ) * (Δ + cfg.N1 * cEpoch cfg ρ) + cfg.N1 * kap2 cfg ρ εi κ + cfg.N1 * r := by
    linarith
  calc _ ≤ _ := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left hfin (by positivity)

end fail

end LongTails.Proofs.StrongGrowthAgdTrial
