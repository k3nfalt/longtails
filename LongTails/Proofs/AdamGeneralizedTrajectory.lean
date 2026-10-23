import LongTails.Algorithms.GeneralizedSmoothAdam
import LongTails.Proofs.AdamHeavyTailedTrajectory
import LongTails.Proofs.AdamAccumulator

open MeasureTheory

namespace LongTails.Proofs.AdamGeneralizedTrajectory

open OracleTemplate LongTails.Algorithms.GeneralizedSmoothAdam

lemma secondMoment_lower {d : ℕ} {Ω : Type*}
    (g : Adam.Point d → Ω → Adam.Point d) (β η τ vinit : ℝ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (x0 : Adam.Point d) (ξ : ℕ → Ω) (t : ℕ) (i : Fin d) :
    (1 - ρ) ^ t * vinit ≤ (trajectory g β ρ η τ vinit x0 ξ t).2.2 i := by
  induction t with
  | zero => simp [trajectory]
  | succ t ih =>
      change (1 - ρ) ^ (t + 1) * vinit ≤
        (1 - ρ) * (trajectory g β ρ η τ vinit x0 ξ t).2.2 i +
          ρ * (g (trajectory g β ρ η τ vinit x0 ξ t).1 (ξ t) i) ^ 2
      rw [pow_succ]
      have hm := mul_le_mul_of_nonneg_left ih (sub_nonneg.2 hρ1)
      have hp := mul_nonneg hρ (sq_nonneg (g (trajectory g β ρ η τ vinit x0 ξ t).1 (ξ t) i))
      nlinarith

lemma secondMoment_pos {d : ℕ} {Ω : Type*}
    (g : Adam.Point d → Ω → Adam.Point d) (β η τ : ℝ) {vinit ρ : ℝ}
    (hv : 0 < vinit) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (x0 : Adam.Point d) (ξ : ℕ → Ω) (t : ℕ) (i : Fin d) :
    0 < (trajectory g β ρ η τ vinit x0 ξ t).2.2 i := by
  exact lt_of_lt_of_le (mul_pos (pow_pos (sub_pos.2 hρ1) t) hv)
    (secondMoment_lower g β η τ vinit hρ hρ1.le x0 ξ t i)

lemma predictable_secondMoment_lower {d : ℕ} {Ω : Type*}
    (g : Adam.Point d → Ω → Adam.Point d) (β η τ : ℝ) {vinit : ℝ} (hv : 0 < vinit)
    {T t : ℕ} (hT : 2 ≤ T) (ht : t < T) (x0 : Adam.Point d) (ξ : ℕ → Ω) (i : Fin d) :
    vinit / 4 ≤ (1 - 1 / (T : ℝ)) *
      (trajectory g β (1 / (T : ℝ)) η τ vinit x0 ξ t).2.2 i := by
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hi : 1 / (T : ℝ) ≤ 1 := (div_le_one hT0).2 (by linarith)
  have hh := secondMoment_lower g β η τ vinit (one_div_nonneg.2 hT0.le) hi x0 ξ t i
  have hp := mul_le_mul_of_nonneg_left hh (sub_nonneg.2 hi)
  have hf := mul_le_mul_of_nonneg_right
    (AdamAccumulator.decay_prefix_lower hT (Nat.succ_le_of_lt ht)) hv.le
  rw [pow_succ] at hf
  nlinarith

lemma momentum_normalized {d : ℕ} {Ω : Type*}
    (g : Adam.Point d → Ω → Adam.Point d) (η τ : ℝ) {β ρ vinit : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hbρ : β ≤ 1 - ρ) (hv : 0 < vinit)
    (x0 : Adam.Point d) (ξ : ℕ → Ω) (t : ℕ) (i : Fin d) :
    ρ * ((trajectory g β ρ η τ vinit x0 ξ t).2.1 i) ^ 2 ≤
      (trajectory g β ρ η τ vinit x0 ξ t).2.2 i := by
  induction t with
  | zero => simpa [trajectory] using hv.le
  | succ t ih =>
      exact AdamAccumulator.momentum_normalized_square hβ hβ1 hbρ hρ
        (secondMoment_pos g β η τ hv hρ hρ1 x0 ξ t i).le ih

lemma measurable_trajectory {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Adam.Point d → Ω → Adam.Point d} (hg : Measurable (Function.uncurry g))
    (β ρ η τ vinit : ℝ) (x0 : Adam.Point d) (t : ℕ) :
    Measurable (fun ξ : ℕ → Ω => trajectory g β ρ η τ vinit x0 ξ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hg' := hg.comp (ih.fst.prodMk (measurable_pi_apply t))
      have hm := (ih.snd.fst.const_smul β).add (hg'.const_smul (1 - β))
      have hv := (Adam.measurable_secondMomentStep ρ).comp (ih.snd.snd.prodMk hg')
      exact (ih.fst.sub (((Adam.measurable_direction τ).comp (hm.prodMk hv)).const_smul η)).prodMk
        (hm.prodMk hv)

lemma trajectory_congr {d : ℕ} {Ω : Type*}
    (g : Adam.Point d → Ω → Adam.Point d) (β ρ η τ vinit : ℝ) (x0 : Adam.Point d)
    (t : ℕ) {ξ ζ : ℕ → Ω} (h : ∀ k < t, ξ k = ζ k) :
    trajectory g β ρ η τ vinit x0 ξ t = trajectory g β ρ η τ vinit x0 ζ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hp := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
      simp only [trajectory, hp, h t (Nat.lt_succ_self t)]

lemma stateAt_initial {d : ℕ} {Ω : Type*}
    (g : Adam.Point d → Ω → Adam.Point d) (β ρ η τ vinit : ℝ) (x0 : Adam.Point d)
    (ξ : ℕ → Ω) (t : ℕ) :
    AdamHeavyTailedProcess.stateAt (Adam.stateTransition g β ρ η τ)
      (x0, 0, WithLp.toLp 2 (fun _ => vinit)) ξ t = trajectory g β ρ η τ vinit x0 ξ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [AdamHeavyTailedProcess.stateAt_succ, ih]
      rfl

lemma trajectory_noise_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : Adam.Point d → Ω → Adam.Point d} {grad : Adam.Point d → Adam.Point d}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad) {σ : ℝ}
    (hi : ∀ x, Integrable (fun ω => ‖g x ω - grad x‖ ^ 2) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - grad x‖ ^ 2 ∂P) ≤ σ ^ 2)
    (β ρ η τ vinit : ℝ) (x0 : Adam.Point d) (ω0 : Ω) (t : ℕ) :
    Integrable (fun ξ => ‖g (trajectory g β ρ η τ vinit x0 ξ t).1 (ξ t) -
      grad (trajectory g β ρ η τ vinit x0 ξ t).1‖ ^ 2)
      (Measure.infinitePi (fun _ : ℕ => P)) ∧
    (∫ ξ, ‖g (trajectory g β ρ η τ vinit x0 ξ t).1 (ξ t) -
      grad (trajectory g β ρ η τ vinit x0 ξ t).1‖ ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ σ ^ 2 := by
  let F := fun s : Adam.Point d × Adam.Point d × Adam.Point d =>
    fun ω => ‖g s.1 ω - grad s.1‖ ^ 2
  have hF : Measurable (Function.uncurry F) :=
    ((hg.comp (by fun_prop : Measurable
      (fun z : (Adam.Point d × Adam.Point d × Adam.Point d) × Ω => (z.1.1, z.2)))).sub
      (hgrad.comp (by fun_prop : Measurable
        (fun z : (Adam.Point d × Adam.Point d × Adam.Point d) × Ω => z.1.1)))).norm.pow_const 2
  have hh := AdamHeavyTailedProcess.stateAt_sample_integrable_bound P
    (Adam.measurable_stateTransition hg β ρ η τ) hF
    (fun s ω => sq_nonneg _) (fun s => hi s.1) (fun s => hm s.1)
    (x0, 0, WithLp.toLp 2 (fun _ => vinit)) ω0 t
  simpa only [F, stateAt_initial] using hh

lemma trajectory_noise_average {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : Adam.Point d → Ω → Adam.Point d} {grad : Adam.Point d → Adam.Point d}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad) {σ : ℝ}
    (hi : ∀ x, Integrable (fun ω => ‖g x ω - grad x‖ ^ 2) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - grad x‖ ^ 2 ∂P) ≤ σ ^ 2)
    (β ρ η τ vinit : ℝ) (x0 : Adam.Point d) (ω0 : Ω) {T : ℕ} (hT : 0 < T) :
    Integrable (fun ξ => (∑ t ∈ Finset.range T,
      ‖g (trajectory g β ρ η τ vinit x0 ξ t).1 (ξ t) -
        grad (trajectory g β ρ η τ vinit x0 ξ t).1‖ ^ 2) / (T * (1 + σ ^ 2)))
      (Measure.infinitePi (fun _ : ℕ => P)) ∧
    (∫ ξ, (∑ t ∈ Finset.range T,
      ‖g (trajectory g β ρ η τ vinit x0 ξ t).1 (ξ t) -
        grad (trajectory g β ρ η τ vinit x0 ξ t).1‖ ^ 2) / (T * (1 + σ ^ 2))
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 1 := by
  have hh := trajectory_noise_moment P hg hgrad hi hm β ρ η τ vinit x0 ω0
  have hsum := integrable_finsetSum (Finset.range T) (fun t _ => (hh t).1)
  refine ⟨hsum.div_const _, ?_⟩
  rw [integral_div, integral_finsetSum _ (fun t _ => (hh t).1)]
  have hb := Finset.sum_le_sum (s := Finset.range T) (fun t _ => (hh t).2)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hb
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  apply (div_le_one (by positivity : 0 < (T : ℝ) * (1 + σ ^ 2))).2
  nlinarith

noncomputable def executionState {d : ℕ} {Ω : Type*} (g : Adam.Point d → Ω → Adam.Point d)
    (q ρ η τ vinit : ℝ) (x0 : Adam.Point d) (ξ : ℕ → Ω) (selected t : ℕ) : Adam.State d :=
  { selected := selected
    time := t
    point := (trajectory g q ρ η τ vinit x0 ξ t).1
    momentum := (trajectory g q ρ η τ vinit x0 ξ t).2.1
    secondMoment := (trajectory g q ρ η τ vinit x0 ξ t).2.2
    saved := if selected < t then (trajectory g q ρ η τ vinit x0 ξ selected).1 else x0 }

lemma executionState_succ {d : ℕ} {Ω : Type*} (g : Adam.Point d → Ω → Adam.Point d)
    (q ρ η τ vinit : ℝ) (x0 : Adam.Point d) (ξ : ℕ → Ω) (selected t : ℕ) :
    executionState g q ρ η τ vinit x0 ξ selected (t + 1) =
      Adam.update q ρ η τ (executionState g q ρ η τ vinit x0 ξ selected t)
        (g (trajectory g q ρ η τ vinit x0 ξ t).1 (ξ t)) := by
  by_cases hlt : selected < t
  · simp [executionState, Adam.update, trajectory, hlt, Nat.lt_succ_of_lt hlt,
      show t ≠ selected by omega]
  · by_cases he : selected = t
    · subst selected
      simp [executionState, Adam.update, trajectory]
    · simp [executionState, Adam.update, trajectory, hlt, show ¬ selected < t + 1 by omega,
        show t ≠ selected by omega]

lemma execute_trajectory {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (g : Adam.Point d → Ω → Adam.Point d) (P : ProbabilityMeasure (ℕ → Ω))
    (q ρ η τ vinit : ℝ) (n : ℕ) (x0 : Adam.Point d) (selected : Fin (n + 1)) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω
              law := P
              answer := fun _ (_, x) ω => g x ω }
      (LongTails.Setups.GeneralizedSmoothAdam.method q ρ η τ vinit n x0) (fun _ => n + 1) selected ξ =
        (trajectory g q ρ η τ vinit x0 ξ selected.val).1 := by
  apply execute_eq_of_safe_prefix
    (state := executionState g q ρ η τ vinit x0 ξ selected.val)
    (remaining := fun t _ => n + 1 - t) (T := n + 1)
  · simp [executionState, trajectory, LongTails.Setups.GeneralizedSmoothAdam.method]
  · intro t
    exact executionState_succ g q ρ η τ vinit x0 ξ selected.val t.length
  · rfl
  · intro t
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [LongTails.Setups.GeneralizedSmoothAdam.method]
    omega
  · intro t ht
    simpa using Nat.sub_pos_of_lt ht
  · intro t ht
    have hk : selected.val < t := lt_of_lt_of_le selected.isLt ht
    simp [LongTails.Setups.GeneralizedSmoothAdam.method, executionState, hk]
  · simp


end LongTails.Proofs.AdamGeneralizedTrajectory
