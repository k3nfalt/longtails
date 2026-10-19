import LongTails.Algorithms.Adam
import LongTails.Proofs.Execution
import LongTails.Proofs.AdamHeavyTailedNormalizer
import LongTails.Proofs.AdamHeavyTailedProcess
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory

namespace OracleTemplate.Adam

noncomputable def trajectory {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) : ℕ → Point d × Point d × Point d
  | 0 => (x0, 0, 0)
  | t + 1 =>
      let s := trajectory g q ρ η τ x0 ξ t
      let reply := g s.1 (ξ t)
      let m := q • s.2.1 + (1 - q) • reply
      let v := secondMomentStep ρ s.2.2 reply
      (s.1 - η • direction τ m v, m, v)

lemma trajectory_secondMoment_nonneg {d : ℕ} {Ω : Type*}
    (g : Point d → Ω → Point d) (q η τ : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (x0 : Point d) (ξ : ℕ → Ω) (t : ℕ) (i : Fin d) :
    0 ≤ (trajectory g q ρ η τ x0 ξ t).2.2 i := by
  induction t with
  | zero => simp [trajectory]
  | succ t ih =>
      change 0 ≤ (1 - ρ) * (trajectory g q ρ η τ x0 ξ t).2.2 i +
        ρ * (g (trajectory g q ρ η τ x0 ξ t).1 (ξ t) i) ^ 2
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hρ1) ih) (mul_nonneg hρ (sq_nonneg _))

lemma measurable_coordinate {d : ℕ} (i : Fin d) :
    Measurable (fun x : Point d => x i) :=
  (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin d → ℝ))

lemma measurable_secondMomentStep {d : ℕ} (ρ : ℝ) :
    Measurable (fun z : Point d × Point d => secondMomentStep ρ z.1 z.2) := by
  apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
  apply Measurable.of_eval
  intro i
  exact (measurable_const.mul ((measurable_coordinate i).comp measurable_fst)).add
    (measurable_const.mul (((measurable_coordinate i).comp measurable_snd).pow_const 2))

lemma measurable_direction {d : ℕ} (τ : ℝ) :
    Measurable (fun z : Point d × Point d => direction τ z.1 z.2) := by
  apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
  apply Measurable.of_eval
  intro i
  exact ((measurable_coordinate i).comp measurable_fst).div
    (((measurable_coordinate i).comp measurable_snd).sqrt.add_const τ)

lemma measurable_trajectory {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → Point d} (hg : Measurable (Function.uncurry g))
    (q ρ η τ : ℝ) (x0 : Point d) (t : ℕ) :
    Measurable (fun ξ : ℕ → Ω => trajectory g q ρ η τ x0 ξ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hg' := hg.comp (ih.fst.prodMk (measurable_pi_apply t))
      have hm := (ih.snd.fst.const_smul q).add (hg'.const_smul (1 - q))
      have hv := (measurable_secondMomentStep ρ).comp (ih.snd.snd.prodMk hg')
      exact (ih.fst.sub (((measurable_direction τ).comp (hm.prodMk hv)).const_smul η)).prodMk
        (hm.prodMk hv)

lemma trajectory_congr {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (t : ℕ) {ξ ζ : ℕ → Ω}
    (h : ∀ k < t, ξ k = ζ k) :
    trajectory g q ρ η τ x0 ξ t = trajectory g q ρ η τ x0 ζ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hprev := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
      simp only [trajectory, hprev, h t (Nat.lt_succ_self t)]

lemma update_trajectory_coordinates {d : ℕ} {Ω : Type*}
    (g : Point d → Ω → Point d) (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω)
    (t : ℕ) (s : State d)
    (hx : s.point = (trajectory g q ρ η τ x0 ξ t).1)
    (hm : s.momentum = (trajectory g q ρ η τ x0 ξ t).2.1)
    (hv : s.secondMoment = (trajectory g q ρ η τ x0 ξ t).2.2) :
    let s' := update q ρ η τ s (g s.point (ξ t))
    s'.point = (trajectory g q ρ η τ x0 ξ (t + 1)).1 ∧
      s'.momentum = (trajectory g q ρ η τ x0 ξ (t + 1)).2.1 ∧
      s'.secondMoment = (trajectory g q ρ η τ x0 ξ (t + 1)).2.2 := by
  simp [update, trajectory, hx, hm, hv]

noncomputable def executionState {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (selected t : ℕ) : State d :=
  { selected := selected
    time := t
    point := (trajectory g q ρ η τ x0 ξ t).1
    momentum := (trajectory g q ρ η τ x0 ξ t).2.1
    secondMoment := (trajectory g q ρ η τ x0 ξ t).2.2
    saved := if selected < t then (trajectory g q ρ η τ x0 ξ selected).1 else x0 }

lemma executionState_succ {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (selected t : ℕ) :
    executionState g q ρ η τ x0 ξ selected (t + 1) =
      update q ρ η τ (executionState g q ρ η τ x0 ξ selected t)
        (g (trajectory g q ρ η τ x0 ξ t).1 (ξ t)) := by
  by_cases hlt : selected < t
  · simp [executionState, update, trajectory, hlt, Nat.lt_succ_of_lt hlt,
      show t ≠ selected by omega]
  · by_cases he : selected = t
    · subst selected
      simp [executionState, update, trajectory]
    · simp [executionState, update, trajectory, hlt, show ¬ selected < t + 1 by omega,
        show t ≠ selected by omega]

lemma execute_trajectory {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (g : Point d → Ω → Point d) (P : ProbabilityMeasure (ℕ → Ω))
    (q ρ η τ : ℝ) (n : ℕ) (x0 : Point d) (selected : Fin (n + 1)) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω
              law := P
              answer := fun _ (_, x) ω => g x ω }
      (method q ρ η τ n x0) (fun _ => n + 1) selected ξ =
        (trajectory g q ρ η τ x0 ξ selected.val).1 := by
  apply execute_eq_of_safe_prefix
    (state := executionState g q ρ η τ x0 ξ selected.val)
    (remaining := fun t _ => n + 1 - t) (T := n + 1)
  · simp [executionState, trajectory, method]
  · intro t
    exact executionState_succ g q ρ η τ x0 ξ selected.val t
  · rfl
  · intro t
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [method]
    omega
  · intro t ht
    simpa using Nat.sub_pos_of_lt ht
  · intro t ht
    have hk : selected.val < t := lt_of_lt_of_le selected.isLt ht
    simp [method, executionState, hk]
  · simp

noncomputable def velocity {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (t : ℕ) : Point d :=
  direction τ (trajectory g q ρ η τ x0 ξ t).2.1 (trajectory g q ρ η τ x0 ξ t).2.2

noncomputable def instantDirection {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (t : ℕ) : Point d :=
  direction τ (g (trajectory g q ρ η τ x0 ξ t).1 (ξ t))
    (trajectory g q ρ η τ x0 ξ (t + 1)).2.2

lemma instantDirection_coordinate_bound {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    {q ρ η τ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hτ : 0 < τ)
    (x0 : Point d) (ξ : ℕ → Ω) (t : ℕ) (i : Fin d) :
    |instantDirection g q ρ η τ x0 ξ t i| ≤ 1 / Real.sqrt ρ := by
  exact LongTails.Proofs.AdamHeavyTailedNormalizer.normalized_current_bound
    (trajectory_secondMoment_nonneg g q η τ hρ.le hρ1 x0 ξ t i) hρ hρ1 hτ
    (g (trajectory g q ρ η τ x0 ξ t).1 (ξ t) i)

lemma velocity_coordinate_bound {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (x0 : Point d) (ξ : ℕ → Ω) (t : ℕ) (i : Fin d) :
    |velocity g q ρ η τ x0 ξ t i| ≤
      (1 - q) * (1 / Real.sqrt ρ) / (1 - q / Real.sqrt (1 - ρ)) := by
  apply LongTails.Proofs.AdamHeavyTailedAlgebra.geometric_uniform_bound
    (div_nonneg hq (Real.sqrt_nonneg _)) hstable (sub_nonneg.mpr hq1) (by positivity)
    (fun t => |velocity g q ρ η τ x0 ξ t i|)
    (fun t => |instantDirection g q ρ η τ x0 ξ t i|)
  · simp [velocity, trajectory, direction]
  · intro t
    exact instantDirection_coordinate_bound g hρ hρ1.le hτ x0 ξ t i
  · intro t
    exact LongTails.Proofs.AdamHeavyTailedNormalizer.normalized_momentum_step
      hρ.le hρ1 hτ hq hq1
      ((trajectory g q ρ η τ x0 ξ t).2.1 i)
      (g (trajectory g q ρ η τ x0 ξ t).1 (ξ t) i)

lemma velocity_norm_bound {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (x0 : Point d) (ξ : ℕ → Ω) (t : ℕ) :
    ‖velocity g q ρ η τ x0 ξ t‖ ≤
      ((d : ℝ) + 1) * ((1 - q) * (1 / Real.sqrt ρ) / (1 - q / Real.sqrt (1 - ρ))) := by
  let C := (1 - q) * (1 / Real.sqrt ρ) / (1 - q / Real.sqrt (1 - ρ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : ‖velocity g q ρ η τ x0 ξ t‖ ^ 2 ≤ (d : ℝ) * C ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _i : Fin d, C ^ 2 := Finset.sum_le_sum fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (velocity_coordinate_bound g hq hq1 hρ hρ1 hτ hstable x0 ξ t i) 2
      _ = _ := by simp
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hc : 0 ≤ ((d : ℝ) + 1) * C := by positivity
  have hsq : (d : ℝ) * C ^ 2 ≤ (((d : ℝ) + 1) * C) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (sq_nonneg C),
      mul_nonneg hd (sq_nonneg C)]
  nlinarith [norm_nonneg (velocity g q ρ η τ x0 ξ t)]

lemma trajectory_distance_bound {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (x0 : Point d) (ξ : ℕ → Ω) (t : ℕ) :
    ‖(trajectory g q ρ η τ x0 ξ t).1 - x0‖ ≤
      (t : ℝ) * (|η| * (((d : ℝ) + 1) *
        ((1 - q) * (1 / Real.sqrt ρ) / (1 - q / Real.sqrt (1 - ρ))))) := by
  induction t with
  | zero => simp [trajectory]
  | succ t ih =>
      have he : (trajectory g q ρ η τ x0 ξ (t + 1)).1 - x0 =
          ((trajectory g q ρ η τ x0 ξ t).1 - x0) - η • velocity g q ρ η τ x0 ξ (t + 1) := by
        simp only [trajectory, velocity]
        abel
      rw [he]
      have hv := velocity_norm_bound (η := η) g hq hq1 hρ hρ1 hτ hstable x0 ξ (t + 1)
      have hn := norm_sub_le ((trajectory g q ρ η τ x0 ξ t).1 - x0)
        (η • velocity g q ρ η τ x0 ξ (t + 1))
      rw [norm_smul, Real.norm_eq_abs] at hn
      have hm := mul_le_mul_of_nonneg_left hv (abs_nonneg η)
      push_cast
      nlinarith

lemma velocity_coordinate_energy {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (x0 : Point d) (ξ : ℕ → Ω) (T : ℕ) (i : Fin d) :
    (∑ t ∈ Finset.range T, (velocity g q ρ η τ x0 ξ (t + 1) i) ^ 2) ≤
      ((1 - q) / (1 - q / Real.sqrt (1 - ρ))) ^ 2 *
        ∑ t ∈ Finset.range T, (instantDirection g q ρ η τ x0 ξ t i) ^ 2 := by
  have hzero : |velocity g q ρ η τ x0 ξ 0 i| = 0 := by
    simp [velocity, trajectory, direction]
  have hstep (t : ℕ) : |velocity g q ρ η τ x0 ξ (t + 1) i| ≤
      (q / Real.sqrt (1 - ρ)) * |velocity g q ρ η τ x0 ξ t i| +
        (1 - q) * |instantDirection g q ρ η τ x0 ξ t i| := by
    exact LongTails.Proofs.AdamHeavyTailedNormalizer.normalized_momentum_step
      hρ hρ1 hτ hq hq1
      ((trajectory g q ρ η τ x0 ξ t).2.1 i)
      (g (trajectory g q ρ η τ x0 ξ t).1 (ξ t) i)
  have hh := LongTails.Proofs.AdamHeavyTailedAlgebra.geometric_energy
    (div_nonneg hq (Real.sqrt_nonneg _)) hstable
    (fun t => |velocity g q ρ η τ x0 ξ t i|)
    (fun t => |instantDirection g q ρ η τ x0 ξ t i|)
    (fun _ => abs_nonneg _) hzero hstep T
  simpa only [sq_abs] using hh

lemma velocity_energy {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (x0 : Point d) (ξ : ℕ → Ω) (T : ℕ) :
    (∑ t ∈ Finset.range T, ‖velocity g q ρ η τ x0 ξ (t + 1)‖ ^ 2) ≤
      ((1 - q) / (1 - q / Real.sqrt (1 - ρ))) ^ 2 *
        ∑ t ∈ Finset.range T, ‖instantDirection g q ρ η τ x0 ξ t‖ ^ 2 := by
  simp_rw [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range T), Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => velocity_coordinate_energy g hq hq1 hρ hρ1 hτ hstable x0 ξ T i

lemma momentum_expansion {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (T : ℕ) (i : Fin d) :
    (trajectory g q ρ η τ x0 ξ T).2.1 i =
      (1 - q) * ∑ k ∈ Finset.range T, q ^ (T - 1 - k) *
        g (trajectory g q ρ η τ x0 ξ k).1 (ξ k) i := by
  apply LongTails.Proofs.AdamHeavyTailedAlgebra.linear_recurrence_expansion q (1 - q)
    (fun t => (trajectory g q ρ η τ x0 ξ t).2.1 i)
    (fun t => g (trajectory g q ρ η τ x0 ξ t).1 (ξ t) i)
  · rfl
  · intro t
    rfl

lemma secondMoment_window {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (s T : ℕ) (i : Fin d) :
    (trajectory g q ρ η τ x0 ξ (s + T)).2.2 i =
      (1 - ρ) ^ T * (trajectory g q ρ η τ x0 ξ s).2.2 i +
        ρ * ∑ k ∈ Finset.range T, (1 - ρ) ^ (T - 1 - k) *
          (g (trajectory g q ρ η τ x0 ξ (s + k)).1 (ξ (s + k)) i) ^ 2 := by
  have hs (k : ℕ) : (trajectory g q ρ η τ x0 ξ (s + (k + 1))).2.2 i =
      (1 - ρ) * (trajectory g q ρ η τ x0 ξ (s + k)).2.2 i +
        ρ * (g (trajectory g q ρ η τ x0 ξ (s + k)).1 (ξ (s + k)) i) ^ 2 := by
    rw [← Nat.add_assoc]
    rfl
  simpa only [Nat.add_zero] using LongTails.Proofs.AdamHeavyTailedAlgebra.linear_recurrence_from
    (1 - ρ) ρ (fun k => (trajectory g q ρ η τ x0 ξ (s + k)).2.2 i)
    (fun k => (g (trajectory g q ρ η τ x0 ξ (s + k)).1 (ξ (s + k)) i) ^ 2) hs T

noncomputable def stateTransition {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (s : Point d × Point d × Point d) (ω : Ω) : Point d × Point d × Point d :=
  let s' := update q ρ η τ ⟨0, 0, s.1, s.2.1, s.2.2, s.1⟩ (g s.1 ω)
  (s'.point, s'.momentum, s'.secondMoment)

lemma trajectory_succ_transition {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (t : ℕ) :
    trajectory g q ρ η τ x0 ξ (t + 1) =
      stateTransition g q ρ η τ (trajectory g q ρ η τ x0 ξ t) (ξ t) := rfl

lemma measurable_stateTransition {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → Point d} (hg : Measurable (Function.uncurry g)) (q ρ η τ : ℝ) :
    Measurable (Function.uncurry (stateTransition g q ρ η τ)) := by
  have hs : Measurable (fun z : (Point d × Point d × Point d) × Ω => (z.1.1, z.2)) := by fun_prop
  have hreply := hg.comp hs
  have hm : Measurable (fun z : (Point d × Point d × Point d) × Ω => q • z.1.2.1 + (1 - q) • g z.1.1 z.2) :=
    (by fun_prop : Measurable (fun z : (Point d × Point d × Point d) × Ω => z.1.2.1)).const_smul q |>.add
      (hreply.const_smul (1 - q))
  have hv : Measurable (fun z : (Point d × Point d × Point d) × Ω => secondMomentStep ρ z.1.2.2 (g z.1.1 z.2)) :=
    (measurable_secondMomentStep ρ).comp ((by fun_prop : Measurable (fun z : (Point d × Point d × Point d) × Ω => z.1.2.2)).prodMk hreply)
  exact ((by fun_prop : Measurable (fun z : (Point d × Point d × Point d) × Ω => z.1.1)).sub
    (((measurable_direction τ).comp (hm.prodMk hv)).const_smul η)).prodMk (hm.prodMk hv)

lemma integrable_error_coordinate {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → Point d}
    (hg : Integrable g P) (μ : Point d) (i : Fin d) :
    Integrable (fun ω => (g ω - μ) i) P := by
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).integrable_comp (hg.sub (integrable_const μ))

lemma integral_error_coordinate {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → Point d}
    (hg : Integrable g P) (μ : Point d) (hmean : ∫ ω, g ω ∂P = μ) (i : Fin d) :
    (∫ ω, (g ω - μ) i ∂P) = 0 := by
  have hp := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).integral_comp_comm (hg.sub (integrable_const μ))
  change (∫ ω, (g ω - μ) i ∂P) = (∫ ω, g ω - μ ∂P) i at hp
  rw [integral_sub hg (integrable_const μ), hmean, integral_const, probReal_univ,
    one_smul, sub_self] at hp
  simpa using hp

lemma stateAt_initial {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (t : ℕ) :
    LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ) (x0, 0, 0) ξ t =
      trajectory g q ρ η τ x0 ξ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [LongTails.Proofs.AdamHeavyTailedProcess.stateAt_succ, ih, trajectory_succ_transition]

lemma stateAt_after {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (s t : ℕ) :
    LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ)
      (trajectory g q ρ η τ x0 ξ s) (fun k => ξ (s + k)) t =
        trajectory g q ρ η τ x0 ξ (s + t) := by
  induction t with
  | zero => simp [LongTails.Proofs.AdamHeavyTailedProcess.stateAt_zero]
  | succ t ih =>
    rw [LongTails.Proofs.AdamHeavyTailedProcess.stateAt_succ, ih]
    simpa only [Nat.add_assoc] using (trajectory_succ_transition g q ρ η τ x0 ξ (s + t)).symm

lemma iid_sequence_law {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω} {P : Measure (ℕ → Ω)}
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) p P) :
    P = Measure.infinitePi (fun _ : ℕ => p) := by
  have hh := h.stream_law.map_eq
  change P.map id = _ at hh
  simpa only [Measure.map_id] using hh

noncomputable def stateError {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (grad : Point d → Point d) (s : Point d × Point d × Point d) (ω : Ω) : Fin d → ℝ :=
  fun i => (g s.1 ω - grad s.1) i

lemma measurable_stateError {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → Point d} {grad : Point d → Point d}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad) :
    Measurable (Function.uncurry (stateError g grad)) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_coordinate i).comp
    ((hg.comp (by fun_prop : Measurable (fun z : (Point d × Point d × Point d) × Ω => (z.1.1, z.2)))).sub
      (hgrad.comp (by fun_prop : Measurable (fun z : (Point d × Point d × Point d) × Ω => z.1.1))))

lemma integrable_error_power {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {g : Ω → Point d} (hg : Measurable g) (μ : Point d) (p : ℝ)
    (hm : Integrable (fun ω => ∑ i, |(g ω - μ) i| ^ p) P) (i : Fin d) :
    Integrable (fun ω => |(g ω - μ) i| ^ p) P := by
  have hi : Measurable (fun ω => |(g ω - μ) i| ^ p) := by
    exact (continuous_abs.measurable.comp ((measurable_coordinate i).comp (hg.sub measurable_const))).pow measurable_const
  apply hm.mono' hi.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)

lemma sum_integral_error_power {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {g : Ω → Point d} (hg : Measurable g) (μ : Point d) (p : ℝ)
    (hm : Integrable (fun ω => ∑ i, |(g ω - μ) i| ^ p) P) :
    (∑ i, ∫ ω, |(g ω - μ) i| ^ p ∂P) = ∫ ω, ∑ i, |(g ω - μ) i| ^ p ∂P := by
  exact (integral_finsetSum _ (fun i _ => integrable_error_power hg μ p hm i)).symm

lemma oracle_window_bias {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {grad : Point d → Point d} (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad)
    (hint : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    {p M : ℝ} (hm : ∀ x, Integrable (fun ω => ∑ k, |(g x ω - grad x) k| ^ p) P)
    (hmass : ∀ x, ∫ ω, ∑ k, |(g x ω - grad x) k| ^ p ∂P ≤ M)
    {N : ℕ} (q ρ η : ℝ) {τ B : ℝ} (w : Fin d → ℝ) (a : Fin N → ℝ) (i : Fin N)
    (hw : ∀ k, 0 ≤ w k) (ha : ∀ j, 0 ≤ a j) (hτ : 0 < τ) (hai : 0 < a i)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (s : Point d × Point d × Point d)
    (hcoef : ∀ j k, |grad s.1 k| *
      ((4 * (Real.sqrt (a j) / (Real.sqrt (w k) + τ)) ^ p) / Real.sqrt (a i)) * M ≤ B) :
    (∫ ξ, (∑ k, grad s.1 k * LongTails.Proofs.AdamHeavyTailedWindow.response (w k) a τ i (fun _ => grad s.1 k)) -
      (∑ k, grad s.1 k * LongTails.Proofs.AdamHeavyTailedWindow.response (w k) a τ i
        (fun j => grad s.1 k + stateError g grad
          (LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ) s ξ j.val) (ξ j.val) k))
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ (N : ℝ) * B := by
  apply LongTails.Proofs.AdamHeavyTailedProcess.frozen_window_bias_scaled P
    (stateTransition g q ρ η τ) (stateError g grad)
    (measurable_stateTransition hg q ρ η τ) (measurable_stateError hg hgrad)
    w (fun k => grad s.1 k) a i hw ha hτ hai hp hp2 hB hM
  · intro s' k
    exact integrable_error_coordinate (hint s'.1) (grad s'.1) k
  · intro s' k
    exact integral_error_coordinate (hint s'.1) (grad s'.1) (hmean s'.1) k
  · intro s' k
    exact integrable_error_power (hg.comp measurable_prodMk_left) (grad s'.1) p (hm s'.1) k
  · intro s'
    change (∑ k, ∫ ω, |(g s'.1 ω - grad s'.1) k| ^ p ∂P) ≤ M
    exact (sum_integral_error_power (hg.comp measurable_prodMk_left) (grad s'.1) p (hm s'.1)).trans_le (hmass s'.1)
  · exact hcoef

lemma trajectory_denominator_decay {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q η : ℝ) {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hτ : 0 ≤ τ)
    (x0 : Point d) (ξ : ℕ → Ω) (s j : ℕ) (i : Fin d) :
    Real.sqrt ((1 - ρ) ^ j) * (Real.sqrt ((trajectory g q ρ η τ x0 ξ s).2.2 i) + τ) ≤
      Real.sqrt ((trajectory g q ρ η τ x0 ξ (s + j)).2.2 i) + τ := by
  have hb : 0 ≤ 1 - ρ := sub_nonneg.mpr hρ1
  have hb1 : 1 - ρ ≤ 1 := by linarith
  have hp : (1 - ρ) ^ j ≤ 1 := pow_le_one₀ hb hb1
  have hs : Real.sqrt ((1 - ρ) ^ j) ≤ 1 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by simpa using hp⟩
  have hv : (1 - ρ) ^ j * (trajectory g q ρ η τ x0 ξ s).2.2 i ≤
      (trajectory g q ρ η τ x0 ξ (s + j)).2.2 i := by
    rw [secondMoment_window]
    exact le_add_of_nonneg_right (mul_nonneg hρ (Finset.sum_nonneg fun k _ =>
      mul_nonneg (pow_nonneg hb _) (sq_nonneg _)))
  calc
    _ = Real.sqrt ((1 - ρ) ^ j * (trajectory g q ρ η τ x0 ξ s).2.2 i) +
        Real.sqrt ((1 - ρ) ^ j) * τ := by rw [Real.sqrt_mul (pow_nonneg hb j), mul_add]
    _ ≤ _ := add_le_add (Real.sqrt_le_sqrt hv) (by simpa using mul_le_mul_of_nonneg_right hs hτ)

lemma trajectory_past_response_bound {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q η : ℝ) {ρ τ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ)
    (x0 : Point d) (ξ : ℕ → Ω) (s j : ℕ) (i : Fin d) :
    |g (trajectory g q ρ η τ x0 ξ s).1 (ξ s) i| /
      (Real.sqrt ((trajectory g q ρ η τ x0 ξ (s + j + 1)).2.2 i) + τ) ≤
        (1 / Real.sqrt ((1 - ρ) ^ j)) * |instantDirection g q ρ η τ x0 ξ s i| := by
  have hb : 0 < Real.sqrt ((1 - ρ) ^ j) := Real.sqrt_pos.mpr (pow_pos (sub_pos.mpr hρ1) j)
  have hd : 0 < Real.sqrt ((trajectory g q ρ η τ x0 ξ (s + 1)).2.2 i) + τ := by positivity
  have he : s + j + 1 = s + 1 + j := by omega
  have hdec := trajectory_denominator_decay g q η hρ.le hρ1.le hτ.le x0 ξ (s + 1) j i
  rw [he]
  calc
    _ ≤ |g (trajectory g q ρ η τ x0 ξ s).1 (ξ s) i| /
        (Real.sqrt ((1 - ρ) ^ j) * (Real.sqrt ((trajectory g q ρ η τ x0 ξ (s + 1)).2.2 i) + τ)) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hb hd) hdec
    _ = _ := by
      simp only [instantDirection, direction, abs_div, abs_of_pos hd]
      field_simp

end OracleTemplate.Adam
