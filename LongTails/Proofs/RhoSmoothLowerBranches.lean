import LongTails.Proofs.RhoSmoothHardOracle
import LongTails.Proofs.FinitePrefixExpectation
import LongTails.Proofs.MollifiedSmoothLowerBound
import LongTails.Proofs.FullGeneralizedSmoothZeroQuery
import LongTails.Proofs.TailEntropyBudget
import LongTails.Proofs.FullGeneralizedSmoothParameters
import LongTails.TemplateLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.RhoSmoothLowerBranches

open LongTails.Setups.RhoSmoothConvexFull
open RhoSmoothHardOracle RhoSmoothHardParameters RhoSmoothHardInstance

lemma chain_failure (p : Params) (hp : spec.valid p) (N : ℕ) (hN : N + 1 ≤ links p)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p f O ∧
        ¬ spec.successful p f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  let B := radius p
  let θ := thresh p
  let D := 2 * ((N + 1 : ℕ) : ℝ) ^ 2 * (B ^ 2 / θ ^ 2)
  have hB : 0 < B := radius_pos p hp
  have hθ : 0 < θ := thresh_pos p hp
  have hD : 0 < D := by dsimp [D]; positivity
  have hDs : D + (N + 1 : ℕ) ≤ (p.d : ℝ) := by
    have hh := dimension_ok p hp (N + 1) hN
    change (N + 1 : ℕ) + D ≤ (p.d : ℝ) at hh
    linarith
  let reply := fun π : Fin (N + 1) ↪ Fin p.d => field p hp (N + 1) hN π
  let loss := fun π : Fin (N + 1) ↪ Fin p.d => objective p hp (N + 1) hN π
  let partialFn := partialReply p hp (N + 1)
  let query := fun s => (A.query s).2 - p.x0
  let output := fun s => A.output s - p.x0
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure A.Seed).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  have hε := ε_pos p hp
  obtain ⟨π, hbad⟩ := FinitePrefixExpectation.exists_failure B θ D (3 * p.ε) p.ε hB.le hθ hD
    (by positivity) hDs le_rfl (by linarith)
    partialFn reply loss (partialReply_prefix p hp (N + 1))
    (fun π r x hr hs => partialReply_eq p hp (N + 1) hN π ⟨r, by omega⟩ x hs)
    (objective_nonnegative p hp (N + 1) hN)
    (fun π x hx => objective_near_gap p hp (N + 1) hN π (Fin.last N) x hx)
    (objective_far_gap p hp (N + 1) hN)
    query output A.update (fun w : A.Seed × (ℕ → Unit) => A.initial w.1) P
  let f := loss π
  let g := reply π
  let z := (seed p hp (N + 1) hN π).z
  let O := SmoothConvexFiniteLowerBound.oracle p.x0 g
  refine ⟨fun x : EuclideanSpace ℝ (Fin p.d) => f (x - p.x0), O,
    admissible p hp (N + 1) hN π, ?_⟩
  rintro ⟨xstar, hmin, hi, he⟩
  change EuclideanSpace ℝ (Fin p.d) at xstar
  have hz : f (xstar - p.x0) = 0 := by
    apply le_antisymm
    · have hh := hmin (Set.mem_univ (p.x0 + z))
      change f (xstar - p.x0) ≤ f (p.x0 + z - p.x0) at hh
      rw [add_sub_cancel_left] at hh
      exact hh.trans_eq (objective_zero p hp (N + 1) hN π)
    · exact objective_nonnegative p hp (N + 1) hN π _
  have hout :
      (fun w : A.Seed × (ℕ → Unit) => f (execute O A (fun _ => N) w.1 w.2 - p.x0) - f (xstar - p.x0)) =
      fun w => f (output ((fun s => A.update s (g (query s)))^[N] (A.initial w.1))) := by
    funext w
    rw [hz, sub_zero, SmoothConvexFiniteLowerBound.execute_translated p.x0 g A N w.1 w.2]
  apply hbad
  constructor
  · change Integrable (fun w : A.Seed × (ℕ → Unit) =>
      f (output ((fun s => A.update s (g (query s)))^[N] (A.initial w.1)))) (P : Measure _)
    rw [← hout]
    exact hi
  · change (∫ w : A.Seed × (ℕ → Unit),
      f (output ((fun s => A.update s (g (query s)))^[N] (A.initial w.1))) ∂(P : Measure _)) ≤ p.ε
    rw [← hout]
    exact he

noncomputable def smoothParams (p : Params) : LongTails.Setups.GeneralizedSmoothConvexFull.Params :=
  { d := p.d, L0 := p.L0, L1 := 0, x0 := p.x0, R := p.R, ε := p.ε }

lemma smoothParams_valid (p : Params) (hp : spec.valid p) :
    LongTails.Setups.GeneralizedSmoothConvexFull.spec.valid (smoothParams p) := by
  have hq := sq_nonneg (p.L0 * p.R / (p.L0 / p.L1) ^ (1 / p.ρ))
  have hs := Real.sqrt_nonneg (p.L0 * p.R ^ 2 / p.ε)
  refine ⟨hp.1, le_rfl, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, ?_⟩
  change ⌈17592186044416 * (1 + 0 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 5⌉₊ ≤ p.d
  apply le_trans _ hp.2.2.2.2.2.2.2
  apply Nat.ceil_le_ceil
  have h1 : (1 + 0 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 5 ≤
      (1 + (p.L0 * p.R / (p.L0 / p.L1) ^ (1 / p.ρ)) ^ 2 + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 6 := by
    have hb : 1 ≤ 1 + (p.L0 * p.R / (p.L0 / p.L1) ^ (1 / p.ρ)) ^ 2 +
        Real.sqrt (p.L0 * p.R ^ 2 / p.ε) := by linarith
    calc (1 + 0 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 5
        ≤ (1 + (p.L0 * p.R / (p.L0 / p.L1) ^ (1 / p.ρ)) ^ 2 +
            Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 5 :=
          pow_le_pow_left₀ (by rw [zero_mul]; positivity) (by linarith) 5
      _ ≤ _ := pow_le_pow_right₀ hb (by norm_num)
  linarith

lemma transfer_failure (p : Params) (hp : spec.valid p) (N : ℕ)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d)))
    (h : ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      LongTails.Setups.GeneralizedSmoothConvexFull.spec.admissible (smoothParams p) f O ∧
        ¬ LongTails.Setups.GeneralizedSmoothConvexFull.spec.successful (smoothParams p) f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩) :
    ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p f O ∧
        ¬ spec.successful p f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨f, O, ⟨hc, hg, hd, hH, hmin⟩, hfail⟩ := h
  refine ⟨f, O, ⟨hc, hg, hd, fun k ω x => ?_, hmin⟩, hfail⟩
  have h1 := hH k ω x
  change ‖fderiv ℝ (fun y => O.answer k (0, y) ω) x‖ ≤ p.L0 + 0 * ‖O.answer k (0, x) ω‖ at h1
  have h2 : 0 ≤ p.L1 * ‖O.answer k (0, x) ω‖ ^ p.ρ :=
    mul_nonneg hp.2.1.le (Real.rpow_nonneg (norm_nonneg _) _)
  change ‖fderiv ℝ (fun y => O.answer k (0, y) ω) x‖ ≤ p.L0 + p.L1 * ‖O.answer k (0, x) ω‖ ^ p.ρ
  linarith

lemma links_bound (p : Params) (hp : spec.valid p) (N : ℕ)
    (hbig : 16777216 ≤ (p.ρ - 1) ^ 2 * quad p / 16)
    (hN : N + 1 ≤ ⌊(p.ρ - 1) ^ 2 * quad p / 16 / 33554432⌋₊ + 1) : N + 1 ≤ links p := by
  unfold links
  rw [ratio_sq_eq p hp]
  apply Nat.le_floor
  have hq : 0 ≤ (p.ρ - 1) ^ 2 * quad p := by unfold quad; positivity
  have h1 : (N : ℝ) ≤ (p.ρ - 1) ^ 2 * quad p / 16 / 33554432 := by
    have h2 : N ≤ ⌊(p.ρ - 1) ^ 2 * quad p / 16 / 33554432⌋₊ := by omega
    exact (Nat.cast_le.mpr h2).trans (Nat.floor_le (div_nonneg (div_nonneg hq (by norm_num)) (by norm_num)))
  push_cast
  linarith

end LongTails.Proofs.RhoSmoothLowerBranches
