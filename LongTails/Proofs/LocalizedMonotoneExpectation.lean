import LongTails.Proofs.LocalizedMonotoneAveraging
import LongTails.Proofs.FiniteSumNondualLowerBound
import LongTails.Proofs.LocalizedMonotoneParameters

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.LocalizedMonotoneExpectation

open LocalizedMonotoneSimulation LocalizedMonotoneInstance LocalizedMonotoneAveraging
open FiniteSumNondualLowerAveraging FiniteSumNondualLowerBound

lemma exists_failure {d n k : ℕ} {S Ω : Type*} [MeasurableSpace Ω]
    (a b c γ B η D ε : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (hk : k ≤ n)
    (hB : 3 * b / 2 ≤ B) (hbB : b ≤ B)
    (hcoerce : Real.sqrt (n + 1) * c + (2 * (n + 1) + 1) * η ≤ b)
    (hgap : Real.sqrt (n + 1) * η ≤ c - a - n * (3 * a / 2))
    (hD : 0 < D) (hDs : D + (n + 1 : ℕ) ≤ d)
    (hsize : 2 * (k + 1 : ℕ) * (n + 1 : ℕ) * (B ^ 2 / a ^ 2) ≤ D)
    (hε : 2 * ε < γ * η)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → Reply d → S) (initial : Ω → S) (P : ProbabilityMeasure Ω) :
    ∃ π : Fin (n + 1) ↪ Fin d,
      let loss := fun ω => ‖field a b c γ π
        (output ((fun s => update s (field a b c γ π (query s), jacobian a b γ π (query s)))^[k] (initial ω)))‖
      ¬ (Integrable loss (P : Measure Ω) ∧ (∫ ω, loss ω ∂(P : Measure Ω)) ≤ ε) := by
  classical
  by_contra h
  push Not at h
  let loss := fun (w : CoordinateWords d n) (ω : Ω) =>
    ‖field a b c γ (coordinateEmbedding w)
      (output ((fun s => update s (field a b c γ (coordinateEmbedding w) (query s),
        jacobian a b γ (coordinateEmbedding w) (query s)))^[k] (initial ω)))‖
  have hi (w : CoordinateWords d n) : Integrable (loss w) (P : Measure Ω) :=
    (h (coordinateEmbedding w)).1
  have hu (w : CoordinateWords d n) : (∫ ω, loss w ω ∂(P : Measure Ω)) ≤ ε :=
    (h (coordinateEmbedding w)).2
  have hs : Integrable (fun ω => ∑ w, loss w ω) (P : Measure Ω) :=
    integrable_finsetSum Finset.univ (fun w _ => hi w)
  have hp := integral_mono (integrable_const
    ((γ * η) * Fintype.card (CoordinateWords d n)))
    (hs.const_mul 2) (fun ω => execution_average_residual a b c γ B η D ha hb hc hγ hη hk hB hbB hcoerce hgap
      hD hDs hsize query output update (initial ω))
  have he := integral_finsetSum Finset.univ (fun w (_ : w ∈ Finset.univ) => hi w)
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul, he] at hp
  have hb : (∑ w : CoordinateWords d n, ∫ ω, loss w ω ∂(P : Measure Ω)) ≤
      Fintype.card (CoordinateWords d n) * ε := by
    calc
      _ ≤ ∑ _ : CoordinateWords d n, ε := Finset.sum_le_sum (fun w _ => hu w)
      _ = _ := by simp
  have hd : n + 1 ≤ d := by
    have hh : ((n + 1 : ℕ) : ℝ) ≤ d := by linarith
    exact_mod_cast hh
  have hc : (0 : ℝ) < Fintype.card (CoordinateWords d n) := by
    exact_mod_cast coordinateWords_card_pos d n hd
  have hstrict := mul_lt_mul_of_pos_right hε hc
  change _ ≤ 2 * ∑ w : CoordinateWords d n, ∫ ω, loss w ω ∂(P : Measure Ω) at hp
  nlinarith only [hp, hb, hstrict]

lemma exists_failure_of_dimension {d n k : ℕ} {S Ω : Type*} [MeasurableSpace Ω]
    (L R ε : ℝ) (hL : 0 < L) (hR : 0 < R) (hn : 1 ≤ n) (hk : k ≤ n)
    (hd : 4096 * (n + 1) ^ 5 ≤ d)
    (hε : 2 * ε < L * R ^ 2 / (32 * ((n : ℝ) + 1) ^ 2 * Real.sqrt ((n : ℝ) + 1)))
    (query output : S → Space d) (update : S → Reply d → S) (initial : Ω → S)
    (P : ProbabilityMeasure Ω) :
    let a := LocalizedMonotoneParameters.width R n
    let c := LocalizedMonotoneParameters.offset R n
    ∃ π : Fin (n + 1) ↪ Fin d,
      let loss := fun ω => ‖field a (4 * R) c (L * a / 4) π
        (output ((fun s => update s
          (field a (4 * R) c (L * a / 4) π (query s),
           jacobian a (4 * R) (L * a / 4) π (query s)))^[k] (initial ω)))‖
      ¬ (Integrable loss (P : Measure Ω) ∧ (∫ ω, loss ω ∂(P : Measure Ω)) ≤ ε) := by
  let m : ℝ := (n : ℝ) + 1
  let D : ℝ := 2048 * m ^ 5
  have hm : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm0 : 0 < m := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hd' : 4096 * m ^ 5 ≤ (d : ℝ) := by dsimp [m]; exact_mod_cast hd
  have hpow : m ≤ m ^ 5 := by simpa using pow_le_pow_right₀ hm (by decide : 1 ≤ 5)
  have hDs : D + (n + 1 : ℕ) ≤ (d : ℝ) := by
    push_cast
    change D + m ≤ (d : ℝ)
    dsimp [D]
    nlinarith
  have hsize : 2 * (k + 1 : ℕ) * (n + 1 : ℕ) *
      ((6 * R) ^ 2 / (LocalizedMonotoneParameters.width R n) ^ 2) ≤ D := by
    rw [LocalizedMonotoneParameters.observation_ratio R hR n]
    have hkn : ((k + 1 : ℕ) : ℝ) ≤ m := by dsimp [m]; exact_mod_cast Nat.succ_le_succ hk
    push_cast
    change 2 * ((k : ℝ) + 1) * m * (576 * m ^ 3) ≤ 2048 * m ^ 5
    have hh := mul_le_mul_of_nonneg_right hkn (show 0 ≤ 1152 * m ^ 4 by positivity)
    push_cast at hh
    nlinarith [pow_nonneg hm0.le 5]
  apply exists_failure (LocalizedMonotoneParameters.width R n) (4 * R)
    (LocalizedMonotoneParameters.offset R n) (L * LocalizedMonotoneParameters.width R n / 4)
    (6 * R) (R / (2 * m)) D ε (LocalizedMonotoneParameters.width_pos R hR n)
    (by positivity) (LocalizedMonotoneParameters.offset_nonneg R hR n)
    (by have := LocalizedMonotoneParameters.width_pos R hR n; positivity) (by positivity) hk
    (by linarith) (by linarith) (LocalizedMonotoneParameters.coercivity_budget R hR n)
    (LocalizedMonotoneParameters.terminal_budget R hR n hn) hD hDs hsize
    _ query output update initial P
  simpa only [m, LocalizedMonotoneParameters.residual_scale] using hε

end LongTails.Proofs.LocalizedMonotoneExpectation
