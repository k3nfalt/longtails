import LongTails.Proofs.FixedBatchConfidenceExecution
import LongTails.Proofs.AffineMomentOracle
import LongTails.Proofs.AffineMomentNormalization

open MeasureTheory OracleTemplate
open OracleTemplate.HeavyTailedMarkovGradient OracleTemplate.StochasticGradient
open LongTails.Algorithms.AffineMomentAccelerated

namespace LongTails.Proofs.AffineMomentExecution

lemma blockSize_pos {t : Tuning} (ht : LongTails.Proofs.AffineMomentParameters.Valid t) :
    0 < blockSize t := Nat.mul_pos (by norm_num) (LongTails.Proofs.AffineMomentParameters.sampleSize_pos ht)

lemma batch_length {t : Tuning} (ht : LongTails.Proofs.AffineMomentParameters.Valid t) :
    max 1 (blockSize t) = 2 * sampleSize t := max_eq_right (blockSize_pos ht)

lemma base_update_done (p : LongTails.Setups.AffineMomentConvex.Params)
    (s : ℕ × (p.E × p.E)) (hs : iterations (tuning p) ≤ s.1) (replies : ℕ → p.E) :
    (baseAlgorithm p).update s replies = s := by simp [baseAlgorithm, hs]

noncomputable def baseStep (p : LongTails.Setups.AffineMomentConvex.Params)
    (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (call : ℕ) (state : ℕ × (p.E × p.E)) :
    ℕ × (p.E × p.E) :=
  (baseAlgorithm p).update state (fun i =>
    if hi : i < max 1 (blockSize (tuning p)) then
      (1 / (p.L * p.R)) • g ((baseAlgorithm p).query state).2
        (ξ (call * max 1 (blockSize (tuning p)) + (⟨i, hi⟩ : Fin _).val)) else 0)

lemma baseStep_active (p : LongTails.Setups.AffineMomentConvex.Params)
    (ht : LongTails.Proofs.AffineMomentParameters.Valid (tuning p))
    (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (k : ℕ) (s : p.E × p.E)
    (hk : k < iterations (tuning p)) :
    baseStep p g ξ k (k, s) = (k + 1, blockAdvance (tuning p) k s (fun i =>
      LongTails.Proofs.AffineMomentNormalization.oracle p.L p.R p.x0 g
        (point (tuning p) k s) (ξ (blockSize (tuning p) * k + i)))) := by
  have hn : ¬ iterations (tuning p) ≤ k := Nat.not_le.mpr hk
  simp only [baseStep, baseAlgorithm, hn, ↓reduceIte]
  congr 1
  apply LongTails.Proofs.AffineMomentOracle.blockAdvance_congr
  intro i hi
  have hm : max 1 (blockSize (tuning p)) = blockSize (tuning p) := max_eq_right (blockSize_pos ht)
  simp only [hm, hi, ↓reduceDIte, LongTails.Proofs.AffineMomentNormalization.oracle]
  rw [Nat.mul_comm k]

lemma baseStep_done (p : LongTails.Setups.AffineMomentConvex.Params)
    (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (call : ℕ) (s : ℕ × (p.E × p.E))
    (hs : iterations (tuning p) ≤ s.1) : baseStep p g ξ call s = s := by
  exact base_update_done p s hs _

lemma advance_active (p : LongTails.Setups.AffineMomentConvex.Params)
    (ht : LongTails.Proofs.AffineMomentParameters.Valid (tuning p))
    (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (n k : ℕ)
    (hn : k + n ≤ iterations (tuning p)) :
    OracleTemplate.StochasticGradient.advance (baseStep p g ξ) n k
      (k, sampledIterate (tuning p)
        (LongTails.Proofs.AffineMomentNormalization.oracle p.L p.R p.x0 g) ξ k) =
      (k + n, sampledIterate (tuning p)
        (LongTails.Proofs.AffineMomentNormalization.oracle p.L p.R p.x0 g) ξ (k + n)) := by
  induction n generalizing k with
  | zero => simp [OracleTemplate.StochasticGradient.advance]
  | succ n ih =>
    rw [OracleTemplate.StochasticGradient.advance, baseStep_active p ht g ξ k _ (by omega)]
    change OracleTemplate.StochasticGradient.advance (baseStep p g ξ) n (k + 1)
      (k + 1, sampledIterate _ _ _ (k + 1)) = _
    rw [ih (k + 1) (by omega)]
    simp only [Nat.add_comm, Nat.add_left_comm]

lemma advance_done (p : LongTails.Setups.AffineMomentConvex.Params)
    (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (n k : ℕ) (s : ℕ × (p.E × p.E))
    (hs : iterations (tuning p) ≤ s.1) :
    OracleTemplate.StochasticGradient.advance (baseStep p g ξ) n k s = s := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [OracleTemplate.StochasticGradient.advance, baseStep_done p g ξ k s hs, ih]

lemma advance_final (p : LongTails.Setups.AffineMomentConvex.Params)
    (ht : LongTails.Proofs.AffineMomentParameters.Valid (tuning p))
    (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (n : ℕ)
    (hn : iterations (tuning p) ≤ n) :
    OracleTemplate.StochasticGradient.advance (baseStep p g ξ) n 0 (0, (0, 0)) =
      (iterations (tuning p), sampledIterate (tuning p)
        (LongTails.Proofs.AffineMomentNormalization.oracle p.L p.R p.x0 g) ξ (iterations (tuning p))) := by
  have he : n = iterations (tuning p) + (n - iterations (tuning p)) := by omega
  rw [he, OracleTemplate.HeavyTailedMarkovGradient.advance_add]
  have ha := advance_active p ht g ξ (iterations (tuning p)) 0 (by omega)
  simp only [Nat.zero_add, sampledIterate] at ha
  rw [ha]
  exact advance_done p g ξ _ _ _ (by rfl)

lemma execute_blocks (p : LongTails.Setups.AffineMomentConvex.Params)
    (ht : LongTails.Proofs.AffineMomentParameters.Valid (tuning p))
    (P : ProbabilityMeasure (ℕ → p.Ω)) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (n : ℕ) (hn : iterations (tuning p) ≤ n) :
    runOutput p { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) z => g x z }
      (n * max 1 (blockSize (tuning p))) ξ =
      p.x0 + p.R • (sampledIterate (tuning p)
        (LongTails.Proofs.AffineMomentNormalization.oracle p.L p.R p.x0 g) ξ (iterations (tuning p))).1 := by
  unfold runOutput algorithm
  erw [OracleTemplate.execute_batched]
  change (baseAlgorithm p).output
    (OracleTemplate.StochasticGradient.advance (baseStep p g ξ) n 0 (0, (0, 0))) = _
  erw [advance_final p ht g ξ n hn]
  rfl

lemma execute_calls (p : LongTails.Setups.AffineMomentConvex.Params)
    (ht : LongTails.Proofs.AffineMomentParameters.Valid (tuning p))
    (P : ProbabilityMeasure (ℕ → p.Ω)) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (N : ℕ) (hN : iterations (tuning p) * blockSize (tuning p) ≤ N) :
    runOutput p { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) z => g x z } N ξ =
      p.x0 + p.R • (sampledIterate (tuning p)
        (LongTails.Proofs.AffineMomentNormalization.oracle p.L p.R p.x0 g) ξ (iterations (tuning p))).1 := by
  let b := max 1 (blockSize (tuning p))
  have hb : 0 < b := by dsimp [b]; omega
  have he : N = N / b * b + N % b := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod N b).symm
  have hn : iterations (tuning p) ≤ N / b := by
    apply (Nat.le_div_iff_mul_le hb).mpr
    simpa only [b, max_eq_right (show 1 ≤ blockSize (tuning p) from blockSize_pos ht)] using hN
  conv_lhs => rw [he]
  unfold runOutput algorithm
  erw [OracleTemplate.FixedBatchConfidence.execute_batched_partial]
  · exact execute_blocks p ht P g ξ (N / b) hn
  · exact Nat.mod_lt N hb

end LongTails.Proofs.AffineMomentExecution
