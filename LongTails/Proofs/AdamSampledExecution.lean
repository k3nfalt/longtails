import LongTails.Proofs.AdamMatrixProcess
import LongTails.Proofs.BatchedDirectionExecution

namespace LongTails.Proofs.AdamSampledExecution

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar
open LongTails.Setups.SpectralSmoothAdamComparison LongTails.Setups.BatchedSpectralSmooth
open LongTails.Proofs.AdamMatrixGeometry LongTails.Proofs.AdamScalarProcess
open LongTails.Proofs.AdamSeparationModel LongTails.Proofs.AdamMatrixProcess

noncomputable def streamNoise (s : ℝ) (B : ℕ) (ξ : ℕ → Bool) (t : ℕ) : ℝ :=
  AdamRademacher.batchNoise s B (fun j => ξ (B * t + j.val))

lemma sample_batch {r B : ℕ} (hB : 0 < B) (f : Space r r → ℝ) (s : ℝ)
    (X : Space r r) (ξ : ℕ → Bool) (t : ℕ) :
    (1 / (B : ℝ)) • (∑ j ∈ Finset.range B, sample f s X (ξ (B * t + j))) =
      gradient f X + streamNoise s B ξ t • denseProjection r := by
  simp only [sample, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    ← Nat.cast_smul_eq_nsmul ℝ, ← Finset.sum_smul, ← Finset.mul_sum, smul_add, smul_smul]
  have hB' : (B : ℝ) ≠ 0 := by positivity
  rw [show (1 / (B : ℝ)) * B = 1 by field_simp, one_smul]
  congr 1
  unfold streamNoise AdamRademacher.batchNoise
  rw [Fin.sum_univ_eq_sum_range (fun j => sign (ξ (B * t + j))) B]
  congr 1
  ring

lemma batch_matches {r B T : ℕ} (hr : 1 < r) (hB : 0 < B)
    (a : AdamTuning) (ℓ c w D s : ℝ) (hw : 0 < w) (x0 : Space r r)
    (ξ : ℕ → Bool) (reply : ℕ → Space r r)
    (hreply : ∀ t ≤ T, ∀ j < B, reply (B * t + j) =
      sample (AdamSeparationInstance.objective ℓ c w D x0) s
        (adamIterate a B x0 reply t) (ξ (B * t + j))) :
    ∀ t ≤ T, batchMean B reply t =
      mixedProjection r (ℓ * (trajectory a r ℓ c w D (streamNoise s B ξ) t).stiff + streamNoise s B ξ t)
        (quietGradient c w D (trajectory a r ℓ c w D (streamNoise s B ξ) t)) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    have hiter := iterate_matches (show 0 < r by omega) a ℓ c w D (streamNoise s B ξ) reply x0
      (fun j hj => ih j hj (by omega))
    unfold batchMean
    have hs : (∑ j ∈ Finset.range B, reply (B * t + j)) =
        ∑ j ∈ Finset.range B, sample (AdamSeparationInstance.objective ℓ c w D x0) s
          (adamIterate a B x0 reply t) (ξ (B * t + j)) := by
      exact Finset.sum_congr rfl (fun j hj => hreply t ht j (Finset.mem_range.mp hj))
    rw [hs, sample_batch hB, hiter, AdamSeparationInstance.gradient_objective hr _ _ _ hw,
      AdamSeparationInstance.stiffCoord_mixed (by omega), AdamSeparationInstance.quietCoord_mixed hr]
    unfold mixedProjection quietGradient
    module

open LongTails.Proofs.BatchedDirectionExecution

lemma execute_eq_trajectory {r B T : ℕ} (hr : 1 < r) (hB : 0 < B)
    (a : AdamTuning) (ℓ c w D s : ℝ) (hw : 0 < w) (x0 : Space r r)
    {A : Algorithm (Space r r) (Space r r) (Space r r)} (draw : A.Seed → Fin (T + 1))
    (hA : ∀ seed reply,
      let state := LongTails.Setups.FiniteVarianceSpectralSmooth.replyState A seed reply
      (∀ t j, t ≤ T → j < B →
        (A.query (state (B * t + j))).2 = adamIterate a B x0 reply t) ∧
      ∀ extra, A.output (state (B * (T + 1) + extra)) = adamIterate a B x0 reply (draw seed))
    (seed : A.Seed) (ξ : ℕ → Bool) :
    execute { Seed := fun _ => Bool, law := signStream, answer := fun _ (_, X) ω => sample (AdamSeparationInstance.objective ℓ c w D x0) s X ω }
      A (fun _ => B * (T + 1)) seed ξ =
      x0 + mixedProjection r
        (trajectory a r ℓ c w D (streamNoise s B ξ) (draw seed)).stiff
        (trajectory a r ℓ c w D (streamNoise s B ξ) (draw seed)).quiet := by
  let g := sample (AdamSeparationInstance.objective ℓ c w D x0) s
  rw [StochasticGradient.execute_advance]
  have hadv := advance_stateSeq A seed g ξ (B * (T + 1)) 0
  rw [Nat.zero_add] at hadv
  change A.output (StochasticGradient.advance _ _ 0 (stateSeq A seed g ξ 0)) = _
  rw [hadv]
  let reply := fun i => g (A.query (stateSeq A seed g ξ i)).2 (ξ i)
  have hrep : ∀ k, LongTails.Setups.FiniteVarianceSpectralSmooth.replyState A seed reply k =
      stateSeq A seed g ξ k := replyState_stateSeq A seed g ξ
  obtain ⟨hq, hout⟩ := hA seed reply
  simp only [hrep] at hq hout
  have hout0 := hout 0
  rw [Nat.add_zero] at hout0
  rw [hout0]
  apply iterate_matches (by omega) a ℓ c w D (streamNoise s B ξ) reply x0
  intro j hj
  apply batch_matches (T := T) hr hB a ℓ c w D s hw x0 ξ reply _ j (by omega)
  intro t ht k hk
  exact congrArg (fun X => g X (ξ (B * t + k))) (hq t k ht hk)

end LongTails.Proofs.AdamSampledExecution
