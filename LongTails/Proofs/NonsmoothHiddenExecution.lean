import LongTails.Algorithms.NonsmoothHiddenAveraging
import LongTails.Proofs.AcceleratedMarkovExecution

namespace OracleTemplate.NonsmoothHidden

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma advance_local_block (oracle : E → Ω → E) (r D R : ℝ) (N K e : ℕ)
    (he : e < K) (ξ : ℕ → Ω) (m k call : ℕ) (hcount : k + (m + 1) = N) (b x z : E) :
    StochasticGradient.advance (fun j s => advance r D R N K s
      (oracle (averageQuery s.step s.average s.dual) (ξ j))) (m + 1) call ⟨e, k, b, x, z⟩ =
      let b' := restartOutside R (localRun oracle r D b (m + 1) k x z (fun i => ξ (call + i))).1
      ⟨e + 1, 0, b', b', b'⟩ := by
  induction m generalizing k call x z with
  | zero =>
    simp [StochasticGradient.advance, advance, he, hcount, localRun]
  | succ m ih =>
    have hnot : k + 1 ≠ N := by omega
    rw [StochasticGradient.advance]
    have hstep : advance r D R N K ⟨e, k, b, x, z⟩ (oracle (averageQuery k x z) (ξ call)) =
        ⟨e, k + 1, b, averageQuery k x z,
          LocalHiddenConvex.ballProj b (2 * r) (z - D⁻¹ • oracle (averageQuery k x z) (ξ call))⟩ := by
      simp only [advance, he, ite_true, hnot, ite_false]
    rw [hstep]
    rw [ih (k + 1) (call + 1) (by omega)]
    simp only [localRun, Fin.val_zero, Nat.add_zero, Fin.val_succ,
      Nat.add_comm, Nat.add_left_comm]

lemma advance_epochs (oracle : E → Ω → E) (r D R : ℝ) (N K : ℕ) (hN : 0 < N)
    (ξ : ℕ → Ω) (J e call : ℕ) (he : e + J ≤ K) (b : E) :
    StochasticGradient.advance (fun j s => advance r D R N K s
      (oracle (averageQuery s.step s.average s.dual) (ξ j))) (J * N) call ⟨e, 0, b, b, b⟩ =
      let b' := epochRun oracle r D R N J b (fun i => ξ (call + i))
      ⟨e + J, 0, b', b', b'⟩ := by
  induction J generalizing e call b with
  | zero => simp [StochasticGradient.advance, epochRun]
  | succ J ih =>
    rw [show (J + 1) * N = N + J * N by ring, HeavyTailedMarkovGradient.advance_add]
    have hn : N = (N - 1) + 1 := by omega
    have hblock := advance_local_block oracle r D R N K e (by omega) ξ (N - 1) 0 call
      (by omega) b b b
    rw [← hn] at hblock
    rw [hblock, ih (e + 1) (call + N) (by omega)]
    simp only [epochRun, localOutput]
    have ht : (fun i => ξ (call + N + i)) = (fun i => ξ (call + (N + i))) := by
      funext i
      congr 1
      omega
    rw [ht]
    congr 1
    omega

lemma advance_frozen (oracle : E → Ω → E) (r D R : ℝ) (N K : ℕ)
    (ξ : ℕ → Ω) (J call : ℕ) (s : State E) (hs : K ≤ s.epoch) :
    StochasticGradient.advance (fun j s => advance r D R N K s
      (oracle (averageQuery s.step s.average s.dual) (ξ j))) J call s = s := by
  induction J generalizing call with
  | zero => rfl
  | succ J ih =>
    rw [StochasticGradient.advance]
    simp only [advance, ite_eq_right (Nat.not_lt.mpr hs)]
    exact ih (call + 1)

lemma execute_epochRun [MeasurableSpace Ω] (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (oracle : E → Ω → E) (r D R : ℝ) (N K B : ℕ) (hN : 0 < N) (hB : K * N ≤ B)
    (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) seed => oracle x seed }
      (hiddenAveraging r D R N K) (fun _ => B) () ξ = epochRun oracle r D R N K 0 ξ := by
  erw [StochasticGradient.execute_advance]
  change (StochasticGradient.advance (fun j s => advance r D R N K s
    (oracle (averageQuery s.step s.average s.dual) (ξ j))) B 0 ⟨0, 0, 0, 0, 0⟩).center = _
  rw [show B = K * N + (B - K * N) by omega, HeavyTailedMarkovGradient.advance_add]
  rw [advance_epochs oracle r D R N K hN ξ K 0 0 (by omega)]
  simp only [Nat.zero_add]
  rw [advance_frozen oracle r D R N K ξ (B - K * N) (K * N) _ (by simp)]

end OracleTemplate.NonsmoothHidden
