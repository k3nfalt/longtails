import LongTails.Proofs.AffineMomentFailures

open LongTails.Algorithms.AffineMomentAccelerated
open LongTails.Proofs.AffineMomentParameters
open LongTails.Proofs.AffineMomentProcess
open LongTails.Proofs.AffineMomentFailures

namespace LongTails.Proofs.AffineMomentTrajectory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type*}

lemma sampledIterate_radius {t : Tuning} (ht : Valid t) (oracle : E → Ω → E) (ξ : ℕ → Ω) (k : ℕ) :
    ‖(sampledIterate t oracle ξ k).1‖ ≤ 4 ∧ ‖(sampledIterate t oracle ξ k).2‖ ≤ 1 := by
  induction k with
  | zero => simp [sampledIterate]
  | succ k ih =>
    exact LongTails.Proofs.AffineMomentCoupling.advance_radius ht k _ ih.1 ih.2 _ _

lemma next_pilot {t : Tuning} (g : E → E) (oracle : E → Ω → E)
    (k : ℕ) (s : E × E) (hk : k < iterations t) (hx : ‖s.1‖ ≤ 4) (hz : ‖s.2‖ ≤ 1)
    (ξ : Fin (sampleSize t) → Ω)
    (hh : ‖pilotEstimate t (OracleTemplate.RobustGeneralized.sampleReplies oracle (point t k s) ξ) -
      g (point t k s)‖ ≤ (‖g (point t k s)‖ + pilotRadius t) / 8) :
    next t g oracle (sampleSize t) (k, s, false, 0, false) ξ =
      (k, s, true, pilotEstimate t (OracleTemplate.RobustGeneralized.sampleReplies oracle (point t k s) ξ), false) := by
  simp [next, active, hk, hx, hz, hh]

lemma next_raw {t : Tuning} (g : E → E) (oracle : E → Ω → E)
    (k : ℕ) (s : E × E) (h : E) (hk : k < iterations t) (hx : ‖s.1‖ ≤ 4) (hz : ‖s.2‖ ≤ 1)
    (hh : ‖h - g (point t k s)‖ ≤ (‖g (point t k s)‖ + pilotRadius t) / 8) (ξ : Fin (sampleSize t) → Ω) :
    next t g oracle (sampleSize t) (k, s, true, h, false) ξ =
      (k + 1, advance t k s h (OracleTemplate.RobustGeneralized.meanBlock 0 (sampleSize t)
        (OracleTemplate.RobustGeneralized.sampleReplies oracle (point t k s) ξ)), false, 0, false) := by
  simp [next, active, hk, hx, hz, hh]

lemma trace_tail (t : Tuning) (g : E → E) (oracle : E → Ω → E)
    (s : ProofState E) (ξ : ℕ → Ω) (m : ℕ) :
    (OracleTemplate.StochasticGeneralized.blockTrace (fun _ => sampleSize t)
      (next t g oracle) s ξ m).2 = fun i => ξ (sampleSize t * m + i) := by
  funext i
  rw [OracleTemplate.StochasticGeneralized.blockTrace_tail]
  simp [OracleTemplate.StochasticGeneralized.blockCalls, Nat.mul_comm]

lemma trace_agreement {t : Tuning} (ht : Valid t) (g : E → E) (oracle : E → Ω → E)
    (ξ : ℕ → Ω) (m : ℕ)
    (hf : OracleTemplate.StochasticGeneralized.accumulated (fun _ => sampleSize t)
      (next t g oracle) (failure t g oracle) (2 * m) (0, (0, 0), false, 0, false) ξ < 1)
    (k : ℕ) (hkm : k ≤ m) (hkK : k ≤ iterations t) :
    (OracleTemplate.StochasticGeneralized.blockTrace (fun _ => sampleSize t)
      (next t g oracle) (0, (0, 0), false, 0, false) ξ (2 * k)).1 =
      (k, sampledIterate t oracle ξ k, false, 0, false) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkm' : k ≤ m := by omega
    have hkK' : k ≤ iterations t := by omega
    have hk : k < iterations t := by omega
    have hi := ih hkm' hkK'
    let s := sampledIterate t oracle ξ k
    let v := fun i => oracle (point t k s) (ξ (blockSize t * k + i))
    let a : Fin (sampleSize t) → Ω := fun i => ξ (sampleSize t * (2 * k) + i)
    let b : Fin (sampleSize t) → Ω := fun i => ξ (sampleSize t * (2 * k + 1) + i)
    have hr := sampledIterate_radius ht oracle ξ k
    have hz := failure_zero_of_accumulated_lt t g oracle (2 * m)
      (0, (0, 0), false, 0, false) ξ hf (2 * k) (by omega)
    dsimp only at hz
    rw [hi, trace_tail] at hz
    have hh := pilot_good_of_failure_zero t g oracle k s hk hr.1 hr.2 a hz
    have hp : pilotEstimate t (OracleTemplate.RobustGeneralized.sampleReplies oracle (point t k s) a) =
        pilotEstimate t v := by
      apply LongTails.Proofs.AffineMomentOracle.pilotEstimate_congr
      intro i hi
      simp only [OracleTemplate.RobustGeneralized.sampleReplies, hi, ↓reduceDIte, a, v, blockSize]
      congr 2
      ring
    have hb : OracleTemplate.RobustGeneralized.meanBlock 0 (sampleSize t)
        (OracleTemplate.RobustGeneralized.sampleReplies oracle (point t k s) b) =
        OracleTemplate.RobustGeneralized.meanBlock (sampleSize t) (sampleSize t) v := by
      unfold OracleTemplate.RobustGeneralized.meanBlock
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Nat.zero_add, OracleTemplate.RobustGeneralized.sampleReplies, Fin.isLt, ↓reduceDIte,
        b, v, blockSize]
      congr 2
      ring
    have h1 : (OracleTemplate.StochasticGeneralized.blockTrace (fun _ => sampleSize t)
        (next t g oracle) (0, (0, 0), false, 0, false) ξ (2 * k + 1)).1 =
        (k, s, true, pilotEstimate t v, false) := by
      rw [OracleTemplate.StochasticGeneralized.blockTrace_succ]
      change next t g oracle (sampleSize t) _ _ = _
      rw [hi, trace_tail]
      exact (next_pilot g oracle k s hk hr.1 hr.2 a hh).trans (by rw [hp])
    have hh' : ‖pilotEstimate t v - g (point t k s)‖ ≤ (‖g (point t k s)‖ + pilotRadius t) / 8 := by
      rwa [hp] at hh
    have hidx : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [hidx, OracleTemplate.StochasticGeneralized.blockTrace_succ]
    change next t g oracle (sampleSize t) _ _ = _
    rw [h1, trace_tail]
    rw [next_raw g oracle k s (pilotEstimate t v) hk hr.1 hr.2 hh' b, hb]
    rfl

end LongTails.Proofs.AffineMomentTrajectory
