import LongTails.Proofs.BirchCausalTuning
import LongTails.Proofs.BirchNonEuclideanCertificate

namespace LongTails.Proofs.BirchCausalSuccess

open MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Setups.UscgConstant (IsBallLMO)
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Algorithms.BirchCausalPackets
open LongTails.Algorithms.BirchCausalTuning
open LongTails.Proofs.BirchCausalTuning
open LongTails.Proofs.BirchCausalPhysicalCertificate
open LongTails.Proofs.BirchNonEuclideanExecution

lemma constructed_execute_success {Ω : Type} [MeasurableSpace Ω] {m : ℕ}
    (p : Params) (H : ℕ) (word : ℕ → ℕ → ℕ → Fin m) (recipe : ℕ → ℕ → Packet m → PacketExpr)
    (hH : 0 < H) (hm : 0 < m) (hw : 0 < p.workers) (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε)
    (hp : ∀ K B job, (recipe K B job).Valid p.workers) (hc : ∀ K B job, (recipe K B job).calls = H)
    (I : Instance p.d) (ho : Objective p I) (lmo : Point p.d → Point p.d)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (g : Point p.d → Ω → Point p.d) (hg : StochasticGradient p (μ : Measure Ω) I.f g)
    (w : DualRegularityWitness p.N p.κ) (R : ℝ)
    (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R) (hdef : ∀ x, p.N x = 0 → x = 0)
    (hlmo : IsBallLMO p.N 1 lmo) :
    let a := program p H word recipe
    let Q := ⌈(5 + 528 * (p.L * p.Δ / p.ε)) * ((m : ℝ) * H) + (32 + 1920 * (p.L * p.Δ / p.ε)) * (p.κ * p.σ ^ 2 / p.ε)⌉₊
    a.Legal p.workers ∧ a.oracleCalls ≤ Q ∧
      spec.successful p I (output p H word recipe lmo P g Q)
        ⟨(PMF.uniformOfFintype (Fin (a.outputCount + 1))).toMeasure.prod (P : Measure (ℕ → Ω)), inferInstance⟩ := by
  let B := batchSize H p.κ p.σ p.ε
  let K := horizon H B p.L p.Δ p.ε
  let η := stepSize H B p.L
  let a := program p H word recipe
  let Q := ⌈(5 + 528 * (p.L * p.Δ / p.ε)) * ((m : ℝ) * H) + (32 + 1920 * (p.L * p.Δ / p.ε)) * (p.κ * p.σ ^ 2 / p.ε)⌉₊
  have hκ : 0 ≤ p.κ := (show (0 : ℝ) ≤ 1 by norm_num).trans (w.smoothness_lower.trans w.smoothness_upper)
  have hb := batch_minimum H p.κ p.σ p.ε
  have hB : 0 < B := by dsimp only [B]; omega
  have hk := horizon_positive H B p.L p.Δ p.ε
  have hs := step_conditions H B p.L hH hL
  have ht := tuning_valid H B p.L hH hB hL
  obtain ⟨hlegal, hcalls, ⟨cert⟩⟩ := physicalGraph_certificate p.workers H K B (word K B) (recipe K B) η
    hw hH hk hs.1.ne' ht (by dsimp only [B]; omega) (minimum_batch H B hb) (hp K B) (hc K B)
  change a.oracleCalls = B + H * (K + (ignored (finalSchedule H K B (word K B))).length) at hcalls
  have hbudget : a.oracleCalls ≤ Q := by
    rw [hcalls]
    exact tuned_calls_nat H p.L p.Δ p.κ p.σ p.ε word hH hm hL hΔ hκ hε
  have hcert : ProgramCertificate a K η (drift H B) (1 / (B : ℝ)) := by
    rw [drift_certificate H B hH] at cert
    exact cert
  have hsuccess := LongTails.Proofs.BirchNonEuclideanCertificate.certificate_execute_success
    p a lmo hcert I ho μ P hiid g hg w hR hR0 hdef hlmo hL.le hs.1
    (le_trans (by norm_num : (0 : ℝ) ≤ 2) (drift_lower H B hH)) hs.2.1 hs.2.2.le
    (accuracy_bound H p.L p.Δ p.κ p.σ p.ε hH hL hΔ hε)
  refine ⟨hlegal, hbudget, ?_⟩
  have he : Q = a.oracleCalls + (Q - a.oracleCalls) := (Nat.add_sub_of_le hbudget).symm
  have hout : output p H word recipe lmo P g Q =
      fun z : Fin (a.outputCount + 1) × (ℕ → Ω) =>
        OracleTemplate.execute (OracleTemplate.BirchSgd.gradientOracle P g)
          (programAlgorithm p a lmo) (fun _ => a.oracleCalls) z.1 z.2 := by
    funext z
    change OracleTemplate.execute (OracleTemplate.BirchSgd.gradientOracle P g) (programAlgorithm p a lmo) (fun _ => Q) z.1 z.2 = _
    rw [he]
    exact execute_surplus p a lmo P g z.2 z.1 _
  rw [hout]
  exact hsuccess

end LongTails.Proofs.BirchCausalSuccess
