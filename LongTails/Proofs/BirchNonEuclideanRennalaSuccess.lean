import LongTails.Proofs.BirchNonEuclideanRennalaCertificate
import LongTails.Algorithms.BirchNonEuclideanRennalaProtocols
import LongTails.Proofs.BirchNonEuclideanBatchCertificate
import LongTails.Proofs.BirchNonEuclideanCertificate

namespace LongTails.Proofs.BirchNonEuclideanRennalaSuccess

open MeasureTheory ProbabilityTheory
open OracleTemplate.Rennala (Point Instance)
open OracleTemplate
open LongTails.Setups.BirchNonEuclidean hiding State LegalFrom
open LongTails.Setups.UscgConstant (dualNorm IsBallLMO)
open LongTails.Algorithms.BirchNonEuclideanRennala
open LongTails.Algorithms.BirchNonEuclideanRennalaProtocols
open LongTails.Proofs.BirchNonEuclideanRennalaScheduling
open LongTails.Proofs.BirchNonEuclideanRennalaCosts
open LongTails.Proofs.BirchNonEuclideanRennalaLegality
open LongTails.Proofs.BirchNonEuclideanRennalaCertificate
open LongTails.Proofs.BirchNonEuclideanDeltaCertificate (canonical_valid)

lemma publicFamily_structural {m : ℕ} (p : Params) (events : ℕ → ℕ → List (Event m))
    (he : ∀ K B, 0 < K → 0 < B → CompleteTrace K B (events K B))
    (hw : p.workers = m + 1) (hp : p.protocol = publicFamily events)
    (hc : p.profile = LongTails.Algorithms.BirchNonEuclideanProfiles.minibatchProfile)
    (hq : p.callCount = publicCalls events) : Structural p := by
  intro K B hK hB η hη
  rw [hc] at hB
  have hB0 : 0 < B := hB
  have ht := canonical_valid η B hη.le hB0
  have htrace := he K B hK hB0
  rw [hp, hc, hq, hw]
  refine ⟨eventsProgram_legal K B _ ht (events K B) htrace.1,
    eventsProgram_calls K B (events K B) _, ?_⟩
  simpa only [LongTails.Algorithms.BirchNonEuclideanProfiles.minibatchProfile,
    zero_mul, zero_add, zero_div, add_zero, publicFamily, ProtocolFamily.instantiate, eventsProgram] using
      Nonempty.intro (completeTraceCertificate K B η ht (events K B) hK hB0 htrace)

lemma execute_success {Ω : Type} [MeasurableSpace Ω] {m : ℕ}
    (p : Params) (I : Instance p.d) (ho : Objective p I) (lmo : Point p.d → Point p.d)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (g : Point p.d → Ω → Point p.d) (hg : StochasticGradient p (μ : Measure Ω) I.f g)
    (w : DualRegularityWitness p.N p.κ) (R : ℝ)
    (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R) (hdef : ∀ x, p.N x = 0 → x = 0)
    (hlmo : IsBallLMO p.N 1 lmo) (hL : 0 ≤ p.L)
    (η : ℝ) (B K : ℕ) (events : List (Event m))
    (hη : 0 < η) (hK : 0 < K) (hm : 0 < m) (hB : 0 < B)
    (he : CompleteTrace K B events) (hstep : η * p.L ≤ 1 / 2)
    (hbound : 6 * p.Δ / (η * K) + 16 * p.κ * p.σ ^ 2 / B ≤ p.ε) :
    let a := eventsProgram K B events (canonicalTuning η B)
    let Q := K * B + (run K B events).stale.length + (m - 1)
    a.outputCount + 1 = K ∧ a.oracleCalls = Q ∧ Q ≤ K * (B + m - 1) ∧
      spec.successful p I
        (fun z : Fin (a.outputCount + 1) × (ℕ → Ω) => execute (OracleTemplate.BirchSgd.gradientOracle P g)
          (programAlgorithm p a lmo) (fun _ => Q) z.1 z.2)
        ⟨(PMF.uniformOfFintype (Fin (a.outputCount + 1))).toMeasure.prod (P : Measure (ℕ → Ω)), inferInstance⟩ := by
  have ht := canonical_valid η B hη.le hB
  let c := completeTraceCertificate K B η ht events hK hB he
  have hs := LongTails.Proofs.BirchNonEuclideanCertificate.certificate_execute_success
    p _ lmo c I ho μ P hiid g hg w hR hR0 hdef hlmo hL hη (by norm_num)
    hstep (by norm_num) (by simpa only [mul_one_div] using hbound)
  have hcost := completeTrace_calls K B events (canonicalTuning η B) hK hB he
  have hcostBound := completeTrace_calls_bound K B events (canonicalTuning η B) hm hK hB he
  refine ⟨(eventsProgram_output K B events _ hK).1, hcost, ?_, ?_⟩
  · rw [← hcost]
    exact hcostBound
  · simpa only [hcost] using hs

lemma tuning_conditions (L Δ κ σ ε : ℝ) (hL : 0 < L) (hε : 0 < ε) :
    let B := 1 + ⌈64 * κ * σ ^ 2 / ε⌉₊
    let η := 1 / (4 * L)
    let K := 1 + ⌈48 * L * Δ / ε⌉₊
    0 < B ∧ 0 < η ∧ 0 < K ∧ η * L ≤ 1 / 2 ∧
      6 * Δ / (η * K) + 16 * κ * σ ^ 2 / B ≤ ε := by
  let B := 1 + ⌈64 * κ * σ ^ 2 / ε⌉₊
  let η := 1 / (4 * L)
  let K := 1 + ⌈48 * L * Δ / ε⌉₊
  have hB : (0 : ℝ) < B := by dsimp [B]; positivity
  have hK : (0 : ℝ) < K := by dsimp [K]; positivity
  have hnoise : 16 * κ * σ ^ 2 / B ≤ ε / 4 := by
    have hb : 64 * κ * σ ^ 2 / ε ≤ (B : ℝ) := by
      have hc := Nat.le_ceil (64 * κ * σ ^ 2 / ε)
      dsimp [B]
      push_cast
      linarith
    have hc := (div_le_iff₀ hε).mp hb
    apply (div_le_iff₀ hB).mpr
    nlinarith
  have hgap : 6 * Δ / (η * K) ≤ ε / 2 := by
    have hk : 48 * L * Δ / ε ≤ (K : ℝ) := by
      have hc := Nat.le_ceil (48 * L * Δ / ε)
      dsimp [K]
      push_cast
      linarith
    have hc := (div_le_iff₀ hε).mp hk
    have he : 6 * Δ / (η * K) = 24 * L * Δ / K := by
      dsimp [η]
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ hK).mpr
    nlinarith
  refine ⟨by omega, by positivity, by omega, ?_, by linarith⟩
  have he : η * L = 1 / 4 := by dsimp [η]; field_simp
  rw [he]
  norm_num

lemma tuned_call_bound {m : ℕ} (L Δ κ σ ε : ℝ) (events : List (Event m)) (hm : 0 < m)
    (he : CompleteTrace (1 + ⌈48 * L * Δ / ε⌉₊) (1 + ⌈64 * κ * σ ^ 2 / ε⌉₊) events) :
    (eventsProgram (1 + ⌈48 * L * Δ / ε⌉₊) (1 + ⌈64 * κ * σ ^ 2 / ε⌉₊)
      events (canonicalTuning (1 / (4 * L)) (1 + ⌈64 * κ * σ ^ 2 / ε⌉₊))).oracleCalls ≤
      (1 + ⌈48 * L * Δ / ε⌉₊) * (m + ⌈64 * κ * σ ^ 2 / ε⌉₊) := by
  have hh := completeTrace_calls_bound _ _ events (canonicalTuning (1 / (4 * L)) (1 + ⌈64 * κ * σ ^ 2 / ε⌉₊)) hm (by omega) (by omega) he
  have hc : 1 + ⌈64 * κ * σ ^ 2 / ε⌉₊ + m - 1 = m + ⌈64 * κ * σ ^ 2 / ε⌉₊ := by omega
  simpa only [hc] using hh

end LongTails.Proofs.BirchNonEuclideanRennalaSuccess
