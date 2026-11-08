import LongTails.Proofs.BirchCollectionMoments
import LongTails.Proofs.BirchCollectionLegality
import LongTails.Proofs.BirchNonEuclideanComposition

namespace LongTails.Proofs.BirchCollectionSuccess

open Finset MeasureTheory OracleTemplate
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollections
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchCollectionOrdering
open LongTails.Proofs.BirchCollectionReplay
open LongTails.Proofs.BirchCollectionEvaluation
open LongTails.Proofs.BirchCollectionBlocks
open LongTails.Proofs.BirchCollectionTrajectory
open LongTails.Proofs.BirchCollectionMoments
open LongTails.Setups.UscgConstant (dualNorm IsBallLMO)

lemma calls_bound (p : Params) (he : ValidFrom p.workers {} p.events)
    (K B : ℕ) (hs : Structural (compiled p).trace p.ordering p.controls K B) :
    (program p).oracleCalls ≤ p.controls.initialization + p.controls.waste +
      ⌈(B : ℝ) * p.controls.amplification * ((K : ℝ) * p.controls.upperMass)⌉₊ := by
  let s := (compiled p).trace
  have hraw : RawLedger s := by
    simpa only [s, compiled, compile_trace] using rawLedger_run p.workers p.events he
  have hc : CompletedLedger s := by
    simpa only [s, compiled, compile_trace] using completedLedger_run p.workers p.events he
  have hledger := ordering_raw_ledger s p.ordering K hraw hc hs.1
  have hwaste := hs.2.2.2.2.2.2.2.2.1
  change s.nextRaw - ((range p.ordering.labels.length).biUnion (p.ordering.raw s)).card ≤
    p.controls.waste at hwaste
  have hJ : 0 ≤ (B : ℝ) * p.controls.amplification :=
    mul_nonneg (Nat.cast_nonneg _) hs.2.1.2.2.2.2.le
  have hsum : (∑ n ∈ range p.ordering.labels.length, ((p.ordering.raw s n).card : ℝ)) ≤
      (p.controls.initialization : ℝ) +
        (B : ℝ) * p.controls.amplification * ((K : ℝ) * p.controls.upperMass) := by
    have hpoint (n : ℕ) (hn : n ∈ range p.ordering.labels.length) :
        ((p.ordering.raw s n).card : ℝ) ≤
          (if n = 0 then (p.controls.initialization : ℝ) else 0) +
            ((B : ℝ) * p.controls.amplification) * p.ordering.movement s n := by
      rcases hs.2.2.2.2.2.2.2.1 n (mem_range.mp hn) with h | h
      · obtain ⟨rfl, h0, hcard⟩ := h
        change p.ordering.movement s 0 = 0 at h0
        simpa [h0] using (show ((p.ordering.raw s 0).card : ℝ) ≤
          p.controls.initialization from by exact_mod_cast hcard)
      · exact h.trans (le_add_of_nonneg_left (by split <;> positivity))
    calc
      _ ≤ _ := sum_le_sum hpoint
      _ ≤ _ := by
        rw [sum_add_distrib, ← mul_sum]
        have hinit : (∑ n ∈ range p.ordering.labels.length,
            if n = 0 then (p.controls.initialization : ℝ) else 0) ≤ p.controls.initialization := by
          simp [mem_range.mpr hs.1.1]
        exact add_le_add hinit (mul_le_mul_of_nonneg_left (total_mass_bound s _ _ K B hs) hJ)
  have hsumNat : (∑ n ∈ range p.ordering.labels.length, (p.ordering.raw s n).card) ≤
      p.controls.initialization + ⌈(B : ℝ) * p.controls.amplification *
        ((K : ℝ) * p.controls.upperMass)⌉₊ := by
    exact_mod_cast hsum.trans (add_le_add le_rfl (Nat.le_ceil _))
  have hcalls : (program p).oracleCalls = s.nextRaw := by
    rw [program_calls]
    simpa only [s, compiled, compile_trace] using (run_raw p.events).symm
  rw [hcalls, hledger]
  omega

lemma tuned_energy (p : Params) (hp : spec.valid p) :
    (6 * p.Δ / (1 / (20 * p.L))) / p.controls.lowerMass +
      (16 / p.controls.lowerMass) *
        (p.κ * p.σ ^ 2 / batchSize p * ((horizon p : ℝ) * p.controls.upperMass)) ≤
      p.ε * horizon p := by
  rcases hp with ⟨_, _, hL, _, hε, _, _, ⟨w⟩, _, hs⟩
  have hκ : 0 ≤ p.κ := le_trans zero_le_one (w.smoothness_lower.trans w.smoothness_upper)
  obtain ⟨hh, _, _, hratio, _⟩ := hs.2.1
  have hB : (0 : ℝ) < batchSize p := by
    exact_mod_cast (show 0 < batchSize p by unfold batchSize; omega)
  have hK : (0 : ℝ) ≤ horizon p := Nat.cast_nonneg _
  have hceilK : 240 * p.L * p.Δ / (p.controls.lowerMass * p.ε) ≤ (horizon p : ℝ) := by
    unfold horizon
    rw [Nat.cast_add, Nat.cast_one]
    exact (Nat.le_ceil _).trans (by linarith)
  have hceilB : 32 * p.controls.massRatio * p.κ * p.σ ^ 2 / p.ε ≤ (batchSize p : ℝ) := by
    unfold batchSize
    rw [Nat.cast_add, Nat.cast_one]
    exact (Nat.le_ceil _).trans (by linarith)
  have ha : (6 * p.Δ / (1 / (20 * p.L))) / p.controls.lowerMass ≤ p.ε * horizon p / 2 := by
    have hhK := (div_le_iff₀ (mul_pos hh hε)).mp hceilK
    have hconst : 6 * p.Δ / (1 / (20 * p.L)) = 6 * p.Δ * (20 * p.L) := by
      field_simp
    rw [hconst]
    exact (div_le_iff₀ hh).mpr (by nlinarith only [hhK])
  have hb : 16 * p.κ * p.σ ^ 2 * p.controls.massRatio / batchSize p ≤ p.ε / 2 := by
    have hhB := (div_le_iff₀ hε).mp hceilB
    exact (div_le_iff₀ hB).mpr (by nlinarith only [hhB])
  have hratio' : p.controls.upperMass / p.controls.lowerMass ≤ p.controls.massRatio :=
    (div_le_iff₀ hh).mpr hratio
  have hn : 0 ≤ 16 * p.κ * p.σ ^ 2 / (batchSize p : ℝ) * horizon p := by positivity
  have hb' : (16 / p.controls.lowerMass) *
      (p.κ * p.σ ^ 2 / batchSize p * ((horizon p : ℝ) * p.controls.upperMass)) ≤
        p.ε * horizon p / 2 := by
    calc
      _ = (16 * p.κ * p.σ ^ 2 / (batchSize p : ℝ) * horizon p) *
          (p.controls.upperMass / p.controls.lowerMass) := by ring
      _ ≤ (16 * p.κ * p.σ ^ 2 / (batchSize p : ℝ) * horizon p) * p.controls.massRatio :=
        mul_le_mul_of_nonneg_left hratio' hn
      _ = (16 * p.κ * p.σ ^ 2 * p.controls.massRatio / (batchSize p : ℝ)) * horizon p := by ring
      _ ≤ (p.ε / 2) * horizon p := mul_le_mul_of_nonneg_right hb hK
      _ = _ := by ring
  linarith

lemma execute_calls (p : Params) (O : Oracle (Point p.d) (Point p.d)) (Q : ℕ)
    (seed : (algorithm p).Seed) (samples : (k : ℕ) → O.Seed k) :
    (executeWithTrace O (algorithm p) (fun _ => Q) seed samples).2.length = Q := by
  erw [executeWithTrace_eq_executeIndexedState]
  exact executeIndexedState_length O (algorithm p) seed samples Q

lemma execute_success (p : Params) (hp : spec.valid p) (Q : ℕ)
    (hQ : (program p).oracleCalls ≤ Q)
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d)) (hI : spec.admissible p I O) :
    spec.successful p I (fun z : (algorithm p).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm p) (fun _ => Q) z.1 z.2)
      ⟨((algorithm p).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  rcases hI with ⟨hf, Ω, m, horacle⟩
  let := m
  rcases horacle with ⟨μ, P, g, hiid, hg, rfl⟩
  have hbound := tuned_energy p hp
  rcases hp with ⟨hdef, hcont, hL, _, _, _, _, ⟨w⟩, he, hs⟩
  obtain ⟨R, hRpos, hRbound⟩ :=
    LongTails.Proofs.BirchLmoExistence.exists_norm_le_seminorm p.N hdef hcont
  have hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R := fun v hv => (hRbound v).trans (by nlinarith)
  let lmo := LongTails.Algorithms.BirchNonEuclideanFramework.chosenLMO (native p)
  have hlmo : IsBallLMO p.N 1 lmo :=
    LongTails.Proofs.BirchNonEuclideanComposition.native_chosenLMO_valid (native p) hdef hcont
  let F := fun k (ξ : ℕ → Ω) =>
    dualNorm p.N (gradient I.f (mainPoint p lmo (fun j x => g x (ξ j)) k)) ^ 2
  have hs' : Structural (compiled p).trace p.ordering p.controls (horizon p) (batchSize p) := by
    simpa only [compiled, compile_trace] using hs
  have hB : 0 < batchSize p := by unfold batchSize; omega
  have hK : 0 < horizon p := by unfold horizon; omega
  have hcount : (program p).outputCount + 1 = horizon p := by
    change horizon p - 1 + 1 = horizon p
    omega
  have hm := LongTails.Proofs.BirchNonEuclideanCausality.interpret_prefix_measurable
    (native p) lmo hlmo.measurable hR hRpos.le g hg.measurable (program p).instructions
  have hmain (k : ℕ) : Measurable (fun ξ : ℕ → Ω =>
      mainPoint p lmo (fun j x => g x (ξ j)) k) := hm.1 _
  have hfm (k : ℕ) : Measurable (F k) :=
    ((OracleTemplate.NormBallLMO.continuous_dualNorm hR hRpos.le).measurable.comp
      ((OracleTemplate.NormBallLMO.measurable_gradient_space I.f).comp (hmain k))).pow_const 2
  have henergy := expected_energy p he (horizon p) (batchSize p) hs' hB lmo hlmo I hf μ P hiid g hg
    w hR hRpos.le hdef hL
  have hfi (k : ℕ) (hk : k < horizon p) : Integrable (F k) (P : Measure (ℕ → Ω)) := by
    apply henergy.1.mono' (hfm k).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact single_le_sum (fun j _ => sq_nonneg
      (dualNorm p.N (gradient I.f (mainPoint p lmo (fun i x => g x (ξ i)) j))))
      (mem_range.mpr hk)
  have hu := LongTails.Proofs.BirchNonEuclideanCertificate.uniform_integral (program p).outputCount P
    (fun j => F j.val) (fun j => hfi j.val (hcount ▸ j.isLt))
  have hsum : (∑ j : Fin ((program p).outputCount + 1), ∫ ξ, F j.val ξ ∂(P : Measure (ℕ → Ω))) =
      ∫ ξ, ∑ k ∈ range (horizon p), F k ξ ∂(P : Measure (ℕ → Ω)) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => ∫ ξ, F j ξ ∂(P : Measure (ℕ → Ω))), hcount,
      integral_finsetSum _ (fun k hk => hfi k (mem_range.mp hk))]
  have ha : (1 / (((program p).outputCount + 1 : ℕ) : ℝ)) *
      (∑ j : Fin ((program p).outputCount + 1), ∫ ξ, F j.val ξ ∂(P : Measure (ℕ → Ω))) ≤ p.ε := by
    rw [hsum, hcount]
    have hkR : (0 : ℝ) < horizon p := Nat.cast_pos.mpr hK
    rw [one_div, ← div_eq_inv_mul]
    exact (div_le_iff₀ hkR).mpr (henergy.2.trans hbound)
  have hx (j : Fin ((program p).outputCount + 1)) (ξ : ℕ → Ω) :
      execute (OracleTemplate.BirchSgd.gradientOracle (d := (native p).d) P g) (algorithm p)
        (fun _ => Q) j ξ = mainPoint p lmo (fun i x => g x (ξ i)) j.val := by
    change execute (OracleTemplate.BirchSgd.gradientOracle (d := (native p).d) P g)
      (LongTails.Setups.BirchNonEuclidean.programAlgorithm (native p) (program p) lmo)
        (fun _ => Q) j ξ = _
    rw [show Q = (program p).oracleCalls + (Q - (program p).oracleCalls) by omega]
    exact (LongTails.Proofs.BirchNonEuclideanExecution.execute_surplus
      (native p) (program p) lmo P g ξ j (Q - (program p).oracleCalls)).trans
        (LongTails.Proofs.BirchNonEuclideanExecution.execute_interpret (native p) (program p)
          lmo P g ξ j)
  let μout := (PMF.uniformOfFintype (Fin ((program p).outputCount + 1))).toMeasure.prod
    (P : Measure (ℕ → Ω))
  let out := fun z : Fin ((program p).outputCount + 1) × (ℕ → Ω) =>
    execute (OracleTemplate.BirchSgd.gradientOracle (d := (native p).d) P g)
      (algorithm p) (fun _ => Q) z.1 z.2
  have hfun : out = fun z => mainPoint p lmo (fun i x => g x (z.2 i)) z.1.val := by
    funext z
    exact hx z.1 z.2
  change Measurable out ∧
    Integrable (fun z => dualNorm p.N (gradient I.f (out z)) ^ 2) μout ∧
      (∫ z, dualNorm p.N (gradient I.f (out z)) ^ 2 ∂μout) ≤ p.ε
  rw [hfun]
  exact ⟨measurable_from_prod_countable_right (fun j => hmain j.val), hu.1, hu.2.le.trans ha⟩

end LongTails.Proofs.BirchCollectionSuccess
