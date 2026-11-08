import LongTails.Proofs.BirchNonEuclideanPhysicalReplay
import Mathlib.Probability.Independence.InfinitePi

namespace LongTails.Proofs.BirchNonEuclideanPhysicalSuccess

open MeasureTheory ProbabilityTheory
open OracleTemplate.Rennala (Point Instance)
open OracleTemplate
open LongTails.Setups.BirchNonEuclidean
open LongTails.Setups.UscgConstant (dualNorm IsBallLMO)
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Algorithms.BirchNonEuclideanEvents
open LongTails.Proofs.BirchNonEuclideanExecution
open LongTails.Proofs.BirchNonEuclideanEventLabels
open LongTails.Proofs.BirchNonEuclideanPhysicalReplay
open LongTails.Proofs.BirchNonEuclideanPhysicalCertificate
open LongTails.Proofs.BirchNonEuclideanEventCosts
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanDeltaCertificate

lemma iid_reindex_preserving {Ω : Type} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (index : ℕ → ℕ) (hinj : Function.Injective index) :
    MeasurePreserving (fun ξ k => ξ (index k)) (P : Measure (ℕ → Ω)) (P : Measure (ℕ → Ω)) := by
  have hre := iid_reindex hiid index hinj
  have hp := hiid.independent.map_fun_eq_infinitePi_map hiid.measurable
  have hr := hre.independent.map_fun_eq_infinitePi_map hre.measurable
  simp only [hiid.marginal] at hp
  simp only [hre.marginal] at hr
  have hp' : (P : Measure (ℕ → Ω)) = Measure.infinitePi (fun _ : ℕ => (μ : Measure Ω)) := by
    change Measure.map id (P : Measure (ℕ → Ω)) = _ at hp
    simpa only [Measure.map_id] using hp
  exact ⟨by fun_prop, hr.trans hp'.symm⟩

lemma successful_comp {Ξ : Type} [MeasurableSpace Ξ] (p : Params) (I : Instance p.d)
    (P : ProbabilityMeasure Ξ) (output : Ξ → Point p.d) (T : Ξ → Ξ)
    (hT : MeasurePreserving T (P : Measure Ξ) (P : Measure Ξ))
    (hs : spec.successful p I output P) : spec.successful p I (output ∘ T) P := by
  rcases hs with ⟨hm, hi, hb⟩
  refine ⟨hm.comp hT.measurable, hT.integrable_comp_of_integrable hi, ?_⟩
  have ha : AEStronglyMeasurable (fun z => dualNorm p.N (gradient I.f (output z)) ^ 2)
      ((P : Measure Ξ).map T) := by rw [hT.map_eq]; exact hi.aestronglyMeasurable
  have he := integral_map hT.measurable.aemeasurable ha
  rw [hT.map_eq] at he
  exact he.symm.le.trans hb

lemma completeTrace_execute {Ω : Type} [MeasurableSpace Ω] {m : ℕ}
    (p : Params) (lmo : Point p.d → Point p.d) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d) (η : ℝ) (B H K : ℕ)
    (events : List (Event m)) (word : ℕ → Fin m)
    (ht : (canonicalTuning η B).Valid) (hK : 0 < K) (hm : 0 < m)
    (he : CompleteTrace H K B word events) (j : Fin (K - 1 + 1)) (ξ : ℕ → Ω) :
    let t := canonicalTuning η B
    let perm := completeTrace_labels_perm H K B word events hK hm he
    let a := eventsProgram H K B events t
    let b := (makeTemplate K (physicalLocalCode H K B word)).instantiate t
    execute (OracleTemplate.BirchSgd.gradientOracle P g) (programAlgorithm p a lmo)
        (fun _ => a.oracleCalls) j ξ =
      execute (OracleTemplate.BirchSgd.gradientOracle P g) (programAlgorithm p b lmo)
        (fun _ => b.oracleCalls) j (fun i => ξ (labelIndex perm i)) := by
  let a := eventsProgram H K B events (canonicalTuning η B)
  let b := (makeTemplate K (physicalLocalCode H K B word)).instantiate (canonicalTuning η B)
  let perm := completeTrace_labels_perm H K B word events hK hm he
  exact (execute_interpret p a lmo P g ξ j).trans
    ((congrFun (completeTrace_replay p lmo (fun i x => g x (ξ i)) η B H K events word ht hK hm he) j.val).trans
      (execute_interpret p b lmo P g (fun i => ξ (labelIndex perm i)) j).symm)

lemma completeTrace_success {Ω : Type} [MeasurableSpace Ω] {m : ℕ}
    (p : Params) (I : Instance p.d) (lmo : Point p.d → Point p.d)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (g : Point p.d → Ω → Point p.d) (η : ℝ) (B H K : ℕ)
    (events : List (Event m)) (word : ℕ → Fin m)
    (ht : (canonicalTuning η B).Valid) (hK : 0 < K) (hm : 0 < m)
    (he : CompleteTrace H K B word events)
    (hs : let b := (makeTemplate K (physicalLocalCode H K B word)).instantiate (canonicalTuning η B)
      spec.successful p I
        (fun z : Fin (K - 1 + 1) × (ℕ → Ω) => execute (OracleTemplate.BirchSgd.gradientOracle P g)
          (programAlgorithm p b lmo) (fun _ => b.oracleCalls) z.1 z.2)
        ⟨(PMF.uniformOfFintype (Fin (K - 1 + 1))).toMeasure.prod (P : Measure (ℕ → Ω)), inferInstance⟩) :
    let a := eventsProgram H K B events (canonicalTuning η B)
    spec.successful p I
      (fun z : Fin (K - 1 + 1) × (ℕ → Ω) => execute (OracleTemplate.BirchSgd.gradientOracle P g)
        (programAlgorithm p a lmo) (fun _ => a.oracleCalls) z.1 z.2)
      ⟨(PMF.uniformOfFintype (Fin (K - 1 + 1))).toMeasure.prod (P : Measure (ℕ → Ω)), inferInstance⟩ := by
  let perm := completeTrace_labels_perm H K B word events hK hm he
  have hmp := iid_reindex_preserving μ P hiid (labelIndex perm) (labelIndex_injective perm)
  have hp := (MeasurePreserving.id (PMF.uniformOfFintype (Fin (K - 1 + 1))).toMeasure).prod hmp
  have hh := successful_comp p I _ _ _ hp hs
  dsimp only at hh ⊢
  simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq,
    ← completeTrace_execute p lmo P g η B H K events word ht hK hm he] using hh

lemma physical_execute_success {Ω : Type} [MeasurableSpace Ω] {m : ℕ}
    (p : Params) (I : Instance p.d) (ho : Objective p I) (lmo : Point p.d → Point p.d)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (g : Point p.d → Ω → Point p.d) (hg : StochasticGradient p (μ : Measure Ω) I.f g)
    (w : DualRegularityWitness p.N p.κ) (R : ℝ)
    (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R) (hdef : ∀ x, p.N x = 0 → x = 0)
    (hlmo : IsBallLMO p.N 1 lmo) (hL : 0 ≤ p.L)
    (η : ℝ) (B H K : ℕ) (events : List (Event m)) (word : ℕ → Fin m)
    (hη : 0 < η) (hK : 0 < K) (hm : 0 < m) (hH : 0 < H) (hB : 8 * H ≤ B)
    (he : CompleteTrace H K B word events)
    (hstep : η * p.L ≤ 1 / 2) (hsmall : η * p.L * (2 + 3 * (B : ℝ) / H) ≤ 1 / 4)
    (hbound : 6 * p.Δ / (η * K) + 16 * p.κ * p.σ ^ 2 / B ≤ p.ε) :
    let a := eventsProgram H K B events (canonicalTuning η B)
    let Q := B + H * (K + (finalSchedule H K B word).rejected.length + (m - 1))
    a.oracleCalls = Q ∧
      spec.successful p I
        (fun z : Fin (K - 1 + 1) × (ℕ → Ω) => execute (OracleTemplate.BirchSgd.gradientOracle P g)
          (programAlgorithm p a lmo) (fun _ => Q) z.1 z.2)
        ⟨(PMF.uniformOfFintype (Fin (K - 1 + 1))).toMeasure.prod (P : Measure (ℕ → Ω)), inferInstance⟩ := by
  have ht := canonical_valid η B hη.le (by omega : 0 < B)
  obtain ⟨c⟩ := physicalLocalFamily_certificate H K B (fun _ _ => word) η hK hm hH hB hη
  have hc := LongTails.Proofs.BirchNonEuclideanCertificate.certificate_execute_success
    p _ lmo c I ho μ P hiid g hg w hR hR0 hdef hlmo hL hη (by positivity) hstep hsmall
    (by simpa only [mul_one_div] using hbound)
  have hs := completeTrace_success p I lmo μ P hiid g η B H K events word ht hK hm he hc
  have hq : (eventsProgram H K B events (canonicalTuning η B)).oracleCalls =
      B + H * (K + (finalSchedule H K B word).rejected.length + (m - 1)) := by
    rw [LongTails.Proofs.BirchNonEuclideanEvents.eventsProgram_calls,
      completeTrace_query_count H K B word events hK hm he]
  refine ⟨hq, ?_⟩
  simpa only [hq] using hs

lemma physical_tuning_conditions (L Δ κ σ ε : ℝ) (H : ℕ)
    (hL : 0 < L) (hε : 0 < ε) (hH : 0 < H) :
    let B := 8 * H + ⌈64 * κ * σ ^ 2 / ε⌉₊
    let η := 1 / (12 * L * (1 + (B : ℝ) / H))
    let K := 1 + ⌈144 * L * Δ * (1 + (B : ℝ) / H) / ε⌉₊
    8 * H ≤ B ∧ 0 < η ∧ 0 < K ∧ η * L ≤ 1 / 2 ∧
      η * L * (2 + 3 * (B : ℝ) / H) ≤ 1 / 4 ∧
      6 * Δ / (η * K) + 16 * κ * σ ^ 2 / B ≤ ε := by
  let B := 8 * H + ⌈64 * κ * σ ^ 2 / ε⌉₊
  let u := 1 + (B : ℝ) / H
  let η := 1 / (12 * L * u)
  let K := 1 + ⌈144 * L * Δ * u / ε⌉₊
  have hB : 8 * H ≤ B := by dsimp [B]; omega
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hu : 0 < u := by dsimp [u]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hK : 0 < K := by dsimp [K]; omega
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hηL : η * L = 1 / (12 * u) := by dsimp [η]; field_simp
  have hnoise : 16 * κ * σ ^ 2 / B ≤ ε / 4 := by
    have hb : 64 * κ * σ ^ 2 / ε ≤ (B : ℝ) := by
      have hc := Nat.le_ceil (64 * κ * σ ^ 2 / ε)
      dsimp [B]
      push_cast
      exact hc.trans (le_add_of_nonneg_left (by positivity))
    have hc := (div_le_iff₀ hε).mp hb
    apply (div_le_iff₀ hB0).mpr
    nlinarith
  have hgap : 6 * Δ / (η * K) ≤ ε / 2 := by
    have hb : 144 * L * Δ * u ≤ ε * K := by
      have hc := Nat.le_ceil (144 * L * Δ * u / ε)
      have hk : 144 * L * Δ * u / ε ≤ (K : ℝ) := by
        dsimp [K]
        push_cast
        exact hc.trans (le_add_of_nonneg_left (by norm_num))
      exact (div_le_iff₀ hε).mp hk |>.trans_eq (mul_comm _ _)
    have he : 6 * Δ / (η * K) = 72 * L * Δ * u / K := by
      dsimp [η]
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ hK0).mpr
    nlinarith
  refine ⟨hB, hη, hK, ?_, ?_, by linarith⟩
  · change η * L ≤ 1 / 2
    rw [hηL]
    apply (div_le_iff₀ (by positivity)).mpr
    have hu1 : 1 ≤ u := le_add_of_nonneg_right (by positivity)
    linarith
  · change η * L * (2 + 3 * (B : ℝ) / H) ≤ 1 / 4
    rw [hηL, div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ (by positivity)).mpr
    dsimp [u]
    ring_nf
    norm_num

end LongTails.Proofs.BirchNonEuclideanPhysicalSuccess
