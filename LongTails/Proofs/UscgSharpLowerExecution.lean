import LongTails.Proofs.UscgSharpLowerWitness
import LongTails.Proofs.UscgSharpExecution

namespace LongTails.Proofs.UscgSharpLowerExecution

open MeasureTheory
open OracleTemplate
open OracleTemplate.NormBallLMO
open LongTails.Setups.UscgHighProbability
open LongTails.Setups.UscgConstant (Space IsBallLMO dualNorm)
open LongTails.Algorithms.UscgSharpConfidence
open UscgSharpScalar UscgSharpScalarPath UscgSharpLowerWitness UscgSharpExecution

attribute [instance] Witness.measurableΩ Witness.probability

noncomputable abbrev publicParams (L σ Δ ε δ : ℝ) : Public where
  d := 1
  N := normSeminorm ℝ (Space 1)
  x₁ := 0
  L := L
  L₂ := L
  σ := σ
  Δ := Δ
  R := 1
  ζ := 1
  ε := ε
  δ := δ

noncomputable abbrev params {L σ Δ ε δ α η : ℝ} {T : ℕ} {lmo : Space 1 → Space 1}
    (W : Witness L σ Δ ε δ α η T lmo) : Params where
  toPublic := publicParams L σ Δ ε δ
  Ω := W.Ω

noncomputable abbrev stream {L σ Δ ε δ α η : ℝ} {T : ℕ} {lmo : Space 1 → Space 1}
    (W : Witness L σ Δ ε δ α η T lmo) : ProbabilityMeasure (ℕ → W.Ω) :=
  ⟨Measure.infinitePi (fun _ : ℕ => W.law), inferInstance⟩

lemma valid {L σ Δ ε δ α η : ℝ} {T : ℕ} {lmo : Space 1 → Space 1}
    (W : Witness L σ Δ ε δ α η T lmo)
    (hL : 0 < L) (hσ : 0 ≤ σ) (hΔ : 0 ≤ Δ) (he : 0 < ε) (hd : 0 < δ) (hd1 : δ < 1 / 2) :
    spec.valid (params W) := by
  refine ⟨?_, by norm_num [params, publicParams], ?_, by norm_num [params, publicParams], ?_,
    hL, hL.le, hσ, hΔ, he, hd, hd1⟩
  · intro x hx
    exact norm_eq_zero.mp hx
  · intro x hx
    exact hx
  · intro x
    simpa [params, publicParams] using dualNorm_le_norm
      (N := normSeminorm ℝ (Space 1)) (R := 1) (fun _ h => h) x

lemma admissible {L σ Δ ε δ α η : ℝ} {T : ℕ} {lmo : Space 1 → Space 1}
    (W : Witness L σ Δ ε δ α η T lmo)
    (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo) :
    spec.admissible (params W) (lift W.f)
      (canonicalOracle (publicParams L σ Δ ε δ) (oracle W.f' W.noise) lmo (stream W)) := by
  refine ⟨oracle W.f' W.noise, lmo, ⟨W.law, inferInstance⟩, stream W,
    OracleTemplate.StochasticGeneralized.infinitePi_iid W.law, rfl, hlmo, W.problem⟩

lemma average_execute {L σ Δ ε δ α η : ℝ} {T : ℕ} {lmo : Space 1 → Space 1}
    (W : Witness L σ Δ ε δ α η T lmo) (ξ : ℕ → W.Ω) :
    averageStationarity (publicParams L σ Δ ε δ) (lift W.f)
      (execute (canonicalOracle (publicParams L σ Δ ε δ) (oracle W.f' W.noise) lmo (stream W))
        (algorithm (publicParams L σ Δ ε δ) α η) (fun _ => T) () ξ) =
      (∑ t ∈ Finset.range T, dualNorm (normSeminorm ℝ (Space 1))
        (gradient (lift W.f) (trajectory α η W.f' W.noise lmo (fun k => ξ (2 * k)) t).1)) / T := by
  unfold algorithm
  rw [execute_machine]
  unfold averageStationarity
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  simp [storedTrajectory, Finset.mem_range.mp ht, publicParams, trajectory]

lemma not_successful {L σ Δ ε δ α η : ℝ} {T : ℕ} {lmo : Space 1 → Space 1}
    (W : Witness L σ Δ ε δ α η T lmo) (hT : 0 < T) (hd : 0 ≤ δ)
    (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo) :
    ¬ spec.successful (params W) (lift W.f)
      (fun seed : Unit × (ℕ → W.Ω) => execute
        (canonicalOracle (publicParams L σ Δ ε δ) (oracle W.f' W.noise) lmo (stream W))
        (algorithm (publicParams L σ Δ ε δ) α η) (fun _ => T) seed.1 seed.2)
      ⟨(Measure.dirac ()).prod (stream W : Measure _), inferInstance⟩ := by
  intro hs
  have hp := hs.2.2.2
  let F : Unit × (ℕ → W.Ω) → ℕ → W.Ω := fun seed k => seed.2 (2 * k)
  have hmap : MeasurePreserving F ((Measure.dirac ()).prod (stream W : Measure _))
      (Measure.infinitePi fun _ : ℕ => W.law) :=
    (even_stream_law (OracleTemplate.StochasticGeneralized.infinitePi_iid W.law)).comp measurePreserving_snd
  let S : (ℕ → W.Ω) → ℝ := fun ξ => ∑ t ∈ Finset.range T,
    dualNorm (normSeminorm ℝ (Space 1)) (gradient (lift W.f) (trajectory α η W.f' W.noise lmo ξ t).1)
  have hstep : Measurable (fun z : Space 1 × Space 1 => z.1 + η • lmo z.2) :=
    measurable_fst.add ((hlmo.measurable.comp measurable_snd).const_smul η)
  have hS : Measurable S := by
    apply Finset.measurable_sum
    intro t _
    have hx := (measurable_path (step := fun x m : Space 1 => x + η • lmo m)
      hstep (correctedWeight α) 0 W.problem.measurable t).fst
    have hdual := (continuous_dualNorm (N := normSeminorm ℝ (Space 1)) (R := 1)
      (fun _ h => h) (by norm_num)).measurable
    exact hdual.comp ((measurable_gradient_space (lift W.f)).comp hx)
  have hset : MeasurableSet {ξ | ε * T < S ξ} := measurableSet_lt measurable_const hS
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have hEq : {seed : Unit × (ℕ → W.Ω) | ε < averageStationarity (publicParams L σ Δ ε δ) (lift W.f)
      (execute (canonicalOracle (publicParams L σ Δ ε δ) (oracle W.f' W.noise) lmo (stream W))
        (algorithm (publicParams L σ Δ ε δ) α η) (fun _ => T) seed.1 seed.2)} =
      F ⁻¹' {ξ | ε * T < S ξ} := by
    ext ⟨⟨⟩, ξ⟩
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [average_execute W ξ, lt_div_iff₀ hTp]
  change ((Measure.dirac ()).prod (stream W : Measure (ℕ → W.Ω))) _ ≤ ENNReal.ofReal δ at hp
  rw [hEq, hmap.measure_preimage hset.nullMeasurableSet] at hp
  have hr := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal δ ≠ ⊤) hp
  rw [ENNReal.toReal_ofReal hd] at hr
  exact (not_le_of_gt W.failure) hr

end LongTails.Proofs.UscgSharpLowerExecution
