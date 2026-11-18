import LongTails.Proofs.DistributedNormalizedCausality
import LongTails.Proofs.DistributedSampling
import LongTails.Proofs.HeavyTailedTapeExecution

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.DistributedNormalizedBlocks

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedDownlink

abbrev WorkerDraws (p : Params) := Fin p.n → ℕ → Fin p.d × ℝ
abbrev RoundBlock (p : Params) (cfg : Config) :=
  (Fin p.n → Fin cfg.batch → p.Ω) × (WorkerDraws p × WorkerDraws p)

lemma transpose_streams_preserving {X : Type*} [MeasurableSpace X] (n : ℕ)
    (μ : Fin n → Measure X) [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (fun ξ : Fin n → ℕ → X => fun k i => ξ i k)
      (Measure.pi fun i : Fin n => Measure.infinitePi fun _ : ℕ => μ i)
      (Measure.infinitePi fun _ : ℕ => Measure.pi μ) := by
  have h₁ : MeasurePreserving (MeasurableEquiv.curry (Fin n) ℕ X).symm
      (Measure.pi fun i : Fin n => Measure.infinitePi fun _ : ℕ => μ i)
      (Measure.infinitePi fun v : Fin n × ℕ => μ v.1) := by
    refine ⟨(MeasurableEquiv.curry (Fin n) ℕ X).symm.measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry_symm (fun i (_ : ℕ) => μ i)
  have h₂ : MeasurePreserving (fun ξ : Fin n × ℕ → X => fun v : ℕ × Fin n => ξ v.swap)
      (Measure.infinitePi fun v : Fin n × ℕ => μ v.1)
      (Measure.infinitePi fun v : ℕ × Fin n => μ v.2) := by
    refine ⟨Measurable.of_eval fun v => measurable_pi_apply v.swap, ?_⟩
    exact Measure.map_infinitePi_infinitePi_of_inj
      (P := fun v : Fin n × ℕ => μ v.1) (f := fun v : ℕ × Fin n => v.swap) Prod.swap_injective
  have h₃ : MeasurePreserving (MeasurableEquiv.curry ℕ (Fin n) X)
      (Measure.infinitePi fun v : ℕ × Fin n => μ v.2)
      (Measure.infinitePi fun _ : ℕ => Measure.pi μ) := by
    refine ⟨(MeasurableEquiv.curry ℕ (Fin n) X).measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry (fun (_ : ℕ) i => μ i)
  exact h₃.comp (h₂.comp h₁)

noncomputable def workerDrawsLaw (p : Params) [Nonempty (Fin p.d)] :
    ProbabilityMeasure (WorkerDraws p) :=
  ⟨Measure.pi fun _ : Fin p.n => Measure.infinitePi
    (fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))), inferInstance⟩

lemma worker_stream_law (p : Params) [Nonempty (Fin p.d)] (i : Fin p.n) :
    MeasurePreserving (fun θ : WorkerDraws p => θ i)
      (workerDrawsLaw p : Measure (WorkerDraws p))
      (Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))) :=
  measurePreserving_eval (μ := fun _ : Fin p.n =>
    Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))) i

noncomputable def roundLaw (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) : ProbabilityMeasure (RoundBlock p cfg) :=
  ⟨(Measure.pi fun i : Fin p.n => Measure.pi fun _ : Fin cfg.batch => (μ i : Measure p.Ω)).prod
    ((workerDrawsLaw p : Measure (WorkerDraws p)).prod
      (workerDrawsLaw p : Measure (WorkerDraws p))), inferInstance⟩

lemma round_samples_law (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) :
    (roundLaw p cfg μ : Measure (RoundBlock p cfg)).map Prod.fst =
      Measure.pi (fun i : Fin p.n => Measure.pi fun _ : Fin cfg.batch => (μ i : Measure p.Ω)) := by
  simp only [roundLaw, ProbabilityMeasure.coe_mk, Measure.map_fst_prod, measure_univ, one_smul]

lemma round_up_law (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) :
    (roundLaw p cfg μ : Measure (RoundBlock p cfg)).map (fun z => z.2.1) =
      (workerDrawsLaw p : Measure (WorkerDraws p)) := by
  change (roundLaw p cfg μ : Measure (RoundBlock p cfg)).map (Prod.fst ∘ Prod.snd) = _
  rw [← Measure.map_map measurable_fst measurable_snd]
  simp only [roundLaw, ProbabilityMeasure.coe_mk, Measure.map_snd_prod, Measure.map_fst_prod,
    measure_univ, one_smul]

lemma round_down_law (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) :
    (roundLaw p cfg μ : Measure (RoundBlock p cfg)).map (fun z => z.2.2) =
      (workerDrawsLaw p : Measure (WorkerDraws p)) := by
  change (roundLaw p cfg μ : Measure (RoundBlock p cfg)).map (Prod.snd ∘ Prod.snd) = _
  rw [← Measure.map_map measurable_snd measurable_snd]
  simp only [roundLaw, ProbabilityMeasure.coe_mk, Measure.map_snd_prod, measure_univ, one_smul]

def extractedSamples (p : Params) (cfg : Config)
    (ξ : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) :
    ℕ → Fin p.n → Fin cfg.batch → p.Ω := fun k i j => ξ i (k * cfg.batch + j.val)

def extractedDraws (p : Params) (D : Draws p) : ℕ → WorkerDraws p × WorkerDraws p :=
  fun k => (D (2 * k), D (2 * k + 1))

lemma extracted_samples_preserving (p : Params) (cfg : Config)
    (P : Measure (LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams))
    (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hworkers : iIndepFun (fun i (ξ : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) => ξ i) P)
    (hIID : ∀ i, LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) => ξ i k) (μ i : Measure p.Ω) P) :
    MeasurePreserving (extractedSamples p cfg) P
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun i : Fin p.n =>
        Measure.pi fun _ : Fin cfg.batch => (μ i : Measure p.Ω)) := by
  rw [DistributedSampling.joint_stream_law p.toParams P μ hworkers hIID]
  have hb (i : Fin p.n) := OracleTemplate.FiniteVariance.infinite_block_law
    (μ i : Measure p.Ω) (Measure.infinitePi fun _ : ℕ => (μ i : Measure p.Ω))
    (iIndepFun_infinitePi (P := fun _ : ℕ => (μ i : Measure p.Ω))
      (X := fun _ => id) (fun _ => measurable_id))
    (fun k => Measure.infinitePi_map_eval (fun _ : ℕ => (μ i : Measure p.Ω)) k) cfg.batch
  have hp := measurePreserving_pi
    (fun i : Fin p.n => Measure.infinitePi fun _ : ℕ => (μ i : Measure p.Ω))
    (fun i : Fin p.n => Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin cfg.batch => (μ i : Measure p.Ω)) hb
  exact (transpose_streams_preserving (p.n : ℕ)
    (fun i : Fin p.n => Measure.pi fun _ : Fin cfg.batch => (μ i : Measure p.Ω))).comp hp

lemma extracted_draws_preserving (p : Params) [Nonempty (Fin p.d)] :
    MeasurePreserving (extractedDraws p) (drawsLaw p : Measure (Draws p))
      (Measure.infinitePi fun _ : ℕ => (workerDrawsLaw p : Measure (WorkerDraws p)).prod
        (workerDrawsLaw p : Measure (WorkerDraws p))) := by
  have h := OracleTemplate.FiniteVariance.paired_stream_law
    (workerDrawsLaw p : Measure (WorkerDraws p)) (drawsLaw p : Measure (Draws p))
    (iIndepFun_infinitePi (P := fun _ : ℕ => (workerDrawsLaw p : Measure (WorkerDraws p)))
      (X := fun _ => id) (fun _ => measurable_id))
    (fun k => Measure.infinitePi_map_eval (fun _ : ℕ => (workerDrawsLaw p : Measure (WorkerDraws p))) k)
  unfold extractedDraws
  simpa only [Nat.mul_comm] using h

def extractedMaster (p : Params) (cfg : Config)
    (z : Draws p × LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) :
    ℕ → RoundBlock p cfg := fun k => (extractedSamples p cfg z.2 k, extractedDraws p z.1 k)

lemma extracted_master_preserving (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (P : Measure (LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams))
    [IsProbabilityMeasure P] (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hworkers : iIndepFun (fun i (ξ : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) => ξ i) P)
    (hIID : ∀ i, LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) => ξ i k) (μ i : Measure p.Ω) P) :
    MeasurePreserving (extractedMaster p cfg) ((drawsLaw p : Measure (Draws p)).prod P)
      (Measure.infinitePi fun _ : ℕ => (roundLaw p cfg μ : Measure (RoundBlock p cfg))) := by
  let B := Measure.pi fun i : Fin p.n => Measure.pi fun _ : Fin cfg.batch => (μ i : Measure p.Ω)
  let U := (workerDrawsLaw p : Measure (WorkerDraws p)).prod
    (workerDrawsLaw p : Measure (WorkerDraws p))
  have hp := (extracted_draws_preserving p).prod (extracted_samples_preserving p cfg P μ hworkers hIID)
  have hs := Measure.measurePreserving_swap (μ := Measure.infinitePi fun _ : ℕ => U)
    (ν := Measure.infinitePi fun _ : ℕ => B)
  exact (HeavyTailedTapeExecution.zip_streams_preserving B U).comp (hs.comp hp)

lemma seed_master_preserving (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (P : Measure (LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams))
    [IsProbabilityMeasure P] (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hworkers : iIndepFun (fun i (ξ : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) => ξ i) P)
    (hIID : ∀ i, LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) => ξ i k) (μ i : Measure p.Ω) P) :
    MeasurePreserving
      (fun z : Seed p cfg × LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams =>
        (z.1.1, extractedMaster p cfg (z.1.2, z.2)))
      ((seedLaw p cfg : Measure (Seed p cfg)).prod P)
      ((PMF.uniformOfFintype (Fin cfg.iterations)).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => (roundLaw p cfg μ : Measure (RoundBlock p cfg)))) := by
  exact ((MeasurePreserving.id (PMF.uniformOfFintype (Fin cfg.iterations)).toMeasure).prod
    (extracted_master_preserving p cfg P μ hworkers hIID)).comp
    (measurePreserving_prodAssoc (PMF.uniformOfFintype (Fin cfg.iterations)).toMeasure
      (drawsLaw p : Measure (Draws p)) P)

def assembledDraws (p : Params) (cfg : Config) (ξ : ℕ → RoundBlock p cfg) : Draws p :=
  fun t => if t % 2 = 0 then (ξ (t / 2)).2.1 else (ξ (t / 2)).2.2

def assembledSamples (p : Params) (cfg : Config) (ξ : ℕ → RoundBlock p cfg) :
    LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams :=
  fun i j => (ξ (j / cfg.batch)).1 i ⟨j % cfg.batch, Nat.mod_lt _ cfg.batch.pos⟩

lemma assembled_extracted_draws (p : Params) (cfg : Config)
    (z : Draws p × LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) :
    assembledDraws p cfg (extractedMaster p cfg z) = z.1 := by
  funext t
  unfold assembledDraws extractedMaster extractedDraws
  dsimp only
  split_ifs with h
  · have he : 2 * (t / 2) = t := by omega
    rw [he]
  · have he : 2 * (t / 2) + 1 = t := by omega
    rw [he]

lemma assembled_extracted_samples (p : Params) (cfg : Config)
    (z : Draws p × LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) :
    assembledSamples p cfg (extractedMaster p cfg z) = z.2 := by
  funext i j
  unfold assembledSamples extractedMaster extractedSamples
  dsimp only
  rw [Nat.mul_comm (j / cfg.batch), Nat.div_add_mod]

lemma measurable_assembledDraws (p : Params) (cfg : Config) :
    Measurable (assembledDraws p cfg) := by
  apply Measurable.of_eval
  intro t
  unfold assembledDraws
  split_ifs
  · exact measurable_fst.comp (measurable_snd.comp (measurable_pi_apply (t / 2)))
  · exact measurable_snd.comp (measurable_snd.comp (measurable_pi_apply (t / 2)))

lemma measurable_assembledSamples (p : Params) (cfg : Config) :
    Measurable (assembledSamples p cfg) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact (measurable_pi_apply (⟨j % cfg.batch, Nat.mod_lt _ cfg.batch.pos⟩ : Fin cfg.batch)).comp
    ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_pi_apply (j / cfg.batch))))

lemma assembled_trajectory_prefix (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (ξ ζ : ℕ → RoundBlock p cfg) (k : ℕ) (h : ∀ j, j < k → ξ j = ζ j) :
    trajectory p cfg (assembledDraws p cfg ξ) g (assembledSamples p cfg ξ) k =
      trajectory p cfg (assembledDraws p cfg ζ) g (assembledSamples p cfg ζ) k := by
  apply DistributedNormalizedCausality.trajectory_prefix
  · intro t ht
    have hd : t / 2 < k := by omega
    simp only [assembledDraws, h _ hd]
  · intro i j hj
    have hd : j / (cfg.batch : ℕ) < k := (Nat.div_lt_iff_lt_mul cfg.batch.pos).mpr hj
    simp only [assembledSamples, h _ hd]

lemma assembled_draws_even (p : Params) (cfg : Config) (ξ : ℕ → RoundBlock p cfg) (k : ℕ) :
    assembledDraws p cfg ξ (2 * k) = (ξ k).2.1 := by
  simp [assembledDraws]

lemma assembled_draws_odd (p : Params) (cfg : Config) (ξ : ℕ → RoundBlock p cfg) (k : ℕ) :
    assembledDraws p cfg ξ (2 * k + 1) = (ξ k).2.2 := by
  have hd : (2 * k + 1) / 2 = k := by omega
  have hm : (2 * k + 1) % 2 = 1 := by omega
  simp only [assembledDraws, hd, hm, one_ne_zero, ↓reduceIte]

lemma assembled_sample (p : Params) (cfg : Config) (ξ : ℕ → RoundBlock p cfg)
    (k : ℕ) (i : Fin p.n) (j : Fin cfg.batch) :
    assembledSamples p cfg ξ i (k * cfg.batch + j.val) = (ξ k).1 i j := by
  have hd : (k * (cfg.batch : ℕ) + j.val) / cfg.batch = k := by
    rw [Nat.mul_comm k, Nat.mul_add_div cfg.batch.pos, Nat.div_eq_of_lt j.isLt, add_zero]
  have hm : (k * (cfg.batch : ℕ) + j.val) % cfg.batch = j.val := by
    rw [Nat.mul_comm k, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
  simp only [assembledSamples, hd]
  exact congrArg ((ξ k).1 i) (Fin.ext hm)

lemma assembled_next_local (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (ξ : ℕ → RoundBlock p cfg)
    (k : ℕ) (s : Iterate p) :
    next p cfg (assembledDraws p cfg ξ) g (assembledSamples p cfg ξ) k s =
      next p cfg (assembledDraws p cfg (fun _ => ξ k)) g
        (assembledSamples p cfg (fun _ => ξ k)) k s := by
  apply DistributedNormalizedCausality.next_congr
  · rw [assembled_draws_even, assembled_draws_even]
  · rw [assembled_draws_odd, assembled_draws_odd]
  · intro i j hj
    have h₁ := assembled_sample p cfg ξ k i (⟨j, hj⟩ : Fin cfg.batch)
    have h₂ := assembled_sample p cfg (fun _ => ξ k) k i (⟨j, hj⟩ : Fin cfg.batch)
    exact h₁.trans h₂.symm

lemma assembled_trajectory_step (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (ξ : ℕ → RoundBlock p cfg) (k : ℕ) :
    trajectory p cfg (assembledDraws p cfg ξ) g (assembledSamples p cfg ξ) (k + 1) =
      next p cfg (assembledDraws p cfg (fun _ => ξ k)) g
        (assembledSamples p cfg (fun _ => ξ k)) k
        (trajectory p cfg (assembledDraws p cfg ξ) g (assembledSamples p cfg ξ) k) := by
  rw [trajectory, assembled_next_local]

end LongTails.Proofs.DistributedNormalizedBlocks
