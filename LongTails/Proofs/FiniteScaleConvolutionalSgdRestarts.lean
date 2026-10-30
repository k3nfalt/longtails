import LongTails.Proofs.FiniteScaleConvolutionalSgdExecution

open Classical MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.FiniteScaleConvolutionalSgdRestarts

open ManySampleConvolutionalPerceptronDynamics (State)
open FiniteScaleConvolutionalSgdProcess
open FiniteScaleConvolutionalSgdStopping
open FiniteScaleConvolutionalSgdProbability

lemma noSeparation_history_iff {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nonempty ι] (K δ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (samples : ℕ → ι) (T B : ℕ) (hT : T ≤ B) :
    NoSeparation K δ c p r start (historyStream (fun j : Fin B => samples j)) T ↔
      NoSeparation K δ c p r start samples T := by
  have he (k : ℕ) (hk : k ≤ T) :
      trajectory K δ c p r start (historyStream (fun j : Fin B => samples j)) k =
        trajectory K δ c p r start samples k := by
    apply trajectory_congr
    intro j hj
    have hjB : j < B := hj.trans_le (hk.trans hT)
    simp only [historyStream, dite_eq_left hjB]
  constructor <;> intro h k hk
  · rw [← he k hk]
    exact h k hk
  · rw [he k hk]
    exact h k hk

lemma repeated_failure_bound {E Ω ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ι)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ
      (PMF.uniformOfFintype ι).toMeasure P)
    (K δ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (T B M : ℕ) (hT : T ≤ B) (q : ENNReal)
    (hblock : ∀ j, P {ω | NoSeparation K δ c p r start (fun k => ξ (j * B + k) ω) T} ≤ q) :
    P {ω | ∀ j < M, NoSeparation K δ c p r start (fun k => ξ (j * B + k) ω) T} ≤ q ^ M := by
  let S : Set (Fin B → ι) := {z | NoSeparation K δ c p r start (historyStream z) T}
  have hS (ω : Ω) (j : ℕ) : (fun i : Fin B => ξ (j * B + i) ω) ∈ S ↔
      NoSeparation K δ c p r start (fun k => ξ (j * B + k) ω) T :=
    noSeparation_history_iff K δ c p r start (fun k => ξ (j * B + k) ω) T B hT
  have hh := independent_blocks_failure P ξ hξ.measurable hξ.independent B M S q (fun j => by
    simpa only [hS] using hblock j)
  simpa only [hS] using hh

open OracleTemplate
open LongTails.Setups.FiniteScaleConvolutionalSgd
open LongTails.Algorithms.FiniteScaleConvolutionalSgd
open FiniteScaleConvolutionalSgdGeometry
open FiniteScaleConvolutionalSgdExecution
open FiniteScaleConvolutionalSgdTuning
open ManySampleConvolutionalPerceptronGeometry (plusFeature minusFeature)

lemma state_failure_probability (p : Params) (hp : spec.valid p) (data : Data p.input)
    (G : Geometry p.input data) (M calls : ℕ)
    (hcost : (period p.input : ℕ) * ((p.input.count : ℕ) + 1) * M ≤ calls) :
    (p.input.sampling.law : Measure _) {ω | ¬Separates p.input data
      (stateAt p.input data (stepSize p.input) (scale p.input) (period p.input) ω calls).point} ≤
        ENNReal.ofReal (1 / 4) ^ M := by
  obtain ⟨hη, hε, _, _⟩ := parameter_bounds p hp
  have hs := (initial_conditions p hp).1
  rcases hp with ⟨hd, hg, hgR, hμ, hκ, hκ₁, ha, htlo, hthi, hδ₁, hsmall, hfail, hfail₁, hξ⟩
  have hp : spec.valid p := ⟨hd, hg, hgR, hμ, hκ, hκ₁, ha, htlo, hthi, hδ₁, hsmall, hfail, hfail₁, hξ⟩
  let q := p.input
  let η := stepSize q
  let s := scale q
  let B := (period q : ℕ)
  let T := runSteps q
  let K := s ^ 2 / η
  let δ := perturbation q
  let c := fun i => η * G.background i
  let u := fun i => plusFeature (G.defect i)
  let r := fun i => minusFeature (G.defect i)
  let x := initialState q s (η * q.contrast)
  have hblock (j : ℕ) : (q.sampling.law : Measure _) {ω |
      NoSeparation K δ c u r x (fun k => q.sampling.sample (j * B + k) ω) T} ≤
        ENNReal.ofReal (1 / 4) := by
    exact normalized_failure p hp data G (fun k => q.sampling.sample (j * B + k))
      (iid_shift q.sampling.law _ q.sampling.sample hξ (j * B))
  have hT : T < B := Nat.lt_succ_self _
  have hprob := repeated_failure_bound p.input.sampling.law p.input.sampling.sample hξ
    K δ c u r x T B M hT.le (ENNReal.ofReal (1 / 4)) hblock
  apply le_trans (measure_mono ?_) hprob
  intro ω hω
  apply output_failure_blocks q data G η s (period q) hη hs.ne' hε.ne' hd ω T M calls hT
  · convert hcost using 1
    ring
  · exact hω

lemma execution_failure_probability (p : Params) (hp : spec.valid p) (data : Data p.input)
    (G : Geometry p.input data) (O : Oracle (Query p.input) (Reply p.input.dimension))
    (hO : ∀ history query seed, O.answer history query seed = answer p.input data query.2)
    (M calls : ℕ) (hcost : (period p.input : ℕ) * ((p.input.count : ℕ) + 1) * M ≤ calls) :
    ((p.input.sampling.law : Measure _).prod (O.law : Measure _))
      {ω | ¬Separates p.input data (tunedOutput p.input O calls ω.1 ω.2)} ≤
        ENNReal.ofReal (1 / 4) ^ M := by
  have he (ω : p.input.sampling.Ω × ((k : ℕ) → O.Seed k)) :
      tunedOutput p.input O calls ω.1 ω.2 =
        (stateAt p.input data (stepSize p.input) (scale p.input) (period p.input) ω.1 calls).point :=
    execute_stateAt p.input data O (fun history query seed => hO history (0, query) seed)
      (stepSize p.input) (scale p.input) (period p.input) calls ω.1 ω.2
  simp_rw [he]
  have hset : {ω : p.input.sampling.Ω × ((k : ℕ) → O.Seed k) |
      ¬Separates p.input data
        (stateAt p.input data (stepSize p.input) (scale p.input) (period p.input) ω.1 calls).point} =
      {ω | ¬Separates p.input data
        (stateAt p.input data (stepSize p.input) (scale p.input) (period p.input) ω calls).point} ×ˢ Set.univ := by
    ext ω
    simp
  rw [hset, Measure.prod_prod, measure_univ, mul_one]
  exact state_failure_probability p hp data G M calls hcost

end LongTails.Proofs.FiniteScaleConvolutionalSgdRestarts
