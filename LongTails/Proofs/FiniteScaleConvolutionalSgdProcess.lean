import LongTails.Proofs.FiniteScaleConvolutionalSgdProbability

open scoped RealInnerProductSpace

namespace LongTails.Proofs.FiniteScaleConvolutionalSgdProcess

open ManySampleConvolutionalPerceptronDynamics (State)
open FiniteScaleConvolutionalSgdDynamics

noncomputable def score {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ : ℝ) (p r : E) (x : State E) : ℝ :=
  c * x.a * x.q + δ * ⟪x.a • p + x.t • r, x.z⟫

noncomputable def sampleWeight {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K c δ : ℝ) (p r : E) (x : State E) : ℝ :=
  SoftQuadraticDynamics.weight (K * score c δ p r x)

noncomputable def next {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K c δ : ℝ) (p r : E) (x : State E) : State E :=
  weightedNext c δ (sampleWeight K c δ p r x) p r x

noncomputable def trajectory {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (samples : ℕ → ι) : ℕ → State E
  | 0 => start
  | k + 1 => next K (c (samples k)) δ (p (samples k)) (r (samples k))
      (trajectory K δ c p r start samples k)

noncomputable def pastState {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) :
    (k : ℕ) → (Fin k → ι) → State E
  | 0, _ => start
  | k + 1, z => next K (c (z (Fin.last k))) δ (p (z (Fin.last k))) (r (z (Fin.last k)))
      (pastState K δ c p r start k (fun j => z j.castSucc))

lemma sampleWeight_bounds {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K c δ : ℝ) (p r : E) (x : State E) :
    0 < sampleWeight K c δ p r x ∧ sampleWeight K c δ p r x ≤ 1 :=
  ⟨SoftQuadraticDynamics.weight_pos _, SoftQuadraticDynamics.weight_le_one _⟩

lemma sampleWeight_gate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K c δ : ℝ) (p r : E) (x : State E) (hK : 0 < K) :
    sampleWeight K c δ p r x * score c δ p r x ≤ 1 / K := by
  exact SoftQuadraticDynamics.scaled_weighted_score_le K (score c δ p r x) hK

lemma prefix_snoc {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (k : ℕ) (z : Fin k → ι) (i : ι) :
    pastState K δ c p r start (k + 1) (Fin.snoc z i) =
      next K (c i) δ (p i) (r i) (pastState K δ c p r start k z) := by
  simp only [pastState, Fin.snoc_last, Fin.snoc_castSucc]

lemma trajectory_factor {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (samples : ℕ → ι) (k : ℕ) :
    trajectory K δ c p r start samples k = pastState K δ c p r start k (fun j => samples j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [trajectory, pastState, ih, Fin.val_last, Fin.val_castSucc]

lemma trajectory_orthogonal {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (samples : ℕ → ι) (v : E)
    (hstart : ⟪v, start.z⟫ = 0) (hp : ∀ i, ⟪v, p i⟫ = 0) (hr : ∀ i, ⟪v, r i⟫ = 0) :
    ∀ k, ⟪v, (trajectory K δ c p r start samples k).z⟫ = 0 := by
  intro k
  induction k with
  | zero => exact hstart
  | succ k ih =>
    exact weighted_next_orthogonal _ _ _ _ _ _ _ ih (hp (samples k)) (hr (samples k))

open LongTails.Setups.FiniteScaleConvolutionalSgd (Public Data Geometry Features axis)
open LongTails.Setups.TwoSampleQuadraticPerceptron (margin direction)
open ManySampleConvolutionalPerceptronGeometry (decode plusFeature minusFeature)

lemma physical_score (p : Public) (data : Data p) (G : Geometry p data)
    (η scale : ℝ) (hη : η ≠ 0) (x : State (Features p.dimension))
    (i : Fin p.count) (hd : 0 < p.dimension) (hx : ⟪axis p.dimension, x.z⟫ = 0) :
    margin .conv p.dimension (data i) (scale • decode (η * p.contrast) x) =
      (scale ^ 2 / η) * score (η * G.background i) ((η * p.contrast) ^ 2)
        (plusFeature (G.defect i)) (minusFeature (G.defect i)) x := by
  simpa only [score, inner_add_left, real_inner_smul_left] using
    FiniteScaleConvolutionalSgdGeometry.physical_margin p data G η scale hη x i hd hx

lemma physical_next (p : Public) (data : Data p) (G : Geometry p data)
    (η scale : ℝ) (hη : η ≠ 0) (x : State (Features p.dimension))
    (i : Fin p.count) (hd : 0 < p.dimension) (hx : ⟪axis p.dimension, x.z⟫ = 0) :
    let θ := scale • decode (η * p.contrast) x
    θ + (η / (1 + Real.exp (margin .conv p.dimension (data i) θ))) •
      direction .conv p.dimension (data i) θ =
    scale • decode (η * p.contrast)
      (next (scale ^ 2 / η) (η * G.background i) ((η * p.contrast) ^ 2)
        (plusFeature (G.defect i)) (minusFeature (G.defect i)) x) := by
  have hh := physical_logistic_update p data G η scale x i hd hx
  dsimp only at hh ⊢
  rw [physical_score p data G η scale hη x i hd hx] at hh ⊢
  exact hh

def SeparatesState {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (δ : ℝ) (c : ι → ℝ) (p r : ι → E) (x : State E) : Prop :=
  ∀ i, 0 < score (c i) δ (p i) (r i) x

noncomputable def alivePast {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) :
    (k : ℕ) → (Fin k → ι) → Prop
  | 0, _ => F < meanPotential start ∧ ¬SeparatesState δ c p r start
  | k + 1, z => alivePast K δ F c p r start k (fun j => z j.castSucc) ∧
      F < meanPotential (pastState K δ c p r start (k + 1) z) ∧
      ¬SeparatesState δ c p r (pastState K δ c p r start (k + 1) z)

noncomputable def killedPast {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (k : ℕ) (z : Fin k → ι) : ℝ := by
  classical
  exact if alivePast K δ F c p r start k z then meanPotential (pastState K δ c p r start k z) else 0

lemma alivePast_snoc {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (k : ℕ) (z : Fin k → ι) (i : ι) :
    alivePast K δ F c p r start (k + 1) (Fin.snoc z i) ↔
      alivePast K δ F c p r start k z ∧
      F < meanPotential (next K (c i) δ (p i) (r i) (pastState K δ c p r start k z)) ∧
      ¬SeparatesState δ c p r (next K (c i) δ (p i) (r i) (pastState K δ c p r start k z)) := by
  simp only [alivePast, prefix_snoc, Fin.snoc_castSucc]

lemma killedPast_nonneg {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (k : ℕ) (z : Fin k → ι) : 0 ≤ killedPast K δ F c p r start k z := by
  unfold killedPast
  split_ifs
  · exact mean_potential_nonneg _
  · exact le_rfl

lemma killedPast_le_mean {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (k : ℕ) (z : Fin k → ι) :
    killedPast K δ F c p r start k z ≤ meanPotential (pastState K δ c p r start k z) := by
  unfold killedPast
  split_ifs
  · exact le_rfl
  · exact mean_potential_nonneg _

lemma killedPast_row_bound {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (K δ F α : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (k : ℕ) (z : Fin k → ι)
    (hrow : alivePast K δ F c p r start k z →
      (∑ i, meanPotential (next K (c i) δ (p i) (r i) (pastState K δ c p r start k z))) ≤
        (Fintype.card ι : ℝ) * α * meanPotential (pastState K δ c p r start k z)) :
    (∑ i, killedPast K δ F c p r start (k + 1) (Fin.snoc z i)) ≤
      (Fintype.card ι : ℝ) * α * killedPast K δ F c p r start k z := by
  classical
  by_cases h : alivePast K δ F c p r start k z
  · rw [killedPast, ite_eq_left h]
    calc
      _ ≤ ∑ i, meanPotential (pastState K δ c p r start (k + 1) (Fin.snoc z i)) :=
        Finset.sum_le_sum (fun i _ => killedPast_le_mean K δ F c p r start (k + 1) (Fin.snoc z i))
      _ = ∑ i, meanPotential (next K (c i) δ (p i) (r i) (pastState K δ c p r start k z)) := by
        simp only [prefix_snoc]
      _ ≤ _ := hrow h
  · have hdead (i : ι) : ¬alivePast K δ F c p r start (k + 1) (Fin.snoc z i) := by
      intro hi
      exact h ((alivePast_snoc K δ F c p r start k z i).mp hi).1
    simp only [killedPast, ite_eq_right h, ite_eq_right (hdead _), Finset.sum_const_zero, mul_zero, le_refl]

lemma alivePast_current {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (k : ℕ) (z : Fin k → ι) (h : alivePast K δ F c p r start k z) :
    F < meanPotential (pastState K δ c p r start k z) ∧
      ¬SeparatesState δ c p r (pastState K δ c p r start k z) := by
  cases k with
  | zero => exact h
  | succ k => exact h.2

lemma killedPast_contraction {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] [Nonempty ι] (K δ F ρ H ζ : ℝ) (c : ι → ℝ) (p r : ι → E)
    (start : State E) (k : ℕ) (z : Fin k → ι)
    (hK : 0 < K) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hζ : 0 ≤ ζ) (hKζ : 1 / K ≤ ζ)
    (hcl : ∀ i, ρ ≤ |c i|) (hcu : ∀ i, |c i| ≤ 1 / 4)
    (hp : ∀ i, |⟪p i, (pastState K δ c p r start k z).z⟫| ≤ H)
    (hr : ∀ i, |⟪r i, (pastState K δ c p r start k z).z⟫| ≤ H)
    (ht : |(pastState K δ c p r start k z).t| ≤ 2)
    (hW : meanPotential (pastState K δ c p r start k z) ≤ 4)
    (hdH : δ * H ≤ 1) (hζH : ζ ≤ δ * H)
    (hfloor : 1000 * (Fintype.card ι : ℝ) * (δ * H) ≤ ρ ^ 2 * F) :
    (∑ i, killedPast K δ F c p r start (k + 1) (Fin.snoc z i)) ≤
      (Fintype.card ι : ℝ) * (1 - ρ ^ 2 / (24 * Fintype.card ι)) *
        killedPast K δ F c p r start k z := by
  apply killedPast_row_bound
  intro halive
  obtain ⟨hF, hnsep⟩ := alivePast_current K δ F c p r start k z halive
  obtain ⟨i, hi⟩ : ∃ i, score (c i) δ (p i) (r i) (pastState K δ c p r start k z) ≤ 0 := by
    simpa only [SeparatesState, not_forall, not_lt] using hnsep
  have hscore : K * score (c i) δ (p i) (r i) (pastState K δ c p r start k z) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hK.le hi
  have hfloor' := hfloor.trans (mul_le_mul_of_nonneg_left hF.le (sq_nonneg ρ))
  have hgate (j : ι) := (sampleWeight_gate K (c j) δ (p j) (r j)
    (pastState K δ c p r start k z) hK).trans hKζ
  have hh := FiniteScaleConvolutionalSgdDrift.sum_mean_contraction
    (fun j => K * score (c j) δ (p j) (r j) (pastState K δ c p r start k z))
    c p r (pastState K δ c p r start k z) δ ρ H ζ i hscore hδ hρ hζ
    hcl hcu hp hr ht hW hdH hζH hfloor' hgate
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (Fintype.card ι : ℝ) * (1 - ρ ^ 2 / (24 * Fintype.card ι)) *
      meanPotential (pastState K δ c p r start k z) =
      (Fintype.card ι : ℝ) * meanPotential (pastState K δ c p r start k z) -
        ρ ^ 2 * meanPotential (pastState K δ c p r start k z) / 24 := by
    field_simp
  rw [he]
  exact hh

lemma early_trajectory_bounds {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ H ζ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (T : ℕ)
    (hK : 0 < K) (hδ : 0 ≤ δ) (hζ : 0 ≤ ζ) (hKζ : 1 / K ≤ ζ) (hζH : ζ ≤ δ * H)
    (hH : H = 4 * (T : ℝ) + 1) (hsmall : δ * H * (T : ℝ) ≤ 1 / 100)
    (hdH : δ * H ≤ 1) (hW₀ : meanPotential start ≤ 3)
    (ht₀ : 1 ≤ start.t ∧ start.t ≤ 3 / 2) (hz₀ : ‖start.z‖ ≤ 1)
    (hc : ∀ i, |c i| ≤ 1 / 4) (hp : ∀ i, ‖p i‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1)
    (samples : ℕ → ι) :
    ∀ k ≤ T, meanPotential (trajectory K δ c p r start samples k) ≤ 3 + 44 * δ * H * (k : ℝ) ∧
      |(trajectory K δ c p r start samples k).t - start.t| ≤ δ * H * (k : ℝ) ∧
      ‖(trajectory K δ c p r start samples k).z‖ ≤ 1 + 4 * (k : ℝ) := by
  exact FiniteScaleConvolutionalSgdTrajectory.early_path_bounds
    (trajectory K δ c p r start samples) (fun k => c (samples k))
    (fun k => sampleWeight K (c (samples k)) δ (p (samples k)) (r (samples k))
      (trajectory K δ c p r start samples k)) (fun k => p (samples k)) (fun k => r (samples k))
    δ H ζ T hδ hζ hζH hH hsmall hdH hW₀ ht₀ hz₀
    (fun _ _ => rfl) (fun k _ => ⟨(sampleWeight_bounds _ _ _ _ _ _).1.le,
      (sampleWeight_bounds _ _ _ _ _ _).2⟩)
    (fun k _ => hc (samples k)) (fun k _ => hp (samples k)) (fun k _ => hr (samples k))
    (fun k _ => (sampleWeight_gate _ _ _ _ _ _ hK).trans hKζ)

lemma early_past_bounds {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nonempty ι] (K δ H ζ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (T : ℕ)
    (hK : 0 < K) (hδ : 0 ≤ δ) (hζ : 0 ≤ ζ) (hKζ : 1 / K ≤ ζ) (hζH : ζ ≤ δ * H)
    (hH : H = 4 * (T : ℝ) + 1) (hsmall : δ * H * (T : ℝ) ≤ 1 / 100)
    (hdH : δ * H ≤ 1) (hW₀ : meanPotential start ≤ 3)
    (ht₀ : 1 ≤ start.t ∧ start.t ≤ 3 / 2) (hz₀ : ‖start.z‖ ≤ 1)
    (hc : ∀ i, |c i| ≤ 1 / 4) (hp : ∀ i, ‖p i‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1)
    (k : ℕ) (hk : k ≤ T) (z : Fin k → ι) :
    meanPotential (pastState K δ c p r start k z) ≤ 4 ∧
      (3 / 4 ≤ (pastState K δ c p r start k z).t ∧ (pastState K δ c p r start k z).t ≤ 7 / 4) ∧
      ‖(pastState K δ c p r start k z).z‖ ≤ H := by
  classical
  let samples : ℕ → ι := fun j => if hj : j < k then z ⟨j, hj⟩ else Classical.choice ‹Nonempty ι›
  have he : trajectory K δ c p r start samples k = pastState K δ c p r start k z := by
    rw [trajectory_factor]
    congr 1
    funext j
    simp only [samples, dite_eq_left j.isLt, Fin.eta]
  have hh := early_trajectory_bounds K δ H ζ c p r start T hK hδ hζ hKζ hζH
    hH hsmall hdH hW₀ ht₀ hz₀ hc hp hr samples k hk
  rw [he] at hh
  have hH₀ : 0 ≤ H := by rw [hH]; positivity
  have hcast : (k : ℝ) ≤ (T : ℝ) := by exact_mod_cast hk
  have hsmallk := (mul_le_mul_of_nonneg_left hcast (mul_nonneg hδ hH₀)).trans hsmall
  obtain ⟨hm, ht, hz⟩ := hh
  have htd := abs_le.mp ht
  refine ⟨by nlinarith, ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩, ?_⟩
  rw [hH]
  linarith

open MeasureTheory

lemma killed_integral_bound {E Ω ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ι)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ
      (PMF.uniformOfFintype ι).toMeasure P)
    (K δ F ρ H ζ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (T : ℕ)
    (hK : 0 < K) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hζ : 0 ≤ ζ)
    (hKζ : 1 / K ≤ ζ) (hζH : ζ ≤ δ * H)
    (hH : H = 4 * (T : ℝ) + 1) (hsmall : δ * H * (T : ℝ) ≤ 1 / 100)
    (hdH : δ * H ≤ 1) (hW₀ : meanPotential start ≤ 3)
    (ht₀ : 1 ≤ start.t ∧ start.t ≤ 3 / 2) (hz₀ : ‖start.z‖ ≤ 1)
    (hcl : ∀ i, ρ ≤ |c i|) (hcu : ∀ i, |c i| ≤ 1 / 4)
    (hp : ∀ i, ‖p i‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1)
    (hfloor : 1000 * (Fintype.card ι : ℝ) * (δ * H) ≤ ρ ^ 2 * F) :
    (∫ ω, killedPast K δ F c p r start T (fun j : Fin T => ξ j ω) ∂P) ≤
      (1 - ρ ^ 2 / (24 * Fintype.card ι)) ^ T * 3 := by
  classical
  have hN : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hρu : ρ ≤ 1 / 4 := (hcl (Classical.choice ‹Nonempty ι›)).trans (hcu _)
  have hα : 0 ≤ 1 - ρ ^ 2 / (24 * Fintype.card ι) := by
    have hd : (0 : ℝ) < 24 * Fintype.card ι := by positivity
    have hh : ρ ^ 2 / (24 * Fintype.card ι) ≤ 1 := (div_le_one₀ hd).2 (by nlinarith)
    linarith
  apply FiniteScaleConvolutionalSgdProbability.prefix_contraction P ξ hξ
    (killedPast K δ F c p r start) (1 - ρ ^ 2 / (24 * Fintype.card ι)) 3 T hα
    (fun z => (killedPast_le_mean K δ F c p r start 0 z).trans hW₀) ?_ T le_rfl
  intro k hk z
  obtain ⟨hW, ht, hz⟩ := early_past_bounds K δ H ζ c p r start T hK hδ hζ hKζ hζH
    hH hsmall hdH hW₀ ht₀ hz₀ hcu hp hr k (Nat.le_of_lt hk) z
  have hpi : ∀ i, |⟪p i, (pastState K δ c p r start k z).z⟫| ≤ H := by
    intro i
    calc
      _ ≤ ‖p i‖ * ‖(pastState K δ c p r start k z).z‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * H := by gcongr; exact hp i
      _ = H := one_mul H
  have hri : ∀ i, |⟪r i, (pastState K δ c p r start k z).z⟫| ≤ H := by
    intro i
    calc
      _ ≤ ‖r i‖ * ‖(pastState K δ c p r start k z).z‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * H := by gcongr; exact hr i
      _ = H := one_mul H
  have htAbs : |(pastState K δ c p r start k z).t| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  exact killedPast_contraction K δ F ρ H ζ c p r start k z hK hδ hρ hζ hKζ
    hcl hcu hpi hri htAbs hW hdH hζH hfloor

lemma killed_event_bound {E Ω ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace Ω] [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ι)
    (hξ : ∀ j, Measurable (ξ j)) (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E)
    (start : State E) (T : ℕ) (hF : 0 < F) :
    P {ω | alivePast K δ F c p r start T (fun j : Fin T => ξ j ω)} ≤
      ENNReal.ofReal ((∫ ω, killedPast K δ F c p r start T (fun j : Fin T => ξ j ω) ∂P) / F) := by
  have hm : Measurable (fun ω (j : Fin T) => ξ j ω) := Measurable.of_eval (fun j => hξ j)
  have hi := FiniteScaleConvolutionalSgdProbability.integrable_finite_comp P _ hm
    (killedPast K δ F c p r start T)
  have hn := fun ω => killedPast_nonneg K δ F c p r start T (fun j : Fin T => ξ j ω)
  have hmark := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hn) hi F
  have hsub : {ω | alivePast K δ F c p r start T (fun j : Fin T => ξ j ω)} ⊆
      {ω | F ≤ killedPast K δ F c p r start T (fun j : Fin T => ξ j ω)} := by
    intro ω hω
    change alivePast K δ F c p r start T (fun j : Fin T => ξ j ω) at hω
    have hh := (alivePast_current K δ F c p r start T (fun j : Fin T => ξ j ω) hω).1
    change F ≤ killedPast K δ F c p r start T (fun j : Fin T => ξ j ω)
    rw [killedPast, ite_eq_left hω]
    exact hh.le
  have hmono := measureReal_mono (μ := P) hsub (measure_ne_top _ _)
  have hreal : P.real {ω | alivePast K δ F c p r start T (fun j : Fin T => ξ j ω)} ≤
      (∫ ω, killedPast K δ F c p r start T (fun j : Fin T => ξ j ω) ∂P) / F := by
    apply (le_div_iff₀ hF).2
    have hh := mul_le_mul_of_nonneg_left hmono hF.le
    nlinarith
  rw [← ofReal_measureReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hreal

lemma alivePast_trajectory_iff {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (samples : ℕ → ι) (k : ℕ) :
    alivePast K δ F c p r start k (fun j : Fin k => samples j) ↔
      ∀ j ≤ k, F < meanPotential (trajectory K δ c p r start samples j) ∧
        ¬SeparatesState δ c p r (trajectory K δ c p r start samples j) := by
  induction k with
  | zero => simp only [alivePast, Nat.le_zero, forall_eq, trajectory]
  | succ k ih =>
    change (alivePast K δ F c p r start k (fun j : Fin k => samples j) ∧
      F < meanPotential (pastState K δ c p r start (k + 1) (fun j => samples j)) ∧
      ¬SeparatesState δ c p r (pastState K δ c p r start (k + 1) (fun j => samples j))) ↔ _
    rw [ih, ← trajectory_factor]
    constructor
    · rintro ⟨hpast, hcurrent⟩ j hj
      rcases Nat.eq_or_lt_of_le hj with he | he
      · simpa only [he] using hcurrent
      · exact hpast j (Nat.le_of_lt_succ he)
    · intro h
      exact ⟨fun j hj => h j (Nat.le_succ_of_le hj), h (k + 1) le_rfl⟩

end LongTails.Proofs.FiniteScaleConvolutionalSgdProcess
