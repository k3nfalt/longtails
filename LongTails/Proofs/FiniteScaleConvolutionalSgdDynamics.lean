import LongTails.Proofs.FiniteScaleConvolutionalSgdGeometry

open scoped RealInnerProductSpace

namespace LongTails.Proofs.FiniteScaleConvolutionalSgdDynamics

open LongTails.Setups.FiniteScaleConvolutionalSgd
open LongTails.Setups.TwoSampleQuadraticPerceptron (margin direction)
open LongTails.Proofs.ManySampleConvolutionalPerceptronGeometry (decode plusFeature minusFeature)
open LongTails.Proofs.ManySampleConvolutionalPerceptronDynamics (State)
open FiniteScaleConvolutionalSgdGeometry

noncomputable def weightedNext {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w : ℝ) (p r : E) (x : State E) : State E where
  a := x.a + c * w * x.q + δ * w * ⟪p, x.z⟫
  q := x.q + c * w * x.a
  t := x.t + δ * w * ⟪r, x.z⟫
  z := x.z + w • (x.a • p + x.t • r)

lemma weighted_next_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w : ℝ) (p r v : E) (x : State E)
    (hx : ⟪v, x.z⟫ = 0) (hp : ⟪v, p⟫ = 0) (hr : ⟪v, r⟫ = 0) :
    ⟪v, (weightedNext c δ w p r x).z⟫ = 0 := by
  simp [weightedNext, inner_add_right, inner_smul_right, hx, hp, hr]

lemma normalized_update (p : Public) (data : Data p) (G : Geometry p data)
    (η w : ℝ) (x : State (Features p.dimension)) (i : Fin p.count)
    (hd : 0 < p.dimension) (hx : ⟪axis p.dimension, x.z⟫ = 0) :
    decode (η * p.contrast) x + (η * w) •
      direction .conv p.dimension (data i) (decode (η * p.contrast) x) =
    decode (η * p.contrast) (weightedNext (η * G.background i) ((η * p.contrast) ^ 2) w
      (plusFeature (G.defect i)) (minusFeature (G.defect i)) x) := by
  rw [ManySampleConvolutionalPerceptronGeometry.direction_decode,
    sample_plus p data G i, sample_minus p data G i]
  simp only [inner_add_left, real_inner_smul_left,
    ManySampleConvolutionalPerceptronGeometry.decode_axis hd hx,
    centered_decode_inner _ _ _ (plus_centered p data G i),
    centered_decode_inner _ _ _ (minus_centered p data G i)]
  apply Prod.ext
  · apply Prod.ext <;> simp only [decode, weightedNext, Prod.fst_add, Prod.smul_fst,
      Prod.snd_add, Prod.smul_snd, smul_eq_mul] <;> ring
  · simp only [decode, weightedNext, Prod.snd_add, Prod.smul_snd]
    module

lemma physical_weighted_update (p : Public) (data : Data p) (G : Geometry p data)
    (η scale w : ℝ) (x : State (Features p.dimension)) (i : Fin p.count)
    (hd : 0 < p.dimension) (hx : ⟪axis p.dimension, x.z⟫ = 0) :
    scale • decode (η * p.contrast) x + (η * w) •
      direction .conv p.dimension (data i) (scale • decode (η * p.contrast) x) =
    scale • decode (η * p.contrast)
      (weightedNext (η * G.background i) ((η * p.contrast) ^ 2) w
        (plusFeature (G.defect i)) (minusFeature (G.defect i)) x) := by
  rw [direction_homogeneous]
  calc
    _ = scale • (decode (η * p.contrast) x + (η * w) •
        direction .conv p.dimension (data i) (decode (η * p.contrast) x)) := by module
    _ = _ := by rw [normalized_update p data G η w x i hd hx]

lemma physical_logistic_update (p : Public) (data : Data p) (G : Geometry p data)
    (η scale : ℝ) (x : State (Features p.dimension)) (i : Fin p.count)
    (hd : 0 < p.dimension) (hx : ⟪axis p.dimension, x.z⟫ = 0) :
    let θ := scale • decode (η * p.contrast) x
    let w := SoftQuadraticDynamics.weight (margin .conv p.dimension (data i) θ)
    θ + (η / (1 + Real.exp (margin .conv p.dimension (data i) θ))) •
      direction .conv p.dimension (data i) θ =
    scale • decode (η * p.contrast)
      (weightedNext (η * G.background i) ((η * p.contrast) ^ 2) w
        (plusFeature (G.defect i)) (minusFeature (G.defect i)) x) := by
  dsimp only
  simpa only [SoftQuadraticDynamics.weight, mul_one_div] using
    physical_weighted_update p data G η scale
      (SoftQuadraticDynamics.weight
        (margin .conv p.dimension (data i) (scale • decode (η * p.contrast) x))) x i hd hx

noncomputable def meanEnergy {E : Type*} (x : State E) : ℝ := x.a ^ 2 + x.q ^ 2

noncomputable def imbalance {E : Type*} (x : State E) : ℝ := x.a ^ 2 - x.q ^ 2

noncomputable def meanPotential {E : Type*} (x : State E) : ℝ := meanEnergy x + 2 * |imbalance x|

lemma mean_potential_nonneg {E : Type*} (x : State E) : 0 ≤ meanPotential x := by
  unfold meanPotential meanEnergy
  positivity

lemma mean_potential_control {E : Type*} (x : State E) :
    meanPotential x ≤ 3 * (|imbalance x| + |x.a * x.q|) := by
  have hh := SoftQuadraticDynamics.mean_energy_bound x.a x.q
  unfold meanPotential meanEnergy imbalance
  linarith [abs_nonneg (x.a * x.q)]

lemma mean_potential_box_bound {E : Type*} (x : State E) (ha : |x.a| ≤ 1) (hq : |x.q| ≤ 1) :
    meanPotential x ≤ 3 := by
  have ha₂ : x.a ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg x.a) zero_le_one).2 ha
  have hq₂ : x.q ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg x.q) zero_le_one).2 hq
  unfold meanPotential meanEnergy imbalance
  by_cases hh : 0 ≤ x.a ^ 2 - x.q ^ 2
  · rw [abs_of_nonneg hh]
    nlinarith [sq_nonneg x.q]
  · rw [abs_of_nonpos (le_of_lt (lt_of_not_ge hh))]
    nlinarith [sq_nonneg x.a]

lemma mean_coordinate_bound {E : Type*} (x : State E) :
    |x.a| ≤ Real.sqrt (meanPotential x) ∧ |x.q| ≤ Real.sqrt (meanPotential x) := by
  have hs := Real.sq_sqrt (mean_potential_nonneg x)
  have hn := Real.sqrt_nonneg (meanPotential x)
  have ha := abs_nonneg (imbalance x)
  change Real.sqrt (meanPotential x) ^ 2 = x.a ^ 2 + x.q ^ 2 + 2 * |imbalance x| at hs
  constructor
  · nlinarith [sq_abs x.a, sq_nonneg x.q]
  · nlinarith [sq_abs x.q, sq_nonneg x.a]

lemma mean_energy_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w : ℝ) (p r : E) (x : State E) :
    meanEnergy (weightedNext c δ w p r x) =
      (1 + (c * w) ^ 2) * meanEnergy x + 4 * (c * w) * x.a * x.q +
        2 * (δ * w * ⟪p, x.z⟫) * (x.a + c * w * x.q) + (δ * w * ⟪p, x.z⟫) ^ 2 := by
  exact SoftQuadraticDynamics.mean_energy_identity x.a x.q (c * w) (δ * w * ⟪p, x.z⟫)

lemma imbalance_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w : ℝ) (p r : E) (x : State E) :
    imbalance (weightedNext c δ w p r x) =
      (1 - (c * w) ^ 2) * imbalance x +
        2 * (δ * w * ⟪p, x.z⟫) * (x.a + c * w * x.q) + (δ * w * ⟪p, x.z⟫) ^ 2 := by
  exact SoftQuadraticDynamics.mean_imbalance_identity x.a x.q (c * w) (δ * w * ⟪p, x.z⟫)

lemma coupled_readout_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w : ℝ) (p r : E) (x : State E) :
    2 * δ * ‖(weightedNext c δ w p r x).z‖ ^ 2 + meanEnergy (weightedNext c δ w p r x) =
      2 * δ * ‖x.z‖ ^ 2 + meanEnergy x +
        4 * w * (c * x.a * x.q + δ * ⟪x.a • p + x.t • r, x.z⟫) +
        2 * δ * w * (x.a + c * w * x.q) * ⟪p, x.z⟫ +
        c ^ 2 * w ^ 2 * meanEnergy x + δ ^ 2 * w ^ 2 * ⟪p, x.z⟫ ^ 2 +
        2 * δ * w ^ 2 * ‖x.a • p + x.t • r‖ ^ 2 := by
  rw [mean_energy_step]
  change 2 * δ * ‖x.z + w • (x.a • p + x.t • r)‖ ^ 2 + _ = _
  rw [norm_add_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_comm x.z (x.a • p + x.t • r)]
  ring

noncomputable def forcing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w : ℝ) (p : E) (x : State E) : ℝ :=
  2 * (δ * w * ⟪p, x.z⟫) * (x.a + c * w * x.q) + (δ * w * ⟪p, x.z⟫) ^ 2

lemma mean_potential_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w : ℝ) (p r : E) (x : State E) (hc : |c * w| ≤ 1) :
    meanPotential (weightedNext c δ w p r x) ≤
      meanPotential x - (c * w) ^ 2 * (|imbalance x| + |x.a * x.q|) +
        (4 * w * (c * x.a * x.q) + 3 * (c * w) ^ 2 * |x.a * x.q|) +
        3 * |forcing c δ w p x| := by
  have hf : 0 ≤ 1 - (c * w) ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (c * w)) (show (0 : ℝ) ≤ 1 by norm_num)).2 hc
    rw [sq_abs] at hh
    linarith
  have hid : imbalance (weightedNext c δ w p r x) =
      (1 - (c * w) ^ 2) * imbalance x + forcing c δ w p x := by
    rw [imbalance_step]
    unfold forcing
    ring
  have hD : |imbalance (weightedNext c δ w p r x)| ≤
      (1 - (c * w) ^ 2) * |imbalance x| + |forcing c δ w p x| := by
    rw [hid]
    exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_of_nonneg hf])
  have hE := SoftQuadraticDynamics.mean_energy_bound x.a x.q
  change meanEnergy x ≤ 2 * |x.a * x.q| + |imbalance x| at hE
  have hm := mul_le_mul_of_nonneg_left hE (sq_nonneg (c * w))
  have he : meanEnergy (weightedNext c δ w p r x) =
    (1 + (c * w) ^ 2) * meanEnergy x + 4 * (c * w) * x.a * x.q +
      forcing c δ w p x := by
    rw [mean_energy_step]
    unfold forcing
    ring
  unfold meanPotential
  nlinarith [le_abs_self (forcing c δ w p x)]

lemma signed_work_bound (k w x U : ℝ) (hk : 0 ≤ k) (hk₁ : k ≤ 1 / 3)
    (hw : 0 ≤ w) (hw₁ : w ≤ 1) (hU : 0 ≤ U) (hgate : w * x ≤ U) :
    4 * w * x + 3 * k * w ^ 2 * |x| ≤ 5 * U := by
  have hh : 3 * k * w ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hw₁ hk
    nlinarith
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    have hm := mul_le_mul_of_nonneg_right hh (mul_nonneg hw hx)
    nlinarith
  · have hx₀ : x ≤ 0 := (lt_of_not_ge hx).le
    rw [abs_of_nonpos hx₀]
    have hm := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hw hx₀) (show 0 ≤ 4 - 3 * k * w by linarith)
    nlinarith

lemma mean_signed_work_bound (c w a q U : ℝ) (hc : |c| ≤ 1 / 3)
    (hw : 0 ≤ w) (hw₁ : w ≤ 1) (hU : 0 ≤ U) (hgate : w * (c * a * q) ≤ U) :
    4 * w * (c * a * q) + 3 * (c * w) ^ 2 * |a * q| ≤ 5 * U := by
  have hh := signed_work_bound |c| w (c * a * q) U (abs_nonneg c) hc hw hw₁ hU hgate
  have he : (c * w) ^ 2 * |a * q| = |c| * w ^ 2 * |c * a * q| := by
    calc
      _ = c ^ 2 * w ^ 2 * |a * q| := by ring
      _ = |c| ^ 2 * w ^ 2 * |a * q| := by rw [sq_abs]
      _ = _ := by simp only [abs_mul]; ring
  nlinarith

lemma forcing_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w b A H : ℝ) (p : E) (x : State E) (hδ : 0 ≤ δ)
    (hw : 0 ≤ w) (hw₁ : w ≤ 1) (hb : 0 ≤ b) (hH : 0 ≤ H)
    (hc : |c| ≤ b) (ha : |x.a| ≤ A) (hq : |x.q| ≤ A) (hp : |⟪p, x.z⟫| ≤ H) :
    |forcing c δ w p x| ≤ 2 * δ * w * H * (1 + b) * A + δ ^ 2 * w ^ 2 * H ^ 2 := by
  have hcq : |c * w * x.q| ≤ b * A := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw]
    calc
      _ ≤ b * 1 * A := by gcongr
      _ = _ := by ring
  have haq : |x.a + c * w * x.q| ≤ (1 + b) * A := by
    have hh := abs_add_le x.a (c * w * x.q)
    nlinarith
  have hm : |(δ * w * ⟪p, x.z⟫) * (x.a + c * w * x.q)| ≤
      δ * w * H * ((1 + b) * A) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hδ, abs_of_nonneg hw]
    gcongr
  have hs : (δ * w * ⟪p, x.z⟫) ^ 2 ≤ δ ^ 2 * w ^ 2 * H ^ 2 := by
    calc
      _ = (δ * w) ^ 2 * |⟪p, x.z⟫| ^ 2 := by rw [sq_abs]; ring
      _ ≤ (δ * w) ^ 2 * H ^ 2 :=
        mul_le_mul_of_nonneg_left ((sq_le_sq₀ (abs_nonneg _) hH).2 hp) (sq_nonneg _)
      _ = _ := by ring
  unfold forcing
  calc
    _ ≤ |2 * ((δ * w * ⟪p, x.z⟫) * (x.a + c * w * x.q))| +
        |(δ * w * ⟪p, x.z⟫) ^ 2| := by
      simpa only [mul_assoc] using
        abs_add_le (2 * ((δ * w * ⟪p, x.z⟫) * (x.a + c * w * x.q)))
          ((δ * w * ⟪p, x.z⟫) ^ 2)
    _ ≤ _ := by
      rw [abs_mul]
      rw [abs_of_nonneg (sq_nonneg (δ * w * ⟪p, x.z⟫))]
      rw [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      nlinarith

lemma mean_damping_bound {E : Type*} (c ρ w : ℝ) (x : State E)
    (hρ : 0 ≤ ρ) (hc : ρ ≤ |c|) :
    ρ ^ 2 * w ^ 2 * meanPotential x / 3 ≤
      (c * w) ^ 2 * (|imbalance x| + |x.a * x.q|) := by
  have hs : ρ ^ 2 ≤ c ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hρ (abs_nonneg c)).2 hc
  calc
    _ ≤ ρ ^ 2 * w ^ 2 * (3 * (|imbalance x| + |x.a * x.q|)) / 3 := by
      gcongr
      exact mean_potential_control x
    _ = ρ ^ 2 * w ^ 2 * (|imbalance x| + |x.a * x.q|) := by ring
    _ ≤ c ^ 2 * w ^ 2 * (|imbalance x| + |x.a * x.q|) := by gcongr
    _ = _ := by ring

lemma soft_mean_drift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c δ w ρ H ζ : ℝ) (p r : E) (x : State E)
    (hδ : 0 ≤ δ) (hw : 0 ≤ w) (hw₁ : w ≤ 1) (hρ : 0 ≤ ρ)
    (hcl : ρ ≤ |c|) (hcu : |c| ≤ 1 / 4) (hζ : 0 ≤ ζ)
    (hp : |⟪p, x.z⟫| ≤ H) (hr : |⟪r, x.z⟫| ≤ H) (ht : |x.t| ≤ 2)
    (hgate : w * (c * x.a * x.q + δ * ⟪x.a • p + x.t • r, x.z⟫) ≤ ζ) :
    meanPotential (weightedNext c δ w p r x) ≤
      meanPotential x - ρ ^ 2 * w ^ 2 * meanPotential x / 3 +
        13 * δ * H * w * Real.sqrt (meanPotential x) + 10 * δ * H * w +
        3 * δ ^ 2 * H ^ 2 * w ^ 2 + 5 * ζ := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hp
  have ha := (mean_coordinate_bound x).1
  have hq := (mean_coordinate_bound x).2
  have hA := Real.sqrt_nonneg (meanPotential x)
  have hres : |⟪x.a • p + x.t • r, x.z⟫| ≤ H * (Real.sqrt (meanPotential x) + 2) := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    calc
      _ ≤ |x.a * ⟪p, x.z⟫| + |x.t * ⟪r, x.z⟫| := abs_add_le _ _
      _ = |x.a| * |⟪p, x.z⟫| + |x.t| * |⟪r, x.z⟫| := by rw [abs_mul, abs_mul]
      _ ≤ Real.sqrt (meanPotential x) * H + 2 * H := by gcongr
      _ = _ := by ring
  have hg : w * (c * x.a * x.q) ≤ ζ + δ * w * H * (Real.sqrt (meanPotential x) + 2) := by
    have hh := mul_le_mul_of_nonneg_left ((neg_le_abs _).trans hres) (mul_nonneg hδ hw)
    nlinarith
  have hcore := mean_signed_work_bound c w x.a x.q
    (ζ + δ * w * H * (Real.sqrt (meanPotential x) + 2))
    (show |c| ≤ 1 / 3 by linarith) hw hw₁ (by positivity) hg
  have hf := forcing_bound c δ w (1 / 4) (Real.sqrt (meanPotential x)) H p x
    hδ hw hw₁ (by norm_num) hH hcu ha hq hp
  have hcw : |c * w| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hw]
    have hh := mul_le_mul_of_nonneg_left hw₁ (abs_nonneg c)
    nlinarith
  have hstep := mean_potential_step c δ w p r x hcw
  have hdamp := mean_damping_bound c ρ w x hρ hcl
  have hpos : 0 ≤ δ * H * w * Real.sqrt (meanPotential x) := by positivity
  nlinarith

end LongTails.Proofs.FiniteScaleConvolutionalSgdDynamics
