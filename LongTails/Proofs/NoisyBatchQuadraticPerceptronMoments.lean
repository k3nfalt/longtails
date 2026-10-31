import LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution
import LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift
import Mathlib.Analysis.Complex.ExponentialBounds
namespace LongTails.Proofs.NoisyBatchQuadraticPerceptronMoments
open Classical MeasureTheory ProbabilityTheory
open LongTails.Setups.NoisyBatchQuadraticPerceptron
open LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution
open LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry
open LongTails.Proofs.NoisyBatchQuadraticPerceptronGaussian
open LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift
open scoped RealInnerProductSpace
lemma geometric_recursion_bound (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) (ha : 1 ≤ a) (hb : 0 ≤ b)
    (h : ∀ j < N, x (j + 1) ≤ a * x j + b) :
    x N ≤ a ^ N * (x 0 + N * b) := by
  have hi : ∀ n ≤ N, x n ≤ a ^ n * (x 0 + n * b) := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := h n (by omega)
      have hu := mul_le_mul_of_nonneg_left (ih (by omega)) (by linarith : 0 ≤ a)
      have hp : 1 ≤ a ^ (n + 1) := one_le_pow₀ ha
      have hbp := mul_le_mul_of_nonneg_right hp hb
      rw [pow_succ] at hbp ⊢
      push_cast
      nlinarith
  exact hi N le_rfl
lemma exponential_block_factor (a : ℝ) (N : ℕ) (ha : 0 ≤ a) (hN : N * a ≤ 3) :
    (1 + a) ^ N ≤ 32 := by
  have hle : 1 + a ≤ Real.exp a := by simpa only [add_comm] using Real.add_one_le_exp a
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + a) hle N
  rw [← Real.exp_nat_mul] at hp
  have he : Real.exp ((N : ℝ) * a) ≤ Real.exp 3 := Real.exp_le_exp.mpr hN
  have h3 : Real.exp (3 : ℝ) < 32 := by
    have hcube := pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_nonneg 1) (by norm_num : (3 : ℕ) ≠ 0)
    have heq : Real.exp (3 : ℝ) = Real.exp 1 ^ (3 : ℕ) := by simp
    rw [heq]
    norm_num at hcube
    linarith
  exact hp.trans (he.trans h3.le)
lemma frozen_energy_kernel_le (P : Public) (data : Data P) (η : ℝ)
    (w : Weights P.dimension) (hη : 0 ≤ η) (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    (∫ z : Weights P.dimension,
      ‖if Separates data w then w else
        WithLp.toLp 2 (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
          w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) + P.noiseScale • z‖ ^ 2
      ∂stdGaussian (Weights P.dimension)) ≤
      (1 + η ^ 2 * P.radius ^ 2) * ‖w‖ ^ 2 + P.noiseScale ^ 2 * (P.dimension + 1) := by
  by_cases hs : Separates data w
  · simp only [ite_eq_left hs]
    simp only [integral_const]
    norm_num only [probReal_univ, one_smul]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg η) (sq_nonneg P.radius)) (sq_nonneg ‖w‖),
      mul_nonneg (sq_nonneg P.noiseScale) (show (0 : ℝ) ≤ P.dimension + 1 by positivity)]
  · simp only [ite_eq_right hs]
    rw [gaussian_energy_shift, weights_finrank]
    have hb := deterministic_energy_le P data η w.ofLp.1 w.ofLp.2 hη hR
    have hn : ∀ x : Weights P.dimension, ‖x‖ ^ 2 = ‖x.ofLp.1‖ ^ 2 + x.ofLp.2 ^ 2 := by
      intro x
      simpa using WithLp.prod_norm_sq_eq_of_L2 x
    rw [hn, hn]
    simpa using add_le_add_right hb (P.noiseScale ^ 2 * (P.dimension + 1))
lemma integral_indicator_affine {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω) (hS : MeasurableSet S)
    (f : Ω → ℝ) (hf : Integrable f μ) (a b : ℝ) :
    (∫ ω, S.indicator (fun ω => a * f ω + b) ω ∂μ) =
      a * (∫ ω, S.indicator f ω ∂μ) + b * μ.real S := by
  rw [integral_indicator hS, integral_add (hf.restrict.const_mul a) (integrable_const b),
    integral_const_mul, ← integral_indicator hS, setIntegral_const]
  simp [mul_comm]
lemma tested_energy_growth (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 ≤ η) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (t : ℕ) (A : Set (Fin t → Weights P.dimension)) (hA : MeasurableSet A) :
    let S := {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A}
    (∫ ω, S.indicator (fun ω => ‖(trajectory P data η ω ((P.count : ℕ) * (t + 1))).point‖ ^ 2) ω
      ∂(P.noise.law : Measure P.noise.Ω)) ≤
    (1 + η ^ 2 * P.radius ^ 2) *
      (∫ ω, S.indicator (fun ω => ‖(trajectory P data η ω ((P.count : ℕ) * t)).point‖ ^ 2) ω
        ∂(P.noise.law : Measure P.noise.Ω)) +
      P.noiseScale ^ 2 * (P.dimension + 1) * (P.noise.law : Measure P.noise.Ω).real S := by
  dsimp only
  let V := fun w : Weights P.dimension => ‖w‖ ^ 2
  let H := fun z : (Fin t → Weights P.dimension) × Weights P.dimension =>
    if z.1 ∈ A then V (pastPoint P data η (t + 1) (Fin.snoc z.1 z.2)) else 0
  let B := fun x : Fin t → Weights P.dimension =>
    if x ∈ A then (1 + η ^ 2 * P.radius ^ 2) * V (pastPoint P data η t x) + P.noiseScale ^ 2 * (P.dimension + 1) else 0
  have hV : Measurable V := by fun_prop
  have hi (k : ℕ) : Integrable (fun ω => V (trajectory P data η ω ((P.count : ℕ) * k)).point)
      (P.noise.law : Measure P.noise.Ω) :=
    (memLp_batch_point P data η h.measurable (memLp_noise_sample P h) k).norm.integrable_sq
  have hH : Measurable H := Measurable.ite (hA.preimage measurable_fst)
    (hV.comp ((measurable_pastPoint P data η (t + 1)).comp (measurable_snoc t))) measurable_const
  have hB : Measurable B := Measurable.ite hA
    (((hV.comp (measurable_pastPoint P data η t)).const_mul _).add_const _) measurable_const
  have hS : MeasurableSet {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A} :=
    hA.preimage (Measurable.of_eval fun j => h.measurable j)
  have heH : (fun ω => H ((fun j : Fin t => P.noise.sample j ω), P.noise.sample t ω)) =
      {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A}.indicator
        (fun ω => V (trajectory P data η ω ((P.count : ℕ) * (t + 1))).point) := by
    funext ω
    dsimp only [H]
    rw [sample_snoc, ← batch_point_factor]
    rfl
  have heB : (fun ω => B (fun j : Fin t => P.noise.sample j ω)) =
      {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A}.indicator
        (fun ω => (1 + η ^ 2 * P.radius ^ 2) * V (trajectory P data η ω ((P.count : ℕ) * t)).point +
          P.noiseScale ^ 2 * (P.dimension + 1)) := by
    funext ω
    dsimp only [B]
    rw [← batch_point_factor]
    rfl
  have hHi : Integrable (fun ω => H ((fun j : Fin t => P.noise.sample j ω), P.noise.sample t ω))
      (P.noise.law : Measure P.noise.Ω) := by
    rw [heH]
    exact (hi (t + 1)).indicator hS
  have hBi : Integrable (fun ω => B (fun j : Fin t => P.noise.sample j ω))
      (P.noise.law : Measure P.noise.Ω) := by
    rw [heB]
    exact (((hi t).const_mul _).add (integrable_const _)).indicator hS
  have hb (x : Fin t → Weights P.dimension) :
      (∫ z, H (x, z) ∂stdGaussian (Weights P.dimension)) ≤ B x := by
    by_cases hx : x ∈ A
    · simp only [H, B, hx, ite_eq_left]
      dsimp only [V]
      simp_rw [pastPoint_snoc, deterministic_proposal]
      exact frozen_energy_kernel_le P data η (pastPoint P data η t x) hη hR
    · simp [H, B, hx]
  have hd := integral_past_next_le (P.noise.law : Measure P.noise.Ω)
    (stdGaussian (Weights P.dimension)) P.noise.sample h.measurable h.independent t (h.marginal t)
    H hH hHi B hB hBi hb
  rw [heH, heB] at hd
  rw [integral_indicator_affine (P.noise.law : Measure P.noise.Ω) _ hS _
    (hi t)] at hd
  exact hd
lemma tested_block_energy_growth (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 ≤ η) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (t B : ℕ) (A : Set (Fin t → Weights P.dimension)) (hA : MeasurableSet A) :
    let S := {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A}
    (∫ ω, S.indicator (fun ω => ‖(trajectory P data η ω ((P.count : ℕ) * (t + B))).point‖ ^ 2) ω
      ∂(P.noise.law : Measure P.noise.Ω)) ≤
    (1 + η ^ 2 * P.radius ^ 2) ^ B *
      ((∫ ω, S.indicator (fun ω => ‖(trajectory P data η ω ((P.count : ℕ) * t)).point‖ ^ 2) ω
        ∂(P.noise.law : Measure P.noise.Ω)) +
        B * (P.noiseScale ^ 2 * (P.dimension + 1) * (P.noise.law : Measure P.noise.Ω).real S)) := by
  let S := {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A}
  let x := fun k => ∫ ω, S.indicator
    (fun ω => ‖(trajectory P data η ω ((P.count : ℕ) * (t + k))).point‖ ^ 2) ω
      ∂(P.noise.law : Measure P.noise.Ω)
  have hs (j : ℕ) : x (j + 1) ≤ (1 + η ^ 2 * P.radius ^ 2) * x j +
      P.noiseScale ^ 2 * (P.dimension + 1) * (P.noise.law : Measure P.noise.Ω).real S := by
    let f : (Fin (t + j) → Weights P.dimension) → (Fin t → Weights P.dimension) :=
      fun z k => z (Fin.castLE (Nat.le_add_right t j) k)
    have hf : Measurable f := Measurable.of_eval fun k => measurable_pi_apply _
    have hd := tested_energy_growth P data η h hη hR (t + j) (f ⁻¹' A) (hA.preimage hf)
    simpa only [Nat.add_assoc, x, S, f, Set.mem_preimage, Fin.val_castLE] using hd
  have hb := geometric_recursion_bound x (1 + η ^ 2 * P.radius ^ 2)
    (P.noiseScale ^ 2 * (P.dimension + 1) * (P.noise.law : Measure P.noise.Ω).real S) B
    (by nlinarith [mul_nonneg (sq_nonneg η) (sq_nonneg P.radius)]) (by positivity) (fun j _ => hs j)
  simpa only [x, Nat.add_zero] using hb
lemma tested_block_energy_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 ≤ η) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (t B : ℕ) (A : Set (Fin t → Weights P.dimension)) (hA : MeasurableSet A)
    (hB : B * (η ^ 2 * P.radius ^ 2) ≤ 3) :
    let S := {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A}
    (∫ ω, S.indicator (fun ω => ‖(trajectory P data η ω ((P.count : ℕ) * (t + B))).point‖ ^ 2) ω
      ∂(P.noise.law : Measure P.noise.Ω)) ≤
    32 * ((∫ ω, S.indicator (fun ω => ‖(trajectory P data η ω ((P.count : ℕ) * t)).point‖ ^ 2) ω
      ∂(P.noise.law : Measure P.noise.Ω)) +
        B * (P.noiseScale ^ 2 * (P.dimension + 1) * (P.noise.law : Measure P.noise.Ω).real S)) := by
  have hg := tested_block_energy_growth P data η h hη hR t B A hA
  have he := exponential_block_factor (η ^ 2 * P.radius ^ 2) B (by positivity) hB
  apply hg.trans
  apply mul_le_mul_of_nonneg_right he
  apply add_nonneg
  · exact integral_nonneg fun ω => Set.indicator_nonneg (fun ω _ => sq_nonneg _) ω
  · positivity
lemma trial_growth_tuning (n : ℕ+) (η δ R : ℝ) (hη : 0 < η) (hδ : 0 < δ)
    (htune : 8 * ((n : ℝ) + 1) * η * R ^ 2 = δ)
    (hk : η ^ 2 * R ^ 2 ≤ 1 / 256) :
    ((⌈16 * (n : ℝ) / (η * δ)⌉₊ + 2 : ℕ) : ℝ) * (η ^ 2 * R ^ 2) ≤ 3 := by
  have hden : 0 < η * δ := mul_pos hη hδ
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 16 * (n : ℝ) / (η * δ) by positivity)
  have hm := mul_le_mul_of_nonneg_right hceil.le (show 0 ≤ η ^ 2 * R ^ 2 by positivity)
  have he : (16 * (n : ℝ) / (η * δ)) * (η ^ 2 * R ^ 2) = 2 * (n : ℝ) / ((n : ℝ) + 1) := by
    apply (eq_div_iff (by positivity : (n : ℝ) + 1 ≠ 0)).mpr
    apply (mul_left_cancel₀ hden.ne')
    field_simp
    nlinarith [congrArg (fun x : ℝ => 2 * (n : ℝ) * η * x) htune]
  have hn : 2 * (n : ℝ) / ((n : ℝ) + 1) ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  rw [add_mul, he] at hm
  push_cast
  nlinarith
lemma event_potential_energy_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Public) (data : Data P) (η : ℝ) (w : Ω → Weights P.dimension)
    (hw : MemLp w 2 μ) (hη : 0 ≤ η) (hsmall : η * P.radius ≤ 1 / 16)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (S : Set Ω) (hS : MeasurableSet S) :
    (∫ ω, S.indicator (fun ω => potential data η (w ω).ofLp.1 (w ω).ofLp.2) ω ∂μ) ≤
      2 * (∫ ω, S.indicator (fun ω => ‖w ω‖ ^ 2) ω ∂μ) ∧
    (∫ ω, S.indicator (fun ω => ‖w ω‖ ^ 2) ω ∂μ) ≤
      2 * (∫ ω, S.indicator (fun ω => potential data η (w ω).ofLp.1 (w ω).ofLp.2) ω ∂μ) := by
  have hi := hw.norm.integrable_sq
  have hv := integrable_potential P data η w hw hη hsmall hR
  have hp (ω : Ω) := potential_bounds P data η (w ω).ofLp.1 (w ω).ofLp.2 hη hsmall hR
  have hn (ω : Ω) : ‖w ω‖ ^ 2 = ‖(w ω).ofLp.1‖ ^ 2 + (w ω).ofLp.2 ^ 2 := by
    simpa using WithLp.prod_norm_sq_eq_of_L2 (w ω)
  constructor
  · calc
      _ ≤ ∫ ω, S.indicator (fun ω => 2 * ‖w ω‖ ^ 2) ω ∂μ := by
        apply integral_mono (hv.indicator hS) ((hi.const_mul 2).indicator hS)
        intro ω
        by_cases hs : ω ∈ S
        · simp only [Set.indicator_of_mem hs]
          rw [hn]
          exact (hp ω).2
        · simp only [Set.indicator_of_notMem hs, le_refl]
      _ = _ := by rw [integral_indicator hS, integral_const_mul, ← integral_indicator hS]
  · calc
      _ ≤ ∫ ω, S.indicator (fun ω => 2 * potential data η (w ω).ofLp.1 (w ω).ofLp.2) ω ∂μ := by
        apply integral_mono (hi.indicator hS) ((hv.const_mul 2).indicator hS)
        intro ω
        by_cases hs : ω ∈ S
        · simp only [Set.indicator_of_mem hs]
          rw [hn]
          linarith [(hp ω).1]
        · simp only [Set.indicator_of_notMem hs, le_refl]
      _ = _ := by rw [integral_indicator hS, integral_const_mul, ← integral_indicator hS]
lemma tested_block_potential_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 ≤ η) (hsmall : η * P.radius ≤ 1 / 16) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (t B : ℕ) (A : Set (Fin t → Weights P.dimension)) (hA : MeasurableSet A)
    (hB : B * (η ^ 2 * P.radius ^ 2) ≤ 3) :
    let S := {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A}
    (∫ ω, S.indicator (fun ω => potential data η
      (trajectory P data η ω ((P.count : ℕ) * (t + B))).point.ofLp.1
      (trajectory P data η ω ((P.count : ℕ) * (t + B))).point.ofLp.2) ω
      ∂(P.noise.law : Measure P.noise.Ω)) ≤
    128 * (∫ ω, S.indicator (fun ω => potential data η
      (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.1
      (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2) ω
      ∂(P.noise.law : Measure P.noise.Ω)) +
    64 * B * P.noiseScale ^ 2 * (P.dimension + 1) * (P.noise.law : Measure P.noise.Ω).real S := by
  let S := {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A}
  have hS : MeasurableSet S := hA.preimage (Measurable.of_eval fun j => h.measurable j)
  have hM (k : ℕ) := memLp_batch_point P data η h.measurable (memLp_noise_sample P h) k
  have h0 := event_potential_energy_bounds (P.noise.law : Measure P.noise.Ω) P data η
    (fun ω => (trajectory P data η ω ((P.count : ℕ) * t)).point) (hM t) hη hsmall hR S hS
  have h1 := event_potential_energy_bounds (P.noise.law : Measure P.noise.Ω) P data η
    (fun ω => (trajectory P data η ω ((P.count : ℕ) * (t + B))).point) (hM (t + B)) hη hsmall hR S hS
  have he := tested_block_energy_bound P data η h hη hR t B A hA hB
  dsimp only at he ⊢
  nlinarith [h0.2, h1.1]

end LongTails.Proofs.NoisyBatchQuadraticPerceptronMoments
