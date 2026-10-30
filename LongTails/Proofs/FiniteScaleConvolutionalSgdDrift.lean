import LongTails.Proofs.FiniteScaleConvolutionalSgdDynamics

namespace LongTails.Proofs.FiniteScaleConvolutionalSgdDrift

open scoped RealInnerProductSpace
open ManySampleConvolutionalPerceptronDynamics (State)
open FiniteScaleConvolutionalSgdDynamics
open SoftQuadraticDynamics (weight)

lemma pre_hitting_drift_algebra (N W ρ d ζ S B total : ℝ)
    (hN : 1 ≤ N) (hW : 0 ≤ W) (hd : 0 ≤ d) (hd₁ : d ≤ 1)
    (hζ : ζ ≤ d) (hB : 1 / 4 ≤ B) (hS : S ≤ 2 * N * B)
    (hfloor : 1000 * N * d ≤ ρ ^ 2 * W)
    (hstep : total ≤ N * W - ρ ^ 2 * W * B / 3 +
      36 * d * S + 3 * d ^ 2 * B + 5 * N * ζ) :
    total ≤ N * W - ρ ^ 2 * W / 24 := by
  have hN₀ : 0 ≤ N := by linarith
  have hB₀ : 0 ≤ B := by linarith
  have h₁ : 36 * d * S ≤ 72 * N * d * B := by
    have hh := mul_le_mul_of_nonneg_left hS (show 0 ≤ 36 * d by positivity)
    nlinarith
  have h₂ : 3 * d ^ 2 * B ≤ 3 * N * d * B := by
    have hh : d ^ 2 ≤ N * d := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hh hB₀
    nlinarith
  have h₃ : 5 * N * ζ ≤ 20 * N * d * B := by
    have hh := mul_le_mul_of_nonneg_left hζ (show 0 ≤ 5 * N by positivity)
    have hm := mul_le_mul_of_nonneg_left hB (show 0 ≤ 20 * N * d by positivity)
    nlinarith
  have h₄ := mul_le_mul_of_nonneg_right hfloor hB₀
  have h₅ := mul_le_mul_of_nonneg_left hB (show 0 ≤ ρ ^ 2 * W by positivity)
  nlinarith

lemma sum_mean_contraction {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (z c : ι → ℝ) (p r : ι → E) (x : State E) (δ ρ H ζ : ℝ)
    (i : ι) (hi : z i ≤ 0) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hζ : 0 ≤ ζ)
    (hcl : ∀ j, ρ ≤ |c j|) (hcu : ∀ j, |c j| ≤ 1 / 4)
    (hp : ∀ j, |⟪p j, x.z⟫| ≤ H) (hr : ∀ j, |⟪r j, x.z⟫| ≤ H)
    (ht : |x.t| ≤ 2) (hW : meanPotential x ≤ 4)
    (hsmall : δ * H ≤ 1) (hthermal : ζ ≤ δ * H)
    (hfloor : 1000 * (Fintype.card ι : ℝ) * (δ * H) ≤ ρ ^ 2 * meanPotential x)
    (hgate : ∀ j, weight (z j) *
      (c j * x.a * x.q + δ * ⟪x.a • p j + x.t • r j, x.z⟫) ≤ ζ) :
    (∑ j, meanPotential (weightedNext (c j) δ (weight (z j)) (p j) (r j) x)) ≤
      (Fintype.card ι : ℝ) * meanPotential x - ρ ^ 2 * meanPotential x / 24 := by
  have hH : 0 ≤ H := (abs_nonneg _).trans (hp i)
  have hN : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩)
  have hB : 1 / 4 ≤ ∑ j, weight (z j) ^ 2 := by
    have hh : weight (z i) ^ 2 ≤ ∑ j, weight (z j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (weight (z j))) (Finset.mem_univ i)
    have hw := SoftQuadraticDynamics.weight_ge_half hi
    nlinarith
  have hS : ∑ j, weight (z j) ≤ 2 * (Fintype.card ι : ℝ) * ∑ j, weight (z j) ^ 2 := by
    have hh := SoftQuadraticDynamics.pre_hitting_weight_comparison z i hi
    have hs : Real.sqrt (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) :=
      Real.sqrt_le_self_iff.mpr (Or.inr hN)
    exact hh.trans (by gcongr)
  have hsqrt : Real.sqrt (meanPotential x) ≤ 2 := by
    have hh := Real.sq_sqrt (mean_potential_nonneg x)
    nlinarith [Real.sqrt_nonneg (meanPotential x)]
  have hnext (j : ι) :
      meanPotential (weightedNext (c j) δ (weight (z j)) (p j) (r j) x) ≤
        meanPotential x - (ρ ^ 2 * meanPotential x / 3) * weight (z j) ^ 2 +
          (36 * (δ * H)) * weight (z j) + (3 * (δ * H) ^ 2) * weight (z j) ^ 2 + 5 * ζ := by
    have hw := (SoftQuadraticDynamics.weight_pos (z j)).le
    have hh := soft_mean_drift (c j) δ (weight (z j)) ρ H ζ (p j) (r j) x
      hδ hw (SoftQuadraticDynamics.weight_le_one (z j)) hρ (hcl j) (hcu j) hζ
      (hp j) (hr j) ht (hgate j)
    have hm := mul_le_mul_of_nonneg_left hsqrt
      (show 0 ≤ 13 * δ * H * weight (z j) by positivity)
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hnext j)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  apply pre_hitting_drift_algebra (Fintype.card ι) (meanPotential x) ρ (δ * H) ζ
    (∑ j, weight (z j)) (∑ j, weight (z j) ^ 2) _ hN (mean_potential_nonneg x)
    (mul_nonneg hδ hH) hsmall hthermal hB hS hfloor
  nlinarith

end LongTails.Proofs.FiniteScaleConvolutionalSgdDrift
