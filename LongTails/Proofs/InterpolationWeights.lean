import LongTails.Algorithms.WeakInterpolationDesign
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace LongTails.Proofs.InterpolationWeights

open LongTails.Algorithms.WeakInterpolationDesign

variable {ι : Type*} [Fintype ι]

lemma exists_threshold (L h : ι → ℝ) (M : ℝ) (hL : ∀ i, 0 ≤ L i)
    (hh : ∀ i, 0 < h i) (hM : 0 ≤ M) (hML : M ≤ ∑ i, L i) :
    ∃ c : ℝ, 0 ≤ c ∧ ∑ i, min (L i) (c * h i) = M := by
  classical
  let C := ∑ i, L i / h i
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => div_nonneg (hL i) (hh i).le
  have hsat (i : ι) : L i ≤ C * h i := by
    apply (div_le_iff₀ (hh i)).mp
    exact Finset.single_le_sum (fun j _ => div_nonneg (hL j) (hh j).le) (Finset.mem_univ i)
  let S := fun c : ℝ => ∑ i, min (L i) (c * h i)
  have hs : Continuous S := by unfold S; fun_prop
  have hz : S 0 = 0 := by simp [S, min_eq_right (hL _)]
  have hc : S C = ∑ i, L i := by simp [S, min_eq_left (hsat _)]
  obtain ⟨c, hc', he⟩ := intermediate_value_Icc hC hs.continuousOn
    (show M ∈ Set.Icc (S 0) (S C) by simpa [hz, hc] using And.intro hM hML)
  exact ⟨c, hc'.1, he⟩

lemma robust_curvature (L h z : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) (hh : ∀ i, 0 < h i)
    (hz : ∀ i, z i ≤ L i) (hmass : ∑ i, curvature L h c i ≤ ∑ i, z i) :
    ∑ i, weight L h c i * curvature L h c i ≤ ∑ i, weight L h c i * z i := by
  have hterm (i : ι) : 0 ≤ (weight L h c i - c) * (z i - curvature L h c i) := by
    by_cases hi : L i ≤ c * h i
    · have hw : L i / h i ≤ c := (div_le_iff₀ (hh i)).mpr hi
      simpa [weight, curvature, min_eq_left hi] using
        mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hw) (sub_nonpos.mpr (hz i))
    · simp [weight, curvature, min_eq_right (le_of_not_ge hi), (hh i).ne']
  have hs := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hterm i)
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  linarith [mul_le_mul_of_nonneg_left hmass hc]

lemma scaled_curvature (L h z : ι → ℝ) {c t : ℝ} (hc : 0 ≤ c) (hh : ∀ i, 0 < h i)
    (hz : ∀ i, z i ≤ L i * t)
    (hmass : (∑ i, curvature L h c i) * t ≤ ∑ i, z i) :
    (∑ i, weight L h c i * curvature L h c i) * t ≤ ∑ i, weight L h c i * z i := by
  have hterm (i : ι) :
      0 ≤ (weight L h c i - c) * (z i - curvature L h c i * t) := by
    by_cases hi : L i ≤ c * h i
    · have hw := (div_le_iff₀ (hh i)).mpr hi
      simpa [weight, curvature, min_eq_left hi] using
        mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hw) (sub_nonpos.mpr (hz i))
    · simp [weight, curvature, min_eq_right (le_of_not_ge hi), (hh i).ne']
  have hs := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hterm i)
  simp only [sub_mul, mul_sub, ← mul_assoc, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum] at hs
  linarith [mul_le_mul_of_nonneg_left hmass hc]

lemma noise_identity (L h : ι → ℝ) (c : ℝ) (hh : ∀ i, 0 < h i) :
    ∑ i, weight L h c i ^ 2 * h i = ∑ i, weight L h c i * curvature L h c i := by
  apply Finset.sum_congr rfl
  intro i _
  unfold weight
  field_simp [(hh i).ne']

lemma least_energy (L h z : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) (hh : ∀ i, 0 < h i)
    (hz : ∀ i, z i ≤ L i) (hmass : ∑ i, curvature L h c i ≤ ∑ i, z i) :
    ∑ i, curvature L h c i ^ 2 / h i ≤ ∑ i, z i ^ 2 / h i := by
  have hs := robust_curvature L h z c hc hh hz hmass
  have hterm (i : ι) : 2 * (weight L h c i * z i) ≤
      z i ^ 2 / h i + curvature L h c i ^ 2 / h i := by
    unfold weight
    field_simp [(hh i).ne', hh i]
    nlinarith [sq_nonneg (z i - curvature L h c i)]
  have he (i : ι) : weight L h c i * curvature L h c i = curvature L h c i ^ 2 / h i := by
    unfold weight
    ring
  simp_rw [he] at hs
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  linarith

end LongTails.Proofs.InterpolationWeights
