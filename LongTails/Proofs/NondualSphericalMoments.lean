import LongTails.Proofs.WeightedSphericalMoments
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

open MeasureTheory Metric
open scoped RealInnerProductSpace

namespace LongTails.Proofs.NondualSphericalMoments

open OracleTemplate.ZerothOrder

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0 : E) 1
local notation "Q" => (sphereLaw E : Measure S)

lemma direction_even_moment_bound (a : E) (ha : ‖a‖ = 1) (k : ℕ) :
    (d : ℝ) ^ k * (∫ u : S, ⟪a, (u : E)⟫ ^ (2 * k) ∂Q) ≤
      2 ^ k * (k.factorial : ℝ) := by
  let i : Fin d := ⟨0, NeZero.pos d⟩
  let v : E := EuclideanSpace.single i 1
  have hv : ‖v‖ = 1 := by simp [v]
  let e : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (v - a))ᗮ.reflection
  have he : e v = a := Submodule.reflection_sub (hv.trans ha.symm)
  have h := sphereLaw_integral_rotate E e (fun u : S => ⟪a, (u : E)⟫ ^ (2 * k))
  have hid (u : S) : ⟪a, (sphereRotate e u : E)⟫ = (u : E) i := by
    change ⟪a, e (u : E)⟫ = _
    rw [← he, e.inner_map_map]
    simp [v, PiLp.inner_apply]
  simp_rw [hid] at h
  rw [← h]
  exact WeightedSphericalMoments.sphere_even_moment_bound i k

lemma maximum_moment_bound {ι : Type*} (s : Finset ι) (a : ι → E)
    (ha : ∀ i ∈ s, ‖a i‖ = 1) (b : E → ℝ) (hb : Continuous b)
    (hb0 : ∀ x, 0 ≤ b x) (k : ℕ)
    (hbk : ∀ u : S, b u ^ k ≤ ∑ i ∈ s, ⟪a i, (u : E)⟫ ^ (2 * k)) :
    (d : ℝ) ^ k * (∫ u : S, b u ∂Q) ^ k ≤
      (s.card : ℝ) * (2 ^ k * (k.factorial : ℝ)) := by
  have hi : Integrable (fun u : S => b u) Q := sphere_integrable_continuous hb
  have hip : Integrable (fun u : S => b u ^ k) Q :=
    sphere_integrable_continuous (hb.pow k)
  have hj : (∫ u : S, b u ∂Q) ^ k ≤ ∫ u : S, b u ^ k ∂Q :=
    (convexOn_pow k).map_integral_le (by fun_prop) isClosed_Ici
      (Filter.Eventually.of_forall fun u => hb0 u) hi hip
  have hai (i : ι) : Integrable (fun u : S => ⟪a i, (u : E)⟫ ^ (2 * k)) Q :=
    sphere_integrable_continuous (f := fun x : E => ⟪a i, x⟫ ^ (2 * k)) (by fun_prop)
  have hs := integral_mono hip (integrable_finsetSum s (fun i _ => hai i)) hbk
  rw [integral_finsetSum s (fun i _ => hai i)] at hs
  calc
    (d : ℝ) ^ k * (∫ u : S, b u ∂Q) ^ k ≤
        (d : ℝ) ^ k * ∑ i ∈ s, ∫ u : S, ⟪a i, (u : E)⟫ ^ (2 * k) ∂Q :=
      mul_le_mul_of_nonneg_left (hj.trans hs) (by positivity)
    _ = ∑ i ∈ s, (d : ℝ) ^ k * ∫ u : S, ⟪a i, (u : E)⟫ ^ (2 * k) ∂Q :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ _i ∈ s, 2 ^ k * (k.factorial : ℝ) :=
      Finset.sum_le_sum fun i hi => direction_even_moment_bound (a i) (ha i hi) k
    _ = _ := by simp [mul_comm]

lemma maximum_second_moment_bound {ι : Type*} (s : Finset ι) (a : ι → E)
    (ha : ∀ i ∈ s, ‖a i‖ = 1) (b : E → ℝ) (hb : Continuous b)
    (hb0 : ∀ x, 0 ≤ b x) (k : ℕ) (hk : k ≠ 0) (hcard : s.card ≤ 2 ^ k)
    (hbk : ∀ u : S, b u ^ k ≤ ∑ i ∈ s, ⟪a i, (u : E)⟫ ^ (2 * k)) :
    (d : ℝ) * (∫ u : S, b u ∂Q) ≤ 4 * k := by
  have h := maximum_moment_bound s a ha b hb hb0 k hbk
  have hc : (s.card : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hcard
  have hf : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
    exact_mod_cast Nat.factorial_le_pow k
  apply le_of_pow_le_pow_left₀ hk (by positivity)
  calc
    ((d : ℝ) * ∫ u : S, b u ∂Q) ^ k =
        (d : ℝ) ^ k * (∫ u : S, b u ∂Q) ^ k := mul_pow _ _ _
    _ ≤ (s.card : ℝ) * (2 ^ k * (k.factorial : ℝ)) := h
    _ ≤ 2 ^ k * (2 ^ k * (k : ℝ) ^ k) := by gcongr
    _ = (4 * (k : ℝ)) ^ k := by rw [← mul_pow, ← mul_pow]; congr 1; ring

noncomputable def maximumSquare {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → E) (x : E) : ℝ := s.sup' hs (fun i => ⟪a i, x⟫ ^ 2)

omit [NeZero d] in
lemma maximumSquare_continuous {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → E) : Continuous (maximumSquare s hs a) := by
  apply Continuous.finset_sup'_apply
  intro i hi
  fun_prop

omit [NeZero d] in
lemma maximumSquare_nonneg {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → E) (x : E) : 0 ≤ maximumSquare s hs a x := by
  obtain ⟨i, hi⟩ := hs
  exact (sq_nonneg _).trans (Finset.le_sup' (fun j => ⟪a j, x⟫ ^ 2) hi)

omit [NeZero d] in
lemma maximumSquare_pow_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → E) (x : E) (k : ℕ) :
    maximumSquare s hs a x ^ k ≤ ∑ i ∈ s, ⟪a i, x⟫ ^ (2 * k) := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hs (fun j => ⟪a j, x⟫ ^ 2)
  unfold maximumSquare
  rw [he, ← pow_mul]
  exact Finset.single_le_sum (fun j _ => pow_nonneg (sq_nonneg ⟪a j, x⟫) k |>.trans_eq (pow_mul _ 2 k).symm) hi

lemma maximumSquare_integral_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → E) (ha : ∀ i ∈ s, ‖a i‖ = 1)
    (k : ℕ) (hk : k ≠ 0) (hcard : s.card ≤ 2 ^ k) :
    (d : ℝ) * (∫ u : S, maximumSquare s hs a u ∂Q) ≤ 4 * k :=
  maximum_second_moment_bound s a ha _ (maximumSquare_continuous s hs a)
    (maximumSquare_nonneg s hs a) k hk hcard
    (fun u => maximumSquare_pow_le s hs a u k)

omit [NeZero d] in
lemma inner_abs_le_maximumSquare_sqrt {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → E) (x : E) {i : ι} (hi : i ∈ s) :
    |⟪a i, x⟫| ≤ Real.sqrt (maximumSquare s hs a x) := by
  have h := Finset.le_sup' (fun j => ⟪a j, x⟫ ^ 2) hi
  change ⟪a i, x⟫ ^ 2 ≤ maximumSquare s hs a x at h
  have he := Real.sq_sqrt (maximumSquare_nonneg s hs a x)
  have hn := Real.sqrt_nonneg (maximumSquare s hs a x)
  nlinarith [sq_abs ⟪a i, x⟫, abs_nonneg ⟪a i, x⟫]

end LongTails.Proofs.NondualSphericalMoments
