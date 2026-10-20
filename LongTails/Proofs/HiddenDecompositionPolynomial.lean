import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Arcosh

namespace OracleTemplate.HiddenDecompositionPolynomial

open Polynomial
open scoped BigOperators

lemma chebyshev_trace {K : Type*} [Field K] (z : K) (hz : z ≠ 0) (n : ℕ) :
    (Chebyshev.C K (n : ℤ)).eval (z + z⁻¹) = z ^ n + (z⁻¹) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp; ring
  | one => simp
  | more n ih₀ ih₁ =>
    rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega,
      Chebyshev.C_add_two]
    simp only [eval_sub, eval_mul, eval_X]
    rw [← Nat.cast_add_one, ih₁, ih₀]
    simp only [pow_succ]
    field_simp
    ring

noncomputable def tracePolynomial {K : Type*} [Field K] (p : K[X]) : K[X] :=
  ∑ j ∈ Finset.range (p.natDegree + 1), C (p.coeff j) * Chebyshev.C K (j : ℤ)

lemma tracePolynomial_eval {K : Type*} [Field K] (p : K[X]) (z : K) (hz : z ≠ 0) :
    (tracePolynomial p).eval (z + z⁻¹) = p.eval z + p.eval z⁻¹ := by
  simp only [tracePolynomial, eval_finsetSum, eval_mul, eval_C, chebyshev_trace z hz]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← eval_eq_sum_range, ← eval_eq_sum_range]

lemma chebyshev_trace_degree {K : Type*} [Field K] (n : ℕ) :
    (Chebyshev.C K (n : ℤ)).natDegree ≤ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ =>
    rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega,
      Chebyshev.C_add_two, ← Nat.cast_add_one]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_mul_le.trans (Nat.add_le_add natDegree_X_le ih₁)).trans
        (by omega)
    · omega

lemma tracePolynomial_degree {K : Type*} [Field K] (p : K[X]) :
    (tracePolynomial p).natDegree ≤ p.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_C_mul_le _ _).trans
    ((chebyshev_trace_degree i).trans (by simpa using hi))

lemma tracePolynomial_map {K J : Type*} [Field K] [Field J] (f : K →+* J) (p : K[X]) :
    (tracePolynomial p).map f = tracePolynomial (p.map f) := by
  simp [tracePolynomial, Polynomial.map_sum, Polynomial.natDegree_map_eq_of_injective f.injective]

lemma tracePolynomial_eval_complex (p : ℝ[X]) (w : ℝ) (z : ℂ) (hz : z ≠ 0)
    (hw : z + z⁻¹ = (w : ℂ)) :
    (↑((tracePolynomial p).eval w) : ℂ) =
      (p.map Complex.ofRealHom).eval z + (p.map Complex.ofRealHom).eval z⁻¹ := by
  have h := tracePolynomial_eval (p.map Complex.ofRealHom) z hz
  rw [← tracePolynomial_map, hw] at h
  change (map Complex.ofRealHom (tracePolynomial p)).eval (Complex.ofRealHom w) = _ at h
  rw [eval_map_apply] at h
  exact h

lemma interpolation_energy {ι : Type*} (s : Finset ι) (α : ι → ℝ) (v : ι → ℂ)
    (h : ∑ i ∈ s, (α i : ℂ) * v i = 1) :
    1 ≤ (∑ i ∈ s, |α i|) * ∑ i ∈ s, |α i| * ‖v i‖ ^ 2 := by
  have hn : 1 ≤ ∑ i ∈ s, |α i| * ‖v i‖ := by
    calc
      1 = ‖∑ i ∈ s, (α i : ℂ) * v i‖ := by rw [h]; simp
      _ ≤ ∑ i ∈ s, ‖(α i : ℂ) * v i‖ := norm_sum_le _ _
      _ = _ := by simp
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (f := fun i => |α i|) (g := fun i => |α i| * ‖v i‖ ^ 2)
    (r := fun i => |α i| * ‖v i‖)
    (fun i _ => abs_nonneg (α i))
    (fun i _ => mul_nonneg (abs_nonneg (α i)) (sq_nonneg ‖v i‖))
    (fun i _ => by ring_nf; rfl)
  nlinarith

noncomputable def interpolationWeight (n : ℕ) (x : ℝ) (i : ℕ) : ℝ :=
  (Lagrange.basis (Finset.range (n + 1)) (Chebyshev.node n) i).eval x

lemma interpolate_chebyshev_nodes (n : ℕ) (x : ℝ) (p : ℝ[X])
    (hp : p.natDegree ≤ n) :
    p.eval x = ∑ i ∈ Finset.range (n + 1),
      p.eval (Chebyshev.node n i) * interpolationWeight n x i := by
  have hd : p.degree < ((Finset.range (n + 1)).card : ℕ) := by
    rw [Finset.card_range]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast (show p.natDegree < n + 1 by omega))
  have he := congrArg (fun q : ℝ[X] => q.eval x)
    (Lagrange.eq_interpolate (Chebyshev.strictAntiOn_node n).injOn hd)
  simpa only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C,
    interpolationWeight] using he

lemma interpolate_affine_chebyshev_nodes (n : ℕ) (x c r : ℝ) (p : ℝ[X])
    (hp : p.natDegree ≤ n) :
    p.eval (c - r * x) = ∑ i ∈ Finset.range (n + 1),
      p.eval (c - r * Chebyshev.node n i) * interpolationWeight n x i := by
  have hl : (C c - C r * X : ℝ[X]).natDegree ≤ 1 := by compute_degree
  have hd : (p.comp (C c - C r * X)).natDegree ≤ n := by
    exact natDegree_comp_le.trans
      ((Nat.mul_le_mul_left p.natDegree hl).trans (by simpa using hp))
  simpa only [eval_comp, eval_sub, eval_C, eval_mul, eval_X] using
    interpolate_chebyshev_nodes n x (p.comp (C c - C r * X)) hd

lemma interpolationWeight_sign (n i : ℕ) (hi : i ≤ n) (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ (-1 : ℝ) ^ i * interpolationWeight n x i := by
  have hd := Chebyshev.zero_lt_prod_node_sub_node hi
  have hn : 0 ≤ ∏ j ∈ (Finset.range (n + 1)).erase i, (x - Chebyshev.node n j) :=
    Finset.prod_nonneg fun j _ => sub_nonneg.mpr
      (Chebyshev.node_mem_Icc.2.trans hx)
  have hinv : 0 ≤ (-1 : ℝ) ^ i *
      (∏ j ∈ (Finset.range (n + 1)).erase i,
        (Chebyshev.node n i - Chebyshev.node n j))⁻¹ := by
    have h := (inv_pos.mpr hd).le
    simpa only [mul_inv_rev, ← inv_pow, inv_neg, inv_one, mul_comm] using h
  convert mul_nonneg hinv hn using 1
  simp [interpolationWeight, Lagrange.basis, Lagrange.basisDivisor,
    Finset.prod_mul_distrib, eval_prod, mul_comm, mul_left_comm]

lemma interpolationWeight_mass (n : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    ∑ i ∈ Finset.range (n + 1), |interpolationWeight n x i| =
      (Chebyshev.T ℝ (n : ℤ)).eval x := by
  rw [interpolate_chebyshev_nodes n x (Chebyshev.T ℝ (n : ℤ))
    (by simp [Chebyshev.natDegree_T])]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by simpa using hi
  rw [Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr hin)]
  calc
    |interpolationWeight n x i| =
        |(-1 : ℝ) ^ i * interpolationWeight n x i| := by
      rw [abs_mul, abs_neg_one_pow, one_mul]
    _ = _ := abs_of_nonneg (interpolationWeight_sign n i hin x hx)

lemma unit_circle_trace {w : ℝ} (hw₁ : -2 ≤ w) (hw₂ : w ≤ 2) :
    ∃ z : ℂ, z ≠ 0 ∧ z + z⁻¹ = (w : ℂ) ∧ ‖z‖ = 1 := by
  have hr : 0 ≤ 1 - w ^ 2 / 4 := by nlinarith
  let v := Real.sqrt (1 - w ^ 2 / 4)
  let z : ℂ := ⟨w / 2, v⟩
  have hv : v ^ 2 = 1 - w ^ 2 / 4 := Real.sq_sqrt hr
  have hm : z * star z = 1 := by
    apply Complex.ext <;> simp [z, Complex.mul_re, Complex.mul_im] <;> nlinarith
  have hz : z ≠ 0 := by
    intro h
    simp [h] at hm
  have hi : z⁻¹ = star z := by
    exact inv_eq_of_mul_eq_one_right hm
  refine ⟨z, hz, ?_, ?_⟩
  · rw [hi]
    apply Complex.ext <;> simp [z]
  · rw [Complex.norm_def]
    have hn : Complex.normSq z = 1 := by
      simp [Complex.normSq_apply, z]
      nlinarith
    rw [hn, Real.sqrt_one]

lemma real_trace_root {w : ℝ} (hw : 2 ≤ w) :
    ∃ z : ℝ, 1 ≤ z ∧ z + z⁻¹ = w := by
  let v := Real.sqrt (w ^ 2 - 4)
  let z := (w + v) / 2
  have hv : v ^ 2 = w ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
  have hz : 1 ≤ z := by dsimp [z]; linarith [Real.sqrt_nonneg (w ^ 2 - 4)]
  have hm : z * ((w - v) / 2) = 1 := by dsimp [z]; nlinarith
  have hi : z⁻¹ = (w - v) / 2 := inv_eq_of_mul_eq_one_right hm
  exact ⟨z, hz, by rw [hi]; dsimp [z]; ring⟩

lemma real_trace_root_le {z B : ℝ} (hz : 1 ≤ z) (hB : 1 ≤ B)
    (htrace : z + z⁻¹ ≤ B + B⁻¹) :
    z ≤ B := by
  have hz₀ : 0 < z := by linarith
  have hB₀ : 0 < B := by linarith
  have hi : ((z + z⁻¹) - (B + B⁻¹)) * (z * B) = (z - B) * (z * B - 1) := by
    field_simp
    ring
  have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htrace)
    (mul_nonneg hz₀.le hB₀.le)
  rw [hi] at hp
  by_contra h
  have hlt : B < z := lt_of_not_ge h
  have hm : 1 < z * B := by nlinarith
  exact (not_lt_of_ge hp) (mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hm))

def spectralBox (B : ℝ) (z : ℂ) : Prop :=
  -1 ≤ z.re ∧ z.re ≤ B ∧ |z.im| ≤ 1

lemma spectralBox_of_norm_le {B : ℝ} (hB : 1 ≤ B) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    spectralBox B z := by
  have hr := (abs_le.mp ((Complex.abs_re_le_norm z).trans hz))
  exact ⟨hr.1, hr.2.trans hB, (Complex.abs_im_le_norm z).trans hz⟩

lemma box_trace_pair {B w : ℝ} (hB : 1 ≤ B) (hw₁ : -2 ≤ w)
    (hw₂ : w ≤ B + B⁻¹) :
    ∃ z : ℂ, z ≠ 0 ∧ z + z⁻¹ = (w : ℂ) ∧
      spectralBox B z ∧ spectralBox B z⁻¹ := by
  by_cases hw : w ≤ 2
  · obtain ⟨z, hz, ht, hn⟩ := unit_circle_trace hw₁ hw
    refine ⟨z, hz, ht, spectralBox_of_norm_le hB hn.le, ?_⟩
    apply spectralBox_of_norm_le hB
    simp [norm_inv, hn]
  · obtain ⟨z, hz, ht⟩ := real_trace_root (le_of_not_ge hw)
    have hz₀ : 0 < z := by linarith
    have hzB := real_trace_root_le hz hB (ht ▸ hw₂)
    have hi₀ : 0 ≤ z⁻¹ := inv_nonneg.mpr hz₀.le
    have hi₁ : z⁻¹ ≤ 1 := (inv_le_one₀ hz₀).mpr hz
    refine ⟨(z : ℂ), by exact_mod_cast hz₀.ne', ?_, ?_, ?_⟩
    · exact_mod_cast ht
    · exact ⟨by simpa using (show -1 ≤ z by linarith), hzB, by simp⟩
    · simp only [← Complex.ofReal_inv, spectralBox, Complex.ofReal_re, Complex.ofReal_im,
        abs_zero]
      exact ⟨by linarith, hi₁.trans hB, by norm_num⟩

lemma finite_trace_reconstruction (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n)
    (x c r z0 : ℝ) (hz0 : z0 ≠ 0) (h0 : c - r * x = z0 + z0⁻¹)
    (z : ℕ → ℂ) (hz : ∀ i ∈ Finset.range (n + 1), z i ≠ 0)
    (htrace : ∀ i ∈ Finset.range (n + 1),
      z i + (z i)⁻¹ = (↑(c - r * Chebyshev.node n i) : ℂ)) :
    (↑(p.eval z0) : ℂ) =
      (∑ i ∈ Finset.range (n + 1), (interpolationWeight n x i : ℂ) *
        ((p.map Complex.ofRealHom).eval (z i) +
          (p.map Complex.ofRealHom).eval (z i)⁻¹)) - ↑(p.eval z0⁻¹) := by
  have h := interpolate_affine_chebyshev_nodes n x c r (tracePolynomial p)
    ((tracePolynomial_degree p).trans hp)
  rw [h0, tracePolynomial_eval p z0 hz0] at h
  have hc := congrArg (fun a : ℝ => (a : ℂ)) h
  push_cast at hc
  have hn :
      (∑ i ∈ Finset.range (n + 1),
        (↑((tracePolynomial p).eval (c - r * Chebyshev.node n i)) : ℂ) *
          (interpolationWeight n x i : ℂ)) =
      ∑ i ∈ Finset.range (n + 1), (interpolationWeight n x i : ℂ) *
        ((p.map Complex.ofRealHom).eval (z i) +
          (p.map Complex.ofRealHom).eval (z i)⁻¹) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [tracePolynomial_eval_complex p _ (z i) (hz i hi) (htrace i hi), mul_comm]
  rw [hn] at hc
  linear_combination hc

abbrev SpectralIndex (n : ℕ) := Option (Fin (n + 1) × Bool)

noncomputable def spectralCoefficient (n : ℕ) (x : ℝ) : SpectralIndex n → ℝ
  | none => -1
  | some (i, _) => interpolationWeight n x i

noncomputable def tracePoint (n : ℕ) (z0 : ℝ) (z : ℕ → ℂ) : SpectralIndex n → ℂ
  | none => (z0⁻¹ : ℝ)
  | some (i, true) => z i
  | some (i, false) => (z i)⁻¹

lemma spectralCoefficient_mass (n : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    ∑ i : SpectralIndex n, |spectralCoefficient n x i| =
      1 + 2 * (Chebyshev.T ℝ (n : ℤ)).eval x := by
  simp only [SpectralIndex, Fintype.sum_option, spectralCoefficient, abs_neg, abs_one,
    Fintype.sum_prod_type, Fintype.sum_bool]
  rw [show (∑ i : Fin (n + 1),
      (|interpolationWeight n x i| + |interpolationWeight n x i|)) =
      2 * ∑ i ∈ Finset.range (n + 1), |interpolationWeight n x i| by
    simp only [← two_mul, ← Finset.mul_sum]
    rw [← Finset.sum_range (n := n + 1) (fun i => |interpolationWeight n x i|)]]
  rw [interpolationWeight_mass n x hx]

lemma spectral_reconstruction (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n)
    (x c r z0 : ℝ) (hz0 : z0 ≠ 0) (h0 : c - r * x = z0 + z0⁻¹)
    (z : ℕ → ℂ) (hz : ∀ i ∈ Finset.range (n + 1), z i ≠ 0)
    (htrace : ∀ i ∈ Finset.range (n + 1),
      z i + (z i)⁻¹ = (↑(c - r * Chebyshev.node n i) : ℂ)) :
    ∑ i : SpectralIndex n, (spectralCoefficient n x i : ℂ) *
      (p.map Complex.ofRealHom).eval (tracePoint n z0 z i) = ↑(p.eval z0) := by
  have h := finite_trace_reconstruction n p hp x c r z0 hz0 h0 z hz htrace
  have he : (p.map Complex.ofRealHom).eval (↑(z0⁻¹) : ℂ) = ↑(p.eval z0⁻¹) := by
    exact eval_map_apply Complex.ofRealHom _
  simp only [SpectralIndex, Fintype.sum_option, Fintype.sum_prod_type,
    Fintype.sum_bool, spectralCoefficient, tracePoint, Complex.ofReal_neg,
    Complex.ofReal_one, neg_one_mul, he]
  simp_rw [← mul_add]
  rw [← Finset.sum_range (n := n + 1) (fun i =>
    (interpolationWeight n x i : ℂ) *
      ((p.map Complex.ofRealHom).eval (z i) + (p.map Complex.ofRealHom).eval (z i)⁻¹))]
  linear_combination -h

lemma spectral_energy (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n)
    (x c r z0 : ℝ) (hx : 1 ≤ x) (hz0 : z0 ≠ 0)
    (hp0 : p.eval z0 = 1) (h0 : c - r * x = z0 + z0⁻¹)
    (z : ℕ → ℂ) (hz : ∀ i ∈ Finset.range (n + 1), z i ≠ 0)
    (htrace : ∀ i ∈ Finset.range (n + 1),
      z i + (z i)⁻¹ = (↑(c - r * Chebyshev.node n i) : ℂ)) :
    1 ≤ (1 + 2 * (Chebyshev.T ℝ (n : ℤ)).eval x) *
      ∑ i : SpectralIndex n, |spectralCoefficient n x i| *
        ‖(p.map Complex.ofRealHom).eval (tracePoint n z0 z i)‖ ^ 2 := by
  have h := spectral_reconstruction n p hp x c r z0 hz0 h0 z hz htrace
  rw [hp0, Complex.ofReal_one] at h
  have he := interpolation_energy Finset.univ (spectralCoefficient n x)
    (fun i => (p.map Complex.ofRealHom).eval (tracePoint n z0 z i)) h
  rwa [spectralCoefficient_mass n x hx] at he

lemma chebyshev_exp_bound (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (Chebyshev.T ℝ (n : ℤ)).eval x ≤ Real.exp ((n : ℝ) * Real.arcosh x) := by
  have hn : 0 ≤ (n : ℝ) * Real.arcosh x :=
    mul_nonneg (Nat.cast_nonneg _) (Real.arcosh_nonneg hx)
  have ht : (Chebyshev.T ℝ (n : ℤ)).eval x =
      Real.cosh ((n : ℝ) * Real.arcosh x) := by
    simpa only [Real.cosh_arcosh hx, Int.cast_natCast] using
      Chebyshev.T_real_cosh (Real.arcosh x) (n : ℤ)
  rw [ht, Real.cosh_eq]
  have he := Real.exp_le_exp.mpr (show -((n : ℝ) * Real.arcosh x) ≤
    (n : ℝ) * Real.arcosh x by linarith)
  linarith

lemma arcosh_one_add_bound {d : ℝ} (hd : 0 ≤ d) (hd₁ : d ≤ 1) :
    Real.arcosh (1 + d) ≤ 3 * Real.sqrt d := by
  have hr := Real.sqrt_nonneg d
  have hr₂ := Real.sq_sqrt hd
  have hq := Real.sqrt_nonneg ((1 + d) ^ 2 - 1)
  have hq₂ := Real.sq_sqrt (show 0 ≤ (1 + d) ^ 2 - 1 by nlinarith)
  have hd₂ : d ^ 2 ≤ d := by nlinarith
  have hqle : Real.sqrt ((1 + d) ^ 2 - 1) ≤ 2 * Real.sqrt d := by nlinarith
  have hdle : d ≤ Real.sqrt d := by nlinarith
  have hl := Real.log_le_sub_one_of_pos
    (show 0 < 1 + d + Real.sqrt ((1 + d) ^ 2 - 1) by positivity)
  rw [Real.arcosh]
  linarith

lemma extrapolation_geometry {B t : ℝ} (hB : 1 ≤ B) (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    let C := B + B⁻¹
    let d := 2 * t ^ 2 / ((1 + t) * (C + 2))
    0 ≤ d ∧ d ≤ 1 ∧ d ≤ 2 * t ^ 2 / B ∧
      (C - 2) / 2 - (C + 2) / 2 * (1 + d) =
        -(1 + t) + (-(1 + t))⁻¹ := by
  have hB₀ : 0 < B := by linarith
  have ht₀ : 0 < 1 + t := by linarith
  have hC : 0 < B + B⁻¹ + 2 := by positivity
  have hi : 0 ≤ B⁻¹ := inv_nonneg.mpr hB₀.le
  have hden : 2 ≤ (1 + t) * (B + B⁻¹ + 2) := by nlinarith
  have hdenB : B ≤ (1 + t) * (B + B⁻¹ + 2) := by nlinarith
  dsimp only
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · apply (div_le_one (mul_pos ht₀ hC)).mpr
    nlinarith
  · exact div_le_div_of_nonneg_left (by positivity) hB₀ hdenB
  · field_simp
    ring

lemma affine_node_bounds {B : ℝ} (hB : 1 ≤ B) (n i : ℕ) :
    -2 ≤ (B + B⁻¹ - 2) / 2 -
        (B + B⁻¹ + 2) / 2 * Chebyshev.node n i ∧
      (B + B⁻¹ - 2) / 2 -
        (B + B⁻¹ + 2) / 2 * Chebyshev.node n i ≤ B + B⁻¹ := by
  have hn := Chebyshev.node_mem_Icc (n := n) (i := i)
  have hC : 0 ≤ (B + B⁻¹ + 2) / 2 := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hn.1 hC
  have h₂ := mul_le_mul_of_nonneg_left hn.2 hC
  constructor <;> nlinarith

lemma inverse_anchor_box {B t : ℝ} (hB : 1 ≤ B) (ht : 0 ≤ t) :
    spectralBox B (↑((-(1 + t))⁻¹) : ℂ) := by
  apply spectralBox_of_norm_le hB
  rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_neg,
    abs_of_nonneg (by linarith : 0 ≤ 1 + t)]
  exact (inv_le_one₀ (by linarith : 0 < 1 + t)).mpr (by linarith)

lemma normalized_finite_witness (n : ℕ) (B t : ℝ)
    (hB : 1 ≤ B) (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    let x := 1 + 2 * t ^ 2 / ((1 + t) * (B + B⁻¹ + 2))
    ∃ z : ℕ → ℂ,
      (∀ i : SpectralIndex n, spectralBox B (tracePoint n (-(1 + t)) z i)) ∧
      (∀ p : ℝ[X], p.natDegree ≤ n → p.eval (-(1 + t)) = 1 →
        ∑ i : SpectralIndex n, (spectralCoefficient n x i : ℂ) *
          (p.map Complex.ofRealHom).eval (tracePoint n (-(1 + t)) z i) = 1) := by
  dsimp only
  have hnodes := fun i => box_trace_pair hB (affine_node_bounds hB n i).1
    (affine_node_bounds hB n i).2
  choose z hz htrace hbox hinv using hnodes
  refine ⟨z, ?_, ?_⟩
  · intro i
    rcases i with _ | ⟨i, b⟩
    · exact inverse_anchor_box hB ht
    · cases b
      · exact hinv i
      · exact hbox i
  · intro p hp hp0
    have hgeom := extrapolation_geometry hB ht ht₁
    have ha : -(1 + t) ≠ 0 := by linarith
    have h := spectral_reconstruction n p hp _ ((B + B⁻¹ - 2) / 2)
      ((B + B⁻¹ + 2) / 2) (-(1 + t)) ha hgeom.2.2.2 z
      (fun i _ => hz i) (fun i _ => htrace i)
    simpa only [hp0, Complex.ofReal_one] using h

lemma rectangle_finite_witness (n : ℕ) (μ L s : ℝ)
    (hμ : 0 < μ) (hμs : μ ≤ s) (hsL : 4 * s ≤ L) :
    let B := (L - μ - s) / s
    let t := μ / s
    let x := 1 + 2 * t ^ 2 / ((1 + t) * (B + B⁻¹ + 2))
    ∃ spectrum : SpectralIndex n → ℂ,
      (∀ i, μ ≤ (spectrum i).re ∧ (spectrum i).re ≤ L ∧ |(spectrum i).im| ≤ s) ∧
      (∀ p : ℝ[X], p.natDegree ≤ n → p.eval 0 = 1 →
        ∑ i : SpectralIndex n, (spectralCoefficient n x i : ℂ) *
          (p.map Complex.ofRealHom).eval (spectrum i) = 1) := by
  let B := (L - μ - s) / s
  let t := μ / s
  have hs : 0 < s := hμ.trans_le hμs
  have hB : 1 ≤ B := by
    dsimp [B]
    apply (le_div_iff₀ hs).mpr
    nlinarith
  have ht : 0 ≤ t := div_nonneg hμ.le hs.le
  have ht₁ : t ≤ 1 := (div_le_one hs).mpr hμs
  obtain ⟨z, hbox, hreconstruct⟩ := normalized_finite_witness n B t hB ht ht₁
  let spectrum := fun i : SpectralIndex n =>
    (↑(μ + s) : ℂ) + (s : ℂ) * tracePoint n (-(1 + t)) z i
  refine ⟨spectrum, ?_, ?_⟩
  · intro i
    obtain ⟨hr₁, hr₂, hi⟩ := hbox i
    have he : μ + s + s * B = L := by dsimp [B]; field_simp; ring
    have hl := mul_le_mul_of_nonneg_left hr₁ hs.le
    have hu := mul_le_mul_of_nonneg_left hr₂ hs.le
    have him := mul_le_mul_of_nonneg_left hi hs.le
    dsimp [spectrum]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.mul_im, zero_add, add_zero]
    rw [abs_mul, abs_of_pos hs]
    exact ⟨by linarith, by linarith, by simpa using him⟩
  · intro p hp hp0
    let q := p.comp (C (μ + s) + C s * X)
    have hd : q.natDegree ≤ n := by
      have hl : (C (μ + s) + C s * X : ℝ[X]).natDegree ≤ 1 := by compute_degree
      exact natDegree_comp_le.trans
        ((Nat.mul_le_mul_left p.natDegree hl).trans (by simpa using hp))
    have he : μ + s + s * (-(1 + t)) = 0 := by dsimp [t]; field_simp; ring
    have hq : q.eval (-(1 + t)) = 1 := by
      simp only [q, eval_comp, eval_add, eval_C, eval_mul, eval_X, he, hp0]
    have h := hreconstruct q hd hq
    simpa [q, Polynomial.map_comp, spectrum, B, t] using h

lemma rectangle_extrapolation_bound (μ L s : ℝ)
    (hμ : 0 < μ) (hμs : μ ≤ s) (hsL : 4 * s ≤ L) :
    let B := (L - μ - s) / s
    let t := μ / s
    let d := 2 * t ^ 2 / ((1 + t) * (B + B⁻¹ + 2))
    0 ≤ d ∧ d ≤ 1 ∧ Real.arcosh (1 + d) ≤ 6 * μ / Real.sqrt (L * s) := by
  let B := (L - μ - s) / s
  let t := μ / s
  let d := 2 * t ^ 2 / ((1 + t) * (B + B⁻¹ + 2))
  have hs : 0 < s := hμ.trans_le hμs
  have hL : 0 < L := by linarith
  have hB : 1 ≤ B := by dsimp [B]; apply (le_div_iff₀ hs).mpr; linarith
  have ht : 0 ≤ t := div_nonneg hμ.le hs.le
  have ht₁ : t ≤ 1 := (div_le_one hs).mpr hμs
  have hg := extrapolation_geometry hB ht ht₁
  change 0 ≤ d ∧ d ≤ 1 ∧ Real.arcosh (1 + d) ≤ 6 * μ / Real.sqrt (L * s)
  refine ⟨hg.1, hg.2.1, ?_⟩
  have hD : 0 < L - μ - s := by linarith
  have hhalf : s * L / 2 ≤ s * (L - μ - s) := by
    have hh : L / 2 ≤ L - μ - s := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hh hs.le]
  have hb := div_le_div_of_nonneg_left (show 0 ≤ 2 * μ ^ 2 by positivity)
    (show 0 < s * L / 2 by positivity) hhalf
  have hid : 2 * t ^ 2 / B = 2 * μ ^ 2 / (s * (L - μ - s)) := by
    dsimp [t, B]
    field_simp
  have hd : d ≤ 4 * μ ^ 2 / (L * s) := by
    have hh : d ≤ 2 * t ^ 2 / B := hg.2.2.1
    rw [hid] at hh
    have he : 2 * μ ^ 2 / (s * L / 2) = 4 * μ ^ 2 / (L * s) := by ring
    exact hh.trans (he ▸ hb)
  have hsq : Real.sqrt d ≤ 2 * μ / Real.sqrt (L * s) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg d) (by positivity)).mp
    have he : (2 * μ / Real.sqrt (L * s)) ^ 2 = 4 * μ ^ 2 / (L * s) := by
      rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ L * s)]
      ring
    rw [he, Real.sq_sqrt (show 0 ≤ d from hg.1)]
    exact hd
  have ha := arcosh_one_add_bound hg.1 hg.2.1
  change Real.arcosh (1 + d) ≤ 3 * Real.sqrt d at ha
  calc
    _ ≤ 3 * (2 * μ / Real.sqrt (L * s)) :=
      ha.trans (mul_le_mul_of_nonneg_left hsq (by norm_num))
    _ = _ := by ring

lemma rectangle_mass_bound (n : ℕ) (μ L s : ℝ)
    (hμ : 0 < μ) (hμs : μ ≤ s) (hsL : 4 * s ≤ L) :
    let B := (L - μ - s) / s
    let t := μ / s
    let x := 1 + 2 * t ^ 2 / ((1 + t) * (B + B⁻¹ + 2))
    ∑ i : SpectralIndex n, |spectralCoefficient n x i| ≤
      3 * Real.exp (6 * (n : ℝ) * μ / Real.sqrt (L * s)) := by
  let B := (L - μ - s) / s
  let t := μ / s
  let d := 2 * t ^ 2 / ((1 + t) * (B + B⁻¹ + 2))
  have hg := rectangle_extrapolation_bound μ L s hμ hμs hsL
  change 0 ≤ d ∧ d ≤ 1 ∧ Real.arcosh (1 + d) ≤ 6 * μ / Real.sqrt (L * s) at hg
  change ∑ i : SpectralIndex n, |spectralCoefficient n (1 + d) i| ≤ _
  have hx : 1 ≤ 1 + d := by linarith [hg.1]
  have ht := chebyshev_exp_bound n hx
  have he : (n : ℝ) * Real.arcosh (1 + d) ≤
      6 * (n : ℝ) * μ / Real.sqrt (L * s) := by
    convert mul_le_mul_of_nonneg_left hg.2.2 (Nat.cast_nonneg (α := ℝ) n) using 1
    ring
  have hT := ht.trans (Real.exp_le_exp.mpr he)
  have hone : 1 ≤ Real.exp (6 * (n : ℝ) * μ / Real.sqrt (L * s)) :=
    Real.one_le_exp (by positivity)
  rw [spectralCoefficient_mass n (1 + d) hx]
  linarith

lemma spectralCoefficient_mass_pos (n : ℕ) (x : ℝ) :
    0 < ∑ i : SpectralIndex n, |spectralCoefficient n x i| := by
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (SpectralIndex n))) =>
      abs_nonneg (spectralCoefficient n x i))
    (Finset.mem_univ (none : SpectralIndex n))
  have h₁ : 1 ≤ ∑ i : SpectralIndex n, |spectralCoefficient n x i| := by
    simpa only [spectralCoefficient, abs_neg, abs_one] using h
  linarith

lemma normalized_interpolation_energy {ι : Type*} [Fintype ι] (α : ι → ℝ) (v : ι → ℂ)
    (hM : 0 < ∑ i, |α i|) (h : ∑ i, (α i : ℂ) * v i = 1) :
    1 ≤ (∑ i, |α i|) ^ 2 * ∑ i, (|α i| / ∑ j, |α j|) * ‖v i‖ ^ 2 := by
  have he := interpolation_energy Finset.univ α v h
  have hid : (∑ i, |α i|) ^ 2 * ∑ i, (|α i| / ∑ j, |α j|) * ‖v i‖ ^ 2 =
      (∑ i, |α i|) * ∑ i, |α i| * ‖v i‖ ^ 2 := by
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
    field_simp
  rw [hid]
  exact he

lemma finite_hard_spectrum (n : ℕ) (μ L s : ℝ)
    (hμ : 0 < μ) (hμs : μ ≤ s) (hsL : 4 * s ≤ L) :
    ∃ (spectrum : SpectralIndex n → ℂ) (weight : SpectralIndex n → ℝ),
      (∀ i, μ ≤ (spectrum i).re ∧ (spectrum i).re ≤ L ∧ |(spectrum i).im| ≤ s) ∧
      (∀ i, 0 ≤ weight i) ∧ (∑ i, weight i) = 1 ∧
      (∀ p : ℝ[X], p.natDegree ≤ n → p.eval 0 = 1 →
        1 ≤ (3 * Real.exp (6 * (n : ℝ) * μ / Real.sqrt (L * s))) ^ 2 *
          ∑ i, weight i * ‖(p.map Complex.ofRealHom).eval (spectrum i)‖ ^ 2) := by
  let B := (L - μ - s) / s
  let t := μ / s
  let x := 1 + 2 * t ^ 2 / ((1 + t) * (B + B⁻¹ + 2))
  let α := spectralCoefficient n x
  let M := ∑ i : SpectralIndex n, |α i|
  obtain ⟨spectrum, hbox, hrec⟩ := rectangle_finite_witness n μ L s hμ hμs hsL
  have hM : 0 < M := spectralCoefficient_mass_pos n x
  have hbound : M ≤ 3 * Real.exp (6 * (n : ℝ) * μ / Real.sqrt (L * s)) :=
    rectangle_mass_bound n μ L s hμ hμs hsL
  let weight := fun i => |α i| / M
  refine ⟨spectrum, weight, hbox, (fun i => div_nonneg (abs_nonneg _) hM.le), ?_, ?_⟩
  · change (∑ i : SpectralIndex n, |α i| / M) = 1
    rw [← Finset.sum_div]
    exact div_self hM.ne'
  · intro p hp hp0
    have he := normalized_interpolation_energy α
      (fun i => (p.map Complex.ofRealHom).eval (spectrum i)) hM (hrec p hp hp0)
    have hb : M ^ 2 ≤ (3 * Real.exp (6 * (n : ℝ) * μ / Real.sqrt (L * s))) ^ 2 :=
      (sq_le_sq₀ hM.le (by positivity)).mpr hbound
    exact he.trans (mul_le_mul_of_nonneg_right hb
      (Finset.sum_nonneg fun i _ =>
        mul_nonneg (div_nonneg (abs_nonneg _) hM.le) (sq_nonneg _)))

end OracleTemplate.HiddenDecompositionPolynomial
