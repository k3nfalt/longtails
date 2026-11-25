import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Filter.Basic

open scoped BigOperators Topology

namespace LongTails.Proofs.NcConcaveProx

lemma deriv_nonneg_of_min {g : ℝ → ℝ} {g' : ℝ} (hd : HasDerivAt g g' 0)
    (hmin : ∀ t, 0 < t → t ≤ 1 → g 0 ≤ g t) : 0 ≤ g' := by
  have ht := hd.tendsto_slope_zero_right
  apply ge_of_tendsto ht
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    exact ht.2.le
  filter_upwards [hev, self_mem_nhdsWithin] with t ht1 ht0
  have h0 : (0 : ℝ) < t := ht0
  have := hmin t h0 ht1
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr h0.le) (by linarith)

lemma ball_normal {ι : Type*} [Fintype ι] (v p : ι → ℝ) {R : ℝ} (hR : 0 < R)
    (hp : ∑ i, p i ^ 2 ≤ R ^ 2)
    (hvi : ∀ z : ι → ℝ, ∑ i, z i ^ 2 ≤ R ^ 2 → 0 ≤ ∑ i, v i * (z i - p i)) :
    ∃ l : ℝ, 0 ≤ l ∧ (∀ i, v i = -(l * p i)) ∧ (0 < l → ∑ i, p i ^ 2 = R ^ 2) := by
  by_cases hv : ∀ i, v i = 0
  · exact ⟨0, le_rfl, fun i => by simp [hv i], fun h => absurd h (lt_irrefl _)⟩
  push Not at hv
  set V := ∑ i, v i ^ 2 with hVdef
  set P := ∑ i, p i ^ 2 with hPdef
  set C := ∑ i, v i * p i with hCdef
  have hV : 0 < V := by
    obtain ⟨i, hi⟩ := hv
    have : v i ^ 2 ≤ V := Finset.single_le_sum (f := fun j => v j ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
    have : 0 < v i ^ 2 := by positivity
    linarith
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hsV2 : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV.le
  have hsq : ∀ i, (-(R / Real.sqrt V) * v i) ^ 2 = (R / Real.sqrt V) ^ 2 * v i ^ 2 :=
    fun i => by ring
  have htest := hvi (fun i => -(R / Real.sqrt V) * v i) (by
    simp only [hsq]
    rw [← Finset.mul_sum, div_pow, hsV2, ← hVdef, div_mul_cancel₀ _ hV.ne'])
  have hval : ∑ i, v i * (-(R / Real.sqrt V) * v i - p i) = -(R / Real.sqrt V) * V - C := by
    simp only [mul_sub, Finset.sum_sub_distrib, hCdef, hVdef, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl fun i _ => by ring
  rw [hval] at htest
  have hRV : R / Real.sqrt V * V = R * Real.sqrt V := by
    rw [show R / Real.sqrt V * V = R * (V / Real.sqrt V) by ring, Real.div_sqrt]
  have hRs : 0 < R * Real.sqrt V := mul_pos hR hsV
  have hC1 : C ≤ -(R * Real.sqrt V) := by
    have : -(R / Real.sqrt V) * V = -(R * Real.sqrt V) := by rw [neg_mul, hRV]
    linarith
  have hCS : C ^ 2 ≤ V * P := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hRV2 : (R * Real.sqrt V) ^ 2 = R ^ 2 * V := by rw [mul_pow, hsV2]
  have hC2 : (R * Real.sqrt V) ^ 2 ≤ C ^ 2 := by
    have h0 : 0 ≤ -C - R * Real.sqrt V := by linarith
    nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ -C + R * Real.sqrt V)]
  have hP : P = R ^ 2 := by
    have h2 : R ^ 2 * V ≤ V * P := by rw [← hRV2]; exact hC2.trans hCS
    have h3 : R ^ 2 ≤ P := by
      by_contra hc; push Not at hc
      have := mul_lt_mul_of_pos_left hc hV
      linarith
    linarith
  have hC : C = -(R * Real.sqrt V) := by
    have h5 : C ^ 2 ≤ (R * Real.sqrt V) ^ 2 := by rw [hRV2, ← hP]; linarith [hCS]
    have h6 : -(R * Real.sqrt V) ≤ C := by
      by_contra hc; push Not at hc
      have h0 : 0 < -C - R * Real.sqrt V := by linarith
      nlinarith [mul_pos h0 (by linarith : (0 : ℝ) < -C + R * Real.sqrt V)]
    linarith
  set l := Real.sqrt V / R with hl
  refine ⟨l, by positivity, ?_, fun _ => hP⟩
  have hsum : ∑ i, (v i + l * p i) ^ 2 = 0 := by
    have e : ∑ i, (v i + l * p i) ^ 2 = V + 2 * l * C + l ^ 2 * P := by
      simp only [hVdef, hCdef, hPdef, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, hP, hC, hl]
    have hR0 : R ≠ 0 := hR.ne'
    field_simp
    rw [hsV2]; ring
  intro i
  have hi : (v i + l * p i) ^ 2 = 0 := by
    have := Finset.single_le_sum (f := fun j => (v j + l * p j) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
    nlinarith [sq_nonneg (v i + l * p i)]
  have := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hi
  linarith

lemma approx_prox {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : Set E}
    (hX : Convex ℝ X) {h hh : E → ℝ} {η L : ℝ} (hL : 0 < L)
    (hclose : ∀ z ∈ X, |hh z - h z| ≤ η)
    (hstrong : ∀ z ∈ X, ∀ w ∈ X,
      hh ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w) ≤ hh z / 2 + hh w / 2 - L / 8 * ‖z - w‖ ^ 2)
    {p pp : E} (hp : p ∈ X) (hpp : pp ∈ X) (hpmin : ∀ z ∈ X, h p ≤ h z)
    (hppmin : ∀ z ∈ X, hh pp ≤ hh z) : ‖p - pp‖ ^ 2 ≤ 8 * η / L := by
  have hm : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • pp ∈ X :=
    hX hp hpp (by norm_num) (by norm_num) (by norm_num)
  have h1 := hstrong p hp pp hpp
  have h2 := hppmin _ hm
  have h3 := hpmin pp hpp
  have c1 := abs_le.mp (hclose p hp)
  have c2 := abs_le.mp (hclose pp hpp)
  rw [le_div_iff₀ hL]
  nlinarith

end LongTails.Proofs.NcConcaveProx
