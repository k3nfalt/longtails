import LongTails.Proofs.GradientOnlyQuasarLocal
import LongTails.Proofs.QuasarPowerBarrier

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GradientOnlyQuasar

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def weightedEnergy (f : E → ℝ) (u : E) (A : ℝ) (y z : E) : ℝ :=
  A * (f y - f u) + ‖z - u‖ ^ 2 / 2

omit [InnerProductSpace ℝ E] in
lemma weightedEnergy_nonneg {f : E → ℝ} {u y z : E} {A : ℝ}
    (hA : 0 ≤ A) (hm : IsMinOn f univ u) : 0 ≤ weightedEnergy f u A y z := by
  have hg : 0 ≤ f y - f u := sub_nonneg.mpr (hm (mem_univ y))
  unfold weightedEnergy
  positivity

lemma weightedEnergy_jump {f : E → ℝ} {u y z g : E} {A L a : ℝ}
    (hA : 0 ≤ A)
    (hd : f (y - (1 / L) • g) ≤ f y - ‖g‖ ^ 2 / (2 * L)) :
    weightedEnergy f u A (y - (1 / L) • g) (z - a • g) ≤
      weightedEnergy f u A y z - A * ‖g‖ ^ 2 / (2 * L) -
        a * ⟪g, z - u⟫ + a ^ 2 * ‖g‖ ^ 2 / 2 := by
  have hz : z - a • g - u = (z - u) - a • g := by module
  unfold weightedEnergy
  rw [hz, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_comm (z - u) g]
  have hh := mul_le_mul_of_nonneg_left hd hA
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith

lemma normalized_energy_power_jump {f : E → ℝ} {u y z g : E} {A L a : ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hA : 0 < A) (hL : 0 < L)
    (hm : IsMinOn f univ u)
    (hd : f (y - (1 / L) • g) ≤ f y - ‖g‖ ^ 2 / (2 * L))
    (ha : 64 * (p : ℝ) ^ 2 * L * a ^ 2 ≤ A)
    (hP : 0 < weightedEnergy f u A y z) :
    (weightedEnergy f u A (y - (1 / L) • g) (z - a • g) /
        weightedEnergy f u A y z) ^ p ≤
      1 - (p : ℝ) * (a * ⟪g, z - u⟫ / weightedEnergy f u A y z) := by
  let P := weightedEnergy f u A y z
  have hP0 : 0 < P := hP
  have hgap : 0 ≤ f y - f u := sub_nonneg.mpr (hm (mem_univ y))
  have hnorm : ‖z - u‖ ^ 2 ≤ 2 * P := by
    dsimp [P, weightedEnergy]
    nlinarith [mul_nonneg hA.le hgap]
  have hg : ‖g‖ ^ 2 ≤ 2 * L * (f y - f u) := by
    have hm' := hm (mem_univ (y - (1 / L) • g))
    change f u ≤ f (y - (1 / L) • g) at hm'
    have hh : ‖g‖ ^ 2 / (2 * L) ≤ f y - f u := by linarith
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 2 * L)).mp hh
  have hu1 : A * ‖g‖ ^ 2 / (2 * L * P) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).2
    have hh := mul_le_mul_of_nonneg_left hg hA.le
    have he : A * (f y - f u) ≤ P := by
      dsimp [P, weightedEnergy]
      nlinarith [sq_nonneg ‖z - u‖]
    nlinarith [mul_le_mul_of_nonneg_left he hL.le]
  have hru : 64 * (p : ℝ) ^ 2 * (a ^ 2 * ‖g‖ ^ 2 / (2 * P)) ≤
      A * ‖g‖ ^ 2 / (2 * L * P) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * L * P)).2
    have he : 64 * (p : ℝ) ^ 2 * (a ^ 2 * ‖g‖ ^ 2 / (2 * P)) * (2 * L * P) =
        (64 * (p : ℝ) ^ 2 * L * a ^ 2) * ‖g‖ ^ 2 := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right ha (sq_nonneg ‖g‖)
  have hi : ⟪g, z - u⟫ ^ 2 ≤ ‖g‖ ^ 2 * ‖z - u‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg ⟪g, z - u⟫)
      (abs_real_inner_le_norm g (z - u)) 2
    simpa [sq_abs, mul_pow] using hh
  have hb : (a * ⟪g, z - u⟫ / P) ^ 2 ≤ 4 * (a ^ 2 * ‖g‖ ^ 2 / (2 * P)) := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hP0)).2
    have he : 4 * (a ^ 2 * ‖g‖ ^ 2 / (2 * P)) * P ^ 2 =
        2 * a ^ 2 * ‖g‖ ^ 2 * P := by field_simp; ring
    rw [he, mul_pow]
    have hh := mul_le_mul_of_nonneg_left hi (sq_nonneg a)
    have hn := mul_le_mul_of_nonneg_left hnorm
      (show 0 ≤ a ^ 2 * ‖g‖ ^ 2 by positivity)
    nlinarith
  have hj := weightedEnergy_jump (u := u) (z := z) (a := a) hA.le hd
  have hsu : weightedEnergy f u A (y - (1 / L) • g) (z - a • g) / P ≤
      1 - A * ‖g‖ ^ 2 / (2 * L * P) - a * ⟪g, z - u⟫ / P +
        a ^ 2 * ‖g‖ ^ 2 / (2 * P) := by
    apply (div_le_iff₀ hP0).2
    change _ ≤ P - A * ‖g‖ ^ 2 / (2 * L) - a * ⟪g, z - u⟫ +
      a ^ 2 * ‖g‖ ^ 2 / 2 at hj
    convert hj using 1
    field_simp
  exact power_jump_bound hp (by positivity) hu1 (by positivity) hru hb
    (div_nonneg (weightedEnergy_nonneg hA.le hm) hP0.le) hsu

lemma weightedEnergy_zero_jump {f : E → ℝ} {u y z g : E} {A L a : ℝ}
    (hA : 0 < A) (hL : 0 < L) (hm : IsMinOn f univ u)
    (hd : f (y - (1 / L) • g) ≤ f y - ‖g‖ ^ 2 / (2 * L))
    (hP : weightedEnergy f u A y z = 0) :
    g = 0 ∧ weightedEnergy f u A (y - (1 / L) • g) (z - a • g) = 0 := by
  have hgap : 0 ≤ f y - f u := sub_nonneg.mpr (hm (mem_univ y))
  have hz : f y - f u = 0 := by
    unfold weightedEnergy at hP
    nlinarith [sq_nonneg ‖z - u‖]
  have hm' := hm (mem_univ (y - (1 / L) • g))
  change f u ≤ f (y - (1 / L) • g) at hm'
  have hg : ‖g‖ ^ 2 / (2 * L) ≤ 0 := by linarith
  have hg' := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp hg
  have hg0 : g = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg g]
  refine ⟨hg0, ?_⟩
  simpa only [hg0, smul_zero, sub_zero] using hP

lemma weightedEnergy_flow_bound {f : E → ℝ} {u y z g : E} {γ a : ℝ}
    (ha : 0 ≤ a) (hq : γ * (f y - f u) ≤ ⟪g, y - u⟫) :
    γ * a * (f y - f u) + a * ⟪g, z - y⟫ ≤ a * ⟪g, z - u⟫ := by
  have hh := mul_le_mul_of_nonneg_left hq ha
  have hi : ⟪g, z - y⟫ + ⟪g, y - u⟫ = ⟪g, z - u⟫ := by
    simp only [inner_sub_right]
    ring
  nlinarith

lemma energy_barrier_generator {f : E → ℝ} {u y z g : E} {A L a γ B : ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hA : 0 < A) (hL : 0 < L) (hB : 0 < B) (ha : 0 ≤ a)
    (hm : IsMinOn f univ u) (hq : γ * (f y - f u) ≤ ⟪g, y - u⟫)
    (hd : weightedEnergy f u A y z ≤ B →
      f (y - (1 / L) • g) ≤ f y - ‖g‖ ^ 2 / (2 * L))
    (htune : 64 * (p : ℝ) ^ 2 * L * a ^ 2 ≤ A) :
    barrierSlope ((weightedEnergy f u A y z / B) ^ p) *
      ((p : ℝ) * (weightedEnergy f u A y z / B) ^ (p - 1) *
        ((γ * a * (f y - f u) + a * ⟪g, z - y⟫) / B)) +
      barrier ((weightedEnergy f u A (y - (1 / L) • g) (z - a • g) / B) ^ p) -
      barrier ((weightedEnergy f u A y z / B) ^ p) ≤ 0 := by
  let P := weightedEnergy f u A y z
  have hP0 : 0 ≤ P := weightedEnergy_nonneg hA.le hm
  by_cases hPB : P ≤ B
  · rcases eq_or_lt_of_le hP0 with hzero | hpos
    · have hz := weightedEnergy_zero_jump (a := a) hA hL hm (hd hPB) hzero.symm
      have hgap : 0 ≤ f y - f u := sub_nonneg.mpr (hm (mem_univ y))
      have hgap0 : f y - f u = 0 := by
        dsimp [P, weightedEnergy] at hzero
        nlinarith [sq_nonneg ‖z - u‖]
      rw [hz.2, show weightedEnergy f u A y z = 0 from hzero.symm]
      simp [hz.1, hgap0, barrier, show p ≠ 0 by omega]
    · apply barrier_generator
      apply rescaled_power_drift hp hpos hB
        (b := a * ⟪g, z - u⟫ / P)
      · have hf := weightedEnergy_flow_bound (z := z) ha hq
        convert hf using 1
        field_simp
      · exact normalized_energy_power_jump hp hA hL hm (hd hPB) htune hpos
  · have hq1 : 1 ≤ (P / B) ^ p := by
      apply one_le_pow₀
      exact (le_div_iff₀ hB).2 (by linarith)
    change barrierSlope ((P / B) ^ p) * _ + _ - barrier ((P / B) ^ p) ≤ 0
    rw [barrier_eq_one hq1]
    have hs : barrierSlope ((P / B) ^ p) = 0 := by
      simp [barrierSlope, max_eq_left (sub_nonpos.mpr hq1)]
    rw [hs, zero_mul, zero_add]
    linarith [barrier_le_one
      ((weightedEnergy f u A (y - (1 / L) • g) (z - a • g) / B) ^ p)]

end

end OracleTemplate.GradientOnlyQuasar
