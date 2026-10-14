import LongTails.Proofs.NearestSetPotential

open Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.NearestSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma frozen_energy_step (v n g : E) (a s ρ Fx Fy Fnew : ℝ)
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hq : a * s ≤ 1)
    (hρ : ρ * s ^ 2 ≤ a * s)
    (hdescent : Fnew ≤ Fy - s ^ 2 / 2 * ‖g‖ ^ 2)
    (haim : Fy + a ^ 2 / 2 * ‖n‖ ^ 2 ≤ ⟪g, n⟫)
    (hweak : Fy - s * ⟪g, v⟫ - ρ * s ^ 2 / 2 * ‖v‖ ^ 2 ≤ Fx) :
    Fnew + 1 / 2 * ‖(1 - a * s) • v + a • n - s • g‖ ^ 2 ≤
      (1 - a * s) * (Fx + 1 / 2 * ‖v + a • n‖ ^ 2) := by
  have haim' := mul_le_mul_of_nonneg_left haim (mul_nonneg ha hs)
  have hweak' := mul_le_mul_of_nonneg_left hweak (sub_nonneg.mpr hq)
  have hρ' := mul_le_mul_of_nonneg_right hρ
    (show 0 ≤ (1 - a * s) * ‖v‖ ^ 2 / 2 by positivity)
  simp only [norm_sub_sq_real, norm_add_sq_real, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, inner_add_left, inner_smul_right,
    real_inner_smul_left]
  rw [← real_inner_comm v g, ← real_inner_comm n g]
  nlinarith only [hdescent, haim', hweak', hρ']

noncomputable def energy (M : Set E) (F : E → ℝ) (a s : ℝ) (x v : E)
    (p : E) : ℝ :=
  F x + 1 / 2 * ‖v + a • (x + s • v - p)‖ ^ 2 +
    (a / s) * divergence M p x (x + s • v)

lemma energy_nonneg {M : Set E} {F : E → ℝ} {a s : ℝ} {x v p : E}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hp : p ∈ M)
    (hnear : infDist (x + s • v) M = ‖x + s • v - p‖) :
    F x ≤ energy M F a s x v p := by
  have hD := divergence_nonneg hp hnear x
  unfold energy
  have hterm : 0 ≤ (a / s) * divergence M p x (x + s • v) := by positivity
  nlinarith [sq_nonneg ‖v + a • (x + s • v - p)‖]

lemma projection_correction {M : Set E} (y z w p P : E) (a s : ℝ)
    (hs : s ≠ 0) (hp : infDist y M = ‖y - p‖)
    (hP : infDist (z + s • w) M = ‖z + s • w - P‖) :
    1 / 2 * ‖w + a • (z + s • w - P)‖ ^ 2 -
        1 / 2 * ‖w + a • (z + s • w - p)‖ ^ 2 =
      -(a / s) * (1 + a * s) * divergence M p (z + s • w) y -
        (a / s) * divergence M P z (z + s • w) +
        (a / s) * divergence M p z y := by
  rw [divergence_eq_dist hp, divergence_eq_dist hP, divergence_eq_dist hp, hP]
  simp only [norm_add_sq_real, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, inner_add_left, inner_add_right,
    inner_sub_right, real_inner_smul_left, inner_smul_right]
  rw [real_inner_self_eq_norm_sq]
  rw [← real_inner_comm z w]
  field_simp
  ring

lemma energy_step [ProperSpace E] {M : Set E} (hM : IsClosed M) (hne : M.Nonempty)
    (F : E → ℝ) (x v g p P : E) (a s ρ : ℝ)
    (ha : 0 ≤ a) (hs : 0 < s) (hq : a * s ≤ 1)
    (hρ : ρ * s ^ 2 ≤ a * s)
    (hp : p ∈ M)
    (hnear : infDist (x + s • v) M = ‖x + s • v - p‖)
    (hdescent : F (x + s • v - s ^ 2 • g) ≤
      F (x + s • v) - s ^ 2 / 2 * ‖g‖ ^ 2)
    (haim : F (x + s • v) + a ^ 2 / 2 * ‖x + s • v - p‖ ^ 2 ≤
      ⟪g, x + s • v - p⟫)
    (hweak : F (x + s • v) - s * ⟪g, v⟫ - ρ * s ^ 2 / 2 * ‖v‖ ^ 2 ≤ F x) :
    let z := x + s • v - s ^ 2 • g
    let w := ((1 - a * s) / (1 + a * s)) • (v - s • g)
    infDist (z + s • w) M = ‖z + s • w - P‖ →
    energy M F a s z w P ≤ (1 - a * s) * energy M F a s x v p := by
  dsimp only
  intro hP
  let y := x + s • v
  let z := y - s ^ 2 • g
  let w := ((1 - a * s) / (1 + a * s)) • (v - s • g)
  let Y := z + s • w
  have hden : 1 + a * s ≠ 0 := ne_of_gt (by positivity)
  have hid : w + a • (Y - p) = (1 - a * s) • v + a • (y - p) - s • g := by
    dsimp [Y, z, y, w]
    match_scalars
    all_goals (field_simp <;> ring)
  have hmix : ((1 + a * s) / 2) • Y + ((1 - a * s) / 2) • x = z := by
    dsimp [Y, z, y, w]
    match_scalars
    all_goals (field_simp; ring)
  have hbase := frozen_energy_step v (y - p) g a s ρ (F x) (F y) (F z)
    ha hs.le hq hρ hdescent haim hweak
  have hcor := projection_correction y z w p P a s hs.ne' hnear hP
  change 1 / 2 * ‖w + a • (Y - P)‖ ^ 2 - 1 / 2 * ‖w + a • (Y - p)‖ ^ 2 = _ at hcor
  rw [hid] at hcor
  have hc := (divergence_convex hM hne p y).2 (mem_univ Y) (mem_univ x)
    (show 0 ≤ (1 + a * s) / 2 by positivity)
    (show 0 ≤ (1 - a * s) / 2 by positivity)
    (show (1 + a * s) / 2 + (1 - a * s) / 2 = 1 by ring)
  rw [hmix] at hc
  simp only [smul_eq_mul] at hc
  have hc' := mul_le_mul_of_nonneg_left hc (div_nonneg ha hs.le)
  have hDx := divergence_nonneg hp hnear x
  have hDY := divergence_nonneg hp hnear Y
  have hdropx : 0 ≤ (a / s) * (1 - a * s) * divergence M p x y := by positivity
  have hdropY : 0 ≤ (a / s) * (1 + a * s) * divergence M p Y y := by positivity
  change energy M F a s z w P ≤ (1 - a * s) * energy M F a s x v p
  unfold energy
  change F z + 1 / 2 * ‖w + a • (Y - P)‖ ^ 2 + (a / s) * divergence M P z Y ≤
    (1 - a * s) * (F x + 1 / 2 * ‖v + a • (y - p)‖ ^ 2 +
      (a / s) * divergence M p x y)
  nlinarith only [hbase, hcor, hc', hdropx, hdropY]

end OracleTemplate.NearestSet
