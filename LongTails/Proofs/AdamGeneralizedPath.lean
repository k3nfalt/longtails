import LongTails.Proofs.AdamGeneralizedTrajectory
import LongTails.Proofs.AdamNormalizedMoments

open MeasureTheory

open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdamGeneralizedPath

open OracleTemplate.Adam

lemma norm_le_sqrt_card {d : ℕ} {x : Point d} {C : ℝ} (hC : 0 ≤ C)
    (hx : ∀ i, |x i| ≤ C) : ‖x‖ ≤ Real.sqrt d * C := by
  have hh : ‖x‖ ^ 2 ≤ d * C ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _i : Fin d, C ^ 2 := Finset.sum_le_sum (fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hx i) 2)
      _ = _ := by simp
  have hd := Real.sq_sqrt (Nat.cast_nonneg d)
  have he : (Real.sqrt d * C) ^ 2 = d * C ^ 2 := by rw [mul_pow, hd]
  nlinarith [norm_nonneg x, mul_nonneg (Real.sqrt_nonneg d) hC]

lemma damped_path_squares {d : ℕ} {g v : ℕ → Point d} {τ C : ℝ}
    (hτ : 0 ≤ τ) (hv : ∀ t i, 0 < v (t + 1) i) (n : ℕ)
    (hb : ∀ i, (∑ t ∈ Finset.range n, (g t i) ^ 2 / v (t + 1) i) ≤ C) :
    ∑ t ∈ Finset.range n, ‖direction τ (g t) (v (t + 1))‖ ^ 2 ≤ d * C := by
  simp only [PiLp.norm_sq_eq_of_L2, direction, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i : Fin d, C := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.sum_le_sum (fun t _ => AdamAccumulator.damped_square_le (hv t i) hτ)).trans (hb i)
    _ = _ := by simp

lemma scalar_residual {α r a m d e : ℝ} (hr : 0 ≤ r) (hd : 0 < d) (he : 0 < e)
    (hm : |α * m / d| ≤ a) :
    |α * r * m * (1 / d - 1 / e)| ≤ r * a * |1 - d / e| := by
  have hident : α * r * m * (1 / d - 1 / e) = r * (α * m / d) * (1 - d / e) := by
    field_simp
  rw [hident, abs_mul, abs_mul, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hr) (abs_nonneg _)

lemma vector_residual_sum {d : ℕ} {e : ℕ → Point d} {ratio : ℕ → Fin d → ℝ}
    {r a R : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (n : ℕ)
    (he : ∀ t i, |e t i| ≤ r * a * |1 - ratio t i|)
    (hvariation : ∀ i, (∑ t ∈ Finset.range n, |1 - ratio t i|) ≤ 3 * R) :
    ∑ t ∈ Finset.range n, ‖e t‖ ≤ 3 * r * a * d * R := by
  calc
    _ ≤ ∑ t ∈ Finset.range n, ∑ i : Fin d, r * a * |1 - ratio t i| := by
      apply Finset.sum_le_sum
      intro t _
      exact (AdamNormalizedMoments.norm_le_coordinate_sum _).trans
        (Finset.sum_le_sum (fun i _ => he t i))
    _ = ∑ i : Fin d, r * a * ∑ t ∈ Finset.range n, |1 - ratio t i| := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ _i : Fin d, r * a * (3 * R) := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hvariation i) (mul_nonneg hr ha))
    _ = _ := by simp; ring

lemma gradient_energy_bound {d : ℕ} {g h : ℕ → Point d} {C : ℝ}
    (n : ℕ) (hh : ∀ t < n, ‖h t‖ ≤ C) :
    ∑ t ∈ Finset.range n, ‖g t‖ ^ 2 ≤
      2 * n * C ^ 2 + 2 * ∑ t ∈ Finset.range n, ‖g t - h t‖ ^ 2 := by
  have hp (t : ℕ) (ht : t ∈ Finset.range n) : ‖g t‖ ^ 2 ≤
      2 * C ^ 2 + 2 * ‖g t - h t‖ ^ 2 := by
    have hnorm : ‖g t‖ ≤ ‖h t‖ + ‖g t - h t‖ := by
      have he : g t = h t + (g t - h t) := by abel
      calc ‖g t‖ = ‖h t + (g t - h t)‖ := congrArg norm he
           _ ≤ _ := norm_add_le _ _
    have hs := pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans
      (add_le_add (hh t (Finset.mem_range.1 ht)) le_rfl)) 2
    nlinarith [sq_nonneg (C - ‖g t - h t‖)]
  have hs := Finset.sum_le_sum hp
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_assoc, mul_left_comm] using hs

noncomputable def auxiliaryPoint {d : ℕ} (β η τ : ℝ) (s : Point d × Point d × Point d) : Point d :=
  s.1 - (η * β / (1 - β)) • direction τ s.2.1 s.2.2

noncomputable def residual {d : ℕ} (β η τ : ℝ) (s : Point d × Point d × Point d)
    (w : Point d) : Point d :=
  (η * β / (1 - β)) • (direction τ s.2.1 s.2.2 - direction τ s.2.1 w)

lemma auxiliary_update {d : ℕ} {β η τ : ℝ} (hβ : β ≠ 1) (hτ : 0 ≤ τ)
    (s : Point d × Point d × Point d) (g w : Point d)
    (hv : ∀ i, 0 < s.2.2 i) (hw : ∀ i, 0 < w i) :
    auxiliaryPoint β η τ (s.1 - η • direction τ (β • s.2.1 + (1 - β) • g) w,
      β • s.2.1 + (1 - β) • g, w) =
      auxiliaryPoint β η τ s - η • direction τ g w + residual β η τ s w := by
  apply PiLp.ext
  intro i
  have hvi := hv i
  have hwi := hw i
  have hd : Real.sqrt (s.2.2 i) + τ ≠ 0 := (by positivity : 0 < Real.sqrt (s.2.2 i) + τ).ne'
  have he : Real.sqrt (w i) + τ ≠ 0 := (by positivity : 0 < Real.sqrt (w i) + τ).ne'
  have hh := AdamAccumulator.auxiliary_increment (η := η) (m := s.2.1 i) (g := g i)
    (x := s.1 i) hβ hd he
  simp only [auxiliaryPoint, residual, direction, PiLp.sub_apply, PiLp.smul_apply,
    PiLp.add_apply, smul_eq_mul]
  linear_combination hh

lemma auxiliary_distance {d : ℕ} {β η τ ρ : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hρ : 0 < ρ)
    (s : Point d × Point d × Point d) (hv : ∀ i, 0 < s.2.2 i)
    (hm : ∀ i, ρ * (s.2.1 i) ^ 2 ≤ s.2.2 i) :
    ‖auxiliaryPoint β η τ s - s.1‖ ≤ η * β / (1 - β) * (Real.sqrt d / Real.sqrt ρ) := by
  have hd : ‖direction τ s.2.1 s.2.2‖ ≤ Real.sqrt d / Real.sqrt ρ := by
    have hh := norm_le_sqrt_card (x := direction τ s.2.1 s.2.2) (by positivity : 0 ≤ 1 / Real.sqrt ρ)
      (fun i => AdamAccumulator.momentum_direction_bound hρ (hv i) hτ (hm i))
    simpa only [mul_one_div] using hh
  have hc : 0 ≤ η * β / (1 - β) := by positivity
  have he : auxiliaryPoint β η τ s - s.1 = -(η * β / (1 - β)) • direction τ s.2.1 s.2.2 := by
    dsimp [auxiliaryPoint]
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left hd hc

lemma residual_coordinate {d : ℕ} {β η τ a : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (s : Point d × Point d × Point d) (w : Point d) (i : Fin d)
    (hv : 0 < Real.sqrt (s.2.2 i) + τ) (hw : 0 < Real.sqrt (w i) + τ)
    (hm : |η * s.2.1 i / (Real.sqrt (s.2.2 i) + τ)| ≤ a) :
    |residual β η τ s w i| ≤ β / (1 - β) * a *
      |1 - (Real.sqrt (s.2.2 i) + τ) / (Real.sqrt (w i) + τ)| := by
  have hh := scalar_residual (α := η) (r := β / (1 - β)) (by positivity) hv hw hm
  convert hh using 1; simp only [residual, direction, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul]
  congr 1
  ring

lemma coordinate_accumulator_upper {d : ℕ} {v g : ℕ → Point d} {ρ vinit : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 0 < vinit) (hv0 : ∀ i, v 0 i = vinit)
    (hrec : ∀ t i, v (t + 1) i = (1 - ρ) * v t i + ρ * (g t i) ^ 2)
    (n : ℕ) (i : Fin d) :
    v n i ≤ vinit * (1 + ρ / vinit * ∑ t ∈ Finset.range n, ‖g t‖ ^ 2) := by
  have hh := AdamAccumulator.accumulator_upper (v := fun t => v t i) (g := fun t => g t i) (sub_pos.2 hρ1) (by linarith : 1 - ρ ≤ 1)
    hρ (by rw [hv0 i]; exact hv) (fun t => hrec t i) n
  rw [hv0 i] at hh
  have hs : (∑ t ∈ Finset.range n, (g t i) ^ 2) ≤ ∑ t ∈ Finset.range n, ‖g t‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro t _
    have hn := PiLp.norm_apply_le (g t) i
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  have he : vinit * (1 + ρ / vinit * ∑ t ∈ Finset.range n, ‖g t‖ ^ 2) =
      vinit + ρ * ∑ t ∈ Finset.range n, ‖g t‖ ^ 2 := by field_simp
  rw [he]
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs hρ))

lemma normalized_path_sums {d : ℕ} {g m v : ℕ → Point d} {b ρ τ B : ℝ}
    (hb : 0 ≤ b) (hb1 : b < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hbρ : (1 + b) / 2 ≤ 1 - ρ) (hτ : 0 ≤ τ)
    (hv0 : ∀ i, 0 < v 0 i) (hm0 : m 0 = 0)
    (hm : ∀ t, m (t + 1) = b • m t + (1 - b) • g t)
    (hrec : ∀ t i, v (t + 1) i = (1 - ρ) * v t i + ρ * (g t i) ^ 2)
    (n : ℕ) (hB : 0 < B) (hvn : ∀ i, v n i ≤ v 0 i * B)
    (hlog : -(n : ℝ) * Real.log (1 - ρ) ≤ 2) :
    (∑ t ∈ Finset.range n, ‖direction τ (g t) (v (t + 1))‖ ^ 2) ≤
      d * ((2 + Real.log B) / ρ) ∧
    (∑ t ∈ Finset.range n, ‖direction τ (m (t + 1)) (v (t + 1))‖ ^ 2) ≤
      2 * d * ((2 + Real.log B) / ρ) := by
  have hv (t i) : 0 < v t i := AdamAccumulator.accumulator_pos (v := fun t => v t i) (g := fun t => g t i) (sub_pos.2 hρ1) hρ.le
    (hv0 i) (fun t => hrec t i) t
  have hraw (i) := AdamAccumulator.normalized_square_budget (v := fun t => v t i) (g := fun t => g t i) (sub_pos.2 hρ1) hρ
    (hv0 i) (fun t => hrec t i) n hB (hvn i) hlog
  have hmoment (i) := AdamAccumulator.momentum_ratio_sum (v := fun t => v t i) (g := fun t => g t i) (m := fun t => m t i) hb hb1 (sub_pos.2 hρ1) hbρ hρ.le
    (hv0 i) (by simp [hm0] : m 0 i = 0)
    (fun t => by simp only [hm t, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul])
    (fun t => hrec t i) n
  have hm' : ∀ i, (∑ t ∈ Finset.range n, (m (t + 1) i) ^ 2 / v (t + 1) i) ≤
      2 * ((2 + Real.log B) / ρ) := fun i => (hmoment i).trans
        (mul_le_mul_of_nonneg_left (hraw i) (by norm_num))
  refine ⟨damped_path_squares hτ (fun t i => hv (t + 1) i) n hraw, ?_⟩
  have hh := damped_path_squares hτ (fun t i => hv (t + 1) i) n hm'
  convert hh using 1; ring

lemma preceding_path_sum {d : ℕ} (m v : ℕ → Point d) (τ : ℝ) (hm0 : m 0 = 0) (n : ℕ) :
    (∑ t ∈ Finset.range n, ‖direction τ (m t) (v t)‖ ^ 2) ≤
      ∑ t ∈ Finset.range n, ‖direction τ (m (t + 1)) (v (t + 1))‖ ^ 2 := by
  have hh := Finset.sum_range_succ' (fun t => ‖direction τ (m t) (v t)‖ ^ 2) n
  rw [Finset.sum_range_succ] at hh
  have hz : direction τ (m 0) (v 0) = 0 := by
    apply PiLp.ext
    intro i
    simp [direction, hm0]
  rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hh
  linarith [sq_nonneg ‖direction τ (m n) (v n)‖]

lemma auxiliary_path_sum {d : ℕ} (s : ℕ → Point d × Point d × Point d)
    (β η τ : ℝ) (n : ℕ) {C : ℝ} (hm0 : (s 0).2.1 = 0)
    (hpath : (∑ t ∈ Finset.range n, ‖direction τ (s (t + 1)).2.1 (s (t + 1)).2.2‖ ^ 2) ≤ C) :
    (∑ t ∈ Finset.range n, ‖auxiliaryPoint β η τ (s t) - (s t).1‖ ^ 2) ≤
      (η * β / (1 - β)) ^ 2 * C := by
  have he (t) : ‖auxiliaryPoint β η τ (s t) - (s t).1‖ ^ 2 =
      (η * β / (1 - β)) ^ 2 * ‖direction τ (s t).2.1 (s t).2.2‖ ^ 2 := by
    have hvec : auxiliaryPoint β η τ (s t) - (s t).1 =
        -(η * β / (1 - β)) • direction τ (s t).2.1 (s t).2.2 := by
      dsimp [auxiliaryPoint]
      module
    rw [hvec, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq]
  simp only [he, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact (preceding_path_sum (fun t => (s t).2.1) (fun t => (s t).2.2) τ hm0 n).trans hpath

lemma residual_path_sum {d : ℕ} (s : ℕ → Point d × Point d × Point d)
    {β η τ ρ B : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (hη : 0 ≤ η)
    (hτ : 0 ≤ τ) (hρ : 0 < ρ) (hρq : 1 / 4 ≤ 1 - ρ)
    (hv : ∀ t i, 0 < (s t).2.2 i)
    (hm : ∀ t i, ρ * ((s t).2.1 i) ^ 2 ≤ (s t).2.2 i)
    (hdecay : ∀ t i, (1 - ρ) * (s t).2.2 i ≤ (s (t + 1)).2.2 i)
    (n : ℕ) (hB : 1 ≤ B) (hvn : ∀ i, (s n).2.2 i ≤ (s 0).2.2 i * B)
    (hlog : -(n : ℝ) * Real.log (1 - ρ) ≤ 2) :
    (∑ t ∈ Finset.range n, ‖residual β η τ (s t) (s (t + 1)).2.2‖) ≤
      3 * (β / (1 - β)) * (η / Real.sqrt ρ) * d * (2 + Real.log B) := by
  have hd (t i) : 0 < Real.sqrt ((s t).2.2 i) + τ := by
    have hh := hv t i
    positivity
  apply vector_residual_sum (by positivity : 0 ≤ β / (1 - β)) (by positivity) n
  · intro t i
    apply residual_coordinate hβ hβ1 (s t) (s (t + 1)).2.2 i (hd t i) (hd (t + 1) i)
    have hh := AdamAccumulator.momentum_direction_bound hρ (hv t i) hτ (hm t i)
    rw [mul_div_assoc, abs_mul, abs_of_nonneg hη]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hh hη
  · intro i
    exact AdamAccumulator.damped_variation_sum hρq (by linarith) hτ (fun t => hv t i)
      (fun t => hdecay t i) n hB (hvn i) hlog

lemma direction_norm_bound {d : ℕ} {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 ≤ τ)
    (m v : Point d) (hv : ∀ i, 0 < v i) (hm : ∀ i, ρ * (m i) ^ 2 ≤ v i) :
    ‖direction τ m v‖ ≤ Real.sqrt d / Real.sqrt ρ := by
  have hh := norm_le_sqrt_card (x := direction τ m v) (by positivity : 0 ≤ 1 / Real.sqrt ρ)
    (fun i => AdamAccumulator.momentum_direction_bound hρ (hv i) hτ (hm i))
  simpa only [mul_one_div] using hh

lemma residual_norm {d : ℕ} {β η τ ρ : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hρ : 0 < ρ) (hρq : 1 / 4 ≤ 1 - ρ)
    (s : Point d × Point d × Point d) (w : Point d)
    (hv : ∀ i, 0 < s.2.2 i) (hw : ∀ i, 0 < w i)
    (hdecay : ∀ i, (1 - ρ) * s.2.2 i ≤ w i)
    (hm : ∀ i, ρ * (s.2.1 i) ^ 2 ≤ s.2.2 i) :
    ‖residual β η τ s w‖ ≤ 3 * (β / (1 - β)) * (η / Real.sqrt ρ) * Real.sqrt d := by
  have hcoordinate (i) : |residual β η τ s w i| ≤ 3 * (β / (1 - β)) * (η / Real.sqrt ρ) := by
    have hvi := hv i
    have hwi := hw i
    have hd : 0 < Real.sqrt (s.2.2 i) + τ := by positivity
    have he : 0 < Real.sqrt (w i) + τ := by positivity
    have hm' : |η * s.2.1 i / (Real.sqrt (s.2.2 i) + τ)| ≤ η / Real.sqrt ρ := by
      rw [mul_div_assoc, abs_mul, abs_of_nonneg hη]
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
        (AdamAccumulator.momentum_direction_bound hρ (hv i) hτ (hm i)) hη
    have hr := residual_coordinate hβ hβ1 s w i hd he hm'
    have hratio := AdamAccumulator.damped_ratio hρq (by linarith) hvi (hdecay i) hτ
    have hnonneg : 0 ≤ (Real.sqrt (s.2.2 i) + τ) / (Real.sqrt (w i) + τ) := div_nonneg hd.le he.le
    have habs : |1 - (Real.sqrt (s.2.2 i) + τ) / (Real.sqrt (w i) + τ)| ≤ 3 :=
      abs_le.2 ⟨by linarith, by linarith⟩
    have hb := mul_le_mul_of_nonneg_left habs
      (by positivity : 0 ≤ β / (1 - β) * (η / Real.sqrt ρ))
    nlinarith
  have hh := norm_le_sqrt_card (by positivity) hcoordinate
  convert hh using 1; ring

lemma shifted_radius {d : ℕ} {x z q e : Point d} {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hz : ‖z - x‖ ≤ r * a) (hq : ‖q‖ ≤ a) (he : ‖e‖ ≤ 3 * r * a) :
    ‖z - x‖ ≤ (1 + 4 * r) * a ∧ ‖z - q - x‖ ≤ (1 + 4 * r) * a ∧
      ‖z - q + e - x‖ ≤ (1 + 4 * r) * a := by
  have hw : ‖z - q - x‖ ≤ ‖z - x‖ + ‖q‖ := by
    have hh : z - q - x = (z - x) - q := by abel
    rw [hh]
    exact norm_sub_le _ _
  have hwe : ‖z - q + e - x‖ ≤ ‖z - q - x‖ + ‖e‖ := by
    have hh : z - q + e - x = (z - q - x) + e := by abel
    rw [hh]
    exact norm_add_le _ _
  have hp := mul_nonneg hr ha
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

lemma signal_denominator_bound {d : ℕ} {v : Point d} {ρ V C : ℝ} (hρ : 0 ≤ ρ)
    (hv : ∀ i, 0 ≤ v i) (hvB : ∀ i, v i ≤ V) (h : Point d) (hh : ‖h‖ ≤ C) :
    ∀ i, Real.sqrt ((1 - ρ) * v i + ρ * (h i) ^ 2) + 1 ≤
      1 + Real.sqrt (V + ρ * C ^ 2) := by
  intro i
  have hi := PiLp.norm_apply_le h i
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hi.trans hh) 2
  simp only [Real.norm_eq_abs, sq_abs] at hs
  have hp := mul_le_mul_of_nonneg_left hs hρ
  have hdec := mul_nonneg hρ (hv i)
  have hb : (1 - ρ) * v i + ρ * (h i) ^ 2 ≤ V + ρ * C ^ 2 := by nlinarith [hvB i]
  have ht := Real.sqrt_le_sqrt hb
  linarith

lemma signal_gradient_sum {d : ℕ} (h : ℕ → Point d) (v : ℕ → Point d) (ρ : ℝ) (T : ℕ)
    {H : ℝ} (hH : ∀ t < T, ∀ i, Real.sqrt ((1 - ρ) * v t i + ρ * (h t i) ^ 2) + 1 ≤ H) :
    (∑ t ∈ Finset.range T, ‖h t‖ ^ 2) ≤
      H * ∑ t ∈ Finset.range T, ⟪h t,
        AdamNormalizedMoments.normalized (fun i => (1 - ρ) * v t i) ρ 1 (h t)⟫ := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  exact AdamNormalizedMoments.gradient_square_from_signal (h t)
    (fun i => by positivity) (hH t (Finset.mem_range.1 ht))

end LongTails.Proofs.AdamGeneralizedPath
