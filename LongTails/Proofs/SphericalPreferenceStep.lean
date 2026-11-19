import LongTails.Algorithms.SphericalPreferenceDescent
import LongTails.Proofs.SphericalPreferenceDirection

open MeasureTheory Metric Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SphericalPreferenceStep

open OracleTemplate LongTails.Setups.SphericalRandomUtility LongTails.Algorithms.SphericalPreferenceDescent
open LongTails.Proofs.SphericalPreferenceDirection

lemma tuning (p : Params) {n : ℕ} (hn : 0 < n) (hd : 2 ≤ p.d) (hR : 0 < p.R) :
    0 < stepSize p n ∧ 0 < radius p n ∧ 2 * radius p n ≤ p.R ∧
      0 < probe p n ∧ probe p n < radius p n := by
  have hs : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hr : 0 < (p.R : ℝ) := hR
  have hd' : 2 ≤ (p.d : ℝ) := by exact_mod_cast hd
  have hs' : 0 < Real.sqrt n := by linarith
  have he : 0 < stepSize p n := div_pos hr hs'
  have he' : stepSize p n ≤ p.R := div_le_self hr.le hs
  have ha : 0 < radius p n := div_pos he (by norm_num)
  have hden : 1 < 4 * (p.d : ℝ) * Real.sqrt n := by
    nlinarith only [mul_le_mul hd' hs zero_le_one (by positivity : 0 ≤ (p.d : ℝ))]
  exact ⟨he, ha, by dsimp [radius]; linarith, div_pos ha (by linarith),
    div_lt_self ha hden⟩

lemma jitter_geometry {d : ℕ} {R r h : ℝ} (hR : 0 < R) (hr : 0 ≤ r)
    (hs : 2*r ≤ R) (hh : 0 ≤ h) (hhr : h ≤ r) (x w u : Point d)
    (hx : ‖x‖ ≤ R) (hw : ‖w‖ ≤ r) (hu : ‖u‖ = 1) :
    let y := (1 - 2*r/R) • x + w
    ‖y‖ ≤ R - r ∧ ‖x-y‖ ≤ 3*r ∧ ‖y-h • u‖ ≤ R ∧ ‖y+h • u‖ ≤ R := by
  dsimp only
  have ht : 0 ≤ 1 - 2*r/R := sub_nonneg.mpr ((div_le_one hR).mpr hs)
  have hratio : 0 ≤ 2*r/R := by positivity
  have hscale : (2*r/R)*R = 2*r := div_mul_cancel₀ _ hR.ne'
  have hy := norm_add_le ((1 - 2*r/R) • x) w
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hy
  have hbase : ‖(1 - 2*r/R) • x + w‖ ≤ R-r := by
    linarith only [hy, hw, mul_le_mul_of_nonneg_left hx ht, show (1-2*r/R)*R = R-2*r by linarith only [hscale]]
  have hdist : x - ((1 - 2*r/R) • x + w) = (2*r/R) • x - w := by module
  have hxw := norm_sub_le ((2*r/R) • x) w
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hratio] at hxw
  have hprobe : ‖h • u‖ = h := by simp [norm_smul, hu, abs_of_nonneg hh]
  refine ⟨hbase, ?_, ?_, ?_⟩
  · rw [hdist]
    linarith only [hxw, hw, mul_le_mul_of_nonneg_left hx hratio, hscale]
  · exact (norm_sub_le _ _).trans (by linarith only [hbase, hprobe, hhr])
  · exact (norm_add_le _ _).trans (by linarith only [hbase, hprobe, hhr])

lemma projected_step (p : Params) (n : ℕ) (x u : Point p.d) (o : Feasible p)
    (b : Bool) (hu : ‖u‖ = 1) :
    ‖next p n x u b - o‖ ^ 2 ≤ ‖x-o‖ ^ 2 -
      2 * stepSize p n * ((if b then (1 : ℝ) else -1) * ⟪u, x-o.val⟫) + stepSize p n ^ 2 := by
  let a := if b then stepSize p n else -(stepSize p n)
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (norm_clip_sub_le p.R.coe_nonneg (mem_closedBall_zero_iff.mp o.property) (x-a • u)) 2
  have he : x-a • u-o = (x-o)-a • u := by abel
  rw [he, norm_sub_sq_real (x-o.val) (a • u), norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs,
    real_inner_smul_right, real_inner_comm u (x-o.val)] at h
  change ‖clip _ (x-a • u) - o.val‖ ^ 2 ≤ _
  cases b <;> simp [a] at h ⊢ <;> linarith only [h]

end LongTails.Proofs.SphericalPreferenceStep
