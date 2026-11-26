import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Asymptotics.Lemmas

open scoped Topology
open MeasureTheory intervalIntegral Set

namespace LongTails.Proofs.HsProfile

noncomputable def cut (x : ℝ) : ℝ := max x 0

lemma cut_nonneg (x : ℝ) : 0 ≤ cut x := le_max_right _ _

lemma cut_of_nonneg {x : ℝ} (h : 0 ≤ x) : cut x = x := max_eq_left h

lemma cut_of_nonpos {x : ℝ} (h : x ≤ 0) : cut x = 0 := max_eq_right h

lemma continuous_cut : Continuous cut := continuous_id.max continuous_const

lemma cut_le_abs (x : ℝ) : cut x ≤ |x| := max_le (le_abs_self x) (abs_nonneg x)

lemma hasDerivAt_cut_pow (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    HasDerivAt (fun y => cut y ^ n) ((n : ℝ) * cut x ^ (n - 1)) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hev : (fun y => cut y ^ n) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      rw [cut_of_nonpos (le_of_lt hy), zero_pow (by omega)]
    rw [cut_of_nonpos hx.le, zero_pow (by omega), mul_zero]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  · subst hx
    rw [cut_of_nonneg le_rfl, zero_pow (by omega), mul_zero, hasDerivAt_iff_isLittleO_nhds_zero]
    have hO : (fun h : ℝ => cut (0 + h) ^ n - cut 0 ^ n - h • (0 : ℝ)) =O[𝓝 0]
        fun h : ℝ => h ^ n := by
      refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun h => ?_)
      rw [cut_of_nonneg le_rfl, zero_pow (by omega), smul_zero, sub_zero, sub_zero, zero_add,
        one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_of_nonneg (cut_nonneg h)).le.trans
        (cut_le_abs h)) n
    exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id (by omega))
  · have hev : (fun y => cut y ^ n) =ᶠ[𝓝 x] fun y => y ^ n := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [cut_of_nonneg hy.le]
    rw [cut_of_nonneg hx.le]
    exact (hasDerivAt_pow n x).congr_of_eventuallyEq hev

section Bump

variable (p : ℕ)

noncomputable def base (t : ℝ) : ℝ := cut (1 - t ^ 2) ^ p

noncomputable def dbase (t : ℝ) : ℝ := (p : ℝ) * cut (1 - t ^ 2) ^ (p - 1) * (-(2 * t))

lemma base_nonneg (t : ℝ) : 0 ≤ base p t := pow_nonneg (cut_nonneg _) _

lemma continuous_base : Continuous (base p) :=
  (continuous_cut.comp (continuous_const.sub (continuous_pow 2))).pow p

lemma hasDerivAt_base (hp : 2 ≤ p) (t : ℝ) : HasDerivAt (base p) (dbase p t) t := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_sub 1
    simpa using this
  have h2 := (hasDerivAt_cut_pow p hp (1 - t ^ 2)).comp t h1
  exact h2

lemma base_of_le_neg {t : ℝ} (ht : 1 ≤ |t|) : base p t = 0 ∨ p = 0 := by
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · exact Or.inr h0
  · left
    have h : 1 - t ^ 2 ≤ 0 := by
      have : 1 ≤ t ^ 2 := by
        have := mul_le_mul ht ht zero_le_one (abs_nonneg t)
        rw [one_mul, ← sq, sq_abs] at this
        exact this
      linarith
    rw [base, cut_of_nonpos h, zero_pow (by omega)]

lemma base_eq_zero (hp : 1 ≤ p) {t : ℝ} (ht : 1 ≤ |t|) : base p t = 0 := by
  rcases base_of_le_neg p ht with h | h
  · exact h
  · omega

lemma base_eq_of_mem {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    base p t = (1 - t) ^ p * (1 + t) ^ p := by
  have h : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  rw [base, cut_of_nonneg h, ← mul_pow]
  congr 1
  ring

noncomputable def norm : ℝ := ∫ s in (-1 : ℝ)..1, base p s

lemma one_div_le_norm : 1 / ((p : ℝ) + 1) ≤ norm p := by
  have hsplit : ∫ s in (-1 : ℝ)..1, base p s =
      (∫ s in (-1 : ℝ)..0, base p s) + ∫ s in (0 : ℝ)..1, base p s :=
    (integral_add_adjacent_intervals ((continuous_base p).intervalIntegrable _ _)
      ((continuous_base p).intervalIntegrable _ _)).symm
  have h1 : 0 ≤ ∫ s in (-1 : ℝ)..0, base p s :=
    integral_nonneg (by norm_num) (fun u _ => base_nonneg p u)
  have h2 : ∫ s in (0 : ℝ)..1, (1 - s) ^ p ≤ ∫ s in (0 : ℝ)..1, base p s := by
    apply integral_mono_on (by norm_num)
      ((continuous_const.sub continuous_id).pow p |>.intervalIntegrable _ _)
      ((continuous_base p).intervalIntegrable _ _)
    intro s hs
    show (1 - s) ^ p ≤ base p s
    rw [base, cut_of_nonneg (by nlinarith [hs.1, hs.2])]
    exact pow_le_pow_left₀ (by linarith [hs.2]) (by nlinarith [hs.1, hs.2]) p
  have h3 : ∫ s in (0 : ℝ)..1, (1 - s) ^ p = 1 / ((p : ℝ) + 1) := by
    have := intervalIntegral.integral_comp_sub_left (fun s : ℝ => s ^ p) (a := (0 : ℝ))
      (b := 1) 1
    rw [this, sub_self, sub_zero, integral_pow]
    simp
  unfold norm
  rw [hsplit]
  linarith

lemma norm_pos : 0 < norm p :=
  lt_of_lt_of_le (by positivity) (one_div_le_norm p)

lemma inv_norm_le : 1 / norm p ≤ (p : ℝ) + 1 := by
  have h := one_div_le_norm p
  have hp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  rw [div_le_iff₀ (norm_pos p)]
  rw [div_le_iff₀ hp] at h
  linarith

end Bump

section Profile

variable (p : ℕ)

noncomputable def g2 (t : ℝ) : ℝ := base p t / norm p

noncomputable def g3 (t : ℝ) : ℝ := dbase p t / norm p

noncomputable def g1 (t : ℝ) : ℝ := ∫ s in (-1 : ℝ)..t, g2 p s

noncomputable def g0 (t : ℝ) : ℝ := ∫ s in (-1 : ℝ)..t, g1 p s

lemma continuous_g2 : Continuous (g2 p) := (continuous_base p).div_const _

lemma g2_nonneg (t : ℝ) : 0 ≤ g2 p t := div_nonneg (base_nonneg p t) (norm_pos p).le

lemma hasDerivAt_g2 (hp : 2 ≤ p) (t : ℝ) : HasDerivAt (g2 p) (g3 p t) t :=
  (hasDerivAt_base p hp t).div_const _

lemma hasDerivAt_g1 (t : ℝ) : HasDerivAt (g1 p) (g2 p t) t :=
  ((continuous_g2 p).integral_hasStrictDerivAt (-1) t).hasDerivAt

lemma continuous_g1 : Continuous (g1 p) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_g1 p t).continuousAt

lemma hasDerivAt_g0 (t : ℝ) : HasDerivAt (g0 p) (g1 p t) t :=
  ((continuous_g1 p).integral_hasStrictDerivAt (-1) t).hasDerivAt

lemma g2_eq_zero (hp : 1 ≤ p) {t : ℝ} (ht : 1 ≤ |t|) : g2 p t = 0 := by
  rw [g2, base_eq_zero p hp ht, zero_div]

lemma g3_eq_zero (hp : 2 ≤ p) {t : ℝ} (ht : 1 ≤ |t|) : g3 p t = 0 := by
  have h : 1 - t ^ 2 ≤ 0 := by
    have : 1 ≤ t ^ 2 := by
      have := mul_le_mul ht ht zero_le_one (abs_nonneg t)
      rw [one_mul, ← sq, sq_abs] at this
      exact this
    linarith
  rw [g3, dbase, cut_of_nonpos h, zero_pow (by omega), mul_zero, zero_mul, zero_div]

lemma g1_mono : Monotone (g1 p) :=
  monotone_of_deriv_nonneg (fun t => (hasDerivAt_g1 p t).differentiableAt)
    (fun t => by rw [(hasDerivAt_g1 p t).deriv]; exact g2_nonneg p t)

lemma g1_of_le (hp : 1 ≤ p) {t : ℝ} (ht : t ≤ -1) : g1 p t = 0 := by
  unfold g1
  rw [integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
  intro s hs
  rw [uIcc_of_ge ht] at hs
  exact g2_eq_zero p hp (by rw [abs_of_neg (by linarith [hs.2])]; linarith [hs.2])

lemma g1_one : g1 p 1 = 1 := by
  unfold g1 g2
  rw [intervalIntegral.integral_div]
  exact div_self (norm_pos p).ne'

lemma g1_of_ge (hp : 1 ≤ p) {t : ℝ} (ht : 1 ≤ t) : g1 p t = 1 := by
  have hadd := integral_add_adjacent_intervals
    ((continuous_g2 p).intervalIntegrable (μ := volume) (-1) 1)
    ((continuous_g2 p).intervalIntegrable (μ := volume) 1 t)
  have hz : ∫ s in (1 : ℝ)..t, g2 p s = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact g2_eq_zero p hp (by rw [abs_of_pos (by linarith [hs.1])]; exact hs.1)
  unfold g1 at *
  rw [← hadd, hz, add_zero]
  exact g1_one p

lemma g1_nonneg (hp : 1 ≤ p) (t : ℝ) : 0 ≤ g1 p t := by
  have h := g1_mono p (show -1 ≤ max t (-1) from le_max_right _ _)
  rw [g1_of_le p hp le_rfl] at h
  rcases le_total t (-1) with h1 | h1
  · rw [g1_of_le p hp h1]
  · rwa [max_eq_left h1] at h

lemma g1_le_one (hp : 1 ≤ p) (t : ℝ) : g1 p t ≤ 1 := by
  rcases le_total t 1 with h1 | h1
  · have := g1_mono p h1
    rwa [g1_one] at this
  · rw [g1_of_ge p hp h1]

lemma g0_of_le (hp : 1 ≤ p) {t : ℝ} (ht : t ≤ -1) : g0 p t = 0 := by
  unfold g0
  rw [integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
  intro s hs
  rw [uIcc_of_ge ht] at hs
  exact g1_of_le p hp hs.2

lemma g0_tangent (x y : ℝ) : g0 p x + g1 p x * (y - x) ≤ g0 p y := by
  have hadd := integral_add_adjacent_intervals
    ((continuous_g1 p).intervalIntegrable (μ := volume) (-1) x)
    ((continuous_g1 p).intervalIntegrable (μ := volume) x y)
  have hkey : g1 p x * (y - x) ≤ ∫ s in x..y, g1 p s := by
    rcases le_total x y with hxy | hxy
    · have := integral_mono_on hxy (intervalIntegrable_const (μ := volume) (c := g1 p x))
        ((continuous_g1 p).intervalIntegrable (μ := volume) x y) (fun s hs => g1_mono p hs.1)
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at this
      exact this
    · have := integral_mono_on hxy ((continuous_g1 p).intervalIntegrable (μ := volume) y x)
        (intervalIntegrable_const (μ := volume) (c := g1 p x)) (fun s hs => g1_mono p hs.2)
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      rw [integral_symm]
      nlinarith
  unfold g0
  rw [← hadd]
  linarith

lemma g0_nonneg (hp : 1 ≤ p) (t : ℝ) : 0 ≤ g0 p t := by
  have h := g0_tangent p (-1) t
  rw [g0_of_le p hp le_rfl, g1_of_le p hp le_rfl] at h
  linarith

lemma g0_lower (t : ℝ) : g0 p 1 + (t - 1) ≤ g0 p t := by
  have h := g0_tangent p 1 t
  rwa [g1_one, one_mul] at h

lemma g0_of_ge (hp : 1 ≤ p) {t : ℝ} (ht : 1 ≤ t) : g0 p t = g0 p 1 + (t - 1) := by
  have hadd := integral_add_adjacent_intervals
    ((continuous_g1 p).intervalIntegrable (μ := volume) (-1) 1)
    ((continuous_g1 p).intervalIntegrable (μ := volume) 1 t)
  have hz : ∫ s in (1 : ℝ)..t, g1 p s = t - 1 := by
    rw [integral_congr (g := fun _ => (1 : ℝ)), intervalIntegral.integral_const, smul_eq_mul, mul_one]
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact g1_of_ge p hp hs.1
  unfold g0 at *
  rw [← hadd, hz]

lemma g0_upper (hp : 1 ≤ p) (t : ℝ) : g0 p t ≤ cut (t + 1) := by
  rcases le_total t (-1) with h | h
  · rw [g0_of_le p hp h]
    exact cut_nonneg _
  · rw [cut_of_nonneg (by linarith)]
    unfold g0
    have := integral_mono_on h ((continuous_g1 p).intervalIntegrable (μ := volume) (-1) t)
      (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) (fun s _ => g1_le_one p hp s)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
    linarith

lemma g0_one_le_two (hp : 1 ≤ p) : g0 p 1 ≤ 2 := by
  have h := g0_upper p hp 1
  rw [cut_of_nonneg (by norm_num)] at h
  linarith

lemma g2_le (t : ℝ) : g2 p t ≤ (p : ℝ) + 1 := by
  have hb : base p t ≤ 1 := by
    unfold base
    rcases le_total (1 - t ^ 2) 0 with h | h
    · rcases Nat.eq_zero_or_pos p with h0 | h0
      · rw [h0, pow_zero]
      · rw [cut_of_nonpos h, zero_pow (by omega)]; norm_num
    · rw [cut_of_nonneg h]
      exact pow_le_one₀ h (by nlinarith [sq_nonneg t])
  unfold g2
  have := inv_norm_le p
  calc base p t / norm p ≤ 1 / norm p :=
        div_le_div_of_nonneg_right hb (norm_pos p).le
    _ ≤ _ := this

end Profile

section Bounds

variable (p : ℕ)

lemma integral_one_add_pow (t : ℝ) :
    ∫ s in (-1 : ℝ)..t, (1 + s) ^ p = (1 + t) ^ (p + 1) / ((p : ℝ) + 1) := by
  have := intervalIntegral.integral_comp_add_left (fun s : ℝ => s ^ p) (a := (-1 : ℝ)) (b := t) 1
  rw [this, integral_pow]
  norm_num

lemma integral_one_sub_pow (t : ℝ) :
    ∫ s in t..(1 : ℝ), (1 - s) ^ p = (1 - t) ^ (p + 1) / ((p : ℝ) + 1) := by
  have := intervalIntegral.integral_comp_sub_left (fun s : ℝ => s ^ p) (a := t) (b := (1 : ℝ)) 1
  rw [this, integral_pow]
  norm_num

lemma g1_ge_left {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    g2 p t * (1 + t) / ((p : ℝ) + 1) ≤ g1 p t := by
  have hmono : ∫ s in (-1 : ℝ)..t, (1 - t) ^ p * (1 + s) ^ p ≤ ∫ s in (-1 : ℝ)..t, base p s := by
    apply integral_mono_on ht.1
      ((continuous_const.mul ((continuous_const.add continuous_id).pow p)).intervalIntegrable _ _)
      ((continuous_base p).intervalIntegrable _ _)
    intro s hs
    show (1 - t) ^ p * (1 + s) ^ p ≤ base p s
    have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
    rw [base_eq_of_mem p hs']
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith [hs.1]) _)
    exact pow_le_pow_left₀ (by linarith [ht.2]) (by linarith [hs.2]) p
  rw [intervalIntegral.integral_const_mul, integral_one_add_pow] at hmono
  have hg1 : g1 p t = (∫ s in (-1 : ℝ)..t, base p s) / norm p := by
    unfold g1 g2
    rw [intervalIntegral.integral_div]
  rw [hg1, g2, base_eq_of_mem p ht]
  have hn := norm_pos p
  have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  rw [div_mul_eq_mul_div, div_div, div_le_div_iff₀ (by positivity) hn]
  have e : (1 - t) ^ p * (1 + t) ^ p * (1 + t) = (1 - t) ^ p * (1 + t) ^ (p + 1) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_right hmono hp1.le
  rw [mul_div_assoc', div_mul_cancel₀ _ hp1.ne'] at this
  nlinarith [mul_le_mul_of_nonneg_right this hn.le]

lemma one_sub_g1_eq (t : ℝ) : 1 - g1 p t = ∫ s in t..(1 : ℝ), g2 p s := by
  have hadd := integral_add_adjacent_intervals
    ((continuous_g2 p).intervalIntegrable (μ := volume) (-1) t)
    ((continuous_g2 p).intervalIntegrable (μ := volume) t 1)
  have h1 := g1_one p
  unfold g1 at *
  linarith

lemma g1_ge_right (hp : 1 ≤ p) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    g2 p t * (1 - t) / ((p : ℝ) + 1) ≤ 1 - g1 p t := by
  have hmono : ∫ s in t..(1 : ℝ), (1 - s) ^ p * (1 + t) ^ p ≤ ∫ s in t..(1 : ℝ), base p s := by
    apply integral_mono_on ht.2
      ((((continuous_const.sub continuous_id).pow p).mul continuous_const).intervalIntegrable _ _)
      ((continuous_base p).intervalIntegrable _ _)
    intro s hs
    show (1 - s) ^ p * (1 + t) ^ p ≤ base p s
    have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨ht.1.trans hs.1, hs.2⟩
    rw [base_eq_of_mem p hs']
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith [hs.2]) _)
    exact pow_le_pow_left₀ (by linarith [ht.1]) (by linarith [hs.1]) p
  rw [intervalIntegral.integral_mul_const, integral_one_sub_pow] at hmono
  have hg1 : 1 - g1 p t = (∫ s in t..(1 : ℝ), base p s) / norm p := by
    rw [one_sub_g1_eq p t]
    unfold g2
    rw [intervalIntegral.integral_div]
  rw [hg1, g2, base_eq_of_mem p ht]
  have hn := norm_pos p
  have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  rw [div_mul_eq_mul_div, div_div, div_le_div_iff₀ (by positivity) hn]
  have e : (1 - t) ^ p * (1 + t) ^ p * (1 - t) = (1 - t) ^ (p + 1) * (1 + t) ^ p := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_right hmono hp1.le
  rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hp1.ne'] at this
  nlinarith [mul_le_mul_of_nonneg_right this hn.le]

lemma small_pow_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha2 : a ≤ 2) (hb4 : b ≤ 1 / 4) :
    a ^ p * b ^ p ≤ (1 / 2) ^ p := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg ha hb) (by nlinarith) p

lemma g2_le_g1 (hp : 1 ≤ p) (t : ℝ) :
    g2 p t ≤ 4 * ((p : ℝ) + 1) * g1 p t + ((p : ℝ) + 1) * (1 / 2) ^ p := by
  have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hrest : 0 ≤ ((p : ℝ) + 1) * (1 / 2) ^ p := by positivity
  by_cases hin : t ∈ Icc (-1 : ℝ) 1
  · by_cases hl : 1 / 4 ≤ 1 + t
    · have h := g1_ge_left p hin
      have h2 : g2 p t * (1 / 4) ≤ g2 p t * (1 + t) :=
        mul_le_mul_of_nonneg_left hl (g2_nonneg p t)
      rw [div_le_iff₀ hp1] at h
      nlinarith [g2_nonneg p t]
    · push Not at hl
      have hb : base p t ≤ (1 / 2) ^ p := by
        rw [base_eq_of_mem p hin]
        exact small_pow_bound p (by linarith [hin.2]) (by linarith [hin.1]) (by linarith [hin.1])
          hl.le
      have hg : g2 p t ≤ ((p : ℝ) + 1) * (1 / 2) ^ p := by
        unfold g2
        calc base p t / norm p = base p t * (1 / norm p) := by ring
          _ ≤ (1 / 2) ^ p * ((p : ℝ) + 1) :=
            mul_le_mul hb (inv_norm_le p) (one_div_pos.mpr (norm_pos p)).le (by positivity)
          _ = _ := by ring
      nlinarith [g1_nonneg p hp t]
  · have hz : g2 p t = 0 := by
      apply g2_eq_zero p hp
      simp only [mem_Icc, not_and_or, not_le] at hin
      rcases hin with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hz]
    nlinarith [g1_nonneg p hp t]

lemma g2_le_one_sub_g1 (hp : 1 ≤ p) (t : ℝ) :
    g2 p t ≤ 4 * ((p : ℝ) + 1) * (1 - g1 p t) + ((p : ℝ) + 1) * (1 / 2) ^ p := by
  have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hrest : 0 ≤ ((p : ℝ) + 1) * (1 / 2) ^ p := by positivity
  have hg1 : 0 ≤ 1 - g1 p t := by linarith [g1_le_one p hp t]
  by_cases hin : t ∈ Icc (-1 : ℝ) 1
  · by_cases hl : 1 / 4 ≤ 1 - t
    · have h := g1_ge_right p hp hin
      have h2 : g2 p t * (1 / 4) ≤ g2 p t * (1 - t) :=
        mul_le_mul_of_nonneg_left hl (g2_nonneg p t)
      rw [div_le_iff₀ hp1] at h
      nlinarith [g2_nonneg p t]
    · push Not at hl
      have hb : base p t ≤ (1 / 2) ^ p := by
        rw [base_eq_of_mem p hin, mul_comm]
        exact small_pow_bound p (by linarith [hin.1]) (by linarith [hin.2]) (by linarith [hin.2])
          hl.le
      have hg : g2 p t ≤ ((p : ℝ) + 1) * (1 / 2) ^ p := by
        unfold g2
        calc base p t / norm p = base p t * (1 / norm p) := by ring
          _ ≤ (1 / 2) ^ p * ((p : ℝ) + 1) :=
            mul_le_mul hb (inv_norm_le p) (one_div_pos.mpr (norm_pos p)).le (by positivity)
          _ = _ := by ring
      nlinarith
  · have hz : g2 p t = 0 := by
      apply g2_eq_zero p hp
      simp only [mem_Icc, not_and_or, not_le] at hin
      rcases hin with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hz]
    nlinarith

lemma abs_g3_le (hp : 2 ≤ p) (t : ℝ) :
    |g3 p t| ≤ 4 * (p : ℝ) * g2 p t + 4 * (p : ℝ) * ((p : ℝ) + 1) * (1 / 2) ^ p := by
  have hn := norm_pos p
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hrest : 0 ≤ 4 * (p : ℝ) * ((p : ℝ) + 1) * (1 / 2) ^ p := by positivity
  set c := cut (1 - t ^ 2) with hc
  have hc0 : 0 ≤ c := cut_nonneg _
  have hc1 : c ≤ 1 := by
    rw [hc]
    unfold cut
    exact max_le (by nlinarith [sq_nonneg t]) zero_le_one
  have hg3 : |g3 p t| = 2 * (p : ℝ) * |t| * c ^ (p - 1) / norm p := by
    unfold g3 dbase
    rw [abs_div, abs_of_pos hn, ← hc, abs_mul, abs_mul, abs_neg, abs_mul,
      abs_of_nonneg hp0, abs_of_nonneg (pow_nonneg hc0 _), abs_two]
    ring
  have hg2 : g2 p t = c ^ p / norm p := by unfold g2 base; rw [← hc]
  rcases eq_or_lt_of_le hc0 with h0 | hpos
  · rw [hg3, ← h0, zero_pow (by omega), mul_zero, zero_div]
    exact add_nonneg (by rw [hg2, ← h0, zero_pow (by omega), zero_div, mul_zero]) hrest
  · have ht1 : |t| ≤ 1 := by
      have : 0 < 1 - t ^ 2 := by
        by_contra hh
        push Not at hh
        rw [hc, cut_of_nonpos hh] at hpos
        exact lt_irrefl _ hpos
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (t + 1), sq_nonneg (t - 1)]
    have hpow : c ^ p = c ^ (p - 1) * c := by
      rw [← pow_succ]; congr 1; omega
    rw [hg3, hg2]
    by_cases hbig : 1 / 2 ≤ c
    · have h1 : c ^ (p - 1) ≤ 2 * c ^ p := by
        rw [hpow]; nlinarith [pow_nonneg hc0 (p - 1)]
      have h2 : 2 * (p : ℝ) * |t| * c ^ (p - 1) ≤ 4 * (p : ℝ) * c ^ p := by
        have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * (p : ℝ) by positivity)
        nlinarith [mul_le_mul_of_nonneg_left ht1 (show 0 ≤ 2 * (p : ℝ) * c ^ (p - 1) by positivity)]
      have h3 : 2 * (p : ℝ) * |t| * c ^ (p - 1) / norm p ≤ 4 * (p : ℝ) * (c ^ p / norm p) := by
        rw [mul_div_assoc']
        exact div_le_div_of_nonneg_right h2 hn.le
      linarith
    · push Not at hbig
      have h1 : c ^ (p - 1) ≤ (1 / 2) ^ (p - 1) := pow_le_pow_left₀ hc0 hbig.le _
      have h1' : (1 / 2 : ℝ) ^ (p - 1) = 2 * (1 / 2) ^ p := by
        have : (1 / 2 : ℝ) ^ p = (1 / 2) ^ (p - 1) * (1 / 2) := by
          rw [← pow_succ]; congr 1; omega
        rw [this]; ring
      have h2 : 2 * (p : ℝ) * |t| * c ^ (p - 1) ≤ 4 * (p : ℝ) * (1 / 2) ^ p := by
        have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * (p : ℝ) by positivity)
        nlinarith [mul_le_mul_of_nonneg_left ht1 (show 0 ≤ 2 * (p : ℝ) * c ^ (p - 1) by positivity),
          pow_nonneg (show (0:ℝ) ≤ 1/2 by norm_num) p]
      have h3 : 2 * (p : ℝ) * |t| * c ^ (p - 1) / norm p ≤
          4 * (p : ℝ) * (1 / 2) ^ p * ((p : ℝ) + 1) := by
        calc 2 * (p : ℝ) * |t| * c ^ (p - 1) / norm p
            = 2 * (p : ℝ) * |t| * c ^ (p - 1) * (1 / norm p) := by ring
          _ ≤ 4 * (p : ℝ) * (1 / 2) ^ p * ((p : ℝ) + 1) :=
            mul_le_mul h2 (inv_norm_le p) (by positivity) (by positivity)
      have h4 : 0 ≤ 4 * (p : ℝ) * (c ^ p / norm p) := by positivity
      nlinarith

end Bounds

section Scaled

variable (p : ℕ) (a h : ℝ)

noncomputable def sp0 (t : ℝ) : ℝ := h * g0 p ((t - a) / h)

noncomputable def sp1 (t : ℝ) : ℝ := g1 p ((t - a) / h)

noncomputable def sp2 (t : ℝ) : ℝ := g2 p ((t - a) / h) / h

noncomputable def sp3 (t : ℝ) : ℝ := g3 p ((t - a) / h) / h ^ 2

variable {h}

lemma hasDerivAt_aff (t : ℝ) : HasDerivAt (fun s : ℝ => (s - a) / h) (1 / h) t := by
  have := ((hasDerivAt_id t).sub_const a).div_const h
  simpa using this

lemma hasDerivAt_sp0 (hh : 0 < h) (t : ℝ) : HasDerivAt (sp0 p a h) (sp1 p a h t) t := by
  have h1 := ((hasDerivAt_g0 p ((t - a) / h)).comp t (hasDerivAt_aff a t (h := h))).const_mul h
  exact h1.congr_deriv (by unfold sp1; field_simp [hh.ne'])

lemma hasDerivAt_sp1 (t : ℝ) : HasDerivAt (sp1 p a h) (sp2 p a h t) t := by
  have h1 := (hasDerivAt_g1 p ((t - a) / h)).comp t (hasDerivAt_aff a t (h := h))
  exact h1.congr_deriv (by unfold sp2; ring)

lemma hasDerivAt_sp2 (hp : 2 ≤ p) (t : ℝ) :
    HasDerivAt (sp2 p a h) (sp3 p a h t) t := by
  have h1 := ((hasDerivAt_g2 p hp ((t - a) / h)).comp t (hasDerivAt_aff a t (h := h))).div_const h
  exact h1.congr_deriv (by unfold sp3; ring)

lemma continuous_sp2 : Continuous (sp2 p a h) :=
  ((continuous_g2 p).comp ((continuous_id.sub continuous_const).div_const h)).div_const h

lemma sp1_nonneg (hp : 1 ≤ p) (t : ℝ) : 0 ≤ sp1 p a h t := g1_nonneg p hp _

lemma sp1_le_one (hp : 1 ≤ p) (t : ℝ) : sp1 p a h t ≤ 1 := g1_le_one p hp _

lemma sp2_nonneg (hh : 0 < h) (t : ℝ) : 0 ≤ sp2 p a h t := div_nonneg (g2_nonneg p _) hh.le

lemma sp2_le (hh : 0 < h) (t : ℝ) : sp2 p a h t ≤ ((p : ℝ) + 1) / h :=
  div_le_div_of_nonneg_right (g2_le p _) hh.le

lemma aff_abs_ge (hh : 0 < h) {t : ℝ} (ht : h ≤ |t - a|) : 1 ≤ |(t - a) / h| := by
  rw [abs_div, abs_of_pos hh, le_div_iff₀ hh, one_mul]
  exact ht

lemma sp2_eq_zero (hp : 1 ≤ p) (hh : 0 < h) {t : ℝ} (ht : h ≤ |t - a|) : sp2 p a h t = 0 := by
  rw [sp2, g2_eq_zero p hp (aff_abs_ge a hh ht), zero_div]

lemma sp3_eq_zero (hp : 2 ≤ p) (hh : 0 < h) {t : ℝ} (ht : h ≤ |t - a|) : sp3 p a h t = 0 := by
  rw [sp3, g3_eq_zero p hp (aff_abs_ge a hh ht), zero_div]

lemma aff_le_neg (hh : 0 < h) {t : ℝ} (ht : t ≤ a - h) : (t - a) / h ≤ -1 := by
  rw [div_le_iff₀ hh]; linarith

lemma aff_ge_one (hh : 0 < h) {t : ℝ} (ht : a + h ≤ t) : 1 ≤ (t - a) / h := by
  rw [le_div_iff₀ hh]; linarith

lemma sp0_of_le (hp : 1 ≤ p) (hh : 0 < h) {t : ℝ} (ht : t ≤ a - h) : sp0 p a h t = 0 := by
  rw [sp0, g0_of_le p hp (aff_le_neg a hh ht), mul_zero]

lemma sp1_of_le (hp : 1 ≤ p) (hh : 0 < h) {t : ℝ} (ht : t ≤ a - h) : sp1 p a h t = 0 :=
  g1_of_le p hp (aff_le_neg a hh ht)

lemma sp1_of_ge (hp : 1 ≤ p) (hh : 0 < h) {t : ℝ} (ht : a + h ≤ t) : sp1 p a h t = 1 :=
  g1_of_ge p hp (aff_ge_one a hh ht)

lemma sp0_of_ge (hp : 1 ≤ p) (hh : 0 < h) {t : ℝ} (ht : a + h ≤ t) :
    sp0 p a h t = h * g0 p 1 + (t - a - h) := by
  rw [sp0, g0_of_ge p hp (aff_ge_one a hh ht)]
  field_simp

lemma sp0_tangent (hh : 0 < h) (x y : ℝ) : sp0 p a h x + sp1 p a h x * (y - x) ≤ sp0 p a h y := by
  have h1 := g0_tangent p ((x - a) / h) ((y - a) / h)
  have h2 := mul_le_mul_of_nonneg_left h1 hh.le
  unfold sp0 sp1
  have e : h * (g0 p ((x - a) / h) + g1 p ((x - a) / h) * ((y - a) / h - (x - a) / h)) =
      h * g0 p ((x - a) / h) + g1 p ((x - a) / h) * (y - x) := by
    field_simp
    ring
  linarith

lemma sp0_nonneg (hp : 1 ≤ p) (hh : 0 < h) (t : ℝ) : 0 ≤ sp0 p a h t :=
  mul_nonneg hh.le (g0_nonneg p hp _)

lemma sp0_ge (hp : 1 ≤ p) (hh : 0 < h) (t : ℝ) : t - a - h ≤ sp0 p a h t := by
  have h1 := g0_lower p ((t - a) / h)
  have h0 := g0_nonneg p hp 1
  have h2 := mul_le_mul_of_nonneg_left h1 hh.le
  unfold sp0
  have e : h * (g0 p 1 + ((t - a) / h - 1)) = h * g0 p 1 + (t - a - h) := by
    field_simp
  nlinarith

lemma sp0_le (hp : 1 ≤ p) (hh : 0 < h) (t : ℝ) : sp0 p a h t ≤ cut (t - a + h) := by
  have h1 := g0_upper p hp ((t - a) / h)
  unfold sp0
  rcases le_total 0 (t - a + h) with hc | hc
  · rw [cut_of_nonneg hc]
    have e : (t - a) / h + 1 = (t - a + h) / h := by field_simp
    rw [e, cut_of_nonneg (div_nonneg hc hh.le)] at h1
    have := mul_le_mul_of_nonneg_left h1 hh.le
    rwa [mul_div_cancel₀ _ hh.ne'] at this
  · have hle : (t - a) / h ≤ -1 := by
      rw [div_le_iff₀ hh]; linarith
    rw [g0_of_le p hp hle, mul_zero]
    exact cut_nonneg _

lemma abs_sp3_le (hp : 2 ≤ p) (hh : 0 < h) (t : ℝ) :
    |sp3 p a h t| ≤ 4 * (p : ℝ) / h * sp2 p a h t +
      4 * (p : ℝ) * ((p : ℝ) + 1) * (1 / 2) ^ p / h ^ 2 := by
  have h1 := abs_g3_le p hp ((t - a) / h)
  unfold sp3 sp2
  have hh2 : 0 < h ^ 2 := by positivity
  rw [abs_div, abs_of_pos hh2, div_le_iff₀ hh2]
  have e : (4 * (p : ℝ) / h * (g2 p ((t - a) / h) / h) +
      4 * (p : ℝ) * ((p : ℝ) + 1) * (1 / 2) ^ p / h ^ 2) * h ^ 2 =
      4 * (p : ℝ) * g2 p ((t - a) / h) + 4 * (p : ℝ) * ((p : ℝ) + 1) * (1 / 2) ^ p := by
    field_simp
  rw [e]
  exact h1

lemma sp2_le_sp1 (hp : 1 ≤ p) (hh : 0 < h) (t : ℝ) :
    sp2 p a h t ≤ 4 * ((p : ℝ) + 1) / h * sp1 p a h t + ((p : ℝ) + 1) * (1 / 2) ^ p / h := by
  have h1 := g2_le_g1 p hp ((t - a) / h)
  unfold sp2 sp1
  have := div_le_div_of_nonneg_right h1 hh.le
  have e : (4 * ((p : ℝ) + 1) * g1 p ((t - a) / h) + ((p : ℝ) + 1) * (1 / 2) ^ p) / h =
      4 * ((p : ℝ) + 1) / h * g1 p ((t - a) / h) + ((p : ℝ) + 1) * (1 / 2) ^ p / h := by ring
  linarith

lemma sp2_le_one_sub_sp1 (hp : 1 ≤ p) (hh : 0 < h) (t : ℝ) :
    sp2 p a h t ≤ 4 * ((p : ℝ) + 1) / h * (1 - sp1 p a h t) + ((p : ℝ) + 1) * (1 / 2) ^ p / h := by
  have h1 := g2_le_one_sub_g1 p hp ((t - a) / h)
  unfold sp2 sp1
  have := div_le_div_of_nonneg_right h1 hh.le
  have e : (4 * ((p : ℝ) + 1) * (1 - g1 p ((t - a) / h)) + ((p : ℝ) + 1) * (1 / 2) ^ p) / h =
      4 * ((p : ℝ) + 1) / h * (1 - g1 p ((t - a) / h)) + ((p : ℝ) + 1) * (1 / 2) ^ p / h := by
    ring
  linarith

end Scaled

end LongTails.Proofs.HsProfile
