import LongTails.Proofs.CubicRegularization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

namespace LongTails.Proofs.CoupledCubicMoments

variable {E : Type*} [NormedAddCommGroup E]

lemma norm_sq_le_twice_residual (a b : E) :
    ‖a‖ ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 * ‖a - b‖ ^ 2 := by
  have h := norm_add_le b (a - b)
  rw [add_sub_cancel] at h
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b),
    sq_nonneg (‖b‖ - ‖a - b‖)]

lemma coupled_residual_second_moment {ι : Type*} [Fintype ι]
    (a b : ι → E) (κ G R : ℝ)
    (hg : ∑ i, ‖b i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * κ * G ^ 2)
    (hr : ∑ i, ‖a i - b i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * R ^ 2) :
    ∑ i, ‖a i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * (2 * κ * G ^ 2 + 2 * R ^ 2) := by
  calc
    ∑ i, ‖a i‖ ^ 2 ≤ ∑ i, (2 * ‖b i‖ ^ 2 + 2 * ‖a i - b i‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => norm_sq_le_twice_residual (a i) (b i)
    _ = 2 * (∑ i, ‖b i‖ ^ 2) + 2 * (∑ i, ‖a i - b i‖ ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (Fintype.card ι : ℝ) * (2 * κ * G ^ 2 + 2 * R ^ 2) := by
      nlinarith

lemma finite_curve_second_moment [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
    (R D : ι → ℝ → E) (B : ℝ) (hB : 0 ≤ B)
    (hzero : ∀ i, R i 0 = 0)
    (hdiff : ∀ i t, HasDerivAt (R i) (D i t) t)
    (hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ∑ i, ‖D i t‖ ^ 2 ≤ B ^ 2 * t ^ 2) :
    ∑ i, ‖R i 1‖ ^ 2 ≤ B ^ 2 / 4 := by
  let r : ℝ → PiLp 2 (fun _ : ι => E) := fun t => WithLp.toLp 2 (fun i => R i t)
  let d : ℝ → PiLp 2 (fun _ : ι => E) := fun t => WithLp.toLp 2 (fun i => D i t)
  have hd (t : ℝ) : HasDerivAt r (d t) t := by
    have hh : HasDerivAt (fun t => fun i => R i t) (fun i => D i t) t :=
      hasDerivAt_pi.mpr (fun i => hdiff i t)
    exact (PiLp.hasFDerivAt_toLp 2 _).comp_hasDerivAt t hh
  have hpoly (t : ℝ) : HasDerivAt (fun t : ℝ => B / 2 * t ^ 2) (B * t) t := by
    convert ((hasDerivAt_id t).pow 2).const_mul (B / 2) using 1
    · rfl
    · simp
      ring
  have hnorm (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ‖d t‖ ≤ B * t := by
    have he : ‖d t‖ ^ 2 = ∑ i, ‖D i t‖ ^ 2 := by
      simpa [d] using PiLp.norm_sq_eq_of_L2 (fun _ : ι => E) (d t)
    have hb := hbound t ht
    have hBt : 0 ≤ B * t := mul_nonneg hB ht.1
    nlinarith [norm_nonneg (d t)]
  have hr0 : r 0 = 0 := by
    ext i
    simp [r, hzero]
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (a := 0) (b := 1) (f := r) (f' := d)
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).hasDerivWithinAt)
    (B := fun t => B / 2 * t ^ 2)
    (by rw [hr0]; simp) hpoly hnorm (x := 1) (by norm_num)
  have he : ‖r 1‖ ^ 2 = ∑ i, ‖R i 1‖ ^ 2 := by
    simpa [r] using PiLp.norm_sq_eq_of_L2 (fun _ : ι => E) (r 1)
  simp only [one_pow, mul_one] at h
  nlinarith [norm_nonneg (r 1)]

lemma rms_taylor_remainder [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
    (g : ι → E → E) (H : ι → E → E →L[ℝ] E) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hdiff : ∀ i x, HasFDerivAt (g i) (H i x) x)
    (hLip : ∀ x y, ∑ i, ‖H i x - H i y‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ρ ^ 2 * ‖x - y‖ ^ 2) (x v : E) :
    ∑ i, ‖g i (x + v) - g i x - H i x v‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ρ ^ 2 * ‖v‖ ^ 4 / 4 := by
  let R : ι → ℝ → E := fun i t => g i (x + t • v) - g i x - t • H i x v
  let D : ι → ℝ → E := fun i t => (H i (x + t • v) - H i x) v
  have hR (i : ι) (t : ℝ) : HasDerivAt (R i) (D i t) t := by
    have hline : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have hh := ((hdiff i (x + t • v)).comp_hasDerivAt t hline).sub_const (g i x)
    convert hh.sub ((hasDerivAt_id t).smul_const (H i x v)) using 1
    · rfl
    · simp [D]
  have hc : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hsqrt := Real.sq_sqrt hc
  have hD (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      ∑ i, ‖D i t‖ ^ 2 ≤ (Real.sqrt (Fintype.card ι) * ρ * ‖v‖ ^ 2) ^ 2 * t ^ 2 := by
    have hs (i : ι) : ‖D i t‖ ^ 2 ≤ ‖H i (x + t • v) - H i x‖ ^ 2 * ‖v‖ ^ 2 := by
      have ho := (H i (x + t • v) - H i x).le_opNorm v
      have hn : 0 ≤ ‖H i (x + t • v) - H i x‖ * ‖v‖ := by positivity
      dsimp [D]
      nlinarith [norm_nonneg ((H i (x + t • v) - H i x) v)]
    calc
      ∑ i, ‖D i t‖ ^ 2 ≤ ∑ i, ‖H i (x + t • v) - H i x‖ ^ 2 * ‖v‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => hs i)
      _ = (∑ i, ‖H i (x + t • v) - H i x‖ ^ 2) * ‖v‖ ^ 2 := by
        rw [Finset.sum_mul]
      _ ≤ ((Fintype.card ι : ℝ) * ρ ^ 2 * ‖(x + t • v) - x‖ ^ 2) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hLip (x + t • v) x) (sq_nonneg _)
      _ = (Real.sqrt (Fintype.card ι) * ρ * ‖v‖ ^ 2) ^ 2 * t ^ 2 := by
        simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
          mul_pow, hsqrt]
        ring
  have hh := finite_curve_second_moment R D (Real.sqrt (Fintype.card ι) * ρ * ‖v‖ ^ 2)
    (by positivity) (by intro i; simp [R]) hR hD
  simpa only [R, one_smul, mul_pow, hsqrt, ← pow_mul] using hh

lemma cubic_residual_moment [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
    (g : ι → E → E) (H : ι → E → E →L[ℝ] E) (gbar : E → E)
    (κ ρ M : ℝ) (hκ : 1 ≤ κ) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M)
    (hdiff : ∀ i x, HasFDerivAt (g i) (H i x) x)
    (hLip : ∀ x y, ∑ i, ‖H i x - H i y‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ρ ^ 2 * ‖x - y‖ ^ 2)
    (hSGC : ∀ y, ∑ i, ‖g i y‖ ^ 2 ≤ (Fintype.card ι : ℝ) * κ * ‖gbar y‖ ^ 2)
    (x s : E) (hnew : ‖gbar (x + s)‖ ≤ M * ‖s‖ ^ 2) :
    ∑ i, ‖g i x + H i x s‖ ^ 2 ≤
      5 / 2 * (Fintype.card ι : ℝ) * κ * M ^ 2 * ‖s‖ ^ 4 := by
  have hM : 0 ≤ M := hρ.trans hρM
  have hk0 : 0 ≤ κ := by linarith
  have hc : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hg : ∑ i, ‖g i (x + s)‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * κ * (M * ‖s‖ ^ 2) ^ 2 := by
    apply (hSGC (x + s)).trans
    gcongr
  have hr : ∑ i, ‖g i x + H i x s - g i (x + s)‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * (M * ‖s‖ ^ 2 / 2) ^ 2 := by
    have he (i : ι) : ‖g i x + H i x s - g i (x + s)‖ =
        ‖g i (x + s) - g i x - H i x s‖ := by
      rw [← norm_neg (g i (x + s) - g i x - H i x s)]
      congr 1
      abel
    simp_rw [he]
    apply (rms_taylor_remainder g H ρ hρ hdiff hLip x s).trans
    have hs : ρ ^ 2 ≤ M ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hs
      (show 0 ≤ (Fintype.card ι : ℝ) * ‖s‖ ^ 4 by positivity)
    nlinarith
  have hh := coupled_residual_second_moment (fun i => g i x + H i x s)
    (fun i => g i (x + s)) κ (M * ‖s‖ ^ 2) (M * ‖s‖ ^ 2 / 2) hg hr
  have hp := mul_nonneg (show 0 ≤ κ - 1 by linarith)
    (show 0 ≤ (Fintype.card ι : ℝ) * M ^ 2 * ‖s‖ ^ 4 by positivity)
  nlinarith [hh, hp]


lemma stationary_sgc_hessian_moment [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
    (g : ι → E → E) (H : ι → E → E →L[ℝ] E) (gbar : E → E)
    (Hbar : E → E →L[ℝ] E) (κ : ℝ)
    (hdiff : ∀ i x, HasFDerivAt (g i) (H i x) x)
    (hbar : ∀ x, HasFDerivAt gbar (Hbar x) x)
    (hSGC : ∀ y, ∑ i, ‖g i y‖ ^ 2 ≤ (Fintype.card ι : ℝ) * κ * ‖gbar y‖ ^ 2)
    (x v : E) (hzero : gbar x = 0) :
    ∑ i, ‖H i x v‖ ^ 2 ≤ (Fintype.card ι : ℝ) * κ * ‖Hbar x v‖ ^ 2 := by
  have hsum : ∑ i, ‖g i x‖ ^ 2 ≤ 0 := by
    simpa only [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] using hSGC x
  have hgi (i : ι) : g i x = 0 := by
    have hi : ‖g i x‖ ^ 2 ≤ ∑ j, ‖g j x‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖g j x‖) (Finset.mem_univ i)
    have hn : ‖g i x‖ = 0 := by nlinarith [norm_nonneg (g i x)]
    exact norm_eq_zero.mp hn
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hi (i : ι) : Filter.Tendsto (fun t : ℝ => t⁻¹ • g i (x + t • v))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (H i x v)) := by
    have hd : HasDerivAt (fun t : ℝ => g i (x + t • v)) (H i x v) 0 := by
      simpa [Function.comp_def] using (hdiff i (x + (0 : ℝ) • v)).comp_hasDerivAt 0 hline
    simpa [hgi i] using hd.tendsto_slope_zero_right
  have hb : Filter.Tendsto (fun t : ℝ => t⁻¹ • gbar (x + t • v))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Hbar x v)) := by
    have hd : HasDerivAt (fun t : ℝ => gbar (x + t • v)) (Hbar x v) 0 := by
      simpa [Function.comp_def] using (hbar (x + (0 : ℝ) • v)).comp_hasDerivAt 0 hline
    simpa [hzero] using hd.tendsto_slope_zero_right
  apply le_of_tendsto_of_tendsto
    (tendsto_finsetSum Finset.univ (fun i _ => (hi i).norm.pow 2))
    ((hb.norm.pow 2).const_mul ((Fintype.card ι : ℝ) * κ))
  exact Filter.Eventually.of_forall fun t => by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, ← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left (hSGC (x + t • v)) (sq_nonneg |t⁻¹|)
    nlinarith [hh]


lemma norm_triple_sq (a b c : E) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have ht := (norm_add_le (a + b) c).trans (add_le_add (norm_add_le a b) le_rfl)
  nlinarith [norm_nonneg (a + b + c), norm_nonneg a, norm_nonneg b, norm_nonneg c,
    sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖c‖ - ‖a‖)]

lemma cubic_hessian_moment_unit [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
    (g : ι → E → E) (H : ι → E → E →L[ℝ] E) (gbar : E → E)
    (κ ρ M : ℝ) (hκ : 1 ≤ κ) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M)
    (hdiff : ∀ i x, HasFDerivAt (g i) (H i x) x)
    (hLip : ∀ x y, ∑ i, ‖H i x - H i y‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ρ ^ 2 * ‖x - y‖ ^ 2)
    (hSGC : ∀ y, ∑ i, ‖g i y‖ ^ 2 ≤ (Fintype.card ι : ℝ) * κ * ‖gbar y‖ ^ 2)
    (x s v w : E) (hs : 0 < ‖s‖) (hv : ‖v‖ = 1)
    (hnew : ‖gbar (x + s)‖ ≤ M * ‖s‖ ^ 2)
    (htilt : ‖gbar (x + (s + ‖s‖ • v))‖ ^ 2 ≤
      2 * ‖s‖ ^ 2 * ‖w‖ ^ 2 + 25 / 2 * M ^ 2 * ‖s‖ ^ 4) :
    ∑ i, ‖H i x v‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * κ * (6 * ‖w‖ ^ 2 + 57 * M ^ 2 * ‖s‖ ^ 2) := by
  have hM : 0 ≤ M := hρ.trans hρM
  have hk0 : 0 ≤ κ := by linarith
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  let z := s + ‖s‖ • v
  let a : ι → E := fun i => g i x + H i x s
  let R : ι → E := fun i => g i (x + z) - g i x - H i x z
  have hz : ‖z‖ ≤ 2 * ‖s‖ := by
    have hh := norm_add_le s (‖s‖ • v)
    simpa [z, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg s), hv,
      two_mul] using hh
  have hz4 : ‖z‖ ^ 4 ≤ 16 * ‖s‖ ^ 4 := by
    have hh := pow_le_pow_left₀ (norm_nonneg z) hz 4
    nlinarith [hh]
  have hr0 := rms_taylor_remainder g H ρ hρ hdiff hLip x z
  have hρsq : ρ ^ 2 ≤ M ^ 2 := by nlinarith
  have hr : ∑ i, ‖R i‖ ^ 2 ≤ 4 * (Fintype.card ι : ℝ) * M ^ 2 * ‖s‖ ^ 4 := by
    have hh := mul_le_mul hρsq hz4 (by positivity) (sq_nonneg M)
    have hh' := mul_le_mul_of_nonneg_left hh hn
    dsimp [R]
    nlinarith [hr0, hh']
  have ha := cubic_residual_moment g H gbar κ ρ M hκ hρ hρM hdiff hLip hSGC x s hnew
  have hg : ∑ i, ‖g i (x + z)‖ ^ 2 ≤ (Fintype.card ι : ℝ) * κ *
      (2 * ‖s‖ ^ 2 * ‖w‖ ^ 2 + 25 / 2 * M ^ 2 * ‖s‖ ^ 4) :=
    (hSGC (x + z)).trans (mul_le_mul_of_nonneg_left htilt (mul_nonneg hn hk0))
  have hi (i : ι) : ‖s‖ ^ 2 * ‖H i x v‖ ^ 2 ≤
      3 * (‖g i (x + z)‖ ^ 2 + ‖a i‖ ^ 2 + ‖R i‖ ^ 2) := by
    have he : g i (x + z) + -(a i) + -(R i) = ‖s‖ • H i x v := by
      dsimp [a, R, z]
      simp only [map_add, map_smul]
      abel
    have hh := norm_triple_sq (g i (x + z)) (-(a i)) (-(R i))
    rw [he] at hh
    simpa only [norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg s), mul_pow] using hh
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hi i)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hkr := mul_nonneg (show 0 ≤ κ - 1 by linarith)
    (show 0 ≤ (Fintype.card ι : ℝ) * M ^ 2 * ‖s‖ ^ 4 by positivity)
  apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hs)).mp
  dsimp [a] at hsum
  nlinarith [hsum, ha, hg, hr, hkr]


lemma cubic_stationary_gradient_norm [NormedSpace ℝ E]
    (H : E →L[ℝ] E) (g s G : E) (M : ℝ) (hM : 0 ≤ M)
    (hs : g + H s + (M / 2 * ‖s‖) • s = 0)
    (hrem : ‖G - (g + H s)‖ ≤ M / 2 * ‖s‖ ^ 2) :
    ‖G‖ ≤ M * ‖s‖ ^ 2 := by
  have he : g + H s = -((M / 2 * ‖s‖) • s) := eq_neg_of_add_eq_zero_left hs
  have hn : ‖g + H s‖ = M / 2 * ‖s‖ ^ 2 := by
    rw [he, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ M / 2 * ‖s‖ by positivity)]
    ring
  have ht := norm_add_le (G - (g + H s)) (g + H s)
  rw [sub_add_cancel, hn] at ht
  linarith

lemma cubic_tilted_gradient_sq [NormedSpace ℝ E]
    (H : E →L[ℝ] E) (g s v G : E) (M : ℝ) (hM : 0 ≤ M) (hv : ‖v‖ = 1)
    (hs : g + H s + (M / 2 * ‖s‖) • s = 0)
    (hrem : ‖G - (g + H (s + ‖s‖ • v))‖ ≤ M / 2 * ‖s + ‖s‖ • v‖ ^ 2) :
    ‖G‖ ^ 2 ≤ 2 * ‖s‖ ^ 2 * ‖H v‖ ^ 2 + 25 / 2 * M ^ 2 * ‖s‖ ^ 4 := by
  have he : g + H (s + ‖s‖ • v) = ‖s‖ • H v - (M / 2 * ‖s‖) • s := by
    have hh : g + H s = -((M / 2 * ‖s‖) • s) := eq_neg_of_add_eq_zero_left hs
    rw [map_add, map_smul, ← add_assoc, hh]
    abel
  have hz : ‖s + ‖s‖ • v‖ ≤ 2 * ‖s‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg s), hv,
      mul_one, two_mul] using norm_add_le s (‖s‖ • v)
  have hzsq : ‖s + ‖s‖ • v‖ ^ 2 ≤ 4 * ‖s‖ ^ 2 := by
    nlinarith [norm_nonneg (s + ‖s‖ • v), norm_nonneg s]
  have hlin : ‖g + H (s + ‖s‖ • v)‖ ≤ ‖s‖ * ‖H v‖ + M / 2 * ‖s‖ ^ 2 := by
    rw [he]
    have hh := norm_sub_le (‖s‖ • H v) ((M / 2 * ‖s‖) • s)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg s),
      abs_of_nonneg (show 0 ≤ M / 2 * ‖s‖ by positivity)] at hh
    nlinarith [hh]
  have ht := norm_add_le (G - (g + H (s + ‖s‖ • v))) (g + H (s + ‖s‖ • v))
  rw [sub_add_cancel] at ht
  have hz' := mul_le_mul_of_nonneg_left hzsq (show 0 ≤ M / 2 by positivity)
  have hb : ‖G‖ ≤ ‖s‖ * ‖H v‖ + 5 / 2 * M * ‖s‖ ^ 2 := by
    linarith
  have hb2 := pow_le_pow_left₀ (norm_nonneg G) hb 2
  nlinarith [hb2, sq_nonneg (‖s‖ * ‖H v‖ - 5 / 2 * M * ‖s‖ ^ 2)]


lemma cubic_hessian_moment [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι]
    (g : ι → E → E) (H : ι → E → E →L[ℝ] E)
    (gbar : E → E) (Hbar : E → E →L[ℝ] E)
    (κ ρ M : ℝ) (hκ : 1 ≤ κ) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M)
    (hdiff : ∀ i x, HasFDerivAt (g i) (H i x) x)
    (hbar : ∀ x, HasFDerivAt gbar (Hbar x) x)
    (hLip : ∀ x y, ∑ i, ‖H i x - H i y‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ρ ^ 2 * ‖x - y‖ ^ 2)
    (hbarLip : ∀ x y, ‖Hbar x - Hbar y‖ ≤ ρ * ‖x - y‖)
    (hSGC : ∀ y, ∑ i, ‖g i y‖ ^ 2 ≤ (Fintype.card ι : ℝ) * κ * ‖gbar y‖ ^ 2)
    (x s : E) (hs : 0 < ‖s‖)
    (hstat : gbar x + Hbar x s + (M / 2 * ‖s‖) • s = 0) (v : E) :
    ∑ i, ‖H i x v‖ ^ 2 ≤ 64 * (Fintype.card ι : ℝ) * κ *
      (‖Hbar x v‖ ^ 2 + M ^ 2 * ‖s‖ ^ 2 * ‖v‖ ^ 2) := by
  have hM : 0 ≤ M := hρ.trans hρM
  have hk0 : 0 ≤ κ := by linarith
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have ht (d : E) : ‖gbar (x + d) - (gbar x + Hbar x d)‖ ≤ M / 2 * ‖d‖ ^ 2 := by
    have hh := CubicRegularization.gradient_taylor hbar hbarLip x d
    rw [sub_add_eq_sub_sub]
    have hm := mul_le_mul_of_nonneg_right hρM (sq_nonneg ‖d‖)
    linarith
  have hu (w : E) (hw : ‖w‖ = 1) : ∑ i, ‖H i x w‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * κ * (6 * ‖Hbar x w‖ ^ 2 + 57 * M ^ 2 * ‖s‖ ^ 2) := by
    exact cubic_hessian_moment_unit g H gbar κ ρ M hκ hρ hρM hdiff hLip hSGC
      x s w (Hbar x w) hs hw
      (cubic_stationary_gradient_norm (Hbar x) (gbar x) s (gbar (x + s)) M hM hstat (ht s))
      (cubic_tilted_gradient_sq (Hbar x) (gbar x) s w
        (gbar (x + (s + ‖s‖ • w))) M hM hw hstat (ht (s + ‖s‖ • w)))
  by_cases hv : v = 0
  · subst v
    simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    simp [w, norm_smul, ne_of_gt hvpos]
  have hscale : ‖v‖ • w = v := by
    simp [w, smul_smul, ne_of_gt hvpos]
  have he (A : E →L[ℝ] E) : ‖A v‖ ^ 2 = ‖v‖ ^ 2 * ‖A w‖ ^ 2 := by
    conv_lhs => rw [← hscale, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hvpos, mul_pow]
  have hh := mul_le_mul_of_nonneg_left (hu w hw) (sq_nonneg ‖v‖)
  have hsum : ∑ i, ‖H i x v‖ ^ 2 = ‖v‖ ^ 2 * ∑ i, ‖H i x w‖ ^ 2 := by
    simp_rw [he]
    rw [Finset.mul_sum]
  rw [hsum, he (Hbar x)]
  have hp := mul_nonneg (mul_nonneg hn hk0) (sq_nonneg ‖Hbar x w‖)
  have hq := mul_nonneg (mul_nonneg hn hk0)
    (show 0 ≤ M ^ 2 * ‖s‖ ^ 2 by positivity)
  have hp' := mul_le_mul_of_nonneg_left (show 6 * ((Fintype.card ι : ℝ) * κ * ‖Hbar x w‖ ^ 2) ≤
      64 * ((Fintype.card ι : ℝ) * κ * ‖Hbar x w‖ ^ 2) by nlinarith [hp]) (sq_nonneg ‖v‖)
  have hq' := mul_le_mul_of_nonneg_left (show 57 * ((Fintype.card ι : ℝ) * κ * M ^ 2 * ‖s‖ ^ 2) ≤
      64 * ((Fintype.card ι : ℝ) * κ * M ^ 2 * ‖s‖ ^ 2) by nlinarith [hq]) (sq_nonneg ‖v‖)
  nlinarith [hh, hp', hq']

lemma cubic_hessian_moment_all_steps [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι]
    (g : ι → E → E) (H : ι → E → E →L[ℝ] E)
    (gbar : E → E) (Hbar : E → E →L[ℝ] E)
    (κ ρ M : ℝ) (hκ : 1 ≤ κ) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M)
    (hdiff : ∀ i x, HasFDerivAt (g i) (H i x) x)
    (hbar : ∀ x, HasFDerivAt gbar (Hbar x) x)
    (hLip : ∀ x y, ∑ i, ‖H i x - H i y‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ρ ^ 2 * ‖x - y‖ ^ 2)
    (hbarLip : ∀ x y, ‖Hbar x - Hbar y‖ ≤ ρ * ‖x - y‖)
    (hSGC : ∀ y, ∑ i, ‖g i y‖ ^ 2 ≤ (Fintype.card ι : ℝ) * κ * ‖gbar y‖ ^ 2)
    (x s : E) (hstat : gbar x + Hbar x s + (M / 2 * ‖s‖) • s = 0) (v : E) :
    ∑ i, ‖H i x v‖ ^ 2 ≤ 64 * (Fintype.card ι : ℝ) * κ *
      (‖Hbar x v‖ ^ 2 + M ^ 2 * ‖s‖ ^ 2 * ‖v‖ ^ 2) := by
  by_cases hs : s = 0
  · have hg : gbar x = 0 := by simpa [hs] using hstat
    have hh := stationary_sgc_hessian_moment g H gbar Hbar κ hdiff hbar hSGC x v hg
    have hp : 0 ≤ (Fintype.card ι : ℝ) * κ * ‖Hbar x v‖ ^ 2 := by positivity
    simp only [hs, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero]
    nlinarith
  · exact cubic_hessian_moment g H gbar Hbar κ ρ M hκ hρ hρM hdiff hbar hLip
      hbarLip hSGC x s (norm_pos_iff.mpr hs) hstat v

end LongTails.Proofs.CoupledCubicMoments
