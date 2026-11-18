import LongTails.Proofs.FiniteSumNondualLowerComponents
import LongTails.Proofs.GdConvex
import LongTails.Setups.FlatTransferDueling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open scoped RealInnerProductSpace
open LongTails.Setups.StronglyConvexDueling

namespace LongTails.Proofs.DuelingSignFamily

open FiniteSumNondualLowerComponents

def sign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def phase (h t : ℝ) (b : Bool) := (t - sign b * h / 4) / h

noncomputable def profile (h : ℝ) (b : Bool) (t : ℝ) :=
  t^2 / 2 - sign b * h^2 / 4 * Real.sin (phase h t b)

noncomputable def slope (h : ℝ) (b : Bool) (t : ℝ) :=
  t - sign b * h / 4 * Real.cos (phase h t b)

noncomputable def loss {d : ℕ} (h : ℝ) (θ : Fin d → Bool) :=
  separableEnergy (fun i => profile h (θ i))

noncomputable def field {d : ℕ} (h : ℝ) (θ : Fin d → Bool) :=
  separableSlope (fun i => slope h (θ i))

noncomputable def center {d : ℕ} (h : ℝ) (θ : Fin d → Bool) : Point d :=
  WithLp.toLp 2 (fun i => sign (θ i) * h / 4)

lemma sine_model (x y : ℝ) :
    |Real.sin y - Real.sin x - Real.cos x * (y-x)| ≤ (y-x)^2 / 2 := by
  have hg (t : ℝ) : HasGradientAt Real.sin (Real.cos t) t := by
    simpa using (Real.hasDerivAt_sin t).hasGradientAt
  have hn (t : ℝ) : HasGradientAt (fun z => -Real.sin z) (-Real.cos t) t := by
    exact (Real.hasDerivAt_sin t).fun_neg.hasGradientAt'
  have hl (a b : ℝ) : ‖Real.cos a - Real.cos b‖ ≤ 1 * ‖a-b‖ := by
    simpa using Real.abs_cos_sub_cos_le a b
  have hnl (a b : ℝ) : ‖-Real.cos a - -Real.cos b‖ ≤ 1 * ‖a-b‖ := by
    simpa only [neg_sub_neg, norm_sub_rev (Real.cos b) (Real.cos a)] using hl a b
  have hu := OracleTemplate.Gradient.smooth_upper_bound hg hl x y
  have hd := OracleTemplate.Gradient.smooth_upper_bound hn hnl x y
  simp only [Real.inner_apply, Real.norm_eq_abs, sq_abs] at hu hd
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma profile_model {h : ℝ} (hh : 0 < h) (b : Bool) (x y : ℝ) :
    (y-x)^2/4 ≤ profile h b y - profile h b x - slope h b x * (y-x) ∧
    profile h b y - profile h b x - slope h b x * (y-x) ≤ (y-x)^2 := by
  have ht := abs_le.mp (sine_model (phase h x b) (phase h y b))
  have he : phase h y b - phase h x b = (y-x)/h := by unfold phase; ring
  rw [he] at ht
  have hlo := mul_le_mul_of_nonneg_left ht.1 (sq_nonneg h)
  have hhi := mul_le_mul_of_nonneg_left ht.2 (sq_nonneg h)
  field_simp [hh.ne'] at hlo hhi
  cases b <;> simp [slope,profile,sign] at * <;> constructor <;> nlinarith [sq_nonneg (y-x)]

lemma profile_lipschitz {h : ℝ} (hh : 0 < h) (b : Bool) (x y : ℝ) :
    |slope h b x-slope h b y| ≤ 2*|x-y| := by
  have hc := Real.abs_cos_sub_cos_le (phase h x b) (phase h y b)
  rw [show phase h x b - phase h y b = (x-y)/h by unfold phase; ring,
    abs_div, abs_of_pos hh] at hc
  have ha : |sign b| = 1 := by cases b <;> norm_num [sign]
  rw [show slope h b x - slope h b y =
    (x-y) + (-(sign b*h/4))*(Real.cos (phase h x b)-Real.cos (phase h y b)) by unfold slope; ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_neg, abs_div, abs_mul, ha, abs_of_pos hh]
  have hh' := (le_div_iff₀ hh).mp hc
  norm_num
  nlinarith [abs_nonneg (x-y)]

lemma gradient_loss {d : ℕ} {h : ℝ} (hh : 0 < h) (θ : Fin d → Bool) (x : Point d) :
    HasGradientAt (loss h θ) (field h θ x) x :=
  separable_hasGradientAt _ _ (fun j a b => ⟨(by nlinarith [sq_nonneg (b-a),
    (profile_model hh (θ j) a b).1]), (profile_model hh (θ j) a b).2⟩) x

lemma strong_loss {d : ℕ} {h : ℝ} (hh : 0 < h) (θ : Fin d → Bool) (x y : Point d) :
    loss h θ x + ⟪field h θ x,y-x⟫ + (1/4:ℝ)*‖y-x‖^2 ≤ loss h θ y := by
  have hm := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin d) _ =>
    (profile_model hh (θ i) (x i) (y i)).1)
  simp only [loss, separableEnergy, field, separableSlope, PiLp.inner_apply, RCLike.inner_apply,
    EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply, conj_trivial]
  simp only [← Finset.sum_div, Finset.sum_sub_distrib] at hm
  simpa only [mul_comm] using (by linarith : (∑ i, profile h (θ i) (x i)) +
    (∑ i, slope h (θ i) (x i) * (y i-x i)) + (1/4:ℝ)*(∑ i, (y i-x i)^2)
    ≤ ∑ i, profile h (θ i) (y i))

lemma field_center {d : ℕ} (h : ℝ) (θ : Fin d → Bool) : field h θ (center h θ) = 0 := by
  ext i
  simp [field, separableSlope, center, slope, phase]

end LongTails.Proofs.DuelingSignFamily
