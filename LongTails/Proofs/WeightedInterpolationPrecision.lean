import LongTails.Proofs.WeightedInterpolationAllocation
import LongTails.Proofs.WeakInterpolationGeometry

namespace LongTails.Proofs.WeightedInterpolationPrecision

open LongTails.Setups.DistributedWeakInterpolation LongTails.Algorithms.WeakInterpolationDesign
open LongTails.Algorithms.WeightedInterpolationSgd WeakInterpolationDesign WeightedInterpolationAllocation

variable {p : Params}

lemma noise_nonneg (hp : spec.valid p) : 0 ≤ noiseRadius p := by
  apply div_nonneg _ (cap_pos hp).le
  exact mul_nonneg hp.2.2.2.2.2.1
    ((profile_nonneg hp 0).trans (Finset.le_sup' (profile p) (Finset.mem_univ 0)))

lemma alpha_profile (hp : spec.valid p) (i : Fin p.n) :
    weights p i / fraction p i ≤ 2 * (∑ j, (p.h j : ℝ)⁻¹) * profile p i := by
  have hh : 0 < (p.h i : ℝ) := by exact_mod_cast hp.1 i
  have h := mul_le_mul_of_nonneg_left (fraction_cost hp i) (weight_nonneg hp i)
  calc
    _ = weights p i * (1 / fraction p i) := by ring
    _ ≤ _ := h
    _ = _ := by change profile p i / (p.h i : ℝ) * _ = _; field_simp

lemma alpha_bounds (hp : spec.valid p) (k : ℕ) (i : Fin p.n) :
    let a := stepSize p k * weights p i / fraction p i
    0 ≤ a ∧ a * p.L i ≤ 1 ∧ a * p.σ ≤ noiseRadius p := by
  dsimp only
  obtain ⟨ht, htC⟩ := step_bounds hp k
  have hw := weight_nonneg hp i
  have hq := fraction_pos p i
  have hh := alpha_profile hp i
  have hs := speed_pos hp
  have hm := cap_pos hp
  have hcap : profile p i * p.L i ≤ largestCurvature p :=
    Finset.le_sup' (fun j => profile p j * p.L j) (Finset.mem_univ i)
  have hκ := mul_le_mul_of_nonneg_left hcap (mul_nonneg ht (mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num) hs.le))
  have h1 := mul_le_mul_of_nonneg_left hh (mul_nonneg ht (hp.2.1 i))
  unfold smoothness at htC
  have hσ := hp.2.2.2.2.2.1
  have hmax : profile p i ≤ Finset.univ.sup' Finset.univ_nonempty (profile p) :=
    Finset.le_sup' (profile p) (Finset.mem_univ i)
  have h2 := mul_le_mul_of_nonneg_left hh ht
  have h3 := mul_le_mul_of_nonneg_right h2 (mul_nonneg hσ hm.le)
  constructor
  · exact div_nonneg (mul_nonneg ht hw) hq.le
  constructor
  · rw [mul_div_assoc]
    calc
      _ ≤ (1 / 2 : ℝ) := by linear_combination h1 + hκ + htC
      _ ≤ _ := by norm_num
  · rw [noiseRadius, le_div_iff₀ hm, mul_div_assoc]
    have h4 := mul_le_mul_of_nonneg_right htC (mul_nonneg hσ (profile_nonneg hp i))
    nlinarith [mul_le_mul_of_nonneg_left hmax hσ, mul_nonneg hσ (profile_nonneg hp i)]

lemma scale_bounds (hp : spec.valid p) :
    0 < scale p ∧ Real.sqrt p.ε ≤ scale p ∧ p.R ≤ scale p := by
  have he := Real.sqrt_pos.mpr hp.2.2.2.2.2.2
  have hn := noise_nonneg hp
  have hK : 1 ≤ (rounds p : ℝ) := by exact_mod_cast (show 1 ≤ rounds p by unfold rounds; omega)
  have hR := hp.2.2.2.2.1
  unfold scale
  constructor
  · positivity
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hK) he.le,
    mul_nonneg (zero_le_one.trans hK) hn]

lemma tolerance_pos (hp : spec.valid p) : 0 < tolerance p := by
  have hK : 0 < (rounds p : ℝ) := by exact_mod_cast (show 0 < rounds p by unfold rounds; omega)
  exact div_pos hp.2.2.2.2.2.2 (by have := (scale_bounds hp).1; positivity)

lemma guard_nonneg (hp : spec.valid p) : 0 ≤ guardRadius p := by
  unfold guardRadius
  have hR := hp.2.2.2.2.1
  have he := tolerance_pos hp
  positivity

lemma radius_eq (hp : spec.valid p) (x : Point p) :
    Algorithms.DistributedBatchedSgd.radius (rawParams p) x =
      2 * (guardRadius p + ‖x - p.x0‖) + Real.sqrt p.ε := by
  change 2 * (Real.sqrt (2 * 1 * (guardRadius p ^ 2 / 2)) + 1 * _) + _ + 32 * 0 ^ 2 / _ = _
  rw [show 2 * 1 * (guardRadius p ^ 2 / 2) = guardRadius p ^ 2 by ring,
    Real.sqrt_sq (guard_nonneg hp)]
  simp [rawParams, transport]
  rfl

lemma local_radius (hp : spec.valid p) (k : ℕ) (i : Fin p.n) (f : Functions p)
    (hlip : ∀ x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x - y‖)
    {z : Point p} (hz : z ∈ solutions p f) (hinit : ‖p.x0-z‖ ≤ p.R) (x : Point p) :
    let a := stepSize p k * weights p i / fraction p i
    ‖a • gradient (f i) x‖ ≤ ‖x-p.x0‖ + p.R := by
  dsimp only
  let a := stepSize p k * weights p i / fraction p i
  obtain ⟨ha, haL, _⟩ := alpha_bounds hp k i
  have hzero : gradient (f i) z = 0 := by
    simp [gradient, ((hz i).isLocalMin Filter.univ_mem).fderiv_eq_zero]
  have hg := hlip x z
  rw [hzero, sub_zero] at hg
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  have hdist := norm_sub_le_norm_sub_add_norm_sub x p.x0 z
  nlinarith [mul_le_mul_of_nonneg_left hg ha, mul_le_mul_of_nonneg_right haL (norm_nonneg (x-z))]

lemma level_bound (p : Params) :
    64 * (1 + Real.sqrt p.d) * (guardRadius p + scale p) / tolerance p ≤
      ((2 ^ ((width p : ℕ)) - 1 : ℕ) : ℝ) := by
  let a := 64 * (1 + Real.sqrt p.d) * (guardRadius p + scale p) / tolerance p
  have h := Nat.lt_size_self ⌈a⌉₊
  have he : (width p : ℕ) = Nat.size ⌈a⌉₊ + 1 := rfl
  have hn : ⌈a⌉₊ ≤ 2 ^ (width p : ℕ) - 1 := by rw [he, pow_succ]; omega
  exact (Nat.le_ceil _).trans (by exact_mod_cast hn)

lemma bias_margin (hp : spec.valid p) (x u : Point p) (hu : ‖u‖ ≤ ‖x-p.x0‖ + p.R) :
    let r := Algorithms.DistributedBatchedSgd.radius (rawParams p) x
    ‖u‖ < r ∧ noiseRadius p ^ 2 / (r - ‖u‖) ≤ tolerance p := by
  dsimp only
  rw [radius_eq hp]
  have he := tolerance_pos hp
  have hnoise := div_nonneg (sq_nonneg (noiseRadius p)) he.le
  have hpos := Real.sqrt_pos.mpr hp.2.2.2.2.2.2
  have hR := hp.2.2.2.2.1
  have hg : p.R + noiseRadius p ^ 2 / tolerance p ≤ guardRadius p := by
    unfold guardRadius; linarith
  have hmargin : 0 < 2*(guardRadius p + ‖x-p.x0‖) + Real.sqrt p.ε - ‖u‖ := by
    linarith [norm_nonneg (x-p.x0)]
  refine ⟨by linarith, (div_le_iff₀ hmargin).mpr ?_⟩
  have hsmall : noiseRadius p ^ 2 / tolerance p ≤
      2*(guardRadius p + ‖x-p.x0‖) + Real.sqrt p.ε - ‖u‖ := by
    linarith [norm_nonneg (x-p.x0)]
  linarith [(div_le_iff₀ he).mp hsmall]

lemma grid_error (hp : spec.valid p) (T : DistributedTemplate.Time) (x z : Point p) (hR : ‖p.x0-z‖ ≤ p.R) :
    Real.sqrt (p.d * Algorithms.DistributedBatchedSgd.spacing (rawParams p) (rawConfig p T) x ^ 2) ≤
      tolerance p * (1 + ‖x-z‖ / scale p) := by
  let r := Algorithms.DistributedBatchedSgd.radius (rawParams p) x
  let M : ℝ := ((2 ^ (width p : ℕ) - 1 : ℕ) : ℝ)
  have hM : 0 < M := Nat.cast_pos.mpr (show 0 < 2 ^ (width p : ℕ) - 1 from DistributedBatchedSgd.levels_pos (rawConfig p T))
  have hsc := (scale_bounds hp).1
  have htol := tolerance_pos hp
  have hg := guard_nonneg hp
  have hs := scale_bounds hp
  have hr : 0 ≤ r := by dsimp [r]; rw [radius_eq hp]; positivity
  have hx := norm_sub_le_norm_sub_add_norm_sub x z p.x0
  rw [norm_sub_rev z p.x0] at hx
  have hr' : r ≤ 3 * (guardRadius p + scale p) + 2 * ‖x-z‖ := by
    dsimp [r]; rw [radius_eq hp]; linarith [hs.2.1, hs.2.2]
  change Real.sqrt ((p.d : ℝ) * (2 * r / M) ^ 2) ≤ _
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity), ← mul_div_assoc,
    div_le_iff₀ hM]
  have hwidth := (div_le_iff₀ htol).mp (level_bound p)
  change _ ≤ M * tolerance p at hwidth
  have hmajor : Real.sqrt p.d * (2*r) ≤
      64*(1+Real.sqrt p.d)*(guardRadius p+scale p)*(1+‖x-z‖/scale p) := by
    have h1 := mul_le_mul_of_nonneg_left hr' (Real.sqrt_nonneg (p.d : ℝ))
    have h2 := mul_nonneg (Real.sqrt_nonneg (p.d : ℝ)) (norm_nonneg (x-z))
    have h3 : 0 ≤ Real.sqrt p.d * guardRadius p * (‖x-z‖/scale p) := by positivity
    have h4 : 0 ≤ Real.sqrt p.d * (guardRadius p + scale p) := by positivity
    have hid : scale p * (‖x-z‖/scale p) = ‖x-z‖ := by field_simp
    have h5 := mul_nonneg (by linarith : 0 ≤ guardRadius p + scale p) (by positivity : 0 ≤ 1+‖x-z‖/scale p)
    linarith only [h1,h2,h3,h4,h5,congrArg (fun a => Real.sqrt p.d * a) hid]
  apply hmajor.trans
  nlinarith [mul_le_mul_of_nonneg_right hwidth (show 0 ≤ 1+‖x-z‖/scale p by positivity)]

end LongTails.Proofs.WeightedInterpolationPrecision
