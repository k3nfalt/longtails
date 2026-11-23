import LongTails.Proofs.OptimumHeterogeneityAllocation
import LongTails.Proofs.OptimumHeterogeneityGrowth

namespace LongTails.Proofs.OptimumHeterogeneityPrecision

open LongTails.Setups.DistributedOptimumHeterogeneity LongTails.Algorithms.OptimumHeterogeneityDesign
open LongTails.Algorithms.OptimumHeterogeneitySgd OptimumHeterogeneityAllocation OptimumHeterogeneityGrowth

variable {p : Params}

lemma noise_nonneg (hp : spec.valid p) : 0 ≤ noiseRadius p := by
  unfold noiseRadius
  have := capacity_nn hp (v := fun _ => 1) (fun _ => zero_le_one)
  have := hp.1.2.2.2.2.2.1
  have := hp.2
  positivity

lemma multiplier_bounds (hp : spec.valid p) (k : ℕ) (i : Fin p.n) :
    let a := multiplier p i k
    0 ≤ a ∧ a * p.L i ≤ 1 ∧ a * (p.σ + Real.sqrt p.n * p.ζ) ≤ noiseRadius p := by
  dsimp only [multiplier]
  have hw := weight_nn hp i
  obtain ⟨he,hm,hL⟩ := step_bounds hp k
  have hq := fraction_pos p i
  have hα := mul_le_mul_of_nonneg_left (capacity_bound hp p.L hp.1.2.1 i) he
  have ha : weights p i / fraction p i ≤ capacity p (fun _ => 1) := by
    simpa only [mul_one] using capacity_bound hp (fun _ => 1) (fun _ => zero_le_one) i
  have ht := mul_le_mul hm ha (div_nonneg hw hq.le) (by positivity)
  have hσ := hp.1.2.2.2.2.2.1
  have hζ := hp.2
  have hr := mul_le_mul_of_nonneg_right ht
    (by positivity : 0 ≤ p.σ + Real.sqrt p.n * p.ζ)
  refine ⟨div_nonneg (mul_nonneg he hw) hq.le, ?_, ?_⟩
  · rw [mul_div_assoc, mul_assoc]
    linarith only [hα,hL]
  · unfold noiseRadius
    calc
      _ = (stepSize p k * (weights p i / fraction p i)) * _ := by ring
      _ ≤ _ := hr
      _ = _ := by ring

lemma scale_bounds (hp : spec.valid p) :
    0 < scale p ∧ p.ε ≤ scale p ∧ p.R ≤ scale p := by
  have he := hp.1.2.2.2.2.2.2
  have hn := noise_nonneg hp
  have hK : 1 ≤ (rounds p : ℝ) := by exact_mod_cast (show 1 ≤ rounds p by unfold rounds; omega)
  have hR := hp.1.2.2.2.2.1
  unfold scale
  constructor
  · positivity
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hK) he.le,
    mul_nonneg (zero_le_one.trans hK) hn]

lemma tolerance_pos (hp : spec.valid p) : 0 < tolerance p := by
  have hK : 0 < (rounds p : ℝ) := by exact_mod_cast (show 0 < rounds p by unfold rounds; omega)
  exact div_pos (sq_pos_of_pos hp.1.2.2.2.2.2.2) (by have := (scale_bounds hp).1; positivity)

lemma guard_nonneg (hp : spec.valid p) : 0 ≤ guardRadius p := by
  unfold guardRadius
  have hε := hp.1.2.2.2.2.2.2
  have := noise_nonneg hp
  have hR := hp.1.2.2.2.2.1
  have he := tolerance_pos hp
  positivity

lemma radius_eq (hp : spec.valid p) (x : Point p) :
    Algorithms.DistributedBatchedSgd.radius (transport p) x =
      2 * (guardRadius p + ‖x - p.x0‖) + p.ε := by
  change 2 * (Real.sqrt (2 * 1 * (guardRadius p ^ 2 / 2)) + 1 * _) + _ + 32 * 0 ^ 2 / _ = _
  rw [show 2 * 1 * (guardRadius p ^ 2 / 2) = guardRadius p ^ 2 by ring,
    Real.sqrt_sq (guard_nonneg hp)]
  simp [transport, Real.sqrt_sq hp.1.2.2.2.2.2.2.le]
  rfl

lemma local_radius {f : Functions p} {z : Point p} (D : Geometry p f z) (k : ℕ) (i : Fin p.n) (x : Point p) :
    ‖multiplier p i k • gradient (f i) x‖ ≤ ‖x-p.x0‖ + p.R + noiseRadius p := by
  obtain ⟨ha,hL,hN⟩ := multiplier_bounds D.valid k i
  have h₁ := (Finset.single_le_sum (s := Finset.univ) (f := fun j => ‖gradient (f j) z‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)).trans D.offsets
  have h₂ : ‖gradient (f i) z‖ ≤ Real.sqrt p.n * p.ζ := by
    have hn : 0 ≤ (p.n : ℝ) := by positivity
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) D.valid.2)
    rwa [mul_pow, Real.sq_sqrt hn]
  have h₃ := norm_le_norm_sub_add (gradient (f i) x) (gradient (f i) z)
  have h₄ := norm_sub_le_norm_sub_add_norm_sub x p.x0 z
  have hσ := D.valid.1.2.2.2.2.2.1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  nlinarith only [mul_le_mul_of_nonneg_left h₃ ha, mul_le_mul_of_nonneg_left (D.lip i x z) ha,
    mul_le_mul_of_nonneg_left h₂ ha, mul_le_mul_of_nonneg_right hL (norm_nonneg (x-z)),
    mul_nonneg ha hσ, h₄, D.initial, hN]

lemma level_bound (p : Params) :
    64 * (1 + Real.sqrt p.d) * (guardRadius p + scale p) / tolerance p ≤
      ((2 ^ ((width p : ℕ)) - 1 : ℕ) : ℝ) := by
  let a := 64 * (1 + Real.sqrt p.d) * (guardRadius p + scale p) / tolerance p
  have h := Nat.lt_size_self ⌈a⌉₊
  have he : (width p : ℕ) = Nat.size ⌈a⌉₊ + 1 := rfl
  have hn : ⌈a⌉₊ ≤ 2 ^ (width p : ℕ) - 1 := by rw [he, pow_succ]; omega
  exact (Nat.le_ceil _).trans (by exact_mod_cast hn)

lemma bias_margin (hp : spec.valid p) (x u : Point p) (hu : ‖u‖ ≤ ‖x-p.x0‖ + p.R + noiseRadius p) :
    let r := Algorithms.DistributedBatchedSgd.radius (transport p) x
    ‖u‖ < r ∧ noiseRadius p ^ 2 / (r - ‖u‖) ≤ tolerance p := by
  dsimp only
  rw [radius_eq hp]
  have he := tolerance_pos hp
  have hnoise := div_nonneg (sq_nonneg (noiseRadius p)) he.le
  have hpos := hp.1.2.2.2.2.2.2
  have hR := hp.1.2.2.2.2.1
  have hg : p.R + noiseRadius p + noiseRadius p ^ 2 / tolerance p ≤ guardRadius p := by
    unfold guardRadius; linarith
  have := noise_nonneg hp
  have hmargin : 0 < 2*(guardRadius p + ‖x-p.x0‖) + p.ε - ‖u‖ := by
    linarith [norm_nonneg (x-p.x0)]
  refine ⟨by linarith, (div_le_iff₀ hmargin).mpr ?_⟩
  have hsmall : noiseRadius p ^ 2 / tolerance p ≤
      2*(guardRadius p + ‖x-p.x0‖) + p.ε - ‖u‖ := by
    linarith [norm_nonneg (x-p.x0)]
  linarith [(div_le_iff₀ he).mp hsmall]

lemma grid_error (hp : spec.valid p) (T : DistributedTemplate.Time) (x z : Point p) (hR : ‖p.x0-z‖ ≤ p.R) :
    Real.sqrt (p.d * Algorithms.DistributedBatchedSgd.spacing (transport p) (config p T) x ^ 2) ≤
      tolerance p * (1 + ‖x-z‖ / scale p) := by
  let r := Algorithms.DistributedBatchedSgd.radius (transport p) x
  let M : ℝ := ((2 ^ (width p : ℕ) - 1 : ℕ) : ℝ)
  have hM : 0 < M := Nat.cast_pos.mpr (show 0 < 2 ^ (width p : ℕ) - 1 from DistributedBatchedSgd.levels_pos (config p T))
  have hsc := (scale_bounds hp).1
  have htol := tolerance_pos hp
  have hg := guard_nonneg hp
  have hs := scale_bounds hp
  have hε := hp.1.2.2.2.2.2.2
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

end LongTails.Proofs.OptimumHeterogeneityPrecision
