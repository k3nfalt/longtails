import LongTails.Algorithms.HeavyTailSaddleEstimator
import LongTails.Proofs.RobustEnergyConcentration
import LongTails.Proofs.TemporalAcceleratedEnergy
import LongTails.Proofs.AdaptiveOracleConcentration
import LongTails.Proofs.StochasticGeneralizedConcentration
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailSaddleEnergy

open OracleTemplate.TemporalDiscrepancy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma tilted_descent {f : E → ℝ} {A t : ℝ} (ht : 0 ≤ t) (hAt : A * t ≤ 1)
    (y g e : E)
    (hs : ∀ v, f v ≤ f y + ⟪g, v - y⟫ + A / 2 * ‖v - y‖ ^ 2) :
    f (y - t • (g + e)) + ⟪e, y - t • (g + e)⟫ ≤
      f y + ⟪e, y⟫ - t / 2 * ‖g + e‖ ^ 2 := by
  have h := hs (y - t • (g + e))
  have heq : y - t • (g + e) - y = -t • (g + e) := by module
  rw [heq, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  have hi : ⟪g, g + e⟫ + ⟪e, g + e⟫ = ‖g + e‖ ^ 2 := by
    rw [← inner_add_left, real_inner_self_eq_norm_sq]
  have hb := mul_le_mul_of_nonneg_right hAt (mul_nonneg ht (sq_nonneg ‖g + e‖))
  rw [inner_sub_right, inner_smul_right]
  nlinarith

lemma tilted_energy_step {f : E → ℝ} {m a : ℝ}
    (hm : 0 < m) (ha : 0 ≤ a) (ha1 : a ≤ 1) (x z u g e : E)
    (hx : f (acceleratedQuery a (x, z)) +
      ⟪g, x - acceleratedQuery a (x, z)⟫ +
        m / 2 * ‖x - acceleratedQuery a (x, z)‖ ^ 2 ≤ f x)
    (hu : f (acceleratedQuery a (x, z)) +
      ⟪g, u - acceleratedQuery a (x, z)⟫ +
        m / 2 * ‖u - acceleratedQuery a (x, z)‖ ^ 2 ≤ f u)
    (hd : f (acceleratedUpdate a m (x, z) (g + e)).1 +
        ⟪e, (acceleratedUpdate a m (x, z) (g + e)).1⟫ ≤
      f (acceleratedQuery a (x, z)) + ⟪e, acceleratedQuery a (x, z)⟫ -
        a ^ 2 / (2 * m) * ‖g + e‖ ^ 2) :
    f (acceleratedUpdate a m (x, z) (g + e)).1 - f u +
        m / 2 * ‖(acceleratedUpdate a m (x, z) (g + e)).2 - u‖ ^ 2 ≤
      (1 - a) * (f x - f u + m / 2 * ‖z - u‖ ^ 2) -
        a * ⟪(acceleratedUpdate a m (x, z) g).2 - u, e⟫ +
        a ^ 2 / m * ‖e‖ ^ 2 := by
  let fe := fun w => f w + ⟪e, w⟫
  have hx' : fe (acceleratedQuery a (x, z)) +
      ⟪g + e, x - acceleratedQuery a (x, z)⟫ +
        m / 2 * ‖x - acceleratedQuery a (x, z)‖ ^ 2 ≤ fe x := by
    dsimp [fe]
    simp only [inner_add_left, inner_sub_right] at hx ⊢
    linarith
  have hu' : fe (acceleratedQuery a (x, z)) +
      ⟪g + e, u - acceleratedQuery a (x, z)⟫ +
        m / 2 * ‖u - acceleratedQuery a (x, z)‖ ^ 2 ≤ fe u := by
    dsimp [fe]
    simp only [inner_add_left, inner_sub_right] at hu ⊢
    linarith
  have h := accelerated_energy_step (f := fe) hm ha ha1 x z u (g + e) hx' hu' hd
  have hden : 1 + a ≠ 0 := by positivity
  have heq : (1 - a) • x - (acceleratedUpdate a m (x, z) (g + e)).1 + a • u =
      -a • ((acceleratedUpdate a m (x, z) g).2 - u) + (a ^ 2 / m) • e := by
    dsimp [acceleratedUpdate, acceleratedQuery]
    match_scalars
    all_goals (field_simp <;> ring)
  have hip := congrArg (fun w => ⟪e, w⟫) heq
  simp only [inner_add_right, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq] at hip
  rw [real_inner_comm e ((acceleratedUpdate a m (x, z) g).2 - u)]
  simp only [inner_sub_right]
  dsimp [fe] at h
  nlinarith

lemma accelerated_noisy_step {f : E → ℝ} {m a A : ℝ}
    (hm : 0 < m) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hstep : A * a ^ 2 ≤ m)
    (x z u g e : E) (hmin : ∀ v, f u ≤ f v)
    (hsc : ∀ v, f (acceleratedQuery a (x, z)) +
      ⟪g, v - acceleratedQuery a (x, z)⟫ +
        m / 2 * ‖v - acceleratedQuery a (x, z)‖ ^ 2 ≤ f v)
    (hsm : ∀ v, f v ≤ f (acceleratedQuery a (x, z)) +
      ⟪g, v - acceleratedQuery a (x, z)⟫ +
        A / 2 * ‖v - acceleratedQuery a (x, z)‖ ^ 2) :
    (f (acceleratedUpdate a m (x, z) (g + e)).1 - f u +
        m / 2 * ‖(acceleratedUpdate a m (x, z) (g + e)).2 - u‖ ^ 2 ≤
      (1 - a) * (f x - f u + m / 2 * ‖z - u‖ ^ 2) -
        a * ⟪(acceleratedUpdate a m (x, z) g).2 - u, e⟫ +
        a ^ 2 / m * ‖e‖ ^ 2) ∧
      ‖(acceleratedUpdate a m (x, z) g).2 - u‖ ^ 2 ≤
        2 * (f x - f u + m / 2 * ‖z - u‖ ^ 2) / m := by
  have ht : 0 ≤ a ^ 2 / m := div_nonneg (sq_nonneg _) hm.le
  have hAt : A * (a ^ 2 / m) ≤ 1 := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hm).mpr (by simpa using hstep)
  have hd (e' : E) : f (acceleratedUpdate a m (x, z) (g + e')).1 +
        ⟪e', (acceleratedUpdate a m (x, z) (g + e')).1⟫ ≤
      f (acceleratedQuery a (x, z)) + ⟪e', acceleratedQuery a (x, z)⟫ -
        a ^ 2 / (2 * m) * ‖g + e'‖ ^ 2 := by
    simpa only [acceleratedUpdate, div_div, mul_comm m 2] using
      tilted_descent ht hAt (acceleratedQuery a (x, z)) g e' hsm
  refine ⟨tilted_energy_step hm ha ha1 x z u g e (hsc x) (hsc u) (hd e), ?_⟩
  have hd0 := hd (0 : E)
  simp only [add_zero, inner_zero_left] at hd0
  have he := accelerated_energy_step hm ha ha1 x z u g (hsc x) (hsc u) hd0
  have hP : 0 ≤ f x - f u + m / 2 * ‖z - u‖ ^ 2 :=
    add_nonneg (sub_nonneg.mpr (hmin x)) (by positivity)
  have hgap := hmin (acceleratedUpdate a m (x, z) g).1
  apply (le_div_iff₀ hm).mpr
  nlinarith [mul_nonneg ha hP]

lemma accelerated_query_gradient_sq {m H B a gap : ℝ}
    (hm : 0 < m) (hH : 0 ≤ H) (ha : 0 ≤ a) (hstep : a ^ 2 * H ≤ m)
    (x z u : E) (g : E → E) (hgap : 0 ≤ gap)
    (henergy : gap + m / 2 * ‖z - u‖ ^ 2 ≤ 4 * B)
    (hxdist : m * ‖x - u‖ ^ 2 ≤ 2 * gap) (hg : ‖g x‖ ^ 2 ≤ 2 * H * gap)
    (hl : ‖g (acceleratedQuery a (x, z)) - g x‖ ≤
      H * ‖acceleratedQuery a (x, z) - x‖) :
    ‖g (acceleratedQuery a (x, z))‖ ^ 2 ≤ 72 * H * B := by
  have hden : 0 < 1 + a := by linarith
  have heq : acceleratedQuery a (x, z) - x = (a / (1 + a)) • (z - x) := by
    dsimp [acceleratedQuery]
    match_scalars
    all_goals (field_simp <;> ring)
  have hratio : a / (1 + a) ≤ a := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg a]
  have hdist : ‖z - x‖ ≤ ‖z - u‖ + ‖x - u‖ := by
    simpa only [norm_sub_rev u x] using norm_sub_le_norm_sub_add_norm_sub z u x
  have hy : ‖acceleratedQuery a (x, z) - x‖ ≤ a * (‖z - u‖ + ‖x - u‖) := by
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hden.le)]
    exact mul_le_mul hratio hdist (norm_nonneg _) ha
  have hq : ‖g (acceleratedQuery a (x, z))‖ ≤
      ‖g x‖ + H * a * ‖z - u‖ + H * a * ‖x - u‖ := by
    have hn := norm_sub_le_norm_sub_add_norm_sub (g (acceleratedQuery a (x, z))) (g x) 0
    simp only [sub_zero] at hn
    have hh := mul_le_mul_of_nonneg_left hy hH
    nlinarith only [hn, hl, hh]
  have hgapB : gap ≤ 4 * B := by nlinarith [sq_nonneg ‖z - u‖]
  have hzB : m * ‖z - u‖ ^ 2 ≤ 8 * B := by linarith
  have hxB : m * ‖x - u‖ ^ 2 ≤ 8 * B := by linarith
  have hgB : ‖g x‖ ^ 2 ≤ 8 * H * B := by
    nlinarith [mul_le_mul_of_nonneg_left hgapB hH]
  have hscaled (v : E) (hv : m * ‖v - u‖ ^ 2 ≤ 8 * B) :
      (H * a * ‖v - u‖) ^ 2 ≤ 8 * H * B := by
    have h1 := mul_le_mul_of_nonneg_left hstep (mul_nonneg hH (sq_nonneg ‖v - u‖))
    have h2 := mul_le_mul_of_nonneg_left hv hH
    nlinarith only [h1, h2]
  have hq2 := pow_le_pow_left₀ (norm_nonneg _) hq 2
  nlinarith [hscaled x hxB, hscaled z hzB,
    sq_nonneg (‖g x‖ - H * a * ‖z - u‖),
    sq_nonneg (‖g x‖ - H * a * ‖x - u‖),
    sq_nonneg (H * a * ‖z - u‖ - H * a * ‖x - u‖)]

lemma epoch_scalar_calibration {a B ell A x M d S : ℝ}
    (ha : 0 ≤ a) (hB : 0 < B) (hell : 2304 ≤ ell) (hA : 0 < A)
    (hS : 0 ≤ S)
    (hx2 : A * x ^ 2 ≤ 8 * B) (hM2 : ell ^ 2 * M ^ 2 ≤ 2304 * A * B)
    (hd2 : 1048576 * d ^ 2 ≤ a ^ 2 * A * B)
    (hvariance : 512 * ell * S ≤ a * A * B) :
    x * M + M ^ 2 / A ≤ 145 * B / ell ∧
      x * d + S / A ≤ a * B / 128 ∧
      2 * (x ^ 2 + M ^ 2 / A ^ 2) * S ≤ 17 * B * S / A := by
  have hell0 : 0 < ell := by linarith
  have hp := mul_le_mul hx2 hM2 (by positivity) (by positivity)
  have hprod : (ell * x * M) ^ 2 ≤ 18432 * B ^ 2 := by
    apply (mul_le_mul_iff_right₀ hA).mp
    nlinarith only [hp]
  have hxm : ell * (x * M) ≤ 144 * B := by
    nlinarith [sq_nonneg (ell * x * M - 144 * B)]
  have hMsmall : ell * M ^ 2 ≤ A * B := by
    have hh := mul_le_mul_of_nonneg_right hell (mul_nonneg hell0.le (sq_nonneg M))
    nlinarith only [hM2, hh]
  have hfirst : x * M + M ^ 2 / A ≤ 145 * B / ell := by
    apply (le_div_iff₀ hell0).mpr
    have hq : ell * (M ^ 2 / A) ≤ B := by
      rw [← mul_div_assoc]
      exact (div_le_iff₀ hA).mpr (by nlinarith only [hMsmall])
    nlinarith only [hxm, hq]
  have hp' := mul_le_mul hx2 hd2 (by positivity) (by positivity)
  have hprod' : 1048576 * (x * d) ^ 2 ≤ 8 * (a * B) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hA).mp
    nlinarith only [hp']
  have hxd : x * d ≤ a * B / 256 := by
    have hn : 0 ≤ a * B := mul_nonneg ha hB.le
    nlinarith [sq_nonneg (256 * x * d - a * B)]
  have hSsmall : S / A ≤ a * B / 256 := by
    apply (div_le_iff₀ hA).mpr
    have hh := mul_le_mul_of_nonneg_right (show 256 ≤ 512 * ell by linarith) hS
    nlinarith only [hvariance, hh]
  refine ⟨hfirst, by linarith, ?_⟩
  have hMsq : 2 * M ^ 2 ≤ A * B := by
    have he : 4608 ≤ ell ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right he (sq_nonneg M)
    nlinarith only [hM2, hh]
  have hcoef : 2 * (x ^ 2 + M ^ 2 / A ^ 2) ≤ 17 * B / A := by
    apply (le_div_iff₀ hA).mpr
    have hh : 2 * (M ^ 2 / A ^ 2) * A ≤ B := by
      have heq : 2 * (M ^ 2 / A ^ 2) * A = 2 * M ^ 2 / A := by field_simp
      rw [heq]
      exact (div_le_iff₀ hA).mpr (by nlinarith only [hMsq])
    nlinarith only [hx2, hh]
  simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right hcoef hS

lemma epoch_increment_mgf [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → E} (hY : Measurable Y) (hYi : Integrable Y P)
    (hY2i : Integrable (fun ω => ‖Y ω‖ ^ 2) P)
    {a B ell A c M d S t : ℝ} (ha : 0 ≤ a) (hB : 0 < B)
    (hell : 2304 ≤ ell) (hA : 0 < A) (hc : 0 ≤ c) (hca : c * a ^ 2 = 1 / A)
    (hS : 0 ≤ S) (ht : 0 ≤ t) (htop : t ≤ ell / (300 * B)) (z : E)
    (hz : A * (a * ‖z‖) ^ 2 ≤ 8 * B)
    (hM : ell ^ 2 * M ^ 2 ≤ 2304 * A * B)
    (hd : 1048576 * d ^ 2 ≤ a ^ 2 * A * B)
    (hvariance : 512 * ell * S ≤ a * A * B)
    (hbound : ∀ ω, ‖Y ω‖ ≤ M) (hmean : ‖∫ ω, Y ω ∂P‖ ≤ d)
    (hsecond : (∫ ω, ‖Y ω‖ ^ 2 ∂P) ≤ S) :
    Integrable (fun ω => Real.exp (t * (-a * ⟪z, Y ω⟫ + c * a ^ 2 * ‖Y ω‖ ^ 2))) P ∧
      (∫ ω, Real.exp (t * (-a * ⟪z, Y ω⟫ + c * a ^ 2 * ‖Y ω‖ ^ 2)) ∂P) ≤
        Real.exp (t * a * B / 128 + t ^ 2 * (17 * B * S / A)) := by
  have hb := epoch_scalar_calibration ha hB hell hA hS hz hM hd hvariance
  have hell0 : 0 < ell := by linarith
  have hsmall : t * (a * M * ‖z‖ + c * a ^ 2 * M ^ 2) ≤ 1 := by
    rw [hca]
    have heq : a * M * ‖z‖ + 1 / A * M ^ 2 = (a * ‖z‖) * M + M ^ 2 / A := by ring
    rw [heq]
    have h1 := mul_le_mul_of_nonneg_left hb.1 ht
    have h2 := mul_le_mul_of_nonneg_right htop (show 0 ≤ 145 * B / ell by positivity)
    have h3 : ell / (300 * B) * (145 * B / ell) = 145 / 300 := by field_simp
    linarith
  have h := OracleTemplate.RobustGradient.energy_increment_mgf hY hYi hY2i
    ha ha le_rfl hc ht z hbound hmean hsecond hsmall
  refine ⟨h.1, h.2.trans (Real.exp_le_exp.mpr ?_)⟩
  have heq : c ^ 2 * a ^ 4 = 1 / A ^ 2 := by
    calc
      _ = (c * a ^ 2) ^ 2 := by ring
      _ = _ := by rw [hca]; ring
  rw [hca, heq]
  have h1 := mul_le_mul_of_nonneg_left hb.2.1 ht
  have h2 := mul_le_mul_of_nonneg_left hb.2.2 (sq_nonneg t)
  simp only [div_eq_mul_inv] at h1 h2 ⊢
  nlinarith only [h1, h2]

lemma geometric_weight_mass {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    a * (∑ i ∈ Finset.range n, (1 - a) ^ i) ≤ 1 ∧
      a * (∑ i ∈ Finset.range n, ((1 - a) ^ i) ^ 2) ≤ 1 := by
  have hρ : 0 ≤ 1 - a := by linarith
  have hid : a * (∑ i ∈ Finset.range n, (1 - a) ^ i) = 1 - (1 - a) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring
  have hfirst : a * (∑ i ∈ Finset.range n, (1 - a) ^ i) ≤ 1 := by
    rw [hid]
    exact sub_le_self _ (pow_nonneg hρ n)
  refine ⟨hfirst, le_trans (mul_le_mul_of_nonneg_left ?_ ha) hfirst⟩
  apply Finset.sum_le_sum
  intro i hi
  have hp := pow_nonneg hρ i
  have hq := pow_le_one₀ hρ (show 1 - a ≤ 1 by linarith) (n := i)
  nlinarith

lemma geometric_epoch_cost {a B ell S A s : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 ≤ B) (hell : 0 < ell)
    (hS : 0 ≤ S) (hA : 0 < A) (hs : 0 ≤ s)
    (hvariance : 512 * ell * S ≤ a * A * B) (n : ℕ) :
    (∑ i ∈ Finset.range n,
      (s * a * B / 128 * (1 - a) ^ i +
        s ^ 2 * (17 * B * S / A) * ((1 - a) ^ i) ^ 2)) ≤
      s * B / 128 + s ^ 2 * B ^ 2 / (16 * ell) := by
  have hw := geometric_weight_mass ha.le ha1 n
  have hlin := mul_le_mul_of_nonneg_left hw.1 (show 0 ≤ s * B / 128 by positivity)
  have hquad := mul_le_mul_of_nonneg_left hw.2
    (show 0 ≤ s ^ 2 * (17 * B * S / A) / a by positivity)
  have hv : s ^ 2 * (17 * B * S / A) / a ≤ s ^ 2 * B ^ 2 / (16 * ell) := by
    apply (div_le_iff₀ ha).mpr
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hA).mpr
    have hh := mul_le_mul_of_nonneg_left hvariance (show 0 ≤ 17 * s ^ 2 * B by positivity)
    have hn : 0 ≤ a * A * s ^ 2 * B ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply (le_div_iff₀ (show 0 < 16 * ell by positivity)).mpr
    nlinarith
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have heq : (s ^ 2 * (17 * B * S / A) / a) *
      (a * ∑ i ∈ Finset.range n, ((1 - a) ^ i) ^ 2) =
        s ^ 2 * (17 * B * S / A) * ∑ i ∈ Finset.range n, ((1 - a) ^ i) ^ 2 := by
    field_simp
  rw [heq] at hquad
  nlinarith

lemma predictable_epoch_tail {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] {pnoise : Measure Z} [IsProbabilityMeasure pnoise]
    {ξ : ℕ → Ω → Z}
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ pnoise P)
    {increment : (n : ℕ) → (Fin n → Z) × Z → ℝ} (cost : ℕ → ℝ)
    {B ell : ℝ} (hB : 0 < B) (hell : 0 < ell)
    (hinc : ∀ n, Measurable (increment n))
    (hei : ∀ n a, Integrable (fun z => Real.exp (ell / (300 * B) * increment n (a, z))) pnoise)
    (heb : ∀ n a, (∫ z, Real.exp (ell / (300 * B) * increment n (a, z)) ∂pnoise) ≤
      Real.exp (cost n)) (n : ℕ)
    (hcost : ∑ i ∈ Finset.range n, cost i ≤
      ell / (300 * B) * B / 128 + (ell / (300 * B)) ^ 2 * B ^ 2 / (16 * ell)) :
    P {ω | B / 128 + B / 8 < ∑ i ∈ Finset.range n,
      increment i ((fun j => ξ j ω), ξ i ω)} ≤ ENNReal.ofReal (Real.exp (-ell / 2500)) := by
  have h := AdaptiveOracleConcentration.iid_predictable_sum_exponential_bound
    hIID.measurable hIID.independent hIID.marginal cost (ell / (300 * B)) hinc hei heb n
  have ht : 0 ≤ ell / (300 * B) := by positivity
  have hb := h.2.trans (Real.exp_le_exp.mpr hcost)
  have htail := OracleTemplate.StochasticGeneralized.exponential_tail ht h.1 hb
    (r := B / 128 + B / 8)
  refine htail.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  have heq : ell / (300 * B) * B / 128 +
      (ell / (300 * B)) ^ 2 * B ^ 2 / (16 * ell) -
      ell / (300 * B) * (B / 128 + B / 8) = -599 * ell / 1440000 := by
    field_simp
    ring
  rw [heq]
  linarith

lemma discounted_recursion_sum {total increment : ℕ → ℝ} {ρ : ℝ}
    (hzero : total 0 = 0) (hstep : ∀ n, total (n + 1) = ρ * total n + increment n)
    (n : ℕ) : total n = ∑ i ∈ Finset.range n, ρ ^ (n - 1 - i) * increment i := by
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      rw [hstep, ih, Finset.mul_sum, Finset.sum_range_succ]
      have heq : ∑ i ∈ Finset.range n, ρ * (ρ ^ (n - 1 - i) * increment i) =
          ∑ i ∈ Finset.range n, ρ ^ (n + 1 - 1 - i) * increment i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have he : n + 1 - 1 - i = (n - 1 - i) + 1 := by omega
        rw [he, pow_succ]
        ring
      rw [heq]
      simp
lemma epoch_length_tuning {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    let N := ⌈4 / a⌉₊
    (1 - a) ^ N ≤ 1 / 16 ∧ (N : ℝ) ≤ 5 / a := by
  intro N
  have hN : 4 / a ≤ (N : ℝ) := Nat.le_ceil _
  have hNa : 4 ≤ a * N := by
    have hh := (div_le_iff₀ ha).mp hN
    nlinarith
  have hh := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - a) (Real.one_sub_le_exp_neg a) N
  rw [← Real.exp_nat_mul] at hh
  have hexp : Real.exp (-(4 : ℝ)) ≤ 1 / 16 := by
    have he := Real.add_one_le_exp (1 : ℝ)
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (show 2 ≤ Real.exp 1 by linarith) 4
    have he4 : Real.exp (4 : ℝ) = Real.exp 1 ^ 4 := by
      simp [← Real.exp_nat_mul]
    rw [Real.exp_neg, he4]
    norm_num at hp
    simpa [one_div, ← Real.exp_nat_mul] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 16) hp
  refine ⟨hh.trans ((Real.exp_le_exp.mpr (by nlinarith : (N : ℝ) * -a ≤ -4)).trans hexp), ?_⟩
  have hu := Nat.ceil_lt_add_one (show 0 ≤ 4 / a by positivity)
  change (N : ℝ) < 4 / a + 1 at hu
  have h1 : 1 ≤ 1 / a := (le_div_iff₀ ha).mpr (by simpa using ha1)
  rw [show 5 / a = 4 / a + 1 / a by ring]
  linarith
lemma epoch_confidence_tuning {k δ : ℝ} (hk : 1 ≤ k) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let ell := 100000 * (1 + Real.log (100000 * k / δ))
    let a := 1 / (k * ell)
    let N := ⌈4 / a⌉₊
    2304 ≤ ell ∧ 0 < a ∧ a ≤ 1 ∧ (N + 1 : ℝ) * Real.exp (-ell / 2500) ≤ δ := by
  intro ell a N
  let b := 100000 * k / δ
  have hk0 : 0 < k := by linarith
  have hb : 100000 ≤ b := by
    dsimp [b]
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hell : 100000 ≤ ell := by
    have hh := Real.log_nonneg hb1
    change 100000 ≤ 100000 * (1 + Real.log b)
    linarith
  have hell0 : 0 < ell := by linarith
  have hke : 1 ≤ k * ell := by nlinarith
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact (div_le_one (mul_pos hk0 hell0)).mpr hke
  have hN := (epoch_length_tuning ha ha1).2
  change (N : ℝ) ≤ 5 / a at hN
  have hN' : (N : ℝ) + 1 ≤ 6 * k * ell := by
    have heq : 5 / a = 5 * k * ell := by dsimp [a]; field_simp
    rw [heq] at hN
    nlinarith
  have hellb : ell ≤ 100000 * b := by
    have hh := Real.log_le_sub_one_of_pos hb0
    change 100000 * (1 + Real.log b) ≤ 100000 * b
    linarith
  have hdb : δ * b = 100000 * k := by dsimp [b]; field_simp
  have hsmall : (N : ℝ) + 1 ≤ δ * b ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hellb (show 0 ≤ 6 * k by positivity)
    have hb6 : 6 ≤ b := by linarith
    calc
      _ ≤ 6 * k * ell := hN'
      _ ≤ 600000 * k * b := by nlinarith only [hmul]
      _ = 6 * δ * b ^ 2 := by nlinarith only [congrArg (fun x => 6 * b * x) hdb]
      _ ≤ δ * b ^ 3 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hb6) (show 0 ≤ δ * b ^ 2 by positivity)]
  have hexp : b ^ (3 : ℕ) ≤ Real.exp (ell / 2500) := by
    have hlog := Real.log_nonneg hb1
    have he : 3 * Real.log b ≤ ell / 2500 := by
      change 3 * Real.log b ≤ (100000 * (1 + Real.log b)) / 2500
      linarith
    have hh := Real.exp_le_exp.mpr he
    rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hb0] at hh
    exact hh
  have ht : (N : ℝ) + 1 ≤ δ * Real.exp (ell / 2500) :=
    hsmall.trans (mul_le_mul_of_nonneg_left hexp hδ.le)
  refine ⟨by linarith, ha, ha1, ?_⟩
  rw [show -ell / 2500 = -(ell / 2500) by ring, Real.exp_neg]
  exact (mul_inv_le_iff₀ (Real.exp_pos _)).mpr ht

lemma stopped_weighted_tail {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] {pnoise : Measure Z} [IsProbabilityMeasure pnoise]
    {ξ : ℕ → Ω → Z}
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ pnoise P)
    {increment : (j : ℕ) → (Fin j → Z) × Z → ℝ}
    {good : (j : ℕ) → (Fin j → Z) → Prop} [∀ j, DecidablePred (good j)]
    (hgood : ∀ j, MeasurableSet {v | good j v})
    (hinc : ∀ j, Measurable (increment j))
    {a B ell S A : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 < B)
    (hell : 0 < ell) (hS : 0 ≤ S) (hA : 0 < A)
    (hvariance : 512 * ell * S ≤ a * A * B)
    (hmgf : ∀ j v, good j v → ∀ t : ℝ, 0 ≤ t → t ≤ ell / (300 * B) →
      Integrable (fun z => Real.exp (t * increment j (v, z))) pnoise ∧
      (∫ z, Real.exp (t * increment j (v, z)) ∂pnoise) ≤
        Real.exp (t * a * B / 128 + t ^ 2 * (17 * B * S / A))) (n : ℕ) :
    P {ω | B / 128 + B / 8 < ∑ j ∈ Finset.range n,
      (1 - a) ^ (n - 1 - j) *
        (if good j (fun i => ξ i ω) then increment j ((fun i => ξ i ω), ξ j ω) else 0)} ≤
      ENNReal.ofReal (Real.exp (-ell / 2500)) := by
  classical
  let s := ell / (300 * B)
  let w := fun j => (1 - a) ^ (n - 1 - j)
  let cost := fun j => s * a * B / 128 * w j + s ^ 2 * (17 * B * S / A) * (w j) ^ 2
  let stopped := fun j (v : (Fin j → Z) × Z) =>
    w j * (if good j v.1 then increment j v else 0)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hw0 (j : ℕ) : 0 ≤ w j := pow_nonneg (by linarith) _
  have hw1 (j : ℕ) : w j ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hc0 (j : ℕ) : 0 ≤ cost j := by dsimp [cost]; positivity
  have hsm (j : ℕ) : Measurable (stopped j) := by
    apply Measurable.const_mul
    exact Measurable.ite ((hgood j).preimage measurable_fst) (hinc j) measurable_const
  have hm (j : ℕ) (v : Fin j → Z) :
      Integrable (fun z => Real.exp (s * stopped j (v, z))) pnoise ∧
      (∫ z, Real.exp (s * stopped j (v, z)) ∂pnoise) ≤ Real.exp (cost j) := by
    by_cases hv : good j v
    · have ht := hmgf j v hv (s * w j) (mul_nonneg hs (hw0 j))
        (by change s * w j ≤ s; nlinarith [hw1 j])
      have heq : ∀ z, s * stopped j (v, z) = (s * w j) * increment j (v, z) := by
        intro z
        dsimp [stopped]
        rw [ite_eq_left hv]
        ring
      simp_rw [heq]
      refine ⟨ht.1, ht.2.trans_eq ?_⟩
      congr 1
      dsimp [cost]
      ring
    · have heq : ∀ z, Real.exp (s * stopped j (v, z)) = 1 := by
        intro z
        simp [stopped, hv]
      simp_rw [heq]
      exact ⟨integrable_const 1, by simpa using (Real.one_le_exp_iff.mpr (hc0 j))⟩
  have hcost : ∑ j ∈ Finset.range n, cost j ≤ s * B / 128 + s ^ 2 * B ^ 2 / (16 * ell) := by
    have heq : ∑ j ∈ Finset.range n, cost j = ∑ j ∈ Finset.range n,
        (s * a * B / 128 * (1 - a) ^ j + s ^ 2 * (17 * B * S / A) * ((1 - a) ^ j) ^ 2) := by
      exact Finset.sum_range_reflect
        (fun j => s * a * B / 128 * (1 - a) ^ j +
          s ^ 2 * (17 * B * S / A) * ((1 - a) ^ j) ^ 2) n
    rw [heq]
    exact geometric_epoch_cost ha ha1 hB.le hell hS hA hs hvariance n
  exact predictable_epoch_tail hIID cost hB hell hsm (fun j v => (hm j v).1)
    (fun j v => (hm j v).2) n hcost

lemma killed_energy_epoch {energy total increment : ℕ → ℝ} {B ρ : ℝ} {N : ℕ}
    (hB : 0 < B) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hstart : energy 0 ≤ B)
    (hzero : total 0 = 0)
    (hstep : ∀ n < N, energy (n + 1) ≤ ρ * energy n + increment n)
    (htotal : ∀ n < N, total (n + 1) = ρ * total n +
      if ∀ j ≤ n, energy j ≤ 4 * B then increment n else 0)
    (hnoise : ∀ n ≤ N, total n ≤ B / 128 + B / 8)
    (hdecay : ρ ^ N ≤ 1 / 16) :
    (∀ n ≤ N, energy n ≤ 4 * B) ∧ energy N ≤ 25 * B / 128 := by
  classical
  have hc : ∀ n, n ≤ N → energy n ≤ ρ ^ n * B + total n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      cases n with
      | zero => simpa [hzero] using hstart
      | succ k =>
        have hg : ∀ j ≤ k, energy j ≤ 4 * B := by
          intro j hj
          have hjN : j ≤ N := by omega
          have hp := ih j (by omega) hjN
          have hw := hnoise j hjN
          have hpow := mul_le_mul_of_nonneg_right (pow_le_one₀ hρ hρ1 (n := j)) hB.le
          nlinarith
        have hw := htotal k (by omega)
        rw [ite_eq_left hg] at hw
        have hp := hstep k (by omega)
        have hi := mul_le_mul_of_nonneg_left (ih k (by omega) (by omega)) hρ
        rw [pow_succ]
        nlinarith
  refine ⟨?_, ?_⟩
  · intro n hn
    have hp := hc n hn
    have hw := hnoise n hn
    have hpow := mul_le_mul_of_nonneg_right (pow_le_one₀ hρ hρ1 (n := n)) hB.le
    nlinarith
  · have hp := hc N le_rfl
    have hw := hnoise N le_rfl
    have hd := mul_le_mul_of_nonneg_right hdecay hB.le
    linarith

lemma killed_energy_epoch_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {energy total increment : Ω → ℕ → ℝ} {B ρ : ℝ} {N : ℕ}
    {q : ENNReal} (hB : 0 < B) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hstart : ∀ ω, energy ω 0 ≤ B) (hzero : ∀ ω, total ω 0 = 0)
    (hstep : ∀ ω n, n < N → energy ω (n + 1) ≤ ρ * energy ω n + increment ω n)
    (htotal : ∀ ω n, n < N → total ω (n + 1) = ρ * total ω n +
      if ∀ j ≤ n, energy ω j ≤ 4 * B then increment ω n else 0)
    (htail : ∀ n ≤ N, P {ω | B / 128 + B / 8 < total ω n} ≤ q)
    (hdecay : ρ ^ N ≤ 1 / 16) :
    P {ω | (∃ n ≤ N, 4 * B < energy ω n) ∨ 25 * B / 128 < energy ω N} ≤
      (N + 1 : ℕ) * q := by
  have hsub : {ω | (∃ n ≤ N, 4 * B < energy ω n) ∨ 25 * B / 128 < energy ω N} ⊆
      ⋃ n : Fin (N + 1), {ω | B / 128 + B / 8 < total ω n} := by
    intro ω hω
    by_contra hn
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hn
    have hnoise : ∀ n ≤ N, total ω n ≤ B / 128 + B / 8 := by
      intro n hnN
      exact hn ⟨n, by omega⟩
    have he := killed_energy_epoch hB hρ hρ1 (hstart ω) (hzero ω)
      (hstep ω) (htotal ω) hnoise hdecay
    rcases hω with ⟨n, hnN, hbad⟩ | hbad
    · exact (not_lt_of_ge (he.1 n hnN)) hbad
    · exact (not_lt_of_ge he.2) hbad
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  calc
    _ ≤ ∑ _ : Fin (N + 1), q := Finset.sum_le_sum (fun n _ => htail n (by omega))
    _ = _ := by simp

lemma accelerated_query_radius {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a R : ℝ} (ha : 0 ≤ a) (x z u : E)
    (hx : ‖x - u‖ ≤ R) (hz : ‖z - u‖ ≤ R) :
    ‖acceleratedQuery a (x, z) - u‖ ≤ R := by
  have hden : 0 < 1 + a := by linarith
  have heq : acceleratedQuery a (x, z) - u =
      (1 / (1 + a)) • ((x - u) + a • (z - u)) := by
    dsimp [acceleratedQuery]
    match_scalars
    all_goals (field_simp <;> ring)
  rw [heq, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (1 + a))]
  have hn : ‖(x - u) + a • (z - u)‖ ≤ (1 + a) * R := by
    have hh := norm_add_le (x - u) (a • (z - u))
    rw [norm_smul, Real.norm_of_nonneg ha] at hh
    nlinarith [mul_le_mul_of_nonneg_left hz ha]
  calc
    _ ≤ (1 / (1 + a)) * ((1 + a) * R) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = R := by field_simp

lemma frozen_reference_query_bound {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] {a m B gap : ℝ} (ha : 0 ≤ a) (hm : 0 < m) (hB : 0 < B)
    (x z u : E) (r : X) (U : E → X)
    (hU : ∀ v w, ‖U v - U w‖ ≤ ‖v - w‖)
    (hgap : 0 ≤ gap) (henergy : gap + m / 2 * ‖z - u‖ ^ 2 ≤ 4 * B)
    (hxdist : m * ‖x - u‖ ^ 2 ≤ 2 * gap)
    (href : m * ‖r - U u‖ ^ 2 ≤ B) :
    m * ‖r - U (acceleratedQuery a (x, z))‖ ^ 2 ≤ 16 * B := by
  let R := Real.sqrt (B / m)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = B / m := Real.sq_sqrt (div_pos hB hm).le
  have hx : m * ‖x - u‖ ^ 2 ≤ 8 * B := by nlinarith [sq_nonneg ‖z - u‖]
  have hz : m * ‖z - u‖ ^ 2 ≤ 8 * B := by linarith
  have hdist (v : E) (hv : m * ‖v - u‖ ^ 2 ≤ 8 * B) : ‖v - u‖ ≤ 3 * R := by
    have hh : ‖v - u‖ ^ 2 ≤ 8 * R ^ 2 := by
      calc
        _ ≤ 8 * B / m := (le_div_iff₀ hm).mpr (by nlinarith only [hv])
        _ = _ := by rw [hR2]; ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3 * R)).mp (by nlinarith [sq_nonneg R])
  have hr : ‖r - U u‖ ≤ R := by
    apply (sq_le_sq₀ (norm_nonneg _) hR).mp
    rw [hR2]
    exact (le_div_iff₀ hm).mpr (by nlinarith only [href])
  have hq := accelerated_query_radius ha x z u (hdist x hx) (hdist z hz)
  have hru : ‖r - U (acceleratedQuery a (x, z))‖ ≤ 4 * R := by
    have hh := norm_sub_le_norm_sub_add_norm_sub r (U u) (U (acceleratedQuery a (x, z)))
    have hl := hU (acceleratedQuery a (x, z)) u
    rw [norm_sub_rev (U (acceleratedQuery a (x, z))) (U u)] at hl
    linarith
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hru 2) hm.le
  have hmR : m * R ^ 2 = B := by rw [hR2]; field_simp
  nlinarith only [hh, hmR]

lemma kernel_epoch_calibration {m H B ell : ℝ} (hm : 0 < m) (hmH : m ≤ H)
    (hB : 0 < B) (hell : 2304 ≤ ell) :
    let a := Real.sqrt m / (Real.sqrt H * ell)
    let A := H * ell ^ 2
    let M := 48 * Real.sqrt (H * B)
    let d := Real.sqrt (m * B) / 1024
    let S := Real.sqrt (m * B) * Real.sqrt (H * B) / 512
    0 < a ∧ a ≤ 1 ∧ 0 < A ∧ a ^ 2 * A = m ∧
      ell ^ 2 * M ^ 2 ≤ 2304 * A * B ∧
      1048576 * d ^ 2 ≤ a ^ 2 * A * B ∧
      512 * ell * S ≤ a * A * B := by
  intro a A M d S
  have hH : 0 < H := lt_of_lt_of_le hm hmH
  have he : 0 < ell := by linarith
  have hsH : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hsH2 := Real.sq_sqrt hH.le
  have hsm2 := Real.sq_sqrt hm.le
  have hb2 := Real.sq_sqrt hB.le
  have hmB2 := Real.sq_sqrt (mul_pos hm hB).le
  have hHB2 := Real.sq_sqrt (mul_pos hH hB).le
  have ha : 0 < a := div_pos hsm (mul_pos hsH he)
  have hA : 0 < A := mul_pos hH (sq_pos_of_pos he)
  have haA : a ^ 2 * A = m := by
    dsimp [a, A]
    rw [div_pow, mul_pow, hsH2, hsm2]
    field_simp
  refine ⟨ha, ?_, hA, haA, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ (mul_pos hsH he)).mpr
    have hh := Real.sqrt_le_sqrt hmH
    nlinarith
  · dsimp [M, A]
    rw [mul_pow, hHB2]
    ring_nf
    exact le_rfl
  · rw [haA]
    dsimp [d]
    rw [div_pow, hmB2]
    ring_nf
    exact le_rfl
  · have heq : Real.sqrt (m * B) * Real.sqrt (H * B) = Real.sqrt m * Real.sqrt H * B := by
      rw [Real.sqrt_mul hm.le, Real.sqrt_mul hH.le]
      calc
        _ = Real.sqrt m * Real.sqrt H * (Real.sqrt B) ^ 2 := by ring
        _ = _ := by rw [hb2]
    dsimp [S, a, A]
    rw [heq]
    apply le_of_eq
    field_simp
    nlinarith only [hsH2]
lemma calibrated_kernel_increment_mgf {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → E} (hY : Measurable Y) (hYi : Integrable Y P)
    (hY2i : Integrable (fun ω => ‖Y ω‖ ^ 2) P)
    {m H B ell t : ℝ} (hm : 0 < m) (hmH : m ≤ H) (hB : 0 < B) (hell : 2304 ≤ ell)
    (ht : 0 ≤ t) (htop : t ≤ ell / (300 * B)) (z : E)
    (hz : m * ‖z‖ ^ 2 ≤ 8 * B)
    (hbound : ∀ ω, ‖Y ω‖ ≤ 48 * Real.sqrt (H * B))
    (hmean : ‖∫ ω, Y ω ∂P‖ ≤ Real.sqrt (m * B) / 1024)
    (hsecond : (∫ ω, ‖Y ω‖ ^ 2 ∂P) ≤ Real.sqrt (m * B) * Real.sqrt (H * B) / 512) :
    let a := Real.sqrt m / (Real.sqrt H * ell)
    let S := Real.sqrt (m * B) * Real.sqrt (H * B) / 512
    let A := H * ell ^ 2
    Integrable (fun ω => Real.exp (t * (-a * ⟪z, Y ω⟫ + a ^ 2 / m * ‖Y ω‖ ^ 2))) P ∧
      (∫ ω, Real.exp (t * (-a * ⟪z, Y ω⟫ + a ^ 2 / m * ‖Y ω‖ ^ 2)) ∂P) ≤
        Real.exp (t * a * B / 128 + t ^ 2 * (17 * B * S / A)) := by
  intro a S A
  have hc := kernel_epoch_calibration hm hmH hB hell
  change 0 < a ∧ a ≤ 1 ∧ 0 < A ∧ a ^ 2 * A = m ∧ _ at hc
  have hca : (1 / m) * a ^ 2 = 1 / A := by
    apply (mul_right_cancel₀ (ne_of_gt hc.2.2.1))
    rw [one_div_mul_cancel (ne_of_gt hc.2.2.1)]
    calc
      _ = (a ^ 2 * A) / m := by ring
      _ = 1 := by rw [hc.2.2.2.1]; exact div_self hm.ne'
  have hz' : A * (a * ‖z‖) ^ 2 ≤ 8 * B := by
    calc
      _ = (a ^ 2 * A) * ‖z‖ ^ 2 := by ring
      _ = m * ‖z‖ ^ 2 := by rw [hc.2.2.2.1]
      _ ≤ _ := hz
  have hh := epoch_increment_mgf hY hYi hY2i hc.1.le hB hell hc.2.2.1
    (show 0 ≤ 1 / m by positivity) hca (show 0 ≤ S by dsimp [S]; positivity)
    ht htop z hz' hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2 hbound hmean hsecond
  simpa only [one_div_mul_eq_div] using hh

open LongTails.Algorithms.HeavyTailSaddleEstimator

lemma epoch_explicit_tuning {m H δ : ℝ} (hm : 0 < m) (hmH : m ≤ H)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2304 ≤ epochLog m H δ ∧ 0 < epochMomentum m H δ ∧ epochMomentum m H δ ≤ 1 ∧
      (1 - epochMomentum m H δ) ^ epochSteps m H δ ≤ 1 / 16 ∧
      (epochSteps m H δ + 1 : ℝ) * Real.exp (-epochLog m H δ / 2500) ≤ δ ∧
      (epochSteps m H δ : ℝ) ≤ 5 * Real.sqrt H * epochLog m H δ / Real.sqrt m := by
  have hH : 0 < H := lt_of_lt_of_le hm hmH
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hsH : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
  let k := Real.sqrt H / Real.sqrt m
  have hk : 1 ≤ k := (le_div_iff₀ hsm).mpr (by simpa using Real.sqrt_le_sqrt hmH)
  have hell : 100000 * (1 + Real.log (100000 * k / δ)) = epochLog m H δ := by
    unfold epochLog k
    congr 2
    field_simp
  have ha : 1 / (k * epochLog m H δ) = epochMomentum m H δ := by
    unfold epochMomentum k
    field_simp
  have hN : ⌈4 / epochMomentum m H δ⌉₊ = epochSteps m H δ := by
    unfold epochMomentum epochSteps
    congr 1
    field_simp
  have ht := epoch_confidence_tuning hk hδ hδ1
  dsimp only at ht
  rw [hell, ha, hN] at ht
  have hl := epoch_length_tuning ht.2.1 ht.2.2.1
  dsimp only at hl
  rw [hN] at hl
  refine ⟨ht.1, ht.2.1, ht.2.2.1, hl.1, ht.2.2.2, ?_⟩
  convert hl.2 using 1
  unfold epochMomentum
  field_simp

end LongTails.Proofs.HeavyTailSaddleEnergy
