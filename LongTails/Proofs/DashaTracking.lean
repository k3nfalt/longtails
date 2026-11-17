import LongTails.Proofs.AdaptiveReplicaMoments
import LongTails.Proofs.GdConvex

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.DashaTracking

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P]

lemma inexact_descent {f : E → ℝ} {grad : E → E} {L : ℝ}
    (hg : ∀ x, HasGradientAt f (grad x) x)
    (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (x g : E) (γ : ℝ) :
    f (x - γ • g) ≤ f x - γ / 2 * ‖grad x‖ ^ 2 -
      (γ / 2 - L * γ ^ 2 / 2) * ‖g‖ ^ 2 + γ / 2 * ‖g - grad x‖ ^ 2 := by
  have hd := OracleTemplate.Gradient.smooth_upper_bound hg hlip x (x - γ • g)
  have he : x - γ • g - x = -γ • g := by module
  rw [he] at hd
  simp only [inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    neg_sq] at hd
  convert hd using 1
  rw [norm_sub_sq_real, real_inner_comm g (grad x)]
  ring

omit [CompleteSpace E] in
lemma tracking_identity (g h hnext compressed : E) (a : ℝ) :
    g + compressed - hnext =
      (1 - a) • (g - h) + (compressed - (hnext - h - a • (g - h))) := by
  module

lemma tracking_second_moment (g h hnext : E) (a : ℝ) (compressed : Ω → E)
    (hi : Integrable (fun ω => compressed ω - (hnext - h - a • (g - h))) P)
    (hi2 : Integrable (fun ω => ‖compressed ω - (hnext - h - a • (g - h))‖ ^ 2) P)
    (hz : ∫ ω, compressed ω - (hnext - h - a • (g - h)) ∂P = 0) :
    (∫ ω, ‖g + compressed ω - hnext‖ ^ 2 ∂P) =
      (1 - a) ^ 2 * ‖g - h‖ ^ 2 +
        ∫ ω, ‖compressed ω - (hnext - h - a • (g - h))‖ ^ 2 ∂P := by
  simp_rw [tracking_identity g h hnext (a := a)]
  rw [LongTails.Proofs.AdaptiveReplicaMoments.shifted_second_moment _ hi hi2 hz]
  simp [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

lemma tracking_second_moment_le (g h hnext : E) (a ω δ : ℝ)
    (hω : 0 ≤ ω) (compressed : Ω → E)
    (hi : Integrable (fun ξ => compressed ξ - (hnext - h - a • (g - h))) P)
    (hi2 : Integrable (fun ξ => ‖compressed ξ - (hnext - h - a • (g - h))‖ ^ 2) P)
    (hz : ∫ ξ, compressed ξ - (hnext - h - a • (g - h)) ∂P = 0)
    (hv : (∫ ξ, ‖compressed ξ - (hnext - h - a • (g - h))‖ ^ 2 ∂P) ≤
      ω * ‖hnext - h - a • (g - h)‖ ^ 2 + δ) :
    (∫ ξ, ‖g + compressed ξ - hnext‖ ^ 2 ∂P) ≤
      2 * ω * ‖hnext - h‖ ^ 2 +
        (2 * a ^ 2 * ω + (1 - a) ^ 2) * ‖g - h‖ ^ 2 + δ := by
  rw [tracking_second_moment g h hnext a compressed hi hi2 hz]
  have hn := norm_sub_le (hnext - h) (a • (g - h))
  have hs : ‖hnext - h - a • (g - h)‖ ^ 2 ≤
      2 * ‖hnext - h‖ ^ 2 + 2 * a ^ 2 * ‖g - h‖ ^ 2 := by
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    have hab := sq_nonneg (‖hnext - h‖ - ‖a • (g - h)‖)
    have he : ‖a • (g - h)‖ ^ 2 = a ^ 2 * ‖g - h‖ ^ 2 := by
      simp [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hs hω
  nlinarith

lemma momentum_contraction (ω : ℝ) (hω : 0 ≤ ω) :
    2 * (1 / (2 * ω + 1)) ^ 2 * ω + (1 - 1 / (2 * ω + 1)) ^ 2 =
      1 - 1 / (2 * ω + 1) := by
  have hd : 2 * ω + 1 ≠ 0 := by positivity
  field_simp [hd]
  ring

lemma aggregate_second_moment {ι : Type*} [Fintype ι]
    [MeasurableSpace E] [BorelSpace E] (w : E) (c : ℝ) (z : ι → Ω → E)
    (hind : ProbabilityTheory.iIndepFun z P)
    (hi : ∀ i, Integrable (z i) P)
    (hi2 : ∀ i, Integrable (fun ξ => ‖z i ξ‖ ^ 2) P)
    (hz : ∀ i, ∫ ξ, z i ξ ∂P = 0) :
    (∫ ξ, ‖w + c • ∑ i, z i ξ‖ ^ 2 ∂P) =
      ‖w‖ ^ 2 + c ^ 2 * ∑ i, ∫ ξ, ‖z i ξ‖ ^ 2 ∂P := by
  have hsum := OracleTemplate.RobustGradient.independent_sum_second_moment z hind hi hi2 hz
  have hsi : Integrable (fun ξ => ∑ i, z i ξ) P :=
    integrable_finsetSum _ (fun i _ => hi i)
  have hci : Integrable (fun ξ => c • ∑ i, z i ξ) P := hsi.smul c
  have hc2 : Integrable (fun ξ => ‖c • ∑ i, z i ξ‖ ^ 2) P := by
    simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using hsum.1.const_mul (c ^ 2)
  have hcz : (∫ ξ, c • ∑ i, z i ξ ∂P) = 0 := by
    rw [integral_smul, integral_finsetSum _ (fun i _ => hi i)]
    simp [hz]
  rw [LongTails.Proofs.AdaptiveReplicaMoments.shifted_second_moment w hci hc2 hcz]
  simp_rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, hsum.2]

lemma aggregate_tracking_bound {n : ℕ} [MeasurableSpace E] [BorelSpace E]
    (g h hnext : Fin n → E) (a ω δ : ℝ) (hω : 0 ≤ ω)
    (compressed : Fin n → Ω → E)
    (hind : ProbabilityTheory.iIndepFun
      (fun i ξ => compressed i ξ - (hnext i - h i - a • (g i - h i))) P)
    (hi : ∀ i, Integrable
      (fun ξ => compressed i ξ - (hnext i - h i - a • (g i - h i))) P)
    (hi2 : ∀ i, Integrable
      (fun ξ => ‖compressed i ξ - (hnext i - h i - a • (g i - h i))‖ ^ 2) P)
    (hz : ∀ i, ∫ ξ, compressed i ξ - (hnext i - h i - a • (g i - h i)) ∂P = 0)
    (hv : ∀ i, (∫ ξ, ‖compressed i ξ - (hnext i - h i - a • (g i - h i))‖ ^ 2 ∂P) ≤
      ω * ‖hnext i - h i - a • (g i - h i)‖ ^ 2 + δ) :
    (∫ ξ, ‖(1 / (n : ℝ)) • ∑ i, (g i + compressed i ξ - hnext i)‖ ^ 2 ∂P) ≤
      (1 - a) ^ 2 * ‖(1 / (n : ℝ)) • ∑ i, (g i - h i)‖ ^ 2 +
        (1 / (n : ℝ)) ^ 2 * ∑ i,
          (2 * ω * ‖hnext i - h i‖ ^ 2 + 2 * a ^ 2 * ω * ‖g i - h i‖ ^ 2 + δ) := by
  classical
  let z : Fin n → Ω → E := fun i ξ =>
    compressed i ξ - (hnext i - h i - a • (g i - h i))
  have heq (ξ : Ω) : (1 / (n : ℝ)) • ∑ i, (g i + compressed i ξ - hnext i) =
      (1 - a) • ((1 / (n : ℝ)) • ∑ i, (g i - h i)) +
        (1 / (n : ℝ)) • ∑ i, z i ξ := by
    have hs : (∑ i, (g i + compressed i ξ - hnext i)) =
        ∑ i, ((1 - a) • (g i - h i) + z i ξ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact tracking_identity (g i) (h i) (hnext i) (compressed i ξ) a
    rw [hs, Finset.sum_add_distrib, ← Finset.smul_sum, smul_add, smul_smul, smul_smul]
    rw [mul_comm (1 / (n : ℝ)) (1 - a)]
  simp_rw [heq]
  rw [aggregate_second_moment _ _ z hind hi hi2 hz]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  have hb := tracking_second_moment_le (g i) (h i) (hnext i) a ω δ hω
    (compressed i) (hi i) (hi2 i) (hz i) (hv i)
  rw [tracking_second_moment (g i) (h i) (hnext i) a (compressed i)
    (hi i) (hi2 i) (hz i)] at hb
  dsimp only [z]
  linarith

lemma potential_step {a γ ω n f fnext e enext v vnext r s q H D : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hγ : 0 ≤ γ) (hω : 0 ≤ ω) (hn : 0 < n)
    (he : 0 ≤ e) (hs : 0 ≤ s)
    (hf : fnext ≤ f - γ / 2 * r - D * s + γ / 2 * e)
    (hec : enext ≤ (1 - a) ^ 2 * e + 2 * ω / n * H * s +
      2 * a ^ 2 * ω / n * v + q / n)
    (hvc : vnext ≤ (1 - a) * v + 2 * ω * H * s + q)
    (hD : (γ / a * (2 * ω / n) + 2 * γ * ω / n * (2 * ω)) * H ≤ D) :
    fnext + γ / a * enext + 2 * γ * ω / n * vnext ≤
      f + γ / a * e + 2 * γ * ω / n * v - γ / 2 * r +
        (γ / a + 2 * γ * ω) * q / n := by
  have hE := mul_le_mul_of_nonneg_left hec (show 0 ≤ γ / a by positivity)
  have hV := mul_le_mul_of_nonneg_left hvc (show 0 ≤ 2 * γ * ω / n by positivity)
  have hS := mul_le_mul_of_nonneg_right hD hs
  have hneg : γ * (a - 3 / 2) * e ≤ 0 := by
    have : a - 3 / 2 ≤ 0 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hγ this) he
  have hcancel :
      γ / 2 * e + γ / a * ((1 - a) ^ 2 * e + 2 * ω / n * H * s +
        2 * a ^ 2 * ω / n * v + q / n) +
        2 * γ * ω / n * ((1 - a) * v + 2 * ω * H * s + q) =
      γ / a * e + 2 * γ * ω / n * v + γ * (a - 3 / 2) * e +
        (γ / a * (2 * ω / n) + 2 * γ * ω / n * (2 * ω)) * H * s +
        (γ / a + 2 * γ * ω) * q / n := by
    field_simp [ne_of_gt ha, ne_of_gt hn]
    ring
  linarith

lemma summed_accuracy (energy residual : ℕ → ℝ) (γ noise lower : ℝ)
    (hstep : ∀ k, energy (k + 1) ≤ energy k - γ / 2 * residual k + noise)
    (hlower : ∀ k, lower ≤ energy k) (K : ℕ) :
    γ / 2 * (∑ k ∈ Finset.range K, residual k) ≤
      energy 0 - lower + K * noise := by
  have ht : ∀ k, energy k + γ / 2 * (∑ j ∈ Finset.range k, residual j) ≤
      energy 0 + k * noise := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      linarith [hstep k]
  linarith [ht K, hlower K]

omit [CompleteSpace E] in
lemma pathwise_tracking (g h hnext compressed : E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hc : ‖compressed - (hnext - h - (4 / 5 : ℝ) • (g - h))‖ ≤
      ‖hnext - h - (4 / 5 : ℝ) • (g - h)‖ / 4 + δ) :
    ‖g + compressed - hnext‖ ^ 2 ≤
      ‖g - h‖ ^ 2 / 2 + ‖hnext - h‖ ^ 2 / 4 + 3 * δ ^ 2 := by
  have ht := norm_add_le ((1 - (4 / 5 : ℝ)) • (g - h))
    (compressed - (hnext - h - (4 / 5 : ℝ) • (g - h)))
  rw [← tracking_identity g h hnext compressed (4 / 5)] at ht
  have hu := norm_sub_le (hnext - h) ((4 / 5 : ℝ) • (g - h))
  norm_num [norm_smul] at ht hu
  have hb : ‖g + compressed - hnext‖ ≤
      (2 / 5 : ℝ) * ‖g - h‖ + ‖hnext - h‖ / 4 + δ := by linarith
  have hb0 : 0 ≤ (2 / 5 : ℝ) * ‖g - h‖ + ‖hnext - h‖ / 4 + δ := by positivity
  have hs := (sq_le_sq₀ (norm_nonneg _) hb0).mpr hb
  nlinarith [sq_nonneg ((2 / 5 : ℝ) * ‖g - h‖ - ‖hnext - h‖ / 4),
    sq_nonneg ((2 / 5 : ℝ) * ‖g - h‖ - δ),
    sq_nonneg (‖hnext - h‖ / 4 - δ), sq_nonneg ‖g - h‖,
    sq_nonneg ‖hnext - h‖]

lemma pathwise_potential {F Fnext v vnext r s η L δ : ℝ}
    (hη : 0 ≤ η) (hηL : η * L ≤ 1 / 4) (hL : 0 ≤ L) (hs : 0 ≤ s)
    (hf : Fnext ≤ F - η / 2 * r - (η / 2 - L * η ^ 2 / 2) * s + η / 2 * v)
    (hv : vnext ≤ v / 2 + L ^ 2 * η ^ 2 / 4 * s + 3 * δ ^ 2) :
    Fnext + η * vnext ≤ F + η * v - η / 2 * r - η / 4 * s + 3 * η * δ ^ 2 := by
  have hm := mul_le_mul_of_nonneg_left hv hη
  have hc : η * L / 2 + (η * L) ^ 2 / 4 ≤ 1 / 4 := by
    have hz : 0 ≤ η * L := mul_nonneg hη hL
    have hsq := mul_self_le_mul_self hz hηL
    nlinarith
  have hprod := mul_nonneg (mul_nonneg hη hs) (sub_nonneg.mpr hc)
  nlinarith

end LongTails.Proofs.DashaTracking
