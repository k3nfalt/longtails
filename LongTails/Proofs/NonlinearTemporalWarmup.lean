import LongTails.Proofs.QuasarInexact
import LongTails.Proofs.HessianLipschitzModel
import LongTails.Proofs.QuadraticTemporalEnergy

open scoped RealInnerProductSpace

namespace OracleTemplate.NonlinearTemporalDiscrepancy

open LongTails.Setups.HessianLipschitzTemporalDiscrepancy

open TemporalDiscrepancy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma nonlinear_energy_step {f : E → ℝ} {G : E → E} {L μ θ : ℝ}
    (hμ : 0 < μ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hstep : θ ^ 2 * L ≤ μ)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hs : ∀ x y, f x + ⟪G x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (s : E × E) (u e : E) (hmin : ∀ x, f u ≤ f x) :
    SimilarQuasar.energy f μ u
        (acceleratedUpdate θ μ s (G (acceleratedQuery θ s) + e)) ≤
      (1 - 3 * θ / 4) * SimilarQuasar.energy f μ u s + 3 * θ / μ * ‖e‖ ^ 2 := by
  have hx : f (SimilarQuasar.query θ s) +
      ⟪G (SimilarQuasar.query θ s), s.1 - SimilarQuasar.query θ s⟫ -
        1 * μ / (2 * θ) * ‖s.1 - SimilarQuasar.query θ s‖ ^ 2 ≤ f s.1 := by
    have hh := hs (SimilarQuasar.query θ s) s.1
    have hp : 0 ≤ μ / (2 * θ) * ‖s.1 - SimilarQuasar.query θ s‖ ^ 2 := by positivity
    have hp' : 0 ≤ μ / 2 * ‖s.1 - SimilarQuasar.query θ s‖ ^ 2 := by positivity
    simp only [one_mul]
    linarith
  have hu : 1 * f (SimilarQuasar.query θ s) +
      ⟪G (SimilarQuasar.query θ s), u - SimilarQuasar.query θ s⟫ +
        1 * μ / 2 * ‖u - SimilarQuasar.query θ s‖ ^ 2 ≤ 1 * f u := by
    simpa only [one_mul] using hs (SimilarQuasar.query θ s) u
  have hh := SimilarQuasar.robust_energy_step hμ (by norm_num : (0 : ℝ) < 1) hθ
    (by simpa using hθ1) hstep hg hlip s.1 s.2 u e hmin hx hu
  simpa only [one_mul, mul_one, SimilarQuasar.update, SimilarQuasar.query,
    acceleratedUpdate, acceleratedQuery] using hh

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma shifted_prefix_bound (e : ℕ → E) {D : ℝ}
    (he : ∀ n, ‖∑ i ∈ Finset.range n, e i‖ ≤ D) (start n : ℕ) :
    ‖∑ i ∈ Finset.range n, e (start + i)‖ ≤ 2 * D := by
  have hid : (∑ i ∈ Finset.range n, e (start + i)) =
      (∑ i ∈ Finset.range (start + n), e i) - ∑ i ∈ Finset.range start, e i := by
    rw [Finset.sum_range_add]
    abel
  rw [hid]
  calc
    _ ≤ ‖∑ i ∈ Finset.range (start + n), e i‖ + ‖∑ i ∈ Finset.range start, e i‖ :=
      norm_sub_le _ _
    _ ≤ D + D := add_le_add (he _) (he _)
    _ = _ := by ring

omit [CompleteSpace E] in
lemma frozen_error_bound (e : ℕ → E) {D : ℝ}
    (he : ∀ n, ‖∑ i ∈ Finset.range n, e i‖ ≤ D) {b : ℕ} (hb : 0 < b) (start : ℕ) :
    ‖(b : ℝ)⁻¹ • ∑ i ∈ Finset.range b, e (start + i)‖ ≤ 2 * D / b := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (b : ℝ)⁻¹)]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left (shifted_prefix_bound e he start b)
      (show 0 ≤ (b : ℝ)⁻¹ by positivity)

lemma warmup_energy_bound {f : E → ℝ} {G : E → E} {L μ θ δ : ℝ}
    (hμ : 0 < μ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hstep : θ ^ 2 * L ≤ μ)
     (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hs : ∀ x y, f x + ⟪G x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (u : E) (hmin : ∀ x, f u ≤ f x) (v : ℕ → E × E) (e : ℕ → E)
    (he : ∀ k, ‖e k‖ ≤ δ)
    (hv : ∀ k, v (k + 1) = acceleratedUpdate θ μ (v k) (G (acceleratedQuery θ (v k)) + e k))
    (n : ℕ) :
    SimilarQuasar.energy f μ u (v n) ≤
      (1 - 3 * θ / 4) ^ n * SimilarQuasar.energy f μ u (v 0) + 4 * δ ^ 2 / μ := by
  have hρ : 0 ≤ 1 - 3 * θ / 4 := by linarith
  induction n with
  | zero =>
      simp only [pow_zero, one_mul]
      have hh : 0 ≤ 4 * δ ^ 2 / μ := by positivity
      linarith
  | succ n ih =>
      have hh := nonlinear_energy_step hμ hθ hθ1 hstep hg hlip hs (v n) u (e n) hmin
      rw [← hv] at hh
      have hnoise := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (he n) 2) (show 0 ≤ 3 * θ / μ by positivity)
      have hm := mul_le_mul_of_nonneg_left ih hρ
      calc
        _ ≤ (1 - 3 * θ / 4) *
              ((1 - 3 * θ / 4) ^ n * SimilarQuasar.energy f μ u (v 0) + 4 * δ ^ 2 / μ) +
              (3 * θ / μ) * δ ^ 2 := hh.trans (add_le_add hm hnoise)
        _ = _ := by rw [pow_succ]; ring

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma initial_nonlinear_energy {f : E → ℝ} {μ Δ : ℝ} (x u : E)
    (hgap : f x - f u ≤ Δ) (hstrong : μ / 2 * ‖x - u‖ ^ 2 ≤ f x - f u) :
    SimilarQuasar.energy f μ u (x, x) ≤ 2 * Δ := by
  unfold SimilarQuasar.energy
  dsimp only
  linarith

omit [CompleteSpace E] in
lemma local_energy_conversion {f : E → ℝ} {μ M : ℝ} (hμ : 0 < μ)
    (A : E →L[ℝ] E) (u : E) (s : E × E)
    (hstrong : μ / 2 * ‖s.1 - u‖ ^ 2 ≤ f s.1 - f u)
    (hrem : |f s.1 - f u - ‖A (s.1 - u)‖ ^ 2 / 2| ≤ M * ‖s.1 - u‖ ^ 3)
    (hsmall : M ^ 2 * SimilarQuasar.energy f μ u s ≤ μ ^ 3 / 1024) :
    energySeminorm A μ (s - (u, u)) ^ 2 ≤ (8 / 3 : ℝ) * SimilarQuasar.energy f μ u s ∧
      M * (energySeminorm A μ (s - (u, u)) / Real.sqrt μ) ≤ μ / 16 := by
  have hz : 0 ≤ μ / 2 * ‖s.2 - u‖ ^ 2 := by positivity
  have hg : 0 ≤ f s.1 - f u := (by positivity : 0 ≤ μ / 2 * ‖s.1 - u‖ ^ 2).trans hstrong
  have hx : μ / 2 * ‖s.1 - u‖ ^ 2 ≤ SimilarQuasar.energy f μ u s := by
    unfold SimilarQuasar.energy
    linarith
  have hxM := mul_le_mul_of_nonneg_left hx (sq_nonneg M)
  have hloc : 6 * M * ‖s.1 - u‖ ≤ μ := by
    have hs : (6 * M * ‖s.1 - u‖) ^ 2 ≤ μ ^ 2 := by
      nlinarith
    nlinarith [sq_nonneg (6 * M * ‖s.1 - u‖ - μ)]
  have hA := local_quadratic_upper A u s.1 hstrong hrem hloc
  have hp := energySeminorm_sq A hμ.le (s - (u, u))
  simp only [Prod.fst_sub, Prod.snd_sub] at hp
  have hpbound : energySeminorm A μ (s - (u, u)) ^ 2 ≤
      (8 / 3 : ℝ) * SimilarQuasar.energy f μ u s := by
    unfold SimilarQuasar.energy
    nlinarith
  refine ⟨hpbound, ?_⟩
  have hχ : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hχ2 := Real.sq_sqrt hμ.le
  have hpM := mul_le_mul_of_nonneg_left hpbound (sq_nonneg M)
  have hquad : (M * energySeminorm A μ (s - (u, u))) ^ 2 ≤
      (μ * Real.sqrt μ / 16) ^ 2 := by nlinarith
  have hlinear : M * energySeminorm A μ (s - (u, u)) ≤ μ * Real.sqrt μ / 16 := by
    have hpos : 0 ≤ μ * Real.sqrt μ / 16 := by positivity
    nlinarith [sq_nonneg (M * energySeminorm A μ (s - (u, u)) - μ * Real.sqrt μ / 16)]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hχ).mpr
  linarith

end OracleTemplate.NonlinearTemporalDiscrepancy
