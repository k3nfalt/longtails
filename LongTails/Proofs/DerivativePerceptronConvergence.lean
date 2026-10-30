import LongTails.Proofs.DerivativePerceptronTrajectory
import LongTails.Proofs.DerivativePerceptronCounting
import LongTails.Proofs.DerivativePerceptronParameters

open scoped RealInnerProductSpace

namespace LongTails.Proofs.DerivativePerceptronConvergence

open ManySampleConvolutionalPerceptronDynamics (State)
open ClusteredConvolutionalPerceptronDynamics (step)
open DerivativePerceptronTrajectory DerivativePerceptronCounting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
lemma postwarm_contradiction (x : ℕ → State E) (b : ℕ → ℝ) (p rvec : ℕ → E)
    (w : E) (δ κ r h ρ : ℝ) (K K₀ N : ℕ)
    (hδ : 0 < δ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hr : 0 < r) (hr₁ : r ≤ 1)
    (hh : 0 < h) (hhκ : h ≤ κ / 4) (hρeq : ρ = r * h) (hw : ‖w‖ = 1)
    (htotal : K = N + K₀) (hinit : 16777216 * (K₀ : ℝ) ≤ κ ^ 2 * r ^ 2 * (K : ℝ))
    (hlinear : 65536 ≤ κ ^ 2 * (K : ℝ)) (hΛ : 1024 * leakage h h ρ ≤ κ ^ 2)
    (hcubic : 16384 * δ * (K : ℝ) ≤ κ ^ 2) (hK₀size : 1 ≤ ρ ^ 2 * (K₀ : ℝ))
    (hz₀ : ‖(x 0).z‖ ≤ 4 * (K₀ : ℝ))
    (hx₀ : (max |(x 0).a| |(x 0).q|) ^ 2 ≤ 4096 * δ * (K₀ : ℝ) / ρ ^ 2)
    (hu : ∀ k < N, x (k + 1) = step (b k) δ (p k) (rvec k) (x k))
    (hp : ∀ k < N, ‖p k‖ ≤ 1) (hrvec : ∀ k < N, ‖rvec k‖ ≤ 1)
    (hsep : ∀ k < N, κ ≤ ⟪rvec k, w⟫)
    (hb : ∀ k < N, ρ ≤ |b k|) (hbu : ∀ k < N, |b k| ≤ h)
    (hx : ∀ k < N, max |(x k).a| |(x k).q| ≤ h)
    (ht : ∀ k < N, |(x k).t| ≤ 2) (htlow : ∀ k < N, 1 / 2 ≤ (x k).t)
    (hz : ∀ k < N, ‖(x k).z‖ ≤ 4 * (K : ℝ))
    (hplateau : ∀ k < N, (x k).a ^ 2 ≤ 4096 * δ * (K : ℝ) / ρ ^ 2)
    (hg : ∀ k < N, b k * (x k).a * (x k).q +
      δ * ((x k).a * ⟪p k, (x k).z⟫ + (x k).t * ⟪rvec k, (x k).z⟫) ≤ 0) : False := by
  have hρ : 0 < ρ := hρeq ▸ mul_pos hr hh
  have hhu : h ≤ 1 := by linarith only [hhκ, hκ₁]
  let Q := 4096 * δ * (K₀ : ℝ) / ρ ^ 2
  let J := Q + 16 * δ * (K : ℝ) * h / ρ ^ 2
  let D := Q + 12 * δ * (K : ℝ) / ρ + J + 24 * δ * (K : ℝ) +
    16 * h ^ 2 * δ * (K : ℝ) * h
  let P := 4096 * δ * (K : ℝ) / ρ ^ 2
  have hparams := barrier_parameters δ h h ρ (K : ℝ) (K₀ : ℝ)
    hδ.le hh.le hρ (Nat.cast_nonneg K) (Nat.cast_nonneg K₀)
  dsimp only at hparams
  obtain ⟨hJ, hDJ, hQJ, hQD, hforce, hD⟩ := hparams
  have hm₀ : 0 ≤ max |(x 0).a| |(x 0).q| := (abs_nonneg _).trans (le_max_left _ _)
  have ha₀ : (x 0).a ^ 2 ≤ Q := by
    have hm := le_max_left |(x 0).a| |(x 0).q|
    dsimp [Q]
    nlinarith only [hx₀, hm, hm₀, sq_abs (x 0).a, abs_nonneg (x 0).a]
  have hq₀ : (x 0).q ^ 2 ≤ Q := by
    have hm := le_max_right |(x 0).a| |(x 0).q|
    dsimp [Q]
    nlinarith only [hx₀, hm, hm₀, sq_abs (x 0).q, abs_nonneg (x 0).q]
  have hI₀ : (x 0).q ^ 2 - (x 0).a ^ 2 ≤ J := by
    change Q ≤ J at hQJ
    nlinarith only [hq₀, hQJ, sq_nonneg (x 0).a]
  have hF₀ : (x 0).q ^ 2 - h ^ 2 * (x 0).a ^ 2 ≤ D := by
    change Q ≤ D at hQD
    nlinarith only [hq₀, hQD, mul_nonneg (sq_nonneg h) (sq_nonneg (x 0).a)]
  have hbar := trajectory_barriers x b p rvec δ ρ h h (4 * (K : ℝ)) J D N
    hδ.le hρ hh.le hhu hhu (by positivity) hJ hDJ hforce hD hI₀ hF₀
    hu hp hrvec hb hbu hx ht hz hg
  have henergy := energy_sum x b p rvec δ h h (4 * (K : ℝ)) P D N
    hδ.le hh.le hhu hhu hu hp hrvec hbu hx ht hz hplateau
    (fun k hk => (hbar k (Nat.le_of_lt hk)).2) hg
  have hstart := restart_energy_bound ‖(x 0).z‖ (x 0).a δ ρ (K₀ : ℝ)
    (norm_nonneg _) hδ.le hρ (Nat.cast_nonneg K₀) hz₀ ha₀ hK₀size
  let C := 9 * δ + 4 * δ * h * (4 * (K : ℝ)) + δ ^ 2 * (4 * (K : ℝ)) ^ 2 +
    h ^ 4 * P + h ^ 2 * D
  have hD₀ : 0 ≤ D := le_trans hJ hDJ
  have hC₀ : 0 ≤ C := by dsimp [C, P]; positivity
  have hC := scaled_increment_identity δ h h r (K : ℝ) (K₀ : ℝ) hh hr
  dsimp only at hC
  rw [← hρeq] at hC
  change C = δ * (9 + 8192 * (K₀ : ℝ) / r ^ 2 + leakage h h ρ * (K : ℝ) +
    16 * δ * (K : ℝ) ^ 2) at hC
  have hNK : (N : ℝ) ≤ K := Nat.cast_le.mpr (by omega)
  have hNC := mul_le_mul_of_nonneg_right hNK hC₀
  have hKC := congrArg (fun v : ℝ => (K : ℝ) * v) hC
  change δ * ‖(x N).z‖ ^ 2 + (x N).a ^ 2 ≤
    δ * ‖(x 0).z‖ ^ 2 + (x 0).a ^ 2 + (N : ℝ) * C at henergy
  have hupper : δ * ‖(x N).z‖ ^ 2 + (x N).a ^ 2 ≤ δ *
      (4112 * (K₀ : ℝ) ^ 2 + 9 * (K : ℝ) + 8192 * (K : ℝ) * (K₀ : ℝ) / r ^ 2 +
        leakage h h ρ * (K : ℝ) ^ 2 + 16 * δ * (K : ℝ) ^ 3) := by
    simp only [div_eq_mul_inv] at hKC ⊢
    nlinarith only [henergy, hstart, hNC, hKC]
  have hprogress := projection_sum x b p rvec δ κ w N hκ.le hw hu hp hsep
    (fun k hk => (le_max_left _ _).trans ((hx k hk).trans hhκ)) htlow
  have hr₂ : r ^ 2 ≤ 1 := by nlinarith only [hr.le, hr₁]
  have hκ₂ : κ ^ 2 ≤ κ := by nlinarith only [hκ.le, hκ₁]
  have hm := mul_le_mul_of_nonneg_left hr₂ (sq_nonneg κ)
  have hκr : κ ^ 2 * r ^ 2 ≤ κ := by nlinarith only [hm, hκ₂]
  have hmK := mul_le_mul_of_nonneg_right hκr (Nat.cast_nonneg K)
  have hsize : 64 * (K₀ : ℝ) ≤ κ * (K : ℝ) := by nlinarith only [hinit, hmK, (show (0 : ℝ) ≤ K₀ from Nat.cast_nonneg K₀)]
  have hnorm := projection_norm_lower (x 0).z (x N).z w κ (K : ℝ) (K₀ : ℝ) (N : ℝ)
    hw hκ.le hκ₁ (Nat.cast_nonneg K) (Nat.cast_nonneg K₀)
    (by exact_mod_cast htotal) hz₀ hsize hprogress
  have hKpos : (0 : ℝ) < K := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg κ) (le_of_not_gt hn)
    linarith only [hm, hlinear]
  apply energy_contradiction ((δ * ‖(x N).z‖ ^ 2 + (x N).a ^ 2) / δ)
    (K : ℝ) (K₀ : ℝ) κ r δ (leakage h h ρ) hKpos (Nat.cast_nonneg K₀)
    hκ hκ₁ hr hr₁ hinit hlinear hΛ hcubic
  · apply (div_le_iff₀ hδ).mpr
    nlinarith only [hupper]
  · apply (le_div_iff₀ hδ).mpr
    have hm := mul_le_mul_of_nonneg_left hnorm hδ.le
    nlinarith only [hm, sq_nonneg (x N).a]

set_option maxHeartbeats 1200000 in
lemma mistake_horizon_impossible (x : ℕ → State E) (b : ℕ → ℝ) (p rvec : ℕ → E)
    (w : E) (δ κ r h ρ : ℝ) (K K₀ n₀ : ℕ)
    (hδ : 0 < δ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hr : 0 < r) (hr₁ : r ≤ 1)
    (hh : 0 < h) (hhκ : h ≤ κ / 4) (hρeq : ρ = r * h) (hw : ‖w‖ = 1)
    (hK₀ : 1 ≤ K₀) (hK₀K : K₀ ≤ K) (heven : K₀ = 2 * n₀)
    (hlog : Real.log (1 / δ) ≤ (ρ ^ 2 / 8) * (n₀ : ℝ))
    (hsharp : 16384 * δ * (K : ℝ) ≤ ρ ^ 2 * h ^ 2)
    (hquadratic : δ * (K : ℝ) ^ 2 ≤ 1 / 16)
    (hinit : 16777216 * (K₀ : ℝ) ≤ κ ^ 2 * r ^ 2 * (K : ℝ))
    (hlinear : 65536 ≤ κ ^ 2 * (K : ℝ)) (hΛ : 1024 * leakage h h ρ ≤ κ ^ 2)
    (hcubic : 16384 * δ * (K : ℝ) ≤ κ ^ 2) (hK₀size : 1 ≤ ρ ^ 2 * (K₀ : ℝ))
    (hx₀ : x 0 = ⟨1, 0, 1, 0⟩)
    (hu : ∀ k < K, x (k + 1) = step (b k) δ (p k) (rvec k) (x k))
    (hp : ∀ k < K, ‖p k‖ ≤ 1) (hrvec : ∀ k < K, ‖rvec k‖ ≤ 1)
    (hsep : ∀ k < K, κ ≤ ⟪rvec k, w⟫)
    (hb : ∀ k < K, ρ ≤ |b k|) (hbu : ∀ k < K, |b k| ≤ h)
    (hg : ∀ k < K, b k * (x k).a * (x k).q +
      δ * ((x k).a * ⟪p k, (x k).z⟫ + (x k).t * ⟪rvec k, (x k).z⟫) ≤ 0) : False := by
  have hρ : 0 < ρ := hρeq ▸ mul_pos hr hh
  have hh₄ : h ≤ 1 / 4 := by linarith only [hhκ, hκ₁]
  have hhu : h ≤ 1 := by linarith only [hh₄]
  have hρh : ρ ≤ h := by rw [hρeq]; nlinarith only [mul_le_mul_of_nonneg_right hr₁ hh.le]
  have hρ₄ : ρ ≤ 1 / 4 := hρh.trans hh₄
  have hh₂ : h ^ 2 ≤ 1 := by nlinarith only [hh.le, hhu]
  have hρ₂ : ρ ^ 2 ≤ 1 := by nlinarith only [hρ.le, hρ₄]
  have hmul := mul_le_mul_of_nonneg_left hh₂ (sq_nonneg ρ)
  have hδK : 0 ≤ δ * (K : ℝ) := by positivity
  have hsmall : 864 * δ * (K : ℝ) ≤ ρ ^ 2 := by nlinarith only [hsharp, hmul, hδK]
  have he : δ * (4 * (K : ℝ)) ≤ 1 := by nlinarith only [hsmall, hρ₂, hδK]
  have hxinit : max |(x 0).a| |(x 0).q| ≤ 1 := by simp [hx₀]
  have hcoarse := warmup_bounds x b p rvec δ ρ K hδ.le hρ.le hρ₄ hsmall hquadratic
    hxinit (by simp [hx₀]) (by simp [hx₀]) hu hp hrvec hb
    (fun k hk => (hbu k hk).trans hh₄) hg
  have ht : ∀ k < K, |(x k).t| ≤ 2 := by
    intro k hk
    have hd := (hcoarse k (Nat.le_of_lt hk)).2.1
    have ht := abs_add_le ((x k).t - 1) (1 : ℝ)
    simp only [sub_add_cancel, abs_one] at ht
    linarith only [hd, ht]
  have htlow : ∀ k < K, 1 / 2 ≤ (x k).t := by
    intro k hk
    have hd := (abs_le.mp (hcoarse k (Nat.le_of_lt hk)).2.1).1
    linarith only [hd]
  have hz : ∀ k < K, ‖(x k).z‖ ≤ 4 * (K : ℝ) := by
    intro k hk
    have hd := (hcoarse k (Nat.le_of_lt hk)).2.2
    have hc : (k : ℝ) ≤ K := Nat.cast_le.mpr (Nat.le_of_lt hk)
    linarith only [hd, hc]
  have hKcast : (K₀ : ℝ) ≤ K := Nat.cast_le.mpr hK₀K
  have hδK₀ := mul_le_mul_of_nonneg_left hKcast hδ.le
  have he₀ : δ * (4 * (K₀ : ℝ)) ≤ 1 := by nlinarith only [he, hδK₀]
  have hrestart := postwarm_plateau x b p rvec δ ρ K₀ n₀ hδ hρ hρ₄ hK₀ he₀ hlog hxinit
    (fun j hj => hu j (by omega)) (fun j hj => hp j (by omega))
    (fun j hj => hrvec j (by omega)) (fun j hj => hb j (by omega))
    (fun j hj => (hbu j (by omega)).trans hh₄)
    (fun j hj => (hcoarse j (by omega)).1) (fun j hj => ht j (by omega))
    (fun j hj => by
      have hd := (hcoarse j (by omega)).2.2
      have hc : (j : ℝ) ≤ K₀ := Nat.cast_le.mpr (by omega)
      linarith only [hd, hc])
    (fun j hj => hg j (by omega)) K₀ (by omega) le_rfl
  have hrestartSmall : (max |(x K₀).a| |(x K₀).q|) ^ 2 ≤ h ^ 2 / 4 := by
    apply hrestart.trans
    apply (div_le_iff₀ (sq_pos_of_pos hρ)).mpr
    nlinarith only [hsharp, hδK₀]
  have hplateau := postwarm_plateau x b p rvec δ ρ K n₀ hδ hρ hρ₄
    (hK₀.trans hK₀K) he hlog hxinit hu hp hrvec hb
    (fun j hj => (hbu j hj).trans hh₄) (fun j hj => (hcoarse j (Nat.le_of_lt hj)).1)
    ht hz hg
  let N := K - K₀
  have htotal : K = N + K₀ := by dsimp [N]; omega
  have hindex : ∀ j < N, K₀ + j < K := by intro j hj; omega
  have hshift : ∀ j < N, x (K₀ + (j + 1)) =
      step (b (K₀ + j)) δ (p (K₀ + j)) (rvec (K₀ + j)) (x (K₀ + j)) := by
    intro j hj
    simpa only [Nat.add_assoc] using hu (K₀ + j) (hindex j hj)
  have hsmallPost : 640 * δ * (4 * (K : ℝ)) ≤ ρ ^ 2 * h ^ 2 := by
    nlinarith only [hsharp, hδK]
  have henvelope := small_scalar_envelope (fun j => x (K₀ + j)) (fun j => b (K₀ + j))
    (fun j => p (K₀ + j)) (fun j => rvec (K₀ + j)) δ ρ h (4 * (K : ℝ)) N
    hδ.le hρ.le hρ₄ hh.le hhu (by positivity) he hsmallPost
    (by simpa using hrestartSmall) hshift
    (fun j hj => hp _ (hindex j hj)) (fun j hj => hrvec _ (hindex j hj))
    (fun j hj => hb _ (hindex j hj)) (fun j hj => (hbu _ (hindex j hj)).trans hh₄)
    (fun j hj => ht _ (hindex j hj)) (fun j hj => hz _ (hindex j hj))
    (fun j hj => hg _ (hindex j hj))
  apply postwarm_contradiction (fun j => x (K₀ + j)) (fun j => b (K₀ + j))
    (fun j => p (K₀ + j)) (fun j => rvec (K₀ + j)) w δ κ r h ρ K K₀ N
    hδ hκ hκ₁ hr hr₁ hh hhκ hρeq hw htotal hinit hlinear hΛ hcubic hK₀size
    (by simpa using (hcoarse K₀ hK₀K).2.2) (by simpa using hrestart) hshift
    (fun j hj => hp _ (hindex j hj)) (fun j hj => hrvec _ (hindex j hj))
    (fun j hj => hsep _ (hindex j hj)) (fun j hj => hb _ (hindex j hj))
    (fun j hj => hbu _ (hindex j hj)) (fun j hj => henvelope j (Nat.le_of_lt hj))
    (fun j hj => ht _ (hindex j hj)) (fun j hj => htlow _ (hindex j hj))
    (fun j hj => hz _ (hindex j hj))
  · intro j hj
    have hh := hplateau (K₀ + j) (by omega) (Nat.le_of_lt (hindex j hj))
    have hm := le_max_left |(x (K₀ + j)).a| |(x (K₀ + j)).q|
    have hn : 0 ≤ max |(x (K₀ + j)).a| |(x (K₀ + j)).q| := (abs_nonneg _).trans hm
    nlinarith only [hh, hm, hn, abs_nonneg (x (K₀ + j)).a, sq_abs (x (K₀ + j)).a]
  · exact fun j hj => hg _ (hindex j hj)

lemma tuned_mistake_horizon_impossible (t : DerivativePerceptronParameters.Tuning)
    (x : ℕ → State E) (b : ℕ → ℝ) (p rvec : ℕ → E) (w : E)
    (hw : ‖w‖ = 1) (hx₀ : x 0 = ⟨1, 0, 1, 0⟩)
    (hu : ∀ k < t.iterations,
      x (k + 1) = step (b k) t.residualScale (p k) (rvec k) (x k))
    (hp : ∀ k < t.iterations, ‖p k‖ ≤ 1)
    (hrvec : ∀ k < t.iterations, ‖rvec k‖ ≤ 1)
    (hsep : ∀ k < t.iterations, t.κ ≤ ⟪rvec k, w⟫)
    (hb : ∀ k < t.iterations, t.backgroundScale ≤ |b k|)
    (hbu : ∀ k < t.iterations, |b k| ≤ t.stepScale)
    (hg : ∀ k < t.iterations, b k * (x k).a * (x k).q +
      t.residualScale * ((x k).a * ⟪p k, (x k).z⟫ +
        (x k).t * ⟪rvec k, (x k).z⟫) ≤ 0) : False := by
  exact mistake_horizon_impossible x b p rvec w t.residualScale t.κ t.r
    t.stepScale t.backgroundScale t.iterations t.warmup
    ⌈8 / t.backgroundScale ^ 2 * Real.log (1 / t.residualScale)⌉₊
    t.residualScale_pos t.margin_pos t.margin_le t.ratio_pos t.ratio_le
    t.stepScale_pos t.stepScale_margin rfl hw t.warmup_pos t.warmup_le_iterations rfl
    t.warmup_log_threshold t.sharp_smallness t.quadratic_smallness t.warmup_dominated
    t.iterations_linear t.leakage_small t.cubic_smallness t.warmup_size
    hx₀ hu hp hrvec hsep hb hbu hg

end LongTails.Proofs.DerivativePerceptronConvergence
