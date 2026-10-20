import LongTails.Proofs.LoraModel
import LongTails.Proofs.LocalGdWarmup

namespace LongTails.Proofs.LoraWarmup

open LongTails.Algorithms.LoraGd LongTails.Setups.LocalSmoothStronglyConvexLora
open LongTails.Proofs.LoraModel LongTails.Proofs.LoraGeometry
open scoped RealInnerProductSpace

variable {p : Params} {f : MatrixSpace p.m p.n → ℝ} {c : Factors p.m p.n p.r}

lemma initial_radius_bound (H : Model p f c) :
    p.μ * p.s ^ 2 / (256 * p.ρ * p.R) ≤ p.s / 256 := by
  apply (div_le_iff₀ (show 0 < 256 * p.ρ * p.R by have := H.rho_pos; have := H.R_pos; positivity)).mpr
  have h1 := mul_le_mul_of_nonneg_right H.mu_le (sq_nonneg p.s)
  have h2 := mul_le_mul_of_nonneg_left H.s_le (show 0 ≤ p.ρ * p.s by
    have := H.rho_pos; have := H.s_pos; positivity)
  nlinarith

lemma initial_gap (H : Model p f c) (x : Factors p.m p.n p.r)
    (hx : ‖x - c‖ ≤ p.μ * p.s ^ 2 / (256 * p.ρ * p.R)) :
    f (product x) - f (product c) ≤ (growth p) ^ 2 / (256 * p.ρ) := by
  have hnear : ‖x - c‖ ≤ p.s / 2 := by
    have hh := hx.trans (initial_radius_bound H)
    have := H.s_pos
    linarith
  have hh := LongTails.Proofs.LoraObjective.objective_upper_ball c x c
    (le_of_lt H.rho_pos) (le_of_lt H.R_pos) (le_of_lt H.s_pos) H.s_le H.reference
    (by simp; have := H.s_pos; positivity) hnear H.gradient_zero H.grad H.lip
  rw [pullback_adjoint, H.gradient_zero, map_zero, inner_zero_left, add_zero] at hh
  have hx2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hscaled := mul_le_mul_of_nonneg_left hx2
    (show 0 ≤ (8 * p.ρ * p.R ^ 2) / 2 by have := H.rho_pos; positivity)
  have he : (8 * p.ρ * p.R ^ 2) / 2 *
      (p.μ * p.s ^ 2 / (256 * p.ρ * p.R)) ^ 2 = (growth p) ^ 2 / (256 * p.ρ) := by
    have := ne_of_gt H.rho_pos
    have := ne_of_gt H.R_pos
    unfold growth
    field_simp
    ring
  rw [he] at hscaled
  linarith

lemma outer_gradient_cap (H : Model p f c) (x : Factors p.m p.n p.r)
    (hx : f (product x) - f (product c) ≤ (growth p) ^ 2 / (256 * p.ρ)) :
    ‖gradient f (product x)‖ ≤ growth p / 8 := by
  have hh := H.self_bound x
  have hs := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2 * p.ρ by have := H.rho_pos; positivity)
  have he : 2 * p.ρ * ((growth p) ^ 2 / (256 * p.ρ)) = (growth p) ^ 2 / 128 := by
    have := ne_of_gt H.rho_pos
    field_simp
    ring
  rw [he] at hs
  have := H.growth_pos
  nlinarith [norm_nonneg (gradient f (product x))]

lemma initial_length_cap (H : Model p f c) {e : ℝ} (he : 0 ≤ e)
    (hecap : e ≤ (growth p) ^ 2 / (256 * p.ρ)) :
    4 * Real.sqrt (2 / growth p) * Real.sqrt e ≤ p.s / 8 := by
  have hα := H.growth_pos
  have hρ := H.rho_pos
  have hs := H.s_pos
  have hroot := Real.sq_sqrt he
  have hrootα := Real.sq_sqrt (show 0 ≤ 2 / growth p by positivity)
  have hcap := mul_le_mul_of_nonneg_left hecap (show 0 ≤ 32 / growth p by positivity)
  have hc : (32 / growth p) * ((growth p) ^ 2 / (256 * p.ρ)) = growth p / (8 * p.ρ) := by
    have := ne_of_gt hα
    have := ne_of_gt hρ
    field_simp
    ring
  rw [hc] at hcap
  have hαs : growth p / (8 * p.ρ) ≤ p.s ^ 2 / 64 := by
    apply (div_le_iff₀ (show 0 < 8 * p.ρ by positivity)).mpr
    unfold growth
    nlinarith [mul_le_mul_of_nonneg_right H.mu_le (sq_nonneg p.s)]
  have heq : (4 * Real.sqrt (2 / growth p) * Real.sqrt e) ^ 2 = (32 / growth p) * e := by
    rw [mul_pow, mul_pow, hroot, hrootα]
    ring
  have hnon : 0 ≤ 4 * Real.sqrt (2 / growth p) * Real.sqrt e := by positivity
  nlinarith

lemma step (H : Model p f c) (u : Factors p.m p.n p.r)
    (hu : ‖u - c‖ ≤ 33 * p.s / 256)
    (he : f (product u) - f (product c) ≤ (growth p) ^ 2 / (256 * p.ρ)) :
    let g := pullback u (gradient f (product u))
    let v := u - (1 / smoothness p) • g
    0 ≤ f (product v) - f (product c) ∧
      f (product v) - f (product c) ≤ f (product u) - f (product c) - ‖g‖ ^ 2 / (2 * smoothness p) ∧
      growth p * (f (product u) - f (product c)) ≤ 2 * ‖g‖ ^ 2 := by
  intro g v
  have hs := H.s_pos
  have hR := H.R_pos
  have hρ := H.rho_pos
  have hL := H.smoothness_pos
  have hnear : ‖u - c‖ ≤ p.s / 2 := by linarith
  have hM := outer_gradient_cap H u he
  have hD : ‖derivative u‖ ≤ 2 * p.R :=
    (derivative_local_bound u c H.reference (le_of_lt hR) hnear).trans (by linarith [H.s_le])
  have hg : ‖g‖ ≤ 2 * p.R * (growth p / 8) := by
    dsimp [g]
    rw [pullback_adjoint]
    calc
      ‖(derivative u).adjoint (gradient f (product u))‖ ≤
          ‖(derivative u).adjoint‖ * ‖gradient f (product u)‖ :=
        (derivative u).adjoint.le_opNorm _
      _ = ‖derivative u‖ * ‖gradient f (product u)‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ _ := mul_le_mul hD hM (norm_nonneg _) (by positivity)
  have hstep : ‖(1 / smoothness p) • g‖ ≤ p.s / 256 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hL)]
    have hh := mul_le_mul_of_nonneg_left hg (le_of_lt (one_div_pos.mpr hL))
    have heq : (1 / smoothness p) * (2 * p.R * (growth p / 8)) =
        p.μ * p.s ^ 2 / (256 * p.ρ * p.R) := by
      have := ne_of_gt hρ
      have := ne_of_gt hR
      unfold smoothness growth
      field_simp
      ring
    rw [heq] at hh
    exact hh.trans (initial_radius_bound H)
  have hv : ‖v - c‖ ≤ p.s / 2 := by
    have hh : ‖v - c‖ ≤ ‖u - c‖ + ‖(1 / smoothness p) • g‖ := by
      have heq : v - c = (u - c) - (1 / smoothness p) • g := by dsimp [v]; abel
      rw [heq]
      exact norm_sub_le _ _
    linarith
  refine ⟨H.gap_nonneg v, ?_, H.domination u hnear (hM.trans (by have := H.growth_pos; linarith))⟩
  have hh := LongTails.Proofs.LoraObjective.objective_upper_ball u v c
    (le_of_lt hρ) (le_of_lt hR) (le_of_lt hs) H.s_le H.reference hnear hv
    H.gradient_zero H.grad H.lip
  change f (product v) ≤ f (product u) + ⟪g, v - u⟫ + smoothness p / 2 * ‖v - u‖ ^ 2 at hh
  have heq : v - u = -(1 / smoothness p) • g := by dsimp [v]; module
  rw [heq, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, abs_neg, abs_of_pos (one_div_pos.mpr hL)] at hh
  have hcoef : -(1 / smoothness p) * ‖g‖ ^ 2 +
      smoothness p / 2 * ((1 / smoothness p) * ‖g‖) ^ 2 = -‖g‖ ^ 2 / (2 * smoothness p) := by
    have := ne_of_gt hL
    field_simp
    ring
  rw [add_assoc, hcoef, neg_div] at hh
  linarith

lemma trajectory (H : Model p f c) (x : ℕ → Factors p.m p.n p.r)
    (hx : ‖x 0 - c‖ ≤ p.μ * p.s ^ 2 / (256 * p.ρ * p.R))
    (hupdate : ∀ k, x (k + 1) = x k - (1 / smoothness p) • pullback (x k) (gradient f (product (x k)))) :
    ∀ k, 0 ≤ f (product (x k)) - f (product c) ∧
      f (product (x k)) - f (product c) ≤
        (f (product (x 0)) - f (product c)) * (1 - growth p / (4 * smoothness p)) ^ k ∧
      ‖x k - c‖ ≤ 33 * p.s / 256 := by
  let e₀ := f (product (x 0)) - f (product c)
  have he₀ : 0 ≤ e₀ := H.gap_nonneg _
  have hecap : e₀ ≤ growth p ^ 2 / (256 * p.ρ) := initial_gap H (x 0) hx
  have hpath := initial_length_cap H he₀ hecap
  have hinit := hx.trans (initial_radius_bound H)
  have hroom : ‖x 0 - c‖ + 4 * Real.sqrt (2 / growth p) * Real.sqrt e₀ ≤ 33 * p.s / 256 := by linarith
  have hh := LongTails.Proofs.LocalGdWarmup.trajectory_bound
    (fun u => f (product u) - f (product c)) (fun u => pullback u (gradient f (product u)))
    x c H.smoothness_pos H.growth_pos
    (show growth p ≤ 4 * smoothness p by have := H.growth_le; have := H.smoothness_pos; linarith)
    he₀ rfl hroom hupdate (fun u hu he => step H u hu (he.trans hecap))
  intro k
  obtain ⟨hnon, hgap, hdist⟩ := hh k
  refine ⟨hnon, hgap, ?_⟩
  have hn : ‖x k - c‖ ≤ ‖x k - x 0‖ + ‖x 0 - c‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (x k - x 0) (x 0 - c)
  have hprod : 0 ≤ 4 * Real.sqrt (2 / growth p) * Real.sqrt (f (product (x k)) - f (product c)) := by positivity
  nlinarith

lemma repair_center (H : Model p f c) (x : Factors p.m p.n p.r)
    (hx : ‖x - c‖ ≤ 33 * p.s / 256)
    (he : f (product x) - f (product c) ≤ growth p ^ 2 / (256 * p.ρ)) :
    ∃ z : Factors p.m p.n p.r, product z = product c ∧
      growth p * ‖x - z‖ ^ 2 ≤ 2 * (f (product x) - f (product c)) ∧
      ‖z - c‖ ≤ 41 * p.s / 256 := by
  have hs := H.s_pos
  have hα := H.growth_pos
  have hρ := H.rho_pos
  obtain ⟨z, hz, hd⟩ := H.repair x (by linarith)
  have hbound : growth p / (128 * p.ρ) ≤ p.s ^ 2 / 1024 := by
    apply (div_le_iff₀ (show 0 < 128 * p.ρ by positivity)).mpr
    unfold growth
    nlinarith [mul_le_mul_of_nonneg_right H.mu_le (sq_nonneg p.s)]
  have hsq : ‖x - z‖ ^ 2 ≤ growth p / (128 * p.ρ) := by
    apply (mul_le_mul_iff_of_pos_left hα).mp
    have heq : 2 * (growth p ^ 2 / (256 * p.ρ)) = growth p * (growth p / (128 * p.ρ)) := by ring
    nlinarith
  have hdist : ‖x - z‖ ≤ p.s / 32 := by nlinarith [norm_nonneg (x - z)]
  refine ⟨z, hz, hd, ?_⟩
  have hn : ‖z - c‖ ≤ ‖x - z‖ + ‖x - c‖ := by
    have hh := norm_add_le (z - x) (x - c)
    rwa [sub_add_sub_cancel, norm_sub_rev z x] at hh
  linarith

end LongTails.Proofs.LoraWarmup
