import LongTails.Proofs.QuasarInexact
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Set Filter InnerProductSpace
open scoped RealInnerProductSpace Topology

namespace OracleTemplate.SimilarQuasar

lemma radial_quasar_growth {F F' : ℝ → ℝ} {c γ : ℝ} (hγ : γ ≤ 1)
    (hzero : F 0 = 0) (hderiv0 : HasDerivAt F 0 0)
    (hderiv : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt F (F' t) t)
    (haim : ∀ t ∈ Ioc (0 : ℝ) 1, γ * F t + c * t ^ 2 ≤ t * F' t) :
    c / (2 - γ) ≤ F 1 := by
  let a := c / (2 - γ)
  let H := fun t : ℝ => (F t / t - a * t) * t ^ (1 - γ)
  have ha : a * (2 - γ) = c := by
    exact div_mul_cancel₀ c (by linarith : 2 - γ ≠ 0)
  have hH : ∀ t ∈ Ioc (0 : ℝ) 1,
      HasDerivAt H ((t * F' t - γ * F t - c * t ^ 2) / t ^ 2 * t ^ (1 - γ)) t := by
    intro t ht
    have hd := (((hderiv t ht).div (hasDerivAt_id t) ht.1.ne').sub
      ((hasDerivAt_id t).const_mul a)).mul
        (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl ht.1.ne'))
    convert hd using 1
    · rfl
    · dsimp
      rw [Real.rpow_sub_one ht.1.ne', ← ha]
      field_simp [ht.1.ne']
      ring
  have hmono : MonotoneOn H (Ioc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
    · exact fun t ht => (hH t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hH t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioc (0 : ℝ) 1 := interior_subset ht
      rw [(hH t ht').deriv]
      exact mul_nonneg (div_nonneg (by linarith [haim t ht']) (sq_nonneg t))
        (Real.rpow_nonneg ht'.1.le _)
  have hlimF : Tendsto (fun t : ℝ => F t / t) (𝓝[>] 0) (𝓝 0) := by
    simpa [hzero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hderiv0.tendsto_slope_zero_right
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpow : ContinuousAt (fun t : ℝ => t ^ (1 - γ)) 0 :=
    Real.continuous_rpow_const (by linarith : 0 ≤ 1 - γ) |>.continuousAt
  have hlim : Tendsto H (𝓝[>] 0) (𝓝 0) := by
    simpa [H] using (hlimF.sub (tendsto_const_nhds.mul ht)).mul
      (hpow.tendsto.mono_left nhdsWithin_le_nhds)
  have hle : 0 ≤ H 1 := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with t ht0 ht1
    exact hmono ⟨ht0, ht1.le⟩ (by simp) ht1.le
  simpa [H, a] using hle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma strong_quasar_quadratic_growth {f : E → ℝ} {g : E → E} {μ γ : ℝ} {u : E}
    (hg : ∀ x, HasGradientAt f (g x) x) (hγ : γ ≤ 1)
    (hmin : ∀ x, f u ≤ f x)
    (hq : ∀ x, γ * f x + ⟪g x, u - x⟫ + γ * μ / 2 * ‖u - x‖ ^ 2 ≤ γ * f u)
    (x : E) : γ * μ / (2 * (2 - γ)) * ‖x - u‖ ^ 2 ≤ f x - f u := by
  let F := fun t : ℝ => f (u + t • (x - u)) - f u
  let F' := fun t : ℝ => ⟪g (u + t • (x - u)), x - u⟫
  have hF : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    have h := ((hg _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const (x - u) |>.const_add u)).sub_const (f u)
    simpa [F, F', toDual_apply_apply] using h
  have hFmin : IsLocalMin F 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa [F] using sub_nonneg.mpr (hmin (u + t • (x - u)))
  have hF'zero : F' 0 = 0 := hFmin.hasDerivAt_eq_zero (hF 0)
  have hbound := radial_quasar_growth (c := γ * μ / 2 * ‖x - u‖ ^ 2) hγ
    (by simp [F]) (by simpa only [hF'zero] using hF 0) (fun t _ => hF t) (by
      intro t ht
      have h := hq (u + t • (x - u))
      have he : u - (u + t • (x - u)) = -(t • (x - u)) := by abel
      rw [he] at h
      simp only [inner_neg_right, inner_smul_right, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht.1, mul_pow] at h
      dsimp [F, F']
      nlinarith only [h])
  have he : γ * μ / 2 * ‖x - u‖ ^ 2 / (2 - γ) =
      γ * μ / (2 * (2 - γ)) * ‖x - u‖ ^ 2 := by
    field_simp
  simpa [F, he] using hbound

omit [CompleteSpace E] in
lemma offset_fullGradient {n : ℕ} (g : Fin n × E → E) (a : Fin n → E)
    (ha : ∑ i, a i = 0) (x : E) :
    FiniteSum.fullGradient (fun ix => g ix + a ix.1) x = FiniteSum.fullGradient g x := by
  simp [FiniteSum.fullGradient, Finset.sum_add_distrib, ha]

omit [CompleteSpace E] in
lemma offset_estimator {n : ℕ} (g : Fin n × E → E) (a : Fin n → E)
    (ha : ∑ i, a i = 0) (w x : E) (i : Fin n) :
    FiniteSum.estimator (fun ix => g ix + a ix.1) w x i = FiniteSum.estimator g w x i := by
  simp only [FiniteSum.estimator, offset_fullGradient g a ha]
  abel

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma offset_similarity {n : ℕ} (g : Fin n × E → E) (G : E → E) (a : Fin n → E)
    (i : Fin n) (x y : E) :
    (g (i, x) + a i - G x) - (g (i, y) + a i - G y) =
      (g (i, x) - G x) - (g (i, y) - G y) := by abel

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma energy_nonneg {f : E → ℝ} {μ : ℝ} (hμ : 0 ≤ μ) {u : E}
    (hmin : ∀ x, f u ≤ f x) (s : E × E) : 0 ≤ energy f μ u s := by
  have hn : 0 ≤ μ / 2 * ‖s.2 - u‖ ^ 2 := by positivity
  dsimp [energy]
  linarith [hmin s.1]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma energy_distances {f : E → ℝ} {μ γ : ℝ} (hμ : 0 < μ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {u : E}
    (hmin : ∀ x, f u ≤ f x)
    (hqg : ∀ x, γ * μ / (2 * (2 - γ)) * ‖x - u‖ ^ 2 ≤ f x - f u)
    (s : E × E) :
    γ * μ * ‖s.1 - u‖ ^ 2 ≤ 4 * energy f μ u s ∧
      γ * μ * ‖s.2 - u‖ ^ 2 ≤ 4 * energy f μ u s := by
  have hd : 0 < 2 * (2 - γ) := by linarith
  have hx := mul_le_mul_of_nonneg_left (hqg s.1) hd.le
  have hid : 2 * (2 - γ) * (γ * μ / (2 * (2 - γ)) * ‖s.1 - u‖ ^ 2) =
      γ * μ * ‖s.1 - u‖ ^ 2 := by field_simp [ne_of_gt (show 0 < 2 - γ by linarith)]
  rw [hid] at hx
  have hf := hmin s.1
  have hg := mul_nonneg hγ.le (sub_nonneg.mpr hf)
  have hn : 0 ≤ μ * ‖s.2 - u‖ ^ 2 := by positivity
  have hz := mul_le_mul_of_nonneg_right hγ1 hn
  dsimp [energy]
  constructor <;> nlinarith

omit [CompleteSpace E] in
lemma query_distance {μ γ θ B : ℝ} (hμ : 0 < μ) (hγ : 0 < γ)
    (hθ : 0 ≤ θ) (s : E × E) (u : E)
    (hx : γ * μ * ‖s.1 - u‖ ^ 2 ≤ B)
    (hz : γ * μ * ‖s.2 - u‖ ^ 2 ≤ B) :
    γ * μ * ‖query θ s - u‖ ^ 2 ≤ B := by
  have ht : 0 < 1 + θ := by positivity
  have he : (1 + θ) • (query θ s - u) = (s.1 - u) + θ • (s.2 - u) := by
    dsimp [query]
    rw [smul_sub, smul_smul, mul_one_div_cancel ht.ne', one_smul]
    module
  have hn := congrArg (fun v : E => ‖v‖ ^ 2) he
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow,
    norm_add_sq_real, real_inner_smul_right] at hn
  rw [abs_of_nonneg hθ] at hn
  have hc : 2 * ⟪s.1 - u, s.2 - u⟫ ≤ ‖s.1 - u‖ ^ 2 + ‖s.2 - u‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(s.1 - u) - (s.2 - u)‖,
      norm_sub_sq_real (s.1 - u) (s.2 - u)]
  have hc' := mul_le_mul_of_nonneg_left hc hθ
  have hnorm : (1 + θ) ^ 2 * ‖query θ s - u‖ ^ 2 ≤
      (1 + θ) * (‖s.1 - u‖ ^ 2 + θ * ‖s.2 - u‖ ^ 2) := by nlinarith
  have hnorm' := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ γ * μ by positivity)
  have hbound := mul_le_mul_of_nonneg_left
    (add_le_add hx (mul_le_mul_of_nonneg_left hz hθ)) ht.le
  have hfinal : (1 + θ) ^ 2 * (γ * μ * ‖query θ s - u‖ ^ 2) ≤
      (1 + θ) ^ 2 * B := by nlinarith
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp hfinal

omit [CompleteSpace E] in
lemma similarity_error {n : ℕ} [NeZero n] {g : Fin n × E → E} {G : E → E}
    {δ μ γ : ℝ} (hδ : 0 ≤ δ) (hμ : 0 < μ) (hγ : 0 < γ)
    (hfull : ∀ x, FiniteSum.fullGradient g x = G x)
    (hsim : ∀ i x y, ‖(g (i, x) - G x) - (g (i, y) - G y)‖ ≤ δ * ‖x - y‖)
    (x w u : E) {B C : ℝ}
    (hx : γ * μ * ‖x - u‖ ^ 2 ≤ 4 * B)
    (hw : γ * μ * ‖w - u‖ ^ 2 ≤ 4 * C) :
    γ * μ * ‖FiniteSum.estimator g w x 0 - G x‖ ^ 2 ≤ 8 * δ ^ 2 * (B + C) := by
  have he : FiniteSum.estimator g w x 0 - G x =
      (g (0, x) - G x) - (g (0, w) - G w) := by
    rw [FiniteSum.estimator, hfull]
    abel
  have hs := hsim 0 x w
  rw [← he] at hs
  have hs' := sq_le_sq₀ (norm_nonneg _) (show 0 ≤ δ * ‖x - w‖ by positivity) |>.mpr hs
  rw [mul_pow] at hs'
  have hd := FiniteSum.norm_sub_sq_le (x - u) (w - u)
  have hid : (x - u) - (w - u) = x - w := by abel
  rw [hid] at hd
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ γ * μ by positivity)
  have hds : γ * μ * ‖x - w‖ ^ 2 ≤ 8 * (B + C) := by nlinarith
  have hds' := mul_le_mul_of_nonneg_left hds (sq_nonneg δ)
  have hs'' := mul_le_mul_of_nonneg_left hs' (show 0 ≤ γ * μ by positivity)
  nlinarith

lemma cached_energy_step {n : ℕ} [NeZero n] {f : E → ℝ}
    {g : Fin n × E → E} {G : E → E} {L μ γ θ δ : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hθ : 0 < θ)
    (hrt : γ * θ ≤ 1) (hstep : θ ^ 2 * L ≤ μ) (hδ : 0 ≤ δ)
    (hsmall : 384 * δ ^ 2 ≤ γ ^ 3 * μ ^ 2)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hfull : ∀ x, FiniteSum.fullGradient g x = G x)
    (hsim : ∀ i x y, ‖(g (i, x) - G x) - (g (i, y) - G y)‖ ≤ δ * ‖x - y‖)
    (u : E) (hmin : ∀ x, f u ≤ f x)
    (hcurv : ∀ x y, f x + ⟪G x, y - x⟫ - γ * μ / (2 * θ) * ‖y - x‖ ^ 2 ≤ f y)
    (hquasar : ∀ x, γ * f x + ⟪G x, u - x⟫ + γ * μ / 2 * ‖u - x‖ ^ 2 ≤ γ * f u)
    (hqg : ∀ x, γ * μ / (2 * (2 - γ)) * ‖x - u‖ ^ 2 ≤ f x - f u)
    (s anchor : E × E) :
    energy f μ u (update γ θ μ s (FiniteSum.estimator g anchor.1 (query θ s) 0)) ≤
      (1 - γ * θ / 2) * energy f μ u s +
        (24 * θ * δ ^ 2 / (γ ^ 2 * μ ^ 2)) * energy f μ u anchor := by
  let B := energy f μ u s
  let C := energy f μ u anchor
  let e := FiniteSum.estimator g anchor.1 (query θ s) 0 - G (query θ s)
  have hB : 0 ≤ B := energy_nonneg hμ.le hmin s
  have hC : 0 ≤ C := energy_nonneg hμ.le hmin anchor
  have hd := energy_distances hμ hγ hγ1 hmin hqg s
  have ha := energy_distances hμ hγ hγ1 hmin hqg anchor
  have hy := query_distance hμ hγ hθ.le s u hd.1 hd.2
  have he := similarity_error hδ hμ hγ hfull hsim (query θ s) anchor.1 u hy ha.1
  change γ * μ * ‖e‖ ^ 2 ≤ 8 * δ ^ 2 * (B + C) at he
  have hs := robust_energy_step hμ hγ hθ hrt hstep hg hlip s.1 s.2 u e hmin
    (hcurv (query θ s) s.1) (hquasar (query θ s))
  have hid : G (query θ s) + e = FiniteSum.estimator g anchor.1 (query θ s) 0 := by
    dsimp [e]
    abel
  rw [hid] at hs
  have he' := mul_le_mul_of_nonneg_left he
    (show 0 ≤ 3 * θ / (γ ^ 2 * μ ^ 2) by positivity)
  have hid1 : 3 * θ / (γ ^ 2 * μ ^ 2) * (γ * μ * ‖e‖ ^ 2) =
      3 * θ / (γ * μ) * ‖e‖ ^ 2 := by field_simp
  have hid2 : 3 * θ / (γ ^ 2 * μ ^ 2) * (8 * δ ^ 2 * (B + C)) =
      24 * θ * δ ^ 2 / (γ ^ 2 * μ ^ 2) * (B + C) := by ring
  rw [hid1, hid2] at he'
  have hcoeff : 24 * θ * δ ^ 2 / (γ ^ 2 * μ ^ 2) ≤ γ * θ / 16 := by
    apply (div_le_iff₀ (show 0 < γ ^ 2 * μ ^ 2 by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsmall hθ.le]
  have heB := mul_le_mul_of_nonneg_right hcoeff hB
  change _ ≤ (1 - γ * θ / 2) * B + (24 * θ * δ ^ 2 / (γ ^ 2 * μ ^ 2)) * C
  change _ ≤ (1 - 3 * γ * θ / 4) * B + 3 * θ / (γ * μ) * ‖e‖ ^ 2 at hs
  nlinarith [mul_nonneg (show 0 ≤ γ * θ by positivity) hB]

end OracleTemplate.SimilarQuasar
