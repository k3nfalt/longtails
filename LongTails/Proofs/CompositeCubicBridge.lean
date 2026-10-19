import LongTails.Proofs.CompositeModel
import LongTails.Algorithms.CompositeLazyCubic

namespace LongTails.Proofs.CompositeCubicBridge

open LongTails.Setups.CompositeLipschitzHessian
open LongTails.Proofs.CubicRegularization
open scoped RealInnerProductSpace

lemma residual_norm {p : Params} {g : p.E → p.E} {B : p.E →L[ℝ] p.E}
    {x z : p.E} {H : ℝ} (hH : 0 ≤ H)
    (ht : ‖g z - g x - B (z - x)‖ ≤ H * ‖z - x‖ ^ 2 / 2) :
    ‖g z - g x - B (z - x) - (H * ‖z - x‖) • (z - x)‖ ≤
      3 * H * ‖z - x‖ ^ 2 / 2 := by
  have hn := norm_sub_le (g z - g x - B (z - x)) ((H * ‖z - x‖) • (z - x))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hH (norm_nonneg _))] at hn
  nlinarith only [ht, hn]

lemma residual_subgradient {p : Params} (F : Problem p) {h : p.E → ℝ}
    {g : p.E → p.E} {B : p.E →L[ℝ] p.E} {x z : p.E} {H : ℝ}
    (hs : (⟨x, g x, B, H, 1⟩ : Model p).solution F z)
    (hconv : ∀ u, h z + ⟪g z, u - z⟫ ≤ h u) :
    ∀ u ∈ F.domain, h z + F.ψ z +
      ⟪g z - g x - B (z - x) - (H * ‖z - x‖) • (z - x), u - z⟫ ≤ h u + F.ψ u := by
  intro u hu
  have hv := hs.2 u hu
  simp only [Model.derivative, one_mul, inner_add_left] at hv
  have hc := hconv u
  simp only [inner_sub_left]
  linarith

lemma cubic_descent {p : Params} (F : Problem p) {h : p.E → ℝ}
    {g : p.E} {B : p.E →L[ℝ] p.E} {x z : p.E} {H : ℝ}
    (hx : x ∈ F.domain) (hs : (⟨x, g, B, H, 1⟩ : Model p).solution F z)
    (ht : h z ≤ h x + ⟪g, z - x⟫ + ⟪z - x, B (z - x)⟫ / 2 + H * ‖z - x‖ ^ 3 / 6) :
    ⟪z - x, B (z - x)⟫ / 2 + 5 * H * ‖z - x‖ ^ 3 / 6 ≤
      h x + F.ψ x - (h z + F.ψ z) := by
  have hv := hs.2 x hx
  have he : x - z = -(z - x) := by abel
  simp only [Model.derivative, one_mul, he, inner_add_left, inner_neg_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq] at hv
  have hc : ⟪B (z - x), z - x⟫ = ⟪z - x, B (z - x)⟫ := real_inner_comm _ _
  rw [hc] at hv
  nlinarith only [hv, ht]

lemma first_model_gap {p : Params} (F : Problem p) {h : p.E → ℝ}
    {g : p.E} {B : p.E →L[ℝ] p.E} {x z w : p.E} {H : ℝ}
    (hvalid : (⟨x, g, B, H, 1⟩ : Model p).valid)
    (hs : (⟨x, g, B, H, 1⟩ : Model p).solution F z) (hw : w ∈ F.domain)
    (htz : h z ≤ h x + ⟪g, z - x⟫ + ⟪z - x, B (z - x)⟫ / 2 + H * ‖z - x‖ ^ 3 / 6)
    (htw : h x + ⟪g, w - x⟫ + ⟪w - x, B (w - x)⟫ / 2 ≤ h w + H * ‖w - x‖ ^ 3 / 6) :
    h z + F.ψ z - (h w + F.ψ w) ≤ H * ‖w - x‖ ^ 3 / 2 := by
  have hg := CompositeModel.solution_growth (⟨x, g, B, H, 1⟩ : Model p) F hvalid hs hw
  have hq := hvalid.2.2.2.1 (w - z)
  have hc := mul_nonneg hvalid.2.1 (pow_nonneg (norm_nonneg (w - z)) 3)
  have hc' := mul_nonneg hvalid.2.1 (pow_nonneg (norm_nonneg (z - x)) 3)
  simp only [CompositeModel.smoothValue, cubic, one_mul] at hg
  nlinarith only [hg, hq, hc, hc', htz, htw]

lemma residual_gap_cube {b H d D : ℝ} (hb : 0 ≤ b) (hH : 0 ≤ H) (hd : 0 ≤ d)
    (hr : b ≤ 3 * H * d ^ 2 / 2) (hdescent : 5 * H * d ^ 3 / 6 ≤ D) :
    b ^ 3 ≤ 9 * H * D ^ 2 := by
  have hc := pow_le_pow_left₀ hb hr 3
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 5 * H * d ^ 3 / 6) hdescent 2
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 9 * H)
  have hp : 0 ≤ H ^ 3 * d ^ 6 := by positivity
  nlinarith only [hc, hm, hp]

lemma cubic_gap_from_residual {b γ d D : ℝ} (hb : 0 ≤ b) (hγ : 0 < γ) (hd : 0 ≤ d)
    (hgap : D ≤ b * d - γ * d ^ 3 / 12) :
    D ≤ 2 * b * Real.sqrt (b / γ) := by
  let t := Real.sqrt (b / γ)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : γ * t ^ 2 = b := by
    dsimp [t]
    rw [Real.sq_sqrt (div_nonneg hb hγ.le)]
    field_simp
  have hp := mul_nonneg (sq_nonneg (d - 2 * t)) (by positivity : 0 ≤ d + 4 * t)
  have hm := mul_nonneg hγ.le hp
  have ht3 : 0 ≤ γ * t ^ 3 := by positivity
  change D ≤ 2 * b * t
  rw [← ht2] at hgap ⊢
  nlinarith only [hgap, hm, ht3]

lemma relative_residual_transfer {b γ r R d : ℝ}
    (hb : 0 ≤ b) (hγ : 0 < γ) (hr : 0 ≤ r) (hR : 0 ≤ R) (hd : 0 ≤ d)
    (hsmall : b ≤ γ * R ^ 2 / 128) (hgrowth : γ * d ^ 3 / 12 ≤ b * d)
    (htriangle : R ≤ r + d) : b ≤ γ * r ^ 2 / 32 := by
  have hd2 : d ^ 2 ≤ 12 * b / γ := by
    by_cases hd0 : d = 0
    · simpa [hd0] using (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hb) hγ.le)
    · have hdp : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
      apply (le_div_iff₀ hγ).mpr
      nlinarith only [hgrowth, hdp]
  have hscaled := (le_div_iff₀ hγ).mp hd2
  have hsquare : γ * d ^ 2 ≤ γ * (R ^ 2 / 4) := by
    have hp := mul_nonneg hγ.le (sq_nonneg R)
    nlinarith only [hscaled, hsmall, hp]
  have hcancel := le_of_mul_le_mul_left hsquare hγ
  have hdR : d ≤ R / 2 := by nlinarith only [hcancel, hd, hR]
  have hRr : R ≤ 2 * r := by linarith
  have hs : R ^ 2 ≤ 4 * r ^ 2 := by nlinarith only [hRr, hr, hR]
  have hm := mul_le_mul_of_nonneg_left hs hγ.le
  linarith

lemma regularized_minimizer_exists {p : Params} (F : Problem p) (center : p.E) {γ : ℝ}
    (hγ : 0 < γ) (hf : ConvexOn ℝ Set.univ F.f) (hfc : Continuous F.f)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    {x0 : p.E} (hx0 : x0 ∈ F.domain) :
    ∃ z ∈ F.domain, ∀ u ∈ F.domain,
      F.f z + F.ψ z + γ * cubic (z - center) ≤ F.f u + F.ψ u + γ * cubic (u - center) := by
  let F' : Problem p := ⟨0, fun x => F.f x + F.ψ x, F.domain, F.xstar⟩
  let q : Model p := ⟨center, 0, 0, γ, 1⟩
  have hvalid : q.valid := by
    refine ⟨by norm_num, hγ.le, ?_, ?_, Or.inl hγ⟩
    · intro x y; simp [q]
    · intro x; simp [q]
  have hconv : ConvexOn ℝ F'.domain F'.ψ :=
    (hf.subset (Set.subset_univ _) hψ.1).add hψ
  have hcont : Continuous (fun z : p.E × ℝ => (z.1, z.2 - F.f z.1)) :=
    continuous_fst.prodMk (continuous_snd.sub (hfc.comp continuous_fst))
  have hclose : IsClosed {z : p.E × ℝ | z.1 ∈ F'.domain ∧ F'.ψ z.1 ≤ z.2} := by
    convert hclosed.preimage hcont using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, F']
    constructor <;> rintro ⟨hmem, hv⟩ <;> exact ⟨hmem, by linarith⟩
  obtain ⟨z, hz⟩ := CompositeModel.solution_exists q F' hvalid hconv hclose hx0
  have hm := (CompositeModel.solution_iff_minimizer q F' hvalid hconv z).mp hz
  refine ⟨z, hm.1, fun u hu => ?_⟩
  have h := hm.2 u hu
  simp only [CompositeModel.smoothValue, q, F', inner_zero_left,
    zero_apply, inner_zero_right, zero_div, zero_add, one_mul] at h
  linarith

lemma bridge_small_residual {b γ H κ a Δ R : ℝ}
    (hb : 0 ≤ b) (hγ : 0 < γ) (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hH : H = γ * κ) (hsmall : a * κ ^ 2 ≤ (1 : ℝ) / 16384)
    (hinit : γ * Δ ^ 2 ≤ 9 * H ^ 3 * R ^ 6)
    (hfinal : b ^ 3 ≤ 9 * H * a ^ 2 * Δ ^ 2) :
    b ≤ γ * R ^ 2 / 128 := by
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ a * κ ^ 2) hsmall 2
  have h1 := mul_le_mul_of_nonneg_left hfinal hγ.le
  have h2 := mul_le_mul_of_nonneg_left hinit (by positivity : 0 ≤ 9 * H * a ^ 2)
  have h3 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 81 * γ ^ 4 * R ^ 6)
  have hc : γ * b ^ 3 ≤ γ * (γ * R ^ 2 / 128) ^ 3 := by
    rw [hH] at h1 h2
    nlinarith only [h1, h2, h3, mul_nonneg (pow_nonneg hγ.le 4) (pow_nonneg hR 6)]
  have hpow := le_of_mul_le_mul_left hc hγ
  exact (pow_le_pow_iff_left₀ hb (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp hpow

lemma initial_gap_square {b γ H R : ℝ} (hb : 0 ≤ b) (hγ : 0 < γ)
    (hres : b ^ 3 ≤ (9 : ℝ) / 4 * H ^ 3 * R ^ 6) :
    γ * (2 * b * Real.sqrt (b / γ)) ^ 2 ≤ 9 * H ^ 3 * R ^ 6 := by
  have hs := Real.sq_sqrt (div_nonneg hb hγ.le)
  have he : γ * (2 * b * Real.sqrt (b / γ)) ^ 2 = 4 * b ^ 3 := by
    rw [mul_pow, mul_pow, hs]
    field_simp
    ring
  rw [he]
  linarith

lemma gap_from_strong_subgradient {p : Params} {G : p.E → ℝ} {x w r : p.E} {γ : ℝ}
    (hγ : 0 < γ)
    (hs : G x + ⟪r, w - x⟫ + γ * ‖w - x‖ ^ 3 / 6 ≤ G w) :
    G x - G w ≤ 2 * ‖r‖ * Real.sqrt (‖r‖ / γ) := by
  have hi := real_inner_le_norm r (x - w)
  have he : w - x = -(x - w) := by abel
  rw [he, inner_neg_right, norm_neg] at hs
  apply cubic_gap_from_residual (norm_nonneg r) hγ (norm_nonneg (x - w))
  have hn : 0 ≤ γ * ‖x - w‖ ^ 3 := by positivity
  linarith

lemma distance_from_strong_subgradient {p : Params} {G : p.E → ℝ} {x w r : p.E} {γ : ℝ}
    (hγ : 0 ≤ γ) (hm : G w ≤ G x)
    (hs : G x + ⟪r, w - x⟫ + γ * ‖w - x‖ ^ 3 / 6 ≤ G w) :
    γ * ‖x - w‖ ^ 3 / 12 ≤ ‖r‖ * ‖x - w‖ := by
  have hi := real_inner_le_norm r (x - w)
  have he : w - x = -(x - w) := by abel
  rw [he, inner_neg_right, norm_neg] at hs
  have hn : 0 ≤ γ * ‖x - w‖ ^ 3 := by positivity
  linarith

end LongTails.Proofs.CompositeCubicBridge
