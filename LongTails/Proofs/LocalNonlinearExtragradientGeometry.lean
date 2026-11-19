import LongTails.Proofs.ClippedExtragradientStability
import LongTails.Proofs.CachedJacobianGeometry

open scoped RealInnerProductSpace
open Filter

namespace LongTails.Proofs.LocalNonlinearExtragradientGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma exact_step_contraction (x p g q : E) {η μ : ℝ}
    (hη : 0 ≤ η) (hμ : 0 ≤ μ) (hcap : η * μ ≤ 1 / 4)
    (hlocal : η ^ 2 * ‖q - g‖ ^ 2 ≤ 1 / 2 * ‖η • g‖ ^ 2)
    (hmono : μ * ‖x - η • g - p‖ ^ 2 ≤ ⟪q, x - η • g - p⟫) :
    ‖x - η • q - p‖ ^ 2 ≤ (1 - η * μ) * ‖x - p‖ ^ 2 := by
  have he := OracleTemplate.ClippedExtragradient.extragradient_identity x p g q 0 η
  simp only [add_zero, inner_zero_left, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero] at he
  have hd := OracleTemplate.ClippedExtragradient.small_step_drift hη hμ hcap x p (η • g)
  have hm := mul_le_mul_of_nonneg_left hmono (show 0 ≤ 2 * η by positivity)
  nlinarith

lemma lipschitz_step_contraction (F : E → E) (x p : E) {L μ : ℝ}
    (hL : 0 < L) (hμ : 0 ≤ μ) (hμL : μ ≤ L)
    (hlip : ∀ a b, ‖F a - F b‖ ≤ L * ‖a - b‖)
    (hmono : ∀ a, μ * ‖a - p‖ ^ 2 ≤ ⟪F a, a - p⟫) :
    ‖x - (1 / (4 * L)) • F (x - (1 / (4 * L)) • F x) - p‖ ^ 2 ≤
      (1 - μ / (4 * L)) * ‖x - p‖ ^ 2 := by
  let η : ℝ := 1 / (4 * L)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hηL : η * L = 1 / 4 := by dsimp [η]; field_simp
  have hcap : η * μ ≤ 1 / 4 := by nlinarith [mul_le_mul_of_nonneg_left hμL hη]
  have hn := hlip (x - η • F x) x
  have he : x - η • F x - x = -(η • F x) := by abel
  rw [he, norm_neg] at hn
  have hs : ‖F (x - η • F x) - F x‖ ^ 2 ≤ (L * ‖η • F x‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg η)
  have hi : η ^ 2 * (L * ‖η • F x‖) ^ 2 = (1 / 16 : ℝ) * ‖η • F x‖ ^ 2 := by
    calc
      _ = (η * L) ^ 2 * ‖η • F x‖ ^ 2 := by ring
      _ = _ := by rw [hηL]; ring
  rw [hi] at hh
  have hz := exact_step_contraction x p (F x) (F (x - η • F x)) hη hμ hcap
    (by nlinarith [sq_nonneg ‖η • F x‖]) (hmono (x - η • F x))
  convert hz using 1
  dsimp [η]
  ring

lemma clipping_bias_bound (v : E) {H : ℝ} (hH : 0 < H) :
    ‖v - OracleTemplate.clip H v‖ ≤ ‖v‖ ^ 2 / H := by
  rw [OracleTemplate.clip_residual_norm hH.le]
  apply max_le
  · positivity
  · apply (le_div_iff₀ hH).mpr
    nlinarith [sq_nonneg (‖v‖ - H), mul_nonneg hH.le (norm_nonneg v)]

lemma derivative_norm_bound (F : E → E) (A : E →L[ℝ] E) (p : E) {L : ℝ}
    (hL : 0 ≤ L) (hd : HasFDerivAt F A p)
    (hlip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) : ‖A‖ ≤ L :=
  hd.le_of_lip' hL (Filter.Eventually.of_forall fun x => hlip x p)

lemma derivative_strong_monotonicity (F : E → E) (A : E →L[ℝ] E) (p v : E) (μ : ℝ)
    (hd : HasFDerivAt F A p)
    (hm : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫) :
    μ * ‖v‖ ^ 2 ≤ ⟪A v, v⟫ := by
  let G : E → E := fun x => F x - μ • x
  have hg : HasFDerivAt G (A - μ • ContinuousLinearMap.id ℝ E) p :=
    hd.sub ((hasFDerivAt_id p).const_smul μ)
  have hgm : ∀ x ∈ (Set.univ : Set E), ∀ y ∈ (Set.univ : Set E),
      0 ≤ ⟪G x - G y, x - y⟫ := by
    intro x _ y _
    have he : G x - G y = (F x - F y) - μ • (x - y) := by dsimp [G]; module
    rw [he, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact sub_nonneg.mpr (hm x y)
  have h := CachedJacobianGeometry.derivative_monotone_on_differences
    (s := p) (x := v) (y := 0) convex_univ (Set.mem_univ _) (Set.mem_univ _)
    (Set.mem_univ _) hg.differentiableAt hgm
  rw [hg.fderiv] at h
  simp only [sub_zero, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at h
  linarith

lemma root_derivative_coercivity (F : E → E) (A : E →L[ℝ] E) (p v : E) (μ : ℝ)
    (hd : HasFDerivAt F A p) (hp : F p = 0)
    (hm : ∀ x, μ * ‖x - p‖ ^ 2 ≤ ⟪F x, x - p⟫) :
    μ * ‖v‖ ^ 2 ≤ ⟪A v, v⟫ := by
  let g : ℝ → ℝ := fun t => ⟪F (p + t • v), v⟫
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hF : HasDerivAt (fun t : ℝ => F (p + t • v)) (A v) 0 := by
    have hd' : HasFDerivAt F A (p + (0 : ℝ) • v) := by simpa using hd
    simpa only [Function.comp_def] using hd'.comp_hasDerivAt 0 hline
  have hg : HasDerivAt g ⟪A v, v⟫ 0 := by
    simpa [g] using hF.inner ℝ (hasDerivAt_const (0 : ℝ) v)
  apply ge_of_tendsto hg.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have hh := hm (p + t • v)
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0,
    mul_pow, real_inner_smul_right] at hh
  have hs : μ * ‖v‖ ^ 2 * t ≤ g t := by
    apply (mul_le_mul_iff_left₀ ht0).mp
    dsimp [g]
    nlinarith only [hh]
  simpa only [zero_add, g, zero_smul, add_zero, hp, inner_zero_left, sub_zero,
    smul_eq_mul, ← div_eq_inv_mul] using (le_div_iff₀ ht0).mpr hs

lemma mean_perturbation_bound (A : E →L[ℝ] E) (u v : E) {L M ρ V : ℝ}
    (hL : 0 < L) (hM : 0 ≤ M) (hρ : 1 ≤ ρ) (hV : 0 ≤ V)
    (hA : ‖A‖ ≤ L) (hu : ‖u‖ ≤ M / 2 * V)
    (hv : ‖v‖ ≤ M / 2 * ((1 + ρ / 16) * V)) :
    ‖(1 / (4 * L)) ^ 2 • A u - (1 / (4 * L)) • v‖ ≤
      ρ * M / (4 * L) * V := by
  have hau : ‖A u‖ ≤ L * (M / 2 * V) :=
    (A.le_opNorm u).trans (mul_le_mul hA hu (norm_nonneg _) hL.le)
  have hη : 0 ≤ (1 / (4 * L) : ℝ) := by positivity
  have hn := norm_sub_le ((1 / (4 * L)) ^ 2 • A u) ((1 / (4 * L)) • v)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη,
    abs_of_nonneg (sq_nonneg (1 / (4 * L)))] at hn
  have h₁ := mul_le_mul_of_nonneg_left hau (sq_nonneg (1 / (4 * L)))
  have h₂ := mul_le_mul_of_nonneg_left hv hη
  have he : (1 / (4 * L)) ^ 2 * (L * (M / 2 * V)) +
      (1 / (4 * L)) * (M / 2 * ((1 + ρ / 16) * V)) =
      (20 + ρ) * (M * V / (128 * L)) := by field_simp; ring
  have hb : ‖(1 / (4 * L)) ^ 2 • A u - (1 / (4 * L)) • v‖ ≤
      (20 + ρ) * (M * V / (128 * L)) := by nlinarith
  have hc := mul_le_mul_of_nonneg_right (show 20 + ρ ≤ 32 * ρ by linarith)
    (show 0 ≤ M * V / (128 * L) by positivity)
  have hf : 32 * ρ * (M * V / (128 * L)) = ρ * M / (4 * L) * V := by ring
  exact hb.trans (hf ▸ hc)

omit [InnerProductSpace ℝ E] in
lemma norm_from_squared_contraction (x y : E) {a : ℝ}
    (ha1 : a ≤ 1) (h : ‖y‖ ^ 2 ≤ (1 - a) * ‖x‖ ^ 2) :
    ‖y‖ ≤ (1 - a / 2) * ‖x‖ := by
  have hq : 0 ≤ 1 - a / 2 := by linarith
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq (norm_nonneg _))).mp
  nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg ‖x‖)]

lemma linear_extragradient_norm (A : E →L[ℝ] E) (x : E) {L μ : ℝ}
    (hL : 0 < L) (hμ : 0 ≤ μ) (hμL : μ ≤ L) (hA : ‖A‖ ≤ L)
    (hm : ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪A v, v⟫) :
    ‖x - (1 / (4 * L)) • A x + (1 / (4 * L)) ^ 2 • A (A x)‖ ≤
      (1 - μ / (8 * L)) * ‖x‖ := by
  have hlip : ∀ a b, ‖A a - A b‖ ≤ L * ‖a - b‖ := by
    intro a b
    rw [← map_sub]
    exact (A.le_opNorm (a - b)).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hs := lipschitz_step_contraction (fun z => A z) x 0 hL hμ hμL hlip
    (by simpa only [sub_zero] using hm)
  simp only [sub_zero] at hs
  have ha1 : μ / (4 * L) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hn := norm_from_squared_contraction x _ ha1 hs
  have he : x - (1 / (4 * L)) • A (x - (1 / (4 * L)) • A x) =
      x - (1 / (4 * L)) • A x + (1 / (4 * L)) ^ 2 • A (A x) := by
    simp only [map_sub, map_smul, smul_sub, smul_smul]
    module
  rw [he] at hn
  convert hn using 1
  ring

end LongTails.Proofs.LocalNonlinearExtragradientGeometry
