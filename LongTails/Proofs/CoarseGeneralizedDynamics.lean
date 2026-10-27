import LongTails.Algorithms.CoarseGeneralizedWarmstart
import LongTails.Proofs.CoarseGeneralizedEnergy
import LongTails.Proofs.CoarseGeneralizedGeometry

open scoped RealInnerProductSpace

namespace OracleTemplate.CoarseGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma weight_spec (t : Tuning) (s : Iterate E) (h : E)
    (hL : 0 < t.L) (hL1 : 0 ≤ t.L1) (hh : 0 < ‖h‖)
    (hP : 0 ≤ surplus t h) (hA : 0 ≤ s.A) :
    0 < weight t s.A h ∧
      (weight t s.A h) ^ 2 * ‖h‖ ^ 2 =
        (s.A + weight t s.A h) * decrement t h / 128 + weight t s.A h * surplus t h / 2 := by
  have hD : 0 < decrement t h := by unfold decrement; positivity
  exact quadratic_weight_identity (sq_pos_of_pos hh) hD hP hA

lemma advance_energy [CompleteSpace E] (t : Tuning) (s : Iterate E)
    {f : E → ℝ} {g : E → E} {u y h : E}
    (hL : 0 < t.L) (hL1 : 0 ≤ t.L1) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ t.L + t.L1 * ‖g x‖)
    (hh : 0 < ‖h‖) (hA : 0 ≤ s.A) (hP : 0 ≤ surplus t h)
    (he : ‖h - g y‖ ≤ t.ζ) (hnoise : t.ζ ≤ ‖h‖ / 4)
    (hsearch : f y ≤ f s.x + decrement t h / 256)
    (halign : ⟪h, y - s.v⟫ ≤ decrement t h / 256)
    (hsupport : f y - f u + surplus t h ≤ ⟪h, y - u⟫) :
    (advance t s y h).A * (f (advance t s y h).x - f u) +
      1 / 2 * ‖(advance t s y h).v - u‖ ^ 2 +
      1 / 2 * (weight t s.A h) ^ 2 * ‖h‖ ^ 2 ≤
        s.A * (f s.x - f u) + 1 / 2 * ‖s.v - u‖ ^ 2 := by
  have hw := weight_spec t s h hL hL1 hh hP hA
  have hD : 0 ≤ decrement t h := by unfold decrement; positivity
  have hd := normalized_noisy_descent hL hL1 hf hg hH he hnoise
  exact coarse_energy_step hA hw.1.le hD hsearch halign hsupport hd hw.2

lemma advance_radius (t : Tuning) (s : Iterate E) {u y h : E}
    (hL : 0 < t.L) (hL1 : 0 ≤ t.L1)
    (hsupport : surplus t h ≤ ⟪h, y - u⟫)
    (hP : decrement t h / 32 ≤ surplus t h) :
    ‖(advance t s y h).x - u‖ ^ 2 ≤ ‖y - u‖ ^ 2 := by
  apply coarse_step_distance (P := surplus t h) (by positivity) hsupport
  have heq : 1 / (16 * (t.L + t.L1 * ‖h‖)) * ‖h‖ ^ 2 = decrement t h / 16 := by
    unfold decrement
    field_simp
  change 1 / (16 * (t.L + t.L1 * ‖h‖)) * ‖h‖ ^ 2 ≤ 2 * surplus t h
  rw [heq]
  linarith

omit [InnerProductSpace ℝ E] in
lemma surplus_dominates_decrement (t : Tuning) (h : E)
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hlarge : 32 * t.L ≤ t.L1 * ‖h‖) :
    decrement t h / 32 ≤ surplus t h := by
  have hs : 0 < ‖h‖ := by nlinarith
  have hden : 0 < t.L + t.L1 * ‖h‖ := by positivity
  have hr : 16 ≤ t.L1 * ‖h‖ / (2 * t.L) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have hl : 2 ≤ Real.log (t.L1 * ‖h‖ / (2 * t.L)) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have h16 : (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hr
    rw [h16, Real.log_pow] at hm
    norm_num at hh hm
    linarith
  have hD : decrement t h ≤ ‖h‖ / t.L1 := by
    unfold decrement
    apply (div_le_div_iff₀ hden hL1).mpr
    nlinarith [mul_nonneg hL.le hs.le]
  have hP : ‖h‖ / (32 * t.L1) ≤ surplus t h := by
    unfold surplus
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_left hl (mul_nonneg hs.le hL1.le)
    nlinarith
  have heq : ‖h‖ / (32 * t.L1) = (‖h‖ / t.L1) / 32 := by ring
  rw [heq] at hP
  linarith

omit [InnerProductSpace ℝ E] in
lemma high_reply_noise (t : Tuning) (h : E) {R : ℝ}
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hζ : 0 ≤ t.ζ) (hR : 1 ≤ t.L1 * R)
    (hinflate : t.L1 ^ 2 * R * t.ζ ≤ t.L)
    (hlarge : 4096 * t.L / t.L1 < ‖h‖) :
    t.ζ ≤ ‖h‖ / 4 ∧ R * t.ζ ≤ decrement t h / 1024 := by
  have hs : 0 < ‖h‖ := (div_pos (by positivity) hL1).trans hlarge
  have hhigh : 4096 * t.L < ‖h‖ * t.L1 := (div_lt_iff₀ hL1).mp hlarge
  have hbase : t.L ≤ t.L1 * ‖h‖ := by nlinarith
  have hn : 4096 * t.L1 * R * t.ζ ≤ ‖h‖ := by
    have hm := mul_le_mul_of_nonneg_left hinflate (by norm_num : (0 : ℝ) ≤ 4096)
    apply (mul_le_mul_iff_right₀ hL1).mp
    nlinarith only [hm, hhigh.le]
  have hζs : 4096 * t.ζ ≤ ‖h‖ := by
    have hh := mul_le_mul_of_nonneg_right hR hζ
    nlinarith only [hn, hh]
  have hD : ‖h‖ / (2 * t.L1) ≤ decrement t h := by
    unfold decrement
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hbase hs.le
    nlinarith only [hm]
  have hnoiseD : 2048 * (R * t.ζ) ≤ ‖h‖ / (2 * t.L1) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hn]
  have hRn : 0 ≤ R * t.ζ := mul_nonneg (by nlinarith) hζ
  constructor
  · linarith
  · linarith

lemma low_reply_gap [CompleteSpace E] (t : Tuning) {f : E → ℝ} {g : E → E}
    {R : ℝ} {u y h : E} (hc : ConvexOn ℝ Set.univ f)
    (hf : ∀ x, HasGradientAt f (g x) x)
    (hL1 : 0 < t.L1) (hζ : 0 ≤ t.ζ) (hR : 1 ≤ t.L1 * R)
    (hinflate : t.L1 ^ 2 * R * t.ζ ≤ t.L)
    (hy : ‖y - u‖ ≤ R) (he : ‖h - g y‖ ≤ t.ζ)
    (hsmall : ‖h‖ ≤ 4096 * t.L / t.L1) :
    f y - f u ≤ 4097 * R * t.L / t.L1 := by
  have hRp : 0 < R := by nlinarith
  have hζL : t.ζ ≤ t.L / t.L1 := by
    apply (le_div_iff₀ hL1).mpr
    have hm := mul_le_mul_of_nonneg_right hR (mul_nonneg hL1.le hζ)
    nlinarith only [hm, hinflate]
  have hs := Gradient.convex_support hc hf y u
  have hi : ⟪g y, u - y⟫ = -⟪g y, y - u⟫ := by
    rw [← inner_neg_right]
    congr 1
    abel
  rw [hi] at hs
  have hn := norm_le_norm_sub_add (g y) h
  rw [norm_sub_rev (g y) h] at hn
  have hg : ‖g y‖ ≤ 4097 * t.L / t.L1 := by
    have heq : 4097 * t.L / t.L1 = 4096 * t.L / t.L1 + t.L / t.L1 := by ring
    rw [heq]
    linarith
  have hm := mul_le_mul hg hy (norm_nonneg (y - u))
    ((norm_nonneg (g y)).trans hg)
  have hh := real_inner_le_norm (g y) (y - u)
  have heq : 4097 * t.L / t.L1 * R = 4097 * R * t.L / t.L1 := by ring
  rw [heq] at hm
  linarith

omit [InnerProductSpace ℝ E] in
lemma normalized_weight_identity (t : Tuning) (s : Iterate E) (h : E)
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hh : 0 < ‖h‖)
    (hP : 0 ≤ surplus t h) (hA : 0 ≤ s.A) :
    let b := t.L1 * weight t s.A h * ‖h‖
    let u := t.L1 * ‖h‖ / t.L
    let w := t.L * (s.A + weight t s.A h)
    b ^ 2 = w * u ^ 2 / (128 * (1 + u)) + b * Real.log (u / 2) / 128 := by
  have hw := (weight_spec t s h hL hL1.le hh hP hA).2
  have hden : t.L + t.L1 * ‖h‖ ≠ 0 := ne_of_gt (by positivity)
  dsimp only
  have hlog : Real.log (t.L1 * ‖h‖ / t.L / 2) = Real.log (t.L1 * ‖h‖ / (2 * t.L)) := by
    congr 1
    ring
  rw [hlog]
  calc
    _ = t.L1 ^ 2 * ((weight t s.A h) ^ 2 * ‖h‖ ^ 2) := by ring
    _ = _ := by
      rw [hw]
      unfold decrement surplus
      field_simp
      ring

omit [InnerProductSpace ℝ E] in
lemma bracket_error_absorption (t : Tuning) (h : E) {R ρ : ℝ}
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hρ : 0 ≤ ρ)
    (hlarge : t.L ≤ t.L1 * ‖h‖)
    (hdepth : 65536 * (t.L1 * R) ^ 2 * ρ ≤ 1) :
    16 * R ^ 2 * (t.L + t.L1 * ‖h‖) * ρ ≤ decrement t h / 1024 := by
  have hden : 0 < t.L + t.L1 * ‖h‖ := by positivity
  have hd : t.L + t.L1 * ‖h‖ ≤ 2 * t.L1 * ‖h‖ := by linarith
  have hsq := pow_le_pow_left₀ hden.le hd 2
  have hm := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 16384 * R ^ 2 * ρ by positivity)
  have ht := mul_le_mul_of_nonneg_right hdepth (sq_nonneg ‖h‖)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1024)).mpr
  unfold decrement
  apply (le_div_iff₀ hden).mpr
  nlinarith only [hm, ht]

lemma high_reply_support [CompleteSpace E] (t : Tuning) {f : E → ℝ} {g : E → E}
    {R : ℝ} {u y h : E} (hL : 0 < t.L) (hL1 : 0 < t.L1) (hζ : 0 ≤ t.ζ)
    (hR : 1 ≤ t.L1 * R) (hinflate : t.L1 ^ 2 * R * t.ζ ≤ t.L)
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : Differentiable ℝ g) (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ t.L + t.L1 * ‖g x‖)
    (hu : g u = 0) (hy : ‖y - u‖ ≤ R) (he : ‖h - g y‖ ≤ t.ζ)
    (hlarge : 4096 * t.L / t.L1 < ‖h‖) :
    f y - f u + surplus t h ≤ ⟪h, y - u⟫ := by
  have hn := high_reply_noise t h hL hL1 hζ hR hinflate hlarge
  have hh := (div_lt_iff₀ hL1).mp hlarge
  have hP := surplus_dominates_decrement t h hL hL1 (by nlinarith)
  have hD : 0 ≤ decrement t h := by unfold decrement; positivity
  apply noisy_anchored_surplus hL hL1 hc hf hg hH hu hy hζ he
  · linarith [norm_nonneg h]
  · apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  · change t.ζ * R ≤ surplus t h
    nlinarith only [hn.2, hP, hD]

lemma uncertain_search_slack [CompleteSpace E] (t : Tuning) {f : E → ℝ} {g : E → E}
    {R θ : ℝ} {u x v y h : E} (hL : 0 < t.L) (hL1 : 0 < t.L1) (hζ : 0 ≤ t.ζ)
    (hR : 1 ≤ t.L1 * R) (hinflate : t.L1 ^ 2 * R * t.ζ ≤ t.L)
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (g x) x)
    (hx : ‖x - u‖ ≤ R) (hv : ‖v - u‖ ≤ R)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hy : y = v + θ • (x - v))
    (he : ‖h - g y‖ ≤ t.ζ) (hdir : |⟪h, x - v⟫| ≤ t.ζ * ‖x - v‖)
    (hlarge : 4096 * t.L / t.L1 < ‖h‖) :
    f y ≤ f x + decrement t h / 256 ∧ ⟪h, y - v⟫ ≤ decrement t h / 256 := by
  have hn := (high_reply_noise t h hL hL1 hζ hR hinflate hlarge).2
  have hd := radius_pair_distance hx hv
  have hm := mul_le_mul_of_nonneg_left hd hζ
  have hb := uncertain_direction_bounds hc hf hθ hθ1 hζ hy he hdir
  have hD : 0 ≤ decrement t h := by unfold decrement; positivity
  constructor <;> nlinarith only [hb.1, hb.2, hn, hm, hD]

lemma bracket_search_slack [CompleteSpace E] (t : Tuning) {f : E → ℝ} {g : E → E}
    {R θ ρ : ℝ} {u x v y z h : E} (hL : 0 < t.L) (hL1 : 0 < t.L1) (hζ : 0 ≤ t.ζ)
    (hR : 1 ≤ t.L1 * R) (hinflate : t.L1 ^ 2 * R * t.ζ ≤ t.L)
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : Differentiable ℝ g) (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ t.L + t.L1 * ‖g x‖)
    (hx : ‖x - u‖ ≤ R) (hv : ‖v - u‖ ≤ R)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hy : y = v + θ • (x - v))
    (he : ‖h - g y‖ ≤ t.ζ) (hleft : ⟪g z, x - v⟫ ≤ 0) (hright : 0 ≤ ⟪g y, x - v⟫)
    (hlarge : 4096 * t.L / t.L1 < ‖h‖) (hρ : 0 ≤ ρ)
    (hdist : ‖z - y‖ ≤ 2 * R * ρ) (hshort : 8 * (t.L1 * R) * ρ ≤ 1)
    (hdepth : 65536 * (t.L1 * R) ^ 2 * ρ ≤ 1) :
    f y ≤ f x + decrement t h / 256 ∧ ⟪h, y - v⟫ ≤ decrement t h / 256 := by
  have hn := high_reply_noise t h hL hL1 hζ hR hinflate hlarge
  have hRp : 0 ≤ R := (norm_nonneg (x - u)).trans hx
  have hden : 0 < t.L + t.L1 * ‖h‖ := by positivity
  have hloc : t.L1 * ‖z - y‖ ≤ 1 / 4 := by
    have hm := mul_le_mul_of_nonneg_left hdist hL1.le
    nlinarith only [hm, hshort]
  have hgrad := bracket_gradient_difference hL.le hL1.le hg hH he
    (show t.ζ ≤ ‖h‖ by linarith [norm_nonneg h]) hloc
  have hb := bracket_endpoint_bounds hc hf hθ hθ1 hζ
    (show 0 ≤ 4 * (t.L + t.L1 * ‖h‖) * ‖z - y‖ by positivity) hy he hleft hright hgrad
  have hd := radius_pair_distance hx hv
  have hcoef : 4 * (t.L + t.L1 * ‖h‖) * ‖z - y‖ + t.ζ ≤
      8 * (t.L + t.L1 * ‖h‖) * R * ρ + t.ζ := by
    have hm := mul_le_mul_of_nonneg_left hdist (show 0 ≤ 4 * (t.L + t.L1 * ‖h‖) by positivity)
    nlinarith only [hm]
  have hm := mul_le_mul hcoef hd (norm_nonneg (x - v))
    (show 0 ≤ 8 * (t.L + t.L1 * ‖h‖) * R * ρ + t.ζ by positivity)
  have hh := (div_lt_iff₀ hL1).mp hlarge
  have hgeom := bracket_error_absorption t h hL hL1 hρ (by nlinarith) hdepth
  have hD : 0 ≤ decrement t h := by unfold decrement; positivity
  constructor
  · linarith [hb.1]
  · nlinarith only [hb.2, hm, hgeom, hn.2, hD]

lemma reliable_direction {g h d : E} {ζ : ℝ} (he : ‖h - g‖ ≤ ζ)
    (ha : ζ * ‖d‖ < |⟪h, d⟫|) :
    (0 ≤ ⟪h, d⟫ → 0 ≤ ⟪g, d⟫) ∧ (⟪h, d⟫ ≤ 0 → ⟪g, d⟫ ≤ 0) := by
  have hb := abs_le.mp (direction_error (d := d) he)
  constructor
  · intro hh
    rw [abs_of_nonneg hh] at ha
    linarith
  · intro hh
    rw [abs_of_nonpos hh] at ha
    linarith

lemma endpoint_search_slack [CompleteSpace E] (t : Tuning) {f : E → ℝ} {g : E → E}
    {x v h : E} (hL : 0 < t.L) (hL1 : 0 ≤ t.L1)
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (g x) x) :
    (0 ≤ ⟪g v, x - v⟫ →
      f v ≤ f x + decrement t h / 256 ∧ ⟪h, v - v⟫ ≤ decrement t h / 256) ∧
    (⟪h, x - v⟫ ≤ 0 →
      f x ≤ f x + decrement t h / 256 ∧ ⟪h, x - v⟫ ≤ decrement t h / 256) := by
  have hD : 0 ≤ decrement t h := by unfold decrement; positivity
  constructor
  · intro hh
    have hs := Gradient.convex_support hc hf v x
    constructor
    · linarith
    · simp only [sub_self, inner_zero_right]
      positivity
  · intro hh
    constructor <;> linarith

lemma high_advance_radius [CompleteSpace E] (t : Tuning) (s : Iterate E)
    {f : E → ℝ} {g : E → E} {R : ℝ} {u y h : E}
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hζ : 0 ≤ t.ζ)
    (hR : 1 ≤ t.L1 * R) (hinflate : t.L1 ^ 2 * R * t.ζ ≤ t.L)
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : Differentiable ℝ g) (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ t.L + t.L1 * ‖g x‖)
    (hu : g u = 0) (hmin : ∀ x, f u ≤ f x)
    (hy : ‖y - u‖ ≤ R) (he : ‖h - g y‖ ≤ t.ζ)
    (hlarge : 4096 * t.L / t.L1 < ‖h‖) :
    ‖(advance t s y h).x - u‖ ≤ R := by
  have hs := high_reply_support t hL hL1 hζ hR hinflate hc hf hg hH hu hy he hlarge
  have hh := (div_lt_iff₀ hL1).mp hlarge
  have hp := surplus_dominates_decrement t h hL hL1 (by nlinarith)
  have ha := advance_radius t s hL hL1.le (by linarith [hmin y]) hp
  have hb := pow_le_pow_left₀ (norm_nonneg _) hy 2
  nlinarith only [ha, hb, norm_nonneg ((advance t s y h).x - u),
    (norm_nonneg (y - u)).trans hy]

end OracleTemplate.CoarseGeneralized
