import LongTails.Proofs.ConstrainedAnchoredStep
import LongTails.Proofs.ClippedExtragradientStability

open scoped RealInnerProductSpace

namespace OracleTemplate.ConstrainedMonotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma Proj.energy {X : Set E} {P : E → E} (hP : Proj X P)
    {p : E} (hp : p ∈ X) (x q : E) (γ : ℝ) :
    let z := P (x - γ • q)
    ‖z - p‖ ^ 2 ≤ ‖x - p‖ ^ 2 - ‖x - z‖ ^ 2 - 2 * γ * ⟪q, z - p⟫ := by
  dsimp only
  set z := P (x - γ • q)
  have hv := hP.var (x - γ • q) p hp
  change ⟪x - γ • q - z, p - z⟫ ≤ 0 at hv
  rw [show x - γ • q - z = (x - z) - γ • q by abel,
    show p - z = -(z - p) by abel, inner_neg_right, inner_sub_left,
    real_inner_smul_left] at hv
  have he : ‖x - p‖ ^ 2 = ‖x - z‖ ^ 2 + 2 * ⟪x - z, z - p⟫ + ‖z - p‖ ^ 2 := by
    rw [← norm_add_sq_real, sub_add_sub_cancel]
  linarith

lemma Proj.extragradient_energy {X : Set E} {P : E → E} (hP : Proj X P)
    {p : E} (hp : p ∈ X) (x g q : E) (γ : ℝ) :
    let y := P (x - γ • g)
    let z := P (x - γ • q)
    ‖z - p‖ ^ 2 ≤ ‖x - p‖ ^ 2 - ‖x - y‖ ^ 2 - ‖z - y‖ ^ 2 -
      2 * γ * ⟪q, y - p⟫ + 2 * γ * ⟪g - q, z - y⟫ := by
  dsimp only
  set y := P (x - γ • g)
  set z := P (x - γ • q)
  have hz := hP.energy hp x q γ
  change ‖z - p‖ ^ 2 ≤ ‖x - p‖ ^ 2 - ‖x - z‖ ^ 2 - 2 * γ * ⟪q, z - p⟫ at hz
  have hy := hP.var (x - γ • g) z (hP.mem (x - γ • q))
  change ⟪x - γ • g - y, z - y⟫ ≤ 0 at hy
  rw [show x - γ • g - y = (x - y) - γ • g by abel,
    inner_sub_left, real_inner_smul_left] at hy
  have he : ‖x - z‖ ^ 2 = ‖x - y‖ ^ 2 - 2 * ⟪x - y, z - y⟫ + ‖z - y‖ ^ 2 := by
    rw [← norm_sub_sq_real, sub_sub_sub_cancel_right]
  have hq : ⟪q, z - p⟫ = ⟪q, y - p⟫ + ⟪q, z - y⟫ := by
    rw [← inner_add_right]
    congr 1
    abel
  rw [he, hq] at hz
  rw [inner_sub_left]
  nlinarith

lemma Proj.noisy_displacement {X : Set E} {P : E → E} (hP : Proj X P)
    {p : E} (hp : p ∈ X) (x g e : E) {γ : ℝ} (hγ : 0 ≤ γ) :
    let y := P (x - γ • (g + e))
    γ * ⟪g, x - p⟫ ≤ ‖x - y‖ * ‖x - p‖ - ‖x - y‖ ^ 2 +
      γ * ‖g‖ * ‖x - y‖ + γ * ‖e‖ * (‖x - p‖ + ‖x - y‖) := by
  dsimp only
  set y := P (x - γ • (g + e))
  have hv := hP.var (x - γ • (g + e)) p hp
  change ⟪x - γ • (g + e) - y, p - y⟫ ≤ 0 at hv
  have he : x - γ • (g + e) - y = (x - y) - γ • (g + e) := by abel
  have hpv : p - y = (x - y) - (x - p) := by abel
  rw [he, hpv] at hv
  have ident (u v g e : E) :
      ⟪u - γ • (g + e), u - v⟫ = ‖u‖ ^ 2 - ⟪u, v⟫ -
        γ * (⟪g, u⟫ + ⟪e, u⟫ - ⟪g, v⟫ - ⟪e, v⟫) := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, inner_add_left,
      real_inner_self_eq_norm_sq]
    ring
  rw [ident] at hv
  have h1 := real_inner_le_norm (x - y) (x - p)
  have h2 := mul_le_mul_of_nonneg_left (real_inner_le_norm g (x - y)) hγ
  have h3 := mul_le_mul_of_nonneg_left (real_inner_le_norm e (x - y)) hγ
  have h4 := mul_le_mul_of_nonneg_left (real_inner_le_norm (-e) (x - p)) hγ
  simp only [inner_neg_left, norm_neg] at h4
  nlinarith

lemma Proj.noisy_saturation {X : Set E} {P : E → E} (hP : Proj X P)
    {p x : E} (hp : p ∈ X) (hx : x ∈ X) (g e : E)
    {γ h B a d : ℝ} (hγ : 0 ≤ γ) (hh : 0 ≤ h)
    (hd : ‖x - p‖ ≤ d) (hsat : γ * ‖g + e‖ = a)
    (hcap : γ * B ≤ a / 4)
    (hcoerce : h * ‖g‖ ≤ h * B + ⟪g, x - p⟫) :
    let y := P (x - γ • (g + e))
    3 * h * a / 4 ≤ ‖x - y‖ * (d + a) +
      γ * ‖e‖ * (h + d + 2 * a) := by
  dsimp only
  set y := P (x - γ • (g + e))
  have hD : ‖x - y‖ ≤ a := by
    have hv := hP.dist_le (x - γ • (g + e)) hx
    rw [show x - γ • (g + e) - x = -(γ • (g + e)) by abel,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ, hsat] at hv
    exact (norm_sub_rev x y).trans_le hv
  have hn1 : a ≤ γ * ‖g‖ + γ * ‖e‖ := by
    have := mul_le_mul_of_nonneg_left (norm_add_le g e) hγ
    nlinarith
  have hn2 : γ * ‖g‖ ≤ a + γ * ‖e‖ := by
    have ht : ‖g‖ ≤ ‖g + e‖ + ‖e‖ := by
      simpa using norm_sub_le (g + e) e
    have := mul_le_mul_of_nonneg_left ht hγ
    nlinarith
  have hv := hP.noisy_displacement hp x g e hγ
  change γ * ⟪g, x - p⟫ ≤ ‖x - y‖ * ‖x - p‖ - ‖x - y‖ ^ 2 +
    γ * ‖g‖ * ‖x - y‖ + γ * ‖e‖ * (‖x - p‖ + ‖x - y‖) at hv
  have he0 : 0 ≤ γ * ‖e‖ := mul_nonneg hγ (norm_nonneg _)
  have h1 := mul_le_mul_of_nonneg_left hn1 hh
  have h2 := mul_le_mul_of_nonneg_right hn2 (norm_nonneg (x - y))
  have h3 := mul_le_mul_of_nonneg_left hcoerce hγ
  have h4 := mul_le_mul_of_nonneg_left hcap hh
  have h5 := mul_le_mul_of_nonneg_left hd (norm_nonneg (x - y))
  have h6 := mul_le_mul_of_nonneg_left hd he0
  have h7 := mul_le_mul_of_nonneg_left hD he0
  nlinarith [sq_nonneg ‖x - y‖]

omit [InnerProductSpace ℝ E] in
lemma projected_local_error {A b γ : ℝ} (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (H : E → E) (x y g : E) (hA : γ * A ≤ 1 / 16)
    (hg : γ * b * ‖g‖ ≤ 1 / 16) (hd : b * ‖x - y‖ ≤ 1 / 16)
    (hl : ‖H y - H x‖ ≤ 2 * (A + b * ‖H x‖) * ‖x - y‖) :
    γ * ‖H y - g‖ ≤ ‖x - y‖ / 4 + 9 / 8 * γ * ‖g - H x‖ := by
  have hn : ‖H x‖ ≤ ‖g‖ + ‖g - H x‖ := by
    simpa [norm_sub_rev] using norm_sub_le g (g - H x)
  have ht : ‖H y - g‖ ≤ ‖H y - H x‖ + ‖g - H x‖ := by
    simpa [norm_sub_rev] using norm_add_le (H y - H x) (H x - g)
  have hl' : ‖H y - g‖ ≤
      2 * (A + b * (‖g‖ + ‖g - H x‖)) * ‖x - y‖ + ‖g - H x‖ := by
    apply ht.trans
    gcongr
    exact hl.trans (by gcongr)
  have hmain := mul_le_mul_of_nonneg_left hl' hγ
  have h1 := mul_le_mul_of_nonneg_right hA (norm_nonneg (x - y))
  have h2 := mul_le_mul_of_nonneg_right hg (norm_nonneg (x - y))
  have h3 := mul_le_mul_of_nonneg_right hd (mul_nonneg hγ (norm_nonneg (g - H x)))
  nlinarith

lemma Proj.noisy_extragradient_energy {X : Set E} {P : E → E} (hP : Proj X P)
    {p : E} (hp : p ∈ X) (H : E → E) (x g e : E) {γ μ : ℝ} (hγ : 0 ≤ γ)
    (hm : let y := P (x - γ • g); μ * ‖y - p‖ ^ 2 ≤ ⟪H y, y - p⟫)
    (hl : let y := P (x - γ • g);
      γ ^ 2 * ‖g - H y‖ ^ 2 ≤ ‖x - y‖ ^ 2 / 8 + 81 / 32 * γ ^ 2 * ‖g - H x‖ ^ 2) :
    let y := P (x - γ • g)
    let z := P (x - γ • (H y + e))
    ‖z - p‖ ^ 2 ≤ ‖x - p‖ ^ 2 - ‖x - y‖ ^ 2 / 2 -
      2 * μ * γ * ‖y - p‖ ^ 2 + 81 / 8 * γ ^ 2 * ‖g - H x‖ ^ 2 +
      4 * γ ^ 2 * ‖e‖ ^ 2 - 2 * γ * ⟪e, y - p⟫ := by
  dsimp only at hm hl ⊢
  set y := P (x - γ • g)
  change μ * ‖y - p‖ ^ 2 ≤ ⟪H y, y - p⟫ at hm
  change γ ^ 2 * ‖g - H y‖ ^ 2 ≤ ‖x - y‖ ^ 2 / 8 +
    81 / 32 * γ ^ 2 * ‖g - H x‖ ^ 2 at hl
  set z := P (x - γ • (H y + e))
  have hv := hP.extragradient_energy hp x g (H y + e) γ
  change ‖z - p‖ ^ 2 ≤ ‖x - p‖ ^ 2 - ‖x - y‖ ^ 2 - ‖z - y‖ ^ 2 -
    2 * γ * ⟪H y + e, y - p⟫ + 2 * γ * ⟪g - (H y + e), z - y⟫ at hv
  rw [inner_add_left] at hv
  have hn : ‖g - (H y + e)‖ ≤ ‖g - H y‖ + ‖e‖ := by
    simpa [sub_add_eq_sub_sub] using norm_sub_le (g - H y) e
  have hn2 : ‖g - (H y + e)‖ ^ 2 ≤ 2 * ‖g - H y‖ ^ 2 + 2 * ‖e‖ ^ 2 := by
    nlinarith [sq_nonneg (‖g - H y‖ - ‖e‖), norm_nonneg (g - (H y + e)),
      norm_nonneg (g - H y), norm_nonneg e]
  have hi := mul_le_mul_of_nonneg_left (real_inner_le_norm (g - (H y + e)) (z - y)) hγ
  have hyoung := sq_nonneg (‖z - y‖ - 2 * γ * ‖g - (H y + e)‖)
  have hnoise := mul_le_mul_of_nonneg_left hn2 (sq_nonneg γ)
  have hmono := mul_le_mul_of_nonneg_left hm hγ
  nlinarith [sq_nonneg ‖z - y‖]

lemma saturation_square {h a d D t : ℝ} (hh : 0 ≤ h) (ha : 0 ≤ a)
    (hd : 0 < d + a) (hhd : h ≤ d) (ht : 0 ≤ t)
    (hs : 3 * h * a / 4 ≤ D * (d + a) + t * (h + d + 2 * a)) :
    (3 * h * a / (4 * (d + a))) ^ 2 / 4 ≤ D ^ 2 / 2 + 2 * t ^ 2 := by
  have h1 : t * (h + d + 2 * a) ≤ 2 * t * (d + a) := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hhd)]
  have hc : 0 ≤ 3 * h * a / (4 * (d + a)) := by positivity
  have hcD : 3 * h * a / (4 * (d + a)) ≤ D + 2 * t := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hs2 := pow_le_pow_left₀ hc hcD 2
  nlinarith [sq_nonneg (D - 2 * t)]

lemma Proj.saturated_drift {X : Set E} {P : E → E} (hP : Proj X P)
    {p x : E} (hp : p ∈ X) (hx : x ∈ X) (g e : E)
    {γ h B a d κ : ℝ} (hγ : 0 ≤ γ) (hh : 0 ≤ h) (hhd : h ≤ d)
    (hda : 0 < d + a) (hκ : 0 ≤ κ) (hd : ‖x - p‖ ≤ d)
    (hsat : γ * ‖g + e‖ = a) (hcap : γ * B ≤ a / 4)
    (hcoerce : h * ‖g‖ ≤ h * B + ⟪g, x - p⟫)
    (hscale : κ * d ^ 2 ≤ (3 * h * a / (4 * (d + a))) ^ 2 / 4) :
    let y := P (x - γ • (g + e))
    κ * ‖x - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 / 2 + 2 * γ ^ 2 * ‖e‖ ^ 2 := by
  dsimp only
  have ha : 0 ≤ a := hsat ▸ mul_nonneg hγ (norm_nonneg (g + e))
  have hs := hP.noisy_saturation hp hx g e hγ hh hd hsat hcap hcoerce
  have hsq := saturation_square hh ha hda hhd (mul_nonneg hγ (norm_nonneg e)) hs
  have hn := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd 2) hκ
  nlinarith

lemma regularized_coercivity {F : E → E} {L0 L1 μ h d : ℝ}
    (hF : GeneralizedMonotone.Hyp F L0 L1) {X : Set E} {p x : E} (c : E)
    (hx : x ∈ X) (hp : Normal X p (-(F p + μ • (p - c))))
    (hμ : 0 ≤ μ) (hh : 0 < h) (hcap : L1 * h ≤ 1 / 2) (hd : ‖x - p‖ ≤ d) :
    h * ‖F x + μ • (x - c)‖ ≤
      h * (‖F p‖ + μ * (‖p - c‖ + d) + 2 * (L0 + L1 * ‖F p‖) * (d + h)) +
        ⟪F x + μ • (x - c), x - p⟫ := by
  have ho := one_point hF x p hh hcap
  have hpv := hp x hx
  rw [inner_neg_left] at hpv
  have he : F x - F p = (F x + μ • (x - c)) - (F p + μ • (p - c)) - μ • (x - p) := by
    module
  have hi : ⟪F x - F p, x - p⟫ ≤ ⟪F x + μ • (x - c), x - p⟫ := by
    rw [he, inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith [mul_nonneg hμ (sq_nonneg ‖x - p‖)]
  have hn : ‖F x‖ ≤ ‖F x - F p‖ + ‖F p‖ := by
    simpa using norm_add_le (F x - F p) (F p)
  have hxc : ‖x - c‖ ≤ d + ‖p - c‖ := by
    have := norm_add_le (x - p) (p - c)
    rw [sub_add_sub_cancel] at this
    linarith
  have ht := norm_add_le (F x) (μ • (x - c))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ] at ht
  have hnorm : ‖F x + μ • (x - c)‖ ≤ ‖F x - F p‖ + ‖F p‖ + μ * (d + ‖p - c‖) := by
    have := mul_le_mul_of_nonneg_left hxc hμ
    linarith
  have hhN := mul_le_mul_of_nonneg_left hnorm hh.le
  have hL : 0 ≤ 2 * (L0 + L1 * ‖F p‖) * h := by
    have := hF.L0_pos
    have := hF.L1_nonneg
    positivity
  have hdist := mul_le_mul_of_nonneg_left hd hL
  nlinarith

lemma Proj.clipped_drift {X : Set E} {P : E → E} (hP : Proj X P)
    {p x : E} (hp : p ∈ X) (hx : x ∈ X) (g e : E)
    {b S μ h B d : ℝ} (hb : 0 ≤ b) (hS : 0 < S) (hμ : 0 ≤ μ)
    (hμS : μ ≤ S) (hh : 0 < h) (hhd : h ≤ d) (hd : ‖x - p‖ ≤ d)
    (hB : 4 * b * B ≤ S) (hscale : μ * d ^ 2 * (1 + 16 * b * d) ^ 2 ≤ S * h ^ 2)
    (hcoerce : h * ‖g‖ ≤ h * B + ⟪g, x - p⟫) :
    let γ := ClippedExtragradient.stepSize b S (g + e)
    let y := P (x - γ • (g + e))
    μ / (16 * S) * ‖x - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 / 2 +
      2 * μ * γ * ‖y - p‖ ^ 2 + 2 * γ ^ 2 * ‖e‖ ^ 2 := by
  dsimp only
  let γ := ClippedExtragradient.stepSize b S (g + e)
  let y := P (x - γ • (g + e))
  have hγ : 0 < γ := ClippedExtragradient.stepSize_pos hS (g + e)
  have hd0 : 0 < d := hh.trans_le hhd
  by_cases hs : b * ‖g + e‖ ≤ S
  · have heq : γ = 1 / (16 * S) := by
      dsimp [γ, ClippedExtragradient.stepSize]
      rw [max_eq_left hs]
    have hcap : γ * μ ≤ 1 / 4 := by
      rw [heq]
      rw [show 1 / (16 * S) * μ = μ / (16 * S) by ring,
        div_le_iff₀ (by positivity : 0 < 16 * S)]
      nlinarith
    have ht := ClippedExtragradient.small_step_drift hγ.le hμ hcap x p (x - y)
    rw [show x - (x - y) - p = y - p by abel] at ht
    have heq' : γ * μ = μ / (16 * S) := by rw [heq]; ring
    rw [heq'] at ht
    change μ / (16 * S) * ‖x - p‖ ^ 2 ≤ _
    nlinarith [mul_nonneg (sq_nonneg γ) (sq_nonneg ‖e‖)]
  · have hb' : 0 < b := by
      by_contra hn
      have : b = 0 := le_antisymm (le_of_not_gt hn) hb
      simp [this, hS.le] at hs
    let a := 1 / (16 * b)
    have ha : 0 < a := by dsimp [a]; positivity
    have hn : 0 < ‖g + e‖ := by
      by_contra hn
      have hz := le_antisymm (le_of_not_gt hn) (norm_nonneg (g + e))
      simp [hz, hS.le] at hs
    have hsat : γ * ‖g + e‖ = a := by
      dsimp [γ, a, ClippedExtragradient.stepSize]
      rw [max_eq_right (le_of_not_ge hs)]
      field_simp
    have hcap : γ * B ≤ a / 4 := by
      have hgS := ClippedExtragradient.stepSize_le (b := b) hS (g + e)
      change γ ≤ 1 / (16 * S) at hgS
      by_cases hB0 : 0 ≤ B
      · have hmul := mul_le_mul_of_nonneg_right hgS hB0
        dsimp [a]
        rw [div_div, le_div_iff₀ (by positivity : 0 < 16 * b * 4)]
        have hgS' := (le_div_iff₀ (by positivity : 0 < 16 * S)).mp hgS
        nlinarith [mul_le_mul_of_nonneg_left hB hγ.le]
      · exact (mul_nonpos_of_nonneg_of_nonpos hγ.le (le_of_not_ge hB0)).trans (by positivity)
    have hden : 0 < 1 + 16 * b * d := by positivity
    have hfrac : 3 * h * a / (4 * (d + a)) = 3 * h / (4 * (1 + 16 * b * d)) := by
      dsimp [a]
      field_simp
      ring
    have hscale' : μ / (16 * S) * d ^ 2 ≤ (3 * h * a / (4 * (d + a))) ^ 2 / 4 := by
      rw [hfrac]
      field_simp
      nlinarith [mul_nonneg hS.le (sq_nonneg h)]
    have ht := hP.saturated_drift hp hx g e hγ.le hh.le hhd (by positivity : 0 < d + a)
      (by positivity : 0 ≤ μ / (16 * S)) hd hsat hcap hcoerce hscale'
    change μ / (16 * S) * ‖x - p‖ ^ 2 ≤ _
    nlinarith [mul_nonneg (mul_nonneg hμ hγ.le) (sq_nonneg ‖y - p‖)]

lemma Proj.clipped_one_step {X : Set E} {P : E → E} (hP : Proj X P)
    {p x : E} (hp : p ∈ X) (hx : x ∈ X) (H : E → E) (g e : E)
    {A b S μ h B d : ℝ} (hb : 0 ≤ b) (hS : 0 < S) (hμ : 0 ≤ μ)
    (hμS : μ ≤ S) (hAS : A ≤ S) (hh : 0 < h) (hhd : h ≤ d) (hd : ‖x - p‖ ≤ d)
    (hB : 4 * b * B ≤ S) (hscale : μ * d ^ 2 * (1 + 16 * b * d) ^ 2 ≤ S * h ^ 2)
    (hcoerce : h * ‖H x‖ ≤ h * B + ⟪H x, x - p⟫)
    (hm : let γ := ClippedExtragradient.stepSize b S g; let y := P (x - γ • g);
      μ * ‖y - p‖ ^ 2 ≤ ⟪H y, y - p⟫)
    (hl : let γ := ClippedExtragradient.stepSize b S g; let y := P (x - γ • g);
      ‖H y - H x‖ ≤ 2 * (A + b * ‖H x‖) * ‖x - y‖) :
    let γ := ClippedExtragradient.stepSize b S g
    let y := P (x - γ • g)
    let z := P (x - γ • (H y + e))
    ‖z - p‖ ^ 2 ≤ (1 - μ / (16 * S)) * ‖x - p‖ ^ 2 +
      97 / 8 * γ ^ 2 * ‖g - H x‖ ^ 2 + 4 * γ ^ 2 * ‖e‖ ^ 2 -
        2 * γ * ⟪e, y - p⟫ := by
  dsimp only at hm hl ⊢
  let γ := ClippedExtragradient.stepSize b S g
  let y := P (x - γ • g)
  have hγ : 0 < γ := ClippedExtragradient.stepSize_pos hS g
  have hγS : γ * S ≤ 1 / 16 := by
    have ht := ClippedExtragradient.stepSize_le (b := b) hS g
    change γ ≤ 1 / (16 * S) at ht
    have := (le_div_iff₀ (by positivity : 0 < 16 * S)).mp ht
    nlinarith
  have hγA : γ * A ≤ 1 / 16 := (mul_le_mul_of_nonneg_left hAS hγ.le).trans hγS
  have hg : γ * b * ‖g‖ ≤ 1 / 16 := by
    have hmax : γ * max S (b * ‖g‖) = 1 / 16 := by
      dsimp [γ, ClippedExtragradient.stepSize]
      have : 0 < max S (b * ‖g‖) := hS.trans_le (le_max_left _ _)
      field_simp
    have := mul_le_mul_of_nonneg_left (le_max_right S (b * ‖g‖)) hγ.le
    nlinarith
  have hD : ‖x - y‖ ≤ γ * ‖g‖ := by
    have ht := hP.dist_le (x - γ • g) hx
    rw [show x - γ • g - x = -(γ • g) by abel, norm_neg,
      norm_smul, Real.norm_eq_abs, abs_of_pos hγ] at ht
    exact (norm_sub_rev x y).trans_le ht
  have hbD : b * ‖x - y‖ ≤ 1 / 16 := by
    have := mul_le_mul_of_nonneg_left hD hb
    nlinarith
  have hloc := projected_local_error hb hγ.le H x y g hγA hg hbD hl
  have hloc2 : γ ^ 2 * ‖g - H y‖ ^ 2 ≤ ‖x - y‖ ^ 2 / 8 +
      81 / 32 * γ ^ 2 * ‖g - H x‖ ^ 2 := by
    rw [norm_sub_rev g (H y)]
    have hs := pow_le_pow_left₀ (by positivity) hloc 2
    nlinarith [sq_nonneg (‖x - y‖ / 4 - 9 / 8 * γ * ‖g - H x‖)]
  have henergy := hP.noisy_extragradient_energy hp H x g e hγ.le hm hloc2
  have hdrift := hP.clipped_drift hp hx (H x) (g - H x) hb hS hμ hμS hh hhd hd hB hscale hcoerce
  rw [add_sub_cancel] at hdrift
  change μ / (16 * S) * ‖x - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 / 2 +
    2 * μ * γ * ‖y - p‖ ^ 2 + 2 * γ ^ 2 * ‖g - H x‖ ^ 2 at hdrift
  nlinarith

end OracleTemplate.ConstrainedMonotone
