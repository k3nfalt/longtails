import LongTails.Proofs.ComponentEnvelopeInner
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set Metric InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.ComponentEnvelope

open LongTails.Proofs.RecursiveEnvelopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma exists_regularized_minimum [ProperSpace E] {f : E → ℝ}
    (hf : Continuous f) {μ : ℝ} (hμ : 0 < μ) {u : E}
    (hmin : ∀ x, f u ≤ f x) (c : E) :
    ∃ p, ∀ y, regularized f μ c p ≤ regularized f μ c y := by
  set t := (f c - f u) / μ
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr (hmin c)) hμ.le
  have htm : μ * t = f c - f u := by dsimp [t]; field_simp
  set r := 1 + 2 * t
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hcont : Continuous (regularized f μ c) := by
    unfold regularized
    fun_prop
  obtain ⟨p, hp, hpm⟩ := (isCompact_closedBall c r).exists_isMinOn
    (nonempty_closedBall.mpr hr) hcont.continuousOn
  refine ⟨p, fun y => ?_⟩
  by_cases hy : y ∈ closedBall c r
  · exact hpm hy
  · have hd : r < ‖y - c‖ := by simpa [mem_closedBall, dist_eq_norm] using hy
    have hs : 2 * t ≤ ‖y - c‖ ^ 2 := by
      have hh : (1 + 2 * t) ^ 2 ≤ ‖y - c‖ ^ 2 := by
        apply pow_le_pow_left₀ hr hd.le
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hs hμ.le
    have hc := hpm (show c ∈ closedBall c r by simpa using hr)
    have hl := hmin y
    change regularized f μ c p ≤ regularized f μ c c at hc
    simp only [regularized, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero] at hc
    dsimp [regularized]
    linarith

lemma regularized_minimum_stationary {f : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt f (g x) x) (μ : ℝ) (c p : E)
    (hmin : ∀ y, regularized f μ c p ≤ regularized f μ c y) :
    g p + μ • (p - c) = 0 := by
  set r := g p + μ • (p - c)
  have hl : HasDerivAt (fun t : ℝ => p + t • r) r 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const r |>.const_add p
  have hf := (hg (p + (0 : ℝ) • r)).hasFDerivAt.comp_hasDerivAt 0
    (show HasDerivAt (fun t : ℝ => p + t • r) r 0 from hl)
  have hq := ((hl.sub_const c).norm_sq).const_mul (μ / 2)
  have hd := hf.add hq
  have hm : IsLocalMin (fun t : ℝ => regularized f μ c (p + t • r)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa using hmin (p + t • r)
  have hz := hm.hasDerivAt_eq_zero hd
  simp only [zero_smul, add_zero, toDual_apply_apply] at hz
  have he : ‖r‖ ^ 2 = ⟪g p, r⟫ + μ * ⟪p - c, r⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => lhs; unfold r
    rw [inner_add_left, real_inner_smul_left]
  have hn : ‖r‖ = 0 := by nlinarith [norm_nonneg r]
  exact norm_eq_zero.mp hn

lemma component_prox_stationary [ProperSpace E] {f : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt f (g x) x) {μ : ℝ} (hμ : 0 < μ) {u : E}
    (hmin : ∀ x, f u ≤ f x) (c : E) :
    g (prox g μ c) + μ • (prox g μ c - c) = 0 := by
  unfold prox
  apply Classical.epsilon_spec (p := fun x => g x + μ • (x - c) = 0)
  obtain ⟨p, hp⟩ := exists_regularized_minimum
    (continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt) hμ hmin c
  exact ⟨p, regularized_minimum_stationary hg μ c p hp⟩

lemma component_prox_field [ProperSpace E] {f : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt f (g x) x) {μ : ℝ} (hμ : 0 < μ) {u : E}
    (hmin : ∀ x, f u ≤ f x) (c : E) :
    g (prox g μ c) = μ • (c - prox g μ c) := by
  have hs := component_prox_stationary hg hμ hmin c
  have he : μ • (c - prox g μ c) = -(μ • (prox g μ c - c)) := by module
  rw [he]
  exact eq_neg_of_add_eq_zero_left hs

lemma component_prox_minimum [ProperSpace E] {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    {μ : ℝ} (hμ : 0 < μ) {u : E} (hmin : ∀ x, f u ≤ f x) (c y : E) :
    envelope f g μ c + μ / 2 * ‖y - prox g μ c‖ ^ 2 ≤ regularized f μ c y := by
  have hs := regularized_support hc hg μ c (prox g μ c) y
  rw [component_prox_stationary hg hμ hmin c, inner_zero_left, add_zero] at hs
  exact hs

lemma component_envelope_model [ProperSpace E] {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    {μ : ℝ} (hμ : 0 < μ) {u : E} (hmin : ∀ x, f u ≤ f x) :
    Model μ (envelope f g μ) (envelopeField g μ) := by
  have hfield : ∀ x, g (prox g μ x) = envelopeField g μ x :=
    fun x => component_prox_field hg hμ hmin x
  refine ⟨hμ, ?_, ?_⟩
  · intro x y
    have hs := Gradient.convex_support hc hg (prox g μ x) (prox g μ y)
    rw [hfield x] at hs
    have he := envelope_support_identity f μ x y (prox g μ x) (prox g μ y)
    change envelope f g μ y - envelope f g μ x -
      ⟪envelopeField g μ x, y - x⟫ = _ at he
    have hn : 0 ≤ μ / 2 * ‖(prox g μ y - prox g μ x) - (y - x)‖ ^ 2 := by positivity
    change ⟪μ • (x - prox g μ x), prox g μ y - prox g μ x⟫ ≤ _ at hs
    linarith
  · intro x y
    have hs := component_prox_minimum hc hg hμ hmin y (prox g μ x)
    have hn : 0 ≤ μ / 2 * ‖prox g μ x - prox g μ y‖ ^ 2 := by positivity
    have he := envelope_support_identity f μ x y (prox g μ x) (prox g μ x)
    simp only [sub_self, inner_zero_right, zero_sub, norm_neg, zero_add] at he
    change regularized f μ y (prox g μ x) - envelope f g μ x -
      ⟪envelopeField g μ x, y - x⟫ = μ / 2 * ‖y - x‖ ^ 2 at he
    linarith


omit [CompleteSpace E] in
lemma component_displacement_gap {f : E → ℝ} {g : E → E}
    {μ : ℝ} {u : E} (hmin : ∀ x, f u ≤ f x) (c : E) :
    μ / 2 * ‖c - prox g μ c‖ ^ 2 ≤ envelope f g μ c - f u := by
  have hm := hmin (prox g μ c)
  unfold envelope regularized
  rw [norm_sub_rev (prox g μ c) c]
  linarith

lemma component_gap_transfer [ProperSpace E] {f : E → ℝ} {g : E → E} {L0 L1 μ : ℝ}
    (h0 : 0 ≤ L0) (h1 : 0 ≤ L1) (hμ : 0 < μ) (h0μ : L0 ≤ μ)
    (hg : ∀ x, HasGradientAt f (g x) x) (hcont : Continuous g)
    (hs : CompositeGeneralized.SymmetricSmooth g L0 L1) {u : E}
    (hmin : ∀ x, f u ≤ f x) (c : E)
    (hr : L1 * ‖c - prox g μ c‖ ≤ 1 / 2) :
    f c - f u ≤ 5 * (envelope f g μ c - f u) := by
  set p := prox g μ c
  have hu := CompositeGeneralized.ball_upper h0 h1 hg hcont hs
    (x := p) (u := p) (v := c) hr (by simp) le_rfl
  have hf := component_prox_field hg hμ hmin c
  change g p = μ • (c - p) at hf
  rw [hf, real_inner_smul_left, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, abs_of_pos hμ] at hu
  have hb : μ / 2 + L0 + L1 * (μ * ‖c - p‖) ≤ 2 * μ := by
    nlinarith [mul_le_mul_of_nonneg_left hr hμ.le]
  have ht := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖c - p‖)
  have hd := component_displacement_gap hmin (g := g) (μ := μ) c
  have he : envelope f g μ c = f p + μ / 2 * ‖c - p‖ ^ 2 := by
    simp only [envelope, regularized, p, norm_sub_rev]
  change μ / 2 * ‖c - p‖ ^ 2 ≤ _ at hd
  nlinarith


lemma component_residual_error [ProperSpace E] {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    {μ : ℝ} (hμ : 0 < μ) {u : E} (hmin : ∀ x, f u ≤ f x) (c z : E) :
    ‖μ • (c - z) - envelopeField g μ c‖ ≤ ‖g z + μ • (z - c)‖ := by
  set p := prox g μ c
  set r := g z + μ • (z - c)
  have hzp := regularized_support hc hg μ c z p
  have hpz := regularized_support hc hg μ c p z
  have hstat := component_prox_stationary hg hμ hmin c
  change g p + μ • (p - c) = 0 at hstat
  rw [hstat, inner_zero_left, add_zero] at hpz
  have he : ⟪r, p - z⟫ = -⟪r, z - p⟫ := by rw [← inner_neg_right, neg_sub]
  change regularized f μ c z + ⟪r, p - z⟫ + μ / 2 * ‖p - z‖ ^ 2 ≤ _ at hzp
  rw [he, norm_sub_rev p z] at hzp
  have hi := real_inner_le_norm r (z - p)
  have hs : μ * ‖z - p‖ ≤ ‖r‖ := by
    by_cases hz : ‖z - p‖ = 0
    · rw [hz, mul_zero]; exact norm_nonneg r
    · have hpos : 0 < ‖z - p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      apply (mul_le_mul_iff_left₀ hpos).mp
      nlinarith
  have hv : μ • (c - z) - envelopeField g μ c = -μ • (z - p) := by
    unfold envelopeField
    dsimp [p]
    module
  rw [hv, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hμ]
  exact hs

lemma component_prox_distance [ProperSpace E] {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    {μ : ℝ} (hμ : 0 < μ) {u : E} (hmin : ∀ x, f u ≤ f x) (c : E) :
    ‖c - prox g μ c‖ ≤ ‖c - u‖ := by
  set p := prox g μ c
  have hs := Gradient.convex_support hc hg p u
  have hf := component_prox_field hg hμ hmin c
  change g p = μ • (c - p) at hf
  rw [hf, real_inner_smul_left] at hs
  have hm := hmin p
  have hi : 0 ≤ ⟪c - p, p - u⟫ := by
    have he : ⟪c - p, u - p⟫ = -⟪c - p, p - u⟫ := by
      rw [← inner_neg_right, neg_sub]
    rw [he] at hs
    have hh : 0 ≤ μ * ⟪c - p, p - u⟫ := by linarith
    exact nonneg_of_mul_nonneg_right hh hμ
  have he : c - u = (c - p) + (p - u) := by module
  have hn : ‖c - p‖ ^ 2 ≤ ‖c - u‖ ^ 2 := by
    rw [he, norm_add_sq_real]
    nlinarith [sq_nonneg ‖p - u‖]
  nlinarith [norm_nonneg (c - p), norm_nonneg (c - u)]


lemma component_local_residual [ProperSpace E] {f : E → ℝ} {g : E → E}
    {L0 L1 μ : ℝ} (h0 : 0 ≤ L0) (h1 : 0 ≤ L1) (hμ : 0 < μ)
    (hg : ∀ x, HasGradientAt f (g x) x) (hcont : Continuous g)
    (hs : CompositeGeneralized.SymmetricSmooth g L0 L1) {u : E}
    (hmin : ∀ x, f u ≤ f x) (c z : E)
    (hr : L1 * ‖z - prox g μ c‖ ≤ 1 / 2) :
    ‖g z + μ • (z - c)‖ ≤
      2 * (L0 + μ + 2 * μ * L1 * ‖c - prox g μ c‖) * ‖z - prox g μ c‖ := by
  set p := prox g μ c
  have hb := CompositeGeneralized.ball_lipschitz h0 h1 hcont hs
    (x := p) (u := z) (v := p) hr le_rfl (by simp)
  have hf := component_prox_field hg hμ hmin c
  change g p = μ • (c - p) at hf
  have he : g z + μ • (z - c) = (g z - g p) + μ • (z - p) := by
    rw [hf]
    module
  rw [hf, norm_smul, Real.norm_eq_abs, abs_of_pos hμ] at hb
  rw [← hf] at hb
  rw [he]
  have hn := norm_add_le (g z - g p) (μ • (z - p))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ] at hn
  have hq : 0 ≤ μ * L1 * ‖c - p‖ := by positivity
  have hd := norm_nonneg (z - p)
  nlinarith [mul_nonneg hq hd, mul_nonneg hμ.le hd]


lemma component_prox_at_minimum [ProperSpace E] {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    {μ : ℝ} (hμ : 0 < μ) {u : E} (hmin : ∀ x, f u ≤ f x) : prox g μ u = u := by
  have hd := component_prox_distance hc hg hμ hmin u
  simp only [sub_self, norm_zero] at hd
  have hz := norm_eq_zero.mp (le_antisymm hd (norm_nonneg _))
  exact (sub_eq_zero.mp hz).symm

lemma component_envelope_at_minimum [ProperSpace E] {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    {μ : ℝ} (hμ : 0 < μ) {u : E} (hmin : ∀ x, f u ≤ f x) :
    envelope f g μ u = f u ∧ envelopeField g μ u = 0 := by
  have hp := component_prox_at_minimum hc hg hμ hmin
  simp [envelope, envelopeField, regularized, hp]

lemma component_envelope_gap_nonneg [ProperSpace E] {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    {μ : ℝ} (hμ : 0 < μ) {u : E} (hmin : ∀ x, f u ≤ f x) (x : E) :
    0 ≤ envelope f g μ x - envelope f g μ u := by
  have hmodel := component_envelope_model hc hg hμ hmin
  have hh := hmodel.lower u x
  rw [(component_envelope_at_minimum hc hg hμ hmin).2, inner_zero_left, add_zero] at hh
  exact sub_nonneg.mpr hh


end OracleTemplate.ComponentEnvelope
