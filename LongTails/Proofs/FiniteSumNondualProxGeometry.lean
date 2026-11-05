import LongTails.Proofs.RecursiveEnvelopeGeometry
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Compact

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.FiniteSumNondualProxGeometry

open RecursiveEnvelopeGeometry Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def regularized (f : E → ℝ) (μ : ℝ) (c x : E) : ℝ :=
  f x + μ / 2 * ‖x - c‖ ^ 2

noncomputable def regularizedGradient (g : E → E) (μ : ℝ) (c x : E) : E :=
  g x + μ • (x - c)

def Normal (C : Set E) (x v : E) : Prop := ∀ u ∈ C, ⟪v, u - x⟫ ≤ 0

lemma shifted_square (c x y : E) :
    ‖y - c‖ ^ 2 = ‖x - c‖ ^ 2 + 2 * ⟪x - c, y - x⟫ + ‖y - x‖ ^ 2 := by
  have he : y - c = (x - c) + (y - x) := by module
  rw [he, norm_add_sq_real]

lemma regularized_lower {f : E → ℝ} {g : E → E} {L μ : ℝ}
    (hf : Model L f g) (c x y : E) :
    regularized f μ c x + ⟪regularizedGradient g μ c x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤
      regularized f μ c y := by
  have h := hf.lower x y
  unfold regularized regularizedGradient
  rw [inner_add_left, real_inner_smul_left, shifted_square c x y]
  nlinarith

lemma regularized_model {f : E → ℝ} {g : E → E} {L μ : ℝ}
    (hf : Model L f g) (hμ : 0 ≤ μ) (c : E) :
    Model (L + μ) (regularized f μ c) (regularizedGradient g μ c) := by
  refine ⟨by linarith [hf.pos], ?_, ?_⟩
  · intro x y
    have h := regularized_lower (μ := μ) hf c x y
    have hn : 0 ≤ μ / 2 * ‖y - x‖ ^ 2 := by positivity
    linarith
  · intro x y
    have h := hf.upper x y
    unfold regularized regularizedGradient
    rw [inner_add_left, real_inner_smul_left, shifted_square c x y]
    nlinarith

lemma minimizer_variational {C : Set E} (hC : Convex ℝ C) {f : E → ℝ} {g : E → E} {L : ℝ}
    (hf : Model L f g) {x : E} (hx : x ∈ C) (hmin : IsMinOn f C x) (u : E) (hu : u ∈ C) :
    0 ≤ ⟪g x, u - x⟫ := by
  by_contra hn
  have hi : ⟪g x, u - x⟫ < 0 := lt_of_not_ge hn
  let D := L * ‖u - x‖ ^ 2 + 1
  have hD : 0 < D := by dsimp [D]; positivity [hf.pos]
  let t := min (1 / 2 : ℝ) (-⟪g x, u - x⟫ / D)
  have ht : 0 < t := lt_min (by norm_num) (div_pos (neg_pos.mpr hi) hD)
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have htd : t * D ≤ -⟪g x, u - x⟫ :=
    (le_div_iff₀ hD).mp (min_le_right _ _)
  have hmem : x + t • (u - x) ∈ C := by
    have h := hC hx hu (sub_nonneg.mpr ht1) ht.le (by ring : (1 - t) + t = 1)
    convert h using 1
    module
  have hm := hmin hmem
  change f x ≤ f (x + t • (u - x)) at hm
  have hs := hf.upper x (x + t • (u - x))
  simp only [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht] at hs
  have hmul := mul_le_mul_of_nonneg_left htd ht.le
  dsimp [D] at hmul
  nlinarith [sq_pos_of_pos ht]

lemma residual_lower {C : Set E} {f : E → ℝ} {g : E → E} {L μ : ℝ}
    (hf : Model L f g) (c w v u : E) (hv : Normal C w v) (hu : u ∈ C) :
    regularized f μ c w + ⟪regularizedGradient g μ c w + v, u - w⟫ +
      μ / 2 * ‖u - w‖ ^ 2 ≤ regularized f μ c u := by
  have h := regularized_lower (μ := μ) hf c w u
  have hn := hv u hu
  rw [inner_add_left]
  linarith

lemma exact_prox_lower {C : Set E} (hC : Convex ℝ C) {f : E → ℝ} {g : E → E} {L μ : ℝ}
    (hf : Model L f g) (hμ : 0 ≤ μ) (c p : E) (hp : p ∈ C)
    (hmin : IsMinOn (regularized f μ c) C p) (u : E) (hu : u ∈ C) :
    regularized f μ c p + μ / 2 * ‖u - p‖ ^ 2 ≤ regularized f μ c u := by
  have h := regularized_lower (μ := μ) hf c p u
  have hn := minimizer_variational hC (regularized_model hf hμ c) hp hmin u hu
  linarith

lemma residual_distance {C : Set E} (hC : Convex ℝ C) {f : E → ℝ} {g : E → E} {L μ ρ : ℝ}
    (hf : Model L f g) (hμ : 0 < μ) (c p w v : E) (hp : p ∈ C) (hw : w ∈ C)
    (hmin : IsMinOn (regularized f μ c) C p) (hv : Normal C w v)
    (hr : ‖regularizedGradient g μ c w + v‖ ≤ ρ) : ‖w - p‖ ≤ ρ / μ := by
  have hlo := exact_prox_lower hC hf hμ.le c p hp hmin w hw
  have hup := residual_lower (μ := μ) hf c w v p hv hp
  rw [norm_sub_rev p w] at hup
  have he : ⟪regularizedGradient g μ c w + v, p - w⟫ =
      -⟪regularizedGradient g μ c w + v, w - p⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [he] at hup
  have hi := (real_inner_le_norm (regularizedGradient g μ c w + v) (w - p)).trans
    (mul_le_mul_of_nonneg_right hr (norm_nonneg _))
  have hh : μ * ‖w - p‖ ^ 2 ≤ ρ * ‖w - p‖ := by linarith
  apply (le_div_iff₀ hμ).mpr
  by_cases hz : ‖w - p‖ = 0
  · rw [hz, zero_mul]
    exact (norm_nonneg _).trans hr
  · have hd : 0 < ‖w - p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have h := (mul_le_mul_iff_left₀ hd).mp
      (show (μ * ‖w - p‖) * ‖w - p‖ ≤ ρ * ‖w - p‖ by nlinarith only [hh])
    nlinarith only [h]

lemma residual_value_error {C : Set E} {f : E → ℝ} {g : E → E} {L μ ρ : ℝ}
    (hf : Model L f g) (hμ : 0 < μ) (c p w v : E) (hp : p ∈ C)
    (hv : Normal C w v) (hr : ‖regularizedGradient g μ c w + v‖ ≤ ρ) :
    regularized f μ c w - regularized f μ c p ≤ ρ ^ 2 / (2 * μ) := by
  have h := residual_lower (μ := μ) hf c w v p hv hp
  rw [norm_sub_rev p w] at h
  have he : ⟪regularizedGradient g μ c w + v, p - w⟫ =
      -⟪regularizedGradient g μ c w + v, w - p⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [he] at h
  have hi := (real_inner_le_norm (regularizedGradient g μ c w + v) (w - p)).trans
    (mul_le_mul_of_nonneg_right hr (norm_nonneg _))
  apply (le_div_iff₀ (by positivity : 0 < 2 * μ)).mpr
  have hh := mul_le_mul_of_nonneg_left (show regularized f μ c w - regularized f μ c p ≤
    ρ * ‖w - p‖ - μ / 2 * ‖w - p‖ ^ 2 by linarith) hμ.le
  nlinarith [sq_nonneg (μ * ‖w - p‖ - ρ)]

lemma residual_envelope_gradient_error {C : Set E} (hC : Convex ℝ C)
    {f : E → ℝ} {g : E → E} {L μ ρ : ℝ}
    (hf : Model L f g) (hμ : 0 < μ) (c p w v : E) (hp : p ∈ C) (hw : w ∈ C)
    (hmin : IsMinOn (regularized f μ c) C p) (hv : Normal C w v)
    (hr : ‖regularizedGradient g μ c w + v‖ ≤ ρ) :
    ‖μ • (c - w) - μ • (c - p)‖ ≤ ρ := by
  have h := residual_distance hC hf hμ c p w v hp hw hmin hv hr
  have he : μ • (c - w) - μ • (c - p) = μ • (p - w) := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hμ, norm_sub_rev p w]
  have hh := (le_div_iff₀ hμ).mp h
  nlinarith only [hh]

noncomputable def proximalPoint (C : Set E) (f : E → ℝ) (μ : ℝ) (c : E) : E :=
  if h : ∃ p ∈ C, IsMinOn (regularized f μ c) C p then Classical.choose h else 0

omit [InnerProductSpace ℝ E] in
lemma proximalPoint_spec {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    {f : E → ℝ} (hf : Continuous f) (μ : ℝ) (c : E) :
    proximalPoint C f μ c ∈ C ∧ IsMinOn (regularized f μ c) C (proximalPoint C f μ c) := by
  have hc : Continuous (regularized f μ c) :=
    hf.add (((continuous_id.sub continuous_const).norm.pow 2).const_mul (μ / 2))
  have hex : ∃ p ∈ C, IsMinOn (regularized f μ c) C p :=
    hco.exists_isMinOn hne hc.continuousOn
  rw [proximalPoint, dite_eq_left hex]
  exact Classical.choose_spec hex

noncomputable def envelope (C : Set E) (f : E → ℝ) (μ : ℝ) (c : E) : ℝ :=
  regularized f μ c (proximalPoint C f μ c)

noncomputable def envelopeSlope (C : Set E) (f : E → ℝ) (μ : ℝ) (c : E) : E :=
  μ • (c - proximalPoint C f μ c)

lemma envelope_quadratic_identity (μ : ℝ) (c d p q : E) :
    μ / 2 * ‖q - d‖ ^ 2 - μ / 2 * ‖p - c‖ ^ 2 + ⟪μ • (c - p), q - p⟫ -
      ⟪μ • (c - p), d - c⟫ = μ / 2 * ‖(q - p) - (d - c)‖ ^ 2 := by
  have he : q - d = (p - c) + ((q - p) - (d - c)) := by module
  rw [he, norm_add_sq_real, inner_sub_right, real_inner_smul_left, real_inner_smul_left]
  have hpc : p - c = -(c - p) := by module
  rw [hpc, inner_neg_left, inner_neg_left]
  ring

lemma envelope_lower {C : Set E} (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C)
    {f : E → ℝ} {g : E → E} {L μ : ℝ} (hf : Model L f g) (hcont : Continuous f)
    (hμ : 0 < μ) (c d : E) :
    envelope C f μ c + ⟪envelopeSlope C f μ c, d - c⟫ ≤ envelope C f μ d := by
  let p := proximalPoint C f μ c
  let q := proximalPoint C f μ d
  have hp := proximalPoint_spec hne hco hcont μ c
  have hq := proximalPoint_spec hne hco hcont μ d
  have hv := minimizer_variational hcv (regularized_model hf hμ.le c) hp.1 hp.2 q hq.1
  have hs := hf.lower p q
  have he := envelope_quadratic_identity μ c d p q
  have hv' : ⟪μ • (c - p), q - p⟫ ≤ ⟪g p, q - p⟫ := by
    change 0 ≤ ⟪g p + μ • (p - c), q - p⟫ at hv
    rw [inner_add_left, show p - c = -(c - p) by module, smul_neg, inner_neg_left] at hv
    linarith
  change f p + μ / 2 * ‖p - c‖ ^ 2 + ⟪μ • (c - p), d - c⟫ ≤
    f q + μ / 2 * ‖q - d‖ ^ 2
  have hn : 0 ≤ μ / 2 * ‖(q - p) - (d - c)‖ ^ 2 := by positivity
  linarith

lemma envelope_upper {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    {f : E → ℝ} (hcont : Continuous f) (μ : ℝ) (c d : E) :
    envelope C f μ d ≤ envelope C f μ c + ⟪envelopeSlope C f μ c, d - c⟫ +
      μ / 2 * ‖d - c‖ ^ 2 := by
  let p := proximalPoint C f μ c
  have hp := proximalPoint_spec hne hco hcont μ c
  have hq := proximalPoint_spec hne hco hcont μ d
  have h := hq.2 hp.1
  change regularized f μ d (proximalPoint C f μ d) ≤ regularized f μ d p at h
  have he := shifted_square p c d
  rw [norm_sub_rev d p, norm_sub_rev c p] at he
  change envelope C f μ d ≤ f p + μ / 2 * ‖p - d‖ ^ 2 at h
  change envelope C f μ d ≤ f p + μ / 2 * ‖p - c‖ ^ 2 + ⟪μ • (c - p), d - c⟫ +
    μ / 2 * ‖d - c‖ ^ 2
  rw [real_inner_smul_left]
  rw [he] at h
  nlinarith only [h]

lemma envelope_model {C : Set E} (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C)
    {f : E → ℝ} {g : E → E} {L μ : ℝ} (hf : Model L f g) (hcont : Continuous f) (hμ : 0 < μ) :
    Model μ (envelope C f μ) (envelopeSlope C f μ) :=
  ⟨hμ, envelope_lower hne hco hcv hf hcont hμ, envelope_upper hne hco hcont μ⟩

end LongTails.Proofs.FiniteSumNondualProxGeometry
