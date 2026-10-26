import LongTails.Proofs.SharpEnvelopeEnergy
import LongTails.Proofs.SharpEnvelopeTuning
import LongTails.Proofs.RecursiveEnvelopeInner
import LongTails.Proofs.RecursiveEnvelopeExecution
import LongTails.Algorithms.SharpEnvelope

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SharpEnvelopeInner

open OracleTemplate RecursiveEnvelopeGeometry RecursiveEnvelopeExecution
open LongTails.Algorithms.SharpEnvelope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gradient_difference {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (c x : E) :
    ‖g x - g (prox g μ c)‖ ≤ ‖g x + μ • (x - c)‖ := by
  let p := prox g μ c
  have hm := h.monotone x p
  have hs := h.prox_stationary hμ c
  have he : g x + μ • (x - c) = (g x - g p) + μ • (x - p) := by
    have hh : g p = -(μ • (p - c)) := eq_neg_of_add_eq_zero_left hs
    rw [hh]
    module
  have hn : ‖g x + μ • (x - c)‖ ^ 2 = ‖g x - g p‖ ^ 2 +
      2 * μ * ⟪g x - g p, x - p⟫ + μ ^ 2 * ‖x - p‖ ^ 2 := by
    rw [he, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  have hp := mul_nonneg hμ.le hm
  have hsq : 0 ≤ μ ^ 2 * ‖x - p‖ ^ 2 := by positivity
  change ‖g x - g p‖ ≤ _
  nlinarith [norm_nonneg (g x - g p), norm_nonneg (g x + μ • (x - c))]

noncomputable def energy (f : E → ℝ) (g : E → E) (μ : ℝ) (c : E) (s : E × E) : ℝ :=
  regularized f μ c s.1 - envelope f g μ c + μ / 2 * ‖s.2 - prox g μ c‖ ^ 2

lemma energy_nonneg {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (c : E) (s : E × E) :
    0 ≤ energy f g μ c s := by
  have hm := h.prox_minimum hμ c s.1
  have hn : 0 ≤ μ / 2 * ‖s.2 - prox g μ c‖ ^ 2 := by positivity
  unfold energy
  linarith

lemma step_bound {L μ β θ τ A : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hβ : 0 ≤ β) (hτ : 0 < τ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hscale : θ ^ 2 / μ ≤ 1 / (4 * (L + μ)))
    (hA : θ / (2 * μ) + 3 / (4 * (L + μ)) + θ ^ 3 / (2 * μ * (1 - θ ^ 2)) ≤ A)
    (habsorb : A * (1 + 1 / τ) * β ^ 2 ≤ 1 / (4 * (L + μ)))
    (c : E) (s : E × E) (reply : E)
    (herr : ‖reply - g (InexactGradient.query θ s)‖ ≤ β * ‖g (InexactGradient.query θ s)‖) :
    energy f g μ c (step (L + μ) μ θ s
      (reply + μ • (InexactGradient.query θ s - c))) - energy f g μ c s +
      θ * (regularized f μ c s.1 - envelope f g μ c) ≤
      A * (1 + τ) * β ^ 2 * μ ^ 2 * ‖c - prox g μ c‖ ^ 2 := by
  let y := InexactGradient.query θ s
  let G := g y + μ • (y - c)
  let v := reply + μ • (y - c)
  have hL : 0 < L + μ := by have := h.pos; linarith
  have ht : 0 < 1 - θ ^ 2 := by nlinarith
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  have hyq : (1 + θ) • y = s.1 + θ • s.2 := by
    dsimp [y, InexactGradient.query]
    rw [smul_smul, mul_one_div_cancel (by positivity : (1 + θ) ≠ 0), one_smul]
  have hs := SharpEnvelope.sharp_energy hL hμ hθ0 hθ1 hscale hyq
    (h.regularized_upper c y (y - (1 / (L + μ)) • v))
    (h.regularized_lower c y (prox g μ c)) (h.regularized_lower c y s.1)
  have he : v - G = reply - g y := by dsimp [v, G]; abel
  have herr' : ‖v - G‖ ≤ β * ‖g (prox g μ c) + (g y - g (prox g μ c))‖ := by
    rw [add_sub_cancel, he]
    exact herr
  have hb := SharpEnvelope.relative_error_square hβ hτ herr' (gradient_difference h hμ c y)
  have hw : ‖g (prox g μ c)‖ ^ 2 = μ ^ 2 * ‖c - prox g μ c‖ ^ 2 := by
    rw [h.prox_field hμ c, envelopeField, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hw] at hb
  have hAm := mul_le_mul_of_nonneg_right hA (sq_nonneg ‖v - G‖)
  have hg := mul_le_mul_of_nonneg_right habsorb (sq_nonneg ‖G‖)
  have hbm := mul_le_mul_of_nonneg_left hb hA0
  change _ ≤ A * (1 + τ) * β ^ 2 * μ ^ 2 * ‖c - prox g μ c‖ ^ 2
  dsimp only [energy, step, envelope]
  change _ ≤ _ at hs
  dsimp only [regularized] at hs
  dsimp only [regularized]
  dsimp only [v, G, y] at hs hAm hg hbm
  ring_nf at hs hAm hg hbm ⊢
  linarith only [hs, hAm, hg, hbm]


lemma sum_certificate {L μ β θ τ A : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hβ : 0 ≤ β) (hτ : 0 < τ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hscale : θ ^ 2 / μ ≤ 1 / (4 * (L + μ)))
    (hA : θ / (2 * μ) + 3 / (4 * (L + μ)) + θ ^ 3 / (2 * μ * (1 - θ ^ 2)) ≤ A)
    (habsorb : A * (1 + 1 / τ) * β ^ 2 ≤ 1 / (4 * (L + μ)))
    {cost : ℕ} (oraclePlan : E → QueryPlan E E E cost) (reply : ℕ → E → E)
    (herr : ∀ k x, ‖evalAt reply (oraclePlan x) k - g x‖ ≤ β * ‖g x‖)
    (c z : E) (N call : ℕ) (s : E × E) :
    θ * ((N : ℝ) * (regularized f μ c z - envelope f g μ c) +
      ⟪g z + μ • (z - c),
        evalAt reply (sumPlan oraclePlan (L + μ) μ θ c N s) call - (N : ℝ) • z⟫) ≤
      energy f g μ c s + (N : ℝ) *
        (A * (1 + τ) * β ^ 2 * μ ^ 2 * ‖c - prox g μ c‖ ^ 2) := by
  induction N generalizing s call with
  | zero => simpa [sumPlan, evalAt] using energy_nonneg h hμ c s
  | succ N ih =>
      let y := InexactGradient.query θ s
      let v := evalAt reply (oraclePlan y) call
      let s' := step (L + μ) μ θ s (v + μ • (y - c))
      have hs := step_bound h hμ hβ hτ hθ0 hθ1 hscale hA habsorb c s v (herr call y)
      have hi := ih (call + cost) s'
      have hl := h.regularized_lower (μ := μ) c z s.1
      have hn : 0 ≤ μ / 2 * ‖s.1 - z‖ ^ 2 := by positivity
      have hl' : regularized f μ c z - envelope f g μ c +
          ⟪g z + μ • (z - c), s.1 - z⟫ ≤ regularized f μ c s.1 - envelope f g μ c := by
        linarith
      have ht := mul_le_mul_of_nonneg_left hl' hθ0.le
      simp only [sumPlan, evalAt_bind, evalAt_map]
      change θ * (((N + 1 : ℕ) : ℝ) * (regularized f μ c z - envelope f g μ c) +
        ⟪g z + μ • (z - c), s.1 + evalAt reply
          (sumPlan oraclePlan (L + μ) μ θ c N s') (call + cost) - ((N + 1 : ℕ) : ℝ) • z⟫) ≤ _
      have hid (total : E) : s.1 + total - ((N + 1 : ℕ) : ℝ) • z =
          (s.1 - z) + (total - (N : ℝ) • z) := by push_cast; module
      rw [hid, inner_add_right]
      push_cast
      change energy f g μ c s' - energy f g μ c s +
        θ * (regularized f μ c s.1 - envelope f g μ c) ≤ _ at hs
      linarith only [hi, ht, hs]

lemma averaged_accuracy {L μ β θ τ A : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hβ : 0 ≤ β) (hτ : 0 < τ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hscale : θ ^ 2 / μ ≤ 1 / (4 * (L + μ)))
    (hA : θ / (2 * μ) + 3 / (4 * (L + μ)) + θ ^ 3 / (2 * μ * (1 - θ ^ 2)) ≤ A)
    (habsorb : A * (1 + 1 / τ) * β ^ 2 ≤ 1 / (4 * (L + μ)))
    {cost : ℕ} (oraclePlan : E → QueryPlan E E E cost) (reply : ℕ → E → E)
    (herr : ∀ k x, ‖evalAt reply (oraclePlan x) k - g x‖ ≤ β * ‖g x‖)
    (c : E) {N : ℕ} (hN : 0 < N) (call : ℕ) (s : E × E) :
    regularized f μ c ((1 / (N : ℝ)) •
      evalAt reply (sumPlan oraclePlan (L + μ) μ θ c N s) call) - envelope f g μ c ≤
      energy f g μ c s / ((N : ℝ) * θ) +
        A / θ * (1 + τ) * β ^ 2 * μ ^ 2 * ‖c - prox g μ c‖ ^ 2 := by
  let total := evalAt reply (sumPlan oraclePlan (L + μ) μ θ c N s) call
  let z := (1 / (N : ℝ)) • total
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := sum_certificate h hμ hβ hτ hθ0 hθ1 hscale hA habsorb
    oraclePlan reply herr c z N call s
  have hid : total - (N : ℝ) • z = 0 := by
    dsimp [z]
    rw [smul_smul, mul_one_div_cancel (ne_of_gt hn), one_smul, sub_self]
  change θ * ((N : ℝ) * (regularized f μ c z - envelope f g μ c) +
    ⟪g z + μ • (z - c), total - (N : ℝ) • z⟫) ≤ _ at hs
  rw [hid, inner_zero_right, add_zero] at hs
  change regularized f μ c z - envelope f g μ c ≤ _
  have hs' : regularized f μ c z - envelope f g μ c ≤
      (energy f g μ c s + (N : ℝ) *
        (A * (1 + τ) * β ^ 2 * μ ^ 2 * ‖c - prox g μ c‖ ^ 2)) / ((N : ℝ) * θ) := by
    apply (le_div_iff₀ (mul_pos hn hθ0)).mpr
    nlinarith only [hs]
  convert hs' using 1
  field_simp


lemma reset_energy {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (c x : E) :
    energy f g μ c (x, x) ≤ 2 * (regularized f μ c x - envelope f g μ c) := by
  have hg := h.prox_growth hμ c x
  dsimp only [energy]
  change envelope f g μ c + μ / 2 * ‖x - prox g μ c‖ ^ 2 ≤ _ at hg
  linarith

lemma warm_accuracy {L μ β : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 32)
    {cost : ℕ} (oraclePlan : E → QueryPlan E E E cost) (reply : ℕ → E → E)
    (herr : ∀ k x, ‖evalAt reply (oraclePlan x) k - g x‖ ≤ β * ‖g x‖)
    (c : E) (warm call : ℕ)
    (htrans : (1 - InexactGradient.momentum (L + μ) μ (2 * β) / 2) ^ warm * (L + μ) ≤
      32 * β ^ 2 * μ) :
    regularized f μ c
      (evalAt reply (LongTails.Algorithms.RecursiveEnvelope.innerPlan oraclePlan
        (L + μ) μ (2 * β) c warm (c, c)) call) - envelope f g μ c ≤
      128 * β ^ 2 * μ * ‖c - prox g μ c‖ ^ 2 := by
  have hh := RecursiveEnvelopeInner.inner_accuracy h hμ hβ0 hβ
    (fun k y => evalAt reply (oraclePlan y) (call + cost * k)) (fun k y => herr _ _) c warm 0 htrans
  have he := evalAt_innerPlan reply oraclePlan (L + μ) μ (2 * β) c warm call 0 (c, c)
  simp only [mul_zero, add_zero] at he
  rw [← he] at hh
  nlinarith only [hh]

lemma inner_accuracy {L μ β θ τ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 32)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hθ : 0 < θ) (hsmall : θ ≤ τ / 8)
    (hscale : 1 / (4 * (L + μ)) = θ ^ 2 / μ) (hnoise : β ^ 2 ≤ τ * θ / 2)
    {cost : ℕ} (oraclePlan : E → QueryPlan E E E cost) (reply : ℕ → E → E)
    (herr : ∀ k x, ‖evalAt reply (oraclePlan x) k - g x‖ ≤ β * ‖g x‖)
    (c : E) (warm average call : ℕ)
    (htrans : (1 - InexactGradient.momentum (L + μ) μ (2 * β) / 2) ^ warm * (L + μ) ≤
      32 * β ^ 2 * μ)
    (haverage : 512 ≤ (average : ℝ) * θ * τ) :
    regularized f μ c
      (evalAt reply (innerPlan oraclePlan (L + μ) μ β θ c warm average) call) - envelope f g μ c ≤
      ((1 + 2 * τ) * β) ^ 2 * μ / 2 * ‖c - prox g μ c‖ ^ 2 := by
  let x := evalAt reply (LongTails.Algorithms.RecursiveEnvelope.innerPlan oraclePlan
    (L + μ) μ (2 * β) c warm (c, c)) call
  let A := θ / (2 * μ) * (1 + τ)
  have hw := warm_accuracy h hμ hβ0 hβ oraclePlan reply herr c warm call htrans
  change regularized f μ c x - envelope f g μ c ≤ _ at hw
  have hv := reset_energy h hμ c x
  have hθ1 : θ < 1 := by linarith
  have hA := SharpEnvelopeTuning.energy_coefficient hμ hθ hτ1 hsmall hscale
  have ha := SharpEnvelopeTuning.error_absorption hμ hθ hτ hτ1 hnoise hscale
  have hn : 0 < average := by
    by_contra hh
    have hz : average = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_mul] at haverage
    norm_num at haverage
  have he := averaged_accuracy h hμ hβ0 hτ hθ hθ1 (le_of_eq hscale.symm) hA ha
    oraclePlan reply herr c hn (call + cost * warm) (x, x)
  have hd : 0 < (average : ℝ) * θ := mul_pos (by exact_mod_cast hn) hθ
  have hV : energy f g μ c (x, x) ≤ 256 * β ^ 2 * μ * ‖c - prox g μ c‖ ^ 2 := by
    linarith
  have hbudget : energy f g μ c (x, x) / ((average : ℝ) * θ) ≤
      τ * β ^ 2 * μ / 2 * ‖c - prox g μ c‖ ^ 2 := by
    apply (div_le_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_right haverage
      (show 0 ≤ β ^ 2 * μ / 2 * ‖c - prox g μ c‖ ^ 2 by positivity)
    nlinarith only [hV, hh]
  have hid : (θ / (2 * μ) * (1 + τ)) / θ * (1 + τ) * β ^ 2 * μ ^ 2 *
      ‖c - prox g μ c‖ ^ 2 = (1 + τ) ^ 2 * β ^ 2 * μ / 2 * ‖c - prox g μ c‖ ^ 2 := by
    field_simp
  rw [hid] at he
  have hcoef : τ + (1 + τ) ^ 2 ≤ (1 + 2 * τ) ^ 2 := by nlinarith
  have hcoef' := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ β ^ 2 * μ / 2 * ‖c - prox g μ c‖ ^ 2 by positivity)
  simp only [innerPlan, evalAt_bind, evalAt_map]
  change regularized f μ c ((1 / (average : ℝ)) •
    evalAt reply (sumPlan oraclePlan (L + μ) μ θ c average (x, x))
      (call + cost * warm)) - envelope f g μ c ≤ _
  nlinarith only [he, hbudget, hcoef']

end LongTails.Proofs.SharpEnvelopeInner
