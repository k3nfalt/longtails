import LongTails.Proofs.SharpDistanceGeometry
import LongTails.Proofs.SharpDistanceTrajectory
import LongTails.Proofs.SharpDistanceExecution
import LongTails.Proofs.SharpEnvelopeInner
import LongTails.Proofs.AcceleratedMarkovExecution

namespace LongTails.Proofs.SharpDistanceInner

open OracleTemplate RecursiveEnvelopeGeometry SharpDistanceGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma reset_energy {f : E → ℝ} {g : E → E} {L μ : ℝ}
    (h : Model L f g) (hμ : 0 < μ) (c x : E) :
    energy f g μ c (x, x) = regularized f μ c x - envelope f g μ c := by
  exact shifted_gap h hμ c x

omit [CompleteSpace E] in
lemma step_filter {L μ θ : ℝ} (hL : 0 < L) (hμ : 0 < μ) (hθ : 0 < θ)
    (s : E × E) (v p : E) :
    let a := μ / L
    let A := (1 - a) / (1 + θ)
    let c := a / θ
    let t := LongTails.Algorithms.SharpEnvelope.step L μ θ s v
    (t.1 - p) - c • (t.2 - p) =
      A • ((s.1 - p) - c • (s.2 - p)) + ((1 - A) * (1 - c)) • (s.2 - p) := by
  dsimp only
  have hθn : θ ≠ 0 := hθ.ne'
  have hLn : L ≠ 0 := hL.ne'
  have hμn : μ ≠ 0 := hμ.ne'
  have htn : 1 + θ ≠ 0 := by positivity
  dsimp [LongTails.Algorithms.SharpEnvelope.step, InexactGradient.query]
  simp only [smul_add, smul_sub, smul_smul]
  match_scalars <;> field_simp <;> ring

lemma trajectory_energy {L μ θ β τ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hθ : 0 < θ) (hβ : 0 ≤ β)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 8) (hsmall : θ ≤ τ / 8)
    (hnoise : β ^ 2 ≤ τ * θ / 2) (hscale : μ / (L + μ) = 4 * θ ^ 2)
    (c : E) (s : ℕ → E × E) (reply : ℕ → E)
    (hstep : ∀ k, s (k + 1) = LongTails.Algorithms.SharpEnvelope.step (L + μ) μ θ (s k)
      (reply k + μ • (InexactGradient.query θ (s k) - c)))
    (herr : ∀ k, ‖reply k - g (InexactGradient.query θ (s k))‖ ≤
      β * ‖g (InexactGradient.query θ (s k))‖) (n : ℕ) :
    energy f g μ c (s n) ≤ (1 - θ) ^ n * energy f g μ c (s 0) +
      μ / 2 * ((1 + τ) * β * ‖c - prox g μ c‖) ^ 2 := by
  have hw : ‖g (prox g μ c)‖ ^ 2 = μ ^ 2 * ‖c - prox g μ c‖ ^ 2 := by
    rw [h.prox_field hμ c, envelopeField, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  apply SharpDistanceTrajectory.geometric_energy (fun k => energy f g μ c (s k))
    (by linarith) (by positivity) _ n
  intro k
  rw [hstep]
  have hh := relative_step h hμ hθ hβ hτ hτ1 hsmall hnoise hscale c (s k) (reply k) (herr k)
  rw [hw] at hh
  convert hh using 1
  field_simp

lemma trajectory_radius {L μ θ β τ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hθ : 0 < θ) (hβ : 0 ≤ β)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 8) (hsmall : θ ≤ τ / 8)
    (hnoise : β ^ 2 ≤ τ * θ / 2) (hscale : μ / (L + μ) = 4 * θ ^ 2)
    (c : E) (s : ℕ → E × E) (reply : ℕ → E)
    (hinit : (s 0).1 = (s 0).2)
    (hV : energy f g μ c (s 0) ≤ 128 * β ^ 2 * μ * ‖c - prox g μ c‖ ^ 2)
    (hstep : ∀ k, s (k + 1) = LongTails.Algorithms.SharpEnvelope.step (L + μ) μ θ (s k)
      (reply k + μ • (InexactGradient.query θ (s k) - c)))
    (herr : ∀ k, ‖reply k - g (InexactGradient.query θ (s k))‖ ≤
      β * ‖g (InexactGradient.query θ (s k))‖) (n : ℕ) :
    ‖(s n).1 - prox g μ c‖ ≤
      (1 + τ) * β * ‖c - prox g μ c‖ +
        48 * β * ‖c - prox g μ c‖ * (Real.sqrt (1 - θ)) ^ n := by
  let ρ := Real.sqrt (1 - θ)
  let r := ‖c - prox g μ c‖
  have ht : θ ≤ 1 / 4 := by linarith
  have hρ : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρsq : ρ ^ 2 = 1 - θ := Real.sq_sqrt (by linarith)
  have hρlo : 1 / 2 ≤ ρ := by nlinarith
  have hρhi : ρ ≤ 1 := by nlinarith
  have hp (k : ℕ) : (ρ ^ k) ^ 2 = (1 - θ) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, hρsq]
  have hz (k : ℕ) : ‖(s k).2 - prox g μ c‖ ≤ (1 + τ) * β * r + (16 * β * r) * ρ ^ k := by
    have he := trajectory_energy h hμ hθ hβ hτ hτ1 hsmall hnoise hscale c s reply hstep herr k
    have hi := mul_le_mul_of_nonneg_left hV (pow_nonneg (by linarith : 0 ≤ 1 - θ) k)
    have hs := shifted_nonneg h (prox g μ c) (s k).1
    apply SharpDistanceTrajectory.energy_radius hμ (by dsimp [r]; positivity)
      (by dsimp [r]; positivity) (V := energy f g μ c (s k))
    · dsimp only [energy]; linarith
    · rw [mul_pow (16 * β * r), hp]
      dsimp only [r] at *
      nlinarith only [he, hi]
  have hcoef := SharpDistanceEnergy.filter_coefficients hθ
    (show θ ^ 2 ≤ μ / (L + μ) by rw [hscale]; nlinarith [sq_nonneg θ])
    (show μ / (L + μ) ≤ θ by rw [hscale]; nlinarith) (show θ < 1 by linarith)
  have hh := SharpDistanceTrajectory.filter_radius
    (fun k => (s k).1 - prox g μ c) (fun k => (s k).2 - prox g μ c)
    hcoef.2.2.1 hcoef.1 hcoef.2.1 (show 0 ≤ 16 * β * r by dsimp [r]; positivity)
    hρlo hρhi (by rw [hρsq]; exact hcoef.2.2.2.1)
    (congrArg (fun x => x - prox g μ c) hinit) hz
    (fun k => by rw [hstep]; exact step_filter (by have := h.pos; linarith) hμ hθ _ _ _) n
  dsimp only [r, ρ] at hh
  convert hh using 1
  ring

lemma trajectory_accuracy {L μ θ β τ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hθ : 0 < θ) (hβ : 0 ≤ β)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 8) (hsmall : θ ≤ τ / 8)
    (hnoise : β ^ 2 ≤ τ * θ / 2) (hscale : μ / (L + μ) = 4 * θ ^ 2)
    (c : E) (s : ℕ → E × E) (reply : ℕ → E)
    (hinit : (s 0).1 = (s 0).2)
    (hV : energy f g μ c (s 0) ≤ 128 * β ^ 2 * μ * ‖c - prox g μ c‖ ^ 2)
    (hstep : ∀ k, s (k + 1) = LongTails.Algorithms.SharpEnvelope.step (L + μ) μ θ (s k)
      (reply k + μ • (InexactGradient.query θ (s k) - c)))
    (herr : ∀ k, ‖reply k - g (InexactGradient.query θ (s k))‖ ≤
      β * ‖g (InexactGradient.query θ (s k))‖) (n : ℕ)
    (htrans : (1 - θ) ^ n ≤ τ ^ 2 / 4096) :
    ‖(s n).1 - prox g μ c‖ ≤ (1 + 2 * τ) * β * ‖c - prox g μ c‖ ∧
    regularized f μ c (s n).1 - envelope f g μ c ≤
      2 * μ * β ^ 2 * ‖c - prox g μ c‖ ^ 2 := by
  let r := ‖c - prox g μ c‖
  have ht : 0 ≤ 1 - θ := by linarith
  have hp : ((Real.sqrt (1 - θ)) ^ n) ^ 2 = (1 - θ) ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt ht]
  have hρ : (Real.sqrt (1 - θ)) ^ n ≤ τ / 64 := by
    nlinarith [pow_nonneg (Real.sqrt_nonneg (1 - θ)) n]
  have hd := trajectory_radius h hμ hθ hβ hτ hτ1 hsmall hnoise hscale c s reply
    hinit hV hstep herr n
  have hm := mul_le_mul_of_nonneg_left hρ (show 0 ≤ 48 * β * r by dsimp [r]; positivity)
  have hd' : ‖(s n).1 - prox g μ c‖ ≤ (1 + 2 * τ) * β * r := by
    dsimp only [r] at hm ⊢
    nlinarith [mul_nonneg hβ (norm_nonneg (c - prox g μ c))]
  refine ⟨hd', ?_⟩
  have he := trajectory_energy h hμ hθ hβ hτ hτ1 hsmall hnoise hscale c s reply hstep herr n
  have hi := mul_le_mul_of_nonneg_left hV (pow_nonneg ht n)
  have hj := mul_le_mul_of_nonneg_right htrans
    (show 0 ≤ 128 * β ^ 2 * μ * r ^ 2 by positivity)
  have hv : energy f g μ c (s n) ≤ μ * β ^ 2 * r ^ 2 := by
    have hc : 128 * (τ ^ 2 / 4096) + (1 + τ) ^ 2 / 2 ≤ 1 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ μ * β ^ 2 * r ^ 2 by positivity)
    dsimp only [r] at *
    nlinarith only [he, hi, hj, hh]
  have hx : ‖(s n).1 - prox g μ c‖ ^ 2 ≤ 2 * β ^ 2 * r ^ 2 := by
    have hh := sq_le_sq₀ (norm_nonneg ((s n).1 - prox g μ c))
      (show 0 ≤ (1 + 2 * τ) * β * r by dsimp [r]; positivity)
    have hc : (1 + 2 * τ) ^ 2 ≤ 2 := by nlinarith
    have hb := mul_le_mul_of_nonneg_right hc (show 0 ≤ β ^ 2 * r ^ 2 by positivity)
    nlinarith only [hh.mpr hd', hb]
  have hs := shifted_gap h hμ c (s n).1
  have hz : 0 ≤ μ / 2 * ‖(s n).2 - prox g μ c‖ ^ 2 := by positivity
  have hx' := mul_le_mul_of_nonneg_left hx (show 0 ≤ μ / 2 by positivity)
  dsimp only [energy] at hv
  dsimp only [r] at *
  nlinarith only [hs, hv, hz, hx']

open RecursiveEnvelopeExecution LongTails.Algorithms.SharpDistanceEnvelope

lemma last_accuracy {L μ θ β τ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hθ : 0 < θ) (hβ : 0 ≤ β)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 8) (hsmall : θ ≤ τ / 8)
    (hnoise : β ^ 2 ≤ τ * θ / 2) (hscale : μ / (L + μ) = 4 * θ ^ 2)
    {cost : ℕ} (oraclePlan : E → QueryPlan E E E cost) (reply : ℕ → E → E)
    (herr : ∀ k x, ‖evalAt reply (oraclePlan x) k - g x‖ ≤ β * ‖g x‖)
    (c x : E) (n call : ℕ)
    (hwarm : regularized f μ c x - envelope f g μ c ≤
      128 * β ^ 2 * μ * ‖c - prox g μ c‖ ^ 2)
    (htrans : (1 - θ) ^ n ≤ τ ^ 2 / 4096) :
    let output := evalAt reply (lastPlan oraclePlan (L + μ) μ θ c n (x, x)) call
    ‖output - prox g μ c‖ ≤ (1 + 2 * τ) * β * ‖c - prox g μ c‖ ∧
    regularized f μ c output - envelope f g μ c ≤ 2 * μ * β ^ 2 * ‖c - prox g μ c‖ ^ 2 := by
  let update := fun k s => LongTails.Algorithms.SharpEnvelope.step (L + μ) μ θ s
    (evalAt reply (oraclePlan (InexactGradient.query θ s)) (call + cost * k) +
      μ • (InexactGradient.query θ s - c))
  let s := fun k => StochasticGradient.advance update k 0 (x, x)
  have hs (k : ℕ) : s (k + 1) = update k (s k) := by
    dsimp only [s]
    rw [HeavyTailedMarkovGradient.advance_add]
    simp only [StochasticGradient.advance, Nat.zero_add]
  have he := SharpDistanceExecution.evalAt_lastPlan reply oraclePlan (L + μ) μ θ c n call 0 (x, x)
  simp only [mul_zero, add_zero] at he
  change evalAt reply (lastPlan oraclePlan (L + μ) μ θ c n (x, x)) call = (s n).1 at he
  dsimp only
  rw [he]
  apply trajectory_accuracy h hμ hθ hβ hτ hτ1 hsmall hnoise hscale c s
    (fun k => evalAt reply (oraclePlan (InexactGradient.query θ (s k))) (call + cost * k))
    rfl _ hs (fun k => herr _ _) n htrans
  change energy f g μ c (x, x) ≤ _
  rw [reset_energy h hμ]
  exact hwarm

lemma inner_accuracy {L μ θ β τ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hθ : 0 < θ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1 / 32)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 8) (hsmall : θ ≤ τ / 8)
    (hnoise : β ^ 2 ≤ τ * θ / 2) (hscale : μ / (L + μ) = 4 * θ ^ 2)
    {cost : ℕ} (oraclePlan : E → QueryPlan E E E cost) (reply : ℕ → E → E)
    (herr : ∀ k x, ‖evalAt reply (oraclePlan x) k - g x‖ ≤ β * ‖g x‖)
    (c : E) (warm refine call : ℕ)
    (hwarm : (1 - InexactGradient.momentum (L + μ) μ (2 * β) / 2) ^ warm * (L + μ) ≤
      32 * β ^ 2 * μ)
    (htrans : (1 - θ) ^ refine ≤ τ ^ 2 / 4096) :
    let output := evalAt reply (innerPlan oraclePlan (L + μ) μ β θ c warm refine) call
    ‖output - prox g μ c‖ ≤ (1 + 2 * τ) * β * ‖c - prox g μ c‖ ∧
    regularized f μ c output - envelope f g μ c ≤ 2 * μ * β ^ 2 * ‖c - prox g μ c‖ ^ 2 := by
  have hw := SharpEnvelopeInner.warm_accuracy h hμ hβ hβ1 oraclePlan reply herr c warm call hwarm
  simpa only [innerPlan, evalAt_bind] using
    last_accuracy h hμ hθ hβ hτ hτ1 hsmall hnoise hscale oraclePlan reply herr c _ refine
      (call + cost * warm) hw htrans

end LongTails.Proofs.SharpDistanceInner
