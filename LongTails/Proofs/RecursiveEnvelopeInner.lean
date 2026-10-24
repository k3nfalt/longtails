import LongTails.Proofs.RecursiveEnvelopeGeometry
import LongTails.Proofs.InexactAcceleratedConvergence

open scoped RealInnerProductSpace

namespace LongTails.Proofs.RecursiveEnvelopeInner

open OracleTemplate RecursiveEnvelopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma inner_accuracy {L μ β : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 32)
    (answer : ℕ → E → E) (herr : ∀ k x, ‖answer k x - g x‖ ≤ β * ‖g x‖)
    (center : E) (N call : ℕ)
    (htrans : (1 - InexactGradient.momentum (L + μ) μ (2 * β) / 2) ^ N * (L + μ) ≤
      32 * β ^ 2 * μ) :
    regularized f μ center
      (StochasticGradient.advance
        (fun k s => InexactGradient.step (L + μ) μ (InexactGradient.momentum (L + μ) μ (2 * β)) s
          (answer k (InexactGradient.query (InexactGradient.momentum (L + μ) μ (2 * β)) s) +
            μ • (InexactGradient.query (InexactGradient.momentum (L + μ) μ (2 * β)) s - center)))
        N call (center, center)).1 - envelope f g μ center ≤
      (16 * β) ^ 2 * μ / 2 * ‖center - prox g μ center‖ ^ 2 := by
  let θ := InexactGradient.momentum (L + μ) μ (2 * β)
  let r := ‖center - prox g μ center‖
  let δ := β * μ * r
  let F := 2 / θ * (2 / (1 - 2 * β) * (3 / (4 * (L + μ)) + 2 * θ / μ) * δ ^ 2)
  have hL := h.pos
  have hLp : 0 < L + μ := by linarith
  have hβ1 : 2 * β < 1 := by linarith
  obtain ⟨hθ0, hθ1, hθL, hθα, hθlow, _⟩ :=
    InexactGradient.momentum_bounds hμ (show μ ≤ L + μ by linarith) (by positivity : 0 ≤ 2 * β) hβ1
  have he : ∀ k x, ‖(answer k x + μ • (x - center)) - (g x + μ • (x - center))‖ ≤
      (2 * β) * ‖g x + μ • (x - center)‖ + δ := by
    intro k x
    have hg := mul_le_mul_of_nonneg_left (h.regularized_oracle_bound hμ center x) hβ0
    have hid : (answer k x + μ • (x - center)) - (g x + μ • (x - center)) = answer k x - g x := by abel
    rw [hid]
    dsimp [δ, r]
    nlinarith [herr k x]
  have hstep := InexactGradient.advance_potential hLp hμ (by positivity : 0 ≤ 2 * β) hβ1
    hθ0 hθ1 hθL hθα (h.regularized_upper center) (h.regularized_lower center)
    (h.prox_minimum hμ center) (fun k x => answer k x + μ • (x - center)) he N call (center, center)
  have hf0 : 0 ≤ F := by dsimp [F]; positivity
  have hdelta : 136 * δ ^ 2 ≤ μ * (1 - 2 * β) ^ 2 * (192 * β ^ 2 * μ * r ^ 2) := by
    have hb : 136 ≤ 192 * (1 - 2 * β) ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ β ^ 2 * μ ^ 2 * r ^ 2)
    dsimp [δ]
    nlinarith
  have hfloor : F ≤ 96 * β ^ 2 * μ * r ^ 2 := by
    have hh := InexactGradient.floor_le hLp hμ (by positivity : 0 ≤ 2 * β) hβ1 hθ0 hθlow hdelta
    change F ≤ (192 * β ^ 2 * μ * r ^ 2) / 2 at hh
    linarith
  have hinit : InexactGradient.potential (regularized f μ center) μ (prox g μ center)
      (center, center) ≤ (L + μ) * r ^ 2 := by
    have hh := h.regularized_upper (μ := μ) center (prox g μ center) center
    rw [h.prox_stationary hμ, inner_zero_left, add_zero] at hh
    dsimp [InexactGradient.potential, r]
    have hn := sq_nonneg ‖center - prox g μ center‖
    nlinarith
  have hq : 0 ≤ (1 - θ / 2) ^ N := pow_nonneg (by dsimp [θ]; linarith) _
  have hp := mul_le_mul_of_nonneg_left hinit hq
  have ht := mul_le_mul_of_nonneg_right htrans (sq_nonneg r)
  have hf := mul_nonneg hq hf0
  dsimp only [InexactGradient.potential] at hstep
  change _ - F ≤ (1 - θ / 2) ^ N * (_ - F) at hstep
  have hnon : 0 ≤ μ / 4 * ‖(StochasticGradient.advance
      (fun k s => InexactGradient.step (L + μ) μ θ s
        (answer k (InexactGradient.query θ s) + μ • (InexactGradient.query θ s - center)))
      N call (center, center)).2 - prox g μ center‖ ^ 2 := by positivity
  dsimp only [InexactGradient.potential] at hp
  change _ ≤ (16 * β) ^ 2 * μ / 2 * r ^ 2
  dsimp [θ] at hp hf hnon
  dsimp only [θ] at hstep
  unfold envelope
  nlinarith only [hstep, hfloor, hp, ht, hf, hnon]

end LongTails.Proofs.RecursiveEnvelopeInner
