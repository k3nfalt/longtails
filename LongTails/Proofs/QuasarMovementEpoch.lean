import LongTails.Proofs.QuasarMovementStep
import LongTails.Proofs.QuasarMovementTuning
import LongTails.Proofs.QuasarMovementIteration

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.ContinuizedSimilarQuasar.Movement

open LongTails.Setups.ContinuizedSimilarQuasar

open ContinuizedSimilarQuasar
open LongTails.Setups.ContinuizedSimilarQuasar

lemma sample_potential_step (p : Params) {f : p.E → ℝ} {G : p.E → p.E}
    (g : Fin p.n × p.E → p.E) (hp : spec.valid p)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ p.L * ‖x - y‖)
    (hfull : ∀ x, FiniteSum.fullGradient g x = G x)
    (hsim : ∀ x y, (𝔼 i, ‖(g (i, x) - G x) - (g (i, y) - G y)‖ ^ 2) ≤
      p.δ ^ 2 * ‖x - y‖ ^ 2)
    (u : p.E) (hmin : ∀ x, f u ≤ f x)
    (hquasar : ∀ x, p.γ * f x + ⟪G x, u - x⟫ + p.γ * p.μ / 2 * ‖u - x‖ ^ 2 ≤ p.γ * f u)
    (w : p.E) (s : p.E × p.E) (k : ℕ) (hk : k < p.n) :
    let θ := theta p
    let q := 4 / (4 + p.γ * θ)
    let W := backwardWeight q (2 * (θ ^ 2 / p.μ * p.δ ^ 2)) (1 + 6 / (p.n : ℝ))
    let V := fun j (v : p.E × p.E) => SimilarQuasar.energy f p.μ u v + W j * ‖v.1 - w‖ ^ 2
    Integrable (fun a => V k (sampleUpdate p.γ θ p.μ g w s a)) (sampleLaw p.n : Measure _) ∧
      (∫ a, V k (sampleUpdate p.γ θ p.μ g w s a) ∂(sampleLaw p.n : Measure _)) ≤ q * V (k + 1) s := by
  obtain ⟨hμ, hμL, hγ, hγ1, hδ, hΔ, hε⟩ := hp
  obtain ⟨hθ, hθ1, hstep, hrt, hsmall⟩ := theta_bounds p hμ hμL hγ hδ
  let θ := theta p
  let q := 4 / (4 + p.γ * θ)
  let v := θ ^ 2 / p.μ * p.δ ^ 2
  let η := θ ^ 2 / p.μ
  let W := backwardWeight q (2 * v) (1 + 6 / (p.n : ℝ))
  have hn : 0 < p.n := NeZero.pos p.n
  have hnR : 0 < (p.n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast hn
  have hgt : p.γ * θ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hγ1 hθ.le
    dsimp only [θ]
    nlinarith
  have hq : 1 / 2 ≤ q := by
    dsimp [q]
    apply (le_div_iff₀ (show 0 < 4 + p.γ * θ by positivity)).mpr
    linarith
  have hqp : 0 < q := by linarith
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hW0 : 0 ≤ W k := backwardWeight_nonneg hqp (by positivity) (by positivity) k
  have hW : W k ≤ 32768 * v * p.n := by
    have hh := backwardWeight_bound hq (show 0 ≤ 2 * v by positivity)
      (show 0 ≤ 1 + 6 / (p.n : ℝ) by positivity) hn hk.le
      (movement_ratio hn hγ.le hθ.le hrt)
    dsimp only [W]
    convert hh using 1; ring
  have habs := movement_absorption hμ hγ.le hθ.le hn1 hq hgt hsmall hW
  have hnoise := noise_prerequisite hn1 hμ hθ.le hgt hsmall
  have hL : 0 ≤ p.L := hμ.le.trans hμL
  have hG : Continuous G :=
    (show LipschitzWith ⟨p.L, hL⟩ G from lipschitzWith_iff_norm_sub_le.mpr hlip).continuous
  have he := sample_energy_slack g hL hμ hγ.le hθ.le hδ hstep hg hlip hfull hsim u hmin hquasar w s
  have hh := sample_distance_bound (μ := p.μ) g G hγ.le hθ.le hδ hnR hG hfull hsim w s
  have hf := flow_anchor_moment hγ.le hθ.le s w
  let Id := ∫ t in Ioi (0 : ℝ), Real.exp (-t) * ‖(flow p.γ θ t s).2 - (flow p.γ θ t s).1‖ ^ 2
  let Ig := ∫ t in Ioi (0 : ℝ), Real.exp (-t) * ‖G (flow p.γ θ t s).1‖ ^ 2
  have hId : 0 ≤ Id := integral_nonneg (fun t => by positivity)
  have hIg : 0 ≤ Ig := integral_nonneg (fun t => by positivity)
  have hE := energy_coarsening hv hId hf he.2
  have hH := distance_coarsening hn1 (show 0 ≤ η ^ 2 * p.δ ^ 2 by positivity)
    hnoise (sq_nonneg ‖s.1 - w‖) hId hIg hf hh.2
  have hi := he.1.add (hh.1.const_mul (W k))
  refine ⟨hi, ?_⟩
  change (∫ a, SimilarQuasar.energy f p.μ u (sampleUpdate p.γ θ p.μ g w s a) +
      W k * ‖(sampleUpdate p.γ θ p.μ g w s a).1 - w‖ ^ 2 ∂(sampleLaw p.n : Measure _)) ≤ _
  rw [integral_add he.1 (hh.1.const_mul (W k)), integral_const_mul]
  have hweight : 2 * v + W k * (1 + 6 / (p.n : ℝ)) = q * W (k + 1) :=
    backwardWeight_equation hqp.ne' k
  exact coupled_step hId hIg hW0 hE hH hweight habs.1 habs.2

lemma epoch_energy (p : Params) {f : p.E → ℝ} {G : p.E → p.E}
    (g : Fin p.n × p.E → p.E) (hp : spec.valid p)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ p.L * ‖x - y‖)
    (hfull : ∀ x, FiniteSum.fullGradient g x = G x)
    (hsim : ∀ x y, (𝔼 i, ‖(g (i, x) - G x) - (g (i, y) - G y)‖ ^ 2) ≤
      p.δ ^ 2 * ‖x - y‖ ^ 2)
    (u : p.E) (hmin : ∀ x, f u ≤ f x)
    (hquasar : ∀ x, p.γ * f x + ⟪G x, u - x⟫ + p.γ * p.μ / 2 * ‖u - x‖ ^ 2 ≤ p.γ * f u)
    (s : p.E × p.E) :
    Integrable (fun a => SimilarQuasar.energy f p.μ u (epochRun p g s a))
      (Measure.pi (fun _ : Fin p.n => (sampleLaw p.n : Measure _))) ∧
    (∫ a, SimilarQuasar.energy f p.μ u (epochRun p g s a)
      ∂Measure.pi (fun _ : Fin p.n => (sampleLaw p.n : Measure _))) ≤
      (4 / (4 + p.γ * theta p)) ^ p.n * SimilarQuasar.energy f p.μ u s := by
  have hμ := hp.1
  have hγ := hp.2.2.1
  have hδ := hp.2.2.2.2.1
  have hθ := (theta_bounds p hμ hp.2.1 hγ hδ).1
  let q := 4 / (4 + p.γ * theta p)
  let W := backwardWeight q (2 * (theta p ^ 2 / p.μ * p.δ ^ 2)) (1 + 6 / (p.n : ℝ))
  let V := fun k (v : p.E × p.E) => SimilarQuasar.energy f p.μ u v + W k * ‖v.1 - s.1‖ ^ 2
  have hqp : 0 < q := by dsimp [q]; positivity
  have hW0 (k : ℕ) : 0 ≤ W k := backwardWeight_nonneg hqp (by positivity) (by positivity) k
  have hf : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (hg x).hasFDerivAt.continuousAt)
  have hVc (k : ℕ) : Continuous (V k) := by
    have he := energy_continuous hf p.μ u
    dsimp [V]
    fun_prop
  have hV0 (k : ℕ) (v : p.E × p.E) : 0 ≤ V k v :=
    add_nonneg (SimilarQuasar.energy_nonneg hμ.le hmin v)
      (mul_nonneg (hW0 k) (sq_nonneg _))
  have hL : 0 ≤ p.L := hμ.le.trans hp.2.1
  have hG : Continuous G :=
    (show LipschitzWith ⟨p.L, hL⟩ G from lipschitzWith_iff_norm_sub_le.mpr hlip).continuous
  have hcomp := components_continuous g G hδ hG hsim
  have ha := (sampleUpdate_continuous p g hcomp).comp
    (show Continuous (fun z : (p.E × p.E) × (ℝ × Fin p.n) => (s.1, z)) by fun_prop)
  have hs (k : ℕ) (hk : k < p.n) (v : p.E × p.E) :=
    sample_potential_step p g hp hg hlip hfull hsim u hmin hquasar s.1 v k hk
  have hh := iterateSamples_backward_integral ha (sampleLaw p.n) V hVc hV0 hqp.le
    p.n hs p.n le_rfl s
  simpa only [epochRun, innerRun, q, V, W, backwardWeight, zero_mul, add_zero, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0), mul_zero] using hh

end OracleTemplate.ContinuizedSimilarQuasar.Movement
