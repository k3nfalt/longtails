import LongTails.Proofs.KatyushaStep
import LongTails.Proofs.KatyushaAveraging
import LongTails.Proofs.RecursiveGradientEnergy

open Set
open scoped BigOperators

namespace OracleTemplate.Katyusha

open LongTails.Setups.CompositeFiniteSumStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_energy {n : ℕ} [NeZero n] (D : E → ℝ) (τ α L θ d : ℝ)
    (hθ : 0 ≤ θ) (g : Fin n × E → E) (prox : ℝ → E → E → E)
    (snapshot full u : E)
    (hstep : ∀ s : E × E,
      let next := fun i => advance τ α L prox snapshot s
        (g (i, mix τ snapshot s) - g (i, snapshot) + full)
      (𝔼 i, (D (next i).1 + d * θ * ‖(next i).2 - u‖ ^ 2)) ≤
        (1 / 2 - τ) * D s.1 + d * ‖s.2 - u‖ ^ 2 + 1 / 2 * D snapshot)
    (k : ℕ) (s : E × E) :
    (𝔼 samples : Fin k → Fin n,
      ((1 - (1 / 2 - τ) * θ) * innerValues D τ α L θ g prox snapshot full k s samples +
        (1 / 2 - τ) * θ ^ k * D (innerRun τ α L θ g prox snapshot full k s samples).1.1 +
        d * θ ^ k * ‖(innerRun τ α L θ g prox snapshot full k s samples).1.2 - u‖ ^ 2)) ≤
      (1 / 2 - τ) * D s.1 + d * ‖s.2 - u‖ ^ 2 + 1 / 2 * weightSum θ k * D snapshot := by
  induction k generalizing s with
  | zero => simp [innerValues, innerRun, weightSum_zero]
  | succ k ih =>
      let next := fun i : Fin n => advance τ α L prox snapshot s
        (g (i, mix τ snapshot s) - g (i, snapshot) + full)
      have hcond (i : Fin n) :
          (𝔼 tail : Fin k → Fin n,
            ((1 - (1 / 2 - τ) * θ) *
                innerValues D τ α L θ g prox snapshot full (k + 1) s (Fin.cons i tail) +
              (1 / 2 - τ) * θ ^ (k + 1) *
                D (innerRun τ α L θ g prox snapshot full (k + 1) s (Fin.cons i tail)).1.1 +
              d * θ ^ (k + 1) *
                ‖(innerRun τ α L θ g prox snapshot full (k + 1) s (Fin.cons i tail)).1.2 - u‖ ^ 2)) ≤
            D (next i).1 + d * θ * ‖(next i).2 - u‖ ^ 2 +
              θ * (1 / 2 * weightSum θ k * D snapshot) := by
        have hh := mul_le_mul_of_nonneg_left (ih (next i)) hθ
        simp only [innerRun, innerValues, Fin.cons_zero, Fin.cons_succ,
          Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const, pow_succ] at hh ⊢
        dsimp only [next] at hh ⊢
        nlinarith only [hh]
      rw [NonconvexFiniteSum.expect_function_succ]
      have houter := Finset.expect_le_expect (s := Finset.univ) (fun i _ => hcond i)
      have hs := hstep s
      change (𝔼 i, (D (next i).1 + d * θ * ‖(next i).2 - u‖ ^ 2)) ≤ _ at hs
      simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at houter hs ⊢
      rw [weightSum_succ]
      nlinarith only [houter, hs]

lemma epoch_energy {n : ℕ} [NeZero n] (D : E → ℝ) (hc : ConvexOn ℝ univ D)
    (hD : ∀ x, 0 ≤ D x) (τ α L θ d : ℝ) (hθ : 0 < θ)
    (m : ℕ) (hcoef : (1 / 2 - τ) * θ + 1 / 2 * θ ^ m ≤ 1)
    (g : Fin n × E → E) (prox : ℝ → E → E → E) (u : E) (s : State E)
    (hstep : ∀ yz : E × E,
      let next := fun i => advance τ α L prox s.snapshot yz
        (FiniteSum.estimator g s.snapshot (mix τ s.snapshot yz) i)
      (𝔼 i, (D (next i).1 + d * θ * ‖(next i).2 - u‖ ^ 2)) ≤
        (1 / 2 - τ) * D yz.1 + d * ‖yz.2 - u‖ ^ 2 + 1 / 2 * D s.snapshot) :
    θ ^ m * (𝔼 samples : Fin m → Fin n,
      (1 / 2 * weightSum θ m * D (epoch τ α L θ m g prox s samples).snapshot +
        (1 / 2 - τ) * D (epoch τ α L θ m g prox s samples).y +
        d * ‖(epoch τ α L θ m g prox s samples).z - u‖ ^ 2)) ≤
      1 / 2 * weightSum θ m * D s.snapshot + (1 / 2 - τ) * D s.y + d * ‖s.z - u‖ ^ 2 := by
  have hi := inner_energy D τ α L θ d hθ.le g prox s.snapshot
    (FiniteSum.fullGradient g s.snapshot) u hstep m (s.y, s.z)
  have hcoef0 : 0 ≤ 1 - (1 / 2 - τ) * θ := by
    have := pow_nonneg hθ.le m
    linarith
  have hpoint (samples : Fin m → Fin n) :
      θ ^ m * (1 / 2 * weightSum θ m * D (epoch τ α L θ m g prox s samples).snapshot +
        (1 / 2 - τ) * D (epoch τ α L θ m g prox s samples).y +
        d * ‖(epoch τ α L θ m g prox s samples).z - u‖ ^ 2) ≤
      (1 - (1 / 2 - τ) * θ) * innerValues D τ α L θ g prox s.snapshot
        (FiniteSum.fullGradient g s.snapshot) m (s.y, s.z) samples +
        (1 / 2 - τ) * θ ^ m *
          D (innerRun τ α L θ g prox s.snapshot (FiniteSum.fullGradient g s.snapshot)
            m (s.y, s.z) samples).1.1 +
        d * θ ^ m *
          ‖(innerRun τ α L θ g prox s.snapshot (FiniteSum.fullGradient g s.snapshot)
            m (s.y, s.z) samples).1.2 - u‖ ^ 2 := by
    have hj := inner_average hc τ α L θ hθ g prox s.snapshot
      (FiniteSum.fullGradient g s.snapshot) m (s.y, s.z) samples
    have hj' := mul_le_mul_of_nonneg_left hj hcoef0
    have hm := mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (weightSum_nonneg hθ.le m)
        (hD (epoch τ α L θ m g prox s samples).snapshot))
    dsimp only [epoch] at hm ⊢
    nlinarith only [hj', hm]
  have he := Finset.expect_le_expect (s := Finset.univ) (fun samples _ => hpoint samples)
  rw [← Finset.mul_expect] at he
  exact he.trans (by simpa only [add_comm, add_left_comm, add_assoc] using hi)

end OracleTemplate.Katyusha
