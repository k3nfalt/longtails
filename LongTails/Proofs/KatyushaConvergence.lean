import LongTails.Proofs.KatyushaEnergy
import LongTails.Proofs.KatyushaTuning

open Set
open scoped BigOperators

namespace OracleTemplate.Katyusha

open LongTails.Setups.CompositeFiniteSumStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma run_energy {n : ℕ} (τ α L θ : ℝ) (hθ : 0 ≤ θ) (m : ℕ)
    (g : Fin n × E → E) (prox : ℝ → E → E → E) (P : State E → ℝ)
    (hstep : ∀ s, θ ^ m * (𝔼 samples : Fin m → Fin n, P (epoch τ α L θ m g prox s samples)) ≤ P s)
    (S : ℕ) (s : State E) :
    θ ^ (m * S) * (𝔼 samples : Fin S → Fin m → Fin n,
      P (run τ α L θ m g prox S s samples)) ≤ P s := by
  induction S generalizing s with
  | zero => simp [run]
  | succ S ih =>
      have houter := Finset.expect_le_expect (s := Finset.univ)
        (fun first _ => ih (epoch τ α L θ m g prox s first))
      have hh := mul_le_mul_of_nonneg_left houter (pow_nonneg hθ m)
      rw [← Finset.mul_expect] at hh
      have he : θ ^ (m * (S + 1)) * (𝔼 samples : Fin (S + 1) → Fin m → Fin n,
          P (run τ α L θ m g prox (S + 1) s samples)) =
          θ ^ m * (θ ^ (m * S) * (𝔼 first : Fin m → Fin n,
            𝔼 tail : Fin S → Fin m → Fin n,
              P (run τ α L θ m g prox S (epoch τ α L θ m g prox s first) tail))) := by
        rw [NonconvexFiniteSum.expect_function_succ]
        simp only [run, Fin.cons_zero, Fin.cons_succ, Nat.mul_succ, pow_add]
        ring
      rw [he]
      exact hh.trans (hstep s)

noncomputable def potential (p : Params) (F : p.E → ℝ) (u : p.E) (s : State p.E) : ℝ :=
  1 / 2 * weightSum (theta p) (2 * p.n) * (F s.snapshot - F u) +
    (1 / 2 - tau p) * (F s.y - F u) +
    3 * ((2 * p.n : ℕ) : ℝ) * p.μ * ‖s.z - u‖ ^ 2

lemma initial_potential (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ) (hΔ : 0 ≤ p.Δ)
    (F : p.E → ℝ) (hF : StrongConvexOn univ p.μ F) (u : p.E)
    (hu : IsMinOn F univ u) (hgap : F p.x0 - F u ≤ p.Δ) :
    potential p F u ⟨p.x0, p.x0, p.x0⟩ ≤
      7 * weightSum (theta p) (2 * p.n) * p.Δ := by
  obtain ⟨hτ, hτh, hα, _, _⟩ := tuning_bounds p hL hμ
  have hθ : 1 ≤ theta p := by unfold theta; have := mul_pos hα hμ; linarith
  have hW := weightSum_ge hθ (2 * p.n)
  have hm : (1 : ℝ) ≤ (2 * p.n : ℕ) := by exact_mod_cast Nat.mul_pos (by decide) (NeZero.pos p.n)
  have hW0 := weightSum_nonneg (zero_le_one.trans hθ) (2 * p.n)
  have hD : 0 ≤ F p.x0 - F u := sub_nonneg.mpr (hu (mem_univ _))
  have hd := Composite.strong_minimum_bound hF hu p.x0
  have hd' := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 6 * ((2 * p.n : ℕ) : ℝ) by positivity)
  have h₁ := mul_le_mul_of_nonneg_left hgap
    (show 0 ≤ 1 / 2 * weightSum (theta p) (2 * p.n) by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 1 / 2 - tau p by linarith)
  have h₃ := mul_le_mul_of_nonneg_left hgap
    (show 0 ≤ 6 * ((2 * p.n : ℕ) : ℝ) by positivity)
  have h₄ := mul_le_mul_of_nonneg_right hW hΔ
  unfold potential
  dsimp only
  nlinarith

lemma run_rate (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ) (hΔ : 0 ≤ p.Δ)
    (f : Fin p.n → p.E → ℝ) (ψ : p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (prox : ℝ → p.E → p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ p.L * ‖x - y‖)
    (hψ : StrongConvexOn univ p.μ ψ)
    (hp : ∀ a, 0 < a → ∀ z v, IsMinOn (Composite.proxObjective ψ a z v) univ (prox a z v))
    (u : p.E) (hu : IsMinOn (fun x => LongTails.Setups.FiniteSumSmoothAndConvex.objective f x + ψ x) univ u)
    (hgap : LongTails.Setups.FiniteSumSmoothAndConvex.objective f p.x0 + ψ p.x0 - (LongTails.Setups.FiniteSumSmoothAndConvex.objective f u + ψ u) ≤ p.Δ)
    (S : ℕ) :
    let F := fun x => LongTails.Setups.FiniteSumSmoothAndConvex.objective f x + ψ x
    theta p ^ (2 * p.n * S) *
      (𝔼 samples : Fin S → Fin (2 * p.n) → Fin p.n,
        (F (run (tau p) (alpha p) p.L (theta p) (2 * p.n) g prox S
          ⟨p.x0, p.x0, p.x0⟩ samples).snapshot - F u)) ≤ 14 * p.Δ := by
  let F := fun x => LongTails.Setups.FiniteSumSmoothAndConvex.objective f x + ψ x
  let D := fun x => F x - F u
  have hF := Composite.strong_add_convex (FiniteSum.objective_convex hc) hψ
  have hFc : ConvexOn ℝ univ F := strongConvexOn_zero.mp (hF.mono hμ.le)
  have hDc : ConvexOn ℝ univ D := by
    refine ⟨convex_univ, fun x hx y hy a b ha hb hab => ?_⟩
    have h := hFc.2 hx hy ha hb hab
    dsimp only [D]
    simp only [smul_eq_mul] at h ⊢
    have he := congrArg (fun t : ℝ => t * F u) hab
    nlinarith only [h, he]
  have hD (x : p.E) : 0 ≤ D x := sub_nonneg.mpr (hu (mem_univ x))
  obtain ⟨hτ, hτh, hα, htune, _⟩ := tuning_bounds p hL hμ
  have hθ : 0 < theta p := by unfold theta; positivity
  have hW := weightSum_pos hθ.le (show 0 < 2 * p.n from Nat.mul_pos (by decide) (NeZero.pos p.n))
  have hcoeff := (theta_epoch_bounds p hL hμ).2.2
  have hstep (s : State p.E) :
      theta p ^ (2 * p.n) * (𝔼 samples : Fin (2 * p.n) → Fin p.n,
        potential p F u (epoch (tau p) (alpha p) p.L (theta p) (2 * p.n) g prox s samples)) ≤
      potential p F u s := by
    apply epoch_energy D hDc hD (tau p) (alpha p) p.L (theta p)
      (3 * ((2 * p.n : ℕ) : ℝ) * p.μ) hθ (2 * p.n) hcoeff g prox u s
    intro yz
    have h := expected_step hL hμ.le hα hτ hτh htune hc hg hlip hψ hp s.snapshot yz.1 yz.2 u
    dsimp only at h
    rw [distance_scale p hμ] at h
    simpa only [theta, D, F, add_comm, add_left_comm, add_assoc] using h
  have hr := run_energy (tau p) (alpha p) p.L (theta p) hθ.le (2 * p.n) g prox
    (potential p F u) hstep S ⟨p.x0, p.x0, p.x0⟩
  have hinit := initial_potential p hL hμ hΔ F hF u hu hgap
  have hlow (s : State p.E) :
      1 / 2 * weightSum (theta p) (2 * p.n) * D s.snapshot ≤ potential p F u s := by
    have h₁ := mul_nonneg (show 0 ≤ 1 / 2 - tau p by linarith) (hD s.y)
    have h₂ : 0 ≤ 3 * ((2 * p.n : ℕ) : ℝ) * p.μ * ‖s.z - u‖ ^ 2 := by positivity
    unfold potential
    dsimp only [D] at h₁ ⊢
    linarith
  have hl := Finset.expect_le_expect (s := Finset.univ) (fun samples _ =>
    hlow (run (tau p) (alpha p) p.L (theta p) (2 * p.n) g prox S
      ⟨p.x0, p.x0, p.x0⟩ samples))
  rw [← Finset.mul_expect] at hl
  have hh := (mul_le_mul_of_nonneg_left hl (pow_nonneg hθ.le (2 * p.n * S))).trans
    (hr.trans hinit)
  dsimp only
  apply (mul_le_mul_iff_right₀ (show 0 < 1 / 2 * weightSum (theta p) (2 * p.n) by positivity)).mp
  convert hh using 1 <;> ring

end OracleTemplate.Katyusha
