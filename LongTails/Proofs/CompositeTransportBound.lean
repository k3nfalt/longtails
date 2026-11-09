import LongTails.Proofs.CompositeTransportMoments

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.CompositeTransport

open OracleTemplate.SampledComposite

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure PathHyp (f : E → ℝ) (grad : E → E) (ψ : E → ℝ) (Q : Set E) (prox : ℝ → E → E → E)
    (L : ℝ) : Prop where
  hf : ∀ x, HasGradientAt f (grad x) x
  hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖
  hQ : Convex ℝ Q
  hψ : ConvexOn ℝ Q ψ
  hprox : ∀ a, 0 < a → ∀ z v, prox a z v ∈ Q ∧ IsMinOn (proxObj ψ a z v) Q (prox a z v)

variable {f : E → ℝ} {grad : E → E} {ψ : E → ℝ} {Q : Set E} {prox : ℝ → E → E → E} {L : ℝ}

lemma capStep_mem (H : PathHyp f grad ψ Q prox L) (cfg : Config) (hγ : 0 < cfg.γ) (hε : 0 < cfg.ε)
    {x m : E} (hx : x ∈ Q) : capStep cfg x (prox cfg.γ x m) ∈ Q := by
  have hp := (H.hprox cfg.γ hγ x m).1
  set lam := min 1 (2 * cfg.γ * cfg.ε / ‖prox cfg.γ x m - x‖)
  have hl0 : 0 ≤ lam := le_min zero_le_one (by positivity)
  have hl1 : lam ≤ 1 := min_le_left _ _
  have e : capStep cfg x (prox cfg.γ x m) = (1 - lam) • x + lam • prox cfg.γ x m := by
    simp only [capStep, lam]; module
  rw [e]
  exact H.hQ hx hp (by linarith) hl0 (by ring)

lemma traj_mem (H : PathHyp f grad ψ Q prox L) (cfg : Config) (hγ : 0 < cfg.γ) (hε : 0 < cfg.ε)
    {x0 : E} (hx0 : x0 ∈ Q) (g : E → Ω → E) (ξ : ℕ → Ω) : ∀ t, (traj cfg x0 g prox ξ t).1 ∈ Q := by
  intro t
  induction t with
  | zero => exact hx0
  | succ t ih => rw [traj_succ_fst]; exact capStep_mem H cfg hγ hε ih

lemma step_bound (H : PathHyp f grad ψ Q prox L) (hL : 0 < L) (cfg : Config) (hγ : 0 < cfg.γ)
    (hγL : cfg.γ * L ≤ 1) (hε : 0 < cfg.ε) {x m : E} (hx : x ∈ Q) :
    ‖L • (x - prox (1 / L) x (grad x))‖ ≤
      (f x + ψ x - (f (capStep cfg x (prox cfg.γ x m)) + ψ (capStep cfg x (prox cfg.γ x m)))) /
          (cfg.γ * cfg.ε) + 10 * ‖grad x - m‖ ^ 2 / cfg.ε + 11 / 8 * cfg.ε := by
  set γ := cfg.γ
  set ε := cfg.ε
  set p := prox γ x m
  set ps := prox γ x (grad x)
  set e := ‖grad x - m‖
  obtain ⟨hp, hpm⟩ := H.hprox γ hγ x m
  obtain ⟨hps, hpsm⟩ := H.hprox γ hγ x (grad x)
  have hprog := capped_progress H.hf H.hlip H.hQ H.hψ hγ hγL hε hx hp hpm
  simp only at hprog
  have hcap : capStep cfg x p = x + min 1 (2 * γ * ε / ‖p - x‖) • (p - x) := rfl
  rw [hcap]
  have hne : ‖p - ps‖ ≤ γ * e := by
    have := prox_nonexpansive H.hQ H.hψ hγ hp hpm hps hpsm
    refine this.trans (le_of_eq ?_)
    have : (x - γ • m) - (x - γ • grad x) = γ • (grad x - m) := by module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
  have hγ1 : γ ≤ 1 / L := by rw [le_div_iff₀ hL]; linarith
  obtain ⟨hq, hqm⟩ := H.hprox (1 / L) (by positivity) x (grad x)
  have hmono := mapping_antitone H.hQ H.hψ hγ hγ1 hps hpsm hq hqm
  have hLe : L • (x - prox (1 / L) x (grad x)) = (1 / (1 / L)) • (x - prox (1 / L) x (grad x)) := by
    rw [one_div_one_div]
  rw [hLe]
  refine hmono.trans ?_
  have hG : ‖(1 / γ) • (x - ps)‖ ≤ ‖p - x‖ / γ + e := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hγ)]
    have : ‖x - ps‖ ≤ ‖p - x‖ + γ * e := by
      calc ‖x - ps‖ = ‖(x - p) + (p - ps)‖ := by congr 1; abel
        _ ≤ ‖x - p‖ + ‖p - ps‖ := norm_add_le _ _
        _ ≤ ‖p - x‖ + γ * e := by rw [norm_sub_rev]; linarith
    calc 1 / γ * ‖x - ps‖ ≤ 1 / γ * (‖p - x‖ + γ * e) := by gcongr
      _ = ‖p - x‖ / γ + e := by field_simp
  refine hG.trans ?_
  have h1 : ‖p - x‖ / γ ≤ (f x + ψ x - (f (x + min 1 (2 * γ * ε / ‖p - x‖) • (p - x)) +
      ψ (x + min 1 (2 * γ * ε / ‖p - x‖) • (p - x)))) / (γ * ε) + (9 * e ^ 2 + 9 / 8 * ε ^ 2) / ε := by
    rw [div_add_div _ _ (by positivity) hε.ne', le_div_iff₀ (by positivity)]
    have : ‖p - x‖ / γ * (γ * ε * ε) = ε * ‖p - x‖ * ε := by field_simp
    rw [this]
    nlinarith [hprog]
  have h2 : e ≤ e ^ 2 / ε + ε / 4 := by
    rw [div_add_div _ _ hε.ne' (by norm_num), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (e - ε / 2)]
  have h3 : (9 * e ^ 2 + 9 / 8 * ε ^ 2) / ε + (e ^ 2 / ε + ε / 4) = 10 * e ^ 2 / ε + 11 / 8 * ε := by
    field_simp; ring
  linarith

end OracleTemplate.CompositeTransport
