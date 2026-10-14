import LongTails.Proofs.RegularizedProxEgStage

namespace OracleTemplate.StochasticCohypomonotone

open LongTails.Setups.StochasticCohypomonotoneInclusion

noncomputable def stageQ (cfg : RegCfg) (s : ℕ) : ℝ := cfg.α * cfg.γ * cfg.Lam s

noncomputable def stageC (L ρ σ : ℝ) (cfg : RegCfg) (s : ℕ) : ℝ :=
  (stepK L ρ cfg.γ cfg.α (cfg.Lam s) + (cfg.α * cfg.γ) ^ 2) * (σ ^ 2 / cfg.b s)

structure CfgOK (cfg : RegCfg) (L ρ R σ ε M : ℝ) (δ : ℕ → ℝ) : Prop where
  γL : cfg.γ * L < 1
  two_ρ : 2 * ρ ≤ cfg.γ
  lam_pos : ∀ s, 0 < cfg.lam s
  Lam_zero : cfg.Lam 0 = cfg.lam 0
  Lam_succ : ∀ s, cfg.Lam (s + 1) = cfg.Lam s + cfg.lam (s + 1)
  Lam_le : ∀ s, cfg.Lam s ≤ cfg.lam (s + 1)
  step : ∀ s, s ≤ cfg.S → StepOK L ρ cfg.γ cfg.α (cfg.Lam s) M
  four_ρ : ∀ s, s ≤ cfg.S → 4 * ρ * cfg.Lam s ≤ 1
  b_pos : ∀ s, 0 < cfg.b s
  bf_pos : 0 < cfg.bf
  δ_pos : ∀ s, 0 < δ s
  rec0 : (1 - stageQ cfg 0) ^ cfg.T 0 * (2 * R ^ 2) +
    stageC L ρ σ cfg 0 / stageQ cfg 0 ≤ δ 0 ^ 2
  recS : ∀ s, s + 1 ≤ cfg.S → (1 - stageQ cfg (s + 1)) ^ cfg.T (s + 1) * (2 * δ s ^ 2) +
    stageC L ρ σ cfg (s + 1) / stageQ cfg (s + 1) ≤ δ (s + 1) ^ 2
  acc : 8 / cfg.γ * δ cfg.S + 4 * (σ / Real.sqrt cfg.bf) + Real.sqrt 2 * cfg.lam 0 * R +
    3 * ∑ s ∈ Finset.range cfg.S, cfg.lam (s + 1) * δ s ≤ ε

lemma CfgOK.Lam_pos {cfg : RegCfg} {L ρ R σ ε M : ℝ} {δ : ℕ → ℝ} (h : CfgOK cfg L ρ R σ ε M δ) :
    ∀ s, 0 < cfg.Lam s
  | 0 => by rw [h.Lam_zero]; exact h.lam_pos 0
  | s + 1 => by rw [h.Lam_succ]; have := h.Lam_pos s; have := h.lam_pos (s + 1); linarith


end OracleTemplate.StochasticCohypomonotone
