import LongTails.Proofs.ComparisonTrustOuter
import LongTails.Proofs.ComparisonTrustBounds

namespace LongTails.Proofs.ComparisonTrustTuning

open OracleTemplate LongTails.Algorithms.ComparisonTrustRegion LongTails.Setups.ComparisonHessianLipschitz
  LongTails.Proofs.ComparisonTrustQuadratic LongTails.Proofs.ComparisonTrustEpoch
  LongTails.Proofs.ComparisonTrustBounds

noncomputable section

def absOf (p : Params) : Abs where
  L := p.L
  ρ := p.ρ
  ε := p.ε
  G := Real.sqrt (2 * p.L * p.Δ)
  γ := Real.sqrt (p.ρ * p.ε)
  r := Real.sqrt (p.ε / p.ρ) / 4
  n := Module.finrank ℝ p.E
  B0 := 2 + (Module.finrank ℝ p.E : ℝ) + p.L / Real.sqrt (p.ρ * p.ε) +
    Real.sqrt (2 * p.L * p.Δ) / p.ε

lemma sqrt_identities {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    ρ * (Real.sqrt (ε / ρ) / 4) = Real.sqrt (ρ * ε) / 4 ∧
      Real.sqrt (ρ * ε) * (Real.sqrt (ε / ρ) / 4) = ε / 4 := by
  constructor
  · have : Real.sqrt (ρ * ε) = ρ * Real.sqrt (ε / ρ) := by
      rw [show ρ * ε = ρ ^ 2 * (ε / ρ) by field_simp, Real.sqrt_mul (sq_nonneg ρ),
        Real.sqrt_sq hρ.le]
    rw [this]; ring
  · rw [show Real.sqrt (ρ * ε) * (Real.sqrt (ε / ρ) / 4) =
      Real.sqrt (ρ * ε) * Real.sqrt (ε / ρ) / 4 by ring, ← Real.sqrt_mul (by positivity),
      show ρ * ε * (ε / ρ) = ε ^ 2 by field_simp, Real.sqrt_sq hε.le]

lemma absOf_ok (p : Params) (hp : spec.valid p) : (absOf p).OK := by
  obtain ⟨hL, hρ, hΔ, hε⟩ := hp
  obtain ⟨h1, h2⟩ := sqrt_identities hρ hε
  exact ⟨hL, hρ, hε, Real.sqrt_nonneg _, Real.sqrt_pos.mpr (by positivity),
    by have : 0 < Real.sqrt (p.ε / p.ρ) := Real.sqrt_pos.mpr (by positivity); simp [absOf]; positivity,
    h1, h2, Nat.cast_nonneg _, rfl⟩

lemma tuning_fields (p : Params) :
    let A := absOf p
    (tuning p).γ = A.γ ∧ (tuning p).r = A.r ∧ (tuning p).μ = A.γ ∧ (tuning p).LA = A.LA ∧
      (tuning p).a = A.a ∧ (tuning p).η = A.γ / 192 ∧ (tuning p).ε = A.ε ∧
      (tuning p).τ0 = A.τ0 ∧ (tuning p).τ = A.τ ∧ (tuning p).m = A.m ∧ (tuning p).mt = A.m ∧
      (tuning p).N = A.N := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma radius_tmpl (p : Params) :
    radius (tmpl p.E (tuning p)) (2 * (absOf p).G) (tuning p).r = (absOf p).Rad := by
  simp only [radius, tmpl, Abs.Rad]
  show 2 * (2 * (absOf p).G) / (absOf p).γ + (absOf p).r = 4 * (absOf p).G / (absOf p).γ + (absOf p).r
  ring

lemma slackR_tmpl (p : Params) :
    slackR (tmpl p.E (tuning p)) (2 * (absOf p).G) (tuning p).r (4 * (absOf p).K)
      (2 * (absOf p).G * (absOf p).δ) = (absOf p).sR := by
  unfold slackR
  rw [radius_tmpl]
  simp only [Abs.sR]

lemma gmax_tmpl (p : Params) :
    gmax (tmpl p.E (tuning p)) (2 * (absOf p).G) (tuning p).r (4 * (absOf p).K)
      (2 * (absOf p).G * (absOf p).δ) = (absOf p).gm := by
  unfold gmax
  rw [radius_tmpl, slackR_tmpl]
  rfl

lemma slack_tmpl (p : Params) :
    slack (tmpl p.E (tuning p)) (2 * (absOf p).G) (tuning p).r (4 * (absOf p).K)
      (2 * (absOf p).G * (absOf p).δ) = (absOf p).sl := by
  unfold slack
  rw [radius_tmpl, slackR_tmpl, gmax_tmpl]
  rfl

lemma wmax_tmpl (p : Params) :
    wmax (tmpl p.E (tuning p)) (2 * (absOf p).G) (tuning p).r (4 * (absOf p).K)
      (2 * (absOf p).G * (absOf p).δ) = (absOf p).W := by
  unfold wmax
  rw [radius_tmpl, gmax_tmpl]
  rfl

lemma J_spec (p : Params) (hp : spec.valid p) :
    Real.sqrt (2 * p.L * p.Δ) ≤ 2 ^ ((tuning p).J - 1) * p.ε := by
  have hε := hp.2.2.2
  show Real.sqrt (2 * p.L * p.Δ) ≤ 2 ^ (⌈Real.logb 2 (Real.sqrt (2 * p.L * p.Δ) / p.ε)⌉₊ + 1 - 1) * p.ε
  rw [Nat.add_sub_cancel]
  set G := Real.sqrt (2 * p.L * p.Δ)
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  rcases hG0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have hx : 0 < G / p.ε := div_pos hpos hε
    have h1 : G / p.ε ≤ 2 ^ (⌈Real.logb 2 (G / p.ε)⌉₊ : ℝ) := by
      calc G / p.ε = 2 ^ Real.logb 2 (G / p.ε) := (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
        _ ≤ 2 ^ (⌈Real.logb 2 (G / p.ε)⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    rw [Real.rpow_natCast] at h1
    rwa [div_le_iff₀ hε] at h1

lemma N_pos (p : Params) (hp : spec.valid p) : 1 ≤ (tuning p).N := by
  have h := absOf_ok p hp
  show 1 ≤ (absOf p).N
  unfold Abs.N
  apply Nat.one_le_iff_ne_zero.mpr
  intro h0
  rw [Nat.ceil_eq_zero] at h0
  have : 0 < Real.sqrt (2 * (absOf p).L / (absOf p).γ + 4) * (8 * (absOf p).Λ + 40) := by
    have := Abs.Λ_pos h
    have : 0 < Real.sqrt (2 * (absOf p).L / (absOf p).γ + 4) := Real.sqrt_pos.mpr (by
      have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h.hL.le) h.hγ.le
      linarith)
    positivity
  linarith

set_option maxHeartbeats 800000 in
theorem rel_tuning (p : Params) (hp : spec.valid p) (hn : 1 ≤ Module.finrank ℝ p.E) :
    Rel p.E (tuning p) p.L p.ρ p.ε (absOf p).G (absOf p).δ (absOf p).K
      ((absOf p).ε * (absOf p).r / 100) := by
  have h := absOf_ok p hp
  obtain ⟨-, er, eμ, eLA, ea, -, -, -, -, -, -, eN⟩ := tuning_fields p
  have hn1 : 1 ≤ (absOf p).n := by show (1 : ℝ) ≤ Module.finrank ℝ p.E; exact_mod_cast hn
  refine
    { hL := h.hL, hρ := h.hρ, hε := h.hε, hG := h.hG, hγ := h.hγ, hr := h.hr, hμ := rfl,
      hLA := rfl, ha := Abs.a_pos h, ha1 := Abs.a_le_one h,
      htune := by
        show (absOf p).a ^ 2 * (absOf p).LA = (absOf p).γ
        rw [Abs.a_sq h, div_mul_cancel₀ _ (Abs.LA_pos h).ne']
      hη := by show 24 * ((absOf p).γ / 192) ≤ (absOf p).γ / 8; linarith
      hρr := h.hρr, hγr := h.hγr, hτ := by
        show 0 < (absOf p).τ
        unfold Abs.τ; have := h.hr; have := Abs.B0_pos h; positivity
      hτ0 := Abs.τ0_pos h, hLτ0 := Abs.Lτ0 h, hζ := Abs.hζ h hn1, hδ := Abs.hδ h hn1,
      hδ1 := Abs.δ_half h, hK := Abs.hK h,
      hK3 := by
        show (absOf p).K ≤ 3 * ((absOf p).γ / 192)
        have := Abs.K_le h; have := h.hγ; linarith
      hrad := Abs.hrad h, hJ := J_spec p hp, hJ1 := by show 1 ≤ _ + 1; omega,
      hN := N_pos p hp, hεt := rfl,
      hslack := by rw [slack_tmpl, ea, eμ, er]; exact Abs.hslack h
      hfin1 := by rw [wmax_tmpl, ea, eN, eLA, eμ]; exact Abs.hfin1 h
      hfin2 := by rw [slack_tmpl, ea, eLA]; exact Abs.hfin2 h
      hfin3 := by rw [slackR_tmpl]; exact Abs.hfin3 h
      hθ1 := Abs.hθ1 h, hθ2 := Abs.hθ2 h }

end

end LongTails.Proofs.ComparisonTrustTuning
