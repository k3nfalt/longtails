import LongTails.Proofs.HessianNcscOutput

namespace OracleTemplate.HessianNcsc

section Tune

variable (L μ ρ σ ε : ℝ)

noncomputable def tK : ℝ := 1 + L / μ

noncomputable def tQ : ℝ := 40 * ρ * tK L μ / ε + L ^ 2 / (ε ^ 2 + 20 * σ ^ 2)

noncomputable def tM : ℝ := tK L μ ^ 2 * (1 + σ ^ 2 / ε ^ 2) * (1 + ρ * ε * tK L μ / L ^ 2)

noncomputable def tEs : ℝ := 1 / tQ L μ ρ σ ε

noncomputable def tγ : ℝ := 1 / (L ^ 2 / μ + 20 * σ ^ 2 / (μ * tEs L μ ρ σ ε))

noncomputable def tα : ℝ := 1 / (4000 * tM L μ ρ σ ε)

noncomputable def tη : ℝ := tα L μ ρ σ ε * Real.sqrt (tEs L μ ρ σ ε) / (20 * tK L μ)

end Tune

structure TuneHyp (L μ ρ σ ε : ℝ) : Prop where
  μ0 : 0 < μ
  μL : μ ≤ L
  ρ0 : 0 < ρ
  σ0 : 0 < σ
  ε0 : 0 < ε

namespace TuneHyp

variable {L μ ρ σ ε : ℝ} (h : TuneHyp L μ ρ σ ε)
include h

lemma L0 : 0 < L := lt_of_lt_of_le h.μ0 h.μL

lemma k1 : 1 ≤ L / μ := by rw [le_div_iff₀ h.μ0]; linarith [h.μL]

lemma K2 : 2 ≤ tK L μ := by unfold tK; linarith [h.k1]

lemma K0 : 0 < tK L μ := by linarith [h.K2]

omit h in
lemma kK : L / μ ≤ tK L μ := by unfold tK; linarith

lemma Q0 : 0 < tQ L μ ρ σ ε := by
  unfold tQ; have := h.K0; have := h.ρ0; have := h.ε0; have := h.L0; have := h.σ0; positivity

lemma Es0 : 0 < tEs L μ ρ σ ε := by unfold tEs; exact one_div_pos.mpr h.Q0

lemma EsQ : tEs L μ ρ σ ε * tQ L μ ρ σ ε = 1 := by
  unfold tEs; field_simp [h.Q0.ne']

lemma M0 : 0 < tM L μ ρ σ ε := by
  unfold tM; have := h.K0; have := h.ρ0; have := h.ε0; have := h.L0; have := h.σ0; positivity

lemma M1 : 4 ≤ tM L μ ρ σ ε := by
  unfold tM
  have hK := h.K2
  have h1 : 1 ≤ 1 + σ ^ 2 / ε ^ 2 := by have := h.ε0; have := h.σ0; linarith [show 0 ≤ σ ^ 2 / ε ^ 2 by positivity]
  have h2 : 1 ≤ 1 + ρ * ε * tK L μ / L ^ 2 := by
    have := h.K0; have := h.ρ0; have := h.ε0; have := h.L0
    linarith [show 0 ≤ ρ * ε * tK L μ / L ^ 2 by positivity]
  have h4 : 4 ≤ tK L μ ^ 2 := by nlinarith
  calc (4 : ℝ) = 4 * 1 * 1 := by ring
    _ ≤ tK L μ ^ 2 * (1 + σ ^ 2 / ε ^ 2) * (1 + ρ * ε * tK L μ / L ^ 2) := by gcongr

lemma α0 : 0 < tα L μ ρ σ ε := by unfold tα; have := h.M0; positivity

lemma αM : tα L μ ρ σ ε * (4000 * tM L μ ρ σ ε) = 1 := by
  unfold tα; field_simp [h.M0.ne']

lemma α1 : tα L μ ρ σ ε ≤ 1 / 16000 := by
  unfold tα; rw [div_le_div_iff₀ (by have := h.M0; positivity) (by norm_num)]; nlinarith [h.M1]

lemma γ0 : 0 < tγ L μ ρ σ ε := by
  unfold tγ; have := h.Es0; have := h.μ0; have := h.L0; have := h.σ0; positivity

lemma γinv : tγ L μ ρ σ ε * (L ^ 2 / μ + 20 * σ ^ 2 / (μ * tEs L μ ρ σ ε)) = 1 := by
  unfold tγ
  have : 0 < L ^ 2 / μ + 20 * σ ^ 2 / (μ * tEs L μ ρ σ ε) := by
    have := h.Es0; have := h.μ0; have := h.L0; have := h.σ0; positivity
  rw [one_div, inv_mul_cancel₀ this.ne']

lemma γ1 : tγ L μ ρ σ ε ≤ μ / L ^ 2 := by
  have hg := h.γinv
  have hγ := h.γ0
  have hp : 0 ≤ tγ L μ ρ σ ε * (20 * σ ^ 2 / (μ * tEs L μ ρ σ ε)) := by
    have := h.Es0; have := h.μ0; have := h.σ0; positivity
  have : tγ L μ ρ σ ε * (L ^ 2 / μ) ≤ 1 := by rw [mul_add] at hg; linarith
  rw [le_div_iff₀ (by have := h.L0; positivity)]
  have e : tγ L μ ρ σ ε * (L ^ 2 / μ) = tγ L μ ρ σ ε * L ^ 2 / μ := by ring
  rw [e, div_le_one h.μ0] at this; linarith

lemma γσ : 20 * tγ L μ ρ σ ε * σ ^ 2 ≤ μ * tEs L μ ρ σ ε := by
  have hg := h.γinv
  have hγ := h.γ0
  have hE := h.Es0
  have hμ := h.μ0
  have hp : 0 ≤ tγ L μ ρ σ ε * (L ^ 2 / μ) := by have := h.L0; positivity
  have : tγ L μ ρ σ ε * (20 * σ ^ 2 / (μ * tEs L μ ρ σ ε)) ≤ 1 := by rw [mul_add] at hg; linarith
  have e : tγ L μ ρ σ ε * (20 * σ ^ 2 / (μ * tEs L μ ρ σ ε)) =
      (20 * tγ L μ ρ σ ε * σ ^ 2) / (μ * tEs L μ ρ σ ε) := by ring
  rw [e, div_le_one (by positivity)] at this; exact this

lemma Esρ : 40 * ρ * tK L μ * tEs L μ ρ σ ε ≤ ε := by
  have hq := h.EsQ
  have hE := h.Es0
  unfold tQ at hq
  have hp : 0 ≤ tEs L μ ρ σ ε * (L ^ 2 / (ε ^ 2 + 20 * σ ^ 2)) := by
    have := h.ε0; have := h.σ0; positivity
  have : tEs L μ ρ σ ε * (40 * ρ * tK L μ / ε) ≤ 1 := by rw [mul_add] at hq; linarith
  have e : tEs L μ ρ σ ε * (40 * ρ * tK L μ / ε) = 40 * ρ * tK L μ * tEs L μ ρ σ ε / ε := by ring
  rw [e, div_le_one h.ε0] at this; exact this

lemma EsL : L ^ 2 * tEs L μ ρ σ ε ≤ ε ^ 2 + 20 * σ ^ 2 := by
  have hq := h.EsQ
  have hE := h.Es0
  unfold tQ at hq
  have hp : 0 ≤ tEs L μ ρ σ ε * (40 * ρ * tK L μ / ε) := by
    have := h.ε0; have := h.ρ0; have := h.K0; positivity
  have : tEs L μ ρ σ ε * (L ^ 2 / (ε ^ 2 + 20 * σ ^ 2)) ≤ 1 := by rw [mul_add] at hq; linarith
  have e : tEs L μ ρ σ ε * (L ^ 2 / (ε ^ 2 + 20 * σ ^ 2)) = L ^ 2 * tEs L μ ρ σ ε / (ε ^ 2 + 20 * σ ^ 2) := by ring
  rw [e, div_le_one (by have := h.ε0; have := h.σ0; positivity)] at this; exact this

lemma Lu : L * Real.sqrt (tEs L μ ρ σ ε) ≤ ε + 5 * σ := by
  have hE := h.Es0
  have hs := Real.sq_sqrt hE.le
  have hu := Real.sqrt_nonneg (tEs L μ ρ σ ε)
  have hl := h.EsL
  have hε := h.ε0
  have hσ := h.σ0
  apply le_of_sq_le_sq_nonneg (by positivity)
  rw [mul_pow, hs]; nlinarith

lemma αs : tα L μ ρ σ ε * (1 + σ ^ 2 / ε ^ 2) * (1 + ρ * ε * tK L μ / L ^ 2) * (4000 * tK L μ ^ 2) = 1 := by
  have := h.αM; unfold tM at this; linarith

lemma αsq : tα L μ ρ σ ε * σ ^ 2 * (1 + ρ * ε * tK L μ / L ^ 2) ≤ ε ^ 2 / (4000 * tK L μ ^ 2) := by
  have ha := h.αs
  have hα := h.α0
  have hε := h.ε0
  have hK := h.K0
  have hv : 0 ≤ ρ * ε * tK L μ / L ^ 2 := by have := h.ρ0; have := h.L0; positivity
  rw [le_div_iff₀ (by positivity)]
  have hs : 0 ≤ σ ^ 2 / ε ^ 2 := by positivity
  have h1 : tα L μ ρ σ ε * (σ ^ 2 / ε ^ 2) * (1 + ρ * ε * tK L μ / L ^ 2) * (4000 * tK L μ ^ 2) ≤
      tα L μ ρ σ ε * (1 + σ ^ 2 / ε ^ 2) * (1 + ρ * ε * tK L μ / L ^ 2) * (4000 * tK L μ ^ 2) := by
    gcongr; linarith
  have e : tα L μ ρ σ ε * σ ^ 2 * (1 + ρ * ε * tK L μ / L ^ 2) * (4000 * tK L μ ^ 2) =
      ε ^ 2 * (tα L μ ρ σ ε * (σ ^ 2 / ε ^ 2) * (1 + ρ * ε * tK L μ / L ^ 2) * (4000 * tK L μ ^ 2)) := by
    field_simp
  rw [e]
  nlinarith

lemma αsq' : tα L μ ρ σ ε * σ ^ 2 ≤ ε ^ 2 / (4000 * tK L μ ^ 2) := by
  refine le_trans ?_ h.αsq
  have := h.α0
  have hv : 0 ≤ ρ * ε * tK L μ / L ^ 2 := by have := h.ρ0; have := h.L0; have := h.K0; have := h.ε0; positivity
  have : 0 ≤ tα L μ ρ σ ε * σ ^ 2 * (ρ * ε * tK L μ / L ^ 2) := by positivity
  linarith [show tα L μ ρ σ ε * σ ^ 2 * (1 + ρ * ε * tK L μ / L ^ 2) =
    tα L μ ρ σ ε * σ ^ 2 + tα L μ ρ σ ε * σ ^ 2 * (ρ * ε * tK L μ / L ^ 2) by ring]

lemma αs1 : tα L μ ρ σ ε * (1 + σ ^ 2 / ε ^ 2) * (4000 * tK L μ ^ 2) ≤ 1 := by
  have ha := h.αs
  have hα := h.α0
  have hv : 0 ≤ ρ * ε * tK L μ / L ^ 2 := by have := h.ρ0; have := h.L0; have := h.K0; have := h.ε0; positivity
  have hs : 0 ≤ σ ^ 2 / ε ^ 2 := by positivity
  have hK := h.K0
  have h0 : 0 ≤ tα L μ ρ σ ε * (1 + σ ^ 2 / ε ^ 2) * (4000 * tK L μ ^ 2) := by positivity
  nlinarith

lemma αK : tα L μ ρ σ ε * (4000 * tK L μ ^ 2) ≤ 1 := by
  have := h.αs1
  have hα := h.α0
  have hs : 0 ≤ σ ^ 2 / ε ^ 2 := by positivity
  have hK := h.K0
  nlinarith [show 0 ≤ tα L μ ρ σ ε * (σ ^ 2 / ε ^ 2) * (4000 * tK L μ ^ 2) by positivity]

lemma αe : tα L μ ρ σ ε * (ε + 5 * σ) ≤ ε / (1000 * tK L μ ^ 2) := by
  have h1 := h.αs1
  have hα := h.α0
  have hε := h.ε0
  have hσ := h.σ0
  have hK := h.K0
  rw [le_div_iff₀ (by positivity)]
  have key : ε + 5 * σ ≤ 3.5 * ε * (1 + σ ^ 2 / ε ^ 2) := by
    have e : 3.5 * ε * (1 + σ ^ 2 / ε ^ 2) = 3.5 * ε + 3.5 * σ ^ 2 / ε := by field_simp
    rw [e, ← sub_nonneg]
    have : 3.5 * ε + 3.5 * σ ^ 2 / ε - (ε + 5 * σ) = (3.5 * ε ^ 2 - 5 * σ * ε + 3.5 * σ ^ 2 - ε ^ 2) / ε := by
      field_simp; ring
    rw [this]; apply div_nonneg _ hε.le; nlinarith [sq_nonneg (ε - σ), sq_nonneg (ε - 2 * σ)]
  calc tα L μ ρ σ ε * (ε + 5 * σ) * (1000 * tK L μ ^ 2)
      ≤ tα L μ ρ σ ε * (3.5 * ε * (1 + σ ^ 2 / ε ^ 2)) * (1000 * tK L μ ^ 2) := by gcongr
    _ = 0.875 * ε * (tα L μ ρ σ ε * (1 + σ ^ 2 / ε ^ 2) * (4000 * tK L μ ^ 2)) := by ring
    _ ≤ 0.875 * ε * 1 := by gcongr
    _ ≤ ε := by linarith

lemma ασ1 : tα L μ ρ σ ε * σ ≤ ε / (8000 * tK L μ ^ 2) := by
  have h1 := h.αs1
  have hα := h.α0
  have hε := h.ε0
  have hσ := h.σ0
  have hK := h.K0
  rw [le_div_iff₀ (by positivity)]
  have key : σ ≤ ε * (1 + σ ^ 2 / ε ^ 2) / 2 := by
    have e : ε * (1 + σ ^ 2 / ε ^ 2) / 2 = (ε ^ 2 + σ ^ 2) / (2 * ε) := by field_simp
    rw [e, le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (ε - σ)]
  calc tα L μ ρ σ ε * σ * (8000 * tK L μ ^ 2) ≤ tα L μ ρ σ ε * (ε * (1 + σ ^ 2 / ε ^ 2) / 2) * (8000 * tK L μ ^ 2) := by
        gcongr
    _ = ε * (tα L μ ρ σ ε * (1 + σ ^ 2 / ε ^ 2) * (4000 * tK L μ ^ 2)) := by ring
    _ ≤ ε * 1 := by gcongr
    _ = ε := by ring

lemma v_sq : Real.sqrt (ρ * ε * tK L μ / L ^ 2) ^ 2 = ρ * ε * tK L μ / L ^ 2 := by
  have := h.ρ0; have := h.ε0; have := h.K0; have := h.L0
  exact Real.sq_sqrt (by positivity)

lemma v_half : Real.sqrt (ρ * ε * tK L μ / L ^ 2) ≤ (1 + ρ * ε * tK L μ / L ^ 2) / 2 := by
  have hv := h.v_sq
  nlinarith [sq_nonneg (Real.sqrt (ρ * ε * tK L μ / L ^ 2) - 1)]

lemma inv_u : 1 ≤ Real.sqrt (tEs L μ ρ σ ε) *
    (7 * Real.sqrt (ρ * ε * tK L μ / L ^ 2) * L / ε + L / (4 * σ)) := by
  have hE := h.Es0
  have hs := Real.sq_sqrt hE.le
  have hu := Real.sqrt_nonneg (tEs L μ ρ σ ε)
  have hv := h.v_sq
  have hv0 := Real.sqrt_nonneg (ρ * ε * tK L μ / L ^ 2)
  have hε := h.ε0
  have hσ := h.σ0
  have hL := h.L0
  have hq := h.EsQ
  have hQ : tQ L μ ρ σ ε ≤ (7 * Real.sqrt (ρ * ε * tK L μ / L ^ 2) * L / ε + L / (4 * σ)) ^ 2 := by
    unfold tQ
    have e1 : (7 * Real.sqrt (ρ * ε * tK L μ / L ^ 2) * L / ε) ^ 2 = 49 * ρ * tK L μ / ε := by
      rw [div_pow, mul_pow, mul_pow, hv]; field_simp; ring
    have e2 : (L / (4 * σ)) ^ 2 = L ^ 2 / (16 * σ ^ 2) := by ring
    have h1 : 40 * ρ * tK L μ / ε ≤ 49 * ρ * tK L μ / ε := by
      have := h.ρ0; have := h.K0; gcongr; norm_num
    have h2 : L ^ 2 / (ε ^ 2 + 20 * σ ^ 2) ≤ L ^ 2 / (16 * σ ^ 2) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
    have h3 : 0 ≤ 2 * (7 * Real.sqrt (ρ * ε * tK L μ / L ^ 2) * L / ε) * (L / (4 * σ)) := by positivity
    nlinarith
  apply le_of_sq_le_sq_nonneg (by positivity)
  rw [mul_pow, hs, one_pow]
  calc (1 : ℝ) = tEs L μ ρ σ ε * tQ L μ ρ σ ε := hq.symm
    _ ≤ _ := by gcongr

lemma key2 : tα L μ ρ σ ε ≤ tγ L μ ρ σ ε * μ / 4 := by
  have hρ := h.ρ0
  have hε := h.ε0
  have hσ := h.σ0
  have hg := h.γinv
  have hγ := h.γ0
  have hα := h.α0
  have hμ := h.μ0
  have hE := h.Es0
  have hL := h.L0
  have hK := h.K0
  have hq := h.EsQ
  have hk := (kK (L := L) (μ := μ))
  have hk1 := h.k1
  have haK := h.αK
  have hsq := h.αsq
  have hv := h.v_sq
  set α := tα L μ ρ σ ε
  set γ := tγ L μ ρ σ ε
  set E := tEs L μ ρ σ ε
  set K := tK L μ
  have hQE : 1 / E = tQ L μ ρ σ ε := by field_simp; linarith
  have hb : α * (L ^ 2 / μ + 20 * σ ^ 2 / (μ * E)) ≤ μ / 4 := by
    have e1 : α * (L ^ 2 / μ) = α * (L / μ) ^ 2 * μ := by field_simp
    have hαk : α * (L / μ) ^ 2 ≤ 1 / 4000 := by
      have : (L / μ) ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (by positivity) hk 2
      have h4 : α * K ^ 2 ≤ 1 / 4000 := by linarith
      calc α * (L / μ) ^ 2 ≤ α * K ^ 2 := by gcongr
        _ ≤ 1 / 4000 := h4
    have e2 : 20 * σ ^ 2 / (μ * E) = 20 * σ ^ 2 * tQ L μ ρ σ ε / μ := by rw [← hQE]; field_simp
    have hQ1 : α * σ ^ 2 * tQ L μ ρ σ ε ≤ L ^ 2 / (100 * K ^ 2) + α * L ^ 2 / 20 := by
      unfold tQ
      have t1 : α * σ ^ 2 * (40 * ρ * K / ε) ≤ L ^ 2 / (100 * K ^ 2) := by
        have hv1 : ρ * ε * K / L ^ 2 / (1 + ρ * ε * K / L ^ 2) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        have e : α * σ ^ 2 * (40 * ρ * K / ε) =
            40 * (α * σ ^ 2 * (1 + ρ * ε * K / L ^ 2)) * (L ^ 2 / ε ^ 2) * (ρ * ε * K / L ^ 2 / (1 + ρ * ε * K / L ^ 2)) := by
          have : (1 + ρ * ε * K / L ^ 2) ≠ 0 := by positivity
          have := h.ε0
          field_simp
        rw [e]
        have hε := h.ε0
        calc 40 * (α * σ ^ 2 * (1 + ρ * ε * K / L ^ 2)) * (L ^ 2 / ε ^ 2) * (ρ * ε * K / L ^ 2 / (1 + ρ * ε * K / L ^ 2))
            ≤ 40 * (ε ^ 2 / (4000 * K ^ 2)) * (L ^ 2 / ε ^ 2) * 1 := by
              have := h.ρ0
              gcongr
          _ = L ^ 2 / (100 * K ^ 2) := by field_simp; ring
      have t2 : α * σ ^ 2 * (L ^ 2 / (ε ^ 2 + 20 * σ ^ 2)) ≤ α * L ^ 2 / 20 := by
        have hσ := h.σ0; have hε := h.ε0
        rw [show α * σ ^ 2 * (L ^ 2 / (ε ^ 2 + 20 * σ ^ 2)) = α * L ^ 2 * (σ ^ 2 / (ε ^ 2 + 20 * σ ^ 2)) by ring]
        have : σ ^ 2 / (ε ^ 2 + 20 * σ ^ 2) ≤ 1 / 20 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
        calc α * L ^ 2 * (σ ^ 2 / (ε ^ 2 + 20 * σ ^ 2)) ≤ α * L ^ 2 * (1 / 20) := by gcongr
          _ = α * L ^ 2 / 20 := by ring
      rw [mul_add]; linarith
    have hLK : L ^ 2 / (100 * K ^ 2) ≤ μ ^ 2 / 100 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : L ≤ μ * K := by
        have : L / μ ≤ K := hk
        rwa [div_le_iff₀ hμ, mul_comm] at this
      nlinarith
    have e3 : α * (20 * σ ^ 2 * tQ L μ ρ σ ε / μ) = 20 * (α * σ ^ 2 * tQ L μ ρ σ ε) / μ := by ring
    have e4 : α * L ^ 2 / 20 = α * (L / μ) ^ 2 * μ ^ 2 / 20 := by field_simp
    rw [mul_add, e1, e2, e3]
    have : 20 * (α * σ ^ 2 * tQ L μ ρ σ ε) / μ ≤ 20 * (μ ^ 2 / 100 + α * (L / μ) ^ 2 * μ ^ 2 / 20) / μ := by
      gcongr; linarith
    have e5 : 20 * (μ ^ 2 / 100 + α * (L / μ) ^ 2 * μ ^ 2 / 20) / μ = μ / 5 + α * (L / μ) ^ 2 * μ := by
      field_simp; ring
    nlinarith
  have e : α = γ * (α * (L ^ 2 / μ + 20 * σ ^ 2 / (μ * E))) := by
    calc α = (γ * (L ^ 2 / μ + 20 * σ ^ 2 / (μ * E))) * α := by rw [hg, one_mul]
      _ = _ := by ring
  rw [e]
  calc γ * (α * (L ^ 2 / μ + 20 * σ ^ 2 / (μ * E))) ≤ γ * (μ / 4) := by gcongr
    _ = γ * μ / 4 := by ring

lemma LleK : L ≤ μ * tK L μ := by
  have := (kK (L := L) (μ := μ)); rwa [div_le_iff₀ h.μ0, mul_comm] at this

lemma kK2 : (L / μ) ^ 2 ≤ tK L μ ^ 2 := pow_le_pow_left₀ (by have := h.L0; have := h.μ0; positivity) (kK (L := L) (μ := μ)) 2

lemma b3 : (L / μ) * tα L μ ρ σ ε * Real.sqrt (tEs L μ ρ σ ε) / tγ L μ ρ σ ε ≤ ε / 40 := by
  have hρ := h.ρ0
  have hε := h.ε0
  have hσ := h.σ0
  have hμ := h.μ0
  have hL := h.L0
  have hK := h.K0
  have hγ := h.γ0
  have hα := h.α0
  have hE := h.Es0
  have hg := h.γinv
  have hkK := h.kK2
  have hu := Real.sqrt_pos.mpr hE
  have hs := Real.sq_sqrt hE.le
  have hX := h.inv_u
  have hLu := h.Lu
  have hae := h.αe
  have hsq := h.αsq
  have hs1 := h.ασ1
  have hvh := h.v_half
  have hv0 := Real.sqrt_nonneg (ρ * ε * tK L μ / L ^ 2)
  set α := tα L μ ρ σ ε
  set γ := tγ L μ ρ σ ε
  set E := tEs L μ ρ σ ε
  set K := tK L μ
  set u := Real.sqrt E
  set v := Real.sqrt (ρ * ε * K / L ^ 2)
  set X := 7 * v * L / ε + L / (4 * σ)
  have hX0 : 0 < X := by positivity
  have hinvγ : 1 / γ = L ^ 2 / μ + 20 * σ ^ 2 / (μ * E) := by
    rw [div_eq_iff hγ.ne', mul_comm]; exact hg.symm
  have hinvu : 1 / u ≤ X := by rw [div_le_iff₀ hu]; linarith
  have e : (L / μ) * α * u / γ = (L / μ) ^ 2 * (α * (L * u)) + 20 * (L / μ) * (α * σ ^ 2) / μ * (1 / u) := by
    rw [div_eq_mul_one_div _ γ, hinvγ, ← hs]; field_simp
  rw [e]
  have t1 : (L / μ) ^ 2 * (α * (L * u)) ≤ ε / 1000 := by
    have : α * (L * u) ≤ ε / (1000 * K ^ 2) := by
      calc α * (L * u) ≤ α * (ε + 5 * σ) := by gcongr
        _ ≤ _ := hae
    calc (L / μ) ^ 2 * (α * (L * u)) ≤ K ^ 2 * (ε / (1000 * K ^ 2)) := by
          apply mul_le_mul hkK this (by positivity) (by positivity)
      _ = ε / 1000 := by field_simp
  have t2 : 20 * (L / μ) * (α * σ ^ 2) / μ * (1 / u) ≤ 140 * (L / μ) ^ 2 * (v * (α * σ ^ 2)) / ε +
      5 * (L / μ) ^ 2 * (α * σ) := by
    calc 20 * (L / μ) * (α * σ ^ 2) / μ * (1 / u) ≤ 20 * (L / μ) * (α * σ ^ 2) / μ * X := by gcongr
      _ = _ := by simp only [X]; field_simp; ring
  have t3 : v * (α * σ ^ 2) ≤ ε ^ 2 / (8000 * K ^ 2) := by
    have : v * (α * σ ^ 2) ≤ (1 + ρ * ε * K / L ^ 2) / 2 * (α * σ ^ 2) := by gcongr
    have e2 : ε ^ 2 / (8000 * K ^ 2) = ε ^ 2 / (4000 * K ^ 2) / 2 := by field_simp; ring
    rw [e2]; nlinarith
  have t4 : 140 * (L / μ) ^ 2 * (v * (α * σ ^ 2)) / ε ≤ 7 * ε / 400 := by
    rw [div_le_iff₀ hε]
    calc 140 * (L / μ) ^ 2 * (v * (α * σ ^ 2)) ≤ 140 * K ^ 2 * (ε ^ 2 / (8000 * K ^ 2)) := by
          gcongr
      _ = 7 * ε / 400 * ε := by field_simp; ring
  have t5 : 5 * (L / μ) ^ 2 * (α * σ) ≤ ε / 1600 := by
    calc 5 * (L / μ) ^ 2 * (α * σ) ≤ 5 * K ^ 2 * (ε / (8000 * K ^ 2)) := by gcongr
      _ = ε / 1600 := by field_simp; ring
  linarith

lemma key1 : (L / μ) * L * tη L μ ρ σ ε ≤ ε * tγ L μ ρ σ ε * μ / 800 := by
  have hb := h.b3
  have hγ := h.γ0
  have hK := h.K0
  have hμ := h.μ0
  have hL := h.L0
  have hLK := h.LleK
  have e : (L / μ) * L * tη L μ ρ σ ε =
      ((L / μ) * tα L μ ρ σ ε * Real.sqrt (tEs L μ ρ σ ε) / tγ L μ ρ σ ε) * (tγ L μ ρ σ ε * L / (20 * tK L μ)) := by
    unfold tη; field_simp
  rw [e]
  have h2 : tγ L μ ρ σ ε * L / (20 * tK L μ) ≤ tγ L μ ρ σ ε * μ / 20 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  calc _ ≤ ε / 40 * (tγ L μ ρ σ ε * μ / 20) := by
        apply mul_le_mul hb h2 (by positivity) (by have := h.ε0; positivity)
    _ = ε * tγ L μ ρ σ ε * μ / 800 := by ring

lemma s2K : Real.sqrt (1 + (L / μ) ^ 2) ≤ tK L μ := by
  have hk : 0 ≤ L / μ := by have := h.L0; have := h.μ0; positivity
  rw [Real.sqrt_le_left (by have := h.K0; linarith)]
  unfold tK; nlinarith

lemma k2K : 1 + (L / μ) ^ 2 ≤ tK L μ ^ 2 := by
  have hk : 0 ≤ L / μ := by have := h.L0; have := h.μ0; positivity
  unfold tK; nlinarith

lemma ρu : ρ * Real.sqrt (tEs L μ ρ σ ε) ≤ Real.sqrt (ρ * ε * tK L μ / L ^ 2) * L / (6 * tK L μ) := by
  have hE := h.Es0
  have hs := Real.sq_sqrt hE.le
  have hv := h.v_sq
  have hρ := h.ρ0
  have hK := h.K0
  have hL := h.L0
  have hε := h.ε0
  have h40 := h.Esρ
  apply le_of_sq_le_sq_nonneg (by positivity)
  rw [mul_pow, hs, div_pow, mul_pow, hv]
  rw [show ρ * ε * tK L μ / L ^ 2 * L ^ 2 / (6 * tK L μ) ^ 2 = ρ * ε / (36 * tK L μ) by field_simp; ring]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma κη : (L / μ) * tη L μ ρ σ ε ≤ tγ L μ ρ σ ε * μ * Real.sqrt (tEs L μ ρ σ ε) / 80 := by
  have hk := (kK (L := L) (μ := μ))
  have hK := h.K0
  have hα := h.α0
  have k2 := h.key2
  have hu := Real.sqrt_nonneg (tEs L μ ρ σ ε)
  unfold tη
  have hk0 : 0 ≤ L / μ := by have := h.L0; have := h.μ0; positivity
  calc L / μ * (tα L μ ρ σ ε * Real.sqrt (tEs L μ ρ σ ε) / (20 * tK L μ))
      = (L / μ / tK L μ) * (tα L μ ρ σ ε * Real.sqrt (tEs L μ ρ σ ε) / 20) := by field_simp
    _ ≤ 1 * (tγ L μ ρ σ ε * μ / 4 * Real.sqrt (tEs L μ ρ σ ε) / 20) := by
        gcongr
        rw [div_le_one hK]; exact hk
    _ = _ := by ring

end TuneHyp

section Cfg

noncomputable def tCfg (L μ ρ σ ε G : ℝ) (T : ℕ) : IgtConfig where
  α := tα L μ ρ σ ε
  η := tη L μ ρ σ ε
  lam := ε / 4
  γ := tγ L μ ρ σ ε
  NA := ⌈Real.log (1 + G ^ 2 / μ ^ 2 * tQ L μ ρ σ ε) / (tγ L μ ρ σ ε * μ)⌉₊
  NB := ⌈4000 * tM L μ ρ σ ε⌉₊
  NC := ⌈4 / (tγ L μ ρ σ ε * μ)⌉₊
  T := T

noncomputable def tPs (L μ ρ σ ε : ℝ) : ℝ :=
  4 * L ^ 2 * tEs L μ ρ σ ε +
    4 * (ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * tη L μ ρ σ ε ^ 2 / tα L μ ρ σ ε / tα L μ ρ σ ε) ^ 2 +
    2 * tα L μ ρ σ ε * σ ^ 2

end Cfg

namespace TuneHyp

variable {L μ ρ σ ε : ℝ} (h : TuneHyp L μ ρ σ ε)
include h

lemma ηα : tη L μ ρ σ ε ^ 2 / tα L μ ρ σ ε ^ 2 = tEs L μ ρ σ ε / (400 * tK L μ ^ 2) := by
  have hE := h.Es0
  have hs := Real.sq_sqrt hE.le
  have := h.α0; have := h.K0
  unfold tη; field_simp; rw [hs]; ring

lemma DDa : ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * tη L μ ρ σ ε ^ 2 / tα L μ ρ σ ε / tα L μ ρ σ ε ≤ ε / 16000 := by
  have hk2 := h.k2K
  have hK := h.K0
  have hρ := h.ρ0
  have hα := h.α0
  have h40 := h.Esρ
  have hE := h.Es0
  have e : ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * tη L μ ρ σ ε ^ 2 / tα L μ ρ σ ε / tα L μ ρ σ ε =
      ρ * tK L μ * (1 + (L / μ) ^ 2) * (tη L μ ρ σ ε ^ 2 / tα L μ ρ σ ε ^ 2) := by unfold tK; ring
  rw [e, h.ηα]
  calc ρ * tK L μ * (1 + (L / μ) ^ 2) * (tEs L μ ρ σ ε / (400 * tK L μ ^ 2))
      ≤ ρ * tK L μ * tK L μ ^ 2 * (tEs L μ ρ σ ε / (400 * tK L μ ^ 2)) := by gcongr
    _ = 40 * ρ * tK L μ * tEs L μ ρ σ ε / 16000 := by field_simp; ring
    _ ≤ ε / 16000 := by gcongr

set_option maxHeartbeats 2000000 in
lemma c1 (G : ℝ) (T : ℕ) :
    kAe L μ (tCfg L μ ρ σ ε G T) * tEs L μ ρ σ ε + kAh L μ (tCfg L μ ρ σ ε G T) * tPs L μ ρ σ ε +
      kA0 L μ ρ σ (tCfg L μ ρ σ ε G T) ≤ tEs L μ ρ σ ε := by
  have hρ := h.ρ0
  have hε := h.ε0
  have hσ := h.σ0
  have hμ := h.μ0
  have hL := h.L0
  have hK := h.K0
  have hγ := h.γ0
  have hα := h.α0
  have hE := h.Es0
  have hs := Real.sq_sqrt hE.le
  have hu0 := Real.sqrt_nonneg (tEs L μ ρ σ ε)
  have k1 := h.key1
  have k2 := h.key2
  have hκη := h.κη
  have hρu := h.ρu
  have hsq := h.αsq
  have hsq' := h.αsq'
  have hγσ := h.γσ
  have hs2 := h.s2K
  have hk2 := h.k2K
  have hDD := h.DDa
  have hηα := h.ηα
  have hvh := h.v_half
  have hv0 := Real.sqrt_nonneg (ρ * ε * tK L μ / L ^ 2)
  have hLK := h.LleK
  have hkK := (kK (L := L) (μ := μ))
  simp only [kAe, kAh, kA0, kC0, kCe, kCh, tCfg, tPs]
  set α := tα L μ ρ σ ε
  set γ := tγ L μ ρ σ ε
  set η := tη L μ ρ σ ε
  set E := tEs L μ ρ σ ε
  set K := tK L μ
  set u := Real.sqrt E
  set v := Real.sqrt (ρ * ε * K / L ^ 2)
  set κ := L / μ
  set g := γ * μ
  set D := ρ * (1 + κ) * (1 + κ ^ 2) * η ^ 2 / α / α
  have hg : 0 < g := by positivity
  have hk0 : 0 ≤ κ := by positivity
  have hη0 : 0 ≤ η := by simp only [η, tη]; positivity
  have hD0 : 0 ≤ D := by positivity
  have r2 : 2 * η / (ε / 4) = 8 * η / ε := by field_simp; ring
  rw [r2, show 6 * η * α * σ ^ 2 / (ε / 4) ^ 2 = 96 * η * (α * σ ^ 2) / ε ^ 2 by field_simp; ring]
  have hk1' : κ * L * η ≤ ε * g / 800 := by simp only [g]; linarith [k1]
  have hk2' : α ≤ g / 4 := by simp only [g]; linarith [k2]
  have hκη' : κ * η ≤ g * u / 80 := by simp only [g]; linarith [hκη]
  have hE2 : E = u ^ 2 := hs.symm
  have hκη2 : κ ^ 2 * η ^ 2 ≤ g ^ 2 * E / 6400 := by
    have := mul_le_mul hκη' hκη' (by positivity) (by positivity)
    calc κ ^ 2 * η ^ 2 = (κ * η) * (κ * η) := by ring
      _ ≤ (g * u / 80) * (g * u / 80) := this
      _ = g ^ 2 * E / 6400 := by rw [hE2]; ring
  have hCe : κ * (8 * η / ε) * L ≤ g / 100 := by
    rw [show κ * (8 * η / ε) * L = 8 * (κ * L * η) / ε by field_simp]
    rw [div_le_iff₀ hε]; linarith
  have hCe2 : (κ * (8 * η / ε) * L) ^ 2 ≤ g ^ 2 / 10000 := by
    have h0 : 0 ≤ κ * (8 * η / ε) * L := by positivity
    calc (κ * (8 * η / ε) * L) ^ 2 ≤ (g / 100) ^ 2 := pow_le_pow_left₀ h0 hCe 2
      _ = g ^ 2 / 10000 := by ring
  have hCh2L : (κ * (8 * η / ε)) ^ 2 * L ^ 2 ≤ g ^ 2 / 10000 := by
    rw [← mul_pow]; exact hCe2
  have hηα2 : η ^ 2 = α ^ 2 * E / (400 * K ^ 2) := by
    calc η ^ 2 = α ^ 2 * (η ^ 2 / α ^ 2) := by field_simp
      _ = α ^ 2 * (E / (400 * K ^ 2)) := by rw [hηα]
      _ = _ := by ring
  have hK4 : 4 ≤ K ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) h.K2 2
    norm_num at this; exact this
  have hη2E : κ ^ 2 * η ^ 2 * σ ^ 2 ≤ α * E * ε ^ 2 / 1600000 := by
    have hk2' : κ ^ 2 ≤ K ^ 2 := h.kK2
    calc κ ^ 2 * η ^ 2 * σ ^ 2 = κ ^ 2 * (α * E / (400 * K ^ 2)) * (α * σ ^ 2) := by rw [hηα2]; ring
      _ ≤ K ^ 2 * (α * E / (400 * K ^ 2)) * (ε ^ 2 / (4000 * K ^ 2)) := by gcongr
      _ ≤ α * E * ε ^ 2 / 1600000 := by
          rw [show K ^ 2 * (α * E / (400 * K ^ 2)) * (ε ^ 2 / (4000 * K ^ 2)) = α * E * ε ^ 2 / (1600000 * K ^ 2) by
            field_simp; ring]
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
          linarith
  have hC0 : κ * η + κ * (8 * η / ε) * (L * Real.sqrt (1 + κ ^ 2) * (η / α)) +
      (κ * (96 * η * (α * σ ^ 2) / ε ^ 2) + ρ / μ * (1 + κ ^ 2) * ((8 * η / ε) ^ 2 * σ ^ 2)) ≤ g * u / 10 := by
    have a1 : κ * (8 * η / ε) * (L * Real.sqrt (1 + κ ^ 2) * (η / α)) ≤ g * u / 2000 := by
      have e : κ * (8 * η / ε) * (L * Real.sqrt (1 + κ ^ 2) * (η / α)) =
          8 * (κ * L * η) * Real.sqrt (1 + κ ^ 2) * (η / α) / ε := by field_simp
      have hηdef : η = α * u / (20 * K) := rfl
      have hηa : η / α = u / (20 * K) := by rw [hηdef]; field_simp
      rw [e, hηa]
      calc 8 * (κ * L * η) * Real.sqrt (1 + κ ^ 2) * (u / (20 * K)) / ε
          ≤ 8 * (ε * g / 800) * K * (u / (20 * K)) / ε := by gcongr
        _ = g * u / 2000 := by field_simp; ring
    have a2 : κ * (96 * η * (α * σ ^ 2) / ε ^ 2) ≤ g * u / 2000 := by
      have : α * σ ^ 2 ≤ ε ^ 2 / 4000 := by
        refine hsq'.trans ?_
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num); nlinarith
      calc κ * (96 * η * (α * σ ^ 2) / ε ^ 2) = 96 * (κ * η) * (α * σ ^ 2) / ε ^ 2 := by ring
        _ ≤ 96 * (g * u / 80) * (ε ^ 2 / 4000) / ε ^ 2 := by gcongr
        _ ≤ g * u / 2000 := by
            rw [show 96 * (g * u / 80) * (ε ^ 2 / 4000) / ε ^ 2 = 96 * g * u / 320000 by field_simp; ring]
            have : 0 ≤ g * u := by positivity
            linarith
    have a3 : ρ / μ * (1 + κ ^ 2) * ((8 * η / ε) ^ 2 * σ ^ 2) ≤ g * u / 2000 := by
      have e : ρ / μ * (1 + κ ^ 2) * ((8 * η / ε) ^ 2 * σ ^ 2) =
          64 * (1 + κ ^ 2) * (ρ * u) * u * α * (α * σ ^ 2) / (400 * K ^ 2 * μ * ε ^ 2) := by
        rw [show (8 * η / ε) ^ 2 = 64 * η ^ 2 / ε ^ 2 by ring, hηα2, hE2]; field_simp
      rw [e]
      have hv1 : v * (α * σ ^ 2) ≤ ε ^ 2 / (8000 * K ^ 2) := by
        have : v * (α * σ ^ 2) ≤ (1 + ρ * ε * K / L ^ 2) / 2 * (α * σ ^ 2) := by gcongr
        have e2 : ε ^ 2 / (8000 * K ^ 2) = ε ^ 2 / (4000 * K ^ 2) / 2 := by field_simp; ring
        rw [e2]; nlinarith
      calc 64 * (1 + κ ^ 2) * (ρ * u) * u * α * (α * σ ^ 2) / (400 * K ^ 2 * μ * ε ^ 2)
          ≤ 64 * K ^ 2 * (v * L / (6 * K)) * u * (g / 4) * (α * σ ^ 2) / (400 * K ^ 2 * μ * ε ^ 2) := by
            gcongr
        _ = 64 * L * u * g * (v * (α * σ ^ 2)) / (9600 * K * μ * ε ^ 2) := by field_simp; ring
        _ ≤ 64 * (μ * K) * u * g * (ε ^ 2 / (8000 * K ^ 2)) / (9600 * K * μ * ε ^ 2) := by gcongr
        _ = g * u / (1200000 * K ^ 2) := by field_simp; ring
        _ ≤ g * u / 2000 := by
            apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
            linarith
    have a0 : κ * η ≤ g * u / 80 := hκη'
    have : 0 ≤ g * u := by positivity
    linarith
  have hC0sq : (κ * η + κ * (8 * η / ε) * (L * Real.sqrt (1 + κ ^ 2) * (η / α)) +
      (κ * (96 * η * (α * σ ^ 2) / ε ^ 2) + ρ / μ * (1 + κ ^ 2) * ((8 * η / ε) ^ 2 * σ ^ 2))) ^ 2 ≤
      g ^ 2 * E / 100 := by
    have h0 : 0 ≤ κ * η + κ * (8 * η / ε) * (L * Real.sqrt (1 + κ ^ 2) * (η / α)) +
        (κ * (96 * η * (α * σ ^ 2) / ε ^ 2) + ρ / μ * (1 + κ ^ 2) * ((8 * η / ε) ^ 2 * σ ^ 2)) := by positivity
    have := mul_le_mul hC0 hC0 h0 (by positivity)
    rw [pow_two]; refine this.trans (le_of_eq ?_); rw [hE2]; ring
  have hDsq : D ^ 2 ≤ (ε / 16000) ^ 2 := pow_le_pow_left₀ hD0 hDD 2
  have hP1 : (κ * (8 * η / ε)) ^ 2 * (4 * D ^ 2) ≤ g ^ 2 * E / 1000000 := by
    have e : (κ * (8 * η / ε)) ^ 2 = 64 * (κ ^ 2 * η ^ 2) / ε ^ 2 := by field_simp; ring
    rw [e]
    calc 64 * (κ ^ 2 * η ^ 2) / ε ^ 2 * (4 * D ^ 2) ≤ 64 * (g ^ 2 * E / 6400) / ε ^ 2 * (4 * (ε / 16000) ^ 2) := by
          gcongr
      _ ≤ g ^ 2 * E / 1000000 := by
          rw [show 64 * (g ^ 2 * E / 6400) / ε ^ 2 * (4 * (ε / 16000) ^ 2) = g ^ 2 * E / 6400000000 by field_simp; ring]
          have : 0 ≤ g ^ 2 * E := by positivity
          linarith
  have hP2 : (κ * (8 * η / ε)) ^ 2 * (2 * α * σ ^ 2) ≤ g ^ 2 * E / 100000 := by
    have e : (κ * (8 * η / ε)) ^ 2 * (2 * α * σ ^ 2) = 128 * (κ ^ 2 * η ^ 2 * σ ^ 2) * α / ε ^ 2 := by
      field_simp; ring
    rw [e]
    calc 128 * (κ ^ 2 * η ^ 2 * σ ^ 2) * α / ε ^ 2 ≤ 128 * (α * E * ε ^ 2 / 1600000) * (g / 4) / ε ^ 2 := by gcongr
      _ = 128 * α * E * g / 6400000 := by field_simp; ring
      _ ≤ 128 * (g / 4) * E * g / 6400000 := by gcongr
      _ ≤ g ^ 2 * E / 100000 := by
          have : 0 ≤ g ^ 2 * E := by positivity
          linarith
  have hA1 : 2 * γ ^ 2 * σ ^ 2 * g ≤ g ^ 2 * E / 10 := by
    have : 2 * γ ^ 2 * σ ^ 2 * g = g * γ * (20 * γ * σ ^ 2) / 10 := by ring
    rw [this]
    calc g * γ * (20 * γ * σ ^ 2) / 10 ≤ g * γ * (μ * E) / 10 := by gcongr
      _ = g ^ 2 * E / 10 := by simp only [g]; ring
  have hA2 : 2 * κ ^ 2 * ((8 * η / ε) ^ 2 * σ ^ 2) * g ≤ g ^ 2 * E / 10000 := by
    have e : 2 * κ ^ 2 * ((8 * η / ε) ^ 2 * σ ^ 2) * g = 128 * (κ ^ 2 * η ^ 2 * σ ^ 2) * g / ε ^ 2 := by
      field_simp; ring
    rw [e]
    calc 128 * (κ ^ 2 * η ^ 2 * σ ^ 2) * g / ε ^ 2 ≤ 128 * (α * E * ε ^ 2 / 1600000) * g / ε ^ 2 := by gcongr
      _ = 128 * α * E * g / 1600000 := by field_simp
      _ ≤ 128 * (g / 4) * E * g / 1600000 := by gcongr
      _ ≤ g ^ 2 * E / 10000 := by
          have : 0 ≤ g ^ 2 * E := by positivity
          linarith
  have goal_mul : 9 / g * (κ * (8 * η / ε) * L) ^ 2 * E +
      9 / g * (κ * (8 * η / ε)) ^ 2 * (4 * L ^ 2 * E + 4 * D ^ 2 + 2 * α * σ ^ 2) +
      (2 * γ ^ 2 * σ ^ 2 + 2 * κ ^ 2 * ((8 * η / ε) ^ 2 * σ ^ 2) +
        9 / g * (κ * η + κ * (8 * η / ε) * (L * Real.sqrt (1 + κ ^ 2) * (η / α)) +
          (κ * (96 * η * (α * σ ^ 2) / ε ^ 2) + ρ / μ * (1 + κ ^ 2) * ((8 * η / ε) ^ 2 * σ ^ 2))) ^ 2) ≤
      g * E / 2 := by
    rw [← mul_le_mul_iff_of_pos_left hg]
    have e : g * (9 / g * (κ * (8 * η / ε) * L) ^ 2 * E +
      9 / g * (κ * (8 * η / ε)) ^ 2 * (4 * L ^ 2 * E + 4 * D ^ 2 + 2 * α * σ ^ 2) +
      (2 * γ ^ 2 * σ ^ 2 + 2 * κ ^ 2 * ((8 * η / ε) ^ 2 * σ ^ 2) +
        9 / g * (κ * η + κ * (8 * η / ε) * (L * Real.sqrt (1 + κ ^ 2) * (η / α)) +
          (κ * (96 * η * (α * σ ^ 2) / ε ^ 2) + ρ / μ * (1 + κ ^ 2) * ((8 * η / ε) ^ 2 * σ ^ 2))) ^ 2)) =
      9 * (κ * (8 * η / ε) * L) ^ 2 * E + 36 * ((κ * (8 * η / ε)) ^ 2 * L ^ 2) * E +
        9 * ((κ * (8 * η / ε)) ^ 2 * (4 * D ^ 2)) + 9 * ((κ * (8 * η / ε)) ^ 2 * (2 * α * σ ^ 2)) +
        2 * γ ^ 2 * σ ^ 2 * g + 2 * κ ^ 2 * ((8 * η / ε) ^ 2 * σ ^ 2) * g +
        9 * (κ * η + κ * (8 * η / ε) * (L * Real.sqrt (1 + κ ^ 2) * (η / α)) +
          (κ * (96 * η * (α * σ ^ 2) / ε ^ 2) + ρ / μ * (1 + κ ^ 2) * ((8 * η / ε) ^ 2 * σ ^ 2))) ^ 2 := by
      field_simp; ring
    rw [e]
    have : 0 ≤ g ^ 2 * E := by positivity
    have b1 : 9 * (κ * (8 * η / ε) * L) ^ 2 * E ≤ 9 * (g ^ 2 / 10000) * E := by gcongr
    have b2 : 36 * ((κ * (8 * η / ε)) ^ 2 * L ^ 2) * E ≤ 36 * (g ^ 2 / 10000) * E := by gcongr
    linarith [hP1, hP2, hA1, hA2, hC0sq]
  have hcoef : 9 / (γ * μ) = 9 / g := rfl
  rw [hcoef]
  linarith [goal_mul]

lemma c2 (G : ℝ) (T : ℕ) :
    (1 - (tCfg L μ ρ σ ε G T).α) * tPs L μ ρ σ ε + 4 * (tCfg L μ ρ σ ε G T).α * L ^ 2 * tEs L μ ρ σ ε +
      (4 * kDD L μ ρ (tCfg L μ ρ σ ε G T) ^ 2 / (tCfg L μ ρ σ ε G T).α +
        (tCfg L μ ρ σ ε G T).α ^ 2 * σ ^ 2) ≤ tPs L μ ρ σ ε := by
  have hα := h.α0
  simp only [tCfg, kDD, tPs]
  set α := tα L μ ρ σ ε
  have e : 4 * (ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * tη L μ ρ σ ε ^ 2 / α) ^ 2 / α =
      α * (4 * (ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * tη L μ ρ σ ε ^ 2 / α / α) ^ 2) := by
    field_simp
  rw [e]
  have : 0 ≤ α ^ 2 * σ ^ 2 := by positivity
  nlinarith

omit h in
lemma pow_le_inv {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) : (1 - x) ^ n * (1 + n * x) ≤ 1 := by
  have hb := one_add_mul_le_pow (show -2 ≤ x by linarith) n
  have h1 : (1 - x) ^ n * (1 + x) ^ n ≤ 1 := by
    rw [← mul_pow]; apply pow_le_one₀ (by nlinarith) (by nlinarith)
  have h2 : 0 ≤ (1 - x) ^ n := pow_nonneg (by linarith) n
  calc (1 - x) ^ n * (1 + n * x) ≤ (1 - x) ^ n * (1 + x) ^ n := by gcongr
    _ ≤ 1 := h1

lemma γμ1 : tγ L μ ρ σ ε * μ ≤ 1 := by
  have h1 : tγ L μ ρ σ ε * μ ≤ μ / L ^ 2 * μ := mul_le_mul_of_nonneg_right h.γ1 h.μ0.le
  have h2 : μ / L ^ 2 * μ ≤ 1 := by
    have := h.L0; have := h.μ0
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]; nlinarith [h.μL]
  linarith

lemma hA (G : ℝ) (T : ℕ) :
    (1 - (tCfg L μ ρ σ ε G T).γ * μ) ^ (tCfg L μ ρ σ ε G T).NA * (G / μ) ^ 2 +
      (tCfg L μ ρ σ ε G T).γ ^ 2 * σ ^ 2 / (1 - (1 - (tCfg L μ ρ σ ε G T).γ * μ)) ≤ 2 * tEs L μ ρ σ ε := by
  have hγ := h.γ0
  have hμ := h.μ0
  have hE := h.Es0
  have hσ := h.γσ
  have h1 := h.γμ1
  simp only [tCfg]
  set γ := tγ L μ ρ σ ε
  set E := tEs L μ ρ σ ε
  set N := ⌈Real.log (1 + G ^ 2 / μ ^ 2 * tQ L μ ρ σ ε) / (γ * μ)⌉₊
  have hN : Real.log (1 + G ^ 2 / μ ^ 2 * tQ L μ ρ σ ε) / (γ * μ) ≤ N := Nat.le_ceil _
  have hQ := h.Q0
  have hEQ := h.EsQ
  set a := G ^ 2 / μ ^ 2 * tQ L μ ρ σ ε
  have ha : 0 ≤ a := by positivity
  have t1 : (1 - γ * μ) ^ N * (G / μ) ^ 2 ≤ E := by
    have e1 : 1 - γ * μ ≤ Real.exp (-(γ * μ)) := by linarith [Real.add_one_le_exp (-(γ * μ))]
    have e2 : (1 - γ * μ) ^ N ≤ Real.exp (-(γ * μ)) ^ N := pow_le_pow_left₀ (by linarith) e1 N
    rw [← Real.exp_nat_mul] at e2
    have e3 : Real.exp (N * -(γ * μ)) ≤ Real.exp (-Real.log (1 + a)) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ (by positivity)] at hN; linarith
    rw [Real.exp_neg, Real.exp_log (by linarith)] at e3
    have hGa : (G / μ) ^ 2 = a * E := by
      simp only [a]; field_simp
      calc G ^ 2 = G ^ 2 * (E * tQ L μ ρ σ ε) := by rw [hEQ, mul_one]
        _ = _ := by ring
    have hq : 0 ≤ (1 - γ * μ) ^ N := pow_nonneg (by linarith) N
    calc (1 - γ * μ) ^ N * (G / μ) ^ 2 ≤ (1 + a)⁻¹ * (a * E) := by
          rw [hGa]; exact mul_le_mul_of_nonneg_right (e2.trans e3) (by positivity)
      _ ≤ E := by
          rw [inv_mul_le_iff₀ (by linarith)]; nlinarith
  have t2 : γ ^ 2 * σ ^ 2 / (1 - (1 - γ * μ)) ≤ E := by
    rw [show 1 - (1 - γ * μ) = γ * μ by ring, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

lemma hC (G : ℝ) (T : ℕ) :
    (1 - (tCfg L μ ρ σ ε G T).γ * μ) ^ (tCfg L μ ρ σ ε G T).NC * (2 * (2 * tEs L μ ρ σ ε) +
      2 * ((L / μ) * ((tCfg L μ ρ σ ε G T).η / (tCfg L μ ρ σ ε G T).α)) ^ 2) +
      (tCfg L μ ρ σ ε G T).γ ^ 2 * σ ^ 2 / (1 - (1 - (tCfg L μ ρ σ ε G T).γ * μ)) ≤ tEs L μ ρ σ ε := by
  have hγ := h.γ0
  have hμ := h.μ0
  have hE := h.Es0
  have hσ := h.γσ
  have h1 := h.γμ1
  have hK := h.K0
  have hk := (kK (L := L) (μ := μ))
  have hα := h.α0
  have hs := Real.sq_sqrt hE.le
  simp only [tCfg]
  set γ := tγ L μ ρ σ ε
  set E := tEs L μ ρ σ ε
  set N := ⌈4 / (γ * μ)⌉₊
  have hN : 4 / (γ * μ) ≤ N := Nat.le_ceil _
  have hp := pow_le_inv (show 0 ≤ γ * μ by positivity) h1 N
  have h5 : (1 - γ * μ) ^ N * 5 ≤ 1 := by
    have : 4 ≤ N * (γ * μ) := by rwa [div_le_iff₀ (by positivity)] at hN
    have hq : 0 ≤ (1 - γ * μ) ^ N := pow_nonneg (by linarith) N
    nlinarith
  have hκ : ((L / μ) * (tη L μ ρ σ ε / tα L μ ρ σ ε)) ^ 2 ≤ E / 400 := by
    have e : tη L μ ρ σ ε / tα L μ ρ σ ε = Real.sqrt E / (20 * tK L μ) := by unfold tη; field_simp; rfl
    rw [e]
    have hk0 : 0 ≤ L / μ := by have := h.L0; positivity
    have : (L / μ) * (Real.sqrt E / (20 * tK L μ)) ≤ Real.sqrt E / 20 := by
      rw [show (L / μ) * (Real.sqrt E / (20 * tK L μ)) = (L / μ / tK L μ) * (Real.sqrt E / 20) by field_simp]
      have : L / μ / tK L μ ≤ 1 := by rw [div_le_one hK]; exact hk
      have : 0 ≤ Real.sqrt E / 20 := by positivity
      nlinarith
    calc ((L / μ) * (Real.sqrt E / (20 * tK L μ))) ^ 2 ≤ (Real.sqrt E / 20) ^ 2 :=
          pow_le_pow_left₀ (by positivity) this 2
      _ = E / 400 := by rw [div_pow, hs]; ring
  have t2 : γ ^ 2 * σ ^ 2 / (1 - (1 - γ * μ)) ≤ E / 20 := by
    rw [show 1 - (1 - γ * μ) = γ * μ by ring, div_le_iff₀ (by positivity)]
    nlinarith
  have hq : 0 ≤ (1 - γ * μ) ^ N := pow_nonneg (by linarith) N
  have t1 : (1 - γ * μ) ^ N * (2 * (2 * E) + 2 * ((L / μ) * (tη L μ ρ σ ε / tα L μ ρ σ ε)) ^ 2) ≤
      (1 - γ * μ) ^ N * (5 * E) := by
    gcongr; linarith
  nlinarith

lemma hB (G : ℝ) (T : ℕ) :
    2 * σ ^ 2 / (tCfg L μ ρ σ ε G T).NB + 2 * L ^ 2 * (2 * tEs L μ ρ σ ε) ≤ tPs L μ ρ σ ε := by
  have hα := h.α0
  have hM := h.M0
  have haM := h.αM
  simp only [tCfg, tPs]
  have hN : 4000 * tM L μ ρ σ ε ≤ ⌈4000 * tM L μ ρ σ ε⌉₊ := Nat.le_ceil _
  have hN0 : (0 : ℝ) < ⌈4000 * tM L μ ρ σ ε⌉₊ := by linarith
  have : 2 * σ ^ 2 / ⌈4000 * tM L μ ρ σ ε⌉₊ ≤ 2 * tα L μ ρ σ ε * σ ^ 2 := by
    rw [div_le_iff₀ hN0]
    have h2 : 2 * tα L μ ρ σ ε * σ ^ 2 * (4000 * tM L μ ρ σ ε) = 2 * σ ^ 2 := by
      rw [show 2 * tα L μ ρ σ ε * σ ^ 2 * (4000 * tM L μ ρ σ ε) = 2 * σ ^ 2 * (tα L μ ρ σ ε * (4000 * tM L μ ρ σ ε)) by ring,
        haM, mul_one]
    have : 0 ≤ 2 * tα L μ ρ σ ε * σ ^ 2 := by positivity
    nlinarith
  have : 0 ≤ 4 * (ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * tη L μ ρ σ ε ^ 2 / tα L μ ρ σ ε / tα L μ ρ σ ε) ^ 2 := by
    positivity
  linarith

lemma NB1 (G : ℝ) (T : ℕ) : 1 ≤ (tCfg L μ ρ σ ε G T).NB := by
  simp only [tCfg]
  have := h.M1
  exact Nat.one_le_iff_ne_zero.mpr (by
    intro h0; rw [Nat.ceil_eq_zero] at h0; linarith)

lemma cfgOK (G : ℝ) (T : ℕ) : CfgOK (tCfg L μ ρ σ ε G T) L μ where
  α0 := h.α0
  α1 := by have := h.α1; simp only [tCfg]; linarith
  γ0 := h.γ0
  γ1 := h.γ1
  l0 := by simp only [tCfg]; have := h.ε0; positivity
  η0 := by simp only [tCfg, tη]; have := h.α0; have := h.K0; positivity

lemma η0 : 0 < tη L μ ρ σ ε := by
  unfold tη; have := h.α0; have := h.K0; have := Real.sqrt_pos.mpr h.Es0; positivity

set_option maxHeartbeats 1000000 in
lemma stat (G : ℝ) (T : ℕ) :
    L * (L / μ + 1 / 2) * (tCfg L μ ρ σ ε G T).η +
      2 * (Real.sqrt ((tCfg L μ ρ σ ε G T).α * ((1 + (L / μ) ^ 2) * σ ^ 2)) +
        (kq0 L μ ρ (tCfg L μ ρ σ ε G T) + kq1 L μ ρ (tCfg L μ ρ σ ε G T) * Real.sqrt (tEs L μ ρ σ ε) +
          kq2 L μ ρ (tCfg L μ ρ σ ε G T) * tEs L μ ρ σ ε) / (1 - (1 - (tCfg L μ ρ σ ε G T).α)) +
        (4 * (L / μ) ^ 2 * (tCfg L μ ρ σ ε G T).η / (tCfg L μ ρ σ ε G T).γ +
          (tCfg L μ ρ σ ε G T).α / (tCfg L μ ρ σ ε G T).γ * (L / μ) * Real.sqrt (tEs L μ ρ σ ε))) ≤ ε / 2 := by
  have hρ := h.ρ0
  have hε := h.ε0
  have hσ := h.σ0
  have hμ := h.μ0
  have hL := h.L0
  have hK := h.K0
  have hγ := h.γ0
  have hα := h.α0
  have hE := h.Es0
  have hs := Real.sq_sqrt hE.le
  have hu := Real.sqrt_pos.mpr hE
  have k1 := h.key1
  have k2 := h.key2
  have hb3 := h.b3
  have hsq' := h.αsq'
  have hs2 := h.s2K
  have hk2 := h.k2K
  have hDD := h.DDa
  have h40 := h.Esρ
  have hLu := h.Lu
  have hae := h.αe
  have hkK := (kK (L := L) (μ := μ))
  have hK4 : 4 ≤ tK L μ ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) h.K2 2
    norm_num at this; exact this
  simp only [tCfg, kq0, kq1, kq2]
  set α := tα L μ ρ σ ε
  set γ := tγ L μ ρ σ ε
  set η := tη L μ ρ σ ε
  set E := tEs L μ ρ σ ε
  set K := tK L μ
  set u := Real.sqrt E
  set κ := L / μ
  have hk0 : 0 ≤ κ := by positivity
  have hηdef : η = α * u / (20 * K) := rfl
  have hη0 : 0 ≤ η := by rw [hηdef]; positivity
  have hE2 : E = u ^ 2 := hs.symm
  have hKk : 1 + κ = K := rfl
  have hag : α / (γ * μ) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hρKE : 0 ≤ ρ * K * E := by positivity
  have hag' := mul_le_mul_of_nonneg_left hag hρKE
  rw [show 1 - (1 - α) = α by ring, hKk]
  have s1 : Real.sqrt (α * ((1 + κ ^ 2) * σ ^ 2)) ≤ ε / 60 := by
    rw [Real.sqrt_le_left (by positivity)]
    have : α * σ ^ 2 ≤ ε ^ 2 / (4000 * K ^ 2) := hsq'
    calc α * ((1 + κ ^ 2) * σ ^ 2) = (1 + κ ^ 2) * (α * σ ^ 2) := by ring
      _ ≤ K ^ 2 * (α * σ ^ 2) := mul_le_mul_of_nonneg_right hk2 (by positivity)
      _ ≤ K ^ 2 * (ε ^ 2 / (4000 * K ^ 2)) := by gcongr
      _ ≤ (ε / 60) ^ 2 := by rw [show K ^ 2 * (ε ^ 2 / (4000 * K ^ 2)) = ε ^ 2 / 4000 by field_simp]; nlinarith
  have s2 : 4 * κ ^ 2 * η / γ ≤ ε / 200 := by
    rw [div_le_iff₀ hγ]
    have e : 4 * κ ^ 2 * η = 4 * (κ * L * η) / μ := by simp only [κ]; field_simp
    rw [e, div_le_iff₀ hμ]
    linarith
  have s3 : α / γ * κ * u ≤ ε / 40 := by
    have : α / γ * κ * u = κ * α * u / γ := by ring
    rw [this]; exact hb3
  have s4 : α * (ρ * K) * E / α ≤ ε / 40 := by
    rw [show α * (ρ * K) * E / α = ρ * K * E by field_simp]; linarith
  have s5a : ρ * K * Real.sqrt (1 + κ ^ 2) * η * u / α ≤ ε / 800 := by
    calc ρ * K * Real.sqrt (1 + κ ^ 2) * η * u / α ≤ ρ * K * K * η * u / α := by gcongr
      _ = ρ * K * E / 20 := by rw [hηdef, hE2]; field_simp
      _ ≤ ε / 800 := by linarith
  have s5b : α / γ * (ρ / μ * K * Real.sqrt (1 + κ ^ 2) * η) * u / α ≤ ε / 3200 := by
    calc α / γ * (ρ / μ * K * Real.sqrt (1 + κ ^ 2) * η) * u / α ≤ α / γ * (ρ / μ * K * K * η) * u / α := by
          gcongr
      _ = ρ * K * E * (α / (γ * μ)) / 20 := by rw [hηdef, hE2]; field_simp
      _ ≤ ρ * K * E * (1 / 4) / 20 := by linarith
      _ ≤ ε / 3200 := by linarith
  have s5c : α / γ * (α * κ) * u / α = α / γ * κ * u := by field_simp
  have s6a : ρ * K * (1 + κ ^ 2) * η ^ 2 / α / α ≤ ε / 16000 := hDD
  have s6b : α / γ * (ρ / μ * K * Real.sqrt (1 + κ ^ 2) * η) * (4 * κ * η / α) / α ≤ ε / 16000 := by
    have hκK : κ ≤ K := hkK
    calc α / γ * (ρ / μ * K * Real.sqrt (1 + κ ^ 2) * η) * (4 * κ * η / α) / α
        ≤ α / γ * (ρ / μ * K * K * η) * (4 * K * η / α) / α := by gcongr
      _ = ρ * K * E * (α / (γ * μ)) / 100 := by rw [hηdef, hE2]; field_simp; ring
      _ ≤ ρ * K * E * (1 / 4) / 100 := by linarith
      _ ≤ ε / 16000 := by linarith
  have s0 : L * (κ + 1 / 2) * η ≤ ε / 20000 := by
    calc L * (κ + 1 / 2) * η ≤ L * K * η := by gcongr; rw [← hKk]; linarith
      _ = α * (L * u) / 20 := by rw [hηdef]; field_simp
      _ ≤ α * (ε + 5 * σ) / 20 := by gcongr
      _ ≤ ε / (1000 * K ^ 2) / 20 := by gcongr
      _ ≤ ε / 20000 := by
          rw [div_div]; apply div_le_div_of_nonneg_left hε.le (by norm_num); nlinarith
  have split : (ρ * K * (1 + κ ^ 2) * η ^ 2 / α + α / γ * (ρ / μ * K * Real.sqrt (1 + κ ^ 2) * η) * (4 * κ * η / α) +
      (ρ * K * Real.sqrt (1 + κ ^ 2) * η + α / γ * (ρ / μ * K * Real.sqrt (1 + κ ^ 2) * η + α * κ)) * u +
      α * (ρ * K) * E) / α =
      ρ * K * (1 + κ ^ 2) * η ^ 2 / α / α + α / γ * (ρ / μ * K * Real.sqrt (1 + κ ^ 2) * η) * (4 * κ * η / α) / α +
      ρ * K * Real.sqrt (1 + κ ^ 2) * η * u / α + α / γ * (ρ / μ * K * Real.sqrt (1 + κ ^ 2) * η) * u / α +
      α / γ * (α * κ) * u / α + α * (ρ * K) * E / α := by
    field_simp; ring
  rw [split, s5c]
  linarith

lemma R0b : Real.sqrt (tPs L μ ρ σ ε) + tα L μ ρ σ ε / tγ L μ ρ σ ε * (L / μ) * Real.sqrt (tEs L μ ρ σ ε) ≤
    3 * ε + 10 * σ := by
  have hε := h.ε0
  have hσ := h.σ0
  have hE := h.Es0
  have hs := Real.sq_sqrt hE.le
  have hb3 := h.b3
  have hLu := h.Lu
  have hDD := h.DDa
  have hsq' := h.αsq'
  have hK4 : 4 ≤ tK L μ ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) h.K2 2
    norm_num at this; exact this
  have hP : Real.sqrt (tPs L μ ρ σ ε) ≤ 2.5 * ε + 10 * σ := by
    rw [Real.sqrt_le_left (by positivity)]
    unfold tPs
    set D := ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * tη L μ ρ σ ε ^ 2 / tα L μ ρ σ ε / tα L μ ρ σ ε
    have hD0 : 0 ≤ D := by
      simp only [D]; have := h.ρ0; have := h.α0; have := h.L0; have := h.μ0; positivity
    have h1 : 4 * L ^ 2 * tEs L μ ρ σ ε ≤ 4 * (ε + 5 * σ) ^ 2 := by
      have : (L * Real.sqrt (tEs L μ ρ σ ε)) ^ 2 ≤ (ε + 5 * σ) ^ 2 :=
        pow_le_pow_left₀ (by have := h.L0; positivity) hLu 2
      rw [mul_pow, hs] at this; linarith
    have h2 : 4 * D ^ 2 ≤ ε ^ 2 := by
      have := pow_le_pow_left₀ hD0 hDD 2; nlinarith
    have h3 : 2 * tα L μ ρ σ ε * σ ^ 2 ≤ ε ^ 2 := by
      have : tα L μ ρ σ ε * σ ^ 2 ≤ ε ^ 2 / 16000 := by
        refine hsq'.trans ?_
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num); nlinarith
      nlinarith
    nlinarith
  have : tα L μ ρ σ ε / tγ L μ ρ σ ε * (L / μ) * Real.sqrt (tEs L μ ρ σ ε) ≤ ε / 40 := by
    have e : tα L μ ρ σ ε / tγ L μ ρ σ ε * (L / μ) * Real.sqrt (tEs L μ ρ σ ε) =
        (L / μ) * tα L μ ρ σ ε * Real.sqrt (tEs L μ ρ σ ε) / tγ L μ ρ σ ε := by ring
    rw [e]; exact hb3
  linarith

lemma hfin (G Δ : ℝ) (hΔ : 0 ≤ Δ) (T : ℕ)
    (hT : 8 * Δ / (ε * tη L μ ρ σ ε) + 16 * (3 * ε + 10 * σ) / (ε * tα L μ ρ σ ε) ≤ T + 1) :
    Δ / (tCfg L μ ρ σ ε G T).η + ((tCfg L μ ρ σ ε G T).T + 1) *
        ((tCfg L μ ρ σ ε G T).lam + L * (L / μ + 1 / 2) * (tCfg L μ ρ σ ε G T).η) +
      2 * (((tCfg L μ ρ σ ε G T).T + 1) * (Real.sqrt ((tCfg L μ ρ σ ε G T).α * ((1 + (L / μ) ^ 2) * σ ^ 2)) +
        (kq0 L μ ρ (tCfg L μ ρ σ ε G T) + kq1 L μ ρ (tCfg L μ ρ σ ε G T) * Real.sqrt (tEs L μ ρ σ ε) +
          kq2 L μ ρ (tCfg L μ ρ σ ε G T) * tEs L μ ρ σ ε) / (1 - (1 - (tCfg L μ ρ σ ε G T).α)) +
        (4 * (L / μ) ^ 2 * (tCfg L μ ρ σ ε G T).η / (tCfg L μ ρ σ ε G T).γ +
          (tCfg L μ ρ σ ε G T).α / (tCfg L μ ρ σ ε G T).γ * (L / μ) * Real.sqrt (tEs L μ ρ σ ε))) +
        (Real.sqrt (tPs L μ ρ σ ε) + (tCfg L μ ρ σ ε G T).α / (tCfg L μ ρ σ ε G T).γ * (L / μ) *
          Real.sqrt (tEs L μ ρ σ ε)) / (tCfg L μ ρ σ ε G T).α) ≤ ((tCfg L μ ρ σ ε G T).T + 1) * ε := by
  have hst := h.stat G T
  have hR := h.R0b
  have hε := h.ε0
  have hσ := h.σ0
  have hη := h.η0
  have hα := h.α0
  set B := Real.sqrt ((tCfg L μ ρ σ ε G T).α * ((1 + (L / μ) ^ 2) * σ ^ 2)) +
        (kq0 L μ ρ (tCfg L μ ρ σ ε G T) + kq1 L μ ρ (tCfg L μ ρ σ ε G T) * Real.sqrt (tEs L μ ρ σ ε) +
          kq2 L μ ρ (tCfg L μ ρ σ ε G T) * tEs L μ ρ σ ε) / (1 - (1 - (tCfg L μ ρ σ ε G T).α)) +
        (4 * (L / μ) ^ 2 * (tCfg L μ ρ σ ε G T).η / (tCfg L μ ρ σ ε G T).γ +
          (tCfg L μ ρ σ ε G T).α / (tCfg L μ ρ σ ε G T).γ * (L / μ) * Real.sqrt (tEs L μ ρ σ ε))
  simp only [tCfg] at hst ⊢
  set R0 := Real.sqrt (tPs L μ ρ σ ε) + tα L μ ρ σ ε / tγ L μ ρ σ ε * (L / μ) * Real.sqrt (tEs L μ ρ σ ε)
  have hT1 : (0 : ℝ) < T + 1 := by positivity
  have h1 : Δ / tη L μ ρ σ ε ≤ (T + 1) * ε / 8 := by
    have : 8 * Δ / (ε * tη L μ ρ σ ε) ≤ T + 1 := by
      have : 0 ≤ 16 * (3 * ε + 10 * σ) / (ε * tα L μ ρ σ ε) := by positivity
      linarith
    rw [div_le_iff₀ (by positivity)] at this
    rw [div_le_iff₀ hη]; nlinarith
  have h2 : R0 / tα L μ ρ σ ε ≤ (T + 1) * ε / 16 := by
    have : 16 * (3 * ε + 10 * σ) / (ε * tα L μ ρ σ ε) ≤ T + 1 := by
      have : 0 ≤ 8 * Δ / (ε * tη L μ ρ σ ε) := by positivity
      linarith
    rw [div_le_iff₀ (by positivity)] at this
    rw [div_le_iff₀ hα]; nlinarith
  nlinarith

set_option maxHeartbeats 2000000 in
lemma budget_ok (G Δ : ℝ) (hΔ : 0 ≤ Δ) (T : ℕ) :
    ((tCfg L μ ρ σ ε G T).NA : ℝ) + (tCfg L μ ρ σ ε G T).NB + (tCfg L μ ρ σ ε G T).NC +
        (8 * Δ / (ε * tη L μ ρ σ ε) + 16 * (3 * ε + 10 * σ) / (ε * tα L μ ρ σ ε)) + 1 ≤
      10 ^ 6 * (1 + L / μ) ^ 2 * (1 + σ ^ 2 / ε ^ 2) * (1 + ρ * ε * (1 + L / μ) / L ^ 2) *
        ((1 + L / μ) * Δ / ε * Real.sqrt (40 * ρ * (1 + L / μ) / ε + L ^ 2 / (ε ^ 2 + 20 * σ ^ 2)) + 1 +
          σ / ε + Real.log (1 + G ^ 2 / μ ^ 2 * (40 * ρ * (1 + L / μ) / ε + L ^ 2 / (ε ^ 2 + 20 * σ ^ 2)))) := by
  have hρ := h.ρ0
  have hε := h.ε0
  have hσ := h.σ0
  have hμ := h.μ0
  have hL := h.L0
  have hK := h.K0
  have hγ := h.γ0
  have hα := h.α0
  have hE := h.Es0
  have hQ := h.Q0
  have hM := h.M0
  have hM4 := h.M1
  have haM := h.αM
  have hg := h.γinv
  have hEQ := h.EsQ
  have hkK := h.kK2
  simp only [tCfg]
  set α := tα L μ ρ σ ε
  set γ := tγ L μ ρ σ ε
  set E := tEs L μ ρ σ ε
  set Q := tQ L μ ρ σ ε
  set M := tM L μ ρ σ ε
  set K := tK L μ
  set κ := L / μ
  have hQdef : Q = 40 * ρ * (1 + L / μ) / ε + L ^ 2 / (ε ^ 2 + 20 * σ ^ 2) := rfl
  have hMdef : M = (1 + L / μ) ^ 2 * (1 + σ ^ 2 / ε ^ 2) * (1 + ρ * ε * (1 + L / μ) / L ^ 2) := rfl
  rw [show (10 : ℝ) ^ 6 * (1 + κ) ^ 2 * (1 + σ ^ 2 / ε ^ 2) * (1 + ρ * ε * (1 + κ) / L ^ 2) = 10 ^ 6 * M by
      rw [hMdef]; ring,
    show 1 + κ = K from rfl]
  have hEinv : 1 / E = Q := by rw [div_eq_iff hE.ne']; linarith
  have hγinv : 1 / γ = L ^ 2 / μ + 20 * σ ^ 2 * Q / μ := by
    have h20 : 20 * σ ^ 2 / (μ * E) = 20 * σ ^ 2 * Q / μ := by rw [← hEinv]; field_simp
    rw [div_eq_iff hγ.ne', ← h20, mul_comm]; exact hg.symm
  have hu : Real.sqrt E * Real.sqrt Q = 1 := by
    rw [← Real.sqrt_mul hE.le, hEQ, Real.sqrt_one]
  have hu0 : 0 < Real.sqrt E := Real.sqrt_pos.mpr hE
  have hS : σ ^ 2 * Q / μ ^ 2 ≤ 41 * M := by
    rw [hQdef, hMdef]
    have e : σ ^ 2 * (40 * ρ * (1 + L / μ) / ε + L ^ 2 / (ε ^ 2 + 20 * σ ^ 2)) / μ ^ 2 =
        40 * (κ ^ 2 * (σ ^ 2 / ε ^ 2) * (ρ * ε * (1 + L / μ) / L ^ 2)) + κ ^ 2 * (σ ^ 2 / (ε ^ 2 + 20 * σ ^ 2)) := by
      simp only [κ]; field_simp
    rw [e]
    have hk2 : κ ^ 2 ≤ (1 + L / μ) ^ 2 := hkK
    have hs0 : 0 ≤ σ ^ 2 / ε ^ 2 := by positivity
    have hv0 : 0 ≤ ρ * ε * (1 + L / μ) / L ^ 2 := by positivity
    have a1 : κ ^ 2 * (σ ^ 2 / ε ^ 2) * (ρ * ε * (1 + L / μ) / L ^ 2) ≤
        (1 + L / μ) ^ 2 * (1 + σ ^ 2 / ε ^ 2) * (1 + ρ * ε * (1 + L / μ) / L ^ 2) := by
      gcongr <;> linarith
    have a2 : κ ^ 2 * (σ ^ 2 / (ε ^ 2 + 20 * σ ^ 2)) ≤ (1 + L / μ) ^ 2 * (1 + σ ^ 2 / ε ^ 2) * (1 + ρ * ε * (1 + L / μ) / L ^ 2) := by
      have : σ ^ 2 / (ε ^ 2 + 20 * σ ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      calc κ ^ 2 * (σ ^ 2 / (ε ^ 2 + 20 * σ ^ 2)) ≤ (1 + L / μ) ^ 2 * 1 * 1 := by
            rw [mul_one, mul_one]; calc κ ^ 2 * (σ ^ 2 / (ε ^ 2 + 20 * σ ^ 2)) ≤ κ ^ 2 * 1 := by gcongr
              _ ≤ _ := by linarith
        _ ≤ _ := by gcongr <;> linarith
    linarith
  have hkM : κ ^ 2 ≤ M := by
    rw [hMdef]
    have hKK : K ^ 2 = (1 + L / μ) ^ 2 := rfl
    calc κ ^ 2 ≤ (1 + L / μ) ^ 2 * 1 * 1 := by linarith [hkK]
      _ ≤ _ := by
          have : 0 ≤ σ ^ 2 / ε ^ 2 := by positivity
          have : 0 ≤ ρ * ε * (1 + L / μ) / L ^ 2 := by positivity
          gcongr <;> linarith
  have hGQ : 0 ≤ G ^ 2 / μ ^ 2 * Q := by positivity
  have hlog0 : 0 ≤ Real.log (1 + G ^ 2 / μ ^ 2 * Q) := Real.log_nonneg (by linarith)
  have nA : (⌈Real.log (1 + G ^ 2 / μ ^ 2 * Q) / (γ * μ)⌉₊ : ℝ) ≤ 821 * M * Real.log (1 + G ^ 2 / μ ^ 2 * Q) + 1 := by
    refine (Nat.ceil_lt_add_one (by positivity)).le.trans ?_
    have e : Real.log (1 + G ^ 2 / μ ^ 2 * Q) / (γ * μ) =
        Real.log (1 + G ^ 2 / μ ^ 2 * Q) * (κ ^ 2 + 20 * (σ ^ 2 * Q / μ ^ 2)) := by
      rw [show Real.log (1 + G ^ 2 / μ ^ 2 * Q) / (γ * μ) = Real.log (1 + G ^ 2 / μ ^ 2 * Q) * (1 / γ) / μ by
        field_simp, hγinv]
      simp only [κ]; field_simp
    rw [e]
    have : κ ^ 2 + 20 * (σ ^ 2 * Q / μ ^ 2) ≤ 821 * M := by linarith
    nlinarith
  have nB : (⌈4000 * M⌉₊ : ℝ) ≤ 4000 * M + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have nC : (⌈4 / (γ * μ)⌉₊ : ℝ) ≤ 3284 * M + 1 := by
    refine (Nat.ceil_lt_add_one (by positivity)).le.trans ?_
    have e : 4 / (γ * μ) = 4 * κ ^ 2 + 80 * (σ ^ 2 * Q / μ ^ 2) := by
      rw [show 4 / (γ * μ) = 4 * (1 / γ) / μ by field_simp, hγinv]
      simp only [κ]; field_simp; ring
    rw [e]; linarith
  have tη' : 8 * Δ / (ε * tη L μ ρ σ ε) = 640000 * M * (K * Δ / ε * Real.sqrt Q) := by
    have hη : tη L μ ρ σ ε = α * Real.sqrt E / (20 * K) := rfl
    have hα' : α = 1 / (4000 * M) := by rw [eq_div_iff (by positivity)]; linarith
    have hsE : Real.sqrt E = 1 / Real.sqrt Q := by
      rw [eq_div_iff (Real.sqrt_pos.mpr hQ).ne']; exact hu
    rw [hη, hα', hsE]
    field_simp
    ring
  have tα' : 16 * (3 * ε + 10 * σ) / (ε * α) = 192000 * M + 640000 * M * (σ / ε) := by
    have hα' : α = 1 / (4000 * M) := by rw [eq_div_iff (by positivity)]; linarith
    rw [hα']; field_simp; ring
  rw [tη', tα']
  have hD0 : 0 ≤ K * Δ / ε * Real.sqrt Q := by positivity
  have hG0 : 0 ≤ Real.log (1 + G ^ 2 / μ ^ 2 * Q) := hlog0
  have hs0 : 0 ≤ σ / ε := by positivity
  have hQe : 40 * ρ * K / ε + L ^ 2 / (ε ^ 2 + 20 * σ ^ 2) = Q := rfl
  rw [hQe]
  linarith [mul_nonneg hM.le hD0, mul_nonneg hM.le hG0, mul_nonneg hM.le hs0]

end TuneHyp

end OracleTemplate.HessianNcsc
