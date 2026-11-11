import LongTails.Proofs.CompositeTransportMain

namespace OracleTemplate.CompositeTransport

noncomputable def tα (σ ε : ℝ) : ℝ := (ε / 3) ^ 2 / ((ε / 3) ^ 2 + 120 * σ ^ 2)

noncomputable def tγ (L ρ σ ε : ℝ) : ℝ := 1 / (L + 7 * Real.sqrt (ρ * (ε / 3)) / tα σ ε)

noncomputable def tunedConfig (L ρ σ Δ ε : ℝ) : Config :=
  { n0 := ⌈120 * σ ^ 2 / (ε / 3) ^ 2⌉₊ + 1
    T := ⌈Δ / (tγ L ρ σ ε * (ε / 3) ^ 2)⌉₊
    α := tα σ ε
    γ := tγ L ρ σ ε
    ε := ε / 3 }

variable {L ρ σ Δ ε : ℝ}

lemma tα_pos (hε : 0 < ε) : 0 < tα σ ε := by unfold tα; positivity

lemma tα_le_one (hε : 0 < ε) : tα σ ε ≤ 1 := by
  unfold tα
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg σ]

lemma tα_mul (hε : 0 < ε) : tα σ ε * ((ε / 3) ^ 2 + 120 * σ ^ 2) = (ε / 3) ^ 2 := by
  unfold tα
  have : (ε / 3) ^ 2 + 120 * σ ^ 2 ≠ 0 := by positivity
  field_simp

lemma tα_inv (hε : 0 < ε) : 1 / tα σ ε = 1 + 1080 * σ ^ 2 / ε ^ 2 := by
  unfold tα
  have h1 : (ε / 3) ^ 2 + 120 * σ ^ 2 ≠ 0 := by positivity
  have h2 : ε ≠ 0 := hε.ne'
  field_simp
  ring

lemma tγ_pos (hL : 0 < L) (hε : 0 < ε) : 0 < tγ L ρ σ ε := by
  have := tα_pos (σ := σ) hε
  unfold tγ; positivity

lemma tγ_mul (hL : 0 < L) (hε : 0 < ε) :
    tγ L ρ σ ε * (L + 7 * Real.sqrt (ρ * (ε / 3)) / tα σ ε) = 1 := by
  have := tα_pos (σ := σ) hε
  have h : L + 7 * Real.sqrt (ρ * (ε / 3)) / tα σ ε ≠ 0 := by positivity
  unfold tγ
  field_simp

lemma tuned_hyp (hL : 0 < L) (hρ : 0 ≤ ρ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    CfgHyp (tunedConfig L ρ σ Δ ε) L ρ σ Δ := by
  have hα := tα_pos (σ := σ) hε
  have hα1 := tα_le_one (σ := σ) hε
  have hαm := tα_mul (σ := σ) hε
  have hγ := tγ_pos (ρ := ρ) (σ := σ) hL hε
  have hm := tγ_mul (ρ := ρ) (σ := σ) hL hε
  have he : 0 < ε / 3 := by positivity
  have hs : 0 ≤ Real.sqrt (ρ * (ε / 3)) := Real.sqrt_nonneg _
  have hX : 0 ≤ tγ L ρ σ ε * (7 * Real.sqrt (ρ * (ε / 3)) / tα σ ε) := by positivity
  have hγL : tγ L ρ σ ε * L ≤ 1 := by nlinarith
  refine ⟨by simp [tunedConfig], hα, hα1, hγ, hγL, he, ?_, ?_, hΔ⟩
  · show 20 * ((ρ * (2 * tγ L ρ σ ε * (ε / 3)) ^ 2 / tα σ ε ^ 2) ^ 2 +
      σ ^ 2 / ((⌈120 * σ ^ 2 / (ε / 3) ^ 2⌉₊ + 1 : ℕ) : ℝ) + tα σ ε * σ ^ 2) / (ε / 3) ≤ ε / 3 / 2
    set α := tα σ ε
    set γ := tγ L ρ σ ε
    set n : ℝ := ((⌈120 * σ ^ 2 / (ε / 3) ^ 2⌉₊ + 1 : ℕ) : ℝ)
    have hn : 120 * σ ^ 2 / (ε / 3) ^ 2 ≤ n := by
      simp only [n]; push_cast; linarith [Nat.le_ceil (120 * σ ^ 2 / (ε / 3) ^ 2)]
    have hnpos : 0 < n := by simp only [n]; positivity
    have hn' : 120 * σ ^ 2 ≤ n * (ε / 3) ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hn; linarith
    have h1 : σ ^ 2 / n ≤ (ε / 3) ^ 2 / 120 := by
      rw [div_le_div_iff₀ hnpos (by norm_num)]; nlinarith
    have h2 : α * σ ^ 2 ≤ (ε / 3) ^ 2 / 120 := by
      have : 0 ≤ α * (ε / 3) ^ 2 := by positivity
      nlinarith
    have h7 : 7 * γ * Real.sqrt (ρ * (ε / 3)) ≤ α := by
      have h' : γ * (7 * Real.sqrt (ρ * (ε / 3)) / α) ≤ 1 := by
        have : 0 ≤ γ * L := by positivity
        nlinarith
      rw [mul_div_assoc', div_le_one hα] at h'
      linarith
    have h49 : 49 * γ ^ 2 * (ρ * (ε / 3)) ≤ α ^ 2 := by
      have hsq : Real.sqrt (ρ * (ε / 3)) ^ 2 = ρ * (ε / 3) := Real.sq_sqrt (by positivity)
      calc 49 * γ ^ 2 * (ρ * (ε / 3)) = (7 * γ * Real.sqrt (ρ * (ε / 3))) ^ 2 := by
            rw [mul_pow, hsq]; ring
        _ ≤ α ^ 2 := pow_le_pow_left₀ (by positivity) h7 2
    have hB : ρ * (2 * γ * (ε / 3)) ^ 2 / α ^ 2 ≤ 4 * (ε / 3) / 49 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have := mul_le_mul_of_nonneg_left h49 (by positivity : (0 : ℝ) ≤ 4 * (ε / 3))
      nlinarith
    have hB0 : 0 ≤ ρ * (2 * γ * (ε / 3)) ^ 2 / α ^ 2 := by positivity
    have h3 : (ρ * (2 * γ * (ε / 3)) ^ 2 / α ^ 2) ^ 2 ≤ (ε / 3) ^ 2 / 120 := by
      have := pow_le_pow_left₀ hB0 hB 2
      nlinarith
    rw [div_le_div_iff₀ he (by norm_num)]
    nlinarith
  · show Δ / (tγ L ρ σ ε * (ε / 3)) ≤ ((⌈Δ / (tγ L ρ σ ε * (ε / 3) ^ 2)⌉₊ : ℕ) + 1 : ℝ) * (ε / 3)
    have hc := Nat.le_ceil (Δ / (tγ L ρ σ ε * (ε / 3) ^ 2))
    have e : Δ / (tγ L ρ σ ε * (ε / 3)) = Δ / (tγ L ρ σ ε * (ε / 3) ^ 2) * (ε / 3) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (by linarith) he.le

lemma tuned_calls (hL : 0 < L) (hρ : 0 ≤ ρ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (tunedConfig L ρ σ Δ ε).n0 + 2 * (tunedConfig L ρ σ Δ ε).T ≤
      ⌈10 ^ 6 * (L * Δ / ε ^ 2 + (1 + σ ^ 2 / ε ^ 2) * Δ * Real.sqrt (ρ * ε) / ε ^ 2 + σ ^ 2 / ε ^ 2 + 1)⌉₊ := by
  have hα := tα_pos (σ := σ) hε
  have hγ := tγ_pos (ρ := ρ) (σ := σ) hL hε
  have hinvα := tα_inv (σ := σ) hε
  set S := Real.sqrt (ρ * (ε / 3))
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSle : S ≤ Real.sqrt (ρ * ε) := Real.sqrt_le_sqrt (by nlinarith)
  have hinvγ : 1 / tγ L ρ σ ε = L + 7 * S * (1 + 1080 * σ ^ 2 / ε ^ 2) := by
    unfold tγ
    rw [one_div_one_div, ← hinvα]
    ring
  have hTv : Δ / (tγ L ρ σ ε * (ε / 3) ^ 2) = 9 * Δ / ε ^ 2 * (L + 7 * S * (1 + 1080 * σ ^ 2 / ε ^ 2)) := by
    rw [← hinvγ]
    field_simp
    ring
  have hnv : 120 * σ ^ 2 / (ε / 3) ^ 2 = 1080 * (σ ^ 2 / ε ^ 2) := by field_simp; ring
  have hn := Nat.ceil_lt_add_one (show 0 ≤ 120 * σ ^ 2 / (ε / 3) ^ 2 by positivity)
  have hT := Nat.ceil_lt_add_one (show 0 ≤ Δ / (tγ L ρ σ ε * (ε / 3) ^ 2) by positivity)
  have hn2 : 120 * σ ^ 2 / (ε / 3) ^ 2 + 1 = 1080 * (σ ^ 2 / ε ^ 2) + 1 := by rw [hnv]
  have hT2 : Δ / (tγ L ρ σ ε * (ε / 3) ^ 2) + 1 =
      9 * Δ / ε ^ 2 * (L + 7 * S * (1 + 1080 * σ ^ 2 / ε ^ 2)) + 1 := by rw [hTv]
  have q : 0 ≤ σ ^ 2 / ε ^ 2 := by positivity
  have hk : 9 * Δ / ε ^ 2 * (L + 7 * S * (1 + 1080 * σ ^ 2 / ε ^ 2)) ≤
      9 * (L * Δ / ε ^ 2) + 68040 * ((1 + σ ^ 2 / ε ^ 2) * Δ * Real.sqrt (ρ * ε) / ε ^ 2) := by
    have h1 : 1 + 1080 * σ ^ 2 / ε ^ 2 ≤ 1080 * (1 + σ ^ 2 / ε ^ 2) := by
      rw [mul_div_assoc]; nlinarith
    have h2 : 7 * S * (1 + 1080 * σ ^ 2 / ε ^ 2) ≤ 7 * Real.sqrt (ρ * ε) * (1080 * (1 + σ ^ 2 / ε ^ 2)) :=
      mul_le_mul (by linarith) h1 (by positivity) (by positivity)
    have h3 : 0 ≤ 9 * Δ / ε ^ 2 := by positivity
    calc 9 * Δ / ε ^ 2 * (L + 7 * S * (1 + 1080 * σ ^ 2 / ε ^ 2))
        ≤ 9 * Δ / ε ^ 2 * (L + 7 * Real.sqrt (ρ * ε) * (1080 * (1 + σ ^ 2 / ε ^ 2))) := by gcongr
      _ = _ := by ring
  have key : (((tunedConfig L ρ σ Δ ε).n0 + 2 * (tunedConfig L ρ σ Δ ε).T : ℕ) : ℝ) ≤
      10 ^ 6 * (L * Δ / ε ^ 2 + (1 + σ ^ 2 / ε ^ 2) * Δ * Real.sqrt (ρ * ε) / ε ^ 2 + σ ^ 2 / ε ^ 2 + 1) := by
    simp only [tunedConfig]
    push_cast
    have p1 : 0 ≤ L * Δ / ε ^ 2 := by positivity
    have p2 : 0 ≤ (1 + σ ^ 2 / ε ^ 2) * Δ * Real.sqrt (ρ * ε) / ε ^ 2 := by positivity
    linarith
  exact_mod_cast key.trans (Nat.le_ceil _)

end OracleTemplate.CompositeTransport
