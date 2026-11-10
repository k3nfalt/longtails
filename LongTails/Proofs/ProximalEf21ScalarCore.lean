import Mathlib

namespace LongTails.Proofs.ProximalEf21ScalarCore

lemma scalar_constant_conditions :
    (1 / 16 - 15 / 8192 - 12 / 524288 : ℝ) ≥ 1 / 32 ∧
    (-1 / 64 + 15 / 8192 + 6 / 524288 : ℝ) ≤ -1 / 128 ∧
    (-1 / 2 + 5 / 128 : ℝ) ≤ -1 / 4 ∧
    (5 + 1 / 32 + 6 / 524288 : ℝ) ≤ 6 ∧
    (3 / 2 + 1 / 64 : ℝ) ≤ 2 := by
  norm_num

lemma tuning_bounds {μ M δ τ γ α : ℝ}
    (hμ : 0 < μ) (hμM : μ ≤ M) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hτ : τ = 1 / (4096 * M)) (hγ : 0 < γ)
    (hγbound : γ ≤ δ * τ / 128) (hα : α = μ * γ) :
    0 < M ∧ 0 < τ ∧
    M * τ = 1 / 4096 ∧
    M * γ / δ ≤ 1 / 524288 ∧
    γ / τ ≤ δ / 128 ∧
    0 < α ∧ α ≤ δ / 524288 ∧ α ≤ 1 := by
  have hM : 0 < M := lt_of_lt_of_le hμ hμM
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hMt : M * τ = 1 / 4096 := by
    rw [hτ]
    field_simp [ne_of_gt hM]
    <;> ring
  have hMγ : M * γ ≤ δ / 524288 := by
    calc
      M * γ ≤ M * (δ * τ / 128) :=
        mul_le_mul_of_nonneg_left hγbound (le_of_lt hM)
      _ = δ * (M * τ) / 128 := by ring
      _ = δ / 524288 := by rw [hMt]; ring
  have hMγδ : M * γ / δ ≤ 1 / 524288 := by
    apply (div_le_iff₀ hδ).2
    nlinarith [hMγ]
  have hγτ : γ / τ ≤ δ / 128 := by
    apply (div_le_iff₀ hτpos).2
    nlinarith [hγbound]
  have hαpos : 0 < α := by rw [hα]; positivity
  have hαbound : α ≤ δ / 524288 := by
    calc
      α = μ * γ := hα
      _ ≤ M * γ := mul_le_mul_of_nonneg_right hμM (le_of_lt hγ)
      _ ≤ δ / 524288 := hMγ
  have hα1 : α ≤ 1 := by linarith
  exact ⟨hM, hτpos, hMt, hMγδ, hγτ, hαpos, hαbound, hα1⟩

lemma coefficient_conditions {μ M δ τ γ : ℝ}
    (hμ : 0 < μ) (hμM : μ ≤ M) (hδ : 0 < δ)
    (hτ : τ = 1 / (4096 * M)) (hγ : 0 < γ)
    (hγbound : γ ≤ δ * τ / 128) :
    1 / 8 - 15 * M * τ / 2 - 1 / 16 - 12 * M * γ / δ ≥ 1 / 32 ∧
    -1 / (64 * M) + 15 * τ / 2 + 6 * γ / δ ≤ -1 / (128 * M) ∧
    -δ / 2 + 5 * γ / τ ≤ -δ / 4 ∧
    5 + μ / (32 * M) + 6 * μ * γ / δ ≤ 6 ∧
    3 / 2 + μ / (64 * M) ≤ 2 := by
  have hM : 0 < M := lt_of_lt_of_le hμ hμM
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hMt : M * τ = 1 / 4096 := by
    rw [hτ]
    field_simp [ne_of_gt hM]
    <;> ring
  have hMγ : M * γ ≤ δ / 524288 := by
    calc
      M * γ ≤ M * (δ * τ / 128) :=
        mul_le_mul_of_nonneg_left hγbound (le_of_lt hM)
      _ = δ * (M * τ) / 128 := by ring
      _ = δ / 524288 := by rw [hMt]; ring
  have hMγδ : M * γ / δ ≤ 1 / 524288 := by
    apply (div_le_iff₀ hδ).2
    nlinarith [hMγ]
  have hγτ : γ / τ ≤ δ / 128 := by
    apply (div_le_iff₀ hτpos).2
    nlinarith [hγbound]
  have hμγ : μ * γ ≤ δ / 524288 :=
    le_trans (mul_le_mul_of_nonneg_right hμM (le_of_lt hγ)) hMγ
  have hμγδ : μ * γ / δ ≤ 1 / 524288 := by
    apply (div_le_iff₀ hδ).2
    nlinarith [hμγ]
  have hμ32 : μ / (32 * M) ≤ 1 / 32 := by
    apply (div_le_iff₀ (by positivity : 0 < 32 * M)).2
    nlinarith [hμM]
  have hμ64 : μ / (64 * M) ≤ 1 / 64 := by
    apply (div_le_iff₀ (by positivity : 0 < 64 * M)).2
    nlinarith [hμM]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [hMt, hMγδ]
  · apply (mul_le_mul_left hM).mp
    have hleft :
        M * (-1 / (64 * M) + 15 * τ / 2 + 6 * γ / δ) =
          -1 / 64 + 15 * (M * τ) / 2 + 6 * (M * γ / δ) := by
      field_simp [ne_of_gt hM, ne_of_gt hδ]
      <;> ring
    have hright : M * (-1 / (128 * M)) = -1 / 128 := by
      field_simp [ne_of_gt hM]
      <;> ring
    rw [hleft, hright, hMt]
    nlinarith [hMγδ]
  · nlinarith [hγτ]
  · nlinarith [hμ32, hμγδ]
  · nlinarith [hμ64]


lemma assembled_descent
    {E₀ E₁ V₀ V₁ W₀ W₁ Δ displacement remainder₁ remainder₂ bias² σ² μ M δ τ γ α : ℝ}
    (hμ : 0 < μ) (hμM : μ ≤ M) (hδ : 0 < δ)
    (hτ : τ = 1 / (4096 * M)) (hγ : 0 < γ)
    (hγbound : γ ≤ δ * τ / 128) (hα : α = μ * γ)
    (hΔ : 0 ≤ Δ) (hdisplacement : 0 ≤ displacement)
    (hW : 0 ≤ W₀) (hV : 0 ≤ V₀) (hbias : 0 ≤ bias²) (hnoise : 0 ≤ σ²)
    (hE : E₁ ≤ E₀ - α * (1 / 8 - 15 * M * τ / 2) * Δ -
      5 / (8 * γ) * displacement - α / 8 * remainder₁ -
      1 / (μ * τ) * remainder₂ + 15 * α * τ / 2 * W₀ +
      5 * γ / (μ * τ) * V₀ + 5 * γ * bias² + μ * γ ^ 2 / 2 * σ²)
    (hWstep : W₁ ≤ (1 - α) * W₀ + 4 * α * M * Δ +
      2 * α * bias² + α ^ 2 * σ²)
    (hVstep : V₁ ≤ (1 - δ / 2) * V₀ + 6 * α ^ 2 / δ * W₀ +
      12 * α ^ 2 * M / δ * Δ + 6 * α ^ 2 / δ * bias² + α ^ 2 * σ²) :
    E₁ + V₁ / μ + W₁ / (64 * M) ≤
      (E₀ + V₀ / μ + W₀ / (64 * M)) - α / 32 * Δ -
      1 / (2 * γ) * displacement - α / 8 * remainder₁ -
      1 / (μ * τ) * remainder₂ - α / (128 * M) * W₀ -
      δ / (4 * μ) * V₀ + 6 * γ * bias² + 2 * μ * γ ^ 2 * σ² := by
  have hM : 0 < M := lt_of_lt_of_le hμ hμM
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hαpos : 0 < α := by rw [hα]; positivity
  obtain ⟨hcΔ, hcW, hcV, hcbias, hcnoise⟩ :=
    coefficient_conditions hμ hμM hδ hτ hγ hγbound
  have hsum := add_le_add
    (add_le_add hE (div_le_div_of_nonneg_right hVstep (le_of_lt hμ)))
    (div_le_div_of_nonneg_right hWstep (by positivity : (0 : ℝ) ≤ 64 * M))
  have hid :
      (E₀ - α * (1 / 8 - 15 * M * τ / 2) * Δ -
        5 / (8 * γ) * displacement - α / 8 * remainder₁ -
        1 / (μ * τ) * remainder₂ + 15 * α * τ / 2 * W₀ +
        5 * γ / (μ * τ) * V₀ + 5 * γ * bias² + μ * γ ^ 2 / 2 * σ²) +
      ((1 - δ / 2) * V₀ + 6 * α ^ 2 / δ * W₀ +
        12 * α ^ 2 * M / δ * Δ + 6 * α ^ 2 / δ * bias² + α ^ 2 * σ²) / μ +
      ((1 - α) * W₀ + 4 * α * M * Δ + 2 * α * bias² + α ^ 2 * σ²) / (64 * M) =
      (E₀ + V₀ / μ + W₀ / (64 * M)) -
      α * (1 / 8 - 15 * M * τ / 2 - 1 / 16 - 12 * M * γ / δ) * Δ -
      5 / (8 * γ) * displacement - α / 8 * remainder₁ -
      1 / (μ * τ) * remainder₂ +
      α * (-1 / (64 * M) + 15 * τ / 2 + 6 * γ / δ) * W₀ +
      (-δ / 2 + 5 * γ / τ) * V₀ / μ +
      γ * (5 + μ / (32 * M) + 6 * μ * γ / δ) * bias² +
      μ * γ ^ 2 * (3 / 2 + μ / (64 * M)) * σ² := by
    rw [hα]
    field_simp [ne_of_gt hμ, ne_of_gt hM, ne_of_gt hδ,
      ne_of_gt hτpos, ne_of_gt hγ]
    <;> ring
  rw [hid] at hsum
  have hgapterm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcΔ hΔ) (le_of_lt hαpos)
  have hWterm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcW hW) (le_of_lt hαpos)
  have hVterm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcV hV) (le_of_lt hμ)
  have hbiasterm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcbias hbias) (le_of_lt hγ)
  have hnoiseterm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcnoise hnoise)
    (by positivity : (0 : ℝ) ≤ μ * γ ^ 2)
  have hdcoef : (1 : ℝ) / (2 * γ) ≤ 5 / (8 * γ) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * γ)
      (by positivity : 0 < 8 * γ)).2
    nlinarith
  have hdterm := mul_le_mul_of_nonneg_right hdcoef hdisplacement
  nlinarith only [hsum, hgapterm, hWterm, hVterm, hbiasterm, hnoiseterm, hdterm]

lemma contraction_from_dissipation
    {Λ Λnext Δ displacement remainder₁ remainder₂ W V noise μ M γ τ α δ : ℝ}
    (hμ : 0 < μ) (hM : 0 < M) (hγ : 0 < γ) (hτ : 0 < τ)
    (hα : α = μ * γ) (hα1 : α ≤ 1) (hαδ : 5 * α ≤ 128 * δ)
    (hΔ : 0 ≤ Δ) (hdisplacement : 0 ≤ displacement)
    (hrem₁ : 0 ≤ remainder₁) (hrem₂ : 0 ≤ remainder₂)
    (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hupper : Λ ≤
      3 * Δ + 5 / (μ * γ ^ 2) * displacement + remainder₁ / 8 +
      2 / (μ * τ) * remainder₂ + 2 / M * W + 5 / μ * V)
    (hdescent : Λnext ≤
      Λ - α / 32 * Δ - 1 / (2 * γ) * displacement - α / 8 * remainder₁ -
      1 / (μ * τ) * remainder₂ - α / (128 * M) * W - δ / (4 * μ) * V + noise) :
    Λnext ≤ (1 - α / 512) * Λ + noise := by
  have hαpos : 0 < α := by rw [hα]; positivity
  have h₁ : α / 512 * 3 ≤ α / 32 := by nlinarith
  have h₂ : α / 512 * (5 / (μ * γ ^ 2)) ≤ 1 / (2 * γ) := by
    rw [hα]
    have heq : μ * γ / 512 * (5 / (μ * γ ^ 2)) = 5 / (512 * γ) := by
      field_simp [ne_of_gt hμ, ne_of_gt hγ]
      <;> ring
    rw [heq]
    apply (div_le_div_iff₀ (by positivity : 0 < 512 * γ)
      (by positivity : 0 < 2 * γ)).2
    nlinarith
  have h₃ : α / 512 * (1 / 8) ≤ α / 8 := by nlinarith
  have h₄ : α / 512 * (2 / (μ * τ)) ≤ 1 / (μ * τ) := by
    have heq : α / 512 * (2 / (μ * τ)) = (α / 256) / (μ * τ) := by ring
    rw [heq]
    apply (div_le_div_iff_of_pos_right (mul_pos hμ hτ)).2
    nlinarith
  have h₅ : α / 512 * (2 / M) ≤ α / (128 * M) := by
    have heq₁ : α / 512 * (2 / M) = (α / 256) / M := by ring
    have heq₂ : α / (128 * M) = (α / 128) / M := by ring
    rw [heq₁, heq₂]
    apply (div_le_div_iff_of_pos_right hM).2
    nlinarith
  have h₆ : α / 512 * (5 / μ) ≤ δ / (4 * μ) := by
    have heq₁ : α / 512 * (5 / μ) = (5 * α / 512) / μ := by ring
    have heq₂ : δ / (4 * μ) = (δ / 4) / μ := by ring
    rw [heq₁, heq₂]
    apply (div_le_div_iff_of_pos_right hμ).2
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hupper
    (by positivity : (0 : ℝ) ≤ α / 512)
  have hterm₁ := mul_le_mul_of_nonneg_right h₁ hΔ
  have hterm₂ := mul_le_mul_of_nonneg_right h₂ hdisplacement
  have hterm₃ := mul_le_mul_of_nonneg_right h₃ hrem₁
  have hterm₄ := mul_le_mul_of_nonneg_right h₄ hrem₂
  have hterm₅ := mul_le_mul_of_nonneg_right h₅ hW
  have hterm₆ := mul_le_mul_of_nonneg_right h₆ hV
  have htotal : α / 512 * Λ ≤
      α / 32 * Δ + 1 / (2 * γ) * displacement + α / 8 * remainder₁ +
      1 / (μ * τ) * remainder₂ + α / (128 * M) * W + δ / (4 * μ) * V := by
    nlinarith only [hscaled, hterm₁, hterm₂, hterm₃, hterm₄, hterm₅, hterm₆]
  nlinarith only [hdescent, htotal]

lemma centered_contraction_unroll (Λ : ℕ → ℝ) (q a : ℝ)
    (hq : 0 ≤ q)
    (hstep : ∀ t, Λ (t + 1) ≤ q * Λ t + (1 - q) * a) :
    ∀ k, Λ k ≤ q ^ k * Λ 0 + (1 - q ^ k) * a := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        Λ (k + 1) ≤ q * Λ k + (1 - q) * a := hstep k
        _ ≤ q * (q ^ k * Λ 0 + (1 - q ^ k) * a) + (1 - q) * a :=
          add_le_add_right (mul_le_mul_of_nonneg_left ih hq) _
        _ = q ^ (k + 1) * Λ 0 + (1 - q ^ (k + 1)) * a := by
          simp only [pow_succ]
          ring

lemma inner_geometric_bound (Λ : ℕ → ℝ) {μ γ σ² bias² B : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hB : 0 < B)
    (hstepSize : μ * γ ≤ 512)
    (hstep : ∀ t, Λ (t + 1) ≤
      (1 - μ * γ / 512) * Λ t + 6 * γ * bias² + 2 * μ * γ ^ 2 * σ² / B) :
    ∀ k, Λ k ≤
      (1 - μ * γ / 512) ^ k * Λ 0 +
      (1 - (1 - μ * γ / 512) ^ k) * (3072 * bias² / μ + 1024 * γ * σ² / B) := by
  apply centered_contraction_unroll
  · linarith
  · intro t
    have hforcing :
        (1 - (1 - μ * γ / 512)) * (3072 * bias² / μ + 1024 * γ * σ² / B) =
          6 * γ * bias² + 2 * μ * γ ^ 2 * σ² / B := by
      field_simp [ne_of_gt hμ, ne_of_gt hB]
      <;> ring
    rw [hforcing]
    exact hstep t

lemma stage_transfer_from_model_control
    {previous incoming model compression distance : ℝ}
    (hdistance : 0 ≤ distance) (hcompression : 0 ≤ compression)
    (hcontrol : (7 / 8 : ℝ) * model + compression ≤ previous)
    (hidentity : incoming = previous - distance + model + compression) :
    incoming ≤ (15 / 7 : ℝ) * previous := by
  linarith

lemma stage_invariant_step {previous incoming terminal scale : ℝ}
    (hscale : 0 ≤ scale)
    (hprevious : previous ≤ 2 * scale)
    (htransfer : incoming ≤ (15 / 7 : ℝ) * previous)
    (hinner : terminal ≤ incoming / 16 + scale / 2) :
    terminal ≤ scale := by
  linarith

lemma stage_invariant (μ incoming terminal : ℕ → ℝ) (scale : ℝ)
    (hscale : 0 ≤ scale) (hμ : ∀ s, 0 ≤ μ s)
    (hdyadic : ∀ s, μ s = 2 * μ (s + 1))
    (hbase : terminal 0 ≤ scale * μ 0)
    (htransfer : ∀ s, incoming (s + 1) ≤ (15 / 7 : ℝ) * terminal s)
    (hinner : ∀ s, terminal (s + 1) ≤ incoming (s + 1) / 16 + scale * μ (s + 1) / 2) :
    ∀ s, terminal s ≤ scale * μ s := by
  intro s
  induction s with
  | zero => exact hbase
  | succ s ih =>
      apply stage_invariant_step
        (previous := terminal s) (incoming := incoming (s + 1))
        (scale := scale * μ (s + 1))
      · exact mul_nonneg hscale (hμ (s + 1))
      · rw [hdyadic s] at ih
        nlinarith only [ih]
      · exact htransfer s
      · exact hinner s

lemma objective_from_final_potential {gap potential μ R ε : ℝ}
    (hε : 0 ≤ ε)
    (hgap : gap ≤ (8 / 7 : ℝ) * potential)
    (hpotential : potential ≤ 8192 * μ * R ^ 2)
    (hstage : μ * R ^ 2 ≤ ε / 16384) : gap ≤ ε := by
  nlinarith

lemma initialize_stage {H scale : ℝ} (hH : 0 ≤ H) (hscale : 0 < scale) :
    H / (2 + 2 * H / scale) ≤ scale / 2 := by
  have hden : 0 < 2 + 2 * H / scale := by positivity
  apply (div_le_iff₀ hden).2
  have heq : scale / 2 * (2 + 2 * H / scale) = scale + H := by
    field_simp [ne_of_gt hscale]
    <;> ring
  rw [heq]
  linarith

end LongTails.Proofs.ProximalEf21ScalarCore
