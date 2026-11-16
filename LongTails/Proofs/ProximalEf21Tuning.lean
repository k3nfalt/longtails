import LongTails.Setups.StochasticProximalEf21
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

section ScalarCore

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
    linarith only [hMγ]
  have hγτ : γ / τ ≤ δ / 128 := by
    apply (div_le_iff₀ hτpos).2
    linarith only [hγbound]
  have hαpos : 0 < α := by rw [hα]; positivity
  have hαbound : α ≤ δ / 524288 := by
    calc
      α = μ * γ := hα
      _ ≤ M * γ := mul_le_mul_of_nonneg_right hμM (le_of_lt hγ)
      _ ≤ δ / 524288 := hMγ
  have hα1 : α ≤ 1 := by linarith only [hαbound, hδ1]
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
    linarith only [hMγ]
  have hγτ : γ / τ ≤ δ / 128 := by
    apply (div_le_iff₀ hτpos).2
    linarith only [hγbound]
  have hμγ : μ * γ ≤ δ / 524288 :=
    le_trans (mul_le_mul_of_nonneg_right hμM (le_of_lt hγ)) hMγ
  have hμγδ : μ * γ / δ ≤ 1 / 524288 := by
    apply (div_le_iff₀ hδ).2
    linarith only [hμγ]
  have hμ32 : μ / (32 * M) ≤ 1 / 32 := by
    apply (div_le_iff₀ (by positivity : 0 < 32 * M)).2
    linarith only [hμM]
  have hμ64 : μ / (64 * M) ≤ 1 / 64 := by
    apply (div_le_iff₀ (by positivity : 0 < 64 * M)).2
    linarith only [hμM]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hid :
        1 / 8 - 15 * M * τ / 2 - 1 / 16 - 12 * M * γ / δ =
          1 / 16 - (15 / 2 : ℝ) * (M * τ) - 12 * (M * γ / δ) := by
      ring
    rw [hid, hMt]
    linarith only [hMγδ]
  · apply (mul_le_mul_iff_of_pos_left hM).mp
    have hleft :
        M * (-1 / (64 * M) + 15 * τ / 2 + 6 * γ / δ) =
          -1 / 64 + 15 * (M * τ) / 2 + 6 * (M * γ / δ) := by
      field_simp [ne_of_gt hM, ne_of_gt hδ]
      <;> ring
    have hright : M * (-1 / (128 * M)) = -1 / 128 := by
      field_simp [ne_of_gt hM]
      <;> ring
    rw [hleft, hright, hMt]
    linarith only [hMγδ]
  · rw [show 5 * γ / τ = 5 * (γ / τ) by ring]
    linarith only [hγτ, hδ]
  · rw [show 6 * μ * γ / δ = 6 * (μ * γ / δ) by ring]
    linarith only [hμ32, hμγδ]
  · linarith only [hμ64]

lemma assembled_descent
    {E₀ E₁ V₀ V₁ W₀ W₁ Δ displacement remainder₁ remainder₂ biasSq variance μ M δ τ γ α : ℝ}
    (hμ : 0 < μ) (hμM : μ ≤ M) (hδ : 0 < δ)
    (hτ : τ = 1 / (4096 * M)) (hγ : 0 < γ)
    (hγbound : γ ≤ δ * τ / 128) (hα : α = μ * γ)
    (hΔ : 0 ≤ Δ) (hdisplacement : 0 ≤ displacement)
    (hW : 0 ≤ W₀) (hV : 0 ≤ V₀) (hbias : 0 ≤ biasSq) (hnoise : 0 ≤ variance)
    (hE : E₁ ≤ E₀ - α * (1 / 8 - 15 * M * τ / 2) * Δ -
      5 / (8 * γ) * displacement - α / 8 * remainder₁ -
      1 / (μ * τ) * remainder₂ + 15 * α * τ / 2 * W₀ +
      5 * γ / (μ * τ) * V₀ + 5 * γ * biasSq + μ * γ ^ 2 / 2 * variance)
    (hWstep : W₁ ≤ (1 - α) * W₀ + 4 * α * M * Δ +
      2 * α * biasSq + α ^ 2 * variance)
    (hVstep : V₁ ≤ (1 - δ / 2) * V₀ + 6 * α ^ 2 / δ * W₀ +
      12 * α ^ 2 * M / δ * Δ + 6 * α ^ 2 / δ * biasSq + α ^ 2 * variance) :
    E₁ + V₁ / μ + W₁ / (64 * M) ≤
      (E₀ + V₀ / μ + W₀ / (64 * M)) - α / 32 * Δ -
      1 / (2 * γ) * displacement - α / 8 * remainder₁ -
      1 / (μ * τ) * remainder₂ - α / (128 * M) * W₀ -
      δ / (4 * μ) * V₀ + 6 * γ * biasSq + 2 * μ * γ ^ 2 * variance := by
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
        5 * γ / (μ * τ) * V₀ + 5 * γ * biasSq + μ * γ ^ 2 / 2 * variance) +
      ((1 - δ / 2) * V₀ + 6 * α ^ 2 / δ * W₀ +
        12 * α ^ 2 * M / δ * Δ + 6 * α ^ 2 / δ * biasSq + α ^ 2 * variance) / μ +
      ((1 - α) * W₀ + 4 * α * M * Δ + 2 * α * biasSq + α ^ 2 * variance) / (64 * M) =
      (E₀ + V₀ / μ + W₀ / (64 * M)) -
      α * (1 / 8 - 15 * M * τ / 2 - 1 / 16 - 12 * M * γ / δ) * Δ -
      5 / (8 * γ) * displacement - α / 8 * remainder₁ -
      1 / (μ * τ) * remainder₂ +
      α * (-1 / (64 * M) + 15 * τ / 2 + 6 * γ / δ) * W₀ +
      (-δ / 2 + 5 * γ / τ) * V₀ / μ +
      γ * (5 + μ / (32 * M) + 6 * μ * γ / δ) * biasSq +
      μ * γ ^ 2 * (3 / 2 + μ / (64 * M)) * variance := by
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
    linarith only [hγ]
  have hdterm := mul_le_mul_of_nonneg_right hdcoef hdisplacement
  ring_nf at hsum hgapterm hWterm hVterm hbiasterm hnoiseterm hdterm ⊢
  linarith only [hsum, hgapterm, hWterm, hVterm, hbiasterm, hnoiseterm, hdterm]

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
  have h₁ : α / 512 * 3 ≤ α / 32 := by linarith only [hαpos]
  have h₂ : α / 512 * (5 / (μ * γ ^ 2)) ≤ 1 / (2 * γ) := by
    rw [hα]
    have heq : μ * γ / 512 * (5 / (μ * γ ^ 2)) = 5 / (512 * γ) := by
      field_simp [ne_of_gt hμ, ne_of_gt hγ]
      <;> ring
    rw [heq]
    apply (div_le_div_iff₀ (by positivity : 0 < 512 * γ)
      (by positivity : 0 < 2 * γ)).2
    linarith only [hγ]
  have h₃ : α / 512 * (1 / 8) ≤ α / 8 := by linarith only [hαpos]
  have h₄ : α / 512 * (2 / (μ * τ)) ≤ 1 / (μ * τ) := by
    have heq : α / 512 * (2 / (μ * τ)) = (α / 256) / (μ * τ) := by ring
    rw [heq]
    apply (div_le_div_iff_of_pos_right (mul_pos hμ hτ)).2
    linarith only [hα1]
  have h₅ : α / 512 * (2 / M) ≤ α / (128 * M) := by
    have heq₁ : α / 512 * (2 / M) = (α / 256) / M := by ring
    have heq₂ : α / (128 * M) = (α / 128) / M := by ring
    rw [heq₁, heq₂]
    apply (div_le_div_iff_of_pos_right hM).2
    linarith only [hαpos]
  have h₆ : α / 512 * (5 / μ) ≤ δ / (4 * μ) := by
    have heq₁ : α / 512 * (5 / μ) = (5 * α / 512) / μ := by ring
    have heq₂ : δ / (4 * μ) = (δ / 4) / μ := by ring
    rw [heq₁, heq₂]
    apply (div_le_div_iff_of_pos_right hμ).2
    linarith only [hαδ]
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
    ring_nf at hscaled hterm₁ hterm₂ hterm₃ hterm₄ hterm₅ hterm₆ ⊢
    linarith only [hscaled, hterm₁, hterm₂, hterm₃, hterm₄, hterm₅, hterm₆]
  ring_nf at hdescent htotal ⊢
  linarith only [hdescent, htotal]

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
          add_le_add (mul_le_mul_of_nonneg_left ih hq) le_rfl
        _ = q ^ (k + 1) * Λ 0 + (1 - q ^ (k + 1)) * a := by
          simp only [pow_succ]
          ring

lemma inner_geometric_bound (Λ : ℕ → ℝ) {μ γ variance biasSq B : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hB : 0 < B)
    (hstepSize : μ * γ ≤ 512)
    (hstep : ∀ t, Λ (t + 1) ≤
      (1 - μ * γ / 512) * Λ t + 6 * γ * biasSq + 2 * μ * γ ^ 2 * variance / B) :
    ∀ k, Λ k ≤
      (1 - μ * γ / 512) ^ k * Λ 0 +
      (1 - (1 - μ * γ / 512) ^ k) * (3072 * biasSq / μ + 1024 * γ * variance / B) := by
  apply centered_contraction_unroll
  · linarith
  · intro t
    have hforcing :
        (1 - (1 - μ * γ / 512)) * (3072 * biasSq / μ + 1024 * γ * variance / B) =
          6 * γ * biasSq + 2 * μ * γ ^ 2 * variance / B := by
      field_simp [ne_of_gt hμ, ne_of_gt hB]
      <;> ring
    rw [hforcing]
    simpa only [add_assoc] using hstep t

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
        linarith only [ih]
      · exact htransfer s
      · exact hinner s

lemma objective_from_final_potential {gap potential μ R ε : ℝ}
    (hε : 0 ≤ ε)
    (hgap : gap ≤ (8 / 7 : ℝ) * potential)
    (hpotential : potential ≤ 8192 * μ * R ^ 2)
    (hstage : μ * R ^ 2 ≤ ε / 16384) : gap ≤ ε := by
  linarith only [hgap, hpotential, hstage, hε]

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


end ScalarCore


section Schedule

open scoped BigOperators

namespace LongTails.Proofs.ProximalEf21Schedule

open LongTails.Proofs.ProximalEf21ScalarCore

lemma real_two_power_sum (s : ℕ) :
    (∑ j ∈ Finset.range s, (2 : ℝ) ^ j) = (2 : ℝ) ^ s - 1 := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

lemma real_four_power_sum (s : ℕ) :
    (∑ j ∈ Finset.range s, (4 : ℝ) ^ j) = ((4 : ℝ) ^ s - 1) / 3 := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

lemma dyadic_inverse_sums {L : ℝ} (hL : 0 < L) (s : ℕ) :
    (∑ j ∈ Finset.range (s + 1), 1 / (2 * L / (2 : ℝ) ^ j)) ≤
        2 / (2 * L / (2 : ℝ) ^ s) ∧
    (∑ j ∈ Finset.range (s + 1), 1 / (2 * L / (2 : ℝ) ^ j) ^ 2) ≤
        4 / (3 * (2 * L / (2 : ℝ) ^ s) ^ 2) := by
  have hpower : ∀ j : ℕ, (0 : ℝ) < 2 ^ j := fun j => pow_pos (by norm_num) j
  have hinv : ∀ j : ℕ, 1 / (2 * L / (2 : ℝ) ^ j) = (2 : ℝ) ^ j / (2 * L) := by
    intro j
    field_simp [ne_of_gt hL, ne_of_gt (hpower j)]
  have hinv₂ : ∀ j : ℕ, 1 / (2 * L / (2 : ℝ) ^ j) ^ 2 =
      (4 : ℝ) ^ j / (4 * L ^ 2) := by
    intro j
    have hp : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
      rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
      norm_num
    field_simp [ne_of_gt hL, ne_of_gt (hpower j)]
    nlinarith [hp]
  constructor
  · simp_rw [hinv]
    rw [← Finset.sum_div, real_two_power_sum, pow_succ]
    have hr : 2 / (2 * L / (2 : ℝ) ^ s) = 2 * (2 : ℝ) ^ s / (2 * L) := by
      field_simp [ne_of_gt hL, ne_of_gt (hpower s)]
    rw [hr]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  · simp_rw [hinv₂]
    rw [← Finset.sum_div, real_four_power_sum, pow_succ]
    have hr : 4 / (3 * (2 * L / (2 : ℝ) ^ s) ^ 2) =
        (4 * (4 : ℝ) ^ s / 3) / (4 * L ^ 2) := by
      have hh := hinv₂ s
      field_simp [ne_of_gt hL, ne_of_gt (hpower s)] at hh ⊢
      nlinarith only [hh]
    rw [hr]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith

lemma dyadic_ceiling_bounds {a : ℝ} (ha : 1 ≤ a) :
    a ≤ (2 : ℝ) ^ ⌈Real.log a / Real.log 2⌉₊ ∧
      (2 : ℝ) ^ ⌈Real.log a / Real.log 2⌉₊ < 2 * a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log a := Real.log_nonneg ha
  have hq : 0 ≤ Real.log a / Real.log 2 := div_nonneg hlog (le_of_lt hlog₂)
  have hlo := Nat.le_ceil (Real.log a / Real.log 2)
  have hhi := Nat.ceil_lt_add_one hq
  have hmullo := mul_le_mul_of_nonneg_right hlo (le_of_lt hlog₂)
  have hmulhi := mul_lt_mul_of_pos_right hhi hlog₂
  have hcancel : Real.log a / Real.log 2 * Real.log 2 = Real.log a := by
    field_simp [ne_of_gt hlog₂]
  rw [hcancel] at hmullo
  have hexpand : (Real.log a / Real.log 2 + 1) * Real.log 2 =
      Real.log a + Real.log 2 := by
    field_simp [ne_of_gt hlog₂]
    <;> ring
  rw [hexpand] at hmulhi
  constructor
  · calc
      a = Real.exp (Real.log a) := (Real.exp_log ha0).symm
      _ ≤ Real.exp ((⌈Real.log a / Real.log 2⌉₊ : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr hmullo
      _ = (2 : ℝ) ^ ⌈Real.log a / Real.log 2⌉₊ := by
        rw [← Real.log_pow]
        exact Real.exp_log (pow_pos (by norm_num) _)
  · have he : (2 : ℝ) ^ ⌈Real.log a / Real.log 2⌉₊ =
        Real.exp ((⌈Real.log a / Real.log 2⌉₊ : ℝ) * Real.log 2) := by
      rw [← Real.log_pow]
      exact (Real.exp_log (pow_pos (by norm_num) _)).symm
    rw [he]
    calc
      Real.exp ((⌈Real.log a / Real.log 2⌉₊ : ℝ) * Real.log 2) <
          Real.exp (Real.log a + Real.log 2) := Real.exp_lt_exp.mpr hmulhi
      _ = 2 * a := by rw [Real.exp_add, Real.exp_log ha0,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]; ring

lemma terminal_regularization_bounds {L R ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) (hεupper : ε ≤ L * R ^ 2) :
    let S := ⌈Real.log (32768 * L * R ^ 2 / ε) / Real.log 2⌉₊
    ε / (32768 * R ^ 2) < 2 * L / (2 : ℝ) ^ S ∧
      2 * L / (2 : ℝ) ^ S ≤ ε / (16384 * R ^ 2) := by
  dsimp
  have ha : 1 ≤ 32768 * L * R ^ 2 / ε := by
    apply (le_div_iff₀ hε).2
    nlinarith
  obtain ⟨hlo, hhi⟩ := dyadic_ceiling_bounds ha
  have hp : (0 : ℝ) < 2 ^ ⌈Real.log (32768 * L * R ^ 2 / ε) / Real.log 2⌉₊ :=
    pow_pos (by norm_num) _
  constructor
  · apply (div_lt_div_iff₀ (by positivity : 0 < 32768 * R ^ 2) hp).2
    have h := mul_lt_mul_of_pos_right hhi hε
    field_simp [ne_of_gt hε] at h
    nlinarith only [h]
  · apply (div_le_div_iff₀ hp (by positivity : 0 < 16384 * R ^ 2)).2
    have h := mul_le_mul_of_nonneg_right hlo (le_of_lt hε)
    field_simp [ne_of_gt hε] at h
    nlinarith only [h]

lemma ceiling_exponential_decay {θ a : ℝ} (hθ : 0 < θ) (ha : 0 < a) :
    Real.exp (-θ * (⌈Real.log a / θ⌉₊ : ℝ)) ≤ 1 / a := by
  have hceil := Nat.le_ceil (Real.log a / θ)
  have hmul := mul_le_mul_of_nonneg_left hceil (le_of_lt hθ)
  have hid : θ * (Real.log a / θ) = Real.log a := by field_simp [ne_of_gt hθ]
  rw [hid] at hmul
  calc
    Real.exp (-θ * (⌈Real.log a / θ⌉₊ : ℝ)) ≤ Real.exp (-Real.log a) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = 1 / a := by simp only [Real.exp_neg, Real.exp_log ha, one_div]

lemma batch_ceiling_bound {q : ℝ} (hq : 0 ≤ q) :
    ((max 1 ⌈q⌉₊ : ℕ) : ℝ) ≤ 1 + q := by
  rw [Nat.cast_max]
  norm_num only [Nat.cast_one]
  apply max_le
  · linarith
  · have h := Nat.ceil_lt_add_one hq
    linarith

lemma positive_stage_length_bound {μ γ : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hsmall : μ * γ ≤ 1) :
    ((⌈512 * Real.log 16 / (μ * γ)⌉₊ : ℕ) : ℝ) ≤
      (512 * Real.log 16 + 1) / (μ * γ) := by
  have hlog : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ 512 * Real.log 16 / (μ * γ) by positivity)
  have hone : 1 ≤ 1 / (μ * γ) := by
    apply (le_div_iff₀ (mul_pos hμ hγ)).2
    simpa using hsmall
  have hid : (512 * Real.log 16 + 1) / (μ * γ) =
      512 * Real.log 16 / (μ * γ) + 1 / (μ * γ) := by ring
  rw [hid]
  linarith

lemma single_stage_sample_bound {μ γ R σ : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hR : 0 < R) (hsmall : μ * γ ≤ 1) :
    ((max 1 ⌈γ * σ ^ 2 / (μ * R ^ 2)⌉₊ : ℕ) : ℝ) *
        ((⌈512 * Real.log 16 / (μ * γ)⌉₊ : ℕ) : ℝ) ≤
      (512 * Real.log 16 + 1) * (1 / (γ * μ) + σ ^ 2 / (μ ^ 2 * R ^ 2)) := by
  have hB := batch_ceiling_bound (show 0 ≤ γ * σ ^ 2 / (μ * R ^ 2) by positivity)
  have hK := positive_stage_length_bound hμ hγ hsmall
  have hprod := mul_le_mul hB hK (Nat.cast_nonneg _)
    (show 0 ≤ 1 + γ * σ ^ 2 / (μ * R ^ 2) by positivity)
  have hid :
      (1 + γ * σ ^ 2 / (μ * R ^ 2)) * ((512 * Real.log 16 + 1) / (μ * γ)) =
      (512 * Real.log 16 + 1) * (1 / (γ * μ) + σ ^ 2 / (μ ^ 2 * R ^ 2)) := by
    field_simp [ne_of_gt hμ, ne_of_gt hγ, ne_of_gt hR]
    <;> ring
  simpa only [hid] using hprod

lemma inner_polynomial_bound_to_exponential
    (Λ : ℕ → ℝ) {μ γ variance biasSq B : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hB : 0 < B)
    (hsmall : μ * γ ≤ 512) (hΛ : 0 ≤ Λ 0)
    (hσ : 0 ≤ variance) (hb : 0 ≤ biasSq)
    (hstep : ∀ t, Λ (t + 1) ≤
      (1 - μ * γ / 512) * Λ t + 6 * γ * biasSq + 2 * μ * γ ^ 2 * variance / B) :
    ∀ k, Λ k ≤ Real.exp (-μ * γ * k / 512) * Λ 0 +
      3072 * biasSq / μ + 1024 * γ * variance / B := by
  intro k
  have hg := inner_geometric_bound Λ hμ hγ hB hsmall hstep k
  have hq : 0 ≤ 1 - μ * γ / 512 := by linarith
  have he : 1 - μ * γ / 512 ≤ Real.exp (-μ * γ / 512) := by
    have h := Real.add_one_le_exp (-μ * γ / 512)
    linarith
  have hp : (1 - μ * γ / 512) ^ k ≤ (Real.exp (-μ * γ / 512)) ^ k :=
    pow_le_pow_left₀ hq he k
  have hpowexp : (Real.exp (-μ * γ / 512)) ^ k =
      Real.exp (-μ * γ * k / 512) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpowexp] at hp
  have htransient := mul_le_mul_of_nonneg_right hp hΛ
  have hfloor : 0 ≤ 3072 * biasSq / μ + 1024 * γ * variance / B := by positivity
  have hdiscard := mul_nonneg (pow_nonneg hq k) hfloor
  nlinarith only [hg, htransient, hdiscard]

lemma homotopy_budget_numerical_constants :
    (2 * 32768 * 1572864 * (512 * 15 + 1) : ℝ) ≤ 1125899906842624 ∧
    ((4 / 3) * 32768 ^ 2 * (512 * 15 + 1) : ℝ) ≤ 1125899906842624 ∧
    (512 * 786432 : ℝ) + 1 ≤ 1125899906842624 ∧
    (128 : ℝ) + 1 ≤ 1125899906842624 := by
  norm_num

end LongTails.Proofs.ProximalEf21Schedule


end Schedule


section CountedBudget

open scoped BigOperators

noncomputable section

namespace LongTails.Proofs.ProximalEf21CountedBudget

open LongTails.Proofs.ProximalEf21Schedule

noncomputable def mu (L : ℝ) (s : ℕ) : ℝ := 2 * L / (2 : ℝ) ^ s
noncomputable def gamma (L δ : ℝ) : ℝ := δ / (1572864 * L)
noncomputable def lastStage (L R ε : ℝ) : ℕ := ⌈Real.log (32768 * L * R ^ 2 / ε) / Real.log 2⌉₊
noncomputable def batches (L R σ δ : ℝ) (s : ℕ) : ℕ := max 1 ⌈gamma L δ * σ ^ 2 / (mu L s * R ^ 2)⌉₊
noncomputable def length (L R δ H : ℝ) (s : ℕ) : ℕ := if s = 0 then ⌈512 / (mu L 0 * gamma L δ) * Real.log (2 + 2 * H / (8192 * mu L 0 * R ^ 2))⌉₊ else ⌈512 * Real.log 16 / (mu L s * gamma L δ)⌉₊
noncomputable def samples (L R σ δ H ε : ℝ) : ℕ := ∑ s ∈ Finset.range (lastStage L R ε + 1), batches L R σ δ s * length L R δ H s
noncomputable def rounds (L R δ H ε : ℝ) : ℕ := ∑ s ∈ Finset.range (lastStage L R ε + 1), length L R δ H s
noncomputable def sampleBudget (L R σ δ H ε : ℝ) : ℕ := ⌈1152921504606846976 * (L * R ^ 2 / (δ * ε) + σ ^ 2 * R ^ 2 / ε ^ 2 + (1 / δ + σ ^ 2 / (L ^ 2 * R ^ 2)) * Real.log (2 + H / (L * R ^ 2)))⌉₊
noncomputable def roundBudget (L R δ H ε : ℝ) : ℕ := ⌈1152921504606846976 * (L * R ^ 2 / (δ * ε) + Real.log (2 + H / (L * R ^ 2)) / δ)⌉₊

lemma mu_positive {L : ℝ} (hL : 0 < L) (s : ℕ) : 0 < mu L s := by
  unfold mu
  positivity

lemma mu_le_initial {L : ℝ} (hL : 0 < L) (s : ℕ) : mu L s ≤ 2 * L := by
  have hp : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  unfold mu
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) s)).2
  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * L by positivity)]

lemma mu_dyadic (L : ℝ) (s : ℕ) : mu L s = 2 * mu L (s + 1) := by
  unfold mu
  rw [pow_succ]
  field_simp
  <;> ring

lemma mu_step_small {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (s : ℕ) : mu L s * gamma L δ ≤ 1 := by
  have hg : 0 < gamma L δ := by unfold gamma; positivity
  have hm := mul_le_mul_of_nonneg_right (mu_le_initial hL s) hg.le
  have hid : 2 * L * gamma L δ = δ / 786432 := by
    unfold gamma
    field_simp [ne_of_gt hL]
    <;> ring
  rw [hid] at hm
  linarith

lemma batches_positive (L R σ δ : ℝ) (s : ℕ) : 0 < batches L R σ δ s := by
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

lemma batch_floor {L R σ δ : ℝ} (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ)
    (s : ℕ) : gamma L δ * σ ^ 2 / (batches L R σ δ s : ℝ) ≤ mu L s * R ^ 2 := by
  have hμ := mu_positive hL s
  have hB : (0 : ℝ) < batches L R σ δ s := by exact_mod_cast batches_positive L R σ δ s
  have hmax : ⌈gamma L δ * σ ^ (2 : ℕ) / (mu L s * R ^ 2)⌉₊ ≤
      batches L R σ δ s := by
    exact le_max_right _ _
  have hlo : gamma L δ * σ ^ 2 / (mu L s * R ^ 2) ≤ (batches L R σ δ s : ℝ) := by
    calc
      gamma L δ * σ ^ 2 / (mu L s * R ^ 2) ≤
          (⌈gamma L δ * σ ^ (2 : ℕ) / (mu L s * R ^ 2)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (batches L R σ δ s : ℝ) := by exact_mod_cast hmax
  have h := (div_le_iff₀ (show 0 < mu L s * R ^ 2 by positivity)).mp hlo
  apply (div_le_iff₀ hB).2
  nlinarith only [h]

lemma positive_length_decay {L R δ H : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) {s : ℕ} (hs : s ≠ 0) :
    Real.exp (-mu L s * gamma L δ * (length L R δ H s : ℝ) / 512) ≤ 1 / 16 := by
  have hμ := mu_positive hL s
  have hg : 0 < gamma L δ := by unfold gamma; positivity
  have hid : 512 * Real.log 16 / (mu L s * gamma L δ) =
      Real.log 16 / (mu L s * gamma L δ / 512) := by ring
  have h := ceiling_exponential_decay
    (show 0 < mu L s * gamma L δ / 512 by positivity) (by norm_num : (0 : ℝ) < 16)
  unfold length
  rw [if_neg hs, hid]
  convert h using 1 <;> congr 1 <;> ring

lemma initial_length_decay {L R δ H : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hH : 0 ≤ H) :
    Real.exp (-mu L 0 * gamma L δ * (length L R δ H 0 : ℝ) / 512) * H ≤
      8192 * mu L 0 * R ^ 2 / 2 := by
  have hμ := mu_positive hL 0
  have hg : 0 < gamma L δ := by unfold gamma; positivity
  have ha : 0 < 2 + 2 * H / (8192 * mu L 0 * R ^ 2) := by positivity
  have hid : 512 / (mu L 0 * gamma L δ) *
      Real.log (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) =
      Real.log (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) /
        (mu L 0 * gamma L δ / 512) := by ring
  have he := ceiling_exponential_decay
    (show 0 < mu L 0 * gamma L δ / 512 by positivity) ha
  have he' : Real.exp (-mu L 0 * gamma L δ * (length L R δ H 0 : ℝ) / 512) ≤
      1 / (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) := by
    unfold length
    rw [if_pos rfl, hid]
    convert he using 1 <;> congr 1 <;> ring
  have hb := LongTails.Proofs.ProximalEf21ScalarCore.initialize_stage hH
    (show 0 < 8192 * mu L 0 * R ^ 2 by positivity)
  have hm := mul_le_mul_of_nonneg_right he' hH
  calc
    _ ≤ 1 / (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) * H := hm
    _ = H / (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) := by ring
    _ ≤ _ := hb

lemma initial_round_bound {L R δ H : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hH : 0 ≤ H) :
    (length L R δ H 0 : ℝ) ≤
      1073741824 / δ * Real.log (2 + H / (L * R ^ 2)) := by
  have hden : 0 < L * R ^ 2 := by positivity
  have hμ : 0 < mu L 0 := mu_positive hL 0
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    rw [Real.log_inv] at h
    norm_num at h
    linarith only [h]
  have hfrac_nonneg : 0 ≤ H / (L * R ^ 2) := div_nonneg hH hden.le
  have harg : 2 ≤ 2 + H / (L * R ^ 2) := by linarith only [hfrac_nonneg]
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 + H / (L * R ^ 2)) :=
    hlog2.trans (Real.log_le_log (by norm_num) harg)
  have hlognon : 0 ≤ Real.log (2 + H / (L * R ^ 2)) := by linarith only [hlog]
  have hid : mu L 0 * gamma L δ = δ / 786432 := by
    unfold mu gamma
    norm_num
    field_simp [ne_of_gt hL]
    <;> ring
  have hμ0 : mu L 0 = 2 * L := by simp [mu]
  have ha : 2 + 2 * H / (8192 * mu L 0 * R ^ 2) ≤ 2 + H / (L * R ^ 2) := by
    rw [hμ0]
    have hfrac : 2 * H / (8192 * (2 * L) * R ^ 2) =
        (1 / 8192 : ℝ) * (H / (L * R ^ 2)) := by ring
    rw [hfrac]
    linarith only [hfrac_nonneg]
  have ha_nonneg : 0 ≤ 2 * H / (8192 * mu L 0 * R ^ 2) := by positivity
  have ha_pos : 0 < 2 + 2 * H / (8192 * mu L 0 * R ^ 2) := by
    linarith only [ha_nonneg]
  have ha_one : 1 ≤ 2 + 2 * H / (8192 * mu L 0 * R ^ 2) := by
    linarith only [ha_nonneg]
  have hl := Real.log_le_log ha_pos ha
  have hq : 0 ≤ 512 / (mu L 0 * gamma L δ) *
      Real.log (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) := by
    have hlg := Real.log_nonneg ha_one
    rw [hid]
    positivity
  have hc := (Nat.ceil_lt_add_one hq).le
  change (length L R δ H 0 : ℝ) ≤
    512 / (mu L 0 * gamma L δ) * Real.log (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) + 1 at hc
  have hm := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ 512 / (mu L 0 * gamma L δ) by rw [hid]; positivity)
  have hcoef : 512 / (mu L 0 * gamma L δ) = 402653184 / δ := by
    rw [hid]
    field_simp [ne_of_gt hδ]
    <;> ring
  rw [hcoef] at hc hm
  have hunit : 1 ≤ (2 * Real.log (2 + H / (L * R ^ 2))) / δ := by
    apply (le_div_iff₀ hδ).2
    linarith only [hδ1, hlog]
  calc
    (length L R δ H 0 : ℝ) ≤
        402653184 / δ * Real.log (2 + 2 * H / (8192 * mu L 0 * R ^ 2)) + 1 := hc
    _ ≤ 402653184 / δ * Real.log (2 + H / (L * R ^ 2)) +
        (2 * Real.log (2 + H / (L * R ^ 2))) / δ := add_le_add hm hunit
    _ = (402653184 + 2) / δ * Real.log (2 + H / (L * R ^ 2)) := by ring
    _ ≤ 1073741824 / δ * Real.log (2 + H / (L * R ^ 2)) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by norm_num : (402653184 + 2 : ℝ) ≤ 1073741824) hδ.le)
        hlognon

lemma initial_sample_bound {L R σ δ H : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hH : 0 ≤ H) :
    (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) ≤
      1073741824 * (1 / δ + σ ^ 2 / (L ^ 2 * R ^ 2)) *
        Real.log (2 + H / (L * R ^ 2)) := by
  have hγ : 0 < gamma L δ := by unfold gamma; positivity
  have hμ := mu_positive hL 0
  have hB := batch_ceiling_bound (show 0 ≤ gamma L δ * σ ^ 2 / (mu L 0 * R ^ 2) by positivity)
  change (batches L R σ δ 0 : ℝ) ≤ 1 + gamma L δ * σ ^ 2 / (mu L 0 * R ^ 2) at hB
  have hK := initial_round_bound hL hR hδ hδ1 hH
  have hp := mul_le_mul hB hK (Nat.cast_nonneg _)
    (show 0 ≤ 1 + gamma L δ * σ ^ 2 / (mu L 0 * R ^ 2) by positivity)
  have hid : (1 + gamma L δ * σ ^ 2 / (mu L 0 * R ^ 2)) *
      (1073741824 / δ * Real.log (2 + H / (L * R ^ 2))) =
      1073741824 * (1 / δ + σ ^ 2 / (3145728 * L ^ 2 * R ^ 2)) *
        Real.log (2 + H / (L * R ^ 2)) := by
    unfold mu gamma
    norm_num
    field_simp [ne_of_gt hL, ne_of_gt hR, ne_of_gt hδ]
    <;> ring
  rw [hid] at hp
  have hσ : σ ^ 2 / (3145728 * L ^ 2 * R ^ 2) ≤ σ ^ 2 / (L ^ 2 * R ^ 2) := by
    have hq : 0 ≤ σ ^ 2 / (L ^ 2 * R ^ 2) := by positivity
    have heq : σ ^ 2 / (3145728 * L ^ 2 * R ^ 2) =
      (σ ^ 2 / (L ^ 2 * R ^ 2)) / 3145728 := by ring
    rw [heq]
    linarith
  have harg : 1 ≤ 2 + H / (L * R ^ 2) := by
    have hz : 0 ≤ H / (L * R ^ 2) := by positivity
    linarith only [hz]
  have hlog : 0 ≤ Real.log (2 + H / (L * R ^ 2)) := Real.log_nonneg harg
  have hsum : 1 / δ + σ ^ 2 / (3145728 * L ^ 2 * R ^ 2) ≤
      1 / δ + σ ^ 2 / (L ^ 2 * R ^ 2) := add_le_add le_rfl hσ
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1073741824)) hlog
  exact hp.trans hs

lemma exact_round_sum_bound {L R δ H ε : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (rounds L R δ H ε : ℝ) ≤ (length L R δ H 0 : ℝ) +
      (512 * Real.log 16 + 1) * (2 / (gamma L δ * mu L (lastStage L R ε))) := by
  have hγ : 0 < gamma L δ := by unfold gamma; positivity
  have hC : 0 ≤ 512 * Real.log 16 + 1 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
    linarith
  have hpoint : ∀ s, (length L R δ H s : ℝ) ≤
      (if s = 0 then (length L R δ H 0 : ℝ) else 0) +
      (512 * Real.log 16 + 1) / (mu L s * gamma L δ) := by
    intro s
    by_cases hs : s = 0
    · subst s
      have hμ := mu_positive hL 0
      have hh : 0 ≤ (512 * Real.log 16 + 1) / (mu L 0 * gamma L δ) := by positivity
      have hb : (length L R δ H 0 : ℝ) ≤ (length L R δ H 0 : ℝ) +
          (512 * Real.log 16 + 1) / (mu L 0 * gamma L δ) := by
        linarith only [hh]
      simpa using hb
    · simpa [length, hs] using
        positive_stage_length_bound (mu_positive hL s) hγ (mu_step_small hL hδ hδ1 s)
  have hs := Finset.sum_le_sum (fun s (_ : s ∈ Finset.range (lastStage L R ε + 1)) => hpoint s)
  have hz : (∑ s ∈ Finset.range (lastStage L R ε + 1),
      if s = 0 then (length L R δ H 0 : ℝ) else 0) = length L R δ H 0 := by simp
  have hsum := (dyadic_inverse_sums hL (lastStage L R ε)).1
  change (∑ s ∈ Finset.range (lastStage L R ε + 1), 1 / mu L s) ≤
    2 / mu L (lastStage L R ε) at hsum
  have hscaled := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (512 * Real.log 16 + 1) / gamma L δ by positivity)
  have hid (s : ℕ) : (512 * Real.log 16 + 1) / (mu L s * gamma L δ) =
      ((512 * Real.log 16 + 1) / gamma L δ) * (1 / mu L s) := by ring
  simp_rw [hid] at hs
  rw [Finset.sum_add_distrib, hz, ← Finset.mul_sum] at hs
  have hcount : (rounds L R δ H ε : ℝ) =
      ∑ s ∈ Finset.range (lastStage L R ε + 1), (length L R δ H s : ℝ) := by
    simp [rounds, Nat.cast_sum]
  calc
    (rounds L R δ H ε : ℝ) =
        ∑ s ∈ Finset.range (lastStage L R ε + 1), (length L R δ H s : ℝ) := hcount
    _ ≤ (length L R δ H 0 : ℝ) + (512 * Real.log 16 + 1) / gamma L δ *
        (∑ s ∈ Finset.range (lastStage L R ε + 1), 1 / mu L s) := hs
    _ ≤ (length L R δ H 0 : ℝ) +
        (512 * Real.log 16 + 1) / gamma L δ * (2 / mu L (lastStage L R ε)) :=
      add_le_add le_rfl hscaled
    _ = (length L R δ H 0 : ℝ) +
        (512 * Real.log 16 + 1) * (2 / (gamma L δ * mu L (lastStage L R ε))) := by ring

lemma exact_sample_sum_bound {L R σ δ H ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (samples L R σ δ H ε : ℝ) ≤
      (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) +
      (512 * Real.log 16 + 1) *
        (2 / (gamma L δ * mu L (lastStage L R ε)) +
          4 * σ ^ 2 / (3 * (mu L (lastStage L R ε)) ^ 2 * R ^ 2)) := by
  have hγ : 0 < gamma L δ := by unfold gamma; positivity
  have hC : 0 ≤ 512 * Real.log 16 + 1 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
    linarith
  have hpoint : ∀ s, (batches L R σ δ s : ℝ) * (length L R δ H s : ℝ) ≤
      (if s = 0 then (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) else 0) +
      (512 * Real.log 16 + 1) *
        (1 / (gamma L δ * mu L s) + σ ^ 2 / ((mu L s) ^ 2 * R ^ 2)) := by
    intro s
    by_cases hs : s = 0
    · subst s
      have hμ := mu_positive hL 0
      have hh : 0 ≤ (512 * Real.log 16 + 1) *
          (1 / (gamma L δ * mu L 0) + σ ^ 2 / ((mu L 0) ^ 2 * R ^ 2)) := by positivity
      have hb : (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) ≤
          (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) +
            (512 * Real.log 16 + 1) *
              (1 / (gamma L δ * mu L 0) + σ ^ 2 / ((mu L 0) ^ 2 * R ^ 2)) := by
        linarith only [hh]
      simpa using hb
    · simpa [batches, length, hs] using
        single_stage_sample_bound (mu_positive hL s) hγ hR (mu_step_small hL hδ hδ1 s)
  have hs := Finset.sum_le_sum (fun s (_ : s ∈ Finset.range (lastStage L R ε + 1)) => hpoint s)
  have hz : (∑ s ∈ Finset.range (lastStage L R ε + 1),
      if s = 0 then (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) else 0) =
      (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) := by simp
  obtain ⟨h1, h2⟩ := dyadic_inverse_sums hL (lastStage L R ε)
  change (∑ s ∈ Finset.range (lastStage L R ε + 1), 1 / mu L s) ≤
    2 / mu L (lastStage L R ε) at h1
  change (∑ s ∈ Finset.range (lastStage L R ε + 1), 1 / (mu L s) ^ 2) ≤
    4 / (3 * (mu L (lastStage L R ε)) ^ 2) at h2
  have h1s := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 / gamma L δ by positivity)
  have h2s := mul_le_mul_of_nonneg_left h2 (show 0 ≤ σ ^ 2 / R ^ 2 by positivity)
  have hid (s : ℕ) : 1 / (gamma L δ * mu L s) + σ ^ 2 / ((mu L s) ^ 2 * R ^ 2) =
      (1 / gamma L δ) * (1 / mu L s) + (σ ^ 2 / R ^ 2) * (1 / (mu L s) ^ 2) := by ring
  simp_rw [hid] at hs
  rw [Finset.sum_add_distrib, hz, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hcombined := mul_le_mul_of_nonneg_left (add_le_add h1s h2s) hC
  have hcount : (samples L R σ δ H ε : ℝ) =
      ∑ s ∈ Finset.range (lastStage L R ε + 1),
        (batches L R σ δ s : ℝ) * (length L R δ H s : ℝ) := by
    simp [samples, Nat.cast_sum, Nat.cast_mul]
  calc
    (samples L R σ δ H ε : ℝ) = ∑ s ∈ Finset.range (lastStage L R ε + 1),
        (batches L R σ δ s : ℝ) * (length L R δ H s : ℝ) := hcount
    _ ≤ (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) +
        (512 * Real.log 16 + 1) *
          ((1 / gamma L δ) * (∑ s ∈ Finset.range (lastStage L R ε + 1), 1 / mu L s) +
            (σ ^ 2 / R ^ 2) * (∑ s ∈ Finset.range (lastStage L R ε + 1), 1 / (mu L s) ^ 2)) := hs
    _ ≤ (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) +
        (512 * Real.log 16 + 1) *
          ((1 / gamma L δ) * (2 / mu L (lastStage L R ε)) +
            (σ ^ 2 / R ^ 2) * (4 / (3 * (mu L (lastStage L R ε)) ^ 2))) :=
      add_le_add le_rfl hcombined
    _ = (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) +
        (512 * Real.log 16 + 1) *
          (2 / (gamma L δ * mu L (lastStage L R ε)) +
            4 * σ ^ 2 / (3 * (mu L (lastStage L R ε)) ^ 2 * R ^ 2)) := by ring

lemma terminal_inverse_bounds {L R ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) (hεL : ε ≤ L * R ^ 2) :
    1 / mu L (lastStage L R ε) ≤ 32768 * R ^ 2 / ε ∧
      1 / (mu L (lastStage L R ε)) ^ 2 ≤ (32768 * R ^ 2 / ε) ^ 2 := by
  have hl := (terminal_regularization_bounds hL hR hε hεL).1.le
  change ε / (32768 * R ^ 2) ≤ mu L (lastStage L R ε) at hl
  have hm := mu_positive hL (lastStage L R ε)
  have h1 : 1 / mu L (lastStage L R ε) ≤ 32768 * R ^ 2 / ε := by
    apply (div_le_div_iff₀ hm hε).2
    have h := (div_le_iff₀ (show 0 < 32768 * R ^ 2 by positivity)).mp hl
    simpa [mul_comm] using h
  refine ⟨h1, ?_⟩
  have ha : 0 ≤ 1 / mu L (lastStage L R ε) := by positivity
  have hb : 0 ≤ 32768 * R ^ 2 / ε := by positivity
  have hsq : (1 / mu L (lastStage L R ε)) ^ 2 ≤ (32768 * R ^ 2 / ε) ^ 2 := by
    nlinarith
  simpa only [div_pow, one_pow] using hsq

lemma leading_cost_bound {L R σ δ ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ)
    (hε : 0 < ε) (hεL : ε ≤ L * R ^ 2) :
    (512 * Real.log 16 + 1) *
      (2 / (gamma L δ * mu L (lastStage L R ε)) +
        4 * σ ^ 2 / (3 * (mu L (lastStage L R ε)) ^ 2 * R ^ 2)) ≤
      1125899906842624 * (L * R ^ 2 / (δ * ε) + σ ^ 2 * R ^ 2 / ε ^ 2) := by
  have hγ : 0 < gamma L δ := by unfold gamma; positivity
  obtain ⟨h1, h2⟩ := terminal_inverse_bounds hL hR hε hεL
  have hlog : Real.log 16 ≤ 15 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)
    norm_num at h
    exact h
  have hC : 0 ≤ 512 * Real.log 16 + 1 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
    linarith
  have ha := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 / gamma L δ by positivity)
  have hb := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4 * σ ^ 2 / (3 * R ^ 2) by positivity)
  have hcoef : 512 * Real.log 16 + 1 ≤ 7681 := by linarith
  have hsum := add_le_add ha hb
  have hright : 0 ≤ (2 / gamma L δ) * (32768 * R ^ 2 / ε) +
      (4 * σ ^ 2 / (3 * R ^ 2)) * (32768 * R ^ 2 / ε) ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hC
  have hprod := hscaled.trans (mul_le_mul_of_nonneg_right hcoef hright)
  have haid : (2 / gamma L δ) * (32768 * R ^ 2 / ε) =
      (2 * 32768 * 1572864 : ℝ) * (L * R ^ 2 / (δ * ε)) := by
    unfold gamma
    field_simp [ne_of_gt hL, ne_of_gt hδ, ne_of_gt hε]
    <;> ring
  have hbid : (4 * σ ^ 2 / (3 * R ^ 2)) * (32768 * R ^ 2 / ε) ^ 2 =
      ((4 / 3) * 32768 ^ 2 : ℝ) * (σ ^ 2 * R ^ 2 / ε ^ 2) := by
    field_simp [ne_of_gt hR, ne_of_gt hε]
    <;> ring
  rw [haid, hbid] at hprod
  have ha0 : 0 ≤ L * R ^ 2 / (δ * ε) := by positivity
  have hb0 : 0 ≤ σ ^ 2 * R ^ 2 / ε ^ 2 := by positivity
  have hca : (7681 * (2 * 32768 * 1572864) : ℝ) ≤ 1125899906842624 := by norm_num
  have hcb : (7681 * ((4 / 3) * 32768 ^ 2) : ℝ) ≤ 1125899906842624 := by norm_num
  have hca' := mul_le_mul_of_nonneg_right hca ha0
  have hcb' := mul_le_mul_of_nonneg_right hcb hb0
  have hLid : 2 / (gamma L δ * mu L (lastStage L R ε)) +
      4 * σ ^ 2 / (3 * (mu L (lastStage L R ε)) ^ 2 * R ^ 2) =
      (2 / gamma L δ) * (1 / mu L (lastStage L R ε)) +
      (4 * σ ^ 2 / (3 * R ^ 2)) * (1 / (mu L (lastStage L R ε)) ^ 2) := by ring
  have hnumeric :
      7681 * ((2 * 32768 * 1572864 : ℝ) * (L * R ^ 2 / (δ * ε)) +
        ((4 / 3) * 32768 ^ 2 : ℝ) * (σ ^ 2 * R ^ 2 / ε ^ 2)) ≤
      1125899906842624 * (L * R ^ 2 / (δ * ε) + σ ^ 2 * R ^ 2 / ε ^ 2) := by
    convert (add_le_add hca' hcb') using 1 <;> ring
  rw [hLid]
  exact hprod.trans hnumeric

lemma counted_sample_budget {L R σ δ H ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hH : 0 ≤ H) (hε : 0 < ε) (hεL : ε ≤ L * R ^ 2) :
    samples L R σ δ H ε ≤ sampleBudget L R σ δ H ε := by
  have hs := exact_sample_sum_bound (R := R) (σ := σ) (H := H) (ε := ε) hL hR hδ hδ1
  have hi := initial_sample_bound (σ := σ) hL hR hδ hδ1 hH
  have hl := leading_cost_bound (σ := σ) hL hR hδ hε hεL
  have harg : 1 ≤ 2 + H / (L * R ^ 2) := by
    have hz : 0 ≤ H / (L * R ^ 2) := by positivity
    linarith only [hz]
  have hlog : 0 ≤ Real.log (2 + H / (L * R ^ 2)) := Real.log_nonneg harg
  have ha : 0 ≤ L * R ^ 2 / (δ * ε) + σ ^ 2 * R ^ 2 / ε ^ 2 := by positivity
  have hb : 0 ≤ (1 / δ + σ ^ 2 / (L ^ 2 * R ^ 2)) * Real.log (2 + H / (L * R ^ 2)) := by positivity
  have ha' := mul_le_mul_of_nonneg_right
    (by norm_num : (1125899906842624 : ℝ) ≤ 1152921504606846976) ha
  have hb' := mul_le_mul_of_nonneg_right
    (by norm_num : (1073741824 : ℝ) ≤ 1152921504606846976) hb
  have hi' : (batches L R σ δ 0 : ℝ) * (length L R δ H 0 : ℝ) ≤
      1073741824 * ((1 / δ + σ ^ 2 / (L ^ 2 * R ^ 2)) *
        Real.log (2 + H / (L * R ^ 2))) := by
    simpa only [mul_assoc] using hi
  have hcombined := hs.trans (add_le_add (hi'.trans hb') (hl.trans ha'))
  have hreal : (samples L R σ δ H ε : ℝ) ≤
      1152921504606846976 * (L * R ^ 2 / (δ * ε) + σ ^ 2 * R ^ 2 / ε ^ 2 +
        (1 / δ + σ ^ 2 / (L ^ 2 * R ^ 2)) * Real.log (2 + H / (L * R ^ 2))) := by
    convert hcombined using 1 <;> ring
  have hc := hreal.trans (Nat.le_ceil _)
  exact_mod_cast hc

lemma counted_round_budget {L R δ H ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hH : 0 ≤ H) (hε : 0 < ε) (hεL : ε ≤ L * R ^ 2) :
    rounds L R δ H ε ≤ roundBudget L R δ H ε := by
  have hs := exact_round_sum_bound (R := R) (H := H) (ε := ε) hL hδ hδ1
  have hi := initial_round_bound hL hR hδ hδ1 hH
  have hl := leading_cost_bound (σ := 0) hL hR hδ hε hεL
  norm_num only [zero_pow, zero_mul, mul_zero, zero_div, add_zero] at hl
  have harg : 1 ≤ 2 + H / (L * R ^ 2) := by
    have hz : 0 ≤ H / (L * R ^ 2) := by positivity
    linarith only [hz]
  have hlog : 0 ≤ Real.log (2 + H / (L * R ^ 2)) := Real.log_nonneg harg
  have ha : 0 ≤ L * R ^ 2 / (δ * ε) := by positivity
  have hb : 0 ≤ Real.log (2 + H / (L * R ^ 2)) / δ := by positivity
  have ha' := mul_le_mul_of_nonneg_right
    (by norm_num : (1125899906842624 : ℝ) ≤ 1152921504606846976) ha
  have hb' := mul_le_mul_of_nonneg_right
    (by norm_num : (1073741824 : ℝ) ≤ 1152921504606846976) hb
  have hi' : (length L R δ H 0 : ℝ) ≤
      1073741824 * (Real.log (2 + H / (L * R ^ 2)) / δ) := by
    convert hi using 1 <;> ring
  have hcombined := hs.trans (add_le_add (hi'.trans hb') (hl.trans ha'))
  have hreal : (rounds L R δ H ε : ℝ) ≤
      1152921504606846976 * (L * R ^ 2 / (δ * ε) + Real.log (2 + H / (L * R ^ 2)) / δ) := by
    convert hcombined using 1 <;> ring
  have hc := hreal.trans (Nat.le_ceil _)
  exact_mod_cast hc

end LongTails.Proofs.ProximalEf21CountedBudget

end

end CountedBudget


section BudgetBridge

noncomputable section

namespace LongTails.Proofs.ProximalEf21BudgetBridge

open LongTails.Setups.StochasticProximalEf21
open LongTails.Proofs.ProximalEf21CountedBudget

noncomputable def budget : (let S := LongTails.Setups.StochasticProximalEf21.spec; S.Params → Fin S.numOracles → ℕ) := fun p i => if i = 3 then 0 else if i = 0 then ⌈1152921504606846976 * (p.L * p.R ^ 2 / (p.δ * p.ε) + p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 + (1 / p.δ + p.σ ^ 2 / (p.L ^ 2 * p.R ^ 2)) * Real.log (2 + p.H / (p.L * p.R ^ 2)))⌉₊ else ⌈1152921504606846976 * (p.L * p.R ^ 2 / (p.δ * p.ε) + Real.log (2 + p.H / (p.L * p.R ^ 2)) / p.δ)⌉₊

lemma executionStep_eq (p : Params) : executionStep p = gamma p.L p.δ := rfl
lemma regularization_eq (p : Params) (s : ℕ) : regularization p s = mu p.L s := rfl
lemma finalStage_eq (p : Params) : finalStage p = lastStage p.L p.R p.ε := rfl
lemma batchSize_eq (p : Params) (s : ℕ) : batchSize p s = batches p.L p.R p.σ p.δ s := rfl
lemma stageLength_eq (p : Params) (s : ℕ) : stageLength p s = ProximalEf21CountedBudget.length p.L p.R p.δ p.H s := rfl
lemma iterationCount_eq (p : Params) : iterationCount p = rounds p.L p.R p.δ p.H p.ε := rfl
lemma samplesPerWorker_eq (p : Params) : samplesPerWorker p = samples p.L p.R p.σ p.δ p.H p.ε := rfl

lemma oracle_budget_sufficient (p : Params)
    (hp : LongTails.Setups.StochasticProximalEf21.spec.valid p) :
    samplesPerWorker p ≤ budget p 0 ∧
    iterationCount p ≤ budget p 1 ∧
    iterationCount p ≤ budget p 2 ∧
    budget p 3 = 0 := by
  rcases hp with ⟨hn, hL, hR, hσ, hδ, hδ1, hε, hεL, hH⟩
  have hs := counted_sample_budget (σ := p.σ) hL hR hδ hδ1 hH hε hεL
  have ht := counted_round_budget hL hR hδ hδ1 hH hε hεL
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [samplesPerWorker_eq, budget, sampleBudget] using hs
  · simpa [iterationCount_eq, budget, roundBudget] using ht
  · simpa [iterationCount_eq, budget, roundBudget] using ht
  · simp [budget]

lemma all_worker_costs (p : Params)
    (hp : LongTails.Setups.StochasticProximalEf21.spec.valid p) :
    allWorkerSamples p ≤ p.workers * budget p 0 ∧
    allWorkerMessages p ≤ p.workers * budget p 1 := by
  obtain ⟨hs, ht, _, _⟩ := oracle_budget_sufficient p hp
  exact ⟨Nat.mul_le_mul_left p.workers hs, Nat.mul_le_mul_left p.workers ht⟩

end LongTails.Proofs.ProximalEf21BudgetBridge

end

end BudgetBridge
