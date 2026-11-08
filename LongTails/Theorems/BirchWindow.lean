import LongTails.Setups.BirchWindow
import LongTails.Proofs.BirchWindowExecution
import LongTails.Proofs.BirchWindowMoments
import LongTails.Proofs.BirchNonEuclideanComposition

namespace LongTails.Theorems.BirchWindow

open Finset MeasureTheory OracleTemplate
open OracleTemplate.NormBallLMO
open LongTails.Setups.BirchWindow
open LongTails.Algorithms.BirchWindow
open LongTails.Proofs.BirchWindow
open LongTails.Setups.UscgConstant (dualNorm IsBallLMO)

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 1 + ⌈32 * p.κ * p.σ ^ 2 / p.ε⌉₊ + ⌈48 * p.L * (1 + (⌈32 * p.κ * p.σ ^ 2 / p.ε⌉₊ : ℝ)) * p.Δ / p.ε⌉₊

theorem result : Convergence LongTails.Setups.BirchWindow.spec budget := by
  classical
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp I O hI
  rcases hp with ⟨hdef, hcont, hL, _, hε, _, ⟨w⟩⟩
  rcases hI with ⟨hf, Ω, m, horacle⟩
  let := m
  rcases horacle with ⟨μ, P, g, hiid, hg, rfl⟩
  let q := native p
  let B := batchSize p
  let K := horizon p
  let η := stepSize p
  let lmo := LongTails.Algorithms.BirchNonEuclideanFramework.chosenLMO q
  let a := program B K η
  have hB : 0 < B := by dsimp [B, batchSize]; omega
  have hK : 0 < K := by dsimp [K, horizon]; omega
  have hb : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hk : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hη : 0 < η := by change 0 < 1 / (4 * p.L * B); positivity
  have hsmall : η * p.L * B = 1 / 4 := by
    change (1 / (4 * p.L * B)) * p.L * B = 1 / 4
    field_simp
  have hstep : η * p.L ≤ 1 / 2 := by
    have hb1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
    have hh := mul_le_mul_of_nonneg_left hb1 (mul_nonneg hη.le hL.le)
    nlinarith only [hh, hsmall]
  have hcount : a.outputCount + 1 = K := by change K - 1 + 1 = K; omega
  have hbudget : budget p = fun _ => calls B K := by
    funext i
    simp only [budget, B, K, calls, horizon, batchSize, Nat.cast_add, Nat.cast_one]
    omega
  obtain ⟨R, hRpos, hRbound⟩ :=
    LongTails.Proofs.BirchLmoExistence.exists_norm_le_seminorm p.N hdef hcont
  have hR : ∀ v, q.N v ≤ 1 → ‖v‖ ≤ R := fun v hv => (hRbound v).trans (by
    change p.N v ≤ 1 at hv
    nlinarith)
  have hlmo : IsBallLMO q.N 1 lmo :=
    LongTails.Proofs.BirchNonEuclideanComposition.native_chosenLMO_valid q hdef hcont
  let X := fun k (ξ : ℕ → Ω) => iterate q B η lmo (fun j x => g x (ξ j)) k
  let F := fun k (ξ : ℕ → Ω) => dualNorm p.N (gradient I.f (X k ξ)) ^ 2
  have hmain (k : ℕ) : Measurable (X k) :=
    iterate_measurable q B η lmo hlmo.measurable g hg.measurable hR hRpos.le k
  have hfm (k : ℕ) : Measurable (F k) :=
    ((continuous_dualNorm hR hRpos.le).measurable.comp
      ((measurable_gradient_space I.f).comp (hmain k))).pow_const 2
  have henergy := expected_window q B K hB η hη hL hstep hsmall.le lmo hlmo I hf
    μ P hiid g hg w hR hRpos.le hdef
  have hfi (k : ℕ) (hk : k < K) : Integrable (F k) (P : Measure (ℕ → Ω)) := by
    apply henergy.1.mono' (hfm k).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact single_le_sum (f := fun j => F j ξ) (fun j _ => sq_nonneg _) (mem_range.mpr hk))
  have hKceil : 48 * p.L * (B : ℝ) * p.Δ / p.ε ≤ K := by
    change _ ≤ ((1 + ⌈48 * p.L * B * p.Δ / p.ε⌉₊ : ℕ) : ℝ)
    rw [Nat.cast_add, Nat.cast_one]
    exact (Nat.le_ceil _).trans (by linarith)
  have hBceil : 32 * p.κ * p.σ ^ 2 / p.ε ≤ B := by
    change _ ≤ ((1 + ⌈32 * p.κ * p.σ ^ 2 / p.ε⌉₊ : ℕ) : ℝ)
    rw [Nat.cast_add, Nat.cast_one]
    exact (Nat.le_ceil _).trans (by linarith)
  have hdet : 6 * p.Δ / η ≤ p.ε * K / 2 := by
    have h := (div_le_iff₀ hε).mp hKceil
    have he : 6 * p.Δ / η = 24 * p.L * (B : ℝ) * p.Δ := by
      change 6 * p.Δ / (1 / (4 * p.L * B)) = _
      rw [div_div_eq_mul_div, div_one]
      ring
    rw [he]
    linarith
  have hnoise : 16 * (p.κ * p.σ ^ 2 / B) ≤ p.ε / 2 := by
    have h := (div_le_iff₀ hε).mp hBceil
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hb).2 (by nlinarith only [h])
  have hbound : (∫ ξ, ∑ k ∈ range K, F k ξ ∂(P : Measure (ℕ → Ω))) ≤ p.ε * K := by
    apply henergy.2.trans
    have h := mul_le_mul_of_nonneg_right hnoise hk.le
    change 6 * p.Δ / η + 16 * K * (p.κ * p.σ ^ 2 / B) ≤ _
    linarith only [hdet, h]
  have hu := LongTails.Proofs.BirchNonEuclideanCertificate.uniform_integral a.outputCount P
    (fun j => F j.val) (fun j => hfi j.val (hcount ▸ j.isLt))
  have ha : (1 / (((a.outputCount + 1 : ℕ) : ℝ))) *
      (∑ j : Fin (a.outputCount + 1), ∫ ξ, F j.val ξ ∂(P : Measure (ℕ → Ω))) ≤ p.ε := by
    rw [Fin.sum_univ_eq_sum_range (fun j => ∫ ξ, F j ξ ∂(P : Measure (ℕ → Ω))), hcount,
      ← integral_finsetSum _ (fun k h => hfi k (mem_range.mp h)), one_div, ← div_eq_inv_mul]
    exact (div_le_iff₀ hk).2 hbound
  rw [hbudget]
  let out := fun z : Fin (a.outputCount + 1) × (ℕ → Ω) =>
    execute (OracleTemplate.BirchSgd.gradientOracle P g) (algorithm p)
      (fun _ => calls B K) z.1 z.2
  have hout : out = fun z => X z.1.val z.2 := by
    funext z
    exact execute_window q B K hB hK η lmo P g z.1 z.2
  change Measurable out ∧ Integrable (fun z => dualNorm p.N (gradient I.f (out z)) ^ 2) _ ∧
    (∫ z, dualNorm p.N (gradient I.f (out z)) ^ 2 ∂_) ≤ p.ε
  rw [hout]
  exact ⟨measurable_from_prod_countable_right (fun j => hmain j.val), hu.1, hu.2.le.trans ha⟩

end LongTails.Theorems.BirchWindow
