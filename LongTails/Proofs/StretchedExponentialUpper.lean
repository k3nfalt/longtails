import LongTails.Proofs.StretchedExponentialMarkovInclusion
import LongTails.Theorems.AcceleratedHeavyTailedMarkovConvex

namespace OracleTemplate.StretchedExponentialUpperBound

open LongTails.Setups.StretchedExponentialMarkovConvex

noncomputable def mixingTarget (p : Params) : ℝ :=
  256 * p.L * p.R ^ 2 / p.ε + 64 * (256 * p.σ * p.R / p.ε) ^ (p.α / (p.α - 1))

lemma mixingTarget_gt_one (p : Params) (hp : spec.valid p) : 1 < mixingTarget p := by
  rcases hp with ⟨_, hL, hR, hσ, _, _, _, _, _, hε, hLR, _⟩
  have hdet : (4 : ℝ) ≤ p.L * p.R ^ 2 / p.ε := (le_div_iff₀ hε).mpr hLR
  have hnoise : 0 ≤ (256 * p.σ * p.R / p.ε) ^ (p.α / (p.α - 1)) := by positivity
  unfold mixingTarget
  have he : 256 * p.L * p.R ^ 2 / p.ε = 256 * (p.L * p.R ^ 2 / p.ε) := by ring
  rw [he]
  linarith

lemma inverse_log_power {x : ℝ} (hx : 1 < x) : x ^ (1 / Real.log x) = Real.exp 1 := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
  congr 1
  field_simp [(Real.log_pos hx).ne']

lemma inherited_budget (p : Params) (hp : spec.valid p) (i : Fin 1) :
    HeavyTailedMarkovGradient.budget (p.polynomial (Real.log (mixingTarget p))) i =
      max 1 ⌈Real.sqrt (32 * p.L * p.R ^ 2 / p.ε) +
        (256 * p.σ * p.R / p.ε) ^ (p.α / (p.α - 1))⌉₊ *
      max 1 ⌈Real.exp 1 * p.τ * (Real.log (mixingTarget p) / p.γ) ^ (1 / p.γ)⌉₊ := by
  have hx := mixingTarget_gt_one p hp
  change max 1 ⌈Real.sqrt (32 * p.L * p.R ^ 2 / p.ε) +
      (256 * p.σ * p.R / p.ε) ^ (p.α / (p.α - 1))⌉₊ *
    max 1 ⌈p.τ * (Real.log (mixingTarget p) / p.γ) ^ (1 / p.γ) *
      mixingTarget p ^ (1 / Real.log (mixingTarget p))⌉₊ = _
  rw [inverse_log_power hx]
  congr 3
  ring

lemma inherited_budget_simplified (p : Params) (hp : spec.valid p) (i : Fin 1) :
    HeavyTailedMarkovGradient.budget (p.polynomial (Real.log (mixingTarget p))) i =
      ⌈Real.sqrt (32 * p.L * p.R ^ 2 / p.ε) +
        (256 * p.σ * p.R / p.ε) ^ (p.α / (p.α - 1))⌉₊ *
      ⌈Real.exp 1 * p.τ * (Real.log (mixingTarget p) / p.γ) ^ (1 / p.γ)⌉₊ := by
  have hβ : 0 < Real.log (mixingTarget p) := Real.log_pos (mixingTarget_gt_one p hp)
  rcases hp with ⟨hd, hL, hR, hσ, hα, hα2, hτ, hγ, hγ1, hε, rest⟩
  have ht : 0 < p.τ := by linarith
  have hN : 0 < Real.sqrt (32 * p.L * p.R ^ 2 / p.ε) +
      (256 * p.σ * p.R / p.ε) ^ (p.α / (p.α - 1)) := by positivity
  have hm : 0 < Real.exp 1 * p.τ * (Real.log (mixingTarget p) / p.γ) ^ (1 / p.γ) := by positivity
  rw [inherited_budget p ⟨hd, hL, hR, hσ, hα, hα2, hτ, hγ, hγ1, hε, rest⟩ i,
    max_eq_right (Nat.one_le_ceil_iff.mpr hN), max_eq_right (Nat.one_le_ceil_iff.mpr hm)]

lemma transfer (B : Params → ℕ)
    (hB : ∀ p, spec.valid p → HeavyTailedMarkovGradient.budget
      (p.polynomial (Real.log (mixingTarget p))) = fun _ => B p) :
    Convergence spec (fun p _ => B p) := by
  obtain ⟨make, correct, _⟩ := HeavyTailedMarkovGradient.result
  refine ⟨fun p => make (p.polynomial (Real.log (mixingTarget p))), ?_, fun _ _ => trivial⟩
  intro p hp f O h
  have hβ : 0 < Real.log (mixingTarget p) := Real.log_pos (mixingTarget_gt_one p hp)
  let inc := StretchedExponentialMarkov.polynomialInclusion (Real.log (mixingTarget p)) hβ
  have hv := inc.valid p hp
  have ho := inc.admissible p hp f O h
  have hr := correct (p.polynomial (Real.log (mixingTarget p))) hv f O ho
  rw [hB p hp] at hr
  exact hr

end OracleTemplate.StretchedExponentialUpperBound
