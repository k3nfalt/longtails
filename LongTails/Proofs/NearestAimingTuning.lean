import LongTails.Setups.LocalStrongAiming
import LongTails.Proofs.GdPL
import Mathlib.Tactic

namespace OracleTemplate.NearestAiming

open LongTails.Setups.LocalStrongAiming

lemma parameters (p : Params) (hp : spec.valid p) :
    let a := Real.sqrt p.μ
    let s := 1 / (2 * Real.sqrt p.L)
    let B := 2 * Real.sqrt p.Δ
    0 < a ∧ 0 < s ∧ a * s ≤ 1 / 2 ∧ a ^ 2 = p.μ ∧
      s ^ 2 * p.L = 1 / 4 ∧
      (2 * Real.sqrt (p.μ * p.L)) * s ^ 2 = a * s ∧
      0 ≤ B ∧ B ^ 2 / 2 = 2 * p.Δ ∧ B ≤ a * p.r / 8 := by
  obtain ⟨hμ, hμL, hr, hΔ, hsmall, hε⟩ := hp
  have hL : 0 < p.L := hμ.trans_le hμL
  have ha : 0 < Real.sqrt p.μ := Real.sqrt_pos.mpr hμ
  have hLs : 0 < Real.sqrt p.L := Real.sqrt_pos.mpr hL
  have ha2 := Real.sq_sqrt hμ.le
  have hLs2 := Real.sq_sqrt hL.le
  have hΔ2 := Real.sq_sqrt hΔ
  dsimp only
  refine ⟨ha, by positivity, ?_, ha2, ?_, ?_, by positivity, ?_, ?_⟩
  · have h := Real.sqrt_le_sqrt hμL
    calc
      _ = Real.sqrt p.μ / (2 * Real.sqrt p.L) := by ring
      _ ≤ 1 / 2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  · field_simp
    nlinarith
  · rw [Real.sqrt_mul hμ.le]
    field_simp
  · nlinarith
  · have har : 0 ≤ Real.sqrt p.μ * p.r := mul_nonneg ha.le hr.le
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    have he : (16 * Real.sqrt p.Δ) ^ 2 ≤ (Real.sqrt p.μ * p.r) ^ 2 := by
      simp only [mul_pow, ha2]
      nlinarith only [hsmall, hΔ2]
    have hb := (sq_le_sq₀ (by positivity : 0 ≤ 16 * Real.sqrt p.Δ) har).mp he
    nlinarith only [hb]

lemma accuracy_budget (p : Params) (hp : spec.valid p) (K : ℕ)
    (hK : ⌈2 * Real.sqrt (p.L / p.μ) * Real.log (1 + 2 * p.Δ / p.ε)⌉₊ ≤ K) :
    (1 - Real.sqrt p.μ * (1 / (2 * Real.sqrt p.L))) ^ K * (2 * p.Δ) ≤ p.ε := by
  have ht := parameters p hp
  dsimp only at ht
  have hμ := hp.1
  have hL : 0 < p.L := hμ.trans_le hp.2.1
  have ha : 0 < Real.sqrt p.μ := Real.sqrt_pos.mpr hμ
  have hsL : 0 < Real.sqrt p.L := Real.sqrt_pos.mpr hL
  have he : 1 / (Real.sqrt p.μ * (1 / (2 * Real.sqrt p.L))) =
      2 * Real.sqrt (p.L / p.μ) := by
    rw [Real.sqrt_div hL.le]
    field_simp
  have hΔ := hp.2.2.2.1
  have h := PLGradient.geometric_budget 1
    (Real.sqrt p.μ * (1 / (2 * Real.sqrt p.L))) (2 * p.Δ) p.ε
    (by positivity) (by linarith [ht.2.2.1])
    (by positivity) hp.2.2.2.2.2 K (by simpa only [div_one, he] using hK)
  simpa only [div_one, he] using h

end OracleTemplate.NearestAiming
