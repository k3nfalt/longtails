import LongTails.Algorithms.CyclicPerceptronLinearComparison
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CyclicPerceptronLinearComparison

open LongTails.Setups.CyclicFullWidthPerceptron
open LongTails.Algorithms.CyclicPerceptronLinearComparison

lemma linear_integer_obstruction {d : ℕ} (μ ν T : ℝ) (a b : ℕ) (U u : Features d)
    (hμ : 0 < μ) (hν : 0 ≤ ν) (hT : 0 ≤ T) (hTb : T ≤ b * μ ^ 2)
    (hU : ‖U‖ ≤ b) (hu : ‖u‖ ≤ 1)
    (href : 0 < (a : ℝ) - b - T)
    (hneg : 0 < -(1 + ν) * ((a : ℝ) - b - T) + μ ^ 2 * ⟪U, u⟫) :
    1 / (2 * μ ^ 2) < (b : ℝ) := by
  have hab : b < a := by
    by_contra hh
    have hh' : (a : ℝ) ≤ b := by exact_mod_cast le_of_not_gt hh
    linarith
  have hab' : (b : ℝ) + 1 ≤ a := by exact_mod_cast hab
  have hi : ⟪U, u⟫ ≤ b := (real_inner_le_norm _ _).trans
    (by nlinarith [mul_le_mul hU hu (norm_nonneg u) (Nat.cast_nonneg b)])
  by_contra hn
  have hb : (b : ℝ) ≤ 1 / (2 * μ ^ 2) := le_of_not_gt hn
  have hb' : (b : ℝ) * μ ^ 2 ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * μ ^ 2)).mp hb
    nlinarith
  have hq : 1 / 2 ≤ (a : ℝ) - b - T := by nlinarith
  have hprod := mul_nonneg hν href.le
  have hinner := mul_le_mul_of_nonneg_left hi (sq_nonneg μ)
  nlinarith

lemma linear_representation (p : Params) (D : Data p.dimension p.count)
    (η : ℝ) (index : ℕ → Fin (p.count + 1))
    (hoff : ∀ i, 0 ≤ D.offset i ∧ D.offset i ≤ p.ν)
    (hu : ∀ i, ‖D.residual i‖ ≤ 1) (k : ℕ) :
    ∃ (a b : ℕ) (T : ℝ) (U : Features p.dimension), b ≤ k ∧
      0 ≤ T ∧ T ≤ b * p.ν ∧ ‖U‖ ≤ b ∧
      linearIterate p D η index k = (η * ((a : ℝ) - b - T), -(η * p.μ) • U) := by
  induction k with
  | zero => refine ⟨0, 0, 0, 0, by omega, by simp, by simp, by simp, ?_⟩; simp [linearIterate]; rfl
  | succ k ih =>
      obtain ⟨a, b, T, U, hbk, hT, hTb, hU, he⟩ := ih
      rw [linearIterate]
      split
      · cases hi : index k using Fin.cases with
        | zero =>
            refine ⟨a + 1, b, T, U, by omega, hT, hTb, hU, ?_⟩
            rw [he]
            simp only [sample, Fin.cases_zero, Prod.smul_mk, Prod.mk_add_mk,
              smul_eq_mul, smul_zero, add_zero, Nat.cast_add, Nat.cast_one]
            congr 1
            ring
        | succ i =>
            refine ⟨a, b + 1, T + D.offset i, U + D.residual i, by omega,
              by linarith [(hoff i).1], ?_, ?_, ?_⟩
            · push_cast; linarith [(hoff i).2]
            · push_cast
              exact (norm_add_le _ _).trans (by linarith [hu i])
            · rw [he]
              simp only [sample, Fin.cases_succ, Prod.smul_mk, Prod.mk_add_mk,
                smul_eq_mul, smul_smul, Nat.cast_add, Nat.cast_one]
              apply Prod.ext
              · dsimp; ring
              · dsimp; module
      · exact ⟨a, b, T, U, by omega, hT, hTb, hU, he⟩

lemma linear_calls_lower (p : Params) (D : Data p.dimension p.count)
    (η : ℝ) (index : ℕ → Fin (p.count + 1)) (K : ℕ)
    (hη : 0 < η) (hp : spec.valid p) (hg : Geometry p D)
    (hsep : ∀ i, 0 < linearMargin (sample p D i) (linearIterate p D η index K)) :
    1 / (2 * p.μ ^ 2) < (K : ℝ) := by
  obtain ⟨hn, hκ, hκ₁, hμ, _, _, hνs⟩ := hp
  have hκ₁₂ : p.κ ^ 12 ≤ 1 := pow_le_one₀ hκ.le hκ₁
  have hm := mul_le_mul_of_nonneg_right hκ₁₂ (sq_nonneg p.μ)
  have hν : p.ν ≤ p.μ ^ 2 := by nlinarith [sq_nonneg p.μ]
  obtain ⟨hoff, hu, _⟩ := hg
  obtain ⟨a, b, T, U, hbk, hT, hTb, hU, he⟩ := linear_representation p D η index hoff hu K
  let i₀ : Fin p.count := ⟨0, hn⟩
  have href : 0 < (a : ℝ) - b - T := by
    have hh := hsep 0
    rw [he] at hh
    simp only [sample, Fin.cases_zero, linearMargin, one_mul, inner_zero_left, add_zero] at hh
    exact (mul_pos_iff_of_pos_left hη).mp hh
  have hneg : 0 < -(1 + D.offset i₀) * ((a : ℝ) - b - T) + p.μ ^ 2 * ⟪U, D.residual i₀⟫ := by
    have hh := hsep i₀.succ
    rw [he] at hh
    simp only [sample, Fin.cases_succ, linearMargin, real_inner_smul_left,
      real_inner_smul_right] at hh
    rw [real_inner_comm U (D.residual i₀)] at hh
    have heq : -(1 + D.offset i₀) * (η * ((a : ℝ) - b - T)) +
        -(η * p.μ) * (-p.μ * ⟪U, D.residual i₀⟫) =
        η * (-(1 + D.offset i₀) * ((a : ℝ) - b - T) + p.μ ^ 2 * ⟪U, D.residual i₀⟫) := by ring
    rw [heq] at hh
    exact (mul_pos_iff_of_pos_left hη).mp hh
  have hTb' : T ≤ b * p.μ ^ 2 := hTb.trans (mul_le_mul_of_nonneg_left hν (Nat.cast_nonneg b))
  have hb := linear_integer_obstruction p.μ (D.offset i₀) T a b U (D.residual i₀)
    hμ (hoff i₀).1 hT hTb' hU (hu i₀) href hneg
  exact hb.trans_le (by exact_mod_cast hbk)

end LongTails.Proofs.CyclicPerceptronLinearComparison
