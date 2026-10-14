import LongTails.Setups.SmoothPL
import LongTails.Proofs.GdConvex
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OracleTemplate.PLGradient

open LongTails.Setups.SmoothPL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gd_rate (f : E → ℝ) (L μ Δ : ℝ) (x0 xstar : E)
    (hμ : 0 < μ) (hμL : μ ≤ L) (hgap : f x0 - f xstar ≤ Δ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hpl : ∀ x, 2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2) (k : ℕ) :
    f ((fun x => x - (1 / L) • gradient f x)^[k] x0) - f xstar ≤
      (1 - μ / L) ^ k * Δ := by
  have hL : 0 < L := hμ.trans_le hμL
  have hq : 0 ≤ 1 - μ / L := sub_nonneg.mpr ((div_le_one hL).mpr hμL)
  induction k with
  | zero => simpa using hgap
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hd := Gradient.descent hL hg hlip
      ((fun x => x - (1 / L) • gradient f x)^[k] x0)
    have hp := (div_le_div_iff_of_pos_right (show 0 < 2 * L by positivity)).mpr
      (hpl ((fun x => x - (1 / L) • gradient f x)^[k] x0))
    have he (a : ℝ) : 2 * μ * a / (2 * L) = (μ / L) * a := by ring
    rw [he] at hp
    have hi := mul_le_mul_of_nonneg_left ih hq
    rw [pow_succ]
    nlinarith

lemma geometric_budget (L μ Δ ε : ℝ) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (K : ℕ := ⌈(L / μ) * Real.log (1 + Δ / ε)⌉₊)
    (hK : ⌈(L / μ) * Real.log (1 + Δ / ε)⌉₊ ≤ K := by exact le_rfl) :
    (1 - μ / L) ^ K * Δ ≤ ε := by
  have hL : 0 < L := hμ.trans_le hμL
  have hq : 0 ≤ 1 - μ / L := sub_nonneg.mpr ((div_le_one hL).mpr hμL)
  have ht : 0 < 1 + Δ / ε := by positivity
  have hceil : (L / μ) * Real.log (1 + Δ / ε) ≤ (K : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hK)
  have hmul := mul_le_mul_of_nonneg_left hceil (div_pos hμ hL).le
  have hid : μ / L * (L / μ * Real.log (1 + Δ / ε)) =
      Real.log (1 + Δ / ε) := by field_simp
  rw [hid] at hmul
  have hbase : 1 - μ / L ≤ Real.exp (-(μ / L)) := by
    linarith [Real.add_one_le_exp (-(μ / L))]
  have hpow := pow_le_pow_left₀ hq hbase K
  rw [← Real.exp_nat_mul] at hpow
  have hexp : Real.exp ((K : ℝ) * -(μ / L)) ≤
      Real.exp (-Real.log (1 + Δ / ε)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbound := mul_le_mul_of_nonneg_right (hpow.trans hexp) hΔ
  rw [Real.exp_neg, Real.exp_log ht] at hbound
  have hlast : (1 + Δ / ε)⁻¹ * Δ ≤ ε := by
    rw [← div_eq_inv_mul]
    apply (div_le_iff₀ ht).mpr
    have : ε * (1 + Δ / ε) = ε + Δ := by field_simp
    rw [this]
    linarith
  exact hbound.trans hlast

lemma gd_accuracy (f : E → ℝ) (L μ Δ ε : ℝ) (x0 xstar : E)
    (hμ : 0 < μ) (hμL : μ ≤ L) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hgap : f x0 - f xstar ≤ Δ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hpl : ∀ x, 2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2)
    (K : ℕ) (hK : ⌈(L / μ) * Real.log (1 + Δ / ε)⌉₊ ≤ K) :
    let output := execute { answer := fun _ (_, x) _ => gradient f x } (Gradient.gd (L, x0)) (fun _ => K)
    f output - f xstar ≤ ε := by
  dsimp only
  rw [Gradient.execute_gd]
  exact (gd_rate f L μ Δ x0 xstar hμ hμL hgap hg hlip hpl _).trans
    (geometric_budget L μ Δ ε hμ hμL hΔ hε K hK)

end OracleTemplate.PLGradient
