import LongTails.Setups.GeneralizedSmoothConvexFull
import LongTails.Proofs.PolynomialDimensionGeneralizedSmoothLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.FullGeneralizedSmoothTransient

open LongTails.Setups.GeneralizedSmoothConvexFull

noncomputable def params (p : Params) : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.Params :=
  { d := p.d, L0 := p.L0, L1 := p.L1, x0 := p.x0, R := p.R,
    ε := max p.ε (p.L0 / p.L1 ^ 2) }

lemma valid (p : Params) (hp : spec.valid p) (hq : 1048576 ≤ p.L1 * p.R) :
    LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.spec.valid (params p) := by
  rcases hp with ⟨h0, h1, hR, hε, hu, hd⟩
  have h1p : 0 < p.L1 := by nlinarith
  have hupper : p.L0 / p.L1 ^ 2 ≤ p.L0 * p.R ^ 2 / 16 := by
    apply (div_le_iff₀ (sq_pos_of_pos h1p)).mpr
    have hsq : 16 ≤ (p.L1 * p.R) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsq h0.le
    nlinarith only [hm]
  refine ⟨h0, h1p, hR, lt_of_lt_of_le hε (le_max_left _ _), hq,
    le_max_right _ _, max_le hu hupper, ?_⟩
  apply le_trans _ hd
  apply Nat.ceil_le_ceil
  have hs := Real.sqrt_nonneg (p.L0 * p.R ^ 2 / p.ε)
  have hq0 : 0 ≤ p.L1 * p.R := mul_nonneg h1 hR.le
  change 17592186044416 * (1 + p.L1 * p.R) ^ 5 ≤
    17592186044416 * (1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 5
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact pow_le_pow_left₀ (by linarith) (by linarith) 5

lemma exists_failure (p : Params) (hp : spec.valid p) (hq : 1048576 ≤ p.L1 * p.R)
    (N : ℕ) (hN : N ≤ ⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p f O ∧
        ¬ spec.successful p f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨f, O, hadm, hbad⟩ := PolynomialDimensionGeneralizedSmoothLowerBound.exists_failure
    (params p) (valid p hp hq) N hN A
  refine ⟨f, O, hadm, ?_⟩
  rintro ⟨xstar, hm, hi, he⟩
  exact hbad ⟨xstar, hm, hi, he.trans (le_max_left _ _)⟩

end LongTails.Proofs.FullGeneralizedSmoothTransient
