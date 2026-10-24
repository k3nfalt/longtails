import LongTails.Proofs.CyclicPerceptronBlocks

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CyclicPerceptronBounds

open LongTails.Setups.CyclicFullWidthPerceptron
open CyclicPerceptronBlocks

structure Envelope {d : ℕ} (H : ℝ) (c : Coordinates d) : Prop where
  a_bound : |c.a| ≤ 2
  matrix_bound : ‖c.F‖ ≤ 2
  S_bound : ‖c.S‖ ≤ 4 * H
  X_bound : ‖c.X‖ ≤ 4 * H
  R_bound : ‖c.R‖ ≤ 4 * H
  B_bound : |c.B| ≤ 16 * H ^ 2

lemma matrix_increment {d : ℕ} (b : Bool) (α μ β H : ℝ) (c : Coordinates d)
    (u : Features d) (hα : 0 ≤ α) (hα₁ : α ≤ 1) (hH : 0 ≤ H)
    (hu : ‖u‖ ≤ 1) (hc : Envelope H c) :
    ‖(pairedCoordinates b α μ β c u).F - c.F‖ ≤ 8 * α * μ ^ 2 * H := by
  have hinner : ‖c.S + (if b then 0 else α • c.X)‖ ≤ 8 * H := by
    have hx : ‖(if b then (0 : Features d) else α • c.X)‖ ≤ 4 * H := by
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hα]
        have hm := mul_le_mul_of_nonneg_left hc.X_bound hα
        nlinarith
      · simpa using (show 0 ≤ 4 * H by positivity)
    exact (norm_add_le _ _).trans (by linarith [hc.S_bound])
  have hrank : ‖InnerProductSpace.rankOne ℝ
      (c.S + (if b then 0 else α • c.X)) u‖ ≤ 8 * H := by
    rw [InnerProductSpace.norm_rankOne]
    have hm := mul_le_mul_of_nonneg_right hinner (norm_nonneg u)
    nlinarith
  simp only [pairedCoordinates, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hα (sq_nonneg μ))]
  have hm := mul_le_mul_of_nonneg_left hrank (mul_nonneg hα (sq_nonneg μ))
  nlinarith

lemma bias_envelope {d : ℕ} (H : ℝ) (c : Coordinates d) (hH : 0 ≤ H)
    (hc : Envelope H c) : |bias c| ≤ 48 * H ^ 2 := by
  have hprod : |c.a * c.B| ≤ 32 * H ^ 2 := by
    rw [abs_mul]
    have hm := mul_le_mul hc.a_bound hc.B_bound (abs_nonneg c.B) (by norm_num)
    nlinarith
  have hi : |⟪c.X, c.S⟫| ≤ 16 * H ^ 2 := by
    have hm := mul_le_mul hc.X_bound hc.S_bound (norm_nonneg c.S) (by positivity)
    exact (abs_real_inner_le_norm _ _).trans (by nlinarith)
  exact (abs_add_le _ _).trans (by linarith)

lemma S_increment {d : ℕ} (b : Bool) (α μ β H : ℝ) (c : Coordinates d)
    (u : Features d) (hα : 0 ≤ α) (hα₁ : α ≤ 1) (hβ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hμ : μ ^ 2 ≤ 1) (hH : 1 ≤ H) (hu : ‖u‖ ≤ 1) (hc : Envelope H c)
    (hF : ‖c.F - ContinuousLinearMap.id ℝ (Features d)‖ ≤ 8 * α * μ ^ 2 * H ^ 2) :
    ‖(pairedCoordinates b α μ β c u).S - (c.S + u)‖ ≤ 20 * α * H ^ 2 := by
  let ν := β * α * μ ^ 2
  have hν : 0 ≤ ν := by dsimp [ν]; positivity
  have hν₁ : ν ≤ α := by
    calc
      β * α * μ ^ 2 ≤ 1 * α * 1 := by gcongr
      _ = α := by ring
  have hcoef : α * (1 + ν) ≤ 2 * α := by nlinarith
  have hcoef' : α * ν ≤ α := by nlinarith
  have he : (pairedCoordinates b α μ β c u).S - (c.S + u) =
      -(α * (1 + ν)) • c.S - (α * ν) • c.X +
        (c.F - ContinuousLinearMap.id ℝ (Features d)) u := by
    simp only [pairedCoordinates, ν, sub_apply, ContinuousLinearMap.id_apply]
    module
  have hs : ‖-(α * (1 + ν)) • c.S‖ ≤ 8 * α * H := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
    have hm := mul_le_mul hcoef hc.S_bound (norm_nonneg c.S) (by positivity)
    nlinarith
  have hx : ‖(α * ν) • c.X‖ ≤ 4 * α * H := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hm := mul_le_mul hcoef' hc.X_bound (norm_nonneg c.X) hα
    nlinarith
  have hf : ‖(c.F - ContinuousLinearMap.id ℝ (Features d)) u‖ ≤ 8 * α * H ^ 2 := by
    have hm := (c.F - ContinuousLinearMap.id ℝ (Features d)).le_opNorm u
    have hb := mul_le_mul hF hu (norm_nonneg u) (by positivity)
    have hp := mul_le_mul_of_nonneg_left hμ (show 0 ≤ 8 * α * H ^ 2 by positivity)
    nlinarith
  rw [he]
  have ht := norm_add_le (-(α * (1 + ν)) • c.S - (α * ν) • c.X)
    ((c.F - ContinuousLinearMap.id ℝ (Features d)) u)
  have ht' := norm_sub_le (-(α * (1 + ν)) • c.S) ((α * ν) • c.X)
  have hp := mul_nonneg hα (show 0 ≤ H ^ 2 - H by nlinarith)
  linarith

lemma X_increment {d : ℕ} (b : Bool) (α μ β H : ℝ) (c : Coordinates d)
    (u : Features d) (hα : 0 ≤ α) (hα₁ : α ≤ 1) (hβ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hμ : μ ^ 2 ≤ 1) (hH : 1 ≤ H) (hu : ‖u‖ ≤ 1) (hc : Envelope H c)
    (hF : ‖c.F - ContinuousLinearMap.id ℝ (Features d)‖ ≤ 8 * α * μ ^ 2 * H ^ 2) :
    ‖(pairedCoordinates b α μ β c u).X - (c.X + (if b then u else 0))‖ ≤ 20 * α * H ^ 2 := by
  let ν := β * α * μ ^ 2
  have hν : 0 ≤ ν := by dsimp [ν]; positivity
  have hν₁ : ν ≤ α := by
    calc
      β * α * μ ^ 2 ≤ 1 * α * 1 := by gcongr
      _ = α := by ring
  have hcoef : α * (1 + ν) ≤ 2 * α := by nlinarith
  have hcoef' : ν ≤ α := hν₁
  have he : (pairedCoordinates b α μ β c u).X - (c.X + (if b then u else 0)) =
      -(α * (1 + ν)) • c.X - ν • c.S +
        (if b then (c.F - ContinuousLinearMap.id ℝ (Features d)) u else 0) := by
    cases b <;> simp only [pairedCoordinates, ν, Bool.false_eq_true, ↓reduceIte,
      sub_apply, ContinuousLinearMap.id_apply] <;> module
  have hs : ‖-(α * (1 + ν)) • c.X‖ ≤ 8 * α * H := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
    have hm := mul_le_mul hcoef hc.X_bound (norm_nonneg c.X) (by positivity)
    nlinarith
  have hx : ‖ν • c.S‖ ≤ 4 * α * H := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hm := mul_le_mul hcoef' hc.S_bound (norm_nonneg c.S) hα
    nlinarith
  have hfBase : ‖(c.F - ContinuousLinearMap.id ℝ (Features d)) u‖ ≤ 8 * α * H ^ 2 := by
    have hm := (c.F - ContinuousLinearMap.id ℝ (Features d)).le_opNorm u
    have hb := mul_le_mul hF hu (norm_nonneg u) (by positivity)
    have hp := mul_le_mul_of_nonneg_left hμ (show 0 ≤ 8 * α * H ^ 2 by positivity)
    nlinarith
  have hf : ‖(if b then (c.F - ContinuousLinearMap.id ℝ (Features d)) u else 0)‖ ≤
      8 * α * H ^ 2 := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, norm_zero]; positivity
    · simpa using hfBase
  rw [he]
  have ht := norm_add_le (-(α * (1 + ν)) • c.X - ν • c.S)
    (if b then (c.F - ContinuousLinearMap.id ℝ (Features d)) u else 0)
  have ht' := norm_sub_le (-(α * (1 + ν)) • c.X) (ν • c.S)
  have hp := mul_nonneg hα (show 0 ≤ H ^ 2 - H by nlinarith)
  linarith

lemma R_increment {d : ℕ} (b : Bool) (α μ β H : ℝ) (c : Coordinates d)
    (u : Features d) (hα : 0 ≤ α) (hμ : μ ^ 2 ≤ 1) (hH : 1 ≤ H)
    (hu : ‖u‖ ≤ 1) (hc : Envelope H c) (ha : |c.a - 1| ≤ 5 * α * H) :
    ‖(pairedCoordinates b α μ β c u).R - (c.R + (if b then 0 else u))‖ ≤
      21 * α * H ^ 2 := by
  have he : (pairedCoordinates b α μ β c u).R - (c.R + (if b then 0 else u)) =
      (α * μ ^ 2 * c.B) • u + (if b then 0 else (c.a - 1) • u) := by
    cases b <;> simp only [pairedCoordinates, Bool.false_eq_true, ↓reduceIte] <;> module
  have hb : ‖(α * μ ^ 2 * c.B) • u‖ ≤ 16 * α * H ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hα,
      abs_of_nonneg (sq_nonneg μ)]
    calc
      α * μ ^ 2 * |c.B| * ‖u‖ ≤ α * 1 * (16 * H ^ 2) * 1 := by
        gcongr
        exact hc.B_bound
      _ = 16 * α * H ^ 2 := by ring
  have ha' : ‖(if b then (0 : Features d) else (c.a - 1) • u)‖ ≤ 5 * α * H := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, norm_smul, Real.norm_eq_abs]
      have hm := mul_le_mul ha hu (norm_nonneg u) (by positivity)
      simpa using hm
    · simp only [↓reduceIte, norm_zero]
      positivity
  rw [he]
  have ht := norm_add_le ((α * μ ^ 2 * c.B) • u)
    (if b then (0 : Features d) else (c.a - 1) • u)
  have hp := mul_nonneg hα (show 0 ≤ H ^ 2 - H by nlinarith)
  linarith

lemma B_increment {d : ℕ} (b : Bool) (α μ β H : ℝ) (c : Coordinates d)
    (u R₀ : Features d) (hα : 0 ≤ α) (hα₁ : α ≤ 1) (hβ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hμ : μ ^ 2 ≤ 1) (hH : 1 ≤ H) (hu : ‖u‖ ≤ 1) (hc : Envelope H c)
    (ha : |c.a - 1| ≤ 5 * α * H) (hR : ‖c.R - R₀‖ ≤ 21 * α * H ^ 3) :
    |(pairedCoordinates b α μ β c u).B - (c.B + ⟪R₀, u⟫ - β)| ≤
      58 * α * H ^ 3 := by
  let ν := β * α * μ ^ 2
  have hν : 0 ≤ ν := by dsimp [ν]; positivity
  have hν₁ : ν ≤ 1 := by
    calc
      β * α * μ ^ 2 ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  have he : (pairedCoordinates b α μ β c u).B - (c.B + ⟪R₀, u⟫ - β) =
      -(α * (1 + ν) * c.B) - β * (c.a - 1) + ⟪c.R - R₀, u⟫ := by
    simp only [pairedCoordinates, ν, inner_sub_left]
    ring
  have hb : |α * (1 + ν) * c.B| ≤ 32 * α * H ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg (by positivity)]
    calc
      α * (1 + ν) * |c.B| ≤ α * 2 * (16 * H ^ 2) := by gcongr; linarith; exact hc.B_bound
      _ = 32 * α * H ^ 2 := by ring
  have ha' : |β * (c.a - 1)| ≤ 5 * α * H := by
    rw [abs_mul, abs_of_nonneg hβ]
    have hm := mul_le_mul hβ₁ ha (abs_nonneg _) (by norm_num)
    simpa using hm
  have hr : |⟪c.R - R₀, u⟫| ≤ 21 * α * H ^ 3 := by
    have hm := mul_le_mul hR hu (norm_nonneg u) (by positivity)
    exact (abs_real_inner_le_norm _ _).trans (by simpa using hm)
  rw [he]
  have ht := abs_add_le (-(α * (1 + ν) * c.B) - β * (c.a - 1)) ⟪c.R - R₀, u⟫
  have ht' := abs_sub (-(α * (1 + ν) * c.B)) (β * (c.a - 1))
  rw [abs_neg] at ht'
  have hp := mul_nonneg hα (show 0 ≤ H ^ 3 - H ^ 2 by nlinarith [sq_nonneg H])
  have hp' := mul_nonneg hα (show 0 ≤ H ^ 3 - H by nlinarith [sq_nonneg H])
  linarith

lemma a_increment {d : ℕ} (b : Bool) (α μ β H : ℝ) (c : Coordinates d)
    (u : Features d) (hα : 0 ≤ α) (hα₁ : α ≤ 1) (hβ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hμ : μ ^ 2 ≤ 1) (hH : 1 ≤ H) (hu : ‖u‖ ≤ 1) (hc : Envelope H c)
    (hsmall : α * H ^ 2 ≤ 1 / 1024) :
    |(pairedCoordinates b α μ β c u).a - c.a| ≤ 5 * α := by
  let ν := β * α * μ ^ 2
  have hν : 0 ≤ ν := by dsimp [ν]; positivity
  have hν₁ : ν ≤ α := by
    calc
      β * α * μ ^ 2 ≤ 1 * α * 1 := by gcongr
      _ = α := by ring
  have he : (pairedCoordinates b α μ β c u).a - c.a =
      -(α * (1 + ν) * c.a) - α ^ 2 * ν * μ ^ 2 * c.B +
        (if b then α ^ 2 * μ ^ 2 * ⟪c.R, u⟫ else 0) := by
    simp only [pairedCoordinates, ν]
    ring
  have ha : |α * (1 + ν) * c.a| ≤ 4 * α := by
    rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg (by positivity)]
    calc
      α * (1 + ν) * |c.a| ≤ α * 2 * 2 := by gcongr; linarith; exact hc.a_bound
      _ = 4 * α := by ring
  have hb : |α ^ 2 * ν * μ ^ 2 * c.B| ≤ 16 * α ^ 3 * H ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc
      α ^ 2 * ν * μ ^ 2 * |c.B| ≤ α ^ 2 * α * 1 * (16 * H ^ 2) := by
        gcongr
        exact hc.B_bound
      _ = 16 * α ^ 3 * H ^ 2 := by ring
  have hr : |⟪c.R, u⟫| ≤ 4 * H := by
    have hm := mul_le_mul hc.R_bound hu (norm_nonneg u) (by positivity)
    exact (abs_real_inner_le_norm _ _).trans (by simpa using hm)
  have hr' : |(if b then α ^ 2 * μ ^ 2 * ⟪c.R, u⟫ else 0)| ≤ 4 * α ^ 2 * H := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, abs_zero]; positivity
    · simp only [↓reduceIte, abs_mul, abs_of_nonneg (sq_nonneg α),
        abs_of_nonneg (sq_nonneg μ)]
      calc
        α ^ 2 * μ ^ 2 * |⟪c.R, u⟫| ≤ α ^ 2 * 1 * (4 * H) := by gcongr
        _ = 4 * α ^ 2 * H := by ring
  have hαH : α * H ≤ 1 / 1024 := by
    have hm := mul_nonneg hα (show 0 ≤ H ^ 2 - H by nlinarith)
    linarith
  have hsmall' := mul_le_mul_of_nonneg_left hsmall (sq_nonneg α)
  have hαsq : α ^ 2 ≤ α := by nlinarith
  have hsmall'' := mul_le_mul_of_nonneg_left hαH hα
  rw [he]
  have ht := abs_add_le (-(α * (1 + ν) * c.a) - α ^ 2 * ν * μ ^ 2 * c.B)
    (if b then α ^ 2 * μ ^ 2 * ⟪c.R, u⟫ else 0)
  have ht' := abs_sub (-(α * (1 + ν) * c.a)) (α ^ 2 * ν * μ ^ 2 * c.B)
  rw [abs_neg] at ht'
  nlinarith

end LongTails.Proofs.CyclicPerceptronBounds
