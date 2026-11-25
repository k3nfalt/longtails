import LongTails.Setups.SpatialRankingLogistic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

namespace LongTails.Proofs.LogisticPathBounds

private def grid : ℕ := 1073741824

private def squares (a : ℕ) : ℕ → ℕ
  | 0 => a
  | j+1 => squares a j ^ 2 / grid

private lemma squares_le (a j : ℕ) (x : ℝ) (ha : (a : ℝ) / grid ≤ Real.exp x) :
    (squares a j : ℝ) / grid ≤ Real.exp ((2:ℝ)^j * x) := by
  have hg : (0 : ℝ) < grid := by norm_num [grid]
  induction j with
  | zero => simpa [squares] using ha
  | succ j ih =>
    unfold squares
    rw [pow_succ (2:ℝ) j, show (2:ℝ)^j * 2 * x = 2 * (2^j*x) by ring, show Real.exp (2 * (2^j*x)) = Real.exp (2^j*x)^2 from Real.exp_nat_mul _ 2]
    apply le_trans _ (pow_le_pow_left₀ (by positivity) ih 2)
    have h : (((squares a j ^ 2 / grid : ℕ) : ℝ) * grid) ≤ (squares a j : ℝ)^2 := by
      exact_mod_cast Nat.div_mul_le_self (squares a j ^ 2) grid
    rw [div_pow, div_le_div_iff₀ hg (sq_pos_of_pos hg)]
    nlinarith [mul_le_mul_of_nonneg_right h hg.le]

private def lowerExp (q : ℚ) : ℚ :=
  (squares ⌊(grid : ℚ) * max 0 (1 + q / 16384)⌋₊ 14 : ℚ) / grid

private lemma lowerExp_nonneg (q : ℚ) : 0 ≤ lowerExp q := by
  unfold lowerExp
  positivity

private lemma lowerExp_le (q : ℚ) : (lowerExp q : ℝ) ≤ Real.exp q := by
  let a := ⌊(grid : ℚ) * max 0 (1 + q / 16384)⌋₊
  have hg : (0 : ℝ) < grid := by norm_num [grid]
  have ha : (a : ℝ) ≤ (grid : ℝ) * max 0 (1 + (q:ℝ)/16384) := by
    exact_mod_cast Nat.floor_le (show 0 ≤ (grid:ℚ) * max 0 (1+q/16384) by positivity)
  have hb := (div_le_iff₀ hg).2 (show (a:ℝ) ≤ max 0 (1 + (q:ℝ)/16384) * grid by linarith)
  have hc := squares_le a 14 ((q:ℝ)/16384) (hb.trans (max_le (Real.exp_pos _).le (by
    linarith only [Real.add_one_le_exp ((q:ℝ)/16384)])))
  norm_num at hc
  rw [show 16384 * ((q:ℝ) / 16384) = q by ring] at hc
  simpa [lowerExp, a] using hc

private def upperSigmoid (q : ℚ) : ℚ := (1 + lowerExp (-q))⁻¹

private lemma sigmoid_le_upper (q : ℚ) : Real.sigmoid q ≤ (upperSigmoid q : ℝ) := by
  simp only [upperSigmoid, Real.sigmoid_def, Rat.cast_inv, Rat.cast_add, Rat.cast_one]
  have hn : 0 ≤ ((lowerExp (-q) : ℚ) : ℝ) := by exact_mod_cast lowerExp_nonneg (-q)
  apply inv_anti₀ (by linarith : 0 < 1 + ((lowerExp (-q):ℚ):ℝ))
  simpa using add_le_add_right (lowerExp_le (-q)) 1

open Inclusion IntervalDyadicReal

private def sigmoidInterval (I : Interval Dyadic) : Interval Dyadic :=
  let lo := I.lb.elim 0 fun d => (1 - upperSigmoid (-d.toRat)).toDyadic 30
  let hi := I.ub.elim 1 fun d => -(-upperSigmoid d.toRat).toDyadic 30
  Interval.Icc lo hi

private lemma round_down (q : ℚ) : (q.toDyadic 30).toReal ≤ (q:ℝ) := by
  unfold Dyadic.toReal
  exact_mod_cast (show (q.toDyadic 30).toRat ≤ q from Rat.toRat_toDyadic_le)

@[local inclusion_op interval_dyadic_real]
private lemma sigmoid_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) :
    Real.sigmoid x ∈ sigmoidInterval I := by
  rcases I with ⟨lo,hi⟩
  apply Interval.mem_map_Icc
  · cases lo with
    | bot => change (0 : Dyadic).toReal ≤ Real.sigmoid x
             simpa [Dyadic.toReal] using Real.sigmoid_nonneg x
    | coe d =>
      have h := Interval.map_lb_le Dyadic.toReal hx
      have he := sigmoid_le_upper (-d.toRat)
      simp only [Rat.cast_neg, Real.sigmoid_neg] at he
      change 1 - Real.sigmoid d.toReal ≤ (upperSigmoid (-d.toRat) : ℝ) at he
      exact (round_down _).trans (by
        push_cast
        linarith only [he, Real.sigmoid_le h])
  · cases hi with
    | top => change Real.sigmoid x ≤ (1 : Dyadic).toReal
             rw [show (1 : Dyadic).toReal = 1 by
               unfold Dyadic.toReal
               exact_mod_cast (show (1 : Dyadic).toRat = 1 by decide)]
             exact Real.sigmoid_le_one x
    | coe d =>
      have h := Interval.le_map_ub Dyadic.toReal hx
      have he := round_down (-upperSigmoid d.toRat)
      change Real.sigmoid x ≤ (-(-upperSigmoid d.toRat).toDyadic 30).toReal
      rw [show ∀ d : Dyadic, (-d).toReal = -d.toReal from fun d =>
        map_neg Dyadic.toRealAddMonoidHom d]
      apply (Real.sigmoid_le h).trans ((sigmoid_le_upper d.toRat).trans ?_)
      push_cast at he
      linarith

open LongTails.Setups.SpatialRankingLogistic

noncomputable def extremeWeight (p : Population) : ℝ :=
  p.scale * Real.sigmoid (-(p.scale * p.scale))

noncomputable def anchorCoeff (p : Population) : ℝ := p.scale + 2 * extremeWeight p

noncomputable def nearCoeff (p : Population) : ℝ := p.scale - 2 * extremeWeight p

noncomputable def secondTaps (u : ℝ) : ℝ × ℝ :=
  let direct p := 4 * p.scale * extremeWeight p
  let lag p := 4 * p.scale * p.anchorLag * extremeWeight p -
    p.scale * p.slope * u * nearCoeff p
  (1 + direct first + direct second, lag first + lag second)

structure Weights where
  left : ℝ
  near : ℝ
  bulk : ℝ
  right : ℝ

noncomputable def weights (p : Population) (u v a b : ℝ) : Weights :=
  let A := anchorCoeff p
  let B := nearCoeff p
  let T := a + b * p.itemLag
  let U := a + b * p.anchorLag
  let s := b * A
  let step := p.slope * u * v
  let posterior m := p.scale * Real.sigmoid (-(p.scale * m))
  ⟨posterior (U*A - b*B*p.slope*u - T*B - p.left*u*s),
   posterior (T*B - step*s), posterior (-step*s),
   posterior (U*A - T*B + p.right*u*s)⟩

def contact (p : Population) (u v : ℝ) (w : Weights) : ℝ :=
  p.left*u*(w.near-w.left) + p.right*u*(w.right-w.near) +
    (-p.slope*u+2*p.slope*u*v)*(w.bulk-w.near)

noncomputable def tapCorrection (p : Population) (u v a b : ℝ) : ℝ × ℝ :=
  let w := weights p u v a b
  let ends := anchorCoeff p * (w.left+w.right)
  let near := nearCoeff p * (2*w.near-w.left-w.right)
  (2*(ends+near), 2*(p.anchorLag*ends+p.itemLag*near -
    w.left*nearCoeff p*p.slope*u + anchorCoeff p*contact p u v w))

noncomputable def thirdTaps (u v : ℝ) : ℝ × ℝ :=
  let c := secondTaps u
  c + tapCorrection first u v c.1 c.2 + tapCorrection second u v c.1 c.2

noncomputable def bulkSlope (p : Population) (u v : ℝ) : ℝ :=
  let c := secondTaps u
  let d := thirdTaps u v
  let w := weights p u v c.1 c.2
  (-p.scale) * p.slope *
    (2*d.1*c.2*w.left + d.2*(anchorCoeff p + 2*c.1*w.right))

inductive BoundaryEdge where
  | leftAnchor | leftNear | interior | rightNear | rightAnchor

noncomputable def boundaryMargin (p : Population) (u v : ℝ) (edge : BoundaryEdge) : ℝ :=
  let c := secondTaps u
  let d := thirdTaps u v
  let w := weights p u v c.1 c.2
  let A := anchorCoeff p
  let B := nearCoeff p
  let E := d.1 + d.2*p.itemLag
  let E₀ := d.1 + d.2*p.anchorLag
  let K := 2*(E*c.1 + (p.itemLag*d.1+d.2)*c.2)
  let K₀ := 2*(E₀*c.1 + (p.anchorLag*d.1+d.2)*c.2)
  let C := 2*d.1*c.2*w.left + d.2*(A + 2*c.1*w.right)
  let J := contact p u v w
  let step := p.slope*u*v*C
  p.scale * match edge with
  | .leftAnchor => E₀*A + K₀*w.left + d.2*(-B*p.slope*u + 2*c.1*J) -
      E*B - K*(w.near-w.left) - p.left*u*C
  | .leftNear => E*B + K*(2*w.near-w.left-w.bulk) - step
  | .interior => K*(w.bulk-w.near) - step
  | .rightNear => E*B + K*(2*w.near-w.right-w.bulk) - step
  | .rightAnchor => -E*B + K*(w.right-w.near) + p.right*u*C +
      E₀*A + K₀*w.right + 2*d.1*c.2*J

private lemma split_length {u : ℝ} (hu : u ∈ Set.Icc 0 0.375) :
    u ∈ Set.Icc 0 0.09375 ∨ u ∈ Set.Icc 0.09375 0.1875 ∨
    u ∈ Set.Icc 0.1875 0.28125 ∨ u ∈ Set.Icc 0.28125 0.375 := by
  rcases hu with ⟨hl, hr⟩
  by_cases h₁ : u ≤ 0.09375
  · exact Or.inl ⟨hl, h₁⟩
  by_cases h₂ : u ≤ 0.1875
  · exact Or.inr (Or.inl ⟨(lt_of_not_ge h₁).le, h₂⟩)
  by_cases h₃ : u ≤ 0.28125
  · exact Or.inr (Or.inr (Or.inl ⟨(lt_of_not_ge h₂).le, h₃⟩))
  exact Or.inr (Or.inr (Or.inr ⟨(lt_of_not_ge h₃).le, hr⟩))

local macro "verify_path_bound " hu:ident : tactic => `(tactic|
  (dsimp [bulkSlope, boundaryMargin, thirdTaps, tapCorrection, weights, secondTaps, contact,
    anchorCoeff, nearCoeff, extremeWeight, first, second]
   rcases split_length $hu with H | H | H | H <;> clear $hu))

set_option maxHeartbeats 8000000 in
lemma bulk_margin_bounds {u v : ℝ} (hu : u ∈ Set.Icc 0 0.375) (hv : v ∈ Set.Icc 0 0.17) :
    0.001 < bulkSlope first u v ∧ 0.001 < bulkSlope second u v := by
  constructor <;> verify_path_bound hu <;> dyadic_interval [prec := 32]

set_option maxHeartbeats 16000000 in
lemma boundary_margin_bounds {u v : ℝ} (hu : u ∈ Set.Icc 0 0.375) (hv : v ∈ Set.Icc 0 0.17)
    (e : BoundaryEdge) : 0.05 < boundaryMargin first u v e ∧ 0.05 < boundaryMargin second u v e := by
  cases e <;> constructor <;> verify_path_bound hu <;> dyadic_interval [prec := 32]

end LongTails.Proofs.LogisticPathBounds
