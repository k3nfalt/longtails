import LongTails.Proofs.CyclicPerceptronBounds
import LongTails.Proofs.CyclicPerceptronComparisonDynamics

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CyclicPerceptronBootstrap

open LongTails.Setups.CyclicFullWidthPerceptron
open CyclicPerceptronBlocks CyclicPerceptronBounds CyclicPerceptronComparisonDynamics

structure Errors {d : ℕ} (α μ H j : ℝ) (c : Coordinates d) (s : Comparison d) : Prop where
  a_error : |c.a - 1| ≤ 5 * α * j
  F_error : ‖c.F - ContinuousLinearMap.id ℝ (Features d)‖ ≤ 8 * α * μ ^ 2 * H * j
  S_error : ‖c.S - s.U‖ ≤ 20 * α * H ^ 2 * j
  X_error : ‖c.X - s.V‖ ≤ 20 * α * H ^ 2 * j
  R_error : ‖c.R - s.R‖ ≤ 21 * α * H ^ 2 * j
  B_error : |c.B - s.B| ≤ 58 * α * H ^ 3 * j

lemma norm_le_error_add {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
  simpa only [sub_add_cancel] using norm_add_le (x - y) y

lemma abs_le_error_add (x y : ℝ) : |x| ≤ |x - y| + |y| := by
  simpa only [sub_add_cancel] using abs_add_le (x - y) y

lemma envelope_of_errors {d : ℕ} (α μ H j : ℝ) (c : Coordinates d) (s : Comparison d)
    (hα : 0 ≤ α) (hμ : μ ^ 2 ≤ 1) (hH : 1 ≤ H) (hj : 0 ≤ j) (hjH : j ≤ H)
    (hsmall : α * H ^ 2 ≤ 1 / 1024) (he : Errors α μ H j c s)
    (hs : ComparisonBound j s) : Envelope H c := by
  have hH0 : 0 ≤ H := by linarith
  have hjH₂ : j ≤ H ^ 2 := by nlinarith
  have hαj : α * j ≤ 1 / 1024 := by
    have hm := mul_le_mul_of_nonneg_left hjH₂ hα
    linarith
  have hαHj : α * H * j ≤ 1 / 1024 := by
    have hm := mul_le_mul_of_nonneg_left hjH (mul_nonneg hα hH0)
    nlinarith
  have hαH₂j : α * H ^ 2 * j ≤ H / 1024 := by
    have hm := mul_le_mul hsmall hjH hj (by norm_num)
    nlinarith
  have hαH₃j : α * H ^ 3 * j ≤ H ^ 2 / 1024 := by
    have hm := mul_le_mul_of_nonneg_left hαH₂j hH0
    nlinarith
  constructor
  · have ht := abs_le_error_add c.a 1
    norm_num at ht
    nlinarith [he.a_error]
  · have ht := norm_le_error_add c.F (ContinuousLinearMap.id ℝ (Features d))
    have hid : ‖ContinuousLinearMap.id ℝ (Features d)‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    have hm := mul_le_mul_of_nonneg_left hμ (show 0 ≤ α * H * j by positivity)
    nlinarith [he.F_error]
  · have ht := norm_le_error_add c.S s.U
    nlinarith [he.S_error, hs.U_bound]
  · have ht := norm_le_error_add c.X s.V
    nlinarith [he.X_error, hs.V_bound]
  · have ht := norm_le_error_add c.R s.R
    nlinarith [he.R_error, hs.R_bound]
  · have ht := abs_le_error_add c.B s.B
    have hj₂ : j ^ 2 ≤ H ^ 2 := by nlinarith
    nlinarith [he.B_error, hs.B_bound]

lemma norm_error_transport {E : Type*} [SeminormedAddCommGroup E] (x' x y v : E)
    (A B : ℝ) (ha : ‖x' - (x + v)‖ ≤ A) (hb : ‖x - y‖ ≤ B) :
    ‖x' - (y + v)‖ ≤ A + B := by
  have he : x' - (y + v) = (x' - (x + v)) + (x - y) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add ha hb)

lemma abs_error_transport (x' x y v A B : ℝ)
    (ha : |x' - (x + v)| ≤ A) (hb : |x - y| ≤ B) :
    |x' - (y + v)| ≤ A + B := by
  exact norm_error_transport x' x y v A B ha hb

lemma errors_step {d : ℕ} (b : Bool) (α μ β H j : ℝ) (c : Coordinates d)
    (s : Comparison d) (u : Features d) (hα : 0 ≤ α) (hα₁ : α ≤ 1)
    (hβ : 0 ≤ β) (hβ₁ : β ≤ 1) (hμ : μ ^ 2 ≤ 1) (hH : 1 ≤ H)
    (hjH : j ≤ H) (hu : ‖u‖ ≤ 1)
    (hsmall : α * H ^ 2 ≤ 1 / 1024) (hc : Envelope H c)
    (he : Errors α μ H j c s) :
    Errors α μ H (j + 1) (pairedCoordinates b α μ β c u) (comparisonStep b β s u) := by
  have hF : ‖c.F - ContinuousLinearMap.id ℝ (Features d)‖ ≤ 8 * α * μ ^ 2 * H ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hjH (show 0 ≤ 8 * α * μ ^ 2 * H by positivity)
    nlinarith [he.F_error]
  have ha : |c.a - 1| ≤ 5 * α * H :=
    he.a_error.trans (mul_le_mul_of_nonneg_left hjH (by positivity))
  have hr : ‖c.R - s.R‖ ≤ 21 * α * H ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left hjH (show 0 ≤ 21 * α * H ^ 2 by positivity)
    nlinarith [he.R_error]
  constructor
  · have hi := a_increment b α μ β H c u hα hα₁ hβ hβ₁ hμ hH hu hc hsmall
    have ht := abs_error_transport (pairedCoordinates b α μ β c u).a c.a 1 0
      (5 * α) (5 * α * j) (by simpa using hi) he.a_error
    simp only [add_zero] at ht
    nlinarith
  · have hi := matrix_increment b α μ β H c u hα hα₁ (by linarith) hu hc
    have ht := norm_error_transport (pairedCoordinates b α μ β c u).F c.F
      (ContinuousLinearMap.id ℝ (Features d)) 0
      (8 * α * μ ^ 2 * H) (8 * α * μ ^ 2 * H * j) (by simpa using hi) he.F_error
    simp only [add_zero] at ht
    nlinarith
  · have hi := S_increment b α μ β H c u hα hα₁ hβ hβ₁ hμ hH hu hc hF
    have ht := norm_error_transport (pairedCoordinates b α μ β c u).S c.S s.U u
      (20 * α * H ^ 2) (20 * α * H ^ 2 * j) hi he.S_error
    change ‖(pairedCoordinates b α μ β c u).S - (s.U + u)‖ ≤ _
    nlinarith
  · have hi := X_increment b α μ β H c u hα hα₁ hβ hβ₁ hμ hH hu hc hF
    have ht := norm_error_transport (pairedCoordinates b α μ β c u).X c.X s.V
      (if b then u else 0) (20 * α * H ^ 2) (20 * α * H ^ 2 * j) hi he.X_error
    change ‖(pairedCoordinates b α μ β c u).X - (s.V + (if b then u else 0))‖ ≤ _
    nlinarith
  · have hi := R_increment b α μ β H c u hα hμ hH hu hc ha
    have ht := norm_error_transport (pairedCoordinates b α μ β c u).R c.R s.R
      (if b then 0 else u) (21 * α * H ^ 2) (21 * α * H ^ 2 * j) hi he.R_error
    change ‖(pairedCoordinates b α μ β c u).R - (s.R + (if b then 0 else u))‖ ≤ _
    nlinarith
  · have hi := B_increment b α μ β H c u s.R hα hα₁ hβ hβ₁ hμ hH hu hc ha hr
    have ht := abs_error_transport (pairedCoordinates b α μ β c u).B c.B s.B
      (⟪s.R, u⟫ - β) (58 * α * H ^ 3) (58 * α * H ^ 3 * j)
      (by simpa only [sub_eq_add_neg, add_assoc] using hi) he.B_error
    change |(pairedCoordinates b α μ β c u).B - (s.B + ⟪s.R, u⟫ - β)| ≤ _
    simp only [sub_eq_add_neg, add_assoc] at ht ⊢
    nlinarith

noncomputable def coordinateStart (d : ℕ) : Coordinates d :=
  ⟨1, 0, 0, 0, 0, ContinuousLinearMap.id ℝ (Features d)⟩

noncomputable def comparisonStart (d : ℕ) : Comparison d := ⟨0, 0, 0, 0, 0⟩

lemma bias_error {d : ℕ} (α μ H j : ℝ) (c : Coordinates d) (s : Comparison d)
    (hα : 0 ≤ α) (hH : 1 ≤ H) (hj : 0 ≤ j) (hjH : j ≤ H)
    (he : Errors α μ H j c s) (hc : Envelope H c) (hs : ComparisonBound j s) :
    |bias c - comparisonBias s| ≤ 256 * α * H ^ 4 := by
  have hH0 : 0 ≤ H := by linarith
  have ha : |(c.a - 1) * c.B| ≤ 80 * α * H ^ 3 := by
    rw [abs_mul]
    calc
      |c.a - 1| * |c.B| ≤ (5 * α * j) * (16 * H ^ 2) :=
        mul_le_mul he.a_error hc.B_bound (abs_nonneg _) (by positivity)
      _ ≤ (5 * α * H) * (16 * H ^ 2) := by gcongr
      _ = 80 * α * H ^ 3 := by ring
  have hb : |c.B - s.B| ≤ 58 * α * H ^ 4 := by
    have hm := mul_le_mul_of_nonneg_left hjH (show 0 ≤ 58 * α * H ^ 3 by positivity)
    nlinarith [he.B_error]
  have hx : |⟪c.X - s.V, c.S⟫| ≤ 80 * α * H ^ 4 := by
    calc
      |⟪c.X - s.V, c.S⟫| ≤ ‖c.X - s.V‖ * ‖c.S‖ := abs_real_inner_le_norm _ _
      _ ≤ (20 * α * H ^ 2 * j) * (4 * H) :=
        mul_le_mul he.X_error hc.S_bound (norm_nonneg _) (by positivity)
      _ ≤ (20 * α * H ^ 2 * H) * (4 * H) := by gcongr
      _ = 80 * α * H ^ 4 := by ring
  have hz : |⟪s.V, c.S - s.U⟫| ≤ 20 * α * H ^ 4 := by
    calc
      |⟪s.V, c.S - s.U⟫| ≤ ‖s.V‖ * ‖c.S - s.U‖ := abs_real_inner_le_norm _ _
      _ ≤ j * (20 * α * H ^ 2 * j) :=
        mul_le_mul hs.V_bound he.S_error (norm_nonneg _) hj
      _ ≤ H * (20 * α * H ^ 2 * H) := by gcongr
      _ = 20 * α * H ^ 4 := by ring
  have hd : bias c - comparisonBias s = (c.a - 1) * c.B + (c.B - s.B) +
      ⟪c.X - s.V, c.S⟫ + ⟪s.V, c.S - s.U⟫ := by
    simp only [bias, comparisonBias, inner_sub_left, inner_sub_right]
    ring
  rw [hd]
  have h1 := abs_add_le ((c.a - 1) * c.B) (c.B - s.B)
  have h2 := abs_add_le ((c.a - 1) * c.B + (c.B - s.B)) ⟪c.X - s.V, c.S⟫
  have h3 := abs_add_le ((c.a - 1) * c.B + (c.B - s.B) + ⟪c.X - s.V, c.S⟫)
    ⟪s.V, c.S - s.U⟫
  have hp := mul_nonneg hα (show 0 ≤ H ^ 4 - H ^ 3 by
    nlinarith [mul_nonneg (show 0 ≤ H ^ 3 by positivity) (show 0 ≤ H - 1 by linarith)])
  have hp' : 0 ≤ α * H ^ 4 := by positivity
  linarith

lemma score_error {d : ℕ} (α μ β H j : ℝ) (c : Coordinates d) (s : Comparison d)
    (u : Features d) (hα : 0 ≤ α) (hα₁ : α ≤ 1) (hβ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hμ : μ ^ 2 ≤ 1) (hH : 1 ≤ H) (hj : 0 ≤ j) (hjH : j ≤ H) (hu : ‖u‖ ≤ 1)
    (he : Errors α μ H j c s) (hc : Envelope H c) (hs : ComparisonBound j s) :
    |⟪c.S, c.F u⟫ - α * (1 + β * α * μ ^ 2) * bias c +
        α ^ 2 * μ ^ 2 * c.B * ⟪c.R, u⟫ - ⟪s.U, u⟫| ≤ 256 * α * H ^ 3 := by
  have hH0 : 0 ≤ H := by linarith
  have hν : 0 ≤ β * α * μ ^ 2 := by positivity
  have hν₁ : β * α * μ ^ 2 ≤ 1 := by
    calc
      β * α * μ ^ 2 ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  have hFu : ‖c.F u‖ ≤ 2 := by
    exact (c.F.le_opNorm u).trans (by nlinarith [mul_le_mul hc.matrix_bound hu (norm_nonneg u) (by norm_num)])
  have hF : ‖(c.F - ContinuousLinearMap.id ℝ (Features d)) u‖ ≤ 8 * α * H ^ 2 := by
    calc
      ‖(c.F - ContinuousLinearMap.id ℝ (Features d)) u‖ ≤
          ‖c.F - ContinuousLinearMap.id ℝ (Features d)‖ * ‖u‖ :=
        (c.F - ContinuousLinearMap.id ℝ (Features d)).le_opNorm u
      _ ≤ (8 * α * μ ^ 2 * H * j) * 1 :=
        mul_le_mul he.F_error hu (norm_nonneg _) (by positivity)
      _ ≤ (8 * α * 1 * H * H) * 1 := by gcongr
      _ = 8 * α * H ^ 2 := by ring
  have hS : |⟪c.S - s.U, c.F u⟫| ≤ 40 * α * H ^ 3 := by
    calc
      |⟪c.S - s.U, c.F u⟫| ≤ ‖c.S - s.U‖ * ‖c.F u‖ := abs_real_inner_le_norm _ _
      _ ≤ (20 * α * H ^ 2 * j) * 2 :=
        mul_le_mul he.S_error hFu (norm_nonneg _) (by positivity)
      _ ≤ (20 * α * H ^ 2 * H) * 2 := by gcongr
      _ = 40 * α * H ^ 3 := by ring
  have hU : |⟪s.U, (c.F - ContinuousLinearMap.id ℝ (Features d)) u⟫| ≤
      8 * α * H ^ 3 := by
    calc
      |⟪s.U, (c.F - ContinuousLinearMap.id ℝ (Features d)) u⟫| ≤
          ‖s.U‖ * ‖(c.F - ContinuousLinearMap.id ℝ (Features d)) u‖ := abs_real_inner_le_norm _ _
      _ ≤ j * (8 * α * H ^ 2) := mul_le_mul hs.U_bound hF (norm_nonneg _) hj
      _ ≤ H * (8 * α * H ^ 2) := by gcongr
      _ = 8 * α * H ^ 3 := by ring
  have hC : |α * (1 + β * α * μ ^ 2) * bias c| ≤ 96 * α * H ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc
      α * (1 + β * α * μ ^ 2) * |bias c| ≤ α * 2 * (48 * H ^ 2) := by
        gcongr
        · linarith
        · exact bias_envelope H c hH0 hc
      _ = 96 * α * H ^ 2 := by ring
  have hRu : |⟪c.R, u⟫| ≤ 4 * H := by
    exact (abs_real_inner_le_norm _ _).trans
      (by nlinarith [mul_le_mul hc.R_bound hu (norm_nonneg _) (by positivity)])
  have hB : |α ^ 2 * μ ^ 2 * c.B * ⟪c.R, u⟫| ≤ 64 * α * H ^ 3 := by
    simp only [abs_mul, abs_of_nonneg (sq_nonneg α), abs_of_nonneg (sq_nonneg μ)]
    calc
      α ^ 2 * μ ^ 2 * |c.B| * |⟪c.R, u⟫| ≤ α * 1 * (16 * H ^ 2) * (4 * H) := by
        gcongr
        · nlinarith
        · exact hc.B_bound
      _ = 64 * α * H ^ 3 := by ring
  have hd : ⟪c.S, c.F u⟫ - ⟪s.U, u⟫ =
      ⟪c.S - s.U, c.F u⟫ + ⟪s.U, (c.F - ContinuousLinearMap.id ℝ (Features d)) u⟫ := by
    simp only [inner_sub_left, sub_apply, ContinuousLinearMap.id_apply, inner_sub_right]
    ring
  have hD := abs_add_le ⟪c.S - s.U, c.F u⟫
    ⟪s.U, (c.F - ContinuousLinearMap.id ℝ (Features d)) u⟫
  rw [← hd] at hD
  have ht := abs_sub (⟪c.S, c.F u⟫ - ⟪s.U, u⟫) (α * (1 + β * α * μ ^ 2) * bias c)
  have ht' := abs_add_le ((⟪c.S, c.F u⟫ - ⟪s.U, u⟫) -
    α * (1 + β * α * μ ^ 2) * bias c) (α ^ 2 * μ ^ 2 * c.B * ⟪c.R, u⟫)
  have hrew : (⟪c.S, c.F u⟫ - ⟪s.U, u⟫) - α * (1 + β * α * μ ^ 2) * bias c +
      α ^ 2 * μ ^ 2 * c.B * ⟪c.R, u⟫ =
      ⟪c.S, c.F u⟫ - α * (1 + β * α * μ ^ 2) * bias c +
        α ^ 2 * μ ^ 2 * c.B * ⟪c.R, u⟫ - ⟪s.U, u⟫ := by ring
  rw [hrew] at ht'
  have hp' := mul_nonneg hα (show 0 ≤ H ^ 3 - H ^ 2 by nlinarith [sq_nonneg H])
  have hp'' : 0 ≤ α * H ^ 3 := by positivity
  linarith

end LongTails.Proofs.CyclicPerceptronBootstrap
