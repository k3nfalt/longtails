import LongTails.Proofs.BiasedLowerInstance

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.BiasedLowerOracle

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardOracle
open LongTails.Proofs.AbcLowerParameters LongTails.Proofs.AbcLowerAssembly
open LongTails.Proofs.AbcLowerMeasure LongTails.Proofs.AbcHardContinuity
open LongTails.Proofs.BiasedDecoy LongTails.Proofs.BiasedLowerInstance
open LongTails.Setups.HighDimensionalBiasedNoiseNonconvex

noncomputable def qfB (q : Params) : ℕ → ℝ := revealProb (abcParams q) (chainDim (abcParams q))

noncomputable def zc (q : Params) (sg : ℝ) (x : Space (q.d + 1)) : ℝ :=
  sg * ⟪eLast (d := q.d), x - q.x0⟫ - 100 * wid q

noncomputable def objB (q : Params) (S : Scale) (π : Fin (chainDim (abcParams q) + 1) ↪ Fin q.d)
    (sg : ℝ) (x : Space (q.d + 1)) : ℝ :=
  objective S π (drop q.x0) (drop x) + amp q * pr (wid q) (zc q sg x)

noncomputable def decoyGrad (q : Params) (sg : ℝ) (x : Space (q.d + 1)) : ℝ :=
  amp q * dpr (wid q) (zc q sg x) * sg

noncomputable def gradB (q : Params) (S : Scale) (π : Fin (chainDim (abcParams q) + 1) ↪ Fin q.d)
    (sg : ℝ) (x : Space (q.d + 1)) : Space (q.d + 1) :=
  pad (objGrad S π (drop q.x0) (drop x)) + decoyGrad q sg x • eLast

def Hides (q : Params) (S : Scale) (π : Fin (chainDim (abcParams q) + 1) ↪ Fin q.d) (sg : ℝ)
    (x : Space (q.d + 1)) : Prop :=
  theta q * |dpr (wid q) (zc q sg x)| ≤ ‖objGrad S π (drop q.x0) (drop x)‖

noncomputable def replyB (q : Params) (S : Scale) (π : Fin (chainDim (abcParams q) + 1) ↪ Fin q.d)
    (sg : ℝ) (x : Space (q.d + 1)) (ω : ℝ) : Space (q.d + 1) :=
  open Classical in
  if Hides q S π sg x then pad (reply S (qfB q) π (drop q.x0) (drop x) ω)
  else pad (reply S (qfB q) π (drop q.x0) (drop x) ω) + decoyGrad q sg x • eLast

noncomputable def oracleB (q : Params) (S : Scale) (π : Fin (chainDim (abcParams q) + 1) ↪ Fin q.d)
    (sg : ℝ) : Oracle (Space (q.d + 1)) (Space (q.d + 1)) where
  Seed := fun _ => ℝ
  law := ⟨stream, inferInstance⟩
  answer := fun _ (_, x) ω => replyB q S π sg x ω

section Facts

variable (q : Params) (hv : spec.valid q) (S : Scale)
  (π : Fin (chainDim (abcParams q) + 1) ↪ Fin q.d) (sg : ℝ)

lemma sg_sq (hsg : sg = 1 ∨ sg = -1) : sg ^ 2 = 1 := by rcases hsg with h | h <;> rw [h] <;> norm_num

lemma abs_sg (hsg : sg = 1 ∨ sg = -1) : |sg| = 1 := by rcases hsg with h | h <;> rw [h] <;> norm_num

include hv in
lemma objB_hasGradientAt (x : Space (q.d + 1)) :
    HasGradientAt (objB q S π sg) (gradB q S π sg x) x := by
  have h1 := comp_drop_hasGradientAt (objective_hasGradientAt S π (drop q.x0) (drop x))
  have h2 := decoy_hasGradientAt q.x0 (amp q) (wid q) (100 * wid q) sg (wid_pos q hv) x
  have h := h1.add h2
  have hf : objB q S π sg = ((fun y => objective S π (drop q.x0) (drop y)) +
      fun y => amp q * pr (wid q) (sg * ⟪eLast (d := q.d), y - q.x0⟫ - 100 * wid q)) := by
    funext y; rfl
  rw [hf, hasGradientAt_iff_hasFDerivAt]
  have hg : gradB q S π sg x = pad (objGrad S π (drop q.x0) (drop x)) + decoyGrad q sg x • eLast :=
    rfl
  rw [hg, map_add]
  exact h

include hv in
lemma objB_gradient (x : Space (q.d + 1)) : gradient (objB q S π sg) x = gradB q S π sg x :=
  (objB_hasGradientAt q hv S π sg x).gradient

include hv in
lemma gradB_lip (hsg : sg = 1 ∨ sg = -1) (hS : 1024 * S.a / S.lam ^ 2 = q.L / 2)
    (x y : Space (q.d + 1)) :
    ‖gradB q S π sg x - gradB q S π sg y‖ ≤ q.L * ‖x - y‖ := by
  have hw := wid_pos q hv
  have ha := amp_nonneg q hv
  have hdiv := amp_div_wid q hv
  have he : gradB q S π sg x - gradB q S π sg y =
      pad (objGrad S π (drop q.x0) (drop x) - objGrad S π (drop q.x0) (drop y)) +
        (decoyGrad q sg x - decoyGrad q sg y) • eLast := by
    simp only [gradB, map_sub, sub_smul]; abel
  rw [he]
  have h1 : ‖pad (objGrad S π (drop q.x0) (drop x) - objGrad S π (drop q.x0) (drop y))‖ ≤
      q.L / 2 * ‖x - y‖ := by
    rw [norm_pad]
    have hl := objGrad_lipschitz S π (drop q.x0) (drop x) (drop y)
    rw [hS, ← map_sub] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left (norm_drop_le _) (by linarith [hv.1]))
  have h2 : ‖(decoyGrad q sg x - decoyGrad q sg y) • eLast (d := q.d)‖ ≤ q.L / 2 * ‖x - y‖ := by
    rw [norm_smul, norm_eLast, mul_one, Real.norm_eq_abs]
    have hin : ⟪eLast (d := q.d), x - q.x0⟫ - ⟪eLast (d := q.d), y - q.x0⟫ =
        ⟪eLast (d := q.d), x - y⟫ := by
      rw [← inner_sub_right]; congr 1; abel
    have hd : zc q sg x - zc q sg y = sg * ⟪eLast (d := q.d), x - y⟫ := by
      unfold zc
      linear_combination sg * hin
    have hz : |zc q sg x - zc q sg y| ≤ ‖x - y‖ := by
      rw [hd, abs_mul, abs_sg sg hsg, one_mul]
      exact abs_inner_eLast_le _
    have hd := dpr_lip hw (zc q sg x) (zc q sg y)
    unfold decoyGrad
    rw [show amp q * dpr (wid q) (zc q sg x) * sg - amp q * dpr (wid q) (zc q sg y) * sg =
      amp q * sg * (dpr (wid q) (zc q sg x) - dpr (wid q) (zc q sg y)) by ring, abs_mul, abs_mul,
      abs_of_nonneg ha, abs_sg sg hsg, mul_one]
    calc amp q * |dpr (wid q) (zc q sg x) - dpr (wid q) (zc q sg y)| ≤
        amp q * (‖x - y‖ / wid q) := mul_le_mul_of_nonneg_left (hd.trans
          (div_le_div_of_nonneg_right hz hw.le)) ha
      _ = amp q / wid q * ‖x - y‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdiv (norm_nonneg _)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ q.L / 2 * ‖x - y‖ + q.L / 2 * ‖x - y‖ := add_le_add h1 h2
    _ = _ := by ring

lemma norm_gradB_sq (x : Space (q.d + 1)) :
    ‖gradB q S π sg x‖ ^ 2 = ‖objGrad S π (drop q.x0) (drop x)‖ ^ 2 + decoyGrad q sg x ^ 2 :=
  norm_sq_pad_add _ _

lemma decoyGrad_sq (hsg : sg = 1 ∨ sg = -1) (x : Space (q.d + 1)) :
    decoyGrad q sg x ^ 2 = (amp q * dpr (wid q) (zc q sg x)) ^ 2 := by
  unfold decoyGrad
  rw [mul_pow, mul_pow, sg_sq sg hsg, mul_one]

include hv in
lemma decoyGrad_abs_le (hsg : sg = 1 ∨ sg = -1) (x : Space (q.d + 1)) :
    amp q * |dpr (wid q) (zc q sg x)| ≤ ‖gradB q S π sg x‖ := by
  have h := norm_gradB_sq q S π sg x
  rw [decoyGrad_sq q sg hsg] at h
  have ha := amp_nonneg q hv
  have hsq : (amp q * |dpr (wid q) (zc q sg x)|) ^ 2 ≤ ‖gradB q S π sg x‖ ^ 2 := by
    rw [h, mul_pow, sq_abs, ← mul_pow]
    nlinarith [sq_nonneg ‖objGrad S π (drop q.x0) (drop x)‖]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hsq

lemma objGrad_le_gradB (x : Space (q.d + 1)) :
    ‖objGrad S π (drop q.x0) (drop x)‖ ≤ ‖gradB q S π sg x‖ := by
  have h := norm_gradB_sq q S π sg x
  have hsq : ‖objGrad S π (drop q.x0) (drop x)‖ ^ 2 ≤ ‖gradB q S π sg x‖ ^ 2 := by
    rw [h]; nlinarith [sq_nonneg (decoyGrad q sg x)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

end Facts

end LongTails.Proofs.BiasedLowerOracle
