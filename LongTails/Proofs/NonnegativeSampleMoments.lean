import LongTails.Setups.NonnegativeSmoothSampleLoss
import LongTails.Proofs.GdConvex
import LongTails.Proofs.ProxLinearOracleMoments
import Mathlib.Analysis.Asymptotics.Lemmas

open MeasureTheory Filter Asymptotics
open scoped Topology RealInnerProductSpace

namespace LongTails.Proofs.NonnegativeSampleMoments

open LongTails.Setups.NonnegativeSmoothSampleLoss
open OracleTemplate

abbrev parameters (q : Params) : LongTails.Setups.ExpectedSmoothnessNonconvex.Params where
  E := q.E
  Ω := q.Ω
  L := q.L
  A := q.L
  C := 0
  Δ := q.Δ
  ε := q.ε
  x0 := q.x0

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

lemma mean_hasGradientAt {loss : Ω → E → ℝ} {g : E → Ω → E} {L : ℝ}
    (hg : ∀ ω x, HasGradientAt (loss ω) (g x ω) x)
    (hl : ∀ ω x y, ‖g x ω - g y ω‖ ≤ L * ‖x - y‖)
    (hi : ∀ x, Integrable (fun ω => loss ω x) p) (hgi : ∀ x, Integrable (g x) p) (x : E) :
    HasGradientAt (fun y => ∫ ω, loss ω y ∂p) (∫ ω, g x ω ∂p) x := by
  rw [hasGradientAt_iff_isLittleO]
  apply Asymptotics.IsBigO.trans_isLittleO _ (Asymptotics.isLittleO_pow_sub_sub x
    (by norm_num : 1 < 2))
  apply Asymptotics.IsBigO.of_bound (L / 2)
  filter_upwards [] with y
  have hm : ∀ ω, |loss ω y - loss ω x - ⟪g x ω, y - x⟫| ≤ L / 2 * ‖y - x‖ ^ 2 := by
    intro ω
    have hu := Gradient.smooth_upper_bound (hg ω) (hl ω) x y
    have hn := Gradient.smooth_upper_bound (L := L) (f := fun z => -loss ω z) (oracle := fun z => -g z ω)
      (fun z => by
        rw [hasGradientAt_iff_hasFDerivAt]
        rw [map_neg]
        exact (hg ω z).hasFDerivAt.neg)
      (fun z w => by
        rw [show -g z ω - -g w ω = -(g z ω - g w ω) by abel, norm_neg]
        exact hl ω z w) x y
    rw [inner_neg_left] at hn
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hint : Integrable (fun ω => loss ω y - loss ω x - ⟪g x ω, y - x⟫) p :=
    ((hi y).sub (hi x)).sub ((hgi x).inner_const _)
  have hav : (∫ ω, ⟪g x ω, y - x⟫ ∂p) = ⟪∫ ω, g x ω ∂p, y - x⟫ := by
    calc
      _ = ∫ ω, ⟪y - x, g x ω⟫ ∂p := integral_congr_ae (Eventually.of_forall fun _ => real_inner_comm _ _)
      _ = _ := by rw [integral_inner (hgi x), real_inner_comm (∫ ω, g x ω ∂p) (y - x)]
  have hid : (∫ ω, loss ω y ∂p) - (∫ ω, loss ω x ∂p) - ⟪∫ ω, g x ω ∂p, y - x⟫ =
      ∫ ω, loss ω y - loss ω x - ⟪g x ω, y - x⟫ ∂p := by
    rw [integral_sub (f := fun ω => loss ω y - loss ω x) (g := fun ω => ⟪g x ω, y - x⟫)
      ((hi y).sub (hi x)) ((hgi x).inner_const _), integral_sub (hi y) (hi x), hav]
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖y - x‖)]
  rw [hid]
  exact (abs_integral_le_integral_abs).trans (by
    simpa using integral_mono hint.abs (integrable_const (L / 2 * ‖y - x‖ ^ 2)) hm)

lemma admissible {q : Params} (hL : 0 < q.L) {f O} (h : spec.admissible q f O) :
    LongTails.Setups.ExpectedSmoothnessNonconvex.spec.admissible (parameters q) f O := by
  obtain ⟨loss, g, p, P, hIID, rfl, hnn, hg, hl, hmeas, hi, hf, hΔ⟩ := h
  have hme (x : q.E) : Measurable (g x) := hmeas.comp (measurable_const.prodMk measurable_id)
  have hself (x : q.E) (ω : q.Ω) : ‖g x ω‖ ^ 2 ≤ 2 * q.L * loss ω x := by
    have hd := Gradient.descent hL (hg ω) (hl ω) x
    have hn := hnn ω (x - (1 / q.L) • g x ω)
    have hb : ‖g x ω‖ ^ 2 / (2 * q.L) ≤ loss ω x := by linarith
    simpa [mul_comm] using (div_le_iff₀ (by positivity : 0 < 2 * q.L)).mp hb
  have h2 (x : q.E) : Integrable (fun ω => ‖g x ω‖ ^ 2) (p : Measure _) :=
    ((hi x).const_mul (2 * q.L)).mono' ((hme x).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa using hself x ω)
  have hgi (x : q.E) : Integrable (g x) (p : Measure _) :=
    ((OracleTemplate.TwoSidedPL.memLp_two_iff_sq (hme x).aestronglyMeasurable).mpr (h2 x)).integrable
      (by norm_num)
  have hfg (x : q.E) : HasGradientAt f (∫ ω, g x ω ∂(p : Measure _)) x := by
    rw [show f = _ from funext hf]
    exact mean_hasGradientAt hg hl hi hgi x
  have hm (x : q.E) := (hfg x).gradient
  have hdiff (x y : q.E) (ω : q.Ω) : ‖g x ω - g y ω‖ ^ 2 ≤ q.L ^ 2 * ‖x - y‖ ^ 2 := by
    simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hl ω x y) 2
  have hdi (x y : q.E) : Integrable (fun ω => ‖g x ω - g y ω‖ ^ 2) (p : Measure _) :=
    (integrable_const (q.L ^ 2 * ‖x - y‖ ^ 2)).mono'
      (((hme x).sub (hme y)).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa using hdiff x y ω)
  have hvar (x : q.E) := ProxLinearOracleMoments.centered_second_moment (hgi x) (h2 x) _ (hm x).symm
  refine ⟨g, p, P, hIID, rfl, fun x => by rw [hm x]; exact hfg x, ?_, hmeas, hgi, fun x => (hm x).symm,
    fun x => (hvar x).1, hdi, ?_, 0, ?_, by simpa using hΔ, ?_⟩
  · intro x y
    rw [hm x, hm y, ← integral_sub (hgi x) (hgi y)]
    apply (norm_integral_le_integral_norm _).trans
    simpa using integral_mono ((hgi x).sub (hgi y)).norm (integrable_const _) (fun ω => hl ω x y)
  · intro x y
    simpa [parameters] using integral_mono (hdi x y) (integrable_const _) (hdiff x y)
  · intro x
    rw [hf x]
    exact integral_nonneg (fun ω => hnn ω x)
  · intro x
    rw [(hvar x).2, hf x]
    have hb := integral_mono (h2 x) ((hi x).const_mul _) (hself x)
    rw [integral_const_mul] at hb
    dsimp [parameters]
    linarith [sq_nonneg ‖gradient f x‖]

end LongTails.Proofs.NonnegativeSampleMoments
