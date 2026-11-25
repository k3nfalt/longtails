import LongTails.Proofs.NcPlParams
import LongTails.Proofs.NonconvexPLMoreau
import LongTails.Proofs.AbcLowerMeasure
import LongTails.Proofs.Execution
import LongTails.TemplateLowerBound

open MeasureTheory OracleTemplate
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.NcPlLowerBound

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open LongTails.Setups.HighDimensionalStochasticNonconvexPL
open LongTails.Setups.StochasticTwoSidedPL (maxValue minimaxValue)
open LongTails.Setups.StochasticNonconvexPL (IsJointOracle IsProxPoint moreauResidual)
open OracleTemplate.NonconvexPL (Hyp xbar)
open LongTails.Proofs.NcPlChainPL LongTails.Proofs.NcPlCut LongTails.Proofs.NcPlInstance
open LongTails.Proofs.NcPlLipschitz LongTails.Proofs.NcPlPL LongTails.Proofs.NcPlMoreau
open LongTails.Proofs.NcPlOracle LongTails.Proofs.NcPlOracleStats LongTails.Proofs.NcPlHiding
open LongTails.Proofs.NcPlParams
open LongTails.Proofs.AbcHardFunction (Space sel sel_norm adjoint_norm)
open LongTails.Proofs.MintyChainGeometry (ball)
open LongTails.Proofs.AbcHardOracle (unif)
open LongTails.Proofs.AbcHardExecution (coinCount)
open LongTails.Proofs.AbcLowerMeasure (stream coinCount_tail coinCount_measurable)
open LongTails.Proofs.FiniteSumNondualLowerAveraging LongTails.Proofs.FiniteSumNondualLowerBound

variable (q : Params)

noncomputable def ux (x : Space q.d) : Space q.d := (1 / ss q) • (x - q.x0)

noncomputable def uy (y : Space q.d) : Space q.d := (1 / ss q) • (y - q.y0)

noncomputable def hardFn (π : Fin ((geo q).k + 1) ↪ Fin q.d) :
    Space q.d → Space q.d → ℝ := fun x y =>
  ee q * hardF (geo q) π (ux q x) (uy q y)

noncomputable def gxS (π : Fin ((geo q).k + 1) ↪ Fin q.d) (x y : Space q.d) : Space q.d :=
  (ee q / ss q) • hardGx (geo q) π (ux q x) (uy q y)

noncomputable def gyS (π : Fin ((geo q).k + 1) ↪ Fin q.d) (x y : Space q.d) : Space q.d :=
  (ee q / ss q) • hardGy (geo q) π (ux q x) (uy q y)

noncomputable def GxS (π : Fin ((geo q).k + 1) ↪ Fin q.d) (w : Space q.d × Space q.d) (ω : ℝ) :
    Space q.d :=
  (ee q / ss q) • replyX (geo q) π (th q) (qq q) (ux q w.1) (uy q w.2) ω

noncomputable def GyS (π : Fin ((geo q).k + 1) ↪ Fin q.d) (w : Space q.d × Space q.d) (ω : ℝ) :
    Space q.d :=
  (ee q / ss q) • replyY (geo q) π (th q) (qq q) (ux q w.1) (uy q w.2) ω

noncomputable def hardOracle (π : Fin ((geo q).k + 1) ↪ Fin q.d) :
    Oracle (Space q.d × Space q.d) (Space q.d × Space q.d) where
  Seed := fun _ => ℝ
  law := ⟨stream, inferInstance⟩
  answer := fun _ w ω => (GxS q π w.2 ω, GyS q π w.2 ω)

lemma ux_hasFDerivAt (x : Space q.d) :
    HasFDerivAt (ux q) ((1 / ss q) • ContinuousLinearMap.id ℝ (Space q.d)) x := by
  have h := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const q.x0).const_smul (1 / ss q)
  have he : ux q = fun y => (1 / ss q) • (y - q.x0) := rfl
  rw [he]
  exact h

lemma uy_hasFDerivAt (y : Space q.d) :
    HasFDerivAt (uy q) ((1 / ss q) • ContinuousLinearMap.id ℝ (Space q.d)) y := by
  have h := ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const q.y0).const_smul (1 / ss q)
  have he : uy q = fun z => (1 / ss q) • (z - q.y0) := rfl
  rw [he]
  exact h

lemma ux_x0 : ux q q.x0 = 0 := by
  unfold ux
  rw [sub_self, smul_zero]

lemma uy_y0 : uy q q.y0 = 0 := by
  unfold uy
  rw [sub_self, smul_zero]

lemma hardFn_grad_x (π : Fin ((geo q).k + 1) ↪ Fin q.d) (x y : Space q.d) :
    HasGradientAt (fun x => hardFn q π x y) (gxS q π x y) x := by
  have hd := ((hardF_hasGradientAt_x (geo q) π (ux q x) (uy q y)).hasFDerivAt.comp x
    (ux_hasFDerivAt q x)).const_mul (ee q)
  rw [hasGradientAt_iff_hasFDerivAt]
  refine HasFDerivAt.congr_fderiv hd ?_
  ext v
  have key : ee q * ⟪hardGx (geo q) π (ux q x) (uy q y), (1 / ss q) • v⟫ =
      ⟪gxS q π x y, v⟫ := by
    unfold gxS
    rw [real_inner_smul_right, real_inner_smul_left]
    ring
  exact key

lemma hardFn_grad_y (π : Fin ((geo q).k + 1) ↪ Fin q.d) (x y : Space q.d) :
    HasGradientAt (fun y => hardFn q π x y) (gyS q π x y) y := by
  have hd := ((hardF_hasGradientAt_y (geo q) π (ux q x) (uy q y)).hasFDerivAt.comp y
    (uy_hasFDerivAt q y)).const_mul (ee q)
  rw [hasGradientAt_iff_hasFDerivAt]
  refine HasFDerivAt.congr_fderiv hd ?_
  ext v
  have key : ee q * ⟪hardGy (geo q) π (ux q x) (uy q y), (1 / ss q) • v⟫ =
      ⟪gyS q π x y, v⟫ := by
    unfold gyS
    rw [real_inner_smul_right, real_inner_smul_left]
    ring
  exact key

section Valid

variable {q} (hv : spec.valid q) (π : Fin ((geo q).k + 1) ↪ Fin q.d)

include hv

lemma ux_sub (x x' : Space q.d) : ‖ux q x - ux q x'‖ = ‖x - x'‖ / ss q := by
  have hs := ss_pos hv
  unfold ux
  rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_of_nonneg (by positivity)]
  ring

lemma uy_sub (y y' : Space q.d) : ‖uy q y - uy q y'‖ = ‖y - y'‖ / ss q := by
  have hs := ss_pos hv
  unfold uy
  rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_of_nonneg (by positivity)]
  ring

lemma ux_inv (v : Space q.d) : ux q (q.x0 + ss q • v) = v := by
  have hs := ss_pos hv
  unfold ux
  rw [add_sub_cancel_left, smul_smul, one_div, inv_mul_cancel₀ hs.ne', one_smul]

lemma uy_inv (v : Space q.d) : uy q (q.y0 + ss q • v) = v := by
  have hs := ss_pos hv
  unfold uy
  rw [add_sub_cancel_left, smul_smul, one_div, inv_mul_cancel₀ hs.ne', one_smul]

lemma scale_lip (a b : ℝ) :
    ee q / ss q * (2 ^ 26 * (a / ss q + b / ss q)) = q.L * (a + b) := by
  have hs := ss_pos hv
  have h := ee_div_ss_sq hv
  have e : ee q / ss q * (2 ^ 26 * (a / ss q + b / ss q)) =
      ee q / ss q ^ 2 * 2 ^ 26 * (a + b) := by
    field_simp
  rw [e, h]
  ring

lemma gxS_lip (x x' y y' : Space q.d) :
    ‖gxS q π x y - gxS q π x' y'‖ ≤ q.L * (‖x - x'‖ + ‖y - y'‖) := by
  have he := ee_pos hv
  have hs := ss_pos hv
  have hl := hardGx_lip (geo q) π (ux q x') (uy q y') (ux q x) (uy q y)
  rw [ux_sub hv, uy_sub hv] at hl
  unfold gxS
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [← scale_lip hv]
  exact mul_le_mul_of_nonneg_left hl (by positivity)

lemma gyS_lip (x x' y y' : Space q.d) :
    ‖gyS q π x y - gyS q π x' y'‖ ≤ q.L * (‖x - x'‖ + ‖y - y'‖) := by
  have he := ee_pos hv
  have hs := ss_pos hv
  have hl := hardGy_lip (geo q) π (ux q x') (uy q y') (ux q x) (uy q y)
  rw [ux_sub hv, uy_sub hv] at hl
  unfold gyS
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [← scale_lip hv]
  exact mul_le_mul_of_nonneg_left hl (by positivity)

lemma scale_sq : (ee q / ss q) ^ 2 = ee q * (q.L / 2 ^ 26) := by
  have hs := ss_pos hv
  rw [← ee_div_ss_sq hv]
  field_simp

lemma hardFn_pl (x y y' : Space q.d) :
    2 * q.μ * (hardFn q π x y' - hardFn q π x y) ≤ ‖gyS q π x y‖ ^ 2 := by
  have he := ee_pos hv
  have hμ := pos_μ hv
  have hpl := hardF_pl (geo q) π (ux q x) (uy q y) (uy q y')
  have hc := pl_const hv
  have hn := sq_nonneg ‖hardGy (geo q) π (ux q x) (uy q y)‖
  unfold gyS hardFn
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, scale_sq hv]
  have h1 : 2 * q.μ * (ee q * (hardF (geo q) π (ux q x) (uy q y') -
      hardF (geo q) π (ux q x) (uy q y))) ≤
      2 * q.μ * (ee q * (147 / lamOf (geo q).n * ‖hardGy (geo q) π (ux q x) (uy q y)‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpl he.le) (by positivity)
  have h2 : 2 * q.μ * (147 / lamOf (nn q)) * (ee q * ‖hardGy (geo q) π (ux q x) (uy q y)‖ ^ 2) ≤
      q.L / 2 ^ 26 * (ee q * ‖hardGy (geo q) π (ux q x) (uy q y)‖ ^ 2) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  have e3 : (geo q).n = nn q := rfl
  rw [e3] at h1
  nlinarith

lemma hardFn_attain (x : Space q.d) : ∃ y, ∀ y', hardFn q π x y' ≤ hardFn q π x y := by
  have he := ee_pos hv
  obtain ⟨yt, hyt⟩ := hardF_attain (geo q) π (ux q x)
  refine ⟨q.y0 + ss q • yt, fun y' => ?_⟩
  unfold hardFn
  rw [uy_inv hv]
  exact mul_le_mul_of_nonneg_left (hyt _) he.le

lemma hardFn_lower (x : Space q.d) :
    -(6 * ee q * ((mm q : ℝ) + 1)) ≤ hardFn q π x q.y0 := by
  have he := ee_pos hv
  have h := hardF_ge (geo q) π (ux q x) (uy q q.y0)
  rw [uy_y0, base_zero _ (geo q).scales.hρ.le] at h
  have e3 : ((geo q).m : ℝ) = (mm q : ℝ) := rfl
  rw [e3] at h
  unfold hardFn
  rw [uy_y0]
  have hx : 0 ≤ ‖ux q x‖ ^ 2 / 32 := by positivity
  nlinarith

lemma hardFn_bddAbove (x : Space q.d) : BddAbove (Set.range (hardFn q π x)) := by
  obtain ⟨y, hy⟩ := hardFn_attain hv π x
  exact ⟨hardFn q π x y, by rintro _ ⟨y', rfl⟩; exact hy y'⟩

lemma maxValue_lower (x : Space q.d) :
    -(6 * ee q * ((mm q : ℝ) + 1)) ≤ maxValue (hardFn q π) x :=
  (hardFn_lower hv π x).trans (le_ciSup (hardFn_bddAbove hv π x) q.y0)

theorem hyp : Hyp (hardFn q π) (gxS q π) (gyS q π) q.L q.μ where
  hL := pos_L hv
  hμy := pos_μ hv
  hμyL := hv.1.2.1
  hgx := hardFn_grad_x q π
  hgy := hardFn_grad_y q π
  lipx := fun x x' y y' => gxS_lip hv π x x' y y'
  lipy := fun x x' y y' => gyS_lip hv π x x' y y'
  ply := hardFn_pl hv π
  attain := hardFn_attain hv π
  bdd := ⟨-(6 * ee q * ((mm q : ℝ) + 1)), by rintro _ ⟨x, rfl⟩; exact maxValue_lower hv π x⟩

lemma maxValue_eq (x : Space q.d) :
    maxValue (hardFn q π) x = ee q * Phi (geo q) π (ux q x) := by
  have he := ee_pos hv
  have H := hyp hv π
  apply le_antisymm
  · obtain ⟨y, hy⟩ := H.maxValue_attained x
    rw [hy]
    exact mul_le_mul_of_nonneg_left (ymax_spec (geo q) π (ux q x) (uy q y)) he.le
  · have h := H.le_maxValue x (q.y0 + ss q • ymax (geo q) π (ux q x))
    unfold hardFn at h
    rw [uy_inv hv] at h
    exact h

theorem moreau_big (zout : Space q.d)
    (hsmall : |ball (2 * (geo q).Bx) (ux q zout)
      (π ⟨(geo q).m * ((geo q).n + 2) + ((geo q).n + 1), upos_lt (geo q) le_rfl⟩)| ≤ 1 / 4) :
    2 * q.ε ≤ moreauResidual (hardFn q π) q.L zout := by
  have he := ee_pos hv
  have hs := ss_pos hv
  have hL := pos_L hv
  have hε := pos_ε hv
  have H := hyp hv π
  rw [H.moreauResidual_eq]
  have hp := H.isProxPoint_xbar zout
  have hscale : ∀ a b : Space q.d, q.L * ‖a - b‖ ^ 2 = ee q * (2 ^ 26 * ‖ux q a - ux q b‖ ^ 2) := by
    intro a b
    rw [ux_sub hv, div_pow]
    have h := ee_div_ss_sq hv
    have e : ee q * (2 ^ 26 * (‖a - b‖ ^ 2 / ss q ^ 2)) = ee q / ss q ^ 2 * 2 ^ 26 * ‖a - b‖ ^ 2 := by
      field_simp
    rw [e, h]
    ring
  have hprox : ∀ x', Phi (geo q) π (ux q (xbar (hardFn q π) q.L zout)) +
      2 ^ 26 * ‖ux q (xbar (hardFn q π) q.L zout) - ux q zout‖ ^ 2 ≤
      Phi (geo q) π x' + 2 ^ 26 * ‖x' - ux q zout‖ ^ 2 := by
    intro x'
    have h := hp (q.x0 + ss q • x')
    rw [maxValue_eq hv π, maxValue_eq hv π, hscale, hscale, ux_inv hv] at h
    have h2 : ee q * (Phi (geo q) π (ux q (xbar (hardFn q π) q.L zout)) +
        2 ^ 26 * ‖ux q (xbar (hardFn q π) q.L zout) - ux q zout‖ ^ 2) ≤
        ee q * (Phi (geo q) π x' + 2 ^ 26 * ‖x' - ux q zout‖ ^ 2) := by linarith
    exact le_of_mul_le_mul_left h2 he
  have hm := moreau_lower (geo q) π (ux q zout) (ux q (xbar (hardFn q π) q.L zout)) hprox hsmall
  rw [ux_sub hv] at hm
  rw [norm_sub_rev]
  have e : 2 * q.L * ‖xbar (hardFn q π) q.L zout - zout‖ =
      2 ^ 5 * q.ε * (2 * 2 ^ 26 * (‖xbar (hardFn q π) q.L zout - zout‖ / ss q)) := by
    unfold ss
    field_simp
  rw [e]
  nlinarith

theorem hard_admissible : spec.admissible q (hardFn q π) (hardOracle q π) := by
  have he := ee_pos hv
  have hs := ss_pos hv
  have hL := pos_L hv
  have hε := pos_ε hv
  have H := hyp hv π
  have hq0 := qq_pos hv
  have hq1 := qq_le_one hv
  have hes : 0 ≤ ee q / ss q := by positivity
  refine ⟨fun z => gxS q π z.1 z.2, fun z => gyS q π z.1 z.2, GxS q π, GyS q π,
    ⟨unif, inferInstanceAs (IsProbabilityMeasure unif)⟩, rfl, fun z => H.hgx z.1 z.2, fun z => H.hgy z.1 z.2,
    fun z z' => H.lipx z.1 z'.1 z.2 z'.2, fun z z' => H.lipy z.1 z'.1 z.2 z'.2,
    H.ply, H.attain, H.bdd, ?_, ?_⟩
  · have hm : Measurable (fun z : (Space q.d × Space q.d) × ℝ =>
        ((ux q z.1.1, uy q z.1.2), z.2)) :=
      ((((measurable_fst.comp measurable_fst).sub_const q.x0).const_smul (1 / ss q)).prodMk
        (((measurable_snd.comp measurable_fst).sub_const q.y0).const_smul (1 / ss q))).prodMk
        measurable_snd
    have hsq : ∀ (w : Space q.d × Space q.d) (ω : ℝ),
        ‖GxS q π w ω - gxS q π w.1 w.2‖ ^ 2 + ‖GyS q π w ω - gyS q π w.1 w.2‖ ^ 2 =
        (ee q / ss q) ^ 2 *
          (‖replyX (geo q) π (th q) (qq q) (ux q w.1) (uy q w.2) ω -
              hardGx (geo q) π (ux q w.1) (uy q w.2)‖ ^ 2 +
            ‖replyY (geo q) π (th q) (qq q) (ux q w.1) (uy q w.2) ω -
              hardGy (geo q) π (ux q w.1) (uy q w.2)‖ ^ 2) := by
      intro w ω
      unfold GxS GyS gxS gyS
      rw [← smul_sub, ← smul_sub, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
        sq_abs]
      ring
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ((replyX_measurable (geo q) π (th q) (qq q)).comp hm).const_smul (ee q / ss q)
    · exact ((replyY_measurable (geo q) π (th q) (qq q)).comp hm).const_smul (ee q / ss q)
    · intro w
      exact (replyX_integrable (geo q) π (th q) (qq q) _ _).smul (ee q / ss q)
    · intro w
      exact (replyY_integrable (geo q) π (th q) (qq q) _ _).smul (ee q / ss q)
    · intro w
      change ∫ ω, (ee q / ss q) • replyX (geo q) π (th q) (qq q) (ux q w.1) (uy q w.2) ω ∂unif = _
      rw [integral_smul, replyX_integral (geo q) π (th q) hq0 hq1]
      rfl
    · intro w
      change ∫ ω, (ee q / ss q) • replyY (geo q) π (th q) (qq q) (ux q w.1) (uy q w.2) ω ∂unif = _
      rw [integral_smul, replyY_integral (geo q) π (th q) hq0 hq1]
      rfl
    · intro w
      have hi := (reply_var_integrable (geo q) π (th q) (q := qq q) (ux q w.1)
        (uy q w.2)).const_mul ((ee q / ss q) ^ 2)
      have hfun : (fun ω => ‖GxS q π w ω - gxS q π w.1 w.2‖ ^ 2 +
          ‖GyS q π w ω - gyS q π w.1 w.2‖ ^ 2) = fun ω => (ee q / ss q) ^ 2 *
          (‖replyX (geo q) π (th q) (qq q) (ux q w.1) (uy q w.2) ω -
              hardGx (geo q) π (ux q w.1) (uy q w.2)‖ ^ 2 +
            ‖replyY (geo q) π (th q) (qq q) (ux q w.1) (uy q w.2) ω -
              hardGy (geo q) π (ux q w.1) (uy q w.2)‖ ^ 2) := funext fun ω => hsq w ω
      change Integrable (fun ω => ‖GxS q π w ω - gxS q π w.1 w.2‖ ^ 2 +
          ‖GyS q π w ω - gyS q π w.1 w.2‖ ^ 2) unif
      rw [hfun]
      exact hi
    · intro w
      have hfun : (fun ω => ‖GxS q π w ω - gxS q π w.1 w.2‖ ^ 2 +
          ‖GyS q π w ω - gyS q π w.1 w.2‖ ^ 2) = fun ω => (ee q / ss q) ^ 2 *
          (‖replyX (geo q) π (th q) (qq q) (ux q w.1) (uy q w.2) ω -
              hardGx (geo q) π (ux q w.1) (uy q w.2)‖ ^ 2 +
            ‖replyY (geo q) π (th q) (qq q) (ux q w.1) (uy q w.2) ω -
              hardGy (geo q) π (ux q w.1) (uy q w.2)‖ ^ 2) := funext fun ω => hsq w ω
      change ∫ ω, (‖GxS q π w ω - gxS q π w.1 w.2‖ ^ 2 +
          ‖GyS q π w ω - gyS q π w.1 w.2‖ ^ 2) ∂unif ≤ q.σ ^ 2
      rw [hfun, integral_const_mul]
      have hvar := reply_var_le (geo q) π (th_pos q).le (th_le_rho q)
        (le_trans (th_le_quarter q) (by norm_num)) hq0 hq1 (ux q w.1) (uy q w.2)
      have hw := mask_width q
      have hw0 : 0 ≤ 2 ^ 23 * th q + 1 / (3 * ((nn q : ℝ) + 1) * (1 / (n1 q : ℝ))) := by
        have := th_pos q
        have := n1_real_pos q
        positivity
      have hw2 := pow_le_pow_left₀ hw0 hw 2
      have hq' : 0 ≤ 1 / qq q - 1 := by
        rw [sub_nonneg, le_div_iff₀ hq0]
        linarith
      have hqv := qq_var hv
      have h1 : (1 / qq q - 1) * (2 ^ 23 * th q +
          1 / (3 * ((nn q : ℝ) + 1) * (1 / (n1 q : ℝ)))) ^ 2 ≤ q.σ ^ 2 / (1024 * q.ε ^ 2) := by
        rw [← hqv]
        exact mul_le_mul_of_nonneg_left hw2 hq'
      have e32 : (ee q / ss q) ^ 2 = 1024 * q.ε ^ 2 := by
        rw [ee_div_ss hv]
        ring
      rw [e32]
      have h2 := mul_le_mul_of_nonneg_left (hvar.trans h1) (by positivity : (0 : ℝ) ≤ 1024 * q.ε ^ 2)
      have e3 : 1024 * q.ε ^ 2 * (q.σ ^ 2 / (1024 * q.ε ^ 2)) = q.σ ^ 2 := by
        field_simp
      rw [e3] at h2
      exact h2
  · change 2 * maxValue (hardFn q π) q.x0 - minimaxValue (hardFn q π) - hardFn q π q.x0 q.y0 +
      ‖gxS q π q.x0 q.y0‖ ^ 2 / q.L ≤ q.Δ
    have hm0 : (0 : ℝ) ≤ (mm q : ℝ) + 1 := by positivity
    have h1 : maxValue (hardFn q π) q.x0 ≤ 0 := by
      rw [maxValue_eq hv π, ux_x0]
      have h := hardF_le (geo q) π 0 (ymax (geo q) π 0)
      have hb := base_le_zero (lamOf_pos (geo q).n).le (geo q).ρ (ymax (geo q) π 0)
      rw [norm_zero] at h
      have : Phi (geo q) π 0 ≤ 0 := by
        unfold Phi
        linarith
      nlinarith
    have h2 : -(6 * ee q * ((mm q : ℝ) + 1)) ≤ minimaxValue (hardFn q π) :=
      le_ciInf fun x => maxValue_lower hv π x
    have h3 := hardFn_lower hv π q.x0
    have h4 : ‖gxS q π q.x0 q.y0‖ ^ 2 / q.L ≤ ee q * ((mm q : ℝ) + 1) := by
      unfold gxS
      rw [ux_x0, uy_y0, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, scale_sq hv]
      have hg : hardGx (geo q) π 0 0 = cutv (geo q).Bx (0 : Space q.d) •
          (sel π).adjoint (vA (geo q) π 0 0) := by
        unfold hardGx
        rw [smul_zero, map_zero, inner_zero_right, zero_smul, zero_add, add_zero]
      have hn : ‖hardGx (geo q) π 0 0‖ ^ 2 ≤ 2 ^ 16 * ((mm q : ℝ) + 1) := by
        have hv2 := gAvec_sq (geo q) (chA (geo q) π 0) (seq (sel π (0 : Space q.d)))
          (cutv_nonneg (geo q).By (0 : Space q.d)) (cutv_le_one (geo q).By (0 : Space q.d))
        have hle : ‖hardGx (geo q) π 0 0‖ ≤ ‖vA (geo q) π 0 0‖ := by
          rw [hg, norm_smul, Real.norm_eq_abs]
          have h5 := cutv_abs (geo q).Bx (0 : Space q.d)
          have h6 := adjoint_norm π (vA (geo q) π 0 0)
          have h7 := norm_nonneg ((sel π).adjoint (vA (geo q) π 0 0))
          nlinarith [abs_nonneg (cutv (geo q).Bx (0 : Space q.d))]
        have hsq2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
        exact hsq2.trans hv2
      rw [div_le_iff₀ hL]
      have h8 := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ ee q * (q.L / 2 ^ 26))
      have hpos : 0 ≤ ee q * ((mm q : ℝ) + 1) * q.L := by positivity
      nlinarith
    have h5 := delta_room hv
    nlinarith

end Valid

end LongTails.Proofs.NcPlLowerBound
