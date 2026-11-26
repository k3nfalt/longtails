import LongTails.Proofs.BiasedLowerOracle

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.BiasedLowerAdmissible

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardOracle
open LongTails.Proofs.AbcLowerParameters LongTails.Proofs.AbcLowerAssembly
open LongTails.Proofs.AbcLowerMeasure LongTails.Proofs.AbcHardContinuity
open LongTails.Proofs.BiasedDecoy LongTails.Proofs.BiasedLowerInstance
open LongTails.Proofs.BiasedLowerOracle
open LongTails.Setups.HighDimensionalBiasedNoiseNonconvex

section AbcVariance

open LongTails.Proofs.AbcHardGeometry

lemma abc_reply_var (p : LongTails.Setups.HighDimensionalAbcNoiseNonconvex.Params)
    (hv : LongTails.Setups.HighDimensionalAbcNoiseNonconvex.spec.valid p) (hA : p.A = 0)
    (π : Fin (chainDim p + 1) ↪ Fin p.d) (x : Space p.d) :
    ∫ ω, ‖reply (scaleOf p hv.1 hv.2.2.2.2.1) (revealProb p (chainDim p)) π p.x0 x ω -
        objGrad (scaleOf p hv.1 hv.2.2.2.2.1) π p.x0 x‖ ^ 2 ∂unif ≤
      p.B * ‖objGrad (scaleOf p hv.1 hv.2.2.2.2.1) π p.x0 x‖ ^ 2 + p.C := by
  have hB := hv.2.2.1
  have hC := hv.2.2.2.1
  have hε := hv.2.2.2.2.1
  set S := scaleOf p hv.1 hv.2.2.2.2.1
  have hratio : S.a / S.lam = 60 * p.ε := amplitude_ratio p hv.1 hε
  rw [reply_variance S _ (revealProb_pos p hε (chainDim p)) (revealProb_le p hε (chainDim p))]
  set w := toUnit S p.x0 x
  set m := stage (sel π w)
  have hsec := secret_norm S π p.x0 x
  rw [hratio] at hsec
  by_cases hfull : (chainDim p) + 1 ≤ m
  · rw [objGrad, knownPart, knownGrad_full π m w hfull, sub_self, norm_zero]
    nlinarith [mul_nonneg hB (sq_nonneg ‖objGrad S π p.x0 x‖), hC]
  · push Not at hfull
    have hlev : 0 ≤ levelBudget p (chainDim p) m := by
      unfold levelBudget
      rw [hA]
      nlinarith [sq_nonneg p.ε]
    have hvar := variance_le_budget p hε (chainDim p) m _ (norm_nonneg _)
      (le_of_le_of_eq hsec (by ring)) hlev
    refine hvar.trans ?_
    unfold levelBudget
    rw [hA]
    have hgrad := hardGrad_lower π w (last_small_of_stage _ (by omega))
    have hgo : 3 * p.ε ≤ ‖objGrad S π p.x0 x‖ := by
      rw [objGrad, norm_smul, Real.norm_of_nonneg (by have := S.ha; have := S.hlam; positivity),
        hratio]
      nlinarith
    have hg2 : 9 * p.B * p.ε ^ 2 ≤ p.B * ‖objGrad S π p.x0 x‖ ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hgo 2
      nlinarith
    linarith

end AbcVariance

noncomputable def scaleB (q : Params) (hv : spec.valid q) : Scale :=
  scaleOf (abcParams q) (abc_valid q hv).1 (abc_valid q hv).2.2.2.2.1

section

variable (q : Params) (hv : spec.valid q) (π : Fin (chainDim (abcParams q) + 1) ↪ Fin q.d)
  (sg : ℝ)

include hv in
lemma qfB_pos : ∀ m, 0 < qfB q m :=
  fun m => revealProb_pos (abcParams q) (abc_valid q hv).2.2.2.2.1 _ m

include hv in
lemma qfB_le : ∀ m, qfB q m ≤ 1 :=
  fun m => revealProb_le (abcParams q) (abc_valid q hv).2.2.2.2.1 _ m

lemma replyB_integrable (S : Scale) (x : Space (q.d + 1)) : Integrable (replyB q S π sg x) unif := by
  unfold replyB
  split_ifs
  · exact pad.integrable_comp (reply_integrable S (qfB q) π (drop q.x0) (drop x))
  · exact (pad.integrable_comp (reply_integrable S (qfB q) π (drop q.x0) (drop x))).add
      (integrable_const _)

include hv in
lemma integral_replyB (S : Scale) (x : Space (q.d + 1)) :
    ∫ ω, replyB q S π sg x ω ∂unif =
      (open Classical in if Hides q S π sg x then pad (objGrad S π (drop q.x0) (drop x))
      else gradB q S π sg x) := by
  have hpad : ∫ ω, pad (reply S (qfB q) π (drop q.x0) (drop x) ω) ∂unif =
      pad (objGrad S π (drop q.x0) (drop x)) := by
    rw [ContinuousLinearMap.integral_comp_comm pad
      (reply_integrable S (qfB q) π (drop q.x0) (drop x)),
      reply_integral S (qfB q) (qfB_pos q hv) (qfB_le q hv)]
  unfold replyB
  split_ifs with h
  · exact hpad
  · rw [integral_add (pad.integrable_comp (reply_integrable S (qfB q) π (drop q.x0) (drop x)))
      (integrable_const _), hpad, integral_const]
    simp [gradB]

include hv in
lemma replyB_sub_mean (S : Scale) (x : Space (q.d + 1)) (ω : ℝ) :
    replyB q S π sg x ω - ∫ ω', replyB q S π sg x ω' ∂unif =
      pad (reply S (qfB q) π (drop q.x0) (drop x) ω - objGrad S π (drop q.x0) (drop x)) := by
  rw [integral_replyB q hv π sg S x]
  unfold replyB gradB
  split_ifs
  · simp only [map_sub]
  · simp only [map_sub]
    abel

include hv in
set_option maxHeartbeats 800000 in
lemma replyB_measurable (S : Scale) : Measurable (Function.uncurry (replyB q S π sg)) := by
  classical
  have hw := wid_pos q hv
  have hzc : Continuous (zc q sg) := by
    unfold zc
    exact (continuous_const.mul (continuous_const.inner (continuous_id.sub continuous_const))).sub
      continuous_const
  have hdec : Continuous (decoyGrad q sg) := by
    unfold decoyGrad
    exact (continuous_const.mul ((dpr_continuous hw).comp hzc)).mul continuous_const
  have hog : Continuous (fun x : Space (q.d + 1) => objGrad S π (drop q.x0) (drop x)) :=
    (objGrad_continuous S π (drop q.x0)).comp drop.continuous
  have hf1 : Measurable (fun p : Space (q.d + 1) × ℝ => theta q * |dpr (wid q) (zc q sg p.1)|) :=
    ((continuous_const.mul ((dpr_continuous hw).comp hzc).abs).comp continuous_fst).measurable
  have hf2 : Measurable (fun p : Space (q.d + 1) × ℝ => ‖objGrad S π (drop q.x0) (drop p.1)‖) :=
    (hog.norm.comp continuous_fst).measurable
  have hset : MeasurableSet {p : Space (q.d + 1) × ℝ | Hides q S π sg p.1} :=
    measurableSet_le hf1 hf2
  have hR0 := (reply_measurable S (qfB q) π (drop q.x0)).comp
    ((drop.continuous.measurable.comp measurable_fst).prodMk measurable_snd)
  have hR : Measurable (fun p : Space (q.d + 1) × ℝ =>
      reply S (qfB q) π (drop q.x0) (drop p.1) p.2) := by
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using hR0
  have hA : Measurable (fun p : Space (q.d + 1) × ℝ =>
      pad (reply S (qfB q) π (drop q.x0) (drop p.1) p.2)) :=
    pad.continuous.measurable.comp hR
  have hD : Measurable (fun p : Space (q.d + 1) × ℝ => decoyGrad q sg p.1 • eLast (d := q.d)) :=
    (hdec.measurable.comp measurable_fst).smul_const _
  have hB : Measurable (fun p : Space (q.d + 1) × ℝ =>
      pad (reply S (qfB q) π (drop q.x0) (drop p.1) p.2) + decoyGrad q sg p.1 • eLast) :=
    hA.add hD
  have heq : Function.uncurry (replyB q S π sg) = fun p : Space (q.d + 1) × ℝ =>
      if Hides q S π sg p.1 then pad (reply S (qfB q) π (drop q.x0) (drop p.1) p.2)
      else pad (reply S (qfB q) π (drop q.x0) (drop p.1) p.2) + decoyGrad q sg p.1 • eLast := by
    funext p
    rfl
  rw [heq]
  exact Measurable.ite hset hA hB

theorem admissibleB (hsg : sg = 1 ∨ sg = -1) :
    spec.admissible q (objB q (scaleB q hv) π sg) (oracleB q (scaleB q hv) π sg) := by
  have hva := abc_valid q hv
  set S := scaleB q hv with hSdef
  obtain ⟨_, _, _, fstar0, _, _, _, _, hlow0, hinf0, hgap0, _⟩ :=
    hard_admissible (abcParams q) hva π
  have hS : 1024 * S.a / S.lam ^ 2 = q.L / 2 := smoothness_eq (abcParams q) hva.1 hva.2.2.2.2.1
  have hvarR : ∀ x : Space q.d,
      ∫ ω, ‖reply S (qfB q) π (drop q.x0) x ω - objGrad S π (drop q.x0) x‖ ^ 2 ∂unif ≤
        q.M * ‖objGrad S π (drop q.x0) x‖ ^ 2 + q.σ ^ 2 :=
    fun x => abc_reply_var (abcParams q) hva rfl π x
  have hm0 := hv.2.1
  have hM0 := hv.2.2.2.1
  have hw := wid_pos q hv
  have ha := amp_nonneg q hv
  refine ⟨fun x ω => replyB q S π sg x ω, ⟨unif, inferInstanceAs (IsProbabilityMeasure unif)⟩,
    ⟨stream, inferInstanceAs (IsProbabilityMeasure stream)⟩, fstar0 + amp q * wid q, stream_iid,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro (x : Space (q.d + 1))
    change HasGradientAt (objB q S π sg) (gradient (objB q S π sg) x) x
    rw [objB_gradient q hv S π sg x]
    exact objB_hasGradientAt q hv S π sg x
  · intro (x : Space (q.d + 1)) (y : Space (q.d + 1))
    change ‖gradient (objB q S π sg) x - gradient (objB q S π sg) y‖ ≤ q.L * ‖x - y‖
    rw [objB_gradient q hv S π sg x, objB_gradient q hv S π sg y]
    exact gradB_lip q hv S π sg hsg hS x y
  · intro (x : Space (q.d + 1))
    have h1 : fstar0 ≤ objective S π (drop q.x0) (drop x) := hlow0 (drop x)
    have h2 := pr_ge (w := wid q) (zc q sg x)
    have h3 := mul_le_mul_of_nonneg_left h2 ha
    unfold objB
    linarith
  · intro η hη
    obtain ⟨x0', hx'⟩ := hinf0 η hη
    obtain ⟨x', hxx⟩ : ∃ x' : Space q.d, x' = x0' := ⟨x0', rfl⟩
    have hx'' : objective S π (drop q.x0) x' < fstar0 + η := by rw [hxx]; exact hx'
    set t : ℝ := ⟪eLast (d := q.d), q.x0⟫ + sg * (100 * wid q) with ht
    let y : Space (q.d + 1) := pad (d := q.d) x' + t • eLast (d := q.d)
    refine ⟨y, ?_⟩
    have hd : drop y = x' := by
      change drop (pad (d := q.d) x' + t • eLast (d := q.d)) = x'
      rw [map_add, map_smul, drop_pad, drop_eLast, smul_zero, add_zero]
    have hz : zc q sg y = 0 := by
      change zc q sg (pad (d := q.d) x' + t • eLast (d := q.d)) = 0
      unfold zc
      rw [inner_sub_right, inner_eLast_pad_add, ht]
      have := sg_sq sg hsg
      linear_combination (100 * wid q) * this
    unfold objB
    rw [hd, hz, pr_zero hw]
    linarith
  · change objB q S π sg q.x0 - (fstar0 + amp q * wid q) ≤ q.Δ
    have h1 : objective S π (drop q.x0) (drop q.x0) - fstar0 ≤ q.Δ / 2 := hgap0
    have hz : zc q sg q.x0 = -(100 * wid q) := by
      unfold zc; rw [sub_self, inner_zero_right, mul_zero]; ring
    have h2 := pr_le hw (zc q sg q.x0)
    rw [hz, abs_neg, abs_of_pos (by positivity)] at h2
    have h3 := gap_decoy q hv
    have h4 := mul_le_mul_of_nonneg_left h2 ha
    unfold objB
    rw [hz]
    nlinarith
  · exact replyB_measurable q hv π sg S
  · intro (x : Space (q.d + 1))
    exact replyB_integrable q π sg S x
  · intro (x : Space (q.d + 1))
    change ‖(∫ ω, replyB q S π sg x ω ∂unif) - gradient (objB q S π sg) x‖ ^ 2 ≤
      q.m * ‖gradient (objB q S π sg) x‖ ^ 2 + q.ζ ^ 2
    rw [objB_gradient q hv S π sg x, integral_replyB q hv π sg S x]
    split_ifs with h
    · have he : pad (objGrad S π (drop q.x0) (drop x)) - gradB q S π sg x =
          -(decoyGrad q sg x • eLast) := by simp [gradB]
      rw [he, norm_neg, norm_smul, norm_eLast, mul_one, Real.norm_eq_abs, sq_abs,
        norm_gradB_sq, decoyGrad_sq q sg hsg]
      have hb := bias_budget q hv ‖objGrad S π (drop q.x0) (drop x)‖ (dpr (wid q) (zc q sg x)) h
      nlinarith [sq_nonneg q.ζ]
    · rw [sub_self, norm_zero]
      have : 0 ≤ q.m * ‖gradB q S π sg x‖ ^ 2 := by positivity
      nlinarith [sq_nonneg q.ζ]
  · intro (x : Space (q.d + 1))
    change Integrable (fun ω => ‖replyB q S π sg x ω - ∫ ω', replyB q S π sg x ω' ∂unif‖ ^ 2) unif
    have he : (fun ω => ‖replyB q S π sg x ω - ∫ ω', replyB q S π sg x ω' ∂unif‖ ^ 2) =
        fun ω => ‖reply S (qfB q) π (drop q.x0) (drop x) ω -
          objGrad S π (drop q.x0) (drop x)‖ ^ 2 := by
      funext ω; rw [replyB_sub_mean q hv π sg S x ω, norm_pad]
    rw [he]
    exact reply_variance_integrable S (qfB q) π (drop q.x0) (drop x)
  · intro (x : Space (q.d + 1))
    change ∫ ω, ‖replyB q S π sg x ω - ∫ ω', replyB q S π sg x ω' ∂unif‖ ^ 2 ∂unif ≤
      q.M * ‖∫ ω, replyB q S π sg x ω ∂unif‖ ^ 2 + q.σ ^ 2
    have he : (fun ω => ‖replyB q S π sg x ω - ∫ ω', replyB q S π sg x ω' ∂unif‖ ^ 2) =
        fun ω => ‖reply S (qfB q) π (drop q.x0) (drop x) ω -
          objGrad S π (drop q.x0) (drop x)‖ ^ 2 := by
      funext ω; rw [replyB_sub_mean q hv π sg S x ω, norm_pad]
    rw [he]
    refine (hvarR (drop x)).trans ?_
    have hmean : ‖objGrad S π (drop q.x0) (drop x)‖ ^ 2 ≤
        ‖∫ ω, replyB q S π sg x ω ∂unif‖ ^ 2 := by
      rw [integral_replyB q hv π sg S x]
      split_ifs
      · rw [norm_pad]
      · rw [norm_gradB_sq]; nlinarith [sq_nonneg (decoyGrad q sg x)]
    nlinarith [mul_le_mul_of_nonneg_left hmean hM0]

end

end LongTails.Proofs.BiasedLowerAdmissible
