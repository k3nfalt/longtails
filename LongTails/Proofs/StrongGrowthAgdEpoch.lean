import LongTails.Proofs.StrongGrowthAgdInvariant
import LongTails.Proofs.StrongGrowthAgdMeasurable

namespace LongTails.Proofs.StrongGrowthAgdEpoch

open MeasureTheory LongTails.Algorithms.StrongGrowthRestartedAgd LongTails.Proofs.StrongGrowthAgdProcess
  LongTails.Proofs.StrongGrowthAgdMoments LongTails.Proofs.StrongGrowthAgdMeasurable
  LongTails.Proofs.StrongGrowthAgdWeights LongTails.Proofs.StrongGrowthAgdModel
  LongTails.Proofs.StrongGrowthAgdEpochEnd LongTails.Proofs.StrongGrowthAgdInvariant
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable (cfg : Config) (x0 : E) (g : E → Ω → E) (f : E → ℝ) {L ρ κ : ℝ}

noncomputable def W (sN : State E × E) : ℝ :=
  1 + ‖sN.1.x - x0‖ ^ 2 + ‖sN.1.xPrev - x0‖ ^ 2 + ‖sN.1.xStart - x0‖ ^ 2 + ‖sN.1.glast‖ ^ 2 +
    ‖sN.1.ybar‖ ^ 2 + ‖sN.2‖ ^ 2

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma W_pos (sN : State E × E) : 1 ≤ W x0 sN := by
  unfold W
  have : 0 ≤ ‖sN.1.x - x0‖ ^ 2 + ‖sN.1.xPrev - x0‖ ^ 2 + ‖sN.1.xStart - x0‖ ^ 2 + ‖sN.1.glast‖ ^ 2 +
      ‖sN.1.ybar‖ ^ 2 + ‖sN.2‖ ^ 2 := by positivity
  linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma W_nonneg (sN : State E × E) : 0 ≤ W x0 sN := by linarith [W_pos x0 sN]

lemma sq_le_five_quarter (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b + c) :
    a ^ 2 ≤ 5 / 4 * b ^ 2 + 5 * c ^ 2 := by
  have h1 : a * a ≤ (b + c) * (b + c) := mul_le_mul h h ha (add_nonneg hb hc)
  nlinarith [sq_nonneg (b / 2 - 2 * c)]

lemma sq_quarter_le (A B G : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B) (hG : 0 ≤ G) (h : A ≤ G + B / 8) :
    A ^ 2 / 4 - B ^ 2 / 192 ≤ G ^ 2 := by
  by_cases hcase : B / 8 ≤ A
  · have h' : A - B / 8 ≤ G := by linarith
    have h1 : (A - B / 8) * (A - B / 8) ≤ G * G := mul_le_mul h' h' (by linarith) hG
    nlinarith [sq_nonneg (A - 4 / 3 * (B / 8))]
  · rw [not_le] at hcase
    have h1 : A * A ≤ (B / 8) * (B / 8) := mul_le_mul hcase.le hcase.le hA (by linarith)
    nlinarith [sq_nonneg G]

lemma W_measurable : Measurable (W x0 : State E × E → ℝ) := by
  unfold W
  have hx : Measurable (fun sN : State E × E => sN.1.x) := measurable_x.comp measurable_fst
  have hxp : Measurable (fun sN : State E × E => sN.1.xPrev) := measurable_xPrev.comp measurable_fst
  have hxs : Measurable (fun sN : State E × E => sN.1.xStart) := measurable_xStart.comp measurable_fst
  have hgl : Measurable (fun sN : State E × E => sN.1.glast) := measurable_glast.comp measurable_fst
  have hyb : Measurable (fun sN : State E × E => sN.1.ybar) := measurable_ybar.comp measurable_fst
  have hN : Measurable (fun sN : State E × E => sN.2) := measurable_snd
  exact ((((((measurable_const.add ((hx.sub measurable_const).norm.pow_const 2)).add
    ((hxp.sub measurable_const).norm.pow_const 2)).add
    ((hxs.sub measurable_const).norm.pow_const 2)).add (hgl.norm.pow_const 2)).add
    (hyb.norm.pow_const 2)).add (hN.norm.pow_const 2))

lemma gradient_measurable (h : Hyp f L ρ) : Measurable (gradient f) :=
  h.gradDiff.continuous.measurable

lemma measurable_nextN (h : Hyp f L ρ) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => nextN cfg g f z.1 z.2) := by
  unfold nextN
  have hT : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => z.1.1.t) :=
    measurable_t.comp (measurable_fst.comp measurable_fst)
  have hD : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => z.1.1.done) :=
    measurable_done.comp (measurable_fst.comp measurable_fst)
  have hTr : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => z.1.1.trig) :=
    measurable_trig.comp (measurable_fst.comp measurable_fst)
  have hN : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hY : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => ypoint cfg z.1.1) :=
    (measurable_ypoint cfg).comp (measurable_fst.comp measurable_fst)
  have hset : MeasurableSet {z : (State E × E) × (Fin cfg.b → Ω) |
      z.1.1.done = false ∧ cfg.pos z.1.1.t < cfg.K ∧ z.1.1.trig = false} := by
    refine MeasurableSet.inter (hD (MeasurableSet.of_discrete (s := {false}))) ?_
    exact MeasurableSet.inter (hT (MeasurableSet.of_discrete (s := {n | cfg.pos n < cfg.K})))
      (hTr (MeasurableSet.of_discrete (s := {false})))
  refine Measurable.ite hset ?_ hN
  refine Measurable.add ?_ ?_
  · exact Measurable.ite (hT (MeasurableSet.of_discrete (s := {n | cfg.pos n = 0}))) measurable_const hN
  · refine Measurable.smul ((measurable_from_nat (f := fun n => pw cfg.K (cfg.pos n))).comp hT) ?_
    refine Measurable.sub ?_ ((gradient_measurable f h).comp hY)
    exact bmean_measurable_joint cfg hg (α := State E × E) (q := fun sN => ypoint cfg sN.1)
      ((measurable_ypoint cfg).comp measurable_fst)

lemma measurable_astep (h : Hyp f L ρ) (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (astep cfg x0 g f)) := by
  unfold Function.uncurry astep
  refine Measurable.prodMk ?_ (measurable_nextN cfg g f h hg)
  exact (measurable_blockStep cfg x0 hg).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

lemma measurable_astep_fun (h : Hyp f L ρ) (hg : Measurable (Function.uncurry g)) (sN : State E × E) :
    Measurable (fun ω : Fin cfg.b → Ω => astep cfg x0 g f sN ω) :=
  (measurable_astep cfg x0 g f h hg).comp (measurable_const.prodMk measurable_id)

section bounds

variable (hb : 0 < cfg.b) (h : Hyp f L ρ) (ho : OracleHyp g (gradient f) p κ) (hκ : 1 ≤ κ)
include hb h ho hκ

omit h hκ in
lemma integrable_of_quad_bound (F : (Fin cfg.b → Ω) → ℝ) (hF : Measurable F) (q : E) (a c : ℝ)
    (hbd : ∀ ω, |F ω| ≤ a + c * ‖bmean cfg g q ω‖ ^ 2) :
    Integrable F (Measure.pi fun _ : Fin cfg.b => p) := by
  refine ((integrable_const a).add ((bmean_sq_integrable cfg hb ho q).const_mul c)).mono'
    hF.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs]
  exact hbd ω

omit hb h ho hκ [MeasurableSpace E] [BorelSpace E] in
lemma gradf_sq_le (h : Hyp f L ρ) (y : E) :
    ‖gradient f y‖ ^ 2 ≤ 2 * ‖gradient f x0‖ ^ 2 + 2 * L ^ 2 * ‖y - x0‖ ^ 2 := by
  have h1 : ‖gradient f y‖ ≤ ‖gradient f x0‖ + L * ‖y - x0‖ := by
    have := h.lip y x0
    have h2 := norm_sub_norm_le (gradient f y) (gradient f x0)
    linarith
  have h0 : 0 ≤ ‖gradient f x0‖ + L * ‖y - x0‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg h.hL.le (norm_nonneg _))
  nlinarith [sq_nonneg (‖gradient f x0‖ - L * ‖y - x0‖), norm_nonneg (gradient f y), h.hL.le]

lemma ghat_sq_integral_le (q : E) :
    ∫ ω, ‖bmean cfg g q ω‖ ^ 2 ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      (1 + (κ - 1) / cfg.b) * (2 * ‖gradient f x0‖ ^ 2 + 2 * L ^ 2 * ‖q - x0‖ ^ 2) := by
  refine (integral_bmean_sq_le cfg hb ho q).trans ?_
  have hδ : 0 ≤ 1 + (κ - 1) / cfg.b := by
    have : 0 ≤ (κ - 1) / cfg.b := div_nonneg (by linarith) (Nat.cast_nonneg _)
    linarith
  exact mul_le_mul_of_nonneg_left (gradf_sq_le x0 f h q) hδ

omit hb h ho hκ [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_add_sq_le_two (a b : E) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := norm_add_le a b
  nlinarith [norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖), norm_nonneg (a + b)]

omit hb h ho hκ [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_sub_sq_le_two (a b : E) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  rw [sub_eq_add_neg]
  have := norm_add_sq_le_two a (-b)
  rwa [norm_neg] at this

omit hb h ho hκ [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_smul_sq_le (c : ℝ) (v : E) (hc : |c| ≤ 1) : ‖c • v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow]
  have : |c| ^ 2 ≤ 1 := by nlinarith [abs_nonneg c]
  nlinarith [sq_nonneg ‖v‖]

omit hb h ho hκ [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma ypoint_sub_sq_le (hc : CfgHyp cfg) (s : State E) :
    ‖ypoint cfg s - x0‖ ^ 2 ≤ 6 * ‖s.x - x0‖ ^ 2 + 4 * ‖s.xPrev - x0‖ ^ 2 := by
  have e : ypoint cfg s - x0 = (s.x - x0) + (1 - cfg.θ) • ((s.x - x0) - (s.xPrev - x0)) := by
    unfold ypoint; abel
  rw [e]
  have h1 := norm_add_sq_le_two (s.x - x0) ((1 - cfg.θ) • ((s.x - x0) - (s.xPrev - x0)))
  have h2 := norm_smul_sq_le (1 - cfg.θ) ((s.x - x0) - (s.xPrev - x0))
    (by rw [abs_le]; constructor <;> linarith [hc.hθ0, hc.hθ1])
  have h3 := norm_sub_sq_le_two (s.x - x0) (s.xPrev - x0)
  nlinarith

omit hb h ho hκ [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma query_sub_sq_le (hc : CfgHyp cfg) (s : State E) :
    ‖queryPoint cfg s - x0‖ ^ 2 ≤
      6 * ‖s.x - x0‖ ^ 2 + 4 * ‖s.xPrev - x0‖ ^ 2 + 2 * ‖s.ybar‖ ^ 2 + 2 * ‖x0‖ ^ 2 := by
  unfold queryPoint
  have hy := ypoint_sub_sq_le cfg x0 hc s
  have hyb := norm_sub_sq_le_two s.ybar x0
  split_ifs <;> nlinarith [sq_nonneg ‖s.x - x0‖, sq_nonneg ‖s.xPrev - x0‖, sq_nonneg ‖s.ybar‖,
    sq_nonneg ‖x0‖]

omit hb h ho hκ [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] in
lemma W_astep_le (hc : CfgHyp cfg) (sN : State E × E) (ω : Fin cfg.b → Ω) :
    W x0 (astep cfg x0 g f sN ω) ≤ 40 * W x0 sN + 4 * ‖x0‖ ^ 2 +
      (2 * cfg.η ^ 2 + 4 * cfg.ηf ^ 2 + 5) * ‖bmean cfg g (queryPoint cfg sN.1) ω‖ ^ 2 +
      4 * ‖gradient f (ypoint cfg sN.1)‖ ^ 2 := by
  obtain ⟨s, N⟩ := sN
  have hW1 := W_pos x0 (s, N)
  have hgh := sq_nonneg ‖bmean cfg g (queryPoint cfg s) ω‖
  have hgf := sq_nonneg ‖gradient f (ypoint cfg s)‖
  have hx0 := sq_nonneg ‖x0‖
  have hη := sq_nonneg cfg.η
  have hηf := sq_nonneg cfg.ηf
  have ha := sq_nonneg ‖s.x - x0‖
  have hb' := sq_nonneg ‖s.xPrev - x0‖
  have hcc := sq_nonneg ‖s.xStart - x0‖
  have hgl := sq_nonneg ‖s.glast‖
  have hyb := sq_nonneg ‖s.ybar‖
  have hn := sq_nonneg ‖N‖
  unfold astep
  by_cases hd : s.done = true
  · rw [blockStep_of_done cfg x0 g hd, nextN_of_not cfg g f ω (by simp [hd])]
    unfold W at *
    nlinarith
  have hd' : s.done = false := by simpa using hd
  by_cases hkK : cfg.pos s.t < cfg.K
  · by_cases htr : s.trig = true
    · rw [blockStep_frozen cfg x0 g hd' hkK htr, nextN_of_not cfg g f ω (by simp [htr])]
      unfold W at *
      simp only
      nlinarith
    · have htr' : s.trig = false := by simpa using htr
      rw [blockStep_agd cfg x0 g hd' hkK htr', nextN_agd cfg g f ω hd' hkK htr']
      have hq : queryPoint cfg s = ypoint cfg s := by simp [queryPoint, hkK, htr']
      rw [hq] at hgh ⊢
      have hK2 : 2 ≤ cfg.K := by have := hc.hK; omega
      have hw0 : 0 ≤ pw cfg.K (cfg.pos s.t) := pw_nonneg hK2 hkK.le
      have hw1 : pw cfg.K (cfg.pos s.t) ≤ 1 := by
        refine (pw_le hK2).trans ?_
        rw [div_le_one (by exact_mod_cast (show 0 < cfg.K by omega))]
        exact_mod_cast hK2
      have hwabs : |pw cfg.K (cfg.pos s.t)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have hy0 := ypoint_sub_sq_le cfg x0 hc s
      have hxn : ‖ypoint cfg s - cfg.η • bmean cfg g (ypoint cfg s) ω - x0‖ ^ 2 ≤
          2 * ‖ypoint cfg s - x0‖ ^ 2 + 2 * cfg.η ^ 2 * ‖bmean cfg g (ypoint cfg s) ω‖ ^ 2 := by
        have e : ypoint cfg s - cfg.η • bmean cfg g (ypoint cfg s) ω - x0 =
            (ypoint cfg s - x0) - cfg.η • bmean cfg g (ypoint cfg s) ω := by abel
        rw [e]
        have := norm_sub_sq_le_two (ypoint cfg s - x0) (cfg.η • bmean cfg g (ypoint cfg s) ω)
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at this
        linarith
      have hybn : ‖s.ybar + pw cfg.K (cfg.pos s.t) • ypoint cfg s‖ ^ 2 ≤
          2 * ‖s.ybar‖ ^ 2 + 2 * (2 * ‖ypoint cfg s - x0‖ ^ 2 + 2 * ‖x0‖ ^ 2) := by
        have h1 := norm_add_sq_le_two s.ybar (pw cfg.K (cfg.pos s.t) • ypoint cfg s)
        have h2 := norm_smul_sq_le (pw cfg.K (cfg.pos s.t)) (ypoint cfg s) hwabs
        have h3 : ‖ypoint cfg s‖ ^ 2 ≤ 2 * ‖ypoint cfg s - x0‖ ^ 2 + 2 * ‖x0‖ ^ 2 := by
          have := norm_add_sq_le_two (ypoint cfg s - x0) x0
          rwa [sub_add_cancel] at this
        nlinarith
      have hNn : ‖(if cfg.pos s.t = 0 then 0 else N) +
          pw cfg.K (cfg.pos s.t) • (bmean cfg g (ypoint cfg s) ω - gradient f (ypoint cfg s))‖ ^ 2 ≤
          2 * ‖N‖ ^ 2 + 2 * (2 * ‖bmean cfg g (ypoint cfg s) ω‖ ^ 2 + 2 * ‖gradient f (ypoint cfg s)‖ ^ 2) := by
        have h1 := norm_add_sq_le_two (if cfg.pos s.t = 0 then (0 : E) else N)
          (pw cfg.K (cfg.pos s.t) • (bmean cfg g (ypoint cfg s) ω - gradient f (ypoint cfg s)))
        have h2 := norm_smul_sq_le (pw cfg.K (cfg.pos s.t))
          (bmean cfg g (ypoint cfg s) ω - gradient f (ypoint cfg s)) hwabs
        have h3 := norm_sub_sq_le_two (bmean cfg g (ypoint cfg s) ω) (gradient f (ypoint cfg s))
        have h4 : ‖(if cfg.pos s.t = 0 then (0 : E) else N)‖ ^ 2 ≤ ‖N‖ ^ 2 := by
          split_ifs <;> simp
        nlinarith
      unfold W at *
      simp only
      nlinarith [mul_nonneg hη hgh, mul_nonneg hηf hgh]
  · by_cases hkE : cfg.pos s.t = cfg.K
    · rw [blockStep_gd cfg x0 g hd' hkE, nextN_of_not cfg g f ω (by omega)]
      have hq : queryPoint cfg s = s.x := by simp [queryPoint, hkE]
      rw [hq] at hgh ⊢
      have hxn : ‖s.x - cfg.ηf • bmean cfg g s.x ω - x0‖ ^ 2 ≤
          2 * ‖s.x - x0‖ ^ 2 + 2 * cfg.ηf ^ 2 * ‖bmean cfg g s.x ω‖ ^ 2 := by
        have e : s.x - cfg.ηf • bmean cfg g s.x ω - x0 = (s.x - x0) - cfg.ηf • bmean cfg g s.x ω := by abel
        rw [e]
        have := norm_sub_sq_le_two (s.x - x0) (cfg.ηf • bmean cfg g s.x ω)
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at this
        linarith
      unfold W at *
      simp only
      nlinarith [mul_nonneg hη hgh, mul_nonneg hηf hgh]
    · have hkK' : cfg.K < cfg.pos s.t := by omega
      have hEb : 1 < cfg.Eb := Eb_gt cfg (by have := hc.hK; omega)
      by_cases hlt : cfg.pos s.t + 1 < cfg.Eb
      · rw [blockStep_val cfg x0 g hd' hkK' hlt, nextN_of_not cfg g f ω (by omega)]
        unfold W at *
        simp only
        nlinarith
      · have heq : cfg.pos s.t + 1 = cfg.Eb := by
          have := pos_lt_Eb cfg (by omega) s.t; omega
        rw [blockStep_last cfg x0 g hd' hkK' heq, nextN_of_not cfg g f ω (by omega)]
        by_cases h1 : ¬ s.trig = true ∧ 2 * (if s.trig = true then s.vCount
            else s.vCount + (if ‖bmean cfg g s.ybar ω‖ ≤ cfg.thr then 1 else 0)) > cfg.m
        · rw [ite_eq_left h1]; unfold W at *; simp only; nlinarith
        · rw [ite_eq_right h1]
          unfold restart
          unfold W at *
          simp only
          split_ifs with h4
          · simp only [sub_self, norm_zero]; nlinarith
          · simp only [norm_zero]; nlinarith

omit hκ in
lemma W_astep_integrable (hc : CfgHyp cfg) (sN : State E × E) :
    Integrable (fun ω => W x0 (astep cfg x0 g f sN ω)) (Measure.pi fun _ : Fin cfg.b => p) := by
  refine integrable_of_quad_bound cfg g f hb ho _ ((W_measurable x0).comp
    (measurable_astep_fun cfg x0 g f h ho.meas sN)) (queryPoint cfg sN.1)
    (40 * W x0 sN + 4 * ‖x0‖ ^ 2 + 4 * ‖gradient f (ypoint cfg sN.1)‖ ^ 2)
    (2 * cfg.η ^ 2 + 4 * cfg.ηf ^ 2 + 5) (fun ω => ?_)
  rw [abs_of_nonneg (W_nonneg x0 _)]
  linarith [W_astep_le cfg x0 g f hc sN ω]

lemma W_astep_bound (hc : CfgHyp cfg) :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 ≤ C ∧ ∀ sN : State E × E,
      ∫ ω, W x0 (astep cfg x0 g f sN ω) ∂(Measure.pi fun _ : Fin cfg.b => p) ≤ A * W x0 sN + C := by
  set δ2 := (κ - 1) / cfg.b with hδ2
  have hδ0 : 0 ≤ δ2 := div_nonneg (by linarith) (Nat.cast_nonneg _)
  set c1 := 2 * cfg.η ^ 2 + 4 * cfg.ηf ^ 2 + 5 with hc1
  have hc10 : 0 ≤ c1 := by positivity
  refine ⟨40 + 12 * L ^ 2 * c1 * (1 + δ2) + 48 * L ^ 2,
    4 * ‖x0‖ ^ 2 + c1 * (1 + δ2) * (2 * ‖gradient f x0‖ ^ 2 + 4 * L ^ 2 * ‖x0‖ ^ 2) + 8 * ‖gradient f x0‖ ^ 2,
    by nlinarith [sq_nonneg L, mul_nonneg (mul_nonneg (sq_nonneg L) hc10) (by linarith : (0:ℝ) ≤ 1 + δ2)],
    by positivity, fun sN => ?_⟩
  have hWn := W_nonneg x0 sN
  have hpt : ∀ ω, W x0 (astep cfg x0 g f sN ω) ≤
      (40 * W x0 sN + 4 * ‖x0‖ ^ 2 + 4 * ‖gradient f (ypoint cfg sN.1)‖ ^ 2) +
        c1 * ‖bmean cfg g (queryPoint cfg sN.1) ω‖ ^ 2 := fun ω => by
    linarith [W_astep_le cfg x0 g f hc sN ω]
  have hint2 := (bmean_sq_integrable cfg hb ho (queryPoint cfg sN.1)).const_mul c1
  have h1 : ∫ ω, W x0 (astep cfg x0 g f sN ω) ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      ∫ ω, ((40 * W x0 sN + 4 * ‖x0‖ ^ 2 + 4 * ‖gradient f (ypoint cfg sN.1)‖ ^ 2) +
        c1 * ‖bmean cfg g (queryPoint cfg sN.1) ω‖ ^ 2) ∂(Measure.pi fun _ : Fin cfg.b => p) :=
    integral_mono (W_astep_integrable cfg x0 g f hb h ho hc sN) ((integrable_const _).add hint2) hpt
  rw [integral_add (integrable_const _) hint2, integral_const, integral_const_mul] at h1
  simp only [probReal_univ, one_smul] at h1
  have h2 := ghat_sq_integral_le cfg x0 g f hb h ho hκ (queryPoint cfg sN.1)
  have h3 := gradf_sq_le x0 f h (ypoint cfg sN.1)
  have h4 := query_sub_sq_le cfg x0 hc sN.1
  have h5 := ypoint_sub_sq_le cfg x0 hc sN.1
  have hW : ‖sN.1.x - x0‖ ^ 2 + ‖sN.1.xPrev - x0‖ ^ 2 + ‖sN.1.ybar‖ ^ 2 ≤ W x0 sN := by
    unfold W; nlinarith [sq_nonneg ‖sN.1.xStart - x0‖, sq_nonneg ‖sN.1.glast‖, sq_nonneg ‖sN.2‖]
  have hq6 : ‖queryPoint cfg sN.1 - x0‖ ^ 2 ≤ 6 * W x0 sN + 2 * ‖x0‖ ^ 2 := by
    nlinarith [sq_nonneg ‖sN.1.x - x0‖, sq_nonneg ‖sN.1.xPrev - x0‖, sq_nonneg ‖sN.1.ybar‖]
  have hy6 : ‖ypoint cfg sN.1 - x0‖ ^ 2 ≤ 6 * W x0 sN := by
    nlinarith [sq_nonneg ‖sN.1.x - x0‖, sq_nonneg ‖sN.1.xPrev - x0‖, sq_nonneg ‖sN.1.ybar‖]
  have hL2 := sq_nonneg L
  have hg0 := sq_nonneg ‖gradient f x0‖
  have hx02 := sq_nonneg ‖x0‖
  have hc1δ : 0 ≤ c1 * (1 + δ2) := by positivity
  have h2' := mul_le_mul_of_nonneg_left h2 hc10
  have h6 : c1 * ((1 + δ2) * (2 * ‖gradient f x0‖ ^ 2 + 2 * L ^ 2 * ‖queryPoint cfg sN.1 - x0‖ ^ 2)) ≤
      c1 * (1 + δ2) * (2 * ‖gradient f x0‖ ^ 2 + 2 * L ^ 2 * (6 * W x0 sN + 2 * ‖x0‖ ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hq6 (by positivity : (0:ℝ) ≤ 2 * L ^ 2)
    nlinarith
  have h7 : 4 * ‖gradient f (ypoint cfg sN.1)‖ ^ 2 ≤ 8 * ‖gradient f x0‖ ^ 2 + 48 * L ^ 2 * W x0 sN := by
    have := mul_le_mul_of_nonneg_left hy6 (by positivity : (0:ℝ) ≤ 2 * L ^ 2)
    nlinarith
  nlinarith

end bounds

section potential

variable {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (xS : E)

noncomputable def Psi (s : State E) : ℝ :=
  Phi b eig (fderiv ℝ (gradient f) xS) xS (gradient f xS) (f xS) cfg.η cfg.θ s.x (s.x - s.xPrev) +
    9 / 50 * cfg.η * ‖s.glast‖ ^ 2

variable {b eig xS}

omit [MeasurableSpace E] [BorelSpace E] in
lemma eig_le (h : Hyp f L ρ) (hH : ∀ j v, ⟪b j, fderiv ℝ (gradient f) xS v⟫ = eig j * ⟪b j, v⟫) (j : ι) :
    |eig j| ≤ L := by
  have h1 := hH j (b j)
  rw [real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow, mul_one] at h1
  rw [← h1]
  calc |⟪b j, fderiv ℝ (gradient f) xS (b j)⟫| ≤ ‖b j‖ * ‖fderiv ℝ (gradient f) xS (b j)‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖b j‖ * (‖fderiv ℝ (gradient f) xS‖ * ‖b j‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖fderiv ℝ (gradient f) xS‖ := by rw [b.norm_eq_one]; ring
    _ ≤ L := h.hessNorm xS

omit [MeasurableSpace E] [BorelSpace E] in
lemma heig_of (h : Hyp f L ρ) (hη : cfg.η = 1 / (8 * L))
    (hH : ∀ j v, ⟪b j, fderiv ℝ (gradient f) xS v⟫ = eig j * ⟪b j, v⟫) (j : ι) :
    -1 / 8 ≤ cfg.η * eig j ∧ cfg.η * eig j ≤ 1 / 8 := by
  have hL := h.hL
  have he := eig_le f h hH j
  rw [abs_le] at he
  rw [hη]
  constructor
  · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; nlinarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sum_cj_le (x d : E) :
    |∑ j, cj eig cfg.η cfg.θ j * ⟪b j, x⟫ * ⟪b j, d⟫| ≤ 3 / 10 * (‖x‖ ^ 2 + ‖d‖ ^ 2) := by
  have hc : ∀ j, |cj eig cfg.η cfg.θ j| ≤ 3 / 5 := by
    intro j; unfold cj; split_ifs <;> norm_num
  calc |∑ j, cj eig cfg.η cfg.θ j * ⟪b j, x⟫ * ⟪b j, d⟫|
      ≤ ∑ j, |cj eig cfg.η cfg.θ j * ⟪b j, x⟫ * ⟪b j, d⟫| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, 3 / 10 * (⟪b j, x⟫ ^ 2 + ⟪b j, d⟫ ^ 2) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [abs_mul, abs_mul]
        have h1 := hc j
        have h2 : |⟪b j, x⟫| * |⟪b j, d⟫| ≤ (⟪b j, x⟫ ^ 2 + ⟪b j, d⟫ ^ 2) / 2 := by
          nlinarith [sq_nonneg (|⟪b j, x⟫| - |⟪b j, d⟫|), sq_abs ⟪b j, x⟫, sq_abs ⟪b j, d⟫]
        have h3 : 0 ≤ |⟪b j, x⟫| * |⟪b j, d⟫| := by positivity
        nlinarith [abs_nonneg (cj eig cfg.η cfg.θ j)]
    _ = 3 / 10 * (‖x‖ ^ 2 + ‖d‖ ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← AdaptiveSilverSplit.norm_sq_coords b x,
          ← AdaptiveSilverSplit.norm_sq_coords b d]

omit [MeasurableSpace E] [BorelSpace E] in
lemma gradModel_norm_le (h : Hyp f L ρ) (x : E) :
    ‖gradModel (fderiv ℝ (gradient f) xS) xS (gradient f xS) x‖ ≤ ‖gradient f xS‖ + L * ‖x - xS‖ := by
  unfold gradModel
  refine (norm_add_le _ _).trans ?_
  have := (fderiv ℝ (gradient f) xS).le_opNorm (x - xS)
  have h2 := h.hessNorm xS
  nlinarith [norm_nonneg (x - xS)]

omit [MeasurableSpace E] [BorelSpace E] in
lemma gmodel_abs_le (h : Hyp f L ρ) (x : E) :
    |gmodel (fderiv ℝ (gradient f) xS) xS (gradient f xS) (f xS) x| ≤
      |f xS| + ‖gradient f xS‖ * ‖x - xS‖ + L / 2 * ‖x - xS‖ ^ 2 := by
  unfold gmodel
  refine (abs_add_three _ _ _).trans ?_
  have h1 := abs_real_inner_le_norm (gradient f xS) (x - xS)
  have h2 := h.hessQuad xS (x - xS)
  rw [abs_div, abs_two]
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
lemma Phi_abs_le (hc : CfgHyp cfg) (h : Hyp f L ρ) (x d : E) :
    |Phi b eig (fderiv ℝ (gradient f) xS) xS (gradient f xS) (f xS) cfg.η cfg.θ x d| ≤
      (|f xS| + 11 / 10 * ‖gradient f xS‖ ^ 2) + (1 / 2 + L / 2 + 3 / 5 * L ^ 2) * ‖x - xS‖ ^ 2 +
        (3 / 10 + 1 / (2 * cfg.η)) * ‖d‖ ^ 2 := by
  unfold Phi
  refine (abs_add_three _ _ _).trans ?_
  have h1 := gmodel_abs_le f h (xS := xS) x
  have h2 := sum_cj_le cfg (b := b) (eig := eig) (gradModel (fderiv ℝ (gradient f) xS) xS (gradient f xS) x) d
  have h3 := gradModel_norm_le f h (xS := xS) x
  have h4 : ‖gradModel (fderiv ℝ (gradient f) xS) xS (gradient f xS) x‖ ^ 2 ≤
      2 * ‖gradient f xS‖ ^ 2 + 2 * L ^ 2 * ‖x - xS‖ ^ 2 := by
    have h0 : 0 ≤ ‖gradient f xS‖ + L * ‖x - xS‖ := by have := h.hL; positivity
    nlinarith [sq_nonneg (‖gradient f xS‖ - L * ‖x - xS‖), norm_nonneg
      (gradModel (fderiv ℝ (gradient f) xS) xS (gradient f xS) x), h.hL.le]
  have h5 : ‖gradient f xS‖ * ‖x - xS‖ ≤ ‖gradient f xS‖ ^ 2 / 2 + ‖x - xS‖ ^ 2 / 2 := by
    nlinarith [sq_nonneg (‖gradient f xS‖ - ‖x - xS‖)]
  have h6 : |‖d‖ ^ 2 / (2 * cfg.η)| = 1 / (2 * cfg.η) * ‖d‖ ^ 2 := by
    rw [abs_of_nonneg (by have := hc.hη; positivity)]; field_simp
  rw [h6]
  nlinarith [sq_nonneg ‖x - xS‖, sq_nonneg ‖d‖, h.hL.le]

omit [MeasurableSpace E] [BorelSpace E] in
lemma Psi_abs_le_W (hc : CfgHyp cfg) (h : Hyp f L ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ sN : State E × E, |Psi cfg f b eig xS sN.1| ≤ C * W x0 sN := by
  set c0 := |f xS| + 11 / 10 * ‖gradient f xS‖ ^ 2 with hc0
  set c1 := 1 / 2 + L / 2 + 3 / 5 * L ^ 2 with hc1
  set c2 := 3 / 10 + 1 / (2 * cfg.η) with hc2
  have hc00 : 0 ≤ c0 := by positivity
  have hc10 : 0 ≤ c1 := by have := h.hL; positivity
  have hc20 : 0 ≤ c2 := by have := hc.hη; positivity
  refine ⟨c0 + 2 * c1 * ‖xS - x0‖ ^ 2 + 2 * c1 + 2 * c2 + 9 / 50 * cfg.η, by have := hc.hη; positivity,
    fun sN => ?_⟩
  obtain ⟨s, N⟩ := sN
  unfold Psi
  refine (abs_add_le _ _).trans ?_
  have h1 : |Phi b eig (fderiv ℝ (gradient f) xS) xS (gradient f xS) (f xS) cfg.η cfg.θ s.x (s.x - s.xPrev)| ≤
      c0 + c1 * ‖s.x - xS‖ ^ 2 + c2 * ‖s.x - s.xPrev‖ ^ 2 :=
    Phi_abs_le cfg f hc h (b := b) (eig := eig) (xS := xS) s.x (s.x - s.xPrev)
  have h2 : ‖s.x - xS‖ ^ 2 ≤ 2 * ‖s.x - x0‖ ^ 2 + 2 * ‖xS - x0‖ ^ 2 := by
    have e : s.x - xS = (s.x - x0) - (xS - x0) := by abel
    rw [e]; exact norm_sub_sq_le_two _ _
  have h3 : ‖s.x - s.xPrev‖ ^ 2 ≤ 2 * ‖s.x - x0‖ ^ 2 + 2 * ‖s.xPrev - x0‖ ^ 2 := by
    have e : s.x - s.xPrev = (s.x - x0) - (s.xPrev - x0) := by abel
    rw [e]; exact norm_sub_sq_le_two _ _
  have hη0 := hc.hη
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 9 / 50 * cfg.η * ‖s.glast‖ ^ 2)]
  have hW := W_pos x0 (s, N)
  have hWa : ‖s.x - x0‖ ^ 2 ≤ W x0 (s, N) := by
    unfold W; simp only
    linarith [sq_nonneg ‖s.xPrev - x0‖, sq_nonneg ‖s.xStart - x0‖, sq_nonneg ‖s.glast‖,
      sq_nonneg ‖s.ybar‖, sq_nonneg ‖N‖]
  have hWab : ‖s.x - x0‖ ^ 2 + ‖s.xPrev - x0‖ ^ 2 ≤ W x0 (s, N) := by
    unfold W; simp only
    linarith [sq_nonneg ‖s.xStart - x0‖, sq_nonneg ‖s.glast‖, sq_nonneg ‖s.ybar‖, sq_nonneg ‖N‖]
  have hWd : ‖s.glast‖ ^ 2 ≤ W x0 (s, N) := by
    unfold W; simp only
    linarith [sq_nonneg ‖s.x - x0‖, sq_nonneg ‖s.xPrev - x0‖, sq_nonneg ‖s.xStart - x0‖,
      sq_nonneg ‖s.ybar‖, sq_nonneg ‖N‖]
  have t1 : c0 ≤ c0 * W x0 (s, N) := le_mul_of_one_le_right hc00 hW
  have t2 : 2 * c1 * ‖xS - x0‖ ^ 2 ≤ 2 * c1 * ‖xS - x0‖ ^ 2 * W x0 (s, N) :=
    le_mul_of_one_le_right (mul_nonneg (mul_nonneg (by norm_num) hc10) (sq_nonneg _)) hW
  have t3 : 2 * c1 * ‖s.x - x0‖ ^ 2 ≤ 2 * c1 * W x0 (s, N) :=
    mul_le_mul_of_nonneg_left hWa (mul_nonneg (by norm_num) hc10)
  have t4 : 2 * c2 * (‖s.x - x0‖ ^ 2 + ‖s.xPrev - x0‖ ^ 2) ≤ 2 * c2 * W x0 (s, N) :=
    mul_le_mul_of_nonneg_left hWab (mul_nonneg (by norm_num) hc20)
  have t5 : 9 / 50 * cfg.η * ‖s.glast‖ ^ 2 ≤ 9 / 50 * cfg.η * W x0 (s, N) :=
    mul_le_mul_of_nonneg_left hWd (by positivity)
  have u1 := mul_le_mul_of_nonneg_left h2 hc10
  have u2 := mul_le_mul_of_nonneg_left h3 hc20
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
lemma f_sub_abs_le (h : Hyp f L ρ) (z : E) :
    |f z - f x0| ≤ ‖gradient f x0‖ * ‖z - x0‖ + 3 / 2 * L * ‖z - x0‖ ^ 2 := by
  have h1 := OracleTemplate.Gradient.smooth_upper_bound h.hasGrad h.lip x0 z
  have h2 := OracleTemplate.Gradient.smooth_upper_bound h.hasGrad h.lip z x0
  have h3 := abs_real_inner_le_norm (gradient f x0) (z - x0)
  have h4 := abs_real_inner_le_norm (gradient f z) (x0 - z)
  have h5 : ‖gradient f z‖ ≤ ‖gradient f x0‖ + L * ‖z - x0‖ := by
    have := h.lip z x0
    have h6 := norm_sub_norm_le (gradient f z) (gradient f x0)
    linarith
  rw [norm_sub_rev x0 z] at h2 h4
  rw [abs_le] at h3 h4 ⊢
  have hn := norm_nonneg (z - x0)
  constructor
  · nlinarith [h.hL.le]
  · nlinarith [h.hL.le]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma Phi_continuous (H : E →L[ℝ] E) (g0 : E) (f0 η θ : ℝ) :
    Continuous (fun q : E × E => Phi b eig H xS g0 f0 η θ q.1 q.2) := by
  unfold Phi gmodel gradModel
  fun_prop

lemma Psi_measurable : Measurable (fun s : State E => Psi cfg f b eig xS s) := by
  unfold Psi
  have h1 := (Phi_continuous (b := b) (eig := eig) (xS := xS) (fderiv ℝ (gradient f) xS) (gradient f xS)
    (f xS) cfg.η cfg.θ).measurable
  exact (h1.comp (measurable_x.prodMk (measurable_x.sub measurable_xPrev))).add
    ((measurable_glast.norm.pow_const 2).const_mul _)

end potential

section blocks

variable {ι : Type*} [Fintype ι] {b : OrthonormalBasis ι ℝ E} {eig : ι → ℝ} {xS : E}
variable (hb : 0 < cfg.b) (h : Hyp f L ρ) (ho : OracleHyp g (gradient f) p κ) (hκ : 1 ≤ κ)
  (hc : CfgHyp cfg) (hη : cfg.η = 1 / (8 * L)) (hθ8 : cfg.θ ≤ 1 / 8)
  (hH : ∀ j v, ⟪b j, fderiv ℝ (gradient f) xS v⟫ = eig j * ⟪b j, v⟫)
  (hδ : (κ - 1) / cfg.b ≤ 1 / 800)
include hb h ho hκ hc hη hH hδ

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] [IsProbabilityMeasure p] hb ho hκ hc hη hH hδ in
lemma gradf_le_gM_add (y : E) (hy : ‖y - xS‖ ≤ 2 * cfg.B) :
    ‖gradient f y‖ ≤ ‖gradModel (fderiv ℝ (gradient f) xS) xS (gradient f xS) y‖ + Dm cfg ρ ∧
    ‖gradient f y - gradModel (fderiv ℝ (gradient f) xS) xS (gradient f xS) y‖ ≤ Dm cfg ρ := by
  have hδv : ‖gradient f y - gradModel (fderiv ℝ (gradient f) xS) xS (gradient f xS) y‖ ≤ Dm cfg ρ := by
    refine (h.gradModel_err xS y).trans ?_
    unfold Dm
    have hsq : ‖y - xS‖ ^ 2 ≤ (2 * cfg.B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
    have := mul_le_mul_of_nonneg_left hsq h.hρ
    nlinarith [this]
  refine ⟨?_, hδv⟩
  have := norm_sub_norm_le (gradient f y) (gradModel (fderiv ℝ (gradient f) xS) xS (gradient f xS) y)
  linarith

include hθ8 in
theorem agd_block {s : State E} {N : E} (hd : s.done = false) (hk : cfg.pos s.t < cfg.K)
    (htr : s.trig = false) (hxS : s.xStart = xS) (hA : InvAgd cfg f ρ (s, N)) :
    ∫ ω, (Psi cfg f b eig xS (blockStep cfg x0 g s ω) +
        (cfg.θ / cfg.η / 16 * ‖(blockStep cfg x0 g s ω).x - s.x‖ ^ 2 +
          cfg.η / 32 * ‖gradModel (fderiv ℝ (gradient f) xS) xS (gradient f xS) (ypoint cfg s)‖ ^ 2))
        ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      Psi cfg f b eig xS s + (58 / 25 * (cfg.η / cfg.θ) + 8 * cfg.η) * Dm cfg ρ ^ 2 := by
  set y := ypoint cfg s with hy
  set gM := gradModel (fderiv ℝ (gradient f) xS) xS (gradient f xS) y with hgM
  have hyS : ‖y - xS‖ ≤ 2 * cfg.B := by have := hA.y_le hc; simp only at this; rwa [hxS] at this
  obtain ⟨hgf, hδv⟩ := gradf_le_gM_add cfg f h y hyS
  set δv := gradient f y - gM with hδvdef
  have hDm : 0 ≤ Dm cfg ρ := by unfold Dm; have := h.hρ; positivity
  have hδv2 : ‖δv‖ ^ 2 ≤ Dm cfg ρ ^ 2 := by nlinarith [norm_nonneg δv]
  have heig := heig_of cfg f h hη hH
  have hηpos := hc.hη
  have hθpos := hc.hθ0
  set M := Mvec b eig xS (gradient f xS) cfg.η cfg.θ s.x (s.x - s.xPrev) with hM
  set cδ := 58 / 25 * (cfg.η / cfg.θ) + 791 / 100 * cfg.η with hcδ
  have hcδ0 : 0 ≤ cδ := by positivity
  have hpt : ∀ ω, Psi cfg f b eig xS (blockStep cfg x0 g s ω) +
      (cfg.θ / cfg.η / 16 * ‖(blockStep cfg x0 g s ω).x - s.x‖ ^ 2 + cfg.η / 32 * ‖gM‖ ^ 2) ≤
      (Psi cfg f b eig xS s - 7 / 800 * cfg.η * ‖gM‖ ^ 2 + cδ * Dm cfg ρ ^ 2) +
        (-⟪M, bmean cfg g y ω - gradient f y⟫ + 279 / 100 * cfg.η * ‖bmean cfg g y ω - gradient f y‖ ^ 2) := by
    intro ω
    rw [blockStep_agd cfg x0 g hd hk htr]
    unfold Psi
    simp only
    rw [← hy]
    set gh := bmean cfg g y ω with hgh
    set e := gh - gradient f y with he
    have key := Phi_step xS (gradient f xS) (f xS) cfg.η cfg.θ hηpos hθpos hθ8 hH heig s.x (s.x - s.xPrev)
      δv e
    simp only at key
    have hy' : s.x + (1 - cfg.θ) • (s.x - s.xPrev) = y := rfl
    rw [hy'] at key
    have hsum : gM + δv + e = gh := by rw [hδvdef, he]; abel
    rw [hsum] at key
    have hgl : 0 ≤ 9 / 50 * cfg.η * ‖s.glast‖ ^ 2 := by positivity
    have hcd := mul_le_mul_of_nonneg_left hδv2 hcδ0
    rw [← hgM, ← hM, ← hcδ] at key
    linarith
  obtain ⟨C, hC0, hCW⟩ := Psi_abs_le_W cfg x0 f hc h (b := b) (eig := eig) (xS := xS)
  have hq : queryPoint cfg s = y := by simp [queryPoint, hk, htr, hy]
  have hLHS : Integrable (fun ω => Psi cfg f b eig xS (blockStep cfg x0 g s ω) +
      (cfg.θ / cfg.η / 16 * ‖(blockStep cfg x0 g s ω).x - s.x‖ ^ 2 + cfg.η / 32 * ‖gM‖ ^ 2))
      (Measure.pi fun _ : Fin cfg.b => p) := by
    have hmeas : Measurable (fun ω => Psi cfg f b eig xS (blockStep cfg x0 g s ω) +
        (cfg.θ / cfg.η / 16 * ‖(blockStep cfg x0 g s ω).x - s.x‖ ^ 2 + cfg.η / 32 * ‖gM‖ ^ 2)) := by
      have hbs : Measurable (fun ω => blockStep cfg x0 g s ω) :=
        (measurable_blockStep cfg x0 ho.meas).comp (measurable_const.prodMk measurable_id)
      exact ((Psi_measurable cfg f).comp hbs).add
        ((((measurable_x.comp hbs).sub measurable_const).norm.pow_const 2).const_mul _ |>.add
          measurable_const)
    have hbd : ∀ ω, |Psi cfg f b eig xS (blockStep cfg x0 g s ω) +
        (cfg.θ / cfg.η / 16 * ‖(blockStep cfg x0 g s ω).x - s.x‖ ^ 2 + cfg.η / 32 * ‖gM‖ ^ 2)| ≤
        ((C + cfg.θ / cfg.η / 8) * (40 * W x0 (s, (0 : E)) + 4 * ‖x0‖ ^ 2 + 4 * ‖gradient f y‖ ^ 2) +
          cfg.θ / cfg.η / 8 * W x0 (s, (0 : E)) + cfg.η / 32 * ‖gM‖ ^ 2) +
        ((C + cfg.θ / cfg.η / 8) * (2 * cfg.η ^ 2 + 4 * cfg.ηf ^ 2 + 5)) * ‖bmean cfg g y ω‖ ^ 2 := by
      intro ω
      have hW' := W_astep_le cfg x0 g f hc (s, (0 : E)) ω
      dsimp only at hW'
      rw [hq, ← hy] at hW'
      have hW'0 : W x0 (blockStep cfg x0 g s ω, (0 : E)) ≤ W x0 (astep cfg x0 g f (s, 0) ω) := by
        unfold astep W; simp only; nlinarith [sq_nonneg ‖nextN cfg g f (s, (0 : E)) ω‖, norm_zero (E := E)]
      have hPsi := hCW (blockStep cfg x0 g s ω, (0 : E))
      simp only at hPsi
      have hdd : ‖(blockStep cfg x0 g s ω).x - s.x‖ ^ 2 ≤
          2 * W x0 (blockStep cfg x0 g s ω, (0 : E)) + 2 * W x0 (s, (0 : E)) := by
        have e : (blockStep cfg x0 g s ω).x - s.x = ((blockStep cfg x0 g s ω).x - x0) - (s.x - x0) := by abel
        rw [e]
        have := norm_sub_sq_le_two ((blockStep cfg x0 g s ω).x - x0) (s.x - x0)
        unfold W; simp only
        nlinarith [sq_nonneg ‖(blockStep cfg x0 g s ω).xPrev - x0‖, sq_nonneg ‖(blockStep cfg x0 g s ω).xStart - x0‖,
          sq_nonneg ‖(blockStep cfg x0 g s ω).glast‖, sq_nonneg ‖(blockStep cfg x0 g s ω).ybar‖,
          sq_nonneg ‖s.xPrev - x0‖, sq_nonneg ‖s.xStart - x0‖, sq_nonneg ‖s.glast‖, sq_nonneg ‖s.ybar‖]
      have hθη : 0 ≤ cfg.θ / cfg.η / 16 := div_nonneg (div_nonneg hθpos.le hηpos.le) (by norm_num)
      have hθη8 : 0 ≤ cfg.θ / cfg.η / 8 := div_nonneg (div_nonneg hθpos.le hηpos.le) (by norm_num)
      have hC' : 0 ≤ C + cfg.θ / cfg.η / 8 := add_nonneg hC0 hθη8
      have hWs := W_nonneg x0 (s, (0 : E))
      have hWs' := W_nonneg x0 (blockStep cfg x0 g s ω, (0 : E))
      have hgG : 0 ≤ cfg.η / 32 * ‖gM‖ ^ 2 := by positivity
      have hWbs := hW'0.trans hW'
      have k1 := mul_le_mul_of_nonneg_left hWbs hC'
      have k2 := mul_le_mul_of_nonneg_left hdd hθη
      have k3 := mul_nonneg hθη8 hWs'
      have k4 := mul_nonneg hθη8 hWs
      have hP := abs_le.mp hPsi
      have hD0 : 0 ≤ cfg.θ / cfg.η / 16 * ‖(blockStep cfg x0 g s ω).x - s.x‖ ^ 2 :=
        mul_nonneg hθη (sq_nonneg _)
      rw [abs_le]
      constructor
      · linarith
      · linarith
    exact integrable_of_quad_bound cfg g f hb ho _ hmeas y _ _ hbd
  have hint_e : Integrable (fun ω => bmean cfg g y ω - gradient f y) (Measure.pi fun _ : Fin cfg.b => p) :=
    (bmean_integrable cfg hb ho y).sub (integrable_const _)
  have hint_e2 := bmean_err_integrable cfg hb ho y
  have hint_M : Integrable (fun ω => ⟪M, bmean cfg g y ω - gradient f y⟫) (Measure.pi fun _ : Fin cfg.b => p) :=
    hint_e.const_inner M
  have hM' : Integrable (fun ω => -⟪M, bmean cfg g y ω - gradient f y⟫) (Measure.pi fun _ : Fin cfg.b => p) :=
    hint_M.neg
  have hE' : Integrable (fun ω => 279 / 100 * cfg.η * ‖bmean cfg g y ω - gradient f y‖ ^ 2)
      (Measure.pi fun _ : Fin cfg.b => p) := hint_e2.const_mul _
  have hR1 : Integrable (fun _ : Fin cfg.b → Ω => Psi cfg f b eig xS s - 7 / 800 * cfg.η * ‖gM‖ ^ 2 +
      cδ * Dm cfg ρ ^ 2) (Measure.pi fun _ : Fin cfg.b => p) := integrable_const _
  have hR2 : Integrable (fun ω => -⟪M, bmean cfg g y ω - gradient f y⟫ +
      279 / 100 * cfg.η * ‖bmean cfg g y ω - gradient f y‖ ^ 2) (Measure.pi fun _ : Fin cfg.b => p) :=
    hM'.add hE'
  have hRHS : Integrable (fun ω => (Psi cfg f b eig xS s - 7 / 800 * cfg.η * ‖gM‖ ^ 2 + cδ * Dm cfg ρ ^ 2) +
      (-⟪M, bmean cfg g y ω - gradient f y⟫ + 279 / 100 * cfg.η * ‖bmean cfg g y ω - gradient f y‖ ^ 2))
      (Measure.pi fun _ : Fin cfg.b => p) := hR1.add hR2
  have h1 := integral_mono hLHS hRHS hpt
  rw [integral_add hR1 hR2, integral_const, integral_add hM' hE', integral_neg, integral_const_mul,
    integral_inner_bmean_err cfg hb ho y M] at h1
  simp only [probReal_univ, one_smul, neg_zero, zero_add] at h1
  have h2 := integral_bmean_err cfg hb ho y
  have h3 : ‖gradient f y‖ ^ 2 ≤ 2 * ‖gM‖ ^ 2 + 2 * Dm cfg ρ ^ 2 := by
    nlinarith [norm_nonneg (gradient f y), norm_nonneg gM, sq_nonneg (‖gM‖ - Dm cfg ρ)]
  have hδ0 : 0 ≤ (κ - 1) / cfg.b := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have h4 : ∫ ω, ‖bmean cfg g y ω - gradient f y‖ ^ 2 ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      (κ - 1) / cfg.b * (2 * ‖gM‖ ^ 2 + 2 * Dm cfg ρ ^ 2) :=
    h2.trans (mul_le_mul_of_nonneg_left h3 hδ0)
  have hgM2 := sq_nonneg ‖gM‖
  have hDm2 := sq_nonneg (Dm cfg ρ)
  refine h1.trans ?_
  rw [hcδ]
  nlinarith [mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 279 / 100 * cfg.η),
    mul_nonneg hηpos.le hgM2, mul_nonneg hηpos.le hDm2,
    mul_le_mul_of_nonneg_left hδ (mul_nonneg hηpos.le hgM2),
    mul_le_mul_of_nonneg_left hδ (mul_nonneg hηpos.le hDm2)]

theorem gd_block {s : State E} (hd : s.done = false) (hk : cfg.pos s.t = cfg.K) (_hxS : s.xStart = xS)
    (hηf : cfg.ηf = 1 / L) (hlast : ‖s.x + cfg.η • s.glast - xS‖ ≤ 2 * cfg.B) :
    ∫ ω, f (blockStep cfg x0 g s ω).x ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      Psi cfg f b eig xS s + 8 * ρ * cfg.B ^ 3 + 18 * cfg.η * Dm cfg ρ ^ 2 := by
  have hL := h.hL
  have hηpos := hc.hη
  have hLη : L * cfg.η = 1 / 8 := by rw [hη]; field_simp
  set y := s.x + cfg.η • s.glast with hy
  have hxy : s.x = y - cfg.η • s.glast := by rw [hy]; abel
  obtain ⟨hgf, hδv⟩ := gradf_le_gM_add cfg f h y hlast
  set gM := gradModel (fderiv ℝ (gradient f) xS) xS (gradient f xS) y with hgM
  have hDm : 0 ≤ Dm cfg ρ := by unfold Dm; have := h.hρ; positivity
  have hδv2 : ‖gradient f y - gM‖ ^ 2 ≤ Dm cfg ρ ^ 2 := by nlinarith [norm_nonneg (gradient f y - gM)]
  have hend := epoch_end_f_bound h b eig xS hη hc.hθ0 hc.hB.le hH y s.glast (s.x - s.xPrev) hlast
  simp only at hend
  rw [← hxy] at hend
  have hbs : ∀ ω, (blockStep cfg x0 g s ω).x = s.x - cfg.ηf • bmean cfg g s.x ω := by
    intro ω; rw [blockStep_gd cfg x0 g hd hk]
  simp_rw [hbs]
  set e : (Fin cfg.b → Ω) → E := fun ω => bmean cfg g s.x ω - gradient f s.x with he
  have hpt : ∀ ω, f (s.x - cfg.ηf • bmean cfg g s.x ω) ≤
      (f s.x - 1 / L * ‖gradient f s.x‖ ^ 2 + 1 / (2 * L) * ‖gradient f s.x‖ ^ 2) +
        1 / (2 * L) * ‖e ω‖ ^ 2 := by
    intro ω
    have hsm := OracleTemplate.Gradient.smooth_upper_bound h.hasGrad h.lip s.x
      (s.x - cfg.ηf • bmean cfg g s.x ω)
    have hdiff : s.x - cfg.ηf • bmean cfg g s.x ω - s.x = -(cfg.ηf • bmean cfg g s.x ω) := by abel
    rw [hdiff, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs, hηf,
      abs_of_pos (by positivity)] at hsm
    have hgh : bmean cfg g s.x ω = gradient f s.x + e ω := by simp [he]
    rw [hgh, inner_add_right, real_inner_self_eq_norm_sq] at hsm
    have hsq : ‖gradient f s.x + e ω‖ ^ 2 = ‖gradient f s.x‖ ^ 2 + 2 * ⟪gradient f s.x, e ω⟫ + ‖e ω‖ ^ 2 :=
      norm_add_sq_real _ _
    rw [mul_pow, hsq] at hsm
    have e1 : L / 2 * ((1 / L) ^ 2 * (‖gradient f s.x‖ ^ 2 + 2 * ⟪gradient f s.x, e ω⟫ + ‖e ω‖ ^ 2)) =
        1 / (2 * L) * ‖gradient f s.x‖ ^ 2 + 1 / L * ⟪gradient f s.x, e ω⟫ + 1 / (2 * L) * ‖e ω‖ ^ 2 := by
      field_simp
    rw [hηf, hgh]
    linarith
  have hint_e2 : Integrable (fun ω => ‖e ω‖ ^ 2) (Measure.pi fun _ : Fin cfg.b => p) :=
    bmean_err_integrable cfg hb ho s.x
  have hR1 : Integrable (fun _ : Fin cfg.b → Ω => f s.x - 1 / L * ‖gradient f s.x‖ ^ 2 +
      1 / (2 * L) * ‖gradient f s.x‖ ^ 2) (Measure.pi fun _ : Fin cfg.b => p) := integrable_const _
  have hR2 : Integrable (fun ω => 1 / (2 * L) * ‖e ω‖ ^ 2) (Measure.pi fun _ : Fin cfg.b => p) :=
    hint_e2.const_mul _
  have hRHS : Integrable (fun ω => (f s.x - 1 / L * ‖gradient f s.x‖ ^ 2 + 1 / (2 * L) * ‖gradient f s.x‖ ^ 2) +
      1 / (2 * L) * ‖e ω‖ ^ 2) (Measure.pi fun _ : Fin cfg.b => p) := hR1.add hR2
  have hLHS : Integrable (fun ω => f (s.x - cfg.ηf • bmean cfg g s.x ω)) (Measure.pi fun _ : Fin cfg.b => p) := by
    have hmeas : Measurable (fun ω => f (s.x - cfg.ηf • bmean cfg g s.x ω)) :=
      h.hf.continuous.measurable.comp
        (measurable_const.sub ((bmean_measurable cfg ho.meas s.x).const_smul _))
    refine integrable_of_quad_bound cfg g f hb ho _ hmeas s.x
      (|f x0| + ‖gradient f x0‖ ^ 2 / 2 + (1 / 2 + 3 / 2 * L) * (2 * ‖s.x - x0‖ ^ 2))
      ((1 / 2 + 3 / 2 * L) * (2 * cfg.ηf ^ 2)) (fun ω => ?_)
    have h1 := f_sub_abs_le x0 f h (s.x - cfg.ηf • bmean cfg g s.x ω)
    have hz : ‖s.x - cfg.ηf • bmean cfg g s.x ω - x0‖ ^ 2 ≤
        2 * ‖s.x - x0‖ ^ 2 + 2 * cfg.ηf ^ 2 * ‖bmean cfg g s.x ω‖ ^ 2 := by
      have e2 : s.x - cfg.ηf • bmean cfg g s.x ω - x0 = (s.x - x0) - cfg.ηf • bmean cfg g s.x ω := by abel
      rw [e2]
      have := norm_sub_sq_le_two (s.x - x0) (cfg.ηf • bmean cfg g s.x ω)
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at this
      linarith
    have h2 : ‖gradient f x0‖ * ‖s.x - cfg.ηf • bmean cfg g s.x ω - x0‖ ≤
        ‖gradient f x0‖ ^ 2 / 2 + ‖s.x - cfg.ηf • bmean cfg g s.x ω - x0‖ ^ 2 / 2 := by
      nlinarith [sq_nonneg (‖gradient f x0‖ - ‖s.x - cfg.ηf • bmean cfg g s.x ω - x0‖)]
    have h3 : |f (s.x - cfg.ηf • bmean cfg g s.x ω)| ≤ |f x0| + |f (s.x - cfg.ηf • bmean cfg g s.x ω) - f x0| := by
      have := abs_add_le (f x0) (f (s.x - cfg.ηf • bmean cfg g s.x ω) - f x0)
      rwa [add_sub_cancel] at this
    have hL0 : 0 ≤ 1 / 2 + 3 / 2 * L := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hz hL0, sq_nonneg ‖s.x - x0‖, sq_nonneg cfg.ηf,
      sq_nonneg ‖bmean cfg g s.x ω‖]
  have h1 := integral_mono hLHS hRHS hpt
  rw [integral_add hR1 hR2, integral_const, integral_const_mul] at h1
  simp only [probReal_univ, one_smul] at h1
  have h2 := integral_bmean_err cfg hb ho s.x
  have hgx : ‖gradient f y‖ ≤ ‖gradient f s.x‖ + ‖s.glast‖ / 8 := by
    have := h.lip y s.x
    have h5 : y - s.x = cfg.η • s.glast := by rw [hy]; abel
    rw [h5, norm_smul, Real.norm_eq_abs, abs_of_pos hηpos] at this
    have h6 := norm_sub_norm_le (gradient f y) (gradient f s.x)
    have h7 : L * (cfg.η * ‖s.glast‖) = 1 / 8 * ‖s.glast‖ := by rw [← mul_assoc, hLη]
    linarith
  have hgx2 : ‖gradient f y‖ ^ 2 / 4 - ‖s.glast‖ ^ 2 / 192 ≤ ‖gradient f s.x‖ ^ 2 :=
    sq_quarter_le _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hgx
  have hgM2 : ‖gM‖ ^ 2 ≤ 5 / 4 * ‖gradient f y‖ ^ 2 + 5 * Dm cfg ρ ^ 2 := by
    have := norm_sub_norm_le gM (gradient f y)
    rw [norm_sub_rev] at this
    exact sq_le_five_quarter _ _ _ (norm_nonneg _) (norm_nonneg _) hDm (by linarith)
  have hδ0 : 0 ≤ (κ - 1) / cfg.b := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have h4 : 1 / (2 * L) = 4 * cfg.η := by rw [hη]; field_simp; ring
  have h5 : 1 / L = 8 * cfg.η := by rw [hη]; field_simp
  rw [h4, h5] at h1
  rw [← hgM] at hend
  unfold Psi
  have hgs2 := sq_nonneg ‖gradient f s.x‖
  have hi2 : ∫ ω, ‖e ω‖ ^ 2 ∂(Measure.pi fun _ : Fin cfg.b => p) ≤ 1 / 800 * ‖gradient f s.x‖ ^ 2 :=
    h2.trans (mul_le_mul_of_nonneg_right hδ hgs2)
  have m1 := mul_le_mul_of_nonneg_left hi2 (by positivity : (0:ℝ) ≤ 4 * cfg.η)
  have m2 := mul_le_mul_of_nonneg_left hgx2 (by positivity : (0:ℝ) ≤ 799 / 200 * cfg.η)
  have m3 := mul_le_mul_of_nonneg_left hgM2 (by positivity : (0:ℝ) ≤ 9 / 25 * cfg.η)
  have m4 := mul_le_mul_of_nonneg_left hδv2 (by positivity : (0:ℝ) ≤ 16 * cfg.η)
  have n1 := mul_nonneg hηpos.le (sq_nonneg ‖gradient f y‖)
  have n2 := mul_nonneg hηpos.le (sq_nonneg ‖s.glast‖)
  have n3 := mul_nonneg hηpos.le (sq_nonneg (Dm cfg ρ))
  linarith

end blocks

end LongTails.Proofs.StrongGrowthAgdEpoch
