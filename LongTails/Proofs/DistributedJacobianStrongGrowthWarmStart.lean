import LongTails.Proofs.LocalNonlinearExtragradientIteration
import LongTails.Proofs.DistributedJacobianStrongGrowthWarmProcess
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.DistributedJacobianStrongGrowthWarmStart

lemma independent_majority_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (B : Fin n → Ω → Bool)
    (hBm : ∀ i, Measurable (B i)) (hB : iIndepFun B P)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hp : ∀ i, P.real {ω | B i ω = true} ≤ θ) :
    P {ω | n ≤ 2 * (Finset.univ.filter (fun i => B i ω = true)).card} ≤
      ENNReal.ofReal ((2 * Real.sqrt θ) ^ n) := by
  classical
  let s : ℝ := 1 / Real.sqrt θ
  have hsq : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθ
  have hs1 : 1 ≤ s := by
    apply (one_le_div hsq).mpr
    simpa using Real.sqrt_le_sqrt hθ1
  have hs2 : s ^ 2 = 1 / θ := by
    dsimp [s]
    rw [div_pow, Real.sq_sqrt hθ.le, one_pow]
  let F : Fin n → Ω → ℝ := fun i ω => if B i ω = true then s ^ 2 else 1
  have hF1 (i : Fin n) (ω : Ω) : 1 ≤ F i ω := by
    dsimp [F]
    split_ifs <;> nlinarith
  have hFb (i : Fin n) (ω : Ω) : F i ω ≤ s ^ 2 := by
    dsimp [F]
    split_ifs <;> nlinarith
  have hm (i : Fin n) : Measurable (F i) :=
    (measurable_of_countable (fun b : Bool => if b = true then s ^ 2 else 1)).comp (hBm i)
  have hi : iIndepFun F P := hB.comp
    (fun _ (b : Bool) => if b = true then s ^ 2 else 1) (fun _ => measurable_of_countable _)
  have hFe (i : Fin n) : (∫ ω, F i ω ∂P) = 1 + (s ^ 2 - 1) * P.real {ω | B i ω = true} := by
    have he : F i = fun ω => 1 + (s ^ 2 - 1) *
        {ω | B i ω = true}.indicator (fun _ => (1 : ℝ)) ω := by
      funext ω
      by_cases h : B i ω = true <;> simp [F, h]
    have hevent : MeasurableSet {ω | B i ω = true} := (hBm i) (measurableSet_singleton true)
    rw [he, integral_add (integrable_const 1)
      (((integrable_const 1).indicator hevent).const_mul (s ^ 2 - 1)), integral_const_mul]
    change (∫ a, (1 : ℝ) ∂P) + (s ^ 2 - 1) *
      (∫ a, {ω | B i ω = true}.indicator 1 a ∂P) = _
    rw [integral_indicator_one hevent]
    simp
  have hFn (i : Fin n) : 0 ≤ ∫ ω, F i ω ∂P :=
    integral_nonneg fun ω => zero_le_one.trans (hF1 i ω)
  have hFbound (i : Fin n) : (∫ ω, F i ω ∂P) ≤ 2 := by
    rw [hFe]
    have h1 := mul_le_mul_of_nonneg_left (hp i) (by nlinarith : 0 ≤ s ^ 2 - 1)
    have h2 : (s ^ 2 - 1) * θ ≤ 1 := by
      rw [hs2, sub_mul, div_mul_cancel₀ 1 hθ.ne']
      linarith
    linarith
  let W : Ω → ℝ := fun ω => ∏ i, F i ω
  have hWm : Measurable W := Finset.measurable_prod _ (fun i _ => hm i)
  have hW0 (ω : Ω) : 0 ≤ W ω := Finset.prod_nonneg fun i _ => zero_le_one.trans (hF1 i ω)
  have hWb (ω : Ω) : W ω ≤ (s ^ 2) ^ n := by
    calc
      _ ≤ ∏ _ : Fin n, s ^ 2 := Finset.prod_le_prod₀
        (fun i _ => zero_le_one.trans (hF1 i ω)) (fun i _ => hFb i ω)
      _ = _ := by simp
  have hWi : Integrable W P := Integrable.of_bound hWm.aestronglyMeasurable ((s ^ 2) ^ n)
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_of_nonneg (hW0 ω)]; exact hWb ω)
  have hWe (ω : Ω) : W ω = (s ^ 2) ^ (Finset.univ.filter (fun i => B i ω = true)).card := by
    simp only [W, F, ← Finset.prod_filter, Finset.prod_const]
  have h := (hWi.div_const (s ^ n)).measure_le_integral
    (Filter.Eventually.of_forall fun ω => div_nonneg (hW0 ω) (by positivity))
    (s := {ω | n ≤ 2 * (Finset.univ.filter (fun i => B i ω = true)).card}) (by
      intro ω hω
      apply (one_le_div (by positivity : 0 < s ^ n)).mpr
      rw [hWe, ← pow_mul]
      exact pow_le_pow_right₀ hs1 hω)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div]
  change (∫ ω, ∏ i, F i ω ∂P) / s ^ n ≤ _
  rw [hi.integral_fun_prod_eq_prod_integral (fun i => (hm i).aestronglyMeasurable)]
  calc
    _ ≤ (∏ _ : Fin n, (2 : ℝ)) / s ^ n := div_le_div_of_nonneg_right
      (Finset.prod_le_prod₀ (fun i _ => hFn i) (fun i _ => hFbound i)) (by positivity)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← div_pow]
      congr 1
      dsimp [s]
      field_simp

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientWarmStart

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma warm_worker_bound (p : Params) (hp : valid p) (I : Problem p)
    (hI : problemAssumptions p I)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (hg : oracleAssumptions p I g S) (s : ℕ) (i : Fin p.n) :
    let X := fun ω => LongTails.Algorithms.LocalNonlinearExtragradient.warmRun
      (p.μ / (p.ρ * p.L ^ 2)) (g i) p.x0 (fun j => S.sample (p.n * j + i.val) ω) s
    Integrable (fun ω => ‖X ω - I.solution‖ ^ 2) (S.law : Measure S.Seed) ∧
      (∫ ω, ‖X ω - I.solution‖ ^ 2 ∂(S.law : Measure S.Seed)) ≤
        (1 - p.μ ^ 2 / (p.ρ * p.L ^ 2)) ^ s * p.R ^ 2 := by
  rcases hp with ⟨_, _, _, _, _, _, hμ, hμL, hρ, _, hR, _, _⟩
  rcases hI with ⟨_, hlip, _, hroot, hinit, hmono⟩
  have hL : 0 < p.L := hμ.trans_le hμL
  have hρ0 : 0 < p.ρ := by linarith
  have hiid := LocalNonlinearExtragradientSampling.interleaved_worker_iid
    (S.law : Measure S.Seed) (S.marginal : Measure p.Ω) S.sample S.iid p.n.pos 0 i
  simp only [Nat.zero_add] at hiid
  have hf (x : Point p) : ‖I.F x‖ ^ 2 ≤ p.L ^ 2 * ‖x - I.solution‖ ^ 2 := by
    have hh := hlip x I.solution
    rw [hroot, sub_zero] at hh
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL.le (norm_nonneg _))).mpr hh
    simpa only [mul_pow] using hs
  have hb := LocalNonlinearExtragradientIteration.warm_run_bound
    (S.law : Measure S.Seed) (S.marginal : Measure p.Ω) I.solution p.x0 I.F (g i)
    (fun j => S.sample (p.n * j + i.val)) hL hρ hμ.le hμL (hg.1 i) hiid
    (hg.2.1 i) (hg.2.2.1 i) (hg.2.2.2.1 i) (hg.2.2.2.2 i)
    (fun x => by simpa only [real_inner_comm] using hmono x) hf s
  have hμ2 := (sq_le_sq₀ hμ.le hL.le).mpr hμL
  have hden : p.μ ^ 2 ≤ p.ρ * p.L ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hρ (sq_nonneg p.L)]
  have hq : 0 ≤ 1 - p.μ ^ 2 / (p.ρ * p.L ^ 2) := by
    have hh := (div_le_one (by positivity : 0 < p.ρ * p.L ^ 2)).mpr hden
    linarith
  have hR2 := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hinit
  exact ⟨hb.1, hb.2.trans (mul_le_mul_of_nonneg_left hR2 (pow_nonneg hq s))⟩

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma squared_distance_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (p : Params) (X : Ω → Point p) (y : Point p)
    {a : ℝ} (ha : 0 < a) (hi : Integrable (fun ω => ‖X ω - y‖ ^ 2) P) :
    P.real {ω | a < ‖X ω - y‖} ≤ (∫ ω, ‖X ω - y‖ ^ 2 ∂P) / a ^ 2 := by
  have hb := (hi.div_const (a ^ 2)).measure_le_integral
    (Filter.Eventually.of_forall fun ω => div_nonneg (sq_nonneg _) (sq_nonneg a))
    (s := {ω | a < ‖X ω - y‖}) (by
      intro ω hω
      apply (one_le_div (sq_pos_of_pos ha)).mpr
      exact (sq_le_sq₀ ha.le (norm_nonneg _)).mpr hω.le)
  have h0 : 0 ≤ ∫ ω, ‖X ω - y‖ ^ 2 / a ^ 2 ∂P :=
    integral_nonneg fun _ => div_nonneg (sq_nonneg _) (sq_nonneg a)
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal h0, integral_div] at hh
  exact hh

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma warmCenter_failure_probability (p : Params) (hp : valid p) (I : Problem p)
    (hI : problemAssumptions p I)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (hg : oracleAssumptions p I g S) (s width : ℕ) (spacing a θ : ℝ)
    (hs : 0 < spacing) (ha : 0 < a) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hrange : p.R ≤ spacing * ((2 ^ width - 1 : ℕ) : ℝ) / 2)
    (haccuracy : (1 - p.μ ^ 2 / (p.ρ * p.L ^ 2)) ^ s * p.R ^ 2 / a ^ 2 ≤ θ) :
    (S.law : Measure S.Seed)
      {ω | Real.sqrt p.d * (a + spacing) <
        ‖warmCenter p s width spacing g (fun j => S.sample j ω) - I.solution‖} ≤
      ENNReal.ofReal ((2 * Real.sqrt θ) ^ (p.n : ℕ)) := by
  classical
  let X : Fin p.n → S.Seed → Point p := fun i ω =>
    LongTails.Algorithms.LocalNonlinearExtragradient.warmRun
      (p.μ / (p.ρ * p.L ^ 2)) (g i) p.x0 (fun j => S.sample (p.n * j + i.val) ω) s
  let flag : Point p → Bool := fun x => decide (a < ‖x - I.solution‖)
  let B : Fin p.n → S.Seed → Bool := fun i ω => flag (X i ω)
  have hXm (i : Fin p.n) : Measurable (X i) :=
    (LocalNonlinearExtragradientSampling.measurable_warmRun
      (p.μ / (p.ρ * p.L ^ 2)) (g i) p.x0 (hg.1 i) s).comp
      (Measurable.of_eval fun j => S.iid.measurable (p.n * j + i.val))
  have hflag : Measurable flag := by
    have he : flag = fun x => if a < ‖x - I.solution‖ then true else false := by
      funext x
      by_cases hh : a < ‖x - I.solution‖ <;> simp [flag, hh]
    rw [he]
    exact Measurable.ite (measurableSet_lt measurable_const ((measurable_id.sub_const I.solution).norm))
      measurable_const measurable_const
  have hXi : iIndepFun X (S.law : Measure S.Seed) := by
    simpa only [X, Nat.zero_add] using
      LocalNonlinearExtragradientSampling.interleaved_warmRuns_independent
        (S.law : Measure S.Seed) (S.marginal : Measure p.Ω) S.sample S.iid p.n.pos 0 s
        (p.μ / (p.ρ * p.L ^ 2)) g p.x0 hg.1
  have hBi : iIndepFun B (S.law : Measure S.Seed) :=
    hXi.comp (fun _ => flag) (fun _ => hflag)
  have hprob (i : Fin p.n) : (S.law : Measure S.Seed).real {ω | B i ω = true} ≤ θ := by
    have hw := warm_worker_bound p hp I hI g S hg s i
    have hb := squared_distance_probability (S.law : Measure S.Seed) p (X i) I.solution ha hw.1
    have htail := hb.trans ((div_le_div_of_nonneg_right hw.2 (sq_nonneg a)).trans haccuracy)
    simpa only [B, flag, decide_eq_true_eq] using htail
  have hmajor := independent_majority_probability (S.law : Measure S.Seed) B
    (fun i => hflag.comp (hXm i)) hBi hθ hθ1 hprob
  apply (measure_mono ?_).trans hmajor
  intro ω hfail
  by_contra hnot
  have hnat : 2 * (Finset.univ.filter (fun i => B i ω = true)).card < (p.n : ℕ) :=
    Nat.lt_of_not_ge hnot
  have hsum : (∑ i, if B i ω then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun i => B i ω = true)).card : ℝ) := by
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hbad : (∑ i, if B i ω then (1 : ℝ) else 0) < (p.n : ℝ) / 2 := by
    rw [hsum]
    have hh : 2 * ((Finset.univ.filter (fun i => B i ω = true)).card : ℝ) < (p.n : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hgood (i : Fin p.n) (hi : ¬ B i ω) : ‖X i ω - I.solution‖ ≤ a := by
    simpa only [B, flag, decide_eq_true_eq, not_lt] using hi
  have hR : 0 ≤ p.R := le_of_lt hp.2.2.2.2.2.2.2.2.2.2.1
  have hy : ‖I.solution - p.x0‖ ≤ p.R := by simpa only [norm_sub_rev] using hI.2.2.2.2.1
  exact (not_le_of_gt hfail) (DistributedJacobianStrongGrowthMedian.warmCenter_accuracy
    p s width spacing hs g (fun j => S.sample j ω) I.solution a ha.le hR hy hrange
    (fun i => B i ω) hgood hbad)

end LongTails.Proofs.DistributedJacobianStrongGrowthWarmStart
