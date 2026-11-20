import LongTails.Proofs.HighProbabilityAdapted
import LongTails.Proofs.WeakGradientConvolution

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.HighProbabilityRounds

open LongTails.Proofs.HighProbabilityAdapted

section Fraction

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma fraction_failure {k : ℕ} {A : Fin k → Set Ω} [∀ i, DecidablePred (· ∈ A i)]
    (hA : ∀ i, MeasurableSet (A i)) {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hp : ∀ i, P.real (A i) ≤ θ) (a : ℕ) :
    (Measure.pi fun _ : Fin k => P) {ξ | a ≤ (Finset.univ.filter (fun i => ξ i ∈ A i)).card} ≤
      ENNReal.ofReal ((1 + Real.sqrt θ) ^ k * Real.sqrt θ ^ a) := by
  classical
  have hs : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθ
  set M : ℝ := 1 / Real.sqrt θ with hM
  have hM1 : 0 < M := by positivity
  let F : Fin k → Ω → ℝ := fun i ω => if ω ∈ A i then M else 1
  have hFm (i : Fin k) : Measurable (F i) := Measurable.ite (hA i) measurable_const measurable_const
  have hFnn (i : Fin k) (ω : Ω) : 0 ≤ F i ω := by
    dsimp [F]; split_ifs <;> positivity
  have hFi (i : Fin k) : Integrable (F i) P := Integrable.of_bound (hFm i).aestronglyMeasurable
    (M + 1) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn i ω)]
      dsimp [F]; split_ifs <;> linarith)
  have hFe (i : Fin k) : (∫ ω, F i ω ∂P) ≤ 1 + Real.sqrt θ := by
    have he : F i = fun ω => 1 + (M - 1) * (A i).indicator (fun _ => (1 : ℝ)) ω := by
      ext ω
      by_cases h : ω ∈ A i <;> simp [F, h]
    rw [he, integral_add (integrable_const 1)
      (((integrable_const 1).indicator (hA i)).const_mul _), integral_const_mul,
      integral_indicator_const (1 : ℝ) (hA i), integral_const, probReal_univ, one_smul,
      smul_eq_mul, mul_one]
    by_cases hM1' : M - 1 ≤ 0
    · nlinarith [measureReal_nonneg (μ := P) (s := A i), hs]
    · push Not at hM1'
      have h1 : (M - 1) * P.real (A i) ≤ (M - 1) * θ := mul_le_mul_of_nonneg_left (hp i) hM1'.le
      have h2 : (M - 1) * θ ≤ Real.sqrt θ := by
        have hsq : Real.sqrt θ * Real.sqrt θ = θ := Real.mul_self_sqrt hθ.le
        have : M * θ = Real.sqrt θ := by
          rw [hM, one_div, inv_mul_eq_div, Real.div_sqrt]
        nlinarith
      linarith
  let W : (Fin k → Ω) → ℝ := fun ξ => ∏ i, F i (ξ i)
  have hWm : Measurable W := by
    dsimp [W]
    exact Finset.measurable_prod _ fun i _ => (hFm i).comp (measurable_pi_apply i)
  have hWnonneg (ξ : Fin k → Ω) : 0 ≤ W ξ := Finset.prod_nonneg fun i _ => hFnn i (ξ i)
  have hWi : Integrable W (Measure.pi fun _ : Fin k => P) := by
    refine Integrable.of_bound hWm.aestronglyMeasurable ((M + 1) ^ k)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg ξ)]
    calc W ξ ≤ ∏ _i : Fin k, (M + 1) := Finset.prod_le_prod₀ (fun i _ => hFnn i (ξ i))
          (fun i _ => by dsimp [F]; split_ifs <;> linarith)
      _ = (M + 1) ^ k := by simp
  have hWlow (ξ : Fin k → Ω) : M ^ (Finset.univ.filter (fun i => ξ i ∈ A i)).card ≤ W ξ := by
    have hsplit : W ξ = (∏ i ∈ Finset.univ.filter (fun i => ξ i ∈ A i), F i (ξ i)) *
        ∏ i ∈ Finset.univ.filter (fun i => ¬ ξ i ∈ A i), F i (ξ i) :=
      (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
    have h1 : (∏ i ∈ Finset.univ.filter (fun i => ξ i ∈ A i), F i (ξ i)) =
        M ^ (Finset.univ.filter (fun i => ξ i ∈ A i)).card := by
      rw [Finset.prod_congr rfl (g := fun _ => M) (fun i hi => by
        simp only [Finset.mem_filter] at hi; simp [F, hi.2]), Finset.prod_const]
    have h2 : (∏ i ∈ Finset.univ.filter (fun i => ¬ ξ i ∈ A i), F i (ξ i)) = 1 := by
      exact Finset.prod_eq_one (fun i hi => by
        simp only [Finset.mem_filter] at hi; simp [F, hi.2])
    rw [hsplit, h1, h2, mul_one]
  have hmark := (hWi.div_const (M ^ a)).measure_le_integral
    (Filter.Eventually.of_forall (fun ξ => div_nonneg (hWnonneg ξ) (by positivity)))
    (s := {ξ | a ≤ (Finset.univ.filter (fun i => ξ i ∈ A i)).card}) (by
      intro ξ hξ
      apply (one_le_div (by positivity : (0 : ℝ) < M ^ a)).mpr
      have hge : 1 ≤ M := by
        rw [hM, le_div_iff₀ hs, one_mul]
        exact Real.sqrt_le_one.mpr hθ1
      exact (pow_le_pow_right₀ hge hξ).trans (hWlow ξ))
  refine hmark.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [integral_div]
  have hprod : (∫ ξ, W ξ ∂(Measure.pi fun _ : Fin k => P)) = ∏ i, ∫ ω, F i ω ∂P := by
    exact integral_fintype_prod_eq_prod (f := fun i ω => F i ω)
  rw [hprod]
  have hb : (∏ i, ∫ ω, F i ω ∂P) ≤ (1 + Real.sqrt θ) ^ k := by
    calc (∏ i, ∫ ω, F i ω ∂P) ≤ ∏ _i : Fin k, (1 + Real.sqrt θ) :=
          Finset.prod_le_prod₀ (fun i _ => integral_nonneg (hFnn i)) (fun i _ => hFe i)
      _ = (1 + Real.sqrt θ) ^ k := by simp
  have hMa : M ^ a = 1 / Real.sqrt θ ^ a := by rw [hM, div_pow, one_pow]
  rw [hMa, div_div_eq_mul_div, div_one]
  exact mul_le_mul_of_nonneg_right hb (by positivity)

end Fraction

section Chain

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z] {pw : Measure Z}
  [IsProbabilityMeasure pw]

lemma chain_health {F : X → Z → X} (hF : Measurable (Function.uncurry F)) (x0 : X)
    (H : ℕ → Set X) (hH : ∀ n, MeasurableSet (H n)) (h0 : x0 ∈ H 0) (ζ : ℕ → ℝ)
    (hζ : ∀ n, 0 ≤ ζ n)
    (hstep : ∀ n x, x ∈ H n → pw.real {z | F x z ∉ H (n + 1)} ≤ ζ n) (N : ℕ) :
    (Measure.infinitePi fun _ : ℕ => pw).real {b | traj F x0 b N ∉ H N} ≤
      ∑ n ∈ Finset.range N, ζ n := by
  have hiid := OracleTemplate.StochasticGeneralized.infinitePi_iid pw
  set P := Measure.infinitePi fun _ : ℕ => pw
  have hhist (n : ℕ) : Measurable (fun b : ℕ → Z => fun i : Fin n => b i) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have htrajm : ∀ n, Measurable (fun b : ℕ → Z => traj F x0 b n) := by
    intro n
    have h := (measurable_histPoint hF x0 n).comp (hhist n)
    simpa only [Function.comp_def, histPoint_eq] using h
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    have : {b : ℕ → Z | traj F x0 b 0 ∉ H 0} = ∅ := by
      ext b; simp [traj, h0]
    rw [this]; simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    let G : Set (ℕ → Z) := {b | traj F x0 b N ∈ H N ∧ F (traj F x0 b N) (b N) ∉ H (N + 1)}
    have hsub : {b : ℕ → Z | traj F x0 b (N + 1) ∉ H (N + 1)} ⊆
        {b | traj F x0 b N ∉ H N} ∪ G := by
      intro b hb
      by_cases hN : traj F x0 b N ∈ H N
      · right; exact ⟨hN, hb⟩
      · left; exact hN
    have hset : MeasurableSet {w : X × Z | w.1 ∈ H N ∧ F w.1 w.2 ∉ H (N + 1)} :=
      (measurable_fst (hH N)).inter (hF (hH (N + 1))).compl
    let h : X × Z → ℝ := Set.indicator {w : X × Z | w.1 ∈ H N ∧ F w.1 w.2 ∉ H (N + 1)} 1
    have hhm : Measurable h := measurable_const.indicator hset
    have hind : IndepFun (fun b : ℕ → Z => fun i : Fin N => b i) (fun b => b N) P :=
      LongTails.Proofs.AdaptiveOracleConcentration.iid_history_independent hiid.measurable
        hiid.independent N
    have hfm : Measurable (fun az : (Fin N → Z) × Z => h (histPoint F x0 N az.1, az.2)) :=
      hhm.comp (((measurable_histPoint hF x0 N).comp measurable_fst).prodMk measurable_snd)
    have hfib := LongTails.Proofs.AdaptiveOracleConcentration.independent_nonnegative_fiber_bound
      (f := fun az : (Fin N → Z) × Z => h (histPoint F x0 N az.1, az.2))
      (bound := fun _ => ζ N) (hhist N) (measurable_pi_apply N) hind (hiid.marginal N) hfm
      (fun _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      (fun a => Integrable.of_bound
        (hfm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun z => by
          simp only [h, Set.indicator]
          split_ifs <;> simp))
      (integrable_const _)
      (fun a => by
        by_cases ha : histPoint F x0 N a ∈ H N
        · have hmz : MeasurableSet {z | F (histPoint F x0 N a) z ∉ H (N + 1)} :=
            ((hF.comp (measurable_const.prodMk measurable_id)) (hH (N + 1))).compl
          have hz : (fun z => h (histPoint F x0 N a, z)) =
              fun z => Set.indicator {z | F (histPoint F x0 N a) z ∉ H (N + 1)} 1 z := by
            funext z
            by_cases hzz : F (histPoint F x0 N a) z ∈ H (N + 1) <;> simp [h, Set.indicator, ha, hzz]
          rw [hz, integral_indicator_one hmz]
          exact hstep N _ ha
        · have hz : (fun z => h (histPoint F x0 N a, z)) = fun _ => 0 := by
            funext z; simp [h, ha]
          rw [hz, integral_zero]
          exact hζ N)
    have hGmeas : MeasurableSet G :=
      ((htrajm N) (hH N)).inter
        ((hF.comp ((htrajm N).prodMk (measurable_pi_apply N))) (hH (N + 1))).compl
    have hGint : P.real G = ∫ b, h (histPoint F x0 N (fun i => b i), b N) ∂P := by
      have he : (fun b : ℕ → Z => h (histPoint F x0 N (fun i => b i), b N)) =
          fun b => G.indicator 1 b := by
        funext b
        simp only [h, G, histPoint_eq, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
      rw [he, integral_indicator_one hGmeas]
    have hGle : P.real G ≤ ζ N := by
      rw [hGint]
      refine hfib.2.trans ?_
      simp
    calc P.real {b : ℕ → Z | traj F x0 b (N + 1) ∉ H (N + 1)} ≤
          P.real ({b | traj F x0 b N ∉ H N} ∪ G) := measureReal_mono hsub
      _ ≤ P.real {b | traj F x0 b N ∉ H N} + P.real G := measureReal_union_le _ _
      _ ≤ (∑ n ∈ Finset.range N, ζ n) + ζ N := add_le_add ih hGle

end Chain

end LongTails.Proofs.HighProbabilityRounds
