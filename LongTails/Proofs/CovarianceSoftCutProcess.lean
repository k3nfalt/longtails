import LongTails.Proofs.CovarianceSoftCutOracle
import LongTails.Proofs.CovarianceSoftCutTrajectory
import LongTails.Proofs.CovarianceSoftCutFreshness
import LongTails.Proofs.CovarianceSoftCutLocalization

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutProcess

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut
open LongTails.Proofs.CovarianceSoftCutDensity

def sampleCuts (q : Params) (α η : ℝ) (b : ℕ) (g : Space q → q.Ω → Space q) :
    (n : ℕ) → (ℕ → q.Ω) → Fin n → Cut q
  | 0, _ => Fin.elim0
  | n + 1, ξ =>
    let cuts := sampleCuts q α η b g n ξ
    let x := centroid q α η (List.ofFn cuts)
    Fin.append cuts (fun _ : Fin 1 => ((1 / (b : ℝ)) • ∑ i : Fin b, g x (ξ (n*b+i)), x))

def samplePoint (q : Params) (α η : ℝ) (b : ℕ) (g : Space q → q.Ω → Space q)
    (n : ℕ) (ξ : ℕ → q.Ω) : Space q :=
  centroid q α η (List.ofFn (sampleCuts q α η b g n ξ))

lemma measurable_sampleCuts (q : Params) (hR : 0 < q.R) (α η : ℝ) (b : ℕ)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (sampleCuts q α η b g n) := by
  induction n with
  | zero => exact Measurable.of_eval (fun i => Fin.elim0 i)
  | succ n ih =>
    have hx : Measurable (fun ξ => centroid q α η (List.ofFn (sampleCuts q α η b g n ξ))) :=
      (continuous_centroid_ofFn q hR α η n).measurable.comp ih
    have hgi (i : Fin b) : Measurable (fun ξ =>
        g (centroid q α η (List.ofFn (sampleCuts q α η b g n ξ))) (ξ (n*b+i))) :=
      hg.comp (hx.prodMk (measurable_pi_apply _))
    have hm : Measurable (fun ξ => (1 / (b : ℝ)) • ∑ i : Fin b,
        g (centroid q α η (List.ofFn (sampleCuts q α η b g n ξ))) (ξ (n*b+i))) := by
      fun_prop
    apply Measurable.of_eval
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [sampleCuts, Fin.append_left, Function.comp_def] using (measurable_pi_apply j).comp ih
    · simpa only [sampleCuts, Fin.append_right] using hm.prodMk hx

lemma measurable_samplePoint (q : Params) (hR : 0 < q.R) (α η : ℝ) (b : ℕ)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (samplePoint q α η b g n) :=
  (continuous_centroid_ofFn q hR α η n).measurable.comp
    (measurable_sampleCuts q hR α η b g hg n)

lemma sampleCuts_eq_of_prefix (q : Params) (α η : ℝ) (b n : ℕ)
    (g : Space q → q.Ω → Space q) (ξ ζ : ℕ → q.Ω)
    (h : ∀ i, i < n*b → ξ i = ζ i) :
    sampleCuts q α η b g n ξ = sampleCuts q α η b g n ζ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := ih (fun i hi => h i (lt_of_lt_of_le hi (Nat.mul_le_mul_right b (Nat.le_succ n))))
    have hb (i : Fin b) : ξ (n*b+i) = ζ (n*b+i) := by
      apply h
      have hi := i.isLt
      rw [Nat.add_mul, one_mul]
      omega
    simp only [sampleCuts, hp, hb]

def sampleReplies (q : Params) (α η : ℝ) (b : ℕ) (g : Space q → q.Ω → Space q)
    (ξ : ℕ → q.Ω) (i : ℕ) : Space q :=
  g (samplePoint q α η b g (i / b) ξ) (ξ i)

lemma sampleCuts_eq_generatorCuts (q : Params) (α η : ℝ) (b : ℕ) (hb : 0 < b)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (n : ℕ) :
    sampleCuts q α η b g n ξ = generatorCuts q α η b n (sampleReplies q α η b g ξ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hdiv (i : Fin b) : (n*b+i.val)/b = n := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
    have hm : batchMean q b n (sampleReplies q α η b g ξ) =
        (1 / (b : ℝ)) • ∑ i : Fin b, g (samplePoint q α η b g n ξ) (ξ (n*b+i)) := by
      simp only [batchMean, sampleReplies, hdiv, one_div]
    simp only [sampleCuts, generatorCuts, hm]
    unfold samplePoint
    rw [ih]

lemma samplePoint_eq_generatorPoint (q : Params) (α η : ℝ) (b : ℕ) (hb : 0 < b)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (n : ℕ) :
    samplePoint q α η b g n ξ = generatorPoint q α η b n (sampleReplies q α η b g ξ) := by
  unfold samplePoint generatorPoint
  rw [sampleCuts_eq_generatorCuts q α η b hb g ξ n]

abbrev History (q : Params) := ℕ × (ℕ → Cut q)

def historyPoint (q : Params) (α η : ℝ) (s : History q) : Space q :=
  centroid q α η (List.ofFn (fun i : Fin s.1 => s.2 i))

def historyNext (q : Params) (α η : ℝ) (g : Space q → q.Ω → Space q)
    (b : ℕ) (s : History q) (ζ : Fin b → q.Ω) : History q :=
  (s.1 + 1, Function.update s.2 s.1
    ((1 / (b : ℝ)) • ∑ i, g (historyPoint q α η s) (ζ i), historyPoint q α η s))

lemma measurable_historyPoint (q : Params) (hR : 0 < q.R) (α η : ℝ) :
    Measurable (historyPoint q α η) := by
  apply measurable_from_prod_countable_right
  intro n
  exact (continuous_centroid_ofFn q hR α η n).measurable.comp
    (Measurable.of_eval (fun i : Fin n => measurable_pi_apply i.val))

lemma measurable_historyNext (q : Params) (hR : 0 < q.R) (α η : ℝ)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) (b : ℕ) :
    Measurable (Function.uncurry (historyNext q α η g b)) := by
  have hx := (measurable_historyPoint q hR α η).comp
    (measurable_fst : Measurable (Prod.fst : History q × (Fin b → q.Ω) → History q))
  have hgi (i : Fin b) : Measurable (fun z : History q × (Fin b → q.Ω) =>
      g (historyPoint q α η z.1) (z.2 i)) := hg.comp (hx.prodMk (by fun_prop))
  have hm : Measurable (fun z : History q × (Fin b → q.Ω) =>
      (1 / (b : ℝ)) • ∑ i, g (historyPoint q α η z.1) (z.2 i)) := by fun_prop
  apply Measurable.prodMk (by fun_prop)
  apply Measurable.of_eval
  intro i
  change Measurable (fun z : History q × (Fin b → q.Ω) =>
    Function.update z.1.2 z.1.1
      ((1 / (b : ℝ)) • ∑ j, g (historyPoint q α η z.1) (z.2 j), historyPoint q α η z.1) i)
  simp only [Function.update_apply]
  exact Measurable.ite (by measurability) (hm.prodMk hx) (by fun_prop)

def historyPenalty (q : Params) (α η : ℝ) (g : Space q → q.Ω → Space q)
    (f : Space q → ℝ) (value : ℝ) (μ : Measure (Space q))
    (b : ℕ) (s : History q) (ζ : Fin b → q.Ω) : ℝ :=
  if α ≤ f (historyPoint q α η s) - value then
    ∫ y, (2 / α) * max 0
      (⟪(1 / (b : ℝ)) • ∑ i, g (historyPoint q α η s) (ζ i), y-historyPoint q α η s⟫ + α / 2) ∂μ
  else 0

lemma measurable_historyPenalty (q : Params) (hR : 0 < q.R) (α η : ℝ)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g))
    (f : Space q → ℝ) (hf : Measurable f) (value : ℝ)
    (μ : Measure (Space q)) [SFinite μ] (b : ℕ) :
    Measurable (Function.uncurry (historyPenalty q α η g f value μ b)) := by
  have hx := (measurable_historyPoint q hR α η).comp
    (measurable_fst : Measurable (Prod.fst : History q × (Fin b → q.Ω) → History q))
  have hgi (i : Fin b) : Measurable (fun z : History q × (Fin b → q.Ω) =>
      g (historyPoint q α η z.1) (z.2 i)) := hg.comp (hx.prodMk (by fun_prop))
  have hm : Measurable (fun z : History q × (Fin b → q.Ω) =>
      (1 / (b : ℝ)) • ∑ i, g (historyPoint q α η z.1) (z.2 i)) := by fun_prop
  have hF : Measurable (fun z : (History q × (Fin b → q.Ω)) × Space q =>
      (2 / α) * max 0 (⟪(1 / (b : ℝ)) • ∑ i, g (historyPoint q α η z.1.1) (z.1.2 i),
        z.2-historyPoint q α η z.1.1⟫ + α / 2)) := by
    have hm' : Measurable (fun z : (History q × (Fin b → q.Ω)) × Space q =>
        (1 / (b : ℝ)) • ∑ i, g (historyPoint q α η z.1.1) (z.1.2 i)) := hm.comp measurable_fst
    have hx' : Measurable (fun z : (History q × (Fin b → q.Ω)) × Space q =>
        historyPoint q α η z.1.1) := hx.comp measurable_fst
    fun_prop
  exact Measurable.ite (measurableSet_le measurable_const ((hf.comp hx).sub_const value))
    hF.stronglyMeasurable.integral_prod_right.measurable measurable_const

lemma historyPenalty_nonneg (q : Params) (α η : ℝ) (hα : 0 < α)
    (g : Space q → q.Ω → Space q) (f : Space q → ℝ) (value : ℝ)
    (μ : Measure (Space q)) (b : ℕ) (s : History q) (ζ : Fin b → q.Ω) :
    0 ≤ historyPenalty q α η g f value μ b s ζ := by
  unfold historyPenalty
  split_ifs
  · apply integral_nonneg
    intro y
    exact mul_nonneg (by positivity) (le_max_left _ _)
  · exact le_refl 0

lemma historyPenalty_mean (q : Params) (hd : 0 < q.d) (hL : 0 < q.L) (hR : 0 < q.R)
    (α η : ℝ) (hα : 0 < α) (hαR : α ≤ q.L * q.R)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (hlip : ∀ x y, |f x - f y| ≤ q.L * ‖x-y‖)
    (xstar : Space q) (hxstar : ‖xstar‖ ≤ q.R)
    (μ : Measure (Space q)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ y ∂μ, ‖y-xstar‖ ≤ α / (4 * q.L))
    (b : ℕ) (hb : 0 < b)
    (hbatch : 1024 * q.σ ^ 2 * q.R ^ 2 ≤ (q.d : ℝ) * b * α ^ 2)
    (s : History q) :
    Integrable (historyPenalty q α η g f (f xstar) μ b s) (Measure.pi fun _ => p) ∧
    (∫ ζ, historyPenalty q α η g f (f xstar) μ b s ζ ∂Measure.pi (fun _ => p)) ≤ 1 / 32 := by
  change Integrable (fun ζ => historyPenalty q α η g f (f xstar) μ b s ζ) _ ∧ _
  by_cases hbad : α ≤ f (historyPoint q α η s) - f xstar
  · have hs : ∀ᵐ y ∂μ, ⟪v (historyPoint q α η s), y-historyPoint q α η s⟫ ≤ -(3 * α / 4) := by
      filter_upwards [hμ] with y hy
      exact CovarianceSoftCutLocalization.target_signal_bound q hL α f v hg.support hlip _ xstar y hbad hy
    have hu : ∀ᵐ y ∂μ, ‖y-historyPoint q α η s‖ ≤ 4 * q.R := by
      filter_upwards [hμ] with y hy
      have hsub := CovarianceSoftCutLocalization.target_ball_subset q hL hR α hαR xstar hxstar
      have hy' : y ∈ Metric.closedBall xstar (α / (4 * q.L)) := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
      have hyn : ‖y‖ ≤ 2 * q.R := by simpa using hsub hy'
      have hxn := norm_centroid_le q hR α η (List.ofFn (fun i : Fin s.1 => s.2 i))
      have hn := norm_sub_le y (historyPoint q α η s)
      change ‖historyPoint q α η s‖ ≤ 2 * q.R at hxn
      linarith
    have h := CovarianceSoftCutOracle.target_integrated_hinge_bound q hd hR p f v g hg
      (historyPoint q α η s) μ b hb α hα hu hs hbatch
    simpa only [historyPenalty, ite_eq_left hbad, probReal_univ, one_div] using h
  · simp only [historyPenalty, ite_eq_right hbad, integral_zero]
    norm_num

lemma cumulativePenalty_mean (q : Params) (hd : 0 < q.d) (hL : 0 < q.L) (hR : 0 < q.R)
    (α η : ℝ) (hα : 0 < α) (hαR : α ≤ q.L * q.R)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q) (hf : Measurable f)
    (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (hlip : ∀ x y, |f x - f y| ≤ q.L * ‖x-y‖)
    (xstar : Space q) (hxstar : ‖xstar‖ ≤ q.R)
    (μ : Measure (Space q)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ y ∂μ, ‖y-xstar‖ ≤ α / (4 * q.L))
    (b : ℕ) (hb : 0 < b)
    (hbatch : 1024 * q.σ ^ 2 * q.R ^ 2 ≤ (q.d : ℝ) * b * α ^ 2)
    {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ) (ξ : ℕ → Ξ → q.Ω)
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (T : ℕ) (s : History q) :
    Integrable (fun ω => OracleTemplate.StochasticGeneralized.accumulated (fun _ => b)
      (historyNext q α η g) (historyPenalty q α η g f (f xstar) μ) T s (fun i => ξ i ω)) P ∧
    (∫ ω, OracleTemplate.StochasticGeneralized.accumulated (fun _ => b)
      (historyNext q α η g) (historyPenalty q α η g f (f xstar) μ) T s (fun i => ξ i ω) ∂P) ≤ (T : ℝ) / 32 := by
  have hstate := historyPenalty_mean q hd hL hR α η hα hαR p f v g hg hlip
    xstar hxstar μ hμ b hb hbatch
  have h := CovarianceSoftCutFreshness.accumulated_mean_iid p P ξ h_samples
    (cost := fun _ : History q => b) measurable_const
    (measurable_historyNext q hR α η g hg.measurable)
    (measurable_historyPenalty q hR α η g hg.measurable f hf (f xstar) μ)
    (historyPenalty_nonneg q α η hα g f (f xstar) μ)
    (fun s => (hstate s).1) (fun s => (hstate s).2) T s
  simpa only [one_div, div_eq_mul_inv, one_mul] using h

def historyCuts (q : Params) (s : History q) : List (Cut q) :=
  List.ofFn (fun i : Fin s.1 => s.2 i)

lemma historyCuts_next (q : Params) (α η : ℝ) (g : Space q → q.Ω → Space q)
    (b : ℕ) (s : History q) (ζ : Fin b → q.Ω) :
    historyCuts q (historyNext q α η g b s ζ) = historyCuts q s ++
      [((1 / (b : ℝ)) • ∑ i, g (historyPoint q α η s) (ζ i), historyPoint q α η s)] := by
  unfold historyCuts historyNext
  rw [List.ofFn_succ_last]
  simp only [Fin.val_castSucc, Fin.val_last, Function.update_self]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact Function.update_of_ne (Nat.ne_of_lt i.isLt) _ _

lemma historyTrace_tail (q : Params) (α η : ℝ) (g : Space q → q.Ω → Space q)
    (b : ℕ) (s : History q) (ξ : ℕ → q.Ω) (n k : ℕ) :
    (OracleTemplate.StochasticGeneralized.blockTrace (fun _ => b)
      (historyNext q α η g) s ξ n).2 k = ξ (n*b+k) := by
  rw [OracleTemplate.StochasticGeneralized.blockTrace_tail]
  simp [OracleTemplate.StochasticGeneralized.blockCalls]

lemma historyTrace_cuts (q : Params) (α η : ℝ) (g : Space q → q.Ω → Space q)
    (b n : ℕ) (ξ : ℕ → q.Ω) :
    historyCuts q (OracleTemplate.StochasticGeneralized.blockTrace (fun _ => b)
      (historyNext q α η g) (0, fun _ => (0, 0)) ξ n).1 = List.ofFn (sampleCuts q α η b g n ξ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [OracleTemplate.StochasticGeneralized.blockTrace_succ]
    change historyCuts q (historyNext q α η g b _ _) = _
    rw [historyCuts_next, ih]
    have hp : historyPoint q α η (OracleTemplate.StochasticGeneralized.blockTrace (fun _ => b)
        (historyNext q α η g) (0, fun _ => (0, 0)) ξ n).1 = samplePoint q α η b g n ξ := by
      change centroid q α η (historyCuts q _) = _
      rw [ih]
      rfl
    rw [hp]
    simp only [sampleCuts]
    rw [List.ofFn_fin_append]
    simp only [List.ofFn_succ, List.ofFn_zero, historyTrace_tail, samplePoint]

lemma historyTrace_point (q : Params) (α η : ℝ) (g : Space q → q.Ω → Space q)
    (b n : ℕ) (ξ : ℕ → q.Ω) :
    historyPoint q α η (OracleTemplate.StochasticGeneralized.blockTrace (fun _ => b)
      (historyNext q α η g) (0, fun _ => (0, 0)) ξ n).1 = samplePoint q α η b g n ξ := by
  change centroid q α η (historyCuts q _) = _
  rw [historyTrace_cuts]
  rfl

lemma sampleCuts_list_succ (q : Params) (α η : ℝ) (g : Space q → q.Ω → Space q)
    (b n : ℕ) (ξ : ℕ → q.Ω) :
    List.ofFn (sampleCuts q α η b g (n+1) ξ) = List.ofFn (sampleCuts q α η b g n ξ) ++
      [((1 / (b : ℝ)) • ∑ i : Fin b, g (samplePoint q α η b g n ξ) (ξ (n*b+i)),
        samplePoint q α η b g n ξ)] := by
  simp only [sampleCuts]
  rw [List.ofFn_fin_append]
  rfl

lemma sampleLoss_sum (q : Params) (hL : 0 < q.L) (α η : ℝ) (hα : 0 < α)
    (g : Space q → q.Ω → Space q) (b n : ℕ) (ξ : ℕ → q.Ω) (xstar : Space q) :
    (∫ y, lossSum q α (List.ofFn (sampleCuts q α η b g n ξ)) y
      ∂CovarianceSoftCutLocalization.targetMeasure q α xstar) =
    ∑ t ∈ Finset.range n, ∫ y, hinge q α
      ((1 / (b : ℝ)) • ∑ i : Fin b, g (samplePoint q α η b g t ξ) (ξ (t*b+i)),
        samplePoint q α η b g t ξ) y ∂CovarianceSoftCutLocalization.targetMeasure q α xstar := by
  induction n with
  | zero => simp [sampleCuts, lossSum]
  | succ n ih =>
    rw [sampleCuts_list_succ, CovarianceSoftCutLocalization.targetMeasure_lossSum_append q hL α hα,
      ih, Finset.sum_range_succ]

lemma cumulativePenalty_eq_loss_on_bad (q : Params) (hL : 0 < q.L)
    (α : ℝ) (hα : 0 < α) (g : Space q → q.Ω → Space q)
    (f : Space q → ℝ) (xstar : Space q) (b T : ℕ) (ξ : ℕ → q.Ω)
    (hbad : ∀ t, t < T → α ≤ f (samplePoint q α (2 / α) b g t ξ) - f xstar) :
    OracleTemplate.StochasticGeneralized.accumulated (fun _ => b) (historyNext q α (2 / α) g)
      (historyPenalty q α (2 / α) g f (f xstar) (CovarianceSoftCutLocalization.targetMeasure q α xstar))
      T (0, fun _ => (0, 0)) ξ =
    (2 / α) * ∫ y, lossSum q α (List.ofFn (sampleCuts q α (2 / α) b g T ξ)) y
      ∂CovarianceSoftCutLocalization.targetMeasure q α xstar := by
  rw [OracleTemplate.StochasticGeneralized.accumulated_eq_sum, sampleLoss_sum q hL α (2 / α) hα,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hb := hbad t (Finset.mem_range.mp ht)
  simp only [historyPenalty, historyTrace_point, ite_eq_left hb, historyTrace_tail,
    integral_const_mul, hinge]

end LongTails.Proofs.CovarianceSoftCutProcess
