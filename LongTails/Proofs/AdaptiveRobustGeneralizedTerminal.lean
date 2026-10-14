import LongTails.Proofs.AdaptiveRobustGeneralizedStoppedEnergy
import LongTails.Proofs.AdaptiveRobustGeneralizedConcentration

open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.AdaptiveRobustGeneralized

open StochasticGeneralized
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate tentativeWeight energy)
open StochasticGeneralized (proofActive proofWeight target confidence_log_gt_one)

lemma proofNoise_accumulated_measurable (p : Params) {f : p.E → ℝ}
    (hf : Measurable f) (hgrad : Measurable (gradient f)) (u : p.E)
    {oracle : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry oracle))
    (n : ℕ) (s : Iterate p.E) :
    Measurable (accumulated (proofCost p f u) (proofNext p f u oracle) (proofNoise p f u oracle) n s) := by
  exact (accumulated_measurable (measurable_proofCost p hf u)
    (measurable_proofNext p hf hgrad u hg) (measurable_proofNoise p hf hgrad u hg) n).comp
    (measurable_const.prodMk measurable_id)

lemma proofNoise_accumulated_control (p : Params) (hp : spec.valid p)
    {f : p.E → ℝ} (hf : Measurable f) (hgrad : Measurable (gradient f))
    (u : p.E) (hmin : IsMinOn f univ u) {μ : Measure p.Ω} [IsProbabilityMeasure μ]
    {oracle : p.E → p.Ω → p.E} (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    (n : ℕ) (s : Iterate p.E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (ha : tentativeWeight s ≤ 2*target p.R p.ε) :
    let ℓ := Real.log (Real.exp 1/p.δ)
    let Z := accumulated (proofCost p f u) (proofNext p f u oracle) (proofNoise p f u oracle) n s
    Integrable (fun ξ => Real.exp ((ℓ/p.R^2)*Z ξ)) (Measure.infinitePi fun _ : ℕ => μ) ∧
      (∫ ξ, Real.exp ((ℓ/p.R^2)*Z ξ) ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤ Real.exp ℓ := by
  let ℓ := Real.log (Real.exp 1/p.δ)
  let t := ℓ/p.R^2
  let κ := ℓ*p.ε/(1048576*p.R^2)
  have hℓ : 1 < ℓ := confidence_log_gt_one hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2
  have hR := hp.2.2.1
  have ht : 0 < t := by dsimp [t]; positivity
  have hκ : 0 ≤ κ := by dsimp [κ]; have he := hp.2.2.2.2.2.1; positivity
  have hc : κ*(32*target p.R p.ε) ≤ ℓ := by
    have he := hp.2.2.2.2.2.1
    have hℓ0 : 0 < ℓ := by linarith
    dsimp [κ, target]
    field_simp
    nlinarith
  have h := proof_accumulated_control p hp hf hgrad u hmin hg n s
  apply remove_compensator (proofNoise_accumulated_measurable p hf hgrad u hg.measurable n s) h.1 h.2
  intro ξ
  have he : accumulated (proofCost p f u) (proofNext p f u oracle)
      (proofIncrement p f u oracle) n s ξ =
      t*accumulated (proofCost p f u) (proofNext p f u oracle) (proofNoise p f u oracle) n s ξ-
      κ*accumulated (proofCost p f u) (proofNext p f u oracle) (proofWeight p f u) n s ξ := by
    change accumulated (proofCost p f u) (proofNext p f u oracle)
      (fun n s b => t*proofNoise p f u oracle n s b-κ*proofWeight p f u n s b) n s ξ = _
    simpa only [sub_eq_add_neg, neg_mul] using
      accumulated_linear (proofCost p f u) (proofNext p f u oracle)
        (proofNoise p f u oracle) (proofWeight p f u) t (-κ) n s ξ
  rw [he]
  have hw := proofTrace_weight_sum p hp f u oracle s hA hG ha ξ n
  have hm := mul_le_mul_of_nonneg_left hw hκ
  change t*_ ≤ ℓ+(t*_-κ*_)
  linarith

lemma proofNoise_tail (p : Params) (hp : spec.valid p)
    {f : p.E → ℝ} (hf : Measurable f) (hgrad : Measurable (gradient f))
    (u : p.E) (hmin : IsMinOn f univ u) {μ : Measure p.Ω} [IsProbabilityMeasure μ]
    {oracle : p.E → p.Ω → p.E} (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    (n : ℕ) (s : Iterate p.E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (ha : tentativeWeight s ≤ 2*target p.R p.ε) :
    (Measure.infinitePi fun _ : ℕ => μ) {ξ | 2*p.R^2 <
      accumulated (proofCost p f u) (proofNext p f u oracle) (proofNoise p f u oracle) n s ξ} ≤
      ENNReal.ofReal (p.δ/2) := by
  let ℓ := Real.log (Real.exp 1/p.δ)
  have hR := hp.2.2.1
  have hδ := hp.2.2.2.2.2.2.1
  have hℓ : 0 < ℓ := lt_trans zero_lt_one (confidence_log_gt_one hδ hp.2.2.2.2.2.2.2)
  have h := proofNoise_accumulated_control p hp hf hgrad u hmin hg n s hA hG ha
  have hb := exponential_tail (show 0 ≤ ℓ/p.R^2 by positivity) h.1 h.2 (r := 2*p.R^2)
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hex : ℓ-(ℓ/p.R^2)*(2*p.R^2) = -ℓ := by field_simp; ring
  rw [hex]
  have hδ1 := hp.2.2.2.2.2.2.2
  have hlogδ : Real.log p.δ ≤ 0 := Real.log_nonpos hδ.le hδ1.le
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hell : ℓ = 1-Real.log p.δ := by
    dsimp [ℓ]
    rw [Real.log_div (Real.exp_ne_zero _) hδ.ne', Real.log_exp]
  calc
    _ ≤ Real.exp (Real.log (p.δ/2)) := by
      apply Real.exp_le_exp.mpr
      rw [Real.log_div hδ.ne' (by norm_num), hell]
      linarith
    _ = _ := Real.exp_log (by positivity)

lemma proofNoise_tail_iid (p : Params) (hp : spec.valid p)
    {f : p.E → ℝ} (hf : Measurable f) (hgrad : Measurable (gradient f))
    (u : p.E) (hmin : IsMinOn f univ u) {μ : Measure p.Ω} [IsProbabilityMeasure μ]
    {oracle : p.E → p.Ω → p.E} (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ}
    {ξ : ℕ → Ξ → p.Ω} (hξ : IID ξ μ P)
    (n : ℕ) (s : Iterate p.E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (ha : tentativeWeight s ≤ 2*target p.R p.ε) :
    P {ω | 2*p.R^2 < accumulated (proofCost p f u) (proofNext p f u oracle)
      (proofNoise p f u oracle) n s (fun k => ξ k ω)} ≤ ENNReal.ofReal (p.δ/2) := by
  have hm := proofNoise_accumulated_measurable p hf hgrad u hg.measurable n s
  have hl : HasLaw (fun ω k => ξ k ω) (Measure.infinitePi fun _ : ℕ => μ) P :=
    ⟨hξ.stream_law.measurable.aemeasurable, hξ.stream_law.map_eq⟩
  rw [hl.measure_eq (measurableSet_lt measurable_const hm)]
  exact proofNoise_tail p hp hf hgrad u hmin hg n s hA hG ha

lemma proofTrace_target_accuracy (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0+p.L1*‖gradient f x‖)
    (u : p.E) (hmin : IsMinOn f univ u) (oracle : p.E → p.Ω → p.E) (s : Iterate p.E)
    (hinit : energy f u s ≤ p.R^2) (ξ : ℕ → p.Ω) (n : ℕ)
    (hnoise : accumulated (proofCost p f u) (proofNext p f u oracle) (proofNoise p f u oracle) n s ξ ≤ 2*p.R^2)
    (hT : target p.R p.ε ≤ (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n).1.A) :
    f (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n).1.x-f u ≤ p.ε := by
  let q := (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n).1
  have he := proofTrace_energy p hp hc hg hdiff hH u oracle s ξ n
  have hd := accumulated_nonneg (proofCost p f u) (proofNext p f u oracle)
    (proofDissipation p f u oracle) (proofDissipation_nonneg p hp f u oracle) n s ξ
  have hend : energy f u q ≤ 3*p.R^2 := by linarith
  have hgap : 0 ≤ f q.x-f u := sub_nonneg.mpr (hmin (mem_univ _))
  have hm := mul_le_mul_of_nonneg_right hT hgap
  have hR := hp.2.2.1
  have hε := hp.2.2.2.2.2.1
  have ht : 0 < target p.R p.ε := by dsimp [target]; positivity
  have hid : target p.R p.ε*p.ε = 16*p.R^2 := by dsimp [target]; field_simp
  apply (mul_le_mul_iff_right₀ ht).mp
  dsimp only [energy] at hend
  change target p.R p.ε*(f q.x-f u) ≤ target p.R p.ε*p.ε
  rw [hid]
  nlinarith [sq_nonneg ‖q.z-u‖, sq_nonneg p.R]

end OracleTemplate.AdaptiveRobustGeneralized
