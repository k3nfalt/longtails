import LongTails.Proofs.StoppedVectorConcentration
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.IidVectorConcentration

open AdaptiveOracleConcentration StoppedVectorConcentration

lemma iid_vector_tail {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]
    {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = p)
    {Y : (n : ℕ) → (Fin n → Z) × Z → E} (hY : ∀ n, Measurable (Y n))
    {R b θe θc energy cross ell : ℝ} (hR : 0 ≤ R) (hθe : 0 ≤ θe) (hθc : 0 ≤ θc)
    (hsmall : θe * b ≤ 1) (variance cost : ℕ → ℝ)
    (hcap : ∀ i a z, ‖Y i (a, z)‖ ^ 2 ≤ b)
    (hvariance : ∀ i a, (∫ z, ‖Y i (a, z)‖ ^ 2 ∂p) ≤ variance i)
    (hdirection : ∀ i a v, ‖v‖ ≤ R →
      Integrable (fun z => Real.exp (θc * ⟪v, Y i (a, z)⟫)) p ∧
        (∫ z, Real.exp (θc * ⟪v, Y i (a, z)⟫) ∂p) ≤ Real.exp (cost i))
    (n : ℕ)
    (hebudget : 2 * θe * (∑ i ∈ Finset.range n, variance i) - θe * energy ≤ -ell)
    (hcbudget : (∑ i ∈ Finset.range n, cost i) - θc * cross ≤ -ell)
    (hrbudget : energy + 2 * cross ≤ R ^ 2) :
    P.real {ω | R < ‖∑ i ∈ Finset.range n, Y i ((fun j => ξ j ω), ξ i ω)‖} ≤
      2 * Real.exp (-ell) := by
  let energyInc := fun i az => ‖Y i az‖ ^ 2
  have hem : ∀ i, Measurable (energyInc i) := fun i => (hY i).norm.pow_const 2
  have hepoint : ∀ i a,
      Integrable (fun z => Real.exp (θe * energyInc i (a, z))) p ∧
        (∫ z, Real.exp (θe * energyInc i (a, z)) ∂p) ≤ Real.exp (2 * θe * variance i) := by
    intro i a
    have hmeas : Measurable (fun z => energyInc i (a, z)) :=
      (hem i).comp (measurable_const.prodMk measurable_id)
    have hh := bounded_nonnegative_mgf (P := p) hmeas (fun z => sq_nonneg _) (hcap i a) hθe hsmall
    refine ⟨hh.1, hh.2.trans (Real.exp_le_exp.mpr ?_)⟩
    exact mul_le_mul_of_nonneg_left (hvariance i a) (by positivity)
  have he := iid_predictable_sum_exponential_bound hξ hind hlaw (fun i => 2 * θe * variance i)
    θe hem (fun i a => (hepoint i a).1) (fun i a => (hepoint i a).2) n
  have heTail := exponential_tail_of_bound hθe he.1 he.2 energy
  have heCost : (∑ i ∈ Finset.range n, 2 * θe * variance i) - θe * energy ≤ -ell := by
    rw [← Finset.mul_sum]
    exact hebudget
  have heTail' : P.real {ω | energy ≤ ∑ i ∈ Finset.range n,
      ‖Y i ((fun j => ξ j ω), ξ i ω)‖ ^ 2} ≤ Real.exp (-ell) :=
    heTail.trans (Real.exp_le_exp.mpr heCost)
  let crossInc := fun i az => ⟪historyStoppedDirection Y R i az.1, Y i az⟫
  have hcm : ∀ i, Measurable (crossInc i) := by
    intro i
    exact ((history_stopped_direction_measurable hY R i).comp measurable_fst).inner (hY i)
  have hcpoint : ∀ i a,
      Integrable (fun z => Real.exp (θc * crossInc i (a, z))) p ∧
        (∫ z, Real.exp (θc * crossInc i (a, z)) ∂p) ≤ Real.exp (cost i) := by
    intro i a
    exact hdirection i a (historyStoppedDirection Y R i a) (history_stopped_direction_norm_le Y hR i a)
  have hc := iid_predictable_sum_exponential_bound hξ hind hlaw cost θc hcm
    (fun i a => (hcpoint i a).1) (fun i a => (hcpoint i a).2) n
  have hcTail := (exponential_tail_of_bound hθc hc.1 hc.2 cross).trans (Real.exp_le_exp.mpr hcbudget)
  have hcTail' : P.real {ω | cross ≤ ∑ i ∈ Finset.range n,
      ⟪stoppedSum (fun i => Y i ((fun j => ξ j ω), ξ i ω)) R i,
        stoppedIncrement (fun i => Y i ((fun j => ξ j ω), ξ i ω)) R i⟫} ≤ Real.exp (-ell) := by
    simpa only [crossInc, history_stopped_cross_eq] using hcTail
  have hh := stopped_energy_tail hR n heTail' hcTail' hrbudget
  nlinarith only [hh]

end LongTails.Proofs.IidVectorConcentration
