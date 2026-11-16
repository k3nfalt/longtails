import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.QuasarCoinLaw

noncomputable def coinMeasure (ν : ℝ) : Measure Bool :=
  ENNReal.ofReal ν • Measure.dirac true + ENNReal.ofReal (1 - ν) • Measure.dirac false

lemma coinMeasure_true (ν : ℝ) : coinMeasure ν {true} = ENNReal.ofReal ν := by
  simp [coinMeasure]

lemma coinMeasure_false (ν : ℝ) : coinMeasure ν {false} = ENNReal.ofReal (1 - ν) := by
  simp [coinMeasure]

lemma coinMeasure_isProb {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 1) :
    IsProbabilityMeasure (coinMeasure ν) := by
  constructor
  simp only [coinMeasure, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

noncomputable def coinLaw (ν : ℝ) (h0 : 0 ≤ ν) (h1 : ν ≤ 1) : ProbabilityMeasure Bool :=
  haveI := coinMeasure_isProb h0 h1
  ⟨coinMeasure ν, inferInstance⟩

noncomputable def coinPath (ν : ℝ) (h0 : 0 ≤ ν) (h1 : ν ≤ 1) : ProbabilityMeasure (ℕ → Bool) :=
  haveI := coinMeasure_isProb h0 h1
  ⟨Measure.infinitePi (fun _ : ℕ => coinMeasure ν), inferInstance⟩

lemma coinPath_iid {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 1) :
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Bool) => ξ k)
      ((coinLaw ν h0 h1 : ProbabilityMeasure Bool) : Measure Bool)
      ((coinPath ν h0 h1 : ProbabilityMeasure (ℕ → Bool)) : Measure (ℕ → Bool)) := by
  have := coinMeasure_isProb h0 h1
  refine ⟨fun k => measurable_pi_apply k, ?_, fun k => ?_⟩
  · change iIndepFun (fun k (ξ : ℕ → Bool) => id (ξ k))
      (Measure.infinitePi (fun _ : ℕ => coinMeasure ν))
    exact iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  · change (Measure.infinitePi (fun _ : ℕ => coinMeasure ν)).map (fun ξ => ξ k) = coinMeasure ν
    exact Measure.infinitePi_map_eval _ k

lemma coinPath_silent {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 1) (K : ℕ) :
    ((coinPath ν h0 h1 : ProbabilityMeasure (ℕ → Bool)) : Measure (ℕ → Bool))
      {ξ | ∀ t < K, ξ t = false} = ENNReal.ofReal (1 - ν) ^ K := by
  have := coinMeasure_isProb h0 h1
  have he : {ξ : ℕ → Bool | ∀ t < K, ξ t = false} =
      Set.pi (Finset.range K : Set ℕ) (fun _ => ({false} : Set Bool)) := by
    ext ξ
    simp
  change Measure.infinitePi (fun _ : ℕ => coinMeasure ν) _ = _
  rw [he]
  have hp := Measure.infinitePi_pi (μ := fun _ : ℕ => coinMeasure ν) (s := Finset.range K)
    (t := fun _ => ({false} : Set Bool)) (fun _ _ => measurableSet_singleton false)
  rw [hp]
  simp [coinMeasure_false]

lemma silent_measurable (K : ℕ) : MeasurableSet {ξ : ℕ → Bool | ∀ t < K, ξ t = false} := by
  have he : {ξ : ℕ → Bool | ∀ t < K, ξ t = false} = ⋂ t ∈ Finset.range K, {ξ | ξ t = false} := by
    ext ξ; simp
  rw [he]
  exact Finset.measurableSet_biInter _ (fun t _ => measurableSet_eq_fun (measurable_pi_apply t)
    measurable_const)

end LongTails.Proofs.QuasarCoinLaw
