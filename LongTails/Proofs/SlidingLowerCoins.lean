import LongTails.Proofs.HolderNoiseCoinExposure
import LongTails.Proofs.AdaptiveOracleConcentration

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.SlidingLowerCoins

open QuasarCoinLaw HolderNoiseCoinExposure

noncomputable def extend (N : ℕ) (v : Fin N → Bool) : ℕ → Bool :=
  fun s => if h : s < N then v ⟨s, h⟩ else false

lemma extend_agree (N : ℕ) (β : ℕ → Bool) : ∀ s < N, extend N (fun i : Fin N => β i) s = β s := by
  intro s hs
  simp [extend, hs]

lemma measurable_of_dep {M : Type*} [MeasurableSpace M] (N : ℕ) (g : (ℕ → Bool) → M)
    (hg : ∀ β β' : ℕ → Bool, (∀ s < N, β s = β' s) → g β = g β') : Measurable g := by
  have he : g = (fun v : Fin N → Bool => g (extend N v)) ∘ (fun β (i : Fin N) => β i) := by
    funext β
    exact hg β _ (fun s hs => (extend_agree N β s hs).symm)
  rw [he]
  exact (measurable_of_countable _).comp (Measurable.of_eval (fun i => measurable_pi_apply (i : ℕ)))

lemma adapted_coin_integral {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℕ)
    (g : (ℕ → Bool) → ℝ) (hg : ∀ β β' : ℕ → Bool, (∀ s < t, β s = β' s) → g β = g β') :
    (∫ β, g β * (if β t then (1 : ℝ) else 0) ∂(coinPath p hp hp1 : Measure (ℕ → Bool))) =
      p * ∫ β, g β ∂(coinPath p hp hp1 : Measure (ℕ → Bool)) := by
  have hiid := coinPath_iid hp hp1
  have hind := AdaptiveOracleConcentration.iid_history_independent
    (P := (coinPath p hp hp1 : Measure (ℕ → Bool))) (ξ := fun k (β : ℕ → Bool) => β k)
    (fun i => measurable_pi_apply i) hiid.independent t
  let G : (Fin t → Bool) → ℝ := fun v => g (extend t v)
  let H : Bool → ℝ := fun b => if b then 1 else 0
  have hG : Measurable G := measurable_of_countable _
  have hH : Measurable H := measurable_of_countable _
  have hc := hind.comp hG hH
  have he : (fun β : ℕ → Bool => g β) = fun β => G (fun i : Fin t => β i) := by
    funext β
    exact hg β _ (fun s hs => (extend_agree t β s hs).symm)
  have hX : Measurable (fun β : ℕ → Bool => G (fun i : Fin t => β i)) :=
    hG.comp (Measurable.of_eval (fun i => measurable_pi_apply (i : ℕ)))
  have hY : Measurable (fun β : ℕ → Bool => H (β t)) := hH.comp (measurable_pi_apply t)
  have hm := hc.integral_fun_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable
  have h1 : (∫ β, g β * (if β t then (1 : ℝ) else 0) ∂(coinPath p hp hp1 : Measure (ℕ → Bool))) =
      ∫ β, G (fun i : Fin t => β i) * H (β t) ∂(coinPath p hp hp1 : Measure (ℕ → Bool)) := by
    congr 1
    funext β
    rw [show g β = G (fun i : Fin t => β i) from congrFun he β]
  simp only [Function.comp_def] at hm
  rw [h1, hm]
  have h2 : (∫ β, H (β t) ∂(coinPath p hp hp1 : Measure (ℕ → Bool))) = p :=
    coinIndicator_integral p hp hp1 t
  rw [h2, mul_comm, ← he]

end LongTails.Proofs.SlidingLowerCoins
