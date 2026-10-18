import LongTails.Proofs.QuantileQuadraticOracle
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import LongTails.Proofs.SgdConvex
import LongTails.Proofs.ZerothOrderEstimator

open MeasureTheory

namespace LongTails.Proofs.QuantileExecutionLowerBound

noncomputable def finiteLaw {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    (w : ι → ℝ) : Measure ι := ∑ i, ENNReal.ofReal (w i) • Measure.dirac i

lemma finiteLaw_singleton {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (w : ι → ℝ) (i : ι) :
    finiteLaw w {i} = ENNReal.ofReal (w i) := by
  classical
  simp [finiteLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Set.indicator_apply, eq_comm]

lemma finiteLaw_probability {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    IsProbabilityMeasure (finiteLaw w) := by
  constructor
  simp only [finiteLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hs]
  simp

lemma finiteLaw_map {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    (w x : ι → ℝ) (hx : Measurable x) :
    (finiteLaw w).map x = QuantileShellOracle.atomicMeasure w x := by
  unfold finiteLaw QuantileShellOracle.atomicMeasure
  rw [← Measure.mapₗ_apply_of_measurable hx, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.mapₗ_apply_of_measurable hx, Measure.map_smul, Measure.map_dirac' hx]
  exact hx.aemeasurable

lemma finiteLaw_pi {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (N : ℕ) :
    (Measure.pi fun _ : Fin N => finiteLaw w) = finiteLaw (fun v => ∏ j, w (v j)) := by
  let := finiteLaw_probability w hw hs
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.pi_singleton, finiteLaw_singleton]
  simp only [finiteLaw_singleton]
  exact (ENNReal.ofReal_prod_of_nonneg (fun j _ => hw (v j))).symm

lemma finiteLaw_integral {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∫ i, f i ∂finiteLaw w) = ∑ i, w i * f i := by
  rw [integral_fintype]
  · simp only [Measure.real, finiteLaw_singleton, ENNReal.toReal_ofReal (hw _), smul_eq_mul]
  · apply integrable_finsetSum_measure.mpr
    intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma integrable_sections {ι Ω : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace Ω] {ρ : Measure Ω} [SFinite ρ]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) {f : Ω × ι → ℝ}
    (hi : Integrable f (ρ.prod (finiteLaw w))) (i : ι) :
    Integrable (fun ω => f (ω, i)) ρ := by
  apply (ae_iff_of_countable.mp hi.prod_left_ae) i
  rw [finiteLaw_singleton]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (hw i))

lemma product_integral {ι Ω : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace Ω] {ρ : Measure Ω} [SFinite ρ]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {f : Ω × ι → ℝ}
    (hi : Integrable f (ρ.prod (finiteLaw w))) :
    (∫ s, f s ∂ρ.prod (finiteLaw w)) = ∑ i, w i * ∫ ω, f (ω, i) ∂ρ := by
  let : IsFiniteMeasure (finiteLaw w) := by
    constructor
    simp [finiteLaw, Measure.finsetSum_apply, Measure.smul_apply, ENNReal.sum_lt_top]
  rw [integral_prod_symm _ hi]
  exact finiteLaw_integral w _ hw

def prefixFill {N : ℕ} (z : Fin N → ℝ) (n : ℕ) : ℝ :=
  if hn : n < N then z ⟨n, hn⟩ else 0

lemma measurable_prefixFill (N : ℕ) : Measurable (@prefixFill N) := by
  apply Measurable.of_eval
  intro n
  unfold prefixFill
  split <;> fun_prop

lemma finite_observation_integral {ι Ω : Type} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace Ω]
    (ρ : ProbabilityMeasure Ω) (w x : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hs : ∑ i, w i = 1) (hx : Measurable x) (N : ℕ)
    (F : Ω × (ℕ → ℝ) → ℝ) (hF : Measurable F)
    (hpref : ∀ a ξ ζ, (∀ n, n < N → ξ n = ζ n) → F (a, ξ) = F (a, ζ))
    (hI : Integrable F ((ρ : Measure Ω).prod
      (Measure.infinitePi fun _ : ℕ => QuantileShellOracle.atomicMeasure w x))) :
    (∀ v : Fin N → ι, Integrable (fun a => F (a, prefixFill (fun j => x (v j)))) (ρ : Measure Ω)) ∧
    (∫ s, F s ∂(ρ : Measure Ω).prod
      (Measure.infinitePi fun _ : ℕ => QuantileShellOracle.atomicMeasure w x)) =
      ∑ v : Fin N → ι, (∏ j, w (v j)) * ∫ a, F (a, prefixFill (fun j => x (v j))) ∂(ρ : Measure Ω) := by
  let p := QuantileShellOracle.atomicMeasure w x
  let := QuantileShellOracle.atomic_probability w x (fun i => (hw i).le) hs
  let := finiteLaw_probability w (fun i => (hw i).le) hs
  let G := fun s : Ω × (Fin N → ℝ) => F (s.1, prefixFill s.2)
  have hG : Measurable G := hF.comp (measurable_fst.prodMk
    ((measurable_prefixFill N).comp measurable_snd))
  have hpre := (MeasurePreserving.id (ρ : Measure Ω)).prod
    (OracleTemplate.StochasticGradient.prefix_measurePreserving p N)
  have he : G ∘ Prod.map id (fun ξ : ℕ → ℝ => fun j : Fin N => ξ j) = F := by
    funext s
    apply hpref
    intro n hn
    simp [prefixFill, hn]
  have hGI : Integrable G ((ρ : Measure Ω).prod (Measure.pi fun _ : Fin N => p)) := by
    apply (hpre.integrable_comp hG.aestronglyMeasurable).mp
    simpa only [he] using hI
  have hcode : MeasurePreserving (fun v : Fin N → ι => fun j => x (v j))
      (finiteLaw (fun v : Fin N → ι => ∏ j, w (v j))) (Measure.pi fun _ : Fin N => p) := by
    rw [← finiteLaw_pi w (fun i => (hw i).le) hs N]
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.pi_map_pi (fun _ => hx.aemeasurable)]
    simp only [finiteLaw_map w x hx, p]
  have hc := (MeasurePreserving.id (ρ : Measure Ω)).prod hcode
  have hci := hc.integrable_comp_of_integrable hGI
  refine ⟨fun v => integrable_sections _ (fun v => Finset.prod_pos fun j _ => hw (v j)) hci v, ?_⟩
  have h1 := OracleTemplate.ZerothOrder.integral_comp_preserving hpre hGI
  have h2 := OracleTemplate.ZerothOrder.integral_comp_preserving hc hGI
  have he' (s) := congrFun he s
  dsimp only [Function.comp_apply] at he'
  simp only [he'] at h1
  rw [h1, ← h2]
  exact product_integral _ (fun v => Finset.prod_nonneg fun j _ => (hw (v j)).le) hci

open QuantileOracleLowerBound
open LongTails.Setups.QuantileSymmetricRemainderConvex

lemma atomic_observation_testing {ι Ω : Type} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace Ω] {d : ℕ}
    (ρ : ProbabilityMeasure Ω) (P Q x : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i)
    (hPs : ∑ i, P i = 1) (hQs : ∑ i, Q i = 1) (hx : Measurable x)
    (N : ℕ) (hN : N * (∑ i, (P i - Q i) ^ 2 / Q i) ≤ 1 / 8)
    (out : Ω × (ℕ → ℝ) → Space d) (hout : Measurable out)
    (hpref : ∀ a ξ ζ, (∀ n, n < N → ξ n = ζ n) → out (a, ξ) = out (a, ζ))
    {lam : ℝ} (hlam : 0 ≤ lam) (c : Space d)
    (hp : Integrable (fun s => centeredQuadratic lam c (out s)) ((ρ : Measure Ω).prod
      (Measure.infinitePi fun _ : ℕ => QuantileShellOracle.atomicMeasure P x)))
    (hq : Integrable (fun s => centeredQuadratic lam (-c) (out s)) ((ρ : Measure Ω).prod
      (Measure.infinitePi fun _ : ℕ => QuantileShellOracle.atomicMeasure Q x))) :
    lam * ‖c‖ ^ 2 / 4 ≤
      (∫ s, centeredQuadratic lam c (out s) ∂(ρ : Measure Ω).prod
        (Measure.infinitePi fun _ : ℕ => QuantileShellOracle.atomicMeasure P x)) +
      (∫ s, centeredQuadratic lam (-c) (out s) ∂(ρ : Measure Ω).prod
        (Measure.infinitePi fun _ : ℕ => QuantileShellOracle.atomicMeasure Q x)) := by
  have hm (v : Space d) : Measurable (fun s => centeredQuadratic lam v (out s)) := by
    unfold centeredQuadratic
    fun_prop
  have hplus := finite_observation_integral ρ P x hP hPs hx N _ (hm c)
    (fun a ξ ζ he => congrArg (centeredQuadratic lam c) (hpref a ξ ζ he)) hp
  have hminus := finite_observation_integral ρ Q x hQ hQs hx N _ (hm (-c))
    (fun a ξ ζ he => congrArg (centeredQuadratic lam (-c)) (hpref a ξ ζ he)) hq
  rw [hplus.2, hminus.2, ← Finset.sum_add_distrib]
  apply randomized_quadratic_testing (E := Space d) (ρ := (ρ : Measure Ω))
    (fun v : Fin N → ι => ∏ j, P (v j)) (fun v : Fin N → ι => ∏ j, Q (v j))
    (fun v => Finset.prod_nonneg fun j _ => (hP (v j)).le)
    (fun v => Finset.prod_pos fun j _ => hQ (v j))
    (by rw [product_weight_sum, hPs, one_pow])
    (by rw [product_weight_sum, hQs, one_pow]) _ hlam c
    (fun v a => out (a, prefixFill (fun j => x (v j))))
    (fun _ => hout.comp (measurable_id.prodMk measurable_const)) hplus.1 hminus.1
  rw [product_chi_square_eq P Q (fun i => (hQ i).ne') hPs hQs N]
  have hc : 0 ≤ ∑ i, (P i - Q i) ^ 2 / Q i :=
    Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hQ i).le
  have h := one_add_pow_le_linear hc N (by linarith)
  nlinarith

end LongTails.Proofs.QuantileExecutionLowerBound
