import LongTails.Proofs.MultiplicativeAccelerationTuning
import LongTails.Proofs.MultiplicativeAccelerationExecution
import LongTails.Proofs.MultiplicativeAccelerationStochastic
import LongTails.Setups.HeavyTailedStrongGrowthConvex

open MeasureTheory Set
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

namespace OracleTemplate.SplitRobustAcceleration

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma measurable_sampled_estimate {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (Λ : ℝ) (k b : ℕ) :
    Measurable (fun w : E × (Fin (k+2) → Fin (b+1) → Ω) =>
      MultiplicativeRobustEstimator.estimate Λ (fun i j => g w.1 (w.2 i j))) :=
  (MultiplicativeRobustEstimator.measurable_estimate Λ).comp
    (Measurable.of_eval (fun i => Measurable.of_eval (fun j =>
      hg.comp (measurable_fst.prodMk
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd))))))

lemma output_rate {f : E → ℝ} {g : E → Ω → E} {L V α Λ : ℝ}
    (hL : 0 < L) (hV : 0 < V) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hgm : Measurable (Function.uncurry g))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ProbabilityMeasure (ℕ → Ω))
    (hIID : IID (fun t (ξ : ℕ → Ω) => ξ t) μ (P : Measure _))
    (k b N : ℕ) (hN : 0 < N) (u x0 : E) (hm : IsMinOn f univ u)
    (hest : ∀ y,
      let Q := Measure.pi (fun _ : Fin (k+2) => Measure.pi fun _ : Fin (b+1) => μ)
      let e := fun ξ : Fin (k+2) → Fin (b+1) → Ω =>
        MultiplicativeRobustEstimator.estimate Λ (fun i j => g y (ξ i j))
      Integrable (fun ξ => (e ξ).2) Q ∧
      Integrable (fun ξ => ‖(e ξ).1-gradient f y‖^2) Q ∧
      Integrable (fun ξ => ‖(e ξ).2‖^2) Q ∧
      (∫ ξ, ‖(e ξ).1-gradient f y‖^2 ∂Q) ≤ ‖gradient f y‖^2/64 ∧
      (∫ ξ, ‖(e ξ).2‖^2 ∂Q) ≤ V*‖gradient f y‖^2 ∧
      ‖(∫ ξ, (e ξ).2 ∂Q)-gradient f y‖ ≤ α*‖gradient f y‖) :
    let O : Oracle E E := {Seed := fun _ => Ω, law := P, answer := fun _ (_,x) ω => g x ω}
    Measurable (output O L V Λ k b N x0) ∧
    Integrable (fun ξ => f (output O L V Λ k b N x0 ξ)-f u) (P : Measure _) ∧
    (∫ ξ, f (output O L V Λ k b N x0 ξ)-f u ∂(P : Measure _)) ≤
      (1+α^2/(2*V))^N*‖x0-u‖^2/(2*weight L V N) := by
  let Q := Measure.pi (fun _ : Fin (k+2) => Measure.pi fun _ : Fin (b+1) => μ)
  let G := fun x (ω : Fin (k+2) → Fin (b+1) → Ω) =>
    MultiplicativeRobustEstimator.estimate Λ (fun i j => g x (ω i j))
  have hG : Measurable (Function.uncurry G) := measurable_sampled_estimate hgm Λ k b
  have hf : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hg x).continuousAt)).measurable
  have hstep := energy_step (P := Q) hL hV hc hg hlip hG
    (fun y => (hest y).1) (fun y => (hest y).2.1) (fun y => (hest y).2.2.1)
    (fun y => (hest y).2.2.2.1) (fun y => (hest y).2.2.2.2.1)
    (fun y => (hest y).2.2.2.2.2)
  have henergy := integrate_energy_recursion (P := Q) hL hV (by positivity) hf hG u hm
    (fun n x z => hstep x z u hm n) N 0 x0 x0
  simp only [Nat.zero_add] at henergy
  have he : energy f L V u 0 (x0,x0) = ‖x0-u‖^2/2 := by simp [energy, weight]
  have hbound : (∫ ξ, energy f L V u N (run G L V N 0 x0 x0 ξ)
      ∂Measure.pi fun _ : Fin N => Q) ≤ (1+α^2/(2*V))^N*‖x0-u‖^2/2 := by
    simpa only [he, mul_div_assoc] using henergy.2
  have hrate := objective_from_energy (P := Q) hL hV hf hG u x0 hm N hN henergy.1 hbound
  have hs := matrix_samples_law μ (P : Measure _) hIID k b N
  let samples := fun ξ : ℕ → Ω => fun t : Fin N => fun i : Fin (k+2) => fun j : Fin (b+1) =>
    ξ (t.val*((k+2)*(b+1))+(finProdFinEquiv (i,j)).val)
  have hl : ProbabilityTheory.HasLaw samples (Measure.pi fun _ : Fin N => Q) (P : Measure _) :=
    ⟨hs.measurable.aemeasurable,hs.map_eq⟩
  have hrun : Measurable (fun ξ : Fin N → Fin (k+2) → Fin (b+1) → Ω => (run G L V N 0 x0 x0 ξ).1) :=
    (((measurable_run hG L V N 0).comp
      (measurable_const.prodMk measurable_id :
        Measurable (fun ξ : Fin N → Fin (k+2) → Fin (b+1) → Ω => ((x0,x0),ξ)))).fst)
  have hout : output {Seed := fun _ => Ω, law := P, answer := fun _ (_,x) ω => g x ω}
      L V Λ k b N x0 = fun ξ => (run G L V N 0 x0 x0 (samples ξ)).1 :=
    funext (execute_method P g L V Λ k b N x0)
  dsimp only
  rw [hout]
  refine ⟨hrun.comp hs.measurable, hl.integrable_comp hrate.1, ?_⟩
  calc
    _ = ∫ ξ, f (run G L V N 0 x0 x0 ξ).1-f u ∂Measure.pi fun _ : Fin N => Q :=
      hl.integral_comp hrate.1.aestronglyMeasurable
    _ ≤ _ := hrate.2

lemma raw_output_rate {f : E → ℝ} {g : E → Ω → E} {L Λ p ρ : ℝ}
    (hL : 0 < L) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ProbabilityMeasure (ℕ → Ω))
    (hIID : IID (fun t (ξ : ℕ → Ω) => ξ t) μ (P : Measure _))
    (ho : LongTails.Setups.HeavyTailedStrongGrowthConvex.IsRelativeMomentOracle μ f g p ρ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hΛ : 1 ≤ Λ)
    (k b N : ℕ) (hN : 0 < N) (u x0 : E) (hm : IsMinOn f univ u)
    (hk : 8 ≤ k+1) (hb : 4*65536^p*ρ ≤ (b+1 : ℝ)^(p-1))
    (hprob : (1/2 : ℝ)^(k+1) ≤ Λ^(1-p)/64) :
    let V := 32*Λ^(2-p)
    let α := Λ^(1-p)/16
    let O : Oracle E E := {Seed := fun _ => Ω, law := P, answer := fun _ (_,x) ω => g x ω}
    Measurable (output O L V Λ k b N x0) ∧
    Integrable (fun ξ => f (output O L V Λ k b N x0 ξ)-f u) (P : Measure _) ∧
    (∫ ξ, f (output O L V Λ k b N x0 ξ)-f u ∂(P : Measure _)) ≤
      (1+α^2/(2*V))^N*‖x0-u‖^2/(2*weight L V N) := by
  apply output_rate hL (by positivity) hc hg hlip ho.measurable μ P hIID k b N hN u x0 hm
  intro y
  exact MultiplicativeRobustEstimator.batched_estimator_moments
    (ho.measurable.comp (measurable_const.prodMk measurable_id)) (gradient f y)
    hp hp2 hΛ (ho.integrable y) (ho.unbiased y) (ho.moment_integrable y) (ho.moment y)
    k b hk hb hprob

lemma exact_output_rate {f : E → ℝ} {g : E → Ω → E} {L p : ℝ}
    (hL : 0 < L) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ProbabilityMeasure (ℕ → Ω))
    (hIID : IID (fun t (ξ : ℕ → Ω) => ξ t) μ (P : Measure _))
    (ho : LongTails.Setups.HeavyTailedStrongGrowthConvex.IsRelativeMomentOracle μ f g p 0)
    (hp : 0 < p) (N : ℕ) (hN : 0 < N) (u x0 : E) (hm : IsMinOn f univ u) :
    let O : Oracle E E := {Seed := fun _ => Ω, law := P, answer := fun _ (_,x) ω => g x ω}
    Measurable (output O L 32 1 128 0 N x0) ∧
    Integrable (fun ξ => f (output O L 32 1 128 0 N x0 ξ)-f u) (P : Measure _) ∧
    (∫ ξ, f (output O L 32 1 128 0 N x0 ξ)-f u ∂(P : Measure _)) ≤
      ‖x0-u‖^2/(2*weight L 32 N) := by
  have hh := output_rate (α := 0) (Λ := 1) hL (by norm_num : (0:ℝ) < 32) hc hg hlip
    ho.measurable μ P hIID 128 0 N hN u x0 hm
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_div, add_zero, one_pow, one_mul] at hh
  apply hh
  intro y
  have he := MultiplicativeRobustEstimator.exact_estimate_moments (gradient f y)
    (MultiplicativeRobustEstimator.ae_eq_of_zero_power (gradient f y) hp.ne'
      (ho.moment_integrable y) (by simpa only [zero_mul] using ho.moment y))
    (by norm_num : (1:ℝ) ≤ 1) 128 0
  refine ⟨he.1, he.2.1, he.2.2.1, ?_, ?_, ?_⟩
  · rw [he.2.2.2.2.1]
    positivity
  · rw [he.2.2.2.2.2]
    nlinarith [sq_nonneg ‖gradient f y‖]
  · rw [he.2.2.2.1]
    simp

open LongTails.Setups.HeavyTailedStrongGrowthConvex
open LongTails.Proofs.MultiplicativeAccelerationTuning

lemma lastIterate_accuracy (q : LongTails.Setups.HeavyTailedStrongGrowthConvex.Params) (hL : 0 < q.L) (hR : 0 ≤ q.R)
    (hρ : 0 ≤ q.ρ) (hp : 1 < q.p) (hp2 : q.p ≤ 2) (hε : 0 < q.ε)
    {f : q.E → ℝ} {g : q.E → q.Ω → q.E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ q.L*‖x-y‖)
    (μ : Measure q.Ω) [IsProbabilityMeasure μ] (P : ProbabilityMeasure (ℕ → q.Ω))
    (hIID : IID (fun t (ξ : ℕ → q.Ω) => ξ t) μ (P : Measure _))
    (ho : IsRelativeMomentOracle μ f g q.p q.ρ)
    (u : q.E) (hm : IsMinOn f univ u) (hinit : ‖q.x0-u‖ ≤ q.R) :
    let O : Oracle q.E q.E := {Seed := fun _ => q.Ω, law := P, answer := fun _ (_,x) ω => g x ω}
    Measurable (lastIterate q O) ∧
    Integrable (fun ξ => f (lastIterate q O ξ)-f u) (P : Measure _) ∧
    (∫ ξ, f (lastIterate q O ξ)-f u ∂(P : Measure _)) ≤ q.ε := by
  have hH : 1 ≤ scale q := le_max_left _ _
  have hT : q.L*q.R^2/q.ε ≤ scale q := le_max_right _ _
  have hHp : 0 < scale q := by linarith
  by_cases hz : q.ρ = 0
  · have hb : batchExtra q = 0 := by
      simp [batchExtra, hz, Real.zero_rpow (by exact inv_ne_zero (by linarith : q.p-1 ≠ 0) : (q.p-1)⁻¹ ≠ 0)]
    have hn : 0 < ⌈128*Real.sqrt (scale q)⌉₊ := Nat.ceil_pos.mpr (by positivity)
    have hh := exact_output_rate hL hc hg hlip μ P hIID (hz ▸ ho)
      (by linarith : 0 < q.p) _ hn u q.x0 hm
    dsimp only
    unfold lastIterate
    simp only [variance, clippingScale, pilotCount, iterations, hz, ite_true,
      Real.one_rpow, mul_one, hb]
    refine ⟨hh.1, hh.2.1, hh.2.2.trans ?_⟩
    have hs := deterministic_square_bound hH
    have hn2 : 64*q.L*32*q.R^2/q.ε ≤ (⌈128*Real.sqrt (scale q)⌉₊ : ℝ)^2 := by
      simp only [div_eq_mul_inv] at hT ⊢
      nlinarith [hT]
    have ha := accuracy_algebra hL (by norm_num : (0:ℝ) < 32) hR hε
      (norm_nonneg (q.x0-u)) hinit hn hn2
    change ‖q.x0-u‖^2/(2*((⌈128*Real.sqrt (scale q)⌉₊ : ℝ)*
      (⌈128*Real.sqrt (scale q)⌉₊+1)/(64*q.L*32))) ≤ q.ε
    apply le_trans _ ha
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg ‖q.x0-u‖]
  · have hΛ : 1 ≤ (scale q)^(1/(3*q.p-2)) := Real.one_le_rpow hH (by apply div_nonneg (by norm_num); linarith)
    have hV : 0 < 32*((scale q)^(1/(3*q.p-2)))^(2-q.p) := by positivity
    have hn : 0 < ⌈128*(scale q)^(q.p/(3*q.p-2))⌉₊ := Nat.ceil_pos.mpr (by positivity)
    have hh := raw_output_rate hL hc hg hlip μ P hIID ho hp.le hp2 hΛ
      (128+⌈2*Real.log (scale q)⌉₊) (batchExtra q) _ hn u q.x0 hm
      (by omega) (by simpa [batchExtra] using batch_normalization hp hp2 hρ)
      (pilot_failure_bound hp hH)
    dsimp only
    unfold lastIterate
    simp only [variance, clippingScale, pilotCount, iterations, hz, ite_false]
    refine ⟨hh.1, hh.2.1, hh.2.2.trans ?_⟩
    have hs := iteration_square_bound hp hH
    have hmT := mul_le_mul_of_nonneg_left hT hV.le
    have hn2 : 64*q.L*(32*((scale q)^(1/(3*q.p-2)))^(2-q.p))*q.R^2/q.ε ≤
        (⌈128*(scale q)^(q.p/(3*q.p-2))⌉₊ : ℝ)^2 := by
      calc
        _ = 64*((32*((scale q)^(1/(3*q.p-2)))^(2-q.p))*(q.L*q.R^2/q.ε)) := by ring
        _ ≤ 64*((32*((scale q)^(1/(3*q.p-2)))^(2-q.p))*scale q) :=
          mul_le_mul_of_nonneg_left hmT (by norm_num)
        _ ≤ _ := by nlinarith only [hs, mul_nonneg hV.le hHp.le]
    have ha := accuracy_algebra hL hV hR hε (norm_nonneg (q.x0-u)) hinit hn hn2
    apply le_trans _ ha
    apply div_le_div_of_nonneg_right _ (by unfold weight; positivity)
    exact mul_le_mul_of_nonneg_right (bias_growth_bound hp hH) (sq_nonneg _)

end OracleTemplate.SplitRobustAcceleration
