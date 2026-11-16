import LongTails.Proofs.QuasarHardHiding
import LongTails.Proofs.QuasarHardAdmissible
import LongTails.Proofs.TrajectoryExecution
import LongTails.Proofs.SmoothConvexFiniteChain
import LongTails.Proofs.SmoothConvexFiniteLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Metric Classical
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.QuasarHardFailure

open LongTails.Setups HighDimensionalConstrainedQuasar OracleTemplate
open OracleTemplate.LocalHiddenConvex QuasarCoinLaw QuasarHardAdmissible QuasarHardInstance
open QuasarHardHiding FiniteSumNondualLowerComponents FiniteSumNondualLowerAveraging

lemma hiddenPoint_norm {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) {a : ℝ} (ha : 0 ≤ a) :
    ‖hiddenPoint π a‖ = Real.sqrt ((k : ℝ) + 1) * a := by
  have h := SmoothConvexFiniteChain.hiddenPoint_norm_sq π a
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_mul (by positivity), Real.sqrt_sq ha]

lemma hardField_continuous {d k : ℕ} (L a η μ : ℝ) (hL : 0 ≤ L) (ha : 0 < a) (hη : 0 ≤ η)
    (hμ : 0 ≤ μ) (π : Fin (k + 1) ↪ Fin d) : Continuous (hardField L a η μ π) := by
  apply LipschitzWith.continuous (K := ⟨L + 600 * μ / a ^ 2, by positivity⟩)
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm, dist_eq_norm]
  exact hardField_lipschitz L a η μ hL ha hη hμ π z w

noncomputable def detGradient (p : Params) {k : ℕ} (L a η μ : ℝ) (π : Fin (k + 1) ↪ Fin p.d)
    (x : EuclideanSpace ℝ (Fin p.d)) (_ : Bool) : EuclideanSpace ℝ (Fin p.d) :=
  if ‖x - p.x0‖ ≤ p.D / 2 then hardField L a η μ π (x - p.x0) else 0

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma detGradient_measurable (p : Params) {k : ℕ} (L a η μ : ℝ) (hL : 0 ≤ L) (ha : 0 < a)
    (hη : 0 ≤ η) (hμ : 0 ≤ μ) (π : Fin (k + 1) ↪ Fin p.d) :
    Measurable (Function.uncurry (detGradient p L a η μ π)) := by
  have hc := hardField_continuous L a η μ hL ha hη hμ π
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin p.d) =>
      if ‖x - p.x0‖ ≤ p.D / 2 then hardField L a η μ π (x - p.x0) else 0) := by
    refine Measurable.ite ?_ ((hc.comp (continuous_id.sub continuous_const)).measurable)
      measurable_const
    exact measurableSet_le ((measurable_id.sub_const p.x0).norm) measurable_const
  exact hm.comp measurable_fst

noncomputable def hardInstance (p : Params) {k : ℕ} (L a η μ : ℝ) (π : Fin (k + 1) ↪ Fin p.d) :
    StochasticConstrainedQuasar.Instance p.toStochastic :=
  ballInstance p (fun x => hardObjective L a η μ π (x - p.x0)) (p.x0 + hiddenPoint π a)

noncomputable def hardOracle (p : Params) {k : ℕ} (L a η μ : ℝ) (π : Fin (k + 1) ↪ Fin p.d) :
    Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) 2 :=
  ballOracle p (le_refl 0) zero_le_one (detGradient p L a η μ π)

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma hard_admissible (p : Params) (hD : 0 < p.D) {k : ℕ} (a η μ : ℝ) (hL : 0 < p.L)
    (ha : 0 < a) (hη : 0 ≤ η) (hμ : 0 ≤ μ) (hμL : 600 * μ / a ^ 2 ≤ p.L / 2)
    (hrad : Real.sqrt ((k : ℝ) + 1) * a ≤ p.D / 2)
    (π : Fin (k + 1) ↪ Fin p.d)
    (hq : ∀ z, p.γ * hardObjective (p.L / 2) a η μ π z ≤
      ⟪hardField (p.L / 2) a η μ π z, z - hiddenPoint π a⟫) :
    spec.admissible p (hardInstance p (p.L / 2) a η μ π) (hardOracle p (p.L / 2) a η μ π) := by
  have hL2 : 0 ≤ p.L / 2 := by linarith
  apply ball_admissible p hD (le_refl 0) zero_le_one _ (fun x => hardField (p.L / 2) a η μ π (x - p.x0))
  · rw [add_sub_cancel_left, hiddenPoint_norm π ha.le]; exact hrad
  · intro x
    exact SmoothConvexFiniteLowerBound.gradient_translate p.x0 _ _
      (fun z => hardObjective_gradient (p.L / 2) a η μ ha hη π z) x
  · intro x y
    have h := hardField_lipschitz (p.L / 2) a η μ hL2 ha hη hμ π (x - p.x0) (y - p.x0)
    rw [sub_sub_sub_cancel_right] at h
    calc _ ≤ _ := h
      _ ≤ p.L * ‖x - y‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); linarith
  · intro x
    rw [add_sub_cancel_left, hardObjective_hiddenPoint _ a η μ ha hη π]
    exact hardObjective_nonneg _ a η μ hL2 hμ π _
  · intro x
    rw [add_sub_cancel_left, hardObjective_hiddenPoint _ a η μ ha hη π, sub_zero]
    have h := hq (x - p.x0)
    rw [show x - (p.x0 + hiddenPoint π a) = x - p.x0 - hiddenPoint π a by abel]
    exact h
  · exact detGradient_measurable p _ a η μ hL2 ha hη hμ π
  · intro x hx
    have hx' : ‖x - p.x0‖ ≤ p.D / 2 := by rw [← dist_eq_norm]; exact mem_closedBall.mp hx
    simp [detGradient, hx']
  · intro x hx
    have hx' : ‖x - p.x0‖ ≤ p.D / 2 := by rw [← dist_eq_norm]; exact mem_closedBall.mp hx
    simp [detGradient, hx']
    positivity

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma success_bad (p : Params) {k K : ℕ} (a η μ : ℝ) (ha : 0 < a) (hη : 0 ≤ η)
    (hη1 : η ≤ 1 / 5) (π : Fin (k + 1) ↪ Fin p.d)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d)) 2) (b : Fin 2 → ℕ) (hK : b 0 + b 1 = K)
    (hgap : ∀ (y : EuclideanSpace ℝ (Fin p.d)) (t : ℕ), t ≤ K →
      (∀ i : Fin (k + 1), t ≤ i.val → |y (π i)| ≤ a * η / 4) →
        p.ε < hardObjective (p.L / 2) a η μ π y)
    (seed : A.Seed) (ξ : ℕ → Bool)
    (hs : execute (hardOracle p (p.L / 2) a η μ π) A b seed ξ ∈ closedBall p.x0 (p.D / 2) ∧
      hardObjective (p.L / 2) a η μ π (execute (hardOracle p (p.L / 2) a η μ π) A b seed ξ - p.x0) -
        hardObjective (p.L / 2) a η μ π (p.x0 + hiddenPoint π a - p.x0) ≤ p.ε) :
    isBad ⟨p.L / 2, a, η, μ, p.D / 2, p.x0, ballProj p.x0 (p.D / 2)⟩ K (a * η / 4) π
      (fun s => A.query s) (fun s => A.output s) (fun s r => A.update s r) (A.initial seed) := by
  by_contra hgood
  set H : HardData p.d := ⟨p.L / 2, a, η, μ, p.D / 2, p.x0, ballProj p.x0 (p.D / 2)⟩ with hH
  obtain ⟨t, ht, he⟩ := execute_eq_trajectory (hardOracle p (p.L / 2) a η μ π) A b seed ξ
    (reply H π) (by
      intro history _
      generalize A.query _ = q
      obtain ⟨i, x⟩ := q
      simp only [hardOracle, ballOracle, reply, detGradient, hH])
  have htK : t ≤ K := by rw [← hK]; simpa [Fin.sum_univ_two] using ht
  have hc := simState_coupling H K (a * η / 4) π (fun s => A.query s) (fun s => A.output s)
    (fun s r => A.update s r) (A.initial seed) ha hη hη1 le_rfl hgood t htK
  rw [he] at hs
  obtain ⟨hin, hval⟩ := hs
  have hin' : ‖A.output ((fun s => A.update s (reply H π (A.query s)))^[t] (A.initial seed)) -
      p.x0‖ ≤ p.D / 2 := by rw [← dist_eq_norm]; exact mem_closedBall.mp hin
  rw [← hc] at hin' hval
  have hsm := good_output_small H K (a * η / 4) π (fun s => A.query s) (fun s => A.output s)
    (fun s r => A.update s r) (A.initial seed) hgood t htK hin'
  have hg := hgap _ t htK hsm
  rw [add_sub_cancel_left, hardObjective_hiddenPoint _ a η μ ha hη π, sub_zero] at hval
  linarith

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma exists_failure (p : Params) (hD : 0 < p.D) (hL : 0 < p.L)
    (hδ0 : 0 ≤ p.δ) (hδ : p.δ < 3 / 4) {k K : ℕ} (hKk : K ≤ k + 1)
    (a η μ Dc : ℝ) (ha : 0 < a) (hη : 0 < η) (hη1 : η ≤ 1 / 5) (hμ : 0 ≤ μ)
    (hμL : 600 * μ / a ^ 2 ≤ p.L / 2) (hrad : Real.sqrt ((k : ℝ) + 1) * a ≤ p.D / 2)
    (hDc : 0 < Dc) (hDs : Dc + (k + 1 : ℕ) ≤ p.d)
    (hsize : 8 * ((K : ℝ) + 1) * (k + 1 : ℕ) * ((p.D / 2) ^ 2 / (a * η / 4) ^ 2) ≤ Dc)
    (hq : ∀ (π : Fin (k + 1) ↪ Fin p.d) z, p.γ * hardObjective (p.L / 2) a η μ π z ≤
      ⟪hardField (p.L / 2) a η μ π z, z - hiddenPoint π a⟫)
    (hgap : ∀ (π : Fin (k + 1) ↪ Fin p.d) (y : EuclideanSpace ℝ (Fin p.d)) (t : ℕ), t ≤ K →
      (∀ i : Fin (k + 1), t ≤ i.val → |y (π i)| ≤ a * η / 4) →
        p.ε < hardObjective (p.L / 2) a η μ π y)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d)) 2) (b : Fin 2 → ℕ) (hK : b 0 + b 1 = K) :
    ∃ (I : spec.Instance (spec.publicInput p))
      (O : Oracle (spec.Query (spec.publicInput p)) (spec.Reply (spec.publicInput p)) spec.numOracles),
      spec.admissible p I O ∧
        ¬ spec.successful p I (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
            execute O A b seed.1 seed.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  by_contra hcon
  push Not at hcon
  have hθ : 0 < a * η / 4 := by positivity
  let W := CoordinateWords p.d k
  let π := fun w : W => coordinateEmbedding w
  let H : HardData p.d := ⟨p.L / 2, a, η, μ, p.D / 2, p.x0, ballProj p.x0 (p.D / 2)⟩
  let Pm : Measure (A.Seed × (ℕ → Bool)) :=
    (A.law : Measure A.Seed).prod ((coinPath 0 (le_refl 0) zero_le_one : ProbabilityMeasure (ℕ → Bool)) :
      Measure (ℕ → Bool))
  have : IsProbabilityMeasure Pm := by dsimp [Pm]; infer_instance
  let out := fun (w : W) (ω : A.Seed × (ℕ → Bool)) =>
    execute (hardOracle p (p.L / 2) a η μ (π w)) A b ω.1 ω.2
  let S := fun w : W => {ω : A.Seed × (ℕ → Bool) | out w ω ∈ closedBall p.x0 (p.D / 2) ∧
    hardObjective (p.L / 2) a η μ (π w) (out w ω - p.x0) -
      hardObjective (p.L / 2) a η μ (π w) (p.x0 + hiddenPoint (π w) a - p.x0) ≤ p.ε}
  have hsucc (w : W) := hcon (hardInstance p (p.L / 2) a η μ (π w))
    (hardOracle p (p.L / 2) a η μ (π w))
    (hard_admissible p hD a η μ hL ha hη.le hμ hμL hrad (π w) (hq (π w)))
  have hmeasS (w : W) : MeasurableSet (S w) := by
    obtain ⟨hm, _⟩ := hsucc w
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin p.d) =>
        hardObjective (p.L / 2) a η μ (π w) (x - p.x0)) := by
      have hd : Differentiable ℝ (hardObjective (p.L / 2) a η μ (π w)) := fun z =>
        (hardObjective_gradient (p.L / 2) a η μ ha hη.le (π w) z).hasFDerivAt.differentiableAt
      exact hd.continuous.comp (continuous_id.sub continuous_const)
    have hm' : Measurable (out w) := hm
    exact (measurableSet_closedBall.preimage hm').inter
      (measurableSet_le ((hcont.measurable.comp hm').sub_const _) measurable_const)
  have hprob (w : W) : ENNReal.ofReal (1 - p.δ) ≤ Pm (S w) := by
    obtain ⟨_, hfail⟩ := hsucc w
    have hc : Pm (S w)ᶜ ≤ ENNReal.ofReal p.δ := hfail
    have hsum := measure_add_measure_compl (μ := Pm) (hmeasS w)
    rw [measure_univ] at hsum
    have hfin : Pm (S w)ᶜ ≠ ⊤ := measure_ne_top _ _
    have : Pm (S w) = 1 - Pm (S w)ᶜ := by
      rw [← hsum, ENNReal.add_sub_cancel_right hfin]
    rw [this, ENNReal.ofReal_sub _ hδ0, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hc 1
  have hpoint (ω : A.Seed × (ℕ → Bool)) :
      4 * (∑ w : W, (S w).indicator (1 : A.Seed × (ℕ → Bool) → ENNReal) ω) ≤ (Fintype.card W : ENNReal) := by
    have hle : (∑ w : W, (S w).indicator (1 : A.Seed × (ℕ → Bool) → ENNReal) ω) ≤
        ∑ w : W, if isBad H K (a * η / 4) (π w) (fun s => A.query s) (fun s => A.output s)
          (fun s r => A.update s r) (A.initial ω.1) then (1 : ENNReal) else 0 := by
      apply Finset.sum_le_sum
      intro w _
      by_cases hw : ω ∈ S w
      · rw [Set.indicator_of_mem hw]
        have hb := success_bad p a η μ ha hη.le hη1 (π w) A b hK (hgap (π w)) ω.1 ω.2 hw
        split_ifs with hc
        · simp
        · exact absurd hb hc
      · rw [Set.indicator_of_notMem hw]; simp
    have hcount := bad_count H K (a * η / 4) Dc (by simp [H]; linarith) hθ hDc.le hDs hKk
      (fun s => A.query s) (fun s => A.output s) (fun s r => A.update s r) (A.initial ω.1)
    set N := (Finset.univ.filter (fun w : W => isBad H K (a * η / 4) (π w) (fun s => A.query s)
      (fun s => A.output s) (fun s r => A.update s r) (A.initial ω.1))).card with hN
    have hsumN : (∑ w : W, if isBad H K (a * η / 4) (π w) (fun s => A.query s)
        (fun s => A.output s) (fun s r => A.update s r) (A.initial ω.1) then (1 : ℝ) else 0) =
        (N : ℝ) := by rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]; simp [hN]
    have hsumNe : (∑ w : W, if isBad H K (a * η / 4) (π w) (fun s => A.query s)
        (fun s => A.output s) (fun s r => A.update s r) (A.initial ω.1) then (1 : ENNReal) else 0) =
        (N : ENNReal) := by rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]; simp [hN]
    rw [hsumN] at hcount
    have hρ : H.ρ = p.D / 2 := rfl
    rw [hρ] at hcount
    have hcard : (0 : ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
    have h4 : 4 * (N : ℝ) ≤ Fintype.card W := by
      have hmul := mul_le_mul_of_nonneg_right hsize hcard
      nlinarith [hcount]
    have h4n : 4 * N ≤ Fintype.card W := by exact_mod_cast h4
    calc 4 * (∑ w : W, (S w).indicator (1 : A.Seed × (ℕ → Bool) → ENNReal) ω) ≤ 4 * (N : ENNReal) := by
          rw [← hsumNe]; gcongr
      _ ≤ _ := by exact_mod_cast h4n
  have hint : 4 * (∑ w : W, Pm (S w)) ≤ (Fintype.card W : ENNReal) := by
    have he : (∑ w : W, Pm (S w)) = ∫⁻ ω, ∑ w : W, (S w).indicator (1 : A.Seed × (ℕ → Bool) → ENNReal) ω ∂Pm := by
      rw [lintegral_finsetSum _ (fun w _ => (measurable_one.indicator (hmeasS w)))]
      apply Finset.sum_congr rfl
      intro w _
      rw [lintegral_indicator_one (hmeasS w)]
    rw [he, ← lintegral_const_mul _ (Finset.measurable_sum _ (fun w _ =>
      measurable_one.indicator (hmeasS w)))]
    calc _ ≤ ∫⁻ _, (Fintype.card W : ENNReal) ∂Pm := lintegral_mono hpoint
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  have hlow : (Fintype.card W : ENNReal) * ENNReal.ofReal (1 - p.δ) ≤ ∑ w : W, Pm (S w) := by
    calc _ = ∑ _ : W, ENNReal.ofReal (1 - p.δ) := by simp [Finset.card_univ]
      _ ≤ _ := Finset.sum_le_sum (fun w _ => hprob w)
  have hW : 0 < Fintype.card W := FiniteSumNondualLowerBound.coordinateWords_card_pos p.d k (by
    have : ((k + 1 : ℕ) : ℝ) ≤ p.d := by linarith
    exact_mod_cast this)
  have hfin : 4 * ((Fintype.card W : ENNReal) * ENNReal.ofReal (1 - p.δ)) ≤
      4 * (∑ w : W, Pm (S w)) := by gcongr
  have htot := hfin.trans hint
  have hreal : 4 * ((Fintype.card W : ℝ) * (1 - p.δ)) ≤ Fintype.card W := by
    have h1 : (4 : ENNReal) * ((Fintype.card W : ENNReal) * ENNReal.ofReal (1 - p.δ)) =
        ENNReal.ofReal (4 * ((Fintype.card W : ℝ) * (1 - p.δ))) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp
    rw [h1] at htot
    have h2 := (ENNReal.ofReal_le_iff_le_toReal (by simp)).mp htot
    simpa using h2
  have hWpos : (0 : ℝ) < Fintype.card W := by exact_mod_cast hW
  nlinarith

end LongTails.Proofs.QuasarHardFailure
