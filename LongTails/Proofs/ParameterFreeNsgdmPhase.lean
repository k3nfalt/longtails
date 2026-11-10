import LongTails.Proofs.ParameterFreeNsgdmExecution
import LongTails.Proofs.ParameterFreeNsgdmGrid
import LongTails.Proofs.AdaptiveIID

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ParameterFreeNsgdmPhase

open OracleTemplate
open LongTails.Setups.ParameterFreeHeavyTailedSmooth
open LongTails.Algorithms.ParameterFreeNsgdm
open ParameterFreeNsgdmRun ParameterFreeNsgdmRunBound ParameterFreeNsgdmSelection
open ParameterFreeNsgdmExecution ParameterFreeNsgdmGrid

variable {d : Public} {Ω : Type} [MeasurableSpace Ω]

lemma selected_le_root_nat {C : ℕ} {p : ℝ} (hp : 1 ≤ p) (y est : ℕ → d.E) (grad : d.E → d.E)
    {sel c : ℕ} (hselC : sel < C) (hsel : ‖est sel‖ ≤ ‖est c‖) :
    ‖grad (y sel)‖ ≤ ‖grad (y c)‖ + ‖est c - grad (y c)‖ +
      (∑ c' ∈ Finset.range C, ‖est c' - grad (y c')‖ ^ p) ^ (1 / p) := by
  have h1 : ‖grad (y sel)‖ ≤ ‖est sel‖ + ‖est sel - grad (y sel)‖ := by
    have := norm_sub_le (est sel) (est sel - grad (y sel))
    simpa using this
  have h2 : ‖est c‖ ≤ ‖grad (y c)‖ + ‖est c - grad (y c)‖ := by
    have := norm_add_le (grad (y c)) (est c - grad (y c))
    simpa using this
  have hp0 : 0 < p := by linarith
  have h3 : ‖est sel - grad (y sel)‖ ≤
      (∑ c' ∈ Finset.range C, ‖est c' - grad (y c')‖ ^ p) ^ (1 / p) := by
    have hle : ‖est sel - grad (y sel)‖ ^ p ≤ ∑ c' ∈ Finset.range C, ‖est c' - grad (y c')‖ ^ p :=
      Finset.single_le_sum (f := fun c' => ‖est c' - grad (y c')‖ ^ p)
        (fun c' _ => Real.rpow_nonneg (norm_nonneg _) p) (Finset.mem_range.mpr hselC)
    calc ‖est sel - grad (y sel)‖ = (‖est sel - grad (y sel)‖ ^ p) ^ (1 / p) := by
          rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hp0.ne', Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) p) hle (by positivity)
  linarith

omit [MeasurableSpace Ω] in
lemma phase_pointwise {p : ℝ} (hp : 1 ≤ p) (g : d.E → Ω → d.E) (grad : d.E → d.E) (s : Seed)
    (k a : ℕ) (ξ : ℕ → Ω) {c : ℕ} (hc : c < candidates k) :
    ‖grad (phaseOutput g s k a ξ)‖ ≤
      ‖grad (phaseSelection g s k a ξ c)‖ +
      ‖batchMean g (horizon k) (a + candidates k * horizon k + c * horizon k)
        (phaseSelection g s k a ξ c) ξ - grad (phaseSelection g s k a ξ c)‖ +
      (∑ c' ∈ Finset.range (candidates k),
        ‖batchMean g (horizon k) (a + candidates k * horizon k + c' * horizon k)
          (phaseSelection g s k a ξ c') ξ - grad (phaseSelection g s k a ξ c')‖ ^ p) ^ (1 / p) := by
  obtain ⟨c₀, hc₀, hb, hn, hmin⟩ := select_spec (phaseEstimates g s k a ξ) (phaseSelection g s k a ξ)
    (candidates k - 1)
  have hC := candidates_pos k
  unfold phaseOutput
  rw [hb]
  have hsel := hmin c (by omega)
  simp only [phaseEstimates, estimate] at hsel
  exact selected_le_root_nat hp (phaseSelection g s k a ξ)
    (fun c' => batchMean g (horizon k) (a + candidates k * horizon k + c' * horizon k)
      (phaseSelection g s k a ξ c') ξ) grad (by omega) hsel


lemma uniform_integral_fin {n : ℕ} [NeZero n] (h : Fin n → ℝ) :
    ∫ j, h j ∂(PMF.uniformOfFintype (Fin n)).toMeasure = (∑ j, h j) / n := by
  rw [integral_fintype (μ := (PMF.uniformOfFintype (Fin n)).toMeasure) (f := h) Integrable.of_finite]
  have hj : ∀ j : Fin n, ((PMF.uniformOfFintype (Fin n)).toMeasure).real {j} = 1 / n := by
    intro j
    rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton j),
      PMF.uniformOfFintype_apply, Fintype.card_fin]
    simp
  simp only [hj, smul_eq_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma seed_coordinate_preserving (k : ℕ) {c : ℕ} (hc : c < candidates k) :
    MeasurePreserving (fun s : Seed => s k ⟨c, hc⟩) seedLaw
      (PMF.uniformOfFintype (Fin (horizon k))).toMeasure := by
  unfold seedLaw
  exact (MeasureTheory.measurePreserving_eval
    (fun _ : Fin (candidates k) => (PMF.uniformOfFintype (Fin (horizon k))).toMeasure) ⟨c, hc⟩).comp
    (measurePreserving_eval_infinitePi
      (fun k => Measure.pi fun _ : Fin (candidates k) => (PMF.uniformOfFintype (Fin (horizon k))).toMeasure) k)

lemma chosen_eq (s : Seed) (k : ℕ) {c : ℕ} (hc : c < candidates k) :
    chosen s k c = (s k ⟨c, hc⟩).val := by
  simp [chosen, hc]

variable {ν : Measure Ω} [IsProbabilityMeasure ν] {g : d.E → Ω → d.E} {σ p L : ℝ}

lemma run_measurable_pair (hg : Measurable (Function.uncurry g)) (α η : ℝ) (x0 : d.E) :
    Measurable (fun z : (ℕ → Ω) × ℕ => run α η g x0 z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro t
  exact run_measurable hg α η x0 t


lemma chosen_measurable (k c : ℕ) : Measurable (fun s : Seed => chosen s k c) := by
  unfold chosen
  split_ifs with h
  · exact (measurable_of_countable Fin.val).comp
      ((measurable_pi_apply (⟨c, h⟩ : Fin (candidates k))).comp (measurable_pi_apply k))
  · exact measurable_const

lemma phaseSelection_measurable (hg : Measurable (Function.uncurry g)) (k a c : ℕ) :
    Measurable (fun z : Seed × (ℕ → Ω) => phaseSelection g z.1 k a z.2 c) := by
  unfold phaseSelection
  split_ifs with hc
  · unfold phaseCands runPoint
    have hshift : Measurable (fun z : Seed × (ℕ → Ω) => fun n => z.2 (a + c * horizon k + n)) := by
      fun_prop
    exact measurable_fst.comp ((run_measurable_pair hg (momentum k c)
      (stepSize k c) d.x0).comp (hshift.prodMk ((chosen_measurable k c).comp measurable_fst)))
  · exact measurable_const

omit [MeasurableSpace Ω] in
lemma phaseSelection_eq_run (s : Seed) (k a : ℕ) (ξ : ℕ → Ω) {c : ℕ} (hc : c < candidates k) :
    phaseSelection g s k a ξ c =
      (run (momentum k c) (stepSize k c) g d.x0 (fun n => ξ (a + c * horizon k + n))
        (s k ⟨c, hc⟩).val).1 := by
  simp [phaseSelection, hc, phaseCands, runPoint, chosen_eq s k hc]

lemma candidate_expectation {f : d.E → ℝ} (hO : Oracle ν g (gradient f) σ p)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L)
    {lower Δ : ℝ} (hlow : ∀ x, lower ≤ f x) (hΔ : f d.x0 - lower ≤ Δ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (k a : ℕ) {c : ℕ} (hc : c < candidates k)
    (hα0 : 0 < momentum k c) (hα1 : momentum k c ≤ 1) (hη : 0 < stepSize k c) :
    Integrable (fun z : Seed × (ℕ → Ω) => ‖gradient f (phaseSelection g z.1 k a z.2 c)‖)
      (seedLaw.prod (Measure.infinitePi fun _ : ℕ => ν)) ∧
    (∫ z, ‖gradient f (phaseSelection g z.1 k a z.2 c)‖
        ∂seedLaw.prod (Measure.infinitePi fun _ : ℕ => ν)) ≤
      (Δ / stepSize k c + 12 * σ / momentum k c +
        12 * σ * (horizon k) * momentum k c ^ ((p - 1) / p) +
        (horizon k) * (2 * L * stepSize k c * (1 - momentum k c) / momentum k c +
          L / 2 * stepSize k c)) / horizon k := by
  set α := momentum k c
  set η := stepSize k c
  set T := horizon k
  have : NeZero T := ⟨Nat.pos_iff_ne_zero.mp (by show 0 < horizon k; unfold horizon; positivity)⟩
  have hgrad : Measurable (gradient f) := grad_measurable hlip hL
  let F : Fin T × (ℕ → Ω) → ℝ := fun w => ‖gradient f (run α η g d.x0 w.2 w.1.val).1‖
  let Φ : Seed × (ℕ → Ω) → Fin T × (ℕ → Ω) :=
    fun z => (z.1 k ⟨c, hc⟩, fun n => z.2 (a + c * T + n))
  have hΦ : MeasurePreserving Φ (seedLaw.prod (Measure.infinitePi fun _ : ℕ => ν))
      ((PMF.uniformOfFintype (Fin T)).toMeasure.prod (Measure.infinitePi fun _ : ℕ => ν)) :=
    (seed_coordinate_preserving k hc).prod (shift_preserving (ν := ν) (a + c * T))
  have hFmeas : Measurable F := by
    have h1 : Measurable (fun w : (ℕ → Ω) × Fin T => ‖gradient f (run α η g d.x0 w.1 w.2.val).1‖) :=
      (hgrad.comp (measurable_fst.comp ((run_measurable_pair
        hO.measurable α η d.x0).comp (measurable_fst.prodMk
          ((measurable_of_countable Fin.val).comp measurable_snd))))).norm
    exact h1.comp measurable_swap
  have hFbound : ∀ w, ‖F w‖ ≤ ‖gradient f d.x0‖ + L * (T * η) := by
    intro w
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have := run_grad_bound hlip hL (α := α) hη.le g d.x0 w.2 w.1.val
    have hT : (w.1.val : ℝ) ≤ T := by exact_mod_cast w.1.isLt.le
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT hη.le) hL]
  have hFint : Integrable F ((PMF.uniformOfFintype (Fin T)).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => ν)) :=
    Integrable.of_bound hFmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hFbound)
  have heq : (fun z : Seed × (ℕ → Ω) => ‖gradient f (phaseSelection g z.1 k a z.2 c)‖) = F ∘ Φ := by
    funext z
    simp only [Function.comp_apply, F, Φ]
    rw [phaseSelection_eq_run z.1 k a z.2 hc]
  rw [heq]
  refine ⟨hΦ.integrable_comp_of_integrable hFint, ?_⟩
  have hmap := integral_map (μ := seedLaw.prod (Measure.infinitePi fun _ : ℕ => ν))
    hΦ.measurable.aemeasurable hFmeas.aestronglyMeasurable
  rw [hΦ.map_eq] at hmap
  rw [show (∫ z, (F ∘ Φ) z ∂seedLaw.prod (Measure.infinitePi fun _ : ℕ => ν)) =
    ∫ z, F (Φ z) ∂seedLaw.prod (Measure.infinitePi fun _ : ℕ => ν) from rfl, ← hmap,
    integral_prod F hFint]
  have hrun := run_average_expectation hO hg hlip hL hlow hΔ hp hp2 hσ hα0 hα1 hη (x0 := d.x0) T
  have hinner : ∀ τ : Fin T, (∫ ζ, F (τ, ζ) ∂Measure.infinitePi (fun _ : ℕ => ν)) =
      ∫ ζ, ‖gradient f (run α η g d.x0 ζ τ.val).1‖ ∂Measure.infinitePi (fun _ : ℕ => ν) :=
    fun τ => rfl
  simp only [hinner]
  rw [uniform_integral_fin (fun τ : Fin T => ∫ ζ, ‖gradient f (run α η g d.x0 ζ τ.val).1‖
    ∂Measure.infinitePi (fun _ : ℕ => ν))]
  have hT0 : (0 : ℝ) < T := by
    exact_mod_cast (show 0 < horizon k by unfold horizon; positivity)
  apply div_le_div_of_nonneg_right _ hT0.le
  have hsum : ∑ τ : Fin T, (∫ ζ, ‖gradient f (run α η g d.x0 ζ τ.val).1‖
      ∂Measure.infinitePi (fun _ : ℕ => ν)) =
      ∑ t ∈ Finset.range T, (∫ ζ, ‖gradient f (run α η g d.x0 ζ t).1‖
        ∂Measure.infinitePi (fun _ : ℕ => ν)) := by
    rw [← Fin.sum_univ_eq_sum_range]
  rw [hsum, ← integral_finsetSum _ (fun t _ =>
    run_grad_integrable hO hgrad hlip hL (α := α) hη.le d.x0 t)]
  exact hrun.2


omit [MeasurableSpace Ω] in
lemma run_congr_prefix (α η : ℝ) (x0 : d.E) {ξ ξ' : ℕ → Ω} (t : ℕ)
    (h : ∀ i < t, ξ i = ξ' i) : run α η g x0 ξ t = run α η g x0 ξ' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [run]
      rw [ih (fun i hi => h i (by omega)), h t (by omega)]

lemma horizon_pos (k : ℕ) : 0 < horizon k := by unfold horizon; positivity

noncomputable def samplesPre (k a c : ℕ) (pre : Fin (a + candidates k * horizon k) → Ω) : ℕ → Ω :=
  fun t => if h : a + c * horizon k + t < a + candidates k * horizon k then pre ⟨_, h⟩
    else pre ⟨0, Nat.lt_of_lt_of_le (Nat.mul_pos (candidates_pos k) (horizon_pos k))
      (Nat.le_add_left _ _)⟩

lemma samplesPre_measurable (k a c : ℕ) :
    Measurable (fun pre : Fin (a + candidates k * horizon k) → Ω => samplesPre k a c pre) := by
  apply Measurable.of_eval
  intro t
  unfold samplesPre
  split_ifs <;> exact measurable_pi_apply _

noncomputable def preCandidate (k a c : ℕ) (s : Seed)
    (pre : Fin (a + candidates k * horizon k) → Ω) : d.E :=
  (run (momentum k c) (stepSize k c) g d.x0 (samplesPre k a c pre) (chosen s k c)).1

omit [MeasurableSpace Ω] in
lemma preCandidate_eq (s : Seed) (k a : ℕ) (ξ : ℕ → Ω) {c : ℕ} (hc : c < candidates k) :
    phaseSelection g s k a ξ c = preCandidate (g := g) k a c s (fun i => ξ i) := by
  simp only [phaseSelection, hc, ↓reduceIte, phaseCands, runPoint, preCandidate]
  congr 1
  apply run_congr_prefix
  intro i hi
  have hch := chosen_lt s k c
  have hT : 0 < horizon k := by unfold horizon; positivity
  have hlt : a + c * horizon k + i < a + candidates k * horizon k := by
    have : (c + 1) * horizon k ≤ candidates k * horizon k := Nat.mul_le_mul_right _ hc
    nlinarith
  simp [samplesPre, hlt]

omit [MeasurableSpace Ω] in
lemma batchMean_tail (k a : ℕ) (x : d.E) (ξ : ℕ → Ω) (c : ℕ) :
    batchMean g (horizon k) (a + candidates k * horizon k + c * horizon k) x ξ =
      batchMean g (horizon k) (c * horizon k) x (fun i => ξ (a + candidates k * horizon k + i)) := by
  simp only [batchMean]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  ring

lemma batchMean_measurable (hg : Measurable (Function.uncurry g)) (T off : ℕ) :
    Measurable (fun z : d.E × (ℕ → Ω) => batchMean g T off z.1 z.2) := by
  unfold batchMean
  apply Measurable.const_smul
  apply Finset.measurable_sum
  intro i _
  exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply (off + i)).comp measurable_snd))

lemma error_moment_fixed_seed {grad : d.E → d.E} (hO : Oracle ν g grad σ p) (hgrad : Measurable grad)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (s : Seed) (k a : ℕ) {c : ℕ} (hc : c < candidates k) :
    Integrable (fun ξ : ℕ → Ω => ‖batchMean g (horizon k) (a + candidates k * horizon k + c * horizon k)
        (phaseSelection g s k a ξ c) ξ - grad (phaseSelection g s k a ξ c)‖ ^ p)
      (Measure.infinitePi fun _ : ℕ => ν) ∧
    (∫ ξ, ‖batchMean g (horizon k) (a + candidates k * horizon k + c * horizon k)
        (phaseSelection g s k a ξ c) ξ - grad (phaseSelection g s k a ξ c)‖ ^ p
      ∂Measure.infinitePi (fun _ : ℕ => ν)) ≤ 6 * σ ^ p / (horizon k : ℝ) ^ (p - 1) := by
  set n := a + candidates k * horizon k
  set T := horizon k
  have hT : 0 < T := by show 0 < horizon k; unfold horizon; positivity
  let e := OracleTemplate.StochasticGeneralized.splitStream (Ω := Ω) n
  let G : (Fin n → Ω) × (ℕ → Ω) → ℝ := fun z =>
    ‖batchMean g T (c * T) (preCandidate (g := g) k a c s z.1) z.2 -
      grad (preCandidate (g := g) k a c s z.1)‖ ^ p
  have hGeq : ∀ ξ, ‖batchMean g T (n + c * T) (phaseSelection g s k a ξ c) ξ -
      grad (phaseSelection g s k a ξ c)‖ ^ p = G (e ξ) := by
    intro ξ
    have he : e ξ = (fun i : Fin n => ξ i, fun i => ξ (n + i)) := rfl
    rw [he]
    simp only [G]
    rw [preCandidate_eq s k a ξ hc, batchMean_tail]
  have hYmeas : Measurable (fun pre : Fin n → Ω => preCandidate (g := g) k a c s pre) := by
    unfold preCandidate
    exact measurable_fst.comp ((run_measurable hO.measurable _ _ d.x0 _).comp
      (samplesPre_measurable k a c))
  have hGmeas : Measurable G := by
    apply Measurable.pow_const
    apply Measurable.norm
    apply Measurable.sub
    · exact (batchMean_measurable hO.measurable T (c * T)).comp
        ((hYmeas.comp measurable_fst).prodMk measurable_snd)
    · exact hgrad.comp (hYmeas.comp measurable_fst)
  have hfiber : ∀ pre : Fin n → Ω,
      Integrable (fun tail => G (pre, tail)) (Measure.infinitePi fun _ : ℕ => ν) ∧
      (∫ tail, G (pre, tail) ∂Measure.infinitePi (fun _ : ℕ => ν)) ≤ 6 * σ ^ p / (T : ℝ) ^ (p - 1) :=
    fun pre => batchMean_moment hO hp hp2 hT (c * T) (preCandidate (g := g) k a c s pre)
  have hcontrol := LongTails.Proofs.WeakGradientConvolution.nonnegative_fiber_integral_bound
    (P := Measure.pi fun _ : Fin n => ν) (Q := Measure.infinitePi fun _ : ℕ => ν)
    hGmeas.stronglyMeasurable (fun z => Real.rpow_nonneg (norm_nonneg _) _)
    (Filter.Eventually.of_forall (fun pre => (hfiber pre).1))
    (integrable_const (6 * σ ^ p / (T : ℝ) ^ (p - 1)))
    (Filter.Eventually.of_forall (fun pre => (hfiber pre).2))
  have hsplit := OracleTemplate.StochasticGeneralized.splitStream_preserving ν n
  have heq : (fun ξ : ℕ → Ω => ‖batchMean g T (n + c * T) (phaseSelection g s k a ξ c) ξ -
      grad (phaseSelection g s k a ξ c)‖ ^ p) = G ∘ e := by
    funext ξ; exact hGeq ξ
  rw [heq]
  refine ⟨hsplit.integrable_comp_of_integrable hcontrol.1, ?_⟩
  have hmap := integral_map (μ := Measure.infinitePi fun _ : ℕ => ν)
    hsplit.measurable.aemeasurable hGmeas.aestronglyMeasurable
  rw [hsplit.map_eq] at hmap
  rw [show (∫ ξ, (G ∘ e) ξ ∂Measure.infinitePi (fun _ : ℕ => ν)) =
    ∫ ξ, G (e ξ) ∂Measure.infinitePi (fun _ : ℕ => ν) from rfl, ← hmap]
  refine hcontrol.2.trans ?_
  rw [integral_const]
  simp


noncomputable def candError (g : d.E → Ω → d.E) (grad : d.E → d.E) (k a : ℕ) (c : ℕ)
    (z : Seed × (ℕ → Ω)) : ℝ :=
  ‖batchMean g (horizon k) (a + candidates k * horizon k + c * horizon k)
    (phaseSelection g z.1 k a z.2 c) z.2 - grad (phaseSelection g z.1 k a z.2 c)‖

lemma candError_measurable {grad : d.E → d.E} (hg : Measurable (Function.uncurry g))
    (hgrad : Measurable grad) (k a c : ℕ) :
    Measurable (candError g grad k a c) := by
  unfold candError
  apply Measurable.norm
  apply Measurable.sub
  · exact (batchMean_measurable hg _ _).comp
      ((phaseSelection_measurable hg k a c).prodMk measurable_snd)
  · exact hgrad.comp (phaseSelection_measurable hg k a c)

lemma error_moment {grad : d.E → d.E} (hO : Oracle ν g grad σ p) (hgrad : Measurable grad)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (k a : ℕ) {c : ℕ} (hc : c < candidates k) :
    Integrable (fun z => candError g grad k a c z ^ p) (seedLaw.prod (Measure.infinitePi fun _ : ℕ => ν)) ∧
    (∫ z, candError g grad k a c z ^ p ∂seedLaw.prod (Measure.infinitePi fun _ : ℕ => ν)) ≤
      6 * σ ^ p / (horizon k : ℝ) ^ (p - 1) := by
  have hmeas : Measurable (fun z => candError g grad k a c z ^ p) :=
    (candError_measurable hO.measurable hgrad k a c).pow_const _
  have hcontrol := LongTails.Proofs.WeakGradientConvolution.nonnegative_fiber_integral_bound
    (P := seedLaw) (Q := Measure.infinitePi fun _ : ℕ => ν)
    hmeas.stronglyMeasurable (fun z => Real.rpow_nonneg (norm_nonneg _) _)
    (Filter.Eventually.of_forall (fun s => (error_moment_fixed_seed hO hgrad hp hp2 s k a hc).1))
    (integrable_const (6 * σ ^ p / (horizon k : ℝ) ^ (p - 1)))
    (Filter.Eventually.of_forall (fun s => (error_moment_fixed_seed hO hgrad hp hp2 s k a hc).2))
  refine ⟨hcontrol.1, hcontrol.2.trans ?_⟩
  rw [integral_const]
  simp

lemma selectNorm_measurable {X : Type*} [MeasurableSpace X] {v : X → ℕ → ℝ}
    (hv : ∀ c, Measurable (fun x => v x c)) (c : ℕ) :
    Measurable (fun x => selectNorm (v x) c) := by
  induction c with
  | zero => exact hv 0
  | succ c ih =>
      simp only [selectNorm, improveNorm, Nat.succ_ne_zero, false_or]
      exact Measurable.ite (measurableSet_lt (hv (c + 1)) ih) (hv (c + 1)) ih

lemma selectBest_measurable {X : Type*} [MeasurableSpace X] {v : X → ℕ → ℝ} {y : X → ℕ → d.E}
    (hv : ∀ c, Measurable (fun x => v x c)) (hy : ∀ c, Measurable (fun x => y x c)) (c : ℕ) :
    Measurable (fun x => selectBest (v x) (y x) c) := by
  induction c with
  | zero => exact hy 0
  | succ c ih =>
      simp only [selectBest, improveBest, Nat.succ_ne_zero, false_or]
      exact Measurable.ite (measurableSet_lt (hv (c + 1)) (selectNorm_measurable hv c)) (hy (c + 1)) ih

lemma phaseEstimates_measurable (hg : Measurable (Function.uncurry g)) (k a c : ℕ) :
    Measurable (fun z : Seed × (ℕ → Ω) => phaseEstimates g z.1 k a z.2 c) := by
  unfold phaseEstimates estimate
  apply Measurable.norm
  exact (batchMean_measurable hg _ _).comp
    ((phaseSelection_measurable hg k a c).prodMk measurable_snd)

lemma phaseOutput_measurable (hg : Measurable (Function.uncurry g)) (k a : ℕ) :
    Measurable (fun z : Seed × (ℕ → Ω) => phaseOutput g z.1 k a z.2) := by
  unfold phaseOutput
  exact selectBest_measurable (phaseEstimates_measurable hg k a)
    (phaseSelection_measurable hg k a) _

lemma momentum_pos (k c : ℕ) : 0 < momentum k c := Real.exp_pos _

lemma momentum_le_one (k c : ℕ) : momentum k c ≤ 1 := by
  unfold momentum
  apply Real.exp_le_one_iff.mpr
  have : (0 : ℝ) ≤ ((c / stepCount k : ℕ) : ℝ) := by positivity
  linarith

lemma stepSize_pos (k c : ℕ) : 0 < stepSize k c := Real.exp_pos _

lemma stepSize_le (k c : ℕ) : stepSize k c ≤ Real.exp k := by
  unfold stepSize
  apply Real.exp_le_exp.mpr
  have : (0 : ℝ) ≤ ((c % stepCount k : ℕ) : ℝ) / 2 := by positivity
  linarith

omit [MeasurableSpace Ω] in
lemma phaseOutput_grad_bound {grad : d.E → d.E} (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hL : 0 ≤ L)
    (s : Seed) (k a : ℕ) (ξ : ℕ → Ω) :
    ‖grad (phaseOutput g s k a ξ)‖ ≤ ‖grad d.x0‖ + L * (horizon k * Real.exp k) := by
  obtain ⟨c₀, hc₀, hb, -, -⟩ := select_spec (phaseEstimates g s k a ξ) (phaseSelection g s k a ξ)
    (candidates k - 1)
  have hC := candidates_pos k
  unfold phaseOutput
  rw [hb, phaseSelection_eq_run s k a ξ (by omega)]
  have h1 := run_grad_bound hlip hL (α := momentum k c₀) (stepSize_pos k c₀).le g d.x0
    (fun n => ξ (a + c₀ * horizon k + n))
    (s k ⟨c₀, by omega⟩).val
  have hT : ((s k ⟨c₀, by omega⟩).val : ℝ) ≤ horizon k := by exact_mod_cast (Fin.isLt _).le
  have hη := stepSize_le k c₀
  have hη0 := (stepSize_pos k c₀).le
  calc ‖grad (run (momentum k c₀) (stepSize k c₀) g d.x0 (fun n => ξ (a + c₀ * horizon k + n))
        (s k ⟨c₀, by omega⟩).val).1‖
      ≤ ‖grad d.x0‖ + L * (((s k ⟨c₀, by omega⟩).val : ℝ) * stepSize k c₀) := h1
    _ ≤ ‖grad d.x0‖ + L * (horizon k * Real.exp k) := by
        gcongr


lemma le_one_add_rpow {x p : ℝ} (hx : 0 ≤ x) (hp : 1 ≤ p) : x ≤ 1 + x ^ p := by
  rcases le_or_gt x 1 with h | h
  · linarith [Real.rpow_nonneg hx p]
  · have : x ≤ x ^ p := by
      calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ p := Real.rpow_le_rpow_of_exponent_le h.le hp
    linarith

lemma root_sum_rpow {C : ℕ} {p : ℝ} (hp : 0 < p) (e : ℕ → ℝ) (he : ∀ c, 0 ≤ e c) :
    ((∑ c ∈ Finset.range C, e c ^ p) ^ (1 / p)) ^ p = ∑ c ∈ Finset.range C, e c ^ p := by
  rw [← Real.rpow_mul (Finset.sum_nonneg (fun c _ => Real.rpow_nonneg (he c) p)),
    one_div_mul_cancel hp.ne', Real.rpow_one]

lemma phase_expectation {f : d.E → ℝ} (hO : Oracle ν g (gradient f) σ p)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L)
    {lower Δ : ℝ} (hlow : ∀ x, lower ≤ f x) (hΔ : f d.x0 - lower ≤ Δ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (k a : ℕ) {c : ℕ} (hc : c < candidates k) :
    Integrable (fun z : Seed × (ℕ → Ω) => ‖gradient f (phaseOutput g z.1 k a z.2)‖)
      (seedLaw.prod (Measure.infinitePi fun _ : ℕ => ν)) ∧
    (∫ z, ‖gradient f (phaseOutput g z.1 k a z.2)‖
        ∂seedLaw.prod (Measure.infinitePi fun _ : ℕ => ν)) ≤
      (Δ / stepSize k c + 12 * σ / momentum k c +
        12 * σ * (horizon k) * momentum k c ^ ((p - 1) / p) +
        (horizon k) * (2 * L * stepSize k c * (1 - momentum k c) / momentum k c +
          L / 2 * stepSize k c)) / horizon k +
      (6 * σ ^ p / (horizon k : ℝ) ^ (p - 1)) ^ (1 / p) +
      (candidates k * (6 * σ ^ p / (horizon k : ℝ) ^ (p - 1))) ^ (1 / p) := by
  have hgrad : Measurable (gradient f) := grad_measurable hlip hL
  set μ := seedLaw.prod (Measure.infinitePi fun _ : ℕ => ν) with hμ
  have hp1 : 1 ≤ p := hp.le
  have hp0 : 0 < p := by linarith
  have hcand := candidate_expectation hO hg hlip hL hlow hΔ hp hp2 hσ k a hc
    (momentum_pos k c) (momentum_le_one k c) (stepSize_pos k c)
  have herr : ∀ c', c' < candidates k → Integrable (fun z => candError g (gradient f) k a c' z ^ p) μ ∧
      (∫ z, candError g (gradient f) k a c' z ^ p ∂μ) ≤ 6 * σ ^ p / (horizon k : ℝ) ^ (p - 1) :=
    fun c' hc' => error_moment hO hgrad hp1 hp2 k a hc'
  have hout_meas : Measurable (fun z : Seed × (ℕ → Ω) => ‖gradient f (phaseOutput g z.1 k a z.2)‖) :=
    (hgrad.comp (phaseOutput_measurable hO.measurable k a)).norm
  have hout_int : Integrable (fun z : Seed × (ℕ → Ω) => ‖gradient f (phaseOutput g z.1 k a z.2)‖) μ := by
    refine Integrable.of_bound hout_meas.aestronglyMeasurable
      (‖gradient f d.x0‖ + L * (horizon k * Real.exp k)) (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact phaseOutput_grad_bound hlip hL z.1 k a z.2
  refine ⟨hout_int, ?_⟩
  let M : Seed × (ℕ → Ω) → ℝ := fun z =>
    (∑ c' ∈ Finset.range (candidates k), candError g (gradient f) k a c' z ^ p) ^ (1 / p)
  have hMp : ∀ z, M z ^ p = ∑ c' ∈ Finset.range (candidates k), candError g (gradient f) k a c' z ^ p :=
    fun z => root_sum_rpow hp0 _ (fun c' => norm_nonneg _)
  have hMmeas : Measurable M :=
    (Finset.measurable_sum _ (fun c' _ => (candError_measurable
      hO.measurable hgrad k a c').pow_const _)).pow_const _
  have hMp_int : Integrable (fun z => M z ^ p) μ := by
    simp only [hMp]
    exact integrable_finsetSum _ (fun c' hc' => (herr c' (Finset.mem_range.mp hc')).1)
  have hMnn : ∀ z, 0 ≤ M z := fun z => Real.rpow_nonneg (Finset.sum_nonneg
    (fun c' _ => Real.rpow_nonneg (norm_nonneg _) p)) _
  have hM_int : Integrable M μ := by
    have hb : Integrable (fun z => 1 + M z ^ p) μ := (integrable_const (1 : ℝ)).add hMp_int
    refine Integrable.mono' hb hMmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => ?_))
    show ‖M z‖ ≤ 1 + M z ^ p
    rw [Real.norm_eq_abs, abs_of_nonneg (hMnn z)]
    exact le_one_add_rpow (hMnn z) hp1
  have he_meas : Measurable (candError g (gradient f) k a c) :=
    candError_measurable hO.measurable hgrad k a c
  have henn : ∀ z, 0 ≤ candError g (gradient f) k a c z := fun z => norm_nonneg _
  have he_int : Integrable (candError g (gradient f) k a c) μ := by
    have hb : Integrable (fun z => 1 + candError g (gradient f) k a c z ^ p) μ :=
      (integrable_const (1 : ℝ)).add (herr c hc).1
    refine Integrable.mono' hb he_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => ?_))
    show ‖candError g (gradient f) k a c z‖ ≤ 1 + candError g (gradient f) k a c z ^ p
    rw [Real.norm_eq_abs, abs_of_nonneg (henn z)]
    exact le_one_add_rpow (henn z) hp1
  have hpoint : ∀ z : Seed × (ℕ → Ω), ‖gradient f (phaseOutput g z.1 k a z.2)‖ ≤
      ‖gradient f (phaseSelection g z.1 k a z.2 c)‖ + candError g (gradient f) k a c z + M z :=
    fun z => phase_pointwise hp1 g (gradient f) z.1 k a z.2 hc
  have hi1 : Integrable (fun z => ‖gradient f (phaseSelection g z.1 k a z.2 c)‖ +
      candError g (gradient f) k a c z) μ := hcand.1.add he_int
  have hi2 : Integrable (fun z => (‖gradient f (phaseSelection g z.1 k a z.2 c)‖ +
      candError g (gradient f) k a c z) + M z) μ := hi1.add hM_int
  have hmono := integral_mono hout_int hi2 hpoint
  rw [integral_add hi1 hM_int, integral_add hcand.1 he_int] at hmono
  have hroot_e : (∫ z, candError g (gradient f) k a c z ∂μ) ≤
      (∫ z, candError g (gradient f) k a c z ^ p ∂μ) ^ (1 / p) := by
    have := HeavyTailedMomentBounds.integral_norm_le_root_moment (P := μ) hp
      he_meas.aestronglyMeasurable (by
        refine (herr c hc).1.congr (Filter.Eventually.of_forall (fun z => ?_))
        simp only [Real.norm_eq_abs, abs_of_nonneg (henn z)])
    have h1 : (∫ z, ‖candError g (gradient f) k a c z‖ ∂μ) = ∫ z, candError g (gradient f) k a c z ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (henn z)]))
    have h2 : (∫ z, ‖candError g (gradient f) k a c z‖ ^ p ∂μ) =
        ∫ z, candError g (gradient f) k a c z ^ p ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (henn z)]))
    rw [h1, h2] at this
    exact this
  have hroot_M : (∫ z, M z ∂μ) ≤ (∫ z, M z ^ p ∂μ) ^ (1 / p) := by
    have := HeavyTailedMomentBounds.integral_norm_le_root_moment (P := μ) hp
      hMmeas.aestronglyMeasurable (by
        have h := hMp_int
        refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
        simp only [Real.norm_eq_abs, abs_of_nonneg (hMnn z)])
    have h1 : (∫ z, ‖M z‖ ∂μ) = ∫ z, M z ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (hMnn z)]))
    have h2 : (∫ z, ‖M z‖ ^ p ∂μ) = ∫ z, M z ^ p ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (hMnn z)]))
    rw [h1, h2] at this
    exact this
  have hMsum : (∫ z, M z ^ p ∂μ) ≤ candidates k * (6 * σ ^ p / (horizon k : ℝ) ^ (p - 1)) := by
    simp only [hMp]
    rw [integral_finsetSum _ (fun c' hc' => (herr c' (Finset.mem_range.mp hc')).1)]
    calc ∑ c' ∈ Finset.range (candidates k), (∫ z, candError g (gradient f) k a c' z ^ p ∂μ)
        ≤ ∑ c' ∈ Finset.range (candidates k), 6 * σ ^ p / (horizon k : ℝ) ^ (p - 1) :=
          Finset.sum_le_sum (fun c' hc' => (herr c' (Finset.mem_range.mp hc')).2)
      _ = candidates k * (6 * σ ^ p / (horizon k : ℝ) ^ (p - 1)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hroot_e' : (∫ z, candError g (gradient f) k a c z ∂μ) ≤
      (6 * σ ^ p / (horizon k : ℝ) ^ (p - 1)) ^ (1 / p) :=
    hroot_e.trans (Real.rpow_le_rpow (integral_nonneg (fun z => Real.rpow_nonneg (norm_nonneg _) _))
      (herr c hc).2 (by positivity))
  have hroot_M' : (∫ z, M z ∂μ) ≤ (candidates k * (6 * σ ^ p / (horizon k : ℝ) ^ (p - 1))) ^ (1 / p) :=
    hroot_M.trans (Real.rpow_le_rpow (integral_nonneg (fun z => Real.rpow_nonneg (Real.rpow_nonneg
      (Finset.sum_nonneg (fun c' _ => Real.rpow_nonneg (norm_nonneg _) p)) _) _)) hMsum (by positivity))
  linarith [hcand.2]

end LongTails.Proofs.ParameterFreeNsgdmPhase
