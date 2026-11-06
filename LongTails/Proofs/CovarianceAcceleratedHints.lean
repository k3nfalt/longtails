import LongTails.Proofs.CovarianceAcceleratedRun
import LongTails.Proofs.CovarianceAcceleratedMeasurable
import LongTails.Proofs.CovarianceAcceleratedConcentration

open MeasureTheory ProbabilityTheory Convexity
open LongTails.Algorithms.CovarianceAccelerated
open LongTails.Proofs.CovarianceAcceleratedExecution
open LongTails.Proofs.CovarianceAcceleratedMeasurable
open LongTails.Proofs.CovarianceAcceleratedConcentration
open LongTails.Proofs.AdamHeavyTailedProcess

namespace LongTails.Proofs.CovarianceAcceleratedHints

noncomputable local instance simplexMeasurableSpace (n : ℕ) : MeasurableSpace (StdSimplex ℝ (Fin n)) := borel _
local instance (n : ℕ) : BorelSpace (StdSimplex ℝ (Fin n)) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (StdSimplex ℝ (Fin n)) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin n)).secondCountableTopology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ} (c : Config E n)

noncomputable def next {Ω : Type*} (g : E → Ω → E) (s : State c) (ω : Ω) : State c :=
  advance c s (g (query c s) ω)

noncomputable def noise {Ω : Type*} (g : E → Ω → E) (v : E → E) (s : State c) (ω : Ω) : E :=
  g (query c s) ω - v (query c s)

omit [BorelSpace E] in
lemma stateAt_trajectory {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) (t : ℕ) :
    stateAt (next c g) (initial c) ξ t = trajectory c g ξ t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [stateAt_succ, ih]; rfl

lemma measurable_next {Ω : Type*} [MeasurableSpace Ω] {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (hβ : 0 ≤ c.β) (hγ : 0 < c.γ)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖c.centers i‖ ≤ M) :
    Measurable (Function.uncurry (next c g)) := by
  exact (measurable_advance c hβ hγ hM hz).comp
    (measurable_fst.prodMk (hg.comp (((measurable_query c).comp measurable_fst).prodMk measurable_snd)))

lemma measurable_noise {Ω : Type*} [MeasurableSpace Ω] {g : E → Ω → E} {v : E → E}
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) :
    Measurable (Function.uncurry (noise c g v)) := by
  exact (hg.comp (((measurable_query c).comp measurable_fst).prodMk measurable_snd)).sub
    (hv.comp ((measurable_query c).comp measurable_fst))

noncomputable def windowIncrement {Ω : Type*} (g : E → Ω → E) (v : E → E)
    (σ : ℝ) (a k : ℕ) (s : State c) (ω : Ω) : ℝ :=
  if a ≤ s.1 ∧ s.1 < a + k then bad σ (noise c g v s) ω - 1 / 32 else 0

lemma measurable_windowIncrement {Ω : Type*} [MeasurableSpace Ω] {g : E → Ω → E} {v : E → E}
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) (σ : ℝ) (a k : ℕ) :
    Measurable (Function.uncurry (windowIncrement c g v σ a k)) := by
  have hm : MeasurableSet {z : State c × Ω | a ≤ z.1.1 ∧ z.1.1 < a + k} :=
    (measurableSet_le measurable_const measurable_fst.fst).inter
      (measurableSet_lt measurable_fst.fst measurable_const)
  have hb : Measurable (fun z : State c × Ω => bad σ (noise c g v z.1) z.2) := by
    change Measurable (bad σ (Function.uncurry (noise c g v)))
    exact bad_measurable (measurable_noise c hg hv) σ
  exact Measurable.ite hm (hb.sub measurable_const) measurable_const

lemma window_exp_control {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
    {g : E → Ω → E} {v : E → E} (hg : Measurable (Function.uncurry g)) (hv : Measurable v)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hi : ∀ x, Integrable (fun ω => ‖g x ω - v x‖ ^ 2) p)
    (hb : ∀ x, (∫ ω, ‖g x ω - v x‖ ^ 2 ∂p) ≤ σ ^ 2) (a k : ℕ) (s : State c) :
    Integrable (fun ω => Real.exp (windowIncrement c g v σ a k s ω)) p ∧
      (∫ ω, Real.exp (windowIncrement c g v σ a k s ω) ∂p) ≤ 1 := by
  by_cases hs : a ≤ s.1 ∧ s.1 < a + k
  · simp only [windowIncrement, ite_eq_left hs]
    exact bad_compensated_exp_control
      ((measurable_noise c hg hv).comp (measurable_const.prodMk measurable_id)) hσ
      (hi (query c s)) (hb (query c s))
  · simp [windowIncrement, hs]

noncomputable def badCount {Ω : Type*} (g : E → Ω → E) (v : E → E)
    (σ : ℝ) (a k : ℕ) (ξ : ℕ → Ω) : ℝ :=
  ∑ j ∈ Finset.range k, bad σ (noise c g v (trajectory c g ξ (a + j))) (ξ (a + j))

omit [BorelSpace E] in
lemma window_sum {Ω : Type*} (g : E → Ω → E) (v : E → E)
    (σ : ℝ) (a k : ℕ) (ξ : ℕ → Ω) :
    (∑ t ∈ Finset.range (a + k), windowIncrement c g v σ a k (trajectory c g ξ t) (ξ t)) =
      badCount c g v σ a k ξ - k / 32 := by
  rw [Finset.sum_range_add]
  have hz : (∑ t ∈ Finset.range a, windowIncrement c g v σ a k (trajectory c g ξ t) (ξ t)) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have ht' : ¬a ≤ t := Nat.not_le_of_gt (Finset.mem_range.mp ht)
    simp [windowIncrement, trajectory_clock, ht']
  rw [hz, zero_add]
  calc
    _ = ∑ j ∈ Finset.range k,
        (bad σ (noise c g v (trajectory c g ξ (a + j))) (ξ (a + j)) - 1 / 32) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hh : a ≤ a + j ∧ a + j < a + k := ⟨by omega, by have := Finset.mem_range.mp hj; omega⟩
      simp only [windowIncrement, trajectory_clock, ite_eq_left hh]
    _ = badCount c g v σ a k ξ - k / 32 := by
      rw [Finset.sum_sub_distrib]
      simp only [badCount, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

lemma window_bad_tail {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {p : Measure Ω} [IsProbabilityMeasure p] {P : Measure Ξ} [IsProbabilityMeasure P]
    {ξ : ℕ → Ξ → Ω}
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {g : E → Ω → E} {v : E → E} (hg : Measurable (Function.uncurry g)) (hv : Measurable v)
    (hβ : 0 ≤ c.β) (hγ : 0 < c.γ) {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖c.centers i‖ ≤ M)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hi : ∀ x, Integrable (fun ω => ‖g x ω - v x‖ ^ 2) p)
    (hb : ∀ x, (∫ ω, ‖g x ω - v x‖ ^ 2 ∂p) ≤ σ ^ 2) (a k : ℕ) :
    P {ω | (k : ℝ) / 4 ≤ badCount c g v σ a k (fun t => ξ t ω)} ≤
      ENNReal.ofReal (Real.exp (-7 * k / 32)) := by
  have h := iid_exponential_tail hsamples (measurable_next c hg hβ hγ hM hz)
    (measurable_windowIncrement c hg hv σ a k)
    (fun s => (window_exp_control c hg hv hσ hi hb a k s).1)
    (fun s => (window_exp_control c hg hv hσ hi hb a k s).2)
    (a + k) (initial c) (7 * (k : ℝ) / 32)
  simp only [stateAt_trajectory, window_sum] at h
  have he : {ω | (k : ℝ) / 4 ≤ badCount c g v σ a k (fun t => ξ t ω)} =
      {ω | 7 * (k : ℝ) / 32 ≤ badCount c g v σ a k (fun t => ξ t ω) - k / 32} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro hh <;> linarith
  rw [he]
  convert h using 1
  congr 2
  ring

lemma windows_bad_tail {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {p : Measure Ω} [IsProbabilityMeasure p] {P : Measure Ξ} [IsProbabilityMeasure P]
    {ξ : ℕ → Ξ → Ω}
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {g : E → Ω → E} {v : E → E} (hg : Measurable (Function.uncurry g)) (hv : Measurable v)
    (hβ : 0 ≤ c.β) (hγ : 0 < c.γ) {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖c.centers i‖ ≤ M)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hi : ∀ x, Integrable (fun ω => ‖g x ω - v x‖ ^ 2) p)
    (hb : ∀ x, (∫ ω, ‖g x ω - v x‖ ^ 2 ∂p) ≤ σ ^ 2) (k T : ℕ) :
    P {ω | ∃ t : Fin T, (k : ℝ) / 4 ≤ badCount c g v σ t.val k (fun j => ξ j ω)} ≤
      ENNReal.ofReal ((T : ℝ) * Real.exp (-7 * k / 32)) := by
  have he : {ω | ∃ t : Fin T, (k : ℝ) / 4 ≤ badCount c g v σ t.val k (fun j => ξ j ω)} =
      ⋃ t : Fin T, {ω | (k : ℝ) / 4 ≤ badCount c g v σ t.val k (fun j => ξ j ω)} := by
    ext ω
    simp
  rw [he]
  calc
    _ ≤ ∑ t : Fin T, P {ω | (k : ℝ) / 4 ≤ badCount c g v σ t.val k (fun j => ξ j ω)} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : Fin T, ENNReal.ofReal (Real.exp (-7 * k / 32)) :=
      Finset.sum_le_sum fun t _ => window_bad_tail c hsamples hg hv hβ hγ hM hz hσ hi hb t.val k
    _ = ENNReal.ofReal ((T : ℝ) * Real.exp (-7 * k / 32)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg T), ENNReal.ofReal_natCast]
      simp

omit [BorelSpace E] in
lemma badCount_history {Ω : Type*} (g : E → Ω → E) (v : E → E) (σ : ℝ)
    (t : ℕ) (ξ : ℕ → Ω) :
    badCount c g v σ t (c.window + 1) ξ =
      ∑ j : Fin (c.window + 1), bad σ
        (noise c g v (trajectory c g ξ (c.window + 1 + t - 1 - j.val)))
        (ξ (c.window + 1 + t - 1 - j.val)) := by
  unfold badCount
  rw [← Fin.sum_univ_eq_sum_range]
  have he := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (c.window + 1)))
    (fun j : Fin (c.window + 1) => bad σ (noise c g v (trajectory c g ξ (t + j.val))) (ξ (t + j.val)))
  rw [← he]
  apply Finset.sum_congr rfl
  intro j _
  change bad σ (noise c g v (trajectory c g ξ (t + j.rev.val))) (ξ (t + j.rev.val)) = _
  have hj : t + j.rev.val = c.window + 1 + t - 1 - j.val := by
    rw [Fin.val_rev]
    omega
  rw [hj]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma good_subset_of_bad_lt {k : ℕ} (e : Fin k → E) (σ : ℝ)
    (hb : (∑ j : Fin k, if 8 * σ < ‖e j‖ then (1 : ℝ) else 0) < k / 4) :
    ∃ G : Finset (Fin k), 3 * k ≤ 4 * G.card ∧ ∀ j ∈ G, ‖e j‖ ≤ 8 * σ := by
  classical
  let G := Finset.univ.filter (fun j => ‖e j‖ ≤ 8 * σ)
  have hsum : (∑ j : Fin k, ((if 8 * σ < ‖e j‖ then (1 : ℝ) else 0) +
      (if ‖e j‖ ≤ 8 * σ then (1 : ℝ) else 0))) = k := by
    calc
      _ = ∑ _ : Fin k, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : ‖e j‖ ≤ 8 * σ
        · simp [h, not_lt.mpr h]
        · simp [h, lt_of_not_ge h]
      _ = k := by simp
  have hg : (∑ j : Fin k, if ‖e j‖ ≤ 8 * σ then (1 : ℝ) else 0) = G.card := by
    simp [G]
  rw [Finset.sum_add_distrib, hg] at hsum
  have hc : 3 * (k : ℝ) ≤ 4 * (G.card : ℝ) := by linarith
  refine ⟨G, by exact_mod_cast hc, ?_⟩
  intro j hj
  exact (Finset.mem_filter.mp hj).2

omit [BorelSpace E] in
lemma medoid_residual_of_bad_lt {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω)
    (hη : 0 < c.η) {M R σ L : ℝ} (hR : 0 ≤ R) (hσ : 0 ≤ σ) (hL : 0 ≤ L)
    (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R)
    (v : E → E) (hlip : ∀ x y, ‖v x - v y‖ ≤ L * ‖x - y‖) (t : ℕ)
    (hb : badCount c g v σ t (c.window + 1) ξ < (c.window + 1 : ℝ) / 4) :
    ‖v (query c (CovarianceAcceleratedRun.phase c g ξ t)) -
      OracleTemplate.MultiplicativeRobustEstimator.medoid (CovarianceAcceleratedRun.phase c g ξ t).2.2.2‖ ≤
      48 * σ + 96 * L * R * (c.window + 1) / ((t : ℝ) + 1) := by
  rw [badCount_history] at hb
  simp only [bad] at hb
  obtain ⟨G, hcard, hgood⟩ := good_subset_of_bad_lt
    (fun j : Fin (c.window + 1) => noise c g v
      (trajectory c g ξ (c.window + 1 + t - 1 - j.val)) (ξ (c.window + 1 + t - 1 - j.val))) σ (by simpa only [Nat.cast_add, Nat.cast_one] using hb)
  exact CovarianceAcceleratedRun.medoid_residual c g ξ hη hR hσ hL hz ha v hlip t G hcard hgood

lemma medoid_failure_probability {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {p : Measure Ω} [IsProbabilityMeasure p] {P : Measure Ξ} [IsProbabilityMeasure P]
    {ξ : ℕ → Ξ → Ω}
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {g : E → Ω → E} {v : E → E} (hg : Measurable (Function.uncurry g)) (hv : Measurable v)
    (hη : 0 < c.η) (hβ : 0 ≤ c.β) (hγ : 0 < c.γ)
    {M R σ L : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hσ : 0 ≤ σ) (hL : 0 ≤ L)
    (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R)
    (hlip : ∀ x y, ‖v x - v y‖ ≤ L * ‖x - y‖)
    (hi : ∀ x, Integrable (fun ω => ‖g x ω - v x‖ ^ 2) p)
    (hb : ∀ x, (∫ ω, ‖g x ω - v x‖ ^ 2 ∂p) ≤ σ ^ 2) (T : ℕ) :
    P {ω | ∃ t : Fin T, 48 * σ + 96 * L * R * (c.window + 1) / ((t.val : ℝ) + 1) <
      ‖v (query c (CovarianceAcceleratedRun.phase c g (fun j => ξ j ω) t.val)) -
        OracleTemplate.MultiplicativeRobustEstimator.medoid
          (CovarianceAcceleratedRun.phase c g (fun j => ξ j ω) t.val).2.2.2‖} ≤
      ENNReal.ofReal ((T : ℝ) * Real.exp (-7 * (c.window + 1) / 32)) := by
  have hsub : {ω | ∃ t : Fin T, 48 * σ + 96 * L * R * (c.window + 1) / ((t.val : ℝ) + 1) <
      ‖v (query c (CovarianceAcceleratedRun.phase c g (fun j => ξ j ω) t.val)) -
        OracleTemplate.MultiplicativeRobustEstimator.medoid
          (CovarianceAcceleratedRun.phase c g (fun j => ξ j ω) t.val).2.2.2‖} ⊆
      {ω | ∃ t : Fin T, ((c.window + 1 : ℕ) : ℝ) / 4 ≤
        badCount c g v σ t.val (c.window + 1) (fun j => ξ j ω)} := by
    rintro ω ⟨t, ht⟩
    refine ⟨t, le_of_not_gt ?_⟩
    intro hbad
    have hm := medoid_residual_of_bad_lt c g (fun j => ξ j ω) hη hR hσ hL hz ha v hlip t.val
      (by simpa only [Nat.cast_add, Nat.cast_one] using hbad)
    exact (not_lt_of_ge hm) ht
  have hw := windows_bad_tail c hsamples hg hv hβ hγ hM hz hσ hi hb (c.window + 1) T
  exact (measure_mono hsub).trans (by simpa only [Nat.cast_add, Nat.cast_one] using hw)

end LongTails.Proofs.CovarianceAcceleratedHints
