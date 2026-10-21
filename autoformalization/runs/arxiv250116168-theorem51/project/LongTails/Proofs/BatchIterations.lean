import LongTails.Proofs.SingleOracleCounted
import LongTails.Algorithms.BatchIterations
import LongTails.Proofs.RennalaConvergence

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace OracleTemplate.BatchIterations

open Rennala

lemma blocks_measurable {Ω : Type} [MeasurableSpace Ω] (S : ℕ) :
    Measurable (blocks (Ω := Ω) S) :=
by
  exact Measurable.of_eval (fun k => Measurable.of_eval (fun i => measurable_pi_apply _))

lemma blocks_law {Ω : Type} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω)) (S : ℕ)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω))) :
    MeasurePreserving (blocks S) (P : Measure (ℕ → Ω))
      (Measure.infinitePi (fun _ : ℕ => Measure.pi (fun _ : Fin S => (μ : Measure Ω)))) := by
  have hc := StochasticGeneralized.infinitePi_iid (μ : Measure Ω)
  exact (FiniteVariance.infinite_block_law (μ : Measure Ω)
    (Measure.infinitePi (fun _ : ℕ => (μ : Measure Ω))) hc.independent hc.marginal S).comp
      hiid.stream_law

lemma path_step {d : ℕ} {Ω : Type} (g : Point d → Ω → Point d)
    (gamma : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (k : ℕ) :
    iterate g gamma 1 x0 ξ (k + 1) =
      iterate g gamma 1 x0 ξ k - gamma • g (iterate g gamma 1 x0 ξ k) (ξ k) := by
  dsimp only [iterate, batchEstimator]
  simp only [Fin.sum_univ_one, Nat.cast_one, div_one, one_smul,
    Nat.mul_one, Fin.val_zero, Nat.add_zero]

lemma block_path {d : ℕ} {Ω : Type} (g : Point d → Ω → Point d)
    (gamma : ℝ) (S : ℕ) (x0 : Point d) (ξ : ℕ → Ω) (k : ℕ) :
    iterate (batchEstimator S g) gamma 1 x0 (blocks S ξ) k =
      iterate g gamma S x0 ξ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [path_step]
    dsimp only [iterate]
    rw [ih]
    rfl

lemma execute_prefix (p : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → Point p.d)
    (j : Fin (p.N + 1)) (ξ : ℕ → Fin p.S → Ω) :
    executeCounted (oracle p P g) (algorithm p) (p.N + 1) j ξ =
      (iterate (batchEstimator p.S g) p.gamma 1 p.x0 ξ j.val, p.N + 1) := by
  classical
  let X := iterate (batchEstimator p.S g) p.gamma 1 p.x0 ξ
  let st : ℕ → State p := fun r =>
    ⟨r, X r, if j.val ≤ r then X j.val else p.x0, j⟩
  let step : ℕ → State p → State p := fun r (s : State p) => (algorithm p).update s
    ((oracle p P g).answer r ((algorithm p).query s) (ξ r))
  have hstep (r : ℕ) : step r (st r) = st (r + 1) := by
    have hx := path_step (batchEstimator p.S g) p.gamma p.x0 ξ r
    change X (r+1) = X r - p.gamma • batchEstimator p.S g (X r) (ξ r) at hx
    dsimp only [step, st, algorithm, oracle]
    rw [← hx]
    by_cases he : r + 1 = j.val
    · simp only [he, le_refl, ite_true]
    · by_cases hj : j.val ≤ r
      · have hj' : j.val ≤ r + 1 := by omega
        simp only [he, hj, hj', ite_false, ite_true]
      · have hj' : ¬j.val ≤ r + 1 := by omega
        simp only [he, hj, hj', ite_false]
  have hinit : (algorithm p).initial j = st 0 := by
    dsimp only [algorithm, st]
    have hx : X 0 = p.x0 := rfl
    rw [hx]
    by_cases hj : j.val ≤ 0
    · have he : j.val = 0 := by omega
      simp only [he, hx, ite_self]
    · simp only [hj, ite_false]
  have hadvance : ∀ K r,
      StochasticGradient.advance step K r (st r) = st (r + K) := by
    intro K
    induction K with
    | zero => intro r; rfl
    | succ K ih =>
      intro r
      dsimp only [StochasticGradient.advance]
      rw [hstep, ih]
      congr 1
      omega
  have hexe := executeCounted_advance (oracle p P g) (algorithm p) (p.N+1) j ξ
  apply hexe.trans
  change ((StochasticGradient.advance step (p.N+1) 0
    (⟨0, p.x0, p.x0, j⟩ : State p)).selected, p.N+1) = _
  change (⟨0, p.x0, p.x0, j⟩ : State p) = st 0 at hinit
  rw [hinit, hadvance]
  have hj : j.val ≤ p.N + 1 := j.isLt.le
  dsimp only [algorithm, st]
  simp only [Nat.zero_add, hj, ite_true]; rfl

lemma uniform_success (p : Public) {Ω : Type} [MeasurableSpace Ω]
    (f : Point p.d → ℝ) (g : Point p.d → Ω → Point p.d)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (L v eps : ℝ) (hS : 0 < p.S) (hL : 0 < L) (hv : 0 ≤ v)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x-y‖)
    (ho : StochasticOracle Ω μ f g v)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (ha : (1 / ((p.N+1 : ℕ) : ℝ)) * ∑ k ∈ Finset.range (p.N+1),
      (∫ ξ, ‖gradient f (iterate g p.gamma p.S p.x0 ξ k)‖ ^ 2 ∂(P : Measure _)) ≤ eps) :
    let R := fun z : Fin (p.N+1) × (ℕ → Fin p.S → Ω) =>
      (executeCounted (oracle p P g) (algorithm p) (p.N+1) z.1 z.2).1
    let Q := (PMF.uniformOfFintype (Fin (p.N+1))).toMeasure.prod
      ((P.map (blocks p.S) : ProbabilityMeasure (ℕ → Fin p.S → Ω)) : Measure _)
    Measurable R ∧ Integrable (fun z => ‖gradient f (R z)‖ ^ 2) Q ∧
      (∫ z, ‖gradient f (R z)‖ ^ 2 ∂Q) ≤ eps := by
  classical
  let X : Fin (p.N+1) → (ℕ → Ω) → Point p.d :=
    fun j ξ => iterate g p.gamma p.S p.x0 ξ j.val
  have hm (j : Fin (p.N+1)) : Measurable (X j) :=
    (finite_moments f g μ P (fun k ξ => ξ k) L v p.gamma p.x0 p.S hS hL hv hg hlip ho hiid j.val).1
  have hi (j : Fin (p.N+1)) : Integrable (fun ξ => ‖gradient f (X j ξ)‖ ^ 2) (P : Measure _) :=
    (finite_moments f g μ P (fun k ξ => ξ k) L v p.gamma p.x0 p.S hS hL hv hg hlip ho hiid j.val).2.2.2
  have ha' : (1 / ((p.N+1 : ℕ) : ℝ)) * ∑ j : Fin (p.N+1),
      (∫ ξ, ‖gradient f (X j ξ)‖ ^ 2 ∂(P : Measure _)) ≤ eps := by
    rw [← Fin.sum_univ_eq_sum_range (fun k =>
      ∫ ξ, ‖gradient f (iterate g p.gamma p.S p.x0 ξ k)‖ ^ 2 ∂(P : Measure _)) (p.N+1)] at ha
    exact ha
  have hu := uniform_prefix_accuracy P f p.N X eps hm hi ha'
  let μB : ProbabilityMeasure (Fin p.S → Ω) :=
    ⟨Measure.pi (fun _ : Fin p.S => (μ : Measure Ω)), inferInstance⟩
  let PB : ProbabilityMeasure (ℕ → Fin p.S → Ω) :=
    ⟨Measure.infinitePi (fun _ : ℕ => (μB : Measure _)), inferInstance⟩
  have hoB : StochasticOracle (Fin p.S → Ω) μB f (batchEstimator p.S g) (v / (p.S : ℝ)) :=
    batch_moments f g μ v hv ho p.S hS
  have hiidB := StochasticGeneralized.infinitePi_iid (μB : Measure (Fin p.S → Ω))
  let Y : Fin (p.N+1) × (ℕ → Fin p.S → Ω) → Point p.d :=
    fun z => iterate (batchEstimator p.S g) p.gamma 1 p.x0 z.2 z.1.val
  have hmY : Measurable Y := by
    apply measurable_from_prod_countable_right
    intro j
    exact (finite_moments f (batchEstimator p.S g) μB PB (fun k ξ => ξ k)
      L (v / (p.S : ℝ)) p.gamma p.x0 1 (by decide) hL
      (div_nonneg hv (Nat.cast_nonneg _)) hg hlip hoB hiidB j.val).1
  let U := (PMF.uniformOfFintype (Fin (p.N+1))).toMeasure
  let Q : Measure (Fin (p.N+1) × (ℕ → Fin p.S → Ω)) :=
    U.prod (P.map (blocks p.S) : Measure (ℕ → Fin p.S → Ω))
  have hblock : MeasurePreserving (blocks p.S) (P : Measure (ℕ → Ω))
      (P.map (blocks p.S) : Measure (ℕ → Fin p.S → Ω)) :=
    ⟨blocks_measurable p.S, rfl⟩
  have hprod := (MeasurePreserving.id U).prod hblock
  have hYmap (z : Fin (p.N+1) × (ℕ → Ω)) :
      Y (Prod.map id (blocks p.S) z) = X z.1 z.2 :=
    block_path g p.gamma p.S p.x0 z.2 z.1.val
  have hgc : Continuous (gradient f) :=
    (lipschitzWith_iff_norm_sub_le.mpr hlip : LipschitzWith ⟨L, hL.le⟩ (gradient f)).continuous
  have hmV : Measurable (fun z => ‖gradient f (Y z)‖ ^ 2) :=
    (hgc.measurable.comp hmY).norm.pow_const 2
  have hiY : Integrable (fun z => ‖gradient f (Y z)‖ ^ 2) Q := by
    apply (hprod.integrable_comp hmV.aestronglyMeasurable).mp
    simpa only [Function.comp_def, hYmap] using hu.2.1
  have hbound : (∫ z, ‖gradient f (Y z)‖ ^ 2 ∂Q) ≤ eps := by
    have heq := integral_map (μ := U.prod (P : Measure (ℕ → Ω)))
      hprod.measurable.aemeasurable hmV.aestronglyMeasurable
    rw [hprod.map_eq] at heq
    rw [heq]
    simpa only [hYmap] using hu.2.2.2
  have hexe : (fun z : Fin (p.N+1) × (ℕ → Fin p.S → Ω) =>
      (executeCounted (oracle p P g) (algorithm p) (p.N+1) z.1 z.2).1) = Y := by
    funext z
    exact congrArg Prod.fst (execute_prefix p P g z.1 z.2)
  change Measurable _ ∧ Integrable _ Q ∧ _
  rw [hexe]
  exact ⟨hmY, hiY, hbound⟩

lemma horizon_coverage (rate : ℝ) (K : ℕ) :
    (0 < K ∧ rate ≤ (K : ℝ)) ↔ ∃ extra : ℕ, K = max 1 ⌈rate⌉₊ + extra := by
  constructor
  · rintro ⟨hK, hrate⟩
    have hb : max 1 ⌈rate⌉₊ ≤ K := max_le (by omega) (Nat.ceil_le.mpr hrate)
    exact ⟨K - max 1 ⌈rate⌉₊, (Nat.add_sub_of_le hb).symm⟩
  · rintro ⟨extra, rfl⟩
    constructor
    · have := le_max_left (1 : ℕ) ⌈rate⌉₊
      omega
    · exact (Nat.le_ceil rate).trans (by exact_mod_cast
        ((le_max_right 1 ⌈rate⌉₊).trans (Nat.le_add_right _ extra)))

lemma block_indexing (K S : ℕ) :
    ∃ e : Fin K × Fin S ≃ Fin (K * S),
      ∀ q, (e q).val = q.1.val * S + q.2.val := by
  refine ⟨finProdFinEquiv, ?_⟩
  intro q
  dsimp [finProdFinEquiv]
  ring

lemma query_cost (p : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → Point p.d)
    (K : ℕ) (j : Fin (p.N + 1)) (ξ : ℕ → Fin p.S → Ω) :
    (executeCounted (oracle p P g) (algorithm p) K j ξ).2 = K ∧
      Fintype.card (Fin K × Fin p.S) = K * p.S := by
  constructor
  · exact congrArg Prod.snd (executeCounted_advance
      (oracle p P g) (algorithm p) K j ξ)
  · simp only [Fintype.card_prod, Fintype.card_fin]

end OracleTemplate.BatchIterations
