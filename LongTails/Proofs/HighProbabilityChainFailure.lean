import LongTails.Proofs.AbcLowerBound

open MeasureTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.HighProbabilityChainFailure

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open LongTails.Proofs.AbcChain LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardGeometry
open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcHardSimulation
open LongTails.Proofs.AbcHardExecution LongTails.Proofs.AbcHardCounting
open LongTails.Proofs.AbcLowerMeasure LongTails.Proofs.AbcLowerParameters
open LongTails.Proofs.AbcLowerAssembly LongTails.Proofs.FiniteSumNondualLowerAveraging
open LongTails.Proofs.FiniteSumNondualLowerBound LongTails.Proofs.AbcLowerBound
open LongTails.Setups.HighDimensionalAbcNoiseNonconvex

lemma hard_gradient_continuous (q : Params) (hv : spec.valid q)
    (π : Fin (chainDim q + 1) ↪ Fin q.d) :
    Continuous (gradient (objective (scaleOf q hv.1 hv.2.2.2.2.1) π q.x0)) := by
  obtain ⟨_, _, _, _, -, -, -, hlip, -⟩ := hard_admissible q hv π
  have hK : LipschitzWith ⟨q.L, hv.1.le⟩
      (gradient (objective (scaleOf q hv.1 hv.2.2.2.2.1) π q.x0)) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm]
      exact hlip x y
  exact hK.continuous

lemma exists_hp_failure (q : Params) (hv : spec.valid q)
    (A : Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d))) (N : ℕ) (hN : N ≤ lowerBudget q) :
    ∃ π : Fin (chainDim q + 1) ↪ Fin q.d,
      ¬ (Measurable (fun w : A.Seed × (ℕ → ℝ) =>
          execute (hardOracle q (scaleOf q hv.1 hv.2.2.2.2.1) π) A (fun _ => N) w.1 w.2) ∧
        3 / 4 ≤ ((A.law : Measure A.Seed).prod stream).real
          {w | ‖gradient (objective (scaleOf q hv.1 hv.2.2.2.2.1) π q.x0)
            (execute (hardOracle q (scaleOf q hv.1 hv.2.2.2.2.1) π) A (fun _ => N) w.1 w.2)‖ ≤
              q.ε}) := by
  have hε := hv.2.2.2.2.1
  have hn1 := chainDim_succ q hv
  set S := scaleOf q hv.1 hε
  set n := chainDim q
  set qf := revealProb q n
  set qbar := revealBar q
  set Mh := n / 2
  let query : A.State → Space q.d := fun s => (A.query s).2
  let W := CoordinateWords q.d n
  have hratio : S.a / S.lam = 60 * q.ε := amplitude_ratio q hv.1 hε
  by_contra hcon
  push Not at hcon
  let P : Measure (A.Seed × (ℕ → ℝ)) := (A.law : Measure A.Seed).prod stream
  let loss : W → A.Seed × (ℕ → ℝ) → ℝ := fun w z =>
    ‖objGrad S (coordinateEmbedding w) q.x0 (A.output (trueState S qf (coordinateEmbedding w)
      q.x0 query A.update (A.initial z.1) z.2 N))‖
  have hloss (w : W) : (fun z : A.Seed × (ℕ → ℝ) => ‖gradient (objective S (coordinateEmbedding w)
      q.x0) (execute (hardOracle q S (coordinateEmbedding w)) A (fun _ => N) z.1 z.2)‖) = loss w := by
    funext z
    rw [objective_gradient, execute_hard]
  have hmeas (w : W) : Measurable (loss w) := by
    rw [← hloss w]
    exact ((hard_gradient_continuous q hv (coordinateEmbedding w)).measurable.comp
      (hcon (coordinateEmbedding w)).1).norm
  have hle (w : W) : 3 / 4 ≤ P.real {z | loss w z ≤ q.ε} := by
    have h := (hcon (coordinateEmbedding w)).2
    have hs : {z : A.Seed × (ℕ → ℝ) | ‖gradient (objective S (coordinateEmbedding w) q.x0)
        (execute (hardOracle q S (coordinateEmbedding w)) A (fun _ => N) z.1 z.2)‖ ≤ q.ε} =
        {z | loss w z ≤ q.ε} := by
      ext z
      simp only [Set.mem_ofPred_eq, ← congrFun (hloss w) z]
    rw [hs] at h
    exact h
  have hlevel_meas (w : W) : MeasurableSet {z : A.Seed × (ℕ → ℝ) | q.ε < loss w z} :=
    measurableSet_lt measurable_const (hmeas w)
  have hbadprob (w : W) : P.real {z | q.ε < loss w z} ≤ 1 / 4 := by
    have hc : {z : A.Seed × (ℕ → ℝ) | q.ε < loss w z} = {z | loss w z ≤ q.ε}ᶜ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    have hm : MeasurableSet {z : A.Seed × (ℕ → ℝ) | loss w z ≤ q.ε} :=
      measurableSet_le (hmeas w) measurable_const
    rw [hc, measureReal_compl hm, probReal_univ]
    linarith [hle w]
  let ind : W → A.Seed × (ℕ → ℝ) → ℝ := fun w z =>
    Set.indicator {z : A.Seed × (ℕ → ℝ) | q.ε < loss w z} 1 z
  let good : A.Seed × (ℕ → ℝ) → ℝ := fun z =>
    Set.indicator {z : A.Seed × (ℕ → ℝ) | coinCount qbar z.2 N ≤ Mh} 1 z
  have hpt (z : A.Seed × (ℕ → ℝ)) :
      (7 / 8) * Fintype.card W * good z ≤ ∑ w, ind w z := by
    by_cases hz : coinCount qbar z.2 N ≤ Mh
    · have hg : good z = 1 := by simp [good, hz]
      rw [hg, mul_one]
      have hlev : level n qbar z.2 N < n + 1 := by
        have := min_le_right (n + 1) (coinCount qbar z.2 N)
        unfold level
        omega
      have hq : ∀ m, m ≤ level n qbar z.2 N → qf m ≤ qbar := by
        intro m hm
        have hm' : m ≤ (chainLength q - 1) / 2 := by
          have := min_le_right (n + 1) (coinCount qbar z.2 N)
          have h2 : m ≤ Mh := by unfold level at hm; omega
          simpa [Mh, n, chainDim] using h2
        exact revealProb_le_bar q hε n m (half_le_level q hv m hm')
      have hbad := bad_fraction q hv N hN S query A.output A.update (A.initial z.1) z.2
      have hterm (w : W) : (1 - if coordinateBad S qf q.x0 query A.output A.update
          (A.initial z.1) qbar z.2 N (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ ind w z := by
        by_cases hw : coordinateBad S qf q.x0 query A.output A.update (A.initial z.1) qbar z.2 N
            (coordinateEmbedding w)
        · simp only [hw, ↓reduceIte, sub_self, ind]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) z
        · simp only [hw, ↓reduceIte, sub_zero]
          have h := good_gradient S qf q.x0 query A.output A.update (A.initial z.1) qbar z.2 N
            (coordinateEmbedding w) hw hlev hq
          rw [hratio] at h
          have hlt : q.ε < loss w z := by
            dsimp only [loss]
            linarith
          have hin : z ∈ {z : A.Seed × (ℕ → ℝ) | q.ε < loss w z} := hlt
          simp only [ind, Set.indicator_of_mem hin, Pi.one_apply, le_refl]
      have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset W)) => hterm w)
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one] at hs
      linarith
    · have hg : good z = 0 := by simp [good, hz]
      rw [hg, mul_zero]
      exact Finset.sum_nonneg (fun w _ => Set.indicator_nonneg (fun _ _ => zero_le_one) z)
  have hsetmeas : MeasurableSet {ω : ℕ → ℝ | coinCount qbar ω N ≤ Mh} := by
    have h := (coinCount_measurable qbar N) (measurableSet_Iic (a := ((Mh : ℕ) : ℝ)))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> exact_mod_cast h
  have hgoodmeas : MeasurableSet {z : A.Seed × (ℕ → ℝ) | coinCount qbar z.2 N ≤ Mh} :=
    measurable_snd hsetmeas
  have hgood_int : ∫ z, good z ∂P = stream.real {ω | coinCount qbar ω N ≤ Mh} := by
    rw [integral_indicator_one hgoodmeas]
    have hm : P.map Prod.snd = stream := by
      dsimp only [P]; rw [Measure.map_snd_prod]; simp
    have hpre : {z : A.Seed × (ℕ → ℝ) | coinCount qbar z.2 N ≤ Mh} =
        Prod.snd ⁻¹' {ω | coinCount qbar ω N ≤ Mh} := rfl
    rw [hpre, Measure.real, ← Measure.map_apply measurable_snd hsetmeas, hm]
    rfl
  have hind_int (w : W) : ∫ z, ind w z ∂P = P.real {z | q.ε < loss w z} :=
    integral_indicator_one (hlevel_meas w)
  have hint_ind (w : W) : Integrable (ind w) P :=
    (integrable_const (1 : ℝ)).indicator (hlevel_meas w)
  have hfrac := good_count_fraction q hv N hN
  have hint_good : Integrable (fun z => (7 / 8) * Fintype.card W * good z) P :=
    ((integrable_const (1 : ℝ)).indicator hgoodmeas).const_mul _
  have hint_sum : Integrable (fun z => ∑ w, ind w z) P :=
    integrable_finsetSum Finset.univ (fun w _ => hint_ind w)
  have hmono := integral_mono hint_good hint_sum hpt
  rw [integral_const_mul, hgood_int, integral_finsetSum Finset.univ (fun w _ => hint_ind w)]
    at hmono
  have hsum : (∑ w : W, ∫ z, ind w z ∂P) ≤ Fintype.card W * (1 / 4) := by
    calc _ ≤ ∑ _w : W, (1 / 4 : ℝ) :=
          Finset.sum_le_sum (fun w _ => (hind_int w).trans_le (hbadprob w))
      _ = _ := by simp
  have hd : n + 1 ≤ q.d := by
    have h := dimension_room q hv N hN
    have hT : ((n + 1 : ℕ) : ℝ) ≤ q.d := by
      rw [hn1]
      nlinarith [pow_nonneg (Nat.cast_nonneg (chainLength q) : (0 : ℝ) ≤ chainLength q) 3,
        (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact_mod_cast hT
  have hc : (0 : ℝ) < Fintype.card W := by exact_mod_cast coordinateWords_card_pos q.d n hd
  have hm1 := mul_le_mul_of_nonneg_left hfrac
    (by positivity : (0 : ℝ) ≤ (7 / 8) * Fintype.card W)
  nlinarith

end LongTails.Proofs.HighProbabilityChainFailure
