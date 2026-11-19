import LongTails.Proofs.StochasticMintyHiding
import LongTails.Proofs.StochasticMintyParameters
import LongTails.Proofs.AbcLowerMeasure
import LongTails.Proofs.Execution
import LongTails.TemplateLowerBound

open MeasureTheory OracleTemplate
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.StochasticMintyLowerBound

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open LongTails.Setups.HighDimensionalStochasticWeakMinty
open LongTails.Proofs.MintyChainGeometry LongTails.Proofs.StochasticMintyOracle
open LongTails.Proofs.StochasticMintyHiding LongTails.Proofs.StochasticMintyParameters
open LongTails.Proofs.AbcHardOracle (unif)
open LongTails.Proofs.AbcHardExecution (coinCount level)
open LongTails.Proofs.AbcLowerMeasure (stream stream_iid coinCount_tail coinCount_measurable)
open LongTails.Proofs.FiniteSumNondualLowerAveraging LongTails.Proofs.FiniteSumNondualLowerBound

noncomputable def hardField (q : Params) (π : Fin (chainDim q + 1) ↪ Fin q.d)
    (x : EuclideanSpace ℝ (Fin q.d)) : EuclideanSpace ℝ (Fin q.d) :=
  field (strength q) (width q) (wall q) π (x - q.x0)

noncomputable def hardReply (q : Params) (π : Fin (chainDim q + 1) ↪ Fin q.d)
    (x : EuclideanSpace ℝ (Fin q.d)) (ω : ℝ) : EuclideanSpace ℝ (Fin q.d) :=
  reply (strength q) (width q) (wall q) (revealBar q) π (x - q.x0) ω

noncomputable def hardOracle (q : Params) (π : Fin (chainDim q + 1) ↪ Fin q.d) :
    Oracle (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d)) where
  Seed := fun _ => ℝ
  law := ⟨stream, inferInstance⟩
  answer := fun _ (_, x) ω => hardReply q π x ω

lemma hard_rad (q : Params) (hv : spec.valid q) :
    4 * ((chainDim q : ℝ) + 1) * width q ^ 2 ≤ wall q ^ 2 := by
  rw [wall_sq]
  have hc : ((chainDim q : ℝ) + 1) = links q := by
    rw [← chainDim_succ q hv]; push_cast; ring
  rw [hc]

lemma hard_admissible (q : Params) (hv : spec.valid q) (π : Fin (chainDim q + 1) ↪ Fin q.d) :
    spec.admissible q (hardField q π) (hardOracle q π) := by
  have hκ := strength_pos q hv
  have hr := width_pos q hv
  have hB := wall_pos q hv
  have hq0 := revealBar_pos q hv
  have hq1 := revealBar_le q hv
  have hrad := hard_rad q hv
  have hR := pos_R q hv
  have hρ : 0 ≤ q.ρ := hv.1.2.1
  refine ⟨hardReply q π,
    ⟨unif, inferInstanceAs (IsProbabilityMeasure unif)⟩,
    ⟨stream, inferInstanceAs (IsProbabilityMeasure stream)⟩, stream_iid, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try dsimp only [toGeneral]
  · intro x y
    have h := field_lipschitz (strength q) (width q) (wall q) hκ.le hr hB π (x - q.x0) (y - q.x0)
    rw [sub_sub_sub_cancel_right] at h
    have hL : 6 * strength q = q.L := by unfold strength; ring
    rw [hL] at h
    exact h
  · refine ⟨q.x0 + target (width q) π, ?_, ?_, ?_⟩
    · change field (strength q) (width q) (wall q) π (q.x0 + target (width q) π - q.x0) = 0
      rw [add_sub_cancel_left]
      exact field_target (strength q) (width q) (wall q) hr.le hB.le π hrad
    · change ‖q.x0 + target (width q) π - q.x0‖ ≤ q.R
      rw [add_sub_cancel_left]
      have h := target_norm_sq (width q) π
      have hk : ((chainDim q : ℝ) + 1) * width q ^ 2 ≤ q.R ^ 2 := by
        have hc : ((chainDim q : ℝ) + 1) = links q := by
          rw [← chainDim_succ q hv]; push_cast; ring
        rw [hc]
        exact links_width q hv
      have hs : ‖target (width q) π‖ ^ 2 ≤ q.R ^ 2 := by rw [h]; exact hk
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR.le two_ne_zero).mp hs
    · intro x
      have h := field_minty (strength q) (width q) (wall q) hκ.le hr hB π hrad (x - q.x0)
      have e : x - (q.x0 + target (width q) π) = x - q.x0 - target (width q) π := by abel
      change -q.ρ * ‖hardField q π x‖ ^ 2 ≤ ⟪hardField q π x, x - (q.x0 + target (width q) π)⟫
      rw [e]
      have : 0 ≤ q.ρ * ‖hardField q π x‖ ^ 2 := by positivity
      unfold hardField at this ⊢
      linarith
  · have he : Function.uncurry (hardReply q π) =
        Function.uncurry (reply (strength q) (width q) (wall q) (revealBar q) π) ∘
          (fun z : EuclideanSpace ℝ (Fin q.d) × ℝ => (z.1 - q.x0, z.2)) := by
      funext z
      rfl
    rw [he]
    exact (reply_measurable _ _ _ _ hκ.le hr hB π).comp
      ((measurable_fst.sub_const q.x0).prodMk measurable_snd)
  · intro x
    exact reply_integrable _ _ _ _ π (x - q.x0)
  · intro x
    exact reply_integral _ _ _ _ hq0 hq1 π (x - q.x0)
  · intro x
    exact reply_variance_integrable _ _ _ _ π (x - q.x0)
  · intro x
    have h := reply_variance (strength q) (width q) (wall q) (revealBar q) hκ.le hr hq0 hq1 π
      (x - q.x0)
    rw [revealBar_variance q hv] at h
    exact h

lemma trueState_iterate (q : Params) (π : Fin (chainDim q + 1) ↪ Fin q.d) {St : Type*}
    (query : St → EuclideanSpace ℝ (Fin q.d)) (update : St → EuclideanSpace ℝ (Fin q.d) → St)
    (initial : St) (ω : ℕ → ℝ) (N : ℕ) :
    ((fun sc : St × ℕ => (update sc.1 (reply (strength q) (width q) (wall q) (revealBar q) π
        (query sc.1 - q.x0) (ω sc.2)), sc.2 + 1))^[N] (initial, 0)) =
      (trueState (strength q) (width q) (wall q) (revealBar q) π (fun s => query s - q.x0) update
        initial ω N, N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

lemma execute_hard (q : Params) (π : Fin (chainDim q + 1) ↪ Fin q.d)
    (A : Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d))) (N : ℕ) (seed : A.Seed) (ω : ℕ → ℝ) :
    execute (hardOracle q π) A (fun _ => N) seed ω =
      A.output (trueState (strength q) (width q) (wall q) (revealBar q) π
        (fun s => (A.query s).2 - q.x0) A.update (A.initial seed) ω N) := by
  rw [execute_indexed_of_answer (hardOracle q π) A N seed ω
    (fun t query => hardReply q π query.2 (ω t))
    (fun _ query => by cases query; rfl)]
  exact congrArg (fun st => A.output st.1) (trueState_iterate q π (fun s => (A.query s).2)
    A.update (A.initial seed) ω N)

lemma good_count_fraction (q : Params) (hv : spec.valid q) (N : ℕ) (hN : N ≤ lowerBudget q) :
    7 / 8 ≤ stream.real {ω | coinCount (revealBar q) ω N ≤ chainDim q} := by
  have ht := coinCount_tail (revealBar q) (revealBar_pos q hv).le (revealBar_le q hv) N
    (chainDim q)
  have hb := reveal_tail q hv N hN
  have hc : {ω : ℕ → ℝ | coinCount (revealBar q) ω N ≤ chainDim q} =
      {ω | chainDim q + 1 ≤ coinCount (revealBar q) ω N}ᶜ := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]; omega
  have hmeas : MeasurableSet {ω : ℕ → ℝ | chainDim q + 1 ≤ coinCount (revealBar q) ω N} := by
    have h := (coinCount_measurable (revealBar q) N)
      (measurableSet_Ici : MeasurableSet (Set.Ici (((chainDim q + 1 : ℕ) : ℝ))))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ici]
    constructor <;> intro h <;> exact_mod_cast h
  rw [hc, measureReal_compl hmeas, probReal_univ]
  linarith

lemma bad_fraction (q : Params) (hv : spec.valid q) (N : ℕ) (hN : N ≤ lowerBudget q)
    {St : Type*} (query output : St → EuclideanSpace ℝ (Fin q.d))
    (update : St → EuclideanSpace ℝ (Fin q.d) → St) (initial : St) (ω : ℕ → ℝ) :
    8 * (∑ w : CoordinateWords q.d (chainDim q), if coordinateBad (strength q) (width q) (wall q)
      (revealBar q) query output update initial ω N (coordinateEmbedding w) then (1 : ℝ)
      else 0) ≤ Fintype.card (CoordinateWords q.d (chainDim q)) := by
  have hroom := dimension_room q hv N hN
  set n := chainDim q
  let D : ℝ := q.d - (n + 1 : ℕ)
  have hpos : (0 : ℝ) ≤ 8 * (((N + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * (64 * ((n + 1 : ℕ) : ℝ))) := by
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    linarith
  have hDs : D + (n + 1 : ℕ) ≤ q.d := by dsimp only [D]; linarith
  have hb := bad_sum_bound (strength q) (width q) (wall q) (revealBar q) (wall_pos q hv).le
    (width_pos q hv) query output update initial ω N D hD hDs
  have hR : wall q ^ 2 / (width q / 4) ^ 2 = 64 * ((n + 1 : ℕ) : ℝ) := by
    have hw := width_pos q hv
    rw [wall_sq]
    have hc : (links q : ℝ) = ((n + 1 : ℕ) : ℝ) := by rw [chainDim_succ q hv]
    rw [hc]
    field_simp
    ring
  rw [hR] at hb
  have hsize : 8 * (((N + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * (64 * ((n + 1 : ℕ) : ℝ))) ≤ D := by
    dsimp only [D]; linarith
  have hcard : (0 : ℝ) ≤ Fintype.card (CoordinateWords q.d n) := Nat.cast_nonneg _
  have hsum : 0 ≤ ∑ w : CoordinateWords q.d n, if coordinateBad (strength q) (width q) (wall q)
      (revealBar q) query output update initial ω N (coordinateEmbedding w) then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  by_contra hcon
  push Not at hcon
  have h1 := mul_le_mul_of_nonneg_right hsize hsum
  have hX : 0 < ((N + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * (64 * ((n + 1 : ℕ) : ℝ)) := by
    positivity
  have h2 := mul_lt_mul_of_pos_left hcon hX
  linarith

lemma exists_failure (q : Params) (hv : spec.valid q)
    (A : Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d))) (N : ℕ) (hN : N ≤ lowerBudget q) :
    ∃ π : Fin (chainDim q + 1) ↪ Fin q.d,
      ¬ spec.successful q (hardField q π)
        (fun w : A.Seed × ((k : ℕ) → (hardOracle q π).Seed k) =>
          execute (hardOracle q π) A (fun _ => N) w.1 w.2)
        ⟨(A.law : Measure _).prod ((hardOracle q π).law : Measure _), inferInstance⟩ := by
  have hε := pos_ε q hv
  have hκ := strength_pos q hv
  have hr := width_pos q hv
  have hB := wall_pos q hv
  have hrad := hard_rad q hv
  have hgap := floor_gap q hv
  set n := chainDim q
  let query : A.State → EuclideanSpace ℝ (Fin q.d) := fun s => (A.query s).2 - q.x0
  let output : A.State → EuclideanSpace ℝ (Fin q.d) := fun s => A.output s - q.x0
  let W := CoordinateWords q.d n
  by_contra hcon
  push Not at hcon
  let P : Measure (A.Seed × (ℕ → ℝ)) := (A.law : Measure A.Seed).prod stream
  let loss : W → A.Seed × (ℕ → ℝ) → ℝ := fun w z =>
    ‖field (strength q) (width q) (wall q) (coordinateEmbedding w)
      (output (trueState (strength q) (width q) (wall q) (revealBar q) (coordinateEmbedding w)
        query A.update (A.initial z.1) z.2 N))‖
  have hloss (w : W) : (fun z : A.Seed × (ℕ → ℝ) => ‖hardField q (coordinateEmbedding w)
      (execute (hardOracle q (coordinateEmbedding w)) A (fun _ => N) z.1 z.2)‖) = loss w := by
    funext z
    rw [execute_hard]
    rfl
  have hi (w : W) : Integrable (loss w) P := by
    have h := (hcon (coordinateEmbedding w)).1
    rw [← hloss w]
    exact h
  have hle (w : W) : ∫ z, loss w z ∂P ≤ q.ε := by
    have h := (hcon (coordinateEmbedding w)).2
    rw [← hloss w]
    exact h
  let good : A.Seed × (ℕ → ℝ) → ℝ := fun z =>
    Set.indicator {z : A.Seed × (ℕ → ℝ) | coinCount (revealBar q) z.2 N ≤ n} 1 z
  have hpt (z : A.Seed × (ℕ → ℝ)) :
      2 * q.ε * (7 / 8) * Fintype.card W * good z ≤ ∑ w, loss w z := by
    by_cases hz : coinCount (revealBar q) z.2 N ≤ n
    · have hg : good z = 1 := by simp [good, hz]
      rw [hg, mul_one]
      have hlev : level n (revealBar q) z.2 N < n + 1 := by
        have := min_le_right (n + 1) (coinCount (revealBar q) z.2 N)
        unfold level
        omega
      have hbad := bad_fraction q hv N hN query output A.update (A.initial z.1) z.2
      have hgood (w : W) : ¬ coordinateBad (strength q) (width q) (wall q) (revealBar q) query
          output A.update (A.initial z.1) z.2 N (coordinateEmbedding w) → 2 * q.ε ≤ loss w z := by
        intro hw
        have h := good_floor (strength q) (width q) (wall q) (revealBar q) hκ hr hB hrad query
          output A.update (A.initial z.1) z.2 N (coordinateEmbedding w) hw hlev
        have h2 : (2 * q.ε) ^ 2 ≤ loss w z ^ 2 := by
          dsimp only [loss]
          nlinarith
        exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h2
      have hterm (w : W) : 2 * q.ε * (1 - if coordinateBad (strength q) (width q) (wall q)
          (revealBar q) query output A.update (A.initial z.1) z.2 N (coordinateEmbedding w)
          then (1 : ℝ) else 0) ≤ loss w z := by
        by_cases hw : coordinateBad (strength q) (width q) (wall q) (revealBar q) query output
            A.update (A.initial z.1) z.2 N (coordinateEmbedding w)
        · simp only [hw, ↓reduceIte, sub_self, mul_zero]; exact norm_nonneg _
        · simp only [hw, ↓reduceIte, sub_zero, mul_one]; exact hgood w hw
      have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset W)) => hterm w)
      simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one] at hs
      have hεp : 0 ≤ 2 * q.ε := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hbad hεp]
    · have hg : good z = 0 := by simp [good, hz]
      rw [hg, mul_zero]
      exact Finset.sum_nonneg (fun w _ => norm_nonneg _)
  have hsetmeas : MeasurableSet {ω : ℕ → ℝ | coinCount (revealBar q) ω N ≤ n} := by
    have h := (coinCount_measurable (revealBar q) N) (measurableSet_Iic (a := ((n : ℕ) : ℝ)))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> exact_mod_cast h
  have hgoodmeas : MeasurableSet {z : A.Seed × (ℕ → ℝ) | coinCount (revealBar q) z.2 N ≤ n} :=
    measurable_snd hsetmeas
  have hgood_int : ∫ z, good z ∂P = stream.real {ω | coinCount (revealBar q) ω N ≤ n} := by
    rw [integral_indicator_one hgoodmeas]
    have hm : P.map Prod.snd = stream := by
      dsimp only [P]; rw [Measure.map_snd_prod]; simp
    have hpre : {z : A.Seed × (ℕ → ℝ) | coinCount (revealBar q) z.2 N ≤ n} =
        Prod.snd ⁻¹' {ω | coinCount (revealBar q) ω N ≤ n} := rfl
    rw [hpre, Measure.real, ← Measure.map_apply measurable_snd hsetmeas, hm]
    rfl
  have hfrac := good_count_fraction q hv N hN
  have hint_good : Integrable (fun z => 2 * q.ε * (7 / 8) * Fintype.card W * good z) P :=
    ((integrable_const (1 : ℝ)).indicator hgoodmeas).const_mul _
  have hint_sum : Integrable (fun z => ∑ w, loss w z) P :=
    integrable_finsetSum Finset.univ (fun w _ => hi w)
  have hmono := integral_mono hint_good hint_sum hpt
  rw [integral_const_mul, hgood_int, integral_finsetSum Finset.univ (fun w _ => hi w)] at hmono
  have hsum : (∑ w : W, ∫ z, loss w z ∂P) ≤ Fintype.card W * q.ε := by
    calc _ ≤ ∑ _w : W, q.ε := Finset.sum_le_sum (fun w _ => hle w)
      _ = _ := by simp
  have hd : n + 1 ≤ q.d := by
    have h := dimension_room q hv N hN
    have hpos : (0 : ℝ) ≤ 8 * (((N + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
        (64 * ((n + 1 : ℕ) : ℝ))) := by positivity
    have hT : ((n + 1 : ℕ) : ℝ) ≤ q.d := by
      linarith
    exact_mod_cast hT
  have hc : (0 : ℝ) < Fintype.card W := by exact_mod_cast coordinateWords_card_pos q.d n hd
  have hm1 := mul_le_mul_of_nonneg_left hfrac
    (by positivity : (0 : ℝ) ≤ 2 * q.ε * (7 / 8) * Fintype.card W)
  nlinarith

end LongTails.Proofs.StochasticMintyLowerBound
