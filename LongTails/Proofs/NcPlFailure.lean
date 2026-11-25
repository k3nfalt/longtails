import LongTails.Proofs.NcPlLowerBound

open MeasureTheory OracleTemplate
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.NcPlFailure

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open LongTails.Setups.HighDimensionalStochasticNonconvexPL
open LongTails.Setups.StochasticNonconvexPL (moreauResidual)
open LongTails.Proofs.NcPlInstance LongTails.Proofs.NcPlMoreau
open LongTails.Proofs.NcPlOracle LongTails.Proofs.NcPlHiding
open LongTails.Proofs.NcPlParams LongTails.Proofs.NcPlLowerBound
open LongTails.Proofs.AbcHardFunction (Space)
open LongTails.Proofs.AbcHardOracle (unif)
open LongTails.Proofs.AbcHardExecution (coinCount)
open LongTails.Proofs.AbcLowerMeasure (stream coinCount_tail coinCount_measurable)
open LongTails.Proofs.FiniteSumNondualLowerAveraging LongTails.Proofs.FiniteSumNondualLowerBound

variable (q : Params)

noncomputable def qryOf (A : Algorithm (Space q.d × Space q.d) (Space q.d × Space q.d) (Space q.d))
    (s : A.State) : Space q.d × Space q.d := (ux q (A.query s).2.1, uy q (A.query s).2.2)

noncomputable def outOf (A : Algorithm (Space q.d × Space q.d) (Space q.d × Space q.d) (Space q.d))
    (s : A.State) : Space q.d := ux q (A.output s)

noncomputable def updOf (A : Algorithm (Space q.d × Space q.d) (Space q.d × Space q.d) (Space q.d))
    (s : A.State) (rp : Space q.d × Space q.d) : A.State :=
  A.update s ((ee q / ss q) • rp.1, (ee q / ss q) • rp.2)

lemma trueState_iterate (π : Fin ((geo q).k + 1) ↪ Fin q.d)
    (A : Algorithm (Space q.d × Space q.d) (Space q.d × Space q.d) (Space q.d))
    (initial : A.State) (ω : ℕ → ℝ) (N : ℕ) :
    ((fun sc : A.State × ℕ => (A.update sc.1 (GxS q π (A.query sc.1).2 (ω sc.2),
        GyS q π (A.query sc.1).2 (ω sc.2)), sc.2 + 1))^[N] (initial, 0)) =
      (trueState (th q) (qq q) π (qryOf q A) (updOf q A) initial ω N, N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

lemma execute_hard (π : Fin ((geo q).k + 1) ↪ Fin q.d)
    (A : Algorithm (Space q.d × Space q.d) (Space q.d × Space q.d) (Space q.d)) (N : ℕ)
    (seed : A.Seed) (ω : ℕ → ℝ) :
    execute (hardOracle q π) A (fun _ => N) seed ω =
      A.output (trueState (th q) (qq q) π (qryOf q A) (updOf q A) (A.initial seed) ω N) := by
  rw [execute_indexed_of_answer (hardOracle q π) A N seed ω
    (fun t query => (GxS q π query.2 (ω t), GyS q π query.2 (ω t)))
    (fun _ query => by cases query; rfl)]
  exact congrArg (fun st => A.output st.1) (trueState_iterate q π A (A.initial seed) ω N)

lemma count_target_pos (q : Params) : 1 ≤ (mm q + 1) * nm (geo q) :=
  Nat.mul_pos (Nat.succ_pos _) (nm_pos (geo q))

section Valid

variable {q} (hv : spec.valid q)

include hv

lemma good_count_fraction {N : ℕ} (hN : N ≤ lowerBudget q) :
    7 / 8 ≤ stream.real {ω | coinCount (qq q) ω N < (mm q + 1) * nm (geo q)} := by
  have hpos := count_target_pos q
  obtain ⟨M, hM⟩ : ∃ M, M + 1 = (mm q + 1) * nm (geo q) :=
    ⟨(mm q + 1) * nm (geo q) - 1, Nat.sub_add_cancel hpos⟩
  have ht := coinCount_tail (qq q) (qq_pos hv).le (qq_le_one hv) N M
  have hb := budget_count hv hN
  have hMr : ((M : ℝ) + 1) = ((mm q : ℝ) + 1) * (((nn q) / 2 + 1 : ℕ) : ℝ) := by
    have h2 : ((M + 1 : ℕ) : ℝ) = (((mm q + 1) * nm (geo q) : ℕ) : ℝ) := by rw [hM]
    push_cast at h2
    rw [h2]
    rfl
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hle : (N : ℝ) * qq q / ((M : ℝ) + 1) ≤ 1 / 8 := by
    rw [div_le_iff₀ hMpos, hMr]
    linarith
  have hc : {ω : ℕ → ℝ | coinCount (qq q) ω N < (mm q + 1) * nm (geo q)} =
      {ω | M + 1 ≤ coinCount (qq q) ω N}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    omega
  have hmeas : MeasurableSet {ω : ℕ → ℝ | M + 1 ≤ coinCount (qq q) ω N} := by
    have h := (coinCount_measurable (qq q) N)
      (measurableSet_Ici : MeasurableSet (Set.Ici (((M + 1 : ℕ) : ℝ))))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ici]
    constructor <;> intro h <;> exact_mod_cast h
  rw [hc, measureReal_compl hmeas, probReal_univ]
  linarith

lemma bad_fraction {N : ℕ} (hN : N ≤ lowerBudget q) {St : Type*}
    (query : St → Space q.d × Space q.d) (output : St → Space q.d)
    (update : St → Space q.d × Space q.d → St) (initial : St) (ω : ℕ → ℝ) :
    8 * (∑ w : CoordinateWords q.d (geo q).k, if coordinateBad (G := geo q) (th q) (qq q) query
      output update initial ω N (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      Fintype.card (CoordinateWords q.d (geo q).k) := by
  have hroom := dimension_room hv hN
  have hth := th_pos q
  let D : ℝ := q.d - (((geo q).k + 1 : ℕ) : ℝ)
  have hBx := (geo q).hBx
  have hBy := (geo q).hBy
  have hX0 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) * (((geo q).k + 1 : ℕ) : ℝ) *
      ((2 * (geo q).Bx + 2 * (geo q).By) ^ 2 / th q ^ 2) := by positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    linarith
  have hDs : D + (((geo q).k + 1 : ℕ) : ℝ) ≤ q.d := by
    dsimp only [D]
    linarith
  have hb := bad_sum_bound (G := geo q) hth (qq q) query output update initial ω N D hD hDs
  have hsize : 8 * (((N + 1 : ℕ) : ℝ) * (((geo q).k + 1 : ℕ) : ℝ) *
      ((2 * (geo q).Bx + 2 * (geo q).By) ^ 2 / th q ^ 2)) ≤ D := by
    dsimp only [D]
    linarith
  have hcard : (0 : ℝ) ≤ Fintype.card (CoordinateWords q.d (geo q).k) := Nat.cast_nonneg _
  have hsum : 0 ≤ ∑ w : CoordinateWords q.d (geo q).k, if coordinateBad (G := geo q) (th q) (qq q)
      query output update initial ω N (coordinateEmbedding w) then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  by_contra hcon
  push Not at hcon
  have h1 := mul_le_mul_of_nonneg_right hsize hsum
  have h2 := mul_lt_mul_of_pos_left hcon hX0
  nlinarith

theorem exists_failure
    (A : Algorithm (Space q.d × Space q.d) (Space q.d × Space q.d) (Space q.d)) (N : ℕ)
    (hN : N ≤ lowerBudget q) :
    ∃ π : Fin ((geo q).k + 1) ↪ Fin q.d,
      ¬ spec.successful q (hardFn q π)
        (fun w : A.Seed × ((k : ℕ) → (hardOracle q π).Seed k) =>
          execute (hardOracle q π) A (fun _ => N) w.1 w.2)
        ⟨(A.law : Measure _).prod ((hardOracle q π).law : Measure _), inferInstance⟩ := by
  have hε := pos_ε hv
  let W := CoordinateWords q.d (geo q).k
  by_contra hcon
  push Not at hcon
  let P : Measure (A.Seed × (ℕ → ℝ)) := (A.law : Measure A.Seed).prod stream
  let loss : W → A.Seed × (ℕ → ℝ) → ℝ := fun w z =>
    moreauResidual (hardFn q (coordinateEmbedding w)) q.L
      (A.output (trueState (th q) (qq q) (coordinateEmbedding w) (qryOf q A) (updOf q A)
        (A.initial z.1) z.2 N))
  have hloss (w : W) : (fun z : A.Seed × (ℕ → ℝ) =>
      moreauResidual (hardFn q (coordinateEmbedding w)) q.L
        (execute (hardOracle q (coordinateEmbedding w)) A (fun _ => N) z.1 z.2)) = loss w := by
    funext z
    rw [execute_hard]
  have hi (w : W) : Integrable (loss w) P := by
    have h := (hcon (coordinateEmbedding w)).2.1
    rw [← hloss w]
    exact h
  have hle (w : W) : ∫ z, loss w z ∂P ≤ q.ε := by
    have h := (hcon (coordinateEmbedding w)).2.2
    rw [← hloss w]
    exact h
  have hnonneg (w : W) (z : A.Seed × (ℕ → ℝ)) : 0 ≤ loss w z := by
    dsimp only [loss]
    unfold moreauResidual
    exact mul_nonneg (mul_nonneg (by norm_num) (pos_L hv).le) Metric.infDist_nonneg
  let good : A.Seed × (ℕ → ℝ) → ℝ := fun z =>
    Set.indicator {z : A.Seed × (ℕ → ℝ) | coinCount (qq q) z.2 N < (mm q + 1) * nm (geo q)} 1 z
  have hpt (z : A.Seed × (ℕ → ℝ)) :
      2 * q.ε * (7 / 8) * Fintype.card W * good z ≤ ∑ w, loss w z := by
    by_cases hz : coinCount (qq q) z.2 N < (mm q + 1) * nm (geo q)
    · have hg : good z = 1 := by simp [good, hz]
      rw [hg, mul_one]
      have hlev : lvl (geo q) (qq q) z.2 N < (geo q).k + 1 := lvl_of_count (geo q) _ _ _ hz
      have hbad := bad_fraction hv hN (qryOf q A) (outOf q A) (updOf q A) (A.initial z.1) z.2
      have hgood (w : W) : ¬ coordinateBad (G := geo q) (th q) (qq q) (qryOf q A) (outOf q A)
          (updOf q A) (A.initial z.1) z.2 N (coordinateEmbedding w) → 2 * q.ε ≤ loss w z := by
        intro hw
        have h := good_output (G := geo q) (th_pos q).le (th_le_rho q) (th_le_quarter q)
          (qryOf q A) (outOf q A) (updOf q A) (A.initial z.1) z.2 N (coordinateEmbedding w) hw hlev
        exact moreau_big hv (coordinateEmbedding w) _ h
      have hterm (w : W) : 2 * q.ε * (1 - if coordinateBad (G := geo q) (th q) (qq q) (qryOf q A)
          (outOf q A) (updOf q A) (A.initial z.1) z.2 N (coordinateEmbedding w)
          then (1 : ℝ) else 0) ≤ loss w z := by
        by_cases hw : coordinateBad (G := geo q) (th q) (qq q) (qryOf q A) (outOf q A)
            (updOf q A) (A.initial z.1) z.2 N (coordinateEmbedding w)
        · simp only [hw, ↓reduceIte, sub_self, mul_zero]
          exact hnonneg w z
        · simp only [hw, ↓reduceIte, sub_zero, mul_one]
          exact hgood w hw
      have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset W)) => hterm w)
      simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one] at hs
      have hεp : 0 ≤ 2 * q.ε := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hbad hεp]
    · have hg : good z = 0 := by simp [good, hz]
      rw [hg, mul_zero]
      exact Finset.sum_nonneg (fun w _ => hnonneg w z)
  have hsetmeas : MeasurableSet {ω : ℕ → ℝ | coinCount (qq q) ω N < (mm q + 1) * nm (geo q)} := by
    have h := (coinCount_measurable (qq q) N)
      (measurableSet_Iio (a := ((((mm q + 1) * nm (geo q) : ℕ)) : ℝ)))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iio]
    constructor <;> intro h <;> exact_mod_cast h
  have hgoodmeas : MeasurableSet
      {z : A.Seed × (ℕ → ℝ) | coinCount (qq q) z.2 N < (mm q + 1) * nm (geo q)} :=
    measurable_snd hsetmeas
  have hgood_int : ∫ z, good z ∂P =
      stream.real {ω | coinCount (qq q) ω N < (mm q + 1) * nm (geo q)} := by
    rw [integral_indicator_one hgoodmeas]
    have hm : P.map Prod.snd = stream := by
      dsimp only [P]
      rw [Measure.map_snd_prod]
      simp
    have hpre : {z : A.Seed × (ℕ → ℝ) | coinCount (qq q) z.2 N < (mm q + 1) * nm (geo q)} =
        Prod.snd ⁻¹' {ω | coinCount (qq q) ω N < (mm q + 1) * nm (geo q)} := rfl
    rw [hpre, Measure.real, ← Measure.map_apply measurable_snd hsetmeas, hm]
    rfl
  have hfrac := good_count_fraction hv hN
  have hint_good : Integrable (fun z => 2 * q.ε * (7 / 8) * Fintype.card W * good z) P :=
    ((integrable_const (1 : ℝ)).indicator hgoodmeas).const_mul _
  have hint_sum : Integrable (fun z => ∑ w, loss w z) P :=
    integrable_finsetSum Finset.univ (fun w _ => hi w)
  have hmono := integral_mono hint_good hint_sum hpt
  rw [integral_const_mul, hgood_int, integral_finsetSum Finset.univ (fun w _ => hi w)] at hmono
  have hsum : (∑ w : W, ∫ z, loss w z ∂P) ≤ Fintype.card W * q.ε := by
    calc _ ≤ ∑ _w : W, q.ε := Finset.sum_le_sum (fun w _ => hle w)
      _ = _ := by simp
  have hd : (geo q).k + 1 ≤ q.d := by
    have h := dimension_room hv hN
    have hth := th_pos q
    have hX0 : (0 : ℝ) ≤ 8 * (((N + 1 : ℕ) : ℝ) * (((geo q).k + 1 : ℕ) : ℝ) *
        ((2 * (geo q).Bx + 2 * (geo q).By) ^ 2 / th q ^ 2)) := by positivity
    have hT : (((geo q).k + 1 : ℕ) : ℝ) ≤ q.d := by linarith
    exact_mod_cast hT
  have hc : (0 : ℝ) < Fintype.card W := by
    exact_mod_cast coordinateWords_card_pos q.d (geo q).k hd
  have hm1 := mul_le_mul_of_nonneg_left hfrac
    (by positivity : (0 : ℝ) ≤ 2 * q.ε * (7 / 8) * Fintype.card W)
  nlinarith

end Valid

end LongTails.Proofs.NcPlFailure
