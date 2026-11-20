import LongTails.Proofs.ThirdOrderLowerAssembly

open MeasureTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.ThirdOrderLowerBound

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open LongTails.Proofs.ThirdOrderMaskedOracle LongTails.Proofs.ThirdOrderMaskedExecution
open LongTails.Proofs.ThirdOrderMaskedScaling LongTails.Proofs.ThirdOrderLowerParameters
open LongTails.Proofs.ThirdOrderLowerAssembly
open LongTails.Proofs.RelativeHessianLocalized (radius)
open LongTails.Proofs.AbcHardOracle (Scale toUnit)
open LongTails.Proofs.AbcHardExecution (coinCount)
open LongTails.Proofs.AbcLowerMeasure
open LongTails.Proofs.FiniteSumNondualLowerAveraging LongTails.Proofs.FiniteSumNondualLowerBound
open LongTails.Setups.HighDimensionalStochasticThirdOrderSmoothNonconvex

lemma good_count_fraction (q : Params) (hv : spec.valid q) (N : ℕ) (hN : N ≤ lowerBudget q) :
    7 / 8 ≤ stream.real {ω | coinCount (revealProb q) ω N ≤ chainDim q - 1} := by
  have hε := hv.2.2.2.2.1
  have hT := chainLength_ge q hv
  have hn1 := chainDim_succ q hv
  have ht := coinCount_tail (revealProb q) (revealProb_pos q hε).le (revealProb_le q hε) N
    (chainDim q - 1)
  have hb := budget_reveal q hv N hN
  have he : (((chainDim q - 1 : ℕ) : ℝ)) + 1 = (chainLength q : ℝ) - 1 := by
    have h1 : chainDim q - 1 + 1 = chainLength q - 1 := by unfold chainDim; omega
    have h2 : (((chainDim q - 1 + 1 : ℕ)) : ℝ) = ((chainLength q - 1 : ℕ) : ℝ) := by rw [h1]
    rw [Nat.cast_sub (by omega)] at h2
    push_cast at h2
    linarith
  rw [he] at ht
  have hpos : (0 : ℝ) < (chainLength q : ℝ) - 1 := by
    have : (8 : ℝ) ≤ chainLength q := by exact_mod_cast hT
    linarith
  have hfrac : (N : ℝ) * revealProb q / ((chainLength q : ℝ) - 1) ≤ 1 / 8 := by
    rw [div_le_iff₀ hpos]
    linarith
  have hc : {ω : ℕ → ℝ | coinCount (revealProb q) ω N ≤ chainDim q - 1} =
      {ω | chainDim q - 1 + 1 ≤ coinCount (revealProb q) ω N}ᶜ := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]; omega
  have hmeas : MeasurableSet {ω : ℕ → ℝ | chainDim q - 1 + 1 ≤ coinCount (revealProb q) ω N} := by
    have h := (coinCount_measurable (revealProb q) N)
      (measurableSet_Ici : MeasurableSet (Set.Ici (((chainDim q - 1 + 1 : ℕ) : ℝ))))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ici]
    constructor <;> intro h <;> exact_mod_cast h
  rw [hc, measureReal_compl hmeas, probReal_univ]
  linarith

lemma bad_fraction (q : Params) (hv : spec.valid q) (N : ℕ) (hN : N ≤ lowerBudget q)
    {St : Type*} (S : Scale) (query output : St → Space q.d) (update : St → Space q.d → St)
    (initial : St) (ω : ℕ → ℝ) :
    8 * (∑ w : CoordinateWords q.d (chainDim q), if coordinateBad S (revealProb q)
      q.x0 query output update initial ω N (coordinateEmbedding w) then (1 : ℝ)
      else 0) ≤ Fintype.card (CoordinateWords q.d (chainDim q)) := by
  have hroom := dimension_room q hv N hN
  have hn1 := chainDim_succ q hv
  set n := chainDim q
  have hcast : ((n + 1 : ℕ) : ℝ) = chainLength q := by rw [hn1]
  have hT0 : (0 : ℝ) ≤ chainLength q := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  let D : ℝ := q.d - (n + 1 : ℕ)
  have hD : 0 ≤ D := by
    dsimp only [D]; rw [hcast]
    nlinarith [pow_nonneg hT0 3, mul_nonneg hN0 (pow_nonneg hT0 3)]
  have hDs : D + (n + 1 : ℕ) ≤ q.d := by dsimp only [D]; linarith
  have hb := bad_sum_bound S (revealProb q) q.x0 query output update initial ω N D hD hDs
  have hR : (2 * radius n) ^ 2 / (1 / 20) ^ 2 = 1600 * 2 ^ 120 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    unfold radius; ring
  rw [hR] at hb
  have hsize : 8 * (((N + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
      (1600 * 2 ^ 120 * ((n + 1 : ℕ) : ℝ) ^ 2)) ≤ D := by
    dsimp only [D]
    rw [hcast]
    push_cast
    nlinarith [pow_nonneg hT0 3, mul_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) + 1) (pow_nonneg hT0 3)]
  have hcard : (0 : ℝ) ≤ Fintype.card (CoordinateWords q.d n) := Nat.cast_nonneg _
  have hsum : 0 ≤ ∑ w : CoordinateWords q.d n, if coordinateBad S (revealProb q) q.x0 query
      output update initial ω N (coordinateEmbedding w) then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  by_contra hcon
  push Not at hcon
  have h1 := mul_le_mul_of_nonneg_right hsize hsum
  have hn1' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hX : 0 < ((N + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * (1600 * 2 ^ 120 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    positivity
  have h2 := mul_lt_mul_of_pos_left hcon hX
  linarith

lemma exists_failure (q : Params) (hv : spec.valid q)
    (A : Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d))) (N : ℕ) (hN : N ≤ lowerBudget q) :
    ∃ π : Fin (chainDim q + 1) ↪ Fin q.d,
      ¬ spec.successful q (objective (scaleOf q hv.1 hv.2.2.2.2.1) π q.x0)
        (fun w : A.Seed × ((k : ℕ) → (hardOracle q (scaleOf q hv.1 hv.2.2.2.2.1) π).Seed k) =>
          execute (hardOracle q (scaleOf q hv.1 hv.2.2.2.2.1) π) A (fun _ => N) w.1 w.2)
        ⟨(A.law : Measure _).prod
          ((hardOracle q (scaleOf q hv.1 hv.2.2.2.2.1) π).law : Measure _), inferInstance⟩ := by
  have hε := hv.2.2.2.2.1
  have hn1 := chainDim_succ q hv
  have hT := chainLength_ge q hv
  set S := scaleOf q hv.1 hε
  set n := chainDim q
  set p := revealProb q
  set Mh := n - 1
  let query : A.State → Space q.d := fun s => (A.query s).2
  let W := CoordinateWords q.d n
  have hratio : S.a / S.lam = 5 * q.ε := amplitude_ratio q hv.1 hε
  by_contra hcon
  push Not at hcon
  let P : Measure (A.Seed × (ℕ → ℝ)) := (A.law : Measure A.Seed).prod stream
  let loss : W → A.Seed × (ℕ → ℝ) → ℝ := fun w z =>
    ‖objGrad S (coordinateEmbedding w) q.x0 (A.output (trueState S p (coordinateEmbedding w)
      q.x0 query A.update (A.initial z.1) z.2 N))‖
  have hloss (w : W) : (fun z : A.Seed × (ℕ → ℝ) => ‖gradient (objective S (coordinateEmbedding w)
      q.x0) (execute (hardOracle q S (coordinateEmbedding w)) A (fun _ => N) z.1 z.2)‖) = loss w := by
    funext z
    rw [objective_gradient, execute_hard]
  have hi (w : W) : Integrable (loss w) P := by
    have h := (hcon (coordinateEmbedding w)).2.1
    rw [← hloss w]
    exact h
  have hle (w : W) : ∫ z, loss w z ∂P ≤ q.ε := by
    have h := (hcon (coordinateEmbedding w)).2.2
    rw [← hloss w]
    exact h
  let good : A.Seed × (ℕ → ℝ) → ℝ := fun z =>
    Set.indicator {z : A.Seed × (ℕ → ℝ) | coinCount p z.2 N ≤ Mh} 1 z
  have hpt (z : A.Seed × (ℕ → ℝ)) :
      3 * q.ε * (7 / 8) * Fintype.card W * good z ≤ ∑ w, loss w z := by
    by_cases hz : coinCount p z.2 N ≤ Mh
    · have hg : good z = 1 := by simp [good, hz]
      rw [hg, mul_one]
      have hlev : lvl n p z.2 N < n + 1 := by
        have := min_le_right (n + 1) (coinCount p z.2 N + 1)
        have hn : 1 ≤ n := by simp only [n, chainDim]; omega
        unfold lvl
        omega
      have hbad := bad_fraction q hv N hN S query A.output A.update (A.initial z.1) z.2
      have hgood (w : W) : ¬ coordinateBad S p q.x0 query A.output A.update (A.initial z.1)
          z.2 N (coordinateEmbedding w) → 3 * q.ε ≤ loss w z := by
        intro hw
        have h := good_gradient S p q.x0 query A.output A.update (A.initial z.1) z.2 N
          (coordinateEmbedding w) hw hlev
        rw [hratio] at h
        dsimp only [loss]
        linarith
      have hterm (w : W) : 3 * q.ε * (1 - if coordinateBad S p q.x0 query A.output A.update
          (A.initial z.1) z.2 N (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ loss w z := by
        by_cases hw : coordinateBad S p q.x0 query A.output A.update (A.initial z.1) z.2 N
            (coordinateEmbedding w)
        · simp only [hw, ↓reduceIte, sub_self, mul_zero]; exact norm_nonneg _
        · simp only [hw, ↓reduceIte, sub_zero, mul_one]; exact hgood w hw
      have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset W)) => hterm w)
      simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one] at hs
      have hεp : 0 ≤ 3 * q.ε := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hbad hεp]
    · have hg : good z = 0 := by simp [good, hz]
      rw [hg, mul_zero]
      exact Finset.sum_nonneg (fun w _ => norm_nonneg _)
  have hsetmeas : MeasurableSet {ω : ℕ → ℝ | coinCount p ω N ≤ Mh} := by
    have h := (coinCount_measurable p N) (measurableSet_Iic (a := ((Mh : ℕ) : ℝ)))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> exact_mod_cast h
  have hgoodmeas : MeasurableSet {z : A.Seed × (ℕ → ℝ) | coinCount p z.2 N ≤ Mh} :=
    measurable_snd hsetmeas
  have hgood_int : ∫ z, good z ∂P = stream.real {ω | coinCount p ω N ≤ Mh} := by
    rw [integral_indicator_one hgoodmeas]
    have hm : P.map Prod.snd = stream := by
      dsimp only [P]; rw [Measure.map_snd_prod]; simp
    have hpre : {z : A.Seed × (ℕ → ℝ) | coinCount p z.2 N ≤ Mh} =
        Prod.snd ⁻¹' {ω | coinCount p ω N ≤ Mh} := rfl
    rw [hpre, Measure.real, ← Measure.map_apply measurable_snd hsetmeas, hm]
    rfl
  have hfrac := good_count_fraction q hv N hN
  have hint_good : Integrable (fun z => 3 * q.ε * (7 / 8) * Fintype.card W * good z) P :=
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
    have hT0 : (0 : ℝ) ≤ chainLength q := Nat.cast_nonneg _
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hTd : ((n + 1 : ℕ) : ℝ) ≤ q.d := by
      rw [hn1]
      nlinarith [pow_nonneg hT0 3, mul_nonneg hN0 (pow_nonneg hT0 3)]
    exact_mod_cast hTd
  have hc : (0 : ℝ) < Fintype.card W := by exact_mod_cast coordinateWords_card_pos q.d n hd
  have hεp : 0 < q.ε := hε
  have hm1 := mul_le_mul_of_nonneg_left hfrac
    (by positivity : (0 : ℝ) ≤ 3 * q.ε * (7 / 8) * Fintype.card W)
  nlinarith

end LongTails.Proofs.ThirdOrderLowerBound
