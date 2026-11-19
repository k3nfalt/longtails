import LongTails.Proofs.MarkovParityHiding
import LongTails.Proofs.MarkovParityOracle

open MeasureTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.MarkovParityLower

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open MarkovParityProgress MarkovParityChain MarkovParitySimulation MarkovParityHiding
open MarkovParityParameters MarkovParityOracle AbcHardFunction AbcHardOracle
open AbcLowerParameters
open AbcLowerAssembly (chainDim_succ)
open FiniteSumNondualLowerAveraging FiniteSumNondualLowerBound
open LongTails.Setups.MarkovSmoothNonconvex

lemma execute_hard (q : Params) (hv : spec.valid q) (π : Fin (dim q + 1) ↪ Fin q.d)
    (A : Algorithm (Space q) (Space q) (Space q)) (N : ℕ) (seed : A.Seed) (ω : ℕ → Color) :
    execute (oracle q hv π) A (fun _ => N) seed ω =
      A.output (runActual (scale q hv) (chance q) π q.x0 (fun s => (A.query s).2) A.update
        (A.initial seed) ω N) := by
  rw [execute_indexed_of_answer (oracle q hv π) A N seed ω
    (fun t query => response (scale q hv) (chance q) π q.x0 query.2 (ω t))
    (fun _ query => by cases query; rfl)]
  have he (k : ℕ) :
      ((fun sc : A.State × ℕ => (A.update sc.1 (response (scale q hv) (chance q) π q.x0
        (A.query sc.1).2 (ω sc.2)), sc.2 + 1))^[k] (A.initial seed, 0)) =
        (runActual (scale q hv) (chance q) π q.x0 (fun s => (A.query s).2) A.update
          (A.initial seed) ω k, k) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl
  rw [he]

lemma good_count_fraction (q : Params) (hv : spec.valid q) (N : ℕ) (hN : N ≤ limit q) :
    3 / 4 ≤ (trajectory q hv : Measure (ℕ → Color)).real {ω | entries ω N ≤ dim q} := by
  let P : Measure (ℕ → Color) := trajectory q hv
  have : IsProbabilityMeasure P := (trajectory q hv).prop
  let K := chainLength (geometry q)
  have hk : dim q + 1 = K := chainDim_succ _ (geometry_valid q hv)
  have hkp : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  let X := fun z : ℕ → Color => (entries z N : ℝ)
  have hi : Integrable X P := Integrable.of_bound
    (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (entries_measurable N)).aestronglyMeasurable)
    N (.of_forall fun z => by simpa [X] using (show (entries z N : ℝ) ≤ N by exact_mod_cast entries_le z N))
  have hmean : ∫ z, X z ∂P ≤ (K : ℝ) / 4 :=
    (entries_mean (chance q) (chance_pos q hv).le (chance_small q hv) (refresh q hv) N).trans
      (entry_budget q hv N hN)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := X) (.of_forall fun z => (Nat.cast_nonneg (entries z N) : (0 : ℝ) ≤ _)) hi (K : ℝ)
  have hm : MeasurableSet {z : ℕ → Color | (K : ℝ) ≤ X z} :=
    measurableSet_le measurable_const ((measurable_of_countable _).comp (entries_measurable N))
  have he : {ω : ℕ → Color | entries ω N ≤ dim q} = {z | (K : ℝ) ≤ X z}ᶜ := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, X, Nat.cast_lt]
    omega
  change _ ≤ P.real _
  rw [he, measureReal_compl hm, probReal_univ]
  nlinarith

lemma bad_fraction (q : Params) (hv : spec.valid q) (N : ℕ) (hN : N ≤ limit q)
    {St : Type*} (S : Scale) (query output : St → Space q) (update : St → Space q → St)
    (initial : St) (ω : ℕ → Color) (hshort : progress ω N ≤ dim q + 1) :
    8 * (∑ w : CoordinateWords q.d (dim q), if coordinateBad S (chance q)
      q.x0 query output update initial ω N (coordinateEmbedding w) then (1 : ℝ)
      else 0) ≤ Fintype.card (CoordinateWords q.d (dim q)) := by
  have hroom := dimension_room (geometry q) (geometry_valid q hv) N (hN.trans (limit_le_geometry q hv))
  change (chainLength (geometry q) : ℝ) + _ ≤ q.d at hroom
  have hn1 := chainDim_succ (geometry q) (geometry_valid q hv)
  set n := dim q
  have hcast : ((n + 1 : ℕ) : ℝ) = chainLength (geometry q) := by rw [hn1]
  let D : ℝ := q.d - (n + 1 : ℕ)
  have hD : 0 ≤ D := by
    dsimp only [D]; rw [hcast]
    nlinarith [pow_nonneg (Nat.cast_nonneg (chainLength (geometry q)) : (0 : ℝ) ≤ chainLength (geometry q)) 3,
      (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hDs : D + (n + 1 : ℕ) ≤ q.d := by dsimp only [D]; linarith
  have hb := bad_sum_bound S (chance q) q.x0 query output update initial ω N
    D hD hDs hshort
  have hR : (2 * radius n) ^ 2 / (1 / 4) ^ 2 = 2 ^ 28 * ((n : ℝ) + 1) ^ 2 := by
    unfold radius; ring
  rw [hR] at hb
  have hsize : 8 * (((N + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * (2 ^ 28 * ((n : ℝ) + 1) ^ 2)) ≤ D := by
    dsimp only [D]
    have hn' : ((n : ℝ) + 1) = chainLength (geometry q) := by rw [← hcast]; push_cast; ring
    rw [hn', hcast]
    push_cast
    nlinarith
  have hcard : (0 : ℝ) ≤ Fintype.card (CoordinateWords q.d n) := Nat.cast_nonneg _
  have hsum : 0 ≤ ∑ w : CoordinateWords q.d n, if coordinateBad S (chance q) q.x0 query
      output update initial ω N (coordinateEmbedding w) then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  by_contra hcon
  push Not at hcon
  have h1 := mul_le_mul_of_nonneg_right hsize hsum
  have hX : 0 < ((N + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * (2 ^ 28 * ((n : ℝ) + 1) ^ 2) := by
    positivity
  have h2 := mul_lt_mul_of_pos_left hcon hX
  linarith

lemma exists_failure (q : Params) (hv : spec.valid q)
    (A : Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d))) (N : ℕ) (hN : N ≤ limit q) :
    ∃ π : Fin (dim q + 1) ↪ Fin q.d,
      ¬ spec.successful q (objective (scale q hv) π q.x0)
        (fun w : A.Seed × ((k : ℕ) → (oracle q hv π).Seed k) =>
          execute (oracle q hv π) A (fun _ => N) w.1 w.2)
        ⟨(A.law : Measure _).prod
          ((oracle q hv π).law : Measure _), inferInstance⟩ := by
  have hε := hv.2.1
  have hn1 := chainDim_succ (geometry q) (geometry_valid q hv)
  set S := scale q hv
  set n := dim q
  set qf := chance q
  let stream : Measure (ℕ → Color) := trajectory q hv
  have : IsProbabilityMeasure stream := (trajectory q hv).prop
  set Mh := n
  let query : A.State → Space q := fun s => (A.query s).2
  let W := CoordinateWords q.d n
  have hratio : S.a / S.lam = 60 * q.ε := amplitude_ratio (geometry q) hv.1 hε
  by_contra hcon
  push Not at hcon
  let P : Measure (A.Seed × (ℕ → Color)) := (A.law : Measure A.Seed).prod stream
  let loss : W → A.Seed × (ℕ → Color) → ℝ := fun w z =>
    ‖objGrad S (coordinateEmbedding w) q.x0 (A.output (runActual S qf (coordinateEmbedding w)
      q.x0 query A.update (A.initial z.1) z.2 N))‖
  have hloss (w : W) : (fun z : A.Seed × (ℕ → Color) => ‖gradient (objective S (coordinateEmbedding w)
      q.x0) (execute (oracle q hv (coordinateEmbedding w)) A (fun _ => N) z.1 z.2)‖) = loss w := by
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
  let good : A.Seed × (ℕ → Color) → ℝ := fun z =>
    Set.indicator {z : A.Seed × (ℕ → Color) | entries z.2 N ≤ Mh} 1 z
  have hpt (z : A.Seed × (ℕ → Color)) :
      3 * q.ε * (7 / 8) * Fintype.card W * good z ≤ ∑ w, loss w z := by
    by_cases hz : entries z.2 N ≤ Mh
    · have hg : good z = 1 := by simp [good, hz]
      rw [hg, mul_one]
      have hlev : progress z.2 N < n + 1 := Nat.lt_succ_of_le ((progress_le_entries _ _).trans hz)
      have hq : qf ≤ 1 := by have := chance_small q hv; dsimp [qf]; linarith [chance_pos q hv]
      have hbad := bad_fraction q hv N hN S query A.output A.update (A.initial z.1) z.2 hlev.le
      have hgood (w : W) : ¬ coordinateBad S qf q.x0 query A.output A.update (A.initial z.1)
          z.2 N (coordinateEmbedding w) → 3 * q.ε ≤ loss w z := by
        intro hw
        have h := good_gradient S qf q.x0 query A.output A.update (A.initial z.1) z.2 N
          (coordinateEmbedding w) hw hlev hq
        rw [hratio] at h
        dsimp only [loss]
        linarith
      have hterm (w : W) : 3 * q.ε * (1 - if coordinateBad S qf q.x0 query A.output A.update
          (A.initial z.1) z.2 N (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ loss w z := by
        by_cases hw : coordinateBad S qf q.x0 query A.output A.update (A.initial z.1) z.2 N
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
  have hsetmeas : MeasurableSet {ω : ℕ → Color | entries ω N ≤ Mh} := by
    exact entries_measurable N (measurableSet_Iic (a := Mh))
  have hgoodmeas : MeasurableSet {z : A.Seed × (ℕ → Color) | entries z.2 N ≤ Mh} :=
    measurable_snd hsetmeas
  have hgood_int : ∫ z, good z ∂P = stream.real {ω | entries ω N ≤ Mh} := by
    rw [integral_indicator_one hgoodmeas]
    have hm : P.map Prod.snd = stream := by
      dsimp only [P]; rw [Measure.map_snd_prod]; simp
    have hpre : {z : A.Seed × (ℕ → Color) | entries z.2 N ≤ Mh} =
        Prod.snd ⁻¹' {ω | entries ω N ≤ Mh} := rfl
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
    have h := dimension_room (geometry q) (geometry_valid q hv) N (hN.trans (limit_le_geometry q hv))
    have hT : ((n + 1 : ℕ) : ℝ) ≤ q.d := by
      rw [hn1]
      change (chainLength (geometry q) : ℝ) + _ ≤ q.d at h
      nlinarith [pow_nonneg (Nat.cast_nonneg (chainLength (geometry q)) : (0 : ℝ) ≤ chainLength (geometry q)) 3,
        (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact_mod_cast hT
  have hc : (0 : ℝ) < Fintype.card W := by exact_mod_cast coordinateWords_card_pos q.d n hd
  have hεp : 0 < q.ε := hε
  have hm1 := mul_le_mul_of_nonneg_left hfrac
    (by positivity : (0 : ℝ) ≤ 3 * q.ε * (7 / 8) * Fintype.card W)
  nlinarith

end LongTails.Proofs.MarkovParityLower
