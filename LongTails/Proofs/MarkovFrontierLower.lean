import LongTails.Proofs.MarkovFrontierOccupancy
import LongTails.Proofs.MarkovFrontierOracle
import LongTails.Proofs.MarkovFrontierHiding

open MeasureTheory ProbabilityTheory OracleTemplate Classical
open scoped BigOperators

namespace LongTails.Proofs.MarkovFrontierLower

open Setups.MarkovSmoothNonconvex
open LongTails.Setups.HighDimensionalMarkovSmoothNonconvex (Valid)
open Setups.HeavyTailedMarkovSmoothAndConvex (pathLaw)
open MarkovFrontierScales MarkovFrontierPhases MarkovFrontierOccupancy MarkovFrontierOracle
open MarkovFrontierSimulation MarkovFrontierHiding MarkovFrontierProgress
open AbcHardFunction AbcHardGeometry AbcHardOracle AbcLowerParameters AbcLowerAssembly
open FiniteSumNondualLowerAveraging FiniteSumNondualLowerBound

noncomputable abbrev stream (p : Params) (hv : Valid p) : Measure (ℕ → ℝ) :=
  pathLaw (chainKernel p hv) (chainLaw p hv)

lemma few_phases (p : Params) (hv : Valid p) (N : ℕ) (hN : N ≤ lowerCalls p) :
    2 / 3 ≤ (stream p hv).real {ξ | count (halfLength p) N ξ < chainLength (chainParams p)} := by
  let h := halfLength p
  let l := chainLength (chainParams p)
  let P := stream p hv
  have hl : (0 : ℝ) < l := by
    have := chainLength_ge _ (chain_valid hv)
    dsimp [l]
    exact_mod_cast (by omega : 0 < chainLength (chainParams p))
  have hh := (half_bounds hv).1
  have he := count_expectation h hh (jump p hv) N
  have hr := CountdownMarkov.calibratedJump_entry (h + h) (rareMass p) (by omega)
    (mass_bounds hv).1.le (by linarith [(mass_bounds hv).2])
  have eqrate : 2 * (jump p hv : ℝ) / (1 + (h + h : ℕ) * (jump p hv : ℝ)) =
      2 * rareMass p / (h + h : ℕ) := by
    simpa only [jump, h, mul_div_assoc] using congrArg (fun x : ℝ => (2 : ℝ) * x) hr
  rw [eqrate] at he
  have hb := he.trans (few_entries hv N hN)
  have ht := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ξ => (count h N ξ : ℝ))
    (.of_forall fun _ => Nat.cast_nonneg _) (count_integrable P h N) (l : ℝ)
  have hset : {ξ | (l : ℝ) ≤ (count h N ξ : ℝ)} = {ξ | l ≤ count h N ξ} := by
    ext ξ
    simp
  rw [hset] at ht
  have hm : MeasurableSet {ξ | l ≤ count h N ξ} := (count_measurable h N) measurableSet_Ici
  have hc : {ξ | count h N ξ < l} = {ξ | l ≤ count h N ξ}ᶜ := by ext ξ; simp
  change 2 / 3 ≤ P.real {ξ | count h N ξ < l}
  rw [hc, measureReal_compl hm, probReal_univ]
  have hb' : (l : ℝ) * P.real {ξ | l ≤ count h N ξ} ≤ l / 3 := ht.trans hb
  have hu : P.real {ξ | l ≤ count h N ξ} ≤ 1 / 3 := by
    apply le_of_mul_le_mul_left (a := (l : ℝ)) _ hl
    linarith
  linarith

lemma execute_hard (p : Params) (hv : Valid p) (π : labels p)
    (A : Algorithm (Setups.MarkovSmoothNonconvex.Space p) (Setups.MarkovSmoothNonconvex.Space p)
      (Setups.MarkovSmoothNonconvex.Space p)) (N : ℕ) (seed : A.Seed) (ξ : ℕ → ℝ) :
    execute (hard p hv π) A (fun _ => N) seed ξ =
      A.output (actual (geometry p hv) (rareMass p / 2) π p.x0 (fun s => (A.query s).2)
        A.update (A.initial seed) (fun t => color (halfLength p) (ξ t)) N) := by
  rw [execute_indexed_of_answer (hard p hv π) A N seed ξ
    (fun t query => estimator p hv π query.2 (ξ t)) (fun _ query => by cases query; rfl)]
  congr 1
  let run := actual (geometry p hv) (rareMass p / 2) π p.x0 (fun s => (A.query s).2)
    A.update (A.initial seed) (fun t => color (halfLength p) (ξ t))
  have hr (t : ℕ) : ((fun z : A.State × ℕ =>
      (A.update z.1 (estimator p hv π (A.query z.1).2 (ξ z.2)), z.2 + 1))^[t]
      (A.initial seed, 0)) = (run t, t) := by
    induction t with
    | zero => rfl
    | succ t ih => rw [Function.iterate_succ_apply', ih]; rfl
  exact congrArg Prod.fst (hr N)

lemma bad_fraction (p : Params) (hv : Valid p) (N : ℕ) (hN : N ≤ lowerCalls p)
    {St : Type*} (S : Scale) (query output : St → Space p.d) (update : St → Space p.d → St)
    (initial : St) (ω : ℕ → MarkovFrontierSimulation.Color)
    (hlev : level ω N < chainLength (chainParams p)) :
    8 * (∑ w : CoordinateWords p.d (chainDim (chainParams p)), if coordinateBad S (rareMass p / 2)
      p.x0 query output update initial ω N (coordinateEmbedding w) then (1 : ℝ)
      else 0) ≤ Fintype.card (CoordinateWords p.d (chainDim (chainParams p))) := by
  let q := chainParams p
  have hroom : (chainLength q : ℝ) + 2^31*((N : ℝ)+1)*(chainLength q : ℝ)^3 ≤ q.d := dimension_available hv N hN
  have hn1 := chainDim_succ q (chain_valid hv)
  set n := chainDim q
  have hcast : ((n + 1 : ℕ) : ℝ) = chainLength q := by rw [hn1]
  let D : ℝ := q.d - (n + 1 : ℕ)
  have hD : 0 ≤ D := by
    dsimp only [D]; rw [hcast]
    nlinarith [pow_nonneg (Nat.cast_nonneg (chainLength q) : (0 : ℝ) ≤ chainLength q) 3,
      (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hDs : D + (n + 1 : ℕ) ≤ p.d := by dsimp only [D]; rw [sub_add_cancel]; rfl
  have hb := bad_sum_bound S (rareMass p / 2) p.x0 query output update initial ω N
    D hD hDs (by rw [hn1]; exact hlev.le)
  have hR : (2 * radius n) ^ 2 / (1 / 4) ^ 2 = 2 ^ 28 * ((n : ℝ) + 1) ^ 2 := by
    unfold radius; ring
  rw [hR] at hb
  have hsize : 8 * (((N + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * (2 ^ 28 * ((n : ℝ) + 1) ^ 2)) ≤ D := by
    dsimp only [D]
    have hn' : ((n : ℝ) + 1) = chainLength q := by rw [← hcast]; push_cast; ring
    rw [hn', hcast]
    push_cast
    nlinarith
  have hcard : (0 : ℝ) ≤ Fintype.card (CoordinateWords p.d n) := Nat.cast_nonneg _
  have hsum : 0 ≤ ∑ w : CoordinateWords p.d n, if coordinateBad S (rareMass p / 2) p.x0 query
      output update initial ω N (coordinateEmbedding w) then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  by_contra hcon
  push Not at hcon
  have h1 := mul_le_mul_of_nonneg_right hsize hsum
  have hX : 0 < ((N + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * (2 ^ 28 * ((n : ℝ) + 1) ^ 2) := by
    positivity
  have h2 := mul_lt_mul_of_pos_left hcon hX
  linarith

lemma exists_failure (p : Params) (hv : Valid p)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d))) (N : ℕ) (hN : N ≤ lowerCalls p) :
    ∃ π : Fin (chainDim (chainParams p) + 1) ↪ Fin p.d,
      ¬ spec.successful p (objective (geometry p hv) π p.x0)
        (fun w : A.Seed × ((k : ℕ) → (hard p hv π).Seed k) =>
          execute (hard p hv π) A (fun _ => N) w.1 w.2)
        ⟨(A.law : Measure _).prod
          ((hard p hv π).law : Measure _), inferInstance⟩ := by
  let q := chainParams p
  have hε := hv.2.1
  have hn1 := chainDim_succ q (chain_valid hv)
  let S := geometry p hv
  let n := chainDim q
  let mass := rareMass p / 2
  let h := halfLength p
  let colors := fun (ξ : ℕ → ℝ) t => color h (ξ t)
  let l := chainLength q
  let query : A.State → Space p.d := fun s => (A.query s).2
  let W := CoordinateWords p.d n
  have hratio : S.a / S.lam = 60 * p.ε := amplitude_ratio q hv.1 hε
  by_contra hcon
  push Not at hcon
  let P : Measure (A.Seed × (ℕ → ℝ)) := (A.law : Measure A.Seed).prod (stream p hv)
  let loss : W → A.Seed × (ℕ → ℝ) → ℝ := fun w z =>
    ‖objGrad S (coordinateEmbedding w) p.x0 (A.output (actual S mass (coordinateEmbedding w)
      p.x0 query A.update (A.initial z.1) (colors z.2) N))‖
  have hloss (w : W) : (fun z : A.Seed × (ℕ → ℝ) => ‖gradient (objective S (coordinateEmbedding w)
      p.x0) (execute (hard p hv (coordinateEmbedding w)) A (fun _ => N) z.1 z.2)‖) = loss w := by
    funext z
    rw [objective_gradient, MarkovFrontierLower.execute_hard]
  have hi (w : W) : Integrable (loss w) P := by
    have h := (hcon (coordinateEmbedding w)).2.1
    rw [← hloss w]
    exact h
  have hle (w : W) : ∫ z, loss w z ∂P ≤ p.ε := by
    have h := (hcon (coordinateEmbedding w)).2.2
    rw [← hloss w]
    exact h
  let good : A.Seed × (ℕ → ℝ) → ℝ := fun z =>
    Set.indicator {z : A.Seed × (ℕ → ℝ) | count h N z.2 < l} 1 z
  have hpt (z : A.Seed × (ℕ → ℝ)) :
      3 * p.ε * (7 / 8) * Fintype.card W * good z ≤ ∑ w, loss w z := by
    by_cases hz : count h N z.2 < l
    · have hg : good z = 1 := by simp [good, hz]
      rw [hg, mul_one]
      have hlev : level (colors z.2) N < chainLength q :=
        (level_le_entries (colors z.2) N).trans_lt hz
      have hlev' : level (colors z.2) N < n + 1 := by rw [hn1]; exact hlev
      have hbad := bad_fraction p hv N hN S query A.output A.update (A.initial z.1) (colors z.2) hlev
      have hq : mass ≤ 1 := by dsimp [mass]; linarith [(mass_bounds hv).2]
      have hgood (w : W) : ¬ coordinateBad S mass p.x0 query A.output A.update (A.initial z.1)
          (colors z.2) N (coordinateEmbedding w) → 3 * p.ε ≤ loss w z := by
        intro hw
        have h := good_gradient S mass p.x0 query A.output A.update (A.initial z.1) (colors z.2) N
          (coordinateEmbedding w) hw hlev' hq
        rw [hratio] at h
        dsimp only [loss]
        linarith
      have hterm (w : W) : 3 * p.ε * (1 - if coordinateBad S mass p.x0 query A.output A.update
          (A.initial z.1) (colors z.2) N (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ loss w z := by
        by_cases hw : coordinateBad S mass p.x0 query A.output A.update (A.initial z.1) (colors z.2) N
            (coordinateEmbedding w)
        · simp only [hw, ↓reduceIte, sub_self, mul_zero]; exact norm_nonneg _
        · simp only [hw, ↓reduceIte, sub_zero, mul_one]; exact hgood w hw
      have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset W)) => hterm w)
      simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one] at hs
      have hεp : 0 ≤ 3 * p.ε := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hbad hεp]
    · have hg : good z = 0 := by simp [good, hz]
      rw [hg, mul_zero]
      exact Finset.sum_nonneg (fun w _ => norm_nonneg _)
  have hsetmeas : MeasurableSet {ω : ℕ → ℝ | count h N ω < l} := by
    exact (count_measurable h N) measurableSet_Iio
  have hgoodmeas : MeasurableSet {z : A.Seed × (ℕ → ℝ) | count h N z.2 < l} :=
    measurable_snd hsetmeas
  have hgood_int : ∫ z, good z ∂P = (stream p hv).real {ω | count h N ω < l} := by
    rw [integral_indicator_one hgoodmeas]
    have hm : P.map Prod.snd = stream p hv := by
      dsimp only [P]; rw [Measure.map_snd_prod]; simp
    have hpre : {z : A.Seed × (ℕ → ℝ) | count h N z.2 < l} =
        Prod.snd ⁻¹' {ω | count h N ω < l} := rfl
    rw [hpre, Measure.real, ← Measure.map_apply measurable_snd hsetmeas, hm]
    rfl
  have hfrac := few_phases p hv N hN
  have hint_good : Integrable (fun z => 3 * p.ε * (7 / 8) * Fintype.card W * good z) P :=
    ((integrable_const (1 : ℝ)).indicator hgoodmeas).const_mul _
  have hint_sum : Integrable (fun z => ∑ w, loss w z) P :=
    integrable_finsetSum Finset.univ (fun w _ => hi w)
  have hmono := integral_mono hint_good hint_sum hpt
  rw [integral_const_mul, hgood_int, integral_finsetSum Finset.univ (fun w _ => hi w)] at hmono
  have hsum : (∑ w : W, ∫ z, loss w z ∂P) ≤ Fintype.card W * p.ε := by
    calc _ ≤ ∑ _w : W, p.ε := Finset.sum_le_sum (fun w _ => hle w)
      _ = _ := by simp
  have hd : n + 1 ≤ p.d := by
    have h : (chainLength q : ℝ) + 2^31*((N : ℝ)+1)*(chainLength q : ℝ)^3 ≤ q.d := dimension_available hv N hN
    have hT : ((n + 1 : ℕ) : ℝ) ≤ p.d := by
      change ((n + 1 : ℕ) : ℝ) ≤ q.d
      rw [hn1]
      nlinarith [pow_nonneg (Nat.cast_nonneg (chainLength q) : (0 : ℝ) ≤ chainLength q) 3,
        (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact_mod_cast hT
  have hc : (0 : ℝ) < Fintype.card W := by exact_mod_cast coordinateWords_card_pos p.d n hd
  have hεp : 0 < p.ε := hε
  have hm1 := mul_le_mul_of_nonneg_left hfrac
    (by positivity : (0 : ℝ) ≤ 3 * p.ε * (7 / 8) * Fintype.card W)
  nlinarith

end LongTails.Proofs.MarkovFrontierLower
