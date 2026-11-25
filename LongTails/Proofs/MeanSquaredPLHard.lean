import LongTails.Setups.HighDimensionalMeanSquaredSmoothPL
import LongTails.Proofs.MeanSquaredPLExecution
import LongTails.Proofs.AbcLowerMeasure
import LongTails.Proofs.Execution
import LongTails.TemplateLowerBound
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

open MeasureTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.MeanSquaredPLHard

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open LongTails.Proofs.ThirdOrderMaskedOracle LongTails.Proofs.ThirdOrderMaskedScaling
open LongTails.Proofs.MeanSquaredPLOracle LongTails.Proofs.MeanSquaredPLExecution
open LongTails.Proofs.ThirdOrderMaskedExecution (lvl)
open LongTails.Proofs.RelativeHessianSimulation (axes axes_orthonormal)
open LongTails.Proofs.RelativeHessianLocalized (radius)
open LongTails.Proofs.AbcHardOracle (unif Scale toUnit)
open LongTails.Proofs.AbcHardExecution (coinCount)
open LongTails.Proofs.AbcLowerMeasure
open LongTails.Proofs.FiniteSumNondualLowerAveraging LongTails.Proofs.FiniteSumNondualLowerBound
open LongTails.Setups.HighDimensionalMeanSquaredSmoothPL

structure ChainData (p : Params) (n : ℕ) (S : Scale) (qc : ℝ) : Prop where
  hq0 : 0 < qc
  hq1 : qc ≤ 1
  smooth : 2 ^ 55 * S.a / S.lam ^ 2 ≤ p.L
  mss : (2 ^ 59 * S.a / S.lam ^ 2) ^ 2 / qc ≤ p.Lbar ^ 2
  var : (1 / qc - 1) * (2 ^ 51 * (S.a / S.lam)) ^ 2 ≤ p.σ ^ 2
  pl : 2 ^ 10 * p.μ * (n + 1 : ℕ) * S.lam ^ 2 ≤ S.a
  gap : S.a * (4 * (n + 1 : ℕ)) ≤ p.Δ

noncomputable def hardOracle (p : Params) {n : ℕ} (S : Scale) (qc : ℝ)
    (π : Fin (n + 1) ↪ Fin p.d) :
    Oracle (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d)) where
  Seed := fun _ => ℝ
  law := ⟨stream, inferInstance⟩
  answer := fun _ (_, z) ω => (plReply S qc π p.x0 z.1 ω, plReply S qc π p.x0 z.2 ω)

noncomputable def minPoint (p : Params) {n : ℕ} (S : Scale) (π : Fin (n + 1) ↪ Fin p.d) :
    EuclideanSpace ℝ (Fin p.d) :=
  p.x0 + S.lam • HessianPLLocalized.minimizer (axes π)

lemma toUnit_minPoint (p : Params) {n : ℕ} (S : Scale) (π : Fin (n + 1) ↪ Fin p.d) :
    toUnit S p.x0 (minPoint p S π) = HessianPLLocalized.minimizer (axes π) := by
  unfold toUnit minPoint
  rw [add_sub_cancel_left, smul_smul, one_div, inv_mul_cancel₀ S.hlam.ne', one_smul]

lemma objective_min (p : Params) {n : ℕ} (S : Scale) (π : Fin (n + 1) ↪ Fin p.d) :
    objective S π p.x0 (minPoint p S π) = S.a * ((n + 1 : ℕ) * HessianPLWell.bottom) := by
  unfold objective hardValue
  rw [toUnit_minPoint, HessianPLLocalized.value_minimizer (axes_orthonormal π)]

lemma objective_lower (p : Params) {n : ℕ} (S : Scale) (π : Fin (n + 1) ↪ Fin p.d)
    (x : EuclideanSpace ℝ (Fin p.d)) :
    S.a * ((n + 1 : ℕ) * HessianPLWell.bottom) ≤ objective S π p.x0 x := by
  unfold objective hardValue
  exact mul_le_mul_of_nonneg_left (HessianPLLocalized.value_lower (axes_orthonormal π) _) S.ha.le

lemma minPoint_isMin (p : Params) {n : ℕ} (S : Scale) (π : Fin (n + 1) ↪ Fin p.d) :
    IsMinOn (objective S π p.x0) Set.univ (minPoint p S π) := by
  intro x _
  change objective S π p.x0 (minPoint p S π) ≤ objective S π p.x0 x
  rw [objective_min]
  exact objective_lower p S π x

lemma objective_pl (p : Params) {n : ℕ} (S : Scale) (π : Fin (n + 1) ↪ Fin p.d)
    (hpl : 2 ^ 10 * p.μ * (n + 1 : ℕ) * S.lam ^ 2 ≤ S.a) (hμ : 0 < p.μ)
    (x : EuclideanSpace ℝ (Fin p.d)) :
    2 * p.μ * (objective S π p.x0 x - objective S π p.x0 (minPoint p S π)) ≤
      ‖gradient (objective S π p.x0) x‖ ^ 2 := by
  have ha := S.ha
  have hl := S.hlam
  rw [objective_min, objective_gradient]
  unfold objective objGrad hardGrad hardValue
  have hv := HessianPLLocalized.value_pl (axes_orthonormal π) (toUnit S p.x0 x)
  set G := ‖gradient (RelativeHessianLocalized.value (axes π)) (toUnit S p.x0 x)‖ ^ 2 with hG
  have hG0 : 0 ≤ G := sq_nonneg _
  rw [norm_smul, mul_pow, Real.norm_of_nonneg (by positivity)]
  have hN : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have h1 : 2 * p.μ * (S.a * RelativeHessianLocalized.value (axes π) (toUnit S p.x0 x) -
      S.a * ((n + 1 : ℕ) * HessianPLWell.bottom)) ≤
      2 * p.μ * S.a * (2 ^ 9 * (n + 1 : ℕ) * G) := by
    have := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ 2 * p.μ * S.a)
    linarith
  have h2 : 2 * p.μ * S.a * (2 ^ 9 * (n + 1 : ℕ) * G) ≤ (S.a / S.lam) ^ 2 * G := by
    have h3 : 2 ^ 10 * p.μ * (n + 1 : ℕ) * S.a ≤ (S.a / S.lam) ^ 2 := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hpl ha.le]
    nlinarith [mul_le_mul_of_nonneg_right h3 hG0]
  exact h1.trans h2

lemma hard_admissible (p : Params) (hv : spec.valid p) {n : ℕ} (S : Scale) (qc : ℝ)
    (hC : ChainData p n S qc) (π : Fin (n + 1) ↪ Fin p.d) :
    spec.admissible p (objective S π p.x0) (hardOracle p S qc π) := by
  have hμ : 0 < p.μ := hv.1.1
  have hg : ∀ x : Space p.d, gradient (objective S π p.x0) x = objGrad S π p.x0 x :=
    fun x => objective_gradient S π p.x0 x
  have h1 : ∀ x : Space p.d, HasGradientAt (objective S π p.x0)
      (gradient (objective S π p.x0) x) x :=
    fun x => ((objective_smooth S π p.x0).differentiable (by norm_num) x).hasGradientAt
  have h2 : ∀ x y : Space p.d, ‖gradient (objective S π p.x0) x -
      gradient (objective S π p.x0) y‖ ≤ p.L * ‖x - y‖ :=
    fun x y => (objective_gradient_lipschitz S π p.x0 x y).trans
      (mul_le_mul_of_nonneg_right hC.smooth (norm_nonneg _))
  have h3 : ∃ xstar : Space p.d, IsMinOn (objective S π p.x0) Set.univ xstar ∧
      objective S π p.x0 p.x0 - objective S π p.x0 xstar ≤ p.Δ ∧
      ∀ x : Space p.d, 2 * p.μ * (objective S π p.x0 x - objective S π p.x0 xstar) ≤
        ‖gradient (objective S π p.x0) x‖ ^ 2 :=
    ⟨minPoint p S π, minPoint_isMin p S π,
      (objective_gap S π p.x0 (minPoint p S π)).trans hC.gap, objective_pl p S π hC.pl hμ⟩
  have h4 : Measurable (Function.uncurry (fun (x : Space p.d) (ω : ℝ) =>
      plReply S qc π p.x0 x ω)) := plReply_measurable S qc π p.x0
  have h5 : ∀ x : Space p.d, Integrable (plReply S qc π p.x0 x) unif :=
    fun x => plReply_integrable S qc π p.x0 x
  have h6 : ∀ x : Space p.d, ∫ ω, plReply S qc π p.x0 x ω ∂unif =
      gradient (objective S π p.x0) x := by
    intro x
    rw [hg x]
    exact plReply_integral S qc hC.hq0 hC.hq1 π p.x0 x
  have h7 : ∀ x : Space p.d, Integrable (fun ω =>
      ‖plReply S qc π p.x0 x ω - gradient (objective S π p.x0) x‖ ^ 2) unif := by
    intro x
    rw [hg x]
    exact (plReply_variance S qc hC.hq0 hC.hq1 π p.x0 x).1
  have h8 : ∀ x : Space p.d, ∫ ω,
      ‖plReply S qc π p.x0 x ω - gradient (objective S π p.x0) x‖ ^ 2 ∂unif ≤ p.σ ^ 2 := by
    intro x
    rw [hg x]
    exact (plReply_variance S qc hC.hq0 hC.hq1 π p.x0 x).2.trans hC.var
  have h9 : ∀ x y : Space p.d, Integrable (fun ω =>
      ‖plReply S qc π p.x0 x ω - plReply S qc π p.x0 y ω‖ ^ 2) unif :=
    fun x y => (plReply_mss S qc hC.hq0 hC.hq1 π p.x0 x y).1
  have h10 : ∀ x y : Space p.d, ∫ ω,
      ‖plReply S qc π p.x0 x ω - plReply S qc π p.x0 y ω‖ ^ 2 ∂unif ≤
        p.Lbar ^ 2 * ‖x - y‖ ^ 2 :=
    fun x y => (plReply_mss S qc hC.hq0 hC.hq1 π p.x0 x y).2.trans
      (mul_le_mul_of_nonneg_right hC.mss (sq_nonneg _))
  exact ⟨fun x ω => plReply S qc π p.x0 x ω,
    ⟨unif, inferInstanceAs (IsProbabilityMeasure unif)⟩,
    ⟨stream, inferInstanceAs (IsProbabilityMeasure stream)⟩, stream_iid, rfl, h1, h2, h3, h4,
    h5, h6, h7, h8, h9, h10⟩

lemma trueState_iterate (S : Scale) (qc : ℝ) {d n : ℕ} (π : Fin (n + 1) ↪ Fin d)
    (x0 : Space d) {St : Type*} (query : St → Space d × Space d)
    (update : St → Space d × Space d → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ) :
    ((fun sc : St × ℕ => (update sc.1 (plReply S qc π x0 (query sc.1).1 (ω sc.2),
      plReply S qc π x0 (query sc.1).2 (ω sc.2)), sc.2 + 1))^[N] (initial, 0)) =
      (trueState S qc π x0 query update initial ω N, N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

lemma execute_hard (p : Params) {n : ℕ} (S : Scale) (qc : ℝ) (π : Fin (n + 1) ↪ Fin p.d)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d))) (N : ℕ) (seed : A.Seed) (ω : ℕ → ℝ) :
    execute (hardOracle p S qc π) A (fun _ => N) seed ω =
      A.output (trueState S qc π p.x0 (fun s => (A.query s).2) A.update
        (A.initial seed) ω N) := by
  have h1 := execute_indexed_of_answer (hardOracle p S qc π) A N seed ω
    (fun t query => (plReply S qc π p.x0 query.2.1 (ω t), plReply S qc π p.x0 query.2.2 (ω t)))
    (fun _ query => by cases query; rfl)
  refine h1.trans ?_
  exact congrArg (fun st => A.output st.1) (trueState_iterate S qc π p.x0
    (fun s => (A.query s).2) A.update (A.initial seed) ω N)

lemma good_count_fraction (qc : ℝ) (hq0 : 0 < qc) (hq1 : qc ≤ 1) (N M : ℕ)
    (hNq : (N : ℝ) * qc * 8 ≤ (M : ℝ) + 1) :
    7 / 8 ≤ stream.real {ω | coinCount qc ω N ≤ M} := by
  have ht := coinCount_tail qc hq0.le hq1 N M
  have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hfrac : (N : ℝ) * qc / ((M : ℝ) + 1) ≤ 1 / 8 := by
    rw [div_le_iff₀ hpos]
    linarith
  have hc : {ω : ℕ → ℝ | coinCount qc ω N ≤ M} = {ω | M + 1 ≤ coinCount qc ω N}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    omega
  have hmeas : MeasurableSet {ω : ℕ → ℝ | M + 1 ≤ coinCount qc ω N} := by
    have h := (coinCount_measurable qc N)
      (measurableSet_Ici : MeasurableSet (Set.Ici (((M + 1 : ℕ)) : ℝ)))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ici]
    constructor <;> intro h <;> exact_mod_cast h
  rw [hc, measureReal_compl hmeas, probReal_univ]
  linarith

theorem chain_failure (p : Params) (hv : spec.valid p) {n : ℕ} (S : Scale) (qc : ℝ)
    (hC : ChainData p n S qc)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d))) (N M : ℕ)
    (hNq : (N : ℝ) * qc * 8 ≤ (M : ℝ) + 1)
    (hloss : 64 * p.ε < 49 * (S.a * ((n : ℝ) - ((M : ℝ) + 1))))
    (hdim : 8 * ((2 * (N + 1 : ℕ) : ℕ) * ((n + 1 : ℕ) : ℝ) *
      ((2 * radius n) ^ 2 / (1 / 40) ^ 2)) + (n + 1 : ℕ) ≤ p.d) :
    ∃ π : Fin (n + 1) ↪ Fin p.d,
      ¬ spec.successful p (objective S π p.x0)
        (fun w : A.Seed × ((k : ℕ) → (hardOracle p S qc π).Seed k) =>
          execute (hardOracle p S qc π) A (fun _ => N) w.1 w.2)
        ⟨(A.law : Measure _).prod ((hardOracle p S qc π).law : Measure _), inferInstance⟩ := by
  have hε : 0 < p.ε := hv.1.2.2.2.2.2
  have ha := S.ha
  let query : A.State → Space p.d × Space p.d := fun s => (A.query s).2
  let W := CoordinateWords p.d n
  set base : ℝ := S.a * ((n + 1 : ℕ) * HessianPLWell.bottom) with hbase
  by_contra hcon
  push Not at hcon
  let P : Measure (A.Seed × (ℕ → ℝ)) := (A.law : Measure A.Seed).prod stream
  let loss : W → A.Seed × (ℕ → ℝ) → ℝ := fun w z =>
    objective S (coordinateEmbedding w) p.x0 (A.output (trueState S qc (coordinateEmbedding w)
      p.x0 query A.update (A.initial z.1) z.2 N)) - base
  have hloss0 (w : W) (z : A.Seed × (ℕ → ℝ)) : 0 ≤ loss w z :=
    sub_nonneg.mpr (objective_lower p S (coordinateEmbedding w) _)
  have hsucc (w : W) : Integrable (loss w) P ∧ ∫ z, loss w z ∂P ≤ p.ε := by
    obtain ⟨-, xs, hxs, hint, hle⟩ := hcon (coordinateEmbedding w)
    have hval : objective S (coordinateEmbedding w) p.x0 xs = base := by
      have h1 := isMinOn_iff.mp hxs (minPoint p S (coordinateEmbedding w)) (Set.mem_univ _)
      have h2 := objective_lower p S (coordinateEmbedding w) xs
      rw [objective_min] at h1
      exact le_antisymm h1 h2
    have hfun : (fun z : A.Seed × (ℕ → ℝ) => objective S (coordinateEmbedding w) p.x0
        (execute (hardOracle p S qc (coordinateEmbedding w)) A (fun _ => N) z.1 z.2) -
        objective S (coordinateEmbedding w) p.x0 xs) = loss w := by
      funext z
      rw [hval, execute_hard]
    rw [← hfun]
    exact ⟨hint, hle⟩
  let good : A.Seed × (ℕ → ℝ) → ℝ := fun z =>
    Set.indicator {z : A.Seed × (ℕ → ℝ) | coinCount qc z.2 N ≤ M} 1 z
  have hD : (0 : ℝ) ≤ (p.d : ℝ) - (n + 1 : ℕ) := by
    have h1 : (0 : ℝ) ≤ 8 * ((2 * (N + 1 : ℕ) : ℕ) * ((n + 1 : ℕ) : ℝ) *
        ((2 * radius n) ^ 2 / (1 / 40) ^ 2)) := by positivity
    linarith
  have hbadfrac (z : A.Seed × (ℕ → ℝ)) :
      8 * (∑ w : W, if coordinateBad S qc p.x0 query A.output A.update (A.initial z.1) z.2 N
        (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ Fintype.card W := by
    have hb := bad_sum_bound S qc p.x0 query A.output A.update (A.initial z.1) z.2 N
      ((p.d : ℝ) - (n + 1 : ℕ)) hD (by linarith)
    have hsum : 0 ≤ ∑ w : W, if coordinateBad S qc p.x0 query A.output A.update
        (A.initial z.1) z.2 N (coordinateEmbedding w) then (1 : ℝ) else 0 :=
      Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    have hcard : (0 : ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
    set X := (2 * (N + 1 : ℕ) : ℕ) * ((n + 1 : ℕ) : ℝ) * ((2 * radius n) ^ 2 / (1 / 40) ^ 2)
      with hX
    have hX0 : 0 < X := by
      have := LongTails.Proofs.RelativeHessianLocalized.radius_pos n
      positivity
    have hsize : 8 * X ≤ (p.d : ℝ) - (n + 1 : ℕ) := by linarith
    by_contra hc
    push Not at hc
    have h1 := mul_le_mul_of_nonneg_right hsize hsum
    have h2 := mul_lt_mul_of_pos_left hc hX0
    linarith
  have hpt (z : A.Seed × (ℕ → ℝ)) :
      S.a * ((n : ℝ) - ((M : ℝ) + 1)) * (7 / 8) * Fintype.card W * good z ≤ ∑ w, loss w z := by
    by_cases hz : coinCount qc z.2 N ≤ M
    · have hg : good z = 1 := by simp [good, hz]
      rw [hg, mul_one]
      have hlev : (lvl n qc z.2 N : ℝ) ≤ (M : ℝ) + 1 := by
        have h1 : lvl n qc z.2 N ≤ M + 1 :=
          (min_le_right _ _).trans (Nat.succ_le_succ hz)
        exact_mod_cast h1
      have hgoodw (w : W) : ¬ coordinateBad S qc p.x0 query A.output A.update (A.initial z.1)
          z.2 N (coordinateEmbedding w) → S.a * ((n : ℝ) - ((M : ℝ) + 1)) ≤ loss w z := by
        intro hw
        have h := good_gap S qc p.x0 query A.output A.update (A.initial z.1) z.2 N
          (coordinateEmbedding w) hw
        have h3 : S.a * ((n : ℝ) - ((M : ℝ) + 1)) ≤ S.a * ((n : ℝ) - lvl n qc z.2 N) :=
          mul_le_mul_of_nonneg_left (by linarith) ha.le
        exact h3.trans h
      by_cases hneg : S.a * ((n : ℝ) - ((M : ℝ) + 1)) ≤ 0
      · have hcard : (0 : ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
        have hs : 0 ≤ ∑ w, loss w z := Finset.sum_nonneg (fun w _ => hloss0 w z)
        have : S.a * ((n : ℝ) - ((M : ℝ) + 1)) * (7 / 8) * Fintype.card W ≤ 0 := by
          have h1 : S.a * ((n : ℝ) - ((M : ℝ) + 1)) * (7 / 8) ≤ 0 := by linarith
          exact mul_nonpos_of_nonpos_of_nonneg h1 hcard
        linarith
      · push Not at hneg
        have hterm (w : W) : S.a * ((n : ℝ) - ((M : ℝ) + 1)) *
            (1 - if coordinateBad S qc p.x0 query A.output A.update
              (A.initial z.1) z.2 N (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ loss w z := by
          by_cases hw : coordinateBad S qc p.x0 query A.output A.update (A.initial z.1) z.2 N
              (coordinateEmbedding w)
          · simp only [hw, ↓reduceIte, sub_self, mul_zero]
            exact hloss0 w z
          · simp only [hw, ↓reduceIte, sub_zero, mul_one]
            exact hgoodw w hw
        have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset W)) => hterm w)
        simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one] at hs
        have hbad := hbadfrac z
        nlinarith [mul_le_mul_of_nonneg_left hbad hneg.le]
    · have hg : good z = 0 := by simp [good, hz]
      rw [hg, mul_zero]
      exact Finset.sum_nonneg (fun w _ => hloss0 w z)
  have hsetmeas : MeasurableSet {ω : ℕ → ℝ | coinCount qc ω N ≤ M} := by
    have h := (coinCount_measurable qc N) (measurableSet_Iic (a := ((M : ℕ) : ℝ)))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> exact_mod_cast h
  have hgoodmeas : MeasurableSet {z : A.Seed × (ℕ → ℝ) | coinCount qc z.2 N ≤ M} :=
    measurable_snd hsetmeas
  have hgood_int : ∫ z, good z ∂P = stream.real {ω | coinCount qc ω N ≤ M} := by
    rw [integral_indicator_one hgoodmeas]
    have hm : P.map Prod.snd = stream := by
      dsimp only [P]
      rw [Measure.map_snd_prod]
      simp
    have hpre : {z : A.Seed × (ℕ → ℝ) | coinCount qc z.2 N ≤ M} =
        Prod.snd ⁻¹' {ω | coinCount qc ω N ≤ M} := rfl
    rw [hpre, Measure.real, ← Measure.map_apply measurable_snd hsetmeas, hm]
    rfl
  have hfrac := good_count_fraction qc hC.hq0 hC.hq1 N M hNq
  have hint_good : Integrable (fun z =>
      S.a * ((n : ℝ) - ((M : ℝ) + 1)) * (7 / 8) * Fintype.card W * good z) P :=
    ((integrable_const (1 : ℝ)).indicator hgoodmeas).const_mul _
  have hint_sum : Integrable (fun z => ∑ w, loss w z) P :=
    integrable_finsetSum Finset.univ (fun w _ => (hsucc w).1)
  have hmono := integral_mono hint_good hint_sum hpt
  rw [integral_const_mul, hgood_int,
    integral_finsetSum Finset.univ (fun w _ => (hsucc w).1)] at hmono
  have hsum : (∑ w : W, ∫ z, loss w z ∂P) ≤ Fintype.card W * p.ε := by
    calc _ ≤ ∑ _w : W, p.ε := Finset.sum_le_sum (fun w _ => (hsucc w).2)
      _ = _ := by simp
  have hd : n + 1 ≤ p.d := by
    have h1 : ((n + 1 : ℕ) : ℝ) ≤ p.d := by linarith
    exact_mod_cast h1
  have hc : (0 : ℝ) < Fintype.card W := by exact_mod_cast coordinateWords_card_pos p.d n hd
  have hApos : 0 < S.a * ((n : ℝ) - ((M : ℝ) + 1)) := by nlinarith
  have hm1 := mul_le_mul_of_nonneg_left hfrac
    (by positivity : (0 : ℝ) ≤ S.a * ((n : ℝ) - ((M : ℝ) + 1)) * (7 / 8) * Fintype.card W)
  nlinarith [mul_pos hc (sub_pos.mpr hloss)]

end LongTails.Proofs.MeanSquaredPLHard
