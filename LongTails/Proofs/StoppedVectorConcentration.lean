import LongTails.Proofs.AdaptiveOracleConcentration
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Probability.Moments.Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.StoppedVectorConcentration

lemma exp_le_one_add_twice {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + 2 * x := by
  have hh := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (show 0 ≤ 1 - x by linarith) hx0 (show (1 - x) + x = 1 by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at hh
  nlinarith [mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le hx0]

lemma bounded_nonnegative_mgf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {b θ : ℝ}
    (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) (hXb : ∀ ω, X ω ≤ b)
    (hθ : 0 ≤ θ) (hsmall : θ * b ≤ 1) :
    Integrable (fun ω => Real.exp (θ * X ω)) P ∧
      (∫ ω, Real.exp (θ * X ω) ∂P) ≤ Real.exp (2 * θ * ∫ ω, X ω ∂P) := by
  have hi : Integrable X P := Integrable.mono' (integrable_const b) hX.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]; exact hXb ω))
  have he : Integrable (fun ω => Real.exp (θ * X ω)) P :=
    ScalarMomentConcentration.bounded_exp_integrable hX
      (fun ω => by rw [abs_of_nonneg (hX0 ω)]; exact hXb ω) θ
  have hpoint (ω : Ω) : Real.exp (θ * X ω) ≤ 1 + 2 * θ * X ω := by
    have hh := exp_le_one_add_twice (mul_nonneg hθ (hX0 ω))
      ((mul_le_mul_of_nonneg_left (hXb ω) hθ).trans hsmall)
    nlinarith only [hh]
  refine ⟨he, (integral_mono he ((integrable_const 1).add (hi.const_mul (2 * θ))) hpoint).trans ?_⟩
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const 1) (hi.const_mul (2 * θ)), integral_const_mul]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  nlinarith only [Real.add_one_le_exp (2 * θ * ∫ ω, X ω ∂P)]

lemma exponential_tail_of_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {θ V : ℝ}
    (hθ : 0 ≤ θ) (hi : Integrable (fun ω => Real.exp (θ * X ω)) P)
    (hb : (∫ ω, Real.exp (θ * X ω) ∂P) ≤ Real.exp V) (t : ℝ) :
    P.real {ω | t ≤ X ω} ≤ Real.exp (V - θ * t) := by
  have hh := measure_ge_le_exp_mul_mgf t hθ hi
  apply hh.trans
  change Real.exp (-θ * t) * (∫ ω, Real.exp (θ * X ω) ∂P) ≤ _
  calc
    Real.exp (-θ * t) * (∫ ω, Real.exp (θ * X ω) ∂P) ≤
        Real.exp (-θ * t) * Real.exp V :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = Real.exp (V - θ * t) := by rw [← Real.exp_add]; congr 1; ring

lemma cross_chernoff_parameters {q ell : ℝ} (hq : 0 < q) (hl : 0 < ell) :
    0 < Real.sqrt ell / (768 * q) ∧
      (256 * q / Real.sqrt ell) * (Real.sqrt ell / (768 * q)) = 1 / 3 ∧
      262144 * q ^ 2 * (Real.sqrt ell / (768 * q)) ^ 2 /
          (1 - (256 * q / Real.sqrt ell) * (Real.sqrt ell / (768 * q))) -
        (Real.sqrt ell / (768 * q)) * (1280 * q * Real.sqrt ell) = -ell := by
  have hs : 0 < Real.sqrt ell := Real.sqrt_pos.mpr hl
  have hs2 := Real.sq_sqrt hl.le
  have he : (256 * q / Real.sqrt ell) * (Real.sqrt ell / (768 * q)) = 1 / 3 := by
    field_simp
    ring
  refine ⟨by positivity, he, ?_⟩
  rw [he]
  field_simp
  nlinarith [hs2]

lemma energy_chernoff_parameters {a ell : ℝ} (ha : 0 < a) (hl : 0 < ell) :
    0 < ell / (4 * a) ∧
      (ell / (4 * a)) * (4 * a / ell) = 1 ∧
      40 * a * (ell / (4 * a)) - (ell / (4 * a)) * (44 * a) = -ell := by
  refine ⟨by positivity, ?_, ?_⟩
  · field_simp
  · field_simp
    ring

lemma stopped_radius_budget {K d ell : ℝ} (hK : 0 ≤ K) (hd : 0 ≤ d) (hl : 0 ≤ ell) :
    44 * d * K + 2 * (1280 * (8192 * Real.sqrt (K * (d + ell))) * Real.sqrt K * Real.sqrt ell) ≤
      (8192 * Real.sqrt (K * (d + ell))) ^ 2 := by
  have hs := Real.sq_sqrt (mul_nonneg hK (add_nonneg hd hl))
  have hp : Real.sqrt K * Real.sqrt ell ≤ Real.sqrt (K * (d + ell)) := by
    rw [← Real.sqrt_mul hK]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hc := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 2560 * (8192 * Real.sqrt (K * (d + ell))) by positivity)
  nlinarith [mul_nonneg hK hl, mul_nonneg hK hd]

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def stoppedSum (Y : ℕ → E) (R : ℝ) : ℕ → E
  | 0 => 0
  | n + 1 => if ‖stoppedSum Y R n‖ ≤ R then stoppedSum Y R n + Y n else stoppedSum Y R n

noncomputable def stoppedIncrement (Y : ℕ → E) (R : ℝ) (n : ℕ) : E :=
  if ‖stoppedSum Y R n‖ ≤ R then Y n else 0

noncomputable def historyStoppedSum {Z : Type*}
    (Y : (n : ℕ) → (Fin n → Z) × Z → E) (R : ℝ) : (n : ℕ) → (Fin n → Z) → E
  | 0, _ => 0
  | n + 1, a =>
    let s := historyStoppedSum Y R n (Fin.init a)
    if ‖s‖ ≤ R then s + Y n (Fin.init a, a (Fin.last n)) else s

lemma history_stopped_sum_measurable {Z : Type*} [MeasurableSpace Z]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {Y : (n : ℕ) → (Fin n → Z) × Z → E}
    (hY : ∀ n, Measurable (Y n)) (R : ℝ) (n : ℕ) :
    Measurable (historyStoppedSum Y R n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hinit : Measurable (Fin.init : (Fin (n + 1) → Z) → Fin n → Z) := by
      apply Measurable.of_eval
      intro i
      exact measurable_pi_apply i.castSucc
    have hs := ih.comp hinit
    have hy := (hY n).comp (hinit.prodMk (measurable_pi_apply (Fin.last n)))
    exact (hs.add hy).ite (measurableSet_le hs.norm measurable_const) hs

lemma history_stopped_sum_eq {Ω Z : Type*} (ξ : ℕ → Ω → Z)
    (Y : (n : ℕ) → (Fin n → Z) × Z → E) (R : ℝ) (n : ℕ) (ω : Ω) :
    historyStoppedSum Y R n (fun i => ξ i ω) =
      stoppedSum (fun i => Y i ((fun j => ξ j ω), ξ i ω)) R n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [historyStoppedSum, stoppedSum, Fin.init_def, Fin.val_castSucc, Fin.val_last, ih]

noncomputable def historyStoppedDirection {Z : Type*}
    (Y : (n : ℕ) → (Fin n → Z) × Z → E) (R : ℝ) (n : ℕ) (a : Fin n → Z) : E :=
  if ‖historyStoppedSum Y R n a‖ ≤ R then historyStoppedSum Y R n a else 0

lemma history_stopped_direction_norm_le {Z : Type*}
    (Y : (n : ℕ) → (Fin n → Z) × Z → E) {R : ℝ} (hR : 0 ≤ R)
    (n : ℕ) (a : Fin n → Z) : ‖historyStoppedDirection Y R n a‖ ≤ R := by
  unfold historyStoppedDirection
  split
  · assumption
  · simpa only [norm_zero] using hR

lemma history_stopped_direction_measurable {Z : Type*} [MeasurableSpace Z]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {Y : (n : ℕ) → (Fin n → Z) × Z → E}
    (hY : ∀ n, Measurable (Y n)) (R : ℝ) (n : ℕ) :
    Measurable (historyStoppedDirection Y R n) := by
  have hs := history_stopped_sum_measurable hY R n
  exact hs.ite (measurableSet_le hs.norm measurable_const) measurable_const

lemma history_stopped_cross_eq [InnerProductSpace ℝ E] {Ω Z : Type*} (ξ : ℕ → Ω → Z)
    (Y : (n : ℕ) → (Fin n → Z) × Z → E) (R : ℝ) (n : ℕ) (ω : Ω) :
    ⟪historyStoppedDirection Y R n (fun i => ξ i ω), Y n ((fun i => ξ i ω), ξ n ω)⟫ =
      ⟪stoppedSum (fun i => Y i ((fun j => ξ j ω), ξ i ω)) R n,
        stoppedIncrement (fun i => Y i ((fun j => ξ j ω), ξ i ω)) R n⟫ := by
  simp only [historyStoppedDirection, history_stopped_sum_eq, stoppedIncrement]
  split <;> simp_all

lemma stopped_sum_step (Y : ℕ → E) (R : ℝ) (n : ℕ) :
    stoppedSum Y R (n + 1) = stoppedSum Y R n + stoppedIncrement Y R n := by
  simp only [stoppedSum, stoppedIncrement]
  split <;> simp_all

lemma stopped_sum_frozen {Y : ℕ → E} {R : ℝ} {t n : ℕ}
    (hexit : R < ‖stoppedSum Y R t‖) (htn : t ≤ n) :
    stoppedSum Y R n = stoppedSum Y R t := by
  induction n, htn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [stoppedSum, ih, ite_eq_right (not_le.mpr hexit)]

lemma stopped_sum_prefix_bound {Y : ℕ → E} {R : ℝ} {n : ℕ}
    (hfinal : ‖stoppedSum Y R n‖ ≤ R) {t : ℕ} (htn : t ≤ n) :
    ‖stoppedSum Y R t‖ ≤ R := by
  by_contra hh
  have he := stopped_sum_frozen (lt_of_not_ge hh) htn
  rw [he] at hfinal
  exact hh hfinal

lemma stopped_sum_eq_unstopped {Y : ℕ → E} {R : ℝ} {n : ℕ}
    (hfinal : ‖stoppedSum Y R n‖ ≤ R) :
    stoppedSum Y R n = ∑ i ∈ Finset.range n, Y i := by
  induction n with
  | zero => simp [stoppedSum]
  | succ n ih =>
    have hp := stopped_sum_prefix_bound hfinal (Nat.le_succ n)
    rw [stoppedSum, ite_eq_left hp, ih hp, Finset.sum_range_succ]

lemma stopped_sum_energy [InnerProductSpace ℝ E] (Y : ℕ → E) (R : ℝ) (n : ℕ) :
    ‖stoppedSum Y R n‖ ^ 2 =
      (∑ i ∈ Finset.range n, ‖stoppedIncrement Y R i‖ ^ 2) +
        2 * ∑ i ∈ Finset.range n, ⟪stoppedSum Y R i, stoppedIncrement Y R i⟫ := by
  induction n with
  | zero => simp [stoppedSum]
  | succ n ih =>
    rw [stopped_sum_step, norm_add_sq_real, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

lemma stopped_increment_norm_le (Y : ℕ → E) (R : ℝ) (n : ℕ) :
    ‖stoppedIncrement Y R n‖ ≤ ‖Y n‖ := by
  unfold stoppedIncrement
  split <;> simp

lemma stopped_energy_control [InnerProductSpace ℝ E] {Y : ℕ → E} {R energy cross : ℝ}
    (hR : 0 ≤ R) (n : ℕ)
    (he : (∑ i ∈ Finset.range n, ‖Y i‖ ^ 2) ≤ energy)
    (hc : (∑ i ∈ Finset.range n, ⟪stoppedSum Y R i, stoppedIncrement Y R i⟫) ≤ cross)
    (hbudget : energy + 2 * cross ≤ R ^ 2) :
    ‖∑ i ∈ Finset.range n, Y i‖ ≤ R := by
  have hes : (∑ i ∈ Finset.range n, ‖stoppedIncrement Y R i‖ ^ 2) ≤ energy := by
    apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) he
    exact pow_le_pow_left₀ (norm_nonneg _) (stopped_increment_norm_le Y R i) 2
  have hidentity := stopped_sum_energy Y R n
  have hfinal : ‖stoppedSum Y R n‖ ≤ R := by nlinarith [norm_nonneg (stoppedSum Y R n)]
  rwa [← stopped_sum_eq_unstopped hfinal]


lemma stopped_energy_tail [InnerProductSpace ℝ E] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℕ → E}
    {R energy cross pe pc : ℝ} (hR : 0 ≤ R) (n : ℕ)
    (he : P.real {ω | energy ≤ ∑ i ∈ Finset.range n, ‖Y ω i‖ ^ 2} ≤ pe)
    (hc : P.real {ω | cross ≤ ∑ i ∈ Finset.range n,
      ⟪stoppedSum (Y ω) R i, stoppedIncrement (Y ω) R i⟫} ≤ pc)
    (hbudget : energy + 2 * cross ≤ R ^ 2) :
    P.real {ω | R < ‖∑ i ∈ Finset.range n, Y ω i‖} ≤ pe + pc := by
  have hsubset : {ω | R < ‖∑ i ∈ Finset.range n, Y ω i‖} ⊆
      {ω | energy ≤ ∑ i ∈ Finset.range n, ‖Y ω i‖ ^ 2} ∪
      {ω | cross ≤ ∑ i ∈ Finset.range n,
        ⟪stoppedSum (Y ω) R i, stoppedIncrement (Y ω) R i⟫} := by
    intro ω hω
    by_contra hn
    have hh := not_or.mp hn
    simp only [Set.mem_ofPred_eq] at hh
    have he' := (lt_of_not_ge hh.1).le
    have hc' := (lt_of_not_ge hh.2).le
    exact (not_le.mpr hω) (stopped_energy_control hR n he' hc' hbudget)
  exact (measureReal_mono hsubset).trans ((measureReal_union_le _ _).trans (add_le_add he hc))

end LongTails.Proofs.StoppedVectorConcentration
