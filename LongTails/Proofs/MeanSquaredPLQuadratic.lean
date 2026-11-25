import LongTails.Setups.HighDimensionalMeanSquaredSmoothPL
import LongTails.Proofs.MeanSquaredPLOracle
import LongTails.Proofs.AbcLowerMeasure
import LongTails.Proofs.FullGeneralizedSmoothZeroQuery
import LongTails.Proofs.Execution
import LongTails.TemplateLowerBound
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

open MeasureTheory OracleTemplate
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.MeanSquaredPLQuadratic

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open LongTails.Proofs.ThirdOrderMaskedOracle (Space)
open LongTails.Proofs.MeanSquaredPLOracle (coin_second_moment)
open LongTails.Proofs.AbcHardOracle (coin unif coin_integral coin_integrable coin_measurable)
open LongTails.Proofs.AbcHardExecution (coinCount)
open LongTails.Proofs.AbcLowerMeasure
open LongTails.Proofs.FullGeneralizedSmoothZeroQuery (quadratic field quadratic_gradient
  quadratic_nonneg quadratic_zero field_lipschitz quadratic_pair)
open LongTails.Setups.HighDimensionalMeanSquaredSmoothPL

variable {d : ℕ}

noncomputable def quadReply (μ qc : ℝ) (x0 v x : Space d) (ω : ℝ) : Space d :=
  μ • (x - x0) - (coin qc ω * μ) • v

lemma quadReply_eq (μ qc : ℝ) (x0 v x : Space d) (ω : ℝ) :
    quadReply μ qc x0 v x ω = field μ (x0 + v) x + (coin qc ω - 1) • (-(μ • v)) := by
  unfold quadReply field
  rw [sub_smul, one_smul, smul_neg, mul_smul, smul_sub, smul_sub, smul_add]
  abel

lemma quadratic_shift (μ : ℝ) (x0 v x : Space d) :
    quadratic μ (x0 + v) x = quadratic μ v (x - x0) := by
  unfold quadratic
  rw [sub_add_eq_sub_sub]

noncomputable def quadOracle (p : Params) (qc : ℝ) (v : Space p.d) :
    Oracle (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d)) where
  Seed := fun _ => ℝ
  law := ⟨stream, inferInstance⟩
  answer := fun _ (_, z) ω => (quadReply p.μ qc p.x0 v z.1 ω, quadReply p.μ qc p.x0 v z.2 ω)

lemma quad_admissible (p : Params) (hv : spec.valid p) (qc : ℝ) (hq0 : 0 < qc) (hq1 : qc ≤ 1)
    (v : Space p.d) (hvar : (1 / qc - 1) * (p.μ ^ 2 * ‖v‖ ^ 2) ≤ p.σ ^ 2)
    (hgap : p.μ / 2 * ‖v‖ ^ 2 ≤ p.Δ) :
    spec.admissible p (quadratic p.μ (p.x0 + v)) (quadOracle p qc v) := by
  obtain ⟨⟨hμ, hL, hLbar, -, -, -⟩, -, -, -⟩ := hv
  change 0 < p.μ at hμ
  change p.μ ≤ p.L at hL
  change p.L ≤ p.Lbar at hLbar
  have hgrad : ∀ x : Space p.d,
      gradient (quadratic p.μ (p.x0 + v)) x = field p.μ (p.x0 + v) x :=
    fun x => (quadratic_gradient p.μ (p.x0 + v) x).gradient
  have hrep : ∀ x : Space p.d, quadReply p.μ qc p.x0 v x = fun ω =>
      field p.μ (p.x0 + v) x + (coin qc ω - 1) • (-(p.μ • v)) :=
    fun x => funext (fun ω => quadReply_eq p.μ qc p.x0 v x ω)
  have hc1 : Integrable (fun ω => coin qc ω - 1) unif :=
    (coin_integrable qc).sub (integrable_const 1)
  have h1 : ∀ x : Space p.d, HasGradientAt (quadratic p.μ (p.x0 + v))
      (gradient (quadratic p.μ (p.x0 + v)) x) x := by
    intro x
    rw [hgrad x]
    exact quadratic_gradient p.μ (p.x0 + v) x
  have h2 : ∀ x y : Space p.d, ‖gradient (quadratic p.μ (p.x0 + v)) x -
      gradient (quadratic p.μ (p.x0 + v)) y‖ ≤ p.L * ‖x - y‖ := by
    intro x y
    rw [hgrad x, hgrad y]
    exact (field_lipschitz p.μ hμ.le (p.x0 + v) x y).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have h3a : IsMinOn (quadratic p.μ (p.x0 + v)) Set.univ (p.x0 + v) := by
    intro x _
    change quadratic p.μ (p.x0 + v) (p.x0 + v) ≤ quadratic p.μ (p.x0 + v) x
    rw [quadratic_zero]
    exact quadratic_nonneg p.μ hμ.le _ _
  have h3b : quadratic p.μ (p.x0 + v) p.x0 - quadratic p.μ (p.x0 + v) (p.x0 + v) ≤ p.Δ := by
    rw [quadratic_zero, sub_zero]
    unfold quadratic
    rw [show p.x0 - (p.x0 + v) = -v by abel, norm_neg]
    exact hgap
  have h3c : ∀ x : Space p.d, 2 * p.μ * (quadratic p.μ (p.x0 + v) x -
      quadratic p.μ (p.x0 + v) (p.x0 + v)) ≤ ‖gradient (quadratic p.μ (p.x0 + v)) x‖ ^ 2 := by
    intro x
    rw [hgrad x, quadratic_zero, sub_zero]
    unfold quadratic field
    rw [norm_smul, mul_pow, Real.norm_of_nonneg hμ.le]
    exact le_of_eq (by ring)
  have h4 : Measurable (Function.uncurry (fun (x : Space p.d) (ω : ℝ) =>
      quadReply p.μ qc p.x0 v x ω)) := by
    have hm1 : Measurable (fun z : Space p.d × ℝ => p.μ • (z.1 - p.x0)) :=
      (measurable_fst.sub_const p.x0).const_smul p.μ
    have hm2 : Measurable (fun z : Space p.d × ℝ => (coin qc z.2 * p.μ) • v) :=
      (((coin_measurable qc).comp measurable_snd).mul_const p.μ).smul_const v
    exact hm1.sub hm2
  have h5 : ∀ x : Space p.d, Integrable (quadReply p.μ qc p.x0 v x) unif := by
    intro x
    rw [hrep x]
    exact (integrable_const _).add (hc1.smul_const _)
  have h6 : ∀ x : Space p.d, ∫ ω, quadReply p.μ qc p.x0 v x ω ∂unif =
      gradient (quadratic p.μ (p.x0 + v)) x := by
    intro x
    rw [hgrad x, hrep x]
    calc ∫ ω, (field p.μ (p.x0 + v) x + (coin qc ω - 1) • (-(p.μ • v))) ∂unif
        = ∫ ω, field p.μ (p.x0 + v) x ∂unif + ∫ ω, (coin qc ω - 1) • (-(p.μ • v)) ∂unif :=
          integral_add (integrable_const _) (hc1.smul_const _)
      _ = field p.μ (p.x0 + v) x + (∫ ω, (coin qc ω - 1) ∂unif) • (-(p.μ • v)) := by
          rw [integral_smul_const]
          simp
      _ = field p.μ (p.x0 + v) x := by
          rw [integral_sub (coin_integrable qc) (integrable_const 1), coin_integral qc hq0 hq1]
          simp
  have hnoise : ∀ x : Space p.d,
      (fun ω => ‖quadReply p.μ qc p.x0 v x ω - gradient (quadratic p.μ (p.x0 + v)) x‖ ^ 2) =
        fun ω => ‖(0 : Space p.d) + (coin qc ω - 1) • (-(p.μ • v))‖ ^ 2 := by
    intro x
    funext ω
    rw [hgrad x, quadReply_eq, add_sub_cancel_left, zero_add]
  have h7 : ∀ x : Space p.d, Integrable (fun ω =>
      ‖quadReply p.μ qc p.x0 v x ω - gradient (quadratic p.μ (p.x0 + v)) x‖ ^ 2) unif := by
    intro x
    rw [hnoise x]
    exact (coin_second_moment qc hq0 hq1 (0 : Space p.d) (-(p.μ • v))).1
  have h8 : ∀ x : Space p.d, ∫ ω,
      ‖quadReply p.μ qc p.x0 v x ω - gradient (quadratic p.μ (p.x0 + v)) x‖ ^ 2 ∂unif ≤
        p.σ ^ 2 := by
    intro x
    rw [hnoise x, (coin_second_moment qc hq0 hq1 (0 : Space p.d) (-(p.μ • v))).2, norm_zero,
      norm_neg, norm_smul, mul_pow, Real.norm_of_nonneg hμ.le]
    linarith
  have hdiff : ∀ x y : Space p.d,
      (fun ω => ‖quadReply p.μ qc p.x0 v x ω - quadReply p.μ qc p.x0 v y ω‖ ^ 2) =
        fun _ => ‖p.μ • (x - y)‖ ^ 2 := by
    intro x y
    funext ω
    unfold quadReply
    congr 2
    rw [smul_sub, smul_sub, smul_sub]
    abel
  have h9 : ∀ x y : Space p.d, Integrable (fun ω =>
      ‖quadReply p.μ qc p.x0 v x ω - quadReply p.μ qc p.x0 v y ω‖ ^ 2) unif := by
    intro x y
    rw [hdiff x y]
    exact integrable_const _
  have h10 : ∀ x y : Space p.d, ∫ ω,
      ‖quadReply p.μ qc p.x0 v x ω - quadReply p.μ qc p.x0 v y ω‖ ^ 2 ∂unif ≤
        p.Lbar ^ 2 * ‖x - y‖ ^ 2 := by
    intro x y
    rw [hdiff x y]
    simp only [integral_const, probReal_univ, one_smul]
    rw [norm_smul, mul_pow, Real.norm_of_nonneg hμ.le]
    have hsq : p.μ ^ 2 ≤ p.Lbar ^ 2 := pow_le_pow_left₀ hμ.le (hL.trans hLbar) 2
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  exact ⟨fun x ω => quadReply p.μ qc p.x0 v x ω,
    ⟨unif, inferInstanceAs (IsProbabilityMeasure unif)⟩,
    ⟨stream, inferInstanceAs (IsProbabilityMeasure stream)⟩, stream_iid, rfl, h1, h2,
    ⟨p.x0 + v, h3a, h3b, h3c⟩, h4, h5, h6, h7, h8, h9, h10⟩

section Run

variable {St : Type*}

noncomputable def baseState (μ : ℝ) (x0 : Space d) (query : St → Space d × Space d)
    (update : St → Space d × Space d → St) (initial : St) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := baseState μ x0 query update initial t
    update s (μ • ((query s).1 - x0), μ • ((query s).2 - x0))

noncomputable def quadState (μ qc : ℝ) (x0 v : Space d) (query : St → Space d × Space d)
    (update : St → Space d × Space d → St) (initial : St) (ω : ℕ → ℝ) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := quadState μ qc x0 v query update initial ω t
    update s (quadReply μ qc x0 v (query s).1 (ω t), quadReply μ qc x0 v (query s).2 (ω t))

lemma quadState_eq_base (μ qc : ℝ) (x0 v : Space d) (query : St → Space d × Space d)
    (update : St → Space d × Space d → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (h : coinCount qc ω N = 0) :
    quadState μ qc x0 v query update initial ω N = baseState μ x0 query update initial N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [coinCount] at h
    have h1 : coinCount qc ω N = 0 := by omega
    have h2 : ¬ ω N ≤ qc := by
      intro hc
      rw [ite_eq_left hc] at h
      omega
    have hc0 : coin qc (ω N) = 0 := by
      unfold coin
      rw [ite_eq_right h2]
    simp only [quadState, baseState, ih h1, quadReply, hc0, zero_mul, zero_smul, sub_zero]

lemma quadState_iterate (μ qc : ℝ) (x0 v : Space d) (query : St → Space d × Space d)
    (update : St → Space d × Space d → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ) :
    ((fun sc : St × ℕ => (update sc.1 (quadReply μ qc x0 v (query sc.1).1 (ω sc.2),
      quadReply μ qc x0 v (query sc.1).2 (ω sc.2)), sc.2 + 1))^[N] (initial, 0)) =
      (quadState μ qc x0 v query update initial ω N, N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

end Run

lemma execute_quad (p : Params) (qc : ℝ) (v : Space p.d)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d))) (N : ℕ) (seed : A.Seed) (ω : ℕ → ℝ) :
    execute (quadOracle p qc v) A (fun _ => N) seed ω =
      A.output (quadState p.μ qc p.x0 v (fun s => (A.query s).2) A.update
        (A.initial seed) ω N) := by
  have h1 := execute_indexed_of_answer (quadOracle p qc v) A N seed ω
    (fun t query => (quadReply p.μ qc p.x0 v query.2.1 (ω t),
      quadReply p.μ qc p.x0 v query.2.2 (ω t)))
    (fun _ query => by cases query; rfl)
  refine h1.trans ?_
  exact congrArg (fun st => A.output st.1) (quadState_iterate p.μ qc p.x0 v
    (fun s => (A.query s).2) A.update (A.initial seed) ω N)

lemma no_coin_fraction (qc : ℝ) (hq0 : 0 < qc) (hq1 : qc ≤ 1) (N : ℕ)
    (hNq : (N : ℝ) * qc * 2 ≤ 1) :
    1 / 2 ≤ stream.real {ω | coinCount qc ω N = 0} := by
  have ht := coinCount_tail qc hq0.le hq1 N 0
  simp only [Nat.cast_zero, zero_add, div_one] at ht
  have hc : {ω : ℕ → ℝ | coinCount qc ω N = 0} = {ω | 1 ≤ coinCount qc ω N}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    omega
  have hmeas : MeasurableSet {ω : ℕ → ℝ | 1 ≤ coinCount qc ω N} := by
    have h := (coinCount_measurable qc N)
      (measurableSet_Ici : MeasurableSet (Set.Ici (((1 : ℕ)) : ℝ)))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ici]
    constructor <;> intro h <;> exact_mod_cast h
  rw [hc, measureReal_compl hmeas, probReal_univ]
  linarith

theorem quad_failure_at (p : Params) (hv : spec.valid p) (hσ : 5 * p.μ * p.ε ≤ p.σ ^ 2)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d))) (N : ℕ)
    (hN : (N : ℝ) * (10 * p.μ * p.ε) ≤ p.σ ^ 2) (hd : 0 < p.d) :
    ∃ (I : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (oracle : Oracle (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
        (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p I oracle ∧
        ¬ spec.successful p I
          (fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) =>
            execute oracle A (fun _ => N) seed.1 seed.2)
          ⟨(A.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩ := by
  have hv' := hv
  obtain ⟨⟨hμ, hL, hLbar, hσ0, hΔ, hε⟩, hκ, hΔε, hdim⟩ := hv'
  change 0 < p.μ at hμ
  change 0 < p.ε at hε
  have hσ2 : 0 < p.σ ^ 2 := lt_of_lt_of_le (by positivity) hσ
  set qc : ℝ := 5 * p.μ * p.ε / p.σ ^ 2 with hqc
  have hq0 : 0 < qc := by positivity
  have hq1 : qc ≤ 1 := by
    rw [hqc, div_le_one hσ2]
    exact hσ
  let e0 : Space p.d := EuclideanSpace.single (⟨0, hd⟩ : Fin p.d) (1 : ℝ)
  have he0 : ‖e0‖ = 1 := by simp [e0]
  set r : ℝ := √(5 * p.ε / p.μ) with hr
  have hr2 : r ^ 2 = 5 * p.ε / p.μ := Real.sq_sqrt (by positivity)
  let v0 : Space p.d := r • e0
  have hv0 : ‖v0‖ ^ 2 = 5 * p.ε / p.μ := by
    simp only [v0]
    rw [norm_smul, he0, mul_one, Real.norm_eq_abs, sq_abs, hr2]
  have hμc : p.μ * (5 * p.ε / p.μ) = 5 * p.ε := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hμ.ne'
  have h5pos : 0 < 5 * p.μ * p.ε := by positivity
  have hvarc : ∀ v : Space p.d, ‖v‖ ^ 2 = 5 * p.ε / p.μ →
      (1 / qc - 1) * (p.μ ^ 2 * ‖v‖ ^ 2) ≤ p.σ ^ 2 := by
    intro v hvn
    rw [hvn]
    have e1 : p.μ ^ 2 * (5 * p.ε / p.μ) = 5 * p.μ * p.ε := by
      calc p.μ ^ 2 * (5 * p.ε / p.μ) = p.μ * (p.μ * (5 * p.ε / p.μ)) := by ring
        _ = 5 * p.μ * p.ε := by rw [hμc]; ring
    have h1 : 1 / qc * (p.μ ^ 2 * (5 * p.ε / p.μ)) = p.σ ^ 2 := by
      rw [e1, hqc, one_div, inv_div]
      exact div_mul_cancel₀ _ h5pos.ne'
    have h2 : 0 ≤ p.μ ^ 2 * (5 * p.ε / p.μ) := by
      rw [e1]
      exact h5pos.le
    linarith
  have hgapc : ∀ v : Space p.d, ‖v‖ ^ 2 = 5 * p.ε / p.μ → p.μ / 2 * ‖v‖ ^ 2 ≤ p.Δ := by
    intro v hvn
    rw [hvn]
    have h1 : p.μ / 2 * (5 * p.ε / p.μ) = 5 / 2 * p.ε := by
      calc p.μ / 2 * (5 * p.ε / p.μ) = 1 / 2 * (p.μ * (5 * p.ε / p.μ)) := by ring
        _ = 5 / 2 * p.ε := by rw [hμc]; ring
    rw [h1]
    linarith
  have hnv0 : ‖-v0‖ ^ 2 = 5 * p.ε / p.μ := by rw [norm_neg]; exact hv0
  by_contra hcon
  push Not at hcon
  have hsP := hcon _ _ (quad_admissible p hv qc hq0 hq1 v0 (hvarc v0 hv0) (hgapc v0 hv0))
  have hsM := hcon _ _ (quad_admissible p hv qc hq0 hq1 (-v0) (hvarc _ hnv0) (hgapc _ hnv0))
  let query : A.State → Space p.d × Space p.d := fun s => (A.query s).2
  let P : Measure (A.Seed × (ℕ → ℝ)) := (A.law : Measure A.Seed).prod stream
  let loss : Space p.d → A.Seed × (ℕ → ℝ) → ℝ := fun v z =>
    quadratic p.μ (p.x0 + v) (A.output (quadState p.μ qc p.x0 v query A.update
      (A.initial z.1) z.2 N))
  have hloss0 (v : Space p.d) (z : A.Seed × (ℕ → ℝ)) : 0 ≤ loss v z :=
    quadratic_nonneg p.μ hμ.le _ _
  have hsucc (v : Space p.d)
      (hs : spec.successful p (quadratic p.μ (p.x0 + v))
        (fun seed : A.Seed × ((k : ℕ) → (quadOracle p qc v).Seed k) =>
          execute (quadOracle p qc v) A (fun _ => N) seed.1 seed.2)
        ⟨(A.law : Measure _).prod ((quadOracle p qc v).law : Measure _), inferInstance⟩) :
      Integrable (loss v) P ∧ ∫ z, loss v z ∂P ≤ p.ε := by
    obtain ⟨-, xs, hxs, hint, hle⟩ := hs
    have hval : quadratic p.μ (p.x0 + v) xs = 0 := by
      have h1 := isMinOn_iff.mp hxs (p.x0 + v) (Set.mem_univ _)
      rw [quadratic_zero] at h1
      exact le_antisymm h1 (quadratic_nonneg p.μ hμ.le _ _)
    have hfun : (fun z : A.Seed × (ℕ → ℝ) => quadratic p.μ (p.x0 + v)
        (execute (quadOracle p qc v) A (fun _ => N) z.1 z.2) -
        quadratic p.μ (p.x0 + v) xs) = loss v := by
      funext z
      rw [hval, sub_zero, execute_quad]
    rw [← hfun]
    exact ⟨hint, hle⟩
  obtain ⟨hiP, hleP⟩ := hsucc v0 hsP
  obtain ⟨hiM, hleM⟩ := hsucc (-v0) hsM
  let good : A.Seed × (ℕ → ℝ) → ℝ := fun z =>
    Set.indicator {z : A.Seed × (ℕ → ℝ) | coinCount qc z.2 N = 0} 1 z
  have hpt (z : A.Seed × (ℕ → ℝ)) : 5 * p.ε * good z ≤ loss v0 z + loss (-v0) z := by
    by_cases hz : coinCount qc z.2 N = 0
    · have hg : good z = 1 := by simp [good, hz]
      rw [hg, mul_one]
      simp only [loss]
      rw [quadState_eq_base p.μ qc p.x0 v0 query A.update (A.initial z.1) z.2 N hz,
        quadState_eq_base p.μ qc p.x0 (-v0) query A.update (A.initial z.1) z.2 N hz,
        quadratic_shift, quadratic_shift]
      have hpair := quadratic_pair p.μ hμ.le v0
        (A.output (baseState p.μ p.x0 query A.update (A.initial z.1) N) - p.x0)
      rw [hv0] at hpair
      have h5 : p.μ * (5 * p.ε / p.μ) = 5 * p.ε := hμc
      linarith
    · have hg : good z = 0 := by simp [good, hz]
      rw [hg, mul_zero]
      exact add_nonneg (hloss0 _ _) (hloss0 _ _)
  have hsetmeas : MeasurableSet {ω : ℕ → ℝ | coinCount qc ω N = 0} := by
    have h := (coinCount_measurable qc N) (measurableSet_singleton (0 : ℝ))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor <;> intro h <;> exact_mod_cast h
  have hgoodmeas : MeasurableSet {z : A.Seed × (ℕ → ℝ) | coinCount qc z.2 N = 0} :=
    measurable_snd hsetmeas
  have hgood_int : ∫ z, good z ∂P = stream.real {ω | coinCount qc ω N = 0} := by
    rw [integral_indicator_one hgoodmeas]
    have hm : P.map Prod.snd = stream := by
      dsimp only [P]
      rw [Measure.map_snd_prod]
      simp
    have hpre : {z : A.Seed × (ℕ → ℝ) | coinCount qc z.2 N = 0} =
        Prod.snd ⁻¹' {ω | coinCount qc ω N = 0} := rfl
    rw [hpre, Measure.real, ← Measure.map_apply measurable_snd hsetmeas, hm]
    rfl
  have hNq : (N : ℝ) * qc * 2 ≤ 1 := by
    rw [hqc]
    have h1 : (N : ℝ) * (5 * p.μ * p.ε / p.σ ^ 2) * 2 = (N : ℝ) * (10 * p.μ * p.ε) / p.σ ^ 2 := by
      ring
    rw [h1, div_le_one hσ2]
    exact hN
  have hfrac := no_coin_fraction qc hq0 hq1 N hNq
  have hint_good : Integrable (fun z => 5 * p.ε * good z) P :=
    ((integrable_const (1 : ℝ)).indicator hgoodmeas).const_mul _
  have hsumI : Integrable (fun z => loss v0 z + loss (-v0) z) P := hiP.add hiM
  have hmono := integral_mono hint_good hsumI hpt
  have hadd : ∫ z, (loss v0 z + loss (-v0) z) ∂P = ∫ z, loss v0 z ∂P + ∫ z, loss (-v0) z ∂P :=
    integral_add hiP hiM
  rw [integral_const_mul, hgood_int, hadd] at hmono
  nlinarith

end LongTails.Proofs.MeanSquaredPLQuadratic
