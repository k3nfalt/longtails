import LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum
import LongTails.Proofs.FullGeneralizedSmoothZeroQuery

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OracleTemplate MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.InterpolatedFiniteSumHiddenComponent

open LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum
open FullGeneralizedSmoothZeroQuery

noncomputable def component (p : Params) (j : Fin p.n) (z : Point p)
    (i : Fin p.n) (x : Point p) : ℝ := if i = j then quadratic p.L0 z x else 0

noncomputable def componentField (p : Params) (j : Fin p.n) (z : Point p)
    (i : Fin p.n) (x : Point p) : Point p := if i = j then field p.L0 z x else 0

lemma component_same (p : Params) (j : Fin p.n) (z : Point p) :
    component p j z j = quadratic p.L0 z := by funext x; simp [component]

lemma component_other (p : Params) (j : Fin p.n) (z : Point p) (i : Fin p.n) (h : i ≠ j) :
    component p j z i = fun _ => 0 := by funext x; simp [component, h]

lemma componentField_same (p : Params) (j : Fin p.n) (z : Point p) :
    componentField p j z j = field p.L0 z := by funext x; simp [componentField]

lemma componentField_other (p : Params) (j : Fin p.n) (z : Point p) (i : Fin p.n) (h : i ≠ j) :
    componentField p j z i = fun _ => 0 := by funext x; simp [componentField, h]

lemma component_gradient (p : Params) (j : Fin p.n) (z : Point p) (i : Fin p.n) (x : Point p) :
    HasGradientAt (component p j z i) (componentField p j z i x) x := by
  by_cases h : i = j
  · subst i
    rw [component_same, componentField_same]
    exact quadratic_gradient p.L0 z x
  · rw [component_other p j z i h, componentField_other p j z i h]
    exact hasGradientAt_const x (0 : ℝ)

lemma component_gradient_eq (p : Params) (j : Fin p.n) (z : Point p) (i : Fin p.n) :
    gradient (component p j z i) = componentField p j z i :=
  funext (fun x => (component_gradient p j z i x).gradient)

lemma component_differentiable (p : Params) (j : Fin p.n) (z : Point p) (i : Fin p.n) :
    Differentiable ℝ (componentField p j z i) := by
  by_cases h : i = j
  · subst i
    rw [componentField_same]
    exact ((differentiable_id : Differentiable ℝ (fun x : Point p => x)).sub_const z).const_smul p.L0
  · rw [componentField_other p j z i h]
    exact differentiable_const _

lemma component_curvature (p : Params) (hL : 0 ≤ p.L0) (j : Fin p.n) (z : Point p)
    (i : Fin p.n) (x : Point p) : ‖fderiv ℝ (componentField p j z i) x‖ ≤ p.L0 := by
  apply norm_fderiv_le_of_lipschitz ℝ (C := ⟨p.L0, hL⟩)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖componentField p j z i x - componentField p j z i y‖ ≤ p.L0 * ‖x - y‖
  by_cases h : i = j
  · simpa only [componentField, ite_eq_left h] using field_lipschitz p.L0 hL z x y
  · simp only [componentField, ite_eq_right h, sub_self, norm_zero]
    positivity

lemma component_nonnegative (p : Params) (hL : 0 ≤ p.L0) (j : Fin p.n) (z : Point p)
    (i : Fin p.n) (x : Point p) : 0 ≤ component p j z i x := by
  unfold component
  split_ifs
  · exact quadratic_nonneg p.L0 hL z x
  · rfl

lemma component_zero (p : Params) (j : Fin p.n) (z : Point p) (i : Fin p.n) :
    component p j z i z = 0 := by simp [component, quadratic_zero]

lemma objective_eq (p : Params) (j : Fin p.n) (z x : Point p) :
    objective (component p j z) x = (p.n : ℝ)⁻¹ * quadratic p.L0 z x := by
  simp [objective, component]

lemma objective_zero (p : Params) (j : Fin p.n) (z : Point p) :
    objective (component p j z) z = 0 := by rw [objective_eq, quadratic_zero, mul_zero]

lemma objective_nonnegative (p : Params) (hL : 0 ≤ p.L0) (j : Fin p.n) (z x : Point p) :
    0 ≤ objective (component p j z) x := by
  rw [objective_eq]
  exact mul_nonneg (by positivity) (quadratic_nonneg p.L0 hL z x)

noncomputable def oracle (p : Params) (j : Fin p.n) (z : Point p) :
    Oracle (Fin p.n × Point p) (ℝ × Point p) where
  answer _ q _ := (component p j z q.2.1 q.2.2, componentField p j z q.2.1 q.2.2)

lemma admissible (p : Params) (hp : spec.valid p) (j : Fin p.n) (z : Point p)
    (hz : ‖z‖ ≤ p.R) (hgap : (p.n : ℝ)⁻¹ * (p.L0 / 2 * ‖z‖ ^ 2) ≤ p.Δ) :
    spec.admissible p (component p j z) (oracle p j z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, z, ?_, hz, ?_⟩
  · intro i
    by_cases h : i = j
    · subst i
      rw [component_same]
      exact quadratic_convex p.L0 hp.1.le z
    · rw [component_other p j z i h]
      exact convexOn_const _ convex_univ
  · intro i x
    rw [component_gradient_eq]
    exact component_gradient p j z i x
  · intro i
    rw [component_gradient_eq]
    exact component_differentiable p j z i
  · intro i x
    rw [component_gradient_eq]
    exact (component_curvature p hp.1.le j z i x).trans
      (le_add_of_nonneg_right (mul_nonneg hp.2.1 (norm_nonneg _)))
  · intro history seed i x
    simp only [oracle, component_gradient_eq]
  · intro i x _
    change component p j z i z ≤ component p j z i x
    rw [component_zero]
    exact component_nonnegative p hp.1.le j z i x
  · simpa [objective, component, quadratic] using hgap

lemma objective_pair (p : Params) (hL : 0 ≤ p.L0) (j : Fin p.n) (z x : Point p) :
    (p.n : ℝ)⁻¹ * (p.L0 * ‖z‖ ^ 2) ≤
      objective (component p j z) x + objective (component p j (-z)) x := by
  rw [objective_eq, objective_eq, ← mul_add]
  exact mul_le_mul_of_nonneg_left (quadratic_pair p.L0 hL z x) (by positivity)

noncomputable def visited (p : Params)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ) (initial : A.State) :
    Finset (Fin p.n) :=
  (Finset.range b).image (fun t => (A.query ((fun s => A.update s (0, 0))^[t] initial)).2.1)

lemma visited_card (p : Params)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ) (initial : A.State) :
    (visited p A b initial).card ≤ b := by
  exact (Finset.card_image_le).trans_eq (Finset.card_range b)

lemma execute_component (p : Params) (j : Fin p.n) (z : Point p)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (seed : A.Seed) (ξ : ℕ → Unit) :
    execute (oracle p j z) A (fun _ => b) seed ξ =
      A.output ((fun s => A.update s (component p j z (A.query s).2.1 (A.query s).2.2,
        componentField p j z (A.query s).2.1 (A.query s).2.2))^[b] (A.initial seed)) := by
  rw [execute_eq_of_answer_eq (oracle p j z)
    (fun q => (component p j z q.1 q.2, componentField p j z q.1 q.2)) (by intros; rfl)]
  exact execute_iterate (fun q : Fin p.n × Point p =>
    (component p j z q.1 q.2, componentField p j z q.1 q.2)) A b seed

lemma execute_unvisited (p : Params) (j : Fin p.n) (z : Point p)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (seed : A.Seed) (ξ : ℕ → Unit) (hj : j ∉ visited p A b (A.initial seed)) :
    execute (oracle p j z) A (fun _ => b) seed ξ =
      A.output ((fun s => A.update s (0, 0))^[b] (A.initial seed)) := by
  rw [execute_component]
  apply congrArg A.output
  let step := fun s => A.update s (component p j z (A.query s).2.1 (A.query s).2.2,
    componentField p j z (A.query s).2.1 (A.query s).2.2)
  have he (k : ℕ) (hk : k ≤ b) : step^[k] (A.initial seed) =
      (fun s => A.update s (0, 0))^[k] (A.initial seed) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
      have hn : (A.query ((fun s => A.update s (0, 0))^[k] (A.initial seed))).2.1 ≠ j := by
        intro h
        apply hj
        exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), h⟩
      simp only [step, component, componentField, ite_eq_right hn]
  exact he b le_rfl

lemma execution_pair_sum (p : Params) (hL : 0 ≤ p.L0) (z : Point p)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (seed : A.Seed) (ξ : ℕ → Unit) :
    ((p.n : ℝ) - b) * ((p.n : ℝ)⁻¹ * (p.L0 * ‖z‖ ^ 2)) ≤
      ∑ j : Fin p.n, (objective (component p j z)
        (execute (oracle p j z) A (fun _ => b) seed ξ) +
        objective (component p j (-z))
        (execute (oracle p j (-z)) A (fun _ => b) seed ξ)) := by
  classical
  let S := visited p A b (A.initial seed)
  let c := (p.n : ℝ)⁻¹ * (p.L0 * ‖z‖ ^ 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ht : (p.n : ℝ) - b ≤ ((Finset.univ \ S).card : ℝ) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by simpa using Finset.card_le_card (Finset.subset_univ S))]
    have hb := visited_card p A b (A.initial seed)
    exact sub_le_sub_left (by exact_mod_cast hb) _
  calc
    _ ≤ ((Finset.univ \ S).card : ℝ) * c := mul_le_mul_of_nonneg_right ht hc
    _ = ∑ j ∈ Finset.univ \ S, c := by simp
    _ ≤ ∑ j ∈ Finset.univ \ S, (objective (component p j z)
        (execute (oracle p j z) A (fun _ => b) seed ξ) +
        objective (component p j (-z))
        (execute (oracle p j (-z)) A (fun _ => b) seed ξ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ∉ S := (Finset.mem_sdiff.mp hj).2
      rw [execute_unvisited p j z A b seed ξ hj',
        execute_unvisited p j (-z) A b seed ξ hj']
      exact objective_pair p hL j z _
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      (fun j _ _ => add_nonneg (objective_nonnegative p hL j z _)
        (objective_nonnegative p hL j (-z) _))

lemma success_integral (p : Params) (hp : spec.valid p) (j : Fin p.n) (z : Point p)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (h : spec.successful p (component p j z)
      (fun w : A.Seed × (ℕ → Unit) => execute (oracle p j z) A (fun _ => b) w.1 w.2)
      ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩) :
    Integrable (fun w : A.Seed × (ℕ → Unit) => objective (component p j z)
      (execute (oracle p j z) A (fun _ => b) w.1 w.2))
      ((A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ()))) ∧
    (∫ w : A.Seed × (ℕ → Unit), objective (component p j z)
      (execute (oracle p j z) A (fun _ => b) w.1 w.2)
      ∂((A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())))) ≤ p.ε := by
  obtain ⟨x, hm, hi, he⟩ := h
  have hz : objective (component p j z) x = 0 := by
    apply le_antisymm
    · rw [objective_eq]
      have hj := hm j (Set.mem_univ z)
      simpa [component, quadratic_zero] using
        mul_le_mul_of_nonneg_left hj (by positivity : 0 ≤ (p.n : ℝ)⁻¹)
    · exact objective_nonnegative p hp.1.le j z x
  simp only [hz, sub_zero] at hi he
  exact ⟨hi, he⟩

lemma finite_mean_obstruction {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : ProbabilityMeasure Ω) (loss : ι → Ω → ℝ) (c e : ℝ)
    (hi : ∀ j, Integrable (loss j) (P : Measure _))
    (he : ∀ j, (∫ w, loss j w ∂(P : Measure _)) ≤ e)
    (hl : ∀ w, c ≤ ∑ j, loss j w) (hc : (Fintype.card ι : ℝ) * e < c) : False := by
  have hh := integral_mono (μ := (P : Measure _)) (integrable_const c)
    (integrable_finsetSum Finset.univ (fun j _ => hi j)) hl
  rw [integral_finsetSum _ (fun j _ => hi j)] at hh
  simp only [integral_const, probReal_univ, one_smul] at hh
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun j _ => he j)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hu
  linarith only [hc, hh, hu]

set_option maxHeartbeats 800000 in
lemma failure_of_radius (p : Params) (hp : spec.valid p) (z : Point p) (b : ℕ)
    (hz : ‖z‖ ≤ p.R) (hgap : (p.n : ℝ)⁻¹ * (p.L0 / 2 * ‖z‖ ^ 2) ≤ p.Δ)
    (hlarge : 2 * p.n * p.ε < ((p.n : ℝ) - b) *
      ((p.n : ℝ)⁻¹ * (p.L0 * ‖z‖ ^ 2)))
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) :
    ∃ (f : Fin p.n → Point p → ℝ) (O : Oracle (Fin p.n × Point p) (ℝ × Point p)),
      spec.admissible p f O ∧ ¬ spec.successful p f
        (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => b) w.1 w.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  by_contra h
  push Not at h
  have hs (j : Fin p.n) (v : Point p) (hv : ‖v‖ ≤ p.R)
      (hg : (p.n : ℝ)⁻¹ * (p.L0 / 2 * ‖v‖ ^ 2) ≤ p.Δ) :=
    success_integral p hp j v A b (h _ _ (admissible p hp j v hv hg))
  have hplus (j : Fin p.n) := hs j z hz hgap
  have hminus (j : Fin p.n) := hs j (-z) (by simpa using hz) (by simpa using hgap)
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  let loss := fun (j : Fin p.n) (w : A.Seed × (ℕ → Unit)) =>
    objective (component p j z) (execute (oracle p j z) A (fun _ => b) w.1 w.2) +
    objective (component p j (-z)) (execute (oracle p j (-z)) A (fun _ => b) w.1 w.2)
  have hi (j : Fin p.n) : Integrable (loss j) (P : Measure _) :=
    (hplus j).1.add (hminus j).1
  have he (j : Fin p.n) : (∫ w, loss j w ∂(P : Measure _)) ≤ 2 * p.ε := by
    dsimp [loss, P]
    rw [integral_add (hplus j).1 (hminus j).1]
    linarith only [(hplus j).2, (hminus j).2]
  exact finite_mean_obstruction P loss
    (((p.n : ℝ) - b) * ((p.n : ℝ)⁻¹ * (p.L0 * ‖z‖ ^ 2))) (2 * p.ε) hi he
    (fun w => execution_pair_sum p hp.1.le z A b w.1 w.2)
    (by simpa only [Fintype.card_fin, mul_comm, mul_left_comm, mul_assoc] using hlarge)


lemma exists_failure (p : Params) (hp : spec.valid p) (hd : 0 < p.d)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p))
    (b : ℕ) (hb : b ≤ p.n / 4) :
    ∃ (f : Fin p.n → Point p → ℝ) (O : Oracle (Fin p.n × Point p) (ℝ × Point p)),
      spec.admissible p f O ∧ ¬ spec.successful p f
        (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => b) w.1 w.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast (show 0 < p.n by have := hp.2.2.2.2.1; omega)
  have hε := hp.2.2.2.1
  have hL := hp.1
  let r := Real.sqrt (4 * p.n * p.ε / p.L0)
  let z : Point p := PiLp.single 2 ⟨0, hd⟩ r
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hz : ‖z‖ = r := by simp [z, Real.norm_of_nonneg hr]
  have hr2 : r ^ 2 = 4 * p.n * p.ε / p.L0 := Real.sq_sqrt (by positivity)
  have hrad : ‖z‖ ≤ p.R := by
    rw [hz]
    have hh := hp.2.2.2.2.2.2.1
    have hu : r ^ 2 ≤ p.R ^ 2 := by
      rw [hr2, div_le_iff₀ hp.1]
      nlinarith only [hh]
    nlinarith [hp.2.2.1]
  have hval : (p.n : ℝ)⁻¹ * (p.L0 * ‖z‖ ^ 2) = 4 * p.ε := by
    rw [hz, hr2]
    field_simp [ne_of_gt hL, ne_of_gt hn]
  have hgap : (p.n : ℝ)⁻¹ * (p.L0 / 2 * ‖z‖ ^ 2) ≤ p.Δ := by
    have h := hp.2.2.2.2.2.1
    nlinarith only [hval, h]
  have hb4 : 4 * (b : ℝ) ≤ p.n := by
    have hh : 4 * b ≤ p.n := (Nat.mul_le_mul_left 4 hb).trans (by omega)
    exact_mod_cast hh
  apply failure_of_radius p hp z b hrad hgap _ A
  rw [hval]
  nlinarith [mul_pos hn hε]

noncomputable def exactOracle (p : Params) (f : Fin p.n → Point p → ℝ)
    (g : Fin p.n → Point p → Point p) : Oracle (Fin p.n × Point p) (ℝ × Point p) where
  answer _ q _ := (f q.2.1 q.2.2, g q.2.1 q.2.2)

lemma success_zero_minimum (p : Params) (f : Fin p.n → Point p → ℝ)
    (g : Fin p.n → Point p → Point p) (z : Point p)
    (hnonneg : ∀ i x, 0 ≤ f i x) (hzero : ∀ i, f i z = 0)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (h : spec.successful p f
      (fun w : A.Seed × (ℕ → Unit) => execute (exactOracle p f g) A (fun _ => b) w.1 w.2)
      ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩) :
    Integrable (fun w : A.Seed × (ℕ → Unit) => objective f
      (execute (exactOracle p f g) A (fun _ => b) w.1 w.2))
      ((A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ()))) ∧
    (∫ w : A.Seed × (ℕ → Unit), objective f
      (execute (exactOracle p f g) A (fun _ => b) w.1 w.2)
      ∂((A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())))) ≤ p.ε := by
  obtain ⟨x, hm, hi, he⟩ := h
  have hx (i : Fin p.n) : f i x = 0 := by
    apply le_antisymm
    · have hh := hm i (Set.mem_univ z)
      change f i x ≤ f i z at hh
      rwa [hzero i] at hh
    · exact hnonneg i x
  have hv : objective f x = 0 := by simp [objective, hx]
  simp only [hv, sub_zero] at hi he
  exact ⟨hi, he⟩

lemma finite_prior_failure (p : Params) {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → Fin p.n → Point p → ℝ) (g : ι → Fin p.n → Point p → Point p)
    (z : ι → Point p) (hAd : ∀ i, spec.admissible p (f i) (exactOracle p (f i) (g i)))
    (hnonneg : ∀ i j x, 0 ≤ f i j x) (hzero : ∀ i j, f i j (z i) = 0)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (K : ℝ) (hK : p.ε < K)
    (hmean : ∀ (seed : A.Seed) (ξ : ℕ → Unit), K * Fintype.card ι ≤
      ∑ i, objective (f i) (execute (exactOracle p (f i) (g i)) A (fun _ => b) seed ξ)) :
    ∃ (F : Fin p.n → Point p → ℝ) (O : Oracle (Fin p.n × Point p) (ℝ × Point p)),
      spec.admissible p F O ∧ ¬ spec.successful p F
        (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => b) w.1 w.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  by_contra h
  push Not at h
  have hs (i : ι) := success_zero_minimum p (f i) (g i) (z i) (hnonneg i) (hzero i) A b
    (h (f i) (exactOracle p (f i) (g i)) (hAd i))
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  let loss := fun (i : ι) (w : A.Seed × (ℕ → Unit)) =>
    objective (f i) (execute (exactOracle p (f i) (g i)) A (fun _ => b) w.1 w.2)
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  exact finite_mean_obstruction P loss (K * Fintype.card ι) p.ε
    (fun i => (hs i).1) (fun i => (hs i).2) (fun w => hmean w.1 w.2)
    (by nlinarith only [mul_lt_mul_of_pos_right hK hcard])

end LongTails.Proofs.InterpolatedFiniteSumHiddenComponent
