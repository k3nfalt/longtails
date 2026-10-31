import LongTails.Proofs.GuardedHessianEstimator

open MeasureTheory
open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.GuardedHessianTransport
open LongTails.Proofs.GuardedHessianExecution
open LongTails.Proofs.GuardedHessianEstimator

namespace LongTails.Proofs.GuardedHessianDescent

noncomputable def shadowPoint {E : Type*} (x0 : E) (alive : ℕ → Bool) (proposal : ℕ → E) : ℕ → E
  | 0 => x0
  | n + 1 => if alive n then proposal n else shadowPoint x0 alive proposal n

lemma shadowPoint_live {E : Type*} (x0 : E) (alive : ℕ → Bool) (point proposal : ℕ → E)
    (h0 : point 0 = x0)
    (halive : ∀ n, alive (n + 1) = true → alive n = true)
    (hnext : ∀ n, alive (n + 1) = true → point (n + 1) = proposal n) (n : ℕ) :
    alive n = true → shadowPoint x0 alive proposal n = point n := by
  cases n with
  | zero => exact fun _ => h0.symm
  | succ n =>
      intro hn
      simp only [shadowPoint, halive n hn, ↓reduceIte]
      exact (hnext n hn).symm

lemma shadowPoint_ledger {E : Type*} (f : E → ℝ) (x0 : E)
    (alive : ℕ → Bool) (point proposal : ℕ → E)
    (hlive : ∀ n, alive n = true → shadowPoint x0 alive proposal n = point n) (N : ℕ) :
    f (shadowPoint x0 alive proposal N) = f x0 +
      ∑ n ∈ Finset.range N, if alive n then f (proposal n) - f (point n) else 0 := by
  induction N with
  | zero => simp [shadowPoint]
  | succ N ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih, shadowPoint]
      by_cases hN : alive N = true
      · rw [ite_eq_left hN, ite_eq_left hN, hlive N hN]
        ring
      · simp only [hN, Bool.false_eq_true, ↓reduceIte, add_zero]

lemma shadowPoint_measurable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (x0 : E) (alive : ℕ → Ω → Bool) (proposal : ℕ → Ω → E)
    (ha : ∀ n, Measurable (alive n)) (hp : ∀ n, Measurable (proposal n)) (n : ℕ) :
    Measurable (fun ω => shadowPoint x0 (fun j => alive j ω) (fun j => proposal j ω) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (hp n).ite ((ha n) (measurableSet_singleton true)) ih

lemma shadowPoint_norm_bound {E : Type*} [SeminormedAddCommGroup E]
    (x0 : E) (alive : ℕ → Bool) (proposal : ℕ → E) {R : ℝ}
    (h0 : ‖x0‖ ≤ R) (hp : ∀ n, ‖proposal n‖ ≤ R) (n : ℕ) :
    ‖shadowPoint x0 alive proposal n‖ ≤ R := by
  induction n with
  | zero => exact h0
  | succ n ih =>
      dsimp only [shadowPoint]
      split_ifs
      · exact hp n
      · exact ih

lemma shadow_descent_sum {E : Type*} (f : E → ℝ) (x0 : E)
    (alive : ℕ → Bool) (point proposal : ℕ → E) (G error : ℕ → ℝ)
    {η curvature : ℝ} (hcurv : 0 ≤ curvature)
    (hlive : ∀ n, alive n = true → shadowPoint x0 alive proposal n = point n)
    (hdescent : ∀ n, alive n = true →
      f (proposal n) ≤ f (point n) - η * G n + 2 * η * error n + curvature) (N : ℕ) :
    η * (∑ n ∈ Finset.range N, if alive n then G n else 0) ≤
      f x0 - f (shadowPoint x0 alive proposal N) +
        2 * η * (∑ n ∈ Finset.range N, if alive n then error n else 0) + N * curvature := by
  have hstep (n : ℕ) : (if alive n then f (proposal n) - f (point n) else 0) ≤
      -η * (if alive n then G n else 0) +
        2 * η * (if alive n then error n else 0) + curvature := by
    by_cases hn : alive n = true
    · simp only [hn, ↓reduceIte]
      linarith [hdescent n hn]
    · simp only [hn, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_add]
      exact hcurv
  have hh := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) => hstep n)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
  have hledger := shadowPoint_ledger f x0 alive point proposal hlive N
  linarith

lemma iter_point_zero (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) :
    (iterState p c answer target ξ 0).point = p.x0 := by
  have hh := (Prod.mk.inj (reset_path_point_alive p c answer target ξ 0 (by omega) (by simp))).1
  simpa only [path, resetTime, Nat.zero_mul, Nat.zero_div, Nat.zero_add,
    HeavyTailedProductProcess.trajectory] using hh

lemma iter_alive_point_succ (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (t : ℕ) (ht : t < c.steps) :
    let X := iterState p c answer target ξ
    (X (t + 1)).alive = true → (X (t + 1)).point = (X t).point + displacement p c (X t) := by
  intro X ha
  let post := HeavyTailedProductProcess.trajectory
    (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
    (cycleCalls c) (X t) (fun k => ξ (transportTime c t + k))
  have hh : ((X (t + 1)).point, (X (t + 1)).alive) = (post.point, post.alive) := by
    simpa only [X, iterState, path, post, HeavyTailedSospEpochIntegration.trajectory_add] using
      transport_next_point_alive p c answer target ξ t ht
  have hp := Prod.mk.inj hh
  have hpa : post.alive = true := hp.2.symm.trans ha
  exact hp.1.trans (fresh_cycle_alive_point p c (X t) answer
    (fun k => ξ (transportTime c t + k)) (transport_shape p c answer target ξ t ht.le).2 hpa)

noncomputable def trialAlive (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (n : ℕ) : Bool :=
  if n ≤ c.steps then (iterState p c answer target ξ n).alive else false

noncomputable def trialProposal (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (n : ℕ) : Space p :=
  let s := iterState p c answer target ξ n
  s.point + displacement p c s

noncomputable def stoppedPoint (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (n : ℕ) : Space p :=
  shadowPoint p.x0 (trialAlive p c answer target ξ) (trialProposal p c answer target ξ) n

lemma trialAlive_previous (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    trialAlive p c answer target ξ (n + 1) = true → trialAlive p c answer target ξ n = true := by
  by_cases hn : n + 1 ≤ c.steps
  · simp only [trialAlive, hn, show n ≤ c.steps by omega, ↓reduceIte]
    exact iter_alive_mono p c answer target ξ (by omega : n ≤ n + 1)
  · simp [trialAlive, hn]

lemma stoppedPoint_live (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    trialAlive p c answer target ξ n = true →
      stoppedPoint p c answer target ξ n = (iterState p c answer target ξ n).point := by
  apply shadowPoint_live p.x0 (trialAlive p c answer target ξ)
    (fun j => (iterState p c answer target ξ j).point) (trialProposal p c answer target ξ)
    (iter_point_zero p c answer target ξ) (trialAlive_previous p c answer target ξ)
  intro j hj
  by_cases hjb : j + 1 ≤ c.steps
  · simp only [trialAlive, hjb, ↓reduceIte] at hj
    exact iter_alive_point_succ p c answer target ξ j (by omega) hj
  · simp [trialAlive, hjb] at hj

lemma stopped_descent (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hη : 0 ≤ c.η)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.η ≤ 1 / 4)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (N : ℕ) :
    let X := iterState p c answer target ξ
    let A := trialAlive p c answer target ξ
    c.η * (∑ n ∈ Finset.range N, if A n then ‖g (X n).point‖ / 2 else 0) ≤
      f p.x0 - f (stoppedPoint p c answer target ξ N) +
        2 * c.η * (∑ n ∈ Finset.range N, if A n then ‖(X n).estimate - g (X n).point‖ else 0) +
        N * (p.L0 * c.η ^ 2) := by
  intro X A
  apply shadow_descent_sum f p.x0 A (fun n => (X n).point)
    (trialProposal p c answer target ξ) (fun n => ‖g (X n).point‖ / 2)
    (fun n => ‖(X n).estimate - g (X n).point‖) (by positivity)
    (stoppedPoint_live p c answer target ξ)
  intro n _
  have hh := GuardedGeneralizedGeometry.normalized_descent hL0 hL1 hη hf hg hH hsmall
    (X n).point (X n).estimate
  rw [norm_sub_rev] at hh
  simpa only [trialProposal, displacement, sub_eq_add_neg, mul_div_assoc] using hh

lemma shadowPoint_norm_bound_alive {E : Type*} [SeminormedAddCommGroup E]
    (x0 : E) (alive : ℕ → Bool) (proposal : ℕ → E) {R : ℝ}
    (h0 : ‖x0‖ ≤ R) (hp : ∀ n, alive n = true → ‖proposal n‖ ≤ R) (n : ℕ) :
    ‖shadowPoint x0 alive proposal n‖ ≤ R := by
  induction n with
  | zero => exact h0
  | succ n ih =>
      dsimp only [shadowPoint]
      split_ifs with hn
      · exact hp n hn
      · exact ih

lemma stoppedPoint_bound (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (hη : 0 ≤ c.η)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (N : ℕ) :
    ‖stoppedPoint p c answer target ξ N‖ ≤ ‖p.x0‖ + (transportTime c c.steps + 1) * c.η := by
  apply shadowPoint_norm_bound_alive p.x0 (trialAlive p c answer target ξ)
    (trialProposal p c answer target ξ) (le_add_of_nonneg_right (by positivity))
  intro n hn
  have hns : n ≤ c.steps := by
    by_contra hh
    simp [trialAlive, hh] at hn
  have hp := GuardedHessianIntegration.trajectory_point_bound p c hη answer
    (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) ξ le_rfl le_rfl (transportTime c n)
  have hd := GuardedHessianIntegration.displacement_norm_le p c hη
    (iterState p c answer target ξ n)
  have htime := (transportTime_strictMono c).monotone hns
  have htR : (transportTime c n : ℝ) ≤ transportTime c c.steps := by exact_mod_cast htime
  have hnorm := norm_add_le (iterState p c answer target ξ n).point
    (displacement p c (iterState p c answer target ξ n))
  change ‖(iterState p c answer target ξ n).point‖ ≤ _ at hp
  change ‖(iterState p c answer target ξ n).point +
    displacement p c (iterState p c answer target ξ n)‖ ≤ _
  nlinarith [mul_le_mul_of_nonneg_right htR hη]

lemma stoppedPoint_measurable (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (target : Fin (c.steps + 1)) (N : ℕ) :
    Measurable (fun ξ : ℕ → ℝ × Ω => stoppedPoint p c answer target ξ N) := by
  have hX (j : ℕ) : Measurable (fun ξ : ℕ → ℝ × Ω => iterState p c answer target ξ j) :=
    (HeavyTailedProductProcess.trajectory_measurable hstep (transportTime c j)).comp
      (measurable_const.prodMk measurable_id)
  apply shadowPoint_measurable
  · intro j
    by_cases hj : j ≤ c.steps
    · simpa only [trialAlive, hj, ↓reduceIte, Function.comp_def] using
        (GuardedHessianMeasurable.measurable_alive p c).comp (hX j)
    · simpa only [trialAlive, hj, ↓reduceIte, Function.comp_def] using
        (measurable_const : Measurable (fun _ : ℕ → ℝ × Ω => false))
  · intro j
    exact ((GuardedHessianMeasurable.measurable_point p c).comp (hX j)).add
      ((GuardedHessianMeasurable.measurable_displacement p c).comp (hX j))

lemma stopped_continuous_integrable (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℕ → ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p) (hη : 0 ≤ c.η)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (target : Fin (c.steps + 1)) (f : Space p → ℝ) (hf : Continuous f) (N : ℕ) :
    Integrable (fun ξ : ℕ → ℝ × Ω => f (stoppedPoint p c answer target ξ N)) Q := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Space p)
    (‖p.x0‖ + (transportTime c c.steps + 1) * c.η)).exists_bound_of_continuousOn hf.continuousOn
  apply (integrable_const C).mono'
    (hf.measurable.comp (stoppedPoint_measurable p c answer hstep target N)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ξ
  apply hC
  simpa only [Metric.mem_closedBall, dist_zero_right] using stoppedPoint_bound p c answer hη target ξ N

lemma trial_alive_integrable (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℕ → ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p) (hη : 0 ≤ c.η)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (target : Fin (c.steps + 1)) (f : Space p → ℝ) (hf : Continuous f) (n : ℕ) :
    Integrable (fun ξ : ℕ → ℝ × Ω => if trialAlive p c answer target ξ n then
      f (iterState p c answer target ξ n).point else 0) Q := by
  by_cases hn : n ≤ c.steps
  · simpa only [trialAlive, hn, ↓reduceIte, iterState, path] using
      GuardedHessianIntegration.trajectory_alive_integrable p c hη Q answer hstep
        (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c)
        le_rfl le_rfl f hf (transportTime c n)
  · simp [trialAlive, hn]

lemma expected_stopped_descent (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℕ → ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hη : 0 ≤ c.η)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.η ≤ 1 / 4)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (target : Fin (c.steps + 1)) {δ : ℝ} (N : ℕ) (hN : N ≤ c.steps + 1)
    (hEi : ∀ n ≤ c.steps, Integrable (fun ξ : ℕ → ℝ × Ω =>
      if (iterState p c answer target ξ n).alive then
        ‖(iterState p c answer target ξ n).estimate - g (iterState p c answer target ξ n).point‖ else 0) Q)
    (hEb : ∀ n ≤ c.steps, (∫ ξ : ℕ → ℝ × Ω,
      if (iterState p c answer target ξ n).alive then
        ‖(iterState p c answer target ξ n).estimate - g (iterState p c answer target ξ n).point‖ else 0 ∂Q) ≤ δ) :
    (∫ ξ : ℕ → ℝ × Ω, f (stoppedPoint p c answer target ξ N) ∂Q) +
      c.η * (∑ n ∈ Finset.range N, ∫ ξ : ℕ → ℝ × Ω,
        if trialAlive p c answer target ξ n then ‖g (iterState p c answer target ξ n).point‖ / 2 else 0 ∂Q) ≤
      f p.x0 + 2 * c.η * N * δ + N * (p.L0 * c.η ^ 2) := by
  let X := fun n (ξ : ℕ → ℝ × Ω) => iterState p c answer target ξ n
  let G := fun n ξ => if trialAlive p c answer target ξ n then ‖g (X n ξ).point‖ / 2 else 0
  let E := fun n ξ => if trialAlive p c answer target ξ n then ‖(X n ξ).estimate - g (X n ξ).point‖ else 0
  have hGi (n : ℕ) : Integrable (G n) Q := trial_alive_integrable p c Q answer hη hstep target
    (fun x => ‖g x‖ / 2) (hg.continuous.norm.div_const 2) n
  have hEin (n : ℕ) (hn : n ∈ Finset.range N) : Integrable (E n) Q := by
    have hns : n ≤ c.steps := by have := Finset.mem_range.mp hn; omega
    simpa only [E, X, trialAlive, hns, ↓reduceIte] using hEi n hns
  have hEsum : Integrable (fun ξ => ∑ n ∈ Finset.range N, E n ξ) Q :=
    integrable_finsetSum _ hEin
  have hGsum : Integrable (fun ξ => ∑ n ∈ Finset.range N, G n ξ) Q :=
    integrable_finsetSum _ (fun n _ => hGi n)
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).differentiableAt.continuousAt)
  have hFi := stopped_continuous_integrable p c Q answer hη hstep target f hfc N
  have hleft := hFi.add (hGsum.const_mul c.η)
  have hright := ((integrable_const (f p.x0)).add (hEsum.const_mul (2 * c.η))).add
    (integrable_const ((N : ℝ) * (p.L0 * c.η ^ 2)))
  have hpath (ξ : ℕ → ℝ × Ω) : f (stoppedPoint p c answer target ξ N) +
      c.η * (∑ n ∈ Finset.range N, G n ξ) ≤
      f p.x0 + 2 * c.η * (∑ n ∈ Finset.range N, E n ξ) + N * (p.L0 * c.η ^ 2) := by
    have hh := stopped_descent p c answer f g hL0 hL1 hη hf hg hH hsmall target ξ N
    change c.η * (∑ n ∈ Finset.range N, G n ξ) ≤
      f p.x0 - f (stoppedPoint p c answer target ξ N) +
        2 * c.η * (∑ n ∈ Finset.range N, E n ξ) + N * (p.L0 * c.η ^ 2) at hh
    linarith
  have hAi : Integrable (fun ξ : ℕ → ℝ × Ω =>
      f p.x0 + 2 * c.η * (∑ n ∈ Finset.range N, E n ξ)) Q :=
    (integrable_const _).add (hEsum.const_mul _)
  have hh := integral_mono hleft hright hpath
  simp only [Pi.add_apply] at hh
  rw [integral_add hFi (hGsum.const_mul _), integral_const_mul,
    integral_add hAi (integrable_const _),
    integral_add (integrable_const _) (hEsum.const_mul _), integral_const_mul,
    integral_const, integral_const, probReal_univ, one_smul, one_smul,
    integral_finsetSum _ (fun n _ => hGi n), integral_finsetSum _ hEin] at hh
  have hsum : (∑ n ∈ Finset.range N, ∫ ξ, E n ξ ∂Q) ≤ N * δ := by
    calc
      _ ≤ ∑ _n ∈ Finset.range N, δ := Finset.sum_le_sum (fun n hn => by
        have hns : n ≤ c.steps := by have := Finset.mem_range.mp hn; omega
        simpa only [E, X, trialAlive, hns, ↓reduceIte] using hEb n hns)
      _ = _ := by simp
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * c.η by positivity)])

lemma expected_gap_and_gradient (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℕ → ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hη : 0 ≤ c.η)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.η ≤ 1 / 4)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (target : Fin (c.steps + 1)) {δ : ℝ} (N : ℕ) (hN : N ≤ c.steps + 1)
    (hEi : ∀ n ≤ c.steps, Integrable (fun ξ : ℕ → ℝ × Ω =>
      if (iterState p c answer target ξ n).alive then
        ‖(iterState p c answer target ξ n).estimate - g (iterState p c answer target ξ n).point‖ else 0) Q)
    (hEb : ∀ n ≤ c.steps, (∫ ξ : ℕ → ℝ × Ω,
      if (iterState p c answer target ξ n).alive then
        ‖(iterState p c answer target ξ n).estimate - g (iterState p c answer target ξ n).point‖ else 0 ∂Q) ≤ δ) {m : ℝ} (hm : ∀ x, m ≤ f x) (hgap : f p.x0 - m ≤ p.Δ) :
    let D := p.Δ + 2 * c.η * N * δ + N * (p.L0 * c.η ^ 2)
    (∫ ξ, f (stoppedPoint p c answer target ξ N) - m ∂Q) ≤ D ∧
      c.η * (∑ n ∈ Finset.range N, ∫ ξ : ℕ → ℝ × Ω,
        if trialAlive p c answer target ξ n then ‖g (iterState p c answer target ξ n).point‖ / 2 else 0 ∂Q) ≤ D := by
  have hd := expected_stopped_descent p c Q answer f g hL0 hL1 hη hf hg hH hsmall
    hstep target N hN hEi hEb
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).differentiableAt.continuousAt)
  have hi := stopped_continuous_integrable p c Q answer hη hstep target f hfc N
  have he : (∫ ξ, f (stoppedPoint p c answer target ξ N) - m ∂Q) =
      (∫ ξ, f (stoppedPoint p c answer target ξ N) ∂Q) - m := by
    rw [integral_sub hi (integrable_const m)]
    simp
  have hG : 0 ≤ ∑ n ∈ Finset.range N, ∫ ξ : ℕ → ℝ × Ω,
      if trialAlive p c answer target ξ n then ‖g (iterState p c answer target ξ n).point‖ / 2 else 0 ∂Q := by
    apply Finset.sum_nonneg
    intro n _
    apply integral_nonneg
    intro ξ
    dsimp only
    split_ifs <;> positivity
  have hD : 0 ≤ ∫ ξ, f (stoppedPoint p c answer target ξ N) - m ∂Q :=
    integral_nonneg (fun ξ => sub_nonneg.mpr (hm _))
  dsimp only
  rw [he] at hD ⊢
  constructor <;> nlinarith [mul_nonneg hη hG]

lemma shadowPoint_freeze {E : Type*} (x0 : E) (alive : ℕ → Bool) (proposal : ℕ → E)
    (n N : ℕ) (hnN : n ≤ N) (hdead : ∀ j, n ≤ j → alive j = false) :
    shadowPoint x0 alive proposal N = shadowPoint x0 alive proposal n := by
  induction N, hnN using Nat.le_induction with
  | base => rfl
  | succ N hn ih => simp only [shadowPoint, hdead N hn, Bool.false_eq_true, ↓reduceIte, ih]

lemma trialAlive_after_reject (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (t j : ℕ) (htj : t < j)
    (hdead : (path p c answer target ξ (transportTime c t + cycleCalls c)).alive = false) :
    trialAlive p c answer target ξ j = false := by
  by_cases hj : j ≤ c.steps
  · have htime : transportTime c t + cycleCalls c ≤ transportTime c j := by
      have hh := (transportTime_strictMono c).monotone (show t + 1 ≤ j by omega)
      rw [transportTime_succ] at hh
      omega
    have hh := path_alive_mono p c answer target ξ htime
    have hfalse : (iterState p c answer target ξ j).alive = false := by
      cases ha : (iterState p c answer target ξ j).alive
      · rfl
      · have htrue := hh ha
        rw [hdead] at htrue
        contradiction
    simp only [trialAlive, hj, ↓reduceIte, hfalse]
  · simp [trialAlive, hj]

lemma stoppedPoint_rejected_proposal (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (t N : ℕ) (ht : t ≤ c.steps)
    (htN : t < N) (halive : (iterState p c answer target ξ t).alive = true)
    (hdead : (path p c answer target ξ (transportTime c t + cycleCalls c)).alive = false) :
    stoppedPoint p c answer target ξ N = trialProposal p c answer target ξ t := by
  have hfreeze := shadowPoint_freeze p.x0 (trialAlive p c answer target ξ)
    (trialProposal p c answer target ξ) (t + 1) N (by omega)
    (fun j hj => trialAlive_after_reject p c answer target ξ t j (by omega) hdead)
  change shadowPoint _ _ _ N = _
  rw [hfreeze, shadowPoint]
  simp only [trialAlive, ht, ↓reduceIte, halive]

lemma proposal_path_alive_point (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (t : ℕ) (ht : t ≤ c.steps) :
    (path p c answer target ξ (transportTime c t + 1)).alive =
      (iterState p c answer target ξ t).alive ∧
    ((iterState p c answer target ξ t).alive = true →
      (path p c answer target ξ (transportTime c t + 1)).point =
        trialProposal p c answer target ξ t) := by
  have hs := (transport_shape p c answer target ξ t ht).2
  change (HeavyTailedProductProcess.trajectory _ _ _ _ : State p c).alive = _ ∧ _
  rw [HeavyTailedProductProcess.trajectory_succ_last, update, hs]
  constructor
  · rfl
  · intro ha
    unfold path
    rw [HeavyTailedProductProcess.trajectory_succ_last, update, hs]
    change (if (iterState p c answer target ξ t).alive then _ else _) = _
    simp only [ha, ↓reduceIte]
    rfl

lemma final_death_has_rejection (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω)
    (hdead : (path p c answer target ξ (trialCalls c)).alive = false) :
    ∃ t, t ≤ c.steps ∧ (iterState p c answer target ξ t).alive = true ∧
      (path p c answer target ξ (transportTime c t + cycleCalls c)).alive = false := by
  by_contra hn
  have hkeep (t : ℕ) (ht : t ≤ c.steps)
      (ha : (iterState p c answer target ξ t).alive = true) :
      (path p c answer target ξ (transportTime c t + cycleCalls c)).alive = true := by
    cases hh : (path p c answer target ξ (transportTime c t + cycleCalls c)).alive
    · exact (hn ⟨t, ht, ha, hh⟩).elim
    · rfl
  have ha : ∀ t, t ≤ c.steps → (iterState p c answer target ξ t).alive = true := by
    intro t
    induction t with
    | zero =>
        intro _
        have hh := (Prod.mk.inj (reset_path_point_alive p c answer target ξ 0 (by omega) (by simp))).2
        simpa only [path, resetTime, Nat.zero_mul, Nat.zero_div, Nat.zero_add,
          HeavyTailedProductProcess.trajectory] using hh
    | succ t ih =>
        intro ht
        have hh := (Prod.mk.inj (transport_next_point_alive p c answer target ξ t (by omega))).2
        exact hh.trans (hkeep t (by omega) (ih (by omega)))
  have hh := hkeep c.steps le_rfl (ha c.steps le_rfl)
  rw [transportTime_final, hdead] at hh
  contradiction

lemma false_rejection_union {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (A : ℕ → Set Ω) (T : ℕ) (δ : ℝ)
    (hA : ∀ t, t < T → Q.real (A t) ≤ δ) :
    Q.real {ξ | ∃ t, t < T ∧ ξ ∈ A t} ≤ T * δ := by
  have he : {ξ | ∃ t, t < T ∧ ξ ∈ A t} = ⋃ t ∈ Finset.range T, A t := by
    ext ξ
    simp
  rw [he]
  calc
    _ ≤ ∑ t ∈ Finset.range T, Q.real (A t) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ Finset.range T, δ := Finset.sum_le_sum (fun t ht => hA t (Finset.mem_range.mp ht))
    _ = _ := by simp

lemma abort_probability_split (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℕ → ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (target : Fin (c.steps + 1)) (M δ D : ℝ)
    (hfalse : ∀ t, t ≤ c.steps → Q.real
      {ξ | (path p c answer target ξ (transportTime c t + 1)).alive = true ∧
        ‖g (path p c answer target ξ (transportTime c t + 1)).point‖ ≤ M ∧
        (path p c answer target ξ (transportTime c t + cycleCalls c)).alive = false} ≤ δ)
    (htrue : Q.real {ξ | ∃ t, t < c.steps + 1 ∧ t ≤ c.steps ∧
      (iterState p c answer target ξ t).alive = true ∧
      (path p c answer target ξ (transportTime c t + cycleCalls c)).alive = false ∧
      M < ‖g (trialProposal p c answer target ξ t)‖} ≤ D) :
    Q.real {ξ | (path p c answer target ξ (trialCalls c)).alive = false} ≤
      (c.steps + 1 : ℕ) * δ + D := by
  let A := fun t => {ξ | (path p c answer target ξ (transportTime c t + 1)).alive = true ∧
    ‖g (path p c answer target ξ (transportTime c t + 1)).point‖ ≤ M ∧
    (path p c answer target ξ (transportTime c t + cycleCalls c)).alive = false}
  let B := {ξ | ∃ t, t < c.steps + 1 ∧ t ≤ c.steps ∧
    (iterState p c answer target ξ t).alive = true ∧
    (path p c answer target ξ (transportTime c t + cycleCalls c)).alive = false ∧
    M < ‖g (trialProposal p c answer target ξ t)‖}
  have hsub : {ξ | (path p c answer target ξ (trialCalls c)).alive = false} ⊆
      {ξ | ∃ t, t < c.steps + 1 ∧ ξ ∈ A t} ∪ B := by
    intro ξ hd
    obtain ⟨t, ht, ha, hr⟩ := final_death_has_rejection p c answer target ξ hd
    by_cases hG : ‖g (trialProposal p c answer target ξ t)‖ ≤ M
    · left
      refine ⟨t, by omega, ?_⟩
      have hh := proposal_path_alive_point p c answer target ξ t ht
      refine ⟨hh.1.trans ha, ?_, hr⟩
      rw [hh.2 ha]
      exact hG
    · right
      exact ⟨t, by omega, ht, ha, hr, lt_of_not_ge hG⟩
  have hF := false_rejection_union Q A (c.steps + 1) δ (fun t ht => hfalse t (by omega))
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add hF htrue))

lemma true_rejection_probability (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℕ → ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p) {m M : ℝ}
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hη : 0 ≤ c.η) (hM : 0 < M)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖) (hm : ∀ x, m ≤ f x)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (target : Fin (c.steps + 1)) (N : ℕ) :
    Q.real {ξ | ∃ t, t < N ∧ t ≤ c.steps ∧
      (iterState p c answer target ξ t).alive = true ∧
      (path p c answer target ξ (transportTime c t + cycleCalls c)).alive = false ∧
      M < ‖g (trialProposal p c answer target ξ t)‖} ≤
      8 * (p.L0 + p.L1 * M) *
        (∫ ξ, f (stoppedPoint p c answer target ξ N) - m ∂Q) / M ^ 2 := by
  let D := fun ξ : ℕ → ℝ × Ω => f (stoppedPoint p c answer target ξ N) - m
  let W := fun ξ => 8 * (p.L0 + p.L1 * M) * D ξ
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).differentiableAt.continuousAt)
  have hDi : Integrable D Q := (stopped_continuous_integrable p c Q answer hη hstep target f hfc N).sub
    (integrable_const m)
  have hD0 (ξ : ℕ → ℝ × Ω) : 0 ≤ D ξ := sub_nonneg.mpr (hm _)
  have hW0 (ξ : ℕ → ℝ × Ω) : 0 ≤ W ξ :=
    mul_nonneg (by positivity) (hD0 ξ)
  have hWi : Integrable W Q := hDi.const_mul _
  have hsub : {ξ | ∃ t, t < N ∧ t ≤ c.steps ∧
      (iterState p c answer target ξ t).alive = true ∧
      (path p c answer target ξ (transportTime c t + cycleCalls c)).alive = false ∧
      M < ‖g (trialProposal p c answer target ξ t)‖} ⊆ {ξ | M ^ 2 ≤ W ξ} := by
    rintro ξ ⟨t, htN, ht, ha, hd, hgrad⟩
    have heq := stoppedPoint_rejected_proposal p c answer target ξ t N ht htN ha hd
    have hMG : M ≤ ‖g (stoppedPoint p c answer target ξ N)‖ := by rw [heq]; exact hgrad.le
    exact GuardedGeneralizedGeometry.threshold_gap hM hMG hL0 (hD0 ξ)
      (GuardedGeneralizedGeometry.gradient_gap_exact hL0 hL1 hf hg hH hm _)
  have hprob := measureReal_mono (μ := Q) hsub
  have hmark := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hW0) hWi (M ^ 2)
  apply (le_div_iff₀ (sq_pos_of_pos hM)).mpr
  have hh := mul_le_mul_of_nonneg_left hprob (sq_nonneg M)
  have he : (∫ ξ, W ξ ∂Q) = 8 * (p.L0 + p.L1 * M) * (∫ ξ, D ξ ∂Q) := integral_const_mul _ _
  rw [he] at hmark
  nlinarith

end LongTails.Proofs.GuardedHessianDescent
