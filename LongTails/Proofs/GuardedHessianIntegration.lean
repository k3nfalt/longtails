import LongTails.Proofs.GuardedGradientMoments
import LongTails.Proofs.GuardedHessianExecution
import LongTails.Proofs.GuardedHessianMeasurable
import LongTails.Proofs.GuardedGeneralizedGeometry

open MeasureTheory
open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.GuardedHessianTransport

namespace LongTails.Proofs.GuardedHessianIntegration

lemma fresh_continuation_probability {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (advance : S → Ω → S)
    (ha : Measurable (Function.uncurry advance)) (n : ℕ) (s : S)
    (A : Set (S × (ℕ → Ω))) (hA : MeasurableSet A) (δ : ℝ)
    (hb : ∀ η : Fin n → Ω,
      (Measure.infinitePi fun _ : ℕ => P).real
        {ξ | (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance n s η, ξ) ∈ A} ≤ δ) :
    (Measure.infinitePi fun _ : ℕ => P).real
      {ξ | (HeavyTailedProductProcess.trajectory advance n s ξ, fun k => ξ (n + k)) ∈ A} ≤ δ := by
  classical
  let F : S × (ℕ → Ω) → ℝ := A.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hA
  have hnon : ∀ w, 0 ≤ F w := by intro w; simp only [F, Set.indicator_apply]; split_ifs <;> norm_num
  have hsection (z : S) : MeasurableSet {ξ : ℕ → Ω | (z, ξ) ∈ A} :=
    hA.preimage (measurable_const.prodMk measurable_id)
  have heq (z : S) : (fun ξ => F (z, ξ)) =
      {ξ : ℕ → Ω | (z, ξ) ∈ A}.indicator (fun _ => (1 : ℝ)) := rfl
  have hh := HeavyTailedSospEpochIntegration.fresh_continuation_bound P advance ha n s F hF hnon
    (fun _ => δ) (integrable_const δ)
    (fun η => by rw [heq]; exact (integrable_const (1 : ℝ)).indicator (hsection _))
    (fun η => by rw [heq, integral_indicator_const 1 (hsection _), smul_eq_mul, mul_one]; exact hb η)
  have hm : Measurable (fun ξ : ℕ → Ω =>
      (HeavyTailedProductProcess.trajectory advance n s ξ, fun k => ξ (n + k))) :=
    ((HeavyTailedProductProcess.trajectory_measurable ha n).comp
      (measurable_const.prodMk measurable_id)).prodMk (by fun_prop)
  have ht : MeasurableSet {ξ : ℕ → Ω |
      (HeavyTailedProductProcess.trajectory advance n s ξ, fun k => ξ (n + k)) ∈ A} := hA.preimage hm
  have hid : (fun ξ => F (HeavyTailedProductProcess.trajectory advance n s ξ,
      fun k => ξ (n + k))) =
      {ξ | (HeavyTailedProductProcess.trajectory advance n s ξ, fun k => ξ (n + k)) ∈ A}.indicator
        (fun _ => (1 : ℝ)) := rfl
  have hh2 := hh.2
  rw [hid, integral_indicator_const (1 : ℝ) ht] at hh2
  simpa using hh2

lemma fresh_guard_second_moment (p : Params) (c : Config) (s : State p c)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Q : Measure (ℕ → Ω)) [IsProbabilityMeasure Q]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) P Q)
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (tape : ℕ → Ω → ℝ) {M G : ℝ}
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    (hM : 0 < M) (hthreshold : c.threshold = 3 * M / 2)
    (hm : Measurable (answer (s.point, none)))
    (hi : Integrable (answer (s.point, none)) P)
    (hmean : (∫ ω, answer (s.point, none) ω ∂P) = g s.point)
    (hpi : Integrable (fun ω => ‖answer (s.point, none) ω - g s.point‖ ^ p.p) P)
    (hb : (∫ ω, ‖answer (s.point, none) ω - g s.point‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g s.point‖ ^ p.p)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.guardBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (hgroups : (1 / 2 : ℝ) ^ (c.groups + 1) ≤ 1 / 16)
    (hG : 0 ≤ G) (hgrowth : ‖g s.point‖ ≤ 2 * max G M) :
    let result := fun ξ : ℕ → Ω => HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      ((c.groups + 1) * (c.guardBatch + 1))
      { s with phase := .guard 0 0 0 (fun _ => 0) } (fun k => (tape k (ξ k), ξ k))
    Integrable (fun ξ => if (result ξ).alive then ‖g (result ξ).point‖ ^ 2 else 0) Q ∧
      (∫ ξ, if (result ξ).alive then ‖g (result ξ).point‖ ^ 2 else 0 ∂Q) ≤
        if s.alive then G ^ 2 / 2 + 4 * M ^ 2 else 0 := by
  let result := fun ξ : ℕ → Ω => HeavyTailedProductProcess.trajectory
    (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
    ((c.groups + 1) * (c.guardBatch + 1))
    { s with phase := .guard 0 0 0 (fun _ => 0) } (fun k => (tape k (ξ k), ξ k))
  let accepted := fun ξ : ℕ → Ω =>
    ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
      (fun j : Fin (c.groups + 1) => ((c.guardBatch + 1 : ℕ) : ℝ)⁻¹ •
        ∑ k ∈ Finset.range (c.guardBatch + 1),
          answer (s.point, none) (ξ (j.val * (c.guardBatch + 1) + k)))‖ ≤ 3 * M / 2
  have heq : (fun ξ => if (result ξ).alive then ‖g (result ξ).point‖ ^ 2 else 0) =
      (fun ξ => if s.alive then if accepted ξ then ‖g s.point‖ ^ 2 else 0 else 0) := by
    funext ξ
    have hh := GuardedHessianExecution.fresh_guard_pass_killed_gradient p c s answer g
      (fun k => (tape k (ξ k), ξ k))
    change (if (result ξ).alive then ‖g (result ξ).point‖ ^ 2 else 0) = _ at hh
    rw [hh]
    cases s.alive <;> simp [hthreshold, accepted]
  change Integrable (fun ξ => if (result ξ).alive then ‖g (result ξ).point‖ ^ 2 else 0) Q ∧ _
  rw [heq]
  cases s.alive with
  | false => simp only [Bool.false_eq_true, ite_false, integral_zero]; exact ⟨integrable_zero _ _ _, le_rfl⟩
  | true =>
      simp only [ite_true]
      exact GuardedGradientMoments.stream_guard_second_moment Q hIID hm (g s.point)
        hp hp2 hσ hα hM hi hmean hpi hb (c.guardBatch + 1) (by omega) hsize
        c.groups hgroups hG hgrowth

lemma fresh_guard_false_alarm (p : Params) (c : Config) (s : State p c)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Q : Measure (ℕ → Ω)) [IsProbabilityMeasure Q]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) P Q)
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (tape : ℕ → Ω → ℝ) {M : ℝ}
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    (hM : 0 < M) (hthreshold : c.threshold = 3 * M / 2)
    (hm : Measurable (answer (s.point, none)))
    (hi : Integrable (answer (s.point, none)) P)
    (hmean : (∫ ω, answer (s.point, none) ω ∂P) = g s.point)
    (hpi : Integrable (fun ω => ‖answer (s.point, none) ω - g s.point‖ ^ p.p) P)
    (hb : (∫ ω, ‖answer (s.point, none) ω - g s.point‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g s.point‖ ^ p.p)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.guardBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (halive : s.alive = true) (hsmall : ‖g s.point‖ ≤ M) :
    let result := fun ξ : ℕ → Ω => HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      ((c.groups + 1) * (c.guardBatch + 1))
      { s with phase := .guard 0 0 0 (fun _ => 0) } (fun k => (tape k (ξ k), ξ k))
    Q {ξ | (result ξ).alive = false} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (c.groups + 1)) := by
  have he := GuardedGradientMoments.stream_medoid_failure Q hIID hm (g s.point)
    hp hp2 hσ hα hM hi hmean hpi hb (c.guardBatch + 1) (by omega) hsize c.groups
  have hh := (GuardedGradientMoments.guard_probability_bounds (g s.point) hM.le he).1 hsmall
  convert hh using 1
  congr 1
  ext ξ
  simp only [Set.mem_ofPred_eq]
  rw [GuardedHessianExecution.fresh_guard_pass, GuardedHessianExecution.guard_pass,
    GuardedHessianExecution.nextStep_alive]
  simp [halive, hthreshold]

lemma trajectory_duplicate_aux (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (n : ℕ) (s : State p c) (ξ : ℕ → ℝ × Ω) :
    HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × (ℝ × Ω)) => update p c s z.1 (answer (query p c s z.1) z.2.2))
      n s (fun k => ((ξ k).1, ξ k)) =
    HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ := by
  induction n generalizing s ξ with
  | zero => rfl
  | succ n ih =>
      simpa only [HeavyTailedProductProcess.trajectory] using
        ih (update p c s (ξ 0).1 (answer (query p c s (ξ 0).1) (ξ 0).2))
          (fun k => ξ (k + 1))

lemma combined_guard_second_moment (p : Params) (c : Config) (s : State p c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) {M G : ℝ}
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    (hM : 0 < M) (hthreshold : c.threshold = 3 * M / 2)
    (hm : Measurable (fun z : ℝ × Ω => answer (s.point, none) z.2))
    (hi : Integrable (fun z : ℝ × Ω => answer (s.point, none) z.2) P)
    (hmean : (∫ z, answer (s.point, none) z.2 ∂P) = g s.point)
    (hpi : Integrable (fun z : ℝ × Ω => ‖answer (s.point, none) z.2 - g s.point‖ ^ p.p) P)
    (hb : (∫ z, ‖answer (s.point, none) z.2 - g s.point‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g s.point‖ ^ p.p)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.guardBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (hgroups : (1 / 2 : ℝ) ^ (c.groups + 1) ≤ 1 / 16)
    (hG : 0 ≤ G) (hgrowth : ‖g s.point‖ ≤ 2 * max G M) :
    let result := fun ξ : ℕ → ℝ × Ω => HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      ((c.groups + 1) * (c.guardBatch + 1))
      { s with phase := .guard 0 0 0 (fun _ => 0) } ξ
    Integrable (fun ξ => if (result ξ).alive then ‖g (result ξ).point‖ ^ 2 else 0)
      (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, if (result ξ).alive then ‖g (result ξ).point‖ ^ 2 else 0
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
        if s.alive then G ^ 2 / 2 + 4 * M ^ 2 else 0 := by
  have hh := fresh_guard_second_moment p c s (Measure.infinitePi fun _ : ℕ => P)
    (OracleTemplate.StochasticGeneralized.infinitePi_iid P)
    (fun query (z : ℝ × Ω) => answer query z.2) g (fun _ z => z.1)
    hp hp2 hσ hα hM hthreshold hm hi hmean hpi hb hsize hgroups hG hgrowth
  simpa only [trajectory_duplicate_aux] using hh

lemma combined_guard_false_alarm (p : Params) (c : Config) (s : State p c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) {M : ℝ}
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    (hM : 0 < M) (hthreshold : c.threshold = 3 * M / 2)
    (hm : Measurable (fun z : ℝ × Ω => answer (s.point, none) z.2))
    (hi : Integrable (fun z : ℝ × Ω => answer (s.point, none) z.2) P)
    (hmean : (∫ z, answer (s.point, none) z.2 ∂P) = g s.point)
    (hpi : Integrable (fun z : ℝ × Ω => ‖answer (s.point, none) z.2 - g s.point‖ ^ p.p) P)
    (hb : (∫ z, ‖answer (s.point, none) z.2 - g s.point‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g s.point‖ ^ p.p)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.guardBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (halive : s.alive = true) (hsmall : ‖g s.point‖ ≤ M) :
    let result := fun ξ : ℕ → ℝ × Ω => HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      ((c.groups + 1) * (c.guardBatch + 1))
      { s with phase := .guard 0 0 0 (fun _ => 0) } ξ
    (Measure.infinitePi fun _ : ℕ => P) {ξ | (result ξ).alive = false} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (c.groups + 1)) := by
  have hh := fresh_guard_false_alarm p c s (Measure.infinitePi fun _ : ℕ => P)
    (OracleTemplate.StochasticGeneralized.infinitePi_iid P)
    (fun query (z : ℝ × Ω) => answer query z.2) g (fun _ z => z.1)
    hp hp2 hσ hα hM hthreshold hm hi hmean hpi hb hsize halive hsmall
  simpa only [trajectory_duplicate_aux] using hh

lemma prefix_guard_false_alarm (p : Params) (c : Config) (s : State p c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (hg : Measurable g) {M : ℝ}
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    (hM : 0 < M) (hthreshold : c.threshold = 3 * M / 2)
    (hm : ∀ x, Measurable (fun z : ℝ × Ω => answer (x, none) z.2))
    (hi : ∀ x, Integrable (fun z : ℝ × Ω => answer (x, none) z.2) P)
    (hmean : ∀ x, (∫ z, answer (x, none) z.2 ∂P) = g x)
    (hpi : ∀ x, Integrable (fun z : ℝ × Ω => ‖answer (x, none) z.2 - g x‖ ^ p.p) P)
    (hb : ∀ x, (∫ z, ‖answer (x, none) z.2 - g x‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.guardBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (n : ℕ)
    (hphase : ∀ ξ : ℕ → ℝ × Ω,
      (HeavyTailedProductProcess.trajectory
        (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ).phase =
        .guard 0 0 0 (fun _ => 0)) :
    let advance := fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)
    let X := fun ξ => HeavyTailedProductProcess.trajectory advance n s ξ
    let Y := fun ξ => HeavyTailedProductProcess.trajectory advance
      (n + (c.groups + 1) * (c.guardBatch + 1)) s ξ
    (Measure.infinitePi fun _ : ℕ => P).real
      {ξ | (X ξ).alive = true ∧ ‖g (X ξ).point‖ ≤ M ∧ (Y ξ).alive = false} ≤
        (1 / 2 : ℝ) ^ (c.groups + 1) := by
  classical
  let advance := fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)
  let N := (c.groups + 1) * (c.guardBatch + 1)
  let A : Set (State p c × (ℕ → ℝ × Ω)) :=
    {w | w.1.alive = true ∧ ‖g w.1.point‖ ≤ M ∧
      (HeavyTailedProductProcess.trajectory advance N w.1 w.2).alive = false}
  have htraj := HeavyTailedProductProcess.trajectory_measurable (step := advance) hstep N
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun ((GuardedHessianMeasurable.measurable_alive p c).comp measurable_fst)
      measurable_const).inter ((measurableSet_le
        ((hg.comp (GuardedHessianMeasurable.measurable_point p c)).comp measurable_fst).norm
        measurable_const).inter (measurableSet_eq_fun
          ((GuardedHessianMeasurable.measurable_alive p c).comp htraj) measurable_const))
  have hh := fresh_continuation_probability P advance hstep n s A hA
    ((1 / 2 : ℝ) ^ (c.groups + 1)) (fun η => ?_)
  · convert hh using 1
    congr 1
    ext ξ
    simp only [Set.mem_ofPred_eq, A]
    rw [HeavyTailedSospEpochIntegration.trajectory_add]
  have : Nonempty (ℝ × Ω) := nonempty_of_isProbabilityMeasure P
  let z := OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance n s η
  have hz : z.phase = .guard 0 0 0 (fun _ => 0) := by
    have he := HeavyTailedSospEpochIntegration.trajectory_finite advance n s
      (fun k => if hk : k < n then η ⟨k, hk⟩ else Classical.choice inferInstance)
    have hfun : (fun i : Fin n =>
        (if hk : (i : ℕ) < n then η ⟨i, hk⟩ else Classical.choice inferInstance)) = η := by
      funext i
      simp
    rw [hfun] at he
    change _ = z at he
    rw [← he]
    exact hphase _
  have he : { z with phase := .guard 0 0 0 (fun _ => 0) } = z := by
    generalize hez : z = r at *
    cases r
    simp_all
  by_cases ha : z.alive = true
  · by_cases hs : ‖g z.point‖ ≤ M
    · have hbnd := combined_guard_false_alarm p c z P answer g hp hp2 hσ hα hM hthreshold
        (hm _) (hi _) (hmean _) (hpi _) (hb _) hsize ha hs
      rw [he] at hbnd
      have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbnd
      simpa [A, z, ha, hs, measureReal_def, ENNReal.toReal_ofReal (by positivity :
        0 ≤ (1 / 2 : ℝ) ^ (c.groups + 1)), N, advance] using hr
    · simp [A, z, hs]
  · simp [A, z, ha]

lemma oracle_guard_false_alarm (p : Params) (c : Config)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (hg : Measurable g) {M : ℝ}
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    (hM : 0 < M) (hthreshold : c.threshold = 3 * M / 2)
    (hm : ∀ x, Measurable (fun z : ℝ × Ω => answer (x, none) z.2))
    (hi : ∀ x, Integrable (fun z : ℝ × Ω => answer (x, none) z.2) P)
    (hmean : ∀ x, (∫ z, answer (x, none) z.2 ∂P) = g x)
    (hpi : ∀ x, Integrable (fun z : ℝ × Ω => ‖answer (x, none) z.2 - g x‖ ^ p.p) P)
    (hb : ∀ x, (∫ z, ‖answer (x, none) z.2 - g x‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.guardBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (target : Fin (c.steps + 1)) (t : ℕ) (ht : t ≤ c.steps) :
    let advance := fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)
    let X := fun ξ n => HeavyTailedProductProcess.trajectory advance n
      (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) ξ
    (Measure.infinitePi fun _ : ℕ => P).real
      {ξ | (X ξ (GuardedHessianExecution.transportTime c t + 1)).alive = true ∧
        ‖g (X ξ (GuardedHessianExecution.transportTime c t + 1)).point‖ ≤ M ∧
        (X ξ (GuardedHessianExecution.transportTime c t + GuardedHessianExecution.cycleCalls c)).alive = false} ≤
      (1 / 2 : ℝ) ^ (c.groups + 1) := by
  let initial : State p c := ⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩
  have hh := prefix_guard_false_alarm p c initial P answer g hg hstep hp hp2 hσ hα hM hthreshold
    hm hi hmean hpi hb hsize (GuardedHessianExecution.transportTime c t + 1) (fun ξ => ?_)
  · simpa only [GuardedHessianExecution.cycleCalls, Nat.add_assoc] using hh
  rw [HeavyTailedProductProcess.trajectory_succ_last]
  have hs := (GuardedHessianExecution.transport_shape p c answer target ξ t ht).2
  rw [update, hs]

lemma fresh_cycle_second_moment (p : Params) (c : Config) (s : State p c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (hg : Measurable g) {M : ℝ}
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (hs : s.phase = .transport)
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    (hM : 0 < M) (hthreshold : c.threshold = 3 * M / 2)
    (hm : ∀ x, Measurable (fun z : ℝ × Ω => answer (x, none) z.2))
    (hi : ∀ x, Integrable (fun z : ℝ × Ω => answer (x, none) z.2) P)
    (hmean : ∀ x, (∫ z, answer (x, none) z.2 ∂P) = g x)
    (hpi : ∀ x, Integrable (fun z : ℝ × Ω => ‖answer (x, none) z.2 - g x‖ ^ p.p) P)
    (hb : ∀ x, (∫ z, ‖answer (x, none) z.2 - g x‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.guardBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (hgroups : (1 / 2 : ℝ) ^ (c.groups + 1) ≤ 1 / 16)
    (hgrowth : ∀ z : ℝ × Ω,
      ‖g (update p c s z.1 (answer (query p c s z.1) z.2)).point‖ ≤ 2 * max ‖g s.point‖ M) :
    let result := fun ξ : ℕ → ℝ × Ω => HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (GuardedHessianExecution.cycleCalls c) s ξ
    Integrable (fun ξ => if (result ξ).alive then ‖g (result ξ).point‖ ^ 2 else 0)
      (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, if (result ξ).alive then ‖g (result ξ).point‖ ^ 2 else 0
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
        if s.alive then ‖g s.point‖ ^ 2 / 2 + 4 * M ^ 2 else 0 := by
  let advance := fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)
  let N := (c.groups + 1) * (c.guardBatch + 1)
  let W := if s.alive then ‖g s.point‖ ^ 2 / 2 + 4 * M ^ 2 else 0
  let F := fun w : State p c × (ℕ → ℝ × Ω) =>
    let r := HeavyTailedProductProcess.trajectory advance N w.1 w.2
    if r.alive then ‖g r.point‖ ^ 2 else 0
  have htraj := HeavyTailedProductProcess.trajectory_measurable (step := advance) hstep N
  have hF : Measurable F := Measurable.ite
    (measurableSet_eq_fun ((GuardedHessianMeasurable.measurable_alive p c).comp htraj)
      measurable_const)
    ((hg.comp ((GuardedHessianMeasurable.measurable_point p c).comp htraj)).norm.pow_const 2)
    measurable_const
  have hguard (z : ℝ × Ω) : Integrable (fun ξ => F (advance s z, ξ))
      (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, F (advance s z, ξ) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ W := by
    have hphase : (advance s z).phase = .guard 0 0 0 (fun _ => 0) := by
      simp [advance, update, hs]
    have he : { advance s z with phase := .guard 0 0 0 (fun _ => 0) } = advance s z := by
      generalize heq : advance s z = r at *
      cases r
      simp_all
    have ha : (advance s z).alive = s.alive := by simp [advance, update, hs]
    have hh := combined_guard_second_moment p c (advance s z) P answer g hp hp2 hσ hα hM
      hthreshold (hm _) (hi _) (hmean _) (hpi _) (hb _) hsize hgroups
      (norm_nonneg (g s.point)) (hgrowth z)
    rw [he] at hh
    simpa only [ha] using hh
  let F' := fun w : (ℝ × Ω) × (ℕ → ℝ × Ω) => F (advance s w.1, w.2)
  have hFm : Measurable F' := hF.comp
    ((hstep.comp ((measurable_const (a := s)).prodMk measurable_fst)).prodMk measurable_snd)
  have hprod := WeakGradientConvolution.nonnegative_fiber_integral_bound
    (P := P) (Q := Measure.infinitePi fun _ : ℕ => P) hFm.stronglyMeasurable
    (fun w => by dsimp [F', F]; split_ifs <;> positivity)
    (Filter.Eventually.of_forall (fun z => (hguard z).1))
    (integrable_const W) (Filter.Eventually.of_forall (fun z => (hguard z).2))
  have hsplit := HeavyTailedProductProcess.head_tail_preserving P
  have heq : (fun ξ : ℕ → ℝ × Ω =>
      let r := HeavyTailedProductProcess.trajectory advance (GuardedHessianExecution.cycleCalls c) s ξ
      if r.alive then ‖g r.point‖ ^ 2 else 0) =
      F' ∘ (fun ξ : ℕ → ℝ × Ω => (ξ 0, fun k => ξ (k + 1))) := by
    funext ξ
    simp only [GuardedHessianExecution.cycleCalls, Nat.add_comm 1,
      HeavyTailedProductProcess.trajectory, Function.comp_apply, F', F, N]
  change Integrable _ _ ∧ _
  rw [heq]
  refine ⟨hsplit.integrable_comp_of_integrable hprod.1, ?_⟩
  simp only [Function.comp_def]
  have hem := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
    hsplit.measurable.aemeasurable hFm.aestronglyMeasurable
  rw [hsplit.map_eq] at hem
  rw [← hem]
  simpa only [integral_const, probReal_univ, one_smul] using hprod.2

lemma displacement_norm_le (p : Params) (c : Config) (hη : 0 ≤ c.η) (s : State p c) :
    ‖displacement p c s‖ ≤ c.η := by
  rw [displacement, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
  exact mul_le_of_le_one_right hη
    (LongTails.Proofs.MatrixPolarCharacterization.normalized_norm_le_one s.estimate)

lemma proposal_gradient_growth (p : Params) (c : Config) (hη : 0 ≤ c.η)
    (g : Space p → Space p) (hg : Differentiable ℝ g)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    {M : ℝ} (hsmall : p.L1 * c.η ≤ 1 / 4) (hbase : p.L0 * c.η ≤ M / 4)
    (h0 : ‖g p.x0‖ ≤ M) (s : State p c) (hs : s.phase = .transport)
    (u : ℝ) (reply : Space p) :
    ‖g (update p c s u reply).point‖ ≤ 2 * max ‖g s.point‖ M := by
  have he : (update p c s u reply).point =
      if s.alive then s.point + displacement p c s else p.x0 := by simp [update, hs]
  rw [he]
  split_ifs
  · apply GuardedGeneralizedGeometry.short_gradient_growth hL0 hL1 hg hH s.point
      (s.point + displacement p c s) _ hsmall hbase
    simpa only [add_sub_cancel_left] using displacement_norm_le p c hη s
  · have hM := le_max_right ‖g s.point‖ M
    have hn := (norm_nonneg (g s.point)).trans (le_max_left ‖g s.point‖ M)
    linarith

lemma update_point_bound (p : Params) (c : Config) (hη : 0 ≤ c.η)
    (s : State p c) (u : ℝ) (r : Space p) {R : ℝ}
    (h0 : ‖p.x0‖ ≤ R) (hs : ‖s.point‖ ≤ R) :
    ‖(update p c s u r).point‖ ≤ R + c.η := by
  have hx : ‖s.point + displacement p c s‖ ≤ R + c.η :=
    (norm_add_le _ _).trans (add_le_add hs (displacement_norm_le p c hη s))
  have hs' : ‖s.point‖ ≤ R + c.η := hs.trans (le_add_of_nonneg_right hη)
  have h0' : ‖p.x0‖ ≤ R + c.η := h0.trans (le_add_of_nonneg_right hη)
  cases hp : s.phase <;> simp only [update, hp]
  · split_ifs <;> exact hs'
  · split_ifs <;> assumption
  · split_ifs <;> first
      | exact hs'
      | rw [GuardedHessianExecution.nextStep_point]; dsimp only; assumption
  · exact hs'

lemma trajectory_point_bound (p : Params) (c : Config) (hη : 0 ≤ c.η) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) {R : ℝ} (h0 : ‖p.x0‖ ≤ R)
    (hs : ‖s.point‖ ≤ R) (n : ℕ) :
    ‖(HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ).point‖ ≤
        R + n * c.η := by
  induction n with
  | zero => simpa [HeavyTailedProductProcess.trajectory] using hs
  | succ n ih =>
      rw [HeavyTailedProductProcess.trajectory_succ_last]
      convert update_point_bound p c hη _ _ _
        (h0.trans (le_add_of_nonneg_right (by positivity : 0 ≤ (n : ℝ) * c.η))) ih using 1
      push_cast
      ring

lemma trajectory_continuous_integrable (p : Params) (c : Config) (hη : 0 ≤ c.η)
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure (ℕ → ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (s : State p c) {R : ℝ} (h0 : ‖p.x0‖ ≤ R) (hs : ‖s.point‖ ≤ R)
    (f : Space p → ℝ) (hf : Continuous f) (n : ℕ) :
    Integrable (fun ξ => f (HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ).point) Q := by
  let Y := fun ξ : ℕ → ℝ × Ω => (HeavyTailedProductProcess.trajectory
    (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ).point
  have hY : Measurable Y := (GuardedHessianMeasurable.measurable_point p c).comp
    ((HeavyTailedProductProcess.trajectory_measurable hstep n).comp
      (measurable_const.prodMk measurable_id))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Space p) (R + n * c.η)).exists_bound_of_continuousOn
    hf.continuousOn
  apply (integrable_const C).mono' (hf.measurable.comp hY).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ξ
  apply hC
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    trajectory_point_bound p c hη answer s ξ h0 hs n

lemma trajectory_alive_integrable (p : Params) (c : Config) (hη : 0 ≤ c.η)
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure (ℕ → ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (s : State p c) {R : ℝ} (h0 : ‖p.x0‖ ≤ R) (hs : ‖s.point‖ ≤ R)
    (f : Space p → ℝ) (hf : Continuous f) (n : ℕ) :
    let result := fun ξ : ℕ → ℝ × Ω => HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ
    Integrable (fun ξ => if (result ξ).alive then f (result ξ).point else 0) Q := by
  let result := fun ξ : ℕ → ℝ × Ω => HeavyTailedProductProcess.trajectory
    (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ
  have hr : Measurable result :=
    (HeavyTailedProductProcess.trajectory_measurable hstep n).comp
      (measurable_const.prodMk measurable_id)
  have hA : MeasurableSet {ξ | (result ξ).alive = true} := measurableSet_eq_fun
    ((GuardedHessianMeasurable.measurable_alive p c).comp hr) measurable_const
  have hi := (trajectory_continuous_integrable p c hη Q answer hstep s h0 hs f hf n).indicator hA
  have heq : ({ξ | (result ξ).alive = true}.indicator (fun ξ => f (result ξ).point)) =
      (fun ξ => if (result ξ).alive then f (result ξ).point else 0) := by
    funext ξ
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  change Integrable ({ξ | (result ξ).alive = true}.indicator (fun ξ => f (result ξ).point)) Q at hi
  rw [heq] at hi
  exact hi

lemma prefix_cycle_second_moment (p : Params) (c : Config) (hη : 0 ≤ c.η)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (hg : Continuous g) (M : ℝ)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (hlocal : ∀ s : State p c, s.phase = .transport →
      let result := fun ξ : ℕ → ℝ × Ω => HeavyTailedProductProcess.trajectory
        (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
        (GuardedHessianExecution.cycleCalls c) s ξ
      Integrable (fun ξ => if (result ξ).alive then ‖g (result ξ).point‖ ^ 2 else 0)
        (Measure.infinitePi fun _ : ℕ => P) ∧
        (∫ ξ, if (result ξ).alive then ‖g (result ξ).point‖ ^ 2 else 0
          ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
          if s.alive then ‖g s.point‖ ^ 2 / 2 + 4 * M ^ 2 else 0)
    (target : Fin (c.steps + 1)) (t : ℕ) (ht : t ≤ c.steps) :
    let X := fun n (ξ : ℕ → ℝ × Ω) => HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      n (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) ξ
    (∫ ξ, if (X (GuardedHessianExecution.transportTime c t + GuardedHessianExecution.cycleCalls c) ξ).alive
      then ‖g (X (GuardedHessianExecution.transportTime c t + GuardedHessianExecution.cycleCalls c) ξ).point‖ ^ 2
      else 0 ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      (∫ ξ, if (X (GuardedHessianExecution.transportTime c t) ξ).alive
        then ‖g (X (GuardedHessianExecution.transportTime c t) ξ).point‖ ^ 2 else 0
        ∂Measure.infinitePi (fun _ : ℕ => P)) / 2 + 4 * M ^ 2 := by
  let advance := fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2)
  let initial : State p c := ⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩
  let k := GuardedHessianExecution.transportTime c t
  let Y := fun η : Fin k → ℝ × Ω => OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
    advance k initial η
  let V := fun η : Fin k → ℝ × Ω => if (Y η).alive then ‖g (Y η).point‖ ^ 2 else 0
  have hY : Measurable Y := (OracleTemplate.GapStrongGrowth.iterateSamples_measurable
    (advance := advance) hstep k).comp (measurable_const.prodMk measurable_id)
  have hV : Measurable V := Measurable.ite
    (measurableSet_eq_fun ((GuardedHessianMeasurable.measurable_alive p c).comp hY) measurable_const)
    ((hg.measurable.comp ((GuardedHessianMeasurable.measurable_point p c).comp hY)).norm.pow_const 2)
    measurable_const
  have hpre := OracleTemplate.StochasticGeneralized.prefix_preserving P k
  have hfull := trajectory_alive_integrable p c hη (Measure.infinitePi fun _ : ℕ => P)
    answer hstep initial le_rfl le_rfl (fun x => ‖g x‖ ^ 2) (hg.norm.pow 2) k
  have hVi : Integrable V (Measure.pi fun _ : Fin k => P) :=
    (hpre.integrable_comp hV.aestronglyMeasurable).mp (by
      simpa only [Function.comp_def, V, Y, HeavyTailedSospEpochIntegration.trajectory_finite] using hfull)
  let F := fun w : State p c × (ℕ → ℝ × Ω) =>
    let r := HeavyTailedProductProcess.trajectory advance (GuardedHessianExecution.cycleCalls c) w.1 w.2
    if r.alive then ‖g r.point‖ ^ 2 else 0
  have htraj := HeavyTailedProductProcess.trajectory_measurable (step := advance) hstep
    (GuardedHessianExecution.cycleCalls c)
  have hF : Measurable F := Measurable.ite
    (measurableSet_eq_fun ((GuardedHessianMeasurable.measurable_alive p c).comp htraj) measurable_const)
    ((hg.measurable.comp ((GuardedHessianMeasurable.measurable_point p c).comp htraj)).norm.pow_const 2)
    measurable_const
  have hphase (η : Fin k → ℝ × Ω) : (Y η).phase = .transport := by
    have hk : 0 < k := by dsimp [k, GuardedHessianExecution.transportTime]; positivity
    obtain ⟨ξ, hξ⟩ := HeavyTailedSospEpochIntegration.finite_iterate_stream advance k hk initial η
    have hh := (GuardedHessianExecution.transport_shape p c answer target ξ t ht).2
    change (HeavyTailedProductProcess.trajectory advance k initial ξ).phase = _ at hh
    rw [← hξ] at hh
    exact hh
  have hb := HeavyTailedSospEpochIntegration.fresh_continuation_bound P advance hstep k initial
    F hF (fun w => by dsimp [F]; split_ifs <;> positivity)
    (fun η => V η / 2 + 4 * M ^ 2)
    ((hVi.div_const 2).add (integrable_const (4 * M ^ 2)))
    (fun η => (hlocal (Y η) (hphase η)).1)
    (fun η => (hlocal (Y η) (hphase η)).2.trans (by
      dsimp [V]
      split_ifs <;> nlinarith [sq_nonneg M]))
  have heint : (∫ η, V η ∂Measure.pi (fun _ : Fin k => P)) =
      ∫ ξ, V (fun i => ξ i) ∂Measure.infinitePi (fun _ : ℕ => P) := by
    rw [← hpre.map_eq, integral_map hpre.measurable.aemeasurable hV.aestronglyMeasurable]
  rw [integral_add (hVi.div_const 2) (integrable_const _), integral_div,
    integral_const, probReal_univ, one_smul, heint] at hb
  dsimp only
  simp_rw [HeavyTailedSospEpochIntegration.trajectory_add]
  simpa only [F, V, Y, HeavyTailedSospEpochIntegration.trajectory_finite] using hb.2

lemma uniform_alive_second_moment (p : Params) (c : Config) (hη : 0 ≤ c.η)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (hg : Continuous g) (M : ℝ)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (hlocal : ∀ s : State p c, s.phase = .transport →
      let result := fun ξ : ℕ → ℝ × Ω => HeavyTailedProductProcess.trajectory
        (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
        (GuardedHessianExecution.cycleCalls c) s ξ
      Integrable (fun ξ => if (result ξ).alive then ‖g (result ξ).point‖ ^ 2 else 0)
        (Measure.infinitePi fun _ : ℕ => P) ∧
        (∫ ξ, if (result ξ).alive then ‖g (result ξ).point‖ ^ 2 else 0
          ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
          if s.alive then ‖g s.point‖ ^ 2 / 2 + 4 * M ^ 2 else 0)

    (hinit : ‖g p.x0‖ ^ 2 ≤ 8 * M ^ 2)
    (target : Fin (c.steps + 1)) (t : ℕ) (ht : t ≤ c.steps) :
    let X := fun n (ξ : ℕ → ℝ × Ω) => HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      n (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) ξ
    (∫ ξ, if (X (GuardedHessianExecution.transportTime c t) ξ).alive
      then ‖g (X (GuardedHessianExecution.transportTime c t) ξ).point‖ ^ 2 else 0
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 8 * M ^ 2 := by
  let X := fun n (ξ : ℕ → ℝ × Ω) => HeavyTailedProductProcess.trajectory
    (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
    n (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) ξ
  change (∫ ξ, if (X (GuardedHessianExecution.transportTime c t) ξ).alive
    then ‖g (X (GuardedHessianExecution.transportTime c t) ξ).point‖ ^ 2 else 0
    ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 8 * M ^ 2
  induction t with
  | zero =>
      have hzero (ξ : ℕ → ℝ × Ω) :
          ((X (GuardedHessianExecution.transportTime c 0) ξ).point,
            (X (GuardedHessianExecution.transportTime c 0) ξ).alive) = (p.x0, true) := by
        rw [GuardedHessianExecution.transportTime_zero]
        exact GuardedHessianExecution.fresh_reset_point_alive p c _ answer ξ rfl
      have heq (ξ : ℕ → ℝ × Ω) :
          (if (X (GuardedHessianExecution.transportTime c 0) ξ).alive
            then ‖g (X (GuardedHessianExecution.transportTime c 0) ξ).point‖ ^ 2 else 0) =
              ‖g p.x0‖ ^ 2 := by
        rcases Prod.mk.inj (hzero ξ) with ⟨hp, ha⟩
        rw [hp, ha]
        rfl
      simpa only [heq, integral_const, probReal_univ, one_smul] using hinit
  | succ t ih =>
      have hi := ih (by omega)
      have hb := prefix_cycle_second_moment p c hη P answer g hg M hstep hlocal target t (by omega)
      have heq : (fun ξ : ℕ → ℝ × Ω =>
          if (X (GuardedHessianExecution.transportTime c (t + 1)) ξ).alive
          then ‖g (X (GuardedHessianExecution.transportTime c (t + 1)) ξ).point‖ ^ 2 else 0) =
          (fun ξ : ℕ → ℝ × Ω =>
            if (X (GuardedHessianExecution.transportTime c t + GuardedHessianExecution.cycleCalls c) ξ).alive
            then ‖g (X (GuardedHessianExecution.transportTime c t + GuardedHessianExecution.cycleCalls c) ξ).point‖ ^ 2
            else 0) := by
        funext ξ
        have hh := GuardedHessianExecution.transport_next_point_alive p c answer target ξ t (by omega)
        rcases Prod.mk.inj hh with ⟨hp, ha⟩
        rw [hp, ha]
      rw [heq]
      exact hb.trans (by linarith)

lemma oracle_alive_second_moment (p : Params) (c : Config) (hη : 0 ≤ c.η)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (hg : Differentiable ℝ g) {M : ℝ}
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hsmall : p.L1 * c.η ≤ 1 / 4) (hbase : p.L0 * c.η ≤ M / 4)
    (h0 : ‖g p.x0‖ ≤ M)
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    (hM : 0 < M) (hthreshold : c.threshold = 3 * M / 2)
    (hm : ∀ x, Measurable (fun z : ℝ × Ω => answer (x, none) z.2))
    (hi : ∀ x, Integrable (fun z : ℝ × Ω => answer (x, none) z.2) P)
    (hmean : ∀ x, (∫ z, answer (x, none) z.2 ∂P) = g x)
    (hpi : ∀ x, Integrable (fun z : ℝ × Ω => ‖answer (x, none) z.2 - g x‖ ^ p.p) P)
    (hb : ∀ x, (∫ z, ‖answer (x, none) z.2 - g x‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.guardBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (hgroups : (1 / 2 : ℝ) ^ (c.groups + 1) ≤ 1 / 16)
    (target : Fin (c.steps + 1)) (t : ℕ) (ht : t ≤ c.steps) :
    let result := fun ξ : ℕ → ℝ × Ω => HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (GuardedHessianExecution.transportTime c t)
      (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) ξ
    (∫ ξ, if (result ξ).alive then ‖g (result ξ).point‖ ^ 2 else 0
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 8 * M ^ 2 := by
  apply uniform_alive_second_moment p c hη P answer g hg.continuous M hstep
    (fun s hs => fresh_cycle_second_moment p c s P answer g hg.continuous.measurable hstep hs
      hp hp2 hσ hα hM hthreshold hm hi hmean hpi hb hsize hgroups
      (fun z => proposal_gradient_growth p c hη g hg hL0 hL1 hH hsmall hbase h0 s hs _ _))
    _ target t ht
  nlinarith [norm_nonneg (g p.x0), sq_nonneg M]

end LongTails.Proofs.GuardedHessianIntegration
