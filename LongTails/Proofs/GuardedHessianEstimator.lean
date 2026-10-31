import LongTails.Proofs.GuardedHessianNoise
import LongTails.Proofs.GuardedHessianIntegration

open MeasureTheory
open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.GuardedHessianTransport
open LongTails.Proofs.GuardedHessianExecution

namespace LongTails.Proofs.GuardedHessianEstimator

noncomputable def transportNoise (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (s : State p c) (z : ℝ × Ω) : Space p :=
  if s.alive then
    answer (s.point + z.1 • displacement p c s, some (displacement p c s)) z.2 -
      (g (s.point + displacement p c s) - g s.point)
  else 0

lemma fresh_cycle_error (p : Params) (c : Config) (s : State p c) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (ξ : ℕ → ℝ × Ω) (hs : s.phase = .transport) :
    let result := HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (cycleCalls c) s ξ
    result.alive = true → result.estimate - g result.point =
      (s.estimate - g s.point) + transportNoise p c answer g s (ξ 0) := by
  intro result ha
  have hsa := trajectory_alive_previous p c answer s ξ (cycleCalls c) ha
  have hx := fresh_cycle_alive_point p c s answer ξ hs ha
  have hv := fresh_cycle_estimate p c s answer ξ hs
  change result.estimate = _ at hv
  rw [hv, hx]
  simp only [hsa, ↓reduceIte, query, hs, transportNoise]
  abel

noncomputable def path (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (n : ℕ) : State p c :=
  HeavyTailedProductProcess.trajectory
    (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
    n (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) ξ

noncomputable def iterState (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (t : ℕ) : State p c :=
  path p c answer target ξ (transportTime c t)

lemma path_alive_mono (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) {n m : ℕ} (hnm : n ≤ m) :
    (path p c answer target ξ m).alive = true →
      (path p c answer target ξ n).alive = true := by
  have he : m = n + (m - n) := by omega
  rw [he, path, HeavyTailedSospEpochIntegration.trajectory_add]
  exact trajectory_alive_previous p c answer _ _ _

lemma iter_alive_mono (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) {a b : ℕ} (hab : a ≤ b) :
    (iterState p c answer target ξ b).alive = true →
      (iterState p c answer target ξ a).alive = true :=
  path_alive_mono p c answer target ξ (transportTime_strictMono c |>.monotone hab)

lemma iter_error_succ (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω)
    (t : ℕ) (ht : t < c.steps) (hr : (t + 1) % (c.epoch + 1) ≠ 0) :
    let X := iterState p c answer target ξ
    (X (t + 1)).alive = true →
      (X (t + 1)).estimate - g (X (t + 1)).point =
        ((X t).estimate - g (X t).point) +
          transportNoise p c answer g (X t) (ξ (transportTime c t)) := by
  intro X ha
  have hphase : (X t).phase = .transport :=
    (transport_shape p c answer target ξ t ht.le).2
  have heq : X (t + 1) = HeavyTailedProductProcess.trajectory
      (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
      (cycleCalls c) (X t) (fun k => ξ (transportTime c t + k)) := by
    dsimp [X, iterState, path]
    rw [transportTime_succ, ite_eq_right hr, Nat.add_zero,
      HeavyTailedSospEpochIntegration.trajectory_add]
  rw [heq] at ha ⊢
  simpa only [Nat.add_zero] using fresh_cycle_error p c (X t) answer g
    (fun k => ξ (transportTime c t + k)) hphase ha

lemma epoch_error_decomposition (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω)
    (a n : ℕ) (ht : a + n ≤ c.steps)
    (hr : ∀ j, a < j → j ≤ a + n → j % (c.epoch + 1) ≠ 0) :
    let X := iterState p c answer target ξ
    (X (a + n)).alive = true →
      (X (a + n)).estimate - g (X (a + n)).point =
        ((X a).estimate - g (X a).point) +
          ∑ j ∈ Finset.range n,
            transportNoise p c answer g (X (a + j)) (ξ (transportTime c (a + j))) := by
  intro X
  induction n with
  | zero => simp
  | succ n ih =>
      intro ha
      have hpast : (X (a + n)).alive = true :=
        iter_alive_mono p c answer target ξ (by omega : a + n ≤ a + (n + 1)) ha
      have hrec := iter_error_succ p c answer g target ξ (a + n)
        (by omega) (hr (a + n + 1) (by omega) (by omega))
      have herr := ih (by omega) (fun j hj hjn => hr j hj (by omega)) hpast
      rw [Nat.add_succ, hrec ha, herr, Finset.sum_range_succ, add_assoc]

lemma epoch_no_reset (c : Config) (t j : ℕ)
    (hj : (c.epoch + 1) * (t / (c.epoch + 1)) < j) (hjt : j ≤ t) :
    j % (c.epoch + 1) ≠ 0 := by
  let a := (c.epoch + 1) * (t / (c.epoch + 1))
  have ht := Nat.mod_add_div t (c.epoch + 1)
  have hmod := Nat.mod_lt t (by omega : 0 < c.epoch + 1)
  have hja : j = a + (j - a) := by dsimp [a]; omega
  have hsmall : j - a < c.epoch + 1 := by dsimp [a]; omega
  have ha : a % (c.epoch + 1) = 0 := by simp [a]
  rw [hja, Nat.add_mod, ha, zero_add, Nat.mod_eq_of_lt hsmall]
  rw [Nat.mod_eq_of_lt hsmall]
  dsimp [a]
  omega

lemma actual_epoch_error (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω)
    (t : ℕ) (ht : t ≤ c.steps) :
    let X := iterState p c answer target ξ
    let a := (c.epoch + 1) * (t / (c.epoch + 1))
    (X t).alive = true →
      (X t).estimate - g (X t).point =
        ((X a).estimate - g (X a).point) +
          ∑ j ∈ Finset.range (t % (c.epoch + 1)),
            transportNoise p c answer g (X (a + j)) (ξ (transportTime c (a + j))) := by
  intro X a
  have he : a + t % (c.epoch + 1) = t := by
    dsimp [a]
    have hh := Nat.mod_add_div t (c.epoch + 1)
    omega
  have hh := epoch_error_decomposition p c answer g target ξ a (t % (c.epoch + 1))
    (by omega) (fun j hj hjt => epoch_no_reset c t j hj (by omega))
  simpa only [he] using hh

noncomputable def prefixState (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (k : ℕ) (ξ : Fin k → ℝ × Ω) : State p c :=
  OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
    (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
    k (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) ξ

noncomputable def epochNoise (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (target : Fin (c.steps + 1)) (a b k : ℕ)
    (ξ : Fin k → ℝ × Ω) (z : ℝ × Ω) : Space p :=
  if k ∈ (Finset.Ico a b).image (transportTime c) then
    transportNoise p c answer g (prefixState p c answer target k ξ) z else 0

lemma prefixState_eq_path (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (k : ℕ) :
    prefixState p c answer target k (fun i => ξ i) = path p c answer target ξ k :=
  (HeavyTailedSospEpochIntegration.trajectory_finite _ _ _ _).symm

lemma epochNoise_at_transport (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω)
    (a b t : ℕ) (hat : a ≤ t) (htb : t < b) :
    epochNoise p c answer g target a b (transportTime c t) (fun i => ξ i)
      (ξ (transportTime c t)) =
      transportNoise p c answer g (iterState p c answer target ξ t) (ξ (transportTime c t)) := by
  rw [epochNoise, ite_eq_left (Finset.mem_image.mpr ⟨t, Finset.mem_Ico.mpr ⟨hat, htb⟩, rfl⟩),
    prefixState_eq_path]
  rfl

lemma epochNoise_sum (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (a b : ℕ) :
    GuardedHessianNoise.prefixNoiseSum (epochNoise p c answer g target a b)
      (transportTime c b) (fun i => ξ i) =
      ∑ t ∈ Finset.Ico a b,
        transportNoise p c answer g (iterState p c answer target ξ t) (ξ (transportTime c t)) := by
  classical
  rw [GuardedHessianNoise.prefixNoiseSum_eq_sum]
  let S := (Finset.Ico a b).image (transportTime c)
  have hsub : S ⊆ Finset.range (transportTime c b) := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr ((transportTime_strictMono c) (Finset.mem_Ico.mp ht).2)
  have heq : (∑ k ∈ Finset.range (transportTime c b),
      epochNoise p c answer g target a b k (fun i => ξ i) (ξ k)) =
      ∑ k ∈ S, epochNoise p c answer g target a b k (fun i => ξ i) (ξ k) := by
    symm
    apply Finset.sum_subset hsub
    intro k _ hk
    exact ite_eq_right hk
  rw [heq]
  dsimp only [S]
  rw [Finset.sum_image (fun _ _ _ _ h => (transportTime_strictMono c).injective h)]
  apply Finset.sum_congr rfl
  intro t ht
  exact epochNoise_at_transport p c answer g target ξ a b t
    (Finset.mem_Ico.mp ht).1 (Finset.mem_Ico.mp ht).2

lemma actual_epoch_prefix_error (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω)
    (t : ℕ) (ht : t ≤ c.steps) :
    let X := iterState p c answer target ξ
    let a := (c.epoch + 1) * (t / (c.epoch + 1))
    (X t).alive = true →
      (X t).estimate - g (X t).point =
        ((X a).estimate - g (X a).point) +
          GuardedHessianNoise.prefixNoiseSum (epochNoise p c answer g target a t)
            (transportTime c t) (fun i => ξ i) := by
  intro X a ha
  rw [epochNoise_sum, Finset.sum_Ico_eq_sum_range]
  have hrem : t - a = t % (c.epoch + 1) := by
    have hh := Nat.mod_add_div t (c.epoch + 1)
    dsimp [a]
    omega
  rw [hrem]
  exact actual_epoch_error p c answer g target ξ t ht ha

lemma killed_estimator_error_le (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω)
    (t : ℕ) (ht : t ≤ c.steps) :
    let X := iterState p c answer target ξ
    let a := (c.epoch + 1) * (t / (c.epoch + 1))
    (if (X t).alive then ‖(X t).estimate - g (X t).point‖ else 0) ≤
      ‖if (X a).alive then (X a).estimate - g (X a).point else 0‖ +
        ‖GuardedHessianNoise.prefixNoiseSum (epochNoise p c answer g target a t)
          (transportTime c t) (fun i => ξ i)‖ := by
  intro X a
  by_cases ha : (X t).alive = true
  · have hbase : (X a).alive = true := iter_alive_mono p c answer target ξ
      (by have hh := Nat.mod_add_div t (c.epoch + 1); dsimp [a]; omega) ha
    rw [ite_eq_left ha, ite_eq_left hbase,
      actual_epoch_prefix_error p c answer g target ξ t ht ha]
    exact norm_add_le _ _
  · rw [ite_eq_right ha]
    positivity

lemma measurable_transportNoise (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (ha : Measurable (fun w : (Space p × Space p) × Ω =>
      answer (w.1.1, some w.1.2) w.2)) (hg : Measurable g) :
    Measurable (Function.uncurry (transportNoise p c answer g)) := by
  have hd := GuardedHessianMeasurable.measurable_displacement p c
  have hquery : Measurable (fun w : State p c × (ℝ × Ω) =>
      ((w.1.point + w.2.1 • displacement p c w.1, displacement p c w.1), w.2.2)) := by
    fun_prop
  have hdiff : Measurable (fun w : State p c × (ℝ × Ω) =>
      g (w.1.point + displacement p c w.1) - g w.1.point) := by fun_prop
  exact ((ha.comp hquery).sub hdiff).ite
    (measurableSet_eq_fun ((GuardedHessianMeasurable.measurable_alive p c).comp measurable_fst)
      measurable_const) measurable_const

lemma measurable_prefixState (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (target : Fin (c.steps + 1)) (k : ℕ) : Measurable (prefixState p c answer target k) :=
  (OracleTemplate.GapStrongGrowth.iterateSamples_measurable hstep k).comp
    (measurable_const.prodMk measurable_id)

lemma measurable_epochNoise (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (ha : Measurable (fun w : (Space p × Space p) × Ω =>
      answer (w.1.1, some w.1.2) w.2)) (hg : Measurable g)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (target : Fin (c.steps + 1)) (a b k : ℕ) :
    Measurable (Function.uncurry (epochNoise p c answer g target a b k)) := by
  change Measurable (fun w : (Fin k → ℝ × Ω) × (ℝ × Ω) =>
    if k ∈ (Finset.Ico a b).image (transportTime c) then
      transportNoise p c answer g (prefixState p c answer target k w.1) w.2 else 0)
  by_cases hk : k ∈ (Finset.Ico a b).image (transportTime c)
  · simp only [hk, ↓reduceIte]
    exact (measurable_transportNoise p c answer g ha hg).comp
        (((measurable_prefixState p c answer hstep target k).comp measurable_fst).prodMk measurable_snd)
  · simp only [hk, ↓reduceIte]
    exact (measurable_const : Measurable (fun _ : (Fin k → ℝ × Ω) × (ℝ × Ω) => (0 : Space p)))

lemma epoch_transport_sum_moment (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (ha : Measurable (fun w : (Space p × Space p) × Ω =>
      answer (w.1.1, some w.1.2) w.2)) (hg : Measurable g)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    {q κ : ℝ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hκ : 0 ≤ κ)
    (hi : ∀ s, Integrable (transportNoise p c answer g s) Q)
    (hz : ∀ s, (∫ z, transportNoise p c answer g s z ∂Q) = 0)
    (target : Fin (c.steps + 1)) (a b : ℕ)
    (hmi : ∀ t ∈ Finset.Ico a b, Integrable (fun ξ : ℕ → ℝ × Ω =>
      ‖transportNoise p c answer g (iterState p c answer target ξ t) (ξ (transportTime c t))‖ ^ q)
        (Measure.infinitePi fun _ : ℕ => Q))
    (hmb : ∀ t ∈ Finset.Ico a b, (∫ ξ : ℕ → ℝ × Ω,
      ‖transportNoise p c answer g (iterState p c answer target ξ t) (ξ (transportTime c t))‖ ^ q
        ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤ κ) :
    Integrable (fun ξ : ℕ → ℝ × Ω =>
      ‖GuardedHessianNoise.prefixNoiseSum (epochNoise p c answer g target a b)
        (transportTime c b) (fun i => ξ i)‖ ^ q)
      (Measure.infinitePi fun _ : ℕ => Q) ∧
    (∫ ξ : ℕ → ℝ × Ω,
      ‖GuardedHessianNoise.prefixNoiseSum (epochNoise p c answer g target a b)
        (transportTime c b) (fun i => ξ i)‖ ^ q
      ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤ 6 * (b - a : ℕ) * κ := by
  let e := epochNoise p c answer g target a b
  have hei (k : ℕ) (η : Fin k → ℝ × Ω) : Integrable (e k η) Q := by
    change Integrable (fun z => if k ∈ (Finset.Ico a b).image (transportTime c) then
      transportNoise p c answer g (prefixState p c answer target k η) z else 0) Q
    by_cases hk : k ∈ (Finset.Ico a b).image (transportTime c)
    · simpa only [e, epochNoise, hk, ↓reduceIte] using hi (prefixState p c answer target k η)
    · simpa only [e, epochNoise, hk, ↓reduceIte] using
        (integrable_const (0 : Space p) : Integrable (fun _ : ℝ × Ω => (0 : Space p)) Q)
  have hez (k : ℕ) (η : Fin k → ℝ × Ω) : (∫ z, e k η z ∂Q) = 0 := by
    by_cases hk : k ∈ (Finset.Ico a b).image (transportTime c)
    · simpa only [e, epochNoise, hk, ↓reduceIte] using hz (prefixState p c answer target k η)
    · simp [e, epochNoise, hk]
  have hep (k : ℕ) : Integrable (fun ξ : ℕ → ℝ × Ω => ‖e k (fun i => ξ i) (ξ k)‖ ^ q)
      (Measure.infinitePi fun _ : ℕ => Q) := by
    by_cases hk : k ∈ (Finset.Ico a b).image (transportTime c)
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
      simpa only [e, epochNoise_at_transport p c answer g target _ a b t
        (Finset.mem_Ico.mp ht).1 (Finset.mem_Ico.mp ht).2] using hmi t ht
    · simp [e, epochNoise, hk, Real.zero_rpow (show q ≠ 0 by linarith)]
  have hh := GuardedHessianNoise.prefix_sum_moment Q hq hq2 e
    (measurable_epochNoise p c answer g ha hg hstep target a b) hei hez hep (transportTime c b)
  have hsum := sum_supported_transport_calls c a b (transportTime c b) hκ
    (F := fun k => ∫ ξ : ℕ → ℝ × Ω, ‖e k (fun i => ξ i) (ξ k)‖ ^ q
      ∂Measure.infinitePi (fun _ : ℕ => Q)) (by
      intro k hk
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
      simpa only [e, epochNoise_at_transport p c answer g target _ a b t
        (Finset.mem_Ico.mp ht).1 (Finset.mem_Ico.mp ht).2] using hmb t ht) (by
      intro k hk
      simp [e, epochNoise, hk, Real.zero_rpow (show q ≠ 0 by linarith)])
  exact ⟨GuardedHessianNoise.prefix_sum_integrable_moment Q (by linarith : 0 < q) e
    (measurable_epochNoise p c answer g ha hg hstep target a b) hep _,
    hh.trans (by nlinarith)⟩

lemma actual_transport_moment (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (ha : Measurable (fun w : (Space p × Space p) × Ω => answer (w.1.1, some w.1.2) w.2))
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hq : 1 ≤ p.q) (hq2 : p.q ≤ 2)
    (hσ : 0 ≤ p.σh) (hα : 0 ≤ p.αh) {M C K : ℝ} (hM : 0 < M) (hη : 0 ≤ c.η)
    (hK : p.L0 + p.L1 * M + p.σh + p.αh * M ≤ K)
    (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hi : ∀ y v, Integrable (answer (y, some v)) P)
    (hm : ∀ y v, (∫ ω, answer (y, some v) ω ∂P) = fderiv ℝ g y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q) P)
    (hb : ∀ y v, (∫ ω, ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q ∂P) ≤
      (p.σh ^ p.q + p.αh ^ p.q * ‖g y‖ ^ p.q) * ‖v‖ ^ p.q)
    (hsmall : p.L1 * c.η ≤ 1 / 4) (hbase : p.L0 * c.η ≤ M / 4)
    (target : Fin (c.steps + 1)) (k : ℕ) :
    let Q := (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod P
    let X := fun ξ : ℕ → ℝ × Ω => path p c answer target ξ k
    Integrable (fun ξ => (if (X ξ).alive then ‖g (X ξ).point‖ else 0) ^ 2)
      (Measure.infinitePi fun _ : ℕ => Q) →
    (∫ ξ, (if (X ξ).alive then ‖g (X ξ).point‖ else 0) ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤ C * M ^ 2 →
    Integrable (fun ξ => ‖transportNoise p c answer g (X ξ) (ξ k)‖ ^ p.q)
      (Measure.infinitePi fun _ : ℕ => Q) ∧
    (∫ ξ, ‖transportNoise p c answer g (X ξ) (ξ k)‖ ^ p.q
      ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤ 64 * (2 + C) * (K * c.η) ^ p.q := by
  intro Q X hGi hGb
  let U : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  let : IsProbabilityMeasure Q := inferInstanceAs (IsProbabilityMeasure (U.prod P))
  let Y := prefixState p c answer target k
  have hY := measurable_prefixState p c answer hstep target k
  let V := fun ξ : Fin k → ℝ × Ω => (if (Y ξ).alive then ‖g (Y ξ).point‖ else 0) ^ 2
  have hV : Measurable V := by
    apply Measurable.pow_const
    exact ((hg.continuous.measurable.comp
      ((GuardedHessianMeasurable.measurable_point p c).comp hY)).norm).ite
      (measurableSet_eq_fun ((GuardedHessianMeasurable.measurable_alive p c).comp hY)
        measurable_const) measurable_const
  have hpre := OracleTemplate.StochasticGeneralized.prefix_preserving Q k
  have hVi : Integrable V (Measure.pi fun _ : Fin k => Q) :=
    (hpre.integrable_comp hV.aestronglyMeasurable).mp (by
      simpa only [Function.comp_def, V, Y, prefixState_eq_path] using hGi)
  have hVb : (∫ ξ, V ξ ∂Measure.pi (fun _ : Fin k => Q)) ≤ C * M ^ 2 := by
    rw [← hpre.map_eq, integral_map hpre.measurable.aemeasurable hV.aestronglyMeasurable]
    simpa only [V, Y, prefixState_eq_path] using hGb
  have hh := GuardedHessianNoise.masked_affine_random_segment_product
    hL0 hL1 hq hq2 hσ hα hM hη hK hg hD hH
    (fun y ω => answer (y.1, some y.2) ω) ha hi hm hpi hb
    (fun ξ => (Y ξ).point) (fun ξ => displacement p c (Y ξ)) (fun ξ => (Y ξ).alive)
    ((GuardedHessianMeasurable.measurable_point p c).comp hY)
    ((GuardedHessianMeasurable.measurable_displacement p c).comp hY)
    ((GuardedHessianMeasurable.measurable_alive p c).comp hY)
    (fun ξ => GuardedHessianIntegration.displacement_norm_le p c hη (Y ξ))
    hsmall hbase hVi hVb
  let F := fun w : State p c × (ℝ × Ω) => ‖transportNoise p c answer g w.1 w.2‖ ^ p.q
  have hFm : Measurable F := (measurable_transportNoise p c answer g ha
    hg.continuous.measurable).norm.pow_const _
  have hf := HeavyTailedSospForecastIntegration.fresh_step_integral Q
    (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
    hstep k (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) F hFm hh.2.2.1
  refine ⟨hf.1, ?_⟩
  exact hf.2.trans_le hh.2.2.2

lemma oracle_epoch_transport_moment (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (ha : Measurable (fun w : (Space p × Space p) × Ω => answer (w.1.1, some w.1.2) w.2))
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hq : 1 ≤ p.q) (hq2 : p.q ≤ 2)
    (hσ : 0 ≤ p.σh) (hα : 0 ≤ p.αh) {M K : ℝ} (hM : 0 < M) (hη : 0 ≤ c.η)
    (hK : p.L0 + p.L1 * M + p.σh + p.αh * M ≤ K)
    (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hi : ∀ y v, Integrable (answer (y, some v)) P)
    (hm : ∀ y v, (∫ ω, answer (y, some v) ω ∂P) = fderiv ℝ g y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q) P)
    (hb : ∀ y v, (∫ ω, ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q ∂P) ≤
      (p.σh ^ p.q + p.αh ^ p.q * ‖g y‖ ^ p.q) * ‖v‖ ^ p.q)
    (hsmall : p.L1 * c.η ≤ 1 / 4) (hbase : p.L0 * c.η ≤ M / 4)
    (target : Fin (c.steps + 1)) (a b : ℕ) :
    let Q := (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod P
    let X := fun t (ξ : ℕ → ℝ × Ω) => iterState p c answer target ξ t
    (∀ t ∈ Finset.Ico a b,
      Integrable (fun ξ => (if (X t ξ).alive then ‖g (X t ξ).point‖ else 0) ^ 2)
        (Measure.infinitePi fun _ : ℕ => Q)) →
    (∀ t ∈ Finset.Ico a b, (∫ ξ, (if (X t ξ).alive then ‖g (X t ξ).point‖ else 0) ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤ 8 * M ^ 2) →
    Integrable (fun ξ : ℕ → ℝ × Ω =>
      ‖GuardedHessianNoise.prefixNoiseSum (epochNoise p c answer g target a b)
        (transportTime c b) (fun i => ξ i)‖ ^ p.q)
      (Measure.infinitePi fun _ : ℕ => Q) ∧
    (∫ ξ : ℕ → ℝ × Ω,
      ‖GuardedHessianNoise.prefixNoiseSum (epochNoise p c answer g target a b)
        (transportTime c b) (fun i => ξ i)‖ ^ p.q
      ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
        3840 * (b - a : ℕ) * (K * c.η) ^ p.q := by
  intro Q X hGi hGb
  let U : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  let : IsProbabilityMeasure Q := inferInstanceAs (IsProbabilityMeasure (U.prod P))
  have hnoise (s : State p c) : Integrable (transportNoise p c answer g s) Q ∧
      (∫ z, transportNoise p c answer g s z ∂Q) = 0 := by
    have hh := GuardedHessianNoise.affine_random_segment_transport
      hL0 hL1 hq hq2 hσ hα hM hη hK hg hD hH
      (fun y ω => answer (y.1, some y.2) ω) ha hi hm hpi hb s.point (displacement p c s)
      (GuardedHessianIntegration.displacement_norm_le p c hη s) hsmall hbase
    by_cases hs : s.alive = true
    · have hni := hh.1.sub (integrable_const (g (s.point + displacement p c s) - g s.point))
      have hnz : (∫ z : ℝ × Ω,
          answer (s.point + z.1 • displacement p c s, some (displacement p c s)) z.2 -
            (g (s.point + displacement p c s) - g s.point) ∂Q) = 0 := by
        rw [integral_sub hh.1 (integrable_const _), hh.2.1,
          integral_const, probReal_univ, one_smul, sub_self]
      constructor
      · change Integrable (fun z => if s.alive then _ else (0 : Space p)) Q
        simp only [hs, ↓reduceIte]
        exact hni
      · simpa only [transportNoise, hs, ↓reduceIte] using hnz
    · constructor
      · change Integrable (fun z => if s.alive then _ else (0 : Space p)) Q
        simpa only [hs, Bool.false_eq_true, ↓reduceIte] using
          (integrable_const (0 : Space p) : Integrable (fun _ : ℝ × Ω => (0 : Space p)) Q)
      · simp [transportNoise, hs]
  have hmom (t : ℕ) (ht : t ∈ Finset.Ico a b) := actual_transport_moment p c P answer g
    ha hstep hL0 hL1 hq hq2 hσ hα hM hη hK hg hD hH hi hm hpi hb hsmall hbase
    target (transportTime c t) (hGi t ht) (hGb t ht)
  have hK0 : 0 ≤ K := by nlinarith [mul_nonneg hL1 hM.le, mul_nonneg hα hM.le]
  have hh := epoch_transport_sum_moment p c Q answer g ha hg.continuous.measurable hstep
    hq hq2 (κ := 640 * (K * c.η) ^ p.q) (by positivity)
    (fun s => (hnoise s).1) (fun s => (hnoise s).2) target a b
    (fun t ht => (hmom t ht).1) (fun t ht => by
      simpa only [iterState, Q, show (64 : ℝ) * (2 + 8) = 640 by norm_num] using (hmom t ht).2)
  exact ⟨hh.1, hh.2.trans_eq (by ring)⟩

lemma reset_path_transition (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (t : ℕ) :
    iterState p c answer target ξ t =
      HeavyTailedProductProcess.trajectory
        (fun s (z : ℝ × Ω) => update p c s z.1 (answer (query p c s z.1) z.2))
        (c.resetBatch + 1) (path p c answer target ξ (resetTime c t))
        (fun k => ξ (resetTime c t + k)) := by
  dsimp [iterState, path]
  rw [← resetTime_add_batch, HeavyTailedSospEpochIntegration.trajectory_add]

lemma reset_path_point_alive (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (t : ℕ)
    (ht : t ≤ c.steps) (hr : t % (c.epoch + 1) = 0) :
    let S := path p c answer target ξ (resetTime c t)
    let X := iterState p c answer target ξ t
    (X.point, X.alive) = (S.point, S.alive) := by
  intro S X
  have hs : S.phase = .reset 0 0 := (reset_shape p c answer target ξ t ht hr).2
  exact (congrArg (fun s : State p c => (s.point, s.alive))
    (reset_path_transition p c answer target ξ t)).trans
      (fresh_reset_point_alive p c S answer _ hs)

lemma actual_reset_error (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (target : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (t : ℕ)
    (ht : t ≤ c.steps) (hr : t % (c.epoch + 1) = 0) :
    let S := path p c answer target ξ (resetTime c t)
    let X := iterState p c answer target ξ t
    (if X.alive then X.estimate - g X.point else 0) =
      if S.alive then ((c.resetBatch + 1 : ℕ) : ℝ)⁻¹ •
        ∑ k ∈ Finset.range (c.resetBatch + 1),
          answer (S.point, none) (ξ (resetTime c t + k)).2 - g S.point else 0 := by
  intro S X
  have hs : S.phase = .reset 0 0 := (reset_shape p c answer target ξ t ht hr).2
  have hp := Prod.mk.inj (reset_path_point_alive p c answer target ξ t ht hr)
  have he := congrArg (fun s : State p c => s.estimate)
    (reset_path_transition p c answer target ξ t)
  rw [fresh_reset_estimate p c S answer _ hs] at he
  change X.estimate = _ at he
  change X.point = S.point ∧ X.alive = S.alive at hp
  rw [hp.1, hp.2, he]
  split_ifs <;> rfl

lemma masked_batch_moment {S Ω E : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure S} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (e : S × Ω → E) (A : S → Bool) (G : S → ℝ)
    (he : Measurable e) (hA : Measurable A) (hG : Measurable G) (hG0 : ∀ s, 0 ≤ G s)
    {p σ α M C : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (hα : 0 ≤ α)
    (hM : 0 < M) (B : ℕ) (hB : 0 < B)
    (hi : ∀ s, Integrable (fun ω => e (s, ω)) P)
    (hm : ∀ s, (∫ ω, e (s, ω) ∂P) = 0)
    (hpi : ∀ s, Integrable (fun ω => ‖e (s, ω)‖ ^ p) P)
    (hb : ∀ s, (∫ ω, ‖e (s, ω)‖ ^ p ∂P) ≤ σ ^ p + α ^ p * G s ^ p)
    (hGi : Integrable (fun s => (if A s then G s else 0) ^ 2) μ)
    (hGb : (∫ s, (if A s then G s else 0) ^ 2 ∂μ) ≤ C * M ^ 2) :
    let F := fun w : S × (ℕ → Ω) => if A w.1 then
      (B : ℝ)⁻¹ • ∑ k ∈ Finset.range B, e (w.1, w.2 k) else 0
    Integrable (fun w => ‖F w‖ ^ p) (μ.prod (Measure.infinitePi fun _ : ℕ => P)) ∧
      (∫ w, ‖F w‖ ^ p ∂μ.prod (Measure.infinitePi fun _ : ℕ => P)) ≤
        6 * (σ ^ p + (1 + C) * α ^ p * M ^ p) / (B : ℝ) ^ (p - 1) := by
  intro F
  let Z := fun s => if A s then G s else 0
  have hZ : Measurable Z := hG.ite (hA (measurableSet_singleton true)) measurable_const
  have hZ0 (s : S) : 0 ≤ Z s := by dsimp [Z]; split; exact hG0 s; exact le_refl 0
  have hGp := GuardedHessianNoise.moment_from_second hZ hZ0 hM
    (by linarith : 0 ≤ p) hp2 hGi hGb
  have hden : 0 < (B : ℝ) ^ (p - 1) := Real.rpow_pos_of_pos (by exact_mod_cast hB) _
  have hFm : Measurable F := by
    apply Measurable.ite ((hA.comp measurable_fst) (measurableSet_singleton true))
    · fun_prop
    · exact measurable_const
  have hlocal (s : S) := HeavyTailedFreshProcess.iid_batch_moment P
    (he.comp measurable_prodMk_left) hp hp2 (hi s) (hm s) (hpi s) (hb s) B hB
  have hfi (s : S) : Integrable (fun ξ : ℕ → Ω => ‖F (s, ξ)‖ ^ p)
      (Measure.infinitePi fun _ : ℕ => P) := by
    by_cases hs : A s = true
    · simpa only [F, hs, ↓reduceIte, Function.comp_apply] using (hlocal s).1
    · simp [F, hs, Real.zero_rpow (show p ≠ 0 by linarith)]
  have hfb (s : S) : (∫ ξ : ℕ → Ω, ‖F (s, ξ)‖ ^ p
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      6 * (σ ^ p + α ^ p * Z s ^ p) / (B : ℝ) ^ (p - 1) := by
    by_cases hs : A s = true
    · simpa only [F, Z, hs, ↓reduceIte, Function.comp_apply] using (hlocal s).2
    · simp only [F, Z, hs, Bool.false_eq_true, ↓reduceIte, norm_zero,
        Real.zero_rpow (show p ≠ 0 by linarith), integral_zero, mul_zero, add_zero]
      positivity
  have hbi := (((integrable_const (σ ^ p)).add (hGp.1.const_mul (α ^ p))).const_mul 6).div_const
    ((B : ℝ) ^ (p - 1))
  have hh := WeakGradientConvolution.nonnegative_fiber_integral_bound
    (hFm.norm.pow_const p).stronglyMeasurable (fun _ => Real.rpow_nonneg (norm_nonneg _) p)
    (Filter.Eventually.of_forall hfi) hbi (Filter.Eventually.of_forall hfb)
  refine ⟨hh.1, hh.2.trans ?_⟩
  simp only [Pi.add_apply] at *
  rw [integral_div, integral_const_mul,
    integral_add (integrable_const _) (hGp.1.const_mul _), integral_const_mul,
    integral_const, probReal_univ, one_smul]
  have hb' := mul_le_mul_of_nonneg_left hGp.2 (Real.rpow_nonneg hα p)
  apply (div_le_div_iff_of_pos_right hden).mpr
  nlinarith

set_option maxHeartbeats 800000 in
lemma actual_reset_moment (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (ha : Measurable (fun w : Space p × (ℝ × Ω) => answer (w.1, none) w.2.2))
    (hg : Measurable g)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    {M : ℝ} (hM : 0 < M)
    (hi : ∀ y, Integrable (fun z : ℝ × Ω => answer (y, none) z.2) Q)
    (hm : ∀ y, (∫ z : ℝ × Ω, answer (y, none) z.2 ∂Q) = g y)
    (hpi : ∀ y, Integrable (fun z : ℝ × Ω => ‖answer (y, none) z.2 - g y‖ ^ p.p) Q)
    (hb : ∀ y, (∫ z : ℝ × Ω, ‖answer (y, none) z.2 - g y‖ ^ p.p ∂Q) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g y‖ ^ p.p)
    (target : Fin (c.steps + 1)) (t : ℕ) (ht : t ≤ c.steps)
    (hr : t % (c.epoch + 1) = 0) :
    let X := fun ξ : ℕ → ℝ × Ω => iterState p c answer target ξ t
    Integrable (fun ξ => (if (X ξ).alive then ‖g (X ξ).point‖ else 0) ^ 2)
      (Measure.infinitePi fun _ : ℕ => Q) →
    (∫ ξ, (if (X ξ).alive then ‖g (X ξ).point‖ else 0) ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤ 8 * M ^ 2 →
    Integrable (fun ξ => ‖if (X ξ).alive then (X ξ).estimate - g (X ξ).point else 0‖ ^ p.p)
      (Measure.infinitePi fun _ : ℕ => Q) ∧
    (∫ ξ, ‖if (X ξ).alive then (X ξ).estimate - g (X ξ).point else 0‖ ^ p.p
      ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
      6 * (p.σg ^ p.p + 9 * p.αg ^ p.p * M ^ p.p) / ((c.resetBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) := by
  intro X hGi hGb
  let r := resetTime c t
  let Y := prefixState p c answer target r
  let V := fun η : Fin r → ℝ × Ω => (if (Y η).alive then ‖g (Y η).point‖ else 0) ^ 2
  have hY := measurable_prefixState p c answer hstep target r
  have hpoint := (GuardedHessianMeasurable.measurable_point p c).comp hY
  have halive := (GuardedHessianMeasurable.measurable_alive p c).comp hY
  have hV : Measurable V := by
    apply Measurable.pow_const
    exact (hg.comp hpoint).norm.ite (halive (measurableSet_singleton true)) measurable_const
  have heq (ξ : ℕ → ℝ × Ω) : V (fun i => ξ i) =
      (if (X ξ).alive then ‖g (X ξ).point‖ else 0) ^ 2 := by
    have hh := Prod.mk.inj (reset_path_point_alive p c answer target ξ t ht hr)
    change (X ξ).point = (path p c answer target ξ r).point ∧
      (X ξ).alive = (path p c answer target ξ r).alive at hh
    simp only [V, Y, prefixState_eq_path, ← hh.1, ← hh.2]
  have hpre := OracleTemplate.StochasticGeneralized.prefix_preserving Q r
  have hVi : Integrable V (Measure.pi fun _ : Fin r => Q) :=
    (hpre.integrable_comp hV.aestronglyMeasurable).mp (by
      simpa only [Function.comp_def, heq] using hGi)
  have hVb : (∫ η, V η ∂Measure.pi (fun _ : Fin r => Q)) ≤ 8 * M ^ 2 := by
    rw [← hpre.map_eq, integral_map hpre.measurable.aemeasurable hV.aestronglyMeasurable]
    simpa only [heq] using hGb
  let e := fun w : (Fin r → ℝ × Ω) × (ℝ × Ω) =>
    answer ((Y w.1).point, none) w.2.2 - g (Y w.1).point
  have he : Measurable e := (ha.comp ((hpoint.comp measurable_fst).prodMk measurable_snd)).sub
    (hg.comp (hpoint.comp measurable_fst))
  have hmean (η : Fin r → ℝ × Ω) : (∫ z, e (η, z) ∂Q) = 0 := by
    dsimp only [e]
    rw [integral_sub (hi _) (integrable_const _), hm, integral_const,
      probReal_univ, one_smul, sub_self]
  have hei (η : Fin r → ℝ × Ω) : Integrable (fun z => e (η, z)) Q :=
    (hi (Y η).point).sub (integrable_const (g (Y η).point))
  have hepi (η : Fin r → ℝ × Ω) : Integrable (fun z => ‖e (η, z)‖ ^ p.p) Q := hpi (Y η).point
  have heb (η : Fin r → ℝ × Ω) : (∫ z, ‖e (η, z)‖ ^ p.p ∂Q) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g (Y η).point‖ ^ p.p := hb (Y η).point
  have hbatch := masked_batch_moment (μ := Measure.pi fun _ : Fin r => Q) (P := Q)
    (p := p.p) (σ := p.σg) (α := p.αg) (M := M) (C := 8)
    e (fun η => (Y η).alive) (fun η => ‖g (Y η).point‖)
    he halive (hg.comp hpoint).norm (fun _ => norm_nonneg _) hp hp2 hσ hα hM
    (c.resetBatch + 1) (by omega) hei hmean hepi heb hVi hVb
  let F := fun w : (Fin r → ℝ × Ω) × (ℕ → ℝ × Ω) =>
    ‖if (Y w.1).alive then ((c.resetBatch + 1 : ℕ) : ℝ)⁻¹ •
      ∑ k ∈ Finset.range (c.resetBatch + 1), e (w.1, w.2 k) else 0‖ ^ p.p
  have hemean (u : Space p) (v : ℕ → Space p) :
      ((c.resetBatch + 1 : ℕ) : ℝ)⁻¹ • ∑ k ∈ Finset.range (c.resetBatch + 1), (v k - u) =
      ((c.resetBatch + 1 : ℕ) : ℝ)⁻¹ • ∑ k ∈ Finset.range (c.resetBatch + 1), v k - u := by
    rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by positivity :
        ((c.resetBatch + 1 : ℕ) : ℝ) ≠ 0), one_smul]
  have hsplit := OracleTemplate.StochasticGeneralized.splitStream_preserving Q r
  have hefun : (fun ξ : ℕ → ℝ × Ω =>
      ‖if (X ξ).alive then (X ξ).estimate - g (X ξ).point else 0‖ ^ p.p) =
      F ∘ OracleTemplate.StochasticGeneralized.splitStream r := by
    funext ξ
    rw [actual_reset_error p c answer g target ξ t ht hr]
    change _ = F ((fun i : Fin r => ξ i), fun k => ξ (r + k))
    dsimp only [F, e, Y]
    simp only [prefixState_eq_path, hemean]
    rfl
  rw [hefun]
  refine ⟨hsplit.integrable_comp_of_integrable hbatch.1, ?_⟩
  simpa only [Function.comp_def, hsplit.integral_comp' F, show (1 : ℝ) + 8 = 9 by norm_num]
    using hbatch.2

lemma expected_estimator_error (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (ha : Measurable (fun w : (Space p × Space p) × Ω => answer (w.1.1, some w.1.2) w.2))
    (hg : Measurable g)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (hp : 1 ≤ p.p) (hq : 1 ≤ p.q) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (target : Fin (c.steps + 1)) (t : ℕ) (ht : t ≤ c.steps) :
    let X := fun j (ξ : ℕ → ℝ × Ω) => iterState p c answer target ξ j
    let a := (c.epoch + 1) * (t / (c.epoch + 1))
    let R := fun ξ => if (X a ξ).alive then (X a ξ).estimate - g (X a ξ).point else 0
    let T := fun ξ : ℕ → ℝ × Ω =>
      GuardedHessianNoise.prefixNoiseSum (epochNoise p c answer g target a t)
        (transportTime c t) (fun i => ξ i)
    Integrable (fun ξ => ‖R ξ‖ ^ p.p) (Measure.infinitePi fun _ : ℕ => Q) →
    (∫ ξ, ‖R ξ‖ ^ p.p ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤ r ^ p.p →
    Integrable (fun ξ => ‖T ξ‖ ^ p.q) (Measure.infinitePi fun _ : ℕ => Q) →
    (∫ ξ, ‖T ξ‖ ^ p.q ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤ s ^ p.q →
    Integrable (fun ξ => if (X t ξ).alive then ‖(X t ξ).estimate - g (X t ξ).point‖ else 0)
      (Measure.infinitePi fun _ : ℕ => Q) ∧
    (∫ ξ, if (X t ξ).alive then ‖(X t ξ).estimate - g (X t ξ).point‖ else 0
      ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤ r + s := by
  intro X a R T hRi hRb hTi hTb
  have hX (j : ℕ) : Measurable (X j) :=
    (HeavyTailedProductProcess.trajectory_measurable hstep (transportTime c j)).comp
      (measurable_const.prodMk measurable_id)
  have hR : Measurable R := by
    exact (((GuardedHessianMeasurable.measurable_estimate p c).comp (hX a)).sub
      (hg.comp ((GuardedHessianMeasurable.measurable_point p c).comp (hX a)))).ite
      (measurableSet_eq_fun ((GuardedHessianMeasurable.measurable_alive p c).comp (hX a))
        measurable_const) measurable_const
  have hT : Measurable T := (GuardedHessianNoise.measurable_prefixNoiseSum _
    (measurable_epochNoise p c answer g ha hg hstep target a t) _).comp (by fun_prop)
  have hRfirst := GuardedHessianNoise.norm_first_from_power hR hp hr hRi hRb
  have hTfirst := GuardedHessianNoise.norm_first_from_power hT hq hs hTi hTb
  let F := fun ξ => if (X t ξ).alive then ‖(X t ξ).estimate - g (X t ξ).point‖ else 0
  have hF : Measurable F := by
    exact ((((GuardedHessianMeasurable.measurable_estimate p c).comp (hX t)).sub
      (hg.comp ((GuardedHessianMeasurable.measurable_point p c).comp (hX t)))).norm).ite
      (measurableSet_eq_fun ((GuardedHessianMeasurable.measurable_alive p c).comp (hX t))
        measurable_const) measurable_const
  have hF0 (ξ : ℕ → ℝ × Ω) : 0 ≤ F ξ := by dsimp [F]; split <;> positivity
  have hbound (ξ : ℕ → ℝ × Ω) : F ξ ≤ ‖R ξ‖ + ‖T ξ‖ :=
    killed_estimator_error_le p c answer g target ξ t ht
  have hFi := (hRfirst.1.add hTfirst.1).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ξ)]
      exact hbound ξ))
  refine ⟨hFi, ?_⟩
  have hh := integral_mono hFi (hRfirst.1.add hTfirst.1) hbound
  simp only [Pi.add_apply] at hh
  rw [integral_add hRfirst.1 hTfirst.1] at hh
  exact hh.trans (add_le_add hRfirst.2 hTfirst.2)

lemma expected_estimator_bound (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (ha : Measurable (fun w : (Space p × Space p) × Ω => answer (w.1.1, some w.1.2) w.2))
    (hg : Measurable g)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (hp : 1 ≤ p.p) (hq : 1 ≤ p.q) {M K : ℝ}
    (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg) (hM : 0 ≤ M) (hK : 0 ≤ K) (hη : 0 ≤ c.η)
    (target : Fin (c.steps + 1)) (t : ℕ) (ht : t ≤ c.steps) :
    let X := fun j (ξ : ℕ → ℝ × Ω) => iterState p c answer target ξ j
    let a := (c.epoch + 1) * (t / (c.epoch + 1))
    let R := fun ξ => if (X a ξ).alive then (X a ξ).estimate - g (X a ξ).point else 0
    let T := fun ξ : ℕ → ℝ × Ω =>
      GuardedHessianNoise.prefixNoiseSum (epochNoise p c answer g target a t)
        (transportTime c t) (fun i => ξ i)
    Integrable (fun ξ => ‖R ξ‖ ^ p.p) (Measure.infinitePi fun _ : ℕ => Q) →
    (∫ ξ, ‖R ξ‖ ^ p.p ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
      6 * (p.σg ^ p.p + 9 * p.αg ^ p.p * M ^ p.p) /
        ((c.resetBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) →
    Integrable (fun ξ => ‖T ξ‖ ^ p.q) (Measure.infinitePi fun _ : ℕ => Q) →
    (∫ ξ, ‖T ξ‖ ^ p.q ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
      3840 * (t - a : ℕ) * (K * c.η) ^ p.q →
    Integrable (fun ξ => if (X t ξ).alive then ‖(X t ξ).estimate - g (X t ξ).point‖ else 0)
      (Measure.infinitePi fun _ : ℕ => Q) ∧
    (∫ ξ, if (X t ξ).alive then ‖(X t ξ).estimate - g (X t ξ).point‖ else 0
      ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
      54 * (p.σg + p.αg * M) *
        (((c.resetBatch + 1 : ℕ) : ℝ) ^ (p.p - 1))⁻¹ ^ p.p⁻¹ +
      3840 * (K * c.η) * ((c.epoch + 1 : ℕ) : ℝ) ^ p.q⁻¹ := by
  intro X a R T hRi hRb hTi hTb
  refine expected_estimator_error p c Q answer g ha hg hstep hp hq (by positivity) (by positivity)
    target t ht hRi ?_ hTi ?_
  · have hden : 0 < ((c.resetBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) := by positivity
    have hs := div_le_div_of_nonneg_right
      (GuardedHessianNoise.reset_moment_scale hσ hα hM hp) hden.le
    have hr := GuardedHessianNoise.scaled_root_power (by norm_num : (1 : ℝ) ≤ 54)
      (show 0 ≤ p.σg + p.αg * M by positivity) (inv_nonneg.mpr hden.le) hp
    exact (hRb.trans hs).trans (by convert hr using 1; ring)
  · have hlen : t - a ≤ c.epoch + 1 := by
      dsimp only [a]
      have hh := Nat.mod_add_div t (c.epoch + 1)
      have hr := Nat.mod_lt t (show 0 < c.epoch + 1 by omega)
      omega
    have hlen' : ((t - a : ℕ) : ℝ) ≤ (c.epoch + 1 : ℕ) := by exact_mod_cast hlen
    have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen' (by norm_num : (0 : ℝ) ≤ 3840))
      (Real.rpow_nonneg (mul_nonneg hK hη) p.q)
    exact (hTb.trans hs).trans (GuardedHessianNoise.scaled_root_power
      (by norm_num) (mul_nonneg hK hη) (by positivity) hq)

end LongTails.Proofs.GuardedHessianEstimator
