import LongTails.Proofs.BirchResourceNativePlan
import LongTails.Proofs.BirchResourceTimedTrace

namespace LongTails.Proofs.BirchResourceNativeTimed

open Finset MeasureTheory OracleTemplate
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections
open LongTails.Proofs.BirchResourceNativePlan
open LongTails.Algorithms.BirchResourceNative
open LongTails.Proofs.BirchResourceDispatch
open LongTails.Proofs.BirchResourcePlans
open LongTails.Proofs.BirchResourceTimedTrace (finish_before_deadline)
open LongTails.Algorithms.BirchCollections (algorithm program)
open LongTails.Setups

noncomputable def prior {Pool : Type*} (d : Dispatch Pool) {Q : ℕ} (i : Fin Q) : Option (Fin Q) :=
  if h : latest d Q d.launch i < i.val then
    some ⟨latest d Q d.launch i, h.trans i.isLt⟩
  else none

lemma prior_ready {Pool : Type*} (d : Dispatch Pool) {Q : ℕ} (i j : Fin Q)
    (h : prior d i = some j) :
    j.val < i.val ∧ d.pool j = d.pool i ∧ d.finish j ≤ d.launch i := by
  classical
  unfold prior at h
  split at h
  next he =>
    have hj := congrArg Fin.val (Option.some.inj h)
    change latest d Q d.launch i = j.val at hj
    have hready : Acceptable d Q (d.launch i) (latest d Q d.launch i) i := by
      let ready := (range i.val).filter (fun k => Acceptable d Q (d.launch i) k i)
      have hn : ready.Nonempty := by
        by_contra hn
        have hf : latest d Q d.launch i = i.val := by
          unfold latest
          exact dite_eq_right hn
        rw [hf] at he
        exact (Nat.lt_irrefl _ he).elim
      have hf : latest d Q d.launch i = ready.max' hn := by
        unfold latest
        exact dite_eq_left hn
      rw [hf]
      have hm : ready.max' hn ∈ (range i.val).filter (fun k => Acceptable d Q (d.launch i) k i) :=
        max'_mem ready hn
      exact (mem_filter.mp hm).2
    rw [hj] at he hready
    exact ⟨he, hready.2.2⟩
  next => simp at h

noncomputable def layout {Pool : Type*} (d : Dispatch Pool) {Q : ℕ}
    (accepted paid : Fin Q → ℕ) : Layout Q :=
  ⟨accepted, paid, prior d⟩

lemma layout_valid {Pool : Type*} (d : Dispatch Pool) {Q B : ℕ} (accepted paid : Fin Q → ℕ)
    (hcount : ∀ i, 0 < accepted i ∧ accepted i ≤ paid i) (hq : ∑ i, accepted i = B) :
    (layout d accepted paid).Valid B :=
  ⟨hcount, hq, fun i j h => (prior_ready d i j h).1⟩

lemma routed_block {Route Device : Type*} [Fintype Route] [Fintype Device]
    [DecidableEq Device] (p : BirchRoutedTime.Profile Route Device) (J B : ℕ)
    (hJ : 0 < J) (hp : p.Valid J) (t : ℝ) (ht : 0 < t) (x : Route → ℝ)
    (hx : BirchRoutedTime.FeasibleRate p t x) (hr : 0 < ∑ r, x r) :
    let T := 2 * (J : ℝ) * ((J : ℝ) * B / (∑ r, x r)) + (4 * J + 2) * t
    ∃ jobs : ℕ → BirchRoutedTime.Job Route, BirchRoutedTime.Legal p jobs (range B) ∧
      let d := routed p jobs id
      let l := layout d (fun _ : Fin B => 1) (fun _ => 1)
      l.Valid B ∧ (∑ i, l.paid i) = B ∧
        ∀ j < B, 0 ≤ d.launch j ∧ d.finish j ≤ T := by
  obtain ⟨jobs, hlegal, htime⟩ := routed_plan p J B hJ hp t ht x hx hr id
  exact ⟨jobs, hlegal, layout_valid _ _ _ (fun _ => ⟨Nat.one_pos, le_rfl⟩) (by simp),
    by simp [layout], htime⟩

lemma power_block {Mode Device : Type*} [Fintype Mode] (p : BirchPowerTime.Profile Mode Device)
    (hp : p.Valid) (t : ℝ) (ht : 0 < t) (u B : ℕ) (hB : 0 < B)
    (hr : 0 < BirchPowerTime.envelope p t u) :
    let T := t + (B : ℝ) / BirchPowerTime.envelope p t u
    let job := LongTails.Proofs.BirchPowerTime.scheduled p
    let weight := fun j => p.samples (job j).mode
    ∃ (s : Finset (Σ _ : Mode, ℕ)) (hS : 0 < s.card) (accepted : (Σ _ : Mode, ℕ) → ℕ)
      (order : Fin s.card ≃ {j // j ∈ s}),
      BirchPowerTime.Legal p job s ∧
      (∀ j ∈ s, 0 ≤ (job j).launch ∧ (job j).launch + p.duration (job j).mode ≤ T ∧
        weight j ≤ u) ∧
      let packet := fun n : ℕ => (order ⟨n % s.card, Nat.mod_lt _ hS⟩).val
      let d := power p (job ∘ packet)
      let l := layout d (fun i => accepted (order i).val) (fun i => weight (order i).val)
      l.Valid B ∧ B ≤ (∑ i, l.paid i) ∧ (∑ i, l.paid i) ≤ B + u ∧
        ∀ j < s.card, 0 ≤ d.launch j ∧ d.finish j ≤ T := by
  classical
  open LongTails.Proofs.BirchPowerTime in
  obtain ⟨modes, hm, he⟩ := envelope_attained p hp t u
  let T := t + (B : ℝ) / BirchPowerTime.envelope p t u
  let job := LongTails.Proofs.BirchPowerTime.scheduled p
  let weight := fun j => p.samples (job j).mode
  let all := LongTails.Proofs.BirchPowerTime.planned p modes T
  have hcap : B ≤ ∑ j ∈ all, weight j := by
    rw [LongTails.Proofs.BirchPowerTime.planned_capacity]
    have hr' : 0 < BirchPowerTime.rate p modes := by rwa [he]
    have ha := LongTails.Proofs.BirchPowerTime.repeated_configuration p hp modes t u B hm hr'
    rw [he] at ha
    exact ha
  have hw (j) (hj : j ∈ all) : 0 < weight j ∧ weight j ≤ u :=
    ⟨(hp.1 (job j).mode).2.1, (hm.2.2 j.1 (mem_sigma.mp hj).1).2⟩
  obtain ⟨s, accept, hs, hpositive, hsum, hpaid⟩ :=
    LongTails.Proofs.BirchPowerTime.exact_quota all weight B u hw hcap
  have hS : 0 < s.card := by
    by_contra! hn
    have he : s = ∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
    rw [he, sum_empty] at hsum
    omega
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have ⟨hlegal, htime⟩ :=
    LongTails.Proofs.BirchPowerTime.scheduled_valid p hp modes t u hm T hT s hs
  have hcard : Fintype.card {j // j ∈ s} = s.card := Fintype.card_coe _
  let order : Fin s.card ≃ {j // j ∈ s} := (finCongr hcard.symm).trans (Fintype.equivFin _).symm
  let packet := fun n : ℕ => (order ⟨n % s.card, Nat.mod_lt _ hS⟩).val
  let d := power p (job ∘ packet)
  let l := layout d (fun i => accept (order i).val) (fun i => weight (order i).val)
  have hfold (f : (Σ _ : Mode, ℕ) → ℕ) : ∑ i, f (order i).val = ∑ j ∈ s, f j := by
    calc
      _ = ∑ j : {j // j ∈ s}, f j.val := Fintype.sum_equiv order _ _ (fun _ => rfl)
      _ = _ := sum_attach _ _
  have hl := layout_valid d (fun i => accept (order i).val) (fun i => weight (order i).val)
    (fun i => hpositive _ (order i).property) ((hfold accept).trans hsum)
  refine ⟨s, hS, accept, order, hlegal, fun j hj =>
    ⟨(htime j hj).1, (htime j hj).2, (hw j (hs hj)).2⟩, hl, ?_, ?_, ?_⟩
  · change B ≤ ∑ i, weight (order i).val
    rw [hfold, ← hsum]
    exact sum_le_sum (fun j hj => (hpositive j hj).2)
  · change (∑ i, weight (order i).val) ≤ B + u
    rw [hfold]
    exact hpaid
  · intro j _
    exact htime _ (order ⟨j % s.card, Nat.mod_lt _ hS⟩).property

structure TimedGuarantee {Pool : Type*} {Q : ℕ} (p : Params) (d : Dispatch Pool)
    (l : Layout Q) (hQ : 0 < Q) (T : ℝ) : Prop where
  predecessor : ∀ i j, l.parent i = some j →
    j.val < i.val ∧ d.pool j = d.pool i ∧ d.finish j ≤ d.launch i
  deadline : ∀ k < horizon (tuned p) * Q,
    (k / Q : ℕ) * T ≤ (repeated d Q T).launch k ∧
      (repeated d Q T).finish k ≤ horizon (tuned p) * T
  work : let q := compiledParams p l hQ
    (program q).oracleCalls = horizon q * (∑ i, l.paid i)
  success : let q := compiledParams p l hQ
    let C := horizon q * (∑ i, l.paid i)
    ∀ (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d)),
      spec.admissible q I O →
      spec.successful q I (fun z : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (algorithm q) (fun _ => C) z.1 z.2)
        ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩

lemma timed_layout {Pool : Type*} {Q : ℕ} (p : Params) (d : Dispatch Pool)
    (a paid : Fin Q → ℕ) (hQ : 0 < Q) (T : ℝ) (hT : 0 ≤ T)
    (hp : GeometryValid p) (hl : (layout d a paid).Valid (batchSize (tuned p)))
    (ht : ∀ j < Q, 0 ≤ d.launch j ∧ d.finish j ≤ T) :
    TimedGuarantee p d (layout d a paid) hQ T := by
  refine ⟨fun i j h => prior_ready d i j h, ?_, (checked p _ hQ hl).1, ?_⟩
  · intro k hk
    exact finish_before_deadline d Q _ hQ T hT ht k hk
  · dsimp only
    intro I O hI
    exact (native_success p _ hQ hl hp.definite hp.continuous hp.Lpos hp.σnonneg hp.εpos
      hp.Δnonneg hp.regular I O hI).2

lemma native_routed {Route Device : Type*} [Fintype Route] [Fintype Device]
    [DecidableEq Device] (p : Params) (hg : GeometryValid p)
    (profile : BirchRoutedTime.Profile Route Device) (J : ℕ) (hJ : 0 < J)
    (hp : profile.Valid J) (t : ℝ) (ht : 0 < t) (x : Route → ℝ)
    (hx : BirchRoutedTime.FeasibleRate profile t x) (hr : 0 < ∑ r, x r) :
    let B := batchSize (tuned p)
    let T := 2 * (J : ℝ) * ((J : ℝ) * B / (∑ r, x r)) + (4 * J + 2) * t
    ∃ (jobs : ℕ → BirchRoutedTime.Job Route) (hB : 0 < B),
      BirchRoutedTime.Legal profile jobs (range B) ∧
      let d := routed profile jobs id
      let l := layout d (fun _ : Fin B => 1) (fun _ => 1)
      (∑ i, l.paid i) = B ∧ TimedGuarantee p d l hB T := by
  let B := batchSize (tuned p)
  let T := 2 * (J : ℝ) * ((J : ℝ) * B / (∑ r, x r)) + (4 * J + 2) * t
  have hB : 0 < B := by unfold B batchSize; omega
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  obtain ⟨jobs, hlegal, hl, hcount, htime⟩ := routed_block profile J B hJ hp t ht x hx hr
  exact ⟨jobs, hB, hlegal, hcount, timed_layout p _ _ _ hB T hT hg hl htime⟩

lemma native_power {Mode Device : Type*} [Fintype Mode] (p : Params) (hg : GeometryValid p)
    (profile : BirchPowerTime.Profile Mode Device) (hp : profile.Valid) (t : ℝ) (ht : 0 < t)
    (u : ℕ) (hr : 0 < BirchPowerTime.envelope profile t u) :
    let B := batchSize (tuned p)
    let T := t + (B : ℝ) / BirchPowerTime.envelope profile t u
    let job := LongTails.Proofs.BirchPowerTime.scheduled profile
    let weight := fun j => profile.samples (job j).mode
    ∃ (s : Finset (Σ _ : Mode, ℕ)) (hS : 0 < s.card) (accepted : (Σ _ : Mode, ℕ) → ℕ)
      (order : Fin s.card ≃ {j // j ∈ s}),
      BirchPowerTime.Legal profile job s ∧
      let packet := fun n : ℕ => (order ⟨n % s.card, Nat.mod_lt _ hS⟩).val
      let d := power profile (job ∘ packet)
      let l := layout d (fun i => accepted (order i).val) (fun i => weight (order i).val)
      B ≤ (∑ i, l.paid i) ∧ (∑ i, l.paid i) ≤ B + u ∧ TimedGuarantee p d l hS T := by
  let B := batchSize (tuned p)
  let T := t + (B : ℝ) / BirchPowerTime.envelope profile t u
  have hB : 0 < B := by unfold B batchSize; omega
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  obtain ⟨s, hS, accept, order, hlegal, _, hl, hlo, hhi, htime⟩ :=
    power_block profile hp t ht u B hB hr
  exact ⟨s, hS, accept, order, hlegal, hlo, hhi, timed_layout p _ _ _ hS T hT hg hl htime⟩

end LongTails.Proofs.BirchResourceNativeTimed
