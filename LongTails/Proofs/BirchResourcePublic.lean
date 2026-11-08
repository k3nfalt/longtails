import LongTails.Proofs.BirchResourceNativeTimed
import LongTails.Proofs.BirchResourceRepetition

namespace LongTails.Proofs.BirchResourcePublic

open Finset MeasureTheory OracleTemplate
open OracleTemplate.Rennala (Point Instance)
open OracleTemplate.BirchSgd (gradientOracle)
open LongTails.Setups
open LongTails.Algorithms.BirchCollections (algorithm program)
open LongTails.Algorithms.BirchResourceNative
open LongTails.Proofs.BirchResourceNativePlan
open LongTails.Proofs.BirchResourceNativeTimed

lemma clocked_execute {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point d → Ω → Point d)
    (A : Algorithm (Point d) (Point d) (Point d)) (T : ℝ) (C : ℕ)
    (seed : A.Seed) (ξ : ℕ → Ω) :
    execute (gradientOracle P g) (clocked A T) (fun _ => C) seed ξ =
      (execute (gradientOracle P g) A (fun _ => C) seed ξ, T) := by
  let response := fun k (q : Fin 1 × Point d) => g q.2 (ξ k)
  have h₁ := StochasticGradient.execute_advance_of_answer (gradientOracle P g)
    (clocked A T) C seed ξ response (fun _ _ => rfl)
  have h₂ := StochasticGradient.execute_advance_of_answer (gradientOracle P g)
    A C seed ξ response (fun _ _ => rfl)
  rw [h₁, h₂]
  rfl

lemma clocked_success {Q : ℕ} (p : BirchCollections.Params) (l : Layout Q) (hQ : 0 < Q)
    (hl : l.Valid (BirchCollections.batchSize (tuned p))) (hp : GeometryValid p)
    (T : ℝ) (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d))
    (hI : BirchCollections.spec.admissible (tuned p) I O) :
    let q := compiledParams p l hQ
    let A := clocked (algorithm q) T
    let C := BirchCollections.horizon q * (∑ i, l.paid i)
    let out := fun z : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => C) z.1 z.2
    let P := ((A.law : Measure _).prod (O.law : Measure _))
    Measurable out ∧ BirchCollections.spec.successful (tuned p) I (fun z => (out z).1)
      ⟨P, inferInstance⟩ ∧ ∀ᵐ z ∂P, (out z).2 ≤ T := by
  let q := compiledParams p l hQ
  let C := BirchCollections.horizon q * (∑ i, l.paid i)
  have hq : BirchCollections.spec.admissible q I O := hI
  have hs := (native_success p l hQ hl hp.definite hp.continuous hp.Lpos hp.σnonneg hp.εpos
    hp.Δnonneg hp.regular I O hq).2
  obtain ⟨_, Ω, mΩ, μ, P, g, _, _, rfl⟩ := hI
  let := mΩ
  let A := algorithm q
  let m : Measure (A.Seed × (ℕ → Ω)) := (A.law : Measure A.Seed).prod (P : Measure (ℕ → Ω))
  let f := fun z : A.Seed × (ℕ → Ω) =>
    execute (gradientOracle P g) A (fun _ => C) z.1 z.2
  let out := fun z : A.Seed × (ℕ → Ω) =>
    execute (gradientOracle P g) (clocked A T) (fun _ => C) z.1 z.2
  have he : out = fun z => (f z, T) := funext fun z => clocked_execute P g A T C z.1 z.2
  have hh : BirchCollections.spec.successful (tuned p) I f ⟨m, inferInstance⟩ := hs
  change Measurable out ∧ BirchCollections.spec.successful (tuned p) I (fun z => (out z).1)
    ⟨m, inferInstance⟩ ∧ ∀ᵐ z ∂m, (out z).2 ≤ T
  rw [he]
  exact ⟨hh.1.prodMk measurable_const, hh, Filter.Eventually.of_forall (fun _ => le_rfl)⟩

structure RoutedPlan (p : BirchRoutedTime.Params) where
  jobs : ℕ → BirchRoutedTime.Job (Fin p.routes)
  layout : Layout (BirchRoutedTime.block p)
  positive : 0 < BirchRoutedTime.block p
  legal : BirchRoutedTime.Legal p.hardware jobs (range (BirchRoutedTime.block p))
  window : ∀ j < BirchRoutedTime.block p, 0 ≤ (jobs j).launch ∧
    (jobs j).launch + BirchRoutedTime.latency p.hardware (jobs j).route ≤ BirchRoutedTime.window p
  unit : ∀ i, layout.accepted i = 1 ∧ layout.paid i = 1
  parent : ∀ i j, layout.parent i = some j →
    j.val < i.val ∧ (jobs j).route = (jobs i).route ∧
      (jobs j).launch + BirchRoutedTime.latency p.hardware (jobs j).route ≤ (jobs i).launch

lemma routed_nonempty (p : BirchRoutedTime.Params) (hp : BirchRoutedTime.Valid p) :
    Nonempty (RoutedPlan p) := by
  obtain ⟨hg, hJ, hv, ht, hx, hr⟩ := hp
  let B := BirchRoutedTime.block p
  obtain ⟨jobs, hlegal, _, _, htime⟩ :=
    routed_block p.hardware p.depth B hJ hv p.cutoff ht p.fractionalRate hx hr
  let dsp := LongTails.Proofs.BirchResourceDispatch.routed p.hardware jobs id
  let l := layout dsp (fun _ : Fin B => 1) (fun _ => 1)
  have hB : 0 < B := by unfold B BirchRoutedTime.block BirchCollections.batchSize; omega
  exact ⟨⟨jobs, l, hB, hlegal, htime, fun _ => ⟨rfl, rfl⟩, fun i j h => prior_ready dsp i j h⟩⟩

noncomputable def routedPlan (p : BirchRoutedTime.Params) (hp : BirchRoutedTime.Valid p) : RoutedPlan p :=
  Classical.choice (routed_nonempty p hp)

lemma RoutedPlan.valid {p : BirchRoutedTime.Params} (r : RoutedPlan p) :
    r.layout.Valid (BirchRoutedTime.block p) := by
  refine ⟨fun i => ?_, ?_, fun i j h => (r.parent i j h).1⟩
  · rw [(r.unit i).1, (r.unit i).2]
    exact ⟨Nat.one_pos, le_rfl⟩
  · simp only [fun i => (r.unit i).1, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_id]

lemma RoutedPlan.paid {p : BirchRoutedTime.Params} (r : RoutedPlan p) :
    ∑ i, r.layout.paid i = BirchRoutedTime.block p := by
  simp only [fun i => (r.unit i).2, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_id]

structure PowerPlan (p : BirchPowerTime.Params) where
  packets : Finset (Σ _ : Fin p.modes, ℕ)
  order : Fin packets.card ≃ {j // j ∈ packets}
  layout : Layout packets.card
  positive : 0 < packets.card
  legal : BirchPowerTime.Legal p.hardware (LongTails.Proofs.BirchPowerTime.scheduled p.hardware) packets
  window : ∀ j ∈ packets,
    let job := LongTails.Proofs.BirchPowerTime.scheduled p.hardware j
    0 ≤ job.launch ∧ job.launch + p.hardware.duration job.mode ≤ BirchPowerTime.window p ∧
      p.hardware.samples job.mode ≤ p.packetLimit
  work : ∀ i, layout.paid i = p.hardware.samples (LongTails.Proofs.BirchPowerTime.scheduled p.hardware (order i).val).mode
  valid : layout.Valid (BirchPowerTime.block p)
  cap : (∑ i, layout.paid i) ≤ BirchPowerTime.block p + p.packetLimit
  charge : (∑ i, layout.paid i) = sInf (BirchPowerTime.chargeOptions p)
  parent : ∀ i j, layout.parent i = some j →
    let vi := LongTails.Proofs.BirchPowerTime.scheduled p.hardware (order i).val
    let vj := LongTails.Proofs.BirchPowerTime.scheduled p.hardware (order j).val
    j.val < i.val ∧ p.hardware.device vj.mode = p.hardware.device vi.mode ∧
      vj.launch + p.hardware.duration vj.mode ≤ vi.launch

open LongTails.Proofs.BirchPowerTime in
lemma power_options_nonempty (p : BirchPowerTime.Params) (hp : BirchPowerTime.Valid p) :
    (BirchPowerTime.chargeOptions p).Nonempty := by
  obtain ⟨_, hv, _, hr⟩ := hp
  let B := BirchPowerTime.block p
  let T := BirchPowerTime.window p
  obtain ⟨modes, hm, he⟩ := envelope_attained p.hardware hv p.cutoff p.packetLimit
  let packets := planned p.hardware modes T
  have hr' : 0 < BirchPowerTime.rate p.hardware modes := by rwa [he]
  have hcap := repeated_configuration p.hardware hv modes p.cutoff p.packetLimit B hm hr'
  rw [he] at hcap
  have hsum : B ≤ ∑ j ∈ packets, p.hardware.samples j.1 := by
    change B ≤ ∑ j ∈ planned p.hardware modes T, p.hardware.samples (scheduled p.hardware j).mode
    rw [planned_capacity]
    exact hcap
  exact ⟨_, hsum, modes, hm, he, packets, Subset.rfl, rfl⟩

open LongTails.Proofs.BirchPowerTime in
lemma power_nonempty (p : BirchPowerTime.Params) (hp : BirchPowerTime.Valid p) :
    Nonempty (PowerPlan p) := by
  classical
  let B := BirchPowerTime.block p
  let T := BirchPowerTime.window p
  let charge := sInf (BirchPowerTime.chargeOptions p)
  let weight := fun (j : Σ _ : Fin p.modes, ℕ) => p.hardware.samples j.1
  have hB : 0 < B := by unfold B BirchPowerTime.block BirchCollections.batchSize; omega
  have hT : 0 ≤ T := by
    have ht := hp.2.2.1
    have hr := hp.2.2.2
    unfold T BirchPowerTime.window
    positivity
  have hmem : charge ∈ BirchPowerTime.chargeOptions p := Nat.sInf_mem (power_options_nonempty p hp)
  obtain ⟨hcharge, modes, hm, he, full, hfull, hsum⟩ := hmem
  have hpaid_full : B ≤ ∑ j ∈ full, weight j := hsum ▸ hcharge
  have hw (j) (hj : j ∈ full) : 0 < weight j ∧ weight j ≤ p.packetLimit :=
    ⟨(hp.2.1.1 j.1).2.1, (hm.2.2 j.1 (mem_sigma.mp (hfull hj)).1).2⟩
  obtain ⟨s, accept, hs, hpositive, haccept, hpaid⟩ :=
    exact_quota full weight B p.packetLimit hw hpaid_full
  have hs' : s ⊆ planned p.hardware modes T := hs.trans hfull
  have hquota : B ≤ ∑ j ∈ s, weight j := haccept ▸ sum_le_sum (fun j hj => (hpositive j hj).2)
  have hc : ∑ j ∈ s, weight j = charge := by
    apply le_antisymm
    · rw [hsum]
      exact sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)
    · exact Nat.sInf_le ⟨hquota, modes, hm, he, s, hs', rfl⟩
  have hS : 0 < s.card := by
    by_contra! h
    have hz : s = ∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero h)
    rw [hz, sum_empty] at haccept
    omega
  have ⟨hlegal, htime⟩ := scheduled_valid p.hardware hp.2.1 modes p.cutoff p.packetLimit hm T hT s hs'
  have hcard : Fintype.card {j // j ∈ s} = s.card := Fintype.card_coe _
  let order : Fin s.card ≃ {j // j ∈ s} := (finCongr hcard.symm).trans (Fintype.equivFin _).symm
  let jobs := scheduled p.hardware
  let packet := fun n : ℕ => (order ⟨n % s.card, Nat.mod_lt _ hS⟩).val
  let dsp := LongTails.Proofs.BirchResourceDispatch.power p.hardware (jobs ∘ packet)
  let l := layout dsp (fun i => accept (order i).val) (fun i => weight (order i).val)
  have hfold (f : (Σ _ : Fin p.modes, ℕ) → ℕ) : ∑ i, f (order i).val = ∑ j ∈ s, f j := by
    calc
      _ = ∑ j : {j // j ∈ s}, f j.val := Fintype.sum_equiv order _ _ (fun _ => rfl)
      _ = _ := sum_attach _ _
  have hl := layout_valid dsp (fun i => accept (order i).val) (fun i => weight (order i).val)
    (fun i => hpositive _ (order i).property) ((hfold accept).trans haccept)
  refine ⟨⟨s, order, l, hS, hlegal, fun j hj =>
    ⟨(htime j hj).1, (htime j hj).2, (hw j (hs hj)).2⟩, fun _ => rfl, hl,
    (hfold weight).trans_le hpaid, (hfold weight).trans hc, ?_⟩⟩
  intro i j h
  have hready := prior_ready dsp i j h
  simpa only [dsp, LongTails.Proofs.BirchResourceDispatch.power, Function.comp_apply, packet,
    Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hready

noncomputable def powerPlan (p : BirchPowerTime.Params) (hp : BirchPowerTime.Valid p) : PowerPlan p :=
  Classical.choice (power_nonempty p hp)

open LongTails.Proofs.BirchResourceRepetition

lemma RoutedPlan.repeatLegal {p : BirchRoutedTime.Params} (r : RoutedPlan p) (hp : BirchRoutedTime.Valid p) :
    BirchRoutedTime.Legal p.hardware (routeJob r.jobs (BirchRoutedTime.window p))
      (range (BirchRoutedTime.rounds p) ×ˢ range (BirchRoutedTime.block p)) := by
  obtain ⟨_, _, hv, ht, _, hr⟩ := hp
  have hw : 0 ≤ BirchRoutedTime.window p := by unfold BirchRoutedTime.window; positivity
  exact routes_legal p.hardware (fun i => (hv.1 i).le) r.jobs _ _ _ hw r.legal
    (fun j hj => r.window j (mem_range.mp hj))

lemma PowerPlan.repeatLegal {p : BirchPowerTime.Params} (r : PowerPlan p) (hp : BirchPowerTime.Valid p) :
    BirchPowerTime.Legal p.hardware
      (powerJob (LongTails.Proofs.BirchPowerTime.scheduled p.hardware) (BirchPowerTime.window p))
      (range (BirchPowerTime.rounds p) ×ˢ r.packets) := by
  obtain ⟨_, hv, ht, hr⟩ := hp
  have hw : 0 ≤ BirchPowerTime.window p := by unfold BirchPowerTime.window; positivity
  exact power_legal p.hardware _ _ _ _ hw hv.2 r.legal
    (fun j hj => ⟨(r.window j hj).1, (r.window j hj).2.1⟩)

end LongTails.Proofs.BirchResourcePublic
