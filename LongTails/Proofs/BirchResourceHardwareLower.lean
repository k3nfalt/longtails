import LongTails.Proofs.BirchResourceHardLower
import LongTails.Proofs.BirchResourcePlans
import LongTails.Proofs.BirchResourceRepetition

namespace LongTails.Proofs.BirchResourceHardwareLower

open Finset Set MeasureTheory
open LongTails.Setups
open LongTails.Proofs.BirchResourceHardRun
open LongTails.Proofs.BirchResourceHardLower
open LongTails.Proofs.BirchResourceLowerWindow
open LongTails.Proofs.BirchResourceAdaptiveLower
open LongTails.Proofs.BirchResourcePlans (slots slots_card)
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

noncomputable def eligibleSet {Packet : Type*} (run : Scheduler Packet) (keep : Slot Packet → Prop)
    (N m : ℕ) (ℓ : ℝ) (ξ : ℕ → Bool) : Finset ℕ := by
  classical
  exact (range N).filter (fun i => past i ξ ∈ eligibility run keep m ℓ i)

lemma eligibility_card {Packet : Type*} (run : Scheduler Packet) (keep : Slot Packet → Prop)
    (N m : ℕ) (ℓ : ℝ) (ξ : ℕ → Bool) :
    ∑ i ∈ range N, (past i ⁻¹' eligibility run keep m ℓ i).indicator (fun _ => (1 : ℝ)) ξ =
      ((eligibleSet run keep N m ℓ ξ).card : ℝ) := by
  classical
  simp only [eligibleSet, indicator_apply, Set.mem_preimage, sum_boole]

structure RoutedExecution {Route Device : Type*} (p : BirchRoutedTime.Profile Route Device)
    (run : Scheduler ℕ) (N : ℕ) where
  completed : (ℕ → Bool) → Finset ℕ
  staged : (ℕ → Bool) → ℕ → BirchRoutedTime.BufferedJob Route Device
  legal : ∀ ξ, BirchRoutedTime.BufferedLegal p (staged ξ) (completed ξ)
  observedStage : ∀ ξ i s, i < N → observed run ξ i = some s →
    i ∈ completed ξ ∧
    ∀ v ∈ p.path (staged ξ i).route, s.launch ≤ (staged ξ i).start v ∧
      (staged ξ i).start v + p.duration v ≤ s.finish

lemma routed_count {Route Device : Type*} [Fintype Route] [DecidableEq Route]
    [DecidableEq Device] (p : BirchRoutedTime.Profile Route Device) (J : ℕ)
    (hp : p.Valid J) {run : Scheduler ℕ} {N : ℕ} (hc : Causal run N) (ex : RoutedExecution p run N)
    (q : ℝ) (hq : 0 < q) (ℓ : ℝ) (hℓ : 0 < ℓ) (hΦ : ℓ = sInf (routedPrices p (1 / q)) / 9)
    (m : ℕ) (ξ : ℕ → Bool) :
    ∑ i ∈ range N, (past i ⁻¹' eligibility run (fun _ => (0 : ℝ) ≤ 1) m ℓ i).indicator
      (fun _ => (1 : ℝ)) ξ ≤ 1 / (8 * q) := by
  classical
  rw [eligibility_card]
  let E := (range N).filter (fun i => past i ξ ∈ eligibility run (fun _ => (0 : ℝ) ≤ 1) m ℓ i)
  let τ := reachTime run ξ N m
  let jobs := fun i : ℕ => BirchRoutedTime.BufferedJob.mk (ex.staged ξ i).route
    (fun v => (ex.staged ξ i).start v - τ)
  have hw (i : ℕ) (hi : i ∈ E) :
      ∃ s, i < N ∧ observed run ξ i = some s ∧ s.source = m ∧ s.finish ≤ τ + ℓ := by
    obtain ⟨h₁, h₂⟩ := mem_filter.mp hi
    have hin := mem_range.mp h₁
    obtain ⟨s, hs, _, hsrc, _, hfin⟩ := (eligible_iff run _ ξ m ℓ hin.le).1 h₂
    exact ⟨s, hin, hs, hsrc, hfin⟩
  have hsub : E ⊆ ex.completed ξ := by
    intro i hi
    obtain ⟨s, hn, hs, _, _⟩ := hw i hi
    exact (ex.observedStage ξ i s hn hs).1
  have hl : BirchRoutedTime.BufferedLegal p jobs E := by
    refine ⟨?_, ?_⟩
    · intro i hi
      refine ((ex.legal ξ).1 i (hsub hi)).imp ?_
      intro a b hab
      change (ex.staged ξ i).start a - τ + p.duration a ≤ (ex.staged ξ i).start b - τ
      linarith only [hab]
    · intro v t i hi j hj ha hb
      have shift (k : ℕ) (h : (jobs k).active p v t) :
          (ex.staged ξ k).active p v (t + τ) :=
        ⟨h.1, by
          have hh := h.2
          change (ex.staged ξ k).start v - τ ≤ t ∧
            t < (ex.staged ξ k).start v - τ + p.duration v at hh
          exact ⟨by linarith only [hh.1], by linarith only [hh.2]⟩⟩
      exact (ex.legal ξ).2 v (t + τ) i (hsub hi) j (hsub hj) (shift i ha) (shift j hb)
  apply routed_short_window p J hp jobs E q hq ℓ hℓ hΦ hl
  intro i hi v hv
  obtain ⟨s, hn, hs, hsrc, hfin⟩ := hw i hi
  have hlaunch := reach_before_launch hc ξ hn s hs
  rw [hsrc] at hlaunch
  obtain ⟨hstart, hend⟩ := (ex.observedStage ξ i s hn hs).2 v hv
  change 0 ≤ (ex.staged ξ i).start v - τ ∧
    (ex.staged ξ i).start v - τ + p.duration v ≤ ℓ
  exact ⟨by linarith only [hlaunch, hstart], by linarith only [hfin, hend]⟩

structure PowerExecution {Mode Device Packet : Type*} (p : BirchPowerTime.Profile Mode Device)
    (run : Scheduler Packet) (N : ℕ) where
  charged : (ℕ → Bool) → Finset Packet
  mode : Packet → Mode
  launch : (ℕ → Bool) → Packet → ℝ
  legal : ∀ ξ, BirchPowerTime.Legal p (fun j => ⟨mode j, launch ξ j⟩) (charged ξ)
  observedPacket : ∀ ξ i s, i < N → observed run ξ i = some s →
    s.packet ∈ charged ξ ∧ s.launch = launch ξ s.packet ∧
      s.finish = launch ξ s.packet + p.duration (mode s.packet) ∧ s.raw < p.samples (mode s.packet)
  rawUnique : ∀ ξ i j s t, i < N → j < N → observed run ξ i = some s →
    observed run ξ j = some t → s.packet = t.packet → s.raw = t.raw → i = j

lemma power_count {Mode Device Packet : Type*} [Fintype Mode]
    (p : BirchPowerTime.Profile Mode Device) (hp : p.Valid)
    {run : Scheduler Packet} {N : ℕ} (hc : Causal run N) (ex : PowerExecution p run N)
    (q : ℝ) (hq : 0 < q) (ℓ U : ℝ) (hℓ : 0 < ℓ) (hU : 0 ≤ U)
    (hΦ : ℓ = sInf (powerPrices p ⌊U⌋₊ (1 / q)) / 9) (m : ℕ) (ξ : ℕ → Bool) :
    ∑ i ∈ range N, (past i ⁻¹' eligibility run (fun s => (p.samples (ex.mode s.packet) : ℝ) ≤ U)
      m ℓ i).indicator (fun _ => (1 : ℝ)) ξ ≤ 1 / (8 * q) := by
  classical
  rw [eligibility_card]
  let size := fun j => p.samples (ex.mode j)
  let keep := fun s : Slot Packet => (size s.packet : ℝ) ≤ U
  let E := (range N).filter (fun i => past i ξ ∈ eligibility run keep m ℓ i)
  let τ := reachTime run ξ N m
  have hw (i : {i // i ∈ E}) :
      ∃ s, observed run ξ i = some s ∧ s.source = m ∧ keep s ∧ s.finish ≤ τ + ℓ := by
    obtain ⟨h₁, h₂⟩ := mem_filter.mp i.property
    obtain ⟨s, hs, _, hsrc, hkeep, hfin⟩ := (eligible_iff run keep ξ m ℓ (mem_range.mp h₁).le).1 h₂
    exact ⟨s, hs, hsrc, hkeep, hfin⟩
  let pick (i : {i // i ∈ E}) := Classical.choose (hw i)
  have hpick (i : {i // i ∈ E}) := Classical.choose_spec (hw i)
  have hn (i : {i // i ∈ E}) : i.val < N := mem_range.mp (mem_filter.mp i.property).1
  have hrec (i : {i // i ∈ E}) := ex.observedPacket ξ i.val (pick i) (hn i) (hpick i).1
  let S := E.attach.image (fun i => (pick i).packet)
  have hsub : S ⊆ ex.charged ξ := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := mem_image.mp hj
    exact (hrec i).1
  let label (i : {i // i ∈ E}) : {j // j ∈ slots S size} :=
    ⟨⟨(pick i).packet, (pick i).raw⟩, mem_sigma.mpr
      ⟨mem_image.mpr ⟨i, mem_attach _ _, rfl⟩, mem_range.mpr (hrec i).2.2.2⟩⟩
  have hi : Function.Injective label := by
    intro i j he
    have hs : (⟨(pick i).packet, (pick i).raw⟩ : Σ _ : Packet, ℕ) =
        ⟨(pick j).packet, (pick j).raw⟩ := congrArg Subtype.val he
    have h₁ : (pick i).packet = (pick j).packet := congrArg Sigma.fst hs
    have h₂ : (pick i).raw = (pick j).raw := congrArg (fun a : Σ _ : Packet, ℕ => a.2) hs
    exact Subtype.ext (ex.rawUnique ξ i.val j.val (pick i) (pick j) (hn i) (hn j)
      (hpick i).1 (hpick j).1 h₁ h₂)
  have hcard := Fintype.card_le_of_injective label hi
  rw [Fintype.card_coe, Fintype.card_coe, slots_card] at hcard
  let jobs := fun j : Packet => BirchPowerTime.Job.mk (ex.mode j) (ex.launch ξ j - τ)
  have hactive (j : Packet) (t : ℝ) :
      (jobs j).active p t ↔ (BirchPowerTime.Job.mk (ex.mode j) (ex.launch ξ j)).active p (t + τ) := by
    change (ex.launch ξ j - τ ≤ t ∧ t < ex.launch ξ j - τ + p.duration (ex.mode j)) ↔
      (ex.launch ξ j ≤ t + τ ∧ t + τ < ex.launch ξ j + p.duration (ex.mode j))
    constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨by linarith only [ha], by linarith only [hb]⟩
  have hl : BirchPowerTime.Legal p jobs S := by
    intro t
    refine ⟨?_, ?_⟩
    · intro j hj k hk hja hka hd
      exact (ex.legal ξ (t + τ)).1 j (hsub hj) k (hsub hk) ((hactive j t).mp hja)
        ((hactive k t).mp hka) hd
    · let f := fun j : Packet => if (jobs j).active p t then p.power (ex.mode j) else 0
      change (∑ j ∈ S, f j) ≤ p.cap
      refine (sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => ?_)).trans ?_
      · dsimp [f]
        split
        · exact (hp.1 _).2.2
        · exact le_rfl
      · simpa only [f, hactive] using (ex.legal ξ (t + τ)).2
  have hwindow (j : Packet) (hj : j ∈ S) :
      0 ≤ (jobs j).launch ∧ (jobs j).launch + p.duration (jobs j).mode ≤ ℓ := by
    obtain ⟨i, _, rfl⟩ := mem_image.mp hj
    have ht := reach_before_launch hc ξ (hn i) (pick i) (hpick i).1
    rw [(hpick i).2.1, (hrec i).2.1] at ht
    have hf := (hpick i).2.2.2
    rw [(hrec i).2.2.1] at hf
    change 0 ≤ ex.launch ξ (pick i).packet - τ ∧
      ex.launch ξ (pick i).packet - τ + p.duration (ex.mode (pick i).packet) ≤ ℓ
    exact ⟨by linarith only [ht], by linarith only [hf]⟩
  have hsmall (j : Packet) (hj : j ∈ S) : p.samples (jobs j).mode ≤ ⌊U⌋₊ := by
    obtain ⟨i, _, rfl⟩ := mem_image.mp hj
    exact (Nat.le_floor_iff hU).2 (hpick i).2.2.1
  have h := power_short_window p hp jobs S ⌊U⌋₊ q hq ℓ hℓ hΦ hl hwindow hsmall
  refine (show (E.card : ℝ) ≤ ∑ j ∈ S, (p.samples (jobs j).mode : ℝ) from ?_).trans h
  exact_mod_cast hcard

end LongTails.Proofs.BirchResourceHardwareLower
