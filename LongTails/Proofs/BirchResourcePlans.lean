import LongTails.Proofs.BirchResourceDispatch
import LongTails.Proofs.BirchRoutedAssignment
import LongTails.Proofs.BirchPowerTime

namespace LongTails.Proofs.BirchResourcePlans

open Finset LongTails.Proofs.BirchResourceDispatch
open LongTails.Setups

def slots {Job : Type*} (s : Finset Job) (samples : Job → ℕ) : Finset (Σ _ : Job, ℕ) :=
  s.sigma (fun j => range (samples j))

lemma slots_card {Job : Type*} (s : Finset Job) (samples : Job → ℕ) :
    (slots s samples).card = ∑ j ∈ s, samples j := by
  simp [slots, card_sigma]

noncomputable def chooseSlots {Job : Type*} (s : Finset Job) (samples : Job → ℕ) {B : ℕ}
    (hB : B ≤ ∑ j ∈ s, samples j) : Fin B ↪ {j // j ∈ slots s samples} := by
  classical
  have hc : B ≤ Fintype.card {j // j ∈ slots s samples} := by simpa [slots_card] using hB
  exact (Fin.castLEEmb hc).trans (Fintype.equivFin _).symm.toEmbedding

lemma chooseSlots_issued {Job : Type*} (s : Finset Job) (samples : Job → ℕ) {B : ℕ}
    (hB : B ≤ ∑ j ∈ s, samples j) (i : Fin B) :
    let j := (chooseSlots s samples hB i).val
    j.1 ∈ s ∧ j.2 < samples j.1 := by
  exact ⟨(mem_sigma.mp (chooseSlots s samples hB i).property).1,
    mem_range.mp (mem_sigma.mp (chooseSlots s samples hB i).property).2⟩

lemma routed_plan {Route Device Pool : Type*} [Fintype Route] [Fintype Device]
    [DecidableEq Device] (p : BirchRoutedTime.Profile Route Device) (depth B : ℕ) (hdepth : 0 < depth)
    (hp : p.Valid depth) (t : ℝ) (ht : 0 < t) (x : Route → ℝ)
    (hx : BirchRoutedTime.FeasibleRate p t x) (hr : 0 < ∑ r, x r) (pool : Route → Pool) :
    let T := 2 * (depth : ℝ) * ((depth : ℝ) * B / (∑ r, x r)) + (4 * depth + 2) * t
    ∃ jobs : ℕ → BirchRoutedTime.Job Route,
      BirchRoutedTime.Legal p jobs (range B) ∧
      ∀ j < B, 0 ≤ (routed p jobs pool).launch j ∧ (routed p jobs pool).finish j ≤ T :=
  LongTails.Proofs.BirchRoutedTime.exists_routed_phase p depth B hdepth hp t ht x hx hr

lemma power_plan {Mode Device : Type*} [Fintype Mode]
    (p : BirchPowerTime.Profile Mode Device) (hp : p.Valid) (t : ℝ) (u B : ℕ)
    (hB : 0 < B) (hr : 0 < BirchPowerTime.envelope p t u) :
    let T := t + (B : ℝ) / BirchPowerTime.envelope p t u
    let scheduled := LongTails.Proofs.BirchPowerTime.scheduled p
    let samples := fun j => p.samples (scheduled j).mode
    ∃ (s : Finset (Σ _ : Mode, ℕ)) (pick : Fin B ↪ {j // j ∈ slots s samples}),
      BirchPowerTime.Legal p scheduled s ∧
      B ≤ (∑ j ∈ s, samples j) ∧ (∑ j ∈ s, samples j) ≤ B + u ∧
      let packet := fun k : ℕ => scheduled ((pick ⟨k % B, Nat.mod_lt _ hB⟩).val.1)
      ∀ j < B, 0 ≤ (power p packet).launch j ∧ (power p packet).finish j ≤ T := by
  obtain ⟨s, hlegal, htime, hlo, hhi⟩ :=
    LongTails.Proofs.BirchPowerTime.exists_power_envelope_phase p hp t u B hr
  let scheduled := LongTails.Proofs.BirchPowerTime.scheduled p
  let samples := fun j => p.samples (scheduled j).mode
  refine ⟨s, chooseSlots s samples hlo, hlegal, hlo, hhi, ?_⟩
  dsimp only
  intro j _
  exact htime _ (chooseSlots_issued s samples hlo ⟨j % B, Nat.mod_lt _ hB⟩).1

end LongTails.Proofs.BirchResourcePlans
