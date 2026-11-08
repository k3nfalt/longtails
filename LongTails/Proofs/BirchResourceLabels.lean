import LongTails.Proofs.BirchNonEuclideanPhysicalSuccess
import LongTails.Proofs.BirchResourcePlans

namespace LongTails.Proofs.BirchResourceLabels

open Finset MeasureTheory
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Proofs.BirchNonEuclideanPhysicalSuccess (iid_reindex_preserving)
open LongTails.Proofs.BirchResourcePlans (slots slots_card)

noncomputable def paidLabel {Job : Type*} (s : Finset Job) (samples : Job → ℕ)
    {B : ℕ} (pick : Fin B ↪ {j // j ∈ slots s samples}) :
    Fin B ↪ Fin (∑ j ∈ s, samples j) := by
  classical
  have hc : Fintype.card {j // j ∈ slots s samples} = ∑ j ∈ s, samples j := by
    simp [slots_card]
  exact pick.trans ((Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb hc.le))

def issued {B W : ℕ} (hB : 0 < B) (pick : Fin B ↪ Fin W) (k : ℕ) : ℕ :=
  k / B * W + (pick ⟨k % B, Nat.mod_lt _ hB⟩).val

lemma issued_window {B W : ℕ} (hB : 0 < B) (pick : Fin B ↪ Fin W) (k : ℕ) :
    k / B * W ≤ issued hB pick k ∧ issued hB pick k < (k / B + 1) * W := by
  unfold issued
  rw [Nat.add_mul, Nat.one_mul]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (Fin.isLt (pick _)) _⟩

lemma issued_injective {B W : ℕ} (hB : 0 < B) (pick : Fin B ↪ Fin W) :
    Function.Injective (issued hB pick) := by
  intro i k he
  have hwin (j : ℕ) := issued_window hB pick j
  have hphase : i / B = k / B := by
    rcases lt_trichotomy (i / B) (k / B) with h | h | h
    · have ha := Nat.mul_le_mul_right W (Nat.succ_le_of_lt h)
      have hb := ((hwin i).2.trans_le ha).trans_le (hwin k).1
      omega
    · exact h
    · have ha := Nat.mul_le_mul_right W (Nat.succ_le_of_lt h)
      have hb := ((hwin k).2.trans_le ha).trans_le (hwin i).1
      omega
  unfold issued at he
  rw [hphase] at he
  have he' := Nat.add_left_cancel he
  have hm := congrArg Fin.val (pick.injective (Fin.ext he'))
  change i % B = k % B at hm
  have hi := Nat.mod_add_div i B
  have hk := Nat.mod_add_div k B
  rw [hphase, hm] at hi
  exact hi.symm.trans hk

def padded (raw : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k % 2 = 0 then 2 * raw (k / 2) else k

lemma padded_even (raw : ℕ → ℕ) (k : ℕ) : padded raw (2 * k) = 2 * raw k := by
  unfold padded
  rw [ite_eq_left (by omega : (2 * k) % 2 = 0), show 2 * k / 2 = k by omega]

lemma padded_injective (raw : ℕ → ℕ) (hr : Function.Injective raw) :
    Function.Injective (padded raw) := by
  intro i j he
  unfold padded at he
  split at he <;> split at he
  next hi hj =>
    have hh : raw (i / 2) = raw (j / 2) := by omega
    have hh' := hr hh
    omega
  next hi hj => omega
  next hi hj => omega
  next hi hj => exact he

lemma integral_reindex {Ω : Type} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : IID (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (index : ℕ → ℕ) (hinj : Function.Injective index) (f : (ℕ → Ω) → ℝ)
    (hf : Measurable f) :
    (∫ ξ, f (fun k => ξ (index k)) ∂(P : Measure (ℕ → Ω))) =
      ∫ ξ, f ξ ∂(P : Measure (ℕ → Ω)) := by
  have h := iid_reindex_preserving μ P hiid index hinj
  rw [← integral_map h.measurable.aemeasurable hf.aestronglyMeasurable, h.map_eq]

end LongTails.Proofs.BirchResourceLabels
