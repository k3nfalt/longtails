import LongTails.Proofs.BirchResourceDispatch
import LongTails.Proofs.BirchResourceReplay

namespace LongTails.Proofs.BirchResourceAtomic

open LongTails.Proofs.BirchResourceForest
open LongTails.Proofs.BirchResourceDispatch
open LongTails.Proofs.BirchResourceReplay

lemma first_exists {Packet : Type*} (packet : ℕ → Packet) (B k : ℕ) :
    ∃ j, phaseRoot B k ≤ j ∧ j ≤ k ∧ packet j = packet k :=
  ⟨k, phaseRoot_le B k, le_rfl, rfl⟩

noncomputable def first {Packet : Type*} [DecidableEq Packet] (packet : ℕ → Packet) (B k : ℕ) : ℕ :=
  Nat.find (first_exists packet B k)

lemma first_spec {Packet : Type*} [DecidableEq Packet] (packet : ℕ → Packet) (B k : ℕ) :
    phaseRoot B k ≤ first packet B k ∧ first packet B k ≤ k ∧
      packet (first packet B k) = packet k :=
  Nat.find_spec (first_exists packet B k)

lemma first_eq {Packet : Type*} [DecidableEq Packet] (packet : ℕ → Packet) (B i k : ℕ)
    (hphase : phaseRoot B i = phaseRoot B k) (hpacket : packet i = packet k) :
    first packet B i = first packet B k := by
  have hi := first_spec packet B i
  have hk := first_spec packet B k
  rcases le_total i k with hik | hki
  · have ha : first packet B k ≤ first packet B i :=
      Nat.find_min' (first_exists packet B k)
        ⟨hphase ▸ hi.1, hi.2.1.trans hik, hi.2.2.trans hpacket⟩
    have hb : first packet B i ≤ first packet B k :=
      Nat.find_min' (first_exists packet B i)
        ⟨hphase.symm ▸ hk.1, ha.trans hi.2.1, hk.2.2.trans hpacket.symm⟩
    exact le_antisymm hb ha
  · have ha : first packet B i ≤ first packet B k :=
      Nat.find_min' (first_exists packet B i)
        ⟨hphase.symm ▸ hk.1, hk.2.1.trans hki, hk.2.2.trans hpacket.symm⟩
    have hb : first packet B k ≤ first packet B i :=
      Nat.find_min' (first_exists packet B k)
        ⟨hphase ▸ hi.1, ha.trans hk.2.1, hi.2.2.trans hpacket⟩
    exact le_antisymm ha hb

noncomputable def packetForest {Packet Pool : Type*} [DecidableEq Packet] (packet : ℕ → Packet)
    (d : Dispatch Pool) (B : ℕ) : Forest where
  root := phaseRoot B
  head k := chooseVertex d B (d.finish k) k (latest d B d.finish)
  saved k :=
    let j := first packet B k
    chooseVertex d B (d.launch j) j (latest d B d.launch)

lemma packetForest_valid {Packet Pool : Type*} [DecidableEq Packet] (packet : ℕ → Packet)
    (d : Dispatch Pool) (B : ℕ) (hB : 0 < B) :
    (packetForest packet d B).Valid B := by
  refine ⟨fun k => ⟨phaseRoot_le B k, phaseRoot_sub_lt hB k⟩,
    fun _ _ => phaseRoot_constant hB, fun k => ⟨chooseVertex_earlier d B _ k _, ?_⟩⟩
  let j := first packet B k
  have hj := first_spec packet B k
  have hroot := phaseRoot_constant hB hj.1 hj.2.1
  change Earlier (phaseRoot B k) k (chooseVertex d B (d.launch j) j _)
  rw [← hroot]
  rcases chooseVertex_earlier d B (d.launch j) j (latest d B d.launch) with h | ⟨i, h₁, h₂, he⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, h₁, h₂.trans_le hj.2.1, he⟩

lemma packet_saved_eq {Packet Pool : Type*} [DecidableEq Packet] (packet : ℕ → Packet)
    (d : Dispatch Pool) (B i k : ℕ) (hphase : phaseRoot B i = phaseRoot B k)
    (hpacket : packet i = packet k) :
    (packetForest packet d B).saved i = (packetForest packet d B).saved k := by
  change chooseVertex d B (d.launch (first packet B i)) (first packet B i) _ =
    chooseVertex d B (d.launch (first packet B k)) (first packet B k) _
  rw [first_eq packet B i k hphase hpacket]

lemma packet_saved_ready {Packet Pool : Type*} [DecidableEq Packet] (packet : ℕ → Packet)
    (d : Dispatch Pool) (B : ℕ) (hlaunch : ∀ i k, packet i = packet k → d.launch i = d.launch k)
    (k j : ℕ) (hs : (packetForest packet d B).saved k = 2 * j + 1) :
    d.finish j ≤ d.launch k := by
  let a := first packet B k
  have h : chooseVertex d B (d.launch a) a (latest d B d.launch) = 2 * j + 1 := hs
  exact (chosen_private_ready d B (d.launch a) a j (latest d B d.launch) h).2.2.2.trans_eq
    (hlaunch a k (first_spec packet B k).2.2)

end LongTails.Proofs.BirchResourceAtomic
