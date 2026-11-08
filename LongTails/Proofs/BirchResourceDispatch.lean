import LongTails.Proofs.BirchResourceForest
import LongTails.Setups.BirchRoutedTime
import LongTails.Setups.BirchPowerTime

namespace LongTails.Proofs.BirchResourceDispatch

open Finset LongTails.Proofs.BirchResourceForest
open LongTails.Setups

structure Dispatch (Pool : Type*) where
  pool : ℕ → Pool
  launch : ℕ → ℝ
  finish : ℕ → ℝ

def phaseRoot (B k : ℕ) : ℕ := k / B * B

lemma phaseRoot_le (B k : ℕ) : phaseRoot B k ≤ k := Nat.div_mul_le_self k B

lemma phaseRoot_sub_lt {B : ℕ} (hB : 0 < B) (k : ℕ) : k - phaseRoot B k < B := by
  have h₁ := Nat.mod_add_div k B
  rw [Nat.mul_comm] at h₁
  have h₂ := Nat.mod_lt k hB
  unfold phaseRoot
  omega

lemma phaseRoot_constant {B i k : ℕ} (hB : 0 < B)
    (hi : phaseRoot B k ≤ i) (hik : i ≤ k) : phaseRoot B i = phaseRoot B k := by
  unfold phaseRoot at hi ⊢
  have ha : i / B ≤ k / B := Nat.div_le_div_right hik
  have hb : k / B ≤ i / B := (Nat.le_div_iff_mul_le hB).2 hi
  rw [le_antisymm ha hb]

def Acceptable {Pool : Type*} (d : Dispatch Pool) (B : ℕ) (deadline : ℝ) (j k : ℕ) : Prop :=
  phaseRoot B k ≤ j ∧ j < k ∧ d.pool j = d.pool k ∧ d.finish j ≤ deadline

noncomputable def chooseVertex {Pool : Type*} (d : Dispatch Pool) (B : ℕ)
    (deadline : ℝ) (k : ℕ) (previous : ℕ → ℕ) : ℕ := by
  classical
  exact if Acceptable d B deadline (previous k) k then 2 * previous k + 1 else 2 * phaseRoot B k

lemma chooseVertex_earlier {Pool : Type*} (d : Dispatch Pool) (B : ℕ)
    (deadline : ℝ) (k : ℕ) (previous : ℕ → ℕ) :
    Earlier (phaseRoot B k) k (chooseVertex d B deadline k previous) := by
  classical
  unfold chooseVertex
  split
  next h => exact Or.inr ⟨previous k, h.1, h.2.1, rfl⟩
  next => exact Or.inl rfl

lemma chosen_private_ready {Pool : Type*} (d : Dispatch Pool) (B : ℕ)
    (deadline : ℝ) (k j : ℕ) (previous : ℕ → ℕ)
    (h : chooseVertex d B deadline k previous = 2 * j + 1) :
    Acceptable d B deadline j k := by
  classical
  unfold chooseVertex at h
  split at h
  next ha =>
    have he : j = previous k := by omega
    rwa [he]
  next => omega

noncomputable def forest {Pool : Type*} (d : Dispatch Pool) (B : ℕ)
    (head saved : ℕ → ℕ) : Forest where
  root := phaseRoot B
  head k := chooseVertex d B (d.finish k) k head
  saved k := chooseVertex d B (d.launch k) k saved

lemma forest_valid {Pool : Type*} (d : Dispatch Pool) (B : ℕ) (hB : 0 < B)
    (head saved : ℕ → ℕ) : (forest d B head saved).Valid B :=
  ⟨fun k => ⟨phaseRoot_le B k, phaseRoot_sub_lt hB k⟩,
    fun _ _ => phaseRoot_constant hB, fun k =>
      ⟨chooseVertex_earlier d B _ k head, chooseVertex_earlier d B _ k saved⟩⟩

def routed {Route Device Pool : Type*} (p : BirchRoutedTime.Profile Route Device)
    (jobs : ℕ → BirchRoutedTime.Job Route) (pool : Route → Pool) : Dispatch Pool where
  pool k := pool (jobs k).route
  launch k := (jobs k).launch
  finish k := (jobs k).launch + BirchRoutedTime.latency p (jobs k).route

def power {Mode Device : Type*} (p : BirchPowerTime.Profile Mode Device)
    (packet : ℕ → BirchPowerTime.Job Mode) : Dispatch Device where
  pool k := p.device (packet k).mode
  launch k := (packet k).launch
  finish k := (packet k).launch + p.duration (packet k).mode

noncomputable def latest {Pool : Type*} (d : Dispatch Pool) (B : ℕ)
    (deadline : ℕ → ℝ) (k : ℕ) : ℕ := by
  classical
  let ready := (range k).filter (fun j => Acceptable d B (deadline k) j k)
  exact if hn : ready.Nonempty then ready.max' hn else k

lemma latest_ready {Pool : Type*} (d : Dispatch Pool) (B : ℕ) (deadline : ℕ → ℝ)
    (j k : ℕ) (hj : Acceptable d B (deadline k) j k) :
    Acceptable d B (deadline k) (latest d B deadline k) k ∧ j ≤ latest d B deadline k := by
  classical
  let ready := (range k).filter (fun j => Acceptable d B (deadline k) j k)
  have hmem : j ∈ ready := mem_filter.mpr ⟨mem_range.mpr hj.2.1, hj⟩
  have hn : ready.Nonempty := ⟨j, hmem⟩
  have he : latest d B deadline k = ready.max' hn := by
    unfold latest
    exact dite_eq_left hn
  rw [he]
  have hm : ready.max' hn ∈ ready := max'_mem ready hn
  have hm' : ready.max' hn ∈ (range k).filter (fun j => Acceptable d B (deadline k) j k) := hm
  exact ⟨(mem_filter.mp hm').2, le_max' _ _ hmem⟩

def repeated {Pool : Type*} (d : Dispatch Pool) (B : ℕ) (T : ℝ) : Dispatch Pool where
  pool k := d.pool (k % B)
  launch k := (k / B : ℕ) * T + d.launch (k % B)
  finish k := (k / B : ℕ) * T + d.finish (k % B)

lemma repeated_window {Pool : Type*} (d : Dispatch Pool) (B : ℕ) (hB : 0 < B) (T : ℝ)
    (hphase : ∀ j < B, 0 ≤ d.launch j ∧ d.finish j ≤ T) (k : ℕ) :
    (k / B : ℕ) * T ≤ (repeated d B T).launch k ∧
      (repeated d B T).finish k ≤ ((k / B + 1 : ℕ) : ℝ) * T := by
  have h := hphase (k % B) (Nat.mod_lt _ hB)
  constructor
  · dsimp [repeated]
    linarith only [h.1]
  · dsimp [repeated]
    push_cast
    linarith only [h.2]

noncomputable def localForest {Pool : Type*} (d : Dispatch Pool) (B : ℕ) : Forest :=
  forest d B (latest d B d.finish) (latest d B d.launch)

lemma localForest_valid {Pool : Type*} (d : Dispatch Pool) (B : ℕ) (hB : 0 < B) :
    (localForest d B).Valid B := forest_valid d B hB _ _

end LongTails.Proofs.BirchResourceDispatch
