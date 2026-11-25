import LongTails.Algorithms.LogisticDefectCloud
import LongTails.Proofs.Execution

open OracleTemplate
open LongTails.Setups.LogisticDefectCloud
open LongTails.Algorithms.LogisticDefectCloud

namespace LongTails.Proofs.LogisticCloudExecution

variable {p : Params} (D : Data p) (η : ℝ)

noncomputable def increment (w : Weights p.d) (i : Index p) : Weights p.d :=
  let r := answer D (i,w)
  Real.sigmoid (-r.margin) • r.direction

noncomputable def fullStep (w : Weights p.d) : Weights p.d :=
  w + (η/(2*p.n)) • ∑ i, increment D w i

noncomputable def step (s : Scan p) : Scan p :=
  advance p η s (answer D (s.cursor,s.point))

def earlier (p : Params) (k : ℕ) : Finset (Fin (2 * (p.n : ℕ))) := Finset.univ.filter (·.val < k)

def correct (θ : Weights p.d) (k : ℕ) : Prop :=
  ∀ i : Fin (2 * (p.n : ℕ)), i.val < k → 0 < (answer D (i, θ)).margin

private lemma prefix_succ (i : Fin (2 * (p.n : ℕ))) :
    earlier p (i.val + 1) = insert i (earlier p i.val) := by
  ext j
  simp only [earlier, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  rw [← Fin.val_inj]; omega

private lemma correct_succ (θ : Weights p.d) (i : Fin (2 * (p.n : ℕ))) :
    correct D θ (i.val + 1) ↔ correct D θ i.val ∧ 0 < (answer D (i, θ)).margin := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), h i (by omega)⟩
  · rintro ⟨h, hi⟩ j hj
    by_cases e : j = i
    · simpa [e] using hi
    · exact h j (by have := Fin.val_ne_of_ne e; omega)

@[reducible] noncomputable def partialScan (θ : Weights p.d) (i : Fin (2 * (p.n : ℕ))) : Scan p :=
  ⟨θ, i, ∑ j ∈ earlier p i.val, increment D θ j, @decide (correct D θ i.val) (Classical.propDecidable _), false⟩

private lemma scanned (θ : Weights p.d) (i : Fin (2 * (p.n : ℕ))) :
    (step D η)^[i.val] (partialScan D θ 0) = partialScan D θ i := by
  classical
  obtain ⟨k,hk⟩ := i
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k < (2 * (p.n : ℕ)) := by omega
    let i : Fin (2 * (p.n : ℕ)) := ⟨k,hk'⟩
    change (step D η)^[k+1] _ = _
    rw [Function.iterate_succ_apply', ih hk']
    have he := prefix_succ i
    have hc := correct_succ D θ i
    have hn : i ∉ earlier p k := by simp [earlier,i]
    change step D η (partialScan D θ i) = _
    change earlier p (k+1) = insert i (earlier p k) at he
    change correct D θ (k+1) ↔ correct D θ k ∧ _ at hc
    unfold step advance
    rw [ite_eq_right (by exact Bool.false_ne_true : ¬(partialScan D θ i).stopped = true)]
    rw [dite_eq_left (show (partialScan D θ i).cursor.val + 1 < (2 * (p.n : ℕ)) from hk)]
    simp only [partialScan, i, he, Finset.sum_insert hn, hc, Bool.decide_and]
    congr 1
    change _ + increment D θ i = _
    rw [add_comm]

private lemma fresh (θ : Weights p.d) : partialScan D θ 0 = ⟨θ, 0, 0, true, false⟩ := by
  simp [partialScan, earlier, correct]

private lemma full_pass (θ : Weights p.d) :
    let s := (step D η)^[(2 * (p.n : ℕ))] (partialScan D θ 0)
    (s.stopped = true ∧ s.point = θ ∧ correct D θ (2 * (p.n : ℕ))) ∨
      s = partialScan D (θ + (η / (2 * (p.n : ℝ))) • ∑ i, increment D θ i) 0 ∧ ¬correct D θ (2 * (p.n : ℕ)) := by
  classical
  let i : Fin (2 * (p.n : ℕ)) := ⟨(2 * (p.n : ℕ)) - 1, by have := p.n.pos; omega⟩
  have hi : i.val + 1 = (2 * (p.n : ℕ)) := by dsimp [i]; have := p.n.pos; omega
  have he : earlier p (i.val + 1) = Finset.univ := by
    ext j; simp [earlier, hi]
  have hsum : (∑ j ∈ earlier p i.val, increment D θ j) + increment D θ i =
      ∑ j, increment D θ j := by
    rw [← he, prefix_succ, Finset.sum_insert (by simp [earlier]), add_comm]
  have hc := correct_succ D θ i
  rw [hi] at hc
  have hn : ¬ i.val + 1 < (2 * (p.n : ℕ)) := by omega
  have heq : (step D η)^[(2 * (p.n : ℕ))] (partialScan D θ 0) = step D η (partialScan D θ i) := by
    calc
      _ = (step D η)^[i.val+1] (partialScan D θ 0) := congrArg (fun t => (step D η)^[t] (partialScan D θ 0)) hi.symm
      _ = _ := by rw [Function.iterate_succ_apply', scanned D η]
  rw [heq]
  change ((step D η (partialScan D θ i)).stopped = true ∧ _ ∧ _) ∨ _
  by_cases good : correct D θ (2 * (p.n : ℕ))
  · left
    obtain ⟨before, last⟩ := hc.mp good
    simp +instances [step, advance, before, last, hi, good]
  · right
    have check : ¬(correct D θ i.val ∧ 0 < (answer D (i,θ)).margin) := fun h => good (hc.mpr h)
    refine ⟨?_, by simpa only [hi] using good⟩
    rw [fresh]
    simp +instances only [step, advance, partialScan, Bool.false_eq_true, ite_false,
      Bool.and_eq_true, decide_eq_true_eq, check, hn, dite_false]
    congr 1
    exact congrArg (fun g => θ + (η / (2 * (p.n : ℝ))) • g) hsum

private lemma frozen {s : Scan p} (hs : s.stopped = true) (t : ℕ) : (step D η)^[t] s = s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih]; simp [step, advance, hs]


private lemma clock (g : Weights p.d) (k : ℕ) :
    let n := 2*(p.n : ℕ)
    let s := (step D η)^[k*n] (start p g)
    (s.stopped = true ∧ correct D s.point n) ∨
      s = partialScan D ((fullStep D η)^[k] (start p g).point) 0 := by
  induction k with
  | zero =>
    right
    simp only [Nat.zero_mul,Function.iterate_zero_apply]
    rw [fresh]
    rfl
  | succ k ih =>
    let n := 2*(p.n : ℕ)
    let s := (step D η)^[k*n] (start p g)
    have he : (step D η)^[(k+1)*n] (start p g) = (step D η)^[n] s := by
      rw [Nat.succ_mul,Nat.add_comm,Function.iterate_add_apply]
    dsimp only
    rw [he]
    rcases ih with ⟨hs,hc⟩ | hp
    · left; rw [frozen D η hs]; exact ⟨hs,hc⟩
    · change s = _ at hp
      rw [hp]
      rcases full_pass D η ((fullStep D η)^[k] (start p g).point) with ⟨hs,hp',hc⟩ | ⟨hp',_⟩
      · left; exact ⟨hs,hp'.symm ▸ hc⟩
      · right; rwa [Function.iterate_succ_apply']

lemma hits_output (O : Oracle (Query p) (Reply p.d))
    (ha : ∀ history q seed, O.answer history (0,q) seed = answer D q)
    (g : Weights p.d) (ξ : (k : ℕ) → O.Seed k) {k K : ℕ} (hk : k ≤ K)
    (hgood : Separates D ((fullStep D η)^[k] (start p g).point)) :
    Separates D (execute O (algorithm p η) (fun _ => (K+1)*(2*(p.n : ℕ))) g ξ) := by
  let n := 2*(p.n : ℕ)
  let s := (step D η)^[k*n] (start p g)
  let w := (fullStep D η)^[k] (start p g).point
  have hall : correct D w n := fun i _ => hgood i
  have hf : ((step D η)^[n] s).stopped = true ∧ correct D ((step D η)^[n] s).point n := by
    rcases clock D η g k with ⟨hs,hc⟩ | he
    · rw [frozen D η hs]; exact ⟨hs,hc⟩
    · change s = partialScan D w 0 at he
      rw [he]
      rcases full_pass D η w with ⟨hs,hp',hc⟩ | ⟨_,hn⟩
      · exact ⟨hs,hp'.symm ▸ hc⟩
      · exact False.elim (hn hall)
  have he := (execute_eq_of_answer_eq O (answer D) ha (algorithm p η) ((K+1)*n) g ξ).trans
    (execute_iterate (answer D) (algorithm p η) ((K+1)*n) g)
  rw [he]
  change Separates D (((step D η)^[(K+1)*n] (start p g)).point)
  have hkn : (K+1)*n = ((K-k)*n+n)+k*n := by
    rw [show K+1 = (K-k+1)+k by omega,Nat.add_mul,Nat.succ_mul]
  simp only [hkn,Function.iterate_add_apply]
  change Separates D (((step D η)^[(K-k)*n] ((step D η)^[n] s)).point)
  rw [frozen D η hf.1]
  exact fun i => hf.2 i i.isLt

end LongTails.Proofs.LogisticCloudExecution
