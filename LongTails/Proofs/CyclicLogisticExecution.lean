import LongTails.Proofs.CyclicLogisticCoordinates
import LongTails.Proofs.Execution

open OracleTemplate
open LongTails.Setups.CyclicLogisticFeatureLearning
open LongTails.Setups.ManySampleConvolutionalPerceptron (Space)
open LongTails.Algorithms.CyclicLogisticFeatureLearning
open LongTails.Proofs.CyclicLogisticCoordinates
open LongTails.Proofs.CyclicLogisticTuning

namespace LongTails.Proofs.CyclicLogisticExecution

variable {p : Params} (D : Data p)

noncomputable def step (s : Scan p) : Scan p :=
  advance p (stepSize p) s (answer p D (s.cursor, s.point))

def earlier (p : Params) (k : ℕ) : Finset (Fin p.n) := Finset.univ.filter (·.val < k)

def correct (θ : Space p.d) (k : ℕ) : Prop :=
  ∀ i : Fin p.n, i.val < k → 0 < (answer p D (i, θ)).margin

private lemma prefix_succ (i : Fin p.n) :
    earlier p (i.val + 1) = insert i (earlier p i.val) := by
  ext j
  simp only [earlier, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  rw [← Fin.val_inj]; omega

private lemma correct_succ (θ : Space p.d) (i : Fin p.n) :
    correct D θ (i.val + 1) ↔ correct D θ i.val ∧ 0 < (answer p D (i, θ)).margin := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), h i (by omega)⟩
  · rintro ⟨h, hi⟩ j hj
    by_cases e : j = i
    · simpa [e] using hi
    · exact h j (by have := Fin.val_ne_of_ne e; omega)

@[reducible] noncomputable def partialScan (θ : Space p.d) (i : Fin p.n) : Scan p :=
  ⟨θ, i, ∑ j ∈ earlier p i.val, increment D θ j, @decide (correct D θ i.val) (Classical.propDecidable _), false⟩

private lemma scanned (θ : Space p.d) (i : Fin p.n) :
    (step D)^[i.val] (partialScan D θ 0) = partialScan D θ i := by
  classical
  obtain ⟨k,hk⟩ := i
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k < p.n := by omega
    let i : Fin p.n := ⟨k,hk'⟩
    change (step D)^[k+1] _ = _
    rw [Function.iterate_succ_apply', ih hk']
    have he := prefix_succ i
    have hc := correct_succ D θ i
    have hn : i ∉ earlier p k := by simp [earlier,i]
    change step D (partialScan D θ i) = _
    change earlier p (k+1) = insert i (earlier p k) at he
    change correct D θ (k+1) ↔ correct D θ k ∧ _ at hc
    unfold step advance
    rw [ite_eq_right (by exact Bool.false_ne_true : ¬(partialScan D θ i).stopped = true)]
    rw [dite_eq_left (show (partialScan D θ i).cursor.val + 1 < p.n from hk)]
    simp only [partialScan, i, he, Finset.sum_insert hn, hc, Bool.decide_and]
    congr 1
    change _ + increment D θ i = _
    rw [add_comm]

private lemma fresh (θ : Space p.d) : partialScan D θ 0 = ⟨θ, 0, 0, true, false⟩ := by
  simp [partialScan, earlier, correct]

private lemma full_pass (θ : Space p.d) :
    let s := (step D)^[p.n.val] (partialScan D θ 0)
    (s.stopped = true ∧ s.point = θ ∧ correct D θ p.n) ∨
      s = partialScan D (θ + (stepSize p / p.n) • ∑ i, increment D θ i) 0 ∧ ¬correct D θ p.n := by
  classical
  let i : Fin p.n := ⟨p.n.val - 1, by have := p.n.pos; omega⟩
  have hi : i.val + 1 = p.n := by dsimp [i]; have := p.n.pos; omega
  have he : earlier p (i.val + 1) = Finset.univ := by
    ext j; simp [earlier, hi]
  have hsum : (∑ j ∈ earlier p i.val, increment D θ j) + increment D θ i =
      ∑ j, increment D θ j := by
    rw [← he, prefix_succ, Finset.sum_insert (by simp [earlier]), add_comm]
  have hc := correct_succ D θ i
  rw [hi] at hc
  have hn : ¬ i.val + 1 < p.n := by omega
  have heq : (step D)^[p.n.val] (partialScan D θ 0) = step D (partialScan D θ i) := by
    calc
      _ = (step D)^[i.val+1] (partialScan D θ 0) := congrArg (fun t => (step D)^[t] (partialScan D θ 0)) hi.symm
      _ = _ := by rw [Function.iterate_succ_apply', scanned]
  rw [heq]
  change ((step D (partialScan D θ i)).stopped = true ∧ _ ∧ _) ∨ _
  by_cases good : correct D θ p.n
  · left
    obtain ⟨before, last⟩ := hc.mp good
    simp +instances [step, advance, before, last, hi, good]
  · right
    have check : ¬(correct D θ i.val ∧ 0 < (answer p D (i,θ)).margin) := fun h => good (hc.mpr h)
    refine ⟨?_, by simpa only [hi] using good⟩
    rw [fresh]
    simp +instances only [step, advance, partialScan, Bool.false_eq_true, ite_false,
      Bool.and_eq_true, decide_eq_true_eq, check, hn, dite_false]
    congr 1
    exact congrArg (fun g => θ + (stepSize p / p.n) • g) hsum

private lemma frozen {s : Scan p} (hs : s.stopped = true) (t : ℕ) : (step D)^[t] s = s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih]; simp [step, advance, hs]

private lemma clock (G : Geometry p D) (k : ℕ) :
    let s := (step D)^[k * p.n] (start p)
    (s.stopped = true ∧ correct D s.point p.n) ∨
      s = partialScan D (physical (state D (stepSize p) k)) 0 := by
  induction k with
  | zero =>
    right
    simp only [Nat.zero_mul, Function.iterate_zero_apply]
    change start p = partialScan D (physical CyclicLogisticTrajectory.initial) 0
    rw [physical_initial, fresh]; rfl
  | succ k ih =>
    let s := (step D)^[k * p.n] (start p)
    have he : (step D)^[(k+1)*p.n] (start p) = (step D)^[p.n.val] s := by
      rw [Nat.succ_mul, Nat.add_comm, Function.iterate_add_apply]
    rw [he]
    rcases ih with ⟨hs,hc⟩ | hp
    · left; rw [frozen D hs]; exact ⟨hs,hc⟩
    · change s = _ at hp
      rw [hp]
      rcases full_pass D (physical (state D (stepSize p) k)) with ⟨hs,hp',hc⟩ | ⟨hp',_⟩
      · left; exact ⟨hs,hp'.symm ▸ hc⟩
      · right; rwa [physical_update D G]

lemma success (hp : spec.valid p) (G : Geometry p D) :
    let s := (step D)^[(horizon p + 1) * p.n] (start p)
    correct D s.point p.n := by
  have t := tuned p hp
  obtain ⟨hμ, hμ', hκ, _, hρ, _⟩ := hp
  obtain ⟨u, hu, hsep⟩ := G.separable
  obtain ⟨k,hk,h⟩ := CyclicLogisticTrajectory.hits_separator (sumFeature ∘ D) (diffFeature ∘ D)
    p.n.pos t.positive t.small hμ hμ' hκ hρ G.sum_bound G.diff_bound G.nonseparable u hu hsep
    t.curvature _ t.energy t.signal
  let s := (step D)^[k * p.n] (start p)
  let θ := physical (state D (stepSize p) k)
  have hall : correct D θ p.n := fun i _ => by
    change 0 < LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv _ _ _
    rw [physical_score _ _ (aligned_state D G (stepSize p) k i)]
    exact h i
  have hf : ((step D)^[p.n.val] s).stopped = true ∧ correct D ((step D)^[p.n.val] s).point p.n := by
    rcases clock D G k with ⟨hs,hc⟩ | he
    · rw [frozen D hs]; exact ⟨hs,hc⟩
    · change s = partialScan D θ 0 at he
      rw [he]
      rcases full_pass D θ with ⟨hs,hp',hc⟩ | ⟨_,hn⟩
      · exact ⟨hs,hp'.symm ▸ hc⟩
      · exact False.elim (hn hall)
  have he : (horizon p + 1) * p.n.val = ((horizon p - k) * p.n + p.n) + k * p.n := by
    rw [show horizon p + 1 = (horizon p - k + 1) + k by omega, Nat.add_mul, Nat.succ_mul]
  simp only [he, Function.iterate_add_apply]
  rw [frozen D hf.1]
  exact hf.2

lemma output_correct (hp : spec.valid p) (G : Geometry p D) (O : Oracle (Query p)
    (LongTails.Setups.ManySampleConvolutionalPerceptron.Reply p.d))
    (ha : ∀ history q seed, O.answer history (0,q) seed = answer p D q)
    (ξ : (k : ℕ) → O.Seed k) :
    correct D (output p O ((horizon p + 1) * p.n) ξ) p.n := by
  have he := (execute_eq_of_answer_eq O (answer p D) ha (algorithm p) ((horizon p + 1) * p.n) () ξ).trans
    (execute_iterate (answer p D) (algorithm p) ((horizon p + 1) * p.n) ())
  unfold output
  rw [he]
  exact success D hp G

end LongTails.Proofs.CyclicLogisticExecution
