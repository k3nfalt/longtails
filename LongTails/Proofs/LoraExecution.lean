import LongTails.Algorithms.LoraSilver
import LongTails.Proofs.Execution
import LongTails.Proofs.SilverTrace

namespace LongTails.Proofs.LoraExecution

open OracleTemplate LongTails.Algorithms.LoraGd
open LongTails.Algorithms.SilverSchedule LongTails.Proofs.SilverTrace
open LongTails.Proofs.SilverCertificate LongTails.Setups.LocalSmoothStronglyConvexLora

lemma iterate_schedule {m n r : ℕ} (G : MatrixSpace m n → MatrixSpace m n)
    (hs : List ℝ) (L : ℝ) (x₀ : Factors m n r) :
    ∀ k, k ≤ hs.length →
      (fun state : ℕ × Factors m n r =>
        (state.1 + 1, state.2 - (hs[state.1]?.getD 1 / L) • pullback state.2 (G (product state.2))))^[k]
          (0, x₀) =
        (k, run (fun x => (1 / L) • pullback x (G (product x))) (hs.take k) x₀) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hlt : k < hs.length := by omega
    rw [Function.iterate_succ_apply', ih (by omega), List.take_succ_eq_append_getElem hlt,
      run_append]
    simp only [List.getElem?_eq_getElem hlt, Option.getD_some, run, smul_smul, div_eq_mul_inv, one_mul]

lemma execute_schedule {m n r : ℕ} (G : MatrixSpace m n → MatrixSpace m n)
    (hs : List ℝ) (L : ℝ) (x₀ : Factors m n r) :
    execute { answer := fun _ query _ => G query.2 }
      (LongTails.Algorithms.LoraGd.method (fun k => hs[k]?.getD 1 / L) x₀)
      (fun _ => hs.length) =
      run (fun x => (1 / L) • pullback x (G (product x))) hs x₀ := by
  erw [execute_iterate]
  change ((fun state : ℕ × Factors m n r =>
    (state.1 + 1, state.2 - (hs[state.1]?.getD 1 / L) • pullback state.2 (G (product state.2))))^[hs.length]
      (0, x₀)).2 = _
  rw [iterate_schedule G hs L x₀ hs.length le_rfl, List.take_length]

lemma schedule_positive (p : Params) : ∀ h ∈ LongTails.Algorithms.LoraSilver.schedule p, 0 < h := by
  intro h hh
  simp only [LongTails.Algorithms.LoraSilver.schedule, List.mem_append, List.mem_replicate,
    List.mem_flatten] at hh
  rcases hh with ⟨_, rfl⟩ | ⟨l, hl, hh⟩
  · norm_num
  · obtain ⟨_, rfl⟩ := hl
    exact steps_positive _ _ hh

lemma getD_positive (hs : List ℝ) (hpos : ∀ h ∈ hs, 0 < h) (k : ℕ) :
    0 < hs[k]?.getD 1 := by
  by_cases hk : k < hs.length
  · rw [List.getElem?_eq_getElem hk, Option.getD_some]
    exact hpos _ (List.getElem_mem hk)
  · simp [List.getElem?_eq_none (Nat.le_of_not_gt hk)]

lemma allowed (p : Params) (hp : spec.valid p) :
    gdFamily p (LongTails.Algorithms.LoraSilver.method p) := by
  obtain ⟨_, _, _, hμ, hμρ, hs, hsR, _⟩ := hp
  have hρ : 0 < p.ρ := hμ.trans_le hμρ
  have hR : 0 < p.R := hs.trans_le hsR
  refine ⟨Prod.snd, (fun state _ => (LongTails.Algorithms.LoraSilver.schedule p)[state.1]?.getD 1 /
    (8 * p.ρ * p.R ^ 2)), (fun _ => rfl), ?_, (fun _ => rfl), (fun _ _ => rfl), (fun _ => rfl)⟩
  intro state _
  exact div_pos (getD_positive _ (schedule_positive p) state.1) (by positivity)

lemma schedule_length (p : Params) :
    (LongTails.Algorithms.LoraSilver.schedule p).length =
      LongTails.Algorithms.LoraSilver.warmup p +
        (2 ^ LongTails.Algorithms.LoraSilver.depth p - 1) * LongTails.Algorithms.LoraSilver.epochs p := by
  simp only [LongTails.Algorithms.LoraSilver.schedule, List.length_append, List.length_replicate,
    List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul]
  have hh := steps_length (LongTails.Algorithms.LoraSilver.depth p)
  have he : (steps (LongTails.Algorithms.LoraSilver.depth p)).length =
      2 ^ LongTails.Algorithms.LoraSilver.depth p - 1 := by omega
  rw [he]
  ring

lemma run_replicate {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : E → E) (h : ℝ) (n : ℕ) (x : E) :
    run g (List.replicate n h) x = (fun u => u - h • g u)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, run, ih, Function.iterate_succ_apply]

lemma run_blocks {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → E) (hs : List ℝ) (n : ℕ) (x : E) :
    run g (List.replicate n hs).flatten x = (run g hs)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, run_append, ih, Function.iterate_succ_apply]

end LongTails.Proofs.LoraExecution
