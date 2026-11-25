import LongTails.Algorithms.SpatialRankingLogistic
import LongTails.Proofs.Execution

open OracleTemplate

namespace LongTails.Proofs.SpatialRankingExecution

open LongTails.Setups.SpatialRankingLogistic
open LongTails.Algorithms.SpatialRankingLogistic

noncomputable def term (p : Params) (D : Items p) (θ : Point p) (k : ℕ) : Point p :=
  answer p D ((decide (p.n ≤ k), k % p.n), θ)

noncomputable def batch (p : Params) (D : Items p) (θ : Point p) : Point p :=
  θ + (2:ℝ) • ∑ k ∈ Finset.range (2*p.n), term p D θ k

noncomputable def step (p : Params) (D : Items p) (s : Scan p) : Scan p :=
  scanUpdate p .joint (4*p.n) s (answer p D (scanQuery p s))

lemma scan_prefix (p : Params) (D : Items p) (θ : Point p) {k : ℕ} (hk : k < 2*p.n) :
    (step p D)^[k] ⟨θ,0,0⟩ = ⟨θ,k,∑ i ∈ Finset.range k, term p D θ i⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp [step, scanUpdate, scanQuery, term, Finset.sum_range_succ, Nat.ne_of_lt hk]

lemma pass (p : Params) (D : Items p) (θ : Point p) (hn : 0 < p.n) :
    (step p D)^[2*p.n] ⟨θ,0,0⟩ = ⟨batch p D θ,0,0⟩ := by
  let k := 2*p.n-1
  have he : k+1=2*p.n := by dsimp [k]; omega
  conv_lhs => rw [← he]
  rw [Function.iterate_succ_apply', scan_prefix p D θ (by omega)]
  have hs : (∑ i ∈ Finset.range k, term p D θ i) + term p D θ k =
      ∑ i ∈ Finset.range (2*p.n), term p D θ i := by rw [← Finset.sum_range_succ, he]
  have hc : (4*(p.n:ℝ)) * ((2*p.n:ℕ):ℝ)⁻¹ = 2 := by
    push_cast
    field_simp
    norm_num
  simp only [step, scanUpdate, he, ite_true]
  change Scan.mk (θ + (4*(p.n:ℝ)) • (((2*p.n:ℕ):ℝ)⁻¹ •
    ((∑ i ∈ Finset.range k, term p D θ i) + term p D θ k))) 0 0 = _
  rw [hs, smul_smul, hc]
  rfl

lemma passes (p : Params) (D : Items p) (θ : Point p) (hn : 0 < p.n) (k : ℕ) :
    (step p D)^[k*(2*p.n)] ⟨θ,0,0⟩ = ⟨(batch p D)^[k] θ,0,0⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.add_comm, Function.iterate_add_apply, ih, pass _ _ _ hn,
      Function.iterate_succ_apply']

lemma output_passes (p : Params) (D : Items p) (O : Oracle (Query p) (Point p))
    (hO : ∀ hist q ω, O.answer hist (0,q) ω = answer p D q) (hn : 0 < p.n)
    (k : ℕ) (ω : (i : ℕ) → O.Seed i) :
    output p O (k*(2*p.n)) ω = (batch p D)^[k] ((1,0),0) := by
  refine ((execute_eq_of_answer_eq O (answer p D) hO (algorithm p) (k*(2*p.n)) () ω).trans
    (execute_iterate (answer p D) (algorithm p) (k*(2*p.n)) ())).trans ?_
  change ((step p D)^[k*(2*p.n)] ⟨((1,0),0),0,0⟩).point = _
  rw [passes p D _ hn]

end LongTails.Proofs.SpatialRankingExecution
