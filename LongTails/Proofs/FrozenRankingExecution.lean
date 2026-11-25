import LongTails.Proofs.FrozenRankingPropagation

open OracleTemplate

namespace LongTails.Proofs.FrozenRankingExecution

open LongTails.Setups.SpatialRankingLogistic
open LongTails.Proofs.SpatialRankingExecution
open LongTails.Proofs.SpatialRankingGradients
open LongTails.Proofs.FrozenRankingPropagation

lemma sum_reply (p : Params) (D : Items p) (θ : Point p) :
    ∑ i ∈ Finset.range (2*p.n), term p D θ i = adjoint θ (force p D θ false + force p D θ true) := by
  have h := add_left_cancel (show θ + (2:ℝ) • (∑ i ∈ Finset.range (2*p.n), term p D θ i) =
      θ + (2:ℝ) • adjoint θ (force p D θ false + force p D θ true) from batch_eq p D θ)
  apply_fun ((1/2:ℝ) • ·) at h
  simpa [smul_smul] using h

lemma execution_fails {p : Params} {D : Items p} (hn : 8 ≤ p.n) (hD : Geometry p D)
    (A : Algorithm (Query p) (Point p) (Point p)) (hA : family p .frozen A)
    (K : ℕ) (hK : K ≤ p.n * (p.n-3)) (ω : A.Seed) :
    ¬Separates p D (execute { answer := fun _ query _ => answer p D query.2 } A (fun _ => K) ω) := by
  obtain ⟨view, taps, rate, hrate, _, start, query, update, out⟩ := hA
  let f (s : A.State) := A.update s (answer p D (A.query s).2)
  let N := 2*p.n
  have hN : 0 < N := by dsimp [N]; omega
  have next (s : A.State) : view (f s) = scanUpdate p .frozen
      (rate s (answer p D (scanQuery p (view s)))) (view s) (answer p D (scanQuery p (view s))) := by
    simp [f, query, update]
  have scanPart (s : A.State) (θ : Point p) (h : view s = ⟨θ,0,0⟩) (k : ℕ) (hk : k < N) :
      view (f^[k] s) = ⟨θ,k,∑ j ∈ Finset.range k, term p D θ j⟩ := by
    induction k with
    | zero => simpa using h
    | succ k ih =>
      rw [Function.iterate_succ_apply', next, ih (by omega)]
      simp [scanUpdate, scanQuery, term, Finset.sum_range_succ, show k+1 ≠ 2*p.n from Nat.ne_of_lt hk]
  have pass (s : A.State) (θ : Point p) (h : view s = ⟨θ,0,0⟩) :
      ∃ r : ℝ, 0 ≤ r ∧ view (f^[N] s) = ⟨frozenBatch p D θ r,0,0⟩ := by
    let k := N-1
    have he : k+1=N := by dsimp [k]; omega
    let t := f^[k] s
    let r := rate t (answer p D (scanQuery p (view t)))
    refine ⟨r * (N:ℝ)⁻¹, mul_nonneg (hrate _ _).le (by positivity), ?_⟩
    have hk := scanPart s θ h k (by omega)
    have hp : r = rate t (term p D θ k) := by
      unfold r
      change rate (f^[k] s) (answer p D (scanQuery p (view (f^[k] s)))) = _
      rw [hk]
      rfl
    conv_lhs => rw [← he, Function.iterate_succ_apply', next, hk]
    have hs : (∑ j ∈ Finset.range k, term p D θ j) + term p D θ k =
        adjoint θ (force p D θ false + force p D θ true) := by
      rw [← Finset.sum_range_succ, he, sum_reply]
    simp only [scanUpdate, show k+1 = 2*p.n from he, ite_true]
    change Scan.mk (θ + rate t (term p D θ k) •
      ((0,0),((N:ℝ)⁻¹ • ((∑ j ∈ Finset.range k, term p D θ j) + term p D θ k)).2)) 0 0 = _
    rw [hs, ← hp]
    congr 1
    apply Prod.ext
    · simp [frozenBatch]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_smul]
      rfl
  have inv (t : ℕ) : ∃ θ, view (f^[t*N] (A.initial ω)) = ⟨θ,0,0⟩ ∧ Interior p D (taps ω) t θ := by
    induction t with
    | zero => exact ⟨_, by simpa using start ω, initial_interior _ _ _⟩
    | succ t ih =>
      obtain ⟨θ,hs,hh⟩ := ih
      obtain ⟨r,hr,he⟩ := pass _ θ hs
      refine ⟨_, ?_, interior_step hD _ _ _ _ hr hh⟩
      simpa [Nat.succ_mul, Nat.add_comm (t*N) N, Function.iterate_add_apply] using he
  let t := K/N
  let k := K%N
  obtain ⟨θ,hs,hh⟩ := inv t
  have htail := scanPart _ θ hs k (Nat.mod_lt _ hN)
  have he : k + t*N = K := by simpa [k, t, Nat.mul_comm] using Nat.mod_add_div K N
  have ht : 2*t+2 < p.n := by
    have hP : (2*t)*p.n ≤ (p.n-3)*p.n := by
      calc (2*t)*p.n = t*N := by dsimp [N]; ring
           _ ≤ K := by omega
           _ ≤ _ := by rwa [Nat.mul_comm] at hK
    have hlt := Nat.le_of_mul_le_mul_right hP (by omega : 0 < p.n)
    omega
  rw [execute_iterate, out]
  change ¬Separates p D (view (f^[K] (A.initial ω))).point
  rw [← he, Function.iterate_add_apply, htail]
  exact fails_inside _ t θ hh ht

end LongTails.Proofs.FrozenRankingExecution
