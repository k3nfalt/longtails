import LongTails.Proofs.ValidatedMuonExecution

namespace LongTails.Proofs.MuonContract

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.ValidatedMuon
open LongTails.Setups.FiniteVarianceSpectralSmooth (muonIterate replyState FollowsMuon)

lemma training_states {m n T b k q : ℕ} (α η ρ : ℝ) (x0 : Space m n)
    (seed : Fin (q + 1) → Fin (T + 1)) (reply : ℕ → Space m n) (hb : 0 < b) :
    let A := validatedMuon α η ρ T b k q x0
    let path := muonIterate α η x0 reply
    let points := fun i : Fin (T + 1) => (path i).1
    (∀ t : Fin (T + 1), (A.query (replyState A seed reply t)).2 = points t) ∧
    replyState A seed reply (T + 1) =
      .validating (fun i => points (seed i)) ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨0, hb⟩ 0
        (fun _ => 0) (fun _ => 0) := by
  dsimp only
  let A := validatedMuon α η ρ T b k q x0
  let path := muonIterate α η x0 reply
  let points := fun i : Fin (T + 1) => (path i).1
  let saved := fun t (i : Fin (T + 1)) => if i.val < t then points i else x0
  have hsave (t : ℕ) (ht : t < T + 1) :
      Function.update (saved t) ⟨t, ht⟩ (path t).1 = saved (t + 1) := by
    funext i
    by_cases hi : i = ⟨t, ht⟩
    · subst i; simp [saved, points]
    · have hv : i.val ≠ t := fun h => hi (Fin.ext h)
      rw [Function.update_of_ne hi]
      dsimp only [saved]
      by_cases hlt : i.val < t
      · simp [hlt, show i.val < t + 1 by omega]
      · simp [hlt, show ¬ i.val < t + 1 by omega]
  have hstate (t : ℕ) (ht : t < T + 1) :
      replyState A seed reply t =
        .training seed ⟨t, ht⟩ (path t).1 (path t).2 (saved t) := by
    induction t with
    | zero => simp [replyState, A, validatedMuon, validatedMuonDirect, path, muonIterate, saved]
    | succ t ih =>
      change A.update (replyState A seed reply t) (reply t) = _
      rw [ih (by omega)]
      have hn : t + 1 ≠ T + 1 := by omega
      simp only [A, validatedMuon, validatedMuonDirect, hn, dite_false]
      rw [hsave]
      rfl
  refine ⟨fun t => ?_, ?_⟩
  · change (A.query (replyState A seed reply t)).2 = _
    rw [hstate t t.isLt]
    rfl
  · change replyState A seed reply (T + 1) = _
    change A.update (replyState A seed reply T) (reply T) = _
    rw [hstate T (by omega)]
    simp only [A, validatedMuon, validatedMuonDirect, dite_true, hb]
    rw [hsave]
    have hfinal : saved (T + 1) = points := by
      funext i; simp [saved, i.isLt]
    rw [hfinal]

lemma validation_queries {m n T b k q : ℕ} (α η ρ : ℝ) (x0 : Space m n)
    (seed : Fin (q + 1) → Fin (T + 1)) (reply : ℕ → Space m n) (hb : 0 < b)
    (sources : Fin (q + 1) → Space m n)
    (hstart : replyState (validatedMuon α η ρ T b k q x0) seed reply (T + 1) =
      .validating sources ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨0, hb⟩ 0 (fun _ => 0) (fun _ => 0)) :
    ∀ (i : Fin (q + 1)) (j : Fin (k + 1)) (u : Fin b),
      ((validatedMuon α η ρ T b k q x0).query
        (replyState (validatedMuon α η ρ T b k q x0) seed reply
          (T + 1 + b * (k + 1) * i + b * j + u))).2 = sources i := by
  let A := validatedMuon α η ρ T b k q x0
  let state := replyState A seed reply
  let offset := fun (i j : ℕ) => T + 1 + b * (k + 1) * i + b * j
  let atSample := fun (i : Fin (q + 1)) (j : Fin (k + 1)) (u : Fin b) =>
    ∃ acc means reps, state (offset i j + u) = .validating sources i j u acc means reps
  have samples (i : Fin (q + 1)) (j : Fin (k + 1))
      (hzero : atSample i j ⟨0, hb⟩) : ∀ u : Fin b, atSample i j u := by
    intro u
    rcases u with ⟨u, hu⟩
    induction u with
    | zero => exact hzero
    | succ u ih =>
      obtain ⟨acc, means, reps, he⟩ := ih (by omega)
      have hs : u + 1 < b := hu
      refine ⟨acc + reply (offset i j + u), means, reps, ?_⟩
      change state (offset i j + (u + 1)) = _
      rw [show offset i j + (u + 1) = (offset i j + u) + 1 by omega]
      change A.update (state (offset i j + u)) (reply (offset i j + u)) = _
      rw [he]
      simp [A, validatedMuon, validatedMuonDirect, hs]
  have next (i : Fin (q + 1)) (j : Fin (k + 1))
      (hzero : atSample i j ⟨0, hb⟩) :
      ∃ acc means reps, state (offset i j + b) =
        A.update (.validating sources i j ⟨b - 1, by omega⟩ acc means reps)
          (reply (offset i j + (b - 1))) := by
    obtain ⟨acc, means, reps, he⟩ := samples i j hzero ⟨b - 1, by omega⟩
    refine ⟨acc, means, reps, ?_⟩
    rw [show offset i j + b = (offset i j + (b - 1)) + 1 by omega]
    change A.update (state (offset i j + (b - 1))) _ = _
    rw [he]
  have batches (i : Fin (q + 1)) (hzero : atSample i ⟨0, by omega⟩ ⟨0, hb⟩) :
      ∀ j : Fin (k + 1), atSample i j ⟨0, hb⟩ := by
    rintro ⟨j, hj⟩
    induction j with
    | zero => exact hzero
    | succ j ih =>
      obtain ⟨acc, means, reps, he⟩ := next i ⟨j, by omega⟩ (ih (by omega))
      have hidx : offset i (j + 1) = offset i j + b := by dsimp [offset]; ring
      dsimp only [atSample]
      simp only [Nat.add_zero]
      rw [hidx, he]
      simp only [A, validatedMuon, validatedMuonDirect,
        show ¬ (b - 1 + 1 < b) by omega, dite_false, hj, dite_true]
      exact ⟨0, _, _, rfl⟩
  have candidates : ∀ i : Fin (q + 1), atSample i ⟨0, by omega⟩ ⟨0, hb⟩ := by
    rintro ⟨i, hi⟩
    induction i with
    | zero =>
      refine ⟨0, (fun _ => 0), (fun _ => 0), ?_⟩
      simpa [state, A, offset] using hstart
    | succ i ih =>
      obtain ⟨acc, means, reps, he⟩ := next ⟨i, by omega⟩ ⟨k, by omega⟩
        (batches ⟨i, by omega⟩ (ih (by omega)) ⟨k, by omega⟩)
      have hidx : offset (i + 1) 0 = offset i k + b := by dsimp [offset]; ring
      dsimp only [atSample]
      simp only [Nat.add_zero]
      rw [hidx, he]
      simp only [A, validatedMuon, validatedMuonDirect,
        show ¬ (b - 1 + 1 < b) by omega, dite_false,
        show ¬ (k + 1 < k + 1) by omega, hi, dite_true]
      exact ⟨0, _, _, rfl⟩
  intro i j u
  obtain ⟨acc, means, reps, he⟩ := samples i j (batches i (candidates i) j) u
  change (A.query (state (offset i j + u))).2 = _
  rw [he]
  rfl

lemma validatedMuon_follows {m n : ℕ} (α η ρ : ℝ) (T b k q : ℕ) (x0 : Space m n)
    (hb : 0 < b) : FollowsMuon α η ρ T b k q x0 (validatedMuon α η ρ T b k q x0) := by
  refine ⟨id, measurable_id, Measure.map_id, ?_⟩
  intro seed reply
  dsimp only [id_eq]
  obtain ⟨htrain, hstart⟩ := training_states α η ρ x0 seed reply hb
  refine ⟨htrain, validation_queries α η ρ x0 seed reply hb _ hstart, ?_⟩
  intro extra
  let A := validatedMuon α η ρ T b k q x0
  have hrun (fuel call : ℕ) :
      QueryPlan.sampledEval (fun _ t => reply t) id
        (MuonSimulation.resumeMuonPlan α η ρ x0 fuel (replyState A seed reply call)) call =
      A.output (replyState A seed reply (call + fuel)) := by
    induction fuel generalizing call with
    | zero => rfl
    | succ fuel ih =>
      rw [MuonSimulation.resumeMuonPlan, QueryPlan.sampledEval]
      change QueryPlan.sampledEval (fun _ t => reply t) id
        (MuonSimulation.resumeMuonPlan α η ρ x0 fuel (replyState A seed reply (call + 1)))
        (call + 1) = _
      rw [ih]
      congr 2
      omega
  have hpath (t : ℕ) : trajectory α η (fun _ j => reply j) id (x0, 0) 0 t =
      muonIterate α η x0 reply t := by
    induction t with
    | zero => rfl
    | succ t ih => simp only [trajectory, muonIterate, ih, Nat.zero_add, id_eq]
  have hh := hrun (T + 1 + (b * (k + 1) * (q + 1) + extra)) 0
  simp only [Nat.zero_add, replyState] at hh
  rw [show T + 1 + b * (k + 1) * (q + 1) + extra =
    T + 1 + (b * (k + 1) * (q + 1) + extra) by omega, ← hh]
  rw [MuonSimulation.sampledEval_training_resume α η ρ x0 (fun _ j => reply j) id seed extra 0]
  rw [MuonValidationSimulation.sampledEval_resumeMuonPlan_validation]
  rw [ValidatedMuonExecution.sampledEval_validationPlan, MuonProcess.sampledEval_trainingPlan]
  simp only [hpath, ValidatedMuonExecution.sampledEval_batchMeanPlan, id_eq, Nat.zero_add]


end LongTails.Proofs.MuonContract
