import LongTails.Proofs.RelativeHessianSimulation
import LongTails.Proofs.SmoothConvexFiniteHiding

namespace LongTails.Proofs.RelativeHessianExposure

open scoped RealInnerProductSpace BigOperators
open Classical RelativeHessianSimulation SmoothConvexFiniteHiding
open FiniteSumNondualLowerHiding FiniteSumNondualLowerExposure FiniteSumNondualLowerAveraging

variable {d m : ℕ} {S : Type*}

noncomputable def observation (query output : S → EuclideanSpace ℝ (Fin d))
    (T : ℕ) (j : Fin (T + 1)) (state : S) : EuclideanSpace ℝ (Fin d) :=
  if j.val < T then query state else output state

noncomputable def observe (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d)) → S)
    (initial : S) (T : ℕ) (j : Fin (T + 1)) (π : Fin (m + 1) ↪ Fin d) : EuclideanSpace ℝ (Fin d) :=
  observation query output T j (simulate π query update initial j.val)

noncomputable def bad (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d)) → S)
    (initial : S) (T : ℕ) (π : Fin (m + 1) ↪ Fin d) : Prop :=
  ∃ j : Fin (T + 1), 0 < hits
    (largeSet (2 * RelativeHessianLocalized.radius m) (1 / 20) (observe query output update initial T j π))
    ((List.ofFn π).drop (j.val + 1))

lemma bad_count (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d)) → S)
    (initial : S) (T : ℕ) (hT : T < m) (D : ℝ) (hD : 0 ≤ D) (hd : D + (m + 1 : ℕ) ≤ d) :
    D * (((distinctWords (m + 1) (Finset.univ : Finset (Fin d))).filter
      (fun w => ∃ j : Fin (T + 1), ∃ π : Fin (m + 1) ↪ Fin d, List.ofFn π = w ∧
        0 < hits (largeSet (2 * RelativeHessianLocalized.radius m) (1 / 20)
          (observe query output update initial T j π)) (w.drop (j.val + 1)))).card : ℝ) ≤
      (T + 1 : ℕ) * (m + 1 : ℕ) * ((2 * RelativeHessianLocalized.radius m) ^ 2 / (1 / 20) ^ 2) *
        (distinctWords (m + 1) (Finset.univ : Finset (Fin d))).card := by
  classical
  have h := bounded_prefix_bad_count (2 * RelativeHessianLocalized.radius m) (1 / 20) D
    (mul_nonneg (by norm_num) (RelativeHessianLocalized.radius_pos m).le) (by norm_num) hD hd
    (fun j : Fin (T + 1) => j.val + 1) (fun j => by omega)
    (observe query output update initial T)
    (fun j π ρ hπ => by
      unfold observe
      rw [simulate_prefix π ρ query update initial j.val hπ])
  simpa using h

lemma not_bad_small (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d)) → S)
    (initial : S) (T : ℕ) (π : Fin (m + 1) ↪ Fin d)
    (hn : ¬bad query output update initial T π) (j : Fin (T + 1))
    (hx : ‖observe query output update initial T j π‖ ≤ 2 * RelativeHessianLocalized.radius m)
    (i : Fin (m + 1)) (hi : j.val < i.val) :
    |observe query output update initial T j π (π i)| ≤ 1 / 20 := by
  apply not_largeSet_small _ _ _ hx
  intro hm
  apply hn
  exact ⟨j, hits_drop_positive π _ _ i (by omega) hm⟩

lemma good_gradient (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d)) → S)
    (initial : S) (T : ℕ) (hT : T < m) (π : Fin (m + 1) ↪ Fin d)
    (hn : ¬bad query output update initial T π) :
    7 / 10 ≤ ‖gradient (RelativeHessianLocalized.value (axes π)) (output (actual π query update initial T))‖ := by
  have hs : actual π query update initial T = simulate π query update initial T := by
    apply coupling
    intro t ht hx i hi
    let j : Fin (T + 1) := ⟨t, by omega⟩
    have ho : observe query output update initial T j π = query (simulate π query update initial t) := by
      simp [observe, observation, j, ht]
    have h := not_bad_small query output update initial T π hn j (by simpa only [ho] using hx) i hi
    simpa only [ho] using h
  rw [hs]
  let x := output (simulate π query update initial T)
  by_cases hx : ‖x‖ ≤ 2 * RelativeHessianLocalized.radius m
  · let j : Fin (T + 1) := ⟨T, by omega⟩
    let i : Fin (m + 1) := ⟨T + 1, by omega⟩
    have ho : observe query output update initial T j π = x := by simp [observe, observation, j, x]
    have h := not_bad_small query output update initial T π hn j (by simpa only [ho] using hx) i (by dsimp [j, i]; omega)
    apply RelativeHessianLocalized.hidden_gradient (axes_orthonormal π)
    refine ⟨i, ?_⟩
    rw [axes_inner]
    rw [ho] at h
    linarith
  · have hr := RelativeHessianLocalized.radius_pos m
    have hg := RelativeHessianLocalized.outside_gradient (axes_orthonormal π) x (by linarith)
    have hR := RelativeHessianLocalized.radius_large m
    change 7 / 10 ≤ ‖gradient (RelativeHessianLocalized.value (axes π)) x‖
    linarith

end LongTails.Proofs.RelativeHessianExposure
