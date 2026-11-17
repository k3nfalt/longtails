import LongTails.Proofs.RelativeHessianOracle

namespace LongTails.Proofs.RelativeHessianSimulation

open scoped RealInnerProductSpace
open RelativeHessianOracle

variable {d m : ℕ} {S : Type*}

noncomputable def axes (π : Fin (m + 1) ↪ Fin d) (j : Fin (m + 1)) : EuclideanSpace ℝ (Fin d) :=
  EuclideanSpace.single (π j) 1

lemma axes_inner (π : Fin (m + 1) ↪ Fin d) (j : Fin (m + 1)) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪axes π j, x⟫ = x (π j) := by simp [axes, EuclideanSpace.inner_single_left]

lemma axes_orthonormal (π : Fin (m + 1) ↪ Fin d) : Orthonormal ℝ (axes π) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  simp [axes, EuclideanSpace.inner_single_left, π.injective.eq_iff]

noncomputable def simulate (π : Fin (m + 1) ↪ Fin d)
    (query : S → EuclideanSpace ℝ (Fin d)) (update : S → Reply (EuclideanSpace ℝ (Fin d)) → S)
    (initial : S) : ℕ → S
  | 0 => initial
  | t + 1 => let state := simulate π query update initial t
      update state (jet (prefixFunction (axes π) (t + 1)) (query state))

noncomputable def actual (π : Fin (m + 1) ↪ Fin d)
    (query : S → EuclideanSpace ℝ (Fin d)) (update : S → Reply (EuclideanSpace ℝ (Fin d)) → S)
    (initial : S) : ℕ → S
  | 0 => initial
  | t + 1 => let state := actual π query update initial t
      update state (jet (RelativeHessianLocalized.value (axes π)) (query state))

lemma simulate_prefix (π ρ : Fin (m + 1) ↪ Fin d)
    (query : S → EuclideanSpace ℝ (Fin d)) (update : S → Reply (EuclideanSpace ℝ (Fin d)) → S)
    (initial : S) (t : ℕ) (hπ : ∀ j, j.val < t + 1 → π j = ρ j) :
    simulate π query update initial t = simulate ρ query update initial t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hs := ih (fun j hj => hπ j (by omega))
    have hf : prefixFunction (axes π) (t + 1) = prefixFunction (axes ρ) (t + 1) :=
      partial_prefix _ _ _ (fun j hj => by simp only [axes, hπ j hj])
    simp only [simulate, hs, hf]

lemma coupling (π : Fin (m + 1) ↪ Fin d)
    (query : S → EuclideanSpace ℝ (Fin d)) (update : S → Reply (EuclideanSpace ℝ (Fin d)) → S)
    (initial : S) (T : ℕ)
    (hgood : ∀ t < T, ‖query (simulate π query update initial t)‖ ≤ 2 * RelativeHessianLocalized.radius m →
      ∀ j : Fin (m + 1), t < j.val → |query (simulate π query update initial t) (π j)| ≤ 1 / 20) :
    actual π query update initial T = simulate π query update initial T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have hs := ih (fun t ht => hgood t (by omega))
    have hj : jet (RelativeHessianLocalized.value (axes π)) (query (simulate π query update initial T)) =
        jet (prefixFunction (axes π) (T + 1)) (query (simulate π query update initial T)) := by
      apply jet_prequery_bounded
      intro hx i hi
      rw [axes_inner]
      have h := hgood T (by omega) hx i.castSucc (by simpa using hi)
      linarith
    simp only [actual, hs, simulate, hj]

end LongTails.Proofs.RelativeHessianSimulation
