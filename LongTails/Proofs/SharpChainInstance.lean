import LongTails.Proofs.SharpChainGeometry

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.SharpChainInstance

open MintyChainGeometry SharpChainGeometry

variable {d k : ℕ}

set_option hygiene false in
local notation "E" => EuclideanSpace ℝ (Fin d)

section Selection

variable (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : E)

lemma best_spec : ∀ t, t ≤ k → ∃ m : Fin (k + 1), m.val ≤ t ∧
    bestUpTo μ0 D π u t = chainPiece μ0 D π m u ∧
    ∀ m' : Fin (k + 1), m'.val ≤ t → chainVal μ0 D π m' u ≤ (bestUpTo μ0 D π u t).1 := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨⟨0, Nat.succ_pos k⟩, le_rfl, rfl, ?_⟩
    intro m' hm'
    have : m' = ⟨0, Nat.succ_pos k⟩ := Fin.ext (Nat.le_zero.mp hm')
    subst this
    exact le_rfl
  | succ t ih =>
    intro ht
    obtain ⟨m, hm, he, hmax⟩ := ih (by omega)
    have h : t + 1 < k + 1 := by omega
    by_cases hc : (bestUpTo μ0 D π u t).1 < chainVal μ0 D π ⟨t + 1, h⟩ u
    · refine ⟨⟨t + 1, h⟩, le_rfl, ?_, ?_⟩
      · simp only [bestUpTo, h, ↓reduceDIte, hc, ↓reduceIte]
      · intro m' hm'
        simp only [bestUpTo, h, ↓reduceDIte, hc, ↓reduceIte, chainPiece]
        rcases Nat.lt_or_ge m'.val (t + 1) with h1 | h1
        · exact (hmax m' (by omega)).trans hc.le
        · have : m' = ⟨t + 1, h⟩ := Fin.ext (by simp; omega)
          subst this
          exact le_rfl
    · refine ⟨m, by omega, ?_, ?_⟩
      · simp only [bestUpTo, h, ↓reduceDIte, hc, ↓reduceIte]
        exact he
      · intro m' hm'
        simp only [bestUpTo, h, ↓reduceDIte, hc, ↓reduceIte]
        rcases Nat.lt_or_ge m'.val (t + 1) with h1 | h1
        · exact hmax m' (by omega)
        · have : m' = ⟨t + 1, h⟩ := Fin.ext (by simp; omega)
          subst this
          exact not_lt.mp hc

lemma best_stable (t : ℕ) (ht : t ≤ k)
    (h : ∀ m : Fin (k + 1), t < m.val → chainVal μ0 D π m u < (bestUpTo μ0 D π u t).1) :
    bestUpTo μ0 D π u k = bestUpTo μ0 D π u t := by
  have key : ∀ s, t + s ≤ k → bestUpTo μ0 D π u (t + s) = bestUpTo μ0 D π u t := by
    intro s
    induction s with
    | zero => intro _; rfl
    | succ s ih =>
      intro hs
      have hh : t + s + 1 < k + 1 := by omega
      rw [← add_assoc]
      simp only [bestUpTo, hh, ↓reduceDIte]
      rw [ih (by omega)]
      have hlt := h ⟨t + s + 1, hh⟩ (show t < t + s + 1 by omega)
      simp only [not_lt.mpr hlt.le, ↓reduceIte]
  have := key (k - t) (by omega)
  rwa [Nat.add_sub_cancel' ht] at this

lemma hardValue_eq :
    hardValue μ0 D π u =
      max (coneVal D u) (max (bestUpTo μ0 D π u k).1 (radialVal μ0 D π u)) := by
  unfold hardValue answer
  split_ifs with h1 h2
  · exact (max_eq_left h1).symm
  · rw [max_eq_right (not_le.mp h1).le, max_eq_left h2]
  · rw [max_eq_right (not_le.mp h1).le, max_eq_right (not_le.mp h2).le]

lemma chainVal_le_hard (m : Fin (k + 1)) : chainVal μ0 D π m u ≤ hardValue μ0 D π u := by
  rw [hardValue_eq]
  obtain ⟨_, _, _, hmax⟩ := best_spec μ0 D π u k le_rfl
  exact (hmax m (by omega)).trans ((le_max_left _ _).trans (le_max_right _ _))

lemma radialVal_le_hard : radialVal μ0 D π u ≤ hardValue μ0 D π u := by
  rw [hardValue_eq]
  exact (le_max_right _ _).trans (le_max_right _ _)

lemma coneVal_le_hard : coneVal D u ≤ hardValue μ0 D π u := by
  rw [hardValue_eq]
  exact le_max_left _ _

lemma answer_subgradient (hμ : 0 ≤ μ0) (hμ0 : μ0 ^ 2 < 1) (hD : 0 < D) (y : E) :
    hardValue μ0 D π u + ⟪(answer μ0 D π u).2, y - u⟫ ≤ hardValue μ0 D π y := by
  obtain ⟨m, -, he, -⟩ := best_spec μ0 D π u k le_rfl
  unfold hardValue
  conv_rhs => rw [← hardValue]
  unfold answer
  split_ifs with h1 h2
  · exact (cone_subgradient D u y).trans (coneVal_le_hard μ0 D π y)
  · rw [he]
    exact (chain_subgradient μ0 D π hμ hμ0 hD m u y).trans (chainVal_le_hard μ0 D π y m)
  · exact (radial_subgradient μ0 D π hμ u y).trans (radialVal_le_hard μ0 D π y)

lemma answer_norm (hμ : 0 ≤ μ0) (hμ1 : μ0 ≤ 1) (hμ0 : μ0 ^ 2 < 1) (hD : 0 < D) :
    ‖(answer μ0 D π u).2‖ ≤ 3 := by
  obtain ⟨m, -, he, -⟩ := best_spec μ0 D π u k le_rfl
  unfold answer
  split_ifs with h1 h2
  · exact coneGrad_norm u
  · rw [he]
    exact (chainGrad_norm μ0 D π hμ hμ0 hD m u).trans (by linarith)
  · exact (radialGrad_norm μ0 D π hμ u).trans (by linarith)

end Selection

section Prefix

variable (μ0 D : ℝ) (u : E)

lemma chainPiece_congr (π ρ : Fin (k + 1) ↪ Fin d) (t : ℕ) (m : Fin (k + 1)) (hm : m.val ≤ t)
    (h : ∀ j : Fin (k + 1), j.val ≤ t → π j = ρ j) :
    chainPiece μ0 D π m u = chainPiece μ0 D ρ m u := by
  have hmask : mask m.val (dev μ0 D π u) = mask m.val (dev μ0 D ρ u) := by
    funext j
    simp only [mask, dev]
    split_ifs with hj
    · rw [h j (by omega)]
    · rfl
  have hl : lift π (mask m.val (dev μ0 D ρ u)) = lift ρ (mask m.val (dev μ0 D ρ u)) := by
    apply lift_congr π ρ _ t _ h
    intro j hj
    simp only [mask]
    rw [ite_eq_right (by omega)]
  have hu : lift π (unit m) = lift ρ (unit m) := by
    apply lift_congr π ρ _ t _ h
    intro j hj
    simp only [unit]
    rw [ite_eq_right (by intro e; subst e; omega)]
  have hpm : π m = ρ m := h m hm
  simp only [chainPiece, chainVal, chainGrad, chainRoot, hmask, hl, hu, hpm]

lemma bestUpTo_prefix (π ρ : Fin (k + 1) ↪ Fin d) (t : ℕ)
    (h : ∀ j : Fin (k + 1), j.val ≤ t → π j = ρ j) :
    bestUpTo μ0 D π u t = bestUpTo μ0 D ρ u t := by
  induction t with
  | zero =>
    exact chainPiece_congr μ0 D u π ρ 0 _ le_rfl h
  | succ t ih =>
    have ih' := ih (fun j hj => h j (by omega))
    unfold bestUpTo
    split_ifs with h1 h2 h3 h3
    · exact chainPiece_congr μ0 D u π ρ (t + 1) _ le_rfl h
    · exfalso
      apply h3
      have e := chainPiece_congr μ0 D u π ρ (t + 1) ⟨t + 1, h1⟩ le_rfl h
      simp only [chainPiece, Prod.mk.injEq] at e
      rw [← ih', ← e.1]
      exact h2
    · exfalso
      apply h2
      have e := chainPiece_congr μ0 D u π ρ (t + 1) ⟨t + 1, h1⟩ le_rfl h
      simp only [chainPiece, Prod.mk.injEq] at e
      rw [ih', e.1]
      exact h3
    · exact ih'
    · exact ih'

lemma partialAnswer_prefix (π ρ : Fin (k + 1) ↪ Fin d) (t : ℕ)
    (h : ∀ j : Fin (k + 1), j.val ≤ t → π j = ρ j) :
    partialAnswer μ0 D π t u = partialAnswer μ0 D ρ t u := by
  unfold partialAnswer
  rw [bestUpTo_prefix μ0 D u π ρ t h]

end Prefix

end LongTails.Proofs.SharpChainInstance
