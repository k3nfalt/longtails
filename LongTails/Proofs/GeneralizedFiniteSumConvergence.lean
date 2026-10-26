import LongTails.Proofs.GeneralizedFiniteSumEpoch

open Set
open scoped BigOperators

namespace OracleTemplate.GeneralizedFiniteSum

open LongTails.Setups.GeneralizedSmoothFiniteSum
open LongTails.Setups.FiniteSumSmoothAndConvex (objective)

lemma trial_accuracy_of_safe (p : Params) (f : Fin p.n → p.E → ℝ) (g : Fin p.n → p.E → p.E)
    (u : p.E) (h : Hyp p f g u)
    (ξ : Fin (epochCount p * p.n) → Fin ((2 * p.n).factorial))
    (hsafe : coreEnergy p f u (stoppedRun (coreStep p g) (coreEnergy p f u)
      (6 * p.n * p.R ^ 2) (epochCount p * p.n) (initialCore p) ξ) ≤ 6 * p.n * p.R ^ 2) :
    objective f (trialOutput p g ξ) - objective f u ≤ p.ε / 2 := by
  let s := stoppedRun (coreStep p g) (coreEnergy p f u) (6 * p.n * p.R ^ 2)
    (epochCount p * p.n) (initialCore p) ξ
  have hi := stoppedRun_invariant (coreStep p g) (coreEnergy p f u) (6 * p.n * p.R ^ 2)
    (CoreInvariant p f u) (coreStep_invariant p f g u h) (epochCount p * p.n)
    (initialCore p) (initialCore_invariant p f g u h) ξ
  have he := stoppedRun_eq_plainRun (coreStep p g) (coreEnergy p f u) (6 * p.n * p.R ^ 2)
    (epochCount p * p.n) (initialCore p) ξ hsafe
  rw [← coreRun_eq_plainRun] at he
  have hterm := coreRun_terminal p g (epochCount p) ξ
  have hgap := (hi.2 hsafe).2.1
  rw [he, hterm.1] at hgap
  have hA := epochWeight_pos p h.positive_L0 h.nonnegative_L1 h.nonnegative_G
    h.positive_R h.positive_gap (epochCount p)
  have hcount := epochCount_sufficient p h.positive_L0 h.nonnegative_L1 h.nonnegative_G
    h.positive_R h.positive_gap h.positive_accuracy
  have hb : 6 * p.R ^ 2 / epochWeight p (epochCount p) ≤ p.ε / 2 := by
    apply (div_le_iff₀ hA).mpr
    have hh := (div_le_iff₀ h.positive_accuracy).mp hcount
    nlinarith only [hh]
  exact hgap.trans hb

lemma trial_failure_bound (p : Params) (f : Fin p.n → p.E → ℝ) (g : Fin p.n → p.E → p.E)
    (u : p.E) (h : Hyp p f g u) :
    (𝔼 ξ : Fin (epochCount p * p.n) → Fin ((2 * p.n).factorial),
      if p.ε / 2 < objective f (trialOutput p g ξ) - objective f u then (1 : ℝ) else 0) ≤ 1 / 4 := by
  classical
  let : NeZero (2 * p.n).factorial := ⟨Nat.factorial_ne_zero _⟩
  have hT : 0 < 6 * (p.n : ℝ) * p.R ^ 2 := by
    have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
    have hR := h.positive_R
    positivity
  have hnonneg (s : LocalCore p) (hs : CoreInvariant p f u s) : 0 ≤ coreEnergy p f u s := by
    have hA := epochWeight_pos p h.positive_L0 h.nonnegative_L1 h.nonnegative_G
      h.positive_R h.positive_gap s.epoch
    have ha := epochIncrement_pos p h.positive_L0 h.nonnegative_L1 h.nonnegative_G h.positive_R.le hA
    exact coreEnergy_nonneg p f u h.minimizer s hs.1 hA.le ha.le
  have hb := stoppedRun_failure (coreStep p g) (coreEnergy p f u) (6 * p.n * p.R ^ 2)
    (CoreInvariant p f u) hT hnonneg (coreStep_invariant p f g u h) (coreStep_mean p f g u h)
    (epochCount p * p.n) (initialCore p) (initialCore_invariant p f g u h)
  have hinit : coreEnergy p f u (initialCore p) / (6 * p.n * p.R ^ 2) ≤ 1 / 4 := by
    apply (div_le_iff₀ hT).mpr
    nlinarith only [initialCore_energy p f g u h]
  apply le_trans ?_ (hb.trans hinit)
  apply Finset.expect_le_expect
  intro ξ _
  by_cases hs : 6 * p.n * p.R ^ 2 < coreEnergy p f u (stoppedRun (coreStep p g)
      (coreEnergy p f u) (6 * p.n * p.R ^ 2) (epochCount p * p.n) (initialCore p) ξ)
  · simp only [ite_eq_left hs]
    split_ifs <;> norm_num
  · have ha := trial_accuracy_of_safe p f g u h ξ (le_of_not_gt hs)
    simp only [ite_eq_right hs, ite_eq_right (not_lt_of_ge ha), le_refl]

lemma selectBest_le_initial {E : Type*} (F : E → ℝ) (best : E) (xs : List E) :
    F (selectBest F best xs) ≤ F best := by
  induction xs generalizing best with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [selectBest]
    apply (ih _).trans
    split_ifs with h
    · exact h.le
    · exact le_rfl

lemma selectBest_le_member {E : Type*} (F : E → ℝ) (best : E) (xs : List E)
    (x : E) (hx : x ∈ xs) : F (selectBest F best xs) ≤ F x := by
  induction xs generalizing best with
  | nil => simp at hx
  | cons y xs ih =>
    simp only [selectBest]
    rcases List.mem_cons.mp hx with rfl | hx
    · apply (selectBest_le_initial F _ xs).trans
      split_ifs with h
      · exact le_rfl
      · exact le_of_not_gt h
    · exact ih _ hx

lemma amplified_accuracy (p : Params) (f : Fin p.n → p.E → ℝ) (g : Fin p.n → p.E → p.E)
    (u : p.E) (h : Hyp p f g u) :
    (𝔼 ξ : LocalSeeds p, (objective f (amplifiedOutput p f g ξ) - objective f u)) ≤ p.ε := by
  classical
  let : NeZero (2 * p.n).factorial := ⟨Nat.factorial_ne_zero _⟩
  by_cases heasy : p.Δ ≤ p.ε
  · simpa only [amplifiedOutput, ite_eq_left heasy, Fintype.expect_const] using h.gap.trans heasy
  · let B := fun ξ : LocalSeeds p => objective f (amplifiedOutput p f g ξ) - objective f u
    let F := fun ξ => objective f (trialOutput p g ξ) - objective f u
    have hb (ξ : LocalSeeds p) : B ξ ≤ p.Δ := by
      have hh := selectBest_le_initial (objective f) p.x0 (List.ofFn (fun j => trialOutput p g (ξ j)))
      dsimp [B, amplifiedOutput]
      rw [ite_eq_right heasy]
      nlinarith only [hh, h.gap]
    have hm (ξ : LocalSeeds p) (j : Fin (trialCount p)) : B ξ ≤ F (ξ j) := by
      have hh := selectBest_le_member (objective f) p.x0 (List.ofFn (fun j => trialOutput p g (ξ j)))
        (trialOutput p g (ξ j)) (List.mem_ofFn.mpr ⟨j, rfl⟩)
      dsimp [B, F, amplifiedOutput]
      rw [ite_eq_right heasy]
      linarith only [hh]
    have hh := finite_minimum_mean F (trialCount p) B (show 0 ≤ p.ε / 2 by have := h.positive_accuracy; positivity)
      h.positive_gap.le hb hm (trial_failure_bound p f g u h)
    have hf := trialCount_failure p h.positive_gap h.positive_accuracy
    have hend : p.ε / 2 + p.Δ * (1 / 4 : ℝ) ^ trialCount p ≤ p.ε := by linarith only [hf]
    exact hh.trans hend

end OracleTemplate.GeneralizedFiniteSum
