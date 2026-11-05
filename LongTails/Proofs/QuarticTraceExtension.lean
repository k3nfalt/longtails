import LongTails.Proofs.QuarticAccelerationTrace

namespace LongTails.Proofs.QuarticTraceExtension

open LongTails.Proofs.QuarticAccelerationTrace
open LongTails.Algorithms.CompositeCubicAcceleration hiding advance damping
open LongTails.Algorithms.QuarticAcceleration
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def append (t : Trace E) (K : ℕ) (γ : ℝ) (y g : E) : Trace E where
  state i := if i ≤ K then t.state i else advance E (t.guess K) γ (t.state K) y g
  guess i := if i ≤ K then t.guess i else nextGuess (t.guess K) (parameter E γ (location t K) y)
  point i := if i < K then t.point i else y
  gradient i := if i < K then t.gradient i else g

lemma append_prefix {t : Trace E} {K i : ℕ} {γ : ℝ} {y g : E} (hi : i ≤ K) :
    (append t K γ y g).state i = t.state i ∧
    (append t K γ y g).guess i = t.guess i ∧
    location (append t K γ y g) i = location t i := by
  simp [append, hi, location]

lemma append_next (t : Trace E) (K : ℕ) (γ : ℝ) (y g : E) :
    (append t K γ y g).state (K + 1) = advance E (t.guess K) γ (t.state K) y g ∧
    (append t K γ y g).guess (K + 1) = nextGuess (t.guess K) (parameter E γ (location t K) y) := by
  simp [append]

lemma append_lam {t : Trace E} {K i : ℕ} {γ : ℝ} {y g : E} (hi : i < K) :
    lam (append t K γ y g) γ i = lam t γ i := by
  unfold lam
  rw [(append_prefix hi.le).2.2]
  simp only [append, ite_eq_left hi]

lemma append_lam_last (t : Trace E) (K : ℕ) (γ : ℝ) (y g : E) :
    lam (append t K γ y g) γ K = parameter E γ (location t K) y := by
  unfold lam
  rw [(append_prefix le_rfl).2.2]
  simp only [append, lt_self_iff_false, ite_false]

lemma append_valid {t : Trace E} {f : E → ℝ} {γ : ℝ} {x0 : E} {K : ℕ}
    (hv : Valid t f γ x0 K) (y g : E)
    (hlam : 0 < parameter E γ (location t K) y)
    (hfirst : K = 0 → t.guess 0 = parameter E γ (location t 0) y)
    (hsub : ∀ x, f y + ⟪g, x - y⟫ ≤ f x)
    (hres : ‖g + (parameter E γ (location t K) y) • (y - location t K)‖ ≤
      γ * ‖y - location t K‖ ^ 3 / 32) : Valid (append t K γ y g) f γ x0 (K + 1) := by
  constructor
  · rw [(append_prefix (Nat.zero_le K)).1]
    exact hv.initial
  · intro i hi
    by_cases hik : i ≤ K
    · rw [(append_prefix hik).2.1]
      exact hv.guess_pos i hik
    · have he : i = K + 1 := by omega
      subst i
      rw [(append_next t K γ y g).2]
      exact LongTails.Proofs.QuarticAcceleration.nextGuess_pos (hv.guess_pos K le_rfl)
  · intro i hi
    by_cases hik : i < K
    · rw [append_lam hik]
      exact hv.lam_pos i hik
    · have he : i = K := by omega
      subst i
      rw [append_lam_last]
      exact hlam
  · intro _
    rw [(append_prefix (Nat.zero_le K)).2.1]
    by_cases hk : K = 0
    · subst K
      rw [append_lam_last]
      exact hfirst rfl
    · rw [append_lam (Nat.pos_of_ne_zero hk)]
      exact hv.first_guess (Nat.pos_of_ne_zero hk)
  · intro i hi
    by_cases hik : i < K
    · rw [(append_prefix (Nat.succ_le_of_lt hik)).1, (append_prefix hik.le).1, (append_prefix hik.le).2.1]
      simpa only [append, ite_eq_left hik] using hv.advance_eq i hik
    · have he : i = K := by omega
      subst i
      rw [(append_next t K γ y g).1, (append_prefix le_rfl).1, (append_prefix le_rfl).2.1]
      simp only [append, lt_self_iff_false, ite_false]
  · intro i hi
    by_cases hik : i < K
    · rw [(append_prefix (Nat.succ_le_of_lt hik)).2.1, (append_prefix hik.le).2.1, append_lam hik]
      exact hv.guess_eq i hik
    · have he : i = K := by omega
      subst i
      rw [(append_next t K γ y g).2, (append_prefix le_rfl).2.1, append_lam_last]
  · intro i hi x
    by_cases hik : i < K
    · simpa only [append, ite_eq_left hik] using hv.support i hik x
    · have he : i = K := by omega
      subst i
      simpa only [append, lt_self_iff_false, ite_false] using hsub x
  · intro i hi
    by_cases hik : i < K
    · rw [append_lam hik, (append_prefix hik.le).2.2]
      simpa only [append, ite_eq_left hik] using hv.residual i hik
    · have he : i = K := by omega
      subst i
      rw [append_lam_last, (append_prefix le_rfl).2.2]
      simpa only [append, lt_self_iff_false, ite_false] using hres

noncomputable def baseTrace (μ : ℝ) (x0 : E) : Trace E where
  state _ := ⟨0, x0, x0⟩
  guess _ := μ
  point _ := x0
  gradient _ := 0

lemma base_valid (f : E → ℝ) (γ : ℝ) (x0 : E) {μ : ℝ} (hμ : 0 < μ) :
    Valid (baseTrace μ x0) f γ x0 0 := by
  constructor
  · rfl
  · intro k _; exact hμ
  · intro k hk; omega
  · intro h; omega
  · intro k hk; omega
  · intro k hk; omega
  · intro k hk; omega
  · intro k hk; omega

noncomputable def startTrace (γ : ℝ) (x0 y g : E) : Trace E :=
  append (baseTrace (parameter E γ x0 y) x0) 0 γ y g

lemma start_valid {f : E → ℝ} {γ : ℝ} (x0 y g : E)
    (hlam : 0 < parameter E γ x0 y) (hsub : ∀ x, f y + ⟪g, x - y⟫ ≤ f x)
    (hres : ‖g + (parameter E γ x0 y) • (y - x0)‖ ≤ γ * ‖y - x0‖ ^ 3 / 32) :
    Valid (startTrace γ x0 y g) f γ x0 1 := by
  have hloc : location (baseTrace (parameter E γ x0 y) x0) 0 = x0 :=
    QuarticAccelerationEnergy.initial_center hlam x0
  apply append_valid (base_valid f γ x0 hlam) y g
  · rwa [hloc]
  · intro _
    rw [hloc]
    rfl
  · exact hsub
  · rwa [hloc]

lemma start_end {γ : ℝ} (x0 y g : E) (hlam : 0 < parameter E γ x0 y) :
    (startTrace γ x0 y g).state 1 = advance E (parameter E γ x0 y) γ ⟨0, x0, x0⟩ y g ∧
    (startTrace γ x0 y g).guess 1 = parameter E γ x0 y / 4 := by
  have hloc : location (baseTrace (parameter E γ x0 y) x0) 0 = x0 :=
    QuarticAccelerationEnergy.initial_center hlam x0
  have hh := append_next (baseTrace (parameter E γ x0 y) x0) 0 γ y g
  rw [hloc] at hh
  simpa only [startTrace, baseTrace, nextGuess, le_refl, ite_true] using hh


end LongTails.Proofs.QuarticTraceExtension
