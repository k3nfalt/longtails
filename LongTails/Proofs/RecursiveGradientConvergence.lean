import LongTails.Proofs.RecursiveGradientEnergy
import LongTails.Proofs.RecursiveGradientQueries

open scoped BigOperators

namespace OracleTemplate.NonconvexFiniteSum

open LongTails.Setups.FiniteSumSmoothNonconvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma recursiveEpochs_energy {n b : ℕ} [NeZero n]
    {f : E → ℝ} {g : Fin n × E → E} {L : ℝ}
    (hL : 0 < L) (hb : 0 < b)
    (hg : ∀ x, HasGradientAt f (FiniteSum.fullGradient g x) x)
    (hmean : ∀ x y, (𝔼 i, ‖g (i, x) - g (i, y)‖ ^ 2) ≤ L ^ 2 * ‖x - y‖ ^ 2)
    (k : ℕ) (hk : k ≤ b) (S : ℕ) (x : E) :
    (𝔼 seed : Fin S → Fin k → Fin b → Fin n,
      let result := recursiveEpochs g (1 / (2 * L)) b x
        (List.ofFn (fun s => List.ofFn (fun j => List.ofFn (seed s j))))
      f result.1 + (result.2.map (fun z => ‖FiniteSum.fullGradient g z‖ ^ 2)).sum / (4 * L)) ≤
      f x := by
  induction S generalizing x with
  | zero => simp [recursiveEpochs]
  | succ S ih =>
      let ep := fun sample : Fin k → Fin b → Fin n =>
        recursiveRun g (1 / (2 * L)) b x (FiniteSum.fullGradient g x)
          (List.ofFn (fun j => List.ofFn (sample j)))
      have hpoint (sample : Fin k → Fin b → Fin n) :
          (𝔼 seed : Fin S → Fin k → Fin b → Fin n,
            let result := recursiveEpochs g (1 / (2 * L)) b (ep sample).1
              (List.ofFn (fun s => List.ofFn (fun j => List.ofFn (seed s j))))
            f result.1 + ((ep sample).2.map (fun z => ‖FiniteSum.fullGradient g z‖ ^ 2)).sum /
              (4 * L) + (result.2.map (fun z => ‖FiniteSum.fullGradient g z‖ ^ 2)).sum / (4 * L)) ≤
            f (ep sample).1 + ((ep sample).2.map (fun z => ‖FiniteSum.fullGradient g z‖ ^ 2)).sum /
              (4 * L) := by
        have h := ih (ep sample).1
        simp only [Finset.expect_add_distrib, Fintype.expect_const] at h ⊢
        linarith
      have hav := Finset.expect_le_expect (s := Finset.univ) (fun sample _ => hpoint sample)
      have hs := recursiveRun_energy hL hb hg hmean k hk x (FiniteSum.fullGradient g x)
      simp only [sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] at hs
      rw [expect_function_succ]
      simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, recursiveEpochs,
        List.map_append, List.sum_append, add_div]
      simpa only [ep, add_assoc] using hav.trans hs

lemma recursiveEpochs_sum_bound {n b : ℕ} [NeZero n]
    {f : E → ℝ} {g : Fin n × E → E} {L Δ : ℝ}
    (hL : 0 < L) (hb : 0 < b)
    (hg : ∀ x, HasGradientAt f (FiniteSum.fullGradient g x) x)
    (hmean : ∀ x y, (𝔼 i, ‖g (i, x) - g (i, y)‖ ^ 2) ≤ L ^ 2 * ‖x - y‖ ^ 2)
    (k : ℕ) (hk : k ≤ b) (S : ℕ) (x : E) (lower : ℝ)
    (hlower : ∀ z, lower ≤ f z) (hgap : f x - lower ≤ Δ) :
    (𝔼 seed : Fin S → Fin k → Fin b → Fin n,
      ((recursiveEpochs g (1 / (2 * L)) b x
        (List.ofFn (fun s => List.ofFn (fun j => List.ofFn (seed s j))))).2.map
          (fun z => ‖FiniteSum.fullGradient g z‖ ^ 2)).sum) ≤ 4 * L * Δ := by
  have he := recursiveEpochs_energy hL hb hg hmean k hk S x
  have hl := Finset.expect_le_expect (s := Finset.univ)
    (fun (seed : Fin S → Fin k → Fin b → Fin n) _ => hlower (recursiveEpochs g (1 / (2 * L)) b x
      (List.ofFn (fun s => List.ofFn (fun j => List.ofFn (seed s j))))).1)
  simp only [Finset.expect_add_distrib, ← Finset.expect_div] at he
  simp only [Fintype.expect_const] at hl
  have h : (𝔼 seed : Fin S → Fin k → Fin b → Fin n,
      ((recursiveEpochs g (1 / (2 * L)) b x
        (List.ofFn (fun s => List.ofFn (fun j => List.ofFn (seed s j))))).2.map
          (fun z => ‖FiniteSum.fullGradient g z‖ ^ 2)).sum) / (4 * L) ≤ Δ := by
    linarith
  exact (div_le_iff₀ (by positivity : 0 < 4 * L)).mp h |>.trans_eq (by ring)

lemma expect_list_getD {A : Type*} (xs : List A) (fallback : A) (c : A → ℝ)
    (T : ℕ) (hT : xs.length = T) :
    (𝔼 i : Fin T, c (xs.getD i.val fallback)) = (xs.map c).sum / T := by
  subst T
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_fin]
  congr 1
  simp [List.getD_eq_getElem?_getD]

end OracleTemplate.NonconvexFiniteSum
