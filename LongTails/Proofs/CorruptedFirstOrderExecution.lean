import LongTails.Proofs.CorruptedFirstOrderProgress

open MeasureTheory OracleTemplate LongTails.Setups.CorruptedFirstOrderNonconvex
open LongTails.Algorithms.CorruptedFirstOrderDescent
open LongTails.Proofs.CorruptedFirstOrderWalk LongTails.Proofs.CorruptedFirstOrderProgress

namespace LongTails.Proofs.CorruptedFirstOrderExecution

lemma walk_output (p : Params) (f : Space p.d → ℝ) (g : Space p.d → Space p.d)
    (hL : 0 < p.L) (he : 0 < p.ε) (_hΔ : 0 ≤ p.Δ)
    (hgap : ∃ l, (∀ x, l ≤ f x) ∧ f p.x0 - l ≤ p.Δ)
    (t e : ℕ) (s : State (Space p.d)) (hi : Invariant p f g t e s) (hb : e ≤ p.k)
    (ht : ⌈16 * p.L * p.Δ / p.ε ^ 2⌉₊ + 5 * p.k + 4 ≤ t) :
    ‖gradient f (output p s)‖ ≤ p.ε := by
  cases s with
  | done x => exact hi
  | sample vs =>
    obtain ⟨_, h, _⟩ := hi
    omega
  | walk a ps x v =>
    obtain ⟨l, hl, hΔl⟩ := hgap
    obtain ⟨_, ha, _, hv, _, htime⟩ := hi
    let D := ⌈16 * p.L * p.Δ / p.ε ^ 2⌉₊ + 1
    have hd : ∀ y j, f y + η p ≤ a - (j : ℕ) * δ p → j ≤ D := by
      intro y j hy
      have hc := Nat.le_ceil (16 * p.L * p.Δ / p.ε ^ 2)
      have hh := hl y
      have hbound : (j : ℝ) * δ p ≤ p.Δ + 2 * η p := by linarith
      have hpos : 0 < δ p := by unfold δ; positivity
      have hsmall : 2 * η p ≤ δ p := by
        unfold η δ
        apply (le_of_eq (by ring : 2 * (p.ε ^ 2 / (128 * p.L)) = (p.ε ^ 2 / (16 * p.L)) / 4)).trans
        linarith
      have heq : p.Δ / δ p = 16 * p.L * p.Δ / p.ε ^ 2 := by unfold δ; field_simp
      have hh' := (div_le_iff₀ hpos).mp ((le_of_eq heq).trans hc)
      have : (j : ℝ) ≤ (D : ℝ) := by
        apply (mul_le_mul_iff_left₀ hpos).mp
        dsimp [D]
        push_cast
        nlinarith
      exact_mod_cast this
    have hr := rank_bound (p := p) f a ps x hd
    have hscore : score (p := p) f g a ps x v ≤ (D : ℤ) + v := by
      unfold score
      have hm := mul_le_mul_of_nonneg_left (rating_le (‖g x‖ ≤ (3 * p.ε / 4))) (Int.natCast_nonneg v)
      linarith
    dsimp [D] at hscore
    omega

lemma execution_accuracy (p : Params) (f : Space p.d → ℝ)
    (O : Oracle (Space p.d) (ℝ × Space p.d)) (hp : spec.valid p) (ho : spec.admissible p f O)
    (K : ℕ) (hK : ⌈16 * p.L * p.Δ / p.ε ^ 2⌉₊ + 5 * p.k + 4 ≤ K)
    (ξ : (j : ℕ) → O.Seed j) :
    ‖gradient f (execute O (algorithm p) (fun _ => K) () ξ)‖ ≤ p.ε := by
  classical
  obtain ⟨hg, hlip, hgap, g, hgerr, herrors⟩ := ho
  let step := fun sh : State (Space p.d) × List ((Fin 1 × Space p.d) × (ℝ × Space p.d)) =>
    let q := (0, output p sh.1)
    let r := O.answer sh.2 q (ξ sh.2.length)
    (advance p sh.1 r, sh.2 ++ [(q, r)])
  let run := fun t => step^[t] (.sample [], [])
  have hs (t : ℕ) : run (t + 1) = step (run t) := Function.iterate_succ_apply' _ _ _
  have hi (t : ℕ) : Reachable O (run t).2 ∧
      Invariant p f g t (errors (accurate p f g) (run t).2) (run t).1 := by
    induction t with
    | zero => exact ⟨.nil, start_invariant p f g⟩
    | succ t ih =>
      obtain ⟨hreach, hinv⟩ := ih
      let s := (run t).1
      let h := (run t).2
      let q : Fin 1 × Space p.d := (0, output p s)
      let r := O.answer h q (ξ h.length)
      let b : ℕ := if accurate p f g (output p s) r then 0 else 1
      have hnew : Reachable O (h ++ [(q, r)]) := hreach.snoc q (ξ h.length)
      have her : errors (accurate p f g) (h ++ [(q, r)]) = errors (accurate p f g) h + b := by
        simp only [errors, List.filter_append, List.length_append]
        by_cases hclean : accurate p f g (output p s) r <;> simp [q, b, hclean]
      have hlim := herrors _ hnew
      rw [her] at hlim
      have hclean : b = 0 → accurate p f g (output p s) r := by
        simp [b]
      change Invariant p f g t (errors (accurate p f g) h) s at hinv
      rw [hs]
      refine ⟨hnew, ?_⟩
      change Invariant p f g (t + 1) (errors (accurate p f g) (h ++ [(q, r)])) (advance p s r)
      rw [her]
      generalize hst : s = st at hinv hclean ⊢
      cases st with
      | sample vs => exact sample_invariant p f g vs r t _ b hlim hclean hinv
      | done x => exact hinv
      | walk a ps x v =>
        exact walk_invariant p f g hg hlip hp.1 hp.2.1 hgerr t _ b hlim a ps x v r hclean hinv
  erw [execute_indexed O (algorithm p) K () ξ]
  exact walk_output p f g hp.1 hp.2.1 hp.2.2 hgap K _ _ (hi K).2 (herrors _ (hi K).1) hK

end LongTails.Proofs.CorruptedFirstOrderExecution
