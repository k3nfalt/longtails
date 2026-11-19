import LongTails.Proofs.CorruptedFirstOrderEstimates

open LongTails.Setups.CorruptedFirstOrderNonconvex LongTails.Algorithms.CorruptedFirstOrderDescent

namespace LongTails.Proofs.CorruptedFirstOrderWalk

open LongTails.Proofs.CorruptedFirstOrderEstimates

variable {p : Params}

noncomputable abbrev η (p : Params) := p.ε ^ 2 / (128 * p.L)
noncomputable abbrev δ (p : Params) := p.ε ^ 2 / (16 * p.L)

noncomputable def rating (P : Prop) : ℤ := by classical exact if P then 1 else -1

lemma rating_ge (P : Prop) : -1 ≤ rating P := by classical unfold rating; split <;> decide

lemma rating_le (P : Prop) : rating P ≤ 1 := by classical unfold rating; split <;> decide

noncomputable def rank (f : Space p.d → ℝ) (a : ℝ) :
    List (Space p.d) → Space p.d → ℤ
  | [], _ => 0
  | y :: ys, x => rank f a ys y +
      rating (f x + η p ≤ a - ((ys.length + 1 : ℕ) : ℝ) * δ p)

lemma rank_length (f : Space p.d → ℝ) (a : ℝ) (ps : List (Space p.d)) (x : Space p.d) :
    rank (p := p) f a ps x ≤ ps.length := by
  induction ps generalizing x with
  | nil => simp [rank]
  | cons y ys ih =>
    simp only [rank, List.length_cons, Nat.cast_add, Nat.cast_one]
    exact add_le_add (ih y) (rating_le _)

lemma rank_bound (f : Space p.d → ℝ) (a : ℝ) (ps : List (Space p.d)) (x : Space p.d)
    {D : ℕ} (h : ∀ y j, f y + η p ≤ a - (j : ℕ) * δ p → j ≤ D) :
    rank (p := p) f a ps x ≤ D := by
  classical
  induction ps generalizing x with
  | nil => simp [rank]
  | cons y ys ih =>
    by_cases hv : f x + η p ≤ a - ((ys.length + 1 : ℕ) : ℝ) * δ p
    · exact (rank_length f a (y :: ys) x).trans (by exact_mod_cast h x _ hv)
    · simp only [rank, rating, ite_eq_right hv]
      linarith [ih y]

noncomputable def score (f : Space p.d → ℝ) (g : Space p.d → Space p.d) (a : ℝ)
    (ps : List (Space p.d)) (x : Space p.d) (v : ℕ) : ℤ :=
  rank (p := p) f a ps x + (v : ℤ) * rating (‖g x‖ ≤ (3 * p.ε / 4))

def root {X : Type} : List X → X → X
  | [], x => x
  | y :: ys, _ => root ys y

def WalkInv (f : Space p.d → ℝ) (g : Space p.d → Space p.d) (t e : ℕ)
    (a : ℝ) (ps : List (Space p.d)) (x : Space p.d) (v : ℕ) : Prop :=
  f p.x0 + η p ≤ a ∧ a ≤ f p.x0 + 3 * η p ∧
  root ps x = p.x0 ∧
  v ≤ p.k ∧ ((3 * p.ε / 4) < ‖g x‖ → v ≤ e) ∧
  (t : ℤ) ≤ 2 * p.k + 1 + 2 * (e : ℤ) + score (p := p) f g a ps x v

def Invariant (p : Params) (f : Space p.d → ℝ) (g : Space p.d → Space p.d)
    (t e : ℕ) : State (Space p.d) → Prop
  | .sample vs => vs.length = t ∧ t < 2 * p.k + 1 ∧ valueErrors vs (f p.x0) (η p) ≤ e
  | .walk a ps x v => WalkInv (p := p) f g t e a ps x v
  | .done x => ‖gradient f x‖ ≤ p.ε

lemma start_invariant (p : Params) (f : Space p.d → ℝ) (g : Space p.d → Space p.d) :
    Invariant p f g 0 0 (.sample []) := by simp [Invariant, valueErrors]

lemma sample_invariant (p : Params) (f : Space p.d → ℝ) (g : Space p.d → Space p.d)
    (vs : List ℝ) (r : ℝ × Space p.d) (t e b : ℕ) (hb : e + b ≤ p.k)
    (hr : b = 0 → accurate p f g p.x0 r)
    (hi : Invariant p f g t e (.sample vs)) :
    Invariant p f g (t + 1) (e + b) (advance p (.sample vs) r) := by
  classical
  obtain ⟨hlen, ht, he⟩ := hi
  have hv : valueErrors (r.1 :: vs) (f p.x0) (η p) ≤ e + b := by
    by_cases h : η p < |r.1 - f p.x0|
    · have hn : b ≠ 0 := fun hb => (not_lt_of_ge (hr hb).1) h
      simp [valueErrors, h] at he ⊢
      omega
    · simpa [valueErrors, List.filter_cons, h] using he.trans (Nat.le_add_right e b)
  simp only [advance]
  split
  · rename_i hs
    exact ⟨by simp [hlen], by simpa only [List.length_cons, hlen] using hs, hv⟩
  · rename_i hn
    have hlen' : (r.1 :: vs).length = 2 * p.k + 1 := by simp [hlen] at *; omega
    obtain ⟨h₁, h₂⟩ := anchor_bounds _ _ _ _ hlen' (hv.trans hb)
    refine ⟨h₁, h₂, rfl, by omega, by simp, ?_⟩
    simp [score, rank]
    omega

end LongTails.Proofs.CorruptedFirstOrderWalk

open LongTails.Setups.CorruptedFirstOrderNonconvex LongTails.Algorithms.CorruptedFirstOrderDescent
open LongTails.Proofs.CorruptedFirstOrderWalk LongTails.Proofs.CorruptedFirstOrderEstimates

namespace LongTails.Proofs.CorruptedFirstOrderProgress

lemma walk_invariant (p : Params) (f : Space p.d → ℝ) (g : Space p.d → Space p.d)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hL : 0 < p.L) (he : 0 < p.ε) (hgerr : ∀ x, ‖g x - gradient f x‖ ≤ p.ε / 8)
    (t e b : ℕ) (hb : e + b ≤ p.k) (a : ℝ) (ps : List (Space p.d))
    (x : Space p.d) (v : ℕ) (r : ℝ × Space p.d) (hr : b = 0 → accurate p f g x r)
    (hi : WalkInv (p := p) f g t e a ps x v) :
    Invariant p f g (t + 1) (e + b) (advance p (.walk a ps x v) r) := by
  classical
  obtain ⟨ha, ha', hroot, hv, hlarge, htime⟩ := hi
  have hcost (z : ℤ) (hmin : score (p := p) f g a ps x v - 1 ≤ z)
      (hclean : b = 0 → score (p := p) f g a ps x v + 1 ≤ z) :
      ((t + 1 : ℕ) : ℤ) ≤ 2 * p.k + 1 + 2 * ((e + b : ℕ) : ℤ) + z := by
    by_cases hb : b = 0
    · specialize hclean hb
      omega
    · omega
  have hend (h : ‖g x‖ ≤ (3 * p.ε / 4)) : ‖gradient f x‖ ≤ p.ε := by
    have hh := norm_le_norm_add_norm_sub (g x) (gradient f x)
    linarith [hgerr x]
  simp only [advance]
  split
  · rename_i hp
    obtain ⟨rfl, hfail⟩ := hp
    cases ps with
    | nil =>
      have hx : x = p.x0 := hroot
      have hn : b ≠ 0 := by
        intro hz
        obtain ⟨hh, _⟩ := hr hz
        obtain ⟨_, hval⟩ := abs_le.mp hh
        simp only [List.length_nil, Nat.cast_zero, zero_mul, sub_zero] at hfail
        rw [hx] at hval
        linarith
      refine ⟨ha, ha', hroot, by omega, by simp, hcost _ (by omega) (fun hz => (hn hz).elim)⟩
    | cons y ys =>
      refine ⟨ha, ha', hroot, by omega, by simp, hcost _ ?_ ?_⟩
      · simp only [score, rank, Nat.cast_zero, zero_mul, add_zero]
        linarith [rating_le (f x + η p ≤ a - ((ys.length + 1 : ℕ) : ℝ) * δ p)]
      · intro hz
        obtain ⟨hh, _⟩ := hr hz
        have hu := (abs_le.mp hh).2
        have hn : ¬f x + η p ≤ a - ((ys.length + 1 : ℕ) : ℝ) * δ p := by
          simp only [List.length_cons] at hfail
          linarith
        simp only [score, rank, Nat.cast_zero, zero_mul, add_zero, rating, ite_eq_right hn]
        omega
  · rename_i hpass
    split
    · rename_i hsmall
      split
      · rename_i hkv
        apply hend
        by_contra! hbig
        have hn : b ≠ 0 := by
          intro hz
          rw [(hr hz).2] at hsmall
          linarith
        have := hlarge hbig
        omega
      · rename_i hkv
        refine ⟨ha, ha', hroot, by omega, ?_, hcost _ ?_ ?_⟩
        · intro hbig
          have hn : b ≠ 0 := by
            intro hz
            rw [(hr hz).2] at hsmall
            linarith
          have := hlarge hbig
          omega
        · simp only [score, Nat.cast_succ, add_mul, one_mul]
          linarith [rating_ge (‖g x‖ ≤ (3 * p.ε / 4))]
        · intro hz
          rw [(hr hz).2] at hsmall
          simp [score, rating, hsmall]
    · rename_i hbig
      split
      · rename_i hvpos
        refine ⟨ha, ha', hroot, by omega, fun h => by have := hlarge h; omega, hcost _ ?_ ?_⟩
        · rw [show v = v - 1 + 1 by omega]
          simp only [Nat.add_sub_cancel, score, Nat.cast_succ, add_mul, one_mul]
          linarith [rating_le (‖g x‖ ≤ (3 * p.ε / 4))]
        · intro hz
          rw [(hr hz).2] at hbig
          simp only [score, rating, ite_eq_right hbig, mul_neg, mul_one]
          omega
      · rename_i hvzero
        have hzero : v = 0 := by omega
        subst v
        let y := x - (1 / p.L) • r.2
        refine ⟨ha, ha', hroot, by omega, by simp, hcost _ ?_ ?_⟩
        · simp only [score, rank, Nat.cast_zero, zero_mul, add_zero]
          linarith [rating_ge (f y + η p ≤ a - ((ps.length + 1 : ℕ) : ℝ) * δ p)]
        · intro hz
          obtain ⟨hh, hsame⟩ := hr hz
          have hu := (abs_le.mp hh).1
          have hp : r.1 ≤ a - (ps.length : ℝ) * δ p := by
            simpa only [true_and, not_lt, eq_self] using hpass
          have hd := trial_decrease hL he hg hlip (hsame ▸ hgerr x) (lt_of_not_ge hbig)
          have hscale : 5 * p.ε ^ 2 / (64 * p.L) = δ p + 2 * η p := by
            unfold δ η
            ring
          have hvalid : f y + η p ≤ a - ((ps.length + 1 : ℕ) : ℝ) * δ p := by
            rw [hscale] at hd
            dsimp [y]
            push_cast
            linarith
          dsimp only [y] at hvalid
          simp only [score, rank, Nat.cast_zero, zero_mul, add_zero, rating, ite_eq_left hvalid, le_refl]

end LongTails.Proofs.CorruptedFirstOrderProgress
