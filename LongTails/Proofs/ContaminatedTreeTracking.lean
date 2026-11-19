import LongTails.Proofs.LeonCalendar

namespace LongTails.Proofs.ContaminatedTreeTracking

open LongTails.Algorithms.LeonCalendar

def child (j t : ℕ) (i : Fin 4) := t + 1 + i.val * (levels j).length

def total (v : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, t => v 0 t
  | j+1, t => v (j+1) t + ∑ i : Fin 4, total v j (child j t i)

def leafMass (error : ℕ → ℝ) := total (fun l t => if l = 0 then error t else 0)

def damage (bad : ℕ → Bool) := total (fun l t => if bad t then (4 : ℝ) ^ (2*l) else 0)

inductive Tracked (s : ℝ) (error : ℕ → ℝ) (bad : ℕ → Bool) : ℕ → ℕ → Prop
  | leaf (t) : Tracked s error bad 0 t
  | fork (j t) (move : ∀ i, error (child j t i) ≤ error t + 11 * (4 : ℝ)^j * s)
      (exact : ∀ i, error t ≤ 2*s → bad (child j t i) = false → error (child j t i) ≤ 2*s)
      (branches : ∀ i, Tracked s error bad j (child j t i)) : Tracked s error bad (j+1) t

lemma damage_nonneg (bad : ℕ → Bool) (j t) : 0 ≤ damage bad j t := by
  induction j generalizing t with
  | zero => simp [damage, total]; split <;> norm_num
  | succ j ih =>
    change 0 ≤ (if bad t then (4 : ℝ)^(2*(j+1)) else 0) + ∑ i, damage bad j (child j t i)
    apply add_nonneg
    · split <;> positivity
    · exact Finset.sum_nonneg (fun i _ => ih _)

lemma damage_at (bad : ℕ → Bool) {j t} (h : bad t = true) : (4 : ℝ)^(2*j) ≤ damage bad j t := by
  cases j with
  | zero => simp [damage,total,h]
  | succ j =>
    change _ ≤ (if bad t then _ else 0) + ∑ i, damage bad j (child j t i)
    simp only [h, ↓reduceIte]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => damage_nonneg _ _ _))

lemma subtree_motion {s : ℝ} {e : ℕ → ℝ} {b : ℕ → Bool} {j t : ℕ}
    (h : Tracked s e b j t) :
    leafMass e j t ≤ (4 : ℝ)^j * (e t + 11/3 * ((4 : ℝ)^j - 1) * s) := by
  induction h with
  | leaf t => simp [leafMass,total]
  | fork j t move _ _ ih =>
    change (if j+1 = 0 then e t else 0) + ∑ i, leafMass e j (child j t i) ≤ _
    simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
    have hi (i) := (ih i).trans (mul_le_mul_of_nonneg_left
      (add_le_add_left (move i) (11 / 3 * ((4 : ℝ)^j-1)*s)) (show 0 ≤ (4 : ℝ)^j by positivity))
    apply (Finset.sum_le_sum (fun i _ => hi i)).trans_eq
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, pow_succ]
    ring

lemma leaf_error_sum {s : ℝ} (hs : 0 ≤ s) {e : ℕ → ℝ} {b : ℕ → Bool} {j t : ℕ}
    (h : Tracked s e b j t) (hmove : e t ≤ 2*s + 11 * (4 : ℝ)^j * s)
    (hgood : b t = false → e t ≤ 2*s) :
    leafMass e j t ≤ (4 : ℝ)^j * (2*s) + 15*s * damage b j t := by
  induction j generalizing t with
  | zero =>
    change e t ≤ _ + 15 * s * (if b t then _ else 0)
    cases hb : b t <;> simp [hb] at hmove hgood ⊢ <;> linarith
  | succ j ih =>
    cases hb : b t with
    | true =>
      have hd := mul_le_mul_of_nonneg_left (damage_at (j := j+1) b hb) (show 0 ≤ 15*s by positivity)
      have hh := subtree_motion h
      have hm := mul_le_mul_of_nonneg_left hmove (show 0 ≤ (4 : ℝ)^(j+1) by positivity)
      rw [pow_mul'] at hd
      nlinarith only [hd, hh, hm, show 0 ≤ (4 : ℝ)^(j+1) * s by positivity,
        show 0 ≤ ((4 : ℝ)^(j+1))^2 * s by positivity]
    | false =>
      cases h with
      | fork _ _ move exact branches =>
        have hi (i) := ih (branches i) ((move i).trans (add_le_add_left (hgood hb) _))
          (exact i (hgood hb))
        change (if j+1 = 0 then e t else 0) + ∑ i, leafMass e j (child j t i) ≤
          (4 : ℝ)^(j+1) * (2*s) + 15*s * ((if b t then _ else 0) + ∑ i, damage b j (child j t i))
        simp only [Nat.succ_ne_zero, ↓reduceIte, hb, Bool.false_eq_true, zero_add]
        apply (Finset.sum_le_sum (fun i _ => hi i)).trans_eq
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum, pow_succ]
        ring

end LongTails.Proofs.ContaminatedTreeTracking
