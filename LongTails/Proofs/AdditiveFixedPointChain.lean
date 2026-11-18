import Mathlib.Tactic

namespace LongTails.Proofs.AdditiveFixedPointChain

def orient (b : Bool) (v : ℝ) : ℝ := if b then v else -v

lemma orient_involutive (b : Bool) (v : ℝ) : orient b (orient b v) = v := by
  cases b <;> simp [orient]

lemma orient_dist (b : Bool) (u v : ℝ) : |orient b u - orient b v| = |u - v| := by
  cases b
  · simpa only [orient, Bool.false_eq_true, ite_false, neg_sub_neg] using abs_sub_comm v u
  · rfl

def move (h u v : ℝ) : ℝ := min (u + h) (max (u - h) v)

lemma move_size {h : ℝ} (hh : 0 ≤ h) (u v : ℝ) : |move h u v - u| ≤ h := by
  rw [abs_le]
  unfold move
  constructor
  · have := le_min (show u - h ≤ u + h by linarith) (le_max_left (u - h) v)
    linarith
  · have := min_le_left (u + h) (max (u - h) v)
    linarith

lemma move_interior {h u v e : ℝ} (he : e < h) (hu : |move h u v - u| ≤ e) :
    |v - u| ≤ e := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans hu
  unfold move at hu
  rw [abs_le] at hu ⊢
  rcases le_total v (u - h) with hv | hv
  · rw [max_eq_left hv, min_eq_right (by linarith)] at hu
    linarith
  · rw [max_eq_right hv] at hu
    rcases le_total v (u + h) with hv' | hv'
    · rwa [min_eq_right hv'] at hu
    · rw [min_eq_left hv'] at hu
      linarith

def score (a : ℝ) (s : ℕ → Bool) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | i + 1 => min (score a s x i) (max 0 (orient (s i) (x i)))

def step (a h : ℝ) (s : ℕ → Bool) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  move h (x i) (orient (s i) (score a s x i))

lemma score_nonneg {a : ℝ} (ha : 0 ≤ a) (s : ℕ → Bool) (x : ℕ → ℝ) (i : ℕ) :
    0 ≤ score a s x i := by
  induction i with
  | zero => exact ha
  | succ i ih => exact le_min ih (le_max_left _ _)

lemma score_failure {a : ℝ} (ha : 0 ≤ a) (s : ℕ → Bool) (x : ℕ → ℝ) {i j : ℕ}
    (hij : i < j) (hx : orient (s i) (x i) ≤ 0) : score a s x j = 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hij) with hij | rfl
    · simp [score, ih hij, le_max_left (0 : ℝ)]
    · simp [score, max_eq_left hx, min_eq_right (score_nonneg ha s x i)]

lemma signs_of_residual {a h e : ℝ} {s : ℕ → Bool} {x : ℕ → ℝ} {m : ℕ}
    (he : 0 ≤ e) (hh : e < h) (ha : (m : ℝ) * e < a)
    (hr : ∀ i < m, |step a h s x i - x i| ≤ e) :
    ∀ i < m, 0 < orient (s i) (x i) := by
  have hstep (i : ℕ) (hi : i < m) : score a s x i - e ≤ orient (s i) (x i) := by
    have hb := move_interior hh (hr i hi)
    rw [← orient_dist (s i), orient_involutive] at hb
    linarith [(abs_le.mp hb).2]
  have hscore (i : ℕ) (hi : i ≤ m) : a - i * e ≤ score a s x i := by
    induction i with
    | zero => simp [score]
    | succ i ih =>
      have h := ih (by omega)
      have h' := hstep i (by omega)
      simp only [score, Nat.cast_succ, add_mul, one_mul]
      apply le_min
      · linarith
      · exact le_trans (by linarith : a - (i * e + e) ≤ orient (s i) (x i)) (le_max_right _ _)
  intro i hi
  have h := hscore i (by omega)
  have h' := hstep i hi
  have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
  nlinarith [mul_le_mul_of_nonneg_right hi' he]

lemma max_close {u v w z r : ℝ} (hu : |u - v| ≤ r) (hw : |w - z| ≤ r) :
    |max u w - max v z| ≤ r := by
  rw [abs_le] at *
  constructor
  · have := max_le (show v ≤ max u w + r by linarith [le_max_left u w])
      (show z ≤ max u w + r by linarith [le_max_right u w])
    linarith
  · have := max_le (show u ≤ max v z + r by linarith [le_max_left v z])
      (show w ≤ max v z + r by linarith [le_max_right v z])
    linarith

lemma min_close {u v w z r : ℝ} (hu : |u - v| ≤ r) (hw : |w - z| ≤ r) :
    |min u w - min v z| ≤ r := by
  rw [abs_le] at *
  constructor
  · have := le_min (show min v z - r ≤ u by linarith [min_le_left v z])
      (show min v z - r ≤ w by linarith [min_le_right v z])
    linarith
  · have := le_min (show min u w - r ≤ v by linarith [min_le_left u w])
      (show min u w - r ≤ z by linarith [min_le_right u w])
    linarith

lemma score_close (a : ℝ) (s : ℕ → Bool) {x y : ℕ → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hxy : ∀ i, |x i - y i| ≤ r) (i : ℕ) : |score a s x i - score a s y i| ≤ r := by
  induction i with
  | zero => simpa [score] using hr
  | succ i ih =>
    apply min_close ih
    apply max_close (by simpa using hr)
    rw [orient_dist]
    exact hxy i

end LongTails.Proofs.AdditiveFixedPointChain
