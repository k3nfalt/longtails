import LongTails.Proofs.RegretMatchingStep
import LongTails.Proofs.Execution

open Finset

namespace OracleTemplate.RegretMatchingPotential

lemma bound_of_potential {R S Φ D E : ℕ → ℝ} {K B c c' : ℝ} (hK : 0 < K) (hc : 0 ≤ c)
    (hc' : 0 ≤ c') (hR0 : R 0 < K) (hR : ∀ t, R (t + 1) ≤ R t + c * D t)
    (hS : ∀ t, S (t + 1) ≤ S t + c' * E t) (hSmono : ∀ t, S t ≤ S (t + 1))
    (hS0 : ∀ t, 0 ≤ S t) (hD : ∀ t, 0 ≤ D t ∧ D t ≤ B) (hE : ∀ t, 0 ≤ E t ∧ E t ≤ B)
    (hΦ : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ B)
    (hlag : ∀ t, D t - 2 * (S (t + 2) - S t) ≤ Φ (t + 1) - Φ t)
    (hhigh : ∀ t, K ≤ R t → K ≤ S t → (D t + E t) / 2 ≤ Φ (t + 1) - Φ t) (T : ℕ) :
    R T ≤ K + c * B + 2 * c * (B + 2 * (2 * K + 3 * c' * B)) := by
  set Wc := 2 * K + 3 * c' * B
  have hB : 0 ≤ B := (hD 0).1.trans (hD 0).2
  let Ψ : ℕ → ℝ := fun t => Φ t + 2 * min (S t + S (t + 1)) Wc
  have hΨ : ∀ t, K ≤ R t → Ψ t + D t / 2 ≤ Ψ (t + 1) := by
    intro t hRt
    have hW : S t + S (t + 1) ≤ S (t + 1) + S (t + 2) := by
      linarith [hSmono t, hSmono (t + 1)]
    show Φ t + 2 * min (S t + S (t + 1)) Wc + D t / 2 ≤
      Φ (t + 1) + 2 * min (S (t + 1) + S (t + 1 + 1)) Wc
    rcases le_or_gt K (S t) with hSt | hSt
    · have := hhigh t hRt hSt
      have := min_le_min_right Wc hW
      linarith [(hE t).1]
    · have h1 : S (t + 1) ≤ K + c' * B := by
        linarith [hS t, mul_le_mul_of_nonneg_left (hE t).2 hc']
      have h2 : S (t + 2) ≤ K + 2 * c' * B := by
        linarith [hS (t + 1), mul_le_mul_of_nonneg_left (hE (t + 1)).2 hc']
      rw [min_eq_left (by linarith), min_eq_left (by linarith)]
      linarith [hlag t, (hD t).1]
  have hΨb : ∀ t, 0 ≤ Ψ t ∧ Ψ t ≤ B + 2 * Wc := by
    intro t
    have hWc : 0 ≤ Wc := by positivity
    constructor
    · have := le_min (add_nonneg (hS0 t) (hS0 (t + 1))) hWc
      linarith [(hΦ t).1]
    · have := min_le_right (S t + S (t + 1)) Wc
      linarith [(hΦ t).2]
  have inv : ∀ T, R T < K ∨ ∃ τ, R T ≤ K + c * B + 2 * c * (Ψ T - Ψ τ) := by
    intro T
    induction T with
    | zero => exact Or.inl hR0
    | succ T ih =>
      right
      rcases lt_or_ge (R T) K with h | h
      · refine ⟨T + 1, ?_⟩
        nlinarith [hR T, mul_le_mul_of_nonneg_left (hD T).2 hc]
      · rcases ih with h' | ⟨τ, hτ⟩
        · exact absurd h' (not_lt.mpr h)
        · refine ⟨τ, ?_⟩
          have := mul_le_mul_of_nonneg_left (hΨ T h) (by linarith : (0 : ℝ) ≤ 2 * c)
          nlinarith [hR T]
  rcases inv T with h | ⟨τ, hτ⟩
  · have : 0 ≤ c * B + 2 * c * (B + 2 * Wc) := by positivity
    linarith
  · have := mul_le_mul_of_nonneg_left
      (show Ψ T - Ψ τ ≤ B + 2 * Wc by linarith [(hΨb T).2, (hΨb τ).1]) (by linarith : (0 : ℝ) ≤ 2 * c)
    linarith

lemma count_le {N : ℕ → ℝ} {bad : ℕ → Prop} [DecidablePred bad] {e : ℝ}
    (hmono : ∀ t, N t ≤ N (t + 1)) (hbad : ∀ t, bad t → e ≤ N (t + 1) - N t) (T : ℕ) :
    e * ((range T).filter bad).card ≤ N T - N 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp)]
      push_cast
      linarith [hbad T h]
    · linarith [hmono T]

lemma exists_good {Nx Ny : ℕ → ℝ} {bx byy : ℕ → Prop} [DecidablePred bx] [DecidablePred byy]
    {e : ℝ} (he : 0 < e) (hx : ∀ t, Nx t ≤ Nx (t + 1)) (hy : ∀ t, Ny t ≤ Ny (t + 1))
    (hbx : ∀ t, bx t → e ≤ Nx (t + 1) - Nx t) (hby : ∀ t, byy t → e ≤ Ny (t + 1) - Ny t)
    {T : ℕ} (hT : Nx T - Nx 0 + (Ny T - Ny 0) < e * T) : ∃ t < T, ¬ bx t ∧ ¬ byy t := by
  by_contra hc
  push Not at hc
  have hsub : range T ⊆ (range T).filter bx ∪ (range T).filter byy := by
    intro t ht
    have ht' := mem_range.mp ht
    by_cases h : bx t
    · exact mem_union_left _ (mem_filter.mpr ⟨ht, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨ht, hc t ht' h⟩)
  have hcard : (T : ℝ) ≤ ((range T).filter bx).card + ((range T).filter byy).card := by
    have := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_range] at this
    exact_mod_cast this
  have h1 := count_le hx hbx T
  have h2 := count_le hy hby T
  nlinarith


variable {m n : ℕ}

noncomputable def payoffX (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) : Fin m → ℝ :=
  fun i => ∑ j, A i j * y j

noncomputable def payoffY (C : Fin m → Fin n → ℝ) (x : Fin m → ℝ) : Fin n → ℝ :=
  fun j => ∑ i, C i j * x i

noncomputable def traj (A C : Fin m → Fin n → ℝ) : ℕ → (Fin m → ℝ) × (Fin n → ℝ)
  | 0 => (0, 0)
  | t + 1 => (step (traj A C t).1 (payoffX A (strategy (traj A C t).2)),
      step (traj A C t).2 (payoffY C (strategy (traj A C t).1)))

noncomputable def pot (P : Fin m → Fin n → ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * P i j * y j

structure Game (A C P : Fin m → Fin n → ℝ) (B : ℝ) : Prop where
  hm : 0 < m
  hn : 0 < n
  hB : 0 < B
  hP : ∀ i j, 0 ≤ P i j ∧ P i j ≤ B
  hA : ∀ i i' j, A i j - A i' j = P i j - P i' j
  hC : ∀ i j j', C i j - C i j' = P i j - P i j'

lemma trajX_succ (A C : Fin m → Fin n → ℝ) (t : ℕ) :
    (traj A C (t + 1)).1 = step (traj A C t).1 (payoffX A (strategy (traj A C t).2)) := rfl

lemma trajY_succ (A C : Fin m → Fin n → ℝ) (t : ℕ) :
    (traj A C (t + 1)).2 = step (traj A C t).2 (payoffY C (strategy (traj A C t).1)) := rfl

lemma traj_nonneg (A C : Fin m → Fin n → ℝ) :
    ∀ t, (∀ a, 0 ≤ (traj A C t).1 a) ∧ ∀ b, 0 ≤ (traj A C t).2 b
  | 0 => ⟨fun _ => le_refl _, fun _ => le_refl _⟩
  | _ + 1 => ⟨step_nonneg _ _, step_nonneg _ _⟩

lemma value_payoffX {A C P : Fin m → Fin n → ℝ} {B : ℝ} (G : Game A C P B) (y : Fin n → ℝ) :
    ∃ k, ∀ x : Fin m → ℝ, ∑ i, x i = 1 → value x (payoffX A y) = pot P x y + k := by
  obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, ∀ i j, A i j = P i j + c j :=
    ⟨fun j => A ⟨0, G.hm⟩ j - P ⟨0, G.hm⟩ j, fun i j => by linarith [G.hA i ⟨0, G.hm⟩ j]⟩
  refine ⟨∑ j, c j * y j, fun x hx => ?_⟩
  unfold value payoffX pot
  simp only [hc]
  calc ∑ i, x i * ∑ j, (P i j + c j) * y j
      = ∑ i, (∑ j, x i * P i j * y j + x i * ∑ j, c j * y j) := sum_congr rfl fun i _ => by
          rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
    _ = _ := by rw [sum_add_distrib, ← sum_mul, hx, one_mul]

lemma value_payoffY {A C P : Fin m → Fin n → ℝ} {B : ℝ} (G : Game A C P B) (x : Fin m → ℝ) :
    ∃ k, ∀ y : Fin n → ℝ, ∑ j, y j = 1 → value y (payoffY C x) = pot P x y + k := by
  obtain ⟨d, hd⟩ : ∃ d : Fin m → ℝ, ∀ i j, C i j = P i j + d i :=
    ⟨fun i => C i ⟨0, G.hn⟩ - P i ⟨0, G.hn⟩, fun i j => by linarith [G.hC i j ⟨0, G.hn⟩]⟩
  refine ⟨∑ i, d i * x i, fun y hy => ?_⟩
  unfold value payoffY pot
  simp only [hd]
  calc ∑ j, y j * ∑ i, (P i j + d i) * x i
      = ∑ j, (∑ i, x i * P i j * y j + y j * ∑ i, d i * x i) := sum_congr rfl fun j _ => by
          rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
    _ = _ := by rw [sum_add_distrib, ← sum_mul, hy, one_mul, sum_comm]

lemma spreadX {A C P : Fin m → Fin n → ℝ} {B : ℝ} (G : Game A C P B) {y : Fin n → ℝ}
    (hy : ∀ j, 0 ≤ y j) (hs : ∑ j, y j = 1) (a b : Fin m) :
    payoffX A y a - payoffX A y b ≤ B := by
  unfold payoffX
  rw [← sum_sub_distrib]
  calc ∑ j, (A a j * y j - A b j * y j) ≤ ∑ j, B * y j := sum_le_sum fun j _ => by
        rw [← sub_mul, G.hA a b j]
        exact mul_le_mul_of_nonneg_right (by linarith [G.hP a j, G.hP b j]) (hy j)
    _ = B := by rw [← mul_sum, hs, mul_one]

lemma spreadY {A C P : Fin m → Fin n → ℝ} {B : ℝ} (G : Game A C P B) {x : Fin m → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i = 1) (a b : Fin n) :
    payoffY C x a - payoffY C x b ≤ B := by
  unfold payoffY
  rw [← sum_sub_distrib]
  calc ∑ i, (C i a * x i - C i b * x i) ≤ ∑ i, B * x i := sum_le_sum fun i _ => by
        rw [← sub_mul, G.hC i a b]
        exact mul_le_mul_of_nonneg_right (by linarith [G.hP i a, G.hP i b]) (hx i)
    _ = B := by rw [← mul_sum, hs, mul_one]

lemma pot_bounds {A C P : Fin m → Fin n → ℝ} {B : ℝ} (G : Game A C P B) {x : Fin m → ℝ}
    {y : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) (hxs : ∑ i, x i = 1) (hy : ∀ j, 0 ≤ y j)
    (hys : ∑ j, y j = 1) : 0 ≤ pot P x y ∧ pot P x y ≤ B := by
  unfold pot
  constructor
  · exact sum_nonneg fun i _ => sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hx i) (G.hP i j).1) (hy j)
  · calc ∑ i, ∑ j, x i * P i j * y j ≤ ∑ i, ∑ j, x i * B * y j :=
          sum_le_sum fun i _ => sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (G.hP i j).2 (hx i)) (hy j)
      _ = B := by
          have : ∑ i, ∑ j, x i * B * y j = ∑ i, x i * B * ∑ j, y j :=
            sum_congr rfl fun i _ => (mul_sum _ _ _).symm
          rw [this, hys]; simp only [mul_one]; rw [← sum_mul, hxs, one_mul]

lemma cross_le {A C P : Fin m → Fin n → ℝ} {B : ℝ} (G : Game A C P B)
    (x x' : Fin m → ℝ) (y y' : Fin n → ℝ) :
    |pot P x' y' - pot P x' y - pot P x y' + pot P x y| ≤
      B * ((∑ i, |x' i - x i|) * ∑ j, |y' j - y j|) := by
  have e : pot P x' y' - pot P x' y - pot P x y' + pot P x y =
      ∑ i, ∑ j, (x' i - x i) * P i j * (y' j - y j) := by
    unfold pot
    simp only [← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [e, sum_mul_sum, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (G.hP i j).1]
  have := mul_le_mul_of_nonneg_left (G.hP i j).2 (abs_nonneg (x' i - x i))
  nlinarith [abs_nonneg (y' j - y j), abs_nonneg (x' i - x i)]


section Run

variable {A C P : Fin m → Fin n → ℝ} {B : ℝ} (G : Game A C P B)
include G

lemma stratX_simplex (t : ℕ) :
    (∀ a, 0 ≤ strategy (traj A C t).1 a) ∧ ∑ a, strategy (traj A C t).1 a = 1 :=
  ⟨strategy_nonneg (traj_nonneg A C t).1, strategy_sum G.hm⟩

lemma stratY_simplex (t : ℕ) :
    (∀ b, 0 ≤ strategy (traj A C t).2 b) ∧ ∑ b, strategy (traj A C t).2 b = 1 :=
  ⟨strategy_nonneg (traj_nonneg A C t).2, strategy_sum G.hn⟩

lemma gainX_eq (t : ℕ) :
    gain (traj A C t).1 (payoffX A (strategy (traj A C t).2)) =
      pot P (strategy (traj A C (t + 1)).1) (strategy (traj A C t).2) -
        pot P (strategy (traj A C t).1) (strategy (traj A C t).2) := by
  obtain ⟨k, hk⟩ := value_payoffX G (strategy (traj A C t).2)
  unfold gain
  rw [← trajX_succ]
  rw [hk _ (stratX_simplex G (t + 1)).2, hk _ (stratX_simplex G t).2]
  ring

lemma gainY_eq (t : ℕ) :
    gain (traj A C t).2 (payoffY C (strategy (traj A C t).1)) =
      pot P (strategy (traj A C t).1) (strategy (traj A C (t + 1)).2) -
        pot P (strategy (traj A C t).1) (strategy (traj A C t).2) := by
  obtain ⟨k, hk⟩ := value_payoffY G (strategy (traj A C t).1)
  unfold gain
  rw [← trajY_succ]
  rw [hk _ (stratY_simplex G (t + 1)).2, hk _ (stratY_simplex G t).2]
  ring

lemma lagX (t : ℕ) :
    -(2 * (size (traj A C (t + 2)).1 - size (traj A C t).1)) ≤
      pot P (strategy (traj A C (t + 1)).1) (strategy (traj A C (t + 1)).2) -
        pot P (strategy (traj A C t).1) (strategy (traj A C (t + 1)).2) := by
  have h := lagged_le G.hm (traj_nonneg A C t).1 (payoffX A (strategy (traj A C t).2))
    (payoffX A (strategy (traj A C (t + 1)).2))
  obtain ⟨k, hk⟩ := value_payoffX G (strategy (traj A C (t + 1)).2)
  have e : value (strategy (traj A C t).1) (regret (traj A C (t + 1)).1
      (payoffX A (strategy (traj A C (t + 1)).2))) =
      value (strategy (traj A C t).1) (payoffX A (strategy (traj A C (t + 1)).2)) -
        value (strategy (traj A C (t + 1)).1) (payoffX A (strategy (traj A C (t + 1)).2)) :=
    value_shift G.hm _ _ _
  rw [hk _ (stratX_simplex G t).2, hk _ (stratX_simplex G (t + 1)).2] at e
  change value (strategy (traj A C t).1) (regret (traj A C (t + 1)).1
      (payoffX A (strategy (traj A C (t + 1)).2))) ≤
      2 * (size (traj A C (t + 2)).1 - size (traj A C t).1) at h
  linarith

lemma lagY (t : ℕ) :
    -(2 * (size (traj A C (t + 2)).2 - size (traj A C t).2)) ≤
      pot P (strategy (traj A C (t + 1)).1) (strategy (traj A C (t + 1)).2) -
        pot P (strategy (traj A C (t + 1)).1) (strategy (traj A C t).2) := by
  have h := lagged_le G.hn (traj_nonneg A C t).2 (payoffY C (strategy (traj A C t).1))
    (payoffY C (strategy (traj A C (t + 1)).1))
  obtain ⟨k, hk⟩ := value_payoffY G (strategy (traj A C (t + 1)).1)
  have e : value (strategy (traj A C t).2) (regret (traj A C (t + 1)).2
      (payoffY C (strategy (traj A C (t + 1)).1))) =
      value (strategy (traj A C t).2) (payoffY C (strategy (traj A C (t + 1)).1)) -
        value (strategy (traj A C (t + 1)).2) (payoffY C (strategy (traj A C (t + 1)).1)) :=
    value_shift G.hn _ _ _
  rw [hk _ (stratY_simplex G t).2, hk _ (stratY_simplex G (t + 1)).2] at e
  change value (strategy (traj A C t).2) (regret (traj A C (t + 1)).2
      (payoffY C (strategy (traj A C (t + 1)).1))) ≤
      2 * (size (traj A C (t + 2)).2 - size (traj A C t).2) at h
  linarith

lemma high_step (t : ℕ) (hKx : 4 * B * (m + n) ≤ size (traj A C t).1)
    (hKy : 4 * B * (m + n) ≤ size (traj A C t).2) :
    (gain (traj A C t).1 (payoffX A (strategy (traj A C t).2)) +
      gain (traj A C t).2 (payoffY C (strategy (traj A C t).1))) / 2 ≤
      pot P (strategy (traj A C (t + 1)).1) (strategy (traj A C (t + 1)).2) -
        pot P (strategy (traj A C t).1) (strategy (traj A C t).2) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast G.hm
  have hn : (0 : ℝ) < n := by exact_mod_cast G.hn
  have hK : 0 < 4 * B * (m + n) := by have := G.hB; positivity
  have hx := move_sq_le G.hm (traj_nonneg A C t).1 (payoffX A (strategy (traj A C t).2)) hK hKx
  have hy := move_sq_le G.hn (traj_nonneg A C t).2 (payoffY C (strategy (traj A C t).1)) hK hKy
  have hc := cross_le G (strategy (traj A C t).1) (strategy (traj A C (t + 1)).1)
    (strategy (traj A C t).2) (strategy (traj A C (t + 1)).2)
  have gx := gainX_eq G t
  have gy := gainY_eq G t
  have gx0 := gain_nonneg G.hm (traj_nonneg A C t).1 (payoffX A (strategy (traj A C t).2))
  have gy0 := gain_nonneg G.hn (traj_nonneg A C t).2 (payoffY C (strategy (traj A C t).1))
  change 4 * B * (m + n) * (∑ a, |strategy (traj A C (t + 1)).1 a - strategy (traj A C t).1 a|) ^ 2 ≤
    4 * m * gain (traj A C t).1 (payoffX A (strategy (traj A C t).2)) at hx
  change 4 * B * (m + n) * (∑ b, |strategy (traj A C (t + 1)).2 b - strategy (traj A C t).2 b|) ^ 2 ≤
    4 * n * gain (traj A C t).2 (payoffY C (strategy (traj A C t).1)) at hy
  set dx := ∑ a, |strategy (traj A C (t + 1)).1 a - strategy (traj A C t).1 a|
  set dy := ∑ b, |strategy (traj A C (t + 1)).2 b - strategy (traj A C t).2 b|
  set Dx := gain (traj A C t).1 (payoffX A (strategy (traj A C t).2))
  set Dy := gain (traj A C t).2 (payoffY C (strategy (traj A C t).1))
  have hs : (0 : ℝ) < 4 * (m + n) := by positivity
  have bx : B * dx ^ 2 ≤ Dx := by
    have : 4 * (m + n) * (B * dx ^ 2) ≤ 4 * (m + n) * Dx := by nlinarith
    exact le_of_mul_le_mul_left this hs
  have byy : B * dy ^ 2 ≤ Dy := by
    have : 4 * (m + n) * (B * dy ^ 2) ≤ 4 * (m + n) * Dy := by nlinarith
    exact le_of_mul_le_mul_left this hs
  have hxy : B * (dx * dy) ≤ (Dx + Dy) / 2 := by
    nlinarith [mul_nonneg G.hB.le (sq_nonneg (dx - dy))]
  have := neg_abs_le (pot P (strategy (traj A C (t + 1)).1) (strategy (traj A C (t + 1)).2) -
    pot P (strategy (traj A C (t + 1)).1) (strategy (traj A C t).2) -
    pot P (strategy (traj A C t).1) (strategy (traj A C (t + 1)).2) +
    pot P (strategy (traj A C t).1) (strategy (traj A C t).2))
  linarith

lemma size_bound (T : ℕ) :
    size (traj A C T).1 ≤ 100 * B * (m + n) ^ 2 ∧ size (traj A C T).2 ≤ 100 * B * (m + n) ^ 2 := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast G.hm
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast G.hn
  have hB := G.hB
  have hK : 0 < 4 * B * (m + n) := by positivity
  have s0 : ∀ {k : ℕ} (Q : Fin k → ℝ), Q = 0 → size Q < 4 * B * (m + n) := by
    intro k Q h; subst h; simp [size, sqNorm]; exact hK
  have hΦ : ∀ t, 0 ≤ pot P (strategy (traj A C t).1) (strategy (traj A C t).2) ∧
      pot P (strategy (traj A C t).1) (strategy (traj A C t).2) ≤ B := fun t =>
    pot_bounds G (stratX_simplex G t).1 (stratX_simplex G t).2 (stratY_simplex G t).1
      (stratY_simplex G t).2
  have hDx : ∀ t, 0 ≤ gain (traj A C t).1 (payoffX A (strategy (traj A C t).2)) ∧
      gain (traj A C t).1 (payoffX A (strategy (traj A C t).2)) ≤ B := fun t =>
    ⟨gain_nonneg G.hm (traj_nonneg A C t).1 _, gain_le G.hm (traj_nonneg A C t).1
      (spreadX G (stratY_simplex G t).1 (stratY_simplex G t).2)⟩
  have hDy : ∀ t, 0 ≤ gain (traj A C t).2 (payoffY C (strategy (traj A C t).1)) ∧
      gain (traj A C t).2 (payoffY C (strategy (traj A C t).1)) ≤ B := fun t =>
    ⟨gain_nonneg G.hn (traj_nonneg A C t).2 _, gain_le G.hn (traj_nonneg A C t).2
      (spreadY G (stratX_simplex G t).1 (stratX_simplex G t).2)⟩
  have hRx : ∀ t, size (traj A C (t + 1)).1 ≤ size (traj A C t).1 +
      2 * m * gain (traj A C t).1 (payoffX A (strategy (traj A C t).2)) := fun t => by
    have := charge G.hm (traj_nonneg A C t).1 (payoffX A (strategy (traj A C t).2))
    rw [← trajX_succ] at this; linarith
  have hRy : ∀ t, size (traj A C (t + 1)).2 ≤ size (traj A C t).2 +
      2 * n * gain (traj A C t).2 (payoffY C (strategy (traj A C t).1)) := fun t => by
    have := charge G.hn (traj_nonneg A C t).2 (payoffY C (strategy (traj A C t).1))
    rw [← trajY_succ] at this; linarith
  have mx : ∀ t, size (traj A C t).1 ≤ size (traj A C (t + 1)).1 := fun t =>
    size_mono G.hm (traj_nonneg A C t).1 _
  have my : ∀ t, size (traj A C t).2 ≤ size (traj A C (t + 1)).2 := fun t =>
    size_mono G.hn (traj_nonneg A C t).2 _
  have key : 4 * B * (m + n) + 2 * n * B + 2 * (2 * n) * (B + 2 * (2 * (4 * B * (m + n)) +
      3 * (2 * m) * B)) ≤ 100 * B * (m + n) ^ 2 ∧ 4 * B * (m + n) + 2 * m * B + 2 * (2 * m) *
      (B + 2 * (2 * (4 * B * (m + n)) + 3 * (2 * n) * B)) ≤ 100 * B * (m + n) ^ 2 := by
    have k1 : (0 : ℝ) ≤ 100 * (m : ℝ) ^ 2 + 88 * m * n + 36 * n ^ 2 - 4 * m - 10 * n := by nlinarith
    have k2 : (0 : ℝ) ≤ 100 * (n : ℝ) ^ 2 + 88 * m * n + 36 * m ^ 2 - 4 * n - 10 * m := by nlinarith
    constructor
    · nlinarith [mul_nonneg hB.le k1]
    · nlinarith [mul_nonneg hB.le k2]
  constructor
  · have := bound_of_potential (R := fun t => size (traj A C t).1)
      (S := fun t => size (traj A C t).2)
      (Φ := fun t => pot P (strategy (traj A C t).1) (strategy (traj A C t).2))
      (D := fun t => gain (traj A C t).1 (payoffX A (strategy (traj A C t).2)))
      (E := fun t => gain (traj A C t).2 (payoffY C (strategy (traj A C t).1)))
      (c := 2 * m) (c' := 2 * n) hK (by positivity) (by positivity) (s0 _ rfl) hRx hRy my
      (fun t => size_nonneg _) hDx hDy hΦ
      (fun t => by
        have := lagY G t; have := gainX_eq G t
        linarith)
      (fun t h1 h2 => high_step G t h1 h2) T
    linarith [key.2]
  · have := bound_of_potential (R := fun t => size (traj A C t).2)
      (S := fun t => size (traj A C t).1)
      (Φ := fun t => pot P (strategy (traj A C t).1) (strategy (traj A C t).2))
      (D := fun t => gain (traj A C t).2 (payoffY C (strategy (traj A C t).1)))
      (E := fun t => gain (traj A C t).1 (payoffX A (strategy (traj A C t).2)))
      (c := 2 * n) (c' := 2 * m) hK (by positivity) (by positivity) (s0 _ rfl) hRy hRx mx
      (fun t => size_nonneg _) hDy hDx hΦ
      (fun t => by
        have := lagX G t; have := gainY_eq G t
        linarith)
      (fun t h1 h2 => by have := high_step G t h2 h1; linarith) T
    linarith [key.1]

end Run

end OracleTemplate.RegretMatchingPotential
