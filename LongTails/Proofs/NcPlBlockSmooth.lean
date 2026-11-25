import LongTails.Proofs.NcPlBlock

open scoped BigOperators

namespace LongTails.Proofs.NcPlBlockSmooth

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlProfiles
open LongTails.Proofs.NcPlBlockPL LongTails.Proofs.NcPlSchedule LongTails.Proofs.NcPlCalc
open LongTails.Proofs.NcPlBlock

structure Scales (n : ℕ) (r : ℕ → ℝ) (ρ : ℝ) : Prop where
  hρ : 0 < ρ
  ge : ∀ k, k ≤ n → ρ ≤ r k
  sq : ∀ k, k ≤ n → r k ^ 2 = wt (n + 1) (k + 1)

namespace Scales

variable {n : ℕ} {r : ℕ → ℝ} {ρ : ℝ}

lemma pos (S : Scales n r ρ) {k : ℕ} (hk : k ≤ n) : 0 < r k := lt_of_lt_of_le S.hρ (S.ge k hk)

lemma le_one (S : Scales n r ρ) {k : ℕ} (hk : k ≤ n) : r k ≤ 1 := by
  have h1 := S.sq k hk
  have h2 := wt_le_one (Nat.succ_pos n) (k + 1)
  have h3 := S.pos hk
  nlinarith

lemma last (S : Scales n r ρ) : r n = 1 := by
  have h1 := S.sq n le_rfl
  rw [wt_top (n + 1) (Nat.succ_pos n)] at h1
  have h3 := S.pos (le_refl n)
  nlinarith

lemma wt_le_sq (S : Scales n r ρ) {k : ℕ} (hk : k ≤ n) : wt (n + 1) k ≤ r k ^ 2 := by
  rw [S.sq k hk]
  exact wt_mono (by omega)

lemma mono (S : Scales n r ρ) {k : ℕ} (hk : k + 1 ≤ n) : r k ≤ r (k + 1) := by
  have h1 := S.sq k (by omega)
  have h2 := S.sq (k + 1) hk
  have h3 : wt (n + 1) (k + 1) ≤ wt (n + 1) (k + 1 + 1) := wt_mono (by omega)
  have ha := S.pos (show k ≤ n by omega)
  have hb := S.pos hk
  nlinarith

end Scales

lemma gate_scaled_lip {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    |gate (a / r) - gate (b / r)| ≤ 2 / r * |a - b| := div_lip hr gate_lipschitz a b

lemma push_scaled_lip {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    |push (a / r) - push (b / r)| ≤ 1 / 3 / r * |a - b| := by
  apply div_lip hr (K := 1 / 3) (fun x y => ?_) a b
  have := push_lipschitz x y
  linarith

lemma dgate_scaled_lip {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    |dgate (a / r) / r - dgate (b / r) / r| ≤ 16 / r ^ 2 * |a - b| := by
  have h := div_lip hr dgate_lipschitz a b
  have e : dgate (a / r) / r - dgate (b / r) / r = (dgate (a / r) - dgate (b / r)) / r := by ring
  rw [e, abs_div, abs_of_pos hr, div_le_iff₀ hr]
  have e2 : 16 / r ^ 2 * |a - b| * r = 16 / r * |a - b| := by field_simp
  rw [e2]
  exact h

lemma dpush_scaled_lip {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    |dpush (a / r) / r - dpush (b / r) / r| ≤ 4 / 3 / r ^ 2 * |a - b| := by
  have h := div_lip hr dpush_lipschitz a b
  have e : dpush (a / r) / r - dpush (b / r) / r = (dpush (a / r) - dpush (b / r)) / r := by ring
  rw [e, abs_div, abs_of_pos hr, div_le_iff₀ hr]
  have e2 : 4 / 3 / r ^ 2 * |a - b| * r = 4 / 3 / r * |a - b| := by field_simp
  rw [e2]
  exact h

lemma gate_scaled_model {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    |gate (b / r) - gate (a / r) - dgate (a / r) / r * (b - a)| ≤ 16 / r ^ 2 * (b - a) ^ 2 :=
  scaled_model (by norm_num) hr gate_hasDerivAt dgate_lipschitz a b

lemma push_scaled_model {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    |push (b / r) - push (a / r) - dpush (a / r) / r * (b - a)| ≤ 4 / 3 / r ^ 2 * (b - a) ^ 2 :=
  scaled_model (by norm_num) hr push_hasDerivAt dpush_lipschitz a b

section Model

variable {n : ℕ} {r : ℕ → ℝ} {ρ : ℝ}

lemma reward_split (α : ℕ → ℝ) (β : ℝ) (y : ℕ → ℝ) :
    rewardVal n r α β y =
      ∑ j ∈ Finset.range n, α (j + 1) * (gate (y j / r j) * push (y (j + 1) / r (j + 1))) +
        α 0 * push (y 0 / r 0) + β * gate (y n / r n) := by
  unfold rewardVal
  rw [Finset.sum_range_succ']
  have e0 : α 0 * gprev r y 0 * push (y 0 / r 0) = α 0 * push (y 0 / r 0) := by simp [gprev]
  rw [e0]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [gprev_succ]
  ring

lemma grad_split (α : ℕ → ℝ) (β : ℝ) (y δ : ℕ → ℝ) :
    ∑ k ∈ Finset.range (n + 1), rewardGrad n r α β y k * δ k =
      ∑ j ∈ Finset.range n, α (j + 1) *
        (dgate (y j / r j) / r j * push (y (j + 1) / r (j + 1)) * δ j +
          gate (y j / r j) * (dpush (y (j + 1) / r (j + 1)) / r (j + 1)) * δ (j + 1)) +
        α 0 * (dpush (y 0 / r 0) / r 0 * δ 0) + β * (dgate (y n / r n) / r n * δ n) := by
  have h1 : ∑ k ∈ Finset.range (n + 1), α k * gprev r y k * dpush (y k / r k) / r k * δ k =
      ∑ j ∈ Finset.range n, α (j + 1) *
        (gate (y j / r j) * (dpush (y (j + 1) / r (j + 1)) / r (j + 1)) * δ (j + 1)) +
        α 0 * (dpush (y 0 / r 0) / r 0 * δ 0) := by
    rw [Finset.sum_range_succ']
    have e0 : α 0 * gprev r y 0 * dpush (y 0 / r 0) / r 0 * δ 0 =
        α 0 * (dpush (y 0 / r 0) / r 0 * δ 0) := by
      simp only [gprev, ite_true]
      ring
    rw [e0]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [gprev_succ]
    ring
  have h2 : ∑ k ∈ Finset.range (n + 1), cval n α β r y k * dgate (y k / r k) / r k * δ k =
      ∑ j ∈ Finset.range n, α (j + 1) *
        (dgate (y j / r j) / r j * push (y (j + 1) / r (j + 1)) * δ j) +
        β * (dgate (y n / r n) / r n * δ n) := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [cval, ite_eq_left (Finset.mem_range.mp hj)]
      ring
    · rw [cval, ite_eq_right (lt_irrefl n)]
      ring
  have h3 : ∑ k ∈ Finset.range (n + 1), rewardGrad n r α β y k * δ k =
      ∑ k ∈ Finset.range (n + 1), α k * gprev r y k * dpush (y k / r k) / r k * δ k +
        ∑ k ∈ Finset.range (n + 1), cval n α β r y k * dgate (y k / r k) / r k * δ k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    unfold rewardGrad
    ring
  rw [h3, h1, h2]
  have e : ∑ j ∈ Finset.range n, α (j + 1) *
      (dgate (y j / r j) / r j * push (y (j + 1) / r (j + 1)) * δ j +
        gate (y j / r j) * (dpush (y (j + 1) / r (j + 1)) / r (j + 1)) * δ (j + 1)) =
      ∑ j ∈ Finset.range n, α (j + 1) *
        (gate (y j / r j) * (dpush (y (j + 1) / r (j + 1)) / r (j + 1)) * δ (j + 1)) +
      ∑ j ∈ Finset.range n, α (j + 1) *
        (dgate (y j / r j) / r j * push (y (j + 1) / r (j + 1)) * δ j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [e]
  ring

lemma sum_shift_sq_le (δ : ℕ → ℝ) :
    ∑ j ∈ Finset.range n, (δ j ^ 2 + δ (j + 1) ^ 2) ≤
      2 * ∑ k ∈ Finset.range (n + 1), δ k ^ 2 := by
  rw [Finset.sum_add_distrib]
  have h1 : ∑ j ∈ Finset.range n, δ j ^ 2 ≤ ∑ k ∈ Finset.range (n + 1), δ k ^ 2 := by
    rw [Finset.sum_range_succ]
    nlinarith [sq_nonneg (δ n)]
  have h2 : ∑ j ∈ Finset.range n, δ (j + 1) ^ 2 ≤ ∑ k ∈ Finset.range (n + 1), δ k ^ 2 := by
    rw [Finset.sum_range_succ' (fun k => δ k ^ 2)]
    nlinarith [sq_nonneg (δ 0)]
  linarith

theorem reward_model (S : Scales n r ρ) {α : ℕ → ℝ} {β B : ℝ} (hα0 : ∀ j, j ≤ n → 0 ≤ α j)
    (hα1 : ∀ j, j ≤ n → α j ≤ 1) (hβ0 : 0 ≤ β) (hβ : β ≤ B) (y y' : ℕ → ℝ) :
    |rewardVal n r α β y' - rewardVal n r α β y -
        ∑ k ∈ Finset.range (n + 1), rewardGrad n r α β y k * (y' k - y k)| ≤
      (40 + 16 * B) / ρ ^ 2 * ∑ k ∈ Finset.range (n + 1), (y' k - y k) ^ 2 := by
  have hρ := S.hρ
  have hB : 0 ≤ B := le_trans hβ0 hβ
  rw [reward_split, reward_split, grad_split]
  set δ : ℕ → ℝ := fun k => y' k - y k with hδ
  have hrk : ∀ k, k ≤ n → 0 < r k := fun k hk => S.pos hk
  have hinv : ∀ k, k ≤ n → 1 / r k ^ 2 ≤ 1 / ρ ^ 2 := by
    intro k hk
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ hρ.le (S.ge k hk) 2
  have hinv2 : ∀ j k, j ≤ n → k ≤ n → 1 / (r j * r k) ≤ 1 / ρ ^ 2 := by
    intro j k hj hk
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]
    exact mul_le_mul (S.ge j hj) (S.ge k hk) hρ.le (hrk j hj).le
  have hS0 : 0 ≤ ∑ k ∈ Finset.range (n + 1), δ k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hmid : ∀ j, j ∈ Finset.range n →
      |α (j + 1) * (gate (y' j / r j) * push (y' (j + 1) / r (j + 1))) -
        α (j + 1) * (gate (y j / r j) * push (y (j + 1) / r (j + 1))) -
        α (j + 1) * (dgate (y j / r j) / r j * push (y (j + 1) / r (j + 1)) * δ j +
          gate (y j / r j) * (dpush (y (j + 1) / r (j + 1)) / r (j + 1)) * δ (j + 1))| ≤
      18 / ρ ^ 2 * (δ j ^ 2 + δ (j + 1) ^ 2) := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hr1 := hrk j (by omega)
    have hr2 := hrk (j + 1) (by omega)
    have hp := pair_model (y := gate (y j / r j)) (y' := gate (y' j / r j))
      (dy := dgate (y j / r j) / r j) (δb := δ j) (z := push (y (j + 1) / r (j + 1)))
      (z' := push (y' (j + 1) / r (j + 1))) (dz := dpush (y (j + 1) / r (j + 1)) / r (j + 1))
      (δc := δ (j + 1)) (MB := 1) (MC := 1) (LB := 2 / r j) (LC := 1 / 3 / r (j + 1))
      (KB := 16 / r j ^ 2) (KC := 4 / 3 / r (j + 1) ^ 2)
      (by rw [abs_of_nonneg (gate_nonneg _)]; exact gate_le_one _)
      (by rw [abs_of_nonneg (push_nonneg _)]; exact push_le_one _)
      (gate_scaled_lip hr1 _ _) (push_scaled_lip hr2 _ _)
      (gate_scaled_model hr1 _ _) (push_scaled_model hr2 _ _)
      (by positivity) (by positivity) (by positivity) (by positivity)
    have hc : 16 / r j ^ 2 * 1 + 1 * (4 / 3 / r (j + 1) ^ 2) + 2 / r j * (1 / 3 / r (j + 1)) ≤
        18 / ρ ^ 2 := by
      have a1 := hinv j (by omega)
      have a2 := hinv (j + 1) (by omega)
      have a3 := hinv2 j (j + 1) (by omega) (by omega)
      have e1 : 16 / r j ^ 2 * 1 = 16 * (1 / r j ^ 2) := by ring
      have e2 : 1 * (4 / 3 / r (j + 1) ^ 2) = 4 / 3 * (1 / r (j + 1) ^ 2) := by ring
      have e3 : 2 / r j * (1 / 3 / r (j + 1)) = 2 / 3 * (1 / (r j * r (j + 1))) := by
        field_simp
      have e4 : 18 / ρ ^ 2 = 18 * (1 / ρ ^ 2) := by ring
      rw [e1, e2, e3, e4]
      linarith
    have hα := hα0 (j + 1) (by omega)
    have hα' := hα1 (j + 1) (by omega)
    have hsq : 0 ≤ δ j ^ 2 + δ (j + 1) ^ 2 := by positivity
    have e : α (j + 1) * (gate (y' j / r j) * push (y' (j + 1) / r (j + 1))) -
        α (j + 1) * (gate (y j / r j) * push (y (j + 1) / r (j + 1))) -
        α (j + 1) * (dgate (y j / r j) / r j * push (y (j + 1) / r (j + 1)) * δ j +
          gate (y j / r j) * (dpush (y (j + 1) / r (j + 1)) / r (j + 1)) * δ (j + 1)) =
        α (j + 1) * (gate (y' j / r j) * push (y' (j + 1) / r (j + 1)) -
          gate (y j / r j) * push (y (j + 1) / r (j + 1)) -
          (dgate (y j / r j) / r j * push (y (j + 1) / r (j + 1)) * δ j +
            gate (y j / r j) * (dpush (y (j + 1) / r (j + 1)) / r (j + 1)) * δ (j + 1))) := by ring
    rw [e, abs_mul, abs_of_nonneg hα]
    calc α (j + 1) * _ ≤ 1 * ((16 / r j ^ 2 * 1 + 1 * (4 / 3 / r (j + 1) ^ 2) +
          2 / r j * (1 / 3 / r (j + 1))) * (δ j ^ 2 + δ (j + 1) ^ 2)) :=
          mul_le_mul hα' hp (abs_nonneg _) zero_le_one
      _ ≤ 18 / ρ ^ 2 * (δ j ^ 2 + δ (j + 1) ^ 2) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right hc hsq
  have hfirst : |α 0 * push (y' 0 / r 0) - α 0 * push (y 0 / r 0) -
      α 0 * (dpush (y 0 / r 0) / r 0 * δ 0)| ≤ 4 / 3 / ρ ^ 2 * δ 0 ^ 2 := by
    have hr0 := hrk 0 (Nat.zero_le n)
    have hm := push_scaled_model hr0 (y 0) (y' 0)
    have e : α 0 * push (y' 0 / r 0) - α 0 * push (y 0 / r 0) -
        α 0 * (dpush (y 0 / r 0) / r 0 * δ 0) =
        α 0 * (push (y' 0 / r 0) - push (y 0 / r 0) - dpush (y 0 / r 0) / r 0 * (y' 0 - y 0)) := by
      simp only [hδ]; ring
    rw [e, abs_mul, abs_of_nonneg (hα0 0 (Nat.zero_le n))]
    have a1 := hinv 0 (Nat.zero_le n)
    have hc : 4 / 3 / r 0 ^ 2 ≤ 4 / 3 / ρ ^ 2 := by
      have e1 : 4 / 3 / r 0 ^ 2 = 4 / 3 * (1 / r 0 ^ 2) := by ring
      have e2 : 4 / 3 / ρ ^ 2 = 4 / 3 * (1 / ρ ^ 2) := by ring
      rw [e1, e2]
      linarith
    calc α 0 * _ ≤ 1 * (4 / 3 / r 0 ^ 2 * (y' 0 - y 0) ^ 2) :=
          mul_le_mul (hα1 0 (Nat.zero_le n)) hm (abs_nonneg _) zero_le_one
      _ ≤ 4 / 3 / ρ ^ 2 * δ 0 ^ 2 := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  have hlast : |β * gate (y' n / r n) - β * gate (y n / r n) -
      β * (dgate (y n / r n) / r n * δ n)| ≤ 16 * B / ρ ^ 2 * δ n ^ 2 := by
    have hrn := hrk n le_rfl
    have hm := gate_scaled_model hrn (y n) (y' n)
    have e : β * gate (y' n / r n) - β * gate (y n / r n) - β * (dgate (y n / r n) / r n * δ n) =
        β * (gate (y' n / r n) - gate (y n / r n) - dgate (y n / r n) / r n * (y' n - y n)) := by
      simp only [hδ]; ring
    rw [e, abs_mul, abs_of_nonneg hβ0]
    have a1 := hinv n le_rfl
    have hc : 16 / r n ^ 2 ≤ 16 / ρ ^ 2 := by
      have e1 : 16 / r n ^ 2 = 16 * (1 / r n ^ 2) := by ring
      have e2 : 16 / ρ ^ 2 = 16 * (1 / ρ ^ 2) := by ring
      rw [e1, e2]
      linarith
    calc β * _ ≤ B * (16 / r n ^ 2 * (y' n - y n) ^ 2) :=
          mul_le_mul hβ hm (abs_nonneg _) hB
      _ ≤ B * (16 / ρ ^ 2 * δ n ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) hB
      _ = 16 * B / ρ ^ 2 * δ n ^ 2 := by ring
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hmid)
  rw [← Finset.mul_sum] at hsum
  have hshift := sum_shift_sq_le (n := n) δ
  have h0mem : δ 0 ^ 2 ≤ ∑ k ∈ Finset.range (n + 1), δ k ^ 2 :=
    Finset.single_le_sum (f := fun k => δ k ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_range.mpr (Nat.succ_pos n))
  have hnmem : δ n ^ 2 ≤ ∑ k ∈ Finset.range (n + 1), δ k ^ 2 :=
    Finset.single_le_sum (f := fun k => δ k ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have c1 : 18 / ρ ^ 2 * ∑ j ∈ Finset.range n, (δ j ^ 2 + δ (j + 1) ^ 2) ≤
      36 / ρ ^ 2 * ∑ k ∈ Finset.range (n + 1), δ k ^ 2 := by
    have := mul_le_mul_of_nonneg_left hshift (by positivity : (0 : ℝ) ≤ 18 / ρ ^ 2)
    calc _ ≤ 18 / ρ ^ 2 * (2 * ∑ k ∈ Finset.range (n + 1), δ k ^ 2) := this
      _ = _ := by ring
  have c2 : 4 / 3 / ρ ^ 2 * δ 0 ^ 2 ≤ 4 / ρ ^ 2 * ∑ k ∈ Finset.range (n + 1), δ k ^ 2 := by
    have h1 : 4 / 3 / ρ ^ 2 * δ 0 ^ 2 ≤ 4 / 3 / ρ ^ 2 * ∑ k ∈ Finset.range (n + 1), δ k ^ 2 :=
      mul_le_mul_of_nonneg_left h0mem (by positivity)
    have h2 : 4 / 3 / ρ ^ 2 * ∑ k ∈ Finset.range (n + 1), δ k ^ 2 ≤
        4 / ρ ^ 2 * ∑ k ∈ Finset.range (n + 1), δ k ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hS0
      rw [div_le_div_iff_of_pos_right hρ2]
      norm_num
    linarith
  have c3 : 16 * B / ρ ^ 2 * δ n ^ 2 ≤ 16 * B / ρ ^ 2 * ∑ k ∈ Finset.range (n + 1), δ k ^ 2 :=
    mul_le_mul_of_nonneg_left hnmem (by positivity)
  have key : ∑ j ∈ Finset.range n, α (j + 1) * (gate (y' j / r j) * push (y' (j + 1) / r (j + 1))) +
      α 0 * push (y' 0 / r 0) + β * gate (y' n / r n) -
      (∑ j ∈ Finset.range n, α (j + 1) * (gate (y j / r j) * push (y (j + 1) / r (j + 1))) +
        α 0 * push (y 0 / r 0) + β * gate (y n / r n)) -
      (∑ j ∈ Finset.range n, α (j + 1) *
        (dgate (y j / r j) / r j * push (y (j + 1) / r (j + 1)) * δ j +
          gate (y j / r j) * (dpush (y (j + 1) / r (j + 1)) / r (j + 1)) * δ (j + 1)) +
        α 0 * (dpush (y 0 / r 0) / r 0 * δ 0) + β * (dgate (y n / r n) / r n * δ n)) =
      ∑ j ∈ Finset.range n, (α (j + 1) * (gate (y' j / r j) * push (y' (j + 1) / r (j + 1))) -
        α (j + 1) * (gate (y j / r j) * push (y (j + 1) / r (j + 1))) -
        α (j + 1) * (dgate (y j / r j) / r j * push (y (j + 1) / r (j + 1)) * δ j +
          gate (y j / r j) * (dpush (y (j + 1) / r (j + 1)) / r (j + 1)) * δ (j + 1))) +
      (α 0 * push (y' 0 / r 0) - α 0 * push (y 0 / r 0) - α 0 * (dpush (y 0 / r 0) / r 0 * δ 0)) +
      (β * gate (y' n / r n) - β * gate (y n / r n) - β * (dgate (y n / r n) / r n * δ n)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring
  rw [key]
  have tri := abs_add_three
    (∑ j ∈ Finset.range n, (α (j + 1) * (gate (y' j / r j) * push (y' (j + 1) / r (j + 1))) -
        α (j + 1) * (gate (y j / r j) * push (y (j + 1) / r (j + 1))) -
        α (j + 1) * (dgate (y j / r j) / r j * push (y (j + 1) / r (j + 1)) * δ j +
          gate (y j / r j) * (dpush (y (j + 1) / r (j + 1)) / r (j + 1)) * δ (j + 1))))
    (α 0 * push (y' 0 / r 0) - α 0 * push (y 0 / r 0) - α 0 * (dpush (y 0 / r 0) / r 0 * δ 0))
    (β * gate (y' n / r n) - β * gate (y n / r n) - β * (dgate (y n / r n) / r n * δ n))
  have efin : (40 + 16 * B) / ρ ^ 2 * ∑ k ∈ Finset.range (n + 1), δ k ^ 2 =
      36 / ρ ^ 2 * ∑ k ∈ Finset.range (n + 1), δ k ^ 2 +
        4 / ρ ^ 2 * ∑ k ∈ Finset.range (n + 1), δ k ^ 2 +
        16 * B / ρ ^ 2 * ∑ k ∈ Finset.range (n + 1), δ k ^ 2 := by ring
  rw [efin]
  linarith

end Model

section Lipschitz

variable {n : ℕ} {r : ℕ → ℝ} {ρ : ℝ}

lemma amp_lipschitz (k : ℕ) (a b : ℝ) : |amp (n + 1) k a - amp (n + 1) k b| ≤ |a - b| := by
  have h := lipschitz_of_deriv (amp (n + 1) k) (damp (n + 1) k) 1 (amp_hasDerivAt k)
    (fun z => by rw [abs_of_nonneg (damp_nonneg k z)]; exact damp_le_one k z) a b
  simpa using h

lemma ampT_lipschitz (a b : ℝ) : |ampT (n + 1) a - ampT (n + 1) b| ≤ |a - b| := by
  have h := lipschitz_of_deriv (ampT (n + 1)) (dampT (n + 1)) 1 ampT_hasDerivAt
    (fun z => by rw [abs_of_nonneg (dampT_nonneg z)]; exact dampT_le_one z) a b
  simpa using h

lemma alphaSeq_lip (k : ℕ) (a b : ℝ) :
    |alphaSeq (n + 1) a k - alphaSeq (n + 1) b k| ≤ wt (n + 1) k * |a - b| := by
  have e : alphaSeq (n + 1) a k - alphaSeq (n + 1) b k =
      wt (n + 1) k * (amp (n + 1) k a - amp (n + 1) k b) := by unfold alphaSeq; ring
  rw [e, abs_mul, abs_of_pos (wt_pos k)]
  exact mul_le_mul_of_nonneg_left (amp_lipschitz k a b) (wt_pos k).le

lemma alphaSeq_abs (k : ℕ) (a : ℝ) : |alphaSeq (n + 1) a k| ≤ wt (n + 1) k := by
  rw [abs_of_nonneg (alphaSeq_nonneg a k)]
  exact mul_le_of_le_one_right (wt_pos k).le (amp_le_one k a)

noncomputable def dprev (y y' : ℕ → ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else |y' (k - 1) - y (k - 1)|

noncomputable def dnext (n : ℕ) (y y' : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k < n then |y' (k + 1) - y (k + 1)| else 0

lemma dprev_nonneg (y y' : ℕ → ℝ) (k : ℕ) : 0 ≤ dprev y y' k := by
  unfold dprev
  split_ifs
  · exact le_rfl
  · exact abs_nonneg _

lemma dnext_nonneg (y y' : ℕ → ℝ) (k : ℕ) : 0 ≤ dnext n y y' k := by
  unfold dnext
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

lemma gprev_lip (S : Scales n r ρ) (y y' : ℕ → ℝ) {k : ℕ} (hk : k ≤ n) :
    wt (n + 1) k / r k * |gprev r y' k - gprev r y k| ≤ 2 * dprev y y' k := by
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    simp [gprev, dprev]
  · have hk1 : k - 1 ≤ n := by omega
    have hr1 := S.pos hk1
    have hrk := S.pos hk
    have hsq := S.sq (k - 1) hk1
    rw [Nat.sub_add_cancel h0] at hsq
    have hmono : r (k - 1) ≤ r k := by
      have := S.mono (k := k - 1) (by omega)
      rwa [Nat.sub_add_cancel h0] at this
    have hl := gate_scaled_lip hr1 (y' (k - 1)) (y (k - 1))
    have hne : k ≠ 0 := Nat.pos_iff_ne_zero.mp h0
    simp only [gprev, dprev, ite_eq_right hne]
    have hfac : wt (n + 1) k / r k * (2 / r (k - 1)) ≤ 2 := by
      rw [← hsq]
      have e : r (k - 1) ^ 2 / r k * (2 / r (k - 1)) = 2 * (r (k - 1) / r k) := by
        field_simp
      rw [e]
      have : r (k - 1) / r k ≤ 1 := (div_le_one hrk).mpr hmono
      linarith
    have hw0 : 0 ≤ wt (n + 1) k / r k := div_nonneg (wt_pos k).le hrk.le
    calc wt (n + 1) k / r k * |gate (y' (k - 1) / r (k - 1)) - gate (y (k - 1) / r (k - 1))|
        ≤ wt (n + 1) k / r k * (2 / r (k - 1) * |y' (k - 1) - y (k - 1)|) :=
          mul_le_mul_of_nonneg_left hl hw0
      _ = wt (n + 1) k / r k * (2 / r (k - 1)) * |y' (k - 1) - y (k - 1)| := by ring
      _ ≤ 2 * |y' (k - 1) - y (k - 1)| := mul_le_mul_of_nonneg_right hfac (abs_nonneg _)

lemma pushTerm_lip (S : Scales n r ρ) (s s' : ℝ) (y y' : ℕ → ℝ) {k : ℕ} (hk : k ≤ n) :
    |alphaSeq (n + 1) s' k * gprev r y' k * (dpush (y' k / r k) / r k) -
      alphaSeq (n + 1) s k * gprev r y k * (dpush (y k / r k) / r k)| ≤
      r k * |s' - s| + dprev y y' k + 2 * |y' k - y k| := by
  have hrk := S.pos hk
  have hwle := S.wt_le_sq hk
  have hw := wt_pos (N := n + 1) k
  have hMc : ∀ v : ℝ, |dpush (v / r k) / r k| ≤ 1 / 3 / r k := by
    intro v
    rw [abs_div, abs_of_pos hrk, abs_of_nonneg (dpush_nonneg _)]
    exact div_le_div_of_nonneg_right (dpush_le _) hrk.le
  have hMb : ∀ z : ℕ → ℝ, |gprev r z k| ≤ 1 := by
    intro z
    rw [abs_of_nonneg (gprev_nonneg r z k)]
    exact gprev_le_one r z k
  have h3 := prod3_lip (a := alphaSeq (n + 1) s k) (a' := alphaSeq (n + 1) s' k)
    (b := gprev r y k) (b' := gprev r y' k) (c := dpush (y k / r k) / r k)
    (c' := dpush (y' k / r k) / r k) (alphaSeq_abs k s) (hMb y) (hMb y') (hMc (y' k))
  have ha := alphaSeq_lip (n := n) k s' s
  have hb := gprev_lip S y y' hk
  have hc := dpush_scaled_lip hrk (y' k) (y k)
  have t1 : |alphaSeq (n + 1) s' k - alphaSeq (n + 1) s k| * 1 * (1 / 3 / r k) ≤ r k * |s' - s| := by
    have e : wt (n + 1) k * |s' - s| * 1 * (1 / 3 / r k) = wt (n + 1) k / r k / 3 * |s' - s| := by
      field_simp
    have h1 : |alphaSeq (n + 1) s' k - alphaSeq (n + 1) s k| * 1 * (1 / 3 / r k) ≤
        wt (n + 1) k * |s' - s| * 1 * (1 / 3 / r k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right ha (by norm_num)
    have h2 : wt (n + 1) k / r k / 3 ≤ r k := by
      rw [div_le_iff₀ (by norm_num), div_le_iff₀ hrk]
      nlinarith
    rw [e] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
  have t2 : wt (n + 1) k * |gprev r y' k - gprev r y k| * (1 / 3 / r k) ≤ dprev y y' k := by
    have e : wt (n + 1) k * |gprev r y' k - gprev r y k| * (1 / 3 / r k) =
        (wt (n + 1) k / r k * |gprev r y' k - gprev r y k|) / 3 := by field_simp
    rw [e]
    have := dprev_nonneg y y' k
    linarith
  have t3 : wt (n + 1) k * 1 * |dpush (y' k / r k) / r k - dpush (y k / r k) / r k| ≤
      2 * |y' k - y k| := by
    have h1 : wt (n + 1) k * 1 * |dpush (y' k / r k) / r k - dpush (y k / r k) / r k| ≤
        wt (n + 1) k * 1 * (4 / 3 / r k ^ 2 * |y' k - y k|) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    have h2 : wt (n + 1) k * 1 * (4 / 3 / r k ^ 2) ≤ 2 := by
      have e : wt (n + 1) k * 1 * (4 / 3 / r k ^ 2) = 4 / 3 * (wt (n + 1) k / r k ^ 2) := by
        field_simp
      rw [e]
      have : wt (n + 1) k / r k ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hwle
      linarith
    calc _ ≤ wt (n + 1) k * 1 * (4 / 3 / r k ^ 2 * |y' k - y k|) := h1
      _ = wt (n + 1) k * 1 * (4 / 3 / r k ^ 2) * |y' k - y k| := by ring
      _ ≤ 2 * |y' k - y k| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  linarith

lemma gateTerm_lip_bulk (S : Scales n r ρ) (s s' : ℝ) (y y' : ℕ → ℝ) {k : ℕ} (hk : k < n) :
    |alphaSeq (n + 1) s' (k + 1) * push (y' (k + 1) / r (k + 1)) * (dgate (y' k / r k) / r k) -
      alphaSeq (n + 1) s (k + 1) * push (y (k + 1) / r (k + 1)) * (dgate (y k / r k) / r k)| ≤
      2 * r k * |s' - s| + |y' (k + 1) - y (k + 1)| + 16 * |y' k - y k| := by
  have hrk := S.pos (show k ≤ n by omega)
  have hrk1 := S.pos (show k + 1 ≤ n by omega)
  have hsq := S.sq k (by omega)
  have hmono := S.mono (k := k) (by omega)
  have hMc : ∀ v : ℝ, |dgate (v / r k) / r k| ≤ 2 / r k := by
    intro v
    rw [abs_div, abs_of_pos hrk, abs_of_nonneg (dgate_nonneg _)]
    exact div_le_div_of_nonneg_right (dgate_le _) hrk.le
  have hMb : ∀ v : ℝ, |push (v / r (k + 1))| ≤ 1 := by
    intro v
    rw [abs_of_nonneg (push_nonneg _)]
    exact push_le_one _
  have h3 := prod3_lip (a := alphaSeq (n + 1) s (k + 1)) (a' := alphaSeq (n + 1) s' (k + 1))
    (b := push (y (k + 1) / r (k + 1))) (b' := push (y' (k + 1) / r (k + 1)))
    (c := dgate (y k / r k) / r k) (c' := dgate (y' k / r k) / r k)
    (alphaSeq_abs (k + 1) s) (hMb _) (hMb _) (hMc (y' k))
  have ha := alphaSeq_lip (n := n) (k + 1) s' s
  have hb := push_scaled_lip hrk1 (y' (k + 1)) (y (k + 1))
  have hc := dgate_scaled_lip hrk (y' k) (y k)
  have hr2 : 0 < r k ^ 2 := by positivity
  have t1 : |alphaSeq (n + 1) s' (k + 1) - alphaSeq (n + 1) s (k + 1)| * 1 * (2 / r k) ≤
      2 * r k * |s' - s| := by
    have h1 : |alphaSeq (n + 1) s' (k + 1) - alphaSeq (n + 1) s (k + 1)| * 1 * (2 / r k) ≤
        wt (n + 1) (k + 1) * |s' - s| * 1 * (2 / r k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right ha (by norm_num)
    have e : wt (n + 1) (k + 1) * |s' - s| * 1 * (2 / r k) = 2 * r k * |s' - s| := by
      rw [← hsq]
      field_simp
    rw [e] at h1
    exact h1
  have t2 : wt (n + 1) (k + 1) * |push (y' (k + 1) / r (k + 1)) - push (y (k + 1) / r (k + 1))| *
      (2 / r k) ≤ |y' (k + 1) - y (k + 1)| := by
    have h1 : wt (n + 1) (k + 1) *
        |push (y' (k + 1) / r (k + 1)) - push (y (k + 1) / r (k + 1))| * (2 / r k) ≤
        wt (n + 1) (k + 1) * (1 / 3 / r (k + 1) * |y' (k + 1) - y (k + 1)|) * (2 / r k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hb (wt_pos _).le
    have e : wt (n + 1) (k + 1) * (1 / 3 / r (k + 1) * |y' (k + 1) - y (k + 1)|) * (2 / r k) =
        2 / 3 * (r k / r (k + 1)) * |y' (k + 1) - y (k + 1)| := by
      rw [← hsq]
      field_simp
    rw [e] at h1
    have hq : r k / r (k + 1) ≤ 1 := (div_le_one hrk1).mpr hmono
    have hq0 : 0 ≤ r k / r (k + 1) := div_nonneg hrk.le hrk1.le
    have : 2 / 3 * (r k / r (k + 1)) * |y' (k + 1) - y (k + 1)| ≤ 1 * |y' (k + 1) - y (k + 1)| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    linarith
  have t3 : wt (n + 1) (k + 1) * 1 * |dgate (y' k / r k) / r k - dgate (y k / r k) / r k| ≤
      16 * |y' k - y k| := by
    have h1 : wt (n + 1) (k + 1) * 1 * |dgate (y' k / r k) / r k - dgate (y k / r k) / r k| ≤
        wt (n + 1) (k + 1) * 1 * (16 / r k ^ 2 * |y' k - y k|) :=
      mul_le_mul_of_nonneg_left hc (by have := wt_pos (N := n + 1) (k + 1); positivity)
    have e : wt (n + 1) (k + 1) * 1 * (16 / r k ^ 2 * |y' k - y k|) = 16 * |y' k - y k| := by
      rw [← hsq]
      field_simp
    rw [e] at h1
    exact h1
  linarith

lemma gateTerm_lip_last (S : Scales n r ρ) (s s' t t' : ℝ) (y y' : ℕ → ℝ) :
    |ampT (n + 1) s' * afun t' * (dgate (y' n / r n) / r n) -
      ampT (n + 1) s * afun t * (dgate (y n / r n) / r n)| ≤
      8 * |s' - s| + 2 * |t' - t| + 64 * |y' n - y n| := by
  have hrn := S.last
  have hMc : ∀ v : ℝ, |dgate (v / r n) / r n| ≤ 2 := by
    intro v
    rw [hrn, div_one, div_one, abs_of_nonneg (dgate_nonneg _)]
    exact dgate_le _
  have hMb : ∀ v : ℝ, |afun v| ≤ 4 := by
    intro v
    rw [abs_of_nonneg (afun_nonneg v)]
    exact afun_le v
  have hMa : |ampT (n + 1) s| ≤ 1 := by
    rw [abs_of_nonneg (ampT_nonneg s)]
    exact ampT_le_one s
  have h3 := prod3_lip (a := ampT (n + 1) s) (a' := ampT (n + 1) s') (b := afun t) (b' := afun t')
    (c := dgate (y n / r n) / r n) (c' := dgate (y' n / r n) / r n) hMa (hMb t) (hMb t')
    (hMc (y' n))
  have ha := ampT_lipschitz (n := n) s' s
  have hb := afun_lipschitz t' t
  have hc := dgate_scaled_lip (r := r n) (by rw [hrn]; norm_num) (y' n) (y n)
  rw [hrn] at hc
  have hc' : |dgate (y' n / r n) / r n - dgate (y n / r n) / r n| ≤ 16 * |y' n - y n| := by
    rw [hrn]
    simpa using hc
  nlinarith [abs_nonneg (s' - s), abs_nonneg (t' - t), abs_nonneg (y' n - y n)]

end Lipschitz

section Sums

variable {n : ℕ} {r : ℕ → ℝ} {ρ : ℝ}

lemma sq_add5 (a b c d e : ℝ) : (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e),
    sq_nonneg (d - e)]

lemma sq_add4 (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

lemma sq_add3 (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

lemma Scales.sum_sq_le (S : Scales n r ρ) : ∑ k ∈ Finset.range (n + 1), r k ^ 2 ≤ 6 := by
  have h1 : ∑ k ∈ Finset.range (n + 1), r k ^ 2 ≤
      ∑ k ∈ Finset.range (n + 1), 4 * wt (n + 1) k := by
    apply Finset.sum_le_sum
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [S.sq k hkn]
    exact wt_succ_le (by omega)
  rw [← Finset.mul_sum] at h1
  have h2 := cum_le (Nat.succ_pos n) (le_refl (n + 1))
  unfold cum at h2
  linarith

lemma sum_dprev_sq (y y' : ℕ → ℝ) :
    ∑ k ∈ Finset.range (n + 1), dprev y y' k ^ 2 ≤ ∑ k ∈ Finset.range (n + 1), (y' k - y k) ^ 2 := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ (fun k => (y' k - y k) ^ 2)]
  have e0 : dprev y y' 0 ^ 2 = 0 := by simp [dprev]
  have e1 : ∀ j ∈ Finset.range n, dprev y y' (j + 1) ^ 2 = (y' j - y j) ^ 2 := by
    intro j _
    simp [dprev, sq_abs]
  rw [e0, add_zero, Finset.sum_congr rfl e1]
  nlinarith [sq_nonneg (y' n - y n)]

lemma sum_dnext_sq (y y' : ℕ → ℝ) :
    ∑ k ∈ Finset.range (n + 1), dnext n y y' k ^ 2 ≤
      ∑ k ∈ Finset.range (n + 1), (y' k - y k) ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun k => (y' k - y k) ^ 2)]
  have e0 : dnext n y y' n ^ 2 = 0 := by simp [dnext]
  have e1 : ∀ j ∈ Finset.range n, dnext n y y' j ^ 2 = (y' (j + 1) - y (j + 1)) ^ 2 := by
    intro j hj
    simp [dnext, Finset.mem_range.mp hj, sq_abs]
  rw [e0, add_zero, Finset.sum_congr rfl e1]
  nlinarith [sq_nonneg (y' 0 - y 0)]

lemma rwGrad_coord_lip (S : Scales n r ρ) (s s' t t' : ℝ) (y y' : ℕ → ℝ) {k : ℕ} (hk : k ≤ n) :
    |rwGrad n r s' t' y' k - rwGrad n r s t y k| ≤
      3 * r k * |s' - s| + dprev y y' k + 18 * |y' k - y k| + dnext n y y' k +
        (if k = n then 8 * |s' - s| + 2 * |t' - t| + 64 * |y' n - y n| else 0) := by
  have hA := pushTerm_lip S s s' y y' hk
  have hrk := S.pos hk
  rcases Nat.lt_or_ge k n with hlt | hge
  · have hC := gateTerm_lip_bulk S s s' y y' hlt
    have e : ∀ (σ τ : ℝ) (z : ℕ → ℝ), rwGrad n r σ τ z k =
        alphaSeq (n + 1) σ k * gprev r z k * (dpush (z k / r k) / r k) +
          alphaSeq (n + 1) σ (k + 1) * push (z (k + 1) / r (k + 1)) * (dgate (z k / r k) / r k) := by
      intro σ τ z
      unfold rwGrad rewardGrad
      rw [cval, ite_eq_left hlt]
      ring
    rw [e s' t' y', e s t y, ite_eq_right (by omega)]
    have hn : dnext n y y' k = |y' (k + 1) - y (k + 1)| := by simp [dnext, hlt]
    rw [hn]
    have tri := abs_add_le
      (alphaSeq (n + 1) s' k * gprev r y' k * (dpush (y' k / r k) / r k) -
        alphaSeq (n + 1) s k * gprev r y k * (dpush (y k / r k) / r k))
      (alphaSeq (n + 1) s' (k + 1) * push (y' (k + 1) / r (k + 1)) * (dgate (y' k / r k) / r k) -
        alphaSeq (n + 1) s (k + 1) * push (y (k + 1) / r (k + 1)) * (dgate (y k / r k) / r k))
    have e2 : alphaSeq (n + 1) s' k * gprev r y' k * (dpush (y' k / r k) / r k) +
        alphaSeq (n + 1) s' (k + 1) * push (y' (k + 1) / r (k + 1)) * (dgate (y' k / r k) / r k) -
        (alphaSeq (n + 1) s k * gprev r y k * (dpush (y k / r k) / r k) +
          alphaSeq (n + 1) s (k + 1) * push (y (k + 1) / r (k + 1)) * (dgate (y k / r k) / r k)) =
        (alphaSeq (n + 1) s' k * gprev r y' k * (dpush (y' k / r k) / r k) -
          alphaSeq (n + 1) s k * gprev r y k * (dpush (y k / r k) / r k)) +
        (alphaSeq (n + 1) s' (k + 1) * push (y' (k + 1) / r (k + 1)) * (dgate (y' k / r k) / r k) -
          alphaSeq (n + 1) s (k + 1) * push (y (k + 1) / r (k + 1)) * (dgate (y k / r k) / r k)) := by
      ring
    rw [e2]
    have := dprev_nonneg y y' k
    have := mul_nonneg hrk.le (abs_nonneg (s' - s))
    linarith
  · have hkn : k = n := by omega
    subst hkn
    have hC := gateTerm_lip_last S s s' t t' y y'
    have e : ∀ (σ τ : ℝ) (z : ℕ → ℝ), rwGrad k r σ τ z k =
        alphaSeq (k + 1) σ k * gprev r z k * (dpush (z k / r k) / r k) +
          ampT (k + 1) σ * afun τ * (dgate (z k / r k) / r k) := by
      intro σ τ z
      unfold rwGrad rewardGrad
      rw [cval, ite_eq_right (lt_irrefl k)]
      ring
    rw [e s' t' y', e s t y, ite_eq_left rfl]
    have hn : dnext k y y' k = 0 := by simp [dnext]
    rw [hn]
    have tri := abs_add_le
      (alphaSeq (k + 1) s' k * gprev r y' k * (dpush (y' k / r k) / r k) -
        alphaSeq (k + 1) s k * gprev r y k * (dpush (y k / r k) / r k))
      (ampT (k + 1) s' * afun t' * (dgate (y' k / r k) / r k) -
        ampT (k + 1) s * afun t * (dgate (y k / r k) / r k))
    have e2 : alphaSeq (k + 1) s' k * gprev r y' k * (dpush (y' k / r k) / r k) +
        ampT (k + 1) s' * afun t' * (dgate (y' k / r k) / r k) -
        (alphaSeq (k + 1) s k * gprev r y k * (dpush (y k / r k) / r k) +
          ampT (k + 1) s * afun t * (dgate (y k / r k) / r k)) =
        (alphaSeq (k + 1) s' k * gprev r y' k * (dpush (y' k / r k) / r k) -
          alphaSeq (k + 1) s k * gprev r y k * (dpush (y k / r k) / r k)) +
        (ampT (k + 1) s' * afun t' * (dgate (y' k / r k) / r k) -
          ampT (k + 1) s * afun t * (dgate (y k / r k) / r k)) := by ring
    rw [e2]
    have := mul_nonneg hrk.le (abs_nonneg (s' - s))
    linarith [abs_nonneg (y' k - y k), abs_nonneg (s' - s), abs_nonneg (t' - t),
      dprev_nonneg y y' k]

theorem rwGrad_lip (S : Scales n r ρ) (s s' t t' : ℝ) (y y' : ℕ → ℝ) :
    ∑ k ∈ Finset.range (n + 1), (rwGrad n r s' t' y' k - rwGrad n r s t y k) ^ 2 ≤
      2 ^ 16 * ((s' - s) ^ 2 + (t' - t) ^ 2 + ∑ k ∈ Finset.range (n + 1), (y' k - y k) ^ 2) := by
  set D := ∑ k ∈ Finset.range (n + 1), (y' k - y k) ^ 2 with hD
  set e : ℕ → ℝ := fun k => if k = n then 8 * |s' - s| + 2 * |t' - t| + 64 * |y' n - y n| else 0
    with he
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hterm : ∀ k ∈ Finset.range (n + 1), (rwGrad n r s' t' y' k - rwGrad n r s t y k) ^ 2 ≤
      5 * (9 * (s' - s) ^ 2 * r k ^ 2 + dprev y y' k ^ 2 + 324 * (y' k - y k) ^ 2 +
        dnext n y y' k ^ 2 + e k ^ 2) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h := rwGrad_coord_lip S s s' t t' y y' hkn
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at h2
    have h5 := sq_add5 (3 * r k * |s' - s|) (dprev y y' k) (18 * |y' k - y k|) (dnext n y y' k)
      (e k)
    have e1 : (3 * r k * |s' - s|) ^ 2 = 9 * (s' - s) ^ 2 * r k ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]; ring
    have e2 : (18 * |y' k - y k|) ^ 2 = 324 * (y' k - y k) ^ 2 := by
      rw [mul_pow, sq_abs]; norm_num
    rw [e1, e2] at h5
    exact h2.trans h5
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := S.sum_sq_le
  have h2 := sum_dprev_sq (n := n) y y'
  have h3 := sum_dnext_sq (n := n) y y'
  have h4 : ∑ k ∈ Finset.range (n + 1), e k ^ 2 =
      (8 * |s' - s| + 2 * |t' - t| + 64 * |y' n - y n|) ^ 2 := by
    rw [Finset.sum_range_succ]
    have hz : ∑ k ∈ Finset.range n, e k ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have : k ≠ n := (Finset.mem_range.mp hk).ne
      simp [he, this]
    rw [hz, zero_add]
    simp [he]
  have h5 := sq_add3 (8 * |s' - s|) (2 * |t' - t|) (64 * |y' n - y n|)
  have e3 : (8 * |s' - s|) ^ 2 = 64 * (s' - s) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  have e4 : (2 * |t' - t|) ^ 2 = 4 * (t' - t) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  have e5 : (64 * |y' n - y n|) ^ 2 = 4096 * (y' n - y n) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  rw [e3, e4, e5] at h5
  have hn : (y' n - y n) ^ 2 ≤ D :=
    Finset.single_le_sum (f := fun k => (y' k - y k) ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  rw [h4]
  have hs2 := sq_nonneg (s' - s)
  have ht2 := sq_nonneg (t' - t)
  have h6 : 9 * (s' - s) ^ 2 * ∑ k ∈ Finset.range (n + 1), r k ^ 2 ≤ 54 * (s' - s) ^ 2 := by
    nlinarith
  nlinarith

end Sums

section Front

variable {n : ℕ} {r : ℕ → ℝ} {ρ : ℝ}

lemma pos_diff_mono {c d a b : ℝ} (hcd : c ≤ d) (hab : a ≤ b) :
    pos (a - c) - pos (a - d) ≤ pos (b - c) - pos (b - d) := by
  simp only [pos, max_def]
  split_ifs <;> linarith

lemma damp_diff (k : ℕ) (s s' : ℝ) :
    wt (n + 1) k * |damp (n + 1) k s' - damp (n + 1) k s| ≤
      wt (n + 1) k * |s' - s| +
        |(pos (s' - cum (n + 1) k) - pos (s' - cum (n + 1) (k + 1))) -
          (pos (s - cum (n + 1) k) - pos (s - cum (n + 1) (k + 1)))| := by
  have hw := wt_pos (N := n + 1) k
  set R := ramp (wt (n + 1) k) (s - cum (n + 1) k) with hR
  set R' := ramp (wt (n + 1) k) (s' - cum (n + 1) k) with hR'
  set D := dramp (wt (n + 1) k) (s - cum (n + 1) k) with hD
  set D' := dramp (wt (n + 1) k) (s' - cum (n + 1) k) with hD'
  have hR0 : 0 ≤ R := ramp_nonneg hw _
  have hD'0 : 0 ≤ D' := dramp_nonneg hw _
  have hD'1 : D' ≤ 1 := dramp_le_one hw _
  have hc0 := dcap_nonneg hR0
  have hc1 := dcap_le_one hR0
  have hRl : |R' - R| ≤ |s' - s| := by
    have := ramp_lipschitz hw (s' - cum (n + 1) k) (s - cum (n + 1) k)
    have e : s' - cum (n + 1) k - (s - cum (n + 1) k) = s' - s := by ring
    rwa [e] at this
  have hcl := dcap_lipschitz R' R
  have e : damp (n + 1) k s' - damp (n + 1) k s = (dcap R' - dcap R) * D' + dcap R * (D' - D) := by
    simp only [damp, ← hR, ← hR', ← hD, ← hD']
    ring
  have h1 : |damp (n + 1) k s' - damp (n + 1) k s| ≤ |s' - s| + |D' - D| := by
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hD'0, abs_of_nonneg hc0]
    have a1 : |dcap R' - dcap R| * D' ≤ |s' - s| * 1 :=
      mul_le_mul (hcl.trans hRl) hD'1 hD'0 (abs_nonneg _)
    have a2 : dcap R * |D' - D| ≤ 1 * |D' - D| := mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
    linarith
  have e2 : wt (n + 1) k * |D' - D| =
      |(pos (s' - cum (n + 1) k) - pos (s' - cum (n + 1) (k + 1))) -
        (pos (s - cum (n + 1) k) - pos (s - cum (n + 1) (k + 1)))| := by
    rw [← wt_dramp, ← wt_dramp, ← mul_sub, abs_mul, abs_of_pos hw]
  rw [← e2]
  have := mul_le_mul_of_nonneg_left h1 hw.le
  linarith

lemma damp_sum_lip_aux {s s' : ℝ} (hss : s ≤ s') :
    ∑ k ∈ Finset.range (n + 1), wt (n + 1) k * |damp (n + 1) k s' - damp (n + 1) k s| ≤
      3 * |s' - s| := by
  have habs : |s' - s| = s' - s := abs_of_nonneg (by linarith)
  have hterm : ∀ k ∈ Finset.range (n + 1),
      wt (n + 1) k * |damp (n + 1) k s' - damp (n + 1) k s| ≤
        wt (n + 1) k * |s' - s| +
          ((if 0 ≤ k then pos (s' - cum (n + 1) k) - pos (s' - cum (n + 1) (k + 1)) else 0) -
            (if 0 ≤ k then pos (s - cum (n + 1) k) - pos (s - cum (n + 1) (k + 1)) else 0)) := by
    intro k _
    have h := damp_diff (n := n) k s s'
    have hm := pos_diff_mono (cum_mono (N := n + 1) (Nat.le_succ k)) hss
    have hm' : pos (s - cum (n + 1) k) - pos (s - cum (n + 1) (k + 1)) ≤
        pos (s' - cum (n + 1) k) - pos (s' - cum (n + 1) (k + 1)) := hm
    rw [abs_of_nonneg (sub_nonneg.mpr hm')] at h
    rw [ite_eq_left (Nat.zero_le k), ite_eq_left (Nat.zero_le k)]
    exact h
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, telescope s' 0 (n + 1) (Nat.zero_le _),
    telescope s 0 (n + 1) (Nat.zero_le _), ← Finset.sum_mul]
  have hc := cum_le (Nat.succ_pos n) (le_refl (n + 1))
  unfold cum at hc
  have h0 : cum (n + 1) 0 = 0 := by simp [cum]
  have hp1 := pos_lipschitz (s' - cum (n + 1) 0) (s - cum (n + 1) 0)
  have e : s' - cum (n + 1) 0 - (s - cum (n + 1) 0) = s' - s := by ring
  rw [e] at hp1
  have hp2 : pos (s - cum (n + 1) (n + 1)) ≤ pos (s' - cum (n + 1) (n + 1)) := by
    simp only [pos]
    exact max_le_max (by linarith) le_rfl
  have hp3 := le_abs_self (pos (s' - cum (n + 1) 0) - pos (s - cum (n + 1) 0))
  have hs0 := abs_nonneg (s' - s)
  nlinarith [mul_le_mul_of_nonneg_right hc hs0]

lemma damp_sum_lip (s s' : ℝ) :
    ∑ k ∈ Finset.range (n + 1), wt (n + 1) k * |damp (n + 1) k s' - damp (n + 1) k s| ≤
      3 * |s' - s| := by
  rcases le_total s s' with h | h
  · exact damp_sum_lip_aux h
  · have := damp_sum_lip_aux (n := n) h
    rw [abs_sub_comm s' s]
    refine le_trans (le_of_eq ?_) this
    apply Finset.sum_congr rfl
    intro k _
    rw [abs_sub_comm]

lemma dampT_lip (s s' : ℝ) : |dampT (n + 1) s' - dampT (n + 1) s| ≤ 3 * |s' - s| := by
  set R := ramp 1 (s - cum (n + 1) (n + 1)) with hR
  set R' := ramp 1 (s' - cum (n + 1) (n + 1)) with hR'
  set D := dramp 1 (s - cum (n + 1) (n + 1)) with hD
  set D' := dramp 1 (s' - cum (n + 1) (n + 1)) with hD'
  have hR0 : 0 ≤ R := ramp_nonneg one_pos _
  have hD'0 : 0 ≤ D' := dramp_nonneg one_pos _
  have hD'1 : D' ≤ 1 := dramp_le_one one_pos _
  have hc0 := dcap_nonneg hR0
  have hc1 := dcap_le_one hR0
  have e0 : s' - cum (n + 1) (n + 1) - (s - cum (n + 1) (n + 1)) = s' - s := by ring
  have hRl : |R' - R| ≤ |s' - s| := by
    have := ramp_lipschitz one_pos (s' - cum (n + 1) (n + 1)) (s - cum (n + 1) (n + 1))
    rwa [e0] at this
  have hcl := dcap_lipschitz R' R
  have hDl : |D' - D| ≤ 2 * |s' - s| := by
    have h1 := pos_lipschitz (s' - cum (n + 1) (n + 1)) (s - cum (n + 1) (n + 1))
    have h2 := pos_lipschitz (s' - cum (n + 1) (n + 1) - 1) (s - cum (n + 1) (n + 1) - 1)
    have e1 : s' - cum (n + 1) (n + 1) - 1 - (s - cum (n + 1) (n + 1) - 1) = s' - s := by ring
    rw [e0] at h1
    rw [e1] at h2
    have e : D' - D = (pos (s' - cum (n + 1) (n + 1)) - pos (s - cum (n + 1) (n + 1))) -
        (pos (s' - cum (n + 1) (n + 1) - 1) - pos (s - cum (n + 1) (n + 1) - 1)) := by
      simp only [hD, hD', dramp]
      ring
    rw [e]
    have := abs_sub (pos (s' - cum (n + 1) (n + 1)) - pos (s - cum (n + 1) (n + 1)))
      (pos (s' - cum (n + 1) (n + 1) - 1) - pos (s - cum (n + 1) (n + 1) - 1))
    linarith
  have e : dampT (n + 1) s' - dampT (n + 1) s = (dcap R' - dcap R) * D' + dcap R * (D' - D) := by
    simp only [dampT, ← hR, ← hR', ← hD, ← hD']
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hD'0, abs_of_nonneg hc0]
  have a1 : |dcap R' - dcap R| * D' ≤ |s' - s| * 1 :=
    mul_le_mul (hcl.trans hRl) hD'1 hD'0 (abs_nonneg _)
  have a2 : dcap R * |D' - D| ≤ 1 * (2 * |s' - s|) :=
    mul_le_mul hc1 hDl (abs_nonneg _) zero_le_one
  linarith

lemma dcomp_lip (s s' : ℝ) : |dcomp n s' - dcomp n s| ≤ 15 * |s' - s| := by
  have h1 := damp_sum_lip (n := n) s s'
  have h2 := dampT_lip (n := n) s s'
  have e : dcomp n s' - dcomp n s =
      ∑ k ∈ Finset.range (n + 1), wt (n + 1) k * (damp (n + 1) k s' - damp (n + 1) k s) +
        4 * (dampT (n + 1) s' - dampT (n + 1) s) := by
    unfold dcomp
    rw [Finset.sum_congr rfl (fun k _ => mul_sub (wt (n + 1) k) _ _), Finset.sum_sub_distrib]
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h3 : |∑ k ∈ Finset.range (n + 1), wt (n + 1) k * (damp (n + 1) k s' - damp (n + 1) k s)| ≤
      ∑ k ∈ Finset.range (n + 1), wt (n + 1) k * |damp (n + 1) k s' - damp (n + 1) k s| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro k _
    rw [abs_mul, abs_of_pos (wt_pos k)]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  linarith

lemma rwDt_lip (S : Scales n r ρ) (s s' t t' : ℝ) (y y' : ℕ → ℝ) :
    |rwDt n r s' t' y' - rwDt n r s t y| ≤ |s' - s| + 4 * |t' - t| + 2 * |y' n - y n| := by
  have hrn := S.last
  have hMa : |ampT (n + 1) s| ≤ 1 := by
    rw [abs_of_nonneg (ampT_nonneg s)]; exact ampT_le_one s
  have hMc : ∀ v : ℝ, |gate (v / r n)| ≤ 1 := by
    intro v
    rw [abs_of_nonneg (gate_nonneg _)]; exact gate_le_one _
  have h3 := prod3_lip (a := ampT (n + 1) s) (a' := ampT (n + 1) s') (b := dafun t) (b' := dafun t')
    (c := gate (y n / r n)) (c' := gate (y' n / r n)) hMa (dafun_abs t) (dafun_abs t') (hMc (y' n))
  have ha := ampT_lipschitz (n := n) s' s
  have hb := dafun_lipschitz t' t
  have hc := gate_scaled_lip (r := r n) (by rw [hrn]; norm_num) (y' n) (y n)
  rw [hrn] at hc
  have hc' : |gate (y' n / r n) - gate (y n / r n)| ≤ 2 * |y' n - y n| := by
    rw [hrn]
    simpa using hc
  unfold rwDt
  linarith

theorem rwDs_lip (S : Scales n r ρ) (s s' t t' : ℝ) (y y' : ℕ → ℝ) :
    (rwDs n r s' t' y' - rwDs n r s t y) ^ 2 ≤
      2 ^ 10 * ((s' - s) ^ 2 + (t' - t) ^ 2 + ∑ k ∈ Finset.range (n + 1), (y' k - y k) ^ 2) := by
  set D := ∑ k ∈ Finset.range (n + 1), (y' k - y k) ^ 2 with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hrn := S.last
  set c : ℕ → ℝ := fun k => 2 * dprev y y' k + |y' k - y k| with hc
  have hterm : ∀ k ∈ Finset.range (n + 1),
      |wt (n + 1) k * damp (n + 1) k s' * gprev r y' k * push (y' k / r k) -
        wt (n + 1) k * damp (n + 1) k s * gprev r y k * push (y k / r k)| ≤
        wt (n + 1) k * |damp (n + 1) k s' - damp (n + 1) k s| + r k * c k := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hrk := S.pos hkn
    have hw := wt_pos (N := n + 1) k
    have hMa : |damp (n + 1) k s| ≤ 1 := by
      rw [abs_of_nonneg (damp_nonneg k s)]; exact damp_le_one k s
    have hMb : ∀ z : ℕ → ℝ, |gprev r z k| ≤ 1 := by
      intro z
      rw [abs_of_nonneg (gprev_nonneg r z k)]; exact gprev_le_one r z k
    have hMc : ∀ v : ℝ, |push (v / r k)| ≤ 1 := by
      intro v
      rw [abs_of_nonneg (push_nonneg _)]; exact push_le_one _
    have h3 := prod3_lip (a := damp (n + 1) k s) (a' := damp (n + 1) k s') (b := gprev r y k)
      (b' := gprev r y' k) (c := push (y k / r k)) (c' := push (y' k / r k)) hMa (hMb y) (hMb y')
      (hMc (y' k))
    have hg := gprev_lip S y y' hkn
    have hp := push_scaled_lip hrk (y' k) (y k)
    have e : wt (n + 1) k * damp (n + 1) k s' * gprev r y' k * push (y' k / r k) -
        wt (n + 1) k * damp (n + 1) k s * gprev r y k * push (y k / r k) =
        wt (n + 1) k * (damp (n + 1) k s' * gprev r y' k * push (y' k / r k) -
          damp (n + 1) k s * gprev r y k * push (y k / r k)) := by ring
    rw [e, abs_mul, abs_of_pos hw]
    have hg' : wt (n + 1) k * |gprev r y' k - gprev r y k| ≤ r k * (2 * dprev y y' k) := by
      have := mul_le_mul_of_nonneg_left hg hrk.le
      have e2 : r k * (wt (n + 1) k / r k * |gprev r y' k - gprev r y k|) =
          wt (n + 1) k * |gprev r y' k - gprev r y k| := by field_simp
      rw [e2] at this
      exact this
    have hp' : wt (n + 1) k * |push (y' k / r k) - push (y k / r k)| ≤ r k * |y' k - y k| := by
      have h1 := mul_le_mul_of_nonneg_left hp hw.le
      have hwle := S.wt_le_sq hkn
      have e2 : wt (n + 1) k * (1 / 3 / r k * |y' k - y k|) =
          wt (n + 1) k / r k / 3 * |y' k - y k| := by field_simp
      rw [e2] at h1
      have h2 : wt (n + 1) k / r k / 3 ≤ r k := by
        rw [div_le_iff₀ (by norm_num), div_le_iff₀ hrk]
        nlinarith
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
    have h4 := mul_le_mul_of_nonneg_left h3 hw.le
    simp only [hc]
    nlinarith
  have hlast : |dampT (n + 1) s' * afun t' * gate (y' n / r n) -
      dampT (n + 1) s * afun t * gate (y n / r n)| ≤
      12 * |s' - s| + |t' - t| + 8 * |y' n - y n| := by
    have hMa : |dampT (n + 1) s| ≤ 1 := by
      rw [abs_of_nonneg (dampT_nonneg s)]; exact dampT_le_one s
    have hMb : ∀ v : ℝ, |afun v| ≤ 4 := by
      intro v
      rw [abs_of_nonneg (afun_nonneg v)]; exact afun_le v
    have hMc : ∀ v : ℝ, |gate (v / r n)| ≤ 1 := by
      intro v
      rw [abs_of_nonneg (gate_nonneg _)]; exact gate_le_one _
    have h3 := prod3_lip (a := dampT (n + 1) s) (a' := dampT (n + 1) s') (b := afun t)
      (b' := afun t') (c := gate (y n / r n)) (c' := gate (y' n / r n)) hMa (hMb t) (hMb t')
      (hMc (y' n))
    have ha := dampT_lip (n := n) s s'
    have hb := afun_lipschitz t' t
    have hcg := gate_scaled_lip (r := r n) (by rw [hrn]; norm_num) (y' n) (y n)
    rw [hrn] at hcg
    have hc' : |gate (y' n / r n) - gate (y n / r n)| ≤ 2 * |y' n - y n| := by
      rw [hrn]
      simpa using hcg
    linarith
  have hsum : |∑ k ∈ Finset.range (n + 1),
      (wt (n + 1) k * damp (n + 1) k s' * gprev r y' k * push (y' k / r k) -
        wt (n + 1) k * damp (n + 1) k s * gprev r y k * push (y k / r k))| ≤
      3 * |s' - s| + ∑ k ∈ Finset.range (n + 1), r k * c k := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib]
    have := damp_sum_lip (n := n) s s'
    linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1)) r c
  have hr2 := S.sum_sq_le
  have hc2 : ∑ k ∈ Finset.range (n + 1), c k ^ 2 ≤ 10 * D := by
    have h1 : ∀ k ∈ Finset.range (n + 1), c k ^ 2 ≤ 8 * dprev y y' k ^ 2 + 2 * (y' k - y k) ^ 2 := by
      intro k _
      simp only [hc]
      nlinarith [sq_nonneg (2 * dprev y y' k - |y' k - y k|), sq_abs (y' k - y k)]
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have := sum_dprev_sq (n := n) y y'
    linarith
  have hX0 : 0 ≤ ∑ k ∈ Finset.range (n + 1), r k * c k := by
    apply Finset.sum_nonneg
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    apply mul_nonneg (S.pos hkn).le
    simp only [hc]
    have := dprev_nonneg y y' k
    have := abs_nonneg (y' k - y k)
    linarith
  have hX2 : (∑ k ∈ Finset.range (n + 1), r k * c k) ^ 2 ≤ 60 * D := by
    have hc0 : 0 ≤ ∑ k ∈ Finset.range (n + 1), c k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    calc _ ≤ (∑ k ∈ Finset.range (n + 1), r k ^ 2) * ∑ k ∈ Finset.range (n + 1), c k ^ 2 := hcs
      _ ≤ 6 * (10 * D) := mul_le_mul hr2 hc2 hc0 (by norm_num)
      _ = 60 * D := by ring
  have hn : (y' n - y n) ^ 2 ≤ D :=
    Finset.single_le_sum (f := fun k => (y' k - y k) ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have etot : rwDs n r s' t' y' - rwDs n r s t y =
      ∑ k ∈ Finset.range (n + 1),
        (wt (n + 1) k * damp (n + 1) k s' * gprev r y' k * push (y' k / r k) -
          wt (n + 1) k * damp (n + 1) k s * gprev r y k * push (y k / r k)) +
      (dampT (n + 1) s' * afun t' * gate (y' n / r n) -
        dampT (n + 1) s * afun t * gate (y n / r n)) := by
    unfold rwDs
    rw [Finset.sum_sub_distrib]
    ring
  have habs : |rwDs n r s' t' y' - rwDs n r s t y| ≤
      15 * |s' - s| + |t' - t| + 8 * |y' n - y n| + ∑ k ∈ Finset.range (n + 1), r k * c k := by
    rw [etot]
    refine (abs_add_le _ _).trans ?_
    linarith
  have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs] at hsq
  have h4 := sq_add4 (15 * |s' - s|) (|t' - t|) (8 * |y' n - y n|)
    (∑ k ∈ Finset.range (n + 1), r k * c k)
  have e1 : (15 * |s' - s|) ^ 2 = 225 * (s' - s) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  have e2 : |t' - t| ^ 2 = (t' - t) ^ 2 := sq_abs _
  have e3 : (8 * |y' n - y n|) ^ 2 = 64 * (y' n - y n) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  rw [e1, e2, e3] at h4
  have hs2 := sq_nonneg (s' - s)
  have ht2 := sq_nonneg (t' - t)
  nlinarith

end Front

end LongTails.Proofs.NcPlBlockSmooth
