import LongTails.Algorithms.LeonTuning
import Mathlib.Tactic

namespace LongTails.Proofs.LeonCalendar

open LongTails.Algorithms.LeonCalendar

lemma leaf_count (j : ℕ) : (levels j).count 0 = 4 ^ j := by
  induction j with
  | zero => simp [levels]
  | succ j ih => simp [levels, ih, pow_succ]; omega

lemma batch_work (j : ℕ) :
    ((levels j).map (fun l => 2 ^ l)).sum + 2 ^ j = 2 * 4 ^ j := by
  induction j with
  | zero => simp [levels]
  | succ j ih => simp [levels, pow_succ]; omega

end LongTails.Proofs.LeonCalendar

namespace LongTails.Proofs.LeonBlocks

open LongTails.Algorithms.LeonCalendar

lemma level_le (j : ℕ) : ∀ l ∈ levels j, l ≤ j := by
  induction j with
  | zero => simp [levels]
  | succ j ih =>
    intro l hl
    simp only [levels, List.mem_cons, List.mem_append, or_self] at hl
    exact hl.elim (fun h => h.le) (fun h => Nat.le_succ_of_le (ih _ h))

lemma leaf_drift {E : Type*} [SeminormedAddCommGroup E] (x : ℕ → E) (level : ℕ → ℕ)
    {δ : ℝ} (hmove : ∀ t, ‖x (t+1) - x t‖ ≤ if level t = 0 then δ else 0)
    (ls : List ℕ) (t : ℕ) (h : ∀ k : Fin ls.length, level (t + k) = ls[k]) :
    ‖x (t + ls.length) - x t‖ ≤ (ls.count 0 : ℝ) * δ := by
  induction ls generalizing t with
  | nil => simp
  | cons l ls ih =>
    have h₀ : level t = l := by simpa using h ⟨0, by simp⟩
    have hs (k : Fin ls.length) : level ((t + 1) + k) = ls[k] := by
      simpa [Nat.add_assoc, Nat.add_comm 1 k.val] using h k.succ
    have he : t + (l :: ls).length = (t + 1) + ls.length := by simp; omega
    rw [he]
    have ht := norm_sub_le_norm_sub_add_norm_sub (x (t + 1 + ls.length)) (x (t + 1)) (x t)
    have hi := ih (t+1) hs
    have hf := hmove t
    rw [h₀] at hf
    by_cases hl : l = 0 <;> simp [hl] at hf ⊢ <;> linarith

lemma slot_constant {A : Type*} (S : ℕ → ℕ → A) (level : ℕ → ℕ)
    (step : ∀ t j, j ≠ level t → S (t + 1) j = S t j) (j : ℕ) (ls : List ℕ) (t : ℕ)
    (h : ∀ k : Fin ls.length, level (t + k) = ls[k]) (hj : j ∉ ls) :
    S (t + ls.length) j = S t j := by
  induction ls generalizing t with
  | nil => simp
  | cons l ls ih =>
    have h₀ : level t = l := by simpa using h ⟨0, by simp⟩
    have hs (k : Fin ls.length) : level ((t + 1) + k) = ls[k] := by
      simpa [Nat.add_assoc, Nat.add_comm 1 k.val] using h k.succ
    simp only [List.mem_cons, not_or] at hj
    have he : t + (l :: ls).length = (t + 1) + ls.length := by simp; omega
    rw [he, ih (t+1) hs hj.2]
    exact step t j (h₀.symm ▸ hj.1)

def Aligned (level : ℕ → ℕ) (t : ℕ) (ls : List ℕ) : Prop :=
  ∀ k : Fin ls.length, level (t + k) = ls[k]

lemma aligned_append {level : ℕ → ℕ} {ls rest : List ℕ} {t : ℕ}
    (h : Aligned level t (ls ++ rest)) : Aligned level t ls ∧ Aligned level (t + ls.length) rest := by
  constructor
  · intro k
    have hk : k.val < (ls ++ rest).length := by simp; omega
    have he := h ⟨k, hk⟩
    change level (t + k.val) = (ls ++ rest)[k.val] at he
    change level (t + k.val) = ls[k.val]
    simpa only [List.getElem_append_left k.isLt] using he
  · intro k
    have hk : ls.length + k.val < (ls ++ rest).length := by simp
    have he := h ⟨ls.length + k.val, hk⟩
    simpa [List.getElem_append_right, Nat.add_assoc] using he

end LongTails.Proofs.LeonBlocks

namespace LongTails.Proofs.LeonBlockCover

open LongTails.Algorithms.LeonCalendar
open LeonBlocks

def copies (ls : List ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => copies ls k ++ ls

lemma copies_len (ls : List ℕ) (k : ℕ) : (copies ls k).length = k * ls.length := by
  induction k with
  | zero => simp [copies]
  | succ k ih => simp [copies, ih, Nat.succ_mul]

lemma copies_count (ls : List ℕ) (k : ℕ) : (copies ls k).count 0 = k * ls.count 0 := by
  induction k with
  | zero => simp [copies]
  | succ k ih => simp [copies, ih, Nat.succ_mul]

lemma copies_mem (ls : List ℕ) (k i : ℕ) (h : i ∈ copies ls k) : i ∈ ls := by
  induction k with
  | zero => simp [copies] at h
  | succ k ih => exact (List.mem_append.mp h).elim ih id

lemma aligned_cons {level : ℕ → ℕ} {t l : ℕ} {ls : List ℕ}
    (h : Aligned level t (l :: ls)) : level t = l ∧ Aligned level (t + 1) ls := by
  refine ⟨by simpa using h ⟨0, by simp⟩, ?_⟩
  intro k
  simpa [Nat.add_assoc, Nat.add_comm 1 k.val] using h k.succ

lemma copies_prefix {level : ℕ → ℕ} {t k j : ℕ} {ls : List ℕ}
    (h : Aligned level t (copies ls k)) (hj : j ≤ k) : Aligned level t (copies ls j) := by
  induction k with
  | zero => simpa [show j = 0 by omega] using h
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hj with he | hl
    · simpa [he] using h
    · exact ih (aligned_append h).1 (by omega)

lemma children {level : ℕ → ℕ} {t j : ℕ} (h : Aligned level t (levels (j + 1))) :
    level t = j + 1 ∧ Aligned level (t + 1) (copies (levels j) 4) := by
  apply aligned_cons
  simpa [levels, copies, List.append_assoc] using h

lemma child_alignment {level : ℕ → ℕ} {t j k : ℕ} (h : Aligned level t (levels (j + 1)))
    (hk : k < 4) :
    Aligned level (t + 1) (copies (levels j) k) ∧
    Aligned level (t + 1 + k * (levels j).length) (levels j) := by
  have hp := copies_prefix (children h).2 (show k + 1 ≤ 4 by omega)
  simpa only [copies_len] using aligned_append hp

lemma all_leaves {level : ℕ → ℕ} (G : ℕ → ℕ → Prop)
    (hchild : ∀ t j k, Aligned level t (levels (j + 1)) → k < 4 →
      G t (j + 1) → G (t + 1 + k * (levels j).length) j)
    (j t u : ℕ) (h : Aligned level t (levels j)) (hg : G t j)
    (hlo : t ≤ u) (hhi : u < t + (levels j).length) (hu : level u = 0) : G u 0 := by
  induction j generalizing t u with
  | zero =>
    have he : u = t := by simp [levels] at hhi; omega
    simpa [he] using hg
  | succ j ih =>
    have hne : u ≠ t := by intro he; subst u; rw [(children h).1] at hu; omega
    let n := (levels j).length
    have hn : 0 < n := by cases j <;> simp [n, levels]
    let k := (u - (t+1)) / n
    have hall : (levels (j+1)).length = 1 + 4 * n := by simp [levels, n]; omega
    have hk : k < 4 := by apply (Nat.div_lt_iff_lt_mul hn).mpr; omega
    have hfirst : t + 1 + k * n ≤ u := by
      have hp := Nat.div_mul_le_self (u - (t+1)) n
      change t + 1 + (u - (t+1)) / n * n ≤ u
      omega
    have hlast : u < t + 1 + k * n + n := by
      have he := Nat.div_add_mod' (u - (t+1)) n
      have hr := Nat.mod_lt (u - (t+1)) hn
      change u < t + 1 + (u - (t+1)) / n * n + n
      omega
    exact ih _ _ (child_alignment h hk).2 (hchild _ _ k h hk hg) hfirst hlast hu

end LongTails.Proofs.LeonBlockCover

namespace LongTails.Proofs.LeonBatchTuning

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonTuning

lemma resolution_pos (p : Params) (h : 0 < p.ε) : 0 < resolution p := by
  unfold resolution
  positivity

lemma iterations_lower (p : Params) :
    2 * p.L * p.Δ / resolution p ^ 2 ≤ iterations p := by
  have h := Nat.le_pow_clog (by decide : 1 < 4) (max 1 ⌈2 * p.L * p.Δ / resolution p ^ 2⌉₊)
  apply (Nat.le_ceil _).trans
  exact_mod_cast (le_max_right _ _).trans h

lemma iterations_upper (p : Params) :
    iterations p ≤ 4 * (1 + ⌈2 * p.L * p.Δ / resolution p ^ 2⌉₊) := by
  unfold iterations height
  generalize ⌈2 * p.L * p.Δ / resolution p ^ 2⌉₊ = n
  cases h : Nat.clog 4 (max 1 n) with
  | zero => simp; omega
  | succ j =>
    have hs : 4 ^ j < max 1 n := Nat.pow_lt_of_lt_clog (by omega)
    rw [pow_succ]
    omega

lemma batch_lower (p : Params) (i : Fin p.n) (l : ℕ) :
    (2 : ℝ) ^ l * (p.σ ^ 2 * (∑ j, (p.h j : ℝ)) /
      ((p.n : ℝ) ^ 2 * resolution p ^ 2 * (p.h i : ℝ))) ≤ (batch p i l : ℕ) := by
  let a := p.σ ^ 2 * (∑ j, (p.h j : ℝ)) / ((p.n : ℝ) ^ 2 * resolution p ^ 2 * (p.h i : ℝ))
  change 2 ^ l * a ≤ ((2 ^ l * max 1 ⌈a⌉₊ : ℕ) : ℝ)
  push_cast
  exact mul_le_mul_of_nonneg_left ((Nat.le_ceil a).trans (by exact_mod_cast le_max_right 1 ⌈a⌉₊))
    (by positivity)

lemma batch_variance (p : Params) (hh : ∀ i, 0 < p.h i) (hε : 0 < p.ε) (l : ℕ) :
    (∑ i, p.σ ^ 2 / ((p.n : ℝ) ^ 2 * (batch p i l : ℕ))) ≤ resolution p ^ 2 / 2 ^ l := by
  let H := ∑ j, (p.h j : ℝ)
  have hH : 0 < H := Finset.sum_pos (fun i _ => by exact_mod_cast hh i) Finset.univ_nonempty
  have hb (i : Fin p.n) : (0 : ℝ) < (batch p i l : ℕ) := by exact_mod_cast (batch p i l).pos
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hs := resolution_pos p hε
  have htwo : (0 : ℝ) < 2 ^ l := by positivity
  have hterm (i : Fin p.n) : p.σ ^ 2 / ((p.n : ℝ) ^ 2 * (batch p i l : ℕ)) ≤
      resolution p ^ 2 / 2 ^ l / H * (p.h i : ℝ) := by
    have hi : (0 : ℝ) < p.h i := by exact_mod_cast hh i
    have hlow := batch_lower p i l
    change 2 ^ l * (p.σ ^ 2 * H / ((p.n : ℝ) ^ 2 * resolution p ^ 2 * (p.h i : ℝ))) ≤ _ at hlow
    field_simp [hn.ne', hs.ne', hi.ne', htwo.ne', hH.ne', (hb i).ne'] at hlow ⊢
    nlinarith
  calc
    _ ≤ ∑ i, resolution p ^ 2 / 2 ^ l / H * (p.h i : ℝ) := Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by rw [← Finset.mul_sum]; change _ / H * H = _; field_simp

end LongTails.Proofs.LeonBatchTuning
