import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import LongTails.Proofs.SymmetricThirdOrderTuning
import Mathlib.Tactic
import LongTails.Proofs.SymmetricThirdOrderOuter

namespace LongTails.Proofs.SymmetricThirdOrderPhasePartition

noncomputable def cut (A : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℕ :=
  Nat.find (show ∃ i, i = N ∨ t ≤ A i from ⟨N, Or.inl rfl⟩)

lemma cut_le (A : ℕ → ℝ) (N : ℕ) (t : ℝ) : cut A N t ≤ N :=
  Nat.find_min' _ (Or.inl rfl)

lemma before_cut {A : ℕ → ℝ} {N i : ℕ} {t : ℝ} (hi : i < cut A N t) :
    A i < t := by
  have h := Nat.find_min (show ∃ i, i = N ∨ t ≤ A i from ⟨N, Or.inl rfl⟩) hi
  exact lt_of_not_ge (fun ht => h (Or.inr ht))

lemma after_cut {A : ℕ → ℝ} {N i : ℕ} {t : ℝ} (hA : Monotone A)
    (hi : cut A N t ≤ i) (hiN : i < N) : t ≤ A i := by
  have h := Nat.find_spec (show ∃ i, i = N ∨ t ≤ A i from ⟨N, Or.inl rfl⟩)
  change cut A N t = N ∨ t ≤ A (cut A N t) at h
  rcases h with h | h
  · omega
  · exact h.trans (hA hi)

lemma cut_mono (A : ℕ → ℝ) (N : ℕ) : Monotone (cut A N) := by
  intro s t hst
  apply Nat.find_min'
  have h := Nat.find_spec (show ∃ i, i = N ∨ t ≤ A i from ⟨N, Or.inl rfl⟩)
  exact h.imp id (fun h => hst.trans h)

lemma cut_start {A : ℕ → ℝ} {N : ℕ} {t : ℝ} (ht : t ≤ A 0) :
    cut A N t = 0 := by
  exact Nat.eq_zero_of_le_zero (Nat.find_min' _ (Or.inr ht))

lemma cut_end {A : ℕ → ℝ} {N : ℕ} {t : ℝ}
    (h : ∀ i < N, A i < t) : cut A N t = N := by
  apply le_antisymm (cut_le A N t)
  by_contra hn
  have hi : cut A N t < N := by omega
  have hs := Nat.find_spec (show ∃ i, i = N ∨ t ≤ A i from ⟨N, Or.inl rfl⟩)
  change cut A N t = N ∨ t ≤ A (cut A N t) at hs
  rcases hs with hs | hs
  · omega
  · exact (not_lt_of_ge hs) (h _ hi)

lemma phase_member {A : ℕ → ℝ} {N r : ℕ} {s t : ℝ} (hA : Monotone A)
    (hr : r < cut A N t - cut A N s) :
    s ≤ A (cut A N s + r) ∧ A (cut A N s + r) < t ∧
      cut A N s + r < N := by
  have hc := cut_le A N t
  have hi : cut A N s + r < cut A N t := by omega
  exact ⟨after_cut (N := N) hA (by omega) (by omega), before_cut hi, by omega⟩

lemma phase_lengths {A : ℕ → ℝ} {N J : ℕ} {b : ℕ → ℝ}
    (hb : Monotone b) (hstart : b 0 ≤ A 0) (hend : ∀ i < N, A i < b J) :
    ∑ j ∈ Finset.range J, (cut A N (b (j + 1)) - cut A N (b j)) = N := by
  have h := Finset.sum_range_tsub ((cut_mono A N).comp hb) (n := J)
  change (∑ j ∈ Finset.range J, (cut A N (b (j + 1)) - cut A N (b j))) =
    cut A N (b J) - cut A N (b 0) at h
  rw [cut_start hstart, cut_end hend, Nat.sub_zero] at h
  exact h

lemma dyadic_threshold_exists {b X : ℝ} (hb : 0 < b) :
    ∃ J : ℕ, X ≤ b * 2 ^ J := by
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (X / b) (by norm_num : (1 : ℝ) < 2)
  exact ⟨J, le_of_lt ((div_lt_iff₀ hb).mp hJ) |>.trans_eq (mul_comm _ _)⟩

noncomputable def phaseNumber (b X : ℝ) (hb : 0 < b) : ℕ :=
  Nat.find (dyadic_threshold_exists (X := X) hb)

lemma phaseNumber_top {b X : ℝ} (hb : 0 < b) :
    X ≤ b * 2 ^ phaseNumber b X hb := Nat.find_spec (dyadic_threshold_exists (X := X) hb)

lemma phaseNumber_before {b X : ℝ} (hb : 0 < b) {j : ℕ}
    (hj : j < phaseNumber b X hb) : b * 2 ^ j < X := by
  exact lt_of_not_ge (Nat.find_min (dyadic_threshold_exists (X := X) hb) hj)

lemma phaseNumber_le {b X : ℝ} (hb : 0 < b) {J : ℕ} (hJ : X ≤ b * 2 ^ J) :
    phaseNumber b X hb ≤ J := Nat.find_min' _ hJ

lemma dyadic_monotone {b : ℝ} (hb : 0 ≤ b) : Monotone (fun j : ℕ => b * 2 ^ j) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hij) hb

lemma dyadic_phase_lengths {A : ℕ → ℝ} {N : ℕ} {b X : ℝ}
    (hb : 0 < b) (hstart : A 0 = b) (hactive : ∀ i < N, A i < X) :
    ∑ j ∈ Finset.range (phaseNumber b X hb),
      (cut A N (b * 2 ^ (j + 1)) - cut A N (b * 2 ^ j)) = N := by
  apply phase_lengths (dyadic_monotone hb.le)
  · simp [hstart]
  · intro i hi
    exact (hactive i hi).trans_le (phaseNumber_top hb)

lemma phaseNumber_log_bound {b X Λ : ℝ} (hb : 0 < b) (hX : 0 ≤ X)
    (hΛ : 0 < Λ) (hinit : 1 / (4 * Λ) ≤ b) :
    phaseNumber b X hb ≤ ⌈Real.log (1 + 4 * Λ * X) / Real.log 2⌉₊ := by
  apply phaseNumber_le hb
  have hp := LoraSilverTuning.pow_ceil_log (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < 1 + 4 * Λ * X)
  have hi : 1 ≤ b * (4 * Λ) := (div_le_iff₀ (by positivity)).mp hinit
  have hm := mul_le_mul_of_nonneg_left hp hb.le
  have hx := mul_le_mul_of_nonneg_right hi hX
  nlinarith

lemma total_phase_count_bound {A : ℕ → ℝ} {N : ℕ} {δ L D b X M : ℝ}
    (hδ : 0 ≤ δ) (hL : 0 ≤ L) (hD : 0 ≤ D) (hb : 0 < b)
    (hX : 0 ≤ X) (hstart : A 0 = b) (hactive : ∀ i < N, A i < X)
    (hcount : ∀ j < phaseNumber b X hb,
      ((cut A N (b * 2 ^ (j + 1)) - cut A N (b * 2 ^ j) : ℕ) : ℝ) ≤
        16 * Real.sqrt (δ * (b * 2 ^ j)) +
        48 * (L * D * (b * 2 ^ j)) ^ (1 / 5 : ℝ) + M + 2) :
    (N : ℝ) ≤ 64 * Real.sqrt (δ * X) + 384 * (L * D * X) ^ (1 / 5 : ℝ) +
      (M + 2) * phaseNumber b X hb := by
  have hsum := dyadic_phase_lengths hb hstart hactive
  cases hj : phaseNumber b X hb with
  | zero =>
    simp only [hj, Finset.range_zero, Finset.sum_empty] at hsum
    subst N
    simp only [Nat.cast_zero, mul_zero, add_zero]
    positivity
  | succ n =>
    have hlast : b * 2 ^ n ≤ X := (phaseNumber_before hb (by omega)).le
    have hc := SymmetricThirdOrderTuning.phase_sum_bound
      (fun j => ((cut A N (b * 2 ^ (j + 1)) - cut A N (b * 2 ^ j) : ℕ) : ℝ))
      hδ hL hD hb.le n hlast (fun i hi => hcount i (by omega))
    rw [hj] at hsum
    have he : (∑ j ∈ Finset.range (n + 1),
        ((cut A N (b * 2 ^ (j + 1)) - cut A N (b * 2 ^ j) : ℕ) : ℝ)) = N := by
      exact_mod_cast hsum
    rw [he] at hc
    simpa only [Nat.cast_add, Nat.cast_one] using hc

lemma segment_sum_le (d : ℕ → ℝ) {a n N : ℕ} (h : a + n ≤ N)
    (hd : ∀ i < N, 0 ≤ d i) :
    (∑ i ∈ Finset.range n, d (a + i)) ≤ ∑ i ∈ Finset.range N, d i := by
  have hp : (∑ i ∈ Finset.range a, d i) + (∑ i ∈ Finset.range n, d (a + i)) =
      ∑ i ∈ Finset.range (a + n), d i := by rw [Finset.sum_range_add]
  have hn : 0 ≤ ∑ i ∈ Finset.range a, d i := by
    apply Finset.sum_nonneg
    intro i hi
    exact hd i (by have := Finset.mem_range.mp hi; omega)
  have hs : (∑ i ∈ Finset.range (a + n), d i) ≤ ∑ i ∈ Finset.range N, d i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    intro i hi _
    exact hd i (Finset.mem_range.mp hi)
  linarith

lemma phase_dissipation_le {A d : ℕ → ℝ} {N : ℕ} {s t D : ℝ}
    (hst : s ≤ t) (hd : ∀ i < N, 0 ≤ d i)
    (hsum : ∑ i ∈ Finset.range N, d i ≤ D) :
    (∑ r ∈ Finset.range (cut A N t - cut A N s), d (cut A N s + r)) ≤ D := by
  apply (segment_sum_le d (by have := cut_mono A N hst; have := cut_le A N t; omega) hd).trans
  exact hsum

lemma total_phase_log_bound {A : ℕ → ℝ} {N : ℕ} {δ L D b X M Λ : ℝ}
    (hδ : 0 ≤ δ) (hL : 0 ≤ L) (hD : 0 ≤ D) (hb : 0 < b)
    (hX : 0 ≤ X) (hM : 0 ≤ M) (hΛ : 0 < Λ) (hinit : 1 / (4 * Λ) ≤ b)
    (hstart : A 0 = b) (hactive : ∀ i < N, A i < X)
    (hcount : ∀ j < phaseNumber b X hb,
      ((cut A N (b * 2 ^ (j + 1)) - cut A N (b * 2 ^ j) : ℕ) : ℝ) ≤
        16 * Real.sqrt (δ * (b * 2 ^ j)) +
        48 * (L * D * (b * 2 ^ j)) ^ (1 / 5 : ℝ) + M + 2) :
    (N : ℝ) ≤ 64 * Real.sqrt (δ * X) + 384 * (L * D * X) ^ (1 / 5 : ℝ) +
      (M + 2) * ⌈Real.log (1 + 4 * Λ * X) / Real.log 2⌉₊ := by
  have hc := total_phase_count_bound hδ hL hD hb hX hstart hactive hcount
  have hj : (phaseNumber b X hb : ℝ) ≤
      (⌈Real.log (1 + 4 * Λ * X) / Real.log 2⌉₊ : ℝ) := by
    exact_mod_cast phaseNumber_log_bound hb hX hΛ hinit
  have hm := mul_le_mul_of_nonneg_left hj (by linarith : 0 ≤ M + 2)
  linarith

lemma scalar_phase_count (A r : ℕ → ℝ) (j : ℕ → ℕ) {n M : ℕ}
    {δ L b D : ℝ} (hδ : 0 < δ) (hL : 0 < L) (hb : 0 < b) (hD : 0 ≤ D)
    (hgrid : ∀ t ≤ n, j t ≤ M)
    (hstep : ∀ t < n, j (t + 1) = if δ + 8 * L * (r t) ^ 2 ≤ δ * 4 ^ j t
      then j t - 1 else min M (j t + 1))
    (hweight : ∀ t < n, A (t + 1) = A t +
      min 1 ((δ * 4 ^ j t) / (δ + 8 * L * (r t) ^ 2)) *
        LongTails.Algorithms.CompositeCubicAcceleration.trialWeight (δ * 4 ^ j t) (A t))
    (hlower : ∀ t < n, b ≤ A t) (hupper : ∀ t < n, A t ≤ 2 * b)
    (htop : ∀ t < n, δ + 8 * L * (r t) ^ 2 ≤ δ * 4 ^ M)
    (hsum : (∑ t ∈ Finset.range n,
      min 1 ((δ * 4 ^ j t) / (δ + 8 * L * (r t) ^ 2)) *
      (A t + LongTails.Algorithms.CompositeCubicAcceleration.trialWeight (δ * 4 ^ j t) (A t)) *
      (δ + 8 * L * (r t) ^ 2) * (r t) ^ 2) ≤ D) :
    (n : ℝ) ≤ 16 * Real.sqrt (δ * b) + 48 * (L * D * b) ^ (1 / 5 : ℝ) + M + 2 := by
  classical
  let U := (L * D * b) ^ (1 / 5 : ℝ)
  let h := 2 * δ + U ^ 2 / b
  have hU : 0 ≤ U := Real.rpow_nonneg (by positivity) _
  have hU₅ : U ^ 5 = L * D * b := SymmetricThirdOrderTuning.fifth_root_power (by positivity)
  have hh : 2 * δ ≤ h := le_add_of_nonneg_right (div_nonneg (sq_nonneg U) hb.le)
  have hhpos : 0 < h := by linarith
  obtain ⟨k, hk, hklo, hkhi⟩ := SymmetricThirdOrderOuter.grid_threshold_exists hδ (by linarith : δ ≤ h) M
  let μ := fun t => δ * 4 ^ j t
  let lam := fun t => δ + 8 * L * (r t) ^ 2
  let a := fun t => LongTails.Algorithms.CompositeCubicAcceleration.trialWeight (μ t) (A t)
  let β := fun t => min 1 (μ t / lam t)
  let d := fun t => β t * (A t + a t) * lam t * (r t) ^ 2
  have hμ (t : ℕ) : 0 < μ t := by dsimp [μ]; positivity
  have hlam (t : ℕ) : 0 < lam t := by dsimp [lam]; positivity
  have hβ (t : ℕ) : 0 < β t := lt_min (by norm_num) (div_pos (hμ t) (hlam t))
  have hA (t : ℕ) (ht : t < n) : 0 ≤ A t := hb.le.trans (hlower t ht)
  have ha (t : ℕ) (ht : t < n) : 0 < a t :=
    LongTails.Proofs.CompositeCubicAcceleration.trialWeight_pos (hμ t) (hA t ht)
  have hmono (t : ℕ) (ht : t < n) : A t ≤ A (t + 1) := by
    have hw := hweight t ht
    change A (t + 1) = A t + β t * a t at hw
    rw [hw]
    exact le_add_of_nonneg_right (mul_nonneg (hβ t).le (ha t ht).le)
  have hlow (t : ℕ) (ht : t < n) (hg : lam t ≤ μ t ∧ j t ≤ k) :
      1 / (4 * Real.sqrt h) ≤ Real.sqrt (A (t + 1)) - Real.sqrt (A t) := by
    have he : β t = 1 := min_eq_left ((le_div_iff₀ (hlam t)).mpr (by simpa using hg.1))
    have hw : A (t + 1) = A t + a t := by
      have hw := hweight t ht
      change A (t + 1) = A t + β t * a t at hw
      simpa [he] using hw
    rw [hw]
    exact SymmetricThirdOrderOuter.low_down_progress (hμ t) (hA t ht) hhpos (hklo _ hg.2)
  have hhigh (t : ℕ) (ht : t < n) (hg : ¬lam t ≤ μ t ∧ k ≤ j t) :
      b * h ^ 2 / (16 * L) ≤ d t := by
    have hup : μ t < lam t := lt_of_not_ge hg.1
    have hmh : h ≤ μ t := by
      rcases hkhi _ hg.2 with hh | hh
      · exact hh
      · have ht' := htop t ht
        change lam t ≤ δ * 4 ^ M at ht'
        exact False.elim ((not_lt_of_ge (ht'.trans hh)) hup)
    have he : β t = μ t / lam t := min_eq_right ((div_le_one (hlam t)).mpr hup.le)
    exact SymmetricThirdOrderOuter.high_up_dissipation hδ hL hb.le
      ((hlower t ht).trans (le_add_of_nonneg_right (ha t ht).le)) hh hmh hup rfl he
  have hc := SymmetricThirdOrderOuter.phase_count_bound j (fun t => lam t ≤ μ t) A d
    hb hhpos hL hk hgrid hstep hmono hupper hlow
    (fun t ht => by dsimp [d]; exact mul_nonneg (mul_nonneg
      (mul_nonneg (hβ t).le (add_nonneg (hA t ht) (ha t ht).le)) (hlam t).le) (sq_nonneg _))
    hhigh hsum
  have hbalance := SymmetricThirdOrderTuning.phase_threshold_balance hδ hb hU hU₅ (show h = 2 * δ + U ^ 2 / b from rfl)
  change (n : ℝ) ≤ 16 * Real.sqrt (δ * b) + 48 * U + M + 2
  linarith

lemma scalar_trajectory_count (A r : ℕ → ℝ) (j : ℕ → ℕ) {N M : ℕ}
    {δ L b D X Λ : ℝ} (hδ : 0 < δ) (hL : 0 < L) (hb : 0 < b) (hD : 0 ≤ D)
    (hX : 0 ≤ X) (hΛ : 0 < Λ) (hinit : 1 / (4 * Λ) ≤ b)
    (hmono : Monotone A) (hstart : A 0 = b) (hactive : ∀ t < N, A t < X)
    (hgrid : ∀ t ≤ N, j t ≤ M)
    (hstep : ∀ t < N, j (t + 1) = if δ + 8 * L * (r t) ^ 2 ≤ δ * 4 ^ j t
      then j t - 1 else min M (j t + 1))
    (hweight : ∀ t < N, A (t + 1) = A t +
      min 1 ((δ * 4 ^ j t) / (δ + 8 * L * (r t) ^ 2)) *
        LongTails.Algorithms.CompositeCubicAcceleration.trialWeight (δ * 4 ^ j t) (A t))
    (htop : ∀ t < N, δ + 8 * L * (r t) ^ 2 ≤ δ * 4 ^ M)
    (hsum : (∑ t ∈ Finset.range N,
      min 1 ((δ * 4 ^ j t) / (δ + 8 * L * (r t) ^ 2)) *
      (A t + LongTails.Algorithms.CompositeCubicAcceleration.trialWeight (δ * 4 ^ j t) (A t)) *
      (δ + 8 * L * (r t) ^ 2) * (r t) ^ 2) ≤ D) :
    (N : ℝ) ≤ 64 * Real.sqrt (δ * X) + 384 * (L * D * X) ^ (1 / 5 : ℝ) +
      ((M : ℝ) + 2) * ⌈Real.log (1 + 4 * Λ * X) / Real.log 2⌉₊ := by
  apply total_phase_log_bound hδ.le hL.le hD hb hX (Nat.cast_nonneg M) hΛ hinit hstart hactive
  intro i _
  let B := b * 2 ^ i
  let c := cut A N B
  let n := cut A N (2 * B) - c
  have hB : 0 < B := by dsimp [B]; positivity
  have hends : c ≤ cut A N (2 * B) := cut_mono A N (by linarith)
  have hbound : c + n ≤ N := by
    have hc := cut_le A N (2 * B)
    dsimp [n]
    omega
  have hmem (t : ℕ) (ht : t < n) : B ≤ A (c + t) ∧ A (c + t) < 2 * B ∧ c + t < N :=
    phase_member hmono ht
  let d := fun t => min 1 ((δ * 4 ^ j t) / (δ + 8 * L * (r t) ^ 2)) *
    (A t + LongTails.Algorithms.CompositeCubicAcceleration.trialWeight (δ * 4 ^ j t) (A t)) *
    (δ + 8 * L * (r t) ^ 2) * (r t) ^ 2
  have hd (t : ℕ) (ht : t < N) : 0 ≤ d t := by
    have hAt : 0 ≤ A t := by rw [← hstart] at hb; exact hb.le.trans (hmono (Nat.zero_le t))
    have ha := LongTails.Proofs.CompositeCubicAcceleration.trialWeight_pos
      (show 0 < δ * 4 ^ j t by positivity) hAt
    dsimp [d]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (add_nonneg hAt ha.le)) (by positivity)) (sq_nonneg _)
  have hs : (∑ t ∈ Finset.range n, d (c + t)) ≤ D :=
    (segment_sum_le d hbound hd).trans hsum
  have hc := scalar_phase_count (fun t => A (c + t)) (fun t => r (c + t))
    (fun t => j (c + t)) hδ hL hB hD
    (fun t ht => hgrid (c + t) (by omega))
    (fun t ht => by simpa only [Nat.add_assoc] using hstep (c + t) (hmem t ht).2.2)
    (fun t ht => by simpa only [Nat.add_assoc] using hweight (c + t) (hmem t ht).2.2)
    (fun t ht => (hmem t ht).1) (fun t ht => (hmem t ht).2.1.le)
    (fun t ht => htop (c + t) (hmem t ht).2.2) hs
  have he : b * 2 ^ (i + 1) = 2 * B := by dsimp [B]; rw [pow_succ]; ring
  simpa only [he] using hc

open LongTails.Algorithms.SymmetricThirdOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def rawDissipation (L δ : ℝ) (s : OuterState E) (z : E) : ℝ :=
  let μ := δ * 4 ^ s.grid
  let lam := δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2
  min 1 (μ / lam) *
    (s.weight + LongTails.Algorithms.CompositeCubicAcceleration.trialWeight μ s.weight) *
    lam * ‖z - outerCenter δ s‖ ^ 2

lemma active_outer_count (S : ℕ → OuterState E) (z g : ℕ → E) (x0 : E)
    {N M : ℕ} {R δ L b D X Λ : ℝ}
    (hδ : 0 < δ) (hL : 0 < L) (hb : 0 < b) (hD : 0 ≤ D)
    (hX : 0 ≤ X) (hΛ : 0 < Λ) (hinit : 1 / (4 * Λ) ≤ b)
    (hstart : (S 0).weight = b) (hgrid₀ : (S 0).grid ≤ M)
    (hrec : ∀ t, S (t + 1) = outerAdvance (Metric.closedBall x0 R) x0 L δ X M (S t) (z t) (g t))
    (hactive : ∀ t < N, (S t).weight < X)
    (hfeasible : ∀ t < N, (S t).point ∈ Metric.closedBall x0 R ∧
      (S t).momentum ∈ Metric.closedBall x0 R ∧ z t ∈ Metric.closedBall x0 R)
    (htop : δ + 32 * L * R ^ 2 ≤ δ * 4 ^ M)
    (hsum : (∑ t ∈ Finset.range N, rawDissipation L δ (S t) (z t)) ≤ D) :
    (N : ℝ) ≤ 64 * Real.sqrt (δ * X) + 384 * (L * D * X) ^ (1 / 5 : ℝ) +
      ((M : ℝ) + 2) * ⌈Real.log (1 + 4 * Λ * X) / Real.log 2⌉₊ := by
  have hnonneg (t : ℕ) : 0 ≤ (S t).weight := by
    induction t with
    | zero => rw [hstart]; exact hb.le
    | succ t ih =>
      rw [hrec]
      exact ih.trans (SymmetricThirdOrderOuter.outerAdvance_weight_mono _ _ M hL.le hδ _ _ _ ih)
  have hmono : Monotone (fun t => (S t).weight) := by
    apply monotone_nat_of_le_succ
    intro t
    rw [hrec]
    exact SymmetricThirdOrderOuter.outerAdvance_weight_mono _ _ M hL.le hδ _ _ _ (hnonneg t)
  have hgrid (t : ℕ) : (S t).grid ≤ M := by
    induction t with
    | zero => exact hgrid₀
    | succ t ih =>
      rw [hrec]
      exact SymmetricThirdOrderOuter.outerAdvance_grid_le _ _ L δ X M _ _ _ ih
  apply scalar_trajectory_count (fun t => (S t).weight)
    (fun t => ‖z t - outerCenter δ (S t)‖) (fun t => (S t).grid)
    hδ hL hb hD hX hΛ hinit hmono hstart hactive (fun t _ => hgrid t)
  · intro t ht
    rw [hrec]
    simp only [outerAdvance, ite_eq_right (not_le.mpr (hactive t ht))]
  · intro t ht
    rw [hrec]
    simp only [outerAdvance, ite_eq_right (not_le.mpr (hactive t ht))]
  · intro t ht
    have hf := hfeasible t ht
    exact (SymmetricThirdOrderOuter.outer_curvature_bounds hL.le hδ (S t) (hnonneg t)
      hf.1 hf.2.1 hf.2.2).2.trans htop
  · exact hsum

end LongTails.Proofs.SymmetricThirdOrderPhasePartition
