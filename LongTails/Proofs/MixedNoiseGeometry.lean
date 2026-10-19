import LongTails.Proofs.RecursiveGradientStep
import LongTails.Proofs.MixedNoiseSchedule
import Mathlib.Algebra.Order.Chebyshev

open scoped BigOperators

namespace OracleTemplate.MixedNoise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma norm_sum_sq_le {ι : Type*} (s : Finset ι) (v : ι → E) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have h := norm_sum_le s v
  have hnon : 0 ≤ ∑ i ∈ s, ‖v i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  exact (show ‖∑ i ∈ s, v i‖ ^ 2 ≤ (∑ i ∈ s, ‖v i‖) ^ 2 by
    nlinarith [norm_nonneg (∑ i ∈ s, v i)]).trans (sq_sum_le_card_mul_sum_sq ..)

omit [InnerProductSpace ℝ E] in
lemma segment_energy (x : ℕ → E) (a n : ℕ) :
    ‖x (a + n) - x a‖ ^ 2 ≤ (n : ℝ) *
      ∑ k ∈ Finset.range n, ‖x (a + k + 1) - x (a + k)‖ ^ 2 := by
  have htel : ∑ k ∈ Finset.range n, (x (a + k + 1) - x (a + k)) =
      x (a + n) - x a := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [Nat.add_succ]
        abel
  have h := norm_sum_sq_le (Finset.range n) (fun k => x (a + k + 1) - x (a + k))
  simpa only [htel, Finset.card_range] using h

lemma window_energy (u : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k) (T w : ℕ) :
    ∑ t ∈ Finset.range T, ∑ k ∈ Finset.range T,
      (if k < t ∧ t ≤ k + w then u k else 0) ≤
      (w : ℝ) * ∑ k ∈ Finset.range T, u k := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  let A := (Finset.range T).filter (fun t => k < t ∧ t ≤ k + w)
  have hsub : A ⊆ Finset.Ico (k + 1) (k + w + 1) := by
    intro t ht
    simp only [A, Finset.mem_filter, Finset.mem_range] at ht
    simp only [Finset.mem_Ico]
    omega
  have hcard : A.card ≤ w := by
    have := Finset.card_le_card hsub
    simp only [Nat.card_Ico] at this
    omega
  have heq : (∑ t ∈ Finset.range T,
      if k < t ∧ t ≤ k + w then u k else 0) = (A.card : ℝ) * u k := by
    rw [← Finset.sum_filter]
    simp [A]
  rw [heq]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hu k)

omit [InnerProductSpace ℝ E] in
lemma segment_energy_Ico (x : ℕ → E) {a b : ℕ} (hab : a ≤ b) :
    ‖x b - x a‖ ^ 2 ≤ ((b - a : ℕ) : ℝ) *
      ∑ k ∈ Finset.Ico a b, ‖x (k + 1) - x k‖ ^ 2 := by
  have h := segment_energy x a (b - a)
  rw [Nat.add_sub_of_le hab] at h
  simpa only [Finset.sum_Ico_eq_sum_range, Nat.add_comm] using h

omit [InnerProductSpace ℝ E] in
lemma segment_energy_in_window (x : ℕ → E) {a b t T w : ℕ}
    (hab : a ≤ b) (hbt : b ≤ t) (htT : t < T) (hta : t ≤ a + w) :
    ‖x b - x a‖ ^ 2 ≤ (w : ℝ) *
      ∑ k ∈ Finset.range T,
        if k < t ∧ t ≤ k + w then ‖x (k + 1) - x k‖ ^ 2 else 0 := by
  let A := (Finset.range T).filter (fun k => k < t ∧ t ≤ k + w)
  have hsub : Finset.Ico a b ⊆ A := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    simp only [A, Finset.mem_filter, Finset.mem_range]
    omega
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k _ _ => sq_nonneg ‖x (k + 1) - x k‖)
  have hlen : ((b - a : ℕ) : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast (show b - a ≤ w by omega)
  calc
    ‖x b - x a‖ ^ 2 ≤ ((b - a : ℕ) : ℝ) *
        ∑ k ∈ Finset.Ico a b, ‖x (k + 1) - x k‖ ^ 2 := segment_energy_Ico x hab
    _ ≤ (w : ℝ) * ∑ k ∈ A, ‖x (k + 1) - x k‖ ^ 2 :=
      mul_le_mul hlen hsum (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    _ = _ := by rw [Finset.sum_filter]

omit [InnerProductSpace ℝ E] in
lemma total_segment_energy (x : ℕ → E) (a b : ℕ → ℕ) (T w : ℕ)
    (hab : ∀ t < T, a t ≤ b t) (hbt : ∀ t < T, b t ≤ t)
    (hta : ∀ t < T, t ≤ a t + w) :
    ∑ t ∈ Finset.range T, ‖x (b t) - x (a t)‖ ^ 2 ≤
      (w : ℝ) ^ 2 * ∑ k ∈ Finset.range T, ‖x (k + 1) - x k‖ ^ 2 := by
  calc
    _ ≤ ∑ t ∈ Finset.range T, (w : ℝ) * ∑ k ∈ Finset.range T,
        if k < t ∧ t ≤ k + w then ‖x (k + 1) - x k‖ ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro t ht
      have ht := Finset.mem_range.mp ht
      exact segment_energy_in_window x (hab t ht) (hbt t ht) ht (hta t ht)
    _ = (w : ℝ) * ∑ t ∈ Finset.range T, ∑ k ∈ Finset.range T,
        if k < t ∧ t ≤ k + w then ‖x (k + 1) - x k‖ ^ 2 else 0 := by
      rw [Finset.mul_sum]
    _ ≤ (w : ℝ) * ((w : ℝ) *
        ∑ k ∈ Finset.range T, ‖x (k + 1) - x k‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (window_energy (fun k => ‖x (k + 1) - x k‖ ^ 2) (fun _ => sq_nonneg _) T w)
        (by positivity)
    _ = _ := by ring

omit [InnerProductSpace ℝ E] in
lemma hierarchy_spatial_energy (cfg : Config) (seed : RepresentativeSeed cfg)
    (x : ℕ → E) {l : ℕ} (hl : l < cfg.m) :
    (∑ t ∈ Finset.range cfg.T,
      ‖x (anchorIndex cfg seed t l) -
        x (anchorIndex cfg seed t (l + 1))‖ ^ 2) ≤
      81 * ((4 : ℝ) ^ l) ^ 2 * ∑ k ∈ Finset.range cfg.T, ‖x (k + 1) - x k‖ ^ 2 := by
  let a := fun t => anchorIndex cfg seed t l
  let b := fun t => anchorIndex cfg seed t (l + 1)
  have hh (t : ℕ) (ht : t < cfg.T) :
      max (a t) (b t) ≤ t ∧ t ≤ min (a t) (b t) + 9 * 4 ^ l :=
    by
      have ha := anchorIndex_le cfg seed hl.le ht.le
      have hb := anchorIndex_le cfg seed (by omega : l + 1 ≤ cfg.m) ht.le
      have hwa := anchorIndex_window cfg seed hl.le ht.le
      have hwb := anchorIndex_window cfg seed (by omega : l + 1 ≤ cfg.m) ht.le
      rw [pow_succ] at hwb
      refine ⟨max_le ha hb, ?_⟩
      dsimp [a, b]
      omega
  have he (t : ℕ) : ‖x (a t) - x (b t)‖ =
      ‖x (max (a t) (b t)) - x (min (a t) (b t))‖ := by
    by_cases hab : a t ≤ b t
    · simp only [max_eq_right hab, min_eq_left hab, norm_sub_rev]
    · have hba := Nat.le_of_lt (Nat.lt_of_not_ge hab)
      simp only [max_eq_left hba, min_eq_right hba]
  change (∑ t ∈ Finset.range cfg.T, ‖x (a t) - x (b t)‖ ^ 2) ≤ _
  simp_rw [he]
  have hs := total_segment_energy x (fun t => min (a t) (b t))
    (fun t => max (a t) (b t)) cfg.T (9 * 4 ^ l)
    (fun _ _ => min_le_max) (fun t ht => (hh t ht).1) (fun t ht => (hh t ht).2)
  convert hs using 1
  push_cast
  ring

variable [CompleteSpace E]

lemma inexact_path_energy {f : E → ℝ} {g : E → E} {L η Δ : ℝ}
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (x v : ℕ → E) (T : ℕ) (hstep : ∀ k, k < T → x (k + 1) = x k - η • v k)
    (hgap : ∀ y, f (x 0) - f y ≤ Δ) :
    η / 2 * ∑ k ∈ Finset.range T, ‖g (x k)‖ ^ 2 +
      η / 2 * (1 - L * η) * ∑ k ∈ Finset.range T, ‖v k‖ ^ 2 ≤
      Δ + η / 2 * ∑ k ∈ Finset.range T, ‖v k - g (x k)‖ ^ 2 := by
  have htel : ∀ n, n ≤ T →
      f (x n) + η / 2 * ∑ k ∈ Finset.range n, ‖g (x k)‖ ^ 2 +
        η / 2 * (1 - L * η) * ∑ k ∈ Finset.range n, ‖v k‖ ^ 2 ≤
        f (x 0) + η / 2 * ∑ k ∈ Finset.range n, ‖v k - g (x k)‖ ^ 2 := by
    intro n
    induction n with
    | zero => intro hn; simp
    | succ n ih =>
        intro hn
        have ih := ih (by omega)
        have hd := NonconvexFiniteSum.inexact_gradient_descent (η := η) hg hlip (x n) (v n)
        rw [← hstep n (by omega)] at hd
        simp only [Finset.sum_range_succ]
        nlinarith
  have := htel T le_rfl
  have := hgap (x T)
  linarith

lemma absorb_error_energy {η L Δ S V R G C : ℝ}
    (hη : 0 < η) (hηL : L * η = 1 / 2)
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hG : G ≤ 2 * L * Δ)
    (hdescent : η / 2 * S + η / 2 * (1 - L * η) * V ≤ Δ + η / 2 * R)
    (herror : R ≤ S / 4 + V / 4 + G + C) :
    η * S ≤ 4 * Δ + 2 * η * C := by
  rw [hηL] at hdescent
  have hmul := mul_le_mul_of_nonneg_left herror (by positivity : 0 ≤ η / 2)
  have hinit := mul_le_mul_of_nonneg_left hG hη.le
  have hscale : η * (2 * L * Δ) = Δ := by
    calc η * (2 * L * Δ) = 2 * (L * η) * Δ := by ring
      _ = Δ := by rw [hηL]; ring
  rw [hscale] at hinit
  have hnoise := mul_nonneg hη.le hC
  nlinarith

end OracleTemplate.MixedNoise
