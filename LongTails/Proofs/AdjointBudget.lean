import LongTails.Proofs.AdjointOuter
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped RealInnerProductSpace

namespace OracleTemplate.CohypomonotoneAdjoint

open CohypomonotoneInclusion (target)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def hsum (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1)

lemma hsum_succ (n : ℕ) : hsum (n + 1) = hsum n + 1 / ((n : ℝ) + 1) := by
  simp [hsum, Finset.sum_range_succ]

lemma hsum_nonneg (n : ℕ) : 0 ≤ hsum n :=
  Finset.sum_nonneg fun i _ => by positivity

lemma hsum_mono {m n : ℕ} (h : m ≤ n) : hsum m ≤ hsum n := by
  unfold hsum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun i _ _ => by positivity

lemma hsum_le_log (n : ℕ) : hsum n ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  have e : (harmonic n : ℝ) = hsum n := by
    rw [harmonic, hsum]; push_cast; simp
  rw [← e]; exact h

variable {F : E → E} {J : E → E →L[ℝ] E} {L L₂ ρ : ℝ}

lemma nonexp_step (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hρ : 0 ≤ ρ) {xs : E} (hxs : F xs = 0)
    (u : E) : ‖yv L ρ F u - (ρ + 1 / L) • F u - xs‖ ≤ ‖yv L ρ F u - xs‖ := by
  have hroot := coco_root h hxs u
  have hμ : 0 ≤ ρ + 1 / L := by positivity
  have hsq : ‖yv L ρ F u - (ρ + 1 / L) • F u - xs‖ ^ 2 ≤ ‖yv L ρ F u - xs‖ ^ 2 := by
    rw [show yv L ρ F u - (ρ + 1 / L) • F u - xs = (yv L ρ F u - xs) - (ρ + 1 / L) • F u by abel,
      norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_comm]
    nlinarith [mul_le_mul_of_nonneg_left hroot hμ]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

lemma tgt_bound (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hρ : 0 ≤ ρ) {xs : E} (hxs : F xs = 0)
    (a u : E) (n : ℕ) :
    ‖tgt L ρ F a u n - xs‖ ≤
      1 / ((n : ℝ) + 2) * ‖a - xs‖ + (1 - 1 / ((n : ℝ) + 2)) * ‖yv L ρ F u - xs‖ := by
  have hβ0 : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
  have hβ1 : 0 ≤ 1 - 1 / ((n : ℝ) + 2) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have e : tgt L ρ F a u n - xs = (1 / ((n : ℝ) + 2)) • (a - xs) +
      (1 - 1 / ((n : ℝ) + 2)) • (yv L ρ F u - (ρ + 1 / L) • F u - xs) := by
    rw [tgt, target]; module
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ0]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ1]
    exact mul_le_mul_of_nonneg_left (nonexp_step h hL hρ hxs u) hβ1

section Run

variable [FiniteDimensional ℝ E] {adj : E → E → E}

lemma err_run (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ)
    (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (x0 : E) (n : ℕ) :
    ‖res L ρ F (tgt L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)
        (run L L₂ ρ F adj x0 (n + 1))‖ ≤
      (ρ + 1 / L) / 2 * ‖F (run L L₂ ρ F adj x0 (n + 1)) -
        (1 - 1 / ((n : ℝ) + 2)) • F (run L L₂ ρ F adj x0 n)‖ := by
  set a := yv L ρ F (run0 L L₂ ρ F adj x0)
  set u := run L L₂ ρ F adj x0 n
  have hguar := inner_guarantee h hL hL₂ hρ hadj (tgt L ρ F a u n) (pred L ρ F a u n)
  exact rel_error h hL hρ (tgt L ρ F a u n) (F u) (run L L₂ ρ F adj x0 (n + 1))
    (1 / ((n : ℝ) + 2)) hguar

lemma gnorm (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ)
    (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (x0 : E) {xs : E} (hxs : F xs = 0) {D : ℝ}
    (hD : ‖x0 - xs‖ ≤ D) (j : ℕ) :
    ‖F (run L L₂ ρ F adj x0 j)‖ ≤ 4 * D / (((j : ℝ) + 1) * (ρ + 1 / L)) := by
  have hr := rate h hL hL₂ hρ hadj x0 hxs j
  have ha := anchor_bound h hL hL₂ hρ hadj x0 hxs
  have hpos : 0 < ((j : ℝ) + 1) * (ρ + 1 / L) := by positivity
  rw [le_div_iff₀ hpos]
  have : ((j : ℝ) + 1) * ((ρ + 1 / L) / 2) * ‖F (run L L₂ ρ F adj x0 j)‖ ≤ 2 * D := by
    have : yv L ρ F (run L L₂ ρ F adj x0 0) = yv L ρ F (run0 L L₂ ρ F adj x0) := rfl
    linarith
  nlinarith

lemma err_bound (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ)
    (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (x0 : E) {xs : E} (hxs : F xs = 0) {D : ℝ}
    (hD : ‖x0 - xs‖ ≤ D) (n : ℕ) :
    ‖res L ρ F (tgt L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)
        (run L L₂ ρ F adj x0 (n + 1))‖ ≤ 4 * D / ((n : ℝ) + 1) := by
  have he := err_run h hL hL₂ hρ hadj x0 n
  have g1 := gnorm h hL hL₂ hρ hadj x0 hxs hD (n + 1)
  have g0 := gnorm h hL hL₂ hρ hadj x0 hxs hD n
  have hμ : 0 < ρ + 1 / L := by positivity
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hD
  have hβ1 : 0 ≤ 1 - 1 / ((n : ℝ) + 2) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hβ2 : 1 - 1 / ((n : ℝ) + 2) ≤ 1 := by
    have : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hw : ‖F (run L L₂ ρ F adj x0 (n + 1)) - (1 - 1 / ((n : ℝ) + 2)) • F (run L L₂ ρ F adj x0 n)‖ ≤
      8 * D / (((n : ℝ) + 1) * (ρ + 1 / L)) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ1]
    have e1 : 4 * D / ((((n + 1 : ℕ) : ℝ) + 1) * (ρ + 1 / L)) ≤
        4 * D / (((n : ℝ) + 1) * (ρ + 1 / L)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      push_cast
      nlinarith
    have e2 : (1 - 1 / ((n : ℝ) + 2)) * ‖F (run L L₂ ρ F adj x0 n)‖ ≤
        4 * D / (((n : ℝ) + 1) * (ρ + 1 / L)) :=
      (mul_le_of_le_one_left (norm_nonneg _) hβ2).trans g0
    have e3 : 8 * D / (((n : ℝ) + 1) * (ρ + 1 / L)) =
        4 * D / (((n : ℝ) + 1) * (ρ + 1 / L)) + 4 * D / (((n : ℝ) + 1) * (ρ + 1 / L)) := by ring
    linarith [g1.trans e1]
  refine he.trans ((mul_le_mul_of_nonneg_left hw (by positivity)).trans (le_of_eq ?_))
  field_simp; ring

lemma iter_bound (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ)
    (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (x0 : E) {xs : E} (hxs : F xs = 0) {D : ℝ}
    (hD : ‖x0 - xs‖ ≤ D) (m : ℕ) :
    ‖yv L ρ F (run L L₂ ρ F adj x0 m) - xs‖ ≤ 2 * D + 4 * D * hsum m := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hD
  have ha : ‖yv L ρ F (run0 L L₂ ρ F adj x0) - xs‖ ≤ 2 * D :=
    (anchor_bound h hL hL₂ hρ hadj x0 hxs).trans (by linarith)
  induction m with
  | zero => simp only [hsum, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]; exact ha
  | succ m ih =>
    set a := yv L ρ F (run0 L L₂ ρ F adj x0)
    set t := tgt L ρ F a (run L L₂ ρ F adj x0 m) m
    have he := err_bound h hL hL₂ hρ hadj x0 hxs hD m
    have ht := tgt_bound h hL hρ hxs a (run L L₂ ρ F adj x0 m) m
    have e : yv L ρ F (run L L₂ ρ F adj x0 (m + 1)) - xs =
        res L ρ F t (run L L₂ ρ F adj x0 (m + 1)) + (t - xs) := by
      rw [res_eq_yv]; abel
    rw [e, hsum_succ]
    have hβ0 : 0 ≤ 1 / ((m : ℝ) + 2) := by positivity
    have hβ1 : 0 ≤ 1 - 1 / ((m : ℝ) + 2) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hs0 := hsum_nonneg m
    have ht' : ‖t - xs‖ ≤ 2 * D + 4 * D * hsum m := by
      refine ht.trans ?_
      have h1 : 1 / ((m : ℝ) + 2) * ‖a - xs‖ ≤ 1 / ((m : ℝ) + 2) * (2 * D + 4 * D * hsum m) :=
        mul_le_mul_of_nonneg_left (ha.trans (by nlinarith)) hβ0
      have h2 := mul_le_mul_of_nonneg_left ih hβ1
      nlinarith
    calc ‖res L ρ F t (run L L₂ ρ F adj x0 (m + 1)) + (t - xs)‖
        ≤ ‖res L ρ F t (run L L₂ ρ F adj x0 (m + 1))‖ + ‖t - xs‖ := norm_add_le _ _
      _ ≤ 4 * D / ((m : ℝ) + 1) + (2 * D + 4 * D * hsum m) := add_le_add he ht'
      _ = 2 * D + 4 * D * (hsum m + 1 / ((m : ℝ) + 1)) := by ring

noncomputable def loopRes (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (x0 : E) : ℕ → ℝ
  | 0 => ‖res L ρ F x0 x0‖
  | n + 1 => ‖res L ρ F (tgt L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)
      (pred L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)‖

omit [FiniteDimensional ℝ E] in
lemma loopRes_zero (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hρ : 0 ≤ ρ) (x0 : E) {xs : E}
    (hxs : F xs = 0) {D : ℝ} (hD : ‖x0 - xs‖ ≤ D) :
    loopRes L L₂ ρ F adj x0 0 ≤ (2 * ρ + 1 / L) * L * D := by
  have e : res L ρ F x0 x0 = (2 * ρ + 1 / L) • F x0 := by rw [res]; abel
  show ‖res L ρ F x0 x0‖ ≤ _
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc]
  have := h.lip x0 xs
  rw [hxs, sub_zero] at this
  exact mul_le_mul_of_nonneg_left (this.trans (mul_le_mul_of_nonneg_left hD hL.le)) (by positivity)

lemma loopRes_succ (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ)
    (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (x0 : E) {xs : E} (hxs : F xs = 0) {D : ℝ}
    (hD : ‖x0 - xs‖ ≤ D) (n : ℕ) :
    loopRes L L₂ ρ F adj x0 (n + 1) ≤
      (2 * ρ + 1 / L) * L * D / ((n : ℝ) + 1) * (24 + 4 * hsum n) := by
  set a := yv L ρ F (run0 L L₂ ρ F adj x0)
  set u := run L L₂ ρ F adj x0 n
  set γ := 2 * ρ + 1 / L with hγ
  set μ := ρ + 1 / L with hμ
  set β := 1 / ((n : ℝ) + 2) with hβ
  have hγ0 : 0 ≤ γ := by positivity
  have hμpos : 0 < μ := by positivity
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hD
  have hβ0 : 0 ≤ β := by positivity
  have hβ1 : β ≤ 1 := by rw [hβ, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hβn : β ≤ 1 / ((n : ℝ) + 1) := by
    rw [hβ]; apply div_le_div_of_nonneg_left zero_le_one (by positivity); linarith
  set t := tgt L ρ F a u n with ht
  set v0 := pred L ρ F a u n with hv0
  have hres : res L ρ F t v0 = γ • F v0 - (γ * (1 - β)) • F u := by
    rw [res, hv0, pred, ← hγ, ← hβ]; abel
  have hvu : v0 - u = β • (a - yv L ρ F u) + (β * γ - (1 - β) * μ) • F u := by
    rw [hv0, pred, tgt, target, yv, ← hγ, ← hμ, ← hβ]; module
  have hg := gnorm h hL hL₂ hρ hadj x0 hxs hD n
  rw [← hμ] at hg
  have hit := iter_bound h hL hL₂ hρ hadj x0 hxs hD n
  have ha : ‖a - xs‖ ≤ 2 * D :=
    (anchor_bound h hL hL₂ hρ hadj x0 hxs).trans (by linarith)
  have hay : ‖a - yv L ρ F u‖ ≤ 4 * D + 4 * D * hsum n := by
    calc ‖a - yv L ρ F u‖ ≤ ‖a - xs‖ + ‖yv L ρ F u - xs‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub a xs (yv L ρ F u)
          rwa [norm_sub_rev xs] at this
      _ ≤ 2 * D + (2 * D + 4 * D * hsum n) := add_le_add ha hit
      _ = 4 * D + 4 * D * hsum n := by ring
  have hcoef : |β * γ - (1 - β) * μ| ≤ γ + μ := by
    rw [abs_le]; constructor <;> nlinarith
  have hvun : ‖v0 - u‖ ≤ β * (4 * D + 4 * D * hsum n) + (γ + μ) * ‖F u‖ := by
    rw [hvu]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ0]
      exact mul_le_mul_of_nonneg_left hay hβ0
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  have hFv0 : ‖F v0‖ ≤ ‖F u‖ + L * ‖v0 - u‖ := by
    have := h.lip v0 u
    calc ‖F v0‖ ≤ ‖F v0 - F u‖ + ‖F u‖ := norm_le_norm_sub_add _ _
      _ ≤ L * ‖v0 - u‖ + ‖F u‖ := add_le_add this le_rfl
      _ = ‖F u‖ + L * ‖v0 - u‖ := by ring
  have hresn : ‖res L ρ F t v0‖ ≤ γ * ‖F v0‖ + γ * ‖F u‖ := by
    rw [hres]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hγ0 (by linarith))]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hγ0 (by linarith)) (norm_nonneg _)
  have hμL : 1 ≤ μ * L := by rw [hμ]; field_simp; nlinarith [mul_nonneg hρ hL.le]
  have hγμ : γ ≤ 2 * μ := by rw [hγ, hμ]; have : 0 < 1 / L := by positivity
                             linarith
  have hFu : ‖F u‖ ≤ 4 * D / (((n : ℝ) + 1) * μ) := hg
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hcomb : ‖res L ρ F t v0‖ ≤ γ * ((2 + L * (γ + μ)) * ‖F u‖ +
      L * β * (4 * D + 4 * D * hsum n)) := by
    have := mul_le_mul_of_nonneg_left hvun hL.le
    nlinarith [norm_nonneg (F u), norm_nonneg (F v0)]
  have hs0 := hsum_nonneg n
  have hA : (2 + L * (γ + μ)) * ‖F u‖ ≤ 20 * L * D / ((n : ℝ) + 1) := by
    have h1 : (2 + L * (γ + μ)) ≤ 5 * (μ * L) := by nlinarith
    calc (2 + L * (γ + μ)) * ‖F u‖ ≤ 5 * (μ * L) * (4 * D / (((n : ℝ) + 1) * μ)) :=
          mul_le_mul h1 hFu (norm_nonneg _) (by positivity)
      _ = 20 * L * D / ((n : ℝ) + 1) := by field_simp; ring
  have hB : L * β * (4 * D + 4 * D * hsum n) ≤ L * D * (4 + 4 * hsum n) / ((n : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_left hβn (by positivity : 0 ≤ L * (4 * D + 4 * D * hsum n))
    calc L * β * (4 * D + 4 * D * hsum n) = L * (4 * D + 4 * D * hsum n) * β := by ring
      _ ≤ L * (4 * D + 4 * D * hsum n) * (1 / ((n : ℝ) + 1)) := this
      _ = L * D * (4 + 4 * hsum n) / ((n : ℝ) + 1) := by field_simp
  show ‖res L ρ F t v0‖ ≤ _
  refine hcomb.trans ?_
  calc γ * ((2 + L * (γ + μ)) * ‖F u‖ + L * β * (4 * D + 4 * D * hsum n))
      ≤ γ * (20 * L * D / ((n : ℝ) + 1) + L * D * (4 + 4 * hsum n) / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) hγ0
    _ = γ * L * D / ((n : ℝ) + 1) * (24 + 4 * hsum n) := by field_simp; ring

lemma loopRes_sum (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ)
    (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (x0 : E) {xs : E} (hxs : F xs = 0) {D : ℝ}
    (hD : ‖x0 - xs‖ ≤ D) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), loopRes L L₂ ρ F adj x0 j ≤
      (2 * ρ + 1 / L) * L * D * (1 + (24 + 4 * hsum N) * hsum N) := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hD
  have hc : 0 ≤ (2 * ρ + 1 / L) * L * D := by positivity
  rw [Finset.sum_range_succ']
  have h0 := loopRes_zero (adj := adj) h hL hρ x0 hxs hD
  have hs : ∑ n ∈ Finset.range N, loopRes L L₂ ρ F adj x0 (n + 1) ≤
      (2 * ρ + 1 / L) * L * D * ((24 + 4 * hsum N) * hsum N) := by
    calc ∑ n ∈ Finset.range N, loopRes L L₂ ρ F adj x0 (n + 1)
        ≤ ∑ n ∈ Finset.range N, (2 * ρ + 1 / L) * L * D * (24 + 4 * hsum N) * (1 / ((n : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro n hn
          have h1 := loopRes_succ h hL hL₂ hρ hadj x0 hxs hD n
          have h2 : hsum n ≤ hsum N := hsum_mono (Finset.mem_range.mp hn).le
          refine h1.trans ?_
          rw [div_mul_eq_mul_div, div_eq_mul_one_div]
          have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) hc) this
      _ = (2 * ρ + 1 / L) * L * D * (24 + 4 * hsum N) * hsum N := by
          rw [← Finset.mul_sum]; rfl
      _ = (2 * ρ + 1 / L) * L * D * ((24 + 4 * hsum N) * hsum N) := by ring
  linarith

end Run

end OracleTemplate.CohypomonotoneAdjoint
