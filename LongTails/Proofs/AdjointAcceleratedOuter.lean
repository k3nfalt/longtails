import LongTails.Proofs.AdjointAcceleratedInner
import LongTails.Proofs.AdjointBudget

open scoped RealInnerProductSpace

namespace OracleTemplate.CohypomonotoneAdjoint.Acc

open CohypomonotoneInclusion (target potential_identity)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def run0 (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (x0 : E) : E :=
  innerSolve L L₂ ρ F adj x0 x0

noncomputable def run (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (x0 : E) : ℕ → E
  | 0 => run0 L L₂ ρ F adj x0
  | n + 1 =>
    innerSolve L L₂ ρ F adj
      (tgt L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)
      (pred L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)

variable {F : E → E} {J : E → E →L[ℝ] E} {L L₂ ρ : ℝ}

lemma pot_step [FiniteDimensional ℝ E] (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂)
    (hρ : 0 ≤ ρ) {adj : E → E → E} (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (x0 : E) (n : ℕ) :
    pot L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (n + 1) (run L L₂ ρ F adj x0 (n + 1)) ≤
      pot L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) n (run L L₂ ρ F adj x0 n) := by
  have hu'def0 : run L L₂ ρ F adj x0 (n + 1) =
      innerSolve L L₂ ρ F adj
        (tgt L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)
        (pred L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n) := rfl
  set a := yv L ρ F (run0 L L₂ ρ F adj x0) with ha
  set u := run L L₂ ρ F adj x0 n with hu
  set u' := run L L₂ ρ F adj x0 (n + 1) with hu'
  set μ := ρ + 1 / L with hμ
  set t := tgt L ρ F a u n with ht
  set v0 := pred L ρ F a u n with hv0
  have hu'def : u' = innerSolve L L₂ ρ F adj t v0 := hu'def0
  set g := F u with hg
  set g' := F u' with hg'
  set k : ℝ := (n : ℝ) + 1 with hk
  have hk0 : 0 < k := by positivity
  have hk1 : k + 1 ≠ 0 := by positivity
  have hβ : 1 / ((n : ℝ) + 2) = 1 / (k + 1) := by rw [hk]; ring_nf
  set e := res L ρ F t u' with he
  set w := g' - (1 - 1 / (k + 1)) • g with hw
  have hguar : ‖e‖ ≤ ‖res L ρ F t v0‖ / (11 + 10 * ρ * L) := by
    rw [he, hu'def]; exact solve_guarantee h hL hL₂ hρ hadj t v0
  have hv0eq : v0 = t - ((2 * ρ + 1 / L) * (1 - 1 / ((n : ℝ) + 2))) • g := rfl
  have hrel := rel_error h hL hρ t g u' (1 / ((n : ℝ) + 2)) (by rw [← hv0eq]; exact hguar)
  rw [hβ] at hrel
  change ‖e‖ ≤ μ / 2 * ‖w‖ at hrel
  have hwe : ⟪w, e⟫ ≤ (μ - μ / 2) * ‖w‖ ^ 2 := by
    have h1 := real_inner_le_norm w e
    have h2 : ‖w‖ * ‖e‖ ≤ ‖w‖ * (μ / 2 * ‖w‖) := mul_le_mul_of_nonneg_left hrel (norm_nonneg w)
    nlinarith
  have hd' : yv L ρ F u' - a = (1 - 1 / (k + 1)) • (yv L ρ F u - a - (2 * (μ / 2)) • g) + e := by
    rw [he, res_eq_yv, ht, tgt, target, hβ]
    module
  have hco : μ * ‖g' - g‖ ^ 2 ≤
      ⟪g' - g, (1 - 1 / (k + 1)) • (yv L ρ F u - a - (2 * (μ / 2)) • g) + e -
        (yv L ρ F u - a)⟫ := by
    rw [← hd', sub_sub_sub_cancel_right]
    exact coco h u u'
  have hid := potential_identity g g' (yv L ρ F u - a) e μ (μ / 2) k hk1
  have hcast : ((n + 1 : ℕ) : ℝ) + 1 = k + 1 := by rw [hk]; push_cast; ring
  unfold pot
  rw [hcast, ← hg', hd', ← hg, ← hk]
  have hc : 0 ≤ k * (k + 1) := by positivity
  have hsq : 0 ≤ (k + 1) ^ 2 := by positivity
  have t1 := mul_nonneg hc (sub_nonneg.mpr hco)
  have t2 : 0 ≤ (k + 1) ^ 2 * ((μ - μ / 2) * ‖w‖ ^ 2 - ⟪w, e⟫) :=
    mul_nonneg hsq (sub_nonneg.mpr hwe)
  linarith

lemma pot_run [FiniteDimensional ℝ E] (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂)
    (hρ : 0 ≤ ρ) {adj : E → E → E} (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (x0 : E) (n : ℕ) :
    pot L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) n (run L L₂ ρ F adj x0 n) ≤ 0 := by
  induction n with
  | zero =>
    show pot L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) 0 (run0 L L₂ ρ F adj x0) ≤ 0
    have hμ : 0 < ρ + 1 / L := by positivity
    simp only [pot, sub_self, inner_zero_right, mul_zero, add_zero, Nat.cast_zero, zero_add,
      one_mul]
    nlinarith [sq_nonneg ‖F (run L L₂ ρ F adj x0 0)‖]
  | succ n ih => exact (pot_step h hL hL₂ hρ hadj x0 n).trans ih

lemma rate [FiniteDimensional ℝ E] (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂)
    (hρ : 0 ≤ ρ) {adj : E → E → E} (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (x0 : E)
    {xs : E} (hxs : F xs = 0) (n : ℕ) :
    ((n : ℝ) + 1) * ((ρ + 1 / L) / 2) * ‖F (run L L₂ ρ F adj x0 n)‖ ≤
      ‖yv L ρ F (run0 L L₂ ρ F adj x0) - xs‖ := by
  set a := yv L ρ F (run0 L L₂ ρ F adj x0) with ha
  set u := run L L₂ ρ F adj x0 n with hu
  have hp := pot_run h hL hL₂ hρ hadj x0 n
  rw [← ha, ← hu] at hp
  have hroot := coco_root h hxs u
  have hμ : 0 < ρ + 1 / L := by positivity
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hsplit : ⟪F u, yv L ρ F u - a⟫ = ⟪F u, yv L ρ F u - xs⟫ + ⟪F u, xs - a⟫ := by
    rw [← inner_add_right]; congr 1; abel
  have hcs : ⟪F u, xs - a⟫ ≥ -(‖F u‖ * ‖a - xs‖) := by
    have := real_inner_le_norm (F u) (a - xs)
    rw [show xs - a = -(a - xs) by abel, inner_neg_right]
    linarith
  unfold pot at hp
  rw [hsplit] at hp
  have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := hn.le
  have h1 := mul_le_mul_of_nonneg_left hroot hn0
  have hcs' : -(‖F u‖ * ‖a - xs‖) ≤ ⟪F u, xs - a⟫ := hcs
  have h3 := mul_le_mul_of_nonneg_left hcs' hn0
  have hk : ((n : ℝ) + 1) * (((n : ℝ) + 1) * ((ρ + 1 / L) / 2) * ‖F u‖ ^ 2 -
      ‖F u‖ * ‖a - xs‖) ≤ 0 := by nlinarith
  have key : ((n : ℝ) + 1) * ((ρ + 1 / L) / 2) * ‖F u‖ ^ 2 ≤ ‖F u‖ * ‖a - xs‖ := by
    by_contra hc
    push Not at hc
    have := mul_pos hn (sub_pos.mpr hc)
    linarith
  rcases (norm_nonneg (F u)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · have : ((n : ℝ) + 1) * ((ρ + 1 / L) / 2) * ‖F u‖ * ‖F u‖ ≤ ‖a - xs‖ * ‖F u‖ := by
      nlinarith
    exact le_of_mul_le_mul_right this hpos

lemma anchor_bound [FiniteDimensional ℝ E] (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂)
    (hρ : 0 ≤ ρ) {adj : E → E → E} (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (x0 : E)
    {xs : E} (hxs : F xs = 0) :
    ‖yv L ρ F (run0 L L₂ ρ F adj x0) - xs‖ ≤ 2 * ‖x0 - xs‖ := by
  have hg0 := solve_guarantee h hL hL₂ hρ hadj x0 x0
  have hg : ‖yv L ρ F (run0 L L₂ ρ F adj x0) - x0‖ ≤ ‖res L ρ F x0 x0‖ / (11 + 10 * ρ * L) := hg0
  have e1 : res L ρ F x0 x0 = (2 * ρ + 1 / L) • F x0 := by rw [res]; abel
  rw [e1] at hg
  have hF : ‖F x0‖ ≤ L * ‖x0 - xs‖ := by
    have := h.lip x0 xs; rwa [hxs, sub_zero] at this
  have hγ0 : 0 ≤ 2 * ρ + 1 / L := by positivity
  have hpos : 0 < 11 + 10 * ρ * L := by positivity
  have h1 : ‖(2 * ρ + 1 / L) • F x0‖ / (11 + 10 * ρ * L) ≤ ‖x0 - xs‖ := by
    rw [div_le_iff₀ hpos, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0]
    have e : (2 * ρ + 1 / L) * L = 1 + 2 * ρ * L := by field_simp; ring
    have h2 : (2 * ρ + 1 / L) * ‖F x0‖ ≤ (1 + 2 * ρ * L) * ‖x0 - xs‖ := by
      rw [← e, mul_assoc]; exact mul_le_mul_of_nonneg_left hF hγ0
    nlinarith [norm_nonneg (x0 - xs), mul_nonneg hρ hL.le]
  calc ‖yv L ρ F (run0 L L₂ ρ F adj x0) - xs‖
      ≤ ‖yv L ρ F (run0 L L₂ ρ F adj x0) - x0‖ + ‖x0 - xs‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖x0 - xs‖ + ‖x0 - xs‖ := add_le_add (hg.trans h1) le_rfl
    _ = 2 * ‖x0 - xs‖ := by ring

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
  have hguar := solve_guarantee h hL hL₂ hρ hadj (tgt L ρ F a u n) (pred L ρ F a u n)
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

end OracleTemplate.CohypomonotoneAdjoint.Acc
