import LongTails.Proofs.AdjointInner
import LongTails.Proofs.MultiStepAnchoredStep

open scoped RealInnerProductSpace

namespace OracleTemplate.CohypomonotoneAdjoint

open CohypomonotoneInclusion (target potential_identity)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def yv (L ρ : ℝ) (F : E → E) (u : E) : E := u + (2 * ρ + 1 / L) • F u

noncomputable def tgt (L ρ : ℝ) (F : E → E) (a u : E) (n : ℕ) : E :=
  target (ρ + 1 / L) n a (yv L ρ F u) (F u)

noncomputable def pred (L ρ : ℝ) (F : E → E) (a u : E) (n : ℕ) : E :=
  tgt L ρ F a u n - ((2 * ρ + 1 / L) * (1 - 1 / ((n : ℝ) + 2))) • F u

noncomputable def run0 (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (x0 : E) : E :=
  innerRun L L₂ ρ F adj x0 x0 (innerLen L L₂ ρ ‖res L ρ F x0 x0‖)

noncomputable def run (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (x0 : E) : ℕ → E
  | 0 => run0 L L₂ ρ F adj x0
  | n + 1 =>
    innerRun L L₂ ρ F adj
      (tgt L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)
      (pred L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)
      (innerLen L L₂ ρ ‖res L ρ F
        (tgt L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)
        (pred L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)‖)

noncomputable def pot (L ρ : ℝ) (F : E → E) (a : E) (n : ℕ) (u : E) : ℝ :=
  ((n : ℝ) + 1) * (((n : ℝ) + 1) * ((ρ + 1 / L) / 2) - (ρ + 1 / L)) * ‖F u‖ ^ 2 +
    ((n : ℝ) + 1) * ⟪F u, yv L ρ F u - a⟫

variable {F : E → E} {J : E → E →L[ℝ] E} {L L₂ ρ : ℝ}

lemma res_eq_yv (t u : E) : res L ρ F t u = yv L ρ F u - t := rfl

lemma coco (h : Hyp F J L L₂ ρ) (u u' : E) :
    (ρ + 1 / L) * ‖F u' - F u‖ ^ 2 ≤ ⟪F u' - F u, yv L ρ F u' - yv L ρ F u⟫ := by
  have hc := h.cohypo u' u
  have e : yv L ρ F u' - yv L ρ F u = (u' - u) + (2 * ρ + 1 / L) • (F u' - F u) := by
    rw [yv, yv, smul_sub]; abel
  rw [e, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  nlinarith

lemma coco_root (h : Hyp F J L L₂ ρ) {xs : E} (hxs : F xs = 0) (u : E) :
    (ρ + 1 / L) * ‖F u‖ ^ 2 ≤ ⟪F u, yv L ρ F u - xs⟫ := by
  have := coco h xs u
  have hy : yv L ρ F xs = xs := by rw [yv, hxs, smul_zero, add_zero]
  rwa [hxs, sub_zero, hy] at this

lemma pot_step [FiniteDimensional ℝ E] (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂)
    (hρ : 0 ≤ ρ) {adj : E → E → E} (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (x0 : E) (n : ℕ) :
    pot L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (n + 1) (run L L₂ ρ F adj x0 (n + 1)) ≤
      pot L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) n (run L L₂ ρ F adj x0 n) := by
  have hu'def0 : run L L₂ ρ F adj x0 (n + 1) =
      innerRun L L₂ ρ F adj
        (tgt L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)
        (pred L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)
        (innerLen L L₂ ρ ‖res L ρ F
          (tgt L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)
          (pred L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 n) n)‖) := rfl
  set a := yv L ρ F (run0 L L₂ ρ F adj x0) with ha
  set u := run L L₂ ρ F adj x0 n with hu
  set u' := run L L₂ ρ F adj x0 (n + 1) with hu'
  set μ := ρ + 1 / L with hμ
  set t := tgt L ρ F a u n with ht
  set v0 := pred L ρ F a u n with hv0
  have hu'def : u' = innerRun L L₂ ρ F adj t v0 (innerLen L L₂ ρ ‖res L ρ F t v0‖) := hu'def0
  set g := F u with hg
  set g' := F u' with hg'
  set k : ℝ := (n : ℝ) + 1 with hk
  have hk0 : 0 < k := by positivity
  have hk1 : k + 1 ≠ 0 := by positivity
  have hβ : 1 / ((n : ℝ) + 2) = 1 / (k + 1) := by rw [hk]; ring_nf
  set e := res L ρ F t u' with he
  set w := g' - (1 - 1 / (k + 1)) • g with hw
  have hguar : ‖e‖ ≤ ‖res L ρ F t v0‖ / (11 + 10 * ρ * L) := by
    rw [he, hu'def]; exact inner_guarantee h hL hL₂ hρ hadj t v0
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
  have hg0 := inner_guarantee h hL hL₂ hρ hadj x0 x0
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

end OracleTemplate.CohypomonotoneAdjoint
