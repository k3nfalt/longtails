import LongTails.Proofs.InexactJacobianInner

open scoped RealInnerProductSpace

namespace LongTails.Proofs.InexactJacobianOuter

open LongTails.Setups.InexactJacobianMonotone
open LongTails.Algorithms.NestedAnchoredInexactJacobian
open InexactJacobianModel InexactJacobianGeometry InexactJacobianPhase InexactJacobianInner
open LazyAnchoredLyapunov

noncomputable section

variable {p : Params}

def resolvent (F : p.E → p.E) (k : ℕ) (z : p.E) : p.E := by
  classical
  exact if h : ∃ xs, F xs + (1 / outerStep p k) • (xs - anchor p k z) = 0 then
    Classical.choose h else p.x0

lemma resolvent_spec (F : p.E → p.E) (hreg : Regular F)
    (hM : 0 < p.M) (hR : 0 < p.R) (hε : 0 < p.ε) (k : ℕ) (z : p.E) :
    F (resolvent F k z) + (1 / outerStep p k) • (resolvent F k z - anchor p k z) = 0 := by
  classical
  have h := regularized_root hM.le (outerStep_pos hR hε k) hreg.deriv hreg.lip hreg.mono
    (anchor p k z)
  simp only [resolvent, h, ↓reduceDIte]
  exact Classical.choose_spec h

lemma nextPoint_certificate (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    {base k : ℕ} {z Fz : p.E} (hs : Succeeds F J base k z Fz) :
    ‖outerStep p k • (F (nextPoint F J base k z Fz) +
      (1 / outerStep p k) • (nextPoint F J base k z Fz - anchor p k z))‖ ≤
      ‖nextPoint F J base k z Fz - center p k z Fz‖ / 2 :=
  (first_spec F J hs).2.1

lemma accepted_root_distance (F : p.E → p.E) (hreg : Regular F)
    (hR : 0 < p.R) (hε : 0 < p.ε) (k : ℕ) (z Fz y xs : p.E)
    (hzero : F xs + (1 / outerStep p k) • (xs - anchor p k z) = 0)
    (he : ‖outerStep p k • (F y + (1 / outerStep p k) • (y - anchor p k z))‖ ≤
      ‖y - center p k z Fz‖ / 2) :
    ‖center p k z Fz - xs‖ ≤ 3 / 2 * ‖y - center p k z Fz‖ := by
  have ha := outerStep_pos hR hε k
  let G := fun x => F x + (1 / outerStep p k) • (x - anchor p k z)
  have hd := strongly_monotone_certificate (G := G) (one_div_pos.mpr ha) hzero
    (regularized_strong (anchor p k z) (1 / outerStep p k) hreg.mono) (y := y)
  have he' : ‖G y‖ / (1 / outerStep p k) ≤ ‖y - center p k z Fz‖ / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at he
    simpa only [G, one_div, div_inv_eq_mul, mul_comm] using he
  have ht := norm_sub_le_norm_sub_add_norm_sub (center p k z Fz) y xs
  rw [norm_sub_rev (center p k z Fz) y] at ht
  linarith

lemma outer_descent (F : p.E → p.E) (hreg : Regular F)
    (J : ℕ → p.E → p.E →L[ℝ] p.E) (hR : 0 < p.R) (hε : 0 < p.ε)
    {base k : ℕ} {z Fz : p.E} (hFz : k = 0 ∨ Fz = F z) (hs : Succeeds F J base k z Fz) :
    potential p.x0 (cumulative p (k + 1)) (nextPoint F J base k z Fz) (F (nextPoint F J base k z Fz)) ≤
      potential p.x0 (cumulative p k) z Fz -
        3 / 8 * (cumulative p (k + 1) / outerStep p k) ^ 2 *
          ‖nextPoint F J base k z Fz - center p k z Fz‖ ^ 2 := by
  let y := nextPoint F J base k z Fz
  let a := outerStep p k
  let A := cumulative p k
  let e := a • (F y + (1 / a) • (y - anchor p k z))
  have ha : 0 < a := outerStep_pos hR hε k
  have hA : 0 ≤ A := cumulative_nonneg hR hε k
  have hsum : 0 < A + a := by positivity
  have hanchor : anchor p k z = (a / (A + a)) • p.x0 + (A / (A + a)) • z := by
    unfold anchor; rw [cumulative_succ]
  have hrec : y - p.x0 = (A / (A + a)) • (z - p.x0) - a • F y + e := by
    have heq : a / (A + a) = 1 - A / (A + a) := by field_simp; ring
    dsimp only [e]
    rw [smul_add, smul_smul, mul_one_div_cancel ha.ne', one_smul, hanchor, heq]
    module
  have hc : center p k z Fz = (a / (A + a)) • p.x0 + (A / (A + a)) • z -
      (a * A / (A + a)) • Fz := by unfold center; rw [hanchor, cumulative_succ]
  have hm : A = 0 ∨ 0 ≤ ⟪F y - Fz, y - z⟫ := by
    rcases hFz with h | h
    · left; simp [A, h, cumulative]
    · right; rw [h]; exact hreg.mono y z
  have he : ‖e‖ ≤ ‖y - center p k z Fz‖ / 2 := nextPoint_certificate F J hs
  have h := accepted_descent p.x0 z y Fz (F y) e (center p k z Fz) hA ha hrec hc hm he
  rw [cumulative_succ]
  exact h

def outerSeq (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E) : ℕ → ℕ × p.E × p.E
  | 0 => (0, p.x0, 0)
  | k + 1 =>
    let s := outerSeq F J k
    let y := nextPoint F J s.1 k s.2.1 s.2.2
    (s.1 + outerTicks F J s.1 k s.2.1 s.2.2, y, F y)

def gap (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E) (k : ℕ) : ℝ :=
  ‖(outerSeq F J (k + 1)).2.1 - center p k (outerSeq F J k).2.1 (outerSeq F J k).2.2‖

def radius (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E) (k : ℕ) : ℝ :=
  ‖center p k (outerSeq F J k).2.1 (outerSeq F J k).2.2 - resolvent F k (outerSeq F J k).2.1‖

lemma outerSeq_value (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E) (k : ℕ) :
    k = 0 ∨ (outerSeq F J k).2.2 = F (outerSeq F J k).2.1 := by
  cases k with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr rfl

lemma outer_energy (F : p.E → p.E) (hreg : Regular F)
    (J : ℕ → p.E → p.E →L[ℝ] p.E) (hJ : ∀ n x, ‖J n x - fderiv ℝ F x‖ ≤ p.δ)
    (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε) (n : ℕ) :
    potential p.x0 (cumulative p n) (outerSeq F J n).2.1 (outerSeq F J n).2.2 ≤
      -(3 / 8 * ∑ k ∈ Finset.range n, (cumulative p (k + 1) / outerStep p k) ^ 2 * gap F J k ^ 2) := by
  induction n with
  | zero => simp [outerSeq, potential, cumulative]
  | succ n ih =>
    have hs := succeeds F hreg J hJ hM hδ hR hε (outerSeq F J n).1 n
      (outerSeq F J n).2.1 (outerSeq F J n).2.2
    have hd := outer_descent F hreg J hR hε (outerSeq_value F J n) hs
    rw [Finset.sum_range_succ]
    change potential p.x0 (cumulative p (n + 1)) (outerSeq F J (n + 1)).2.1
      (outerSeq F J (n + 1)).2.2 ≤ potential p.x0 (cumulative p n) (outerSeq F J n).2.1
      (outerSeq F J n).2.2 - 3 / 8 * (cumulative p (n + 1) / outerStep p n) ^ 2 * gap F J n ^ 2 at hd
    linarith

lemma radius_le_gap (F : p.E → p.E) (hreg : Regular F)
    (J : ℕ → p.E → p.E →L[ℝ] p.E) (hJ : ∀ n x, ‖J n x - fderiv ℝ F x‖ ≤ p.δ)
    (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε) (k : ℕ) :
    radius F J k ≤ 3 / 2 * gap F J k := by
  have hs := succeeds F hreg J hJ hM hδ hR hε (outerSeq F J k).1 k
    (outerSeq F J k).2.1 (outerSeq F J k).2.2
  exact accepted_root_distance F hreg hR hε k _ _ _ _
    (resolvent_spec F hreg hM hR hε k _) (nextPoint_certificate F J hs)

lemma outer_energy_sum (F : p.E → p.E) (hreg : Regular F)
    (J : ℕ → p.E → p.E →L[ℝ] p.E) (hJ : ∀ n x, ‖J n x - fderiv ℝ F x‖ ≤ p.δ)
    (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (xs : p.E) (hzero : F xs = 0) (hx : ‖p.x0 - xs‖ ≤ p.R) (n : ℕ) :
    ∑ k ∈ Finset.range n, (cumulative p (k + 1) / outerStep p k) ^ 2 * gap F J k ^ 2 ≤
      4 / 3 * p.R ^ 2 := by
  have hg : 0 ≤ ⟪(outerSeq F J n).2.2, (outerSeq F J n).2.1 - xs⟫ := by
    rcases outerSeq_value F J n with h | h
    · simp [h, outerSeq]
    · rw [h]
      simpa only [hzero, sub_zero] using hreg.mono (outerSeq F J n).2.1 xs
  have hlo := potential_lower p.x0 xs (outerSeq F J n).2.1 (outerSeq F J n).2.2
    (cumulative p n) p.R (cumulative_nonneg hR hε n) hx hg
  have hi := outer_energy F hreg J hJ hM hδ hR hε n
  linarith

lemma cumulative_final (hR : 0 < p.R) (hε : 0 < p.ε) :
    cumulative p (outerCount p) = 2 * p.R / p.ε := by
  unfold cumulative scale
  have hK : (0 : ℝ) < outerCount p := by unfold outerCount; positivity
  field_simp
  ring

lemma final_accuracy (F : p.E → p.E) (hreg : Regular F)
    (J : ℕ → p.E → p.E →L[ℝ] p.E) (hJ : ∀ n x, ‖J n x - fderiv ℝ F x‖ ≤ p.δ)
    (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (xs : p.E) (hzero : F xs = 0) (hx : ‖p.x0 - xs‖ ≤ p.R) :
    ‖F (outerSeq F J (outerCount p)).2.1‖ ≤ p.ε := by
  have hK : 0 < outerCount p := by unfold outerCount; omega
  have hg : (outerSeq F J (outerCount p)).2.2 = F (outerSeq F J (outerCount p)).2.1 :=
    (outerSeq_value F J (outerCount p)).resolve_left (by omega)
  have hv := outer_energy F hreg J hJ hM hδ hR hε (outerCount p)
  have hsum : 0 ≤ ∑ k ∈ Finset.range (outerCount p),
      (cumulative p (k + 1) / outerStep p k) ^ 2 * gap F J k ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hA : 0 < cumulative p (outerCount p) := by rw [cumulative_final hR hε]; positivity
  have hroot : 0 ≤ ⟪(outerSeq F J (outerCount p)).2.2, (outerSeq F J (outerCount p)).2.1 - xs⟫ := by
    rw [hg]
    simpa only [hzero, sub_zero] using hreg.mono (outerSeq F J (outerCount p)).2.1 xs
  have h := residual_bound p.x0 xs (outerSeq F J (outerCount p)).2.1
    (outerSeq F J (outerCount p)).2.2 (cumulative p (outerCount p)) p.R hA hx hroot (by linarith)
  rw [hg, cumulative_final hR hε] at h
  have he : 2 * p.R / (2 * p.R / p.ε) = p.ε := by field_simp
  rwa [he] at h

end

end LongTails.Proofs.InexactJacobianOuter
