import LongTails.Proofs.HomotopyNewtonInner
import LongTails.Proofs.LazyAnchoredLyapunov

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HomotopyNewtonOuter

open LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone
open LongTails.Algorithms.HomotopyNewtonAEP
open LongTails.Proofs.HomotopyNewtonSchedule
open LongTails.Proofs.MonotoneTensorBounds
open LongTails.Proofs.StiffNewtonStage
open LongTails.Proofs.TikhonovHomotopy
open LongTails.Proofs.HomotopyNewtonInner
open LongTails.Proofs.LazyAnchoredLyapunov

noncomputable section

variable {p : Params} (F : p.E → p.E)

def Succeeds (k : ℕ) (z Fz : p.E) : Prop := gval F k z Fz = 0 ∨ ∃ j, acc F k z Fz j

def firstAttempt (k : ℕ) (z Fz : p.E) : ℕ := by
  classical
  exact if h : ∃ j, acc F k z Fz j then Nat.find h else 0

def nextPoint (k : ℕ) (z Fz : p.E) : p.E := by
  classical
  exact if gval F k z Fz = 0 then center p k z Fz else attemptPoint F k z Fz (firstAttempt F k z Fz)

def outerSeq : ℕ → p.E × p.E
  | 0 => (p.x0, 0)
  | k + 1 =>
      let y := nextPoint F k (outerSeq k).1 (outerSeq k).2
      (y, F y)

def resolvent (k : ℕ) (z : p.E) : p.E := by
  classical
  exact if h : ∃ zs, resid F (step p k) (anchor p k z) zs = 0 then Classical.choose h else p.x0

def gap (k : ℕ) : ℝ :=
  ‖(outerSeq F (k + 1)).1 - center p k (outerSeq F k).1 (outerSeq F k).2‖

def radius (k : ℕ) : ℝ :=
  ‖resolvent F k (outerSeq F k).1 - center p k (outerSeq F k).1 (outerSeq F k).2‖

variable {F}

lemma first_spec {k : ℕ} {z Fz : p.E} (h : ∃ j, acc F k z Fz j) :
    acc F k z Fz (firstAttempt F k z Fz) ∧ ∀ j < firstAttempt F k z Fz, ¬ acc F k z Fz j := by
  classical
  have hj : firstAttempt F k z Fz = Nat.find h := by simp only [firstAttempt, h, ↓reduceDIte]
  rw [hj]
  exact ⟨Nat.find_spec h, fun j hjlt => Nat.find_min h hjlt⟩

lemma resolvent_spec [FiniteDimensional ℝ p.E] (h : Regular F p.L) (hp : Valid p) (k : ℕ)
    (z : p.E) : resid F (step p k) (anchor p k z) (resolvent F k z) = 0 := by
  classical
  have hz := h.zero_exists (step_pos hp k) (anchor p k z)
  simp only [resolvent, hz, ↓reduceDIte]
  exact Classical.choose_spec hz

lemma center_eq (k : ℕ) (z Fz : p.E) (hFz : k = 0 ∨ Fz = F z) :
    center p k z Fz = anchor p k z -
      (step p k * cumulative p k / cumulative p (k + 1)) • F z := by
  unfold center
  rcases hFz with h0 | h0
  · subst h0; simp [cumulative]
  · rw [h0]

lemma anchor_sub (hp : Valid p) (k : ℕ) (z : p.E) :
    anchor p k z - p.x0 =
      (cumulative p k / (cumulative p k + step p k)) • (z - p.x0) := by
  unfold anchor
  rw [cumulative_succ]
  have h1 : cumulative p k + step p k ≠ 0 := by
    have := cumulative_nonneg hp k; have := step_pos hp k; linarith
  have h2 : step p k / (cumulative p k + step p k) =
      1 - cumulative p k / (cumulative p k + step p k) := by field_simp; ring
  rw [h2]
  module

lemma anchor_dist (hp : Valid p) (k : ℕ) (z xs : p.E) :
    ‖anchor p k z - xs‖ ≤ max ‖p.x0 - xs‖ ‖z - xs‖ := by
  have hA := cumulative_nonneg hp k
  have ha := step_pos hp k
  have hA1 := cumulative_succ_pos hp k
  set t := cumulative p k / cumulative p (k + 1)
  have ht0 : 0 ≤ t := by positivity
  have ht1 : step p k / cumulative p (k + 1) = 1 - t := by
    have ht : t = cumulative p k / cumulative p (k + 1) := rfl
    rw [ht, cumulative_succ] at *
    field_simp; ring
  have : anchor p k z - xs = (1 - t) • (p.x0 - xs) + t • (z - xs) := by
    unfold anchor; rw [ht1]; module
  rw [this]
  have ht1' : t ≤ 1 := by
    rw [div_le_one hA1, cumulative_succ]; linarith
  calc ‖(1 - t) • (p.x0 - xs) + t • (z - xs)‖ ≤ (1 - t) * ‖p.x0 - xs‖ + t * ‖z - xs‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht0,
          abs_of_nonneg (by linarith)]
    _ ≤ (1 - t) * max ‖p.x0 - xs‖ ‖z - xs‖ + t * max ‖p.x0 - xs‖ ‖z - xs‖ := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = max ‖p.x0 - xs‖ ‖z - xs‖ := by ring

def attemptCap (k : ℕ) : ℕ := Nat.log2 ⌈step p k * stiff p⌉₊ + 1

lemma cap_pow (k : ℕ) : 1 + step p k * stiff p ≤ (2 : ℝ) ^ attemptCap (p := p) k := by
  have h := Nat.lt_log2_self (n := ⌈step p k * stiff p⌉₊)
  have h' : ((⌈step p k * stiff p⌉₊ : ℕ) : ℝ) + 1 ≤ 2 ^ (Nat.log2 ⌈step p k * stiff p⌉₊ + 1) := by
    exact_mod_cast Nat.succ_le_of_lt h
  have hc : step p k * stiff p ≤ (⌈step p k * stiff p⌉₊ : ℝ) := Nat.le_ceil _
  unfold attemptCap; linarith

structure StepFacts (F : p.E → p.E) (k : ℕ) (z Fz : p.E) : Prop where
  succ : Succeeds F k z Fz
  desc : potential p.x0 (cumulative p (k + 1)) (nextPoint F k z Fz) (F (nextPoint F k z Fz)) ≤
    potential p.x0 (cumulative p k) z (F z) -
      3 / 8 * (cumulative p (k + 1) / step p k) ^ 2 *
        ‖nextPoint F k z Fz - center p k z Fz‖ ^ 2
  rad : ‖resolvent F k z - center p k z Fz‖ ≤ 3 / 2 * ‖nextPoint F k z Fz - center p k z Fz‖
  radD : ‖resolvent F k z - center p k z Fz‖ ≤ p.D
  cost : gval F k z Fz = 0 ∨ (firstAttempt F k z Fz ≤ attemptCap (p := p) k ∧
    guess p k (gval F k z Fz) (firstAttempt F k z Fz) ≤
      2 * ‖resolvent F k z - center p k z Fz‖)

lemma outer_step [FiniteDimensional ℝ p.E] (h : Regular F p.L) (hp : Valid p) {xs : p.E}
    (hxs : F xs = 0) (hD : ‖p.x0 - xs‖ ≤ p.D)
    (hH : ∀ y ∈ Metric.closedBall p.x0 (5 * p.D), ‖fderiv ℝ F y‖ ≤ stiff p)
    (k : ℕ) (z Fz : p.E) (hFz : k = 0 ∨ Fz = F z)
    (hV : potential p.x0 (cumulative p k) z (F z) ≤ 0) (hz : ‖z - xs‖ ≤ 3 * p.D) :
    StepFacts F k z Fz ∧
      ‖nextPoint F k z Fz - xs‖ ≤ max p.D ‖z - xs‖ + ‖nextPoint F k z Fz - center p k z Fz‖ / 2 := by
  classical
  set a := step p k with ha_def
  set A := cumulative p k with hA_def
  have ha : 0 < a := step_pos hp k
  have hA : 0 ≤ A := cumulative_nonneg hp k
  have hA1 : cumulative p (k + 1) = A + a := cumulative_succ k
  set zs := resolvent F k z with hzs_def
  set c := center p k z Fz with hc_def
  set w := anchor p k z
  have hzs : resid F a w zs = 0 := resolvent_spec h hp k z
  have hzsw : a • F zs + zs = w := by simp only [resid, sub_eq_zero] at hzs; exact hzs
  have hceq := center_eq (F := F) k z Fz hFz
  have hctr : c = ((a / (A + a)) • p.x0 + (A / (A + a)) • z) - (a * A / (A + a)) • F z := by
    rw [hc_def, hceq]; unfold anchor; rw [hA1, mul_comm a A, mul_div_assoc]
  have hzs1 : zs - p.x0 = (A / (A + a)) • (z - p.x0) - a • F zs + 0 := by
    have hw' : anchor p k z = a • F zs + zs := hzsw.symm
    rw [add_zero, ← anchor_sub hp k z, hw']; abel
  have desc1 := descent p.x0 z zs (F z) (F zs) 0 a A ha hA hzs1 (h.mono zs z)
  rw [← hctr, norm_zero] at desc1
  have hlow1 : -(p.D ^ 2 / 2) ≤ potential p.x0 (A + a) zs (F zs) := by
    apply potential_lower p.x0 xs zs (F zs) (A + a) p.D (by positivity) hD
    have := h.mono zs xs; rwa [hxs, sub_zero] at this
  have hRsq : ‖zs - c‖ ^ 2 ≤ (p.D * a / (A + a)) ^ 2 := by
    have hpos : 0 < (A + a) ^ 2 / (2 * a ^ 2) := by positivity
    have h1 : (A + a) ^ 2 / (2 * a ^ 2) * ‖zs - c‖ ^ 2 ≤ p.D ^ 2 / 2 := by nlinarith
    have h2 : (p.D * a / (A + a)) ^ 2 = (p.D ^ 2 / 2) / ((A + a) ^ 2 / (2 * a ^ 2)) := by
      field_simp
    rw [h2, le_div_iff₀ hpos]; linarith
  have hRD : ‖zs - c‖ ≤ p.D := by
    have hD0 := hp.D
    have h1 : ‖zs - c‖ ≤ p.D * a / (A + a) :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hRsq
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hzsx : ‖zs - xs‖ ≤ max p.D ‖z - xs‖ := by
    have h1 := h.strong_resolvent ha zs xs
    rw [hzsw, hxs, smul_zero, zero_add] at h1
    exact h1.trans ((anchor_dist hp k z xs).trans (max_le_max hD le_rfl))
  have hball : ∀ y ∈ Metric.closedBall zs ‖zs - c‖, ‖fderiv ℝ F y‖ ≤ stiff p := by
    intro y hy
    apply hH
    rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
    have hmax : max p.D ‖z - xs‖ ≤ 3 * p.D := max_le (by linarith [hp.D]) hz
    calc ‖y - p.x0‖ ≤ ‖y - zs‖ + ‖zs - xs‖ + ‖xs - p.x0‖ := by
          have e : y - p.x0 = (y - zs) + (zs - xs) + (xs - p.x0) := by abel
          rw [e]; exact norm_add₃_le
      _ ≤ p.D + 3 * p.D + p.D := by
          rw [norm_sub_rev xs p.x0]; linarith [hzsx.trans hmax]
      _ = 5 * p.D := by ring
  have hsucc : Succeeds F k z Fz ∧ (gval F k z Fz = 0 ∨ (firstAttempt F k z Fz ≤ attemptCap (p := p) k ∧
      guess p k (gval F k z Fz) (firstAttempt F k z Fz) ≤ 2 * ‖zs - c‖)) := by
    by_cases hg0 : gval F k z Fz = 0
    · exact ⟨Or.inl hg0, Or.inl hg0⟩
    have hg : 0 < gval F k z Fz := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg0)
    obtain ⟨hRg, hgR⟩ := h.bracket hp k z Fz hzs hball
    have hex : ∃ j, ‖zs - c‖ ≤ guess p k (gval F k z Fz) j := by
      refine ⟨attemptCap (p := p) k, ?_⟩
      unfold guess
      have := cap_pow (p := p) k
      have hd := one_le_denom hp k
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    set j0 := Nat.find hex
    have hlo : ‖zs - c‖ ≤ guess p k (gval F k z Fz) j0 := Nat.find_spec hex
    have hhi : guess p k (gval F k z Fz) j0 ≤ 2 * ‖zs - c‖ := by
      rcases Nat.eq_zero_or_pos j0 with h0 | h0
      · rw [h0]; unfold guess
        have hd := one_le_denom hp k
        rw [pow_zero, mul_one, div_le_iff₀ (by linarith)]
        nlinarith [norm_nonneg (zs - c), stiff_nonneg hp, mul_nonneg ha.le (stiff_nonneg hp)]
      · have hm := Nat.find_min hex (show j0 - 1 < j0 by omega)
        have hs := guess_succ (p := p) k (gval F k z Fz) (j0 - 1)
        rw [show j0 - 1 + 1 = j0 by omega] at hs
        rw [hs]; linarith [not_le.mp hm]
    have hacc := attempt_success h hp k z Fz hzs hg hlo hhi hball
    have hj0cap : j0 ≤ attemptCap (p := p) k := by
      apply Nat.find_min'
      unfold guess
      have := cap_pow (p := p) k
      have hd := one_le_denom hp k
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    have hex2 : ∃ j, acc F k z Fz j := ⟨j0, hacc⟩
    obtain ⟨-, hmin⟩ := first_spec hex2
    have hle : firstAttempt F k z Fz ≤ j0 := by
      by_contra hcon; exact hmin j0 (by omega) hacc
    refine ⟨Or.inr hex2, Or.inr ⟨hle.trans hj0cap, ?_⟩⟩
    refine le_trans ?_ hhi
    unfold guess
    have hd := one_le_denom hp k
    gcongr
    · norm_num
  set y := nextPoint F k z Fz with hy_def
  set r := a • F y + y - w with hr_def
  have hacc' : ‖r‖ ≤ ‖y - c‖ / 2 := by
    by_cases hg0 : gval F k z Fz = 0
    · have hyc : y = c := by simp only [hy_def, nextPoint, hg0, ↓reduceIte]; rfl
      have : ‖r‖ = gval F k z Fz := by rw [hr_def, hyc]; rfl
      rw [this, hg0, hyc, sub_self, norm_zero]; norm_num
    · have hex2 : ∃ j, acc F k z Fz j := by
        rcases hsucc.1 with h0 | h0
        · exact absurd h0 hg0
        · exact h0
      have := (first_spec hex2).1
      have hyc : y = attemptPoint F k z Fz (firstAttempt F k z Fz) := by
        simp only [hy_def, nextPoint, hg0, ↓reduceIte]
      rw [hr_def, hyc]; exact this
  have hy1 : y - p.x0 = (A / (A + a)) • (z - p.x0) - a • F y + r := by
    rw [hr_def, ← anchor_sub hp k z]; abel
  have desc2 := descent p.x0 z y (F z) (F y) r a A ha hA hy1 (h.mono y z)
  rw [← hctr] at desc2
  have hr2 : ‖r‖ ^ 2 ≤ ‖y - c‖ ^ 2 / 4 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hacc' 2
    nlinarith
  have hyzs : ‖y - zs‖ ≤ ‖r‖ := by
    have := h.strong_resolvent ha y zs
    rwa [hzsw] at this
  refine ⟨⟨hsucc.1, ?_, ?_, ?_, hsucc.2⟩, ?_⟩
  · rw [hA1]
    have e : (A + a) ^ 2 / (2 * a ^ 2) * (‖y - c‖ ^ 2 / 4 - ‖y - c‖ ^ 2) =
        -(3 / 8 * ((A + a) / a) ^ 2 * ‖y - c‖ ^ 2) := by field_simp; ring
    have hpos : 0 ≤ (A + a) ^ 2 / (2 * a ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_left (show ‖r‖ ^ 2 - ‖y - c‖ ^ 2 ≤ ‖y - c‖ ^ 2 / 4 - ‖y - c‖ ^ 2
      by linarith) hpos
    linarith
  · calc ‖zs - c‖ = ‖(zs - y) + (y - c)‖ := by congr 1; abel
      _ ≤ ‖zs - y‖ + ‖y - c‖ := norm_add_le _ _
      _ ≤ 3 / 2 * ‖y - c‖ := by rw [norm_sub_rev zs y]; linarith
  · exact hRD
  · calc ‖y - xs‖ ≤ ‖y - zs‖ + ‖zs - xs‖ := by
          have := norm_add_le (y - zs) (zs - xs); simpa using this
      _ ≤ max p.D ‖z - xs‖ + ‖y - c‖ / 2 := by linarith

lemma outerSeq_value (k : ℕ) : k = 0 ∨ (outerSeq F k).2 = F (outerSeq F k).1 := by
  cases k with
  | zero => left; rfl
  | succ k => right; rfl

lemma inv_sq_sum (k : ℕ) :
    ∑ l ∈ Finset.range k, (2 / ((l : ℝ) + 2)) ^ 2 ≤ 4 * (1 - 1 / ((k : ℝ) + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : (2 / ((k : ℝ) + 2)) ^ 2 ≤ 4 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + 1)) := by
      rw [div_pow, div_sub_div _ _ (by positivity) (by positivity),
        div_le_iff₀ (by positivity)]
      field_simp
      nlinarith
    push_cast
    linarith

lemma gap_sum_bound (k : ℕ) (S : ℝ)
    (hS : ∑ l ∈ Finset.range k, ((l + 2) / 2 : ℝ) ^ 2 * gap F l ^ 2 ≤ S) (hS0 : 0 ≤ S) :
    ∑ l ∈ Finset.range k, gap F l ≤ 2 * Real.sqrt S := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range k) (fun l => 2 / ((l : ℝ) + 2))
    (fun l => ((l : ℝ) + 2) / 2 * gap F l)
  have hprod : ∀ l ∈ Finset.range k, 2 / ((l : ℝ) + 2) * (((l : ℝ) + 2) / 2 * gap F l) = gap F l := by
    intro l _; field_simp
  rw [Finset.sum_congr rfl hprod] at hcs
  have hsq : ∑ l ∈ Finset.range k, (((l : ℝ) + 2) / 2 * gap F l) ^ 2 ≤ S := by
    refine le_trans (le_of_eq ?_) hS
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_pow]
  have hinv := inv_sq_sum k
  have hk : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
  have hle : (∑ l ∈ Finset.range k, gap F l) ^ 2 ≤ (2 * Real.sqrt S) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hS0]
    calc _ ≤ _ := hcs
      _ ≤ 4 * S := by
          have h1 : 0 ≤ ∑ l ∈ Finset.range k, (((l : ℝ) + 2) / 2 * gap F l) ^ 2 :=
            Finset.sum_nonneg fun _ _ => sq_nonneg _
          have h2 : ∑ l ∈ Finset.range k, (2 / ((l : ℝ) + 2)) ^ 2 ≤ 4 := by linarith
          calc _ ≤ 4 * ∑ l ∈ Finset.range k, (((l : ℝ) + 2) / 2 * gap F l) ^ 2 :=
                mul_le_mul_of_nonneg_right h2 h1
            _ ≤ 4 * S := by linarith
      _ = 2 ^ 2 * S := by norm_num
  have hpos : 0 ≤ 2 * Real.sqrt S := by positivity
  rcases le_or_gt (∑ l ∈ Finset.range k, gap F l) 0 with h0 | h0
  · linarith
  · exact (pow_le_pow_iff_left₀ h0.le hpos (by norm_num)).mp hle

lemma aep_invariant [FiniteDimensional ℝ p.E] (h : Regular F p.L) (hp : Valid p) {xs : p.E}
    (hxs : F xs = 0) (hD : ‖p.x0 - xs‖ ≤ p.D)
    (hH : ∀ y ∈ Metric.closedBall p.x0 (5 * p.D), ‖fderiv ℝ F y‖ ≤ stiff p) :
    ∀ k, (∀ l < k, StepFacts F l (outerSeq F l).1 (outerSeq F l).2) ∧
      potential p.x0 (cumulative p k) (outerSeq F k).1 (F (outerSeq F k).1) ≤
        -(3 / 8 * ∑ l ∈ Finset.range k, ((l + 2) / 2 : ℝ) ^ 2 * gap F l ^ 2) ∧
      ‖(outerSeq F k).1 - xs‖ ≤ p.D + (∑ l ∈ Finset.range k, gap F l) / 2
  | 0 => by
    refine ⟨fun l hl => absurd hl (Nat.not_lt_zero l), ?_, ?_⟩
    · simp [potential, cumulative]
    · simpa [outerSeq] using hD
  | k + 1 => by
    obtain ⟨hprev, hV, hz⟩ := aep_invariant h hp hxs hD hH k
    have hS : 0 ≤ ∑ l ∈ Finset.range k, ((l + 2) / 2 : ℝ) ^ 2 * gap F l ^ 2 :=
      Finset.sum_nonneg (fun l _ => by positivity)
    have hV0 : potential p.x0 (cumulative p k) (outerSeq F k).1 (F (outerSeq F k).1) ≤ 0 := by
      linarith
    have hlow : -(p.D ^ 2 / 2) ≤
        potential p.x0 (cumulative p k) (outerSeq F k).1 (F (outerSeq F k).1) := by
      apply potential_lower p.x0 xs _ _ _ p.D (cumulative_nonneg hp k) hD
      have := h.mono (outerSeq F k).1 xs; rwa [hxs, sub_zero] at this
    have hSb : ∑ l ∈ Finset.range k, ((l + 2) / 2 : ℝ) ^ 2 * gap F l ^ 2 ≤ 4 / 3 * p.D ^ 2 := by
      linarith
    have hgs := gap_sum_bound (F := F) k (4 / 3 * p.D ^ 2) hSb (by positivity)
    have hsq : Real.sqrt (4 / 3 * p.D ^ 2) ≤ 6 / 5 * p.D := by
      rw [Real.sqrt_le_left (by have := hp.D; positivity)]
      nlinarith [sq_nonneg p.D]
    have hz3 : ‖(outerSeq F k).1 - xs‖ ≤ 3 * p.D := by
      have := hp.D; linarith
    obtain ⟨hfacts, hnext⟩ := outer_step h hp hxs hD hH k (outerSeq F k).1 (outerSeq F k).2
      (outerSeq_value k) hV0 hz3
    refine ⟨fun l hl => ?_, ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
      · exact hprev l hl
      · subst hl; exact hfacts
    · rw [Finset.sum_range_succ]
      have e : gap F k = ‖nextPoint F k (outerSeq F k).1 (outerSeq F k).2 -
          center p k (outerSeq F k).1 (outerSeq F k).2‖ := rfl
      have e2 : (outerSeq F (k + 1)).1 = nextPoint F k (outerSeq F k).1 (outerSeq F k).2 := rfl
      have hr := ratio_cumulative hp k
      have hdesc := hfacts.desc
      rw [hr] at hdesc
      rw [e2, e]
      linarith
    · rw [Finset.sum_range_succ]
      have e2 : (outerSeq F (k + 1)).1 = nextPoint F k (outerSeq F k).1 (outerSeq F k).2 := rfl
      have e : gap F k = ‖nextPoint F k (outerSeq F k).1 (outerSeq F k).2 -
          center p k (outerSeq F k).1 (outerSeq F k).2‖ := rfl
      rw [e2]
      rw [e] at *
      have hmax : max p.D ‖(outerSeq F k).1 - xs‖ ≤ p.D + (∑ l ∈ Finset.range k, gap F l) / 2 := by
        have : 0 ≤ ∑ l ∈ Finset.range k, gap F l := Finset.sum_nonneg fun _ _ => norm_nonneg _
        exact max_le (by linarith) hz
      linarith

lemma cumulative_final (hp : Valid p) : cumulative p (outerCount p) = 2 * p.D / p.ε := by
  unfold cumulative scale
  have hN : (0 : ℝ) < outerCount p := by exact_mod_cast outerCount_pos
  have := hp.ε
  field_simp
  ring

lemma final_accuracy [FiniteDimensional ℝ p.E] (h : Regular F p.L) (hp : Valid p) {xs : p.E}
    (hxs : F xs = 0) (hD : ‖p.x0 - xs‖ ≤ p.D)
    (hH : ∀ y ∈ Metric.closedBall p.x0 (5 * p.D), ‖fderiv ℝ F y‖ ≤ stiff p) :
    ‖F (outerSeq F (outerCount p)).1‖ ≤ p.ε := by
  obtain ⟨-, hV, -⟩ := aep_invariant h hp hxs hD hH (outerCount p)
  have hS : 0 ≤ ∑ l ∈ Finset.range (outerCount p), ((l + 2) / 2 : ℝ) ^ 2 * gap F l ^ 2 :=
    Finset.sum_nonneg (fun l _ => by positivity)
  have hA : 0 < cumulative p (outerCount p) := by
    rw [cumulative_final hp]; have := hp.D; have := hp.ε; positivity
  have hg : 0 ≤ ⟪F (outerSeq F (outerCount p)).1, (outerSeq F (outerCount p)).1 - xs⟫ := by
    have := h.mono (outerSeq F (outerCount p)).1 xs; rwa [hxs, sub_zero] at this
  have hres := residual_bound p.x0 xs _ _ _ p.D hA hD hg (by linarith)
  rw [cumulative_final hp] at hres
  have := hp.ε
  calc _ ≤ 2 * p.D / (2 * p.D / p.ε) := hres
    _ = p.ε := by have := hp.D; field_simp

end

end LongTails.Proofs.HomotopyNewtonOuter
