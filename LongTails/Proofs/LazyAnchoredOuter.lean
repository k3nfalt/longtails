import LongTails.Proofs.LazyAnchoredInner
import LongTails.Proofs.LazyAnchoredLyapunov

open scoped RealInnerProductSpace

namespace LongTails.Proofs.LazyAnchoredOuter

open LongTails.Setups.UnconstrainedLipschitzJacobianMonotone
open LongTails.Algorithms.LazyAnchoredExtraProximal
open LongTails.Proofs.FrozenJacobianSplitting
open LongTails.Proofs.LazyAnchoredInner
open LongTails.Proofs.LazyAnchoredLyapunov

noncomputable section

variable {p : Params}

def Succeeds (F : p.E → p.E) (k : ℕ) (z Fz : p.E) : Prop :=
  ∃ j, ∃ i, i < iterations p k j ∧ acc F k z Fz j i

def firstAttempt (F : p.E → p.E) (k : ℕ) (z Fz : p.E) : ℕ := by
  classical
  exact if h : Succeeds F k z Fz then Nat.find h else 0

def firstIndex (F : p.E → p.E) (k : ℕ) (z Fz : p.E) : ℕ := by
  classical
  exact if h : ∃ i, i < iterations p k (firstAttempt F k z Fz) ∧
      acc F k z Fz (firstAttempt F k z Fz) i then Nat.find h else 0

def nextPoint (F : p.E → p.E) (k : ℕ) (z Fz : p.E) : p.E :=
  (trialAt F k z Fz (firstAttempt F k z Fz) (firstIndex F k z Fz)).trialPoint

def outerTicks (F : p.E → p.E) (k : ℕ) (z Fz : p.E) : ℕ :=
  (2 * firstIndex F k z Fz + 1) + attemptTicks (p := p) k (firstAttempt F k z Fz) + 2

lemma first_spec (F : p.E → p.E) {k : ℕ} {z Fz : p.E} (h : Succeeds F k z Fz) :
    firstIndex F k z Fz < iterations p k (firstAttempt F k z Fz) ∧
      acc F k z Fz (firstAttempt F k z Fz) (firstIndex F k z Fz) ∧
      (∀ j < firstAttempt F k z Fz, ∀ i < iterations p k j, ¬ acc F k z Fz j i) ∧
      (∀ i < firstIndex F k z Fz, ¬ acc F k z Fz (firstAttempt F k z Fz) i) := by
  classical
  have hj : firstAttempt F k z Fz = Nat.find h := by simp only [firstAttempt, h, ↓reduceDIte]
  have hspec := Nat.find_spec h
  rw [← hj] at hspec
  have hi : firstIndex F k z Fz = Nat.find hspec := by simp only [firstIndex, hspec, ↓reduceDIte]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hi]; exact (Nat.find_spec hspec).1
  · rw [hi]; exact (Nat.find_spec hspec).2
  · intro j hjlt i hi' hacc
    rw [hj] at hjlt
    exact Nat.find_min h hjlt ⟨i, hi', hacc⟩
  · intro i hilt hacc
    rw [hi] at hilt
    exact Nat.find_min hspec hilt ⟨lt_trans hilt (Nat.find_spec hspec).1, hacc⟩

lemma iterate_outer (F : p.E → p.E) {k : ℕ} {z Fz : p.E} (hk : k ≠ outerCount p)
    (h : Succeeds F k z Fz) :
    (trueStep F)^[outerTicks F k z Fz] (outerStart k z Fz) =
      outerStart (k + 1) (nextPoint F k z Fz) (F (nextPoint F k z Fz)) := by
  obtain ⟨hlt, hacc, hfail, hno⟩ := first_spec F h
  unfold outerTicks
  rw [Function.iterate_add_apply, Function.iterate_add_apply]
  rw [show (trueStep F)^[2] (outerStart k z Fz) = trueStep F (trueStep F (outerStart k z Fz))
    from rfl, step_jacobian F k z Fz hk, iterate_attempts F _ hfail]
  exact iterate_attempt_success F hlt hno hacc

def outerSeq (F : p.E → p.E) : ℕ → p.E × p.E
  | 0 => (p.x0, 0)
  | k + 1 =>
      let y := nextPoint F k (outerSeq F k).1 (outerSeq F k).2
      (y, F y)

def totalTicks (F : p.E → p.E) : ℕ → ℕ
  | 0 => 0
  | k + 1 => outerTicks F k (outerSeq F k).1 (outerSeq F k).2 + totalTicks F k

lemma iterate_total (F : p.E → p.E) :
    ∀ k, k ≤ outerCount p → (∀ l < k, Succeeds F l (outerSeq F l).1 (outerSeq F l).2) →
      (trueStep F)^[totalTicks F k] initial = outerStart k (outerSeq F k).1 (outerSeq F k).2
  | 0, _, _ => rfl
  | k + 1, hk, hs => by
    rw [totalTicks, Function.iterate_add_apply,
      iterate_total F k (by omega) (fun l hl => hs l (by omega)),
      iterate_outer F (by omega) (hs k (by omega))]
    rfl

def resolvent (F : p.E → p.E) (k : ℕ) (z : p.E) : p.E := by
  classical
  exact if h : ∃ zs, step p k • F zs + zs = anchor p k z then Classical.choose h else p.x0

lemma resolvent_spec (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε)
    (k : ℕ) (z : p.E) : step p k • F (resolvent F k z) + resolvent F k z = anchor p k z := by
  classical
  have h : ∃ zs, step p k • F zs + zs = anchor p k z :=
    resolvent_exists hreg.L_nonneg hreg.deriv hreg.lip hreg.mono (step_pos hp k) _
  simp only [resolvent, h, ↓reduceDIte]
  exact Classical.choose_spec h

lemma center_eq (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (hFz : k = 0 ∨ Fz = F z) :
    center p k z Fz = ((step p k / (cumulative p k + step p k)) • p.x0 +
      (cumulative p k / (cumulative p k + step p k)) • z) -
      (step p k * cumulative p k / (cumulative p k + step p k)) • F z := by
  unfold center anchor
  rw [cumulative_succ]
  rcases hFz with h | h
  · subst h; simp [cumulative]
  · rw [h]

lemma anchor_sub (hp : 0 < p.D ∧ 0 < p.ε) (k : ℕ) (z : p.E) :
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

lemma strong_resolvent (F : p.E → p.E) (hreg : Regular p F) {a : ℝ} (ha : 0 < a) (y zs : p.E) :
    ‖y - zs‖ ≤ ‖(a • F y + y) - (a • F zs + zs)‖ := by
  have hm := hreg.mono y zs
  have hinner : ‖y - zs‖ ^ 2 ≤ ⟪(a • F y + y) - (a • F zs + zs), y - zs⟫ := by
    have : (a • F y + y) - (a • F zs + zs) = a • (F y - F zs) + (y - zs) := by module
    rw [this, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith [mul_nonneg ha.le hm]
  have h2 := real_inner_le_norm ((a • F y + y) - (a • F zs + zs)) (y - zs)
  rcases eq_or_lt_of_le (norm_nonneg (y - zs)) with h | h
  · rw [← h]; exact norm_nonneg _
  · nlinarith

lemma certificate_identity (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε)
    (k : ℕ) (z Fz : p.E) (j i : ℕ) :
    (withTrial F (trialAt F k z Fz j i)).certificate =
      step p k • F (trialAt F k z Fz j i).trialPoint + (trialAt F k z Fz j i).trialPoint -
        anchor p k z := by
  have ha := step_pos hp k
  have hτ := innerStep_pos hreg.L_nonneg hp k j
  have hy := solve_spec (fderiv ℝ F (center p k z Fz))
    (jacobian_monotone hreg.mono (hreg.deriv _)) (β := 1 + innerStep p k j / step p k)
    (by positivity) hτ.le
    ((zseq F k z Fz j i).1 - innerStep p k j • (zseq F k z Fz j i).2 -
      innerStep p k j • (F (center p k z Fz) - fderiv ℝ F (center p k z Fz) (center p k z Fz) -
        (step p k)⁻¹ • anchor p k z))
  exact fbf_exact _ _ _ _ _ _ _ _ _ _ ha hτ hy

lemma outer_step (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε) {xs : p.E}
    (hxs : F xs = 0) (hD : ‖p.x0 - xs‖ ≤ p.D) (k : ℕ) (z Fz : p.E) (hFz : k = 0 ∨ Fz = F z)
    (hV : potential p.x0 (cumulative p k) z (F z) ≤ 0) :
    ‖center p k z Fz - resolvent F k z‖ ≤ radiusBound p k ∧ Succeeds F k z Fz ∧
      potential p.x0 (cumulative p (k + 1)) (nextPoint F k z Fz) (F (nextPoint F k z Fz)) ≤
        potential p.x0 (cumulative p k) z (F z) -
          3 / 8 * (cumulative p (k + 1) / step p k) ^ 2 *
            ‖nextPoint F k z Fz - center p k z Fz‖ ^ 2 ∧
      ‖center p k z Fz - resolvent F k z‖ ≤ 3 / 2 * ‖nextPoint F k z Fz - center p k z Fz‖ := by
  set a := step p k with ha_def
  set A := cumulative p k with hA_def
  have ha : 0 < a := step_pos hp k
  have hA : 0 ≤ A := cumulative_nonneg hp k
  have hA1 : cumulative p (k + 1) = A + a := cumulative_succ k
  set zs := resolvent F k z with hzs_def
  set c := center p k z Fz with hc_def
  have hzs : a • F zs + zs = anchor p k z := resolvent_spec F hreg hp k z
  have hceq := center_eq F k z Fz hFz
  have hzs1 : zs - p.x0 = (A / (A + a)) • (z - p.x0) - a • F zs + 0 := by
    rw [add_zero, ← anchor_sub hp k z, ← hzs]; abel
  have desc1 := descent p.x0 z zs (F z) (F zs) 0 a A ha hA hzs1 (hreg.mono zs z)
  rw [← hceq, norm_zero] at desc1
  have hlow1 : -(p.D ^ 2 / 2) ≤ potential p.x0 (A + a) zs (F zs) := by
    apply potential_lower p.x0 xs zs (F zs) (A + a) p.D (by positivity) hD
    have := hreg.mono zs xs; rwa [hxs, sub_zero] at this
  have hRsq : ‖zs - c‖ ^ 2 ≤ (p.D * a / (A + a)) ^ 2 := by
    have hpos : 0 < (A + a) ^ 2 / (2 * a ^ 2) := by positivity
    have h1 : (A + a) ^ 2 / (2 * a ^ 2) * ‖zs - c‖ ^ 2 ≤ p.D ^ 2 / 2 := by nlinarith
    have h2 : (p.D * a / (A + a)) ^ 2 = (p.D ^ 2 / 2) / ((A + a) ^ 2 / (2 * a ^ 2)) := by
      field_simp
    rw [h2, le_div_iff₀ hpos]; linarith
  have hR : ‖c - zs‖ ≤ radiusBound p k := by
    have hrb : radiusBound p k = p.D * a / (A + a) := by
      simp only [radiusBound, hA1, ha_def]
    rw [hrb, norm_sub_rev]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by have := hp.1; positivity) (by norm_num)).mp hRsq
  have hguess : guess p k (doublings p k) = radiusBound p k := by
    unfold guess; field_simp
  have hsucc : Succeeds F k z Fz := by
    obtain ⟨i, hi, hacc⟩ := attempt_success F hreg hp (j := doublings p k) hzs (hguess ▸ hR)
    exact ⟨doublings p k, i, hi, hacc⟩
  refine ⟨hR, hsucc, ?_⟩
  obtain ⟨-, hacc, -, -⟩ := first_spec F hsucc
  set y := nextPoint F k z Fz with hy_def
  set r := (withTrial F (trialAt F k z Fz (firstAttempt F k z Fz)
    (firstIndex F k z Fz))).certificate with hr_def
  have hr : r = a • F y + y - anchor p k z := certificate_identity F hreg hp k z Fz _ _
  have hacc' : ‖r‖ ≤ ‖y - c‖ / 2 := hacc
  have hy1 : y - p.x0 = (A / (A + a)) • (z - p.x0) - a • F y + r := by
    rw [hr, ← anchor_sub hp k z]; abel
  have desc2 := descent p.x0 z y (F z) (F y) r a A ha hA hy1 (hreg.mono y z)
  rw [← hceq] at desc2
  have hr2 : ‖r‖ ^ 2 ≤ ‖y - c‖ ^ 2 / 4 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hacc' 2
    nlinarith
  constructor
  · rw [hA1]
    have e : (A + a) ^ 2 / (2 * a ^ 2) * (‖y - c‖ ^ 2 / 4 - ‖y - c‖ ^ 2) =
        -(3 / 8 * ((A + a) / a) ^ 2 * ‖y - c‖ ^ 2) := by field_simp; ring
    have hpos : 0 ≤ (A + a) ^ 2 / (2 * a ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_left (show ‖r‖ ^ 2 - ‖y - c‖ ^ 2 ≤ ‖y - c‖ ^ 2 / 4 - ‖y - c‖ ^ 2
      by linarith) hpos
    linarith
  · have hyzs : ‖y - zs‖ ≤ ‖r‖ := by
      have := strong_resolvent F hreg ha y zs
      rw [hzs] at this
      have e : a • F y + y - anchor p k z = r := hr.symm
      rwa [e] at this
    calc ‖c - zs‖ = ‖(c - y) + (y - zs)‖ := by congr 1; abel
      _ ≤ ‖c - y‖ + ‖y - zs‖ := norm_add_le _ _
      _ ≤ 3 / 2 * ‖y - c‖ := by rw [norm_sub_rev c y]; linarith

def gap (F : p.E → p.E) (k : ℕ) : ℝ :=
  ‖(outerSeq F (k + 1)).1 - center p k (outerSeq F k).1 (outerSeq F k).2‖

def radius (F : p.E → p.E) (k : ℕ) : ℝ :=
  ‖center p k (outerSeq F k).1 (outerSeq F k).2 - resolvent F k (outerSeq F k).1‖

lemma outerSeq_value (F : p.E → p.E) (k : ℕ) : k = 0 ∨ (outerSeq F k).2 = F (outerSeq F k).1 := by
  cases k with
  | zero => left; rfl
  | succ k => right; rfl

lemma aep_invariant (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε) {xs : p.E}
    (hxs : F xs = 0) (hD : ‖p.x0 - xs‖ ≤ p.D) :
    ∀ k, k ≤ outerCount p →
      (∀ l < k, Succeeds F l (outerSeq F l).1 (outerSeq F l).2 ∧
        radius F l ≤ radiusBound p l ∧ radius F l ≤ 3 / 2 * gap F l) ∧
      potential p.x0 (cumulative p k) (outerSeq F k).1 (F (outerSeq F k).1) ≤
        -(3 / 8 * ∑ l ∈ Finset.range k, (cumulative p (l + 1) / step p l) ^ 2 * gap F l ^ 2)
  | 0, _ => by
    refine ⟨fun l hl => absurd hl (Nat.not_lt_zero l), ?_⟩
    simp [potential, cumulative]
  | k + 1, hk => by
    obtain ⟨hprev, hV⟩ := aep_invariant F hreg hp hxs hD k (by omega)
    have hS : 0 ≤ ∑ l ∈ Finset.range k, (cumulative p (l + 1) / step p l) ^ 2 * gap F l ^ 2 :=
      Finset.sum_nonneg (fun l _ => by positivity)
    have hV0 : potential p.x0 (cumulative p k) (outerSeq F k).1 (F (outerSeq F k).1) ≤ 0 := by
      linarith
    obtain ⟨hR, hsucc, hdesc, hRd⟩ := outer_step F hreg hp hxs hD k (outerSeq F k).1
      (outerSeq F k).2 (outerSeq_value F k) hV0
    refine ⟨fun l hl => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
      · exact hprev l hl
      · subst hl; exact ⟨hsucc, hR, hRd⟩
    · rw [Finset.sum_range_succ]
      have e : gap F k = ‖nextPoint F k (outerSeq F k).1 (outerSeq F k).2 -
          center p k (outerSeq F k).1 (outerSeq F k).2‖ := rfl
      have e2 : (outerSeq F (k + 1)).1 = nextPoint F k (outerSeq F k).1 (outerSeq F k).2 := rfl
      rw [e2, e]
      linarith

lemma cumulative_final (hp : 0 < p.D ∧ 0 < p.ε) : cumulative p (outerCount p) = 2 * p.D / p.ε := by
  unfold cumulative scale
  have hN : (0 : ℝ) < outerCount p := by unfold outerCount; positivity
  have := hp.2
  field_simp
  ring

lemma final_accuracy (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε) {xs : p.E}
    (hxs : F xs = 0) (hD : ‖p.x0 - xs‖ ≤ p.D) :
    ‖F (outerSeq F (outerCount p)).1‖ ≤ p.ε := by
  obtain ⟨-, hV⟩ := aep_invariant F hreg hp hxs hD (outerCount p) le_rfl
  have hS : 0 ≤ ∑ l ∈ Finset.range (outerCount p),
      (cumulative p (l + 1) / step p l) ^ 2 * gap F l ^ 2 :=
    Finset.sum_nonneg (fun l _ => by positivity)
  have hA : 0 < cumulative p (outerCount p) := by
    rw [cumulative_final hp]; have := hp.1; have := hp.2; positivity
  have hg : 0 ≤ ⟪F (outerSeq F (outerCount p)).1, (outerSeq F (outerCount p)).1 - xs⟫ := by
    have := hreg.mono (outerSeq F (outerCount p)).1 xs; rwa [hxs, sub_zero] at this
  have h := residual_bound p.x0 xs _ _ _ p.D hA hD hg (by linarith)
  rw [cumulative_final hp] at h
  have := hp.2
  calc _ ≤ 2 * p.D / (2 * p.D / p.ε) := h
    _ = p.ε := by have := hp.1; field_simp

end

end LongTails.Proofs.LazyAnchoredOuter
