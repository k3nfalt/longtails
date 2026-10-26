import LongTailsOnline.Proofs.TaskAllocationConfidence
import LongTailsOnline.Proofs.TaskAllocationInvariants
import LongTailsOnline.Proofs.TaskAllocationOracle

open MeasureTheory ProbabilityTheory

namespace LongTailsOnline.Proofs.TaskAllocation

open LongTailsOnline.Setups.StationaryTaskAllocation
open LongTailsOnline.Algorithms.ParallelTaskAllocation

lemma level_eq_optimum {k B : ℕ} (u : Worker k → ℝ) :
    level (B := B) u = optimum (B := B) u :=
  (upperOracle_le u (oracle (B := B) u)).antisymm (optimum_le_loss u (upperOracle u))

lemma quota_pos (p : Public) (θ u : ℝ) {C : ℕ} (hC : 0 < C) : 0 < quota p θ u C := by
  unfold quota
  rw [ite_eq_right (Nat.ne_of_gt hC)]
  omega

lemma bias_le_accuracy {p : Public} (hB : 0 < p.B) (hT : 0 < p.T) :
    bias p ≤ accuracy p / (16 * p.B) := by
  have hBr : (1 : ℝ) ≤ p.B := by exact_mod_cast hB
  have hTr : (1 : ℝ) ≤ p.T := by exact_mod_cast hT
  have hn : (1 : ℝ) ≤ p.k + 1 := by linarith [Nat.cast_nonneg (α := ℝ) p.k]
  have hBs : (p.B : ℝ) ≤ (p.B : ℝ) ^ 2 := by nlinarith
  have hTs : (p.T : ℝ) ≤ (p.T : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hTr) (sq_nonneg (p.T : ℝ))]
  have hden : 16 * (p.B : ℝ) * p.T ≤
      64 * (p.k + 1 : ℝ) * (p.B : ℝ) ^ 2 * (p.T : ℝ) ^ 3 := by
    calc
      16 * (p.B : ℝ) * p.T ≤ 64 * (p.B : ℝ) ^ 2 * (p.T : ℝ) ^ 3 := by
        gcongr
        linarith
      _ ≤ 64 * (p.k + 1 : ℝ) * (p.B : ℝ) ^ 2 * (p.T : ℝ) ^ 3 := by
        gcongr
        linarith
  calc
    bias p = 1 / (64 * (p.k + 1 : ℝ) * (p.B : ℝ) ^ 2 * (p.T : ℝ) ^ 3) :=
      bias_eq hB hT
    _ ≤ 1 / (16 * (p.B : ℝ) * p.T) := one_div_le_one_div_of_le (by positivity) hden
    _ = (1 / (p.T : ℝ)) / (16 * p.B) := by ring
    _ ≤ accuracy p / (16 * p.B) := div_le_div_of_nonneg_right
      (inv_horizon_le_accuracy hB hT) (by positivity)

lemma bias_le_phase {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {θ : ℝ} (hθ : accuracy p ≤ θ) {C : ℕ} (hC : 0 < C) (hCB : C ≤ p.B) :
    bias p ≤ θ / (16 * C) := by
  have hθ0 : 0 ≤ θ := (accuracy_pos hB hT).le.trans hθ
  calc
    _ ≤ accuracy p / (16 * p.B) := bias_le_accuracy hB hT
    _ ≤ θ / (16 * p.B) := div_le_div_of_nonneg_right hθ (by positivity)
    _ ≤ θ / (16 * C) := div_le_div_of_nonneg_left hθ0 (by positivity)
      (by exact_mod_cast Nat.mul_le_mul_left 16 hCB)

lemma quota_refinement {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {θ u : ℝ} {C N : ℕ} (hθ : 0 < θ) (hu : 0 ≤ u) (hC : 0 < C)
    (hN : quota p θ u C ≤ N) (hβ : bias p ≤ θ / (16 * C)) :
    2 * radius p u N ≤ θ / (2 * C) := by
  have hχ := scale_ge_one hB hT
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have hNr : (0 : ℝ) < N := by exact_mod_cast (quota_pos p θ u hC).trans_le hN
  have hceil : ⌈256 * scale p * u * (C : ℝ) ^ 2 / θ ^ 2 +
      32 * scale p * C / θ⌉₊ + 1 ≤ N := by
    simpa only [quota, ite_eq_right (Nat.ne_of_gt hC)] using hN
  have hceil' : (⌈256 * scale p * u * (C : ℝ) ^ 2 / θ ^ 2 +
      32 * scale p * C / θ⌉₊ : ℝ) ≤ N := by
    exact_mod_cast (Nat.le_trans (Nat.le_succ _) hceil)
  have hsum := (Nat.le_ceil (256 * scale p * u * (C : ℝ) ^ 2 / θ ^ 2 +
    32 * scale p * C / θ)).trans hceil'
  have h0 : 0 ≤ 256 * scale p * u * (C : ℝ) ^ 2 / θ ^ 2 := by positivity
  have h1 : 0 ≤ 32 * scale p * C / θ := by positivity
  have hquad : 256 * scale p * u * (C : ℝ) ^ 2 ≤ N * θ ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hθ)).mp
    linarith
  have hlinear : 32 * scale p * C ≤ N * θ := by
    apply (div_le_iff₀ hθ).mp
    linarith
  let r := Real.sqrt (u * scale p / N)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : (N : ℝ) * r ^ 2 = u * scale p := by
    dsimp only [r]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hsquare : (16 * (C : ℝ) * r) ^ 2 ≤ θ ^ 2 := by
    apply le_of_mul_le_mul_left (a0 := hNr)
    calc
      (N : ℝ) * (16 * (C : ℝ) * r) ^ 2 = 256 * (C : ℝ) ^ 2 * ((N : ℝ) * r ^ 2) := by ring
      _ = 256 * scale p * u * (C : ℝ) ^ 2 := by rw [hrsq]; ring
      _ ≤ _ := hquad
  have hroot : 4 * r ≤ θ / (4 * C) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * C)).mpr
    nlinarith
  have hlin : 4 * scale p / N ≤ θ / (8 * C) := by
    apply (div_le_div_iff₀ hNr (by positivity : (0 : ℝ) < 8 * C)).mpr
    nlinarith
  have hbias : 2 * bias p ≤ θ / (8 * C) := by
    calc
      _ ≤ 2 * (θ / (16 * C)) := mul_le_mul_of_nonneg_left hβ (by norm_num)
      _ = _ := by ring
  calc
    2 * radius p u N = 4 * r + 4 * scale p / N + 2 * bias p := by unfold radius r; ring
    _ ≤ θ / (4 * C) + θ / (8 * C) + θ / (8 * C) :=
      add_le_add (add_le_add hroot hlin) hbias
    _ = _ := by ring

lemma capacity_le_batch {k : ℕ} (B : ℕ) (L : ℝ) (s : Worker k → ℝ) (i : Worker k) :
    capacity B L s i ≤ B := by
  unfold capacity
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

lemma capacity_antitone {k B : ℕ} {L V : ℝ} {s v : Worker k → ℝ}
    (hV : 0 ≤ V) (hL : L ≤ V) (hs : ∀ i, s i ≤ v i) (i : Worker k) :
    capacity B L v i ≤ capacity B V s i := by
  by_cases hi : 0 < s i
  · have hv : 0 < v i := hi.trans_le (hs i)
    simp only [capacity, ite_eq_left hi, ite_eq_left hv]
    apply min_le_min_left
    apply Nat.floor_mono
    exact (div_le_div_of_nonneg_right hL hv.le).trans
      (div_le_div_of_nonneg_left hV hi (hs i))
  · simp only [capacity, ite_eq_right hi]
    exact capacity_le_batch B L v i

lemma refine_intervals_narrow (p : Public) (s : Statistics p.k) (ci : Intervals p.k)
    (i : Worker p.k) :
    ci.1 i ≤ (refineIntervals p s ci).1 i ∧
      (refineIntervals p s ci).2 i ≤ ci.2 i := by
  unfold refineIntervals
  dsimp only
  split_ifs
  · exact ⟨le_rfl, le_rfl⟩
  · exact ⟨le_max_left _ _, min_le_left _ _⟩

lemma refined_width {p : Public} (s : Statistics p.k) (ci : Intervals p.k)
    (i : Worker p.k) (hN : 0 < s.1 i) :
    (refineIntervals p s ci).2 i - (refineIntervals p s ci).1 i ≤
      2 * radius p (ci.2 i) (s.1 i) := by
  simp only [refineIntervals, ite_eq_right (Nat.ne_of_gt hN)]
  have hl' : s.2 i / s.1 i - radius p (ci.2 i) (s.1 i) ≤
      max (ci.1 i) (max 0 (s.2 i / s.1 i - radius p (ci.2 i) (s.1 i))) :=
    (le_max_right 0 _).trans (le_max_right _ _)
  have hu : min (ci.2 i) (min 1 (s.2 i / s.1 i + radius p (ci.2 i) (s.1 i))) ≤
      s.2 i / s.1 i + radius p (ci.2 i) (s.1 i) :=
    (min_le_right _ _).trans (min_le_right _ _)
  linarith

lemma quota_phase_refinement {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {μ : Worker p.k → ℝ} (s : Statistics p.k) (ci : Intervals p.k)
    (hci : ValidIntervals μ ci) (hnew : ValidIntervals μ (refineIntervals p s ci))
    {θ : ℝ} (hθ : accuracy p < θ)
    (hN : ∀ i, quota p θ (ci.2 i) (capacity p.B (level (B := p.B) ci.2) ci.1 i) ≤
      s.1 i) :
    ∀ i, uncertainty p.B (level (B := p.B) (refineIntervals p s ci).2)
      (refineIntervals p s ci).1 (refineIntervals p s ci).2 i ≤ θ / 2 := by
  let C := capacity p.B (level (B := p.B) ci.2) ci.1
  let ci' := refineIntervals p s ci
  have hθpos : 0 < θ := (accuracy_pos hB hT).trans hθ
  have hV : 0 ≤ level (B := p.B) ci.2 := by
    rw [level_eq_optimum]
    exact optimum_nonneg (fun i => (hci i).1.trans ((hci i).2.1.trans (hci i).2.2.1))
  have hlevel : level (B := p.B) ci'.2 ≤ level (B := p.B) ci.2 := by
    simp only [level_eq_optimum]
    exact optimum_mono (fun i => (refine_intervals_narrow p s ci i).2)
  have hcap (i) : capacity p.B (level (B := p.B) ci'.2) ci'.1 i ≤ C i :=
    capacity_antitone hV hlevel (fun i => (refine_intervals_narrow p s ci i).1) i
  intro i
  by_cases hzero : C i = 0
  · have hz : capacity p.B (level (B := p.B) ci'.2) ci'.1 i = 0 := by
      have := hcap i
      omega
    change (capacity p.B (level (B := p.B) ci'.2) ci'.1 i : ℝ) *
      (ci'.2 i - ci'.1 i) ≤ θ / 2
    rw [hz, Nat.cast_zero, zero_mul]
    positivity
  · have hC : 0 < C i := Nat.pos_of_ne_zero hzero
    have hβ := bias_le_phase hB hT hθ.le hC (capacity_le_batch p.B _ ci.1 i)
    have hr := quota_refinement hB hT hθpos
      ((hci i).1.trans ((hci i).2.1.trans (hci i).2.2.1)) hC (hN i) hβ
    have hwidth := refined_width s ci i ((quota_pos p θ (ci.2 i) hC).trans_le (hN i))
    have hwidth0 : 0 ≤ ci'.2 i - ci'.1 i :=
      sub_nonneg.mpr ((hnew i).2.1.trans (hnew i).2.2.1)
    change (capacity p.B (level (B := p.B) ci'.2) ci'.1 i : ℝ) *
      (ci'.2 i - ci'.1 i) ≤ θ / 2
    calc
      _ ≤ (C i : ℝ) * (ci'.2 i - ci'.1 i) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcap i) hwidth0
      _ ≤ (C i : ℝ) * (2 * radius p (ci.2 i) (s.1 i)) :=
        mul_le_mul_of_nonneg_left hwidth (Nat.cast_nonneg _)
      _ ≤ (C i : ℝ) * (θ / (2 * C i)) :=
        mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _)
      _ = θ / 2 := by field_simp

end LongTailsOnline.Proofs.TaskAllocation
