import LongTails.Proofs.EscapeChainCount

namespace LongTails.Proofs.EscapeChainBounds

open scoped RealInnerProductSpace BigOperators
open EscapeChainProfiles EscapeChainGates EscapeChainCalculus EscapeChainFunction
open EscapeChainCoordinates EscapeChainCount RelativeHessianArctan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {K : ℕ} {u v : ℕ → E}

lemma lam_dead {c : ℝ} (hc : c ^ 2 ≤ 513 / 2097152) :
    lam c ≤ 1 / (24 * 2 ^ 28) ∧ 0 ≤ lam2 c := by
  set w := 16384 * c ^ 2 - 4 with hw
  have hw1 : w ≤ 1 / 128 := by rw [hw]; linarith
  rcases le_or_gt w 0 with h0 | h0
  · obtain ⟨e0, -, e2, -⟩ := unit_flat h0
    have e1 := (unit_flat h0).2.1
    refine ⟨?_, ?_⟩
    · show unit w ≤ _; rw [e0]; positivity
    · unfold lam2; rw [← hw, e2, e1]; simp
  · obtain ⟨e0, e1, e2, -⟩ := piece0 h0.le (by linarith)
    refine ⟨?_, ?_⟩
    · show unit w ≤ _
      rw [e0]
      have : w ^ 4 ≤ (1 / 128) ^ 4 := pow_le_pow_left₀ h0.le hw1 4
      have h4 : (1 / 128 : ℝ) ^ 4 = 1 / 2 ^ 28 := by norm_num
      rw [h4] at this
      calc w ^ 4 / 24 ≤ (1 / 2 ^ 28) / 24 := by gcongr
        _ = _ := by ring
    · unfold lam2; rw [← hw, e2, e1]; positivity

lemma lam_slope_lower {c : ℝ} (hc : 513 / 2097152 < c ^ 2) (hl : lam c < 1 / 24) :
    1 / (6 * 2 ^ 18) ≤ lam1 c * c := by
  set w := 16384 * c ^ 2 - 4 with hw
  have hw0 : 1 / 128 < w := by rw [hw]; linarith
  have hw1 : w < 1 := by
    by_contra h
    have hm := unit_monotone (le_of_not_gt h)
    have h1 : unit 1 = 1 / 24 := by rw [(piece0 (by norm_num) le_rfl).1]; norm_num
    have : lam c = unit w := rfl
    linarith
  obtain ⟨-, e1, -, -⟩ := piece0 (show (0 : ℝ) ≤ w by linarith) hw1.le
  have he : lam1 c * c = unit1 w * (32768 * c ^ 2) := by unfold lam1; rw [← hw]; ring
  rw [he, e1]
  have h3 : (1 / 128 : ℝ) ^ 3 ≤ w ^ 3 := pow_le_pow_left₀ (by norm_num) hw0.le 3
  have hc2 : 1 / 4096 ≤ c ^ 2 := by linarith
  have : (1 / 128 : ℝ) ^ 3 / 6 * (32768 * (1 / 4096)) ≤ w ^ 3 / 6 * (32768 * c ^ 2) := by
    gcongr
  calc (1 : ℝ) / (6 * 2 ^ 18) = (1 / 128 : ℝ) ^ 3 / 6 * (32768 * (1 / 4096)) := by norm_num
    _ ≤ _ := this

lemma lam_curvature {c : ℝ} (hc : 513 / 2097152 < c ^ 2) (hw : 16384 * c ^ 2 - 4 ≤ 19 / 10) :
    3 * (lam1 c * c) ≤ lam2 c * c ^ 2 ∧ 0 ≤ lam1 c * c := by
  set w := 16384 * c ^ 2 - 4 with hwd
  have hw0 : 0 ≤ w := by rw [hwd]; linarith
  have hr := curvature_ratio hw0 hw
  have h1 := unit1_nonneg w
  have hc2 : 8 ≤ 32768 * c ^ 2 := by linarith
  have e1 : lam1 c * c = unit1 w * (32768 * c ^ 2) := by unfold lam1; rw [← hwd]; ring
  have e2 : lam2 c * c ^ 2 = (unit2 w * (32768 * c ^ 2) + unit1 w) * (32768 * c ^ 2) := by
    unfold lam2; rw [← hwd]; ring
  rw [e1, e2]
  constructor
  · have hu2 : 0 ≤ unit2 w := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hc2 hu2]
  · positivity

lemma lam_plateau {c : ℝ} (hw : 19 / 10 < 16384 * c ^ 2 - 4) :
    2 / 5 ≤ lam c ∧ 5 * (lam1 c * c) ≤ 8 * lam c * (32768 * c ^ 2) := by
  set w := 16384 * c ^ 2 - 4 with hwd
  have hm := unit_monotone hw.le
  have hr := slope_ratio hw.le
  have e1 : lam1 c * c = unit1 w * (32768 * c ^ 2) := by unfold lam1; rw [← hwd]; ring
  refine ⟨le_trans unit_at_nineteen_tenths hm, ?_⟩
  rw [e1]
  have : lam c = unit w := rfl
  rw [this]
  nlinarith [sq_nonneg c]

lemma density_lower {t : ℝ} (h0 : -1 / 100 ≤ t) (h1 : t ≤ 4 / 5) : 3 / 5 ≤ density t := by
  unfold density
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma density_lower' {t : ℝ} (h0 : 1 / 2 ≤ t) (h1 : t ≤ 3 / 5) : 7 / 10 ≤ density t := by
  unfold density
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma profile_lower {t : ℝ} (h : -1 ≤ t) : 3 / 4 ≤ profile t := by
  unfold profile
  have h1 : Real.arctan (-1) ≤ Real.arctan t := Real.arctan_le_arctan_iff.2 h
  rw [Real.arctan_neg, Real.arctan_one] at h1
  linarith [Real.pi_gt_three]

lemma prevPsi_bounds (u : ℕ → E) (l : ℕ) (x : E) : 0 ≤ prevPsi u l x ∧ prevPsi u l x ≤ 1 := by
  cases l with
  | zero => simp [prevPsi]
  | succ l => exact ⟨(ag_bounds (by norm_num) _ _).1, (ag_bounds (by norm_num) _ _).2.1⟩

lemma prevGam_bounds (u : ℕ → E) (l : ℕ) (x : E) : 0 ≤ prevGam u l x ∧ prevGam u l x ≤ 1 := by
  cases l with
  | zero => simp [prevGam]
  | succ l => exact ⟨(ag_bounds (by norm_num) _ _).1, (ag_bounds (by norm_num) _ _).2.1⟩

lemma prevGam_zero (u : ℕ → E) (x : E) : prevGam u 0 x = 1 := rfl
lemma prevPsi_zero (u : ℕ → E) (x : E) : prevPsi u 0 x = 1 := rfl
lemma prevGam_succ (u : ℕ → E) (l : ℕ) (x : E) : prevGam u (l + 1) x = gam ⟪u l, x⟫ := rfl
lemma prevPsi_succ (u : ℕ → E) (l : ℕ) (x : E) : prevPsi u (l + 1) x = psi ⟪u l, x⟫ := rfl

lemma inactive_term (u v : ℕ → E) (x : E) {l : ℕ} (hl : ¬ active u v x l) (t : ℝ) :
    prevGam u l x * sad ⟪v l, x⟫ * (loc1 (quarter u v l x) / 2 + loc2 (quarter u v l x) * t / 4) = 0 := by
  unfold active at hl
  rw [not_and_or] at hl
  rcases hl with h | h
  · rw [not_or] at h
    obtain ⟨h0, h1⟩ := h
    obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [prevGam_succ, (gam_flat (by simpa using le_of_not_gt h1)).1]; ring
  · have hq : 4 ≤ quarter u v l x := by unfold quarter; linarith [lt_of_not_ge h]
    obtain ⟨-, h1, h2, -⟩ := loc_zero hq
    rw [h1, h2]; ring

lemma term_bound (u v : ℕ → E) (x : E) (l : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    |prevGam u l x * sad ⟪v l, x⟫ * (loc1 (quarter u v l x) / 2 + loc2 (quarter u v l x) * t / 4)| ≤
      1 / 512 := by
  obtain ⟨g0, g1⟩ := prevGam_bounds u l x
  have hs := sad_abs_small ⟪v l, x⟫
  obtain ⟨-, -, l1a, l1b, l2, -⟩ := loc_bounds (quarter u v l x)
  have hb : |loc1 (quarter u v l x) / 2 + loc2 (quarter u v l x) * t / 4| ≤ 1 := by
    rw [abs_le] at l2 ⊢
    constructor <;> nlinarith
  rw [abs_mul, abs_mul, abs_of_nonneg g0]
  calc prevGam u l x * |sad ⟪v l, x⟫| * |loc1 (quarter u v l x) / 2 + loc2 (quarter u v l x) * t / 4|
      ≤ 1 * (1 / 512) * 1 := by gcongr
    _ = 1 / 512 := by ring

lemma extras_bound (fr : Frame K u v) (x : E) {n : ℕ} (hn : n ≤ K) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    |∑ l ∈ Finset.range n, prevGam u l x * sad ⟪v l, x⟫ *
      (loc1 (quarter u v l x) / 2 + loc2 (quarter u v l x) * t / 4)| ≤ 1 / 10 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n) (active u v x)]
  rw [Finset.sum_eq_zero (s := (Finset.range n).filter (fun l => ¬ active u v x l))
    (fun l hl => inactive_term u v x (Finset.mem_filter.1 hl).2 t), add_zero]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ l ∈ (Finset.range n).filter (active u v x), (1 / 512 : ℝ) :=
        Finset.sum_le_sum fun l _ => term_bound u v x l ht0 ht
    _ = ((Finset.range n).filter (active u v x)).card * (1 / 512) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 45 * (1 / 512) := by
        gcongr
        exact_mod_cast active_card fr x n hn
    _ ≤ 1 / 10 := by norm_num

lemma weight_eq (u v : ℕ → E) (l : ℕ) (x : E) :
    weight u v l x = prevGam u l x * sad ⟪v l, x⟫ *
      (loc1 (quarter u v l x) / 2 + loc2 (quarter u v l x) * 0 / 4) := by
  unfold weight; ring

lemma weight_nonneg (u v : ℕ → E) (l : ℕ) (x : E) : 0 ≤ weight u v l x := by
  unfold weight
  have g0 := (prevGam_bounds u l x).1
  have s0 := sad_nonpos ⟪v l, x⟫
  have l0 := (loc_bounds (quarter u v l x)).2.2.1
  have : 0 ≤ sad ⟪v l, x⟫ * loc1 (quarter u v l x) := mul_nonneg_of_nonpos_of_nonpos s0 l0
  have := mul_nonneg g0 this
  nlinarith

lemma kappa_bounds (fr : Frame K u v) (x : E) {n : ℕ} (hn : n ≤ K) :
    0 ≤ ∑ l ∈ Finset.range n, weight u v l x ∧ ∑ l ∈ Finset.range n, weight u v l x ≤ 1 / 10 := by
  have h0 := Finset.sum_nonneg fun l (_ : l ∈ Finset.range n) => weight_nonneg u v l x
  refine ⟨h0, ?_⟩
  have h := extras_bound fr x hn le_rfl zero_le_one
  rw [Finset.sum_congr rfl fun l _ => weight_eq u v l x]
  exact (le_abs_self _).trans h

end LongTails.Proofs.EscapeChainBounds
