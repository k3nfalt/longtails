import LongTails.Proofs.GatedEscapeEnergy

namespace LongTails.Proofs.GatedEscapeTrajectory

open LongTails.Algorithms.GatedPerturbedEscape LongTails.Proofs.GatedEscapeDirection
  LongTails.Proofs.GatedEscapeEnergy
open scoped RealInnerProductSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

theorem traj_good (H : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, H v⟫ = eig i * ⟪b i, v⟫) {η r θ μ : ℝ} {T : ℕ}
    (hη : 0 < η) (hr : 0 < r) (hθ : 0 < θ) (heig : ∀ i, η * eig i ≤ 1)
    (hμθ : 8 * θ ≤ μ) (haT : (1 + η * μ) ^ T ≤ 5 / 4)
    (v fo e : ℕ → E) (hv : ∀ t, v (t + 1) = clip r (v t - η • H (v t) - η • fo t - η • e t))
    (hfoS : ∑ t ∈ Finset.range T, η * ‖fo t‖ ≤ r / 64)
    (heS : ∑ t ∈ Finset.range T, η * ‖e t‖ ≤ r / 40)
    (hv0 : ‖v 0‖ ≤ r / 32) (τ : ℕ) (hτ : τ < T)
    (hclip : r < ‖v τ - η • H (v τ) - η • fo τ - η • e τ‖)
    (hΨ : ∑ j ∈ posSet eig, eig j * ⟪b j, v T⟫ ^ 2 ≤ 4 * θ * r ^ 2) :
    r / 2 ≤ ‖v T‖ ∧ ⟪v T, H (v T)⟫ ≤ -3 * θ * ‖v T‖ ^ 2 := by
  classical
  have hμ : 0 ≤ μ := by linarith
  set J : Finset ι := Finset.univ.filter (fun j => -μ < eig j) with hJdef
  set N : Finset ι := Finset.univ.filter (fun j => eig j ≤ -μ) with hNdef
  set a : ℝ := 1 + η * μ with ha
  have ha1 : 1 ≤ a := by rw [ha]; nlinarith
  have hJ : ∀ j ∈ J, |1 - η * eig j| ≤ a := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    have h1 := heig j
    rw [abs_le]
    constructor <;> nlinarith
  have hsum_nn : ∀ t, 0 ≤ ∑ s ∈ Finset.range t, η * (‖fo s‖ + ‖e s‖) := fun t =>
    Finset.sum_nonneg fun s _ => mul_nonneg hη.le (by positivity)
  have hsumT : ∑ s ∈ Finset.range T, η * (‖fo s‖ + ‖e s‖) ≤ r / 64 + r / 40 := by
    have : ∑ s ∈ Finset.range T, η * (‖fo s‖ + ‖e s‖) =
        ∑ s ∈ Finset.range T, η * ‖fo s‖ + ∑ s ∈ Finset.range T, η * ‖e s‖ := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro s _; ring
    linarith
  have hsmall := small_modes H b eig hc J ha1 hr.le hJ v fo e hv hη.le
  have hJT : ∀ t ≤ T, pmass b J (v t) ≤ r / 10 := by
    intro t ht
    have h1 := hsmall t
    have hat : a ^ t ≤ 5 / 4 := (pow_le_pow_right₀ ha1 ht).trans haT
    have hst : ∑ s ∈ Finset.range t, η * (‖fo s‖ + ‖e s‖) ≤
        ∑ s ∈ Finset.range T, η * (‖fo s‖ + ‖e s‖) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht)
        (fun s _ _ => mul_nonneg hη.le (by positivity))
    have hin : ‖v 0‖ + ∑ s ∈ Finset.range t, η * (‖fo s‖ + ‖e s‖) ≤ r / 32 + (r / 64 + r / 40) := by
      linarith
    have hnn : 0 ≤ ‖v 0‖ + ∑ s ∈ Finset.range t, η * (‖fo s‖ + ‖e s‖) :=
      add_nonneg (norm_nonneg _) (hsum_nn t)
    calc pmass b J (v t) ≤ a ^ t * (‖v 0‖ + ∑ s ∈ Finset.range t, η * (‖fo s‖ + ‖e s‖)) := h1
      _ ≤ 5 / 4 * (r / 32 + (r / 64 + r / 40)) := by
          apply mul_le_mul hat hin hnn (by norm_num)
      _ ≤ r / 10 := by nlinarith
  have hNJ : ∀ j, j ∈ N ∨ j ∈ J := by
    intro j
    rcases le_or_gt (eig j) (-μ) with h | h
    · left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    · right; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have hN : ∀ j ∈ N, 1 ≤ |1 - η * eig j| := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    have : 1 ≤ 1 - η * eig j := by nlinarith
    exact this.trans (le_abs_self _)
  have hlarge := large_modes H b eig hc N J hNJ hr.le hN v fo e hv hη.le (R := r / 10)
    T hJT τ hclip T hτ le_rfl
  have hIco : ∑ s ∈ Finset.Ico τ T, η * (‖fo s‖ + ‖e s‖) ≤ r / 64 + r / 40 := by
    refine le_trans ?_ hsumT
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => by
      rw [Finset.mem_Ico] at hs; exact Finset.mem_range.mpr hs.2)
      (fun s _ _ => mul_nonneg hη.le (by positivity))
  have hsq : 99 / 100 * r ≤ Real.sqrt (r ^ 2 - (r / 10) ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by nlinarith)]
    nlinarith
  have hNm : 949 / 1000 * r ≤ pmass b N (v T) := by linarith
  have hnormT : ‖v T‖ ≤ r := by
    obtain ⟨m, hm⟩ : ∃ m, T = m + 1 := ⟨T - 1, by omega⟩
    rw [hm, hv]
    exact clip_norm_le _ _ hr.le
  have hge : pmass b N (v T) ≤ ‖v T‖ := pmass_le_norm _ _ _
  refine ⟨by linarith, ?_⟩
  have hdisj : Disjoint N (posSet eig) := by
    rw [Finset.disjoint_left]
    intro j hjN hjP
    have h1 := (Finset.mem_filter.mp hjN).2
    have h2 := (Finset.mem_filter.mp hjP).2
    linarith
  have hsplit := rayleigh_split H b eig hc N (posSet eig)
    (fun j hj => (Finset.mem_filter.mp hj).2)
    (fun j hjN hjP => by
      have h1 : ¬ eig j ≤ -μ := fun h => hjN (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have h2 : ¬ 0 < eig j := fun h => hjP (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      linarith)
    hdisj (v T)
  have hNsq : (949 / 1000 * r) ^ 2 ≤ pmass b N (v T) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hNm 2
  have hvT2 : ‖v T‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnormT 2
  have k1 := mul_le_mul_of_nonneg_right hμθ (sq_nonneg (pmass b N (v T)))
  have k2 := mul_le_mul_of_nonneg_left hNsq (by linarith : (0 : ℝ) ≤ 8 * θ)
  have k3 := mul_le_mul_of_nonneg_left hvT2 hθ.le
  nlinarith

end LongTails.Proofs.GatedEscapeTrajectory
