import LongTails.Algorithms.BirchWindow
import LongTails.Proofs.BirchRetainedEnergy
import LongTails.Proofs.BirchNonEuclideanMoments

namespace LongTails.Proofs.BirchWindow

open Finset MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open OracleTemplate.NormBallLMO
open LongTails.Algorithms.BirchWindow
open LongTails.Setups.UscgConstant (dualNorm IsBallLMO)
open LongTails.Setups.BirchNonEuclidean (Params Objective StochasticGradient DualRegularityWitness)
open LongTails.Proofs.BirchNonEuclideanEnergy

noncomputable def row (B k j : ℕ) : ℝ :=
  if j ∈ Ico k (k + B) then 1 / (B : ℝ) else 0

noncomputable def lag (B k t : ℕ) : ℝ :=
  if t ∈ Ico (k - B) k then 1 else 0

lemma window_subset (B K k : ℕ) (hk : k < K) : Ico k (k + B) ⊆ range (calls B K) := by
  intro j hj
  have := (mem_Ico.mp hj).2
  exact mem_range.mpr (by unfold calls; omega)

lemma row_sum (B K k : ℕ) (hB : 0 < B) (hk : k < K) :
    ∑ j ∈ range (calls B K), row B k j = 1 := by
  simp only [row, ← sum_filter]
  rw [filter_mem_eq_inter, inter_eq_right.mpr (window_subset B K k hk), sum_const, Nat.card_Ico]
  simp [(Nat.cast_pos.mpr hB : (0 : ℝ) < B).ne']

lemma row_square (B K k : ℕ) (hB : 0 < B) (hk : k < K) :
    ∑ j ∈ range (calls B K), row B k j ^ 2 = 1 / (B : ℝ) := by
  have h : ∀ j, row B k j ^ 2 = (1 / (B : ℝ)) * row B k j := by
    intro j
    unfold row
    split <;> ring
  simp only [h, ← mul_sum, row_sum B K k hB hk, mul_one]

lemma sum_row_smul {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (B K k : ℕ) (hk : k < K) (v : ℕ → V) :
    (∑ j ∈ range (calls B K), row B k j • v j) =
      (1 / (B : ℝ)) • ∑ i : Fin B, v (k + i) := by
  simp only [row, ite_smul, zero_smul, ← sum_filter, filter_mem_eq_inter,
    inter_eq_right.mpr (window_subset B K k hk), ← smul_sum]
  congr 1
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Fin.sum_univ_eq_sum_range (fun i => v (k + i))]

lemma lag_row (B K k : ℕ) : (∑ t ∈ range K, lag B k t) ≤ (B : ℝ) := by
  simp only [lag, ← sum_filter, filter_mem_eq_inter, sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast (card_le_card (inter_subset_right.trans (by
    intro t ht
    exact ht) : range K ∩ Ico (k - B) k ⊆ Ico (k - B) k)).trans
    (by rw [Nat.card_Ico]; omega : (Ico (k - B) k).card ≤ B)

lemma lag_column (B K t : ℕ) : (∑ k ∈ range K, lag B k t) ≤ (B : ℝ) := by
  simp only [lag, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have hsub : (range K).filter (fun k => t ∈ Ico (k - B) k) ⊆ Ioc t (t + B) := by
    intro k hk
    obtain ⟨h₁, h₂⟩ := mem_Ico.mp (mem_filter.mp hk).2
    exact mem_Ioc.mpr ⟨h₂, by omega⟩
  exact_mod_cast (card_le_card hsub).trans (by rw [Nat.card_Ioc, Nat.add_sub_cancel_left])

lemma trajectory {d B K : ℕ} {N : Seminorm ℝ (Point d)} {L η Δ R : ℝ}
    {f : Point d → ℝ} {lmo : Point d → Point d} (hB : 0 < B)
    (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0)
    (hlmo : IsBallLMO N 1 lmo) (hL : 0 ≤ L) (hη : 0 < η)
    (hstep : η * L ≤ 1 / 2) (hsmall : η * L * B ≤ 1 / 4)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, dualNorm N (gradient f x - gradient f y) ≤ L * N (x - y))
    (x : ℕ → Point d) (g : ℕ → Point d) (hgap : f (x 0) - f (x K) ≤ Δ)
    (hchain : ∀ k < K, let m := (1 / (B : ℝ)) • ∑ i : Fin B, g (k + i)
      x (k + 1) = x k + η • (dualNorm N m • lmo m)) :
    (∑ k ∈ range K, dualNorm N (gradient f (x k)) ^ 2) ≤
      6 * Δ / η + 16 * ∑ k ∈ range K,
        dualNorm N (∑ j ∈ range (calls B K), row B k j • (g j - gradient f (x (source B j)))) ^ 2 := by
  let m := fun k => ∑ j ∈ range (calls B K), row B k j • g j
  let dir := fun k => dualNorm N (m k) • lmo (m k)
  have hdiff (t : ℕ) (ht : t < K) : x (t + 1) - x t = η • dir t := by
    have h := hchain t ht
    dsimp only at h
    rw [← sum_row_smul B K t ht g] at h
    rw [h]
    exact add_sub_cancel_left _ _
  have hnorm (k : ℕ) (hk : k < K) (j : ℕ) (hj : j ∈ Ico k (k + B)) :
      N (x (source B j) - x k) ≤ η * ∑ t ∈ range K, lag B k t * dualNorm N (m t) := by
    obtain ⟨hj₁, hj₂⟩ := mem_Ico.mp hj
    have hsk : source B j ≤ k := by unfold source; omega
    have hsub : Ico (source B j) k ⊆ Ico (k - B) k := by
      intro t ht
      obtain ⟨ht₁, ht₂⟩ := mem_Ico.mp ht
      exact mem_Ico.mpr ⟨by unfold source at ht₁; omega, ht₂⟩
    have hd : x k - x (source B j) = η • ∑ t ∈ Ico (source B j) k, dir t := by
      rw [smul_sum]
      calc
        _ = ∑ t ∈ Ico (source B j) k, (x (t + 1) - x t) := by
          rw [sum_Ico_eq_sub _ hsk, sum_range_sub, sum_range_sub]
          abel
        _ = _ := sum_congr rfl (fun t ht => hdiff t ((mem_Ico.mp ht).2.trans hk))
    rw [← neg_sub, map_neg_eq_map, hd, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hη.le]
    apply mul_le_mul_of_nonneg_left _ hη.le
    calc
      _ ≤ ∑ t ∈ Ico (source B j) k, N (dir t) :=
        le_sum_of_subadditive N (map_zero N).le (map_add_le_add N) _ _
      _ ≤ ∑ t ∈ Ico (source B j) k, dualNorm N (m t) :=
        sum_le_sum (fun _ _ => sharp_direction_bound hR hlmo _)
      _ ≤ ∑ t ∈ Ico (k - B) k, dualNorm N (m t) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => dualNorm_nonneg hR _)
      _ = _ := by
        have hsub' : Ico (k - B) k ⊆ range K := fun t ht =>
          mem_range.mpr ((mem_Ico.mp ht).2.trans hk)
        simp only [lag, ite_mul, one_mul, zero_mul, ← sum_filter, filter_mem_eq_inter,
          inter_eq_right.mpr hsub']
  have hdrift (k : ℕ) (hk : k < K) :
      dualNorm N (∑ j ∈ range (calls B K), row B k j •
        (gradient f (x (source B j)) - gradient f (x k))) ≤
        η * L * ∑ t ∈ range K, lag B k t * dualNorm N (m t) := by
    have hb (j : ℕ) : 0 ≤ row B k j := by unfold row; split <;> positivity
    calc
      _ ≤ ∑ j ∈ range (calls B K), row B k j *
          dualNorm N (gradient f (x (source B j)) - gradient f (x k)) :=
        (dualNorm_sum_le hR _ _).trans (sum_le_sum (fun j _ => by
          simpa only [abs_of_nonneg (hb j)] using
            dualNorm_smul_le hR (row B k j) (gradient f (x (source B j)) - gradient f (x k))))
      _ ≤ ∑ j ∈ range (calls B K), row B k j *
          (η * L * ∑ t ∈ range K, lag B k t * dualNorm N (m t)) := by
        apply sum_le_sum
        intro j _
        by_cases hj : j ∈ Ico k (k + B)
        · exact mul_le_mul_of_nonneg_left ((hlip _ _).trans (by
            rw [mul_comm η L, mul_assoc]
            exact mul_le_mul_of_nonneg_left (hnorm k hk j hj) hL)) (hb j)
        · simp [row, hj]
      _ = _ := by rw [← sum_mul, row_sum B K k hB hk, one_mul]
  have hcolumn (t : ℕ) :
      (∑ k ∈ range K, (1 : ℝ) * (∑ j ∈ range K, lag B k j) * lag B k t) ≤ (B : ℝ) ^ 2 * 1 := by
    calc
      _ ≤ ∑ k ∈ range K, (B : ℝ) * lag B k t := by
        apply sum_le_sum
        intro k _
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right (lag_row B K k) (by unfold lag; split <;> norm_num)
      _ ≤ _ := by
        rw [← mul_sum, mul_one, pow_two]
        exact mul_le_mul_of_nonneg_left (lag_column B K t) (Nat.cast_nonneg _)
  have hfilter (k : ℕ) (hk : k < K) : (range K).filter (fun e => id e = k) = {k} := by
    ext t
    simp only [mem_filter, mem_range, id_eq, mem_singleton]
    exact ⟨And.right, fun h => ⟨h ▸ hk, h⟩⟩
  have h := LongTails.Proofs.BirchRetainedEnergy.trajectory_energy (D := (B : ℝ))
    (H := 1) hR hdef hlmo hL hη (Nat.cast_nonneg _) zero_le_one
    (by simpa only [mul_one] using hstep) hsmall hgrad hlip
    (range K) (range (calls B K)) K id (fun _ => 1) (fun _ => 1)
    (row B) (lag B) g (fun j => x (source B j)) x m
    (fun _ _ => zero_le_one) (fun _ hk => mem_range.mp hk)
    (fun k hk => by simp only [hfilter k hk, sum_singleton]) (fun _ _ => le_rfl)
    (fun k hk => by
      rw [hfilter k hk, sum_singleton, one_smul]
      exact sub_eq_iff_eq_add'.mp (hdiff k hk))
    hgap (fun _ _ => rfl) (fun k hk => row_sum B K k hB (mem_range.mp hk))
    (fun k _ t _ => by unfold lag; split <;> norm_num)
    (fun k hk => hdrift k (mem_range.mp hk)) (fun t _ => hcolumn t)
  simpa only [one_mul] using h

end LongTails.Proofs.BirchWindow
