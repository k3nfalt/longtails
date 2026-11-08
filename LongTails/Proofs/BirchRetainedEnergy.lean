import LongTails.Proofs.BirchNonEuclideanEnergy
import LongTails.Proofs.BirchTraceDescent

namespace LongTails.Proofs.BirchRetainedEnergy

open OracleTemplate.Rennala (Point)
open LongTails.Setups.UscgConstant (dualNorm IsBallLMO)
open OracleTemplate.NormBallLMO
open LongTails.Proofs.BirchNonEuclideanEnergy

lemma seminorm_weighted_sum_sq_mass {d : ℕ} {ι : Type*} (N : Seminorm ℝ (Point d))
    (s : Finset ι) (w : ι → ℝ) (v : ι → Point d) (hw : ∀ i ∈ s, 0 ≤ w i) :
    N (∑ i ∈ s, w i • v i) ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * N (v i) ^ 2 := by
  have hsum : N (∑ i ∈ s, w i • v i) ≤ ∑ i ∈ s, w i * N (v i) := by
    calc
      _ ≤ ∑ i ∈ s, N (w i • v i) :=
        Finset.le_sum_of_subadditive N (map_zero N).le (map_add_le_add N) _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
  have hsq := (sq_le_sq₀ (apply_nonneg N _) (Finset.sum_nonneg
    (fun i hi => mul_nonneg (hw i hi) (apply_nonneg N (v i))))).mpr hsum
  exact hsq.trans (weighted_sum_sq s w (fun i => N (v i)) hw)

lemma macro_descent {d : ℕ} {ι : Type*} {N : Seminorm ℝ (Point d)}
    {R L η H : ℝ} {f : Point d → ℝ} {lmo : Point d → Point d}
    (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0)
    (hlmo : IsBallLMO N 1 lmo) (hL : 0 ≤ L) (hη : 0 ≤ η) (hH : 0 ≤ H)
    (hstep : η * L * H ≤ 1 / 2)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, dualNorm N (gradient f x - gradient f y) ≤ L * N (x - y))
    (s : Finset ι) (w : ι → ℝ) (m : ι → Point d)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i ≤ H) (x : Point d) :
    f (x + η • ∑ i ∈ s, w i • (dualNorm N (m i) • lmo (m i))) ≤
      f x - η / 2 * (∑ i ∈ s, w i * dualNorm N (m i) ^ 2) +
        η * ∑ i ∈ s, w i * dualNorm N (m i - gradient f x) ^ 2 := by
  let v := fun i => dualNorm N (m i) • lmo (m i)
  let M := ∑ i ∈ s, w i * dualNorm N (m i) ^ 2
  let E := ∑ i ∈ s, w i * dualNorm N (m i - gradient f x) ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
  have hdir : N (∑ i ∈ s, w i • v i) ^ 2 ≤ H * M := by
    apply (seminorm_weighted_sum_sq_mass N s w v hw).trans
    apply mul_le_mul hmass _ (Finset.sum_nonneg
      (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))) hH
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hw i hi)
    exact (sq_le_sq₀ (apply_nonneg N _) (dualNorm_nonneg hR _)).mpr
      (sharp_direction_bound hR hlmo (m i))
  have hinner : inner ℝ (gradient f x) (∑ i ∈ s, w i • v i) ≤ -(3 / 4 : ℝ) * M + E := by
    simp only [inner_sum, inner_smul_right]
    calc
      _ ≤ ∑ i ∈ s, w i * (-(3 / 4 : ℝ) * dualNorm N (m i) ^ 2 +
            dualNorm N (m i - gradient f x) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (sharp_pair_descent hR hdef hlmo _ _) (hw i hi)
      _ = _ := by
        simp [M, E, Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_left_comm]
  have hd := descent hR hdef hgrad hlip x (x + η • ∑ i ∈ s, w i • v i)
  rw [add_sub_cancel_left, inner_smul_right, map_smul_eq_mul,
    Real.norm_eq_abs, abs_of_nonneg hη] at hd
  have hlin := mul_le_mul_of_nonneg_left hinner hη
  have hquad := mul_le_mul_of_nonneg_left hdir (mul_nonneg (div_nonneg hL (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg η))
  have hsmall := mul_le_mul_of_nonneg_left hstep (mul_nonneg hη hM)
  change f (x + η • ∑ i ∈ s, w i • v i) ≤ f x - η / 2 * M + η * E
  nlinarith

lemma partition_owner_sum {ι : Type*} (s : Finset ι) (owner : ι → ℕ) (w : ι → ℝ)
    (h : ℕ → ℝ) (K : ℕ) (howner : ∀ e ∈ s, owner e < K)
    (hmass : ∀ k < K, ∑ e ∈ s.filter (fun e => owner e = k), w e = h k)
    (v : ℕ → ℝ) :
    (∑ e ∈ s, w e * v (owner e)) = ∑ k ∈ Finset.range K, h k * v k := by
  classical
  rw [← partition_sum s owner K howner]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = ∑ e ∈ s.filter (fun e => owner e = k), w e * v k := by
      apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
    _ = h k * v k := by rw [← Finset.sum_mul, hmass k (Finset.mem_range.mp hk)]

lemma trajectory_energy {d : ℕ} {ι τ : Type*} {N : Seminorm ℝ (Point d)}
    {R L η D Δ H : ℝ} {f : Point d → ℝ} {lmo : Point d → Point d}
    (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0)
    (hlmo : IsBallLMO N 1 lmo) (hL : 0 ≤ L) (hη : 0 < η) (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hstep : η * L * H ≤ 1 / 2) (hsmall : η * L * D ≤ 1 / 4)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, dualNorm N (gradient f x - gradient f y) ≤ L * N (x - y))
    (s : Finset ι) (q : Finset τ) (K : ℕ) (owner : ι → ℕ) (w : ι → ℝ) (h : ℕ → ℝ)
    (b : ι → τ → ℝ) (C : ι → ι → ℝ) (reply : τ → Point d)
    (z : τ → Point d) (x : ℕ → Point d) (m : ι → Point d)
    (hw : ∀ e ∈ s, 0 ≤ w e) (howner : ∀ e ∈ s, owner e < K)
    (hpartition : ∀ k < K, ∑ e ∈ s.filter (fun e => owner e = k), w e = h k)
    (hupper : ∀ k < K, h k ≤ H)
    (hchain : ∀ k < K, x (k + 1) = x k +
      η • ∑ e ∈ s.filter (fun e => owner e = k), w e • (dualNorm N (m e) • lmo (m e)))
    (hgap : f (x 0) - f (x K) ≤ Δ)
    (hm : ∀ e ∈ s, m e = ∑ j ∈ q, b e j • reply j)
    (hmass : ∀ e ∈ s, ∑ j ∈ q, b e j = 1)
    (hC : ∀ e ∈ s, ∀ t ∈ s, 0 ≤ C e t)
    (hdrift : ∀ e ∈ s,
      dualNorm N (∑ j ∈ q, b e j • (gradient f (z j) - gradient f (x (owner e)))) ≤
        η * L * ∑ t ∈ s, C e t * dualNorm N (m t))
    (hcolumn : ∀ t ∈ s, (∑ e ∈ s, w e * (∑ j ∈ s, C e j) * C e t) ≤ D ^ 2 * w t) :
    (∑ k ∈ Finset.range K, h k * dualNorm N (gradient f (x k)) ^ 2) ≤ 6 * Δ / η +
      16 * ∑ e ∈ s, w e * dualNorm N (∑ j ∈ q, b e j • (reply j - gradient f (z j))) ^ 2 := by
  classical
  let G := fun k => h k * dualNorm N (gradient f (x k)) ^ 2
  let M := fun e => dualNorm N (m e) ^ 2
  let E := fun e => dualNorm N (m e - gradient f (x (owner e))) ^ 2
  let V := fun e => 2 * dualNorm N (∑ j ∈ q, b e j • (reply j - gradient f (z j))) ^ 2
  let A := fun e t => 2 * (η * L) ^ 2 * (∑ j ∈ s, C e j) * C e t
  have hcoeff (e : ι) :
      w e + (1 / 6 : ℝ) * (2 * w e) = (4 / 3) * w e := by ring
  have hdescent (k : ℕ) (hk : k < K) :
      f (x (k + 1)) - f (x k) ≤ η *
        ∑ e ∈ s.filter (fun e => owner e = k), (w e * E e - (w e / 2) * M e) := by
    have hh := macro_descent hR hdef hlmo hL hη.le hH hstep hgrad hlip
      (s.filter (fun e => owner e = k)) w m
      (fun e he => hw e (Finset.mem_filter.mp he).1) ((hpartition k hk).le.trans (hupper k hk)) (x k)
    rw [← hchain k hk] at hh
    have heq : (∑ e ∈ s.filter (fun e => owner e = k),
          w e * dualNorm N (m e - gradient f (x k)) ^ 2) =
        ∑ e ∈ s.filter (fun e => owner e = k), w e * E e := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [E, (Finset.mem_filter.mp he).2]
    rw [heq] at hh
    rw [Finset.sum_sub_distrib]
    have hM : (∑ e ∈ s.filter (fun e => owner e = k), (w e / 2) * M e) =
        (1 / 2) * ∑ e ∈ s.filter (fun e => owner e = k), w e * dualNorm N (m e) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun e _ => by dsimp only [M]; ring)
    rw [hM]
    nlinarith only [hh]
  have hcompare (k : ℕ) (hk : k < K) :
      G k ≤ ∑ e ∈ s.filter (fun e => owner e = k), (2 * w e * M e + 2 * w e * E e) := by
    dsimp only [G]
    rw [← hpartition k hk, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro e he
    have hx := dualNorm_add_sq hR (m e) (gradient f (x k) - m e)
    rw [add_sub_cancel, OracleTemplate.MinimaxLmo.dualNorm_sub_comm hR] at hx
    have hh := mul_le_mul_of_nonneg_left hx (hw e (Finset.mem_filter.mp he).1)
    simp only [M, E, (Finset.mem_filter.mp he).2]
    nlinarith only [hh]
  have herror (e : ι) (he : e ∈ s) : E e ≤ (∑ t ∈ s, A e t * M t) + V e := by
    have hs := (sq_le_sq₀ (dualNorm_nonneg hR _)
      (mul_nonneg (mul_nonneg hη.le hL) (Finset.sum_nonneg
        (fun t ht => mul_nonneg (hC e he t ht) (dualNorm_nonneg hR _))))).mpr (hdrift e he)
    have hh := dualNorm_add_sq hR (∑ j ∈ q, b e j • (reply j - gradient f (z j)))
      (∑ j ∈ q, b e j • (gradient f (z j) - gradient f (x (owner e))))
    rw [← estimator_decomposition q (b e) reply (fun j => gradient f (z j))
      (gradient f (x (owner e))) (hmass e he), ← hm e he] at hh
    have ht := weighted_sum_sq s (C e) (fun t => dualNorm N (m t)) (hC e he)
    have ht' := mul_le_mul_of_nonneg_left ht (sq_nonneg (η * L))
    rw [mul_pow] at hs
    have heq : (∑ t ∈ s, A e t * M t) =
        2 * (η * L) ^ 2 * ((∑ j ∈ s, C e j) * ∑ t ∈ s, C e t * M t) := by
      rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      dsimp only [A]
      ring
    rw [heq]
    dsimp only [E, V, M]
    linarith
  have hcap (j : ι) (hj : j ∈ s) :
      (∑ e ∈ s, (w e + (1 / 6 : ℝ) * (2 * w e)) * A e j) ≤
        w j / 2 - (1 / 6 : ℝ) * (2 * w j) := by
    simp_rw [hcoeff]
    have heq : (∑ e ∈ s, (4 / 3 : ℝ) * w e * A e j) =
        (4 / 3 * (2 * (η * L) ^ 2)) * ∑ e ∈ s, w e * (∑ t ∈ s, C e t) * C e j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [A]
      ring
    rw [heq]
    have ht := mul_le_mul_of_nonneg_left (hcolumn j hj)
      (by positivity : 0 ≤ (4 / 3 * (2 * (η * L) ^ 2) : ℝ))
    have hs := (sq_le_sq₀ (mul_nonneg (mul_nonneg hη.le hL) hD)
      (show (0 : ℝ) ≤ 1 / 4 by norm_num)).mpr hsmall
    rw [mul_pow] at hs
    have hh := mul_le_mul_of_nonneg_right hs (hw j hj)
    nlinarith only [ht, hh]
  have h := LongTails.Proofs.BirchTraceDescent.convergence s K owner (fun k => f (x k)) G
    (fun _ => 0) (fun _ => 1 / 6) (fun _ => 0) M E
    (fun e => w e / 2) w (fun e => 2 * w e) (fun e => 2 * w e) V A η Δ (1 / 6) hη
    howner (fun _ _ => sq_nonneg _) (fun _ _ => by norm_num)
    (fun _ _ => by rw [zero_add])
    (fun e he => by rw [hcoeff]; exact mul_nonneg (by norm_num) (hw e he)) hcap hgap
    (fun k hk => by simpa only [zero_mul, sub_zero, zero_add] using hdescent k hk)
    hcompare herror
  simp only [hcoeff, Finset.sum_const_zero, add_zero] at h
  have heq : (∑ e ∈ s, 4 / 3 * w e * V e) = (8 / 3) *
      ∑ e ∈ s, w e * dualNorm N (∑ j ∈ q, b e j • (reply j - gradient f (z j))) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    dsimp only [V]
    ring
  rw [heq] at h
  dsimp only [G] at h
  rw [mul_div_assoc]
  linarith only [h]

end LongTails.Proofs.BirchRetainedEnergy
