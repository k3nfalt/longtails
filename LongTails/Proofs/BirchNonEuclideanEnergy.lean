import LongTails.Setups.BirchNonEuclidean
import LongTails.Proofs.NormBallGeometry
import LongTails.Proofs.MinimaxLmoStructure

namespace LongTails.Proofs.BirchNonEuclideanEnergy

open OracleTemplate.Rennala (Point)
open LongTails.Setups.UscgConstant (dualNorm IsBallLMO)
open OracleTemplate.NormBallLMO

lemma weighted_sum_sq {ι : Type*} (s : Finset ι) (c a : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    (∑ i ∈ s, c i * a i) ^ 2 ≤ (∑ i ∈ s, c i) * ∑ i ∈ s, c i * a i ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hc
    (fun i hi => mul_nonneg (hc i hi) (sq_nonneg (a i)))
  intro i _
  exact le_of_eq (by ring)

lemma transport_energy {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (C : ι → ι → ℝ) (a : ι → ℝ) (D : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hC : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ C i j)
    (hcolumn : ∀ j ∈ s,
      (∑ i ∈ s, w i * (∑ t ∈ s, C i t) * C i j) ≤ D ^ 2 * w j) :
    (∑ i ∈ s, w i * (∑ j ∈ s, C i j * a j) ^ 2) ≤ D ^ 2 * ∑ j ∈ s, w j * a j ^ 2 := by
  calc
    (∑ i ∈ s, w i * (∑ j ∈ s, C i j * a j) ^ 2) ≤
        ∑ i ∈ s, w i * ((∑ t ∈ s, C i t) * ∑ j ∈ s, C i j * a j ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (weighted_sum_sq s (C i) a (hC i hi)) (hw i hi)
    _ = ∑ j ∈ s, (∑ i ∈ s, w i * (∑ t ∈ s, C i t) * C i j) * a j ^ 2 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum]
      ring
    _ ≤ ∑ j ∈ s, (D ^ 2 * w j) * a j ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hcolumn j hj) (sq_nonneg (a j))
    _ = D ^ 2 * ∑ j ∈ s, w j * a j ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma close_framework_energy (M E G gap noise : ℝ)
    (hdescent : M / 2 ≤ gap + E) (herror : E ≤ 2 * noise + M / 8)
    (hgradient : G ≤ 2 * M + 2 * E) : G ≤ 6 * gap + 16 * noise := by
  linarith

lemma sharp_direction_bound {d : ℕ} {N : Seminorm ℝ (Point d)} {R : ℝ}
    {lmo : Point d → Point d} (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R)
    (hlmo : IsBallLMO N 1 lmo) (m : Point d) :
    N (dualNorm N m • lmo m) ≤ dualNorm N m := by
  have hn := dualNorm_nonneg hR m
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hn]
  simpa using mul_le_mul_of_nonneg_left (hlmo.feasible m) hn

lemma sharp_inner {d : ℕ} {N : Seminorm ℝ (Point d)} {R : ℝ}
    {lmo : Point d → Point d} (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R)
    (hlmo : IsBallLMO N 1 lmo) (m : Point d) :
    inner ℝ m (dualNorm N m • lmo m) = -(dualNorm N m) ^ 2 := by
  rw [inner_smul_right, lmo_dualNorm_eq hR (by norm_num) hlmo]
  ring

lemma sharp_pair_descent {d : ℕ} {N : Seminorm ℝ (Point d)} {R : ℝ}
    {lmo : Point d → Point d} (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R)
    (hdef : ∀ x, N x = 0 → x = 0) (hlmo : IsBallLMO N 1 lmo) (g m : Point d) :
    inner ℝ g (dualNorm N m • lmo m) ≤
      -(3 / 4 : ℝ) * dualNorm N m ^ 2 + dualNorm N (m - g) ^ 2 := by
  have h := inner_le_dualNorm_mul hR hdef (g - m) (dualNorm N m • lmo m)
  rw [OracleTemplate.MinimaxLmo.dualNorm_sub_comm hR g m] at h
  have hb := mul_le_mul_of_nonneg_left (sharp_direction_bound hR hlmo m)
    (dualNorm_nonneg hR (m - g))
  have ht := h.trans hb
  rw [inner_sub_left, sharp_inner hR hlmo m] at ht
  nlinarith [sq_nonneg (dualNorm N m / 2 - dualNorm N (m - g))]

lemma seminorm_weighted_sum_sq {d : ℕ} {ι : Type*} (N : Seminorm ℝ (Point d))
    (s : Finset ι) (w : ι → ℝ) (v : ι → Point d)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1) :
    N (∑ i ∈ s, w i • v i) ^ 2 ≤ ∑ i ∈ s, w i * N (v i) ^ 2 := by
  have hsum : N (∑ i ∈ s, w i • v i) ≤ ∑ i ∈ s, w i * N (v i) := by
    calc
      N (∑ i ∈ s, w i • v i) ≤ ∑ i ∈ s, N (w i • v i) :=
        Finset.le_sum_of_subadditive N (map_zero N).le (map_add_le_add N) _ _
      _ = ∑ i ∈ s, w i * N (v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
  have hsq := sq_le_sq₀ (apply_nonneg N (∑ i ∈ s, w i • v i)) (Finset.sum_nonneg
    (fun i hi => mul_nonneg (hw i hi) (apply_nonneg N (v i))))
  have hc := weighted_sum_sq s w (fun i => N (v i)) hw
  rw [hmass, one_mul] at hc
  exact (hsq.mpr hsum).trans hc

lemma macro_descent {d : ℕ} {ι : Type*} {N : Seminorm ℝ (Point d)}
    {R L η : ℝ} {f : Point d → ℝ} {lmo : Point d → Point d}
    (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0)
    (hlmo : IsBallLMO N 1 lmo) (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hstep : η * L ≤ 1 / 2)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, dualNorm N (gradient f x - gradient f y) ≤ L * N (x - y))
    (s : Finset ι) (w : ι → ℝ) (m : ι → Point d)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1) (x : Point d) :
    f (x + η • ∑ i ∈ s, w i • (dualNorm N (m i) • lmo (m i))) ≤
      f x - η / 2 * (∑ i ∈ s, w i * dualNorm N (m i) ^ 2) +
        η * ∑ i ∈ s, w i * dualNorm N (m i - gradient f x) ^ 2 := by
  let v := fun i => dualNorm N (m i) • lmo (m i)
  let M := ∑ i ∈ s, w i * dualNorm N (m i) ^ 2
  let E := ∑ i ∈ s, w i * dualNorm N (m i - gradient f x) ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
  have hdir : N (∑ i ∈ s, w i • v i) ^ 2 ≤ M := by
    apply (seminorm_weighted_sum_sq N s w v hw hmass).trans
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hw i hi)
    exact (sq_le_sq₀ (apply_nonneg N _) (dualNorm_nonneg hR _)).mpr
      (sharp_direction_bound hR hlmo (m i))
  have hinner : inner ℝ (gradient f x) (∑ i ∈ s, w i • v i) ≤ -(3 / 4 : ℝ) * M + E := by
    simp only [inner_sum, inner_smul_right]
    calc
      (∑ i ∈ s, w i * inner ℝ (gradient f x) (v i)) ≤
          ∑ i ∈ s, w i * (-(3 / 4 : ℝ) * dualNorm N (m i) ^ 2 +
            dualNorm N (m i - gradient f x) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (sharp_pair_descent hR hdef hlmo _ _) (hw i hi)
      _ = -(3 / 4 : ℝ) * M + E := by
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


lemma dualNorm_zero {d : ℕ} {N : Seminorm ℝ (Point d)} {R : ℝ}
    (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) : dualNorm N 0 = 0 := by
  apply le_antisymm (dualNorm_le_of (fun v _ => by simp)) (dualNorm_nonneg hR 0)

lemma dualNorm_smul_le {d : ℕ} {N : Seminorm ℝ (Point d)} {R : ℝ}
    (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (a : ℝ) (x : Point d) :
    dualNorm N (a • x) ≤ |a| * dualNorm N x := by
  apply dualNorm_le_of
  intro v hv
  have hpos := inner_le_dualNorm hR x hv
  have hneg := inner_le_dualNorm hR x (v := -v) (by simpa using hv)
  rw [inner_neg_right] at hneg
  have habs : |inner ℝ x v| ≤ dualNorm N x := abs_le.mpr ⟨by linarith, hpos⟩
  rw [inner_smul_left]
  exact (le_abs_self _).trans (by
    simpa [abs_mul] using (mul_le_mul_of_nonneg_left habs (abs_nonneg a)))

lemma dualNorm_sum_le {d : ℕ} {ι : Type*} {N : Seminorm ℝ (Point d)} {R : ℝ}
    (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (s : Finset ι) (v : ι → Point d) :
    dualNorm N (∑ i ∈ s, v i) ≤ ∑ i ∈ s, dualNorm N (v i) :=
  Finset.le_sum_of_subadditive (dualNorm N) (dualNorm_zero hR).le (dualNorm_add_le hR) s v

lemma dualNorm_add_sq {d : ℕ} {N : Seminorm ℝ (Point d)} {R : ℝ}
    (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (x y : Point d) :
    dualNorm N (x + y) ^ 2 ≤ 2 * dualNorm N x ^ 2 + 2 * dualNorm N y ^ 2 := by
  have h := (sq_le_sq₀ (dualNorm_nonneg hR (x + y))
    (add_nonneg (dualNorm_nonneg hR x) (dualNorm_nonneg hR y))).mpr
    (dualNorm_add_le hR x y)
  nlinarith [sq_nonneg (dualNorm N x - dualNorm N y)]

lemma gradient_transport {d : ℕ} {ι τ : Type*} {N : Seminorm ℝ (Point d)} {R L η : ℝ}
    {f : Point d → ℝ} (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R)
    (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hlip : ∀ x y, dualNorm N (gradient f x - gradient f y) ≤ L * N (x - y))
    (q : Finset ι) (s : Finset τ) (b : ι → ℝ) (c : ι → τ → ℝ)
    (z : ι → Point d) (x : Point d) (v : τ → Point d) (a : τ → ℝ)
    (hv : ∀ t ∈ s, N (v t) ≤ a t)
    (hz : ∀ j ∈ q, z j - x = η • ∑ t ∈ s, c j t • v t) :
    dualNorm N (∑ j ∈ q, b j • (gradient f (z j) - gradient f x)) ≤
      η * L * ∑ t ∈ s, (∑ j ∈ q, |b j| * |c j t|) * a t := by
  have hpoint (j : ι) (hj : j ∈ q) :
      N (z j - x) ≤ η * ∑ t ∈ s, |c j t| * a t := by
    rw [hz j hj, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hη]
    apply mul_le_mul_of_nonneg_left _ hη
    calc
      N (∑ t ∈ s, c j t • v t) ≤ ∑ t ∈ s, N (c j t • v t) :=
        Finset.le_sum_of_subadditive N (map_zero N).le (map_add_le_add N) s _
      _ ≤ ∑ t ∈ s, |c j t| * a t := by
        apply Finset.sum_le_sum
        intro t ht
        rw [map_smul_eq_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hv t ht) (abs_nonneg _)
  calc
    dualNorm N (∑ j ∈ q, b j • (gradient f (z j) - gradient f x)) ≤
        ∑ j ∈ q, |b j| * dualNorm N (gradient f (z j) - gradient f x) :=
      (dualNorm_sum_le hR q _).trans (Finset.sum_le_sum (fun j _ => dualNorm_smul_le hR _ _))
    _ ≤ ∑ j ∈ q, |b j| * (L * (η * ∑ t ∈ s, |c j t| * a t)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left ((hlip _ _).trans
        (mul_le_mul_of_nonneg_left (hpoint j hj) hL)) (abs_nonneg _)
    _ = η * L * ∑ t ∈ s, (∑ j ∈ q, |b j| * |c j t|) * a t := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma estimator_decomposition {d : ℕ} {ι : Type*} (q : Finset ι) (b : ι → ℝ)
    (g h : ι → Point d) (v : Point d) (hmass : ∑ j ∈ q, b j = 1) :
    (∑ j ∈ q, b j • g j) - v =
      (∑ j ∈ q, b j • (g j - h j)) + ∑ j ∈ q, b j • (h j - v) := by
  simp_rw [smul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, hmass, one_smul]
  abel

lemma estimator_energy {d : ℕ} {ι τ : Type*} {N : Seminorm ℝ (Point d)} {R η L D : ℝ}
    (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (s : Finset ι) (q : Finset τ)
    (w : ι → ℝ) (b : ι → τ → ℝ) (C : ι → ι → ℝ)
    (reply truth : τ → Point d) (target : ι → Point d) (a : ι → ℝ)
    (hw : ∀ e ∈ s, 0 ≤ w e) (hC : ∀ e ∈ s, ∀ t ∈ s, 0 ≤ C e t)
    (ha : ∀ e ∈ s, 0 ≤ a e) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hmass : ∀ e ∈ s, ∑ j ∈ q, b e j = 1)
    (hdrift : ∀ e ∈ s, dualNorm N (∑ j ∈ q, b e j • (truth j - target e)) ≤
      η * L * ∑ t ∈ s, C e t * a t)
    (hcolumn : ∀ t ∈ s, (∑ e ∈ s, w e * (∑ j ∈ s, C e j) * C e t) ≤ D ^ 2 * w t) :
    (∑ e ∈ s, w e * dualNorm N ((∑ j ∈ q, b e j • reply j) - target e) ^ 2) ≤
      2 * (∑ e ∈ s, w e * dualNorm N (∑ j ∈ q, b e j • (reply j - truth j)) ^ 2) +
        2 * (η * L) ^ 2 * D ^ 2 * ∑ e ∈ s, w e * a e ^ 2 := by
  have hpoint (e : ι) (he : e ∈ s) :
      dualNorm N ((∑ j ∈ q, b e j • reply j) - target e) ^ 2 ≤
        2 * dualNorm N (∑ j ∈ q, b e j • (reply j - truth j)) ^ 2 +
          2 * (η * L) ^ 2 * (∑ t ∈ s, C e t * a t) ^ 2 := by
    rw [estimator_decomposition q (b e) reply truth (target e) (hmass e he)]
    have hs := (sq_le_sq₀ (dualNorm_nonneg hR _)
      (mul_nonneg (mul_nonneg hη hL) (Finset.sum_nonneg
        (fun t ht => mul_nonneg (hC e he t ht) (ha t ht))))).mpr (hdrift e he)
    have hh := dualNorm_add_sq hR (∑ j ∈ q, b e j • (reply j - truth j))
      (∑ j ∈ q, b e j • (truth j - target e))
    rw [mul_pow] at hs
    linarith
  have hs := Finset.sum_le_sum (fun e he => mul_le_mul_of_nonneg_left (hpoint e he) (hw e he))
  have ht := mul_le_mul_of_nonneg_left (transport_energy s w C a D hw hC hcolumn)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (η * L)))
  calc
    _ ≤ ∑ e ∈ s, w e * (2 * dualNorm N (∑ j ∈ q, b e j • (reply j - truth j)) ^ 2 +
          2 * (η * L) ^ 2 * (∑ t ∈ s, C e t * a t) ^ 2) := hs
    _ = 2 * (∑ e ∈ s, w e * dualNorm N (∑ j ∈ q, b e j • (reply j - truth j)) ^ 2) +
        2 * (η * L) ^ 2 * ∑ e ∈ s, w e * (∑ t ∈ s, C e t * a t) ^ 2 := by
      simp [Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_assoc, mul_left_comm]
    _ ≤ _ := by linarith

lemma partition_sum {ι : Type*} (s : Finset ι) (owner : ι → ℕ) (K : ℕ)
    (howner : ∀ e ∈ s, owner e < K) (v : ι → ℝ) :
    (∑ k ∈ Finset.range K, ∑ e ∈ s.filter (fun e => owner e = k), v e) = ∑ e ∈ s, v e := by
  classical
  exact Finset.sum_fiberwise_of_maps_to (fun e he => Finset.mem_range.mpr (howner e he)) v

lemma partition_owner_sum {ι : Type*} (s : Finset ι) (owner : ι → ℕ) (w : ι → ℝ) (K : ℕ)
    (howner : ∀ e ∈ s, owner e < K)
    (hmass : ∀ k < K, ∑ e ∈ s.filter (fun e => owner e = k), w e = 1) (v : ℕ → ℝ) :
    (∑ e ∈ s, w e * v (owner e)) = ∑ k ∈ Finset.range K, v k := by
  classical
  rw [← partition_sum s owner K howner]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    (∑ e ∈ s.filter (fun e => owner e = k), w e * v (owner e)) =
        ∑ e ∈ s.filter (fun e => owner e = k), w e * v k := by
      apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
    _ = v k := by rw [← Finset.sum_mul, hmass k (Finset.mem_range.mp hk), one_mul]

lemma trajectory_energy {d : ℕ} {ι τ : Type*} {N : Seminorm ℝ (Point d)}
    {R L η D Δ : ℝ} {f : Point d → ℝ} {lmo : Point d → Point d}
    (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0)
    (hlmo : IsBallLMO N 1 lmo) (hL : 0 ≤ L) (hη : 0 < η) (hD : 0 ≤ D)
    (hstep : η * L ≤ 1 / 2) (hsmall : η * L * D ≤ 1 / 4)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, dualNorm N (gradient f x - gradient f y) ≤ L * N (x - y))
    (s : Finset ι) (q : Finset τ) (K : ℕ) (owner : ι → ℕ) (w : ι → ℝ)
    (b : ι → τ → ℝ) (C : ι → ι → ℝ) (reply : τ → Point d)
    (z : τ → Point d) (x : ℕ → Point d) (m : ι → Point d)
    (hw : ∀ e ∈ s, 0 ≤ w e) (howner : ∀ e ∈ s, owner e < K)
    (hpartition : ∀ k < K, ∑ e ∈ s.filter (fun e => owner e = k), w e = 1)
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
    (∑ k ∈ Finset.range K, dualNorm N (gradient f (x k)) ^ 2) ≤ 6 * Δ / η +
      16 * ∑ e ∈ s, w e * dualNorm N (∑ j ∈ q, b e j • (reply j - gradient f (z j))) ^ 2 := by
  classical
  let M := ∑ e ∈ s, w e * dualNorm N (m e) ^ 2
  let E := ∑ e ∈ s, w e * dualNorm N (m e - gradient f (x (owner e))) ^ 2
  let G := ∑ k ∈ Finset.range K, dualNorm N (gradient f (x k)) ^ 2
  let T := ∑ e ∈ s, w e * dualNorm N (∑ j ∈ q, b e j • (reply j - gradient f (z j))) ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg (fun e he => mul_nonneg (hw e he) (sq_nonneg _))
  have hdescent : M / 2 ≤ Δ / η + E := by
    have hpoint (k : ℕ) (hk : k < K) : f (x (k + 1)) - f (x k) ≤
        -η / 2 * (∑ e ∈ s.filter (fun e => owner e = k), w e * dualNorm N (m e) ^ 2) +
          η * ∑ e ∈ s.filter (fun e => owner e = k), w e *
            dualNorm N (m e - gradient f (x (owner e))) ^ 2 := by
      have hh := macro_descent hR hdef hlmo hL hη.le hstep hgrad hlip
        (s.filter (fun e => owner e = k)) w m
        (fun e he => hw e (Finset.mem_filter.mp he).1) (hpartition k hk) (x k)
      rw [← hchain k hk] at hh
      have heq : (∑ e ∈ s.filter (fun e => owner e = k), w e *
          dualNorm N (m e - gradient f (x k)) ^ 2) =
          ∑ e ∈ s.filter (fun e => owner e = k), w e *
            dualNorm N (m e - gradient f (x (owner e))) ^ 2 := by
        apply Finset.sum_congr rfl
        intro e he
        rw [(Finset.mem_filter.mp he).2]
      rw [heq] at hh
      linarith
    have hs := Finset.sum_le_sum (fun k hk => hpoint k (Finset.mem_range.mp hk))
    rw [Finset.sum_range_sub (fun k => f (x k)), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      partition_sum s owner K howner, partition_sum s owner K howner] at hs
    have hd : Δ / η * η = Δ := div_mul_cancel₀ Δ hη.ne'
    dsimp only [M, E]
    apply (le_of_mul_le_mul_right (a := η))
    · nlinarith
    · exact hη
  have herror : E ≤ 2 * T + M / 8 := by
    have hh := estimator_energy hR s q w b C reply (fun j => gradient f (z j))
      (fun e => gradient f (x (owner e))) (fun e => dualNorm N (m e))
      hw hC (fun e _ => dualNorm_nonneg hR _) hη.le hL hmass hdrift hcolumn
    have heq : (∑ e ∈ s, w e * dualNorm N ((∑ j ∈ q, b e j • reply j) -
        gradient f (x (owner e))) ^ 2) = E := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hm e he]
    rw [heq] at hh
    have hsq := (sq_le_sq₀ (mul_nonneg (mul_nonneg hη.le hL) hD)
      (show (0 : ℝ) ≤ 1 / 4 by norm_num)).mpr hsmall
    have hmul := mul_le_mul_of_nonneg_right hsq hM
    change E ≤ 2 * T + 2 * (η * L) ^ 2 * D ^ 2 * M at hh
    nlinarith
  have hgradient : G ≤ 2 * M + 2 * E := by
    dsimp only [G]
    rw [← partition_owner_sum s owner w K howner hpartition]
    have hh (e : ι) (he : e ∈ s) : dualNorm N (gradient f (x (owner e))) ^ 2 ≤
        2 * dualNorm N (m e) ^ 2 + 2 * dualNorm N (m e - gradient f (x (owner e))) ^ 2 := by
      have hx := dualNorm_add_sq hR (m e) (gradient f (x (owner e)) - m e)
      rw [add_sub_cancel, OracleTemplate.MinimaxLmo.dualNorm_sub_comm hR] at hx
      exact hx
    calc
      _ ≤ ∑ e ∈ s, w e * (2 * dualNorm N (m e) ^ 2 +
          2 * dualNorm N (m e - gradient f (x (owner e))) ^ 2) :=
        Finset.sum_le_sum (fun e he => mul_le_mul_of_nonneg_left (hh e he) (hw e he))
      _ = 2 * M + 2 * E := by
        simp [M, E, Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_left_comm]
  have hh := close_framework_energy M E G (Δ / η) T hdescent herror hgradient
  simpa only [mul_div_assoc] using hh

end LongTails.Proofs.BirchNonEuclideanEnergy
