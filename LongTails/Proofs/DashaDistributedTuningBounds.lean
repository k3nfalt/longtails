import LongTails.Proofs.DashaDistributedLogBounds

namespace LongTails.Proofs.DashaDistributedTuningBounds

open DashaDistributedLogBounds

lemma clipped_quotient_le (A N d k : ℝ) (hA : 0 ≤ A) (hN : 0 < N) (hd : 0 < d)
    (hk : 0 < k) (hclip : min d (A / N) ≤ k) :
    A / k ≤ max N (A / d) := by
  by_cases h : A / N ≤ d
  · have ha : A / N ≤ k := by simpa only [min_eq_right h] using hclip
    have hb := (div_le_iff₀ hN).mp ha
    have hc : A / k ≤ N := (div_le_iff₀ hk).mpr (by nlinarith only [hb])
    exact hc.trans (le_max_left _ _)
  · have ha : d ≤ k := by simpa only [min_eq_left (le_of_not_ge h)] using hclip
    exact (div_le_div_of_nonneg_left hA hd ha).trans (le_max_right _ _)

lemma balanced_root_product (Z B L : ℝ) (hZ : 0 ≤ Z) (hB : 0 < B) (hL : 0 < L) :
    Real.sqrt (Z * B / L) * Real.sqrt (Z * L / B) = Z := by
  rw [← Real.sqrt_mul (by positivity)]
  have he : Z * B / L * (Z * L / B) = Z ^ 2 := by field_simp
  rw [he, Real.sqrt_sq hZ]

lemma scaled_root (Z B L : ℝ) (hB : 0 < B) :
    B * Real.sqrt (Z * L / B) = Real.sqrt (Z * B * L) := by
  calc
    _ = Real.sqrt (B ^ 2) * Real.sqrt (Z * L / B) := by rw [Real.sqrt_sq hB.le]
    _ = Real.sqrt (B ^ 2 * (Z * L / B)) := (Real.sqrt_mul (sq_nonneg B) _).symm
    _ = _ := by congr 1; field_simp

lemma balanced_initializer_bound (d Z B L k₀ : ℝ) (hd : 0 ≤ d) (hZ : 0 ≤ Z)
    (hB : 0 < B) (hL : 0 < L) (hk : 0 < k₀)
    (hblock : d * Real.sqrt (Z * B / L) ≤ k₀) :
    d ^ 2 * Z / k₀ ≤ d * Real.sqrt (Z * L / B) := by
  have hm := mul_le_mul_of_nonneg_left hblock (show 0 ≤ d * Real.sqrt (Z * L / B) by positivity)
  have he := balanced_root_product Z B L hZ hB hL
  apply (div_le_iff₀ hk).mpr
  nlinarith only [hm, congrArg (fun x : ℝ => d ^ 2 * x) he]

lemma log_one_add_le_two_sqrt (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ 2 * Real.sqrt x := by
  have hs := Real.sq_sqrt hx
  have hroot := Real.sqrt_nonneg x
  have hl := Real.log_le_log (show 0 < 1 + x by positivity)
    (show 1 + x ≤ (1 + Real.sqrt x) ^ 2 by nlinarith)
  rw [Real.log_pow] at hl
  norm_num at hl
  have hb := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.sqrt x by positivity)
  nlinarith

noncomputable def initialCharge (B L U Z : ℝ) : ℝ :=
  min (Real.sqrt (Z * B * L)) (min (L + Real.log (1 + Z * B)) U)

lemma initialCharge_small (B L U Z : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hLU : L ≤ U)
    (hZ : 0 ≤ Z) (hsmall : Z * B ≤ L) :
    initialCharge B L U Z = Real.sqrt (Z * B * L) := by
  have hroot : Real.sqrt (Z * B * L) ≤ L := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hL).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hsmall hL]
  have hlog : 0 ≤ Real.log (1 + Z * B) := Real.log_nonneg (by nlinarith [mul_nonneg hZ hB])
  unfold initialCharge
  apply min_eq_left
  exact le_min (by linarith) (hroot.trans hLU)

lemma initialCharge_large (B L U Z : ℝ) (hB : 0 ≤ B) (hL : 1 ≤ L) (hU : 0 ≤ U)
    (hZ : 0 ≤ Z) (hlarge : L ≤ Z * B) :
    min (L + Real.log (1 + Z * B)) U ≤ 3 * initialCharge B L U Z := by
  have hL0 : 0 ≤ L := by linarith
  have hS : 0 ≤ Z * B := mul_nonneg hZ hB
  have hrootL : L ≤ Real.sqrt (Z * B * L) := by
    apply (sq_le_sq₀ hL0 (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hlarge hL0]
  have hrootS : Real.sqrt (Z * B) ≤ Real.sqrt (Z * B * L) :=
    Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left hL hS])
  have hlog := log_one_add_le_two_sqrt (Z * B) hS
  have hm : L + Real.log (1 + Z * B) ≤ 3 * Real.sqrt (Z * B * L) := by linarith
  have hlog0 : 0 ≤ Real.log (1 + Z * B) := Real.log_nonneg (by linarith)
  have hf0 : 0 ≤ min (L + Real.log (1 + Z * B)) U := le_min (by positivity) hU
  unfold initialCharge
  by_cases h : Real.sqrt (Z * B * L) ≤ min (L + Real.log (1 + Z * B)) U
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans hm
  · rw [min_eq_right (le_of_not_ge h)]
    linarith

lemma balanced_initial_input (d Z B L k₀ : ℝ) (hd : 0 ≤ d) (hZ : 0 ≤ Z)
    (hB : 0 < B) (hL : 0 < L) (hk : 0 < k₀)
    (hblock : d * Real.sqrt (Z * B / L) ≤ k₀) :
    d ^ 2 * Real.sqrt Z / k₀ ≤ d * Real.sqrt (L / B) := by
  have he : Real.sqrt (Z * B / L) * Real.sqrt (L / B) = Real.sqrt Z := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hm := mul_le_mul_of_nonneg_left hblock (show 0 ≤ d * Real.sqrt (L / B) by positivity)
  apply (div_le_iff₀ hk).mpr
  nlinarith only [hm, congrArg (fun x : ℝ => d ^ 2 * x) he]

lemma sqrt_ratio_le_one (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (hAB : A ≤ B) :
    Real.sqrt (A / B) ≤ 1 := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
  rw [Real.sq_sqrt (by positivity)]
  norm_num
  exact (div_le_iff₀ hB).mpr (by linarith)

lemma mixed_recipe_bounds (d N X Z B Q k K : ℝ) (hd : 0 ≤ d) (hN : 1 ≤ N)
    (hX : 0 ≤ X) (hZ : 0 ≤ Z) (hB : 2 ≤ B) (hQ : 0 < Q) (hQZ : Z * B ≤ Q)
    (hk : 0 < k) (hkX : d * X / N ≤ k) (hkB : d / (N * B) ≤ k)
    (hkup : k ≤ 1 + d * X / N + d / (N * B))
    (hK : K ≤ 160 * (N + d * X / k + d * Z / (k * Q))) :
    K ≤ 480 * N ∧ k * K * B ≤ 480 * (N * B + d * X * B + d) := by
  have hN0 : 0 < N := by linarith
  have hB0 : 0 < B := by linarith
  have h1 := (div_le_iff₀ hN0).mp hkX
  have h1' : d * X / k ≤ N := (div_le_iff₀ hk).mpr (by nlinarith only [h1])
  have h2 := (div_le_iff₀ (mul_pos hN0 hB0)).mp hkB
  have h2Z := mul_le_mul_of_nonneg_left h2 hZ
  have h2Q := mul_le_mul_of_nonneg_left hQZ (show 0 ≤ N * k by positivity)
  have h2' : d * Z / (k * Q) ≤ N :=
    (div_le_iff₀ (mul_pos hk hQ)).mpr (by nlinarith only [h2Z, h2Q])
  have hK480 : K ≤ 480 * N := by linarith
  have hu := mul_le_mul_of_nonneg_right hkup (show 0 ≤ N * B by positivity)
  have he : (1 + d * X / N + d / (N * B)) * (N * B) = N * B + d * X * B + d := by
    field_simp
  rw [he] at hu
  have hm := mul_le_mul_of_nonneg_left hK480 (show 0 ≤ k * B by positivity)
  exact ⟨hK480, by nlinarith only [hu, hm]⟩

lemma small_recipe_bounds (d N X Z B L k₀ k K : ℝ)
    (hd : 1 ≤ d) (hN : 1 ≤ N) (hX : 0 ≤ X) (hXN : X ≤ N) (hZ : 0 ≤ Z)
    (hB : 2 ≤ B) (hL : 1 ≤ L) (hLB : L ≤ B) (hsmall : Z * B ≤ L)
    (hk₀ : 0 < k₀) (hk : 0 < k)
    (hinit : d * Real.sqrt (Z * B / L) ≤ k₀) (hinitup : k₀ ≤ 1 + d * Real.sqrt (Z * B / L))
    (hmain : min d ((d * X + d ^ 2 * Z / k₀) / N) ≤ k)
    (hmainup : k ≤ 1 + (d * X + d ^ 2 * Z / k₀) / N)
    (hK : K ≤ 160 * (N + (d * X + d ^ 2 * Z / k₀) / k)) :
    K ≤ 480 * N ∧ k * K * B ≤ 480 * (N * B + d * X * B + d * Real.sqrt (Z * B * L)) ∧
      k₀ * L ≤ B + d * Real.sqrt (Z * B * L) ∧ d ^ 2 * Real.sqrt Z / k₀ ≤ d := by
  have hd0 : 0 < d := by linarith
  have hN0 : 0 < N := by linarith
  have hB0 : 0 < B := by linarith
  have hL0 : 0 < L := by linarith
  have hZ1 : Z ≤ 1 := by
    have h : Z ≤ B / B := (le_div_iff₀ hB0).mpr (hsmall.trans hLB)
    simpa only [div_self hB0.ne'] using h
  have hZL : Z * L ≤ B := by
    have h := mul_le_mul_of_nonneg_right hZ1 hL0.le
    nlinarith
  have hroot := sqrt_ratio_le_one (Z * L) B (by positivity) hB0 hZL
  have hC := balanced_initializer_bound d Z B L k₀ hd0.le hZ hB0 hL0 hk₀ hinit
  have hCsmall : d ^ 2 * Z / k₀ ≤ d := by
    have hm := mul_le_mul_of_nonneg_left hroot hd0.le
    nlinarith only [hC, hm]
  let A := d * X + d ^ 2 * Z / k₀
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hAd : A / d ≤ 2 * N := by
    apply (div_le_iff₀ hd0).mpr
    have h1 := mul_le_mul_of_nonneg_left hXN hd0.le
    have h2 := mul_le_mul_of_nonneg_left hN hd0.le
    dsimp [A]
    nlinarith only [h1, h2, hCsmall]
  have hquot : A / k ≤ 2 * N :=
    (clipped_quotient_le A N d k hA0 hN0 hd0 hk hmain).trans (max_le (by linarith) hAd)
  change K ≤ 160 * (N + A / k) at hK
  have hK480 : K ≤ 480 * N := by linarith
  have hu := mul_le_mul_of_nonneg_right hmainup hN0.le
  have he : (1 + A / N) * N = N + A := by field_simp
  change k * N ≤ (1 + A / N) * N at hu
  rw [he] at hu
  have hm := mul_le_mul_of_nonneg_left hK480 hk.le
  have hmainK : k * K ≤ 480 * (N + A) := by nlinarith only [hu, hm]
  have hrootB := scaled_root Z B L hB0
  have hCmul := mul_le_mul_of_nonneg_right hC hB0.le
  have hAB : A * B ≤ d * X * B + d * Real.sqrt (Z * B * L) := by
    have he := congrArg (fun x : ℝ => d * x) hrootB
    dsimp [A]
    nlinarith only [hCmul, he]
  have hmainKB := mul_le_mul_of_nonneg_right hmainK hB0.le
  have hrootL := scaled_root Z L B hL0
  rw [show Z * L * B = Z * B * L by ring] at hrootL
  have hinitL := mul_le_mul_of_nonneg_right hinitup hL0.le
  have hinput := balanced_initial_input d Z B L k₀ hd0.le hZ hB0 hL0 hk₀ hinit
  have hratio := sqrt_ratio_le_one L B hL0.le hB0 hLB
  refine ⟨hK480, ?_, ?_, ?_⟩
  · nlinarith only [hmainKB, hAB]
  · have he := congrArg (fun x : ℝ => d * x) hrootL
    nlinarith only [hinitL, he, hLB]
  · have hm := mul_le_mul_of_nonneg_left hratio hd0.le
    nlinarith only [hinput, hm]

lemma initialCharge_high (B L U Z : ℝ) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) :
    min (Real.log (1 + Z)) U ≤ 2 * initialCharge B L U Z := by
  have hB0 : 0 ≤ B := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hBL : 1 ≤ B * L := by nlinarith [mul_le_mul hB hL (by norm_num) hB0]
  have hroot : Real.sqrt Z ≤ Real.sqrt (Z * B * L) :=
    Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left hBL hZ])
  have hlog := log_one_add_le_two_sqrt Z hZ
  have hlog0 : 0 ≤ Real.log (1 + Z) := Real.log_nonneg (by linarith)
  have hmono := Real.log_le_log (show 0 < 1 + Z by positivity)
    (show 1 + Z ≤ 1 + Z * B by nlinarith [mul_le_mul_of_nonneg_left hB hZ])
  have hmin0 : 0 ≤ min (Real.log (1 + Z)) U := le_min hlog0 hU
  have hm1 := min_le_left (Real.log (1 + Z)) U
  have hm2 := min_le_right (Real.log (1 + Z)) U
  unfold initialCharge
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  exact le_min (by linarith) (le_min (by linarith) (by linarith))

lemma main_charge_collapse (a d X : ℝ) (ha : 1 / 2 ≤ a) (hd : 0 ≤ d) (hX : 0 ≤ X) :
    1 + a + d * min X (1 + a) ≤ 3 * (1 + a + d * min X a) := by
  have hmin : min X (1 + a) ≤ 3 * min X a := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3)]
    exact le_min ((min_le_left _ _).trans (by linarith))
      ((min_le_right _ _).trans (by linarith))
  have hm := mul_le_mul_of_nonneg_left hmin hd
  nlinarith only [hm, ha]

lemma float_word_small_le (d N u : ℝ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (hu : 0 ≤ u) (hbound : u ≤ 32 * d) :
    (Nat.size (Nat.size ⌈u⌉₊) : ℝ) + 3 ≤ 16 * initialLogScale d N := by
  have hb := float_word_le d N 1 u 0 hd hN (by norm_num) hu (by simpa using hbound)
  have hL := (initialLogScale_bounds d d N 0 hd le_rfl hN (by norm_num)).1
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hb
  linarith

lemma float_word_precise_le (d N Z B u : ℝ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (hZ : 0 ≤ Z) (hB : 1 ≤ B) (hu : 0 ≤ u) (hbound : u ≤ 32 * d * Real.sqrt Z) :
    (Nat.size ⌈Z * B⌉₊ : ℝ) + Nat.size (Nat.size ⌈u⌉₊) + 3 + 2 * Real.log (1 + Z) ≤
      32 * (initialLogScale d N + Real.log (1 + Z * B)) := by
  have hb := float_word_le d N Z u (Nat.size ⌈Z * B⌉₊) hd hN hZ hu hbound
  have hs := size_ceil_le_log_one_add (Z * B) (by positivity)
  have hL := (initialLogScale_bounds d d N 0 hd le_rfl hN (by norm_num)).1
  have hlog0 : 0 ≤ Real.log (1 + Z * B) := Real.log_nonneg (by nlinarith)
  have hmono := Real.log_le_log (show 0 < 1 + Z by positivity)
    (show 1 + Z ≤ 1 + Z * B by nlinarith [mul_le_mul_of_nonneg_left hB hZ])
  linarith

end LongTails.Proofs.DashaDistributedTuningBounds
