import LongTails.Proofs.AbcChainProfiles
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Asymptotics.Lemmas

open scoped Topology RealInnerProductSpace

namespace LongTails.Proofs.NcPlCalc

open LongTails.Proofs.AbcChainProfiles

lemma model_of_lipschitz {g g' : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hl : ∀ a b, |g' a - g' b| ≤ K * |a - b|) (a b : ℝ) :
    |g b - g a - g' a * (b - a)| ≤ K * (b - a) ^ 2 := by
  have hd : ∀ y ∈ Set.uIcc a b,
      HasDerivWithinAt (fun y => g y - g' a * y) (g' y - g' a) (Set.uIcc a b) y := by
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => g' a * y) (g' a * 1) y := (hasDerivAt_id' y).const_mul (g' a)
    have h2 := (hg y).sub h1
    rw [mul_one] at h2
    exact h2.hasDerivWithinAt
  have hb : ∀ y ∈ Set.uIcc a b, ‖g' y - g' a‖ ≤ K * |b - a| := by
    intro y hy
    rw [Real.norm_eq_abs]
    refine (hl y a).trans (mul_le_mul_of_nonneg_left ?_ hK)
    exact Set.abs_sub_left_of_mem_uIcc hy
  have h := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have e : g b - g' a * b - (g a - g' a * a) = g b - g a - g' a * (b - a) := by ring
  rw [e] at h
  have e2 : K * |b - a| * |b - a| = K * (b - a) ^ 2 := by
    rw [mul_assoc, ← sq, sq_abs]
  rw [e2] at h
  exact h

lemma triple_model {x x' dx δa y y' dy δb z z' dz δc MA MB MC LA LB LC KA KB KC : ℝ}
    (hMA : |x| ≤ MA) (hMB : |y| ≤ MB) (hMC : |z| ≤ MC) (hMC' : |z'| ≤ MC)
    (hLA : |x' - x| ≤ LA * |δa|) (hLB : |y' - y| ≤ LB * |δb|) (hLC : |z' - z| ≤ LC * |δc|)
    (hKA : |x' - x - dx * δa| ≤ KA * δa ^ 2) (hKB : |y' - y - dy * δb| ≤ KB * δb ^ 2)
    (hKC : |z' - z - dz * δc| ≤ KC * δc ^ 2) (hLA0 : 0 ≤ LA) (hLB0 : 0 ≤ LB) (hLC0 : 0 ≤ LC)
    (hKA1 : 0 ≤ KA) (hKB1 : 0 ≤ KB) (hKC1 : 0 ≤ KC) :
    |x' * y' * z' - x * y * z - (dx * y * z * δa + x * dy * z * δb + x * y * dz * δc)| ≤
      (KA * MB * MC + MA * KB * MC + MA * MB * KC + 3 * LA * LB * MC + LA * LC * MB +
        MA * LB * LC) * (δa ^ 2 + δb ^ 2 + δc ^ 2) := by
  have hMA0 : 0 ≤ MA := le_trans (abs_nonneg _) hMA
  have hMB0 : 0 ≤ MB := le_trans (abs_nonneg _) hMB
  have hMC0 : 0 ≤ MC := le_trans (abs_nonneg _) hMC
  have hKA0 : 0 ≤ KA * δa ^ 2 := le_trans (abs_nonneg _) hKA
  have hKB0 : 0 ≤ KB * δb ^ 2 := le_trans (abs_nonneg _) hKB
  have hKC0 : 0 ≤ KC * δc ^ 2 := le_trans (abs_nonneg _) hKC
  have e : x' * y' * z' - x * y * z - (dx * y * z * δa + x * dy * z * δb + x * y * dz * δc) =
      (x' - x - dx * δa) * (y * z) + x * (y' - y - dy * δb) * z + x * y * (z' - z - dz * δc) +
        ((x' - x) * (y' - y) * z' + (x' - x) * y * (z' - z) + x * (y' - y) * (z' - z)) := by ring
  rw [e]
  have t1 : |(x' - x - dx * δa) * (y * z)| ≤ KA * δa ^ 2 * (MB * MC) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul hKA (mul_le_mul hMB hMC (abs_nonneg _) hMB0) (by positivity) hKA0
  have t2 : |x * (y' - y - dy * δb) * z| ≤ MA * (KB * δb ^ 2) * MC := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul hMA hKB (abs_nonneg _) hMA0) hMC (abs_nonneg _)
      (mul_nonneg hMA0 hKB0)
  have t3 : |x * y * (z' - z - dz * δc)| ≤ MA * MB * (KC * δc ^ 2) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul hMA hMB (abs_nonneg _) hMA0) hKC (abs_nonneg _)
      (mul_nonneg hMA0 hMB0)
  have ha := abs_nonneg δa
  have hb := abs_nonneg δb
  have hc := abs_nonneg δc
  have hab : |δa| * |δb| ≤ δa ^ 2 + δb ^ 2 := by
    nlinarith [sq_nonneg (|δa| - |δb|), sq_abs δa, sq_abs δb]
  have hac : |δa| * |δc| ≤ δa ^ 2 + δc ^ 2 := by
    nlinarith [sq_nonneg (|δa| - |δc|), sq_abs δa, sq_abs δc]
  have hbc : |δb| * |δc| ≤ δb ^ 2 + δc ^ 2 := by
    nlinarith [sq_nonneg (|δb| - |δc|), sq_abs δb, sq_abs δc]
  have t4 : |(x' - x) * (y' - y) * z'| ≤ LA * |δa| * (LB * |δb|) * MC := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul hLA hLB (abs_nonneg _) (by positivity)) hMC' (abs_nonneg _)
      (by positivity)
  have t5 : |(x' - x) * y * (z' - z)| ≤ LA * |δa| * MB * (LC * |δc|) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul hLA hMB (abs_nonneg _) (by positivity)) hLC (abs_nonneg _)
      (by positivity)
  have t6 : |x * (y' - y) * (z' - z)| ≤ MA * (LB * |δb|) * (LC * |δc|) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul hMA hLB (abs_nonneg _) hMA0) hLC (abs_nonneg _) (by positivity)
  have s1 := abs_add_le ((x' - x - dx * δa) * (y * z) + x * (y' - y - dy * δb) * z +
    x * y * (z' - z - dz * δc))
    ((x' - x) * (y' - y) * z' + (x' - x) * y * (z' - z) + x * (y' - y) * (z' - z))
  have s2 := abs_add_three ((x' - x - dx * δa) * (y * z)) (x * (y' - y - dy * δb) * z)
    (x * y * (z' - z - dz * δc))
  have s3 := abs_add_three ((x' - x) * (y' - y) * z') ((x' - x) * y * (z' - z))
    (x * (y' - y) * (z' - z))
  have q4 : LA * |δa| * (LB * |δb|) * MC ≤ LA * LB * MC * (δa ^ 2 + δb ^ 2) := by
    have : LA * |δa| * (LB * |δb|) * MC = LA * LB * MC * (|δa| * |δb|) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hab (by positivity)
  have q5 : LA * |δa| * MB * (LC * |δc|) ≤ LA * LC * MB * (δa ^ 2 + δc ^ 2) := by
    have : LA * |δa| * MB * (LC * |δc|) = LA * LC * MB * (|δa| * |δc|) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hac (by positivity)
  have q6 : MA * (LB * |δb|) * (LC * |δc|) ≤ MA * LB * LC * (δb ^ 2 + δc ^ 2) := by
    have : MA * (LB * |δb|) * (LC * |δc|) = MA * LB * LC * (|δb| * |δc|) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hbc (by positivity)
  have ha2 := sq_nonneg δa
  have hb2 := sq_nonneg δb
  have hc2 := sq_nonneg δc
  have u1 : KA * δa ^ 2 * (MB * MC) ≤ KA * MB * MC * (δa ^ 2 + δb ^ 2 + δc ^ 2) := by
    have := mul_nonneg (mul_nonneg (mul_nonneg hKA1 hMB0) hMC0) (add_nonneg hb2 hc2)
    linarith
  have u2 : MA * (KB * δb ^ 2) * MC ≤ MA * KB * MC * (δa ^ 2 + δb ^ 2 + δc ^ 2) := by
    have := mul_nonneg (mul_nonneg (mul_nonneg hMA0 hKB1) hMC0) (add_nonneg ha2 hc2)
    linarith
  have u3 : MA * MB * (KC * δc ^ 2) ≤ MA * MB * KC * (δa ^ 2 + δb ^ 2 + δc ^ 2) := by
    have := mul_nonneg (mul_nonneg (mul_nonneg hMA0 hMB0) hKC1) (add_nonneg ha2 hb2)
    linarith
  have u4 : LA * LB * MC * (δa ^ 2 + δb ^ 2) ≤ LA * LB * MC * (δa ^ 2 + δb ^ 2 + δc ^ 2) := by
    have := mul_nonneg (mul_nonneg (mul_nonneg hLA0 hLB0) hMC0) hc2
    linarith
  have u5 : LA * LC * MB * (δa ^ 2 + δc ^ 2) ≤ LA * LC * MB * (δa ^ 2 + δb ^ 2 + δc ^ 2) := by
    have := mul_nonneg (mul_nonneg (mul_nonneg hLA0 hLC0) hMB0) hb2
    linarith
  have u6 : MA * LB * LC * (δb ^ 2 + δc ^ 2) ≤ MA * LB * LC * (δa ^ 2 + δb ^ 2 + δc ^ 2) := by
    have := mul_nonneg (mul_nonneg (mul_nonneg hMA0 hLB0) hLC0) ha2
    linarith
  have u7 : 0 ≤ 2 * LA * LB * MC * (δa ^ 2 + δb ^ 2 + δc ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hLA0) hLB0) hMC0)
      (add_nonneg (add_nonneg ha2 hb2) hc2)
  have expand : (KA * MB * MC + MA * KB * MC + MA * MB * KC + 3 * LA * LB * MC + LA * LC * MB +
      MA * LB * LC) * (δa ^ 2 + δb ^ 2 + δc ^ 2) =
      KA * MB * MC * (δa ^ 2 + δb ^ 2 + δc ^ 2) + MA * KB * MC * (δa ^ 2 + δb ^ 2 + δc ^ 2) +
      MA * MB * KC * (δa ^ 2 + δb ^ 2 + δc ^ 2) + LA * LB * MC * (δa ^ 2 + δb ^ 2 + δc ^ 2) +
      2 * LA * LB * MC * (δa ^ 2 + δb ^ 2 + δc ^ 2) +
      LA * LC * MB * (δa ^ 2 + δb ^ 2 + δc ^ 2) + MA * LB * LC * (δa ^ 2 + δb ^ 2 + δc ^ 2) := by
    ring
  rw [expand]
  linarith

lemma pair_model {y y' dy δb z z' dz δc MB MC LB LC KB KC : ℝ}
    (hMB : |y| ≤ MB) (hMC : |z| ≤ MC)
    (hLB : |y' - y| ≤ LB * |δb|) (hLC : |z' - z| ≤ LC * |δc|)
    (hKB : |y' - y - dy * δb| ≤ KB * δb ^ 2) (hKC : |z' - z - dz * δc| ≤ KC * δc ^ 2)
    (hLB0 : 0 ≤ LB) (hLC0 : 0 ≤ LC) (hKB1 : 0 ≤ KB) (hKC1 : 0 ≤ KC) :
    |y' * z' - y * z - (dy * z * δb + y * dz * δc)| ≤
      (KB * MC + MB * KC + LB * LC) * (δb ^ 2 + δc ^ 2) := by
  have hMB0 : 0 ≤ MB := le_trans (abs_nonneg _) hMB
  have hMC0 : 0 ≤ MC := le_trans (abs_nonneg _) hMC
  have e : y' * z' - y * z - (dy * z * δb + y * dz * δc) =
      (y' - y - dy * δb) * z + y * (z' - z - dz * δc) + (y' - y) * (z' - z) := by ring
  rw [e]
  have t1 : |(y' - y - dy * δb) * z| ≤ KB * δb ^ 2 * MC := by
    rw [abs_mul]
    exact mul_le_mul hKB hMC (abs_nonneg _) (by positivity)
  have t2 : |y * (z' - z - dz * δc)| ≤ MB * (KC * δc ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul hMB hKC (abs_nonneg _) hMB0
  have t3 : |(y' - y) * (z' - z)| ≤ LB * |δb| * (LC * |δc|) := by
    rw [abs_mul]
    exact mul_le_mul hLB hLC (abs_nonneg _) (by positivity)
  have hbc : |δb| * |δc| ≤ δb ^ 2 + δc ^ 2 := by
    nlinarith [sq_nonneg (|δb| - |δc|), sq_abs δb, sq_abs δc, abs_nonneg δb, abs_nonneg δc]
  have q3 : LB * |δb| * (LC * |δc|) ≤ LB * LC * (δb ^ 2 + δc ^ 2) := by
    have : LB * |δb| * (LC * |δc|) = LB * LC * (|δb| * |δc|) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hbc (by positivity)
  have hb2 := sq_nonneg δb
  have hc2 := sq_nonneg δc
  have u1 : KB * δb ^ 2 * MC ≤ KB * MC * (δb ^ 2 + δc ^ 2) := by
    have := mul_nonneg (mul_nonneg hKB1 hMC0) hc2
    linarith
  have u2 : MB * (KC * δc ^ 2) ≤ MB * KC * (δb ^ 2 + δc ^ 2) := by
    have := mul_nonneg (mul_nonneg hMB0 hKC1) hb2
    linarith
  have s1 := abs_add_three ((y' - y - dy * δb) * z) (y * (z' - z - dz * δc)) ((y' - y) * (z' - z))
  have expand : (KB * MC + MB * KC + LB * LC) * (δb ^ 2 + δc ^ 2) =
      KB * MC * (δb ^ 2 + δc ^ 2) + MB * KC * (δb ^ 2 + δc ^ 2) + LB * LC * (δb ^ 2 + δc ^ 2) := by
    ring
  rw [expand]
  linarith

lemma scaled_model {g g' : ℝ → ℝ} {K r : ℝ} (hK : 0 ≤ K) (hr : 0 < r)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hl : ∀ a b, |g' a - g' b| ≤ K * |a - b|) (a b : ℝ) :
    |g (b / r) - g (a / r) - g' (a / r) / r * (b - a)| ≤ K / r ^ 2 * (b - a) ^ 2 := by
  have h := model_of_lipschitz hK hg hl (a / r) (b / r)
  have e1 : g' (a / r) * (b / r - a / r) = g' (a / r) / r * (b - a) := by field_simp
  have e2 : K * (b / r - a / r) ^ 2 = K / r ^ 2 * (b - a) ^ 2 := by field_simp
  rw [e1, e2] at h
  exact h

lemma prod3_lip {a a' b b' c c' Ma Mb Mc : ℝ} (ha : |a| ≤ Ma) (hb : |b| ≤ Mb)
    (hb' : |b'| ≤ Mb) (hc' : |c'| ≤ Mc) :
    |a' * b' * c' - a * b * c| ≤ |a' - a| * Mb * Mc + Ma * |b' - b| * Mc + Ma * Mb * |c' - c| := by
  have hMa : 0 ≤ Ma := le_trans (abs_nonneg _) ha
  have hMb : 0 ≤ Mb := le_trans (abs_nonneg _) hb
  have e : a' * b' * c' - a * b * c = (a' - a) * b' * c' + a * (b' - b) * c' + a * b * (c' - c) := by
    ring
  rw [e]
  have t1 : |(a' - a) * b' * c'| ≤ |a' - a| * Mb * Mc := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hb' (abs_nonneg _)) hc' (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) hMb)
  have t2 : |a * (b' - b) * c'| ≤ Ma * |b' - b| * Mc := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_right ha (abs_nonneg _)) hc' (abs_nonneg _)
      (mul_nonneg hMa (abs_nonneg _))
  have t3 : |a * b * (c' - c)| ≤ Ma * Mb * |c' - c| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul ha hb (abs_nonneg _) hMa) (abs_nonneg _)
  have := abs_add_three ((a' - a) * b' * c') (a * (b' - b) * c') (a * b * (c' - c))
  linarith

lemma div_lip {g : ℝ → ℝ} {K r : ℝ} (hr : 0 < r) (hl : ∀ a b, |g a - g b| ≤ K * |a - b|)
    (a b : ℝ) : |g (a / r) - g (b / r)| ≤ K / r * |a - b| := by
  have h := hl (a / r) (b / r)
  have e : a / r - b / r = (a - b) / r := by ring
  rw [e, abs_div, abs_of_pos hr] at h
  have e2 : K / r * |a - b| = K * (|a - b| / r) := by ring
  rw [e2]
  exact h

lemma hasGradientAt_of_model {ι : Type*} [Fintype ι] (F : EuclideanSpace ℝ ι → ℝ)
    (g : EuclideanSpace ℝ ι → ι → ℝ) (K : ℝ)
    (h : ∀ a b : EuclideanSpace ℝ ι,
      |F b - F a - ∑ k, g a k * (b k - a k)| ≤ K * ∑ k, (b k - a k) ^ 2)
    (a : EuclideanSpace ℝ ι) : HasGradientAt F (WithLp.toLp 2 (g a)) a := by
  rw [hasGradientAt_iff_isLittleO]
  have hb : (fun b => F b - F a - ⟪(WithLp.toLp 2 (g a) : EuclideanSpace ℝ ι), b - a⟫) =O[𝓝 a]
      (fun b => ‖b - a‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound K
    filter_upwards [] with b
    have hm := h a b
    have hin : ⟪(WithLp.toLp 2 (g a) : EuclideanSpace ℝ ι), b - a⟫ = ∑ k, g a k * (b k - a k) := by
      simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    have hn : ‖b - a‖ ^ 2 = ∑ k, (b k - a k) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp
    rw [hin, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖b - a‖), hn]
    exact hm
  exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub a (by norm_num : 1 < 2))

end LongTails.Proofs.NcPlCalc
