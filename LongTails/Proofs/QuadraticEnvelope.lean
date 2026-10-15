import LongTails.Proofs.GdConvex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Asymptotics.Lemmas

open Set Filter InnerProductSpace Asymptotics
open scoped RealInnerProductSpace Topology

namespace LongTails.Proofs.QuadraticEnvelope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def cost (L : ℝ) (x : E) (z : E × ℝ) : ℝ :=
  L / 2 * ‖x - z.1‖ ^ 2 + z.2

omit [InnerProductSpace ℝ E] in
lemma cost_continuous (L : ℝ) (x : E) : Continuous (cost L x) := by
  unfold cost
  fun_prop

omit [InnerProductSpace ℝ E] in
lemma exists_minimizer (L : ℝ) (K : Set (E × ℝ)) (hK : IsCompact K)
    (hne : K.Nonempty) (x : E) : ∃ z ∈ K, ∀ w ∈ K, cost L x z ≤ cost L x w :=
  hK.exists_isMinOn hne (cost_continuous L x).continuousOn

noncomputable def minimizer (L : ℝ) (K : Set (E × ℝ)) (hK : IsCompact K)
    (hne : K.Nonempty) (x : E) : E × ℝ :=
  Classical.choose (exists_minimizer L K hK hne x)

omit [InnerProductSpace ℝ E] in
lemma minimizer_mem (L : ℝ) (K : Set (E × ℝ)) (hK : IsCompact K)
    (hne : K.Nonempty) (x : E) : minimizer L K hK hne x ∈ K :=
  (Classical.choose_spec (exists_minimizer L K hK hne x)).1

omit [InnerProductSpace ℝ E] in
lemma minimizer_le (L : ℝ) (K : Set (E × ℝ)) (hK : IsCompact K)
    (hne : K.Nonempty) (x : E) (w : E × ℝ) (hw : w ∈ K) :
    cost L x (minimizer L K hK hne x) ≤ cost L x w :=
  (Classical.choose_spec (exists_minimizer L K hK hne x)).2 w hw

lemma linear_nonneg {B C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ t * B + t ^ 2 * C) : 0 ≤ B := by
  by_contra hn
  have hB : B < 0 := lt_of_not_ge hn
  let t := min 1 (-B / (2 * (C + 1)))
  have hneg : 0 < -B := neg_pos.mpr hB
  have ht : 0 < t := lt_min (by norm_num) (div_pos hneg (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t * (2 * (C + 1)) ≤ -B := by
    exact (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hh := h t ht.le ht1
  have hb : 0 ≤ B + t * C := by
    apply (mul_nonneg_iff_of_pos_left ht).mp
    nlinarith
  nlinarith

lemma cost_mix (L : ℝ) (x : E) (a b : E × ℝ) (t : ℝ) :
    cost L x ((1 - t) • a + t • b) - cost L x a =
      t * (b.2 - a.2 - L * ⟪x - a.1, b.1 - a.1⟫) +
        t ^ 2 * (L / 2 * ‖b.1 - a.1‖ ^ 2) := by
  have he : x - ((1 - t) • a + t • b).1 = (x - a.1) - t • (b.1 - a.1) := by
    change x - ((1 - t) • a.1 + t • b.1) = _
    module
  unfold cost
  rw [he, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right]
  change L / 2 * (‖x - a.1‖ ^ 2 - 2 * (t * ⟪x - a.1, b.1 - a.1⟫) +
    t ^ 2 * ‖b.1 - a.1‖ ^ 2) + ((1 - t) * a.2 + t * b.2) -
    (L / 2 * ‖x - a.1‖ ^ 2 + a.2) = _
  ring

lemma optimality {L : ℝ} (hL : 0 ≤ L) {K : Set (E × ℝ)} (hK : Convex ℝ K)
    {x : E} {a : E × ℝ} (ha : a ∈ K)
    (hmin : ∀ w ∈ K, cost L x a ≤ cost L x w) {b : E × ℝ} (hb : b ∈ K) :
    0 ≤ b.2 - a.2 - L * ⟪x - a.1, b.1 - a.1⟫ := by
  apply linear_nonneg (C := L / 2 * ‖b.1 - a.1‖ ^ 2) (by positivity)
  intro t ht ht1
  have hm := hmin ((1 - t) • a + t • b)
    (hK ha hb (by linarith) ht (by ring))
  have he := cost_mix L x a b t
  linarith

lemma cost_difference (L : ℝ) (x y : E) (a b : E × ℝ) :
    cost L y b - cost L x a - ⟪L • (x - a.1), y - x⟫ =
      b.2 - a.2 - L * ⟪x - a.1, b.1 - a.1⟫ +
        L / 2 * ‖(y - x) - (b.1 - a.1)‖ ^ 2 := by
  have he : y - b.1 = (x - a.1) + ((y - x) - (b.1 - a.1)) := by abel
  unfold cost
  rw [he, norm_add_sq_real, inner_sub_right, real_inner_smul_left]
  ring

noncomputable def envelope (L : ℝ) (K : Set (E × ℝ)) (hK : IsCompact K)
    (hne : K.Nonempty) (x : E) : ℝ := cost L x (minimizer L K hK hne x)

noncomputable def field (L : ℝ) (K : Set (E × ℝ)) (hK : IsCompact K)
    (hne : K.Nonempty) (x : E) : E := L • (x - (minimizer L K hK hne x).1)

lemma envelope_lower {L : ℝ} (hL : 0 ≤ L) {K : Set (E × ℝ)} (hc : Convex ℝ K)
    (hK : IsCompact K) (hne : K.Nonempty) (x y : E) :
    envelope L K hK hne x + ⟪field L K hK hne x, y - x⟫ ≤ envelope L K hK hne y := by
  have ho := optimality hL hc (minimizer_mem L K hK hne x)
    (minimizer_le L K hK hne x) (minimizer_mem L K hK hne y)
  have hd := cost_difference L x y (minimizer L K hK hne x) (minimizer L K hK hne y)
  have hn : 0 ≤ L / 2 * ‖(y - x) -
      ((minimizer L K hK hne y).1 - (minimizer L K hK hne x).1)‖ ^ 2 := by positivity
  dsimp only [envelope, field]
  linarith

lemma envelope_upper (L : ℝ) (K : Set (E × ℝ)) (hK : IsCompact K)
    (hne : K.Nonempty) (x y : E) :
    envelope L K hK hne y ≤ envelope L K hK hne x +
      ⟪field L K hK hne x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  have hm := minimizer_le L K hK hne y (minimizer L K hK hne x)
    (minimizer_mem L K hK hne x)
  have hd := cost_difference L x y (minimizer L K hK hne x) (minimizer L K hK hne x)
  simp only [sub_self, inner_zero_right, mul_zero, sub_zero] at hd
  dsimp only [envelope, field]
  linarith

lemma envelope_hasGradient [CompleteSpace E] {L : ℝ} (hL : 0 ≤ L) {K : Set (E × ℝ)} (hc : Convex ℝ K)
    (hK : IsCompact K) (hne : K.Nonempty) (x : E) :
    HasGradientAt (envelope L K hK hne) (field L K hK hne x) x := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  have hb : ∀ d : E, ‖envelope L K hK hne (x + d) - envelope L K hK hne x -
      (toDual ℝ E (field L K hK hne x)) d‖ ≤ L / 2 * ‖d‖ ^ 2 := by
    intro d
    have hl := envelope_lower hL hc hK hne x (x + d)
    have hu := envelope_upper L K hK hne x (x + d)
    simp only [add_sub_cancel_left] at hl hu
    rw [toDual_apply_apply, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [mul_nonneg hL (sq_nonneg ‖d‖)]
  have hbig : (fun d : E => envelope L K hK hne (x + d) - envelope L K hK hne x -
      (toDual ℝ E (field L K hK hne x)) d) =O[𝓝 0] (fun d : E => ‖d‖ ^ 2) := by
    refine IsBigO.of_bound (L / 2) (Eventually.of_forall fun d => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hb d
  have hlit : (fun d : E => ‖d‖ ^ 2) =o[𝓝 0] (fun d : E => d) := by
    have h := (isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num)).comp_tendsto
      (tendsto_norm_zero (E := E))
    exact isLittleO_norm_right.mp h
  exact hbig.trans_isLittleO hlit

lemma residual_lipschitz {L : ℝ} (hL : 0 < L) {K : Set (E × ℝ)} (hc : Convex ℝ K)
    (hK : IsCompact K) (hne : K.Nonempty) (x y : E) :
    ‖(x - (minimizer L K hK hne x).1) - (y - (minimizer L K hK hne y).1)‖ ≤ ‖x - y‖ := by
  let a := minimizer L K hK hne x
  let b := minimizer L K hK hne y
  have h1 := optimality hL.le hc (minimizer_mem L K hK hne x)
    (minimizer_le L K hK hne x) (minimizer_mem L K hK hne y)
  have h2 := optimality hL.le hc (minimizer_mem L K hK hne y)
    (minimizer_le L K hK hne y) (minimizer_mem L K hK hne x)
  change 0 ≤ b.2 - a.2 - L * ⟪x - a.1, b.1 - a.1⟫ at h1
  change 0 ≤ a.2 - b.2 - L * ⟪y - b.1, a.1 - b.1⟫ at h2
  have hi : ⟪x - a.1, b.1 - a.1⟫ + ⟪y - b.1, a.1 - b.1⟫ =
      ‖a.1 - b.1‖ ^ 2 - ⟪x - y, a.1 - b.1⟫ := by
    rw [← neg_sub a.1 b.1, inner_neg_right,
      ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left]
    ring
  have hm : ‖a.1 - b.1‖ ^ 2 ≤ ⟪x - y, a.1 - b.1⟫ := by
    nlinarith
  have he : (x - a.1) - (y - b.1) = (x - y) - (a.1 - b.1) := by abel
  change ‖(x - a.1) - (y - b.1)‖ ≤ ‖x - y‖
  rw [he]
  have hs := norm_sub_sq_real (x - y) (a.1 - b.1)
  nlinarith [sq_nonneg ‖a.1 - b.1‖, norm_nonneg ((x - y) - (a.1 - b.1)), norm_nonneg (x - y)]

lemma field_lipschitz {L : ℝ} (hL : 0 < L) {K : Set (E × ℝ)} (hc : Convex ℝ K)
    (hK : IsCompact K) (hne : K.Nonempty) (x y : E) :
    ‖field L K hK hne x - field L K hK hne y‖ ≤ L * ‖x - y‖ := by
  unfold field
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  exact mul_le_mul_of_nonneg_left (residual_lipschitz hL hc hK hne x y) hL.le

lemma cost_minimum_of_support {L : ℝ} (hL : 0 ≤ L) {K : Set (E × ℝ)}
    (x : E) (a : E × ℝ)
    (hs : ∀ b ∈ K, 0 ≤ b.2 - a.2 - L * ⟪x - a.1, b.1 - a.1⟫) :
    ∀ b ∈ K, cost L x a ≤ cost L x b := by
  intro b hb
  have hd := cost_difference L x x a b
  simp only [sub_self, inner_zero_right, zero_sub, norm_neg, sub_zero] at hd
  have hn : 0 ≤ L / 2 * ‖b.1 - a.1‖ ^ 2 := by positivity
  linarith [hs b hb]

lemma envelope_at_minimum {L : ℝ} (hL : 0 < L) {K : Set (E × ℝ)} (hc : Convex ℝ K)
    (hK : IsCompact K) (hne : K.Nonempty) (x : E) (a : E × ℝ) (ha : a ∈ K)
    (hmin : ∀ b ∈ K, cost L x a ≤ cost L x b) :
    envelope L K hK hne x = cost L x a ∧ field L K hK hne x = L • (x - a.1) := by
  have h1 := minimizer_le L K hK hne x a ha
  have h2 := hmin _ (minimizer_mem L K hK hne x)
  have he : cost L x (minimizer L K hK hne x) = cost L x a := le_antisymm h1 h2
  refine ⟨he, ?_⟩
  have ho := optimality hL.le hc ha hmin (minimizer_mem L K hK hne x)
  have hd := cost_difference L x x a (minimizer L K hK hne x)
  simp only [sub_self, inner_zero_right, zero_sub, norm_neg, sub_zero] at hd
  have hz : ‖(minimizer L K hK hne x).1 - a.1‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖(minimizer L K hK hne x).1 - a.1‖]
  have hqa : (minimizer L K hK hne x).1 = a.1 :=
    sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  simp only [field, hqa]

lemma support_convexHull (L : ℝ) (x : E) (a : E × ℝ) {S : Set (E × ℝ)}
    (hs : ∀ b ∈ S, 0 ≤ b.2 - a.2 - L * ⟪x - a.1, b.1 - a.1⟫) :
    ∀ b ∈ convexHull ℝ S, 0 ≤ b.2 - a.2 - L * ⟪x - a.1, b.1 - a.1⟫ := by
  apply convexHull_min hs
  intro b hb c hc u v hu hv huv
  change 0 ≤ (u * b.2 + v * c.2) - a.2 - L * ⟪x - a.1, (u • b.1 + v • c.1) - a.1⟫
  have he : (u • b.1 + v • c.1) - a.1 = u • (b.1 - a.1) + v • (c.1 - a.1) := by
    calc
      _ = (u • b.1 + v • c.1) - (u + v) • a.1 := by rw [huv, one_smul]
      _ = _ := by module
  rw [he, inner_add_right, inner_smul_right, inner_smul_right]
  have h1 := mul_nonneg hu hb
  have h2 := mul_nonneg hv hc
  have h3 : u * a.2 + v * a.2 = a.2 := by
    calc
      _ = (u + v) * a.2 := by ring
      _ = a.2 := by rw [huv, one_mul]
  nlinarith

end LongTails.Proofs.QuadraticEnvelope
