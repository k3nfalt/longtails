import LongTails.Algorithms.Svrg
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import LongTails.Proofs.GdConvex
import LongTails.Setups.FiniteSumSmoothAndConvex
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.Order.BigOperators.Expect

open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.FiniteSum

open LongTails.Setups.FiniteSumSmoothAndConvex

open MeasureTheory

lemma uniform_integral {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (f : Ω → ℝ) :
    (∫ ω, f ω ∂(PMF.uniformOfFintype Ω).toMeasure) = 𝔼 ω, f ω := by
  simp [PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
    Fintype.expect_eq_sum_div_card, div_eq_mul_inv, Finset.sum_mul, mul_comm]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gradient_difference_bound {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖g x - g y‖ ^ 2 ≤ 2 * L * (f x - f y - ⟪g y, x - y⟫) := by
  let d := g x - g y
  let z := x - (1 / L) • d
  have hu := Gradient.smooth_upper_bound hg hlip x z
  have hl := Gradient.convex_support hc hg y z
  have hzx : z - x = -(1 / L) • d := by dsimp [z]; module
  have hzy : z - y = (x - y) - (1 / L) • d := by dsimp [z]; module
  rw [hzx] at hu
  rw [hzy, inner_sub_right, inner_smul_right] at hl
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (one_div_pos.mpr hL), mul_pow] at hu
  have hd : ⟪g x, d⟫ - ⟪g y, d⟫ = ‖d‖ ^ 2 := by
    rw [← inner_sub_left]
    exact real_inner_self_eq_norm_sq d
  have hL0 := hL.ne'
  field_simp at hu hl
  dsimp only [d] at hd ⊢
  nlinarith

lemma objective_gradient {n : ℕ} {f : Fin n → E → ℝ} {oracle : Fin n × E → E}
    (hg : ∀ i x, HasGradientAt (f i) (oracle (i, x)) x) (x : E) :
    HasGradientAt (objective f) (fullGradient oracle x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (HasFDerivAt.sum (u := Finset.univ) (fun i _ => (hg i x).hasFDerivAt)).const_mul (n : ℝ)⁻¹
  simp only [Finset.sum_apply] at h
  simp only [fullGradient, map_sum, map_smul]
  exact h

lemma fullGradient_minimizer {n : ℕ} {f : Fin n → E → ℝ} {oracle : Fin n × E → E}
    (hg : ∀ i x, HasGradientAt (f i) (oracle (i, x)) x) {xstar : E}
    (hmin : IsMinOn (objective f) univ xstar) : fullGradient oracle xstar = 0 := by
  apply (toDual ℝ E).injective
  simpa using (hmin.isLocalMin (by simp)).hasFDerivAt_eq_zero
    (objective_gradient hg xstar).hasFDerivAt

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma objective_eq_expect {n : ℕ} (f : Fin n → E → ℝ) (x : E) :
    objective f x = 𝔼 i, f i x := by
  simp [objective, Fintype.expect_eq_sum_div_card, div_eq_mul_inv, mul_comm]

omit [CompleteSpace E] in
lemma expect_inner_left {n : ℕ} (v : Fin n → E) (x : E) :
    (𝔼 i, ⟪v i, x⟫) = ⟪(n : ℝ)⁻¹ • ∑ i, v i, x⟫ := by
  simp [Fintype.expect_eq_sum_div_card, inner_smul_left, sum_inner, div_eq_mul_inv, mul_comm]

omit [CompleteSpace E] in
lemma estimator_unbiased {n : ℕ} [NeZero n] (oracle : Fin n × E → E) (z x : E) :
    (n : ℝ)⁻¹ • ∑ i, estimator oracle z x i = fullGradient oracle x := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp [estimator, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn, fullGradient]

lemma component_second_moment {n : ℕ}
    {f : Fin n → E → ℝ} {oracle : Fin n × E → E} {L : ℝ}
    (hL : 0 < L) (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (oracle (i, x)) x)
    (hlip : ∀ i x y, ‖oracle (i, x) - oracle (i, y)‖ ≤ L * ‖x - y‖)
    {xstar : E} (hmin : IsMinOn (objective f) univ xstar) (x : E) :
    (𝔼 i, ‖oracle (i, x) - oracle (i, xstar)‖ ^ 2) ≤
      2 * L * (objective f x - objective f xstar) := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun i _ => gradient_difference_bound hL (hc i) (hg i) (hlip i) x xstar)
  have hz := fullGradient_minimizer hg hmin
  unfold fullGradient at hz
  simpa only [← Finset.mul_expect, Finset.expect_sub_distrib, expect_inner_left,
    ← objective_eq_expect, hz, inner_zero_left, sub_zero] using h

omit [CompleteSpace E] in
lemma centered_second_moment {n : ℕ} [NeZero n] (v : Fin n → E) :
    (𝔼 i, ‖v i - (n : ℝ)⁻¹ • ∑ j, v j‖ ^ 2) ≤ (𝔼 i, ‖v i‖ ^ 2) := by
  simp only [norm_sub_sq_real, Finset.expect_add_distrib, Finset.expect_sub_distrib,
    ← Finset.mul_expect, expect_inner_left, real_inner_self_eq_norm_sq, Fintype.expect_const]
  nlinarith [sq_nonneg ‖(n : ℝ)⁻¹ • ∑ j, v j‖]

omit [CompleteSpace E] in
lemma norm_sub_sq_le (a b : E) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := sq_nonneg ‖a + b‖
  rw [norm_add_sq_real] at h
  rw [norm_sub_sq_real]
  nlinarith

lemma estimator_second_moment {n : ℕ} [NeZero n]
    {f : Fin n → E → ℝ} {oracle : Fin n × E → E} {L : ℝ}
    (hL : 0 < L) (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (oracle (i, x)) x)
    (hlip : ∀ i x y, ‖oracle (i, x) - oracle (i, y)‖ ≤ L * ‖x - y‖)
    {xstar : E} (hmin : IsMinOn (objective f) univ xstar) (z x : E) :
    (𝔼 i, ‖estimator oracle z x i‖ ^ 2) ≤
      4 * L * ((objective f x - objective f xstar) + (objective f z - objective f xstar)) := by
  let a := fun i => oracle (i, x) - oracle (i, xstar)
  let b := fun i => oracle (i, z) - oracle (i, xstar)
  have hb : (n : ℝ)⁻¹ • ∑ i, b i = fullGradient oracle z := by
    simp only [b, Finset.sum_sub_distrib, smul_sub]
    change fullGradient oracle z - fullGradient oracle xstar = fullGradient oracle z
    rw [fullGradient_minimizer hg hmin, sub_zero]
  have hv : ∀ i, estimator oracle z x i = a i - (b i - (n : ℝ)⁻¹ • ∑ j, b j) := by
    intro i
    rw [hb]
    dsimp [estimator, a, b]
    module
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun i _ => norm_sub_sq_le (a i) (b i - (n : ℝ)⁻¹ • ∑ j, b j))
  simp only [← hv, Finset.expect_add_distrib, ← Finset.mul_expect] at h
  have ha := component_second_moment hL hc hg hlip hmin x
  have hb' := component_second_moment hL hc hg hlip hmin z
  have hvb := centered_second_moment b
  dsimp [a, b] at h hvb
  linarith

lemma objective_support {n : ℕ}
    {f : Fin n → E → ℝ} {oracle : Fin n × E → E}
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (oracle (i, x)) x) (x y : E) :
    ⟪fullGradient oracle x, y - x⟫ ≤ objective f y - objective f x := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun i _ => Gradient.convex_support (hc i) (hg i) x y)
  simpa only [expect_inner_left, fullGradient, Finset.expect_sub_distrib,
    ← objective_eq_expect] using h

lemma inner_step_bound {n : ℕ} [NeZero n]
    {f : Fin n → E → ℝ} {oracle : Fin n × E → E} {L : ℝ}
    (hL : 0 < L) (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (oracle (i, x)) x)
    (hlip : ∀ i x y, ‖oracle (i, x) - oracle (i, y)‖ ≤ L * ‖x - y‖)
    {xstar : E} (hmin : IsMinOn (objective f) univ xstar) (z x : E) :
    (𝔼 i, 16 * L * ‖x - (1 / (8 * L)) • estimator oracle z x i - xstar‖ ^ 2) +
      3 * (objective f x - objective f xstar) ≤
      16 * L * ‖x - xstar‖ ^ 2 + (objective f z - objective f xstar) := by
  have hv := estimator_second_moment hL hc hg hlip hmin z x
  have hs := objective_support hc hg x xstar
  have he : ⟪fullGradient oracle x, xstar - x⟫ = -⟪fullGradient oracle x, x - xstar⟫ := by
    rw [← inner_neg_right]
    congr 1
    module
  rw [he] at hs
  have hn : ∀ i, x - (1 / (8 * L)) • estimator oracle z x i - xstar =
      (x - xstar) - (1 / (8 * L)) • estimator oracle z x i := by intro i; module
  have hnorm : ∀ i, ‖x - (1 / (8 * L)) • estimator oracle z x i - xstar‖ ^ 2 =
      ‖x - xstar‖ ^ 2 - 2 * (1 / (8 * L)) * ⟪estimator oracle z x i, x - xstar⟫ +
        (1 / (8 * L)) ^ 2 * ‖estimator oracle z x i‖ ^ 2 := by
    intro i
    rw [hn, norm_sub_sq_real]
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_comm (x - xstar)]
    ring
  simp only [hnorm, ← Finset.mul_expect, Finset.expect_add_distrib,
    Finset.expect_sub_distrib, expect_inner_left, estimator_unbiased, Fintype.expect_const]
  have hL0 := hL.ne'
  field_simp
  nlinarith

lemma objective_list_average {n : ℕ}
    {f : Fin n → E → ℝ} {oracle : Fin n × E → E}
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (oracle (i, x)) x)
    (xstar : E) (xs : List E) (hne : xs.length ≠ 0) :
    (xs.length : ℝ) * (objective f ((xs.length : ℝ)⁻¹ • xs.sum) - objective f xstar) ≤
      (xs.map (fun x => objective f x - objective f xstar)).sum := by
  have hs : ∀ (xs : List E) (a : E),
      ⟪fullGradient oracle a, xs.sum - (xs.length : ℝ) • a⟫ ≤
        (xs.map (fun x => objective f x - objective f xstar)).sum -
          (xs.length : ℝ) * (objective f a - objective f xstar) := by
    intro xs a
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := objective_support hc hg a x
      have he : x + xs.sum - ((xs.length : ℝ) + 1) • a =
          (x - a) + (xs.sum - (xs.length : ℝ) • a) := by module
      simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
        List.map_cons, he, inner_add_right]
      linarith
  have h := hs xs ((xs.length : ℝ)⁻¹ • xs.sum)
  have hn : (xs.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hne
  simp only [smul_smul, mul_inv_cancel₀ hn, one_smul, sub_self, inner_zero_right] at h
  linarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma innerRun_length {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (oracle : Fin n × E → E) (L : ℝ) (z x : E) (seed : List (Fin n)) :
    (innerRun oracle L z x seed).2.length = seed.length := by
  induction seed generalizing x with
  | nil => rfl
  | cons i tail ih => simp only [innerRun, List.length_cons, ih]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma expect_tape_succ {n k : ℕ} (h : List (Fin n) → ℝ) :
    (𝔼 seed : Fin (k + 1) → Fin n, h (List.ofFn seed)) =
      𝔼 i : Fin n, 𝔼 seed : Fin k → Fin n, h (i :: List.ofFn seed) := by
  rw [Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Fin n)).symm
    (fun seed => h (List.ofFn seed))
    (fun seed => h (seed.1 :: List.ofFn seed.2))]
  · exact Finset.expect_product Finset.univ Finset.univ _
  · intro seed
    rw [List.ofFn_succ]
    rfl

lemma innerRun_bound {n : ℕ} [NeZero n]
    {f : Fin n → E → ℝ} {oracle : Fin n × E → E} {L : ℝ}
    (hL : 0 < L) (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (oracle (i, x)) x)
    (hlip : ∀ i x y, ‖oracle (i, x) - oracle (i, y)‖ ≤ L * ‖x - y‖)
    {xstar : E} (hmin : IsMinOn (objective f) univ xstar) (z x : E) (m : ℕ) :
    (𝔼 seed : Fin m → Fin n,
      let result := innerRun oracle L z x (List.ofFn seed)
      16 * L * ‖result.1 - xstar‖ ^ 2 +
        3 * (result.2.map (fun y => objective f y - objective f xstar)).sum) ≤
      16 * L * ‖x - xstar‖ ^ 2 + (m : ℝ) * (objective f z - objective f xstar) := by
  induction m generalizing x with
  | zero => simp [innerRun]
  | succ m ih =>
    rw [expect_tape_succ (fun seed =>
      let result := innerRun oracle L z x seed
      16 * L * ‖result.1 - xstar‖ ^ 2 +
        3 * (result.2.map (fun y => objective f y - objective f xstar)).sum)]
    simp only [innerRun, List.map_cons, List.sum_cons]
    have h := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
      add_le_add_right (ih (x - (1 / (8 * L)) • estimator oracle z x i))
        (3 * (objective f x - objective f xstar)))
    simp only [Finset.expect_add_distrib, Fintype.expect_const] at h
    have hs := inner_step_bound hL hc hg hlip hmin z x
    simp only [mul_add, ← add_assoc, Finset.expect_add_distrib, ← Finset.mul_expect,
      Fintype.expect_const, Nat.cast_add, Nat.cast_one] at h hs ⊢
    linarith

lemma epoch_bound {n : ℕ} [NeZero n]
    {f : Fin n → E → ℝ} {oracle : Fin n × E → E} {L : ℝ}
    (hL : 0 < L) (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (oracle (i, x)) x)
    (hlip : ∀ i x y, ‖oracle (i, x) - oracle (i, y)‖ ≤ L * ‖x - y‖)
    {xstar : E} (hmin : IsMinOn (objective f) univ xstar) (z x : E) {m : ℕ} (hm : 0 < m) :
    (𝔼 seed : Fin m → Fin n,
      let result := innerRun oracle L z x (List.ofFn seed)
      16 * L * ‖result.1 - xstar‖ ^ 2 +
        (2 * m : ℝ) * (objective f ((m : ℝ)⁻¹ • result.2.sum) - objective f xstar)) ≤
      16 * L * ‖x - xstar‖ ^ 2 + (m : ℝ) * (objective f z - objective f xstar) := by
  apply le_trans _ (innerRun_bound hL hc hg hlip hmin z x m)
  apply Finset.expect_le_expect
  intro seed _
  let result := innerRun oracle L z x (List.ofFn seed)
  have hlen : result.2.length = m := by simp [result, innerRun_length]
  have hj := objective_list_average hc hg xstar result.2 (by omega)
  rw [hlen] at hj
  have hn := hmin (Set.mem_univ ((m : ℝ)⁻¹ • result.2.sum))
  have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  change objective f xstar ≤ objective f ((m : ℝ)⁻¹ • result.2.sum) at hn
  change 16 * L * ‖result.1 - xstar‖ ^ 2 +
    (2 * m : ℝ) * (objective f ((m : ℝ)⁻¹ • result.2.sum) - objective f xstar) ≤
      16 * L * ‖result.1 - xstar‖ ^ 2 +
        3 * (result.2.map (fun y => objective f y - objective f xstar)).sum
  nlinarith

lemma epochRun_bound {n : ℕ} [NeZero n]
    {f : Fin n → E → ℝ} {oracle : Fin n × E → E} {L : ℝ}
    (hL : 0 < L) (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (oracle (i, x)) x)
    (hlip : ∀ i x y, ‖oracle (i, x) - oracle (i, y)‖ ≤ L * ‖x - y‖)
    {xstar : E} (hmin : IsMinOn (objective f) univ xstar) (S m : ℕ) (hm : 0 < m) (z x : E) :
    (𝔼 seed : EpochSeeds n m S,
      let result := epochRun oracle L m S x z seed
      16 * L * ‖result.1 - xstar‖ ^ 2 +
        ((m : ℝ) * 2 ^ S) * (objective f result.2 - objective f xstar)) ≤
      16 * L * ‖x - xstar‖ ^ 2 + (m : ℝ) * (objective f z - objective f xstar) := by
  induction S generalizing m z x with
  | zero => simp [epochRun]
  | succ S ih =>
    change (𝔼 seed : (Fin m → Fin n) × EpochSeeds n (2 * m) S,
      let inner := innerRun oracle L z x (List.ofFn seed.1)
      let result := epochRun oracle L (2 * m) S inner.1 ((m : ℝ)⁻¹ • inner.2.sum) seed.2
      16 * L * ‖result.1 - xstar‖ ^ 2 +
        ((m : ℝ) * 2 ^ (S + 1)) * (objective f result.2 - objective f xstar)) ≤ _
    rw [← Finset.univ_product_univ, Finset.expect_product]
    have h := Finset.expect_le_expect (s := Finset.univ) (fun (seed : Fin m → Fin n) _ =>
      ih (2 * m) (by omega)
        ((m : ℝ)⁻¹ • (innerRun oracle L z x (List.ofFn seed)).2.sum)
        (innerRun oracle L z x (List.ofFn seed)).1)
    have he := epoch_bound hL hc hg hlip hmin z x hm
    apply le_trans ?_ he
    simpa only [Nat.cast_mul, Nat.cast_ofNat, pow_succ, mul_assoc,
      mul_left_comm, mul_comm] using h

lemma initial_gap_bound {n : ℕ} [NeZero n]
    {f : Fin n → E → ℝ} {oracle : Fin n × E → E} {L R : ℝ}
    (hL : 0 < L) (hR : 0 ≤ R)
    (hg : ∀ i x, HasGradientAt (f i) (oracle (i, x)) x)
    (hlip : ∀ i x y, ‖oracle (i, x) - oracle (i, y)‖ ≤ L * ‖x - y‖)
    {xstar x0 : E} (hmin : IsMinOn (objective f) univ xstar) (hdist : ‖x0 - xstar‖ ≤ R) :
    objective f x0 - objective f xstar ≤ L / 2 * R ^ 2 := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun i _ => Gradient.smooth_upper_bound (hg i) (hlip i) xstar x0)
  have hz := fullGradient_minimizer hg hmin
  unfold fullGradient at hz
  simp only [Finset.expect_add_distrib, expect_inner_left, hz, inner_zero_left,
    add_zero, Fintype.expect_const, ← objective_eq_expect] at h
  have hn : ‖x0 - xstar‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg (x0 - xstar)]
  nlinarith

lemma epochRun_rate {n : ℕ} [NeZero n]
    {f : Fin n → E → ℝ} {oracle : Fin n × E → E} {L R : ℝ}
    (hL : 0 < L) (hR : 0 ≤ R) (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (oracle (i, x)) x)
    (hlip : ∀ i x y, ‖oracle (i, x) - oracle (i, y)‖ ≤ L * ‖x - y‖)
    {xstar x0 : E} (hmin : IsMinOn (objective f) univ xstar) (hdist : ‖x0 - xstar‖ ≤ R)
    (S : ℕ) :
    (𝔼 seed : EpochSeeds n 2 S,
      (objective f (epochRun oracle L 2 S x0 x0 seed).2 - objective f xstar)) ≤
      17 * L * R ^ 2 / (2 * 2 ^ S) := by
  have h := epochRun_bound hL hc hg hlip hmin S 2 (by decide) x0 x0
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Nat.cast_ofNat] at h
  have hn := Finset.expect_nonneg (s := Finset.univ) (fun seed _ =>
    sq_nonneg ‖(epochRun oracle L 2 S x0 x0 seed).1 - xstar‖)
  have hg0 := initial_gap_bound hL hR hg hlip hmin hdist
  have hd : ‖x0 - xstar‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg (x0 - xstar)]
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ 16 * L by positivity)
  have hn' := mul_nonneg (show 0 ≤ 16 * L by positivity) hn
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * 2 ^ S)).mpr
  have h' := (le_add_of_nonneg_left hn').trans h
  rw [mul_comm]
  apply h'.trans
  nlinarith only [hd', hg0]

end OracleTemplate.FiniteSum
