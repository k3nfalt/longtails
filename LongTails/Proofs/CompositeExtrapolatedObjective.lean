import LongTails.Proofs.CompositeLocalObjective

namespace LongTails.Proofs.CompositeExtrapolatedObjective

open LongTails.Setups.CompositeLipschitzHessian
open LongTails.Algorithms.CompositeLazyCubic
open LongTails.Proofs.CompositeCurvatureParameters
open LongTails.Proofs.CompositeExtrapolation
open scoped RealInnerProductSpace

noncomputable def point (p : Params) (y v : p.E) (i : ℕ) : p.E :=
  y + extrapolationFactor p ^ i • (v - y)

noncomputable def weight (p : Params) (i : ℕ) : ℝ :=
  (1 / 64 : ℝ) ^ i * extrapolationFactor p ^ (2 * i)

noncomputable def value (p : Params) (f : p.E → ℝ) (y v : p.E) : ℝ :=
  ∑ i ∈ Finset.range (depth p + 1), (1 / 64 : ℝ) ^ i * f (point p y v i)

noncomputable def grad (p : Params) (g : p.E → p.E) (y v : p.E) : p.E :=
  ∑ i ∈ Finset.range (depth p + 1), ((1 / 64 : ℝ) ^ i * extrapolationFactor p ^ i) • g (point p y v i)

noncomputable def hessian (p : Params) (A : p.E → p.E →L[ℝ] p.E) (y v : p.E) : p.E →L[ℝ] p.E :=
  ∑ i ∈ Finset.range (depth p + 1), weight p i • A (point p y v i)

lemma hessian_symmetric {p : Params} {A : p.E → p.E →L[ℝ] p.E}
    (hA : ∀ z x y, ⟪x, A z y⟫ = ⟪A z x, y⟫) (snapshot v x y : p.E) :
    ⟪x, hessian p A snapshot v y⟫ = ⟪hessian p A snapshot v x, y⟫ := by
  simp only [hessian, sum_apply, smul_apply, inner_sum, sum_inner, inner_smul_right, real_inner_smul_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hA]

lemma hessian_nonneg {p : Params} {A : p.E → p.E →L[ℝ] p.E}
    (hA : ∀ z d, 0 ≤ ⟪d, A z d⟫) (snapshot v d : p.E) :
    0 ≤ ⟪d, hessian p A snapshot v d⟫ := by
  simp only [hessian, sum_apply, smul_apply, inner_sum, inner_smul_right]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hessian_weight_bound p i).1 (hA _ _))

lemma point_hasFDerivAt (p : Params) (y v : p.E) (i : ℕ) :
    HasFDerivAt (fun u => point p y u i)
      ((extrapolationFactor p ^ i) • ContinuousLinearMap.id ℝ p.E) v := by
  convert (((hasFDerivAt_id v).sub_const y).const_smul (extrapolationFactor p ^ i)).const_add y using 1
  ext u
  rfl

lemma value_hasGradient {p : Params} {f : p.E → ℝ} {g : p.E → p.E}
    (hg : ∀ x, HasGradientAt f (g x) x) (y v : p.E) :
    HasGradientAt (value p f y) (grad p g y v) v := by
  have hd i := ((hg (point p y v i)).hasFDerivAt.comp v (point_hasFDerivAt p y v i)).const_mul ((1 / 64 : ℝ) ^ i)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert HasFDerivAt.fun_sum (u := Finset.range (depth p + 1)) (fun i _ => hd i) using 1
  · rfl
  · ext d
    simp [grad, InnerProductSpace.toDual_apply_apply]
    apply Finset.sum_congr rfl
    intro i hi
    ring

lemma grad_hasFDerivAt {p : Params} {g : p.E → p.E} {A : p.E → p.E →L[ℝ] p.E}
    (hg : ∀ x, HasFDerivAt g (A x) x) (y v : p.E) :
    HasFDerivAt (grad p g y) (hessian p A y v) v := by
  have hd i := ((hg (point p y v i)).comp v (point_hasFDerivAt p y v i)).const_smul
    ((1 / 64 : ℝ) ^ i * extrapolationFactor p ^ i)
  convert HasFDerivAt.fun_sum (u := Finset.range (depth p + 1)) (fun i _ => hd i) using 1
  · rfl
  · ext d
    simp only [hessian, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
      map_smul, ContinuousLinearMap.id_apply, smul_smul]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    dsimp [weight]
    rw [show 2 * i = i + i by omega, pow_add]
    ring

lemma point_affine (p : Params) (y v z : p.E) (i : ℕ) {a b : ℝ} (hab : a + b = 1) :
    point p y (a • v + b • z) i = a • point p y v i + b • point p y z i := by
  have hy : a • y + b • y = y := by rw [← add_smul, hab, one_smul]
  dsimp [point]
  calc
    _ = a • y + b • y + extrapolationFactor p ^ i • (a • v + b • z - (a • y + b • y)) := by rw [hy]
    _ = _ := by module

lemma value_convex {p : Params} {f : p.E → ℝ} (hf : ConvexOn ℝ Set.univ f) (y : p.E) :
    ConvexOn ℝ Set.univ (value p f y) := by
  have hi (i : ℕ) : ConvexOn ℝ Set.univ (fun v => f (point p y v i)) := by
    refine ⟨convex_univ, ?_⟩
    intro v hv z hz a b ha hb hab
    dsimp only
    rw [point_affine p y v z i hab]
    exact hf.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hs (s : Finset ℕ) : ConvexOn ℝ Set.univ
      (fun v => ∑ i ∈ s, (1 / 64 : ℝ) ^ i * f (point p y v i)) := by
    induction s using Finset.induction_on with
    | empty => simpa using convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set p.E))
    | @insert i s hnot ih =>
        simp only [Finset.sum_insert hnot]
        exact ((hi i).smul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 64) i)).add ih
  exact hs _

lemma value_nonneg {p : Params} {f : p.E → ℝ} (hf : ∀ x, 0 ≤ f x) (y v : p.E) :
    0 ≤ value p f y v := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (pow_nonneg (by norm_num) i) (hf _))

noncomputable def shifted (p : Params) (f : p.E → ℝ) (q w x : p.E) : ℝ :=
  f x - f w - ⟪q, x - w⟫

lemma shifted_convex {p : Params} {f : p.E → ℝ} (hf : ConvexOn ℝ Set.univ f) (q w : p.E) :
    ConvexOn ℝ Set.univ (shifted p f q w) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hf.2 hx hy ha hb hab
  have hc : a * f w + b * f w = f w := by rw [← add_mul, hab, one_mul]
  have hq : a * ⟪q, w⟫ + b * ⟪q, w⟫ = ⟪q, w⟫ := by rw [← add_mul, hab, one_mul]
  simp only [shifted, inner_sub_right, inner_add_right, inner_smul_right, smul_eq_mul] at h ⊢
  nlinarith only [h, hc, hq]

lemma shifted_nonneg {p : Params} {f : p.E → ℝ} {g : p.E → p.E}
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x) (w x : p.E) :
    0 ≤ shifted p f (g w) w x := by
  have h := OracleTemplate.Gradient.convex_support hf hg w x
  dsimp [shifted]
  linarith

lemma shifted_quadratic_bound {p : Params} {f : p.E → ℝ} {g : p.E → p.E}
    {A : p.E → p.E →L[ℝ] p.E} {H : ℝ}
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖) (w x : p.E) :
    ⟪x - w, A w (x - w)⟫ ≤ 2 * shifted p f (g w) w x + H * ‖x - w‖ ^ 3 / 3 := by
  have ht := CubicRegularization.objective_taylor (fun y => (hf y).hasFDerivAt) hg hLip w (x - w)
  have he : w + (x - w) = x := by abel
  rw [he] at ht
  dsimp only [shifted]
  have hl := (abs_le.mp ht).1
  linarith

lemma shifted_taylor {p : Params} {f : p.E → ℝ} {A : p.E → p.E →L[ℝ] p.E} {H : ℝ}
    (ht : ∀ x d, |f (x + d) + f (x - d) - 2 * f x - ⟪d, A x d⟫| ≤ H * ‖d‖ ^ 3 / 3)
    (q w x d : p.E) :
    |shifted p f q w (x + d) + shifted p f q w (x - d) -
      2 * shifted p f q w x - ⟪d, A x d⟫| ≤ H * ‖d‖ ^ 3 / 3 := by
  convert ht x d using 1
  congr 1
  simp only [shifted, inner_sub_right, inner_add_right]
  ring

noncomputable def shiftedRegularizer (p : Params) (ψ : p.E → ℝ) (q w x : p.E) : ℝ :=
  ψ x - ψ w + ⟪q, x - w⟫

lemma shiftedRegularizer_convex {p : Params} {ψ : p.E → ℝ} {C : Set p.E}
    (hψ : ConvexOn ℝ C ψ) (q w : p.E) :
    ConvexOn ℝ C (shiftedRegularizer p ψ q w) := by
  refine ⟨hψ.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hψ.2 hx hy ha hb hab
  have hc : a * ψ w + b * ψ w = ψ w := by rw [← add_mul, hab, one_mul]
  have hq : a * ⟪q, w⟫ + b * ⟪q, w⟫ = ⟪q, w⟫ := by rw [← add_mul, hab, one_mul]
  simp only [shiftedRegularizer, inner_sub_right, inner_add_right, inner_smul_right, smul_eq_mul] at h ⊢
  nlinarith only [h, hc, hq]

lemma shiftedRegularizer_nonneg {p : Params} {f ψ : p.E → ℝ} {C : Set p.E}
    {q w : p.E} (hψ : ConvexOn ℝ C ψ) (hw : w ∈ C) (hg : HasGradientAt f q w)
    (hm : ∀ u ∈ C, f w + ψ w ≤ f u + ψ u) {u : p.E} (hu : u ∈ C) :
    0 ≤ shiftedRegularizer p ψ q w u := by
  have h := composite_optimality hψ hw hg hm hu
  dsimp only [shiftedRegularizer]
  linarith

lemma shifted_sum (p : Params) (f ψ : p.E → ℝ) (q w x : p.E) :
    shifted p f q w x + shiftedRegularizer p ψ q w x = f x + ψ x - (f w + ψ w) := by
  dsimp [shifted, shiftedRegularizer]
  ring

lemma shifted_at_base (p : Params) (f ψ : p.E → ℝ) (q w : p.E) :
    shifted p f q w w = 0 ∧ shiftedRegularizer p ψ q w w = 0 := by
  simp [shifted, shiftedRegularizer]

lemma shifted_value_difference (p : Params) (f ψ : p.E → ℝ) (q w y v z : p.E) :
    (value p (shifted p f q w) y v + regularizerScale p * shiftedRegularizer p ψ q w v) -
        (value p (shifted p f q w) y z + regularizerScale p * shiftedRegularizer p ψ q w z) =
      (value p f y v + regularizerScale p * ψ v) -
        (value p f y z + regularizerScale p * ψ z) := by
  have hp i : ⟪q, point p y v i - w⟫ - ⟪q, point p y z i - w⟫ =
      extrapolationFactor p ^ i * (⟪q, v - w⟫ - ⟪q, z - w⟫) := by
    simp only [point, inner_sub_right, inner_add_right, inner_smul_right]
    ring
  have hs : value p (shifted p f q w) y v - value p (shifted p f q w) y z =
      value p f y v - value p f y z -
        regularizerScale p * (⟪q, v - w⟫ - ⟪q, z - w⟫) := by
    simp only [value, shifted, regularizerScale, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have h := hp i
    have hm := congrArg (fun t : ℝ => (1 / 64 : ℝ) ^ i * t) h
    nlinarith only [hm]
  dsimp only [shiftedRegularizer]
  linarith

lemma shifted_value_offset (p : Params) (f ψ : p.E → ℝ) (q w y v : p.E) :
    value p (shifted p f q w) y v + regularizerScale p * shiftedRegularizer p ψ q w v =
      value p f y v + regularizerScale p * ψ v -
        ((value p f y y + regularizerScale p * ψ y) -
          (value p (shifted p f q w) y y + regularizerScale p * shiftedRegularizer p ψ q w y)) := by
  have h := shifted_value_difference p f ψ q w y v y
  linarith

lemma value_at_snapshot (p : Params) (f : p.E → ℝ) (y : p.E) :
    value p f y y = (∑ i ∈ Finset.range (depth p + 1), (1 / 64 : ℝ) ^ i) * f y := by
  simp [value, point, Finset.sum_mul]

lemma base_weight_le_scale (p : Params) :
    (∑ i ∈ Finset.range (depth p + 1), (1 / 64 : ℝ) ^ i) ≤ regularizerScale p := by
  unfold regularizerScale
  apply Finset.sum_le_sum
  intro i hi
  have hc : 1 ≤ extrapolationFactor p ^ i := one_le_pow₀ (factor_bounds p).1
  have hw : 0 ≤ (1 / 64 : ℝ) ^ i := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left hc hw]

lemma snapshot_level {p : Params} {f ψ : p.E → ℝ} {y : p.E} {Δ : ℝ}
    (hf : 0 ≤ f y) (hgap : f y + ψ y ≤ Δ) :
    value p f y y + regularizerScale p * ψ y ≤ regularizerScale p * Δ := by
  rw [value_at_snapshot]
  apply snapshot_bound _ hf ((scale_bounds p).1.trans' zero_le_one) hgap
  exact base_weight_le_scale p

lemma value_summand_bound {p : Params} {f ψ : p.E → ℝ} {y v : p.E} {Δ : ℝ}
    (hf : ∀ x, 0 ≤ f x) (hψ : 0 ≤ ψ v)
    (hlevel : value p f y v + regularizerScale p * ψ v ≤ 2 * Δ)
    {i : ℕ} (hi : i ≤ depth p) :
    f (point p y v i) ≤ 2 * Δ * (64 : ℝ) ^ i := by
  have hs := nonnegative_summand_bound (Finset.range (depth p + 1))
    (fun j => (1 / 64 : ℝ) ^ j) (fun j => f (point p y v j))
    (fun j _ => pow_nonneg (by norm_num) j) (fun j _ => hf _)
    ((scale_bounds p).1.trans' zero_le_one) hψ hlevel
    (show i ∈ Finset.range (depth p + 1) by simpa using Nat.lt_succ_of_le hi)
  have hm := mul_le_mul_of_nonneg_right hs (pow_nonneg (by norm_num : (0 : ℝ) ≤ 64) i)
  have hid : (1 / 64 : ℝ) ^ i * 64 ^ i = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((1 / 64 : ℝ) ^ i * 64 ^ i) * f (point p y v i) := by rw [hid, one_mul]
    _ = (1 / 64 : ℝ) ^ i * f (point p y v i) * 64 ^ i := by ring
    _ ≤ _ := hm

lemma original_gap_of_level {p : Params} {f ψ : p.E → ℝ} {y v : p.E} {Δ : ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hy0 : 0 ≤ f y) (hy : f y ≤ Δ)
    (hlevel : value p f y v + regularizerScale p * ψ v ≤ 2 * Δ) :
    f v + ψ v ≤ 3 * Δ := by
  have hΔ : 0 ≤ Δ := hy0.trans hy
  have ha := scale_bounds p
  have ha0 : 0 < regularizerScale p := lt_of_lt_of_le zero_lt_one ha.1
  have hl := weighted_lower (Finset.range (depth p + 1))
    (fun i => (1 / 64 : ℝ) ^ i) (fun i => extrapolationFactor p ^ i)
    (fun i _ => pow_nonneg (by norm_num) i)
    (fun i _ => one_le_pow₀ (factor_bounds p).1) (ψ := ψ) hf y v
  change regularizerScale p * (f v + ψ v) -
      (regularizerScale p - ∑ i ∈ Finset.range (depth p + 1), (1 / 64 : ℝ) ^ i) * f y ≤
    value p f y v + regularizerScale p * ψ v at hl
  have hw : 0 ≤ ∑ i ∈ Finset.range (depth p + 1), (1 / 64 : ℝ) ^ i :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (by norm_num) i)
  have hwy := mul_nonneg hw hy0
  have hay := mul_le_mul_of_nonneg_left hy ha0.le
  have had := mul_le_mul_of_nonneg_right ha.1 hΔ
  apply (mul_le_mul_iff_right₀ ha0).mp
  nlinarith only [hl, hlevel, hwy, hay, had]

lemma contraction_of_accuracy {p : Params} {f ψ : p.E → ℝ} {C : Set p.E}
    (hf : ConvexOn ℝ Set.univ f) (hψ : ConvexOn ℝ C ψ) {q w y v : p.E}
    (hy : y ∈ C) (hw : w ∈ C) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hgap : f y + ψ y - (f w + ψ w) ≤ Δ)
    (haccuracy :
      (value p f y v + regularizerScale p * ψ v) -
        (value p f y (y + (extrapolationFactor p ^ depth p)⁻¹ • (w - y)) +
          regularizerScale p * ψ (y + (extrapolationFactor p ^ depth p)⁻¹ • (w - y))) ≤
        regularizerScale p * Δ / 12) :
    f v + ψ v - (f w + ψ w) ≤ 3 * Δ / 4 := by
  have hbase := shifted_at_base p f ψ q w
  have hpow := factor_power_bounds p
  have hc := factor_bounds p
  have h := extrapolated_contraction (v := v) (Finset.range (depth p + 1))
    (fun i => (1 / 64 : ℝ) ^ i) (fun i => extrapolationFactor p ^ i)
    (fun i _ => pow_nonneg (by norm_num) i) (fun i _ => one_le_pow₀ hc.1)
    (show 1 ≤ extrapolationFactor p ^ depth p by linarith [hpow.1]) hpow.2
    (fun i hi => pow_le_pow_right₀ hc.1 (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    (shifted_convex hf q w) (shiftedRegularizer_convex hψ q w) hy hw hbase.1 hbase.2
    hΔ (by simpa only [shifted_sum] using hgap)
    (show 0 < regularizerScale p from lt_of_lt_of_le zero_lt_one (scale_bounds p).1)
  change value p (shifted p f q w) y v + regularizerScale p * shiftedRegularizer p ψ q w v -
      (value p (shifted p f q w) y (y + (extrapolationFactor p ^ depth p)⁻¹ • (w - y)) +
        regularizerScale p * shiftedRegularizer p ψ q w (y + (extrapolationFactor p ^ depth p)⁻¹ • (w - y))) ≤
      regularizerScale p * Δ / 12 →
      shifted p f q w v + shiftedRegularizer p ψ q w v ≤ 3 * Δ / 4 at h
  rw [shifted_value_difference, shifted_sum] at h
  exact h haccuracy

lemma comparator_mem {p : Params} {C : Set p.E} (hC : Convex ℝ C) {y w : p.E}
    (hy : y ∈ C) (hw : w ∈ C) :
    y + (extrapolationFactor p ^ depth p)⁻¹ • (w - y) ∈ C := by
  have hM : 1 ≤ extrapolationFactor p ^ depth p := (factor_power_bounds p).1.trans' (by norm_num)
  exact hC.add_smul_sub_mem hy hw ⟨inv_nonneg.mpr (by linarith), (inv_le_one₀ (by linarith)).mpr hM⟩

lemma comparator_metric_bound {p : Params} (B : p.E →L[ℝ] p.E) (hp : ∀ d, 0 ≤ ⟪d, B d⟫)
    {y w : p.E} {R : ℝ} (hR : ⟪y - w, B (y - w)⟫ ≤ R) :
    CurvatureMetric.metricNorm B ((y + (extrapolationFactor p ^ depth p)⁻¹ • (w - y)) - y) ^ 2 ≤ R := by
  have hM : 1 ≤ extrapolationFactor p ^ depth p := one_le_pow₀ (factor_bounds p).1
  have hM0 : 0 < extrapolationFactor p ^ depth p := lt_of_lt_of_le zero_lt_one hM
  have hi0 : 0 ≤ (extrapolationFactor p ^ depth p)⁻¹ := inv_nonneg.mpr hM0.le
  have hi1 : (extrapolationFactor p ^ depth p)⁻¹ ≤ 1 := (inv_le_one₀ hM0).mpr hM
  rw [add_sub_cancel_left, CurvatureMetric.metricNorm_smul B hp, abs_of_nonneg hi0, mul_pow,
    CurvatureMetric.metricNorm_sq B hp]
  have he : ⟪w - y, B (w - y)⟫ = ⟪y - w, B (y - w)⟫ := by
    have hd : w - y = -(y - w) := by abel
    rw [hd, map_neg, inner_neg_left, inner_neg_right, neg_neg]
  rw [he]
  have hpow : ((extrapolationFactor p ^ depth p)⁻¹) ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ hi0 hi1 2
  have hh := mul_le_mul_of_nonneg_right hpow (hp (y - w))
  nlinarith only [hh, hR]

lemma comparator_level_bound {p : Params} {f ψ : p.E → ℝ} {C : Set p.E}
    (hf : ConvexOn ℝ Set.univ f) (hψ : ConvexOn ℝ C ψ) {y w : p.E}
    (hy : y ∈ C) (hw : w ∈ C) (hfw : f w = 0) (hψw : ψ w = 0)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (hfy : 0 ≤ f y) (hgap : f y + ψ y ≤ Δ) :
    value p f y (y + (extrapolationFactor p ^ depth p)⁻¹ • (w - y)) +
      regularizerScale p * ψ (y + (extrapolationFactor p ^ depth p)⁻¹ • (w - y)) ≤ 2 * Δ := by
  have hc := factor_bounds p
  have hM : 1 ≤ extrapolationFactor p ^ depth p := one_le_pow₀ hc.1
  have hcomp := weighted_comparator (Finset.range (depth p + 1))
    (fun i => (1 / 64 : ℝ) ^ i) (fun i => extrapolationFactor p ^ i)
    (fun i _ => pow_nonneg (by norm_num) i) hM
    (fun i hi => ⟨pow_nonneg (hc.1.trans' zero_le_one) i,
      pow_le_pow_right₀ hc.1 (Nat.le_of_lt_succ (Finset.mem_range.mp hi))⟩) hf hψ hy hw hfw hψw
  have hshift := mul_nonneg (sub_nonneg.mpr (base_weight_le_scale p)) hfy
  have hM0 : 0 < extrapolationFactor p ^ depth p := lt_of_lt_of_le zero_lt_one hM
  have hi0 : 0 ≤ (extrapolationFactor p ^ depth p)⁻¹ := inv_nonneg.mpr hM0.le
  have hi1 : (extrapolationFactor p ^ depth p)⁻¹ ≤ 1 := (inv_le_one₀ hM0).mpr hM
  have ha0 : 0 ≤ regularizerScale p := (scale_bounds p).1.trans' zero_le_one
  have hgap' := mul_le_mul_of_nonneg_left hgap (mul_nonneg ha0 (sub_nonneg.mpr hi1))
  have hcoef := mul_nonneg (mul_nonneg ha0 hΔ) hi0
  have hscale := mul_le_mul_of_nonneg_right (scale_bounds p).2 hΔ
  change value p f y (y + (extrapolationFactor p ^ depth p)⁻¹ • (w - y)) +
      regularizerScale p * ψ (y + (extrapolationFactor p ^ depth p)⁻¹ • (w - y)) +
      (regularizerScale p - ∑ i ∈ Finset.range (depth p + 1), (1 / 64 : ℝ) ^ i) * f y ≤
      regularizerScale p * (1 - (extrapolationFactor p ^ depth p)⁻¹) * (f y + ψ y) at hcomp
  nlinarith only [hcomp, hshift, hgap', hcoef, hscale]

lemma point_sub (p : Params) (y v z : p.E) (i : ℕ) :
    point p y v i - point p y z i = extrapolationFactor p ^ i • (v - z) := by
  dsimp [point]
  module

lemma weight_times_factor (p : Params) (i : ℕ) :
    weight p i * extrapolationFactor p ^ i =
      (1 / 64 : ℝ) ^ i * extrapolationFactor p ^ (3 * i) := by
  dsimp [weight]
  rw [mul_assoc, ← pow_add]
  congr 2
  omega

lemma hessian_lipschitz {p : Params} {A : p.E → p.E →L[ℝ] p.E} {H : ℝ}
    (hH : 0 ≤ H) (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖) (y v z : p.E) :
    ‖hessian p A y v - hessian p A y z‖ ≤ 2 * H * ‖v - z‖ := by
  have hc0 : 0 ≤ extrapolationFactor p := (factor_bounds p).1.trans' zero_le_one
  have hi (i : ℕ) : ‖weight p i • (A (point p y v i) - A (point p y z i))‖ ≤
      (1 / 4 : ℝ) ^ i * (H * ‖v - z‖) := by
    have hw0 : 0 ≤ weight p i := (hessian_weight_bound p i).1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw0]
    have hl := hLip (point p y v i) (point p y z i)
    rw [point_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc0 i)] at hl
    have hs := mul_le_mul_of_nonneg_left hl hw0
    have hw : weight p i * extrapolationFactor p ^ i ≤ (1 / 4 : ℝ) ^ i := by
      rw [weight_times_factor]
      exact (third_weight_bound p i).trans (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4) i)
    have hm := mul_le_mul_of_nonneg_right hw (mul_nonneg hH (norm_nonneg (v - z)))
    nlinarith only [hs, hm]
  calc
    _ = ‖∑ i ∈ Finset.range (depth p + 1), weight p i •
        (A (point p y v i) - A (point p y z i))‖ := by
      congr 1
      simp only [hessian, smul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ Finset.range (depth p + 1), ‖weight p i •
        (A (point p y v i) - A (point p y z i))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (depth p + 1), (1 / 4 : ℝ) ^ i * (H * ‖v - z‖) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = (∑ i ∈ Finset.range (depth p + 1), (1 / 4 : ℝ) ^ i) * (H * ‖v - z‖) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (4 / 3 : ℝ) * (H * ‖v - z‖) :=
      mul_le_mul_of_nonneg_right (geometric_quarter_bound _) (mul_nonneg hH (norm_nonneg _))
    _ ≤ _ := by nlinarith [mul_nonneg hH (norm_nonneg (v - z))]

lemma adjacent_relation (p : Params) (y v : p.E) (i : ℕ) :
    ((depth p : ℝ) + 1) • point p y v i = y + (depth p : ℝ) • point p y v (i + 1) := by
  have hJ : (depth p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) (depth_two_le p)))
  have hc : (depth p : ℝ) * extrapolationFactor p = (depth p : ℝ) + 1 := by
    dsimp [extrapolationFactor]
    field_simp
  simp only [point, pow_succ, smul_add, smul_smul]
  have hp : (depth p : ℝ) * (extrapolationFactor p ^ i * extrapolationFactor p) =
      ((depth p : ℝ) + 1) * extrapolationFactor p ^ i := by
    calc
      _ = ((depth p : ℝ) * extrapolationFactor p) * extrapolationFactor p ^ i := by ring
      _ = _ := by rw [hc]
  rw [hp]
  module

lemma weight_nonneg (p : Params) (i : ℕ) : 0 ≤ weight p i := (hessian_weight_bound p i).1

lemma adjacent_bound {p : Params} {f : p.E → ℝ} {A : p.E → p.E →L[ℝ] p.E} {H r : ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hpos : ∀ x, 0 ≤ f x)
    (htaylor : ∀ x d, |f (x + d) + f (x - d) - 2 * f x - ⟪d, A x d⟫| ≤ H * ‖d‖ ^ 3 / 3)
    (hH : 0 ≤ H) (hr : 0 < r) {y v : p.E}
    (hy : f y ≤ H * r ^ 3)
    (hv : ∀ i ≤ depth p, f (point p y v i) ≤ 2 * H * r ^ 3 * (64 : ℝ) ^ i)
    {i : ℕ} (hi : i < depth p) (d : p.E) :
    ⟪d, A (point p y v i) d⟫ ≤ ((depth p : ℝ) + 1) * ⟪d, A y d⟫ +
      20 * ((depth p : ℝ) + 1) ^ 2 * (H * r * ‖d‖ ^ 2) * (4 : ℝ) ^ i := by
  have hs : 1 ≤ (4 : ℝ) ^ (i + 1) := one_le_pow₀ (by norm_num)
  have hv' : f (point p y v (i + 1)) ≤ 2 * H * r ^ 3 * ((4 : ℝ) ^ (i + 1)) ^ 3 := by
    have he : ((4 : ℝ) ^ (i + 1)) ^ 3 = (64 : ℝ) ^ (i + 1) := by
      rw [← pow_mul, Nat.mul_comm (i + 1) 3, pow_mul]
      norm_num
    rw [he]
    exact hv _ (by omega)
  have h := adjacent_curvature hf hpos htaylor hH hr hs (by positivity : 0 ≤ (depth p : ℝ))
    (adjacent_relation p y v i) hy hv' d
  simp only [pow_succ] at h
  nlinarith only [h]

lemma terminal_bound {p : Params} {A : p.E → p.E →L[ℝ] p.E} {H r : ℝ}
    (hH : 0 ≤ H) (hr : 0 ≤ r) (hm : 1 ≤ p.m)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖) {y v : p.E}
    (hQ : ∀ d, 0 ≤ ⟪d, A y d⟫) (hdist : ‖v - y‖ ≤ 6 * r * condition p) (d : p.E) :
    weight p (depth p) * ⟪d, A (point p y v (depth p)) d⟫ ≤
      weight p (depth p) * (((depth p : ℝ) + 1) * ⟪d, A y d⟫) + 6 * (H * r * ‖d‖ ^ 2) := by
  have hc0 : 0 ≤ extrapolationFactor p := (factor_bounds p).1.trans' zero_le_one
  have hκ0 : 0 ≤ condition p := (condition_bounds p hm).1.trans' zero_le_one
  have hw := weight_nonneg p (depth p)
  have hκ : condition p ≤ (8 : ℝ) ^ depth p :=
    (condition_lt_pow_depth p).le.trans ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.sub_le _ _)).trans (pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ 8) _))
  have hwc : weight p (depth p) * extrapolationFactor p ^ depth p ≤ (1 / 8 : ℝ) ^ depth p := by
    have he : weight p (depth p) * extrapolationFactor p ^ depth p =
        (1 / 64 : ℝ) ^ depth p * extrapolationFactor p ^ (3 * depth p) := by
      dsimp [weight]
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    rw [he]
    exact third_weight_bound p _
  have hproduct : weight p (depth p) * extrapolationFactor p ^ depth p * condition p ≤ 1 := by
    have hh := mul_le_mul hwc hκ hκ0 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8) _)
    have he : (1 / 8 : ℝ) ^ depth p * (8 : ℝ) ^ depth p = 1 := by rw [← mul_pow]; norm_num
    exact hh.trans_eq he
  have hpert := CurvatureMetric.quadratic_perturbation (A y) (A (point p y v (depth p))) d
  have hl := hLip (point p y v (depth p)) y
  have hd : point p y v (depth p) - y = extrapolationFactor p ^ depth p • (v - y) := by
    dsimp [point]; abel
  rw [hd, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc0 _)] at hl
  have hld := mul_le_mul_of_nonneg_left hdist (mul_nonneg hH (pow_nonneg hc0 (depth p)))
  have hnorm : ‖A (point p y v (depth p)) - A y‖ ≤
      6 * H * r * extrapolationFactor p ^ depth p * condition p := by nlinarith only [hl, hld]
  have hnormd := mul_le_mul_of_nonneg_right hnorm (sq_nonneg ‖d‖)
  have hbase : ⟪d, A (point p y v (depth p)) d⟫ ≤ ⟪d, A y d⟫ +
      6 * H * r * extrapolationFactor p ^ depth p * condition p * ‖d‖ ^ 2 := by
    nlinarith only [hpert, hnormd]
  have hscale := mul_le_mul_of_nonneg_left hbase hw
  have hnoise := mul_le_mul_of_nonneg_left hproduct (by positivity : 0 ≤ 6 * H * r * ‖d‖ ^ 2)
  have hterm := mul_nonneg hw (mul_nonneg (Nat.cast_nonneg (depth p)) (hQ d))
  nlinarith only [hscale, hnoise, hterm]

lemma extrapolated_curvature_bound {p : Params} {f : p.E → ℝ}
    {A : p.E → p.E →L[ℝ] p.E} {H r : ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hpos : ∀ x, 0 ≤ f x)
    (htaylor : ∀ x d, |f (x + d) + f (x - d) - 2 * f x - ⟪d, A x d⟫| ≤ H * ‖d‖ ^ 3 / 3)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (hH : 0 ≤ H) (hr : 0 < r) (hm : 1 ≤ p.m) {y v : p.E}
    (hy : f y ≤ H * r ^ 3)
    (hv : ∀ i ≤ depth p, f (point p y v i) ≤ 2 * H * r ^ 3 * (64 : ℝ) ^ i)
    (hQ : ∀ d, 0 ≤ ⟪d, A y d⟫) (hdist : ‖v - y‖ ≤ 6 * r * condition p) (d : p.E) :
    (∑ i ∈ Finset.range (depth p + 1), weight p i * ⟪d, A (point p y v i) d⟫) ≤
      2 * ((depth p : ℝ) + 1) * ⟪d, A y d⟫ +
        256 * ((depth p : ℝ) + 1) ^ 2 * (H * r * ‖d‖ ^ 2) := by
  apply weighted_curvature_bound (by have h := Nat.cast_nonneg (α := ℝ) (depth p); linarith : 1 ≤ (depth p : ℝ) + 1) (hQ d)
    (by positivity : 0 ≤ H * r * ‖d‖ ^ 2)
  · intro i hi
    exact hessian_weight_bound p i
  · intro i hi
    exact adjacent_bound hf hpos htaylor hH hr hy hv hi d
  · exact terminal_bound hH hr.le hm hLip hQ hdist d

lemma growth_distance_bound {D γ κ r : ℝ} (hD : 0 ≤ D) (hγ : 0 < γ)
    (hκ : 2 ≤ κ) (hr : 0 ≤ r) (hgrowth : γ * D ^ 3 / 12 ≤ 3 * (γ * κ * r ^ 3)) :
    D ≤ 3 * κ * r := by
  have hκ0 : 0 ≤ κ := by linarith
  have hκ2 : 4 ≤ κ ^ 2 := by nlinarith
  have hκ3 : 4 * κ ≤ κ ^ 3 := by nlinarith [mul_le_mul_of_nonneg_right hκ2 hκ0]
  have hpow : D ^ 3 ≤ 36 * κ * r ^ 3 := by nlinarith only [hgrowth, hγ]
  apply (pow_le_pow_iff_left₀ hD (by positivity : 0 ≤ 3 * κ * r) (by norm_num : (3 : ℕ) ≠ 0)).mp
  have ht := mul_le_mul_of_nonneg_right hκ3 (pow_nonneg hr 3)
  have hn : 0 ≤ κ * r ^ 3 := by positivity
  nlinarith only [hpow, ht, hn]

lemma sublevel_distance {p : Params} {γ H r : ℝ} {y v w : p.E}
    (hγ : 0 < γ) (hr : 0 ≤ r) (hH : H = γ * condition p)
    (hy : γ * ‖y - w‖ ^ 3 / 12 ≤ H * r ^ 3)
    (hv : γ * ‖v - w‖ ^ 3 / 12 ≤ 3 * (H * r ^ 3)) :
    ‖v - y‖ ≤ 6 * r * condition p := by
  have hκ : 2 ≤ condition p := by
    have hp : 0 ≤ (p.m : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg _) _
    dsimp [condition]
    nlinarith
  have hy' : γ * ‖y - w‖ ^ 3 / 12 ≤ 3 * (γ * condition p * r ^ 3) := by
    rw [hH] at hy
    have hn : 0 ≤ γ * condition p * r ^ 3 := by positivity
    linarith
  have hdy := growth_distance_bound (norm_nonneg _) hγ hκ hr hy'
  have hdv := growth_distance_bound (norm_nonneg _) hγ hκ hr (by simpa only [hH] using hv)
  have ht : ‖v - y‖ ≤ ‖v - w‖ + ‖y - w‖ := by
    calc
      _ = ‖(v - w) - (y - w)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  nlinarith only [hdy, hdv, ht]

lemma sublevel_hessian_bound {p : Params} {f ψ : p.E → ℝ}
    {A : p.E → p.E →L[ℝ] p.E} {γ H r : ℝ} {C : Set p.E} {w y v : p.E}
    (hf : ConvexOn ℝ Set.univ f) (hf0 : ∀ x, 0 ≤ f x) (hψ0 : ∀ x ∈ C, 0 ≤ ψ x)
    (htaylor : ∀ x d, |f (x + d) + f (x - d) - 2 * f x - ⟪d, A x d⟫| ≤ H * ‖d‖ ^ 3 / 3)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (hγ : 0 < γ) (hH : 0 ≤ H) (hr : 0 < r) (hm : 1 ≤ p.m)
    (hidentity : H = γ * condition p)
    (hgrowth : ∀ x ∈ C, γ * ‖x - w‖ ^ 3 / 12 ≤ f x + ψ x)
    (hy : y ∈ C) (hv : v ∈ C) (hgap : f y + ψ y ≤ H * r ^ 3)
    (hlevel : value p f y v + regularizerScale p * ψ v ≤ 2 * (H * r ^ 3))
    (hQ : ∀ d, 0 ≤ ⟪d, A y d⟫) (d : p.E) :
    ⟪d, hessian p A y v d⟫ ≤
      ⟪d, ((32 * ((depth p : ℝ) + 1)) • A y +
        (4096 * ((depth p : ℝ) + 1) ^ 2 * H * r) • ContinuousLinearMap.id ℝ p.E) d⟫ / 16 := by
  have hfy : f y ≤ H * r ^ 3 := by linarith [hψ0 y hy]
  have hvgap := original_gap_of_level hf (hf0 y) hfy hlevel
  have hd := sublevel_distance hγ hr.le hidentity ((hgrowth y hy).trans hgap)
    ((hgrowth v hv).trans hvgap)
  have hb := extrapolated_curvature_bound hf hf0 htaylor hLip hH hr hm hfy
    (fun i hi => by simpa only [mul_assoc] using value_summand_bound hf0 (hψ0 v hv) hlevel hi) hQ hd d
  have he : ⟪d, hessian p A y v d⟫ =
      ∑ i ∈ Finset.range (depth p + 1), weight p i * ⟪d, A (point p y v i) d⟫ := by
    simp [hessian, inner_sum, inner_smul_right]
  rw [he]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  nlinarith only [hb]

lemma metric_radius_cube {H Δ : ℝ} (hH : 0 < H) (hΔ : 0 ≤ Δ) :
    H * ((Δ / H) ^ (1 / 3 : ℝ)) ^ 3 = Δ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hΔ hH.le)]
  norm_num
  field_simp

lemma metric_radius_pos {H Δ : ℝ} (hH : 0 < H) (hΔ : 0 < Δ) :
    0 < (Δ / H) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (div_pos hΔ hH) _

lemma tube_scale {H Δ μ : ℝ} (hH : 0 ≤ H) (hΔ : 0 ≤ Δ) (hμ : 0 ≤ μ)
    (hscale : 4096 * H ^ 2 * Δ ≤ μ ^ 3) :
    2 * H * (4 * Real.sqrt Δ) ≤ (3 / 16 : ℝ) * μ * Real.sqrt μ := by
  apply (sq_le_sq₀ (by positivity : 0 ≤ 2 * H * (4 * Real.sqrt Δ))
    (by positivity : 0 ≤ (3 / 16 : ℝ) * μ * Real.sqrt μ)).mp
  have hleft : (2 * H * (4 * Real.sqrt Δ)) ^ 2 = 64 * H ^ 2 * Δ := by
    simp only [mul_pow, Real.sq_sqrt hΔ]
    ring
  have hright : ((3 / 16 : ℝ) * μ * Real.sqrt μ) ^ 2 = (9 / 256 : ℝ) * μ ^ 3 := by
    simp only [mul_pow, Real.sq_sqrt hμ]
    ring
  rw [hleft, hright]
  have hn : 0 ≤ H ^ 2 * Δ := by positivity
  nlinarith only [hscale, hn]

lemma snapshot_tube_scale {H r j : ℝ} (hH : 0 ≤ H) (hr : 0 ≤ r) (hj : 1 ≤ j) :
    4096 * H ^ 2 * (H * r ^ 3) ≤ (4096 * j ^ 2 * H * r) ^ 3 := by
  have hj2 : 1 ≤ j ^ 2 := one_le_pow₀ hj
  have hm' : 16 * H * r ≤ 4096 * j ^ 2 * H * r := by
    have hh := mul_le_mul_of_nonneg_right hj2 (mul_nonneg hH hr)
    nlinarith only [hh, mul_nonneg hH hr]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 16 * H * r) hm' 3
  nlinarith only [hp]

lemma extrapolated_tube_bound {p : Params} {A : p.E → p.E →L[ℝ] p.E}
    {H r Δ : ℝ} (hH : 0 < H) (hr : 0 < r) (hΔ : H * r ^ 3 = Δ)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (B : p.E →L[ℝ] p.E) (snapshot z u : p.E)
    (hl : ∀ d, (4096 * ((depth p : ℝ) + 1) ^ 2 * H * r) * ‖d‖ ^ 2 ≤ ⟪d, B d⟫)
    (hz : ∀ d, ⟪d, hessian p A snapshot z d⟫ ≤ ⟪d, B d⟫ / 16)
    (hd : CurvatureMetric.metricNorm B (u - z) ≤ 4 * Real.sqrt Δ) :
    ∀ d, ⟪d, hessian p A snapshot u d⟫ ≤ ⟪d, B d⟫ / 4 := by
  have hj : 1 ≤ (depth p : ℝ) + 1 := by have hn := Nat.cast_nonneg (α := ℝ) (depth p); linarith
  have hμ : 0 < 4096 * ((depth p : ℝ) + 1) ^ 2 * H * r := by positivity
  have hΔ0 : 0 ≤ Δ := by rw [← hΔ]; positivity
  have hscale := snapshot_tube_scale hH.le hr.le hj
  rw [hΔ] at hscale
  have ht := tube_scale hH.le hΔ0 hμ.le hscale
  have hb := CurvatureMetric.metric_tube_domination B (hessian p A snapshot z)
    (hessian p A snapshot u) hμ (by positivity : 0 ≤ 2 * H) (by norm_num : (0 : ℝ) ≤ 3 / 16)
    hl (a := (1 / 16 : ℝ)) (fun d => by linarith [hz d])
    (hessian_lipschitz hH.le hLip snapshot u z) hd ht
  intro d
  have h := hb d
  norm_num at h
  linarith

lemma scaled_snapshot_curvature {m Δ Q T : ℝ} (hm : 0 < m) (hΔ : 0 ≤ Δ)
    (hT : T ≤ 60 * m ^ 3 * Δ)
    (hcurv : (1 / (8 * m)) ^ 2 * Q ≤ 2 * Δ + (4 / 3 : ℝ) * (1 / (8 * m)) ^ 3 * T) :
    Q ≤ 192 * m ^ 2 * Δ := by
  have hs := mul_le_mul_of_nonneg_left hcurv (by positivity : 0 ≤ 512 * m ^ 3)
  have he₁ : 512 * m ^ 3 * ((1 / (8 * m)) ^ 2 * Q) = 8 * m * Q := by field_simp; ring
  have he₂ : 512 * m ^ 3 * (2 * Δ + (4 / 3 : ℝ) * (1 / (8 * m)) ^ 3 * T) =
      1024 * m ^ 3 * Δ + (4 / 3 : ℝ) * T := by field_simp; ring
  rw [he₁, he₂] at hs
  have hp : 0 ≤ m ^ 3 * Δ := by positivity
  apply le_of_mul_le_mul_left (a := 8 * m) ?_ (by positivity)
  nlinarith only [hs, hT, hp]

lemma snapshot_radius {D m r : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ m) (hr : 0 ≤ r)
    (h : D ^ 3 ≤ 60 * m ^ 3 * r ^ 3) : D ≤ 4 * m * r := by
  apply (pow_le_pow_iff_left₀ hD (by positivity : 0 ≤ 4 * m * r) (by norm_num : (3 : ℕ) ≠ 0)).mp
  have hp : 0 ≤ m ^ 3 * r ^ 3 := by positivity
  nlinarith only [h, hp]

lemma snapshot_metric_bound {L m Δ Q δ D : ℝ} (hL : 1 ≤ L) (hΔ : 0 ≤ Δ)
    (hQ : Q ≤ 192 * m ^ 2 * Δ) (hD : δ * D ^ 2 ≤ 16 * m ^ 2 * Δ) :
    32 * L * Q + 4096 * L ^ 2 * δ * D ^ 2 ≤ 131072 * L ^ 2 * m ^ 2 * Δ := by
  have h₁ := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 32 * L)
  have h₂ := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 4096 * L ^ 2)
  have h₃ := mul_nonneg (sub_nonneg.mpr hL) (by positivity : 0 ≤ L * m ^ 2 * Δ)
  have h₄ : 0 ≤ L ^ 2 * m ^ 2 * Δ := by positivity
  nlinarith only [h₁, h₂, h₃, h₄]

lemma snapshot_distance_bound {p : Params} {f : p.E → ℝ}
    {A : p.E → p.E →L[ℝ] p.E} {γ H r Δ : ℝ} {w y : p.E}
    (hf : ConvexOn ℝ Set.univ f) (hf0 : ∀ x, 0 ≤ f x)
    (htaylor : ∀ x d, |f (x + d) + f (x - d) - 2 * f x - ⟪d, A x d⟫| ≤ H * ‖d‖ ^ 3 / 3)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (hH : 0 < H) (hr : 0 ≤ r) (hΔ : 0 ≤ Δ) (hm : 1 ≤ p.m)
    (hidentity : H = γ * condition p) (hcube : H * r ^ 3 = Δ)
    (hw : f w = 0) (hy : f y ≤ Δ) (hgrowth : γ * ‖y - w‖ ^ 3 / 12 ≤ Δ) :
    ⟪y - w, ((32 * ((depth p : ℝ) + 1)) • A y +
      (4096 * ((depth p : ℝ) + 1) ^ 2 * H * r) • ContinuousLinearMap.id ℝ p.E) (y - w)⟫ ≤
      131072 * ((depth p : ℝ) + 1) ^ 2 * (p.m : ℝ) ^ 2 * Δ := by
  have hm1 : (1 : ℝ) ≤ p.m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < p.m := by linarith
  have hκ := condition_bounds p hm
  have hκ0 : 0 ≤ condition p := hκ.1.trans' zero_le_one
  have hmul := mul_le_mul_of_nonneg_left hgrowth hκ0
  have hmul' := mul_le_mul_of_nonneg_right hκ.2 hΔ
  have hT : H * ‖y - w‖ ^ 3 ≤ 60 * (p.m : ℝ) ^ 3 * Δ := by
    rw [hidentity]
    nlinarith only [hmul, hmul']
  have hcurv := snapshot_curvature_bound (x := w) hf hf0 htaylor hLip (by simpa only [hw] using hΔ) hy
    (by positivity : 0 ≤ 1 / (8 * (p.m : ℝ)))
    (show 2 * (1 / (8 * (p.m : ℝ))) ≤ 1 by
      have ht : (2 : ℝ) / (8 * (p.m : ℝ)) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
      simpa only [mul_one_div] using ht)
  have hQ : ⟪y - w, A y (y - w)⟫ ≤ 192 * (p.m : ℝ) ^ 2 * Δ :=
    scaled_snapshot_curvature hm0 hΔ hT (by nlinarith only [hcurv])
  have hD3 : ‖y - w‖ ^ 3 ≤ 60 * (p.m : ℝ) ^ 3 * r ^ 3 := by
    rw [← hcube] at hT
    nlinarith only [hT, hH]
  have hD := snapshot_radius (norm_nonneg (y - w)) hm0.le hr hD3
  have hD2 := pow_le_pow_left₀ (norm_nonneg (y - w)) hD 2
  have hscaled := mul_le_mul_of_nonneg_left hD2 (mul_nonneg hH.le hr)
  have hδD : (H * r) * ‖y - w‖ ^ 2 ≤ 16 * (p.m : ℝ) ^ 2 * Δ := by
    rw [← hcube]
    nlinarith only [hscaled]
  have hj : 1 ≤ (depth p : ℝ) + 1 := by have hn := Nat.cast_nonneg (α := ℝ) (depth p); linarith
  have hb := snapshot_metric_bound hj hΔ hQ hδD
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  nlinarith only [hb]

lemma sublevel_metric_bound {p : Params} {f : p.E → ℝ} {g : p.E → p.E}
    {A : p.E → p.E →L[ℝ] p.E} {γ H r Δ : ℝ} {w y x : p.E}
    (hf : ∀ u, HasGradientAt f (g u) u) (hg : ∀ u, HasFDerivAt g (A u) u)
    (hLip : ∀ u v, ‖A u - A v‖ ≤ H * ‖u - v‖) (hA : ∀ d, 0 ≤ ⟪d, A w d⟫)
    (hγ : 0 < γ) (hr : 0 ≤ r) (hΔ : 0 ≤ Δ) (hidentity : H = γ * condition p)
    (hcube : H * r ^ 3 = Δ)
    (hφy : shifted p f (g w) w y ≤ Δ) (hφx : shifted p f (g w) w x ≤ 3 * Δ)
    (hgy : γ * ‖y - w‖ ^ 3 / 12 ≤ Δ) (hgx : γ * ‖x - w‖ ^ 3 / 12 ≤ 3 * Δ) :
    ⟪x - y, ((32 * ((depth p : ℝ) + 1)) • A y +
      (4096 * ((depth p : ℝ) + 1) ^ 2 * H * r) • ContinuousLinearMap.id ℝ p.E) (x - y)⟫ ≤
      153000 * ((depth p : ℝ) + 1) ^ 2 * condition p ^ 3 * Δ := by
  have hκ2 : 2 ≤ condition p := by
    have hn : 0 ≤ (p.m : ℝ) ^ 3 := by positivity
    dsimp [condition]
    linarith
  have hκ1 : 1 ≤ condition p := by linarith
  have hκ0 : 0 ≤ condition p := by linarith
  have hH : 0 ≤ H := by rw [hidentity]; positivity
  have hxnorm := mul_le_mul_of_nonneg_left hgx hκ0
  have hynorm := mul_le_mul_of_nonneg_left hgy hκ0
  have hx3 : H * ‖x - w‖ ^ 3 ≤ 36 * condition p * Δ := by rw [hidentity]; nlinarith only [hxnorm]
  have hy3 : H * ‖y - w‖ ^ 3 ≤ 12 * condition p * Δ := by rw [hidentity]; nlinarith only [hynorm]
  have hQx := shifted_quadratic_bound hf hg hLip w x
  have hQy := shifted_quadratic_bound hf hg hLip w y
  have hQw := CurvatureMetric.quadratic_sub_le (A w) hA (x - w) (y - w)
  have he : (x - w) - (y - w) = x - y := by abel
  rw [he] at hQw
  have hQw' : ⟪x - y, A w (x - y)⟫ ≤ 16 * Δ + 32 * condition p * Δ := by
    nlinarith only [hQw, hQx, hQy, hφx, hφy, hx3, hy3]
  have hd := sublevel_distance hγ hr hidentity (by simpa only [hcube] using hgy)
    (by simpa only [hcube] using hgx)
  have hy' := growth_distance_bound (norm_nonneg (y - w)) hγ hκ2 hr
    (show γ * ‖y - w‖ ^ 3 / 12 ≤ 3 * (γ * condition p * r ^ 3) by rw [← hidentity, hcube]; linarith)
  have hd2 := pow_le_pow_left₀ (norm_nonneg (x - y)) hd 2
  have hdy := mul_le_mul_of_nonneg_left hy' hH
  have hprod := mul_le_mul hdy hd2 (sq_nonneg ‖x - y‖) (by positivity : 0 ≤ H * (3 * condition p * r))
  have hnoise : H * ‖y - w‖ * ‖x - y‖ ^ 2 ≤ 108 * condition p ^ 3 * Δ := by
    rw [← hcube]
    nlinarith only [hprod]
  have hpert := CurvatureMetric.quadratic_perturbation (A w) (A y) (x - y)
  have hlip := mul_le_mul_of_nonneg_right (hLip y w) (sq_nonneg ‖x - y‖)
  have hκ13 : 1 ≤ condition p ^ 3 := one_le_pow₀ hκ1
  have hκ23 : condition p ^ 2 ≤ condition p ^ 3 := pow_le_pow_right₀ hκ1 (by norm_num)
  have hκ03 : condition p ≤ condition p ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hκ1 (by norm_num : 1 ≤ 3)
  have hΔ1 := mul_le_mul_of_nonneg_right hκ13 hΔ
  have hΔκ := mul_le_mul_of_nonneg_right hκ03 hΔ
  have hQ : ⟪x - y, A y (x - y)⟫ ≤ 160 * condition p ^ 3 * Δ := by
    nlinarith only [hQw', hpert, hlip, hnoise, hΔ1, hΔκ, hΔ]
  have hiso := mul_le_mul_of_nonneg_left hd2 (mul_nonneg hH hr)
  have hiso' : (H * r) * ‖x - y‖ ^ 2 ≤ 36 * condition p ^ 2 * Δ := by
    rw [← hcube]
    nlinarith only [hiso]
  have hΔκ2 := mul_le_mul_of_nonneg_right hκ23 hΔ
  have hiso'' : (H * r) * ‖x - y‖ ^ 2 ≤ 36 * condition p ^ 3 * Δ := by nlinarith only [hiso', hΔκ2]
  have hj : 1 ≤ (depth p : ℝ) + 1 := by have hn := Nat.cast_nonneg (α := ℝ) (depth p); linarith
  have hqscaled := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 32 * ((depth p : ℝ) + 1))
  have hiscaled := mul_le_mul_of_nonneg_left hiso'' (by positivity : 0 ≤ 4096 * ((depth p : ℝ) + 1) ^ 2)
  have hjs := mul_nonneg (sub_nonneg.mpr hj) (by positivity : 0 ≤ ((depth p : ℝ) + 1) * condition p ^ 3 * Δ)
  have hn : 0 ≤ ((depth p : ℝ) + 1) ^ 2 * condition p ^ 3 * Δ := by positivity
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  nlinarith only [hqscaled, hiscaled, hjs, hn]

end LongTails.Proofs.CompositeExtrapolatedObjective
