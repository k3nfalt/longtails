import LongTails.Proofs.ZerothOrderSmoothing

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace LongTails.Proofs.WeightedSphericalMoments

open OracleTemplate.ZerothOrder

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0 : E) 1
local notation "Q" => (sphereLaw E : Measure S)

omit [NeZero d] in
lemma weighted_square_gradient {a : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt a (g x) x) (i : Fin d) (n : ℕ) (x : E) :
    HasGradientAt (fun y => a y ^ 2 * y i ^ (n + 1))
      ((2 * a x * x i ^ (n + 1)) • g x +
        ((n + 1 : ℕ) * a x ^ 2 * x i ^ n) • EuclideanSpace.single i (1 : ℝ)) x := by
  have he (y : E) : ⟪EuclideanSpace.single i (1 : ℝ), y⟫ = y i := by
    simp [PiLp.inner_apply]
  have hc : HasFDerivAt (fun y : E => y i)
      (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) x := by
    convert (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))).hasFDerivAt (x := x) using 1
    funext y
    exact (he y).symm
  have h := ((hg x).hasFDerivAt.pow 2).mul (hc.pow (n + 1))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext y
  simp [he]
  ring

lemma sphere_weighted_square_identity {a : E → ℝ} {g : E → E}
    (ha : Continuous a) (hg : Continuous g)
    (hd : ∀ x, HasGradientAt a (g x) x) (i : Fin d) (k : ℕ) :
    ((d : ℝ) + 2 * k) * (∫ u : S, a u ^ 2 * (u : E) i ^ (2 * k + 2) ∂Q) =
      (2 * (k : ℝ) + 1) * (∫ u : S, a u ^ 2 * (u : E) i ^ (2 * k) ∂Q) +
        2 * (∫ u : S, a u * (u : E) i ^ (2 * k + 1) *
          ((g u) i - (u : E) i * ⟪g u, (u : E)⟫) ∂Q) := by
  let f := fun x : E => a x ^ 2 * x i ^ (2 * k + 1)
  let G := fun x : E => (2 * a x * x i ^ (2 * k + 1)) • g x +
    ((2 * k + 1 : ℕ) * a x ^ 2 * x i ^ (2 * k)) • EuclideanSpace.single i (1 : ℝ)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hG : Continuous G := by dsimp [G]; fun_prop
  have h := sphere_tangential_integration_by_parts hf hG (weighted_square_gradient hd i (2 * k)) i
  have hi0 : Integrable (fun u : S => a u ^ 2 * (u : E) i ^ (2 * k)) Q :=
    sphere_integrable_continuous (f := fun x : E => a x ^ 2 * x i ^ (2 * k)) (by fun_prop)
  have hi2 : Integrable (fun u : S => a u ^ 2 * (u : E) i ^ (2 * k + 2)) Q :=
    sphere_integrable_continuous (f := fun x : E => a x ^ 2 * x i ^ (2 * k + 2)) (by fun_prop)
  have hic : Integrable (fun u : S => a u * (u : E) i ^ (2 * k + 1) *
      ((g u) i - (u : E) i * ⟪g u, (u : E)⟫)) Q :=
    sphere_integrable_continuous (f := fun x : E => a x * x i ^ (2 * k + 1) * ((g x) i - x i * ⟪g x, x⟫)) (by fun_prop)
  have he (u : S) : (G u) i - (u : E) i * ⟪G u, (u : E)⟫ =
      2 * (a u * (u : E) i ^ (2 * k + 1) *
        ((g u) i - (u : E) i * ⟪g u, (u : E)⟫)) +
      (2 * (k : ℝ) + 1) * (a u ^ 2 * (u : E) i ^ (2 * k)) -
      (2 * (k : ℝ) + 1) * (a u ^ 2 * (u : E) i ^ (2 * k + 2)) := by
    dsimp [G]
    simp [inner_add_left, inner_smul_left, PiLp.inner_apply, pow_add]
    ring
  have hf' (u : S) : (u : E) i * f u = a u ^ 2 * (u : E) i ^ (2 * k + 2) := by
    dsimp [f]
    simp only [pow_add, pow_one, pow_two]
    ring
  simp_rw [he, hf'] at h
  have hisum := (hic.const_mul 2).add (hi0.const_mul (2 * (k : ℝ) + 1))
  have hsub := integral_sub hisum (hi2.const_mul (2 * (k : ℝ) + 1))
  simp only [Pi.add_apply] at hsub
  rw [hsub,
    integral_add (hic.const_mul 2) (hi0.const_mul (2 * (k : ℝ) + 1)), integral_const_mul,
    integral_const_mul, integral_const_mul] at h
  nlinarith only [h]

omit [NeZero d] in
lemma weighted_young (c a t b : ℝ) (k : ℕ) :
    2 * c * (a * t ^ (2 * k + 1) * b) ≤
      c ^ 2 / 2 * (a ^ 2 * t ^ (2 * k + 2)) + 2 * (t ^ (2 * k) * b ^ 2) := by
  have he : t ^ (2 * k) = (t ^ k) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  simp only [pow_add, he, pow_one, pow_two]
  nlinarith only [sq_nonneg (c * a * t * t ^ k - 2 * t ^ k * b)]

lemma sphere_weighted_square_recurrence {a : E → ℝ} {g : E → E}
    (ha : Continuous a) (hg : Continuous g)
    (hd : ∀ x, HasGradientAt a (g x) x) (i : Fin d) (k : ℕ) :
    ((d : ℝ) + 2 * k) ^ 2 *
        (∫ u : S, a u ^ 2 * (u : E) i ^ (2 * k + 2) ∂Q) ≤
      2 * ((d : ℝ) + 2 * k) * (2 * (k : ℝ) + 1) *
        (∫ u : S, a u ^ 2 * (u : E) i ^ (2 * k) ∂Q) +
      4 * (∫ u : S, (u : E) i ^ (2 * k) *
        ((g u) i - (u : E) i * ⟪g u, (u : E)⟫) ^ 2 ∂Q) := by
  let c : ℝ := d + 2 * k
  have hi2 : Integrable (fun u : S => a u ^ 2 * (u : E) i ^ (2 * k + 2)) Q :=
    sphere_integrable_continuous (f := fun x : E => a x ^ 2 * x i ^ (2 * k + 2)) (by fun_prop)
  have hic : Integrable (fun u : S => a u * (u : E) i ^ (2 * k + 1) *
      ((g u) i - (u : E) i * ⟪g u, (u : E)⟫)) Q :=
    sphere_integrable_continuous (f := fun x : E => a x * x i ^ (2 * k + 1) *
      ((g x) i - x i * ⟪g x, x⟫)) (by fun_prop)
  have hib : Integrable (fun u : S => (u : E) i ^ (2 * k) *
      ((g u) i - (u : E) i * ⟪g u, (u : E)⟫) ^ 2) Q :=
    sphere_integrable_continuous (f := fun x : E => x i ^ (2 * k) *
      ((g x) i - x i * ⟪g x, x⟫) ^ 2) (by fun_prop)
  have hy := integral_mono (hic.const_mul (2 * c))
    ((hi2.const_mul (c ^ 2 / 2)).add (hib.const_mul 2))
    (fun u : S => weighted_young c (a u) ((u : E) i)
      ((g u) i - (u : E) i * ⟪g u, (u : E)⟫) k)
  simp only [Pi.add_apply] at hy
  rw [integral_add (hi2.const_mul (c ^ 2 / 2)) (hib.const_mul 2),
    integral_const_mul, integral_const_mul, integral_const_mul] at hy
  have he := sphere_weighted_square_identity ha hg hd i k
  have hm := congrArg (fun r : ℝ => c * r) he
  dsimp [c] at hy hm
  nlinarith only [hy, hm]

lemma sphere_even_moment_recurrence (i : Fin d) (k : ℕ) :
    ((d : ℝ) + 2 * k) * (∫ u : S, (u : E) i ^ (2 * k + 2) ∂Q) =
      (2 * (k : ℝ) + 1) * (∫ u : S, (u : E) i ^ (2 * k) ∂Q) := by
  have h := sphere_weighted_square_identity (a := fun _ => 1) (g := fun _ => 0)
    continuous_const continuous_const (fun x => hasGradientAt_const x 1) i k
  simpa using h

lemma sphere_even_moment_bound (i : Fin d) (k : ℕ) :
    (d : ℝ) ^ k * (∫ u : S, (u : E) i ^ (2 * k) ∂Q) ≤
      2 ^ k * (k.factorial : ℝ) := by
  let m := fun j : ℕ => ∫ u : S, (u : E) i ^ (2 * j) ∂Q
  have hm (j : ℕ) : 0 ≤ m j := by
    apply integral_nonneg
    intro u
    change 0 ≤ (u : E) i ^ (2 * j)
    rw [mul_comm 2 j, pow_mul]
    exact sq_nonneg _
  have hs (j : ℕ) : (d : ℝ) * m (j + 1) ≤ 2 * (j + 1 : ℝ) * m j := by
    have hr := sphere_even_moment_recurrence i j
    have he : 2 * (j + 1) = 2 * j + 2 := by omega
    change (d : ℝ) * (∫ u : S, (u : E) i ^ (2 * (j + 1)) ∂Q) ≤ _
    rw [he]
    have hn := hm (j + 1)
    dsimp [m] at hn
    rw [he] at hn
    dsimp [m] at hm ⊢
    nlinarith [hm j, mul_nonneg (Nat.cast_nonneg j) hn]
  change (d : ℝ) ^ k * m k ≤ _
  induction k with
  | zero => simp [m]
  | succ k ih =>
    calc
      (d : ℝ) ^ (k + 1) * m (k + 1) = (d : ℝ) ^ k * ((d : ℝ) * m (k + 1)) := by ring
      _ ≤ (d : ℝ) ^ k * (2 * (k + 1 : ℝ) * m k) :=
        mul_le_mul_of_nonneg_left (hs k) (by positivity)
      _ = (2 * (k + 1 : ℝ)) * ((d : ℝ) ^ k * m k) := by ring
      _ ≤ (2 * (k + 1 : ℝ)) * (2 ^ k * (k.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = 2 ^ (k + 1) * ((k + 1).factorial : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
        ring

omit [NeZero d] in
lemma tangent_coordinate_square_le (u : S) (v : E) (i : Fin d) :
    (v i - (u : E) i * ⟪v, (u : E)⟫) ^ 2 ≤ ‖v‖ ^ 2 := by
  let e : E := EuclideanSpace.single i 1
  let w : E := e - (u : E) i • (u : E)
  have hu : ‖(u : E)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using u.property
  have he : ‖e‖ = 1 := by simp [e]
  have heu : ⟪e, (u : E)⟫ = (u : E) i := by simp [e, PiLp.inner_apply]
  have hw : ‖w‖ ^ 2 ≤ 1 := by
    dsimp [w]
    rw [norm_sub_sq_real, he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hu,
      real_inner_smul_right, heu]
    nlinarith [sq_nonneg ((u : E) i)]
  have hi : ⟪v, w⟫ = v i - (u : E) i * ⟪v, (u : E)⟫ := by
    dsimp [w]
    rw [inner_sub_right, real_inner_smul_right]
    congr 1
    simp [e, PiLp.inner_apply]
  have hc := norm_inner_le_norm (𝕜 := ℝ) v w
  rw [Real.norm_eq_abs] at hc
  have hc2 := mul_self_le_mul_self (abs_nonneg ⟪v, w⟫) hc
  rw [← pow_two, ← pow_two, sq_abs, mul_pow] at hc2
  rw [← hi]
  nlinarith [mul_le_mul_of_nonneg_left hw (sq_nonneg ‖v‖)]

lemma relax_weighted_recurrence {c D q a b e : ℝ} (hD : 0 < D) (hc : D ≤ c)
    (hq : 0 ≤ q) (hb : 0 ≤ b) (he : 0 ≤ e)
    (h : c ^ 2 * a ≤ 2 * c * q * b + 4 * e) :
    D ^ 2 * a ≤ 2 * D * q * b + 4 * e := by
  have hc0 : 0 < c := lt_of_lt_of_le hD hc
  have ha : a ≤ 2 * q * b / c + 4 * e / c ^ 2 := by
    calc
      a ≤ (2 * c * q * b + 4 * e) / c ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos hc0)).mpr (by nlinarith only [h])
      _ = _ := by field_simp
  have hh : 2 * q * b / c + 4 * e / c ^ 2 ≤
      2 * q * b / D + 4 * e / D ^ 2 := by
    gcongr
  have hh' := ha.trans hh
  have hm := mul_le_mul_of_nonneg_left hh' (sq_nonneg D)
  convert hm using 1
  field_simp [ne_of_gt hD]

lemma factorial_moment_growth {Y : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h0 : Y 0 ≤ 5 * B)
    (hs : ∀ n, Y (n + 1) ≤ 2 * (2 * (n : ℝ) + 1) * Y n +
      4 * B * 2 ^ n * (n.factorial : ℝ)) (k : ℕ) :
    Y k ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B := by
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have hp : (2 : ℝ) ^ k ≤ 8 ^ k := by gcongr; norm_num
    have h1 := mul_le_mul_of_nonneg_left ih
      (show 0 ≤ 2 * (2 * (k : ℝ) + 1) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hp
      (show 0 ≤ 4 * B * (k.factorial : ℝ) by positivity)
    have h3 : 0 ≤ (20 * (k : ℝ) + 26) * 8 ^ k * (k.factorial : ℝ) * B := by positivity
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    nlinarith [hs k]

lemma weighted_sequence_moment_bound {X m : ℕ → ℝ} {D B : ℝ}
    (hD : 0 ≤ D) (hB : 0 ≤ B) (h0 : D * X 0 ≤ 5 * B)
    (hm : ∀ n, D ^ n * m n ≤ 2 ^ n * (n.factorial : ℝ))
    (hs : ∀ n, D ^ 2 * X (n + 1) ≤
      2 * D * (2 * (n : ℝ) + 1) * X n + 4 * B * m n) (k : ℕ) :
    D ^ (k + 1) * X k ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B := by
  apply factorial_moment_growth hB (by simpa using h0) _ k
  intro n
  have h1 := mul_le_mul_of_nonneg_left (hs n) (pow_nonneg hD n)
  have h2 := mul_le_mul_of_nonneg_left (hm n) (show 0 ≤ 4 * B by positivity)
  simp only [pow_succ]
  nlinarith only [h1, h2]

end LongTails.Proofs.WeightedSphericalMoments
