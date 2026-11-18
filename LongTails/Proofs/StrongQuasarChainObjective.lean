import LongTails.Proofs.StrongQuasarChainScalar
import Mathlib.Analysis.InnerProductSpace.Calculus
import LongTails.Proofs.FiniteSumNondualLowerComponents

open scoped BigOperators RealInnerProductSpace
open Finset

namespace LongTails.Proofs.StrongQuasarChainObjective

open LongTails.Proofs.StrongQuasarChainBlock LongTails.Proofs.StrongQuasarChainScalar
open LongTails.Proofs.FiniteSumNondualLowerComponents

structure Shape where
  k : ℕ
  m : ℕ
  μ : ℝ
  θ : ℝ
  ρ : ℝ

namespace Shape

variable (S : Shape)

noncomputable def q : ℝ := 1 - 1 / (S.m : ℝ)

noncomputable def scale (p : Fin (S.k + 1)) : ℝ := S.q ^ (p.val + 1)

noncomputable def force (p : Fin (S.k + 1)) : ℝ :=
  if p.val < S.k then S.q ^ p.val / (S.m : ℝ) ^ 2 else S.q ^ S.k / S.m - S.θ

noncomputable def beta (p : Fin (S.k + 1)) : ℝ :=
  (S.force p - S.μ * S.scale p) / (S.scale p - S.ρ)

structure Valid : Prop where
  hm : 16 ≤ S.m
  hμ0 : 0 < S.μ
  hμ : S.μ ≤ 1 / 100
  hθ0 : 0 < S.θ
  hθ : 4 * S.m * S.θ ≤ S.q ^ S.k
  hρ0 : 0 < S.ρ
  hρθ : S.ρ ≤ S.θ
  hρμ : S.μ * (S.m : ℝ) ^ 2 * S.ρ ≤ S.q ^ S.k

end Shape

noncomputable def linkProfile (θ : ℝ) {k : ℕ} (j : Fin (k + 1)) (t : ℝ) : ℝ :=
  if j.val = 0 then deadEnergy θ (1 - t) else deadEnergy θ t

noncomputable def linkSlope (θ : ℝ) {k : ℕ} (j : Fin (k + 1)) (t : ℝ) : ℝ :=
  if j.val = 0 then -deadSlope θ (1 - t) else deadSlope θ t

noncomputable def coordProfile (S : Shape) (p : Fin (S.k + 1)) (t : ℝ) : ℝ :=
  S.beta p * deadEnergy S.ρ t + S.μ * S.scale p ^ 2 * bump (t / S.scale p)

noncomputable def coordSlope (S : Shape) (p : Fin (S.k + 1)) (t : ℝ) : ℝ :=
  S.beta p * deadSlope S.ρ t + S.μ * S.scale p * bumpSlope (t / S.scale p)

noncomputable def objective (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  S.μ / 2 * ‖x‖ ^ 2 + separableEnergy (linkProfile S.θ) (selectedChain π x) +
    separableEnergy (coordProfile S) (coordinateMap π x)

noncomputable def field (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  S.μ • x + (selectedChain π).adjoint (separableSlope (linkSlope S.θ) (selectedChain π x)) +
    (coordinateMap π).adjoint (separableSlope (coordSlope S) (coordinateMap π x))

section valid

variable {S : Shape} (V : S.Valid)
include V

lemma Shape.Valid.mR : (16 : ℝ) ≤ S.m := by exact_mod_cast V.hm

lemma Shape.Valid.q_pos : 0 < S.q := by
  have hm := V.mR
  unfold Shape.q
  have : 1 / (S.m : ℝ) ≤ 1 / 16 := one_div_le_one_div_of_le (by norm_num) hm
  linarith

lemma Shape.Valid.q_lt_one : S.q < 1 := by
  have hm := V.mR
  unfold Shape.q
  have : 0 < 1 / (S.m : ℝ) := by positivity
  linarith

lemma Shape.Valid.q_ge : 15 / 16 ≤ S.q := by
  have hm := V.mR
  unfold Shape.q
  have : 1 / (S.m : ℝ) ≤ 1 / 16 := one_div_le_one_div_of_le (by norm_num) hm
  linarith

lemma Shape.Valid.pow_anti {i j : ℕ} (h : i ≤ j) : S.q ^ j ≤ S.q ^ i :=
  pow_le_pow_of_le_one V.q_pos.le V.q_lt_one.le h

lemma Shape.Valid.scale_ge (p : Fin (S.k + 1)) : 15 / 16 * S.q ^ S.k ≤ S.scale p := by
  unfold Shape.scale
  have h1 : S.q ^ (S.k + 1) ≤ S.q ^ (p.val + 1) := V.pow_anti (by omega)
  have h2 : S.q ^ (S.k + 1) = S.q ^ S.k * S.q := pow_succ _ _
  have h3 := V.q_ge
  have h4 : 0 < S.q ^ S.k := pow_pos V.q_pos _
  nlinarith

lemma Shape.Valid.theta_small : S.θ ≤ S.q ^ S.k / 64 := by
  have hm := V.mR
  have h := V.hθ
  have h0 := V.hθ0
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

lemma Shape.Valid.scale_sub_pos (p : Fin (S.k + 1)) :
    59 / 64 * S.q ^ S.k ≤ S.scale p - S.ρ := by
  have h1 := V.scale_ge p
  have h2 := V.theta_small
  have h3 := V.hρθ
  linarith

lemma Shape.Valid.force_pos (p : Fin (S.k + 1)) : S.q ^ S.k / (S.m : ℝ) ^ 2 ≤ S.force p := by
  unfold Shape.force
  have hm := V.mR
  have hq := pow_pos V.q_pos S.k
  split_ifs with h
  · apply div_le_div_of_nonneg_right (V.pow_anti h.le) (by positivity)
  · have hθ := V.hθ
    have : S.θ ≤ S.q ^ S.k / (4 * S.m) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2 : S.q ^ S.k / (S.m : ℝ) ^ 2 ≤ S.q ^ S.k / (4 * S.m) := by
      apply div_le_div_of_nonneg_left hq.le (by positivity)
      nlinarith
    have h3 : S.q ^ S.k / (S.m : ℝ) - S.q ^ S.k / (4 * S.m) = 3 * (S.q ^ S.k / (4 * S.m)) := by
      field_simp; ring
    have h4 : 0 ≤ S.q ^ S.k / (4 * S.m) := by positivity
    linarith

lemma Shape.Valid.force_le (p : Fin (S.k + 1)) : S.force p ≤ S.q ^ p.val / 16 := by
  unfold Shape.force
  have hm := V.mR
  have hq := pow_pos V.q_pos p.val
  split_ifs with h
  · apply div_le_div_of_nonneg_left hq.le (by norm_num)
    nlinarith
  · have hp : p.val = S.k := by omega
    rw [show S.q ^ S.k = S.q ^ p.val by rw [hp]]
    have h0 := V.hθ0
    have : S.q ^ p.val / (S.m : ℝ) ≤ S.q ^ p.val / 16 :=
      div_le_div_of_nonneg_left hq.le (by norm_num) hm
    linarith

lemma Shape.Valid.scale_sub_ge (p : Fin (S.k + 1)) : S.q ^ p.val / 16 ≤ S.scale p - S.ρ := by
  unfold Shape.scale
  have h1 : S.q ^ (p.val + 1) = S.q ^ p.val * S.q := pow_succ _ _
  have h2 := V.q_ge
  have h3 : S.q ^ S.k ≤ S.q ^ p.val := V.pow_anti (by omega)
  have h4 := V.theta_small
  have h5 := V.hρθ
  have h6 : 0 < S.q ^ p.val := pow_pos V.q_pos _
  nlinarith

lemma Shape.Valid.beta_ge (p : Fin (S.k + 1)) : -S.μ ≤ S.beta p := by
  unfold Shape.beta
  have hd := V.scale_sub_pos p
  have hq := pow_pos V.q_pos S.k
  have hpos : 0 < S.scale p - S.ρ := by nlinarith
  rw [le_div_iff₀ hpos]
  have hf := V.force_pos p
  have hρμ := V.hρμ
  have hm := V.mR
  have hμρ : S.μ * S.ρ ≤ S.q ^ S.k / (S.m : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  nlinarith

lemma Shape.Valid.beta_le (p : Fin (S.k + 1)) : S.beta p ≤ 1 := by
  unfold Shape.beta
  have hd := V.scale_sub_ge p
  have h6 : 0 < S.q ^ p.val := pow_pos V.q_pos _
  have hpos : 0 < S.scale p - S.ρ := by linarith
  rw [div_le_iff₀ hpos, one_mul]
  have hf := V.force_le p
  have ha : 0 ≤ S.μ * S.scale p := by
    have := V.hμ0
    unfold Shape.scale
    have := pow_pos V.q_pos (p.val + 1)
    positivity
  linarith

lemma Shape.Valid.scale_pos (p : Fin (S.k + 1)) : 0 < S.scale p := by
  unfold Shape.scale
  exact pow_pos V.q_pos _

lemma Shape.Valid.link_model (j : Fin (S.k + 1)) (u v : ℝ) :
    0 ≤ linkProfile S.θ j v - linkProfile S.θ j u - linkSlope S.θ j u * (v - u) ∧
      linkProfile S.θ j v - linkProfile S.θ j u - linkSlope S.θ j u * (v - u) ≤ (v - u) ^ 2 := by
  unfold linkProfile linkSlope
  have hθ := V.hθ0.le
  split_ifs
  · have h := dead_model S.θ (1 - u) (1 - v) hθ
    have he : (1 - v) - (1 - u) = -(v - u) := by ring
    rw [he] at h
    constructor <;> nlinarith [h.1, h.2, sq_nonneg (v - u)]
  · have h := dead_model S.θ u v hθ
    constructor <;> nlinarith [h.1, h.2, sq_nonneg (v - u)]

lemma Shape.Valid.link_lipschitz (j : Fin (S.k + 1)) (u v : ℝ) :
    |linkSlope S.θ j u - linkSlope S.θ j v| ≤ 2 * |u - v| := by
  unfold linkSlope
  have hθ := V.hθ0.le
  split_ifs
  · have h := dead_lipschitz S.θ (1 - u) (1 - v) hθ
    have he : -deadSlope S.θ (1 - u) - -deadSlope S.θ (1 - v) =
        -(deadSlope S.θ (1 - u) - deadSlope S.θ (1 - v)) := by ring
    rw [he, abs_neg]
    have he2 : (1 - u) - (1 - v) = -(u - v) := by ring
    rw [he2, abs_neg] at h
    linarith [abs_nonneg (u - v)]
  · have h := dead_lipschitz S.θ u v hθ
    linarith [abs_nonneg (u - v)]

lemma Shape.Valid.coord_model (p : Fin (S.k + 1)) (u v : ℝ) :
    |coordProfile S p v - coordProfile S p u - coordSlope S p u * (v - u)| ≤ (v - u) ^ 2 := by
  unfold coordProfile coordSlope
  have hρ := V.hρ0.le
  have hd := dead_model S.ρ u v hρ
  have ha := V.scale_pos p
  have hb := bump_remainder (u / S.scale p) (v / S.scale p)
  have hβ1 := V.beta_le p
  have hβ0 := V.beta_ge p
  have hμ0 := V.hμ0
  have hμ := V.hμ
  have he : S.beta p * deadEnergy S.ρ v + S.μ * S.scale p ^ 2 * bump (v / S.scale p) -
      (S.beta p * deadEnergy S.ρ u + S.μ * S.scale p ^ 2 * bump (u / S.scale p)) -
      (S.beta p * deadSlope S.ρ u + S.μ * S.scale p * bumpSlope (u / S.scale p)) * (v - u) =
      S.beta p * (deadEnergy S.ρ v - deadEnergy S.ρ u - deadSlope S.ρ u * (v - u)) +
      S.μ * S.scale p ^ 2 * (bump (v / S.scale p) - bump (u / S.scale p) -
        bumpSlope (u / S.scale p) * (v / S.scale p - u / S.scale p)) := by
    field_simp
    ring
  rw [he]
  have hsq : (v / S.scale p - u / S.scale p) ^ 2 = (v - u) ^ 2 / S.scale p ^ 2 := by
    field_simp
  rw [hsq] at hb
  have h1 : |S.beta p * (deadEnergy S.ρ v - deadEnergy S.ρ u - deadSlope S.ρ u * (v - u))| ≤
      (v - u) ^ 2 / 2 := by
    rw [abs_mul, abs_of_nonneg hd.1]
    have : |S.beta p| ≤ 1 := abs_le.mpr ⟨by linarith, hβ1⟩
    nlinarith [hd.2, abs_nonneg (S.beta p)]
  have h2 : |S.μ * S.scale p ^ 2 * (bump (v / S.scale p) - bump (u / S.scale p) -
        bumpSlope (u / S.scale p) * (v / S.scale p - u / S.scale p))| ≤ (v - u) ^ 2 / 10 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hs2 : 0 < S.scale p ^ 2 := by positivity
    have : S.μ * S.scale p ^ 2 * (10 * ((v - u) ^ 2 / S.scale p ^ 2)) = 10 * S.μ * (v - u) ^ 2 := by
      field_simp
    calc S.μ * S.scale p ^ 2 * |bump (v / S.scale p) - bump (u / S.scale p) -
          bumpSlope (u / S.scale p) * (v / S.scale p - u / S.scale p)|
        ≤ S.μ * S.scale p ^ 2 * (10 * ((v - u) ^ 2 / S.scale p ^ 2)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 10 * S.μ * (v - u) ^ 2 := this
      _ ≤ (v - u) ^ 2 / 10 := by nlinarith [sq_nonneg (v - u)]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ (v - u) ^ 2 / 2 + (v - u) ^ 2 / 10 := add_le_add h1 h2
    _ ≤ (v - u) ^ 2 := by nlinarith [sq_nonneg (v - u)]

lemma Shape.Valid.coord_lipschitz (p : Fin (S.k + 1)) (u v : ℝ) :
    |coordSlope S p u - coordSlope S p v| ≤ 2 * |u - v| := by
  unfold coordSlope
  have hρ := V.hρ0.le
  have ha := V.scale_pos p
  have hβ1 := V.beta_le p
  have hβ0 := V.beta_ge p
  have hμ0 := V.hμ0
  have hμ := V.hμ
  have hd := dead_lipschitz S.ρ u v hρ
  have hb := bumpSlope_lipschitz (u / S.scale p) (v / S.scale p)
  have hdiv : |u / S.scale p - v / S.scale p| = |u - v| / S.scale p := by
    rw [← sub_div, abs_div, abs_of_pos ha]
  rw [hdiv] at hb
  have he : S.beta p * deadSlope S.ρ u + S.μ * S.scale p * bumpSlope (u / S.scale p) -
      (S.beta p * deadSlope S.ρ v + S.μ * S.scale p * bumpSlope (v / S.scale p)) =
      S.beta p * (deadSlope S.ρ u - deadSlope S.ρ v) +
      S.μ * S.scale p * (bumpSlope (u / S.scale p) - bumpSlope (v / S.scale p)) := by ring
  rw [he]
  have h1 : |S.beta p * (deadSlope S.ρ u - deadSlope S.ρ v)| ≤ |u - v| := by
    rw [abs_mul]
    have : |S.beta p| ≤ 1 := abs_le.mpr ⟨by linarith, hβ1⟩
    nlinarith [abs_nonneg (deadSlope S.ρ u - deadSlope S.ρ v)]
  have h2 : |S.μ * S.scale p * (bumpSlope (u / S.scale p) - bumpSlope (v / S.scale p))| ≤
      19 * S.μ * |u - v| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc S.μ * S.scale p * |bumpSlope (u / S.scale p) - bumpSlope (v / S.scale p)|
        ≤ S.μ * S.scale p * (19 * (|u - v| / S.scale p)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 19 * S.μ * |u - v| := by field_simp
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ |u - v| + 19 * S.μ * |u - v| := add_le_add h1 h2
    _ ≤ 2 * |u - v| := by nlinarith [abs_nonneg (u - v)]

omit V in
lemma separable_model_abs {ι : Type*} [Fintype ι] (φ g : ι → ℝ → ℝ) (C : ℝ)
    (h : ∀ j x y, |φ j y - φ j x - g j x * (y - x)| ≤ C * (y - x) ^ 2)
    (x y : EuclideanSpace ℝ ι) :
    |separableEnergy φ y - separableEnergy φ x - ⟪separableSlope g x, y - x⟫| ≤
      C * ‖y - x‖ ^ 2 := by
  have he : separableEnergy φ y - separableEnergy φ x - ⟪separableSlope g x, y - x⟫ =
      ∑ j, (φ j (y j) - φ j (x j) - g j (x j) * (y j - x j)) := by
    simp [separableEnergy, separableSlope, PiLp.inner_apply, RCLike.inner_apply,
      Finset.sum_sub_distrib, mul_comm]
  rw [he, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  simpa using h j (x j) (y j)

omit V in
lemma separable_hasGradientAt_abs {ι : Type*} [Fintype ι] (φ g : ι → ℝ → ℝ) (C : ℝ)
    (h : ∀ j x y, |φ j y - φ j x - g j x * (y - x)| ≤ C * (y - x) ^ 2)
    (x : EuclideanSpace ℝ ι) :
    HasGradientAt (separableEnergy φ) (separableSlope g x) x := by
  rw [hasGradientAt_iff_isLittleO]
  have hb : (fun y => separableEnergy φ y - separableEnergy φ x -
      ⟪separableSlope g x, y - x⟫) =O[nhds x] (fun y => ‖y - x‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [] with y
    have hm := separable_model_abs φ g C h x y
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖y - x‖)]
    exact hm
  exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub x (by norm_num : 1 < 2))

omit V in
lemma composed_gradient_abs {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (φ g : κ → ℝ → ℝ) (C : ℝ)
    (h : ∀ j x y, |φ j y - φ j x - g j x * (y - x)| ≤ C * (y - x) ^ 2)
    (x : EuclideanSpace ℝ ι) :
    HasGradientAt (fun y => separableEnergy φ (A y)) (A.adjoint (separableSlope g (A x))) x := by
  have hd := (separable_hasGradientAt_abs φ g C h (A x)).hasFDerivAt.comp x A.hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · rfl
  · ext v
    exact A.adjoint_inner_left v (separableSlope g (A x))

omit V in
lemma quadratic_hasGradientAt {d : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (fun y : EuclideanSpace ℝ (Fin d) => c / 2 * ‖y‖ ^ 2) (c • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (c / 2) using 1
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, smul_apply, smul_eq_mul,
    innerSL_apply_apply, real_inner_smul_left, nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma Shape.Valid.objective_gradient {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : HasGradientAt (objective S π) (field S π x) x := by
  have h1 := quadratic_hasGradientAt S.μ x
  have h2 := composed_gradient_abs (selectedChain π) (linkProfile S.θ) (linkSlope S.θ) 1
    (fun j u v => by
      have hm := V.link_model j u v
      rw [abs_of_nonneg hm.1]; linarith [hm.2]) x
  have h3 := composed_gradient_abs (coordinateMap π) (coordProfile S) (coordSlope S) 1
    (fun j u v => by have := V.coord_model j u v; linarith) x
  rw [hasGradientAt_iff_hasFDerivAt] at h1 h2 h3 ⊢
  have e : objective S π = ((fun y => S.μ / 2 * ‖y‖ ^ 2) +
      fun y => separableEnergy (linkProfile S.θ) (selectedChain π y)) +
      fun y => separableEnergy (coordProfile S) (coordinateMap π y) := rfl
  rw [e]
  unfold field
  rw [map_add, map_add]
  exact (h1.add h2).add h3

omit V in
lemma coordinateMap_opNorm {d n : ℕ} (π : Fin n ↪ Fin d) : ‖coordinateMap π‖ ≤ 2 := by
  apply (coordinateMap π).opNorm_le_bound (by norm_num)
  intro x
  have h := coordinateMap_norm π x
  nlinarith [norm_nonneg x]

lemma Shape.Valid.field_lipschitz {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖field S π x - field S π y‖ ≤ 17 * ‖x - y‖ := by
  have h2 := composed_separable_lipschitz (selectedChain π) (linkSlope S.θ)
    (selectedChain_opNorm π) (fun j u v => V.link_lipschitz j u v) x y
  have h3 := composed_separable_lipschitz (coordinateMap π) (coordSlope S)
    (coordinateMap_opNorm π) (fun j u v => V.coord_lipschitz j u v) x y
  have he : field S π x - field S π y = S.μ • (x - y) +
      ((selectedChain π).adjoint (separableSlope (linkSlope S.θ) (selectedChain π x)) -
        (selectedChain π).adjoint (separableSlope (linkSlope S.θ) (selectedChain π y))) +
      ((coordinateMap π).adjoint (separableSlope (coordSlope S) (coordinateMap π x)) -
        (coordinateMap π).adjoint (separableSlope (coordSlope S) (coordinateMap π y))) := by
    unfold field
    rw [smul_sub]
    abel
  rw [he]
  have hμ := V.hμ
  have hμ0 := V.hμ0
  calc _ ≤ ‖S.μ • (x - y) +
        ((selectedChain π).adjoint (separableSlope (linkSlope S.θ) (selectedChain π x)) -
        (selectedChain π).adjoint (separableSlope (linkSlope S.θ) (selectedChain π y)))‖ +
        ‖(coordinateMap π).adjoint (separableSlope (coordSlope S) (coordinateMap π x)) -
        (coordinateMap π).adjoint (separableSlope (coordSlope S) (coordinateMap π y))‖ :=
        norm_add_le _ _
    _ ≤ (‖S.μ • (x - y)‖ +
        ‖(selectedChain π).adjoint (separableSlope (linkSlope S.θ) (selectedChain π x)) -
        (selectedChain π).adjoint (separableSlope (linkSlope S.θ) (selectedChain π y))‖) +
        ‖(coordinateMap π).adjoint (separableSlope (coordSlope S) (coordinateMap π x)) -
        (coordinateMap π).adjoint (separableSlope (coordSlope S) (coordinateMap π y))‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ (S.μ * ‖x - y‖ + 8 * ‖x - y‖) + 8 * ‖x - y‖ := by
        rw [norm_smul, Real.norm_of_nonneg hμ0.le]
        gcongr
    _ ≤ 17 * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]

end valid

noncomputable def xstar (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => ∑ p, if π p = j then S.scale p else 0)

lemma xstar_apply_pi (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) (p : Fin (S.k + 1)) :
    xstar S π (π p) = S.scale p := by
  change (∑ p', if π p' = π p then S.scale p' else 0) = S.scale p
  simp only [π.injective.eq_iff]
  rw [Finset.sum_ite_eq' Finset.univ p]
  simp

lemma xstar_inner (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) (w : EuclideanSpace ℝ (Fin d)) :
    ⟪xstar S π, w⟫ = ∑ p, S.scale p * w (π p) := by
  rw [PiLp.inner_apply]
  change ∑ j, inner ℝ (∑ p, if π p = j then S.scale p else 0) (w j) = _
  simp only [RCLike.inner_apply, conj_trivial]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_eq_single (π p)]
  · simp [mul_comm]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

lemma chain_norm_le {d n : ℕ} (π : Fin n ↪ Fin d) (w : EuclideanSpace ℝ (Fin d)) :
    ∑ p, w (π p) ^ 2 ≤ ‖w‖ ^ 2 := by
  have h := coordinateMap_norm π w
  have he : ‖coordinateMap π w‖ ^ 2 = ∑ p, w (π p) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; rfl
  rw [← he]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma separableEnergy_apply {ι : Type*} [Fintype ι] (φ : ι → ℝ → ℝ) (z : EuclideanSpace ℝ ι) :
    separableEnergy φ z = ∑ j, φ j (z j) := rfl

lemma adjoint_slope_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (g : κ → ℝ → ℝ)
    (z : EuclideanSpace ℝ κ) (v : EuclideanSpace ℝ ι) :
    ⟪A.adjoint (separableSlope g z), v⟫ = ∑ j, g j (z j) * A v j := by
  rw [ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply]
  simp [separableSlope, RCLike.inner_apply, mul_comm]

lemma coordinateMap_apply {d n : ℕ} (π : Fin n ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (p : Fin n) : coordinateMap π x p = x (π p) := rfl

lemma sum_Ioc_zero_eq_range (n : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Ioc 0 n, f i = ∑ p ∈ range n, f (p + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Ioc_succ_top (Nat.zero_le n), ih, sum_range_succ]

noncomputable def chainSeq (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ℕ → ℝ
  | 0 => 1
  | i + 1 => if h : i < S.k + 1 then x (π ⟨i, h⟩) else 0

lemma chainSeq_succ (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (p : Fin (S.k + 1)) :
    chainSeq S π x (p.val + 1) = x (π p) := by
  simp [chainSeq, p.isLt]

noncomputable def linkVar {d k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (c : Fin (k + 1)) : ℝ :=
  if c.val = 0 then 1 - selectedChain π x c else selectedChain π x c

lemma linkVar_eq {S : Shape} {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (c : Fin (S.k + 1)) :
    linkVar π x c = chainSeq S π x c.val - chainSeq S π x (c.val + 1) := by
  induction c using Fin.cases with
  | zero =>
    simp only [linkVar, Fin.val_zero, ↓reduceIte, selectedChain_apply_zero]
    simp [chainSeq]
  | succ j =>
    simp only [linkVar, Fin.val_succ, Nat.add_one_ne_zero, ↓reduceIte, selectedChain_apply_succ]
    have h1 : chainSeq S π x (j.val + 1) = x (π j.castSucc) := by
      have := chainSeq_succ S π x j.castSucc
      simpa using this
    have h2 : chainSeq S π x (j.val + 1 + 1) = x (π j.succ) := by
      have := chainSeq_succ S π x j.succ
      simpa using this
    rw [h1, h2]

lemma link_sum_eq {S : Shape} {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (F : ℕ → ℝ → ℝ) :
    ∑ c : Fin (S.k + 1), F c.val (linkVar π x c) =
      ∑ c ∈ range (S.k + 1), F c (chainSeq S π x c - chainSeq S π x (c + 1)) := by
  simp_rw [linkVar_eq π x]
  exact Fin.sum_univ_eq_sum_range (fun c => F c (chainSeq S π x c - chainSeq S π x (c + 1))) _

lemma coord_sum_eq {S : Shape} {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (G : ℕ → ℝ → ℝ) :
    ∑ p : Fin (S.k + 1), G p.val (x (π p)) =
      ∑ i ∈ Ioc 0 (S.k + 1), G (i - 1) (chainSeq S π x i) := by
  rw [sum_Ioc_zero_eq_range]
  simp_rw [← chainSeq_succ S π x]
  simpa using Fin.sum_univ_eq_sum_range (fun p => G p (chainSeq S π x (p + 1))) (S.k + 1)

lemma selectedChain_xstar_linkVar (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (c : Fin (S.k + 1)) : linkVar π (xstar S π) c = S.q ^ c.val - S.q ^ (c.val + 1) := by
  rw [linkVar_eq]
  rcases c with ⟨c, hc⟩
  simp only
  rcases c with _ | c
  · simp only [chainSeq, Nat.zero_lt_succ, ↓reduceDIte, pow_zero, zero_add, pow_one]
    rw [xstar_apply_pi]
    simp [Shape.scale]
  · have h1 : chainSeq S π (xstar S π) (c + 1) = S.q ^ (c + 1) := by
      simp only [chainSeq, show c < S.k + 1 by omega, ↓reduceDIte]
      rw [xstar_apply_pi]
      simp [Shape.scale]
    have h2 : chainSeq S π (xstar S π) (c + 1 + 1) = S.q ^ (c + 1 + 1) := by
      simp only [chainSeq, hc, ↓reduceDIte]
      rw [xstar_apply_pi]
      simp [Shape.scale]
    rw [h1, h2]

lemma link_piece (θ γ t ts : ℝ) (hθ : 0 ≤ θ) :
    γ * deadEnergy θ t + deadSlope θ t * (ts - t) ≤
      γ * deadEnergy θ ts - (1 - γ) * (deadBreg θ t ts + deadSlope θ ts * (t - ts)) := by
  have h := (dead_model θ t ts hθ).1
  unfold deadBreg
  nlinarith

lemma bump_one : bump 1 = 0 := by simp [bump]

lemma coord_piece (μ γ β ρ a Y : ℝ) (hμ : 0 < μ) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1) (hβ : -μ ≤ β)
    (hρ : 0 ≤ ρ) (ha : 0 < a) :
    γ * (β * deadEnergy ρ Y + μ * a ^ 2 * bump (Y / a)) +
        (β * deadSlope ρ Y + μ * a * bumpSlope (Y / a)) * (a - Y) - (1 - γ) * μ * (Y - a) ^ 2 ≤
      γ * (β * deadEnergy ρ a + μ * a ^ 2 * bump (a / a)) - (1 - γ) * β * deadSlope ρ a * (Y - a) -
        μ * (gain (Y / a) - γ) * (Y - a) ^ 2 := by
  rw [div_self ha.ne', bump_one]
  have m1 := dead_model ρ a Y hρ
  have m2 := dead_model ρ Y a hρ
  set B1 := deadEnergy ρ Y - deadEnergy ρ a - deadSlope ρ a * (Y - a) with hB1
  set B2 := deadEnergy ρ a - deadEnergy ρ Y - deadSlope ρ Y * (a - Y) with hB2
  have hb := (bump_bounds (Y / a)).2
  have hbv : (Y / a - 1) ^ 2 = (Y - a) ^ 2 / a ^ 2 := by field_simp
  rw [hbv] at hb
  have hbump : μ * a ^ 2 * bump (Y / a) ≤ μ * (Y - a) ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ μ * a ^ 2)
    have he : μ * a ^ 2 * ((Y - a) ^ 2 / a ^ 2 / 2) = μ * (Y - a) ^ 2 / 2 := by field_simp
    linarith
  have hslope : μ * a * bumpSlope (Y / a) * (a - Y) = -(μ * gain (Y / a) * (Y - a) ^ 2) := by
    unfold bumpSlope
    field_simp
    ring
  have hsq : (a - Y) ^ 2 = (Y - a) ^ 2 := by ring
  rw [hsq] at m2
  have hB : 0 ≤ (1 - γ) * B1 + B2 := by nlinarith [m1.1, m2.1]
  have hBu : (1 - γ) * B1 + B2 ≤ (2 - γ) * ((Y - a) ^ 2 / 2) := by nlinarith [m1.2, m2.2]
  have hβB : -(β * ((1 - γ) * B1 + B2)) ≤ μ * ((1 - γ) * B1 + B2) := by nlinarith
  have hgam : 0 ≤ γ * (μ * a ^ 2 * bump (Y / a)) := by
    have := (bump_bounds (Y / a)).1
    positivity
  have key : γ * (β * deadEnergy ρ Y) + β * deadSlope ρ Y * (a - Y) =
      γ * (β * deadEnergy ρ a) - (1 - γ) * β * deadSlope ρ a * (Y - a) -
        β * ((1 - γ) * B1 + B2) := by
    rw [hB1, hB2]; ring
  nlinarith

lemma abel_kkt (k : ℕ) (D F W : ℕ → ℝ) (hW : W 0 = 0)
    (hD : ∀ c < k, D (c + 1) - D c = -F c) (hk : D k = F k) :
    ∑ c ∈ range (k + 1), D c * (W c - W (c + 1)) + ∑ c ∈ range (k + 1), F c * W (c + 1) = 0 := by
  have h1 : ∑ c ∈ range (k + 1), D c * (W c - W (c + 1)) =
      ∑ c ∈ range (k + 1), D c * W c - ∑ c ∈ range (k + 1), D c * W (c + 1) := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro c _; ring
  have h2 : ∑ c ∈ range (k + 1), D c * W c = ∑ c ∈ range k, D (c + 1) * W (c + 1) := by
    rw [sum_range_succ', hW, mul_zero, add_zero]
  have h3 : ∑ c ∈ range (k + 1), D c * W (c + 1) =
      ∑ c ∈ range k, D c * W (c + 1) + D k * W (k + 1) := sum_range_succ _ _
  have h4 : ∑ c ∈ range k, D (c + 1) * W (c + 1) - ∑ c ∈ range k, D c * W (c + 1) =
      -∑ c ∈ range k, F c * W (c + 1) := by
    rw [← sum_sub_distrib, ← sum_neg_distrib]
    apply sum_congr rfl
    intro c hc
    have := hD c (mem_range.mp hc)
    have : D (c + 1) * W (c + 1) - D c * W (c + 1) = (D (c + 1) - D c) * W (c + 1) := by ring
    rw [this, hD c (mem_range.mp hc)]
    ring
  rw [h1, h2, h3, sum_range_succ (fun c => F c * W (c + 1)), hk]
  linarith

section sq

variable {S : Shape} (V : S.Valid)
include V

lemma Shape.Valid.regime {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 256)
    (hc : (42 * γ * S.m) ^ 2 * S.μ ≤ 1) : Regime S.m S.q S.μ γ S.θ :=
  ⟨V.hm, rfl, V.hμ0, V.hμ, hγ0, hγ, hc, V.hθ0.le⟩

lemma Shape.Valid.theta_seq (i : ℕ) (hi : i < S.k + 1) : 4 * S.m * S.θ ≤ S.q ^ i :=
  V.hθ.trans (V.pow_anti (by omega))

omit V in
lemma Shape.one_sub_q (S : Shape) : 1 - S.q = 1 / (S.m : ℝ) := by unfold Shape.q; ring

lemma Shape.Valid.link_star_slope (c : ℕ) (hc : c < S.k + 1) :
    deadSlope S.θ (S.q ^ c - S.q ^ (c + 1)) = S.q ^ c / S.m - S.θ := by
  have hg : S.q ^ c - S.q ^ (c + 1) = S.q ^ c / S.m := by
    rw [pow_succ]
    have : S.q ^ c - S.q ^ c * S.q = S.q ^ c * (1 - S.q) := by ring
    rw [this, S.one_sub_q]; ring
  have hm := V.mR
  have hθ := V.theta_seq c hc
  rw [hg, deadSlope_of_ge V.hθ0.le]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [V.hθ0]

lemma Shape.Valid.force_eq (p : Fin (S.k + 1)) :
    S.μ * S.scale p + S.beta p * deadSlope S.ρ (S.scale p) = S.force p := by
  have hd := V.scale_sub_ge p
  have hq : 0 < S.q ^ p.val := pow_pos V.q_pos _
  have hpos : 0 < S.scale p - S.ρ := by linarith
  rw [deadSlope_of_ge V.hρ0.le (by linarith)]
  unfold Shape.beta
  field_simp
  ring

omit V in
lemma objective_expand (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (y : EuclideanSpace ℝ (Fin d)) :
    objective S π y = S.μ / 2 * ‖y‖ ^ 2 +
      ∑ c, deadEnergy S.θ (linkVar π y c) + ∑ p, coordProfile S p (y (π p)) := by
  unfold objective
  rw [separableEnergy_apply, separableEnergy_apply]
  congr 2
  apply sum_congr rfl
  intro c _
  unfold linkProfile linkVar
  split_ifs <;> rfl

omit V in
lemma field_inner (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    ⟪field S π x, xstar S π - x⟫ = S.μ * ⟪x, xstar S π - x⟫ +
      ∑ c, deadSlope S.θ (linkVar π x c) * (linkVar π (xstar S π) c - linkVar π x c) +
      ∑ p, coordSlope S p (x (π p)) * (S.scale p - x (π p)) := by
  unfold field
  rw [inner_add_left, inner_add_left, real_inner_smul_left, adjoint_slope_inner,
    adjoint_slope_inner]
  congr 2
  · apply sum_congr rfl
    intro c _
    rw [map_sub]
    unfold linkSlope linkVar
    simp only [PiLp.sub_apply]
    split_ifs <;> ring
  · funext p
    rw [coordinateMap_apply, coordinateMap_apply, PiLp.sub_apply, xstar_apply_pi]

omit V in
lemma xstar_inner_sub (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    ⟪xstar S π, x - xstar S π⟫ = ∑ p, S.scale p * (x (π p) - S.scale p) := by
  rw [xstar_inner]
  apply sum_congr rfl
  intro p _
  rw [PiLp.sub_apply, xstar_apply_pi]

omit V in
lemma chain_norm_sub (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    ∑ p, (x (π p) - S.scale p) ^ 2 ≤ ‖x - xstar S π‖ ^ 2 := by
  have h := chain_norm_le π (x - xstar S π)
  simp only [PiLp.sub_apply, xstar_apply_pi] at h
  exact h

lemma Shape.Valid.kkt {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    ∑ c, deadSlope S.θ (linkVar π (xstar S π) c) * (linkVar π x c - linkVar π (xstar S π) c) +
      (S.μ * ∑ p, S.scale p * (x (π p) - S.scale p) +
        ∑ p, S.beta p * deadSlope S.ρ (S.scale p) * (x (π p) - S.scale p)) = 0 := by
  have e1 : ∑ c, deadSlope S.θ (linkVar π (xstar S π) c) *
      (linkVar π x c - linkVar π (xstar S π) c) =
      ∑ c ∈ range (S.k + 1), (S.q ^ c / S.m - S.θ) *
        ((chainSeq S π x c - S.q ^ c) - (chainSeq S π x (c + 1) - S.q ^ (c + 1))) := by
    have h0 : ∀ c : Fin (S.k + 1), deadSlope S.θ (linkVar π (xstar S π) c) *
        (linkVar π x c - linkVar π (xstar S π) c) =
        (fun c t => deadSlope S.θ (S.q ^ c - S.q ^ (c + 1)) * (t - (S.q ^ c - S.q ^ (c + 1))))
          c.val (linkVar π x c) := by
      intro c
      rw [selectedChain_xstar_linkVar S π c]
    rw [sum_congr rfl (fun c _ => h0 c), link_sum_eq π x
      (fun c t => deadSlope S.θ (S.q ^ c - S.q ^ (c + 1)) * (t - (S.q ^ c - S.q ^ (c + 1))))]
    apply sum_congr rfl
    intro c hc
    rw [V.link_star_slope c (mem_range.mp hc)]
    ring
  have e2 : S.μ * ∑ p, S.scale p * (x (π p) - S.scale p) +
      ∑ p, S.beta p * deadSlope S.ρ (S.scale p) * (x (π p) - S.scale p) =
      ∑ c ∈ range (S.k + 1), (if c < S.k then S.q ^ c / (S.m : ℝ) ^ 2 else S.q ^ S.k / S.m - S.θ) *
        (chainSeq S π x (c + 1) - S.q ^ (c + 1)) := by
    have h1 : ∀ p : Fin (S.k + 1),
        S.μ * (S.scale p * (x (π p) - S.scale p)) +
          S.beta p * deadSlope S.ρ (S.scale p) * (x (π p) - S.scale p) =
        (fun c t => (if c < S.k then S.q ^ c / (S.m : ℝ) ^ 2 else S.q ^ S.k / S.m - S.θ) *
          (t - S.q ^ (c + 1))) p.val (x (π p)) := by
      intro p
      have hf := V.force_eq p
      simp only
      have : S.μ * (S.scale p * (x (π p) - S.scale p)) +
          S.beta p * deadSlope S.ρ (S.scale p) * (x (π p) - S.scale p) =
          (S.μ * S.scale p + S.beta p * deadSlope S.ρ (S.scale p)) * (x (π p) - S.scale p) := by ring
      rw [this, hf]
      rfl
    rw [mul_sum, ← sum_add_distrib, sum_congr rfl (fun p _ => h1 p), coord_sum_eq π x
      (fun c t => (if c < S.k then S.q ^ c / (S.m : ℝ) ^ 2 else S.q ^ S.k / S.m - S.θ) *
          (t - S.q ^ (c + 1))), sum_Ioc_zero_eq_range]
    apply sum_congr rfl
    intro c _
    simp only [Nat.add_sub_cancel]
  rw [e1, e2]
  apply abel_kkt S.k (fun c => S.q ^ c / S.m - S.θ)
    (fun c => if c < S.k then S.q ^ c / (S.m : ℝ) ^ 2 else S.q ^ S.k / S.m - S.θ)
    (fun c => chainSeq S π x c - S.q ^ c)
  · simp [chainSeq]
  · intro c hc
    simp only [hc, ↓reduceIte]
    have hm := V.mR
    have hm0 : (S.m : ℝ) ≠ 0 := by linarith
    rw [pow_succ]
    generalize S.q ^ c = t
    unfold Shape.q
    field_simp
    ring
  · simp

theorem Shape.Valid.strongQuasar {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 256) (hc : (42 * γ * S.m) ^ 2 * S.μ ≤ 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    γ * objective S π x + ⟪field S π x, xstar S π - x⟫ +
        γ * S.μ / 2 * ‖xstar S π - x‖ ^ 2 ≤ γ * objective S π (xstar S π) := by
  classical
  set xs := xstar S π with hxs
  have R := V.regime hγ0 hγ hc
  have hμ0 := V.hμ0
  have hγ1 : γ ≤ 1 := by linarith
  have hxsp : ∀ p, xs (π p) = S.scale p := fun p => xstar_apply_pi S π p
  have hL : ∀ c, γ * deadEnergy S.θ (linkVar π x c) +
      deadSlope S.θ (linkVar π x c) * (linkVar π xs c - linkVar π x c) ≤
      γ * deadEnergy S.θ (linkVar π xs c) - (1 - γ) * deadBreg S.θ (linkVar π x c) (linkVar π xs c) -
        (1 - γ) * (deadSlope S.θ (linkVar π xs c) * (linkVar π x c - linkVar π xs c)) := by
    intro c
    have := link_piece S.θ γ (linkVar π x c) (linkVar π xs c) V.hθ0.le
    linarith
  have hC : ∀ p, γ * coordProfile S p (x (π p)) +
      coordSlope S p (x (π p)) * (S.scale p - x (π p)) - (1 - γ) * S.μ * (x (π p) - S.scale p) ^ 2 ≤
      γ * coordProfile S p (S.scale p) -
        (1 - γ) * (S.beta p * deadSlope S.ρ (S.scale p) * (x (π p) - S.scale p)) -
        S.μ * (gain (x (π p) / S.scale p) - γ) * (x (π p) - S.scale p) ^ 2 := by
    intro p
    have h := coord_piece S.μ γ (S.beta p) S.ρ (S.scale p) (x (π p)) hμ0 hγ0 hγ1 (V.beta_ge p)
      V.hρ0.le (V.scale_pos p)
    unfold coordProfile coordSlope
    linarith
  have hLs := sum_le_sum (fun c (_ : c ∈ (univ : Finset (Fin (S.k + 1)))) => hL c)
  have hCs := sum_le_sum (fun p (_ : p ∈ (univ : Finset (Fin (S.k + 1)))) => hC p)
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum] at hLs hCs
  have hquad : γ * (S.μ / 2 * ‖x‖ ^ 2) + S.μ * ⟪x, xs - x⟫ + γ * S.μ / 2 * ‖xs - x‖ ^ 2 =
      γ * (S.μ / 2 * ‖xs‖ ^ 2) - (1 - γ) * S.μ * ⟪xs, x - xs⟫ -
        (1 - γ) * S.μ * ‖x - xs‖ ^ 2 := by
    have h1 := norm_sub_sq_real x xs
    have h2 : ‖xs - x‖ = ‖x - xs‖ := norm_sub_rev _ _
    rw [h2, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, h1, real_inner_comm xs x]
    ring
  have hinner := xstar_inner_sub S π x
  have hnorm := chain_norm_sub S π x
  have hkkt := V.kkt π x
  have hchain := R.chain_nonneg (chainSeq S π x) (S.k + 1) rfl
    (fun i hi => V.theta_seq i hi)
  have hb1 : ∑ c, deadBreg S.θ (linkVar π x c) (linkVar π xs c) =
      ∑ c ∈ range (S.k + 1), linkTerm S.θ S.q (chainSeq S π x) c := by
    have h0 : ∀ c : Fin (S.k + 1), deadBreg S.θ (linkVar π x c) (linkVar π xs c) =
        (fun c t => deadBreg S.θ t (S.q ^ c - S.q ^ (c + 1))) c.val (linkVar π x c) := by
      intro c
      rw [hxs, selectedChain_xstar_linkVar S π c]
    rw [sum_congr rfl (fun c _ => h0 c), link_sum_eq π x
      (fun c t => deadBreg S.θ t (S.q ^ c - S.q ^ (c + 1)))]
    rfl
  have hb2 : ∑ p, S.μ * (gain (x (π p) / S.scale p) - γ) * (x (π p) - S.scale p) ^ 2 =
      ∑ i ∈ Ioc 0 (S.k + 1), coordTerm S.μ γ S.q (chainSeq S π x) i := by
    have h0 : ∀ p : Fin (S.k + 1), S.μ * (gain (x (π p) / S.scale p) - γ) * (x (π p) - S.scale p) ^ 2 =
        (fun c t => S.μ * (gain (t / S.q ^ (c + 1)) - γ) * (t - S.q ^ (c + 1)) ^ 2) p.val (x (π p)) := by
      intro p; rfl
    rw [sum_congr rfl (fun p _ => h0 p), coord_sum_eq π x
      (fun c t => S.μ * (gain (t / S.q ^ (c + 1)) - γ) * (t - S.q ^ (c + 1)) ^ 2)]
    apply sum_congr rfl
    intro i hi
    have hi1 : i - 1 + 1 = i := Nat.sub_add_cancel (mem_Ioc.mp hi).1
    simp only [hi1]
    rfl
  rw [objective_expand S π x, objective_expand S π xs, field_inner S π x]
  simp only [hxsp]
  have hγμ : 0 ≤ (1 - γ) * S.μ := by nlinarith
  have hn2 := mul_le_mul_of_nonneg_left hnorm hγμ
  have hcm : (1 - γ) * S.μ * ∑ p, (x (π p) - S.scale p) ^ 2 =
      ∑ p, (1 - γ) * S.μ * (x (π p) - S.scale p) ^ 2 := by rw [mul_sum]
  nlinarith [hLs, hCs, hquad, hinner, hkkt, hchain, hb1, hb2, hn2, hcm]

lemma Shape.Valid.objective_lower {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    ∑ p, S.μ * S.scale p ^ 2 * bump (x (π p) / S.scale p) ≤
      objective S π x - objective S π (xstar S π) := by
  set xs := xstar S π with hxs
  have hμ0 := V.hμ0
  have hxsp : ∀ p, xs (π p) = S.scale p := fun p => xstar_apply_pi S π p
  have hL : ∀ c, deadSlope S.θ (linkVar π xs c) * (linkVar π x c - linkVar π xs c) ≤
      deadEnergy S.θ (linkVar π x c) - deadEnergy S.θ (linkVar π xs c) := by
    intro c
    have := (dead_model S.θ (linkVar π xs c) (linkVar π x c) V.hθ0.le).1
    linarith
  have hC : ∀ p, S.beta p * deadSlope S.ρ (S.scale p) * (x (π p) - S.scale p) -
      S.μ / 2 * (x (π p) - S.scale p) ^ 2 + S.μ * S.scale p ^ 2 * bump (x (π p) / S.scale p) ≤
      coordProfile S p (x (π p)) - coordProfile S p (S.scale p) := by
    intro p
    have m := dead_model S.ρ (S.scale p) (x (π p)) V.hρ0.le
    have hβ := V.beta_ge p
    have hβB : -(S.μ / 2 * (x (π p) - S.scale p) ^ 2) ≤ S.beta p *
        (deadEnergy S.ρ (x (π p)) - deadEnergy S.ρ (S.scale p) -
          deadSlope S.ρ (S.scale p) * (x (π p) - S.scale p)) := by nlinarith [m.1, m.2]
    unfold coordProfile
    rw [div_self (V.scale_pos p).ne', bump_one]
    nlinarith
  have hLs := sum_le_sum (fun c (_ : c ∈ (univ : Finset (Fin (S.k + 1)))) => hL c)
  have hCs := sum_le_sum (fun p (_ : p ∈ (univ : Finset (Fin (S.k + 1)))) => hC p)
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum] at hLs hCs
  have hkkt := V.kkt π x
  have hinner := xstar_inner_sub S π x
  have hnorm := chain_norm_sub S π x
  have hq : S.μ / 2 * ‖x‖ ^ 2 - S.μ / 2 * ‖xs‖ ^ 2 =
      S.μ * ⟪xs, x - xs⟫ + S.μ / 2 * ‖x - xs‖ ^ 2 := by
    have h1 := norm_sub_sq_real x xs
    rw [inner_sub_right, real_inner_self_eq_norm_sq, h1, real_inner_comm xs x]
    ring
  have hn2 := mul_le_mul_of_nonneg_left hnorm (by positivity : (0 : ℝ) ≤ S.μ / 2)
  rw [objective_expand S π x, objective_expand S π xs]
  simp only [hxsp]
  have hcm : S.μ / 2 * ∑ p, (x (π p) - S.scale p) ^ 2 =
      ∑ p, S.μ / 2 * (x (π p) - S.scale p) ^ 2 := by rw [mul_sum]
  nlinarith [hLs, hCs, hkkt, hinner, hq, hn2, hcm]

lemma Shape.Valid.minimizer {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) :
    IsMinOn (objective S π) Set.univ (xstar S π) := by
  intro x _
  have h := V.objective_lower π x
  have h0 : 0 ≤ ∑ p, S.μ * S.scale p ^ 2 * bump (x (π p) / S.scale p) := by
    apply sum_nonneg
    intro p _
    have := (bump_bounds (x (π p) / S.scale p)).1
    have := V.hμ0
    positivity
  change objective S π (xstar S π) ≤ objective S π x
  linarith

end sq

end LongTails.Proofs.StrongQuasarChainObjective
