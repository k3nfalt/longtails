import LongTails.Proofs.FixedBatchConfidenceModel
import LongTails.Algorithms.MarkovQuadraticSgd

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.FixedBatchConfidence

open LongTails.Setups.FixedBatchConfidence

lemma iterate_oracle_map {E Ω Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → Ω → E) (h : Ξ → Ω) (η : ℝ) (x0 : E) (ξ : ℕ → Ξ) (K : ℕ) :
    MarkovQuadratic.iterate (fun x z => g x (h z)) η x0 ξ K =
      MarkovQuadratic.iterate g η x0 (fun k => h (ξ k)) K := by
  induction K with
  | zero => rfl
  | succ K ih => simp only [MarkovQuadratic.iterate, ih]

lemma rank_one_affine_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u z a : E) (η r s : ℝ) :
    (u + r • z) - η • (⟪s • a, (u + r • z) - u⟫ • (s • a)) =
      u + r • (z - (η * s ^ 2) • (⟪a, z⟫ • a)) := by
  rw [add_sub_cancel_left]
  simp only [inner_smul_left, inner_smul_right, conj_trivial, smul_smul, smul_sub]
  module

lemma rank_one_batch_affine_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {b : ℕ} (u z : E) (a : Fin b → E) (η r s : ℝ) :
    (u + r • z) - η • ((b : ℝ)⁻¹ • ∑ i : Fin b,
      ⟪s • a i, (u + r • z) - u⟫ • (s • a i)) =
      u + r • (z - (η * s ^ 2) • ((b : ℝ)⁻¹ • ∑ i : Fin b, ⟪a i, z⟫ • a i)) := by
  have hi (i : Fin b) : ⟪s • a i, r • z⟫ • (s • a i) =
      (r * s ^ 2) • (⟪a i, z⟫ • a i) := by
    simp only [inner_smul_left, inner_smul_right, conj_trivial, smul_smul]
    module
  simp only [add_sub_cancel_left]
  simp_rw [hi]
  rw [← Finset.smul_sum]
  simp only [smul_smul, smul_sub]
  module

lemma rank_one_batch_iterate_affine {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {b : ℕ} (u z0 : E) (ξ : ℕ → Fin b → E) (η r s : ℝ) (K : ℕ) :
    MarkovQuadratic.iterate
      (fun (x : E) (v : Fin b → E) => (b : ℝ)⁻¹ • ∑ i : Fin b, ⟪v i, x - u⟫ • v i)
      η (u + r • z0) (fun k i => s • ξ k i) K =
      u + r • MarkovQuadratic.iterate
        (fun (x : E) (v : Fin b → E) => (b : ℝ)⁻¹ • ∑ i : Fin b, ⟪v i, x⟫ • v i)
        (η * s ^ 2) z0 ξ K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [MarkovQuadratic.iterate, ih]
    exact rank_one_batch_affine_step u _ (ξ K) η r s

lemma boolean_sum {E : Type*} [AddCommGroup E] [Module ℝ E]
    {b : ℕ} (v : Fin b → Bool) (u w : E) :
    (∑ i, if v i then u else w) =
      (∑ i, if v i then (1 : ℝ) else 0) • u +
        ((b : ℝ) - ∑ i, if v i then (1 : ℝ) else 0) • w := by
  have hi (i : Fin b) : (if v i then u else w) =
      (if v i then (1 : ℝ) else 0) • u +
        (1 - if v i then (1 : ℝ) else 0) • w := by
    cases v i <;> simp
  simp_rw [hi]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul,
    Finset.sum_sub_distrib]
  simp

lemma boolean_average {E : Type*} [AddCommGroup E] [Module ℝ E]
    {b : ℕ} (hb : 0 < b) (v : Fin b → Bool) (u w : E) :
    let θ := (b : ℝ)⁻¹ * ∑ i, if v i then (1 : ℝ) else 0
    (b : ℝ)⁻¹ • (∑ i, if v i then u else w) = θ • u + (1 - θ) • w := by
  dsimp
  rw [boolean_sum, smul_add, smul_smul, smul_smul]
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  congr 1
  congr 1
  field_simp

lemma boolean_fraction_bounds {b : ℕ} (hb : 0 < b) (v : Fin b → Bool) :
    let θ := (b : ℝ)⁻¹ * ∑ i, if v i then (1 : ℝ) else 0
    0 ≤ θ ∧ θ ≤ 1 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hs0 : 0 ≤ ∑ i : Fin b, if v i then (1 : ℝ) else 0 := by positivity
  have hs1 : (∑ i : Fin b, if v i then (1 : ℝ) else 0) ≤ b := by
    calc
      _ ≤ ∑ _i : Fin b, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by split_ifs <;> norm_num)
      _ = b := by simp
  dsimp
  constructor
  · positivity
  · have hh := mul_le_mul_of_nonneg_left hs1 (inv_nonneg.mpr hb0.le)
    simpa [ne_of_gt hb0] using hh

lemma batch_gradient_coordinates {b : ℕ} (hb : 0 < b) (v : Fin b → Bool)
    (a c : ℝ) (x : Space) :
    let θ := (b : ℝ)⁻¹ * ∑ i, if v i then (1 : ℝ) else 0
    let g := (b : ℝ)⁻¹ • ∑ i,
      ⟪(if v i then pair a c else pair 0 1), x⟫ •
        (if v i then pair a c else pair 0 1)
    g 0 = θ * a * (a * x 0 + c * x 1) ∧
      g 1 = (1 - θ) * x 1 + θ * c * (a * x 0 + c * x 1) := by
  have hi (i : Fin b) :
      ⟪(if v i then pair a c else pair 0 1), x⟫ •
        (if v i then pair a c else pair 0 1) =
      if v i then ⟪pair a c, x⟫ • pair a c else ⟪pair 0 1, x⟫ • pair 0 1 := by
    cases v i <;> rfl
  dsimp only
  simp_rw [hi]
  rw [boolean_average hb]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pair_zero, pair_one,
    pair_inner_vector]
  constructor <;> ring

lemma normalized_iterate_step {b : ℕ} (hb : 0 < b) (ξ : ℕ → Fin b → Bool)
    (a c η : ℝ) :
    let G := fun (x : Space) (v : Fin b → Bool) => (b : ℝ)⁻¹ • ∑ i,
      ⟪(if v i then pair a c else pair 0 1), x⟫ •
        (if v i then pair a c else pair 0 1)
    let X := MarkovQuadratic.iterate G η (pair 1 0) ξ
    let θ := fun k => (b : ℝ)⁻¹ * ∑ i, if ξ k i then (1 : ℝ) else 0
    ∀ k, X (k + 1) 0 = X k 0 - η * θ k * a * (a * X k 0 + c * X k 1) ∧
      X (k + 1) 1 = X k 1 - η * ((1 - θ k) * X k 1 +
        θ k * c * (a * X k 0 + c * X k 1)) := by
  intro G X θ k
  have hg := batch_gradient_coordinates hb (ξ k) a c (X k)
  change (G (X k) (ξ k)) 0 = _ ∧ (G (X k) (ξ k)) 1 = _ at hg
  have hstep : X (k + 1) = X k - η • G (X k) (ξ k) := rfl
  rw [hstep]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hg.1, hg.2]
  constructor <;> dsimp [θ]; ring

lemma sum_blocks (f : ℕ → ℝ) (b K : ℕ) :
    (∑ k ∈ Finset.range K, ∑ i : Fin b, f (k * b + i.val)) =
      ∑ j ∈ Finset.range (K * b), f j := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun i => f (K * b + i)) b

lemma rare_fraction_sum {b : ℕ} (ξ : ℕ → Bool) (K : ℕ) :
    (∑ k ∈ Finset.range K, (b : ℝ)⁻¹ *
      ∑ i : Fin b, if ξ (k * b + i.val) then (1 : ℝ) else 0) =
      (b : ℝ)⁻¹ * ∑ j ∈ Finset.range (K * b), if ξ j then (1 : ℝ) else 0 := by
  rw [← Finset.mul_sum, sum_blocks (fun j => if ξ j then (1 : ℝ) else 0) b K]

end OracleTemplate.FixedBatchConfidence
