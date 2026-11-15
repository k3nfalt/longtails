import LongTails.Proofs.InterpolatedFiniteSumLinks
import LongTails.Proofs.InterpolatedFiniteSumChains
import LongTails.Proofs.InterpolatedFiniteSumLinkResidual

open scoped BigOperators RealInnerProductSpace
open Classical

namespace LongTails.Proofs.InterpolatedFiniteSumLinkGeometry

open InterpolatedFiniteSumLinks InterpolatedFiniteSumProfiles

noncomputable def basis {d : ℕ} (j : Fin d) : EuclideanSpace ℝ (Fin d) := PiLp.single 2 j 1

def previous {T : ℕ} (j : Fin T) : Fin T := ⟨j.val - 1, by have := j.isLt; omega⟩

noncomputable def vector {d T : ℕ} (π : Fin T → Fin d) (a L : ℝ) (j : Fin T) : EuclideanSpace ℝ (Fin d) :=
  if j.val = 0 then a⁻¹ • basis (π j) else (L / 2) • (basis (π (previous j)) - basis (π j))

noncomputable def offset {T : ℕ} (j : Fin T) : ℝ := if j.val = 0 then 1 else 0

noncomputable def coefficient {T : ℕ} (η : ℝ) (j : Fin T) : ℝ := if j.val = 0 then 2 * η else 1 / 128

noncomputable def raw {d T : ℕ} (π : Fin T → Fin d) (η a L : ℝ) (j : Fin T) : EuclideanSpace ℝ (Fin d) → ℝ :=
  potential (vector π a L j) (offset j) (coefficient η j)

noncomputable def rawField {d T : ℕ} (π : Fin T → Fin d) (η a L : ℝ) (j : Fin T) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  field (vector π a L j) (offset j) (coefficient η j)

lemma basis_norm {d : ℕ} (j : Fin d) : ‖basis j‖ = 1 := by simp [basis]

lemma basis_inner {d : ℕ} (j : Fin d) (x : EuclideanSpace ℝ (Fin d)) : ⟪basis j, x⟫ = x j := by
  simp [basis, EuclideanSpace.inner_single_left]

lemma vector_inner {d T : ℕ} (π : Fin T → Fin d) (a L : ℝ) (j : Fin T) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪vector π a L j, x⟫ = if j.val = 0 then x (π j) / a else (L / 2) * (x (π (previous j)) - x (π j)) := by
  unfold vector
  split <;> simp only [real_inner_smul_left, inner_sub_left, basis_inner]
  ring

lemma vector_first_norm {d T : ℕ} (π : Fin T → Fin d) (a L : ℝ) (ha : 0 < a) (j : Fin T) (hj : j.val = 0) :
    ‖vector π a L j‖ = 1 / a := by
  simp only [vector, ite_eq_left hj, norm_smul, basis_norm, mul_one, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr ha), one_div]

lemma vector_later_norm {d T : ℕ} (π : Fin T → Fin d) (a L : ℝ) (hL : 0 ≤ L) (j : Fin T) (hj : j.val ≠ 0) :
    ‖vector π a L j‖ ≤ L := by
  rw [vector, ite_eq_right hj, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ L / 2)]
  have hh := norm_sub_le (basis (π (previous j))) (basis (π j))
  rw [basis_norm, basis_norm] at hh
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ L / 2)
  linarith only [hm]

lemma coefficient_nonnegative {T : ℕ} (η : ℝ) (hη : 0 ≤ η) (j : Fin T) : 0 ≤ coefficient η j := by
  unfold coefficient
  split <;> positivity

lemma gradient_bound {d T : ℕ} (π : Fin T → Fin d) (η a L : ℝ) (ha : 0 < a)
    (hL : 0 ≤ L) (hfirst : 2 * η / a ≤ L / 14) (j : Fin T) :
    coefficient η j * ‖vector π a L j‖ ≤ L / 14 := by
  by_cases hj : j.val = 0
  · rw [coefficient, ite_eq_left hj, vector_first_norm π a L ha j hj]
    simpa only [mul_one_div] using hfirst
  · rw [coefficient, ite_eq_right hj]
    have hh := mul_le_mul_of_nonneg_left (vector_later_norm π a L hL j hj) (by norm_num : (0 : ℝ) ≤ 1 / 128)
    linarith only [hh, hL]

lemma curvature_bound {d T : ℕ} (π : Fin T → Fin d) (η a L : ℝ) (ha : 0 < a)
    (hL : 0 ≤ L) (hfirst : 6 * η / a ^ 2 ≤ (4 * L ^ 2 / 49) / 3) (j : Fin T) :
    3 * coefficient η j * ‖vector π a L j‖ ^ 2 ≤ (4 * L ^ 2 / 49) / 3 := by
  by_cases hj : j.val = 0
  · rw [coefficient, ite_eq_left hj, vector_first_norm π a L ha j hj]
    convert hfirst using 1
    ring
  · rw [coefficient, ite_eq_right hj]
    have hh := pow_le_pow_left₀ (norm_nonneg _) (vector_later_norm π a L hL j hj) 2
    nlinarith only [hh, sq_nonneg L]

lemma raw_zero {d T : ℕ} (π : Fin T → Fin d) (η a L : ℝ) (j : Fin T) :
    raw π η a L j 0 = if j.val = 0 then η else 0 := by
  have hpos := (profile_linear 1 (by norm_num)).1
  have hneg : profile (-1) = 1 / 2 := by rw [profile_even, hpos]; norm_num
  have hz := (profile_flat 0 (by norm_num)).1
  simp only [raw, potential, inner_zero_right, offset, coefficient]
  split_ifs <;> simp only [zero_sub, hneg, neg_zero, hz] <;> ring

lemma raw_flat_future {d T : ℕ} (π : Fin T → Fin d) (η a L θ : ℝ) (hL : 0 ≤ L)
    (hθL : L * θ ≤ 1 / 4) (r : ℕ) (j : Fin T) (hj : r < j.val) (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ i : Fin T, r ≤ i.val → |x (π i)| ≤ θ) :
    raw π η a L j x = 0 ∧ rawField π η a L j x = 0 := by
  have hj0 : j.val ≠ 0 := by omega
  apply potential_flat
  rw [vector_inner, ite_eq_right hj0, offset, ite_eq_right hj0, sub_zero, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ L / 2)]
  have hp := hx (previous j) (by dsimp [previous]; omega)
  have hc := hx j (by omega)
  have hh := abs_sub (x (π (previous j))) (x (π j))
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ L / 2)
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hp hc) (by positivity : 0 ≤ L / 2)
  nlinarith only [hm, hsum, hθL]

noncomputable def minimizer {d T : ℕ} (π : Fin T ↪ Fin d) (a : ℝ) : EuclideanSpace ℝ (Fin d) :=
  (FiniteSumNondualLowerComponents.coordinateMap π).adjoint (WithLp.toLp 2 (fun _ : Fin T => a))

lemma minimizer_coordinate {d T : ℕ} (π : Fin T ↪ Fin d) (a : ℝ) (j : Fin T) :
    minimizer π a (π j) = a :=
  InterpolatedFiniteSumChains.coordinateMap_adjoint_coordinate π _ j

lemma minimizer_norm_sq {d T : ℕ} (π : Fin T ↪ Fin d) (a : ℝ) :
    ‖minimizer π a‖ ^ 2 ≤ T * a ^ 2 := by
  have hh := pow_le_pow_left₀ (norm_nonneg _)
    (InterpolatedFiniteSumChains.coordinateMap_adjoint_norm π (WithLp.toLp 2 (fun _ : Fin T => a))) 2
  have he : ‖(WithLp.toLp 2 (fun _ : Fin T => a) : EuclideanSpace ℝ (Fin T))‖ ^ 2 = T * a ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq]
  rw [he] at hh
  exact hh

lemma minimizer_outside {d T : ℕ} (π : Fin T ↪ Fin d) (a : ℝ) (j : Fin d) (hj : ∀ i, π i ≠ j) :
    minimizer π a j = 0 := InterpolatedFiniteSumChains.coordinateMap_adjoint_outside π _ j hj

lemma vector_minimizer {d T : ℕ} (π : Fin T ↪ Fin d) (a L : ℝ) (ha : a ≠ 0) (j : Fin T) :
    ⟪vector π a L j, minimizer π a⟫ = offset j := by
  rw [vector_inner]
  simp only [minimizer_coordinate, div_self ha, sub_self, mul_zero, offset]

lemma vector_prefix {d T : ℕ} (π ρ : Fin T → Fin d) (a L : ℝ) (j : Fin T)
    (h : ∀ i : Fin T, i.val ≤ j.val → π i = ρ i) : vector π a L j = vector ρ a L j := by
  have hj := h j le_rfl
  have hp := h (previous j) (by dsimp [previous]; omega)
  simp only [vector, hj, hp]

lemma raw_first {d T : ℕ} (π : Fin T → Fin d) (η a L : ℝ) (j : Fin T) (hj : j.val = 0)
    (x : EuclideanSpace ℝ (Fin d)) : raw π η a L j x = 2 * η * profile (x (π j) / a - 1) := by
  simp only [raw, potential, vector_inner, coefficient, offset, ite_eq_left hj]

lemma raw_later {d T : ℕ} (π : Fin T → Fin d) (η a L : ℝ) (j : Fin T) (hj : j.val ≠ 0)
    (x : EuclideanSpace ℝ (Fin d)) : raw π η a L j x =
      InterpolatedFiniteSumExponential.linkPotential L (x (π (previous j)) - x (π j)) := by
  simp only [raw, potential, vector_inner, coefficient, offset, ite_eq_right hj, sub_zero,
    InterpolatedFiniteSumExponential.linkPotential]
  have he : L / 2 * (x (π (previous j)) - x (π j)) = L * (x (π (previous j)) - x (π j)) / 2 := by ring
  rw [he]
  ring

noncomputable def sequence {d T : ℕ} (π : Fin T → Fin d) (x : EuclideanSpace ℝ (Fin d)) (j : ℕ) : ℝ :=
  if h : j < T then x (π ⟨j, h⟩) else 0

lemma loss_eq {d T : ℕ} (π : Fin T → Fin d) (η a L : ℝ) (x : EuclideanSpace ℝ (Fin d)) (j : Fin T) :
    Real.exp (raw π η a L j x) - 1 =
      InterpolatedFiniteSumLinkResidual.loss η L a (sequence π x) j.val := by
  rcases j with ⟨j, hj⟩
  cases j with
  | zero =>
    rw [raw_first π η a L ⟨0, hj⟩ rfl]
    simp only [InterpolatedFiniteSumLinkResidual.loss, sequence, dite_eq_left hj]
  | succ j =>
    rw [raw_later π η a L ⟨j + 1, hj⟩ (by simp)]
    have hj' : j < T := by omega
    simp only [InterpolatedFiniteSumLinkResidual.loss, sequence, dite_eq_left hj, dite_eq_left hj',
      previous, Nat.add_sub_cancel]

end LongTails.Proofs.InterpolatedFiniteSumLinkGeometry
