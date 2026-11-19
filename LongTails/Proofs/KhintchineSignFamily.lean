import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Finset

namespace LongTails.Proofs.KhintchineSignFamily

variable {p : ℕ} [hp : Fact p.Prime]

abbrev Coeff (p : ℕ) := Fin 4 → ZMod p

def poly (c : Coeff p) (t : ZMod p) : ZMod p := ∑ j : Fin 4, c j * t ^ (j : ℕ)

noncomputable def sgn (t : ZMod p) : ℝ := if t = 0 then 0 else if t.val ≤ p / 2 then 1 else -1

lemma sgn_neg (hp2 : p ≠ 2) (t : ZMod p) : sgn (-t) = -sgn t := by
  have hodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  by_cases ht : t = 0
  · simp [sgn, ht]
  have hnt : -t ≠ 0 := neg_ne_zero.mpr ht
  have hv : (-t).val = p - t.val := by rw [ZMod.neg_val]; simp [ht]
  have hlt := ZMod.val_lt t
  have hpos : 0 < t.val := Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero])
  unfold sgn
  simp only [hnt, ht, ↓reduceIte, hv]
  by_cases hle : t.val ≤ p / 2
  · have : ¬ (p - t.val ≤ p / 2) := by omega
    simp [this, hle]
  · have : p - t.val ≤ p / 2 := by omega
    simp [this, hle]

lemma sgn_sq (t : ZMod p) : sgn t ^ 2 = if t = 0 then 0 else 1 := by
  unfold sgn
  split_ifs <;> norm_num

lemma sgn_pow_three (t : ZMod p) : sgn t ^ 3 = sgn t := by
  unfold sgn
  split_ifs <;> norm_num

lemma sgn_pow_four (t : ZMod p) : sgn t ^ 4 = sgn t ^ 2 := by
  unfold sgn
  split_ifs <;> norm_num

lemma sum_sgn (hp2 : p ≠ 2) : ∑ t : ZMod p, sgn t = 0 := by
  have h : ∑ t : ZMod p, sgn t = ∑ t : ZMod p, sgn (-t) :=
    (Equiv.sum_comp (Equiv.neg (ZMod p)) (fun t => sgn t)).symm
  simp only [sgn_neg hp2, Finset.sum_neg_distrib] at h
  linarith

lemma sum_sgn_sq : ∑ t : ZMod p, sgn t ^ 2 = (p : ℝ) - 1 := by
  simp only [sgn_sq]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter fun t : ZMod p => ¬ t = 0).card = p - 1 := by
    rw [Finset.filter_ne' Finset.univ (0 : ZMod p), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
  rw [hcard, Nat.cast_sub hp.out.one_lt.le]
  simp

noncomputable def moment (k : ℕ) : ℝ := ∑ t : ZMod p, sgn t ^ k

lemma moment_zero : moment (p := p) 0 = p := by
  simp [moment, ZMod.card]

lemma moment_one (hp2 : p ≠ 2) : moment (p := p) 1 = 0 := by
  simp [moment, sum_sgn hp2]

lemma moment_two : moment (p := p) 2 = (p : ℝ) - 1 := sum_sgn_sq

lemma moment_three (hp2 : p ≠ 2) : moment (p := p) 3 = 0 := by
  simp only [moment, sgn_pow_three]
  exact sum_sgn hp2

lemma moment_four : moment (p := p) 4 = (p : ℝ) - 1 := by
  simp only [moment, sgn_pow_four]
  exact sum_sgn_sq

lemma poly_eq_mulVec (c : Coeff p) (τ : Fin 4 → ZMod p) (k : Fin 4) :
    poly c (τ k) = (Matrix.vandermonde τ).mulVec c k := by
  simp only [poly, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma evaluation_bijective {τ : Fin 4 → ZMod p} (hτ : Function.Injective τ) :
    Function.Bijective fun c : Coeff p => fun k => poly c (τ k) := by
  have hdet : (Matrix.vandermonde τ).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hτ
  have hunit : IsUnit (Matrix.vandermonde τ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hinj : Function.Injective (Matrix.vandermonde τ).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  have hsurj : Function.Surjective (Matrix.vandermonde τ).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hunit
  have heq : (fun c : Coeff p => fun k => poly c (τ k)) = (Matrix.vandermonde τ).mulVec := by
    funext c k
    exact poly_eq_mulVec c τ k
  rw [heq]
  exact ⟨hinj, hsurj⟩

lemma sum_eval_eq {τ : Fin 4 → ZMod p} (hτ : Function.Injective τ) (G : (Fin 4 → ZMod p) → ℝ) :
    ∑ c : Coeff p, G (fun k => poly c (τ k)) = ∑ v : Fin 4 → ZMod p, G v :=
  Function.Bijective.sum_comp (evaluation_bijective hτ) G

lemma sum_prod_pow {τ : Fin 4 → ZMod p} (hτ : Function.Injective τ) (m : Fin 4 → ℕ) :
    ∑ c : Coeff p, ∏ k, sgn (poly c (τ k)) ^ m k = ∏ k, moment (p := p) (m k) := by
  rw [sum_eval_eq hτ (fun v => ∏ k, sgn (v k) ^ m k)]
  have h := Finset.prod_univ_sum (fun _ : Fin 4 => (Finset.univ : Finset (ZMod p)))
    (fun k t => sgn t ^ m k)
  simp only [Fintype.piFinset_univ] at h
  rw [← h]
  rfl


section Nodes

variable (p) in
def node (i : ℕ) : ZMod p := (i : ZMod p)

lemma node_injOn {i j : ℕ} (hi : i < p) (hj : j < p) (h : node p i = node p j) : i = j := by
  unfold node at h
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this

lemma node_ne {i j : ℕ} (hi : i < p) (hj : j < p) (h : i ≠ j) : node p i ≠ node p j :=
  fun h' => h (node_injOn hi hj h')

lemma sum_four_nodes {a b c d : ℕ} (ha : a < p) (hb : b < p) (hc : c < p) (hd : d < p)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ma mb mc md : ℕ) :
    ∑ e : Coeff p, sgn (poly e (node p a)) ^ ma * sgn (poly e (node p b)) ^ mb *
        sgn (poly e (node p c)) ^ mc * sgn (poly e (node p d)) ^ md =
      moment (p := p) ma * moment (p := p) mb * moment (p := p) mc * moment (p := p) md := by
  have hinj : Function.Injective ![node p a, node p b, node p c, node p d] := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp at hxy ⊢
    all_goals first
      | exact absurd hxy (node_ne ha hb hab)
      | exact absurd hxy (node_ne hb ha (Ne.symm hab))
      | exact absurd hxy (node_ne ha hc hac)
      | exact absurd hxy (node_ne hc ha (Ne.symm hac))
      | exact absurd hxy (node_ne ha hd had)
      | exact absurd hxy (node_ne hd ha (Ne.symm had))
      | exact absurd hxy (node_ne hb hc hbc)
      | exact absurd hxy (node_ne hc hb (Ne.symm hbc))
      | exact absurd hxy (node_ne hb hd hbd)
      | exact absurd hxy (node_ne hd hb (Ne.symm hbd))
      | exact absurd hxy (node_ne hc hd hcd)
      | exact absurd hxy (node_ne hd hc (Ne.symm hcd))
  have h := sum_prod_pow hinj ![ma, mb, mc, md]
  simpa [Fin.prod_univ_four] using h

lemma sum_eq_of_pointwise {F G : Coeff p → ℝ} (h : ∀ c, F c = G c) :
    ∑ c, F c = ∑ c, G c := Finset.sum_congr rfl fun c _ => h c

end Nodes

section Family

variable {D : ℕ}

noncomputable def sign (c : Coeff p) (i : Fin D) : ℝ := sgn (poly c (node p i))

noncomputable def A1 (p : ℕ) : ℝ := ((p : ℝ) - 1) * (p : ℝ) ^ 3

noncomputable def A2 (p : ℕ) : ℝ := ((p : ℝ) - 1) ^ 2 * (p : ℝ) ^ 2

variable (hDp : D + 4 ≤ p) (hp2 : p ≠ 2)
include hDp hp2

omit hp2 in
lemma sum_sign_sq (i : Fin D) : ∑ c : Coeff p, sign c i ^ 2 = A1 p := by
  have h := sum_four_nodes (p := p) (a := i) (b := D) (c := D + 1) (d := D + 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) 2 0 0 0
  simp only [pow_zero, mul_one] at h
  rw [moment_two, moment_zero] at h
  simp only [sign, A1]
  rw [h]; ring

lemma sum_sign_mul {i j : Fin D} (hij : i ≠ j) : ∑ c : Coeff p, sign c i * sign c j = 0 := by
  have hv : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have h := sum_four_nodes (p := p) (a := i) (b := j) (c := D) (d := D + 1)
    (by omega) (by omega) (by omega) (by omega) hv (by omega) (by omega) (by omega)
    (by omega) (by omega) 1 1 0 0
  simp only [pow_zero, mul_one, pow_one] at h
  rw [moment_one hp2] at h
  simp only [sign]
  rw [h]; ring

omit hp2 in
lemma sum_sign_four (i : Fin D) : ∑ c : Coeff p, sign c i ^ 4 = A1 p := by
  have h := sum_four_nodes (p := p) (a := i) (b := D) (c := D + 1) (d := D + 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) 4 0 0 0
  simp only [pow_zero, mul_one] at h
  rw [moment_four, moment_zero] at h
  simp only [sign, A1]
  rw [h]; ring

omit hp2 in
lemma sum_sign_two_two {i j : Fin D} (hij : i ≠ j) :
    ∑ c : Coeff p, sign c i ^ 2 * sign c j ^ 2 = A2 p := by
  have hv : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have h := sum_four_nodes (p := p) (a := i) (b := j) (c := D) (d := D + 1)
    (by omega) (by omega) (by omega) (by omega) hv (by omega) (by omega) (by omega)
    (by omega) (by omega) 2 2 0 0
  simp only [pow_zero, mul_one] at h
  rw [moment_two, moment_zero] at h
  simp only [sign, A2]
  rw [h]; ring

lemma sum_sign_three_one {i j : Fin D} (hij : i ≠ j) :
    ∑ c : Coeff p, sign c i ^ 3 * sign c j = 0 := by
  have hv : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have h := sum_four_nodes (p := p) (a := i) (b := j) (c := D) (d := D + 1)
    (by omega) (by omega) (by omega) (by omega) hv (by omega) (by omega) (by omega)
    (by omega) (by omega) 3 1 0 0
  simp only [pow_zero, mul_one, pow_one] at h
  rw [moment_three hp2] at h
  simp only [sign]
  rw [h]; ring

lemma sum_sign_two_one_one {i j k : Fin D} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ c : Coeff p, sign c i ^ 2 * sign c j * sign c k = 0 := by
  have h1 : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have h2 : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
  have h3 : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
  have h := sum_four_nodes (p := p) (a := i) (b := j) (c := k) (d := D)
    (by omega) (by omega) (by omega) (by omega) h1 h2 (by omega) h3 (by omega) (by omega)
    2 1 1 0
  simp only [pow_zero, mul_one, pow_one] at h
  rw [moment_one hp2] at h
  simp only [sign]
  rw [h]; ring

lemma sum_sign_one_one_one_one {i j k l : Fin D} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ∑ c : Coeff p, sign c i * sign c j * sign c k * sign c l = 0 := by
  have h1 : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have h2 : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
  have h3 : (i : ℕ) ≠ l := fun h => hil (Fin.ext h)
  have h4 : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
  have h5 : (j : ℕ) ≠ l := fun h => hjl (Fin.ext h)
  have h6 : (k : ℕ) ≠ l := fun h => hkl (Fin.ext h)
  have h := sum_four_nodes (p := p) (a := i) (b := j) (c := k) (d := l)
    (by omega) (by omega) (by omega) (by omega) h1 h2 h3 h4 h5 h6 1 1 1 1
  simp only [pow_one] at h
  rw [moment_one hp2] at h
  simp only [sign]
  rw [h]; ring

lemma fourth_formula (i j k l : Fin D) :
    ∑ c : Coeff p, sign c i * sign c j * sign c k * sign c l =
      A2 p * ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0)) +
      (A1 p - 3 * A2 p) * (if i = j ∧ j = k ∧ k = l then 1 else 0) := by
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = l
    · subst hkl
      by_cases hik : i = k
      · subst hik
        rw [sum_eq_of_pointwise (G := fun c => sign c i ^ 4) (fun c => by ring),
          sum_sign_four hDp]
        simp; ring
      · rw [sum_eq_of_pointwise (G := fun c => sign c i ^ 2 * sign c k ^ 2) (fun c => by ring),
          sum_sign_two_two hDp hik]
        simp [hik]
    · by_cases hik : i = k
      · subst hik
        rw [sum_eq_of_pointwise (G := fun c => sign c i ^ 3 * sign c l) (fun c => by ring),
          sum_sign_three_one hDp hp2 hkl]
        simp [hkl]
      · by_cases hil : i = l
        · subst hil
          rw [sum_eq_of_pointwise (G := fun c => sign c i ^ 3 * sign c k) (fun c => by ring),
            sum_sign_three_one hDp hp2 hik]
          simp [hkl, hik]
        · rw [sum_eq_of_pointwise (G := fun c => sign c i ^ 2 * sign c k * sign c l)
            (fun c => by ring), sum_sign_two_one_one hDp hp2 hik hil hkl]
          simp [hkl, hik, hil]
  · by_cases hkl : k = l
    · subst hkl
      by_cases hik : i = k
      · subst hik
        rw [sum_eq_of_pointwise (G := fun c => sign c i ^ 3 * sign c j) (fun c => by ring),
          sum_sign_three_one hDp hp2 hij]
        simp [hij, Ne.symm hij]
      · by_cases hjk : j = k
        · subst hjk
          rw [sum_eq_of_pointwise (G := fun c => sign c j ^ 3 * sign c i) (fun c => by ring),
            sum_sign_three_one hDp hp2 (Ne.symm hij)]
          simp [hij]
        · rw [sum_eq_of_pointwise (G := fun c => sign c k ^ 2 * sign c i * sign c j)
            (fun c => by ring), sum_sign_two_one_one hDp hp2 (Ne.symm hik) (Ne.symm hjk) hij]
          simp [hij, hik, hjk]
    · by_cases h1 : i = k ∧ j = l
      · obtain ⟨rfl, rfl⟩ := h1
        rw [sum_eq_of_pointwise (G := fun c => sign c i ^ 2 * sign c j ^ 2) (fun c => by ring),
          sum_sign_two_two hDp hij]
        simp [hij]
      · by_cases h2 : i = l ∧ j = k
        · obtain ⟨rfl, rfl⟩ := h2
          rw [sum_eq_of_pointwise (G := fun c => sign c i ^ 2 * sign c j ^ 2) (fun c => by ring),
            sum_sign_two_two hDp hij]
          simp [hij]
        · have hzero : ∑ c : Coeff p, sign c i * sign c j * sign c k * sign c l = 0 := by
            by_cases hik : i = k
            · subst hik
              have hjl : j ≠ l := fun h => h1 ⟨rfl, h⟩
              rw [sum_eq_of_pointwise (G := fun c => sign c i ^ 2 * sign c j * sign c l)
                (fun c => by ring)]
              exact sum_sign_two_one_one hDp hp2 hij hkl hjl
            · by_cases hjk : j = k
              · subst hjk
                have hil : i ≠ l := fun h => h2 ⟨h, rfl⟩
                rw [sum_eq_of_pointwise (G := fun c => sign c j ^ 2 * sign c i * sign c l)
                  (fun c => by ring)]
                exact sum_sign_two_one_one hDp hp2 (Ne.symm hij) hkl hil
              · by_cases hil : i = l
                · subst hil
                  rw [sum_eq_of_pointwise (G := fun c => sign c i ^ 2 * sign c j * sign c k)
                    (fun c => by ring)]
                  exact sum_sign_two_one_one hDp hp2 hij hik hjk
                · by_cases hjl : j = l
                  · subst hjl
                    rw [sum_eq_of_pointwise (G := fun c => sign c j ^ 2 * sign c i * sign c k)
                      (fun c => by ring)]
                    exact sum_sign_two_one_one hDp hp2 (Ne.symm hij) hjk hik
                  · exact sum_sign_one_one_one_one hDp hp2 hij hik hil hjk hjl hkl
          rw [hzero]
          simp [hij, hkl, h1, h2]

end Family

section Moments

variable {D : ℕ}

noncomputable def proj (c : Coeff p) (w : Fin D → ℝ) : ℝ := ∑ i, w i * sign c i

variable (hDp : D + 4 ≤ p) (hp2 : p ≠ 2)
include hDp hp2

lemma second_moment (w : Fin D → ℝ) :
    ∑ c : Coeff p, proj c w ^ 2 = A1 p * ∑ i, w i ^ 2 := by
  have hexp : ∀ c : Coeff p, proj c w ^ 2 = ∑ i, ∑ j, w i * w j * (sign c i * sign c j) := by
    intro c
    simp only [proj, sq, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [sum_eq_of_pointwise hexp, Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.sum_eq_single i]
  · rw [← Finset.mul_sum, show (fun c => sign c i * sign c i) = fun c => sign c i ^ 2 by
      funext c; ring, sum_sign_sq hDp]
    ring
  · intro j _ hji
    rw [← Finset.mul_sum, sum_sign_mul hDp hp2 (Ne.symm hji), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

end Moments

section Deltas

variable {D : ℕ}

lemma sum_delta_pair (w : Fin D → ℝ) (a b : Fin D) :
    ∑ k, ∑ l, w k * w l * (if a = k ∧ b = l then (1 : ℝ) else 0) = w a * w b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro l _ hl; simp [Ne.symm hl]
    · simp
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro l _
    simp [Ne.symm hk]
  · simp

lemma sum_delta_diag (w : Fin D → ℝ) :
    ∑ k, ∑ l, w k * w l * (if k = l then (1 : ℝ) else 0) = ∑ k, w k ^ 2 := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · simp [sq]
  · intro l _ hl; simp [Ne.symm hl]
  · simp

lemma sum_diag_weight (w X : Fin D → ℝ) :
    ∑ i, ∑ j, w i * w j * (if i = j then X i else 0) = ∑ i, w i ^ 2 * X i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [sq]
  · intro j _ hj; simp [Ne.symm hj]
  · simp

end Deltas

section Fourth

variable {D : ℕ} (hDp : D + 4 ≤ p) (hp2 : p ≠ 2)
include hDp hp2

lemma fourth_inner (w : Fin D → ℝ) (i j : Fin D) :
    ∑ k, ∑ l, w k * w l * ∑ c : Coeff p, sign c i * sign c j * sign c k * sign c l =
      A2 p * ((if i = j then ∑ k, w k ^ 2 else 0) + 2 * (w i * w j)) +
        (A1 p - 3 * A2 p) * (if i = j then w i ^ 2 else 0) := by
  simp only [fourth_formula hDp hp2]
  have hsplit : ∀ k l : Fin D, w k * w l * (A2 p * ((if i = j ∧ k = l then (1 : ℝ) else 0) +
      (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) +
      (A1 p - 3 * A2 p) * (if i = j ∧ j = k ∧ k = l then 1 else 0)) =
      A2 p * ((if i = j then (1 : ℝ) else 0) * (w k * w l * (if k = l then 1 else 0))) +
      A2 p * (w k * w l * (if i = k ∧ j = l then 1 else 0)) +
      A2 p * (w k * w l * (if j = k ∧ i = l then 1 else 0)) +
      (A1 p - 3 * A2 p) * ((if i = j then (1 : ℝ) else 0) * (w k * w l * (if i = k ∧ i = l then 1 else 0))) := by
    intro k l
    by_cases h1 : i = j <;> by_cases h2 : i = k <;> by_cases h3 : i = l <;> by_cases h4 : j = k <;>
      by_cases h5 : j = l <;> by_cases h6 : k = l <;> simp_all <;> ring
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hsplit k l]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_delta_diag, sum_delta_pair, sum_delta_pair, sum_delta_pair]
  by_cases h : i = j
  · subst h; simp; ring
  · simp [h]; ring

lemma fourth_moment (w : Fin D → ℝ) :
    ∑ c : Coeff p, proj c w ^ 4 = 3 * A2 p * (∑ i, w i ^ 2) ^ 2 +
      (A1 p - 3 * A2 p) * ∑ i, w i ^ 4 := by
  have hexp : ∀ c : Coeff p, proj c w ^ 4 =
      ∑ i, ∑ j, w i * w j * ∑ k, ∑ l, w k * w l * (sign c i * sign c j * sign c k * sign c l) := by
    intro c
    have : proj c w ^ 4 = (proj c w * proj c w) * (proj c w * proj c w) := by ring
    rw [this]
    simp only [proj, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [sum_eq_of_pointwise hexp]
  have hswap : ∑ c : Coeff p, ∑ i, ∑ j, w i * w j * ∑ k, ∑ l, w k * w l *
      (sign c i * sign c j * sign c k * sign c l) =
      ∑ i, ∑ j, w i * w j * ∑ k, ∑ l, w k * w l *
        ∑ c : Coeff p, sign c i * sign c j * sign c k * sign c l := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_sum]
  rw [hswap]
  simp only [fourth_inner hDp hp2]
  have hsplit : ∀ i j : Fin D, w i * w j * (A2 p * ((if i = j then ∑ k, w k ^ 2 else 0) +
      2 * (w i * w j)) + (A1 p - 3 * A2 p) * (if i = j then w i ^ 2 else 0)) =
      A2 p * (w i * w j * (if i = j then ∑ k, w k ^ 2 else 0)) + 2 * A2 p * (w i ^ 2 * w j ^ 2) +
        (A1 p - 3 * A2 p) * (w i * w j * (if i = j then w i ^ 2 else 0)) := by
    intro i j; ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_diag_weight w (fun _ => ∑ k, w k ^ 2), sum_diag_weight w (fun i => w i ^ 2)]
  have h2 : ∑ i : Fin D, w i ^ 2 * w i ^ 2 = ∑ i, w i ^ 4 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h2, ← Finset.sum_mul]
  ring

omit hp hDp hp2 in
lemma A1_le_three_A2 (h5 : 5 ≤ p) : A1 p ≤ 3 * A2 p := by
  unfold A1 A2
  have hp : (5 : ℝ) ≤ p := by exact_mod_cast h5
  nlinarith [sq_nonneg ((p : ℝ) - 1), mul_pos (by linarith : (0:ℝ) < p) (by linarith : (0:ℝ) < p)]

end Fourth

section Khintchine

lemma abs_ge_quartic {x t : ℝ} (ht : 0 < t) : x ^ 2 / t - x ^ 4 / (4 * t ^ 3) ≤ |x| := by
  have hu : 0 ≤ |x| := abs_nonneg x
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hx4 : x ^ 4 = |x| ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rw [hx2, hx4]
  set u := |x|
  rw [div_sub_div _ _ ht.ne' (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (u - t), sq_nonneg (u - 2 * t), mul_nonneg hu ht.le,
    mul_nonneg (mul_nonneg hu hu) ht.le, mul_nonneg hu (sq_nonneg (u - t)),
    mul_nonneg ht.le (sq_nonneg (u - t)), mul_nonneg hu (sq_nonneg (u - 2 * t))]

variable {D : ℕ} (hDp : D + 4 ≤ p) (hp2 : p ≠ 2)
include hDp hp2

omit hDp hp2 in
lemma card_coeff : (Fintype.card (Coeff p) : ℝ) = (p : ℝ) ^ 4 := by
  simp [Coeff, ZMod.card]

lemma sum_abs_proj_le (w : Fin D → ℝ) :
    ∑ c : Coeff p, |proj c w| ≤ (p : ℝ) ^ 4 * Real.sqrt (∑ i, w i ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Coeff p))
    (fun _ => (1 : ℝ)) (fun c => |proj c w|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    sq_abs] at hcs
  rw [second_moment hDp hp2, card_coeff (p := p)] at hcs
  have hA1 : A1 p ≤ (p : ℝ) ^ 4 := by
    unfold A1
    have : (0 : ℝ) ≤ (p : ℝ) ^ 3 := by positivity
    nlinarith
  have hW : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS : 0 ≤ ∑ c : Coeff p, |proj c w| := Finset.sum_nonneg fun c _ => abs_nonneg _
  have hp4 : 0 ≤ (p : ℝ) ^ 4 := by positivity
  rw [← Real.sqrt_sq hS, ← Real.sqrt_sq hp4, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  calc (∑ c : Coeff p, |proj c w|) ^ 2 ≤ (p : ℝ) ^ 4 * (A1 p * ∑ i, w i ^ 2) := hcs
    _ ≤ (p : ℝ) ^ 4 * ((p : ℝ) ^ 4 * ∑ i, w i ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hp4
        exact mul_le_mul_of_nonneg_right hA1 hW
    _ = ((p : ℝ) ^ 4) ^ 2 * ∑ i, w i ^ 2 := by ring

lemma sum_abs_proj_ge (h5 : 5 ≤ p) (w : Fin D → ℝ) :
    (p : ℝ) ^ 4 * Real.sqrt (∑ i, w i ^ 2) / 3 ≤ ∑ c : Coeff p, |proj c w| := by
  set W := ∑ i, w i ^ 2 with hWdef
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hW.eq_or_lt with h0 | hpos
  · rw [← h0, Real.sqrt_zero]
    simp only [mul_zero, zero_div]
    exact Finset.sum_nonneg fun c _ => abs_nonneg _
  set r := Real.sqrt W
  have hr : 0 < r := Real.sqrt_pos.mpr hpos
  have hr2 : r ^ 2 = W := Real.sq_sqrt hW
  set t := 3 / 2 * r
  have ht : 0 < t := by positivity
  have hpt : ∀ c : Coeff p, proj c w ^ 2 / t - proj c w ^ 4 / (4 * t ^ 3) ≤ |proj c w| :=
    fun c => abs_ge_quartic ht
  have hsum := Finset.sum_le_sum fun c (_ : c ∈ (Finset.univ : Finset (Coeff p))) => hpt c
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    second_moment hDp hp2, fourth_moment hDp hp2] at hsum
  have h4 : 0 ≤ ∑ i, w i ^ 4 := Finset.sum_nonneg fun i _ => by positivity
  have hneg : (A1 p - 3 * A2 p) * ∑ i, w i ^ 4 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [A1_le_three_A2 (p := p) h5]) h4
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h5
  have key : (p : ℝ) ^ 4 * r / 3 ≤ A1 p * W / t - (3 * A2 p * W ^ 2) / (4 * t ^ 3) := by
    have e : A1 p * W / t - (3 * A2 p * W ^ 2) / (4 * t ^ 3) =
        r * (((p : ℝ) - 1) * (p : ℝ) ^ 2 * (4 * p + 2) / 9) := by
      rw [← hr2]
      simp only [t, A1, A2]
      field_simp
      ring
    rw [e]
    have hq : (p : ℝ) ^ 4 / 3 ≤ ((p : ℝ) - 1) * (p : ℝ) ^ 2 * (4 * p + 2) / 9 := by
      have hp2' : (0 : ℝ) ≤ (p : ℝ) ^ 2 := by positivity
      nlinarith [mul_nonneg hp2' (show (0 : ℝ) ≤ (p : ℝ) ^ 2 - 2 * p - 2 by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left hq hr.le]
  calc (p : ℝ) ^ 4 * r / 3 ≤ A1 p * W / t - (3 * A2 p * W ^ 2) / (4 * t ^ 3) := key
    _ ≤ A1 p * W / t - (3 * A2 p * W ^ 2 + (A1 p - 3 * A2 p) * ∑ i, w i ^ 4) / (4 * t ^ 3) := by
        have : 0 < 4 * t ^ 3 := by positivity
        gcongr
        linarith
    _ ≤ _ := hsum

end Khintchine

end LongTails.Proofs.KhintchineSignFamily
