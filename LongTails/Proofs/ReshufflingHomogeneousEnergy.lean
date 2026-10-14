import LongTails.Proofs.ReshufflingCoefficientEnergy
import LongTails.Proofs.ReshufflingPolynomialEnergy

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.Reshuffling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def energyCoefficient {n : ℕ} (A : Fin n → E →L[ℝ] E)
    (w : List (Fin n)) (x : E) (m : ℕ) : ℝ :=
  ∑ π : Equiv.Perm (Fin n), (((w ++ w.reverse).sublistsLen m).map
    (fun v => ⟪x, (v.map (fun i => A (π i))).prod x⟫)).sum

noncomputable def collisionCoefficient {n : ℕ} (A : Fin n → E →L[ℝ] E)
    (w : List (Fin n)) (x : E) (m : ℕ) : ℝ :=
  energyCoefficient A w x m -
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * 2 ^ m / m.factorial *
      ⟪x, ((∑ i, A i) ^ m) x⟫

lemma collisionCoefficient_zero {n : ℕ} (A : Fin n → E →L[ℝ] E)
    (w : List (Fin n)) (x : E) : collisionCoefficient A w x 0 = 0 := by
  simp [collisionCoefficient, energyCoefficient]

lemma collisionCoefficient_one {n : ℕ} (A : Fin n → E →L[ℝ] E)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n) (x : E) :
    collisionCoefficient A w x 1 = 0 := by
  unfold collisionCoefficient energyCoefficient
  rw [palindrome_coefficient_one A w hw hlen x]
  simp

lemma collisionCoefficient_two {n : ℕ} (hn : 0 < n)
    (A : Fin n → E →L[ℝ] E) (hs : ∀ i, (A i).toLinearMap.IsSymmetric)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n) (x : E) :
    collisionCoefficient A w x 2 =
      -(Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ∑ i, ‖A i x‖ ^ 2 := by
  unfold collisionCoefficient energyCoefficient
  rw [palindrome_coefficient_two hn A hs w hw hlen x]
  rw [show (2 : ℝ) ^ 2 = 4 by norm_num, show ((2 : ℕ).factorial : ℝ) = 2 by norm_num]
  ring

lemma inner_operator_list_sum (ops : List (E →L[ℝ] E)) (x : E) :
    ⟪x, ops.sum x⟫ = (ops.map (fun B => ⟪x, B x⟫)).sum := by
  induction ops with
  | nil => simp
  | cons B ops ih => simp [ih, inner_add_right]

lemma palindrome_graded_energy {I : Type*} (A : I → E →L[ℝ] E)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (w : List I) (η : ℝ) (x : E) :
    ‖(w.reverse.map (fun i => 1 + (-η) • A i)).prod x‖ ^ 2 =
      ∑ m ∈ Finset.range (2 * w.length + 1), (-η) ^ m *
        (((w ++ w.reverse).sublistsLen m).map (fun v => ⟪x, (v.map A).prod x⟫)).sum := by
  have hB : ∀ i, (1 + (-η) • A i).toLinearMap.IsSymmetric := by
    intro i u v
    change ⟪u + (-η) • A i u, v⟫ = ⟪u, v + (-η) • A i v⟫
    rw [inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right]
    have he : ⟪A i u, v⟫ = ⟪u, A i v⟫ := hs i u v
    rw [he]
  rw [← palindrome_energy _ hB w x, ordered_product_graded_expansion,
    inner_operator_list_sum, List.map_map]
  simp only [Function.comp_def, smul_apply, inner_smul_right]
  simp_rw [inner_operator_list_sum]
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range, List.length_append, List.length_reverse, ← two_mul,
    List.map_map, Function.comp_def]

lemma expected_homogeneous_expansion {n : ℕ}
    (A : Fin n → E →L[ℝ] E) (hs : ∀ i, (A i).toLinearMap.IsSymmetric)
    (w : List (Fin n)) (hlen : w.length = n) (η : ℝ) (x : E) :
    (∑ π : Equiv.Perm (Fin n),
      ‖(w.reverse.map (fun i => 1 + (-η) • A (π i))).prod x‖ ^ 2) =
      ∑ m ∈ Finset.range (2 * n + 1), (-η) ^ m * energyCoefficient A w x m := by
  simp_rw [palindrome_graded_energy _ (fun i => hs _) w η x, hlen]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.mul_sum]
  rfl

lemma collision_series_nonpos {n : ℕ} (hn : 0 < n)
    (A : Fin n → E →L[ℝ] E) {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (hA : ∀ i, ‖A i‖ ≤ L)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n)
    (hstep : η * n * L ≤ 1 / 32) (K : ℕ) (x : E) :
    (∑ m ∈ Finset.range (K + 3), (-η) ^ m * collisionCoefficient A w x m) ≤ 0 := by
  let C : ℝ := Fintype.card (Equiv.Perm (Fin n))
  let Q : ℝ := ∑ i, ‖A i x‖ ^ 2
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hN : 0 ≤ (n : ℝ) * L := by positivity
  have hsmall : 2 * η * ((n : ℝ) * L) ≤ 1 / 2 := by nlinarith
  have ht : ∀ j, (-η) ^ (j + 3) * collisionCoefficient A w x (j + 3) ≤
      η ^ (j + 3) * (8 * C * (2 * ((n : ℝ) * L)) ^ (j + 1) * Q) := by
    intro j
    have hb := palindrome_coefficient_remainder hn A hL hs hA w hw hlen (j + 1) x
    change |collisionCoefficient A w x (j + 3)| ≤ _ at hb
    calc
      _ ≤ |(-η) ^ (j + 3) * collisionCoefficient A w x (j + 3)| := le_abs_self _
      _ = η ^ (j + 3) * |collisionCoefficient A w x (j + 3)| := by
        rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg hη]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hb) (pow_nonneg hη _)
  have htail : (∑ j ∈ Finset.range K, (-η) ^ (j + 3) * collisionCoefficient A w x (j + 3)) ≤
      32 * C * η ^ 3 * ((n : ℝ) * L) * Q :=
    (Finset.sum_le_sum (fun j _ => ht j)).trans (collision_tail_bound hη hN hC hQ hsmall K)
  rw [show K + 3 = 3 + K by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, collisionCoefficient_zero,
    collisionCoefficient_one A w hw hlen, collisionCoefficient_two hn A hs w hw hlen,
    pow_zero, pow_one, zero_add, mul_zero, add_zero]
  have he : (-η) ^ 2 * (-C * Q) = -C * η ^ 2 * Q := by ring
  change (-η) ^ 2 * (-C * Q) +
    (∑ j ∈ Finset.range K, (-η) ^ (3 + j) * collisionCoefficient A w x (3 + j)) ≤ 0
  simp_rw [show ∀ j : ℕ, 3 + j = j + 3 by omega]
  rw [he]
  have habsorb := mul_le_mul_of_nonneg_left hstep (show 0 ≤ 32 * C * η ^ 2 * Q by positivity)
  nlinarith

lemma pure_series_bound [CompleteSpace E] (H : E →L[ℝ] E) {N η : ℝ}
    (hN : 0 < N) (hη : 0 ≤ η) (hstep : η * N ≤ 1 / 32)
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫) (hH : ‖H‖ ≤ N)
    (K : ℕ) (x : E) :
    (∑ m ∈ Finset.range (K + 2), (-2 * η) ^ m / (m.factorial : ℝ) *
      ⟪x, (H ^ m) x⟫) ≤ ‖x‖ ^ 2 - η * ⟪x, H x⟫ := by
  have hx := hp x
  have ht := positive_power_tail H hN hη (by nlinarith) hs hp hH K x
  rw [show K + 2 = 2 + K by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, one_mul,
    one_apply_eq_self, real_inner_self_eq_norm_sq, zero_add]
  simp_rw [show ∀ j : ℕ, 2 + j = j + 2 by omega]
  have hm := mul_le_mul_of_nonneg_right hstep (show 0 ≤ η * ⟪x, H x⟫ by positivity)
  nlinarith

lemma homogeneous_mean_square_contract [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    (A : Fin n → E →L[ℝ] E) {L μ η : ℝ} (hL : 0 < L) (hμ : 0 ≤ μ) (hη : 0 ≤ η)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (hA : ∀ i, ‖A i‖ ≤ L)
    (hcoercive : ∀ y, (n : ℝ) * μ * ‖y‖ ^ 2 ≤ ⟪y, (∑ i, A i) y⟫)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n)
    (hstep : η * n * L ≤ 1 / 32) (x : E) :
    (∑ π : Equiv.Perm (Fin n),
      ‖(w.reverse.map (fun i => 1 + (-η) • A (π i))).prod x‖ ^ 2) ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (1 - η * n * μ) * ‖x‖ ^ 2 := by
  let C : ℝ := Fintype.card (Equiv.Perm (Fin n))
  let S : E →L[ℝ] E := ∑ i, A i
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hSsym : S.toLinearMap.IsSymmetric := by
    intro u v
    change ⟪S u, v⟫ = ⟪u, S v⟫
    simp only [S, sum_apply, sum_inner, inner_sum]
    exact Finset.sum_congr rfl (fun i _ => hs i u v)
  have hSnorm : ‖S‖ ≤ (n : ℝ) * L := by
    calc
      _ ≤ ∑ i, ‖A i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, L := Finset.sum_le_sum (fun i _ => hA i)
      _ = _ := by simp
  have hSpos : ∀ y, 0 ≤ ⟪y, S y⟫ := fun y =>
    (show 0 ≤ (n : ℝ) * μ * ‖y‖ ^ 2 by positivity).trans (hcoercive y)
  have hnL : 0 < (n : ℝ) * L := mul_pos (by exact_mod_cast hn) hL
  have hbound := pure_series_bound S hnL hη (by nlinarith) hSsym.clm_adjoint_eq hSpos hSnorm
    (2 * n - 1) x
  have hcollision := collision_series_nonpos hn A hL.le hη hs hA w hw hlen hstep (2 * n - 2) x
  have he : ∀ m, (-η) ^ m * energyCoefficient A w x m =
      C * ((-2 * η) ^ m / (m.factorial : ℝ) * ⟪x, (S ^ m) x⟫) +
      (-η) ^ m * collisionCoefficient A w x m := by
    intro m
    unfold collisionCoefficient
    dsimp [C, S]
    rw [show -2 * η = (-η) * 2 by ring, mul_pow]
    ring
  rw [expected_homogeneous_expansion A hs w hlen η x]
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [show 2 * n - 1 + 2 = 2 * n + 1 by omega] at hbound
  rw [show 2 * n - 2 + 3 = 2 * n + 1 by omega] at hcollision
  have hb := mul_le_mul_of_nonneg_left hbound hC
  have hm := mul_le_mul_of_nonneg_left (hcoercive x) (show 0 ≤ C * η by positivity)
  change C * _ + _ ≤ C * (1 - η * n * μ) * ‖x‖ ^ 2
  dsimp [S] at hb
  nlinarith

end OracleTemplate.Reshuffling
