import LongTails.Proofs.ReshufflingAffineEpoch
import LongTails.Proofs.ReshufflingHomogeneousEnergy
import LongTails.Proofs.ReshufflingIteration

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.Reshuffling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma reshuffling_cross_young {η n μ L G r : ℝ} (hη : 0 ≤ η) (hn : 0 ≤ n) (hμ : 0 < μ) :
    32 * η ^ 2 * n * L * G * r ≤
      η * n * μ / 2 * r ^ 2 + 512 * η ^ 3 * n * L ^ 2 * G ^ 2 / μ := by
  have he : η * n * μ / 2 * r ^ 2 + 512 * η ^ 3 * n * L ^ 2 * G ^ 2 / μ -
      32 * η ^ 2 * n * L * G * r = η * n / (2 * μ) * (μ * r - 32 * η * L * G) ^ 2 := by
    field_simp
    ring
  have hp : 0 ≤ η * n / (2 * μ) * (μ * r - 32 * η * L * G) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  linarith

omit [CompleteSpace E] in
lemma affine_pass_energy {I : Type*} (A : I → E →L[ℝ] E) (b : I → E) {η : ℝ}
    (hη : 0 ≤ η) (w : List I) (x : E) :
    ‖RandomReshuffling.pass (fun i y => A i y + b i) η w x‖ ^ 2 =
      ‖epochLinear A η w x‖ ^ 2 - 2 * η * ⟪epochLinear A η w x, epochNoise A b η w⟫ +
        η ^ 2 * ‖epochNoise A b η w‖ ^ 2 := by
  rw [affine_pass, norm_sub_sq_real, inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hη, mul_pow]
  ring

lemma affine_epoch_energy {n : ℕ} (hn : 0 < n)
    (A : Fin n → E →L[ℝ] E) (b : Fin n → E) {L μ G η : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (hη : 0 ≤ η)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (hA : ∀ i, ‖A i‖ ≤ L)
    (hcoercive : ∀ y, (n : ℝ) * μ * ‖y‖ ^ 2 ≤ ⟪y, (∑ i, A i) y⟫)
    (hb : ∑ i, b i = 0) (hbound : ∀ i, ‖b i‖ ≤ G)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n)
    (hstep : η * n * L ≤ 1 / 32) (x : E) :
    (∑ π : Equiv.Perm (Fin n),
      ‖RandomReshuffling.pass (fun i y => A (π i) y + b (π i)) η w x‖ ^ 2) ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
        ((1 - η * n * μ / 2) * ‖x‖ ^ 2 +
          512 * η ^ 3 * n * L ^ 2 * G ^ 2 / μ + 4 * η ^ 4 * (n : ℝ) ^ 3 * L ^ 2 * G ^ 2) := by
  let C : ℝ := Fintype.card (Equiv.Perm (Fin n))
  let U : ℝ := ∑ π : Equiv.Perm (Fin n), ‖epochLinear (fun i => A (π i)) η w x‖ ^ 2
  let V : ℝ := ∑ π : Equiv.Perm (Fin n), ‖epochNoise (fun i => A (π i)) (fun i => b (π i)) η w‖ ^ 2
  let cross : ℝ := ∑ π : Equiv.Perm (Fin n),
    ⟪epochLinear (fun i => A (π i)) η w x, epochNoise (fun i => A (π i)) (fun i => b (π i)) η w⟫
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hU : U ≤ C * (1 - η * n * μ) * ‖x‖ ^ 2 :=
    homogeneous_mean_square_contract hn A hL hμ.le hη hs hA hcoercive w hw hlen hstep x
  have hV : V ≤ 4 * C * η ^ 2 * (n : ℝ) ^ 3 * L ^ 2 * G ^ 2 :=
    epoch_noise_second_moment A b hL.le hη hA hb hbound w hw hlen hstep
  have hc : |cross| ≤ ‖x‖ * (C * 16 * η * n * L * G) :=
    epoch_cross_inner_bound A b hL.le hη hs hA hb hbound w hw hlen hstep x
  have hc' : -2 * η * cross ≤ C * (32 * η ^ 2 * n * L * G * ‖x‖) := by
    have hh := mul_le_mul_of_nonneg_left ((neg_le_abs cross).trans hc) (show 0 ≤ 2 * η by positivity)
    nlinarith
  have hy := mul_le_mul_of_nonneg_left
    (reshuffling_cross_young (L := L) (G := G) (r := ‖x‖) hη (Nat.cast_nonneg n) hμ) hC
  have hv' := mul_le_mul_of_nonneg_left hV (sq_nonneg η)
  have he : (∑ π : Equiv.Perm (Fin n),
      ‖RandomReshuffling.pass (fun i y => A (π i) y + b (π i)) η w x‖ ^ 2) =
      U - 2 * η * cross + η ^ 2 * V := by
    simp_rw [affine_pass_energy _ _ hη]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  rw [he]
  change U - 2 * η * cross + η ^ 2 * V ≤ C * _
  nlinarith

lemma affine_epochs_energy {n : ℕ} (hn : 0 < n)
    (A : Fin n → E →L[ℝ] E) (b : Fin n → E) {L μ G η : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L) (hη : 0 ≤ η)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (hA : ∀ i, ‖A i‖ ≤ L)
    (hcoercive : ∀ y, (n : ℝ) * μ * ‖y‖ ^ 2 ≤ ⟪y, (∑ i, A i) y⟫)
    (hb : ∑ i, b i = 0) (hbound : ∀ i, ‖b i‖ ≤ G)
    (hstep : η * n * L ≤ 1 / 32) (K : ℕ) (x : E) :
    (∑ seed : Fin K → Equiv.Perm (Fin n),
      ‖RandomReshuffling.epochs (fun i y => A i y + b i) η
        (List.ofFn (fun k => List.ofFn (seed k))) x‖ ^ 2) ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ^ K *
        ((1 - η * n * μ / 2) ^ K * ‖x‖ ^ 2 +
          1024 * η ^ 2 * L ^ 2 * G ^ 2 / μ ^ 2 + 8 * η ^ 3 * (n : ℝ) ^ 2 * L ^ 2 * G ^ 2 / μ) := by
  let r := 1 - η * n * μ / 2
  let B := 1024 * η ^ 2 * L ^ 2 * G ^ 2 / μ ^ 2 + 8 * η ^ 3 * (n : ℝ) ^ 2 * L ^ 2 * G ^ 2 / μ
  let g := fun i y => A i y + b i
  let w := List.ofFn (fun i : Fin n => i)
  have hw : w.Nodup := List.nodup_ofFn.mpr Function.injective_id
  have hlen : w.length = n := List.length_ofFn
  have hμstep : η * n * μ ≤ 1 / 32 :=
    (mul_le_mul_of_nonneg_left hμL (show 0 ≤ η * n by positivity)).trans hstep
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpass : ∀ (π : Equiv.Perm (Fin n)) y,
      RandomReshuffling.pass g η (List.ofFn π) y =
        RandomReshuffling.pass (fun i z => A (π i) z + b (π i)) η w y := by
    intro π y
    simpa only [w, List.map_ofFn, Function.comp_def] using RandomReshuffling.pass_map g η π w y
  have hd : 512 * η ^ 3 * n * L ^ 2 * G ^ 2 / μ + 4 * η ^ 4 * (n : ℝ) ^ 3 * L ^ 2 * G ^ 2 =
      (1 - r) * B := by
    dsimp [r, B]
    field_simp; ring
  have hepoch : ∀ y, (∑ π : Equiv.Perm (Fin n), ‖RandomReshuffling.pass g η (List.ofFn π) y‖ ^ 2) ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (r * ‖y‖ ^ 2 + (1 - r) * B) := by
    intro y
    simp_rw [hpass]
    have hh := affine_epoch_energy hn A b hL hμ hη hs hA hcoercive hb hbound w hw hlen hstep y
    have ht : r * ‖y‖ ^ 2 + (1 - r) * B =
        (1 - η * n * μ / 2) * ‖y‖ ^ 2 + 512 * η ^ 3 * n * L ^ 2 * G ^ 2 / μ +
          4 * η ^ 4 * (n : ℝ) ^ 3 * L ^ 2 * G ^ 2 := by rw [← hd]; dsimp [r]; ring
    rw [ht]
    exact hh
  have hiter := RandomReshuffling.epochs_sum_energy g η (fun y => ‖y‖ ^ 2) hr hepoch K x
  calc
    _ ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ^ K * (r ^ K * ‖x‖ ^ 2 + (1 - r ^ K) * B) := hiter
    _ ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ^ K * (r ^ K * ‖x‖ ^ 2 + B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg (pow_nonneg hr K) hB]
    _ = _ := by dsimp [r, B]; ring

end OracleTemplate.Reshuffling
