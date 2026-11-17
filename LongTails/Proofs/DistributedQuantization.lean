import LongTails.Algorithms.DistributedQuantization
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Tactic

namespace LongTails.Proofs.DistributedQuantization

open LongTails.Algorithms.DistributedQuantization

lemma encode_length {d width : ℕ} (x : Grid d width) :
    (encode x).length = d * width := by
  simp [encode]

lemma decode_encode {d width : ℕ} (x : Grid d width) :
    decode d width (encode x) = x := by
  unfold decode
  rw [dite_eq_left (encode_length x)]
  have h : (fun i : Fin (d * width) =>
      (encode x).get ⟨i.val, (encode_length x).symm ▸ i.isLt⟩) = bitEquiv d width x := by
    funext i
    simp [encode]
  rw [h]
  exact (bitEquiv d width).symm_apply_apply x

lemma message_length (d width : ℕ) (spacing : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    (message d width spacing x).length = d * width :=
  encode_length _

lemma receive_message (d width : ℕ) (spacing : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    receive d width spacing (message d width spacing x) =
      reconstruct spacing (quantize d width spacing x) := by
  simp only [receive, message, decode_encode]

lemma coordinate_error (d width : ℕ) (spacing : ℝ) (hspacing : 0 < spacing)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d)
    (hx : |x i| ≤ spacing * ((2 ^ width - 1 : ℕ) : ℝ) / 2) :
    |reconstruct spacing (quantize d width spacing x) i - x i| ≤ spacing := by
  let M : ℕ := 2 ^ width - 1
  have hmul : x i / spacing * spacing = x i := div_mul_cancel₀ _ hspacing.ne'
  have hx' := abs_le.mp hx
  have hzero : 0 ≤ x i / spacing + (M : ℝ) / 2 := by
    dsimp [M]
    nlinarith
  have htop : x i / spacing + (M : ℝ) / 2 ≤ (M : ℝ) := by
    dsimp [M]
    nlinarith
  have hfloor : ⌊x i / spacing + (M : ℝ) / 2⌋₊ ≤ M := Nat.floor_le_of_le htop
  have hlo := Nat.floor_le hzero
  have hhi := Nat.lt_floor_add_one (x i / spacing + (M : ℝ) / 2)
  change |spacing * ((min ⌊x i / spacing + (M : ℝ) / 2⌋₊ M : ℕ) -
    (M : ℝ) / 2) - x i| ≤ spacing
  rw [min_eq_left hfloor]
  apply abs_le.mpr
  constructor <;> nlinarith

lemma reconstruction_error (d width : ℕ) (spacing : ℝ) (hspacing : 0 < spacing)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, |x i| ≤ spacing * ((2 ^ width - 1 : ℕ) : ℝ) / 2) :
    ‖reconstruct spacing (quantize d width spacing x) - x‖ ^ 2 ≤ d * spacing ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _ : Fin d, spacing ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := coordinate_error d width spacing hspacing x i (hx i)
      have hs := mul_self_le_mul_self (abs_nonneg _) h
      simpa only [← pow_two, sq_abs, PiLp.sub_apply] using hs
    _ = _ := by simp

lemma message_error (d width : ℕ) (spacing : ℝ) (hspacing : 0 < spacing)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, |x i| ≤ spacing * ((2 ^ width - 1 : ℕ) : ℝ) / 2) :
    ‖receive d width spacing (message d width spacing x) - x‖ ^ 2 ≤ d * spacing ^ 2 := by
  rw [receive_message]
  exact reconstruction_error d width spacing hspacing x hx

lemma measurable_reconstruction (d width : ℕ) (spacing : ℝ) :
    Measurable (fun x : EuclideanSpace ℝ (Fin d) =>
      reconstruct spacing (quantize d width spacing x)) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  have hx : Measurable (fun x : EuclideanSpace ℝ (Fin d) => x i) :=
    (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)
  have hfloor := Nat.measurable_floor.comp
    ((hx.div_const spacing).add_const (((2 ^ width - 1 : ℕ) : ℝ) / 2))
  have hcode : Measurable (fun m : ℕ =>
      spacing * (((min m (2 ^ width - 1) : ℕ) : ℝ) - ((2 ^ width - 1 : ℕ) : ℝ) / 2)) :=
    measurable_of_countable _
  exact hcode.comp hfloor

lemma measurable_roundTrip (d width : ℕ) (spacing : ℝ) :
    Measurable (fun x : EuclideanSpace ℝ (Fin d) =>
      receive d width spacing (message d width spacing x)) := by
  simp_rw [receive_message]
  exact measurable_reconstruction d width spacing

lemma measurable_roundTrip_joint (d width : ℕ) :
    Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin d) =>
      receive d width z.1 (message d width z.1 z.2)) := by
  simp_rw [receive_message]
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  have hx : Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin d) => z.2 i) :=
    (measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp measurable_snd)
  have hfloor := Nat.measurable_floor.comp
    ((hx.div measurable_fst).add_const (((2 ^ width - 1 : ℕ) : ℝ) / 2))
  have hindex : Measurable (fun m : ℕ =>
      (((min m (2 ^ width - 1) : ℕ) : ℝ) - ((2 ^ width - 1 : ℕ) : ℝ) / 2)) :=
    measurable_of_countable _
  exact measurable_fst.mul (hindex.comp hfloor)

end LongTails.Proofs.DistributedQuantization
