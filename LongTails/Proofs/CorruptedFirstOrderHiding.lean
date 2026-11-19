import LongTails.Proofs.CorruptedFirstOrderChain
import LongTails.Proofs.SmoothConvexFiniteHiding
import LongTails.Proofs.FiniteSumNondualLowerBound

open scoped BigOperators
open LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardOracle
open LongTails.Proofs.CorruptedFirstOrderChain LongTails.Proofs.SmoothConvexFiniteHiding
open LongTails.Proofs.FiniteSumNondualLowerHiding LongTails.Proofs.FiniteSumNondualLowerExposure
open LongTails.Proofs.FiniteSumNondualLowerAveraging LongTails.Proofs.FiniteSumNondualLowerBound

namespace LongTails.Proofs.CorruptedFirstOrderHiding

open Classical

variable {d n : ℕ}

def Hit (A : Method d) (s : A.State) (S : Scale) (x0 : Space d) (w : List (Fin d)) : Prop :=
  ∃ j : Fin (n + 1), ∃ π : Fin (n + 1) ↪ Fin d, List.ofFn π = w ∧
    0 < hits (largeSet (2 * radius n) (1 / 4) (observation A s S x0 j π)) (w.drop j.val)

lemma few_hits (A : Method d) (s : A.State) (S : Scale) (x0 : Space d)
    (hd : 2 ^ 32 * (n + 1) ^ 4 ≤ d) :
    8 * (∑ w : CoordinateWords d n, if Hit (n := n) A s S x0 w.val then (1 : ℝ) else 0) ≤
      Fintype.card (CoordinateWords d n) := by
  let D : ℝ := d - (n + 1)
  have hr : (2 * radius n) ^ 2 / (1 / 4) ^ 2 = 2 ^ 28 * ((n : ℝ) + 1) ^ 2 := by
    unfold radius; ring
  have hd' : 2 ^ 32 * ((n : ℝ) + 1) ^ 4 ≤ (d : ℝ) := by exact_mod_cast hd
  have hpoly : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 4 := by
    nlinarith [pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) 2,
      pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) 3, pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) 4]
  have hroom : 8 * (((n : ℝ) + 1) ^ 2 * (2 ^ 28 * ((n : ℝ) + 1) ^ 2)) ≤ D := by
    dsimp [D]
    nlinarith
  have hD : 0 ≤ D := by
    exact (by positivity : (0 : ℝ) ≤ 8 * (((n : ℝ) + 1) ^ 2 * (2 ^ 28 * ((n : ℝ) + 1) ^ 2))).trans hroom
  have hc := bounded_prefix_bad_count (d := d) (K := n + 1) (2 * radius n) (1 / 4) D
    (by have := radius_pos n; positivity) (by norm_num) hD (by dsimp [D]; push_cast; linarith)
    Fin.val (fun j : Fin (n + 1) => j.isLt.le) (observation A s S x0) (observation_prefix A s S x0)
  let U := (distinctWords (n + 1) (Finset.univ : Finset (Fin d)))
  let B := U.filter (Hit (n := n) A s S x0)
  have heq := subtype_indicator_sum U (Hit (n := n) A s S x0)
  change (∑ w : CoordinateWords d n, if Hit (n := n) A s S x0 w.val then (1 : ℝ) else 0) =
    (B.card : ℝ) at heq
  rw [heq]
  simp only [Fintype.card_fin, hr, Nat.cast_succ] at hc
  have hcnt : D * (B.card : ℝ) ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) *
      (2 ^ 28 * ((n : ℝ) + 1) ^ 2) * (U.card : ℝ) := by
    convert hc using 1
    apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
    ext w
    simp only [B, U, Finset.mem_filter, Hit]
  change 8 * (B.card : ℝ) ≤ Fintype.card (↥U)
  rw [Fintype.card_coe]
  have hm := mul_le_mul_of_nonneg_right hroom (Nat.cast_nonneg B.card : (0 : ℝ) ≤ B.card)
  have hx : 0 < ((n : ℝ) + 1) ^ 2 * (2 ^ 28 * ((n : ℝ) + 1) ^ 2) := by positivity
  apply (mul_le_mul_iff_right₀ hx).mp
  nlinarith only [hm, hcnt]

lemma miss_lower (A : Method d) (s : A.State) (S : Scale) (x0 : Space d)
    (w : CoordinateWords d n) (hh : ¬ Hit (n := n) A s S x0 w.val) :
    S.a / S.lam / 20 ≤ ‖objGrad S (coordinateEmbedding w) x0
      (A.output ((realStep A S x0 (coordinateEmbedding w))^[n] s))‖ := by
  apply hard_output
  intro j hj i hi
  rw [sel_apply]
  apply not_largeSet_small _ _ _ hj
  intro hm
  exact hh ⟨j, coordinateEmbedding w, coordinateEmbedding_labels w,
    by simpa only [coordinateEmbedding_labels] using (hits_drop_positive (coordinateEmbedding w)
      j.val _ i hi hm)⟩

end LongTails.Proofs.CorruptedFirstOrderHiding
