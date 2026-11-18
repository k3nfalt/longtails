import LongTails.Algorithms.LeonAggregate
import LongTails.Proofs.DashaModular
import LongTails.Proofs.DashaQuantization
import LongTails.Algorithms.LeonTuning
import LongTails.Algorithms.LeonTrajectory

namespace LongTails.Proofs.LeonAggregate

open LongTails.Algorithms.LeonAggregate
open LongTails.Algorithms.DashaQuantization (Vector center)
open LongTails.Algorithms.DashaModular (restore modulus)

lemma decode_move {d : ℕ} (n width : ℕ) (spacing radius : ℝ) (hr : 0 ≤ radius)
    (anchor : Vector d) (received : Fin d → ℤ) :
    ‖decode n width spacing radius anchor received - anchor‖ ≤ radius := by
  unfold decode
  dsimp only
  split_ifs with h
  · simpa using h
  · simpa using hr

lemma decode_exact {d : ℕ} (n width : ℕ) (spacing radius : ℝ)
    (anchor : Vector d) (received raw : Fin d → ℤ)
    (hres : ∀ j, received j % modulus width = raw j % modulus width)
    (hlo : ∀ j, -(center width : ℤ) ≤ raw j)
    (hhi : ∀ j, raw j + center width < modulus width)
    (hmove : ‖displacement n spacing raw‖ ≤ radius) :
    decode n width spacing radius anchor received = anchor + displacement n spacing raw := by
  have he : (fun j => restore width (received j)) = raw := by
    funext j
    rw [← DashaModular.restore_mod, hres, DashaModular.restore_mod]
    exact DashaModular.restore_exact _ _ (hlo j) (hhi j)
  simp [decode, he, hmove]

lemma shifted_error {d : ℕ} (n width : ℕ) (spacing radius : ℝ) (hr : 0 ≤ radius)
    (parent actual target : Vector d) (received : Fin d → ℤ) :
    ‖decode n width spacing radius parent received - target‖ ≤
      ‖parent - actual‖ + radius + ‖actual - target‖ := by
  calc
    _ ≤ ‖decode n width spacing radius parent received - parent‖ + ‖parent - target‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ radius + (‖parent - actual‖ + ‖actual - target‖) :=
      add_le_add (decode_move _ _ _ _ hr _ _) (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ = _ := by ring

end LongTails.Proofs.LeonAggregate

namespace LongTails.Proofs.LeonPrecision

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.LeonAggregate
open LongTails.Algorithms.DashaQuantization (center)
open LongTails.Algorithms.DashaModular (modulus)

lemma capacity (p : Params) (l : ℕ) :
    16 * ((p.n : ℕ) * (p.d + 1)) * 4 ^ l < center (width p l) := by
  let m := (p.n : ℕ) * (p.d + 1)
  have hm : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  rw [pow_succ] at hm
  have hw : 2 ^ width p l = 128 * 2 ^ Nat.log2 m * 4 ^ l := by
    simp only [width, m, pow_add, pow_mul]
    norm_num
  rw [center, hw]
  change 16 * m * 4 ^ l < _
  have hpow : 0 < (4 : ℕ) ^ l := by positivity
  have hmul := Nat.mul_lt_mul_of_pos_right hm hpow
  rw [show 128 * 2 ^ Nat.log2 m * 4 ^ l = (64 * (2 ^ Nat.log2 m * 4 ^ l)) * 2 by ring,
    Nat.mul_div_cancel _ (by decide : 0 < 2)]
  nlinarith

lemma capacity_complement (p : Params) (l : ℕ) :
    (center (width p l) : ℤ) * 2 = modulus (width p l) := by
  have hwidth : 0 < width p l := by unfold width; omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hwidth.ne'
  unfold center modulus
  rw [hk, pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)]
  push_cast
  ring

lemma exact_small (p : Params) (hε : 0 < p.ε) (l : ℕ) (anchor : Point p)
    (received raw : Fin p.d → ℤ)
    (hres : ∀ j, received j % modulus (width p l) = raw j % modulus (width p l))
    (hv : ‖displacement p.n (spacing p) raw‖ ≤ radius p l) :
    decode p.n (width p l) (spacing p) (radius p l) anchor received =
      anchor + displacement p.n (spacing p) raw := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hd : 0 < (p.d + 1 : ℕ) := Nat.succ_pos _
  have hs : 0 < resolution p := by unfold resolution; positivity
  have hden : (0 : ℝ) < (p.d + 1 : ℕ) := by exact_mod_cast hd
  have hcap : (16 : ℝ) * ((p.n : ℝ) * (p.d + 1)) * (4 : ℝ) ^ l < center (width p l) := by
    exact_mod_cast capacity p l
  have habs (j : Fin p.d) : |raw j| < (center (width p l) : ℤ) := by
    have hco := (PiLp.norm_apply_le (displacement p.n (spacing p) raw) j).trans hv
    change |resolution p / (p.d + 1 : ℕ) / (p.n : ℝ) * (raw j : ℝ)| ≤
      8 * (4 : ℝ) ^ l * resolution p at hco
    rw [abs_mul, abs_of_pos (div_pos (div_pos hs hden) hn)] at hco
    have hbound : |(raw j : ℝ)| ≤ 8 * (4 : ℝ) ^ l * ((p.d + 1 : ℕ) : ℝ) * p.n := by
      apply (mul_le_mul_iff_right₀ hs).mp
      field_simp at hco ⊢
      nlinarith
    have hc : |(raw j : ℝ)| < center (width p l) := by
      push_cast at hbound
      nlinarith [show 0 ≤ (4 : ℝ) ^ l * (p.d + 1) * (p.n : ℝ) by positivity]
    exact_mod_cast hc
  apply LeonAggregate.decode_exact _ _ _ _ _ _ _ hres _ _ hv
  · intro j
    exact (abs_lt.mp (habs j)).1.le
  · intro j
    have h := (abs_lt.mp (habs j)).2
    linarith [capacity_complement p l]

end LongTails.Proofs.LeonPrecision

namespace LongTails.Proofs.LeonRounding

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonTrajectory
open LongTails.Algorithms.LeonAggregate
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.DashaQuantization (rounded reconstruct indices)

lemma sum_decode (p : Params) (s : Model p) (l : ℕ) (values : Fin p.n → List (Point p)) :
    displacement p.n (spacing p) (totalCodes p s l values) =
      (p.n : ℝ)⁻¹ • ∑ i, rounded p.d false (spacing p) (mean p (values i) - s.anchors (l + 1))
        (fun _ => 0) := by
  ext j
  simp [displacement, reconstruct, totalCodes, localCodes, rounded,
    PiLp.smul_apply, div_eq_inv_mul, Finset.mul_sum, mul_assoc]

lemma raw_error (p : Params) (hε : 0 < p.ε) (s : Model p) (l : ℕ)
    (values : Fin p.n → List (Point p)) :
    ‖s.anchors (l + 1) + displacement p.n (spacing p) (totalCodes p s l values) -
      (p.n : ℝ)⁻¹ • ∑ i, mean p (values i)‖ ≤ resolution p := by
  let a := s.anchors (l + 1)
  let v (i : Fin p.n) := mean p (values i)
  let w (i : Fin p.n) := rounded p.d false (spacing p) (v i - a) (fun _ => 0)
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.pos.ne'
  have hr : 0 < resolution p := by unfold resolution; positivity
  have hq : 0 < spacing p := by unfold spacing; positivity
  have he : a + (p.n : ℝ)⁻¹ • ∑ i, w i - (p.n : ℝ)⁻¹ • ∑ i, v i =
      (p.n : ℝ)⁻¹ • ∑ i, (w i - (v i - a)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_sub, smul_smul,
      inv_mul_cancel₀ hn, one_smul]
    abel
  rw [sum_decode]
  change ‖a + (p.n : ℝ)⁻¹ • ∑ i, w i - (p.n : ℝ)⁻¹ • ∑ i, v i‖ ≤ _
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (p.n : ℝ)⁻¹ * ∑ i, ‖w i - (v i - a)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (p.n : ℝ)⁻¹ * ∑ _i : Fin p.n, p.d * spacing p := by
      gcongr with i
      exact DashaQuantization.vector_initial_error _ _ hq _ _
    _ = p.d * spacing p := by simp [field, hn]
    _ ≤ resolution p := by
      unfold spacing
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      push_cast
      nlinarith

end LongTails.Proofs.LeonRounding

namespace LongTails.Proofs.LeonEstimator

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.LeonAggregate
open LongTails.Algorithms.LeonTrajectory
open LongTails.Algorithms.DashaModular (modulus)

lemma exact_from_anchor (p : Params) (hε : 0 < p.ε) (l : ℕ)
    (anchor truth previous : Point p) (received raw : Fin p.d → ℤ) (M : ℝ)
    (hres : ∀ j, received j % modulus (width p l) = raw j % modulus (width p l))
    (hanchor : ‖anchor - previous‖ ≤ M) (hnoise : ‖anchor + displacement p.n (spacing p) raw - truth‖ ≤ M)
    (hdrift : ‖truth - previous‖ ≤ 3 * (4 : ℝ) ^ l * resolution p)
    (hscale : M ≤ (4 : ℝ) ^ l * resolution p) :
    ‖decode p.n (width p l) (spacing p) (radius p l) anchor received - truth‖ ≤ M := by
  let v := displacement p.n (spacing p) raw
  have he : v = (anchor + v - truth) + (truth - previous) + (previous - anchor) := by abel
  have ht : ‖v‖ ≤ ‖anchor + v - truth‖ + ‖truth - previous‖ + ‖previous - anchor‖ := by
    calc
      _ = ‖(anchor + v - truth) + (truth - previous) + (previous - anchor)‖ := congrArg norm he
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  rw [norm_sub_rev previous] at ht
  have hpos : 0 ≤ (4 : ℝ) ^ l * resolution p := le_trans (norm_nonneg _) (hanchor.trans hscale)
  have hsmall : ‖v‖ ≤ radius p l := by unfold radius; dsimp only [v] at *; linarith
  rw [LeonPrecision.exact_small _ hε _ _ _ _ hres hsmall]
  exact hnoise

lemma initial_error (p : Params) (hε : 0 < p.ε) (l : ℕ) (truth : Point p)
    (received raw : Fin p.d → ℤ)
    (hres : ∀ j, received j % modulus (width p l) = raw j % modulus (width p l))
    (htrue : ‖truth‖ ≤ (4 : ℝ) ^ l * resolution p) :
    ‖decode p.n (width p l) (spacing p) (radius p l) 0 received - truth‖ ≤
      3 / 2 * ‖displacement p.n (spacing p) raw - truth‖ := by
  let v := displacement p.n (spacing p) raw
  by_cases hs : ‖v‖ ≤ radius p l
  · rw [LeonPrecision.exact_small _ hε _ _ _ _ hres hs, zero_add]
    linarith [norm_nonneg (v - truth)]
  · have hr : 0 ≤ radius p l := by
      unfold radius resolution
      positivity
    have hd := LeonAggregate.decode_move p.n (width p l) (spacing p) (radius p l) hr (0 : Point p) received
    rw [sub_zero] at hd
    have he := norm_sub_norm_le v truth
    have ht := norm_sub_le (decode p.n (width p l) (spacing p) (radius p l) 0 received) truth
    change _ ≤ 3 / 2 * ‖v - truth‖
    unfold radius at hs hd ht ⊢
    nlinarith [lt_of_not_ge hs, norm_nonneg truth]

end LongTails.Proofs.LeonEstimator
